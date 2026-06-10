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
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Meta_Simp_mkContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v_a_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; 
v_a_8_ = lean_ctor_get(v___x_7_, 0);
lean_inc(v_a_8_);
lean_dec_ref_known(v___x_7_, 1);
v___x_9_ = l_Lean_Meta_Simp_neutralConfig;
v___x_10_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_getContext___redArg___closed__0));
v___x_11_ = l_Lean_Options_empty;
v___x_12_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_9_, v___x_10_, v_a_8_, v___x_11_, v_a_3_, v_a_4_, v_a_5_);
return v___x_12_;
}
else
{
lean_object* v_a_13_; lean_object* v___x_15_; uint8_t v_isShared_16_; uint8_t v_isSharedCheck_20_; 
v_a_13_ = lean_ctor_get(v___x_7_, 0);
v_isSharedCheck_20_ = !lean_is_exclusive(v___x_7_);
if (v_isSharedCheck_20_ == 0)
{
v___x_15_ = v___x_7_;
v_isShared_16_ = v_isSharedCheck_20_;
goto v_resetjp_14_;
}
else
{
lean_inc(v_a_13_);
lean_dec(v___x_7_);
v___x_15_ = lean_box(0);
v_isShared_16_ = v_isSharedCheck_20_;
goto v_resetjp_14_;
}
v_resetjp_14_:
{
lean_object* v___x_18_; 
if (v_isShared_16_ == 0)
{
v___x_18_ = v___x_15_;
goto v_reusejp_17_;
}
else
{
lean_object* v_reuseFailAlloc_19_; 
v_reuseFailAlloc_19_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_19_, 0, v_a_13_);
v___x_18_ = v_reuseFailAlloc_19_;
goto v_reusejp_17_;
}
v_reusejp_17_:
{
return v___x_18_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_getContext___redArg___boxed(lean_object* v_a_21_, lean_object* v_a_22_, lean_object* v_a_23_, lean_object* v_a_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_getContext___redArg(v_a_21_, v_a_22_, v_a_23_);
lean_dec(v_a_23_);
lean_dec_ref(v_a_22_);
lean_dec_ref(v_a_21_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_getContext(lean_object* v_a_26_, lean_object* v_a_27_, lean_object* v_a_28_, lean_object* v_a_29_){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_getContext___redArg(v_a_26_, v_a_28_, v_a_29_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_getContext___boxed(lean_object* v_a_32_, lean_object* v_a_33_, lean_object* v_a_34_, lean_object* v_a_35_, lean_object* v_a_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_getContext(v_a_32_, v_a_33_, v_a_34_, v_a_35_);
lean_dec(v_a_35_);
lean_dec_ref(v_a_34_);
lean_dec(v_a_33_);
lean_dec_ref(v_a_32_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_matchPattern_x3f_go_x3f(lean_object* v_pattern_40_, lean_object* v_e_41_, lean_object* v_a_42_, lean_object* v_a_43_, lean_object* v_a_44_, lean_object* v_a_45_){
_start:
{
lean_object* v___x_47_; lean_object* v___x_48_; uint8_t v___x_49_; 
lean_inc_ref(v_e_41_);
v___x_47_ = l_Lean_Expr_toHeadIndex(v_e_41_);
lean_inc_ref(v_pattern_40_);
v___x_48_ = l_Lean_Expr_toHeadIndex(v_pattern_40_);
v___x_49_ = l_Lean_instBEqHeadIndex_beq(v___x_47_, v___x_48_);
lean_dec(v___x_48_);
lean_dec(v___x_47_);
if (v___x_49_ == 0)
{
lean_object* v___x_50_; lean_object* v___x_51_; 
lean_dec_ref(v_e_41_);
lean_dec_ref(v_pattern_40_);
v___x_50_ = lean_box(0);
v___x_51_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_51_, 0, v___x_50_);
return v___x_51_;
}
else
{
lean_object* v___x_52_; 
lean_inc_ref(v_e_41_);
lean_inc_ref(v_pattern_40_);
v___x_52_ = l_Lean_Meta_isExprDefEqGuarded(v_pattern_40_, v_e_41_, v_a_42_, v_a_43_, v_a_44_, v_a_45_);
if (lean_obj_tag(v___x_52_) == 0)
{
lean_object* v_a_53_; lean_object* v___x_55_; uint8_t v_isShared_56_; uint8_t v_isSharedCheck_99_; 
v_a_53_ = lean_ctor_get(v___x_52_, 0);
v_isSharedCheck_99_ = !lean_is_exclusive(v___x_52_);
if (v_isSharedCheck_99_ == 0)
{
v___x_55_ = v___x_52_;
v_isShared_56_ = v_isSharedCheck_99_;
goto v_resetjp_54_;
}
else
{
lean_inc(v_a_53_);
lean_dec(v___x_52_);
v___x_55_ = lean_box(0);
v_isShared_56_ = v_isSharedCheck_99_;
goto v_resetjp_54_;
}
v_resetjp_54_:
{
uint8_t v___x_57_; 
v___x_57_ = lean_unbox(v_a_53_);
lean_dec(v_a_53_);
if (v___x_57_ == 0)
{
uint8_t v___x_58_; 
v___x_58_ = l_Lean_Expr_isApp(v_e_41_);
if (v___x_58_ == 0)
{
lean_object* v___x_59_; lean_object* v___x_61_; 
lean_dec_ref(v_e_41_);
lean_dec_ref(v_pattern_40_);
v___x_59_ = lean_box(0);
if (v_isShared_56_ == 0)
{
lean_ctor_set(v___x_55_, 0, v___x_59_);
v___x_61_ = v___x_55_;
goto v_reusejp_60_;
}
else
{
lean_object* v_reuseFailAlloc_62_; 
v_reuseFailAlloc_62_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_62_, 0, v___x_59_);
v___x_61_ = v_reuseFailAlloc_62_;
goto v_reusejp_60_;
}
v_reusejp_60_:
{
return v___x_61_;
}
}
else
{
lean_object* v___x_63_; lean_object* v___x_64_; 
lean_del_object(v___x_55_);
v___x_63_ = l_Lean_Expr_appFn_x21(v_e_41_);
v___x_64_ = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_matchPattern_x3f_go_x3f(v_pattern_40_, v___x_63_, v_a_42_, v_a_43_, v_a_44_, v_a_45_);
if (lean_obj_tag(v___x_64_) == 0)
{
lean_object* v_a_65_; 
v_a_65_ = lean_ctor_get(v___x_64_, 0);
lean_inc(v_a_65_);
if (lean_obj_tag(v_a_65_) == 0)
{
lean_dec_ref(v_e_41_);
return v___x_64_;
}
else
{
lean_object* v___x_67_; uint8_t v_isShared_68_; uint8_t v_isSharedCheck_91_; 
v_isSharedCheck_91_ = !lean_is_exclusive(v___x_64_);
if (v_isSharedCheck_91_ == 0)
{
lean_object* v_unused_92_; 
v_unused_92_ = lean_ctor_get(v___x_64_, 0);
lean_dec(v_unused_92_);
v___x_67_ = v___x_64_;
v_isShared_68_ = v_isSharedCheck_91_;
goto v_resetjp_66_;
}
else
{
lean_dec(v___x_64_);
v___x_67_ = lean_box(0);
v_isShared_68_ = v_isSharedCheck_91_;
goto v_resetjp_66_;
}
v_resetjp_66_:
{
lean_object* v_val_69_; lean_object* v___x_71_; uint8_t v_isShared_72_; uint8_t v_isSharedCheck_90_; 
v_val_69_ = lean_ctor_get(v_a_65_, 0);
v_isSharedCheck_90_ = !lean_is_exclusive(v_a_65_);
if (v_isSharedCheck_90_ == 0)
{
v___x_71_ = v_a_65_;
v_isShared_72_ = v_isSharedCheck_90_;
goto v_resetjp_70_;
}
else
{
lean_inc(v_val_69_);
lean_dec(v_a_65_);
v___x_71_ = lean_box(0);
v_isShared_72_ = v_isSharedCheck_90_;
goto v_resetjp_70_;
}
v_resetjp_70_:
{
lean_object* v_fst_73_; lean_object* v_snd_74_; lean_object* v___x_76_; uint8_t v_isShared_77_; uint8_t v_isSharedCheck_89_; 
v_fst_73_ = lean_ctor_get(v_val_69_, 0);
v_snd_74_ = lean_ctor_get(v_val_69_, 1);
v_isSharedCheck_89_ = !lean_is_exclusive(v_val_69_);
if (v_isSharedCheck_89_ == 0)
{
v___x_76_ = v_val_69_;
v_isShared_77_ = v_isSharedCheck_89_;
goto v_resetjp_75_;
}
else
{
lean_inc(v_snd_74_);
lean_inc(v_fst_73_);
lean_dec(v_val_69_);
v___x_76_ = lean_box(0);
v_isShared_77_ = v_isSharedCheck_89_;
goto v_resetjp_75_;
}
v_resetjp_75_:
{
lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_81_; 
v___x_78_ = l_Lean_Expr_appArg_x21(v_e_41_);
lean_dec_ref(v_e_41_);
v___x_79_ = lean_array_push(v_snd_74_, v___x_78_);
if (v_isShared_77_ == 0)
{
lean_ctor_set(v___x_76_, 1, v___x_79_);
v___x_81_ = v___x_76_;
goto v_reusejp_80_;
}
else
{
lean_object* v_reuseFailAlloc_88_; 
v_reuseFailAlloc_88_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_88_, 0, v_fst_73_);
lean_ctor_set(v_reuseFailAlloc_88_, 1, v___x_79_);
v___x_81_ = v_reuseFailAlloc_88_;
goto v_reusejp_80_;
}
v_reusejp_80_:
{
lean_object* v___x_83_; 
if (v_isShared_72_ == 0)
{
lean_ctor_set(v___x_71_, 0, v___x_81_);
v___x_83_ = v___x_71_;
goto v_reusejp_82_;
}
else
{
lean_object* v_reuseFailAlloc_87_; 
v_reuseFailAlloc_87_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_87_, 0, v___x_81_);
v___x_83_ = v_reuseFailAlloc_87_;
goto v_reusejp_82_;
}
v_reusejp_82_:
{
lean_object* v___x_85_; 
if (v_isShared_68_ == 0)
{
lean_ctor_set(v___x_67_, 0, v___x_83_);
v___x_85_ = v___x_67_;
goto v_reusejp_84_;
}
else
{
lean_object* v_reuseFailAlloc_86_; 
v_reuseFailAlloc_86_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_86_, 0, v___x_83_);
v___x_85_ = v_reuseFailAlloc_86_;
goto v_reusejp_84_;
}
v_reusejp_84_:
{
return v___x_85_;
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
lean_dec_ref(v_e_41_);
return v___x_64_;
}
}
}
else
{
lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_97_; 
lean_dec_ref(v_pattern_40_);
v___x_93_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_matchPattern_x3f_go_x3f___closed__0));
v___x_94_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_94_, 0, v_e_41_);
lean_ctor_set(v___x_94_, 1, v___x_93_);
v___x_95_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_95_, 0, v___x_94_);
if (v_isShared_56_ == 0)
{
lean_ctor_set(v___x_55_, 0, v___x_95_);
v___x_97_ = v___x_55_;
goto v_reusejp_96_;
}
else
{
lean_object* v_reuseFailAlloc_98_; 
v_reuseFailAlloc_98_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_98_, 0, v___x_95_);
v___x_97_ = v_reuseFailAlloc_98_;
goto v_reusejp_96_;
}
v_reusejp_96_:
{
return v___x_97_;
}
}
}
}
else
{
lean_object* v_a_100_; lean_object* v___x_102_; uint8_t v_isShared_103_; uint8_t v_isSharedCheck_107_; 
lean_dec_ref(v_e_41_);
lean_dec_ref(v_pattern_40_);
v_a_100_ = lean_ctor_get(v___x_52_, 0);
v_isSharedCheck_107_ = !lean_is_exclusive(v___x_52_);
if (v_isSharedCheck_107_ == 0)
{
v___x_102_ = v___x_52_;
v_isShared_103_ = v_isSharedCheck_107_;
goto v_resetjp_101_;
}
else
{
lean_inc(v_a_100_);
lean_dec(v___x_52_);
v___x_102_ = lean_box(0);
v_isShared_103_ = v_isSharedCheck_107_;
goto v_resetjp_101_;
}
v_resetjp_101_:
{
lean_object* v___x_105_; 
if (v_isShared_103_ == 0)
{
v___x_105_ = v___x_102_;
goto v_reusejp_104_;
}
else
{
lean_object* v_reuseFailAlloc_106_; 
v_reuseFailAlloc_106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_106_, 0, v_a_100_);
v___x_105_ = v_reuseFailAlloc_106_;
goto v_reusejp_104_;
}
v_reusejp_104_:
{
return v___x_105_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_matchPattern_x3f_go_x3f___boxed(lean_object* v_pattern_108_, lean_object* v_e_109_, lean_object* v_a_110_, lean_object* v_a_111_, lean_object* v_a_112_, lean_object* v_a_113_, lean_object* v_a_114_){
_start:
{
lean_object* v_res_115_; 
v_res_115_ = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_matchPattern_x3f_go_x3f(v_pattern_108_, v_e_109_, v_a_110_, v_a_111_, v_a_112_, v_a_113_);
lean_dec(v_a_113_);
lean_dec_ref(v_a_112_);
lean_dec(v_a_111_);
lean_dec_ref(v_a_110_);
return v_res_115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Conv_matchPattern_x3f_spec__0___redArg(lean_object* v_k_116_, uint8_t v_allowLevelAssignments_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_){
_start:
{
lean_object* v___x_123_; 
v___x_123_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_117_, v_k_116_, v___y_118_, v___y_119_, v___y_120_, v___y_121_);
if (lean_obj_tag(v___x_123_) == 0)
{
lean_object* v_a_124_; lean_object* v___x_126_; uint8_t v_isShared_127_; uint8_t v_isSharedCheck_131_; 
v_a_124_ = lean_ctor_get(v___x_123_, 0);
v_isSharedCheck_131_ = !lean_is_exclusive(v___x_123_);
if (v_isSharedCheck_131_ == 0)
{
v___x_126_ = v___x_123_;
v_isShared_127_ = v_isSharedCheck_131_;
goto v_resetjp_125_;
}
else
{
lean_inc(v_a_124_);
lean_dec(v___x_123_);
v___x_126_ = lean_box(0);
v_isShared_127_ = v_isSharedCheck_131_;
goto v_resetjp_125_;
}
v_resetjp_125_:
{
lean_object* v___x_129_; 
if (v_isShared_127_ == 0)
{
v___x_129_ = v___x_126_;
goto v_reusejp_128_;
}
else
{
lean_object* v_reuseFailAlloc_130_; 
v_reuseFailAlloc_130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_130_, 0, v_a_124_);
v___x_129_ = v_reuseFailAlloc_130_;
goto v_reusejp_128_;
}
v_reusejp_128_:
{
return v___x_129_;
}
}
}
else
{
lean_object* v_a_132_; lean_object* v___x_134_; uint8_t v_isShared_135_; uint8_t v_isSharedCheck_139_; 
v_a_132_ = lean_ctor_get(v___x_123_, 0);
v_isSharedCheck_139_ = !lean_is_exclusive(v___x_123_);
if (v_isSharedCheck_139_ == 0)
{
v___x_134_ = v___x_123_;
v_isShared_135_ = v_isSharedCheck_139_;
goto v_resetjp_133_;
}
else
{
lean_inc(v_a_132_);
lean_dec(v___x_123_);
v___x_134_ = lean_box(0);
v_isShared_135_ = v_isSharedCheck_139_;
goto v_resetjp_133_;
}
v_resetjp_133_:
{
lean_object* v___x_137_; 
if (v_isShared_135_ == 0)
{
v___x_137_ = v___x_134_;
goto v_reusejp_136_;
}
else
{
lean_object* v_reuseFailAlloc_138_; 
v_reuseFailAlloc_138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_138_, 0, v_a_132_);
v___x_137_ = v_reuseFailAlloc_138_;
goto v_reusejp_136_;
}
v_reusejp_136_:
{
return v___x_137_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Conv_matchPattern_x3f_spec__0___redArg___boxed(lean_object* v_k_140_, lean_object* v_allowLevelAssignments_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_147_; lean_object* v_res_148_; 
v_allowLevelAssignments_boxed_147_ = lean_unbox(v_allowLevelAssignments_141_);
v_res_148_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Conv_matchPattern_x3f_spec__0___redArg(v_k_140_, v_allowLevelAssignments_boxed_147_, v___y_142_, v___y_143_, v___y_144_, v___y_145_);
lean_dec(v___y_145_);
lean_dec_ref(v___y_144_);
lean_dec(v___y_143_);
lean_dec_ref(v___y_142_);
return v_res_148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Conv_matchPattern_x3f_spec__0(lean_object* v_00_u03b1_149_, lean_object* v_k_150_, uint8_t v_allowLevelAssignments_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_){
_start:
{
lean_object* v___x_157_; 
v___x_157_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Conv_matchPattern_x3f_spec__0___redArg(v_k_150_, v_allowLevelAssignments_151_, v___y_152_, v___y_153_, v___y_154_, v___y_155_);
return v___x_157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Conv_matchPattern_x3f_spec__0___boxed(lean_object* v_00_u03b1_158_, lean_object* v_k_159_, lean_object* v_allowLevelAssignments_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_166_; lean_object* v_res_167_; 
v_allowLevelAssignments_boxed_166_ = lean_unbox(v_allowLevelAssignments_160_);
v_res_167_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Conv_matchPattern_x3f_spec__0(v_00_u03b1_158_, v_k_159_, v_allowLevelAssignments_boxed_166_, v___y_161_, v___y_162_, v___y_163_, v___y_164_);
lean_dec(v___y_164_);
lean_dec_ref(v___y_163_);
lean_dec(v___y_162_);
lean_dec_ref(v___y_161_);
return v_res_167_;
}
}
static uint64_t _init_l_Lean_Elab_Tactic_Conv_matchPattern_x3f___lam__0___closed__0(void){
_start:
{
uint8_t v___x_168_; uint64_t v___x_169_; 
v___x_168_ = 2;
v___x_169_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_168_);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_matchPattern_x3f___lam__0(lean_object* v_pattern_170_, lean_object* v_e_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_){
_start:
{
lean_object* v___x_177_; 
v___x_177_ = l_Lean_Meta_openAbstractMVarsResult(v_pattern_170_, v___y_172_, v___y_173_, v___y_174_, v___y_175_);
if (lean_obj_tag(v___x_177_) == 0)
{
lean_object* v_a_178_; lean_object* v_snd_179_; lean_object* v_snd_180_; lean_object* v___x_181_; uint8_t v_foApprox_182_; uint8_t v_ctxApprox_183_; uint8_t v_quasiPatternApprox_184_; uint8_t v_constApprox_185_; uint8_t v_isDefEqStuckEx_186_; uint8_t v_unificationHints_187_; uint8_t v_proofIrrelevance_188_; uint8_t v_assignSyntheticOpaque_189_; uint8_t v_offsetCnstrs_190_; uint8_t v_etaStruct_191_; uint8_t v_univApprox_192_; uint8_t v_iota_193_; uint8_t v_beta_194_; uint8_t v_proj_195_; uint8_t v_zeta_196_; uint8_t v_zetaDelta_197_; uint8_t v_zetaUnused_198_; uint8_t v_zetaHave_199_; lean_object* v___x_201_; uint8_t v_isShared_202_; uint8_t v_isSharedCheck_239_; 
v_a_178_ = lean_ctor_get(v___x_177_, 0);
lean_inc(v_a_178_);
lean_dec_ref_known(v___x_177_, 1);
v_snd_179_ = lean_ctor_get(v_a_178_, 1);
lean_inc(v_snd_179_);
lean_dec(v_a_178_);
v_snd_180_ = lean_ctor_get(v_snd_179_, 1);
lean_inc(v_snd_180_);
lean_dec(v_snd_179_);
v___x_181_ = l_Lean_Meta_Context_config(v___y_172_);
v_foApprox_182_ = lean_ctor_get_uint8(v___x_181_, 0);
v_ctxApprox_183_ = lean_ctor_get_uint8(v___x_181_, 1);
v_quasiPatternApprox_184_ = lean_ctor_get_uint8(v___x_181_, 2);
v_constApprox_185_ = lean_ctor_get_uint8(v___x_181_, 3);
v_isDefEqStuckEx_186_ = lean_ctor_get_uint8(v___x_181_, 4);
v_unificationHints_187_ = lean_ctor_get_uint8(v___x_181_, 5);
v_proofIrrelevance_188_ = lean_ctor_get_uint8(v___x_181_, 6);
v_assignSyntheticOpaque_189_ = lean_ctor_get_uint8(v___x_181_, 7);
v_offsetCnstrs_190_ = lean_ctor_get_uint8(v___x_181_, 8);
v_etaStruct_191_ = lean_ctor_get_uint8(v___x_181_, 10);
v_univApprox_192_ = lean_ctor_get_uint8(v___x_181_, 11);
v_iota_193_ = lean_ctor_get_uint8(v___x_181_, 12);
v_beta_194_ = lean_ctor_get_uint8(v___x_181_, 13);
v_proj_195_ = lean_ctor_get_uint8(v___x_181_, 14);
v_zeta_196_ = lean_ctor_get_uint8(v___x_181_, 15);
v_zetaDelta_197_ = lean_ctor_get_uint8(v___x_181_, 16);
v_zetaUnused_198_ = lean_ctor_get_uint8(v___x_181_, 17);
v_zetaHave_199_ = lean_ctor_get_uint8(v___x_181_, 18);
v_isSharedCheck_239_ = !lean_is_exclusive(v___x_181_);
if (v_isSharedCheck_239_ == 0)
{
v___x_201_ = v___x_181_;
v_isShared_202_ = v_isSharedCheck_239_;
goto v_resetjp_200_;
}
else
{
lean_dec(v___x_181_);
v___x_201_ = lean_box(0);
v_isShared_202_ = v_isSharedCheck_239_;
goto v_resetjp_200_;
}
v_resetjp_200_:
{
uint8_t v_trackZetaDelta_203_; lean_object* v_zetaDeltaSet_204_; lean_object* v_lctx_205_; lean_object* v_localInstances_206_; lean_object* v_defEqCtx_x3f_207_; lean_object* v_synthPendingDepth_208_; lean_object* v_canUnfold_x3f_209_; uint8_t v_univApprox_210_; uint8_t v_inTypeClassResolution_211_; uint8_t v_cacheInferType_212_; uint8_t v___x_213_; lean_object* v_config_215_; 
v_trackZetaDelta_203_ = lean_ctor_get_uint8(v___y_172_, sizeof(void*)*7);
v_zetaDeltaSet_204_ = lean_ctor_get(v___y_172_, 1);
lean_inc(v_zetaDeltaSet_204_);
v_lctx_205_ = lean_ctor_get(v___y_172_, 2);
lean_inc_ref(v_lctx_205_);
v_localInstances_206_ = lean_ctor_get(v___y_172_, 3);
lean_inc_ref(v_localInstances_206_);
v_defEqCtx_x3f_207_ = lean_ctor_get(v___y_172_, 4);
lean_inc(v_defEqCtx_x3f_207_);
v_synthPendingDepth_208_ = lean_ctor_get(v___y_172_, 5);
lean_inc(v_synthPendingDepth_208_);
v_canUnfold_x3f_209_ = lean_ctor_get(v___y_172_, 6);
lean_inc(v_canUnfold_x3f_209_);
v_univApprox_210_ = lean_ctor_get_uint8(v___y_172_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_211_ = lean_ctor_get_uint8(v___y_172_, sizeof(void*)*7 + 2);
v_cacheInferType_212_ = lean_ctor_get_uint8(v___y_172_, sizeof(void*)*7 + 3);
v___x_213_ = 2;
if (v_isShared_202_ == 0)
{
v_config_215_ = v___x_201_;
goto v_reusejp_214_;
}
else
{
lean_object* v_reuseFailAlloc_238_; 
v_reuseFailAlloc_238_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_238_, 0, v_foApprox_182_);
lean_ctor_set_uint8(v_reuseFailAlloc_238_, 1, v_ctxApprox_183_);
lean_ctor_set_uint8(v_reuseFailAlloc_238_, 2, v_quasiPatternApprox_184_);
lean_ctor_set_uint8(v_reuseFailAlloc_238_, 3, v_constApprox_185_);
lean_ctor_set_uint8(v_reuseFailAlloc_238_, 4, v_isDefEqStuckEx_186_);
lean_ctor_set_uint8(v_reuseFailAlloc_238_, 5, v_unificationHints_187_);
lean_ctor_set_uint8(v_reuseFailAlloc_238_, 6, v_proofIrrelevance_188_);
lean_ctor_set_uint8(v_reuseFailAlloc_238_, 7, v_assignSyntheticOpaque_189_);
lean_ctor_set_uint8(v_reuseFailAlloc_238_, 8, v_offsetCnstrs_190_);
lean_ctor_set_uint8(v_reuseFailAlloc_238_, 10, v_etaStruct_191_);
lean_ctor_set_uint8(v_reuseFailAlloc_238_, 11, v_univApprox_192_);
lean_ctor_set_uint8(v_reuseFailAlloc_238_, 12, v_iota_193_);
lean_ctor_set_uint8(v_reuseFailAlloc_238_, 13, v_beta_194_);
lean_ctor_set_uint8(v_reuseFailAlloc_238_, 14, v_proj_195_);
lean_ctor_set_uint8(v_reuseFailAlloc_238_, 15, v_zeta_196_);
lean_ctor_set_uint8(v_reuseFailAlloc_238_, 16, v_zetaDelta_197_);
lean_ctor_set_uint8(v_reuseFailAlloc_238_, 17, v_zetaUnused_198_);
lean_ctor_set_uint8(v_reuseFailAlloc_238_, 18, v_zetaHave_199_);
v_config_215_ = v_reuseFailAlloc_238_;
goto v_reusejp_214_;
}
v_reusejp_214_:
{
uint64_t v___x_216_; lean_object* v___x_218_; uint8_t v_isShared_219_; uint8_t v_isSharedCheck_230_; 
lean_ctor_set_uint8(v_config_215_, 9, v___x_213_);
v___x_216_ = l_Lean_Meta_Context_configKey(v___y_172_);
v_isSharedCheck_230_ = !lean_is_exclusive(v___y_172_);
if (v_isSharedCheck_230_ == 0)
{
lean_object* v_unused_231_; lean_object* v_unused_232_; lean_object* v_unused_233_; lean_object* v_unused_234_; lean_object* v_unused_235_; lean_object* v_unused_236_; lean_object* v_unused_237_; 
v_unused_231_ = lean_ctor_get(v___y_172_, 6);
lean_dec(v_unused_231_);
v_unused_232_ = lean_ctor_get(v___y_172_, 5);
lean_dec(v_unused_232_);
v_unused_233_ = lean_ctor_get(v___y_172_, 4);
lean_dec(v_unused_233_);
v_unused_234_ = lean_ctor_get(v___y_172_, 3);
lean_dec(v_unused_234_);
v_unused_235_ = lean_ctor_get(v___y_172_, 2);
lean_dec(v_unused_235_);
v_unused_236_ = lean_ctor_get(v___y_172_, 1);
lean_dec(v_unused_236_);
v_unused_237_ = lean_ctor_get(v___y_172_, 0);
lean_dec(v_unused_237_);
v___x_218_ = v___y_172_;
v_isShared_219_ = v_isSharedCheck_230_;
goto v_resetjp_217_;
}
else
{
lean_dec(v___y_172_);
v___x_218_ = lean_box(0);
v_isShared_219_ = v_isSharedCheck_230_;
goto v_resetjp_217_;
}
v_resetjp_217_:
{
uint64_t v___x_220_; uint64_t v___x_221_; uint64_t v___x_222_; uint64_t v___x_223_; uint64_t v_key_224_; lean_object* v___x_225_; lean_object* v___x_227_; 
v___x_220_ = 3ULL;
v___x_221_ = lean_uint64_shift_right(v___x_216_, v___x_220_);
v___x_222_ = lean_uint64_shift_left(v___x_221_, v___x_220_);
v___x_223_ = lean_uint64_once(&l_Lean_Elab_Tactic_Conv_matchPattern_x3f___lam__0___closed__0, &l_Lean_Elab_Tactic_Conv_matchPattern_x3f___lam__0___closed__0_once, _init_l_Lean_Elab_Tactic_Conv_matchPattern_x3f___lam__0___closed__0);
v_key_224_ = lean_uint64_lor(v___x_222_, v___x_223_);
v___x_225_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_225_, 0, v_config_215_);
lean_ctor_set_uint64(v___x_225_, sizeof(void*)*1, v_key_224_);
if (v_isShared_219_ == 0)
{
lean_ctor_set(v___x_218_, 0, v___x_225_);
v___x_227_ = v___x_218_;
goto v_reusejp_226_;
}
else
{
lean_object* v_reuseFailAlloc_229_; 
v_reuseFailAlloc_229_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_229_, 0, v___x_225_);
lean_ctor_set(v_reuseFailAlloc_229_, 1, v_zetaDeltaSet_204_);
lean_ctor_set(v_reuseFailAlloc_229_, 2, v_lctx_205_);
lean_ctor_set(v_reuseFailAlloc_229_, 3, v_localInstances_206_);
lean_ctor_set(v_reuseFailAlloc_229_, 4, v_defEqCtx_x3f_207_);
lean_ctor_set(v_reuseFailAlloc_229_, 5, v_synthPendingDepth_208_);
lean_ctor_set(v_reuseFailAlloc_229_, 6, v_canUnfold_x3f_209_);
lean_ctor_set_uint8(v_reuseFailAlloc_229_, sizeof(void*)*7, v_trackZetaDelta_203_);
lean_ctor_set_uint8(v_reuseFailAlloc_229_, sizeof(void*)*7 + 1, v_univApprox_210_);
lean_ctor_set_uint8(v_reuseFailAlloc_229_, sizeof(void*)*7 + 2, v_inTypeClassResolution_211_);
lean_ctor_set_uint8(v_reuseFailAlloc_229_, sizeof(void*)*7 + 3, v_cacheInferType_212_);
v___x_227_ = v_reuseFailAlloc_229_;
goto v_reusejp_226_;
}
v_reusejp_226_:
{
lean_object* v___x_228_; 
v___x_228_ = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_matchPattern_x3f_go_x3f(v_snd_180_, v_e_171_, v___x_227_, v___y_173_, v___y_174_, v___y_175_);
lean_dec_ref(v___x_227_);
return v___x_228_;
}
}
}
}
}
else
{
lean_object* v_a_240_; lean_object* v___x_242_; uint8_t v_isShared_243_; uint8_t v_isSharedCheck_247_; 
lean_dec_ref(v___y_172_);
lean_dec_ref(v_e_171_);
v_a_240_ = lean_ctor_get(v___x_177_, 0);
v_isSharedCheck_247_ = !lean_is_exclusive(v___x_177_);
if (v_isSharedCheck_247_ == 0)
{
v___x_242_ = v___x_177_;
v_isShared_243_ = v_isSharedCheck_247_;
goto v_resetjp_241_;
}
else
{
lean_inc(v_a_240_);
lean_dec(v___x_177_);
v___x_242_ = lean_box(0);
v_isShared_243_ = v_isSharedCheck_247_;
goto v_resetjp_241_;
}
v_resetjp_241_:
{
lean_object* v___x_245_; 
if (v_isShared_243_ == 0)
{
v___x_245_ = v___x_242_;
goto v_reusejp_244_;
}
else
{
lean_object* v_reuseFailAlloc_246_; 
v_reuseFailAlloc_246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_246_, 0, v_a_240_);
v___x_245_ = v_reuseFailAlloc_246_;
goto v_reusejp_244_;
}
v_reusejp_244_:
{
return v___x_245_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_matchPattern_x3f___lam__0___boxed(lean_object* v_pattern_248_, lean_object* v_e_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = l_Lean_Elab_Tactic_Conv_matchPattern_x3f___lam__0(v_pattern_248_, v_e_249_, v___y_250_, v___y_251_, v___y_252_, v___y_253_);
lean_dec(v___y_253_);
lean_dec_ref(v___y_252_);
lean_dec(v___y_251_);
return v_res_255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_matchPattern_x3f(lean_object* v_pattern_256_, lean_object* v_e_257_, lean_object* v_a_258_, lean_object* v_a_259_, lean_object* v_a_260_, lean_object* v_a_261_){
_start:
{
lean_object* v___f_263_; uint8_t v___x_264_; lean_object* v___x_265_; 
v___f_263_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_matchPattern_x3f___lam__0___boxed), 7, 2);
lean_closure_set(v___f_263_, 0, v_pattern_256_);
lean_closure_set(v___f_263_, 1, v_e_257_);
v___x_264_ = 0;
v___x_265_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Conv_matchPattern_x3f_spec__0___redArg(v___f_263_, v___x_264_, v_a_258_, v_a_259_, v_a_260_, v_a_261_);
return v___x_265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_matchPattern_x3f___boxed(lean_object* v_pattern_266_, lean_object* v_e_267_, lean_object* v_a_268_, lean_object* v_a_269_, lean_object* v_a_270_, lean_object* v_a_271_, lean_object* v_a_272_){
_start:
{
lean_object* v_res_273_; 
v_res_273_ = l_Lean_Elab_Tactic_Conv_matchPattern_x3f(v_pattern_266_, v_e_267_, v_a_268_, v_a_269_, v_a_270_, v_a_271_);
lean_dec(v_a_271_);
lean_dec_ref(v_a_270_);
lean_dec(v_a_269_);
lean_dec_ref(v_a_268_);
return v_res_273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorIdx(lean_object* v_x_274_){
_start:
{
if (lean_obj_tag(v_x_274_) == 0)
{
lean_object* v___x_275_; 
v___x_275_ = lean_unsigned_to_nat(0u);
return v___x_275_;
}
else
{
lean_object* v___x_276_; 
v___x_276_ = lean_unsigned_to_nat(1u);
return v___x_276_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorIdx___boxed(lean_object* v_x_277_){
_start:
{
lean_object* v_res_278_; 
v_res_278_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorIdx(v_x_277_);
lean_dec_ref(v_x_277_);
return v_res_278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorElim___redArg(lean_object* v_t_279_, lean_object* v_k_280_){
_start:
{
if (lean_obj_tag(v_t_279_) == 0)
{
lean_object* v_subgoals_281_; lean_object* v___x_282_; 
v_subgoals_281_ = lean_ctor_get(v_t_279_, 0);
lean_inc_ref(v_subgoals_281_);
lean_dec_ref_known(v_t_279_, 1);
v___x_282_ = lean_apply_1(v_k_280_, v_subgoals_281_);
return v___x_282_;
}
else
{
lean_object* v_subgoals_283_; lean_object* v_idx_284_; lean_object* v_remaining_285_; lean_object* v___x_286_; 
v_subgoals_283_ = lean_ctor_get(v_t_279_, 0);
lean_inc_ref(v_subgoals_283_);
v_idx_284_ = lean_ctor_get(v_t_279_, 1);
lean_inc(v_idx_284_);
v_remaining_285_ = lean_ctor_get(v_t_279_, 2);
lean_inc(v_remaining_285_);
lean_dec_ref_known(v_t_279_, 3);
v___x_286_ = lean_apply_3(v_k_280_, v_subgoals_283_, v_idx_284_, v_remaining_285_);
return v___x_286_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorElim(lean_object* v_motive_287_, lean_object* v_ctorIdx_288_, lean_object* v_t_289_, lean_object* v_h_290_, lean_object* v_k_291_){
_start:
{
lean_object* v___x_292_; 
v___x_292_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorElim___redArg(v_t_289_, v_k_291_);
return v___x_292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorElim___boxed(lean_object* v_motive_293_, lean_object* v_ctorIdx_294_, lean_object* v_t_295_, lean_object* v_h_296_, lean_object* v_k_297_){
_start:
{
lean_object* v_res_298_; 
v_res_298_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorElim(v_motive_293_, v_ctorIdx_294_, v_t_295_, v_h_296_, v_k_297_);
lean_dec(v_ctorIdx_294_);
return v_res_298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_all_elim___redArg(lean_object* v_t_299_, lean_object* v_all_300_){
_start:
{
lean_object* v___x_301_; 
v___x_301_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorElim___redArg(v_t_299_, v_all_300_);
return v___x_301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_all_elim(lean_object* v_motive_302_, lean_object* v_t_303_, lean_object* v_h_304_, lean_object* v_all_305_){
_start:
{
lean_object* v___x_306_; 
v___x_306_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorElim___redArg(v_t_303_, v_all_305_);
return v___x_306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_occs_elim___redArg(lean_object* v_t_307_, lean_object* v_occs_308_){
_start:
{
lean_object* v___x_309_; 
v___x_309_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorElim___redArg(v_t_307_, v_occs_308_);
return v___x_309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_occs_elim(lean_object* v_motive_310_, lean_object* v_t_311_, lean_object* v_h_312_, lean_object* v_occs_313_){
_start:
{
lean_object* v___x_314_; 
v___x_314_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorElim___redArg(v_t_311_, v_occs_313_);
return v___x_314_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Conv_PatternMatchState_isDone(lean_object* v_x_315_){
_start:
{
if (lean_obj_tag(v_x_315_) == 0)
{
uint8_t v___x_316_; 
v___x_316_ = 0;
return v___x_316_;
}
else
{
lean_object* v_remaining_317_; uint8_t v___x_318_; 
v_remaining_317_ = lean_ctor_get(v_x_315_, 2);
v___x_318_ = l_List_isEmpty___redArg(v_remaining_317_);
return v___x_318_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_isDone___boxed(lean_object* v_x_319_){
_start:
{
uint8_t v_res_320_; lean_object* v_r_321_; 
v_res_320_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_isDone(v_x_319_);
lean_dec_ref(v_x_319_);
v_r_321_ = lean_box(v_res_320_);
return v_r_321_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Conv_PatternMatchState_isReady(lean_object* v_x_322_){
_start:
{
if (lean_obj_tag(v_x_322_) == 0)
{
uint8_t v___x_323_; 
v___x_323_ = 1;
return v___x_323_;
}
else
{
lean_object* v_remaining_324_; 
v_remaining_324_ = lean_ctor_get(v_x_322_, 2);
if (lean_obj_tag(v_remaining_324_) == 1)
{
lean_object* v_head_325_; lean_object* v_idx_326_; lean_object* v_fst_327_; uint8_t v___x_328_; 
v_head_325_ = lean_ctor_get(v_remaining_324_, 0);
v_idx_326_ = lean_ctor_get(v_x_322_, 1);
v_fst_327_ = lean_ctor_get(v_head_325_, 0);
v___x_328_ = lean_nat_dec_eq(v_idx_326_, v_fst_327_);
return v___x_328_;
}
else
{
uint8_t v___x_329_; 
v___x_329_ = 0;
return v___x_329_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_isReady___boxed(lean_object* v_x_330_){
_start:
{
uint8_t v_res_331_; lean_object* v_r_332_; 
v_res_331_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_isReady(v_x_330_);
lean_dec_ref(v_x_330_);
v_r_332_ = lean_box(v_res_331_);
return v_r_332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_skip(lean_object* v_x_333_){
_start:
{
if (lean_obj_tag(v_x_333_) == 1)
{
lean_object* v_subgoals_334_; lean_object* v_idx_335_; lean_object* v_remaining_336_; lean_object* v___x_338_; uint8_t v_isShared_339_; uint8_t v_isSharedCheck_345_; 
v_subgoals_334_ = lean_ctor_get(v_x_333_, 0);
v_idx_335_ = lean_ctor_get(v_x_333_, 1);
v_remaining_336_ = lean_ctor_get(v_x_333_, 2);
v_isSharedCheck_345_ = !lean_is_exclusive(v_x_333_);
if (v_isSharedCheck_345_ == 0)
{
v___x_338_ = v_x_333_;
v_isShared_339_ = v_isSharedCheck_345_;
goto v_resetjp_337_;
}
else
{
lean_inc(v_remaining_336_);
lean_inc(v_idx_335_);
lean_inc(v_subgoals_334_);
lean_dec(v_x_333_);
v___x_338_ = lean_box(0);
v_isShared_339_ = v_isSharedCheck_345_;
goto v_resetjp_337_;
}
v_resetjp_337_:
{
lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_343_; 
v___x_340_ = lean_unsigned_to_nat(1u);
v___x_341_ = lean_nat_add(v_idx_335_, v___x_340_);
lean_dec(v_idx_335_);
if (v_isShared_339_ == 0)
{
lean_ctor_set(v___x_338_, 1, v___x_341_);
v___x_343_ = v___x_338_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_344_; 
v_reuseFailAlloc_344_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_344_, 0, v_subgoals_334_);
lean_ctor_set(v_reuseFailAlloc_344_, 1, v___x_341_);
lean_ctor_set(v_reuseFailAlloc_344_, 2, v_remaining_336_);
v___x_343_ = v_reuseFailAlloc_344_;
goto v_reusejp_342_;
}
v_reusejp_342_:
{
return v___x_343_;
}
}
}
else
{
return v_x_333_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_accept(lean_object* v_mvarId_346_, lean_object* v_x_347_){
_start:
{
if (lean_obj_tag(v_x_347_) == 0)
{
lean_object* v_subgoals_348_; lean_object* v___x_350_; uint8_t v_isShared_351_; uint8_t v_isSharedCheck_356_; 
v_subgoals_348_ = lean_ctor_get(v_x_347_, 0);
v_isSharedCheck_356_ = !lean_is_exclusive(v_x_347_);
if (v_isSharedCheck_356_ == 0)
{
v___x_350_ = v_x_347_;
v_isShared_351_ = v_isSharedCheck_356_;
goto v_resetjp_349_;
}
else
{
lean_inc(v_subgoals_348_);
lean_dec(v_x_347_);
v___x_350_ = lean_box(0);
v_isShared_351_ = v_isSharedCheck_356_;
goto v_resetjp_349_;
}
v_resetjp_349_:
{
lean_object* v___x_352_; lean_object* v___x_354_; 
v___x_352_ = lean_array_push(v_subgoals_348_, v_mvarId_346_);
if (v_isShared_351_ == 0)
{
lean_ctor_set(v___x_350_, 0, v___x_352_);
v___x_354_ = v___x_350_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v___x_352_);
v___x_354_ = v_reuseFailAlloc_355_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
return v___x_354_;
}
}
}
else
{
lean_object* v_remaining_357_; 
v_remaining_357_ = lean_ctor_get(v_x_347_, 2);
if (lean_obj_tag(v_remaining_357_) == 1)
{
lean_object* v_head_358_; lean_object* v_subgoals_359_; lean_object* v_idx_360_; lean_object* v___x_362_; uint8_t v_isShared_363_; uint8_t v_isSharedCheck_380_; 
lean_inc_ref(v_remaining_357_);
v_head_358_ = lean_ctor_get(v_remaining_357_, 0);
lean_inc(v_head_358_);
v_subgoals_359_ = lean_ctor_get(v_x_347_, 0);
v_idx_360_ = lean_ctor_get(v_x_347_, 1);
v_isSharedCheck_380_ = !lean_is_exclusive(v_x_347_);
if (v_isSharedCheck_380_ == 0)
{
lean_object* v_unused_381_; 
v_unused_381_ = lean_ctor_get(v_x_347_, 2);
lean_dec(v_unused_381_);
v___x_362_ = v_x_347_;
v_isShared_363_ = v_isSharedCheck_380_;
goto v_resetjp_361_;
}
else
{
lean_inc(v_idx_360_);
lean_inc(v_subgoals_359_);
lean_dec(v_x_347_);
v___x_362_ = lean_box(0);
v_isShared_363_ = v_isSharedCheck_380_;
goto v_resetjp_361_;
}
v_resetjp_361_:
{
lean_object* v_tail_364_; lean_object* v_snd_365_; lean_object* v___x_367_; uint8_t v_isShared_368_; uint8_t v_isSharedCheck_378_; 
v_tail_364_ = lean_ctor_get(v_remaining_357_, 1);
lean_inc(v_tail_364_);
lean_dec_ref_known(v_remaining_357_, 2);
v_snd_365_ = lean_ctor_get(v_head_358_, 1);
v_isSharedCheck_378_ = !lean_is_exclusive(v_head_358_);
if (v_isSharedCheck_378_ == 0)
{
lean_object* v_unused_379_; 
v_unused_379_ = lean_ctor_get(v_head_358_, 0);
lean_dec(v_unused_379_);
v___x_367_ = v_head_358_;
v_isShared_368_ = v_isSharedCheck_378_;
goto v_resetjp_366_;
}
else
{
lean_inc(v_snd_365_);
lean_dec(v_head_358_);
v___x_367_ = lean_box(0);
v_isShared_368_ = v_isSharedCheck_378_;
goto v_resetjp_366_;
}
v_resetjp_366_:
{
lean_object* v___x_370_; 
if (v_isShared_368_ == 0)
{
lean_ctor_set(v___x_367_, 1, v_mvarId_346_);
lean_ctor_set(v___x_367_, 0, v_snd_365_);
v___x_370_ = v___x_367_;
goto v_reusejp_369_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v_snd_365_);
lean_ctor_set(v_reuseFailAlloc_377_, 1, v_mvarId_346_);
v___x_370_ = v_reuseFailAlloc_377_;
goto v_reusejp_369_;
}
v_reusejp_369_:
{
lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_375_; 
v___x_371_ = lean_array_push(v_subgoals_359_, v___x_370_);
v___x_372_ = lean_unsigned_to_nat(1u);
v___x_373_ = lean_nat_add(v_idx_360_, v___x_372_);
lean_dec(v_idx_360_);
if (v_isShared_363_ == 0)
{
lean_ctor_set(v___x_362_, 2, v_tail_364_);
lean_ctor_set(v___x_362_, 1, v___x_373_);
lean_ctor_set(v___x_362_, 0, v___x_371_);
v___x_375_ = v___x_362_;
goto v_reusejp_374_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v___x_371_);
lean_ctor_set(v_reuseFailAlloc_376_, 1, v___x_373_);
lean_ctor_set(v_reuseFailAlloc_376_, 2, v_tail_364_);
v___x_375_ = v_reuseFailAlloc_376_;
goto v_reusejp_374_;
}
v_reusejp_374_:
{
return v___x_375_;
}
}
}
}
}
else
{
lean_dec(v_mvarId_346_);
return v_x_347_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre_spec__0___redArg(lean_object* v_as_382_, size_t v_sz_383_, size_t v_i_384_, lean_object* v_b_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_){
_start:
{
uint8_t v___x_391_; 
v___x_391_ = lean_usize_dec_lt(v_i_384_, v_sz_383_);
if (v___x_391_ == 0)
{
lean_object* v___x_392_; 
v___x_392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_392_, 0, v_b_385_);
return v___x_392_;
}
else
{
lean_object* v_a_393_; lean_object* v___x_394_; 
v_a_393_ = lean_array_uget_borrowed(v_as_382_, v_i_384_);
lean_inc(v_a_393_);
v___x_394_ = l_Lean_Meta_mkCongrFun(v_b_385_, v_a_393_, v___y_386_, v___y_387_, v___y_388_, v___y_389_);
if (lean_obj_tag(v___x_394_) == 0)
{
lean_object* v_a_395_; size_t v___x_396_; size_t v___x_397_; 
v_a_395_ = lean_ctor_get(v___x_394_, 0);
lean_inc(v_a_395_);
lean_dec_ref_known(v___x_394_, 1);
v___x_396_ = ((size_t)1ULL);
v___x_397_ = lean_usize_add(v_i_384_, v___x_396_);
v_i_384_ = v___x_397_;
v_b_385_ = v_a_395_;
goto _start;
}
else
{
return v___x_394_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre_spec__0___redArg___boxed(lean_object* v_as_399_, lean_object* v_sz_400_, lean_object* v_i_401_, lean_object* v_b_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_){
_start:
{
size_t v_sz_boxed_408_; size_t v_i_boxed_409_; lean_object* v_res_410_; 
v_sz_boxed_408_ = lean_unbox_usize(v_sz_400_);
lean_dec(v_sz_400_);
v_i_boxed_409_ = lean_unbox_usize(v_i_401_);
lean_dec(v_i_401_);
v_res_410_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre_spec__0___redArg(v_as_399_, v_sz_boxed_408_, v_i_boxed_409_, v_b_402_, v___y_403_, v___y_404_, v___y_405_, v___y_406_);
lean_dec(v___y_406_);
lean_dec_ref(v___y_405_);
lean_dec(v___y_404_);
lean_dec_ref(v___y_403_);
lean_dec_ref(v_as_399_);
return v_res_410_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre(lean_object* v_pattern_413_, lean_object* v_state_414_, lean_object* v_e_415_, lean_object* v_a_416_, lean_object* v_a_417_, lean_object* v_a_418_, lean_object* v_a_419_, lean_object* v_a_420_, lean_object* v_a_421_, lean_object* v_a_422_){
_start:
{
lean_object* v___x_424_; uint8_t v___x_425_; uint8_t v___x_426_; 
v___x_424_ = lean_st_ref_get(v_state_414_);
v___x_425_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_isDone(v___x_424_);
lean_dec(v___x_424_);
v___x_426_ = 1;
if (v___x_425_ == 0)
{
lean_object* v___x_427_; 
v___x_427_ = l_Lean_Elab_Tactic_Conv_matchPattern_x3f(v_pattern_413_, v_e_415_, v_a_419_, v_a_420_, v_a_421_, v_a_422_);
if (lean_obj_tag(v___x_427_) == 0)
{
lean_object* v_a_428_; lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_494_; 
v_a_428_ = lean_ctor_get(v___x_427_, 0);
v_isSharedCheck_494_ = !lean_is_exclusive(v___x_427_);
if (v_isSharedCheck_494_ == 0)
{
v___x_430_ = v___x_427_;
v_isShared_431_ = v_isSharedCheck_494_;
goto v_resetjp_429_;
}
else
{
lean_inc(v_a_428_);
lean_dec(v___x_427_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_494_;
goto v_resetjp_429_;
}
v_resetjp_429_:
{
if (lean_obj_tag(v_a_428_) == 1)
{
lean_object* v_val_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_489_; 
v_val_432_ = lean_ctor_get(v_a_428_, 0);
v_isSharedCheck_489_ = !lean_is_exclusive(v_a_428_);
if (v_isSharedCheck_489_ == 0)
{
v___x_434_ = v_a_428_;
v_isShared_435_ = v_isSharedCheck_489_;
goto v_resetjp_433_;
}
else
{
lean_inc(v_val_432_);
lean_dec(v_a_428_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_489_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
lean_object* v_fst_436_; lean_object* v_snd_437_; lean_object* v___x_438_; uint8_t v___x_439_; 
v_fst_436_ = lean_ctor_get(v_val_432_, 0);
lean_inc(v_fst_436_);
v_snd_437_ = lean_ctor_get(v_val_432_, 1);
lean_inc(v_snd_437_);
lean_dec(v_val_432_);
v___x_438_ = lean_st_ref_get(v_state_414_);
v___x_439_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_isReady(v___x_438_);
lean_dec(v___x_438_);
if (v___x_439_ == 0)
{
lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_445_; 
lean_dec(v_snd_437_);
lean_dec(v_fst_436_);
lean_del_object(v___x_434_);
v___x_440_ = lean_st_ref_take(v_state_414_);
v___x_441_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_skip(v___x_440_);
v___x_442_ = lean_st_ref_set(v_state_414_, v___x_441_);
v___x_443_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre___closed__0));
if (v_isShared_431_ == 0)
{
lean_ctor_set(v___x_430_, 0, v___x_443_);
v___x_445_ = v___x_430_;
goto v_reusejp_444_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v___x_443_);
v___x_445_ = v_reuseFailAlloc_446_;
goto v_reusejp_444_;
}
v_reusejp_444_:
{
return v___x_445_;
}
}
else
{
lean_object* v___x_447_; lean_object* v___x_448_; 
lean_del_object(v___x_430_);
v___x_447_ = lean_box(0);
v___x_448_ = l_Lean_Elab_Tactic_Conv_mkConvGoalFor(v_fst_436_, v___x_447_, v_a_419_, v_a_420_, v_a_421_, v_a_422_);
if (lean_obj_tag(v___x_448_) == 0)
{
lean_object* v_a_449_; lean_object* v_fst_450_; lean_object* v_snd_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; size_t v_sz_456_; size_t v___x_457_; lean_object* v___x_458_; 
v_a_449_ = lean_ctor_get(v___x_448_, 0);
lean_inc(v_a_449_);
lean_dec_ref_known(v___x_448_, 1);
v_fst_450_ = lean_ctor_get(v_a_449_, 0);
lean_inc(v_fst_450_);
v_snd_451_ = lean_ctor_get(v_a_449_, 1);
lean_inc(v_snd_451_);
lean_dec(v_a_449_);
v___x_452_ = lean_st_ref_take(v_state_414_);
v___x_453_ = l_Lean_Expr_mvarId_x21(v_snd_451_);
v___x_454_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_accept(v___x_453_, v___x_452_);
v___x_455_ = lean_st_ref_set(v_state_414_, v___x_454_);
v_sz_456_ = lean_array_size(v_snd_437_);
v___x_457_ = ((size_t)0ULL);
v___x_458_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre_spec__0___redArg(v_snd_437_, v_sz_456_, v___x_457_, v_snd_451_, v_a_419_, v_a_420_, v_a_421_, v_a_422_);
if (lean_obj_tag(v___x_458_) == 0)
{
lean_object* v_a_459_; lean_object* v___x_461_; uint8_t v_isShared_462_; uint8_t v_isSharedCheck_472_; 
v_a_459_ = lean_ctor_get(v___x_458_, 0);
v_isSharedCheck_472_ = !lean_is_exclusive(v___x_458_);
if (v_isSharedCheck_472_ == 0)
{
v___x_461_ = v___x_458_;
v_isShared_462_ = v_isSharedCheck_472_;
goto v_resetjp_460_;
}
else
{
lean_inc(v_a_459_);
lean_dec(v___x_458_);
v___x_461_ = lean_box(0);
v_isShared_462_ = v_isSharedCheck_472_;
goto v_resetjp_460_;
}
v_resetjp_460_:
{
lean_object* v___x_463_; lean_object* v___x_465_; 
v___x_463_ = l_Lean_mkAppN(v_fst_450_, v_snd_437_);
lean_dec(v_snd_437_);
if (v_isShared_435_ == 0)
{
lean_ctor_set(v___x_434_, 0, v_a_459_);
v___x_465_ = v___x_434_;
goto v_reusejp_464_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v_a_459_);
v___x_465_ = v_reuseFailAlloc_471_;
goto v_reusejp_464_;
}
v_reusejp_464_:
{
lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_469_; 
v___x_466_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_466_, 0, v___x_463_);
lean_ctor_set(v___x_466_, 1, v___x_465_);
lean_ctor_set_uint8(v___x_466_, sizeof(void*)*2, v___x_426_);
v___x_467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_467_, 0, v___x_466_);
if (v_isShared_462_ == 0)
{
lean_ctor_set(v___x_461_, 0, v___x_467_);
v___x_469_ = v___x_461_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v___x_467_);
v___x_469_ = v_reuseFailAlloc_470_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
return v___x_469_;
}
}
}
}
else
{
lean_object* v_a_473_; lean_object* v___x_475_; uint8_t v_isShared_476_; uint8_t v_isSharedCheck_480_; 
lean_dec(v_fst_450_);
lean_dec(v_snd_437_);
lean_del_object(v___x_434_);
v_a_473_ = lean_ctor_get(v___x_458_, 0);
v_isSharedCheck_480_ = !lean_is_exclusive(v___x_458_);
if (v_isSharedCheck_480_ == 0)
{
v___x_475_ = v___x_458_;
v_isShared_476_ = v_isSharedCheck_480_;
goto v_resetjp_474_;
}
else
{
lean_inc(v_a_473_);
lean_dec(v___x_458_);
v___x_475_ = lean_box(0);
v_isShared_476_ = v_isSharedCheck_480_;
goto v_resetjp_474_;
}
v_resetjp_474_:
{
lean_object* v___x_478_; 
if (v_isShared_476_ == 0)
{
v___x_478_ = v___x_475_;
goto v_reusejp_477_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v_a_473_);
v___x_478_ = v_reuseFailAlloc_479_;
goto v_reusejp_477_;
}
v_reusejp_477_:
{
return v___x_478_;
}
}
}
}
else
{
lean_object* v_a_481_; lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_488_; 
lean_dec(v_snd_437_);
lean_del_object(v___x_434_);
v_a_481_ = lean_ctor_get(v___x_448_, 0);
v_isSharedCheck_488_ = !lean_is_exclusive(v___x_448_);
if (v_isSharedCheck_488_ == 0)
{
v___x_483_ = v___x_448_;
v_isShared_484_ = v_isSharedCheck_488_;
goto v_resetjp_482_;
}
else
{
lean_inc(v_a_481_);
lean_dec(v___x_448_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_488_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
lean_object* v___x_486_; 
if (v_isShared_484_ == 0)
{
v___x_486_ = v___x_483_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_487_; 
v_reuseFailAlloc_487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_487_, 0, v_a_481_);
v___x_486_ = v_reuseFailAlloc_487_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
return v___x_486_;
}
}
}
}
}
}
else
{
lean_object* v___x_490_; lean_object* v___x_492_; 
lean_dec(v_a_428_);
v___x_490_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre___closed__0));
if (v_isShared_431_ == 0)
{
lean_ctor_set(v___x_430_, 0, v___x_490_);
v___x_492_ = v___x_430_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v___x_490_);
v___x_492_ = v_reuseFailAlloc_493_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
return v___x_492_;
}
}
}
}
else
{
lean_object* v_a_495_; lean_object* v___x_497_; uint8_t v_isShared_498_; uint8_t v_isSharedCheck_502_; 
v_a_495_ = lean_ctor_get(v___x_427_, 0);
v_isSharedCheck_502_ = !lean_is_exclusive(v___x_427_);
if (v_isSharedCheck_502_ == 0)
{
v___x_497_ = v___x_427_;
v_isShared_498_ = v_isSharedCheck_502_;
goto v_resetjp_496_;
}
else
{
lean_inc(v_a_495_);
lean_dec(v___x_427_);
v___x_497_ = lean_box(0);
v_isShared_498_ = v_isSharedCheck_502_;
goto v_resetjp_496_;
}
v_resetjp_496_:
{
lean_object* v___x_500_; 
if (v_isShared_498_ == 0)
{
v___x_500_ = v___x_497_;
goto v_reusejp_499_;
}
else
{
lean_object* v_reuseFailAlloc_501_; 
v_reuseFailAlloc_501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_501_, 0, v_a_495_);
v___x_500_ = v_reuseFailAlloc_501_;
goto v_reusejp_499_;
}
v_reusejp_499_:
{
return v___x_500_;
}
}
}
}
else
{
lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; 
lean_dec_ref(v_pattern_413_);
v___x_503_ = lean_box(0);
v___x_504_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_504_, 0, v_e_415_);
lean_ctor_set(v___x_504_, 1, v___x_503_);
lean_ctor_set_uint8(v___x_504_, sizeof(void*)*2, v___x_426_);
v___x_505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_505_, 0, v___x_504_);
v___x_506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_506_, 0, v___x_505_);
return v___x_506_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre___boxed(lean_object* v_pattern_507_, lean_object* v_state_508_, lean_object* v_e_509_, lean_object* v_a_510_, lean_object* v_a_511_, lean_object* v_a_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v_a_517_){
_start:
{
lean_object* v_res_518_; 
v_res_518_ = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre(v_pattern_507_, v_state_508_, v_e_509_, v_a_510_, v_a_511_, v_a_512_, v_a_513_, v_a_514_, v_a_515_, v_a_516_);
lean_dec(v_a_516_);
lean_dec_ref(v_a_515_);
lean_dec(v_a_514_);
lean_dec_ref(v_a_513_);
lean_dec(v_a_512_);
lean_dec_ref(v_a_511_);
lean_dec(v_a_510_);
lean_dec(v_state_508_);
return v_res_518_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre_spec__0(lean_object* v_as_519_, size_t v_sz_520_, size_t v_i_521_, lean_object* v_b_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_){
_start:
{
lean_object* v___x_531_; 
v___x_531_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre_spec__0___redArg(v_as_519_, v_sz_520_, v_i_521_, v_b_522_, v___y_526_, v___y_527_, v___y_528_, v___y_529_);
return v___x_531_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre_spec__0___boxed(lean_object* v_as_532_, lean_object* v_sz_533_, lean_object* v_i_534_, lean_object* v_b_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_){
_start:
{
size_t v_sz_boxed_544_; size_t v_i_boxed_545_; lean_object* v_res_546_; 
v_sz_boxed_544_ = lean_unbox_usize(v_sz_533_);
lean_dec(v_sz_533_);
v_i_boxed_545_ = lean_unbox_usize(v_i_534_);
lean_dec(v_i_534_);
v_res_546_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre_spec__0(v_as_532_, v_sz_boxed_544_, v_i_boxed_545_, v_b_535_, v___y_536_, v___y_537_, v___y_538_, v___y_539_, v___y_540_, v___y_541_, v___y_542_);
lean_dec(v___y_542_);
lean_dec_ref(v___y_541_);
lean_dec(v___y_540_);
lean_dec_ref(v___y_539_);
lean_dec(v___y_538_);
lean_dec_ref(v___y_537_);
lean_dec(v___y_536_);
lean_dec_ref(v_as_532_);
return v_res_546_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; 
v___x_547_ = lean_box(0);
v___x_548_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_549_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_549_, 0, v___x_548_);
lean_ctor_set(v___x_549_, 1, v___x_547_);
return v___x_549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg(){
_start:
{
lean_object* v___x_551_; lean_object* v___x_552_; 
v___x_551_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg___closed__0);
v___x_552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_552_, 0, v___x_551_);
return v___x_552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg___boxed(lean_object* v___y_553_){
_start:
{
lean_object* v_res_554_; 
v_res_554_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg();
return v_res_554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0(lean_object* v_00_u03b1_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_){
_start:
{
lean_object* v___x_565_; 
v___x_565_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg();
return v___x_565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___boxed(lean_object* v_00_u03b1_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_){
_start:
{
lean_object* v_res_576_; 
v_res_576_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0(v_00_u03b1_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_, v___y_574_);
lean_dec(v___y_574_);
lean_dec_ref(v___y_573_);
lean_dec(v___y_572_);
lean_dec_ref(v___y_571_);
lean_dec(v___y_570_);
lean_dec_ref(v___y_569_);
lean_dec(v___y_568_);
lean_dec_ref(v___y_567_);
return v_res_576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__2___redArg(lean_object* v_a_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_){
_start:
{
lean_object* v___x_585_; 
v___x_585_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v_a_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_, v___y_582_, v___y_583_);
return v___x_585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__2___redArg___boxed(lean_object* v_a_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_){
_start:
{
lean_object* v_res_594_; 
v_res_594_ = l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__2___redArg(v_a_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_);
lean_dec(v___y_592_);
lean_dec_ref(v___y_591_);
lean_dec(v___y_590_);
lean_dec_ref(v___y_589_);
lean_dec(v___y_588_);
lean_dec_ref(v___y_587_);
return v_res_594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__2(lean_object* v_00_u03b1_595_, lean_object* v_a_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_){
_start:
{
lean_object* v___x_604_; 
v___x_604_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v_a_596_, v___y_597_, v___y_598_, v___y_599_, v___y_600_, v___y_601_, v___y_602_);
return v___x_604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__2___boxed(lean_object* v_00_u03b1_605_, lean_object* v_a_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_){
_start:
{
lean_object* v_res_614_; 
v_res_614_ = l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__2(v_00_u03b1_605_, v_a_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_);
lean_dec(v___y_612_);
lean_dec_ref(v___y_611_);
lean_dec(v___y_610_);
lean_dec_ref(v___y_609_);
lean_dec(v___y_608_);
lean_dec_ref(v___y_607_);
return v_res_614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__0(lean_object* v_e_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_){
_start:
{
lean_object* v___x_624_; lean_object* v___x_625_; 
v___x_624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_624_, 0, v_e_615_);
v___x_625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_625_, 0, v___x_624_);
return v___x_625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__0___boxed(lean_object* v_e_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_){
_start:
{
lean_object* v_res_635_; 
v_res_635_ = l_Lean_Elab_Tactic_Conv_evalPattern___lam__0(v_e_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_);
lean_dec(v___y_633_);
lean_dec_ref(v___y_632_);
lean_dec(v___y_631_);
lean_dec_ref(v___y_630_);
lean_dec(v___y_629_);
lean_dec_ref(v___y_628_);
lean_dec(v___y_627_);
return v_res_635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__1(lean_object* v___x_636_, lean_object* v___x_637_, uint8_t v___x_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_){
_start:
{
lean_object* v___x_646_; 
v___x_646_ = l_Lean_Elab_Term_elabTerm(v___x_636_, v___x_637_, v___x_638_, v___x_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_, v___y_643_, v___y_644_);
if (lean_obj_tag(v___x_646_) == 0)
{
lean_object* v_a_647_; lean_object* v___x_648_; 
v_a_647_ = lean_ctor_get(v___x_646_, 0);
lean_inc(v_a_647_);
lean_dec_ref_known(v___x_646_, 1);
v___x_648_ = l_Lean_Meta_abstractMVars(v_a_647_, v___x_638_, v___y_641_, v___y_642_, v___y_643_, v___y_644_);
return v___x_648_;
}
else
{
lean_object* v_a_649_; lean_object* v___x_651_; uint8_t v_isShared_652_; uint8_t v_isSharedCheck_656_; 
v_a_649_ = lean_ctor_get(v___x_646_, 0);
v_isSharedCheck_656_ = !lean_is_exclusive(v___x_646_);
if (v_isSharedCheck_656_ == 0)
{
v___x_651_ = v___x_646_;
v_isShared_652_ = v_isSharedCheck_656_;
goto v_resetjp_650_;
}
else
{
lean_inc(v_a_649_);
lean_dec(v___x_646_);
v___x_651_ = lean_box(0);
v_isShared_652_ = v_isSharedCheck_656_;
goto v_resetjp_650_;
}
v_resetjp_650_:
{
lean_object* v___x_654_; 
if (v_isShared_652_ == 0)
{
v___x_654_ = v___x_651_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_655_; 
v_reuseFailAlloc_655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_655_, 0, v_a_649_);
v___x_654_ = v_reuseFailAlloc_655_;
goto v_reusejp_653_;
}
v_reusejp_653_:
{
return v___x_654_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__1___boxed(lean_object* v___x_657_, lean_object* v___x_658_, lean_object* v___x_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_){
_start:
{
uint8_t v___x_18448__boxed_667_; lean_object* v_res_668_; 
v___x_18448__boxed_667_ = lean_unbox(v___x_659_);
v_res_668_ = l_Lean_Elab_Tactic_Conv_evalPattern___lam__1(v___x_657_, v___x_658_, v___x_18448__boxed_667_, v___y_660_, v___y_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_);
lean_dec(v___y_665_);
lean_dec_ref(v___y_664_);
lean_dec(v___y_663_);
lean_dec_ref(v___y_662_);
lean_dec(v___y_661_);
lean_dec_ref(v___y_660_);
return v_res_668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__2(lean_object* v___x_669_, lean_object* v___f_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_){
_start:
{
lean_object* v_fileName_678_; lean_object* v_fileMap_679_; lean_object* v_options_680_; lean_object* v_currRecDepth_681_; lean_object* v_maxRecDepth_682_; lean_object* v_ref_683_; lean_object* v_currNamespace_684_; lean_object* v_openDecls_685_; lean_object* v_initHeartbeats_686_; lean_object* v_maxHeartbeats_687_; lean_object* v_quotContext_688_; lean_object* v_currMacroScope_689_; uint8_t v_diag_690_; lean_object* v_cancelTk_x3f_691_; uint8_t v_suppressElabErrors_692_; lean_object* v_inheritedTraceOptions_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_702_; 
v_fileName_678_ = lean_ctor_get(v___y_675_, 0);
v_fileMap_679_ = lean_ctor_get(v___y_675_, 1);
v_options_680_ = lean_ctor_get(v___y_675_, 2);
v_currRecDepth_681_ = lean_ctor_get(v___y_675_, 3);
v_maxRecDepth_682_ = lean_ctor_get(v___y_675_, 4);
v_ref_683_ = lean_ctor_get(v___y_675_, 5);
v_currNamespace_684_ = lean_ctor_get(v___y_675_, 6);
v_openDecls_685_ = lean_ctor_get(v___y_675_, 7);
v_initHeartbeats_686_ = lean_ctor_get(v___y_675_, 8);
v_maxHeartbeats_687_ = lean_ctor_get(v___y_675_, 9);
v_quotContext_688_ = lean_ctor_get(v___y_675_, 10);
v_currMacroScope_689_ = lean_ctor_get(v___y_675_, 11);
v_diag_690_ = lean_ctor_get_uint8(v___y_675_, sizeof(void*)*14);
v_cancelTk_x3f_691_ = lean_ctor_get(v___y_675_, 12);
v_suppressElabErrors_692_ = lean_ctor_get_uint8(v___y_675_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_693_ = lean_ctor_get(v___y_675_, 13);
v_isSharedCheck_702_ = !lean_is_exclusive(v___y_675_);
if (v_isSharedCheck_702_ == 0)
{
v___x_695_ = v___y_675_;
v_isShared_696_ = v_isSharedCheck_702_;
goto v_resetjp_694_;
}
else
{
lean_inc(v_inheritedTraceOptions_693_);
lean_inc(v_cancelTk_x3f_691_);
lean_inc(v_currMacroScope_689_);
lean_inc(v_quotContext_688_);
lean_inc(v_maxHeartbeats_687_);
lean_inc(v_initHeartbeats_686_);
lean_inc(v_openDecls_685_);
lean_inc(v_currNamespace_684_);
lean_inc(v_ref_683_);
lean_inc(v_maxRecDepth_682_);
lean_inc(v_currRecDepth_681_);
lean_inc(v_options_680_);
lean_inc(v_fileMap_679_);
lean_inc(v_fileName_678_);
lean_dec(v___y_675_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_702_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
lean_object* v_ref_697_; lean_object* v___x_699_; 
v_ref_697_ = l_Lean_replaceRef(v___x_669_, v_ref_683_);
lean_dec(v_ref_683_);
if (v_isShared_696_ == 0)
{
lean_ctor_set(v___x_695_, 5, v_ref_697_);
v___x_699_ = v___x_695_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v_fileName_678_);
lean_ctor_set(v_reuseFailAlloc_701_, 1, v_fileMap_679_);
lean_ctor_set(v_reuseFailAlloc_701_, 2, v_options_680_);
lean_ctor_set(v_reuseFailAlloc_701_, 3, v_currRecDepth_681_);
lean_ctor_set(v_reuseFailAlloc_701_, 4, v_maxRecDepth_682_);
lean_ctor_set(v_reuseFailAlloc_701_, 5, v_ref_697_);
lean_ctor_set(v_reuseFailAlloc_701_, 6, v_currNamespace_684_);
lean_ctor_set(v_reuseFailAlloc_701_, 7, v_openDecls_685_);
lean_ctor_set(v_reuseFailAlloc_701_, 8, v_initHeartbeats_686_);
lean_ctor_set(v_reuseFailAlloc_701_, 9, v_maxHeartbeats_687_);
lean_ctor_set(v_reuseFailAlloc_701_, 10, v_quotContext_688_);
lean_ctor_set(v_reuseFailAlloc_701_, 11, v_currMacroScope_689_);
lean_ctor_set(v_reuseFailAlloc_701_, 12, v_cancelTk_x3f_691_);
lean_ctor_set(v_reuseFailAlloc_701_, 13, v_inheritedTraceOptions_693_);
lean_ctor_set_uint8(v_reuseFailAlloc_701_, sizeof(void*)*14, v_diag_690_);
lean_ctor_set_uint8(v_reuseFailAlloc_701_, sizeof(void*)*14 + 1, v_suppressElabErrors_692_);
v___x_699_ = v_reuseFailAlloc_701_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
lean_object* v___x_700_; 
v___x_700_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v___f_670_, v___y_671_, v___y_672_, v___y_673_, v___y_674_, v___x_699_, v___y_676_);
lean_dec_ref(v___x_699_);
return v___x_700_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__2___boxed(lean_object* v___x_703_, lean_object* v___f_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_){
_start:
{
lean_object* v_res_712_; 
v_res_712_ = l_Lean_Elab_Tactic_Conv_evalPattern___lam__2(v___x_703_, v___f_704_, v___y_705_, v___y_706_, v___y_707_, v___y_708_, v___y_709_, v___y_710_);
lean_dec(v___y_710_);
lean_dec(v___y_708_);
lean_dec_ref(v___y_707_);
lean_dec(v___y_706_);
lean_dec_ref(v___y_705_);
lean_dec(v___x_703_);
return v_res_712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__3(lean_object* v___x_713_, uint8_t v___x_714_, lean_object* v_e_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_){
_start:
{
lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; 
v___x_724_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_724_, 0, v_e_715_);
lean_ctor_set(v___x_724_, 1, v___x_713_);
lean_ctor_set_uint8(v___x_724_, sizeof(void*)*2, v___x_714_);
v___x_725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_725_, 0, v___x_724_);
v___x_726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_726_, 0, v___x_725_);
return v___x_726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__3___boxed(lean_object* v___x_727_, lean_object* v___x_728_, lean_object* v_e_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_){
_start:
{
uint8_t v___x_18542__boxed_738_; lean_object* v_res_739_; 
v___x_18542__boxed_738_ = lean_unbox(v___x_728_);
v_res_739_ = l_Lean_Elab_Tactic_Conv_evalPattern___lam__3(v___x_727_, v___x_18542__boxed_738_, v_e_729_, v___y_730_, v___y_731_, v___y_732_, v___y_733_, v___y_734_, v___y_735_, v___y_736_);
lean_dec(v___y_736_);
lean_dec_ref(v___y_735_);
lean_dec(v___y_734_);
lean_dec_ref(v___y_733_);
lean_dec(v___y_732_);
lean_dec_ref(v___y_731_);
lean_dec(v___y_730_);
return v_res_739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__4(lean_object* v___x_740_, lean_object* v_x_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_){
_start:
{
lean_object* v___x_750_; lean_object* v___x_751_; 
v___x_750_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_750_, 0, v___x_740_);
v___x_751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_751_, 0, v___x_750_);
return v___x_751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__4___boxed(lean_object* v___x_752_, lean_object* v_x_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_){
_start:
{
lean_object* v_res_762_; 
v_res_762_ = l_Lean_Elab_Tactic_Conv_evalPattern___lam__4(v___x_752_, v_x_753_, v___y_754_, v___y_755_, v___y_756_, v___y_757_, v___y_758_, v___y_759_, v___y_760_);
lean_dec(v___y_760_);
lean_dec_ref(v___y_759_);
lean_dec(v___y_758_);
lean_dec_ref(v___y_757_);
lean_dec(v___y_756_);
lean_dec_ref(v___y_755_);
lean_dec(v___y_754_);
lean_dec_ref(v_x_753_);
return v_res_762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__5(lean_object* v___x_763_, lean_object* v_x_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_){
_start:
{
lean_object* v___x_773_; 
v___x_773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_773_, 0, v___x_763_);
return v___x_773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__5___boxed(lean_object* v___x_774_, lean_object* v_x_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_){
_start:
{
lean_object* v_res_784_; 
v_res_784_ = l_Lean_Elab_Tactic_Conv_evalPattern___lam__5(v___x_774_, v_x_775_, v___y_776_, v___y_777_, v___y_778_, v___y_779_, v___y_780_, v___y_781_, v___y_782_);
lean_dec(v___y_782_);
lean_dec_ref(v___y_781_);
lean_dec(v___y_780_);
lean_dec_ref(v___y_779_);
lean_dec(v___y_778_);
lean_dec_ref(v___y_777_);
lean_dec(v___y_776_);
lean_dec_ref(v_x_775_);
return v_res_784_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__5(size_t v_sz_785_, size_t v_i_786_, lean_object* v_bs_787_){
_start:
{
uint8_t v___x_788_; 
v___x_788_ = lean_usize_dec_lt(v_i_786_, v_sz_785_);
if (v___x_788_ == 0)
{
return v_bs_787_;
}
else
{
lean_object* v_v_789_; lean_object* v_snd_790_; lean_object* v___x_791_; lean_object* v_bs_x27_792_; size_t v___x_793_; size_t v___x_794_; lean_object* v___x_795_; 
v_v_789_ = lean_array_uget_borrowed(v_bs_787_, v_i_786_);
v_snd_790_ = lean_ctor_get(v_v_789_, 1);
lean_inc(v_snd_790_);
v___x_791_ = lean_unsigned_to_nat(0u);
v_bs_x27_792_ = lean_array_uset(v_bs_787_, v_i_786_, v___x_791_);
v___x_793_ = ((size_t)1ULL);
v___x_794_ = lean_usize_add(v_i_786_, v___x_793_);
v___x_795_ = lean_array_uset(v_bs_x27_792_, v_i_786_, v_snd_790_);
v_i_786_ = v___x_794_;
v_bs_787_ = v___x_795_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__5___boxed(lean_object* v_sz_797_, lean_object* v_i_798_, lean_object* v_bs_799_){
_start:
{
size_t v_sz_boxed_800_; size_t v_i_boxed_801_; lean_object* v_res_802_; 
v_sz_boxed_800_ = lean_unbox_usize(v_sz_797_);
lean_dec(v_sz_797_);
v_i_boxed_801_ = lean_unbox_usize(v_i_798_);
lean_dec(v_i_798_);
v_res_802_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__5(v_sz_boxed_800_, v_i_boxed_801_, v_bs_799_);
return v_res_802_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6_spec__8___redArg(lean_object* v_hi_803_, lean_object* v_pivot_804_, lean_object* v_as_805_, lean_object* v_i_806_, lean_object* v_k_807_){
_start:
{
uint8_t v___x_808_; 
v___x_808_ = lean_nat_dec_lt(v_k_807_, v_hi_803_);
if (v___x_808_ == 0)
{
lean_object* v___x_809_; lean_object* v___x_810_; 
lean_dec(v_k_807_);
v___x_809_ = lean_array_fswap(v_as_805_, v_i_806_, v_hi_803_);
v___x_810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_810_, 0, v_i_806_);
lean_ctor_set(v___x_810_, 1, v___x_809_);
return v___x_810_;
}
else
{
lean_object* v___x_811_; lean_object* v_fst_812_; lean_object* v_fst_813_; uint8_t v___x_814_; 
v___x_811_ = lean_array_fget_borrowed(v_as_805_, v_k_807_);
v_fst_812_ = lean_ctor_get(v___x_811_, 0);
v_fst_813_ = lean_ctor_get(v_pivot_804_, 0);
v___x_814_ = lean_nat_dec_lt(v_fst_812_, v_fst_813_);
if (v___x_814_ == 0)
{
lean_object* v___x_815_; lean_object* v___x_816_; 
v___x_815_ = lean_unsigned_to_nat(1u);
v___x_816_ = lean_nat_add(v_k_807_, v___x_815_);
lean_dec(v_k_807_);
v_k_807_ = v___x_816_;
goto _start;
}
else
{
lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; 
v___x_818_ = lean_array_fswap(v_as_805_, v_i_806_, v_k_807_);
v___x_819_ = lean_unsigned_to_nat(1u);
v___x_820_ = lean_nat_add(v_i_806_, v___x_819_);
lean_dec(v_i_806_);
v___x_821_ = lean_nat_add(v_k_807_, v___x_819_);
lean_dec(v_k_807_);
v_as_805_ = v___x_818_;
v_i_806_ = v___x_820_;
v_k_807_ = v___x_821_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6_spec__8___redArg___boxed(lean_object* v_hi_823_, lean_object* v_pivot_824_, lean_object* v_as_825_, lean_object* v_i_826_, lean_object* v_k_827_){
_start:
{
lean_object* v_res_828_; 
v_res_828_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6_spec__8___redArg(v_hi_823_, v_pivot_824_, v_as_825_, v_i_826_, v_k_827_);
lean_dec_ref(v_pivot_824_);
lean_dec(v_hi_823_);
return v_res_828_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg___lam__0(lean_object* v_x1_829_, lean_object* v_x2_830_){
_start:
{
lean_object* v_fst_831_; lean_object* v_fst_832_; uint8_t v___x_833_; 
v_fst_831_ = lean_ctor_get(v_x1_829_, 0);
v_fst_832_ = lean_ctor_get(v_x2_830_, 0);
v___x_833_ = lean_nat_dec_lt(v_fst_831_, v_fst_832_);
return v___x_833_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg___lam__0___boxed(lean_object* v_x1_834_, lean_object* v_x2_835_){
_start:
{
uint8_t v_res_836_; lean_object* v_r_837_; 
v_res_836_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg___lam__0(v_x1_834_, v_x2_835_);
lean_dec_ref(v_x2_835_);
lean_dec_ref(v_x1_834_);
v_r_837_ = lean_box(v_res_836_);
return v_r_837_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg(lean_object* v_n_838_, lean_object* v_as_839_, lean_object* v_lo_840_, lean_object* v_hi_841_){
_start:
{
lean_object* v___y_843_; uint8_t v___x_853_; 
v___x_853_ = lean_nat_dec_lt(v_lo_840_, v_hi_841_);
if (v___x_853_ == 0)
{
lean_dec(v_lo_840_);
return v_as_839_;
}
else
{
lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v_mid_856_; lean_object* v___y_858_; lean_object* v___y_864_; lean_object* v___x_869_; lean_object* v___x_870_; uint8_t v___x_871_; 
v___x_854_ = lean_nat_add(v_lo_840_, v_hi_841_);
v___x_855_ = lean_unsigned_to_nat(1u);
v_mid_856_ = lean_nat_shiftr(v___x_854_, v___x_855_);
lean_dec(v___x_854_);
v___x_869_ = lean_array_fget_borrowed(v_as_839_, v_mid_856_);
v___x_870_ = lean_array_fget_borrowed(v_as_839_, v_lo_840_);
v___x_871_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg___lam__0(v___x_869_, v___x_870_);
if (v___x_871_ == 0)
{
v___y_864_ = v_as_839_;
goto v___jp_863_;
}
else
{
lean_object* v___x_872_; 
v___x_872_ = lean_array_fswap(v_as_839_, v_lo_840_, v_mid_856_);
v___y_864_ = v___x_872_;
goto v___jp_863_;
}
v___jp_857_:
{
lean_object* v___x_859_; lean_object* v___x_860_; uint8_t v___x_861_; 
v___x_859_ = lean_array_fget_borrowed(v___y_858_, v_mid_856_);
v___x_860_ = lean_array_fget_borrowed(v___y_858_, v_hi_841_);
v___x_861_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg___lam__0(v___x_859_, v___x_860_);
if (v___x_861_ == 0)
{
lean_dec(v_mid_856_);
v___y_843_ = v___y_858_;
goto v___jp_842_;
}
else
{
lean_object* v___x_862_; 
v___x_862_ = lean_array_fswap(v___y_858_, v_mid_856_, v_hi_841_);
lean_dec(v_mid_856_);
v___y_843_ = v___x_862_;
goto v___jp_842_;
}
}
v___jp_863_:
{
lean_object* v___x_865_; lean_object* v___x_866_; uint8_t v___x_867_; 
v___x_865_ = lean_array_fget_borrowed(v___y_864_, v_hi_841_);
v___x_866_ = lean_array_fget_borrowed(v___y_864_, v_lo_840_);
v___x_867_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg___lam__0(v___x_865_, v___x_866_);
if (v___x_867_ == 0)
{
v___y_858_ = v___y_864_;
goto v___jp_857_;
}
else
{
lean_object* v___x_868_; 
v___x_868_ = lean_array_fswap(v___y_864_, v_lo_840_, v_hi_841_);
v___y_858_ = v___x_868_;
goto v___jp_857_;
}
}
}
v___jp_842_:
{
lean_object* v_pivot_844_; lean_object* v___x_845_; lean_object* v_fst_846_; lean_object* v_snd_847_; uint8_t v___x_848_; 
v_pivot_844_ = lean_array_fget(v___y_843_, v_hi_841_);
lean_inc_n(v_lo_840_, 2);
v___x_845_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6_spec__8___redArg(v_hi_841_, v_pivot_844_, v___y_843_, v_lo_840_, v_lo_840_);
lean_dec(v_pivot_844_);
v_fst_846_ = lean_ctor_get(v___x_845_, 0);
lean_inc(v_fst_846_);
v_snd_847_ = lean_ctor_get(v___x_845_, 1);
lean_inc(v_snd_847_);
lean_dec_ref(v___x_845_);
v___x_848_ = lean_nat_dec_le(v_hi_841_, v_fst_846_);
if (v___x_848_ == 0)
{
lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; 
v___x_849_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg(v_n_838_, v_snd_847_, v_lo_840_, v_fst_846_);
v___x_850_ = lean_unsigned_to_nat(1u);
v___x_851_ = lean_nat_add(v_fst_846_, v___x_850_);
lean_dec(v_fst_846_);
v_as_839_ = v___x_849_;
v_lo_840_ = v___x_851_;
goto _start;
}
else
{
lean_dec(v_fst_846_);
lean_dec(v_lo_840_);
return v_snd_847_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg___boxed(lean_object* v_n_873_, lean_object* v_as_874_, lean_object* v_lo_875_, lean_object* v_hi_876_){
_start:
{
lean_object* v_res_877_; 
v_res_877_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg(v_n_873_, v_as_874_, v_lo_875_, v_hi_876_);
lean_dec(v_hi_876_);
lean_dec(v_n_873_);
return v_res_877_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4_spec__5(lean_object* v_msgData_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_){
_start:
{
lean_object* v___x_884_; lean_object* v_env_885_; lean_object* v___x_886_; lean_object* v_mctx_887_; lean_object* v_lctx_888_; lean_object* v_options_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; 
v___x_884_ = lean_st_ref_get(v___y_882_);
v_env_885_ = lean_ctor_get(v___x_884_, 0);
lean_inc_ref(v_env_885_);
lean_dec(v___x_884_);
v___x_886_ = lean_st_ref_get(v___y_880_);
v_mctx_887_ = lean_ctor_get(v___x_886_, 0);
lean_inc_ref(v_mctx_887_);
lean_dec(v___x_886_);
v_lctx_888_ = lean_ctor_get(v___y_879_, 2);
v_options_889_ = lean_ctor_get(v___y_881_, 2);
lean_inc_ref(v_options_889_);
lean_inc_ref(v_lctx_888_);
v___x_890_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_890_, 0, v_env_885_);
lean_ctor_set(v___x_890_, 1, v_mctx_887_);
lean_ctor_set(v___x_890_, 2, v_lctx_888_);
lean_ctor_set(v___x_890_, 3, v_options_889_);
v___x_891_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_891_, 0, v___x_890_);
lean_ctor_set(v___x_891_, 1, v_msgData_878_);
v___x_892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_892_, 0, v___x_891_);
return v___x_892_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4_spec__5___boxed(lean_object* v_msgData_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_){
_start:
{
lean_object* v_res_899_; 
v_res_899_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4_spec__5(v_msgData_893_, v___y_894_, v___y_895_, v___y_896_, v___y_897_);
lean_dec(v___y_897_);
lean_dec_ref(v___y_896_);
lean_dec(v___y_895_);
lean_dec_ref(v___y_894_);
return v_res_899_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg(lean_object* v_msg_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_){
_start:
{
lean_object* v_ref_906_; lean_object* v___x_907_; lean_object* v_a_908_; lean_object* v___x_910_; uint8_t v_isShared_911_; uint8_t v_isSharedCheck_916_; 
v_ref_906_ = lean_ctor_get(v___y_903_, 5);
v___x_907_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4_spec__5(v_msg_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_);
v_a_908_ = lean_ctor_get(v___x_907_, 0);
v_isSharedCheck_916_ = !lean_is_exclusive(v___x_907_);
if (v_isSharedCheck_916_ == 0)
{
v___x_910_ = v___x_907_;
v_isShared_911_ = v_isSharedCheck_916_;
goto v_resetjp_909_;
}
else
{
lean_inc(v_a_908_);
lean_dec(v___x_907_);
v___x_910_ = lean_box(0);
v_isShared_911_ = v_isSharedCheck_916_;
goto v_resetjp_909_;
}
v_resetjp_909_:
{
lean_object* v___x_912_; lean_object* v___x_914_; 
lean_inc(v_ref_906_);
v___x_912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_912_, 0, v_ref_906_);
lean_ctor_set(v___x_912_, 1, v_a_908_);
if (v_isShared_911_ == 0)
{
lean_ctor_set_tag(v___x_910_, 1);
lean_ctor_set(v___x_910_, 0, v___x_912_);
v___x_914_ = v___x_910_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v___x_912_);
v___x_914_ = v_reuseFailAlloc_915_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
return v___x_914_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg___boxed(lean_object* v_msg_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_){
_start:
{
lean_object* v_res_923_; 
v_res_923_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg(v_msg_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_);
lean_dec(v___y_921_);
lean_dec_ref(v___y_920_);
lean_dec(v___y_919_);
lean_dec_ref(v___y_918_);
return v_res_923_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__12_spec__16___redArg(lean_object* v_x_924_, lean_object* v_x_925_, lean_object* v_x_926_, lean_object* v_x_927_){
_start:
{
lean_object* v_ks_928_; lean_object* v_vs_929_; lean_object* v___x_931_; uint8_t v_isShared_932_; uint8_t v_isSharedCheck_953_; 
v_ks_928_ = lean_ctor_get(v_x_924_, 0);
v_vs_929_ = lean_ctor_get(v_x_924_, 1);
v_isSharedCheck_953_ = !lean_is_exclusive(v_x_924_);
if (v_isSharedCheck_953_ == 0)
{
v___x_931_ = v_x_924_;
v_isShared_932_ = v_isSharedCheck_953_;
goto v_resetjp_930_;
}
else
{
lean_inc(v_vs_929_);
lean_inc(v_ks_928_);
lean_dec(v_x_924_);
v___x_931_ = lean_box(0);
v_isShared_932_ = v_isSharedCheck_953_;
goto v_resetjp_930_;
}
v_resetjp_930_:
{
lean_object* v___x_933_; uint8_t v___x_934_; 
v___x_933_ = lean_array_get_size(v_ks_928_);
v___x_934_ = lean_nat_dec_lt(v_x_925_, v___x_933_);
if (v___x_934_ == 0)
{
lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_938_; 
lean_dec(v_x_925_);
v___x_935_ = lean_array_push(v_ks_928_, v_x_926_);
v___x_936_ = lean_array_push(v_vs_929_, v_x_927_);
if (v_isShared_932_ == 0)
{
lean_ctor_set(v___x_931_, 1, v___x_936_);
lean_ctor_set(v___x_931_, 0, v___x_935_);
v___x_938_ = v___x_931_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v___x_935_);
lean_ctor_set(v_reuseFailAlloc_939_, 1, v___x_936_);
v___x_938_ = v_reuseFailAlloc_939_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
return v___x_938_;
}
}
else
{
lean_object* v_k_x27_940_; uint8_t v___x_941_; 
v_k_x27_940_ = lean_array_fget_borrowed(v_ks_928_, v_x_925_);
v___x_941_ = l_Lean_instBEqMVarId_beq(v_x_926_, v_k_x27_940_);
if (v___x_941_ == 0)
{
lean_object* v___x_943_; 
if (v_isShared_932_ == 0)
{
v___x_943_ = v___x_931_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v_ks_928_);
lean_ctor_set(v_reuseFailAlloc_947_, 1, v_vs_929_);
v___x_943_ = v_reuseFailAlloc_947_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
lean_object* v___x_944_; lean_object* v___x_945_; 
v___x_944_ = lean_unsigned_to_nat(1u);
v___x_945_ = lean_nat_add(v_x_925_, v___x_944_);
lean_dec(v_x_925_);
v_x_924_ = v___x_943_;
v_x_925_ = v___x_945_;
goto _start;
}
}
else
{
lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_951_; 
v___x_948_ = lean_array_fset(v_ks_928_, v_x_925_, v_x_926_);
v___x_949_ = lean_array_fset(v_vs_929_, v_x_925_, v_x_927_);
lean_dec(v_x_925_);
if (v_isShared_932_ == 0)
{
lean_ctor_set(v___x_931_, 1, v___x_949_);
lean_ctor_set(v___x_931_, 0, v___x_948_);
v___x_951_ = v___x_931_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v___x_948_);
lean_ctor_set(v_reuseFailAlloc_952_, 1, v___x_949_);
v___x_951_ = v_reuseFailAlloc_952_;
goto v_reusejp_950_;
}
v_reusejp_950_:
{
return v___x_951_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__12___redArg(lean_object* v_n_954_, lean_object* v_k_955_, lean_object* v_v_956_){
_start:
{
lean_object* v___x_957_; lean_object* v___x_958_; 
v___x_957_ = lean_unsigned_to_nat(0u);
v___x_958_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__12_spec__16___redArg(v_n_954_, v___x_957_, v_k_955_, v_v_956_);
return v___x_958_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__0(void){
_start:
{
size_t v___x_959_; size_t v___x_960_; size_t v___x_961_; 
v___x_959_ = ((size_t)5ULL);
v___x_960_ = ((size_t)1ULL);
v___x_961_ = lean_usize_shift_left(v___x_960_, v___x_959_);
return v___x_961_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__1(void){
_start:
{
size_t v___x_962_; size_t v___x_963_; size_t v___x_964_; 
v___x_962_ = ((size_t)1ULL);
v___x_963_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__0);
v___x_964_ = lean_usize_sub(v___x_963_, v___x_962_);
return v___x_964_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_965_; 
v___x_965_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_965_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg(lean_object* v_x_966_, size_t v_x_967_, size_t v_x_968_, lean_object* v_x_969_, lean_object* v_x_970_){
_start:
{
if (lean_obj_tag(v_x_966_) == 0)
{
lean_object* v_es_971_; size_t v___x_972_; size_t v___x_973_; size_t v___x_974_; size_t v___x_975_; lean_object* v_j_976_; lean_object* v___x_977_; uint8_t v___x_978_; 
v_es_971_ = lean_ctor_get(v_x_966_, 0);
v___x_972_ = ((size_t)5ULL);
v___x_973_ = ((size_t)1ULL);
v___x_974_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__1);
v___x_975_ = lean_usize_land(v_x_967_, v___x_974_);
v_j_976_ = lean_usize_to_nat(v___x_975_);
v___x_977_ = lean_array_get_size(v_es_971_);
v___x_978_ = lean_nat_dec_lt(v_j_976_, v___x_977_);
if (v___x_978_ == 0)
{
lean_dec(v_j_976_);
lean_dec(v_x_970_);
lean_dec(v_x_969_);
return v_x_966_;
}
else
{
lean_object* v___x_980_; uint8_t v_isShared_981_; uint8_t v_isSharedCheck_1015_; 
lean_inc_ref(v_es_971_);
v_isSharedCheck_1015_ = !lean_is_exclusive(v_x_966_);
if (v_isSharedCheck_1015_ == 0)
{
lean_object* v_unused_1016_; 
v_unused_1016_ = lean_ctor_get(v_x_966_, 0);
lean_dec(v_unused_1016_);
v___x_980_ = v_x_966_;
v_isShared_981_ = v_isSharedCheck_1015_;
goto v_resetjp_979_;
}
else
{
lean_dec(v_x_966_);
v___x_980_ = lean_box(0);
v_isShared_981_ = v_isSharedCheck_1015_;
goto v_resetjp_979_;
}
v_resetjp_979_:
{
lean_object* v_v_982_; lean_object* v___x_983_; lean_object* v_xs_x27_984_; lean_object* v___y_986_; 
v_v_982_ = lean_array_fget(v_es_971_, v_j_976_);
v___x_983_ = lean_box(0);
v_xs_x27_984_ = lean_array_fset(v_es_971_, v_j_976_, v___x_983_);
switch(lean_obj_tag(v_v_982_))
{
case 0:
{
lean_object* v_key_991_; lean_object* v_val_992_; lean_object* v___x_994_; uint8_t v_isShared_995_; uint8_t v_isSharedCheck_1002_; 
v_key_991_ = lean_ctor_get(v_v_982_, 0);
v_val_992_ = lean_ctor_get(v_v_982_, 1);
v_isSharedCheck_1002_ = !lean_is_exclusive(v_v_982_);
if (v_isSharedCheck_1002_ == 0)
{
v___x_994_ = v_v_982_;
v_isShared_995_ = v_isSharedCheck_1002_;
goto v_resetjp_993_;
}
else
{
lean_inc(v_val_992_);
lean_inc(v_key_991_);
lean_dec(v_v_982_);
v___x_994_ = lean_box(0);
v_isShared_995_ = v_isSharedCheck_1002_;
goto v_resetjp_993_;
}
v_resetjp_993_:
{
uint8_t v___x_996_; 
v___x_996_ = l_Lean_instBEqMVarId_beq(v_x_969_, v_key_991_);
if (v___x_996_ == 0)
{
lean_object* v___x_997_; lean_object* v___x_998_; 
lean_del_object(v___x_994_);
v___x_997_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_991_, v_val_992_, v_x_969_, v_x_970_);
v___x_998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_998_, 0, v___x_997_);
v___y_986_ = v___x_998_;
goto v___jp_985_;
}
else
{
lean_object* v___x_1000_; 
lean_dec(v_val_992_);
lean_dec(v_key_991_);
if (v_isShared_995_ == 0)
{
lean_ctor_set(v___x_994_, 1, v_x_970_);
lean_ctor_set(v___x_994_, 0, v_x_969_);
v___x_1000_ = v___x_994_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v_x_969_);
lean_ctor_set(v_reuseFailAlloc_1001_, 1, v_x_970_);
v___x_1000_ = v_reuseFailAlloc_1001_;
goto v_reusejp_999_;
}
v_reusejp_999_:
{
v___y_986_ = v___x_1000_;
goto v___jp_985_;
}
}
}
}
case 1:
{
lean_object* v_node_1003_; lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1013_; 
v_node_1003_ = lean_ctor_get(v_v_982_, 0);
v_isSharedCheck_1013_ = !lean_is_exclusive(v_v_982_);
if (v_isSharedCheck_1013_ == 0)
{
v___x_1005_ = v_v_982_;
v_isShared_1006_ = v_isSharedCheck_1013_;
goto v_resetjp_1004_;
}
else
{
lean_inc(v_node_1003_);
lean_dec(v_v_982_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1013_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
size_t v___x_1007_; size_t v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1011_; 
v___x_1007_ = lean_usize_shift_right(v_x_967_, v___x_972_);
v___x_1008_ = lean_usize_add(v_x_968_, v___x_973_);
v___x_1009_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg(v_node_1003_, v___x_1007_, v___x_1008_, v_x_969_, v_x_970_);
if (v_isShared_1006_ == 0)
{
lean_ctor_set(v___x_1005_, 0, v___x_1009_);
v___x_1011_ = v___x_1005_;
goto v_reusejp_1010_;
}
else
{
lean_object* v_reuseFailAlloc_1012_; 
v_reuseFailAlloc_1012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v___x_1009_);
v___x_1011_ = v_reuseFailAlloc_1012_;
goto v_reusejp_1010_;
}
v_reusejp_1010_:
{
v___y_986_ = v___x_1011_;
goto v___jp_985_;
}
}
}
default: 
{
lean_object* v___x_1014_; 
v___x_1014_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1014_, 0, v_x_969_);
lean_ctor_set(v___x_1014_, 1, v_x_970_);
v___y_986_ = v___x_1014_;
goto v___jp_985_;
}
}
v___jp_985_:
{
lean_object* v___x_987_; lean_object* v___x_989_; 
v___x_987_ = lean_array_fset(v_xs_x27_984_, v_j_976_, v___y_986_);
lean_dec(v_j_976_);
if (v_isShared_981_ == 0)
{
lean_ctor_set(v___x_980_, 0, v___x_987_);
v___x_989_ = v___x_980_;
goto v_reusejp_988_;
}
else
{
lean_object* v_reuseFailAlloc_990_; 
v_reuseFailAlloc_990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_990_, 0, v___x_987_);
v___x_989_ = v_reuseFailAlloc_990_;
goto v_reusejp_988_;
}
v_reusejp_988_:
{
return v___x_989_;
}
}
}
}
}
else
{
lean_object* v_ks_1017_; lean_object* v_vs_1018_; lean_object* v___x_1020_; uint8_t v_isShared_1021_; uint8_t v_isSharedCheck_1038_; 
v_ks_1017_ = lean_ctor_get(v_x_966_, 0);
v_vs_1018_ = lean_ctor_get(v_x_966_, 1);
v_isSharedCheck_1038_ = !lean_is_exclusive(v_x_966_);
if (v_isSharedCheck_1038_ == 0)
{
v___x_1020_ = v_x_966_;
v_isShared_1021_ = v_isSharedCheck_1038_;
goto v_resetjp_1019_;
}
else
{
lean_inc(v_vs_1018_);
lean_inc(v_ks_1017_);
lean_dec(v_x_966_);
v___x_1020_ = lean_box(0);
v_isShared_1021_ = v_isSharedCheck_1038_;
goto v_resetjp_1019_;
}
v_resetjp_1019_:
{
lean_object* v___x_1023_; 
if (v_isShared_1021_ == 0)
{
v___x_1023_ = v___x_1020_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v_ks_1017_);
lean_ctor_set(v_reuseFailAlloc_1037_, 1, v_vs_1018_);
v___x_1023_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
lean_object* v_newNode_1024_; uint8_t v___y_1026_; size_t v___x_1032_; uint8_t v___x_1033_; 
v_newNode_1024_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__12___redArg(v___x_1023_, v_x_969_, v_x_970_);
v___x_1032_ = ((size_t)7ULL);
v___x_1033_ = lean_usize_dec_le(v___x_1032_, v_x_968_);
if (v___x_1033_ == 0)
{
lean_object* v___x_1034_; lean_object* v___x_1035_; uint8_t v___x_1036_; 
v___x_1034_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1024_);
v___x_1035_ = lean_unsigned_to_nat(4u);
v___x_1036_ = lean_nat_dec_lt(v___x_1034_, v___x_1035_);
lean_dec(v___x_1034_);
v___y_1026_ = v___x_1036_;
goto v___jp_1025_;
}
else
{
v___y_1026_ = v___x_1033_;
goto v___jp_1025_;
}
v___jp_1025_:
{
if (v___y_1026_ == 0)
{
lean_object* v_ks_1027_; lean_object* v_vs_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; 
v_ks_1027_ = lean_ctor_get(v_newNode_1024_, 0);
lean_inc_ref(v_ks_1027_);
v_vs_1028_ = lean_ctor_get(v_newNode_1024_, 1);
lean_inc_ref(v_vs_1028_);
lean_dec_ref(v_newNode_1024_);
v___x_1029_ = lean_unsigned_to_nat(0u);
v___x_1030_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__2);
v___x_1031_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__13___redArg(v_x_968_, v_ks_1027_, v_vs_1028_, v___x_1029_, v___x_1030_);
lean_dec_ref(v_vs_1028_);
lean_dec_ref(v_ks_1027_);
return v___x_1031_;
}
else
{
return v_newNode_1024_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__13___redArg(size_t v_depth_1039_, lean_object* v_keys_1040_, lean_object* v_vals_1041_, lean_object* v_i_1042_, lean_object* v_entries_1043_){
_start:
{
lean_object* v___x_1044_; uint8_t v___x_1045_; 
v___x_1044_ = lean_array_get_size(v_keys_1040_);
v___x_1045_ = lean_nat_dec_lt(v_i_1042_, v___x_1044_);
if (v___x_1045_ == 0)
{
lean_dec(v_i_1042_);
return v_entries_1043_;
}
else
{
lean_object* v_k_1046_; lean_object* v_v_1047_; uint64_t v___x_1048_; size_t v_h_1049_; size_t v___x_1050_; lean_object* v___x_1051_; size_t v___x_1052_; size_t v___x_1053_; size_t v___x_1054_; size_t v_h_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; 
v_k_1046_ = lean_array_fget_borrowed(v_keys_1040_, v_i_1042_);
v_v_1047_ = lean_array_fget_borrowed(v_vals_1041_, v_i_1042_);
v___x_1048_ = l_Lean_instHashableMVarId_hash(v_k_1046_);
v_h_1049_ = lean_uint64_to_usize(v___x_1048_);
v___x_1050_ = ((size_t)5ULL);
v___x_1051_ = lean_unsigned_to_nat(1u);
v___x_1052_ = ((size_t)1ULL);
v___x_1053_ = lean_usize_sub(v_depth_1039_, v___x_1052_);
v___x_1054_ = lean_usize_mul(v___x_1050_, v___x_1053_);
v_h_1055_ = lean_usize_shift_right(v_h_1049_, v___x_1054_);
v___x_1056_ = lean_nat_add(v_i_1042_, v___x_1051_);
lean_dec(v_i_1042_);
lean_inc(v_v_1047_);
lean_inc(v_k_1046_);
v___x_1057_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg(v_entries_1043_, v_h_1055_, v_depth_1039_, v_k_1046_, v_v_1047_);
v_i_1042_ = v___x_1056_;
v_entries_1043_ = v___x_1057_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__13___redArg___boxed(lean_object* v_depth_1059_, lean_object* v_keys_1060_, lean_object* v_vals_1061_, lean_object* v_i_1062_, lean_object* v_entries_1063_){
_start:
{
size_t v_depth_boxed_1064_; lean_object* v_res_1065_; 
v_depth_boxed_1064_ = lean_unbox_usize(v_depth_1059_);
lean_dec(v_depth_1059_);
v_res_1065_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__13___redArg(v_depth_boxed_1064_, v_keys_1060_, v_vals_1061_, v_i_1062_, v_entries_1063_);
lean_dec_ref(v_vals_1061_);
lean_dec_ref(v_keys_1060_);
return v_res_1065_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___boxed(lean_object* v_x_1066_, lean_object* v_x_1067_, lean_object* v_x_1068_, lean_object* v_x_1069_, lean_object* v_x_1070_){
_start:
{
size_t v_x_18897__boxed_1071_; size_t v_x_18898__boxed_1072_; lean_object* v_res_1073_; 
v_x_18897__boxed_1071_ = lean_unbox_usize(v_x_1067_);
lean_dec(v_x_1067_);
v_x_18898__boxed_1072_ = lean_unbox_usize(v_x_1068_);
lean_dec(v_x_1068_);
v_res_1073_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg(v_x_1066_, v_x_18897__boxed_1071_, v_x_18898__boxed_1072_, v_x_1069_, v_x_1070_);
return v_res_1073_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3___redArg(lean_object* v_x_1074_, lean_object* v_x_1075_, lean_object* v_x_1076_){
_start:
{
uint64_t v___x_1077_; size_t v___x_1078_; size_t v___x_1079_; lean_object* v___x_1080_; 
v___x_1077_ = l_Lean_instHashableMVarId_hash(v_x_1075_);
v___x_1078_ = lean_uint64_to_usize(v___x_1077_);
v___x_1079_ = ((size_t)1ULL);
v___x_1080_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg(v_x_1074_, v___x_1078_, v___x_1079_, v_x_1075_, v_x_1076_);
return v___x_1080_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3___redArg(lean_object* v_mvarId_1081_, lean_object* v_val_1082_, lean_object* v___y_1083_){
_start:
{
lean_object* v___x_1085_; lean_object* v_mctx_1086_; lean_object* v_cache_1087_; lean_object* v_zetaDeltaFVarIds_1088_; lean_object* v_postponed_1089_; lean_object* v_diag_1090_; lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1118_; 
v___x_1085_ = lean_st_ref_take(v___y_1083_);
v_mctx_1086_ = lean_ctor_get(v___x_1085_, 0);
v_cache_1087_ = lean_ctor_get(v___x_1085_, 1);
v_zetaDeltaFVarIds_1088_ = lean_ctor_get(v___x_1085_, 2);
v_postponed_1089_ = lean_ctor_get(v___x_1085_, 3);
v_diag_1090_ = lean_ctor_get(v___x_1085_, 4);
v_isSharedCheck_1118_ = !lean_is_exclusive(v___x_1085_);
if (v_isSharedCheck_1118_ == 0)
{
v___x_1092_ = v___x_1085_;
v_isShared_1093_ = v_isSharedCheck_1118_;
goto v_resetjp_1091_;
}
else
{
lean_inc(v_diag_1090_);
lean_inc(v_postponed_1089_);
lean_inc(v_zetaDeltaFVarIds_1088_);
lean_inc(v_cache_1087_);
lean_inc(v_mctx_1086_);
lean_dec(v___x_1085_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1118_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
lean_object* v_depth_1094_; lean_object* v_levelAssignDepth_1095_; lean_object* v_lmvarCounter_1096_; lean_object* v_mvarCounter_1097_; lean_object* v_lDecls_1098_; lean_object* v_decls_1099_; lean_object* v_userNames_1100_; lean_object* v_lAssignment_1101_; lean_object* v_eAssignment_1102_; lean_object* v_dAssignment_1103_; lean_object* v___x_1105_; uint8_t v_isShared_1106_; uint8_t v_isSharedCheck_1117_; 
v_depth_1094_ = lean_ctor_get(v_mctx_1086_, 0);
v_levelAssignDepth_1095_ = lean_ctor_get(v_mctx_1086_, 1);
v_lmvarCounter_1096_ = lean_ctor_get(v_mctx_1086_, 2);
v_mvarCounter_1097_ = lean_ctor_get(v_mctx_1086_, 3);
v_lDecls_1098_ = lean_ctor_get(v_mctx_1086_, 4);
v_decls_1099_ = lean_ctor_get(v_mctx_1086_, 5);
v_userNames_1100_ = lean_ctor_get(v_mctx_1086_, 6);
v_lAssignment_1101_ = lean_ctor_get(v_mctx_1086_, 7);
v_eAssignment_1102_ = lean_ctor_get(v_mctx_1086_, 8);
v_dAssignment_1103_ = lean_ctor_get(v_mctx_1086_, 9);
v_isSharedCheck_1117_ = !lean_is_exclusive(v_mctx_1086_);
if (v_isSharedCheck_1117_ == 0)
{
v___x_1105_ = v_mctx_1086_;
v_isShared_1106_ = v_isSharedCheck_1117_;
goto v_resetjp_1104_;
}
else
{
lean_inc(v_dAssignment_1103_);
lean_inc(v_eAssignment_1102_);
lean_inc(v_lAssignment_1101_);
lean_inc(v_userNames_1100_);
lean_inc(v_decls_1099_);
lean_inc(v_lDecls_1098_);
lean_inc(v_mvarCounter_1097_);
lean_inc(v_lmvarCounter_1096_);
lean_inc(v_levelAssignDepth_1095_);
lean_inc(v_depth_1094_);
lean_dec(v_mctx_1086_);
v___x_1105_ = lean_box(0);
v_isShared_1106_ = v_isSharedCheck_1117_;
goto v_resetjp_1104_;
}
v_resetjp_1104_:
{
lean_object* v___x_1107_; lean_object* v___x_1109_; 
v___x_1107_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3___redArg(v_eAssignment_1102_, v_mvarId_1081_, v_val_1082_);
if (v_isShared_1106_ == 0)
{
lean_ctor_set(v___x_1105_, 8, v___x_1107_);
v___x_1109_ = v___x_1105_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v_depth_1094_);
lean_ctor_set(v_reuseFailAlloc_1116_, 1, v_levelAssignDepth_1095_);
lean_ctor_set(v_reuseFailAlloc_1116_, 2, v_lmvarCounter_1096_);
lean_ctor_set(v_reuseFailAlloc_1116_, 3, v_mvarCounter_1097_);
lean_ctor_set(v_reuseFailAlloc_1116_, 4, v_lDecls_1098_);
lean_ctor_set(v_reuseFailAlloc_1116_, 5, v_decls_1099_);
lean_ctor_set(v_reuseFailAlloc_1116_, 6, v_userNames_1100_);
lean_ctor_set(v_reuseFailAlloc_1116_, 7, v_lAssignment_1101_);
lean_ctor_set(v_reuseFailAlloc_1116_, 8, v___x_1107_);
lean_ctor_set(v_reuseFailAlloc_1116_, 9, v_dAssignment_1103_);
v___x_1109_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
lean_object* v___x_1111_; 
if (v_isShared_1093_ == 0)
{
lean_ctor_set(v___x_1092_, 0, v___x_1109_);
v___x_1111_ = v___x_1092_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1115_; 
v_reuseFailAlloc_1115_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1115_, 0, v___x_1109_);
lean_ctor_set(v_reuseFailAlloc_1115_, 1, v_cache_1087_);
lean_ctor_set(v_reuseFailAlloc_1115_, 2, v_zetaDeltaFVarIds_1088_);
lean_ctor_set(v_reuseFailAlloc_1115_, 3, v_postponed_1089_);
lean_ctor_set(v_reuseFailAlloc_1115_, 4, v_diag_1090_);
v___x_1111_ = v_reuseFailAlloc_1115_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; 
v___x_1112_ = lean_st_ref_set(v___y_1083_, v___x_1111_);
v___x_1113_ = lean_box(0);
v___x_1114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1114_, 0, v___x_1113_);
return v___x_1114_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3___redArg___boxed(lean_object* v_mvarId_1119_, lean_object* v_val_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_){
_start:
{
lean_object* v_res_1123_; 
v_res_1123_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3___redArg(v_mvarId_1119_, v_val_1120_, v___y_1121_);
lean_dec(v___y_1121_);
return v_res_1123_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg___lam__0(lean_object* v_x1_1124_, lean_object* v_x2_1125_){
_start:
{
lean_object* v_fst_1126_; lean_object* v_fst_1127_; uint8_t v___x_1128_; 
v_fst_1126_ = lean_ctor_get(v_x1_1124_, 0);
v_fst_1127_ = lean_ctor_get(v_x2_1125_, 0);
v___x_1128_ = lean_nat_dec_lt(v_fst_1126_, v_fst_1127_);
return v___x_1128_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg___lam__0___boxed(lean_object* v_x1_1129_, lean_object* v_x2_1130_){
_start:
{
uint8_t v_res_1131_; lean_object* v_r_1132_; 
v_res_1131_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg___lam__0(v_x1_1129_, v_x2_1130_);
lean_dec_ref(v_x2_1130_);
lean_dec_ref(v_x1_1129_);
v_r_1132_ = lean_box(v_res_1131_);
return v_r_1132_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9_spec__13___redArg(lean_object* v_hi_1133_, lean_object* v_pivot_1134_, lean_object* v_as_1135_, lean_object* v_i_1136_, lean_object* v_k_1137_){
_start:
{
uint8_t v___x_1138_; 
v___x_1138_ = lean_nat_dec_lt(v_k_1137_, v_hi_1133_);
if (v___x_1138_ == 0)
{
lean_object* v___x_1139_; lean_object* v___x_1140_; 
lean_dec(v_k_1137_);
v___x_1139_ = lean_array_fswap(v_as_1135_, v_i_1136_, v_hi_1133_);
v___x_1140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1140_, 0, v_i_1136_);
lean_ctor_set(v___x_1140_, 1, v___x_1139_);
return v___x_1140_;
}
else
{
lean_object* v___x_1141_; lean_object* v_fst_1142_; lean_object* v_fst_1143_; uint8_t v___x_1144_; 
v___x_1141_ = lean_array_fget_borrowed(v_as_1135_, v_k_1137_);
v_fst_1142_ = lean_ctor_get(v___x_1141_, 0);
v_fst_1143_ = lean_ctor_get(v_pivot_1134_, 0);
v___x_1144_ = lean_nat_dec_lt(v_fst_1142_, v_fst_1143_);
if (v___x_1144_ == 0)
{
lean_object* v___x_1145_; lean_object* v___x_1146_; 
v___x_1145_ = lean_unsigned_to_nat(1u);
v___x_1146_ = lean_nat_add(v_k_1137_, v___x_1145_);
lean_dec(v_k_1137_);
v_k_1137_ = v___x_1146_;
goto _start;
}
else
{
lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; 
v___x_1148_ = lean_array_fswap(v_as_1135_, v_i_1136_, v_k_1137_);
v___x_1149_ = lean_unsigned_to_nat(1u);
v___x_1150_ = lean_nat_add(v_i_1136_, v___x_1149_);
lean_dec(v_i_1136_);
v___x_1151_ = lean_nat_add(v_k_1137_, v___x_1149_);
lean_dec(v_k_1137_);
v_as_1135_ = v___x_1148_;
v_i_1136_ = v___x_1150_;
v_k_1137_ = v___x_1151_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9_spec__13___redArg___boxed(lean_object* v_hi_1153_, lean_object* v_pivot_1154_, lean_object* v_as_1155_, lean_object* v_i_1156_, lean_object* v_k_1157_){
_start:
{
lean_object* v_res_1158_; 
v_res_1158_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9_spec__13___redArg(v_hi_1153_, v_pivot_1154_, v_as_1155_, v_i_1156_, v_k_1157_);
lean_dec_ref(v_pivot_1154_);
lean_dec(v_hi_1153_);
return v_res_1158_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg(lean_object* v_n_1159_, lean_object* v_as_1160_, lean_object* v_lo_1161_, lean_object* v_hi_1162_){
_start:
{
lean_object* v___y_1164_; uint8_t v___x_1174_; 
v___x_1174_ = lean_nat_dec_lt(v_lo_1161_, v_hi_1162_);
if (v___x_1174_ == 0)
{
lean_dec(v_lo_1161_);
return v_as_1160_;
}
else
{
lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v_mid_1177_; lean_object* v___y_1179_; lean_object* v___y_1185_; lean_object* v___x_1190_; lean_object* v___x_1191_; uint8_t v___x_1192_; 
v___x_1175_ = lean_nat_add(v_lo_1161_, v_hi_1162_);
v___x_1176_ = lean_unsigned_to_nat(1u);
v_mid_1177_ = lean_nat_shiftr(v___x_1175_, v___x_1176_);
lean_dec(v___x_1175_);
v___x_1190_ = lean_array_fget_borrowed(v_as_1160_, v_mid_1177_);
v___x_1191_ = lean_array_fget_borrowed(v_as_1160_, v_lo_1161_);
v___x_1192_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg___lam__0(v___x_1190_, v___x_1191_);
if (v___x_1192_ == 0)
{
v___y_1185_ = v_as_1160_;
goto v___jp_1184_;
}
else
{
lean_object* v___x_1193_; 
v___x_1193_ = lean_array_fswap(v_as_1160_, v_lo_1161_, v_mid_1177_);
v___y_1185_ = v___x_1193_;
goto v___jp_1184_;
}
v___jp_1178_:
{
lean_object* v___x_1180_; lean_object* v___x_1181_; uint8_t v___x_1182_; 
v___x_1180_ = lean_array_fget_borrowed(v___y_1179_, v_mid_1177_);
v___x_1181_ = lean_array_fget_borrowed(v___y_1179_, v_hi_1162_);
v___x_1182_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg___lam__0(v___x_1180_, v___x_1181_);
if (v___x_1182_ == 0)
{
lean_dec(v_mid_1177_);
v___y_1164_ = v___y_1179_;
goto v___jp_1163_;
}
else
{
lean_object* v___x_1183_; 
v___x_1183_ = lean_array_fswap(v___y_1179_, v_mid_1177_, v_hi_1162_);
lean_dec(v_mid_1177_);
v___y_1164_ = v___x_1183_;
goto v___jp_1163_;
}
}
v___jp_1184_:
{
lean_object* v___x_1186_; lean_object* v___x_1187_; uint8_t v___x_1188_; 
v___x_1186_ = lean_array_fget_borrowed(v___y_1185_, v_hi_1162_);
v___x_1187_ = lean_array_fget_borrowed(v___y_1185_, v_lo_1161_);
v___x_1188_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg___lam__0(v___x_1186_, v___x_1187_);
if (v___x_1188_ == 0)
{
v___y_1179_ = v___y_1185_;
goto v___jp_1178_;
}
else
{
lean_object* v___x_1189_; 
v___x_1189_ = lean_array_fswap(v___y_1185_, v_lo_1161_, v_hi_1162_);
v___y_1179_ = v___x_1189_;
goto v___jp_1178_;
}
}
}
v___jp_1163_:
{
lean_object* v_pivot_1165_; lean_object* v___x_1166_; lean_object* v_fst_1167_; lean_object* v_snd_1168_; uint8_t v___x_1169_; 
v_pivot_1165_ = lean_array_fget(v___y_1164_, v_hi_1162_);
lean_inc_n(v_lo_1161_, 2);
v___x_1166_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9_spec__13___redArg(v_hi_1162_, v_pivot_1165_, v___y_1164_, v_lo_1161_, v_lo_1161_);
lean_dec(v_pivot_1165_);
v_fst_1167_ = lean_ctor_get(v___x_1166_, 0);
lean_inc(v_fst_1167_);
v_snd_1168_ = lean_ctor_get(v___x_1166_, 1);
lean_inc(v_snd_1168_);
lean_dec_ref(v___x_1166_);
v___x_1169_ = lean_nat_dec_le(v_hi_1162_, v_fst_1167_);
if (v___x_1169_ == 0)
{
lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; 
v___x_1170_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg(v_n_1159_, v_snd_1168_, v_lo_1161_, v_fst_1167_);
v___x_1171_ = lean_unsigned_to_nat(1u);
v___x_1172_ = lean_nat_add(v_fst_1167_, v___x_1171_);
lean_dec(v_fst_1167_);
v_as_1160_ = v___x_1170_;
v_lo_1161_ = v___x_1172_;
goto _start;
}
else
{
lean_dec(v_fst_1167_);
lean_dec(v_lo_1161_);
return v_snd_1168_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg___boxed(lean_object* v_n_1194_, lean_object* v_as_1195_, lean_object* v_lo_1196_, lean_object* v_hi_1197_){
_start:
{
lean_object* v_res_1198_; 
v_res_1198_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg(v_n_1194_, v_as_1195_, v_lo_1196_, v_hi_1197_);
lean_dec(v_hi_1197_);
lean_dec(v_n_1194_);
return v_res_1198_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1___redArg(lean_object* v_ref_1199_, lean_object* v_msg_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_){
_start:
{
lean_object* v_fileName_1210_; lean_object* v_fileMap_1211_; lean_object* v_options_1212_; lean_object* v_currRecDepth_1213_; lean_object* v_maxRecDepth_1214_; lean_object* v_ref_1215_; lean_object* v_currNamespace_1216_; lean_object* v_openDecls_1217_; lean_object* v_initHeartbeats_1218_; lean_object* v_maxHeartbeats_1219_; lean_object* v_quotContext_1220_; lean_object* v_currMacroScope_1221_; uint8_t v_diag_1222_; lean_object* v_cancelTk_x3f_1223_; uint8_t v_suppressElabErrors_1224_; lean_object* v_inheritedTraceOptions_1225_; lean_object* v_ref_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; 
v_fileName_1210_ = lean_ctor_get(v___y_1207_, 0);
v_fileMap_1211_ = lean_ctor_get(v___y_1207_, 1);
v_options_1212_ = lean_ctor_get(v___y_1207_, 2);
v_currRecDepth_1213_ = lean_ctor_get(v___y_1207_, 3);
v_maxRecDepth_1214_ = lean_ctor_get(v___y_1207_, 4);
v_ref_1215_ = lean_ctor_get(v___y_1207_, 5);
v_currNamespace_1216_ = lean_ctor_get(v___y_1207_, 6);
v_openDecls_1217_ = lean_ctor_get(v___y_1207_, 7);
v_initHeartbeats_1218_ = lean_ctor_get(v___y_1207_, 8);
v_maxHeartbeats_1219_ = lean_ctor_get(v___y_1207_, 9);
v_quotContext_1220_ = lean_ctor_get(v___y_1207_, 10);
v_currMacroScope_1221_ = lean_ctor_get(v___y_1207_, 11);
v_diag_1222_ = lean_ctor_get_uint8(v___y_1207_, sizeof(void*)*14);
v_cancelTk_x3f_1223_ = lean_ctor_get(v___y_1207_, 12);
v_suppressElabErrors_1224_ = lean_ctor_get_uint8(v___y_1207_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1225_ = lean_ctor_get(v___y_1207_, 13);
v_ref_1226_ = l_Lean_replaceRef(v_ref_1199_, v_ref_1215_);
lean_inc_ref(v_inheritedTraceOptions_1225_);
lean_inc(v_cancelTk_x3f_1223_);
lean_inc(v_currMacroScope_1221_);
lean_inc(v_quotContext_1220_);
lean_inc(v_maxHeartbeats_1219_);
lean_inc(v_initHeartbeats_1218_);
lean_inc(v_openDecls_1217_);
lean_inc(v_currNamespace_1216_);
lean_inc(v_maxRecDepth_1214_);
lean_inc(v_currRecDepth_1213_);
lean_inc_ref(v_options_1212_);
lean_inc_ref(v_fileMap_1211_);
lean_inc_ref(v_fileName_1210_);
v___x_1227_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1227_, 0, v_fileName_1210_);
lean_ctor_set(v___x_1227_, 1, v_fileMap_1211_);
lean_ctor_set(v___x_1227_, 2, v_options_1212_);
lean_ctor_set(v___x_1227_, 3, v_currRecDepth_1213_);
lean_ctor_set(v___x_1227_, 4, v_maxRecDepth_1214_);
lean_ctor_set(v___x_1227_, 5, v_ref_1226_);
lean_ctor_set(v___x_1227_, 6, v_currNamespace_1216_);
lean_ctor_set(v___x_1227_, 7, v_openDecls_1217_);
lean_ctor_set(v___x_1227_, 8, v_initHeartbeats_1218_);
lean_ctor_set(v___x_1227_, 9, v_maxHeartbeats_1219_);
lean_ctor_set(v___x_1227_, 10, v_quotContext_1220_);
lean_ctor_set(v___x_1227_, 11, v_currMacroScope_1221_);
lean_ctor_set(v___x_1227_, 12, v_cancelTk_x3f_1223_);
lean_ctor_set(v___x_1227_, 13, v_inheritedTraceOptions_1225_);
lean_ctor_set_uint8(v___x_1227_, sizeof(void*)*14, v_diag_1222_);
lean_ctor_set_uint8(v___x_1227_, sizeof(void*)*14 + 1, v_suppressElabErrors_1224_);
v___x_1228_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg(v_msg_1200_, v___y_1205_, v___y_1206_, v___x_1227_, v___y_1208_);
lean_dec_ref_known(v___x_1227_, 14);
return v___x_1228_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1___redArg___boxed(lean_object* v_ref_1229_, lean_object* v_msg_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_){
_start:
{
lean_object* v_res_1240_; 
v_res_1240_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1___redArg(v_ref_1229_, v_msg_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_);
lean_dec(v___y_1238_);
lean_dec_ref(v___y_1237_);
lean_dec(v___y_1236_);
lean_dec_ref(v___y_1235_);
lean_dec(v___y_1234_);
lean_dec_ref(v___y_1233_);
lean_dec(v___y_1232_);
lean_dec_ref(v___y_1231_);
lean_dec(v_ref_1229_);
return v_res_1240_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_1242_; lean_object* v___x_1243_; 
v___x_1242_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg___closed__0));
v___x_1243_ = l_Lean_stringToMessageData(v___x_1242_);
return v___x_1243_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg(lean_object* v_as_1244_, lean_object* v_i_1245_, lean_object* v_j_1246_, lean_object* v_bs_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_){
_start:
{
lean_object* v_zero_1257_; uint8_t v_isZero_1258_; 
v_zero_1257_ = lean_unsigned_to_nat(0u);
v_isZero_1258_ = lean_nat_dec_eq(v_i_1245_, v_zero_1257_);
if (v_isZero_1258_ == 1)
{
lean_object* v___x_1259_; 
lean_dec(v_j_1246_);
lean_dec(v_i_1245_);
v___x_1259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1259_, 0, v_bs_1247_);
return v___x_1259_;
}
else
{
lean_object* v_one_1260_; lean_object* v_n_1261_; lean_object* v_a_1263_; lean_object* v___x_1267_; lean_object* v___x_1268_; uint8_t v_isZero_1269_; 
v_one_1260_ = lean_unsigned_to_nat(1u);
v_n_1261_ = lean_nat_sub(v_i_1245_, v_one_1260_);
lean_dec(v_i_1245_);
v___x_1267_ = lean_array_fget_borrowed(v_as_1244_, v_j_1246_);
v___x_1268_ = l_Lean_TSyntax_getNat(v___x_1267_);
v_isZero_1269_ = lean_nat_dec_eq(v___x_1268_, v_zero_1257_);
if (v_isZero_1269_ == 1)
{
lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v_a_1272_; lean_object* v___x_1274_; uint8_t v_isShared_1275_; uint8_t v_isSharedCheck_1279_; 
lean_dec(v___x_1268_);
lean_dec(v_n_1261_);
lean_dec_ref(v_bs_1247_);
lean_dec(v_j_1246_);
v___x_1270_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg___closed__1, &l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg___closed__1_once, _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg___closed__1);
v___x_1271_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1___redArg(v___x_1267_, v___x_1270_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_);
v_a_1272_ = lean_ctor_get(v___x_1271_, 0);
v_isSharedCheck_1279_ = !lean_is_exclusive(v___x_1271_);
if (v_isSharedCheck_1279_ == 0)
{
v___x_1274_ = v___x_1271_;
v_isShared_1275_ = v_isSharedCheck_1279_;
goto v_resetjp_1273_;
}
else
{
lean_inc(v_a_1272_);
lean_dec(v___x_1271_);
v___x_1274_ = lean_box(0);
v_isShared_1275_ = v_isSharedCheck_1279_;
goto v_resetjp_1273_;
}
v_resetjp_1273_:
{
lean_object* v___x_1277_; 
if (v_isShared_1275_ == 0)
{
v___x_1277_ = v___x_1274_;
goto v_reusejp_1276_;
}
else
{
lean_object* v_reuseFailAlloc_1278_; 
v_reuseFailAlloc_1278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1278_, 0, v_a_1272_);
v___x_1277_ = v_reuseFailAlloc_1278_;
goto v_reusejp_1276_;
}
v_reusejp_1276_:
{
return v___x_1277_;
}
}
}
else
{
lean_object* v_n_1280_; lean_object* v___x_1281_; 
v_n_1280_ = lean_nat_sub(v___x_1268_, v_one_1260_);
lean_dec(v___x_1268_);
lean_inc(v_j_1246_);
v___x_1281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1281_, 0, v_n_1280_);
lean_ctor_set(v___x_1281_, 1, v_j_1246_);
v_a_1263_ = v___x_1281_;
goto v___jp_1262_;
}
v___jp_1262_:
{
lean_object* v___x_1264_; lean_object* v___x_1265_; 
v___x_1264_ = lean_nat_add(v_j_1246_, v_one_1260_);
lean_dec(v_j_1246_);
v___x_1265_ = lean_array_push(v_bs_1247_, v_a_1263_);
v_i_1245_ = v_n_1261_;
v_j_1246_ = v___x_1264_;
v_bs_1247_ = v___x_1265_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg___boxed(lean_object* v_as_1282_, lean_object* v_i_1283_, lean_object* v_j_1284_, lean_object* v_bs_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_){
_start:
{
lean_object* v_res_1295_; 
v_res_1295_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg(v_as_1282_, v_i_1283_, v_j_1284_, v_bs_1285_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_);
lean_dec(v___y_1293_);
lean_dec_ref(v___y_1292_);
lean_dec(v___y_1291_);
lean_dec_ref(v___y_1290_);
lean_dec(v___y_1289_);
lean_dec_ref(v___y_1288_);
lean_dec(v___y_1287_);
lean_dec_ref(v___y_1286_);
lean_dec_ref(v_as_1282_);
return v_res_1295_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11_spec__13___redArg(lean_object* v_as_1296_, lean_object* v_a_1297_, lean_object* v_x_1298_){
_start:
{
lean_object* v_zero_1299_; uint8_t v_isZero_1300_; 
v_zero_1299_ = lean_unsigned_to_nat(0u);
v_isZero_1300_ = lean_nat_dec_eq(v_x_1298_, v_zero_1299_);
if (v_isZero_1300_ == 1)
{
lean_dec(v_x_1298_);
return v_isZero_1300_;
}
else
{
lean_object* v_fst_1301_; lean_object* v_one_1302_; lean_object* v_n_1303_; lean_object* v___x_1304_; lean_object* v_fst_1305_; uint8_t v___x_1306_; 
v_fst_1301_ = lean_ctor_get(v_a_1297_, 0);
v_one_1302_ = lean_unsigned_to_nat(1u);
v_n_1303_ = lean_nat_sub(v_x_1298_, v_one_1302_);
lean_dec(v_x_1298_);
v___x_1304_ = lean_array_fget_borrowed(v_as_1296_, v_n_1303_);
v_fst_1305_ = lean_ctor_get(v___x_1304_, 0);
v___x_1306_ = lean_nat_dec_eq(v_fst_1301_, v_fst_1305_);
if (v___x_1306_ == 0)
{
v_x_1298_ = v_n_1303_;
goto _start;
}
else
{
lean_dec(v_n_1303_);
return v_isZero_1300_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11_spec__13___redArg___boxed(lean_object* v_as_1308_, lean_object* v_a_1309_, lean_object* v_x_1310_){
_start:
{
uint8_t v_res_1311_; lean_object* v_r_1312_; 
v_res_1311_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11_spec__13___redArg(v_as_1308_, v_a_1309_, v_x_1310_);
lean_dec_ref(v_a_1309_);
lean_dec_ref(v_as_1308_);
v_r_1312_ = lean_box(v_res_1311_);
return v_r_1312_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11(lean_object* v_as_1313_, lean_object* v_i_1314_){
_start:
{
lean_object* v___x_1315_; uint8_t v___x_1316_; 
v___x_1315_ = lean_array_get_size(v_as_1313_);
v___x_1316_ = lean_nat_dec_lt(v_i_1314_, v___x_1315_);
if (v___x_1316_ == 0)
{
uint8_t v___x_1317_; 
lean_dec(v_i_1314_);
v___x_1317_ = 1;
return v___x_1317_;
}
else
{
lean_object* v___x_1318_; uint8_t v___x_1319_; 
v___x_1318_ = lean_array_fget_borrowed(v_as_1313_, v_i_1314_);
lean_inc(v_i_1314_);
v___x_1319_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11_spec__13___redArg(v_as_1313_, v___x_1318_, v_i_1314_);
if (v___x_1319_ == 0)
{
lean_dec(v_i_1314_);
return v___x_1319_;
}
else
{
lean_object* v___x_1320_; lean_object* v___x_1321_; 
v___x_1320_ = lean_unsigned_to_nat(1u);
v___x_1321_ = lean_nat_add(v_i_1314_, v___x_1320_);
lean_dec(v_i_1314_);
v_i_1314_ = v___x_1321_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11___boxed(lean_object* v_as_1323_, lean_object* v_i_1324_){
_start:
{
uint8_t v_res_1325_; lean_object* v_r_1326_; 
v_res_1325_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11(v_as_1323_, v_i_1324_);
lean_dec_ref(v_as_1323_);
v_r_1326_ = lean_box(v_res_1325_);
return v_r_1326_;
}
}
LEAN_EXPORT uint8_t l_Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8(lean_object* v_as_1327_){
_start:
{
lean_object* v___x_1328_; uint8_t v___x_1329_; 
v___x_1328_ = lean_unsigned_to_nat(0u);
v___x_1329_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11(v_as_1327_, v___x_1328_);
return v___x_1329_;
}
}
LEAN_EXPORT lean_object* l_Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8___boxed(lean_object* v_as_1330_){
_start:
{
uint8_t v_res_1331_; lean_object* v_r_1332_; 
v_res_1331_ = l_Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8(v_as_1330_);
lean_dec_ref(v_as_1330_);
v_r_1332_ = lean_box(v_res_1331_);
return v_r_1332_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__0(void){
_start:
{
lean_object* v___x_1333_; 
v___x_1333_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1333_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__1(void){
_start:
{
lean_object* v___x_1334_; lean_object* v___x_1335_; 
v___x_1334_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__0, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__0_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__0);
v___x_1335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1335_, 0, v___x_1334_);
return v___x_1335_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__2(void){
_start:
{
lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; 
v___x_1336_ = lean_unsigned_to_nat(0u);
v___x_1337_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__1, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__1_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__1);
v___x_1338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1338_, 0, v___x_1337_);
lean_ctor_set(v___x_1338_, 1, v___x_1336_);
return v___x_1338_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__3(void){
_start:
{
lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; 
v___x_1339_ = lean_unsigned_to_nat(32u);
v___x_1340_ = lean_mk_empty_array_with_capacity(v___x_1339_);
v___x_1341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1341_, 0, v___x_1340_);
return v___x_1341_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__4(void){
_start:
{
size_t v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; 
v___x_1342_ = ((size_t)5ULL);
v___x_1343_ = lean_unsigned_to_nat(0u);
v___x_1344_ = lean_unsigned_to_nat(32u);
v___x_1345_ = lean_mk_empty_array_with_capacity(v___x_1344_);
v___x_1346_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__3, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__3_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__3);
v___x_1347_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1347_, 0, v___x_1346_);
lean_ctor_set(v___x_1347_, 1, v___x_1345_);
lean_ctor_set(v___x_1347_, 2, v___x_1343_);
lean_ctor_set(v___x_1347_, 3, v___x_1343_);
lean_ctor_set_usize(v___x_1347_, 4, v___x_1342_);
return v___x_1347_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__5(void){
_start:
{
lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; 
v___x_1348_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__4, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__4_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__4);
v___x_1349_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__1, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__1_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__1);
v___x_1350_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1350_, 0, v___x_1349_);
lean_ctor_set(v___x_1350_, 1, v___x_1349_);
lean_ctor_set(v___x_1350_, 2, v___x_1349_);
lean_ctor_set(v___x_1350_, 3, v___x_1348_);
return v___x_1350_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__6(void){
_start:
{
lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; 
v___x_1351_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__5, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__5_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__5);
v___x_1352_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__2, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__2_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__2);
v___x_1353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1353_, 0, v___x_1352_);
lean_ctor_set(v___x_1353_, 1, v___x_1351_);
return v___x_1353_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__8(void){
_start:
{
lean_object* v___x_1355_; lean_object* v___x_1356_; 
v___x_1355_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__7));
v___x_1356_ = l_Lean_stringToMessageData(v___x_1355_);
return v___x_1356_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__10(void){
_start:
{
lean_object* v___x_1358_; lean_object* v___x_1359_; 
v___x_1358_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__9));
v___x_1359_ = l_Lean_stringToMessageData(v___x_1358_);
return v___x_1359_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__12(void){
_start:
{
lean_object* v___x_1361_; lean_object* v___x_1362_; 
v___x_1361_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__11));
v___x_1362_ = l_Lean_stringToMessageData(v___x_1361_);
return v___x_1362_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__14(void){
_start:
{
lean_object* v___x_1364_; lean_object* v___x_1365_; 
v___x_1364_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__13));
v___x_1365_ = l_Lean_stringToMessageData(v___x_1364_);
return v___x_1365_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__17(void){
_start:
{
lean_object* v___x_1369_; lean_object* v___x_1370_; 
v___x_1369_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__16));
v___x_1370_ = l_Lean_stringToMessageData(v___x_1369_);
return v___x_1370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__6(uint8_t v___x_1391_, lean_object* v___f_1392_, uint8_t v___x_1393_, lean_object* v_stx_1394_, lean_object* v___x_1395_, lean_object* v___x_1396_, lean_object* v___x_1397_, lean_object* v___x_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_){
_start:
{
lean_object* v___y_1409_; lean_object* v_subgoals_1410_; lean_object* v___y_1411_; lean_object* v___y_1412_; lean_object* v___y_1413_; lean_object* v___y_1414_; lean_object* v___y_1415_; lean_object* v___y_1416_; lean_object* v___y_1417_; lean_object* v___y_1418_; lean_object* v___y_1456_; lean_object* v___y_1457_; lean_object* v___y_1458_; lean_object* v___y_1459_; lean_object* v___y_1460_; lean_object* v___y_1461_; lean_object* v___y_1462_; lean_object* v___y_1463_; lean_object* v___y_1464_; lean_object* v___y_1465_; lean_object* v___y_1470_; lean_object* v___y_1471_; lean_object* v___y_1472_; lean_object* v___y_1473_; lean_object* v___y_1474_; lean_object* v___y_1475_; lean_object* v___y_1476_; lean_object* v___y_1477_; lean_object* v___y_1478_; lean_object* v___y_1479_; lean_object* v___y_1480_; lean_object* v___y_1481_; lean_object* v___y_1482_; lean_object* v___y_1485_; lean_object* v___y_1486_; lean_object* v___y_1487_; lean_object* v___y_1488_; lean_object* v___y_1489_; lean_object* v___y_1490_; lean_object* v___y_1491_; lean_object* v___y_1492_; lean_object* v___y_1493_; lean_object* v___y_1494_; lean_object* v___y_1495_; lean_object* v___y_1496_; lean_object* v___y_1497_; 
if (v___x_1391_ == 0)
{
lean_object* v___x_1499_; 
lean_dec_ref(v___x_1398_);
lean_dec_ref(v___x_1397_);
lean_dec_ref(v___x_1396_);
lean_dec_ref(v___x_1395_);
lean_dec_ref(v___f_1392_);
v___x_1499_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg();
return v___x_1499_;
}
else
{
lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___y_1503_; lean_object* v___y_1504_; lean_object* v___y_1505_; lean_object* v___y_1506_; lean_object* v___y_1507_; lean_object* v___y_1508_; lean_object* v___y_1509_; lean_object* v___y_1510_; lean_object* v___y_1511_; lean_object* v___y_1512_; lean_object* v___y_1518_; lean_object* v___y_1519_; lean_object* v___y_1520_; lean_object* v___y_1521_; lean_object* v___y_1522_; lean_object* v___y_1523_; lean_object* v___y_1524_; lean_object* v___y_1525_; lean_object* v___y_1526_; lean_object* v___y_1527_; lean_object* v___y_1528_; lean_object* v___y_1529_; lean_object* v___y_1530_; lean_object* v___y_1531_; lean_object* v___y_1532_; uint8_t v___y_1533_; lean_object* v___y_1626_; lean_object* v___y_1627_; lean_object* v___y_1628_; lean_object* v___y_1629_; lean_object* v___y_1630_; lean_object* v_occs_1631_; lean_object* v___y_1632_; lean_object* v___y_1633_; lean_object* v___y_1634_; lean_object* v___y_1635_; lean_object* v___y_1636_; lean_object* v___y_1637_; lean_object* v___y_1638_; lean_object* v___y_1639_; lean_object* v___y_1654_; lean_object* v___y_1655_; lean_object* v___y_1656_; lean_object* v___y_1657_; lean_object* v___y_1658_; lean_object* v___y_1659_; lean_object* v___y_1660_; lean_object* v___y_1661_; lean_object* v___y_1662_; lean_object* v___y_1663_; lean_object* v___y_1664_; lean_object* v___y_1665_; lean_object* v___y_1666_; lean_object* v___y_1667_; lean_object* v___y_1672_; lean_object* v___y_1673_; lean_object* v___y_1674_; lean_object* v___y_1675_; lean_object* v___y_1676_; lean_object* v___y_1677_; lean_object* v___y_1678_; lean_object* v___y_1679_; lean_object* v___y_1680_; lean_object* v___y_1681_; lean_object* v___y_1682_; lean_object* v___y_1683_; lean_object* v___y_1684_; lean_object* v___y_1685_; lean_object* v___y_1690_; lean_object* v___y_1691_; lean_object* v___y_1692_; lean_object* v___y_1693_; lean_object* v___y_1694_; lean_object* v___y_1695_; lean_object* v___y_1696_; lean_object* v___y_1697_; lean_object* v___y_1698_; lean_object* v___y_1699_; lean_object* v___y_1700_; lean_object* v___y_1701_; lean_object* v___y_1702_; lean_object* v___y_1703_; lean_object* v___y_1704_; lean_object* v___y_1705_; lean_object* v___y_1706_; lean_object* v___y_1709_; lean_object* v___y_1710_; lean_object* v___y_1711_; lean_object* v___y_1712_; lean_object* v___y_1713_; lean_object* v___y_1714_; lean_object* v___y_1715_; lean_object* v___y_1716_; lean_object* v___y_1717_; lean_object* v___y_1718_; lean_object* v___y_1719_; lean_object* v___y_1720_; lean_object* v___y_1721_; lean_object* v___y_1722_; lean_object* v___y_1723_; lean_object* v___y_1724_; lean_object* v___y_1725_; lean_object* v_occs_1728_; lean_object* v___y_1729_; lean_object* v___y_1730_; lean_object* v___y_1731_; lean_object* v___y_1732_; lean_object* v___y_1733_; lean_object* v___y_1734_; lean_object* v___y_1735_; lean_object* v___y_1736_; lean_object* v___x_1822_; uint8_t v___x_1823_; 
v___x_1500_ = lean_unsigned_to_nat(0u);
v___x_1501_ = lean_unsigned_to_nat(1u);
v___x_1822_ = l_Lean_Syntax_getArg(v_stx_1394_, v___x_1501_);
v___x_1823_ = l_Lean_Syntax_isNone(v___x_1822_);
if (v___x_1823_ == 0)
{
uint8_t v___x_1824_; 
lean_inc(v___x_1822_);
v___x_1824_ = l_Lean_Syntax_matchesNull(v___x_1822_, v___x_1501_);
if (v___x_1824_ == 0)
{
lean_object* v___x_1825_; 
lean_dec(v___x_1822_);
lean_dec_ref(v___x_1398_);
lean_dec_ref(v___x_1397_);
lean_dec_ref(v___x_1396_);
lean_dec_ref(v___x_1395_);
lean_dec_ref(v___f_1392_);
v___x_1825_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg();
return v___x_1825_;
}
else
{
lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; uint8_t v___x_1829_; 
v___x_1826_ = l_Lean_Syntax_getArg(v___x_1822_, v___x_1500_);
lean_dec(v___x_1822_);
v___x_1827_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__27));
lean_inc_ref(v___x_1398_);
lean_inc_ref(v___x_1397_);
lean_inc_ref(v___x_1396_);
lean_inc_ref(v___x_1395_);
v___x_1828_ = l_Lean_Name_mkStr5(v___x_1395_, v___x_1396_, v___x_1397_, v___x_1398_, v___x_1827_);
lean_inc(v___x_1826_);
v___x_1829_ = l_Lean_Syntax_isOfKind(v___x_1826_, v___x_1828_);
lean_dec(v___x_1828_);
if (v___x_1829_ == 0)
{
lean_object* v___x_1830_; 
lean_dec(v___x_1826_);
lean_dec_ref(v___x_1398_);
lean_dec_ref(v___x_1397_);
lean_dec_ref(v___x_1396_);
lean_dec_ref(v___x_1395_);
lean_dec_ref(v___f_1392_);
v___x_1830_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg();
return v___x_1830_;
}
else
{
lean_object* v___x_1831_; lean_object* v_occs_1832_; lean_object* v___x_1833_; 
v___x_1831_ = lean_unsigned_to_nat(3u);
v_occs_1832_ = l_Lean_Syntax_getArg(v___x_1826_, v___x_1831_);
lean_dec(v___x_1826_);
v___x_1833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1833_, 0, v_occs_1832_);
v_occs_1728_ = v___x_1833_;
v___y_1729_ = v___y_1399_;
v___y_1730_ = v___y_1400_;
v___y_1731_ = v___y_1401_;
v___y_1732_ = v___y_1402_;
v___y_1733_ = v___y_1403_;
v___y_1734_ = v___y_1404_;
v___y_1735_ = v___y_1405_;
v___y_1736_ = v___y_1406_;
goto v___jp_1727_;
}
}
}
else
{
lean_object* v___x_1834_; 
lean_dec(v___x_1822_);
v___x_1834_ = lean_box(0);
v_occs_1728_ = v___x_1834_;
v___y_1729_ = v___y_1399_;
v___y_1730_ = v___y_1400_;
v___y_1731_ = v___y_1401_;
v___y_1732_ = v___y_1402_;
v___y_1733_ = v___y_1403_;
v___y_1734_ = v___y_1404_;
v___y_1735_ = v___y_1405_;
v___y_1736_ = v___y_1406_;
goto v___jp_1727_;
}
v___jp_1502_:
{
lean_object* v___x_1513_; uint8_t v___x_1514_; 
v___x_1513_ = lean_array_get_size(v___y_1503_);
v___x_1514_ = lean_nat_dec_eq(v___x_1513_, v___x_1500_);
if (v___x_1514_ == 0)
{
lean_object* v___x_1515_; uint8_t v___x_1516_; 
v___x_1515_ = lean_nat_sub(v___x_1513_, v___x_1501_);
v___x_1516_ = lean_nat_dec_le(v___x_1500_, v___x_1515_);
if (v___x_1516_ == 0)
{
lean_inc(v___x_1515_);
v___y_1485_ = v___x_1513_;
v___y_1486_ = v___y_1509_;
v___y_1487_ = v___y_1505_;
v___y_1488_ = v___y_1508_;
v___y_1489_ = v___x_1515_;
v___y_1490_ = v___y_1506_;
v___y_1491_ = v___y_1504_;
v___y_1492_ = v___y_1511_;
v___y_1493_ = v___y_1512_;
v___y_1494_ = v___y_1507_;
v___y_1495_ = v___y_1503_;
v___y_1496_ = v___y_1510_;
v___y_1497_ = v___x_1515_;
goto v___jp_1484_;
}
else
{
v___y_1485_ = v___x_1513_;
v___y_1486_ = v___y_1509_;
v___y_1487_ = v___y_1505_;
v___y_1488_ = v___y_1508_;
v___y_1489_ = v___x_1515_;
v___y_1490_ = v___y_1506_;
v___y_1491_ = v___y_1504_;
v___y_1492_ = v___y_1511_;
v___y_1493_ = v___y_1512_;
v___y_1494_ = v___y_1507_;
v___y_1495_ = v___y_1503_;
v___y_1496_ = v___y_1510_;
v___y_1497_ = v___x_1500_;
goto v___jp_1484_;
}
}
else
{
v___y_1456_ = v___y_1509_;
v___y_1457_ = v___y_1512_;
v___y_1458_ = v___y_1507_;
v___y_1459_ = v___y_1505_;
v___y_1460_ = v___y_1508_;
v___y_1461_ = v___y_1510_;
v___y_1462_ = v___y_1506_;
v___y_1463_ = v___y_1504_;
v___y_1464_ = v___y_1511_;
v___y_1465_ = v___y_1503_;
goto v___jp_1455_;
}
}
v___jp_1517_:
{
lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; 
v___x_1534_ = l_Lean_Meta_Simp_Context_setMemoize(v___y_1532_, v___y_1533_);
v___x_1535_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__6, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__6_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__6);
lean_inc(v___y_1522_);
lean_inc_ref(v___y_1528_);
v___x_1536_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre___boxed), 11, 2);
lean_closure_set(v___x_1536_, 0, v___y_1528_);
lean_closure_set(v___x_1536_, 1, v___y_1522_);
lean_inc_ref(v___y_1518_);
lean_inc_ref(v___y_1523_);
v___x_1537_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_1537_, 0, v___x_1536_);
lean_ctor_set(v___x_1537_, 1, v___y_1521_);
lean_ctor_set(v___x_1537_, 2, v___y_1523_);
lean_ctor_set(v___x_1537_, 3, v___f_1392_);
lean_ctor_set(v___x_1537_, 4, v___y_1518_);
lean_ctor_set_uint8(v___x_1537_, sizeof(void*)*5, v___x_1393_);
v___x_1538_ = l_Lean_Meta_Simp_main(v___y_1519_, v___x_1534_, v___x_1535_, v___x_1537_, v___y_1530_, v___y_1531_, v___y_1524_, v___y_1525_);
if (lean_obj_tag(v___x_1538_) == 0)
{
lean_object* v_a_1539_; lean_object* v_fst_1540_; lean_object* v___x_1542_; uint8_t v_isShared_1543_; uint8_t v_isSharedCheck_1615_; 
v_a_1539_ = lean_ctor_get(v___x_1538_, 0);
lean_inc(v_a_1539_);
lean_dec_ref_known(v___x_1538_, 1);
v_fst_1540_ = lean_ctor_get(v_a_1539_, 0);
v_isSharedCheck_1615_ = !lean_is_exclusive(v_a_1539_);
if (v_isSharedCheck_1615_ == 0)
{
lean_object* v_unused_1616_; 
v_unused_1616_ = lean_ctor_get(v_a_1539_, 1);
lean_dec(v_unused_1616_);
v___x_1542_ = v_a_1539_;
v_isShared_1543_ = v_isSharedCheck_1615_;
goto v_resetjp_1541_;
}
else
{
lean_inc(v_fst_1540_);
lean_dec(v_a_1539_);
v___x_1542_ = lean_box(0);
v_isShared_1543_ = v_isSharedCheck_1615_;
goto v_resetjp_1541_;
}
v_resetjp_1541_:
{
lean_object* v___x_1544_; 
v___x_1544_ = lean_st_ref_get(v___y_1522_);
lean_dec(v___y_1522_);
if (lean_obj_tag(v___x_1544_) == 0)
{
lean_object* v_subgoals_1545_; lean_object* v___x_1546_; uint8_t v___x_1547_; 
v_subgoals_1545_ = lean_ctor_get(v___x_1544_, 0);
lean_inc_ref(v_subgoals_1545_);
lean_dec_ref_known(v___x_1544_, 1);
v___x_1546_ = lean_array_get_size(v_subgoals_1545_);
v___x_1547_ = lean_nat_dec_eq(v___x_1546_, v___x_1500_);
if (v___x_1547_ == 0)
{
lean_del_object(v___x_1542_);
lean_dec_ref(v___y_1528_);
v___y_1409_ = v_fst_1540_;
v_subgoals_1410_ = v_subgoals_1545_;
v___y_1411_ = v___y_1526_;
v___y_1412_ = v___y_1527_;
v___y_1413_ = v___y_1529_;
v___y_1414_ = v___y_1520_;
v___y_1415_ = v___y_1530_;
v___y_1416_ = v___y_1531_;
v___y_1417_ = v___y_1524_;
v___y_1418_ = v___y_1525_;
goto v___jp_1408_;
}
else
{
lean_object* v_expr_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1552_; 
lean_dec_ref(v_subgoals_1545_);
lean_dec(v_fst_1540_);
v_expr_1548_ = lean_ctor_get(v___y_1528_, 2);
lean_inc_ref(v_expr_1548_);
lean_dec_ref(v___y_1528_);
v___x_1549_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__8, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__8_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__8);
v___x_1550_ = l_Lean_indentExpr(v_expr_1548_);
if (v_isShared_1543_ == 0)
{
lean_ctor_set_tag(v___x_1542_, 7);
lean_ctor_set(v___x_1542_, 1, v___x_1550_);
lean_ctor_set(v___x_1542_, 0, v___x_1549_);
v___x_1552_ = v___x_1542_;
goto v_reusejp_1551_;
}
else
{
lean_object* v_reuseFailAlloc_1562_; 
v_reuseFailAlloc_1562_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1562_, 0, v___x_1549_);
lean_ctor_set(v_reuseFailAlloc_1562_, 1, v___x_1550_);
v___x_1552_ = v_reuseFailAlloc_1562_;
goto v_reusejp_1551_;
}
v_reusejp_1551_:
{
lean_object* v___x_1553_; lean_object* v_a_1554_; lean_object* v___x_1556_; uint8_t v_isShared_1557_; uint8_t v_isSharedCheck_1561_; 
v___x_1553_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg(v___x_1552_, v___y_1530_, v___y_1531_, v___y_1524_, v___y_1525_);
v_a_1554_ = lean_ctor_get(v___x_1553_, 0);
v_isSharedCheck_1561_ = !lean_is_exclusive(v___x_1553_);
if (v_isSharedCheck_1561_ == 0)
{
v___x_1556_ = v___x_1553_;
v_isShared_1557_ = v_isSharedCheck_1561_;
goto v_resetjp_1555_;
}
else
{
lean_inc(v_a_1554_);
lean_dec(v___x_1553_);
v___x_1556_ = lean_box(0);
v_isShared_1557_ = v_isSharedCheck_1561_;
goto v_resetjp_1555_;
}
v_resetjp_1555_:
{
lean_object* v___x_1559_; 
if (v_isShared_1557_ == 0)
{
v___x_1559_ = v___x_1556_;
goto v_reusejp_1558_;
}
else
{
lean_object* v_reuseFailAlloc_1560_; 
v_reuseFailAlloc_1560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1560_, 0, v_a_1554_);
v___x_1559_ = v_reuseFailAlloc_1560_;
goto v_reusejp_1558_;
}
v_reusejp_1558_:
{
return v___x_1559_;
}
}
}
}
}
else
{
lean_object* v_subgoals_1563_; lean_object* v_idx_1564_; lean_object* v_remaining_1565_; uint8_t v___x_1566_; 
v_subgoals_1563_ = lean_ctor_get(v___x_1544_, 0);
lean_inc_ref(v_subgoals_1563_);
v_idx_1564_ = lean_ctor_get(v___x_1544_, 1);
lean_inc(v_idx_1564_);
v_remaining_1565_ = lean_ctor_get(v___x_1544_, 2);
lean_inc(v_remaining_1565_);
lean_dec_ref_known(v___x_1544_, 3);
v___x_1566_ = lean_nat_dec_eq(v_idx_1564_, v___x_1500_);
if (v___x_1566_ == 0)
{
lean_object* v___x_1567_; 
lean_dec_ref(v___y_1528_);
v___x_1567_ = l_List_getLast_x3f___redArg(v_remaining_1565_);
lean_dec(v_remaining_1565_);
if (lean_obj_tag(v___x_1567_) == 1)
{
lean_object* v_val_1568_; lean_object* v___x_1570_; uint8_t v_isShared_1571_; uint8_t v_isSharedCheck_1599_; 
lean_dec_ref(v_subgoals_1563_);
lean_dec(v_fst_1540_);
v_val_1568_ = lean_ctor_get(v___x_1567_, 0);
v_isSharedCheck_1599_ = !lean_is_exclusive(v___x_1567_);
if (v_isSharedCheck_1599_ == 0)
{
v___x_1570_ = v___x_1567_;
v_isShared_1571_ = v_isSharedCheck_1599_;
goto v_resetjp_1569_;
}
else
{
lean_inc(v_val_1568_);
lean_dec(v___x_1567_);
v___x_1570_ = lean_box(0);
v_isShared_1571_ = v_isSharedCheck_1599_;
goto v_resetjp_1569_;
}
v_resetjp_1569_:
{
lean_object* v_fst_1572_; lean_object* v___x_1574_; uint8_t v_isShared_1575_; uint8_t v_isSharedCheck_1597_; 
v_fst_1572_ = lean_ctor_get(v_val_1568_, 0);
v_isSharedCheck_1597_ = !lean_is_exclusive(v_val_1568_);
if (v_isSharedCheck_1597_ == 0)
{
lean_object* v_unused_1598_; 
v_unused_1598_ = lean_ctor_get(v_val_1568_, 1);
lean_dec(v_unused_1598_);
v___x_1574_ = v_val_1568_;
v_isShared_1575_ = v_isSharedCheck_1597_;
goto v_resetjp_1573_;
}
else
{
lean_inc(v_fst_1572_);
lean_dec(v_val_1568_);
v___x_1574_ = lean_box(0);
v_isShared_1575_ = v_isSharedCheck_1597_;
goto v_resetjp_1573_;
}
v_resetjp_1573_:
{
lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1579_; 
v___x_1576_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__10, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__10_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__10);
v___x_1577_ = l_Nat_reprFast(v_idx_1564_);
if (v_isShared_1571_ == 0)
{
lean_ctor_set_tag(v___x_1570_, 3);
lean_ctor_set(v___x_1570_, 0, v___x_1577_);
v___x_1579_ = v___x_1570_;
goto v_reusejp_1578_;
}
else
{
lean_object* v_reuseFailAlloc_1596_; 
v_reuseFailAlloc_1596_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1596_, 0, v___x_1577_);
v___x_1579_ = v_reuseFailAlloc_1596_;
goto v_reusejp_1578_;
}
v_reusejp_1578_:
{
lean_object* v___x_1580_; lean_object* v___x_1582_; 
v___x_1580_ = l_Lean_MessageData_ofFormat(v___x_1579_);
if (v_isShared_1575_ == 0)
{
lean_ctor_set_tag(v___x_1574_, 7);
lean_ctor_set(v___x_1574_, 1, v___x_1580_);
lean_ctor_set(v___x_1574_, 0, v___x_1576_);
v___x_1582_ = v___x_1574_;
goto v_reusejp_1581_;
}
else
{
lean_object* v_reuseFailAlloc_1595_; 
v_reuseFailAlloc_1595_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1595_, 0, v___x_1576_);
lean_ctor_set(v_reuseFailAlloc_1595_, 1, v___x_1580_);
v___x_1582_ = v_reuseFailAlloc_1595_;
goto v_reusejp_1581_;
}
v_reusejp_1581_:
{
lean_object* v___x_1583_; lean_object* v___x_1585_; 
v___x_1583_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__12, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__12_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__12);
if (v_isShared_1543_ == 0)
{
lean_ctor_set_tag(v___x_1542_, 7);
lean_ctor_set(v___x_1542_, 1, v___x_1583_);
lean_ctor_set(v___x_1542_, 0, v___x_1582_);
v___x_1585_ = v___x_1542_;
goto v_reusejp_1584_;
}
else
{
lean_object* v_reuseFailAlloc_1594_; 
v_reuseFailAlloc_1594_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1594_, 0, v___x_1582_);
lean_ctor_set(v_reuseFailAlloc_1594_, 1, v___x_1583_);
v___x_1585_ = v_reuseFailAlloc_1594_;
goto v_reusejp_1584_;
}
v_reusejp_1584_:
{
lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; 
v___x_1586_ = lean_nat_add(v_fst_1572_, v___x_1501_);
lean_dec(v_fst_1572_);
v___x_1587_ = l_Nat_reprFast(v___x_1586_);
v___x_1588_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1588_, 0, v___x_1587_);
v___x_1589_ = l_Lean_MessageData_ofFormat(v___x_1588_);
v___x_1590_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1590_, 0, v___x_1585_);
lean_ctor_set(v___x_1590_, 1, v___x_1589_);
v___x_1591_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__14, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__14_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__14);
v___x_1592_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1592_, 0, v___x_1590_);
lean_ctor_set(v___x_1592_, 1, v___x_1591_);
v___x_1593_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg(v___x_1592_, v___y_1530_, v___y_1531_, v___y_1524_, v___y_1525_);
return v___x_1593_;
}
}
}
}
}
}
else
{
lean_dec(v___x_1567_);
lean_dec(v_idx_1564_);
lean_del_object(v___x_1542_);
v___y_1503_ = v_subgoals_1563_;
v___y_1504_ = v_fst_1540_;
v___y_1505_ = v___y_1526_;
v___y_1506_ = v___y_1527_;
v___y_1507_ = v___y_1529_;
v___y_1508_ = v___y_1520_;
v___y_1509_ = v___y_1530_;
v___y_1510_ = v___y_1531_;
v___y_1511_ = v___y_1524_;
v___y_1512_ = v___y_1525_;
goto v___jp_1502_;
}
}
else
{
lean_object* v_expr_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1604_; 
lean_dec(v_remaining_1565_);
lean_dec(v_idx_1564_);
lean_dec_ref(v_subgoals_1563_);
lean_dec(v_fst_1540_);
v_expr_1600_ = lean_ctor_get(v___y_1528_, 2);
lean_inc_ref(v_expr_1600_);
lean_dec_ref(v___y_1528_);
v___x_1601_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__8, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__8_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__8);
v___x_1602_ = l_Lean_indentExpr(v_expr_1600_);
if (v_isShared_1543_ == 0)
{
lean_ctor_set_tag(v___x_1542_, 7);
lean_ctor_set(v___x_1542_, 1, v___x_1602_);
lean_ctor_set(v___x_1542_, 0, v___x_1601_);
v___x_1604_ = v___x_1542_;
goto v_reusejp_1603_;
}
else
{
lean_object* v_reuseFailAlloc_1614_; 
v_reuseFailAlloc_1614_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1614_, 0, v___x_1601_);
lean_ctor_set(v_reuseFailAlloc_1614_, 1, v___x_1602_);
v___x_1604_ = v_reuseFailAlloc_1614_;
goto v_reusejp_1603_;
}
v_reusejp_1603_:
{
lean_object* v___x_1605_; lean_object* v_a_1606_; lean_object* v___x_1608_; uint8_t v_isShared_1609_; uint8_t v_isSharedCheck_1613_; 
v___x_1605_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg(v___x_1604_, v___y_1530_, v___y_1531_, v___y_1524_, v___y_1525_);
v_a_1606_ = lean_ctor_get(v___x_1605_, 0);
v_isSharedCheck_1613_ = !lean_is_exclusive(v___x_1605_);
if (v_isSharedCheck_1613_ == 0)
{
v___x_1608_ = v___x_1605_;
v_isShared_1609_ = v_isSharedCheck_1613_;
goto v_resetjp_1607_;
}
else
{
lean_inc(v_a_1606_);
lean_dec(v___x_1605_);
v___x_1608_ = lean_box(0);
v_isShared_1609_ = v_isSharedCheck_1613_;
goto v_resetjp_1607_;
}
v_resetjp_1607_:
{
lean_object* v___x_1611_; 
if (v_isShared_1609_ == 0)
{
v___x_1611_ = v___x_1608_;
goto v_reusejp_1610_;
}
else
{
lean_object* v_reuseFailAlloc_1612_; 
v_reuseFailAlloc_1612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1612_, 0, v_a_1606_);
v___x_1611_ = v_reuseFailAlloc_1612_;
goto v_reusejp_1610_;
}
v_reusejp_1610_:
{
return v___x_1611_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1617_; lean_object* v___x_1619_; uint8_t v_isShared_1620_; uint8_t v_isSharedCheck_1624_; 
lean_dec_ref(v___y_1528_);
lean_dec(v___y_1522_);
v_a_1617_ = lean_ctor_get(v___x_1538_, 0);
v_isSharedCheck_1624_ = !lean_is_exclusive(v___x_1538_);
if (v_isSharedCheck_1624_ == 0)
{
v___x_1619_ = v___x_1538_;
v_isShared_1620_ = v_isSharedCheck_1624_;
goto v_resetjp_1618_;
}
else
{
lean_inc(v_a_1617_);
lean_dec(v___x_1538_);
v___x_1619_ = lean_box(0);
v_isShared_1620_ = v_isSharedCheck_1624_;
goto v_resetjp_1618_;
}
v_resetjp_1618_:
{
lean_object* v___x_1622_; 
if (v_isShared_1620_ == 0)
{
v___x_1622_ = v___x_1619_;
goto v_reusejp_1621_;
}
else
{
lean_object* v_reuseFailAlloc_1623_; 
v_reuseFailAlloc_1623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1623_, 0, v_a_1617_);
v___x_1622_ = v_reuseFailAlloc_1623_;
goto v_reusejp_1621_;
}
v_reusejp_1621_:
{
return v___x_1622_;
}
}
}
}
v___jp_1625_:
{
lean_object* v___x_1640_; lean_object* v___x_1641_; 
lean_inc_ref(v_occs_1631_);
v___x_1640_ = lean_st_mk_ref(v_occs_1631_);
v___x_1641_ = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_getContext___redArg(v___y_1636_, v___y_1638_, v___y_1639_);
if (lean_obj_tag(v___x_1641_) == 0)
{
if (lean_obj_tag(v_occs_1631_) == 0)
{
lean_object* v_a_1642_; 
lean_dec_ref_known(v_occs_1631_, 1);
v_a_1642_ = lean_ctor_get(v___x_1641_, 0);
lean_inc(v_a_1642_);
lean_dec_ref_known(v___x_1641_, 1);
v___y_1518_ = v___y_1627_;
v___y_1519_ = v___y_1626_;
v___y_1520_ = v___y_1635_;
v___y_1521_ = v___y_1628_;
v___y_1522_ = v___x_1640_;
v___y_1523_ = v___y_1629_;
v___y_1524_ = v___y_1638_;
v___y_1525_ = v___y_1639_;
v___y_1526_ = v___y_1632_;
v___y_1527_ = v___y_1633_;
v___y_1528_ = v___y_1630_;
v___y_1529_ = v___y_1634_;
v___y_1530_ = v___y_1636_;
v___y_1531_ = v___y_1637_;
v___y_1532_ = v_a_1642_;
v___y_1533_ = v___x_1393_;
goto v___jp_1517_;
}
else
{
lean_object* v_a_1643_; uint8_t v___x_1644_; 
lean_dec_ref(v_occs_1631_);
v_a_1643_ = lean_ctor_get(v___x_1641_, 0);
lean_inc(v_a_1643_);
lean_dec_ref_known(v___x_1641_, 1);
v___x_1644_ = 0;
v___y_1518_ = v___y_1627_;
v___y_1519_ = v___y_1626_;
v___y_1520_ = v___y_1635_;
v___y_1521_ = v___y_1628_;
v___y_1522_ = v___x_1640_;
v___y_1523_ = v___y_1629_;
v___y_1524_ = v___y_1638_;
v___y_1525_ = v___y_1639_;
v___y_1526_ = v___y_1632_;
v___y_1527_ = v___y_1633_;
v___y_1528_ = v___y_1630_;
v___y_1529_ = v___y_1634_;
v___y_1530_ = v___y_1636_;
v___y_1531_ = v___y_1637_;
v___y_1532_ = v_a_1643_;
v___y_1533_ = v___x_1644_;
goto v___jp_1517_;
}
}
else
{
lean_object* v_a_1645_; lean_object* v___x_1647_; uint8_t v_isShared_1648_; uint8_t v_isSharedCheck_1652_; 
lean_dec(v___x_1640_);
lean_dec_ref(v_occs_1631_);
lean_dec_ref(v___y_1630_);
lean_dec_ref(v___y_1628_);
lean_dec_ref(v___y_1626_);
lean_dec_ref(v___f_1392_);
v_a_1645_ = lean_ctor_get(v___x_1641_, 0);
v_isSharedCheck_1652_ = !lean_is_exclusive(v___x_1641_);
if (v_isSharedCheck_1652_ == 0)
{
v___x_1647_ = v___x_1641_;
v_isShared_1648_ = v_isSharedCheck_1652_;
goto v_resetjp_1646_;
}
else
{
lean_inc(v_a_1645_);
lean_dec(v___x_1641_);
v___x_1647_ = lean_box(0);
v_isShared_1648_ = v_isSharedCheck_1652_;
goto v_resetjp_1646_;
}
v_resetjp_1646_:
{
lean_object* v___x_1650_; 
if (v_isShared_1648_ == 0)
{
v___x_1650_ = v___x_1647_;
goto v_reusejp_1649_;
}
else
{
lean_object* v_reuseFailAlloc_1651_; 
v_reuseFailAlloc_1651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1651_, 0, v_a_1645_);
v___x_1650_ = v_reuseFailAlloc_1651_;
goto v_reusejp_1649_;
}
v_reusejp_1649_:
{
return v___x_1650_;
}
}
}
}
v___jp_1653_:
{
lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; 
v___x_1668_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__15));
v___x_1669_ = lean_array_to_list(v___y_1656_);
v___x_1670_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1670_, 0, v___x_1668_);
lean_ctor_set(v___x_1670_, 1, v___x_1500_);
lean_ctor_set(v___x_1670_, 2, v___x_1669_);
v___y_1626_ = v___y_1655_;
v___y_1627_ = v___y_1654_;
v___y_1628_ = v___y_1657_;
v___y_1629_ = v___y_1658_;
v___y_1630_ = v___y_1659_;
v_occs_1631_ = v___x_1670_;
v___y_1632_ = v___y_1660_;
v___y_1633_ = v___y_1661_;
v___y_1634_ = v___y_1662_;
v___y_1635_ = v___y_1663_;
v___y_1636_ = v___y_1664_;
v___y_1637_ = v___y_1665_;
v___y_1638_ = v___y_1666_;
v___y_1639_ = v___y_1667_;
goto v___jp_1625_;
}
v___jp_1671_:
{
uint8_t v___x_1686_; 
v___x_1686_ = l_Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8(v___y_1685_);
if (v___x_1686_ == 0)
{
lean_object* v___x_1687_; lean_object* v___x_1688_; 
lean_dec_ref(v___y_1685_);
lean_dec_ref(v___y_1680_);
lean_dec_ref(v___y_1675_);
lean_dec_ref(v___y_1674_);
lean_dec_ref(v___f_1392_);
v___x_1687_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__17, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__17_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__17);
v___x_1688_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg(v___x_1687_, v___y_1679_, v___y_1676_, v___y_1682_, v___y_1683_);
return v___x_1688_;
}
else
{
v___y_1654_ = v___y_1673_;
v___y_1655_ = v___y_1674_;
v___y_1656_ = v___y_1685_;
v___y_1657_ = v___y_1675_;
v___y_1658_ = v___y_1677_;
v___y_1659_ = v___y_1680_;
v___y_1660_ = v___y_1672_;
v___y_1661_ = v___y_1684_;
v___y_1662_ = v___y_1678_;
v___y_1663_ = v___y_1681_;
v___y_1664_ = v___y_1679_;
v___y_1665_ = v___y_1676_;
v___y_1666_ = v___y_1682_;
v___y_1667_ = v___y_1683_;
goto v___jp_1653_;
}
}
v___jp_1689_:
{
lean_object* v___x_1707_; 
v___x_1707_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg(v___y_1690_, v___y_1698_, v___y_1694_, v___y_1706_);
lean_dec(v___y_1706_);
lean_dec(v___y_1690_);
v___y_1672_ = v___y_1691_;
v___y_1673_ = v___y_1692_;
v___y_1674_ = v___y_1693_;
v___y_1675_ = v___y_1695_;
v___y_1676_ = v___y_1696_;
v___y_1677_ = v___y_1697_;
v___y_1678_ = v___y_1699_;
v___y_1679_ = v___y_1700_;
v___y_1680_ = v___y_1701_;
v___y_1681_ = v___y_1702_;
v___y_1682_ = v___y_1703_;
v___y_1683_ = v___y_1704_;
v___y_1684_ = v___y_1705_;
v___y_1685_ = v___x_1707_;
goto v___jp_1671_;
}
v___jp_1708_:
{
uint8_t v___x_1726_; 
v___x_1726_ = lean_nat_dec_le(v___y_1725_, v___y_1713_);
if (v___x_1726_ == 0)
{
lean_dec(v___y_1713_);
lean_inc(v___y_1725_);
v___y_1690_ = v___y_1709_;
v___y_1691_ = v___y_1710_;
v___y_1692_ = v___y_1711_;
v___y_1693_ = v___y_1712_;
v___y_1694_ = v___y_1725_;
v___y_1695_ = v___y_1714_;
v___y_1696_ = v___y_1715_;
v___y_1697_ = v___y_1716_;
v___y_1698_ = v___y_1717_;
v___y_1699_ = v___y_1718_;
v___y_1700_ = v___y_1719_;
v___y_1701_ = v___y_1720_;
v___y_1702_ = v___y_1721_;
v___y_1703_ = v___y_1722_;
v___y_1704_ = v___y_1723_;
v___y_1705_ = v___y_1724_;
v___y_1706_ = v___y_1725_;
goto v___jp_1689_;
}
else
{
v___y_1690_ = v___y_1709_;
v___y_1691_ = v___y_1710_;
v___y_1692_ = v___y_1711_;
v___y_1693_ = v___y_1712_;
v___y_1694_ = v___y_1725_;
v___y_1695_ = v___y_1714_;
v___y_1696_ = v___y_1715_;
v___y_1697_ = v___y_1716_;
v___y_1698_ = v___y_1717_;
v___y_1699_ = v___y_1718_;
v___y_1700_ = v___y_1719_;
v___y_1701_ = v___y_1720_;
v___y_1702_ = v___y_1721_;
v___y_1703_ = v___y_1722_;
v___y_1704_ = v___y_1723_;
v___y_1705_ = v___y_1724_;
v___y_1706_ = v___y_1713_;
goto v___jp_1689_;
}
}
v___jp_1727_:
{
lean_object* v_declName_x3f_1737_; lean_object* v_macroStack_1738_; uint8_t v_mayPostpone_1739_; uint8_t v_errToSorry_1740_; lean_object* v_autoBoundImplicitContext_1741_; lean_object* v_autoBoundImplicitForbidden_1742_; lean_object* v_sectionVars_1743_; lean_object* v_sectionFVars_1744_; uint8_t v_implicitLambda_1745_; uint8_t v_heedElabAsElim_1746_; uint8_t v_isNoncomputableSection_1747_; uint8_t v_isMetaSection_1748_; uint8_t v_inPattern_1749_; lean_object* v_tacSnap_x3f_1750_; uint8_t v_saveRecAppSyntax_1751_; uint8_t v_holesAsSyntheticOpaque_1752_; uint8_t v_checkDeprecated_1753_; lean_object* v_fixedTermElabs_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___f_1759_; lean_object* v___f_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; 
v_declName_x3f_1737_ = lean_ctor_get(v___y_1731_, 0);
v_macroStack_1738_ = lean_ctor_get(v___y_1731_, 1);
v_mayPostpone_1739_ = lean_ctor_get_uint8(v___y_1731_, sizeof(void*)*8);
v_errToSorry_1740_ = lean_ctor_get_uint8(v___y_1731_, sizeof(void*)*8 + 1);
v_autoBoundImplicitContext_1741_ = lean_ctor_get(v___y_1731_, 2);
v_autoBoundImplicitForbidden_1742_ = lean_ctor_get(v___y_1731_, 3);
v_sectionVars_1743_ = lean_ctor_get(v___y_1731_, 4);
v_sectionFVars_1744_ = lean_ctor_get(v___y_1731_, 5);
v_implicitLambda_1745_ = lean_ctor_get_uint8(v___y_1731_, sizeof(void*)*8 + 2);
v_heedElabAsElim_1746_ = lean_ctor_get_uint8(v___y_1731_, sizeof(void*)*8 + 3);
v_isNoncomputableSection_1747_ = lean_ctor_get_uint8(v___y_1731_, sizeof(void*)*8 + 4);
v_isMetaSection_1748_ = lean_ctor_get_uint8(v___y_1731_, sizeof(void*)*8 + 5);
v_inPattern_1749_ = lean_ctor_get_uint8(v___y_1731_, sizeof(void*)*8 + 7);
v_tacSnap_x3f_1750_ = lean_ctor_get(v___y_1731_, 6);
v_saveRecAppSyntax_1751_ = lean_ctor_get_uint8(v___y_1731_, sizeof(void*)*8 + 8);
v_holesAsSyntheticOpaque_1752_ = lean_ctor_get_uint8(v___y_1731_, sizeof(void*)*8 + 9);
v_checkDeprecated_1753_ = lean_ctor_get_uint8(v___y_1731_, sizeof(void*)*8 + 10);
v_fixedTermElabs_1754_ = lean_ctor_get(v___y_1731_, 7);
v___x_1755_ = lean_unsigned_to_nat(2u);
v___x_1756_ = l_Lean_Syntax_getArg(v_stx_1394_, v___x_1755_);
v___x_1757_ = lean_box(0);
v___x_1758_ = lean_box(v___x_1393_);
lean_inc(v___x_1756_);
v___f_1759_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__1___boxed), 10, 3);
lean_closure_set(v___f_1759_, 0, v___x_1756_);
lean_closure_set(v___f_1759_, 1, v___x_1757_);
lean_closure_set(v___f_1759_, 2, v___x_1758_);
v___f_1760_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__2___boxed), 9, 2);
lean_closure_set(v___f_1760_, 0, v___x_1756_);
lean_closure_set(v___f_1760_, 1, v___f_1759_);
lean_inc_ref(v_fixedTermElabs_1754_);
lean_inc(v_tacSnap_x3f_1750_);
lean_inc(v_sectionFVars_1744_);
lean_inc(v_sectionVars_1743_);
lean_inc_ref(v_autoBoundImplicitForbidden_1742_);
lean_inc(v_autoBoundImplicitContext_1741_);
lean_inc(v_macroStack_1738_);
lean_inc(v_declName_x3f_1737_);
v___x_1761_ = lean_alloc_ctor(0, 8, 11);
lean_ctor_set(v___x_1761_, 0, v_declName_x3f_1737_);
lean_ctor_set(v___x_1761_, 1, v_macroStack_1738_);
lean_ctor_set(v___x_1761_, 2, v_autoBoundImplicitContext_1741_);
lean_ctor_set(v___x_1761_, 3, v_autoBoundImplicitForbidden_1742_);
lean_ctor_set(v___x_1761_, 4, v_sectionVars_1743_);
lean_ctor_set(v___x_1761_, 5, v_sectionFVars_1744_);
lean_ctor_set(v___x_1761_, 6, v_tacSnap_x3f_1750_);
lean_ctor_set(v___x_1761_, 7, v_fixedTermElabs_1754_);
lean_ctor_set_uint8(v___x_1761_, sizeof(void*)*8, v_mayPostpone_1739_);
lean_ctor_set_uint8(v___x_1761_, sizeof(void*)*8 + 1, v_errToSorry_1740_);
lean_ctor_set_uint8(v___x_1761_, sizeof(void*)*8 + 2, v_implicitLambda_1745_);
lean_ctor_set_uint8(v___x_1761_, sizeof(void*)*8 + 3, v_heedElabAsElim_1746_);
lean_ctor_set_uint8(v___x_1761_, sizeof(void*)*8 + 4, v_isNoncomputableSection_1747_);
lean_ctor_set_uint8(v___x_1761_, sizeof(void*)*8 + 5, v_isMetaSection_1748_);
lean_ctor_set_uint8(v___x_1761_, sizeof(void*)*8 + 6, v___x_1393_);
lean_ctor_set_uint8(v___x_1761_, sizeof(void*)*8 + 7, v_inPattern_1749_);
lean_ctor_set_uint8(v___x_1761_, sizeof(void*)*8 + 8, v_saveRecAppSyntax_1751_);
lean_ctor_set_uint8(v___x_1761_, sizeof(void*)*8 + 9, v_holesAsSyntheticOpaque_1752_);
lean_ctor_set_uint8(v___x_1761_, sizeof(void*)*8 + 10, v_checkDeprecated_1753_);
v___x_1762_ = l_Lean_Elab_Term_withoutModifyingElabMetaStateWithInfo___redArg(v___f_1760_, v___x_1761_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_);
lean_dec_ref_known(v___x_1761_, 8);
if (lean_obj_tag(v___x_1762_) == 0)
{
lean_object* v_a_1763_; lean_object* v___x_1764_; 
v_a_1763_ = lean_ctor_get(v___x_1762_, 0);
lean_inc(v_a_1763_);
lean_dec_ref_known(v___x_1762_, 1);
v___x_1764_ = l_Lean_Elab_Tactic_Conv_getLhs___redArg(v___y_1730_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_);
if (lean_obj_tag(v___x_1764_) == 0)
{
lean_object* v_a_1765_; lean_object* v___x_1766_; lean_object* v___f_1767_; lean_object* v___f_1768_; lean_object* v___f_1769_; 
v_a_1765_ = lean_ctor_get(v___x_1764_, 0);
lean_inc(v_a_1765_);
lean_dec_ref_known(v___x_1764_, 1);
v___x_1766_ = lean_box(v___x_1393_);
v___f_1767_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__3___boxed), 11, 2);
lean_closure_set(v___f_1767_, 0, v___x_1757_);
lean_closure_set(v___f_1767_, 1, v___x_1766_);
v___f_1768_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__18));
v___f_1769_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__19));
if (lean_obj_tag(v_occs_1728_) == 0)
{
lean_object* v___x_1770_; 
lean_dec_ref(v___x_1398_);
lean_dec_ref(v___x_1397_);
lean_dec_ref(v___x_1396_);
lean_dec_ref(v___x_1395_);
v___x_1770_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__22));
v___y_1626_ = v_a_1765_;
v___y_1627_ = v___f_1769_;
v___y_1628_ = v___f_1767_;
v___y_1629_ = v___f_1768_;
v___y_1630_ = v_a_1763_;
v_occs_1631_ = v___x_1770_;
v___y_1632_ = v___y_1729_;
v___y_1633_ = v___y_1730_;
v___y_1634_ = v___y_1731_;
v___y_1635_ = v___y_1732_;
v___y_1636_ = v___y_1733_;
v___y_1637_ = v___y_1734_;
v___y_1638_ = v___y_1735_;
v___y_1639_ = v___y_1736_;
goto v___jp_1625_;
}
else
{
lean_object* v_val_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; uint8_t v___x_1774_; 
v_val_1771_ = lean_ctor_get(v_occs_1728_, 0);
lean_inc_n(v_val_1771_, 2);
lean_dec_ref_known(v_occs_1728_, 1);
v___x_1772_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__23));
lean_inc_ref(v___x_1398_);
lean_inc_ref(v___x_1397_);
lean_inc_ref(v___x_1396_);
lean_inc_ref(v___x_1395_);
v___x_1773_ = l_Lean_Name_mkStr5(v___x_1395_, v___x_1396_, v___x_1397_, v___x_1398_, v___x_1772_);
v___x_1774_ = l_Lean_Syntax_isOfKind(v_val_1771_, v___x_1773_);
lean_dec(v___x_1773_);
if (v___x_1774_ == 0)
{
lean_object* v___x_1775_; lean_object* v___x_1776_; uint8_t v___x_1777_; 
v___x_1775_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__24));
v___x_1776_ = l_Lean_Name_mkStr5(v___x_1395_, v___x_1396_, v___x_1397_, v___x_1398_, v___x_1775_);
lean_inc(v_val_1771_);
v___x_1777_ = l_Lean_Syntax_isOfKind(v_val_1771_, v___x_1776_);
lean_dec(v___x_1776_);
if (v___x_1777_ == 0)
{
lean_object* v___x_1778_; lean_object* v_a_1779_; lean_object* v___x_1781_; uint8_t v_isShared_1782_; uint8_t v_isSharedCheck_1786_; 
lean_dec(v_val_1771_);
lean_dec_ref(v___f_1767_);
lean_dec(v_a_1765_);
lean_dec(v_a_1763_);
lean_dec_ref(v___f_1392_);
v___x_1778_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg();
v_a_1779_ = lean_ctor_get(v___x_1778_, 0);
v_isSharedCheck_1786_ = !lean_is_exclusive(v___x_1778_);
if (v_isSharedCheck_1786_ == 0)
{
v___x_1781_ = v___x_1778_;
v_isShared_1782_ = v_isSharedCheck_1786_;
goto v_resetjp_1780_;
}
else
{
lean_inc(v_a_1779_);
lean_dec(v___x_1778_);
v___x_1781_ = lean_box(0);
v_isShared_1782_ = v_isSharedCheck_1786_;
goto v_resetjp_1780_;
}
v_resetjp_1780_:
{
lean_object* v___x_1784_; 
if (v_isShared_1782_ == 0)
{
v___x_1784_ = v___x_1781_;
goto v_reusejp_1783_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v_a_1779_);
v___x_1784_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1783_;
}
v_reusejp_1783_:
{
return v___x_1784_;
}
}
}
else
{
lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; 
v___x_1787_ = l_Lean_Syntax_getArg(v_val_1771_, v___x_1500_);
lean_dec(v_val_1771_);
v___x_1788_ = l_Lean_Syntax_getArgs(v___x_1787_);
lean_dec(v___x_1787_);
v___x_1789_ = lean_array_get_size(v___x_1788_);
v___x_1790_ = lean_mk_empty_array_with_capacity(v___x_1789_);
v___x_1791_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg(v___x_1788_, v___x_1789_, v___x_1500_, v___x_1790_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_);
lean_dec_ref(v___x_1788_);
if (lean_obj_tag(v___x_1791_) == 0)
{
lean_object* v_a_1792_; lean_object* v___x_1793_; uint8_t v___x_1794_; 
v_a_1792_ = lean_ctor_get(v___x_1791_, 0);
lean_inc(v_a_1792_);
lean_dec_ref_known(v___x_1791_, 1);
v___x_1793_ = lean_array_get_size(v_a_1792_);
v___x_1794_ = lean_nat_dec_eq(v___x_1793_, v___x_1500_);
if (v___x_1794_ == 0)
{
lean_object* v___x_1795_; uint8_t v___x_1796_; 
v___x_1795_ = lean_nat_sub(v___x_1793_, v___x_1501_);
v___x_1796_ = lean_nat_dec_le(v___x_1500_, v___x_1795_);
if (v___x_1796_ == 0)
{
lean_inc(v___x_1795_);
v___y_1709_ = v___x_1793_;
v___y_1710_ = v___y_1729_;
v___y_1711_ = v___f_1769_;
v___y_1712_ = v_a_1765_;
v___y_1713_ = v___x_1795_;
v___y_1714_ = v___f_1767_;
v___y_1715_ = v___y_1734_;
v___y_1716_ = v___f_1768_;
v___y_1717_ = v_a_1792_;
v___y_1718_ = v___y_1731_;
v___y_1719_ = v___y_1733_;
v___y_1720_ = v_a_1763_;
v___y_1721_ = v___y_1732_;
v___y_1722_ = v___y_1735_;
v___y_1723_ = v___y_1736_;
v___y_1724_ = v___y_1730_;
v___y_1725_ = v___x_1795_;
goto v___jp_1708_;
}
else
{
v___y_1709_ = v___x_1793_;
v___y_1710_ = v___y_1729_;
v___y_1711_ = v___f_1769_;
v___y_1712_ = v_a_1765_;
v___y_1713_ = v___x_1795_;
v___y_1714_ = v___f_1767_;
v___y_1715_ = v___y_1734_;
v___y_1716_ = v___f_1768_;
v___y_1717_ = v_a_1792_;
v___y_1718_ = v___y_1731_;
v___y_1719_ = v___y_1733_;
v___y_1720_ = v_a_1763_;
v___y_1721_ = v___y_1732_;
v___y_1722_ = v___y_1735_;
v___y_1723_ = v___y_1736_;
v___y_1724_ = v___y_1730_;
v___y_1725_ = v___x_1500_;
goto v___jp_1708_;
}
}
else
{
v___y_1672_ = v___y_1729_;
v___y_1673_ = v___f_1769_;
v___y_1674_ = v_a_1765_;
v___y_1675_ = v___f_1767_;
v___y_1676_ = v___y_1734_;
v___y_1677_ = v___f_1768_;
v___y_1678_ = v___y_1731_;
v___y_1679_ = v___y_1733_;
v___y_1680_ = v_a_1763_;
v___y_1681_ = v___y_1732_;
v___y_1682_ = v___y_1735_;
v___y_1683_ = v___y_1736_;
v___y_1684_ = v___y_1730_;
v___y_1685_ = v_a_1792_;
goto v___jp_1671_;
}
}
else
{
lean_object* v_a_1797_; lean_object* v___x_1799_; uint8_t v_isShared_1800_; uint8_t v_isSharedCheck_1804_; 
lean_dec_ref(v___f_1767_);
lean_dec(v_a_1765_);
lean_dec(v_a_1763_);
lean_dec_ref(v___f_1392_);
v_a_1797_ = lean_ctor_get(v___x_1791_, 0);
v_isSharedCheck_1804_ = !lean_is_exclusive(v___x_1791_);
if (v_isSharedCheck_1804_ == 0)
{
v___x_1799_ = v___x_1791_;
v_isShared_1800_ = v_isSharedCheck_1804_;
goto v_resetjp_1798_;
}
else
{
lean_inc(v_a_1797_);
lean_dec(v___x_1791_);
v___x_1799_ = lean_box(0);
v_isShared_1800_ = v_isSharedCheck_1804_;
goto v_resetjp_1798_;
}
v_resetjp_1798_:
{
lean_object* v___x_1802_; 
if (v_isShared_1800_ == 0)
{
v___x_1802_ = v___x_1799_;
goto v_reusejp_1801_;
}
else
{
lean_object* v_reuseFailAlloc_1803_; 
v_reuseFailAlloc_1803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1803_, 0, v_a_1797_);
v___x_1802_ = v_reuseFailAlloc_1803_;
goto v_reusejp_1801_;
}
v_reusejp_1801_:
{
return v___x_1802_;
}
}
}
}
}
else
{
lean_object* v___x_1805_; 
lean_dec(v_val_1771_);
lean_dec_ref(v___x_1398_);
lean_dec_ref(v___x_1397_);
lean_dec_ref(v___x_1396_);
lean_dec_ref(v___x_1395_);
v___x_1805_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__26));
v___y_1626_ = v_a_1765_;
v___y_1627_ = v___f_1769_;
v___y_1628_ = v___f_1767_;
v___y_1629_ = v___f_1768_;
v___y_1630_ = v_a_1763_;
v_occs_1631_ = v___x_1805_;
v___y_1632_ = v___y_1729_;
v___y_1633_ = v___y_1730_;
v___y_1634_ = v___y_1731_;
v___y_1635_ = v___y_1732_;
v___y_1636_ = v___y_1733_;
v___y_1637_ = v___y_1734_;
v___y_1638_ = v___y_1735_;
v___y_1639_ = v___y_1736_;
goto v___jp_1625_;
}
}
}
else
{
lean_object* v_a_1806_; lean_object* v___x_1808_; uint8_t v_isShared_1809_; uint8_t v_isSharedCheck_1813_; 
lean_dec(v_a_1763_);
lean_dec(v_occs_1728_);
lean_dec_ref(v___x_1398_);
lean_dec_ref(v___x_1397_);
lean_dec_ref(v___x_1396_);
lean_dec_ref(v___x_1395_);
lean_dec_ref(v___f_1392_);
v_a_1806_ = lean_ctor_get(v___x_1764_, 0);
v_isSharedCheck_1813_ = !lean_is_exclusive(v___x_1764_);
if (v_isSharedCheck_1813_ == 0)
{
v___x_1808_ = v___x_1764_;
v_isShared_1809_ = v_isSharedCheck_1813_;
goto v_resetjp_1807_;
}
else
{
lean_inc(v_a_1806_);
lean_dec(v___x_1764_);
v___x_1808_ = lean_box(0);
v_isShared_1809_ = v_isSharedCheck_1813_;
goto v_resetjp_1807_;
}
v_resetjp_1807_:
{
lean_object* v___x_1811_; 
if (v_isShared_1809_ == 0)
{
v___x_1811_ = v___x_1808_;
goto v_reusejp_1810_;
}
else
{
lean_object* v_reuseFailAlloc_1812_; 
v_reuseFailAlloc_1812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1812_, 0, v_a_1806_);
v___x_1811_ = v_reuseFailAlloc_1812_;
goto v_reusejp_1810_;
}
v_reusejp_1810_:
{
return v___x_1811_;
}
}
}
}
else
{
lean_object* v_a_1814_; lean_object* v___x_1816_; uint8_t v_isShared_1817_; uint8_t v_isSharedCheck_1821_; 
lean_dec(v_occs_1728_);
lean_dec_ref(v___x_1398_);
lean_dec_ref(v___x_1397_);
lean_dec_ref(v___x_1396_);
lean_dec_ref(v___x_1395_);
lean_dec_ref(v___f_1392_);
v_a_1814_ = lean_ctor_get(v___x_1762_, 0);
v_isSharedCheck_1821_ = !lean_is_exclusive(v___x_1762_);
if (v_isSharedCheck_1821_ == 0)
{
v___x_1816_ = v___x_1762_;
v_isShared_1817_ = v_isSharedCheck_1821_;
goto v_resetjp_1815_;
}
else
{
lean_inc(v_a_1814_);
lean_dec(v___x_1762_);
v___x_1816_ = lean_box(0);
v_isShared_1817_ = v_isSharedCheck_1821_;
goto v_resetjp_1815_;
}
v_resetjp_1815_:
{
lean_object* v___x_1819_; 
if (v_isShared_1817_ == 0)
{
v___x_1819_ = v___x_1816_;
goto v_reusejp_1818_;
}
else
{
lean_object* v_reuseFailAlloc_1820_; 
v_reuseFailAlloc_1820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1820_, 0, v_a_1814_);
v___x_1819_ = v_reuseFailAlloc_1820_;
goto v_reusejp_1818_;
}
v_reusejp_1818_:
{
return v___x_1819_;
}
}
}
}
}
v___jp_1408_:
{
lean_object* v___x_1419_; 
v___x_1419_ = l_Lean_Elab_Tactic_Conv_getRhs___redArg(v___y_1412_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_);
if (lean_obj_tag(v___x_1419_) == 0)
{
lean_object* v_a_1420_; lean_object* v_expr_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; 
v_a_1420_ = lean_ctor_get(v___x_1419_, 0);
lean_inc(v_a_1420_);
lean_dec_ref_known(v___x_1419_, 1);
v_expr_1421_ = lean_ctor_get(v___y_1409_, 0);
v___x_1422_ = l_Lean_Expr_mvarId_x21(v_a_1420_);
lean_dec(v_a_1420_);
lean_inc_ref(v_expr_1421_);
v___x_1423_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3___redArg(v___x_1422_, v_expr_1421_, v___y_1416_);
lean_dec_ref(v___x_1423_);
v___x_1424_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_1412_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_);
if (lean_obj_tag(v___x_1424_) == 0)
{
lean_object* v_a_1425_; lean_object* v___x_1426_; 
v_a_1425_ = lean_ctor_get(v___x_1424_, 0);
lean_inc(v_a_1425_);
lean_dec_ref_known(v___x_1424_, 1);
v___x_1426_ = l_Lean_Meta_Simp_Result_getProof(v___y_1409_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_);
if (lean_obj_tag(v___x_1426_) == 0)
{
lean_object* v_a_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; 
v_a_1427_ = lean_ctor_get(v___x_1426_, 0);
lean_inc(v_a_1427_);
lean_dec_ref_known(v___x_1426_, 1);
v___x_1428_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3___redArg(v_a_1425_, v_a_1427_, v___y_1416_);
lean_dec_ref(v___x_1428_);
v___x_1429_ = lean_array_to_list(v_subgoals_1410_);
v___x_1430_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_1429_, v___y_1412_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_);
return v___x_1430_;
}
else
{
lean_object* v_a_1431_; lean_object* v___x_1433_; uint8_t v_isShared_1434_; uint8_t v_isSharedCheck_1438_; 
lean_dec(v_a_1425_);
lean_dec_ref(v_subgoals_1410_);
v_a_1431_ = lean_ctor_get(v___x_1426_, 0);
v_isSharedCheck_1438_ = !lean_is_exclusive(v___x_1426_);
if (v_isSharedCheck_1438_ == 0)
{
v___x_1433_ = v___x_1426_;
v_isShared_1434_ = v_isSharedCheck_1438_;
goto v_resetjp_1432_;
}
else
{
lean_inc(v_a_1431_);
lean_dec(v___x_1426_);
v___x_1433_ = lean_box(0);
v_isShared_1434_ = v_isSharedCheck_1438_;
goto v_resetjp_1432_;
}
v_resetjp_1432_:
{
lean_object* v___x_1436_; 
if (v_isShared_1434_ == 0)
{
v___x_1436_ = v___x_1433_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v_a_1431_);
v___x_1436_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1435_;
}
v_reusejp_1435_:
{
return v___x_1436_;
}
}
}
}
else
{
lean_object* v_a_1439_; lean_object* v___x_1441_; uint8_t v_isShared_1442_; uint8_t v_isSharedCheck_1446_; 
lean_dec_ref(v_subgoals_1410_);
lean_dec_ref(v___y_1409_);
v_a_1439_ = lean_ctor_get(v___x_1424_, 0);
v_isSharedCheck_1446_ = !lean_is_exclusive(v___x_1424_);
if (v_isSharedCheck_1446_ == 0)
{
v___x_1441_ = v___x_1424_;
v_isShared_1442_ = v_isSharedCheck_1446_;
goto v_resetjp_1440_;
}
else
{
lean_inc(v_a_1439_);
lean_dec(v___x_1424_);
v___x_1441_ = lean_box(0);
v_isShared_1442_ = v_isSharedCheck_1446_;
goto v_resetjp_1440_;
}
v_resetjp_1440_:
{
lean_object* v___x_1444_; 
if (v_isShared_1442_ == 0)
{
v___x_1444_ = v___x_1441_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v_a_1439_);
v___x_1444_ = v_reuseFailAlloc_1445_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
return v___x_1444_;
}
}
}
}
else
{
lean_object* v_a_1447_; lean_object* v___x_1449_; uint8_t v_isShared_1450_; uint8_t v_isSharedCheck_1454_; 
lean_dec_ref(v_subgoals_1410_);
lean_dec_ref(v___y_1409_);
v_a_1447_ = lean_ctor_get(v___x_1419_, 0);
v_isSharedCheck_1454_ = !lean_is_exclusive(v___x_1419_);
if (v_isSharedCheck_1454_ == 0)
{
v___x_1449_ = v___x_1419_;
v_isShared_1450_ = v_isSharedCheck_1454_;
goto v_resetjp_1448_;
}
else
{
lean_inc(v_a_1447_);
lean_dec(v___x_1419_);
v___x_1449_ = lean_box(0);
v_isShared_1450_ = v_isSharedCheck_1454_;
goto v_resetjp_1448_;
}
v_resetjp_1448_:
{
lean_object* v___x_1452_; 
if (v_isShared_1450_ == 0)
{
v___x_1452_ = v___x_1449_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v_a_1447_);
v___x_1452_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
return v___x_1452_;
}
}
}
}
v___jp_1455_:
{
size_t v_sz_1466_; size_t v___x_1467_; lean_object* v___x_1468_; 
v_sz_1466_ = lean_array_size(v___y_1465_);
v___x_1467_ = ((size_t)0ULL);
v___x_1468_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__5(v_sz_1466_, v___x_1467_, v___y_1465_);
v___y_1409_ = v___y_1463_;
v_subgoals_1410_ = v___x_1468_;
v___y_1411_ = v___y_1459_;
v___y_1412_ = v___y_1462_;
v___y_1413_ = v___y_1458_;
v___y_1414_ = v___y_1460_;
v___y_1415_ = v___y_1456_;
v___y_1416_ = v___y_1461_;
v___y_1417_ = v___y_1464_;
v___y_1418_ = v___y_1457_;
goto v___jp_1408_;
}
v___jp_1469_:
{
lean_object* v___x_1483_; 
v___x_1483_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg(v___y_1470_, v___y_1480_, v___y_1477_, v___y_1482_);
lean_dec(v___y_1482_);
lean_dec(v___y_1470_);
v___y_1456_ = v___y_1471_;
v___y_1457_ = v___y_1478_;
v___y_1458_ = v___y_1479_;
v___y_1459_ = v___y_1472_;
v___y_1460_ = v___y_1473_;
v___y_1461_ = v___y_1481_;
v___y_1462_ = v___y_1474_;
v___y_1463_ = v___y_1475_;
v___y_1464_ = v___y_1476_;
v___y_1465_ = v___x_1483_;
goto v___jp_1455_;
}
v___jp_1484_:
{
uint8_t v___x_1498_; 
v___x_1498_ = lean_nat_dec_le(v___y_1497_, v___y_1489_);
if (v___x_1498_ == 0)
{
lean_dec(v___y_1489_);
lean_inc(v___y_1497_);
v___y_1470_ = v___y_1485_;
v___y_1471_ = v___y_1486_;
v___y_1472_ = v___y_1487_;
v___y_1473_ = v___y_1488_;
v___y_1474_ = v___y_1490_;
v___y_1475_ = v___y_1491_;
v___y_1476_ = v___y_1492_;
v___y_1477_ = v___y_1497_;
v___y_1478_ = v___y_1493_;
v___y_1479_ = v___y_1494_;
v___y_1480_ = v___y_1495_;
v___y_1481_ = v___y_1496_;
v___y_1482_ = v___y_1497_;
goto v___jp_1469_;
}
else
{
v___y_1470_ = v___y_1485_;
v___y_1471_ = v___y_1486_;
v___y_1472_ = v___y_1487_;
v___y_1473_ = v___y_1488_;
v___y_1474_ = v___y_1490_;
v___y_1475_ = v___y_1491_;
v___y_1476_ = v___y_1492_;
v___y_1477_ = v___y_1497_;
v___y_1478_ = v___y_1493_;
v___y_1479_ = v___y_1494_;
v___y_1480_ = v___y_1495_;
v___y_1481_ = v___y_1496_;
v___y_1482_ = v___y_1489_;
goto v___jp_1469_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___boxed(lean_object** _args){
lean_object* v___x_1835_ = _args[0];
lean_object* v___f_1836_ = _args[1];
lean_object* v___x_1837_ = _args[2];
lean_object* v_stx_1838_ = _args[3];
lean_object* v___x_1839_ = _args[4];
lean_object* v___x_1840_ = _args[5];
lean_object* v___x_1841_ = _args[6];
lean_object* v___x_1842_ = _args[7];
lean_object* v___y_1843_ = _args[8];
lean_object* v___y_1844_ = _args[9];
lean_object* v___y_1845_ = _args[10];
lean_object* v___y_1846_ = _args[11];
lean_object* v___y_1847_ = _args[12];
lean_object* v___y_1848_ = _args[13];
lean_object* v___y_1849_ = _args[14];
lean_object* v___y_1850_ = _args[15];
lean_object* v___y_1851_ = _args[16];
_start:
{
uint8_t v___x_19478__boxed_1852_; uint8_t v___x_19480__boxed_1853_; lean_object* v_res_1854_; 
v___x_19478__boxed_1852_ = lean_unbox(v___x_1835_);
v___x_19480__boxed_1853_ = lean_unbox(v___x_1837_);
v_res_1854_ = l_Lean_Elab_Tactic_Conv_evalPattern___lam__6(v___x_19478__boxed_1852_, v___f_1836_, v___x_19480__boxed_1853_, v_stx_1838_, v___x_1839_, v___x_1840_, v___x_1841_, v___x_1842_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_, v___y_1850_);
lean_dec(v___y_1850_);
lean_dec_ref(v___y_1849_);
lean_dec(v___y_1848_);
lean_dec_ref(v___y_1847_);
lean_dec(v___y_1846_);
lean_dec_ref(v___y_1845_);
lean_dec(v___y_1844_);
lean_dec_ref(v___y_1843_);
lean_dec(v_stx_1838_);
return v_res_1854_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern(lean_object* v_stx_1867_, lean_object* v_a_1868_, lean_object* v_a_1869_, lean_object* v_a_1870_, lean_object* v_a_1871_, lean_object* v_a_1872_, lean_object* v_a_1873_, lean_object* v_a_1874_, lean_object* v_a_1875_){
_start:
{
lean_object* v___f_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; uint8_t v___x_1883_; uint8_t v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___y_1887_; lean_object* v___x_1888_; 
v___f_1877_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___closed__0));
v___x_1878_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___closed__1));
v___x_1879_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___closed__2));
v___x_1880_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___closed__3));
v___x_1881_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___closed__4));
v___x_1882_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___closed__6));
lean_inc(v_stx_1867_);
v___x_1883_ = l_Lean_Syntax_isOfKind(v_stx_1867_, v___x_1882_);
v___x_1884_ = 1;
v___x_1885_ = lean_box(v___x_1883_);
v___x_1886_ = lean_box(v___x_1884_);
v___y_1887_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___boxed), 17, 8);
lean_closure_set(v___y_1887_, 0, v___x_1885_);
lean_closure_set(v___y_1887_, 1, v___f_1877_);
lean_closure_set(v___y_1887_, 2, v___x_1886_);
lean_closure_set(v___y_1887_, 3, v_stx_1867_);
lean_closure_set(v___y_1887_, 4, v___x_1878_);
lean_closure_set(v___y_1887_, 5, v___x_1879_);
lean_closure_set(v___y_1887_, 6, v___x_1880_);
lean_closure_set(v___y_1887_, 7, v___x_1881_);
v___x_1888_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___y_1887_, v_a_1868_, v_a_1869_, v_a_1870_, v_a_1871_, v_a_1872_, v_a_1873_, v_a_1874_, v_a_1875_);
return v___x_1888_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___boxed(lean_object* v_stx_1889_, lean_object* v_a_1890_, lean_object* v_a_1891_, lean_object* v_a_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_, lean_object* v_a_1896_, lean_object* v_a_1897_, lean_object* v_a_1898_){
_start:
{
lean_object* v_res_1899_; 
v_res_1899_ = l_Lean_Elab_Tactic_Conv_evalPattern(v_stx_1889_, v_a_1890_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_, v_a_1896_, v_a_1897_);
lean_dec(v_a_1897_);
lean_dec_ref(v_a_1896_);
lean_dec(v_a_1895_);
lean_dec_ref(v_a_1894_);
lean_dec(v_a_1893_);
lean_dec_ref(v_a_1892_);
lean_dec(v_a_1891_);
lean_dec_ref(v_a_1890_);
return v_res_1899_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1(lean_object* v_00_u03b1_1900_, lean_object* v_ref_1901_, lean_object* v_msg_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_){
_start:
{
lean_object* v___x_1912_; 
v___x_1912_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1___redArg(v_ref_1901_, v_msg_1902_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_);
return v___x_1912_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1___boxed(lean_object* v_00_u03b1_1913_, lean_object* v_ref_1914_, lean_object* v_msg_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_){
_start:
{
lean_object* v_res_1925_; 
v_res_1925_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1(v_00_u03b1_1913_, v_ref_1914_, v_msg_1915_, v___y_1916_, v___y_1917_, v___y_1918_, v___y_1919_, v___y_1920_, v___y_1921_, v___y_1922_, v___y_1923_);
lean_dec(v___y_1923_);
lean_dec_ref(v___y_1922_);
lean_dec(v___y_1921_);
lean_dec_ref(v___y_1920_);
lean_dec(v___y_1919_);
lean_dec_ref(v___y_1918_);
lean_dec(v___y_1917_);
lean_dec_ref(v___y_1916_);
lean_dec(v_ref_1914_);
return v_res_1925_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3(lean_object* v_mvarId_1926_, lean_object* v_val_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_){
_start:
{
lean_object* v___x_1937_; 
v___x_1937_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3___redArg(v_mvarId_1926_, v_val_1927_, v___y_1933_);
return v___x_1937_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3___boxed(lean_object* v_mvarId_1938_, lean_object* v_val_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_){
_start:
{
lean_object* v_res_1949_; 
v_res_1949_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3(v_mvarId_1938_, v_val_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_);
lean_dec(v___y_1947_);
lean_dec_ref(v___y_1946_);
lean_dec(v___y_1945_);
lean_dec_ref(v___y_1944_);
lean_dec(v___y_1943_);
lean_dec_ref(v___y_1942_);
lean_dec(v___y_1941_);
lean_dec_ref(v___y_1940_);
return v_res_1949_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4(lean_object* v_00_u03b1_1950_, lean_object* v_msg_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_){
_start:
{
lean_object* v___x_1961_; 
v___x_1961_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg(v_msg_1951_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_);
return v___x_1961_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___boxed(lean_object* v_00_u03b1_1962_, lean_object* v_msg_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_){
_start:
{
lean_object* v_res_1973_; 
v_res_1973_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4(v_00_u03b1_1962_, v_msg_1963_, v___y_1964_, v___y_1965_, v___y_1966_, v___y_1967_, v___y_1968_, v___y_1969_, v___y_1970_, v___y_1971_);
lean_dec(v___y_1971_);
lean_dec_ref(v___y_1970_);
lean_dec(v___y_1969_);
lean_dec_ref(v___y_1968_);
lean_dec(v___y_1967_);
lean_dec_ref(v___y_1966_);
lean_dec(v___y_1965_);
lean_dec_ref(v___y_1964_);
return v_res_1973_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6(lean_object* v_n_1974_, lean_object* v_as_1975_, lean_object* v_lo_1976_, lean_object* v_hi_1977_, lean_object* v_w_1978_, lean_object* v_hlo_1979_, lean_object* v_hhi_1980_){
_start:
{
lean_object* v___x_1981_; 
v___x_1981_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg(v_n_1974_, v_as_1975_, v_lo_1976_, v_hi_1977_);
return v___x_1981_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___boxed(lean_object* v_n_1982_, lean_object* v_as_1983_, lean_object* v_lo_1984_, lean_object* v_hi_1985_, lean_object* v_w_1986_, lean_object* v_hlo_1987_, lean_object* v_hhi_1988_){
_start:
{
lean_object* v_res_1989_; 
v_res_1989_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6(v_n_1982_, v_as_1983_, v_lo_1984_, v_hi_1985_, v_w_1986_, v_hlo_1987_, v_hhi_1988_);
lean_dec(v_hi_1985_);
lean_dec(v_n_1982_);
return v_res_1989_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7(lean_object* v_as_1990_, lean_object* v_i_1991_, lean_object* v_j_1992_, lean_object* v_inv_1993_, lean_object* v_bs_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_){
_start:
{
lean_object* v___x_2004_; 
v___x_2004_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg(v_as_1990_, v_i_1991_, v_j_1992_, v_bs_1994_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_);
return v___x_2004_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___boxed(lean_object* v_as_2005_, lean_object* v_i_2006_, lean_object* v_j_2007_, lean_object* v_inv_2008_, lean_object* v_bs_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_){
_start:
{
lean_object* v_res_2019_; 
v_res_2019_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7(v_as_2005_, v_i_2006_, v_j_2007_, v_inv_2008_, v_bs_2009_, v___y_2010_, v___y_2011_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_);
lean_dec(v___y_2017_);
lean_dec_ref(v___y_2016_);
lean_dec(v___y_2015_);
lean_dec_ref(v___y_2014_);
lean_dec(v___y_2013_);
lean_dec_ref(v___y_2012_);
lean_dec(v___y_2011_);
lean_dec_ref(v___y_2010_);
lean_dec_ref(v_as_2005_);
return v_res_2019_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9(lean_object* v_n_2020_, lean_object* v_as_2021_, lean_object* v_lo_2022_, lean_object* v_hi_2023_, lean_object* v_w_2024_, lean_object* v_hlo_2025_, lean_object* v_hhi_2026_){
_start:
{
lean_object* v___x_2027_; 
v___x_2027_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg(v_n_2020_, v_as_2021_, v_lo_2022_, v_hi_2023_);
return v___x_2027_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___boxed(lean_object* v_n_2028_, lean_object* v_as_2029_, lean_object* v_lo_2030_, lean_object* v_hi_2031_, lean_object* v_w_2032_, lean_object* v_hlo_2033_, lean_object* v_hhi_2034_){
_start:
{
lean_object* v_res_2035_; 
v_res_2035_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9(v_n_2028_, v_as_2029_, v_lo_2030_, v_hi_2031_, v_w_2032_, v_hlo_2033_, v_hhi_2034_);
lean_dec(v_hi_2031_);
lean_dec(v_n_2028_);
return v_res_2035_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3(lean_object* v_00_u03b2_2036_, lean_object* v_x_2037_, lean_object* v_x_2038_, lean_object* v_x_2039_){
_start:
{
lean_object* v___x_2040_; 
v___x_2040_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3___redArg(v_x_2037_, v_x_2038_, v_x_2039_);
return v___x_2040_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6_spec__8(lean_object* v_n_2041_, lean_object* v_lo_2042_, lean_object* v_hi_2043_, lean_object* v_hhi_2044_, lean_object* v_pivot_2045_, lean_object* v_as_2046_, lean_object* v_i_2047_, lean_object* v_k_2048_, lean_object* v_ilo_2049_, lean_object* v_ik_2050_, lean_object* v_w_2051_){
_start:
{
lean_object* v___x_2052_; 
v___x_2052_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6_spec__8___redArg(v_hi_2043_, v_pivot_2045_, v_as_2046_, v_i_2047_, v_k_2048_);
return v___x_2052_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6_spec__8___boxed(lean_object* v_n_2053_, lean_object* v_lo_2054_, lean_object* v_hi_2055_, lean_object* v_hhi_2056_, lean_object* v_pivot_2057_, lean_object* v_as_2058_, lean_object* v_i_2059_, lean_object* v_k_2060_, lean_object* v_ilo_2061_, lean_object* v_ik_2062_, lean_object* v_w_2063_){
_start:
{
lean_object* v_res_2064_; 
v_res_2064_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6_spec__8(v_n_2053_, v_lo_2054_, v_hi_2055_, v_hhi_2056_, v_pivot_2057_, v_as_2058_, v_i_2059_, v_k_2060_, v_ilo_2061_, v_ik_2062_, v_w_2063_);
lean_dec_ref(v_pivot_2057_);
lean_dec(v_hi_2055_);
lean_dec(v_lo_2054_);
lean_dec(v_n_2053_);
return v_res_2064_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9_spec__13(lean_object* v_n_2065_, lean_object* v_lo_2066_, lean_object* v_hi_2067_, lean_object* v_hhi_2068_, lean_object* v_pivot_2069_, lean_object* v_as_2070_, lean_object* v_i_2071_, lean_object* v_k_2072_, lean_object* v_ilo_2073_, lean_object* v_ik_2074_, lean_object* v_w_2075_){
_start:
{
lean_object* v___x_2076_; 
v___x_2076_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9_spec__13___redArg(v_hi_2067_, v_pivot_2069_, v_as_2070_, v_i_2071_, v_k_2072_);
return v___x_2076_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9_spec__13___boxed(lean_object* v_n_2077_, lean_object* v_lo_2078_, lean_object* v_hi_2079_, lean_object* v_hhi_2080_, lean_object* v_pivot_2081_, lean_object* v_as_2082_, lean_object* v_i_2083_, lean_object* v_k_2084_, lean_object* v_ilo_2085_, lean_object* v_ik_2086_, lean_object* v_w_2087_){
_start:
{
lean_object* v_res_2088_; 
v_res_2088_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9_spec__13(v_n_2077_, v_lo_2078_, v_hi_2079_, v_hhi_2080_, v_pivot_2081_, v_as_2082_, v_i_2083_, v_k_2084_, v_ilo_2085_, v_ik_2086_, v_w_2087_);
lean_dec_ref(v_pivot_2081_);
lean_dec(v_hi_2079_);
lean_dec(v_lo_2078_);
lean_dec(v_n_2077_);
return v_res_2088_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4(lean_object* v_00_u03b2_2089_, lean_object* v_x_2090_, size_t v_x_2091_, size_t v_x_2092_, lean_object* v_x_2093_, lean_object* v_x_2094_){
_start:
{
lean_object* v___x_2095_; 
v___x_2095_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg(v_x_2090_, v_x_2091_, v_x_2092_, v_x_2093_, v_x_2094_);
return v___x_2095_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___boxed(lean_object* v_00_u03b2_2096_, lean_object* v_x_2097_, lean_object* v_x_2098_, lean_object* v_x_2099_, lean_object* v_x_2100_, lean_object* v_x_2101_){
_start:
{
size_t v_x_20596__boxed_2102_; size_t v_x_20597__boxed_2103_; lean_object* v_res_2104_; 
v_x_20596__boxed_2102_ = lean_unbox_usize(v_x_2098_);
lean_dec(v_x_2098_);
v_x_20597__boxed_2103_ = lean_unbox_usize(v_x_2099_);
lean_dec(v_x_2099_);
v_res_2104_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4(v_00_u03b2_2096_, v_x_2097_, v_x_20596__boxed_2102_, v_x_20597__boxed_2103_, v_x_2100_, v_x_2101_);
return v_res_2104_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11_spec__13(lean_object* v_as_2105_, lean_object* v_a_2106_, lean_object* v_x_2107_, lean_object* v_x_2108_){
_start:
{
uint8_t v___x_2109_; 
v___x_2109_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11_spec__13___redArg(v_as_2105_, v_a_2106_, v_x_2107_);
return v___x_2109_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11_spec__13___boxed(lean_object* v_as_2110_, lean_object* v_a_2111_, lean_object* v_x_2112_, lean_object* v_x_2113_){
_start:
{
uint8_t v_res_2114_; lean_object* v_r_2115_; 
v_res_2114_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11_spec__13(v_as_2110_, v_a_2111_, v_x_2112_, v_x_2113_);
lean_dec_ref(v_a_2111_);
lean_dec_ref(v_as_2110_);
v_r_2115_ = lean_box(v_res_2114_);
return v_r_2115_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__12(lean_object* v_00_u03b2_2116_, lean_object* v_n_2117_, lean_object* v_k_2118_, lean_object* v_v_2119_){
_start:
{
lean_object* v___x_2120_; 
v___x_2120_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__12___redArg(v_n_2117_, v_k_2118_, v_v_2119_);
return v___x_2120_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__13(lean_object* v_00_u03b2_2121_, size_t v_depth_2122_, lean_object* v_keys_2123_, lean_object* v_vals_2124_, lean_object* v_heq_2125_, lean_object* v_i_2126_, lean_object* v_entries_2127_){
_start:
{
lean_object* v___x_2128_; 
v___x_2128_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__13___redArg(v_depth_2122_, v_keys_2123_, v_vals_2124_, v_i_2126_, v_entries_2127_);
return v___x_2128_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__13___boxed(lean_object* v_00_u03b2_2129_, lean_object* v_depth_2130_, lean_object* v_keys_2131_, lean_object* v_vals_2132_, lean_object* v_heq_2133_, lean_object* v_i_2134_, lean_object* v_entries_2135_){
_start:
{
size_t v_depth_boxed_2136_; lean_object* v_res_2137_; 
v_depth_boxed_2136_ = lean_unbox_usize(v_depth_2130_);
lean_dec(v_depth_2130_);
v_res_2137_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__13(v_00_u03b2_2129_, v_depth_boxed_2136_, v_keys_2131_, v_vals_2132_, v_heq_2133_, v_i_2134_, v_entries_2135_);
lean_dec_ref(v_vals_2132_);
lean_dec_ref(v_keys_2131_);
return v_res_2137_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__12_spec__16(lean_object* v_00_u03b2_2138_, lean_object* v_x_2139_, lean_object* v_x_2140_, lean_object* v_x_2141_, lean_object* v_x_2142_){
_start:
{
lean_object* v___x_2143_; 
v___x_2143_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__12_spec__16___redArg(v_x_2139_, v_x_2140_, v_x_2141_, v_x_2142_);
return v___x_2143_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1(){
_start:
{
lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; 
v___x_2153_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2154_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___closed__6));
v___x_2155_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___closed__2));
v___x_2156_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalPattern___boxed), 10, 0);
v___x_2157_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2153_, v___x_2154_, v___x_2155_, v___x_2156_);
return v___x_2157_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___boxed(lean_object* v_a_2158_){
_start:
{
lean_object* v_res_2159_; 
v_res_2159_ = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1();
return v_res_2159_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3(){
_start:
{
lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; 
v___x_2186_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___closed__2));
v___x_2187_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__6));
v___x_2188_ = l_Lean_addBuiltinDeclarationRanges(v___x_2186_, v___x_2187_);
return v___x_2188_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___boxed(lean_object* v_a_2189_){
_start:
{
lean_object* v_res_2190_; 
v_res_2190_ = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3();
return v_res_2190_;
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
