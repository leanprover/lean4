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
size_t lean_usize_sub(size_t, size_t);
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
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__0;
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
uint8_t v___x_18446__boxed_667_; lean_object* v_res_668_; 
v___x_18446__boxed_667_ = lean_unbox(v___x_659_);
v_res_668_ = l_Lean_Elab_Tactic_Conv_evalPattern___lam__1(v___x_657_, v___x_658_, v___x_18446__boxed_667_, v___y_660_, v___y_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_);
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
uint8_t v___x_18540__boxed_738_; lean_object* v_res_739_; 
v___x_18540__boxed_738_ = lean_unbox(v___x_728_);
v_res_739_ = l_Lean_Elab_Tactic_Conv_evalPattern___lam__3(v___x_727_, v___x_18540__boxed_738_, v_e_729_, v___y_730_, v___y_731_, v___y_732_, v___y_733_, v___y_734_, v___y_735_, v___y_736_);
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
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_959_; 
v___x_959_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_959_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg(lean_object* v_x_960_, size_t v_x_961_, size_t v_x_962_, lean_object* v_x_963_, lean_object* v_x_964_){
_start:
{
if (lean_obj_tag(v_x_960_) == 0)
{
lean_object* v_es_965_; size_t v___x_966_; size_t v___x_967_; lean_object* v_j_968_; lean_object* v___x_969_; uint8_t v___x_970_; 
v_es_965_ = lean_ctor_get(v_x_960_, 0);
v___x_966_ = ((size_t)31ULL);
v___x_967_ = lean_usize_land(v_x_961_, v___x_966_);
v_j_968_ = lean_usize_to_nat(v___x_967_);
v___x_969_ = lean_array_get_size(v_es_965_);
v___x_970_ = lean_nat_dec_lt(v_j_968_, v___x_969_);
if (v___x_970_ == 0)
{
lean_dec(v_j_968_);
lean_dec(v_x_964_);
lean_dec(v_x_963_);
return v_x_960_;
}
else
{
lean_object* v___x_972_; uint8_t v_isShared_973_; uint8_t v_isSharedCheck_1009_; 
lean_inc_ref(v_es_965_);
v_isSharedCheck_1009_ = !lean_is_exclusive(v_x_960_);
if (v_isSharedCheck_1009_ == 0)
{
lean_object* v_unused_1010_; 
v_unused_1010_ = lean_ctor_get(v_x_960_, 0);
lean_dec(v_unused_1010_);
v___x_972_ = v_x_960_;
v_isShared_973_ = v_isSharedCheck_1009_;
goto v_resetjp_971_;
}
else
{
lean_dec(v_x_960_);
v___x_972_ = lean_box(0);
v_isShared_973_ = v_isSharedCheck_1009_;
goto v_resetjp_971_;
}
v_resetjp_971_:
{
lean_object* v_v_974_; lean_object* v___x_975_; lean_object* v_xs_x27_976_; lean_object* v___y_978_; 
v_v_974_ = lean_array_fget(v_es_965_, v_j_968_);
v___x_975_ = lean_box(0);
v_xs_x27_976_ = lean_array_fset(v_es_965_, v_j_968_, v___x_975_);
switch(lean_obj_tag(v_v_974_))
{
case 0:
{
lean_object* v_key_983_; lean_object* v_val_984_; lean_object* v___x_986_; uint8_t v_isShared_987_; uint8_t v_isSharedCheck_994_; 
v_key_983_ = lean_ctor_get(v_v_974_, 0);
v_val_984_ = lean_ctor_get(v_v_974_, 1);
v_isSharedCheck_994_ = !lean_is_exclusive(v_v_974_);
if (v_isSharedCheck_994_ == 0)
{
v___x_986_ = v_v_974_;
v_isShared_987_ = v_isSharedCheck_994_;
goto v_resetjp_985_;
}
else
{
lean_inc(v_val_984_);
lean_inc(v_key_983_);
lean_dec(v_v_974_);
v___x_986_ = lean_box(0);
v_isShared_987_ = v_isSharedCheck_994_;
goto v_resetjp_985_;
}
v_resetjp_985_:
{
uint8_t v___x_988_; 
v___x_988_ = l_Lean_instBEqMVarId_beq(v_x_963_, v_key_983_);
if (v___x_988_ == 0)
{
lean_object* v___x_989_; lean_object* v___x_990_; 
lean_del_object(v___x_986_);
v___x_989_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_983_, v_val_984_, v_x_963_, v_x_964_);
v___x_990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_990_, 0, v___x_989_);
v___y_978_ = v___x_990_;
goto v___jp_977_;
}
else
{
lean_object* v___x_992_; 
lean_dec(v_val_984_);
lean_dec(v_key_983_);
if (v_isShared_987_ == 0)
{
lean_ctor_set(v___x_986_, 1, v_x_964_);
lean_ctor_set(v___x_986_, 0, v_x_963_);
v___x_992_ = v___x_986_;
goto v_reusejp_991_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v_x_963_);
lean_ctor_set(v_reuseFailAlloc_993_, 1, v_x_964_);
v___x_992_ = v_reuseFailAlloc_993_;
goto v_reusejp_991_;
}
v_reusejp_991_:
{
v___y_978_ = v___x_992_;
goto v___jp_977_;
}
}
}
}
case 1:
{
lean_object* v_node_995_; lean_object* v___x_997_; uint8_t v_isShared_998_; uint8_t v_isSharedCheck_1007_; 
v_node_995_ = lean_ctor_get(v_v_974_, 0);
v_isSharedCheck_1007_ = !lean_is_exclusive(v_v_974_);
if (v_isSharedCheck_1007_ == 0)
{
v___x_997_ = v_v_974_;
v_isShared_998_ = v_isSharedCheck_1007_;
goto v_resetjp_996_;
}
else
{
lean_inc(v_node_995_);
lean_dec(v_v_974_);
v___x_997_ = lean_box(0);
v_isShared_998_ = v_isSharedCheck_1007_;
goto v_resetjp_996_;
}
v_resetjp_996_:
{
size_t v___x_999_; size_t v___x_1000_; size_t v___x_1001_; size_t v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1005_; 
v___x_999_ = ((size_t)5ULL);
v___x_1000_ = lean_usize_shift_right(v_x_961_, v___x_999_);
v___x_1001_ = ((size_t)1ULL);
v___x_1002_ = lean_usize_add(v_x_962_, v___x_1001_);
v___x_1003_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg(v_node_995_, v___x_1000_, v___x_1002_, v_x_963_, v_x_964_);
if (v_isShared_998_ == 0)
{
lean_ctor_set(v___x_997_, 0, v___x_1003_);
v___x_1005_ = v___x_997_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1006_; 
v_reuseFailAlloc_1006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1006_, 0, v___x_1003_);
v___x_1005_ = v_reuseFailAlloc_1006_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
v___y_978_ = v___x_1005_;
goto v___jp_977_;
}
}
}
default: 
{
lean_object* v___x_1008_; 
v___x_1008_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1008_, 0, v_x_963_);
lean_ctor_set(v___x_1008_, 1, v_x_964_);
v___y_978_ = v___x_1008_;
goto v___jp_977_;
}
}
v___jp_977_:
{
lean_object* v___x_979_; lean_object* v___x_981_; 
v___x_979_ = lean_array_fset(v_xs_x27_976_, v_j_968_, v___y_978_);
lean_dec(v_j_968_);
if (v_isShared_973_ == 0)
{
lean_ctor_set(v___x_972_, 0, v___x_979_);
v___x_981_ = v___x_972_;
goto v_reusejp_980_;
}
else
{
lean_object* v_reuseFailAlloc_982_; 
v_reuseFailAlloc_982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_982_, 0, v___x_979_);
v___x_981_ = v_reuseFailAlloc_982_;
goto v_reusejp_980_;
}
v_reusejp_980_:
{
return v___x_981_;
}
}
}
}
}
else
{
lean_object* v_ks_1011_; lean_object* v_vs_1012_; lean_object* v___x_1014_; uint8_t v_isShared_1015_; uint8_t v_isSharedCheck_1032_; 
v_ks_1011_ = lean_ctor_get(v_x_960_, 0);
v_vs_1012_ = lean_ctor_get(v_x_960_, 1);
v_isSharedCheck_1032_ = !lean_is_exclusive(v_x_960_);
if (v_isSharedCheck_1032_ == 0)
{
v___x_1014_ = v_x_960_;
v_isShared_1015_ = v_isSharedCheck_1032_;
goto v_resetjp_1013_;
}
else
{
lean_inc(v_vs_1012_);
lean_inc(v_ks_1011_);
lean_dec(v_x_960_);
v___x_1014_ = lean_box(0);
v_isShared_1015_ = v_isSharedCheck_1032_;
goto v_resetjp_1013_;
}
v_resetjp_1013_:
{
lean_object* v___x_1017_; 
if (v_isShared_1015_ == 0)
{
v___x_1017_ = v___x_1014_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1031_; 
v_reuseFailAlloc_1031_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1031_, 0, v_ks_1011_);
lean_ctor_set(v_reuseFailAlloc_1031_, 1, v_vs_1012_);
v___x_1017_ = v_reuseFailAlloc_1031_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
lean_object* v_newNode_1018_; uint8_t v___y_1020_; size_t v___x_1026_; uint8_t v___x_1027_; 
v_newNode_1018_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__12___redArg(v___x_1017_, v_x_963_, v_x_964_);
v___x_1026_ = ((size_t)7ULL);
v___x_1027_ = lean_usize_dec_le(v___x_1026_, v_x_962_);
if (v___x_1027_ == 0)
{
lean_object* v___x_1028_; lean_object* v___x_1029_; uint8_t v___x_1030_; 
v___x_1028_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1018_);
v___x_1029_ = lean_unsigned_to_nat(4u);
v___x_1030_ = lean_nat_dec_lt(v___x_1028_, v___x_1029_);
lean_dec(v___x_1028_);
v___y_1020_ = v___x_1030_;
goto v___jp_1019_;
}
else
{
v___y_1020_ = v___x_1027_;
goto v___jp_1019_;
}
v___jp_1019_:
{
if (v___y_1020_ == 0)
{
lean_object* v_ks_1021_; lean_object* v_vs_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; 
v_ks_1021_ = lean_ctor_get(v_newNode_1018_, 0);
lean_inc_ref(v_ks_1021_);
v_vs_1022_ = lean_ctor_get(v_newNode_1018_, 1);
lean_inc_ref(v_vs_1022_);
lean_dec_ref(v_newNode_1018_);
v___x_1023_ = lean_unsigned_to_nat(0u);
v___x_1024_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__0);
v___x_1025_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__13___redArg(v_x_962_, v_ks_1021_, v_vs_1022_, v___x_1023_, v___x_1024_);
lean_dec_ref(v_vs_1022_);
lean_dec_ref(v_ks_1021_);
return v___x_1025_;
}
else
{
return v_newNode_1018_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__13___redArg(size_t v_depth_1033_, lean_object* v_keys_1034_, lean_object* v_vals_1035_, lean_object* v_i_1036_, lean_object* v_entries_1037_){
_start:
{
lean_object* v___x_1038_; uint8_t v___x_1039_; 
v___x_1038_ = lean_array_get_size(v_keys_1034_);
v___x_1039_ = lean_nat_dec_lt(v_i_1036_, v___x_1038_);
if (v___x_1039_ == 0)
{
lean_dec(v_i_1036_);
return v_entries_1037_;
}
else
{
lean_object* v_k_1040_; lean_object* v_v_1041_; uint64_t v___x_1042_; size_t v_h_1043_; size_t v___x_1044_; lean_object* v___x_1045_; size_t v___x_1046_; size_t v___x_1047_; size_t v___x_1048_; size_t v_h_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; 
v_k_1040_ = lean_array_fget_borrowed(v_keys_1034_, v_i_1036_);
v_v_1041_ = lean_array_fget_borrowed(v_vals_1035_, v_i_1036_);
v___x_1042_ = l_Lean_instHashableMVarId_hash(v_k_1040_);
v_h_1043_ = lean_uint64_to_usize(v___x_1042_);
v___x_1044_ = ((size_t)5ULL);
v___x_1045_ = lean_unsigned_to_nat(1u);
v___x_1046_ = ((size_t)1ULL);
v___x_1047_ = lean_usize_sub(v_depth_1033_, v___x_1046_);
v___x_1048_ = lean_usize_mul(v___x_1044_, v___x_1047_);
v_h_1049_ = lean_usize_shift_right(v_h_1043_, v___x_1048_);
v___x_1050_ = lean_nat_add(v_i_1036_, v___x_1045_);
lean_dec(v_i_1036_);
lean_inc(v_v_1041_);
lean_inc(v_k_1040_);
v___x_1051_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg(v_entries_1037_, v_h_1049_, v_depth_1033_, v_k_1040_, v_v_1041_);
v_i_1036_ = v___x_1050_;
v_entries_1037_ = v___x_1051_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__13___redArg___boxed(lean_object* v_depth_1053_, lean_object* v_keys_1054_, lean_object* v_vals_1055_, lean_object* v_i_1056_, lean_object* v_entries_1057_){
_start:
{
size_t v_depth_boxed_1058_; lean_object* v_res_1059_; 
v_depth_boxed_1058_ = lean_unbox_usize(v_depth_1053_);
lean_dec(v_depth_1053_);
v_res_1059_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__13___redArg(v_depth_boxed_1058_, v_keys_1054_, v_vals_1055_, v_i_1056_, v_entries_1057_);
lean_dec_ref(v_vals_1055_);
lean_dec_ref(v_keys_1054_);
return v_res_1059_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___boxed(lean_object* v_x_1060_, lean_object* v_x_1061_, lean_object* v_x_1062_, lean_object* v_x_1063_, lean_object* v_x_1064_){
_start:
{
size_t v_x_18883__boxed_1065_; size_t v_x_18884__boxed_1066_; lean_object* v_res_1067_; 
v_x_18883__boxed_1065_ = lean_unbox_usize(v_x_1061_);
lean_dec(v_x_1061_);
v_x_18884__boxed_1066_ = lean_unbox_usize(v_x_1062_);
lean_dec(v_x_1062_);
v_res_1067_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg(v_x_1060_, v_x_18883__boxed_1065_, v_x_18884__boxed_1066_, v_x_1063_, v_x_1064_);
return v_res_1067_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3___redArg(lean_object* v_x_1068_, lean_object* v_x_1069_, lean_object* v_x_1070_){
_start:
{
uint64_t v___x_1071_; size_t v___x_1072_; size_t v___x_1073_; lean_object* v___x_1074_; 
v___x_1071_ = l_Lean_instHashableMVarId_hash(v_x_1069_);
v___x_1072_ = lean_uint64_to_usize(v___x_1071_);
v___x_1073_ = ((size_t)1ULL);
v___x_1074_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg(v_x_1068_, v___x_1072_, v___x_1073_, v_x_1069_, v_x_1070_);
return v___x_1074_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3___redArg(lean_object* v_mvarId_1075_, lean_object* v_val_1076_, lean_object* v___y_1077_){
_start:
{
lean_object* v___x_1079_; lean_object* v_mctx_1080_; lean_object* v_cache_1081_; lean_object* v_zetaDeltaFVarIds_1082_; lean_object* v_postponed_1083_; lean_object* v_diag_1084_; lean_object* v___x_1086_; uint8_t v_isShared_1087_; uint8_t v_isSharedCheck_1112_; 
v___x_1079_ = lean_st_ref_take(v___y_1077_);
v_mctx_1080_ = lean_ctor_get(v___x_1079_, 0);
v_cache_1081_ = lean_ctor_get(v___x_1079_, 1);
v_zetaDeltaFVarIds_1082_ = lean_ctor_get(v___x_1079_, 2);
v_postponed_1083_ = lean_ctor_get(v___x_1079_, 3);
v_diag_1084_ = lean_ctor_get(v___x_1079_, 4);
v_isSharedCheck_1112_ = !lean_is_exclusive(v___x_1079_);
if (v_isSharedCheck_1112_ == 0)
{
v___x_1086_ = v___x_1079_;
v_isShared_1087_ = v_isSharedCheck_1112_;
goto v_resetjp_1085_;
}
else
{
lean_inc(v_diag_1084_);
lean_inc(v_postponed_1083_);
lean_inc(v_zetaDeltaFVarIds_1082_);
lean_inc(v_cache_1081_);
lean_inc(v_mctx_1080_);
lean_dec(v___x_1079_);
v___x_1086_ = lean_box(0);
v_isShared_1087_ = v_isSharedCheck_1112_;
goto v_resetjp_1085_;
}
v_resetjp_1085_:
{
lean_object* v_depth_1088_; lean_object* v_levelAssignDepth_1089_; lean_object* v_lmvarCounter_1090_; lean_object* v_mvarCounter_1091_; lean_object* v_lDecls_1092_; lean_object* v_decls_1093_; lean_object* v_userNames_1094_; lean_object* v_lAssignment_1095_; lean_object* v_eAssignment_1096_; lean_object* v_dAssignment_1097_; lean_object* v___x_1099_; uint8_t v_isShared_1100_; uint8_t v_isSharedCheck_1111_; 
v_depth_1088_ = lean_ctor_get(v_mctx_1080_, 0);
v_levelAssignDepth_1089_ = lean_ctor_get(v_mctx_1080_, 1);
v_lmvarCounter_1090_ = lean_ctor_get(v_mctx_1080_, 2);
v_mvarCounter_1091_ = lean_ctor_get(v_mctx_1080_, 3);
v_lDecls_1092_ = lean_ctor_get(v_mctx_1080_, 4);
v_decls_1093_ = lean_ctor_get(v_mctx_1080_, 5);
v_userNames_1094_ = lean_ctor_get(v_mctx_1080_, 6);
v_lAssignment_1095_ = lean_ctor_get(v_mctx_1080_, 7);
v_eAssignment_1096_ = lean_ctor_get(v_mctx_1080_, 8);
v_dAssignment_1097_ = lean_ctor_get(v_mctx_1080_, 9);
v_isSharedCheck_1111_ = !lean_is_exclusive(v_mctx_1080_);
if (v_isSharedCheck_1111_ == 0)
{
v___x_1099_ = v_mctx_1080_;
v_isShared_1100_ = v_isSharedCheck_1111_;
goto v_resetjp_1098_;
}
else
{
lean_inc(v_dAssignment_1097_);
lean_inc(v_eAssignment_1096_);
lean_inc(v_lAssignment_1095_);
lean_inc(v_userNames_1094_);
lean_inc(v_decls_1093_);
lean_inc(v_lDecls_1092_);
lean_inc(v_mvarCounter_1091_);
lean_inc(v_lmvarCounter_1090_);
lean_inc(v_levelAssignDepth_1089_);
lean_inc(v_depth_1088_);
lean_dec(v_mctx_1080_);
v___x_1099_ = lean_box(0);
v_isShared_1100_ = v_isSharedCheck_1111_;
goto v_resetjp_1098_;
}
v_resetjp_1098_:
{
lean_object* v___x_1101_; lean_object* v___x_1103_; 
v___x_1101_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3___redArg(v_eAssignment_1096_, v_mvarId_1075_, v_val_1076_);
if (v_isShared_1100_ == 0)
{
lean_ctor_set(v___x_1099_, 8, v___x_1101_);
v___x_1103_ = v___x_1099_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1110_; 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v_depth_1088_);
lean_ctor_set(v_reuseFailAlloc_1110_, 1, v_levelAssignDepth_1089_);
lean_ctor_set(v_reuseFailAlloc_1110_, 2, v_lmvarCounter_1090_);
lean_ctor_set(v_reuseFailAlloc_1110_, 3, v_mvarCounter_1091_);
lean_ctor_set(v_reuseFailAlloc_1110_, 4, v_lDecls_1092_);
lean_ctor_set(v_reuseFailAlloc_1110_, 5, v_decls_1093_);
lean_ctor_set(v_reuseFailAlloc_1110_, 6, v_userNames_1094_);
lean_ctor_set(v_reuseFailAlloc_1110_, 7, v_lAssignment_1095_);
lean_ctor_set(v_reuseFailAlloc_1110_, 8, v___x_1101_);
lean_ctor_set(v_reuseFailAlloc_1110_, 9, v_dAssignment_1097_);
v___x_1103_ = v_reuseFailAlloc_1110_;
goto v_reusejp_1102_;
}
v_reusejp_1102_:
{
lean_object* v___x_1105_; 
if (v_isShared_1087_ == 0)
{
lean_ctor_set(v___x_1086_, 0, v___x_1103_);
v___x_1105_ = v___x_1086_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v___x_1103_);
lean_ctor_set(v_reuseFailAlloc_1109_, 1, v_cache_1081_);
lean_ctor_set(v_reuseFailAlloc_1109_, 2, v_zetaDeltaFVarIds_1082_);
lean_ctor_set(v_reuseFailAlloc_1109_, 3, v_postponed_1083_);
lean_ctor_set(v_reuseFailAlloc_1109_, 4, v_diag_1084_);
v___x_1105_ = v_reuseFailAlloc_1109_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; 
v___x_1106_ = lean_st_ref_set(v___y_1077_, v___x_1105_);
v___x_1107_ = lean_box(0);
v___x_1108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1108_, 0, v___x_1107_);
return v___x_1108_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3___redArg___boxed(lean_object* v_mvarId_1113_, lean_object* v_val_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_){
_start:
{
lean_object* v_res_1117_; 
v_res_1117_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3___redArg(v_mvarId_1113_, v_val_1114_, v___y_1115_);
lean_dec(v___y_1115_);
return v_res_1117_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg___lam__0(lean_object* v_x1_1118_, lean_object* v_x2_1119_){
_start:
{
lean_object* v_fst_1120_; lean_object* v_fst_1121_; uint8_t v___x_1122_; 
v_fst_1120_ = lean_ctor_get(v_x1_1118_, 0);
v_fst_1121_ = lean_ctor_get(v_x2_1119_, 0);
v___x_1122_ = lean_nat_dec_lt(v_fst_1120_, v_fst_1121_);
return v___x_1122_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg___lam__0___boxed(lean_object* v_x1_1123_, lean_object* v_x2_1124_){
_start:
{
uint8_t v_res_1125_; lean_object* v_r_1126_; 
v_res_1125_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg___lam__0(v_x1_1123_, v_x2_1124_);
lean_dec_ref(v_x2_1124_);
lean_dec_ref(v_x1_1123_);
v_r_1126_ = lean_box(v_res_1125_);
return v_r_1126_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9_spec__13___redArg(lean_object* v_hi_1127_, lean_object* v_pivot_1128_, lean_object* v_as_1129_, lean_object* v_i_1130_, lean_object* v_k_1131_){
_start:
{
uint8_t v___x_1132_; 
v___x_1132_ = lean_nat_dec_lt(v_k_1131_, v_hi_1127_);
if (v___x_1132_ == 0)
{
lean_object* v___x_1133_; lean_object* v___x_1134_; 
lean_dec(v_k_1131_);
v___x_1133_ = lean_array_fswap(v_as_1129_, v_i_1130_, v_hi_1127_);
v___x_1134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1134_, 0, v_i_1130_);
lean_ctor_set(v___x_1134_, 1, v___x_1133_);
return v___x_1134_;
}
else
{
lean_object* v___x_1135_; lean_object* v_fst_1136_; lean_object* v_fst_1137_; uint8_t v___x_1138_; 
v___x_1135_ = lean_array_fget_borrowed(v_as_1129_, v_k_1131_);
v_fst_1136_ = lean_ctor_get(v___x_1135_, 0);
v_fst_1137_ = lean_ctor_get(v_pivot_1128_, 0);
v___x_1138_ = lean_nat_dec_lt(v_fst_1136_, v_fst_1137_);
if (v___x_1138_ == 0)
{
lean_object* v___x_1139_; lean_object* v___x_1140_; 
v___x_1139_ = lean_unsigned_to_nat(1u);
v___x_1140_ = lean_nat_add(v_k_1131_, v___x_1139_);
lean_dec(v_k_1131_);
v_k_1131_ = v___x_1140_;
goto _start;
}
else
{
lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; 
v___x_1142_ = lean_array_fswap(v_as_1129_, v_i_1130_, v_k_1131_);
v___x_1143_ = lean_unsigned_to_nat(1u);
v___x_1144_ = lean_nat_add(v_i_1130_, v___x_1143_);
lean_dec(v_i_1130_);
v___x_1145_ = lean_nat_add(v_k_1131_, v___x_1143_);
lean_dec(v_k_1131_);
v_as_1129_ = v___x_1142_;
v_i_1130_ = v___x_1144_;
v_k_1131_ = v___x_1145_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9_spec__13___redArg___boxed(lean_object* v_hi_1147_, lean_object* v_pivot_1148_, lean_object* v_as_1149_, lean_object* v_i_1150_, lean_object* v_k_1151_){
_start:
{
lean_object* v_res_1152_; 
v_res_1152_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9_spec__13___redArg(v_hi_1147_, v_pivot_1148_, v_as_1149_, v_i_1150_, v_k_1151_);
lean_dec_ref(v_pivot_1148_);
lean_dec(v_hi_1147_);
return v_res_1152_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg(lean_object* v_n_1153_, lean_object* v_as_1154_, lean_object* v_lo_1155_, lean_object* v_hi_1156_){
_start:
{
lean_object* v___y_1158_; uint8_t v___x_1168_; 
v___x_1168_ = lean_nat_dec_lt(v_lo_1155_, v_hi_1156_);
if (v___x_1168_ == 0)
{
lean_dec(v_lo_1155_);
return v_as_1154_;
}
else
{
lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v_mid_1171_; lean_object* v___y_1173_; lean_object* v___y_1179_; lean_object* v___x_1184_; lean_object* v___x_1185_; uint8_t v___x_1186_; 
v___x_1169_ = lean_nat_add(v_lo_1155_, v_hi_1156_);
v___x_1170_ = lean_unsigned_to_nat(1u);
v_mid_1171_ = lean_nat_shiftr(v___x_1169_, v___x_1170_);
lean_dec(v___x_1169_);
v___x_1184_ = lean_array_fget_borrowed(v_as_1154_, v_mid_1171_);
v___x_1185_ = lean_array_fget_borrowed(v_as_1154_, v_lo_1155_);
v___x_1186_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg___lam__0(v___x_1184_, v___x_1185_);
if (v___x_1186_ == 0)
{
v___y_1179_ = v_as_1154_;
goto v___jp_1178_;
}
else
{
lean_object* v___x_1187_; 
v___x_1187_ = lean_array_fswap(v_as_1154_, v_lo_1155_, v_mid_1171_);
v___y_1179_ = v___x_1187_;
goto v___jp_1178_;
}
v___jp_1172_:
{
lean_object* v___x_1174_; lean_object* v___x_1175_; uint8_t v___x_1176_; 
v___x_1174_ = lean_array_fget_borrowed(v___y_1173_, v_mid_1171_);
v___x_1175_ = lean_array_fget_borrowed(v___y_1173_, v_hi_1156_);
v___x_1176_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg___lam__0(v___x_1174_, v___x_1175_);
if (v___x_1176_ == 0)
{
lean_dec(v_mid_1171_);
v___y_1158_ = v___y_1173_;
goto v___jp_1157_;
}
else
{
lean_object* v___x_1177_; 
v___x_1177_ = lean_array_fswap(v___y_1173_, v_mid_1171_, v_hi_1156_);
lean_dec(v_mid_1171_);
v___y_1158_ = v___x_1177_;
goto v___jp_1157_;
}
}
v___jp_1178_:
{
lean_object* v___x_1180_; lean_object* v___x_1181_; uint8_t v___x_1182_; 
v___x_1180_ = lean_array_fget_borrowed(v___y_1179_, v_hi_1156_);
v___x_1181_ = lean_array_fget_borrowed(v___y_1179_, v_lo_1155_);
v___x_1182_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg___lam__0(v___x_1180_, v___x_1181_);
if (v___x_1182_ == 0)
{
v___y_1173_ = v___y_1179_;
goto v___jp_1172_;
}
else
{
lean_object* v___x_1183_; 
v___x_1183_ = lean_array_fswap(v___y_1179_, v_lo_1155_, v_hi_1156_);
v___y_1173_ = v___x_1183_;
goto v___jp_1172_;
}
}
}
v___jp_1157_:
{
lean_object* v_pivot_1159_; lean_object* v___x_1160_; lean_object* v_fst_1161_; lean_object* v_snd_1162_; uint8_t v___x_1163_; 
v_pivot_1159_ = lean_array_fget(v___y_1158_, v_hi_1156_);
lean_inc_n(v_lo_1155_, 2);
v___x_1160_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9_spec__13___redArg(v_hi_1156_, v_pivot_1159_, v___y_1158_, v_lo_1155_, v_lo_1155_);
lean_dec(v_pivot_1159_);
v_fst_1161_ = lean_ctor_get(v___x_1160_, 0);
lean_inc(v_fst_1161_);
v_snd_1162_ = lean_ctor_get(v___x_1160_, 1);
lean_inc(v_snd_1162_);
lean_dec_ref(v___x_1160_);
v___x_1163_ = lean_nat_dec_le(v_hi_1156_, v_fst_1161_);
if (v___x_1163_ == 0)
{
lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; 
v___x_1164_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg(v_n_1153_, v_snd_1162_, v_lo_1155_, v_fst_1161_);
v___x_1165_ = lean_unsigned_to_nat(1u);
v___x_1166_ = lean_nat_add(v_fst_1161_, v___x_1165_);
lean_dec(v_fst_1161_);
v_as_1154_ = v___x_1164_;
v_lo_1155_ = v___x_1166_;
goto _start;
}
else
{
lean_dec(v_fst_1161_);
lean_dec(v_lo_1155_);
return v_snd_1162_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg___boxed(lean_object* v_n_1188_, lean_object* v_as_1189_, lean_object* v_lo_1190_, lean_object* v_hi_1191_){
_start:
{
lean_object* v_res_1192_; 
v_res_1192_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg(v_n_1188_, v_as_1189_, v_lo_1190_, v_hi_1191_);
lean_dec(v_hi_1191_);
lean_dec(v_n_1188_);
return v_res_1192_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1___redArg(lean_object* v_ref_1193_, lean_object* v_msg_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_){
_start:
{
lean_object* v_fileName_1204_; lean_object* v_fileMap_1205_; lean_object* v_options_1206_; lean_object* v_currRecDepth_1207_; lean_object* v_maxRecDepth_1208_; lean_object* v_ref_1209_; lean_object* v_currNamespace_1210_; lean_object* v_openDecls_1211_; lean_object* v_initHeartbeats_1212_; lean_object* v_maxHeartbeats_1213_; lean_object* v_quotContext_1214_; lean_object* v_currMacroScope_1215_; uint8_t v_diag_1216_; lean_object* v_cancelTk_x3f_1217_; uint8_t v_suppressElabErrors_1218_; lean_object* v_inheritedTraceOptions_1219_; lean_object* v_ref_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; 
v_fileName_1204_ = lean_ctor_get(v___y_1201_, 0);
v_fileMap_1205_ = lean_ctor_get(v___y_1201_, 1);
v_options_1206_ = lean_ctor_get(v___y_1201_, 2);
v_currRecDepth_1207_ = lean_ctor_get(v___y_1201_, 3);
v_maxRecDepth_1208_ = lean_ctor_get(v___y_1201_, 4);
v_ref_1209_ = lean_ctor_get(v___y_1201_, 5);
v_currNamespace_1210_ = lean_ctor_get(v___y_1201_, 6);
v_openDecls_1211_ = lean_ctor_get(v___y_1201_, 7);
v_initHeartbeats_1212_ = lean_ctor_get(v___y_1201_, 8);
v_maxHeartbeats_1213_ = lean_ctor_get(v___y_1201_, 9);
v_quotContext_1214_ = lean_ctor_get(v___y_1201_, 10);
v_currMacroScope_1215_ = lean_ctor_get(v___y_1201_, 11);
v_diag_1216_ = lean_ctor_get_uint8(v___y_1201_, sizeof(void*)*14);
v_cancelTk_x3f_1217_ = lean_ctor_get(v___y_1201_, 12);
v_suppressElabErrors_1218_ = lean_ctor_get_uint8(v___y_1201_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1219_ = lean_ctor_get(v___y_1201_, 13);
v_ref_1220_ = l_Lean_replaceRef(v_ref_1193_, v_ref_1209_);
lean_inc_ref(v_inheritedTraceOptions_1219_);
lean_inc(v_cancelTk_x3f_1217_);
lean_inc(v_currMacroScope_1215_);
lean_inc(v_quotContext_1214_);
lean_inc(v_maxHeartbeats_1213_);
lean_inc(v_initHeartbeats_1212_);
lean_inc(v_openDecls_1211_);
lean_inc(v_currNamespace_1210_);
lean_inc(v_maxRecDepth_1208_);
lean_inc(v_currRecDepth_1207_);
lean_inc_ref(v_options_1206_);
lean_inc_ref(v_fileMap_1205_);
lean_inc_ref(v_fileName_1204_);
v___x_1221_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1221_, 0, v_fileName_1204_);
lean_ctor_set(v___x_1221_, 1, v_fileMap_1205_);
lean_ctor_set(v___x_1221_, 2, v_options_1206_);
lean_ctor_set(v___x_1221_, 3, v_currRecDepth_1207_);
lean_ctor_set(v___x_1221_, 4, v_maxRecDepth_1208_);
lean_ctor_set(v___x_1221_, 5, v_ref_1220_);
lean_ctor_set(v___x_1221_, 6, v_currNamespace_1210_);
lean_ctor_set(v___x_1221_, 7, v_openDecls_1211_);
lean_ctor_set(v___x_1221_, 8, v_initHeartbeats_1212_);
lean_ctor_set(v___x_1221_, 9, v_maxHeartbeats_1213_);
lean_ctor_set(v___x_1221_, 10, v_quotContext_1214_);
lean_ctor_set(v___x_1221_, 11, v_currMacroScope_1215_);
lean_ctor_set(v___x_1221_, 12, v_cancelTk_x3f_1217_);
lean_ctor_set(v___x_1221_, 13, v_inheritedTraceOptions_1219_);
lean_ctor_set_uint8(v___x_1221_, sizeof(void*)*14, v_diag_1216_);
lean_ctor_set_uint8(v___x_1221_, sizeof(void*)*14 + 1, v_suppressElabErrors_1218_);
v___x_1222_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg(v_msg_1194_, v___y_1199_, v___y_1200_, v___x_1221_, v___y_1202_);
lean_dec_ref_known(v___x_1221_, 14);
return v___x_1222_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1___redArg___boxed(lean_object* v_ref_1223_, lean_object* v_msg_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_){
_start:
{
lean_object* v_res_1234_; 
v_res_1234_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1___redArg(v_ref_1223_, v_msg_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_);
lean_dec(v___y_1232_);
lean_dec_ref(v___y_1231_);
lean_dec(v___y_1230_);
lean_dec_ref(v___y_1229_);
lean_dec(v___y_1228_);
lean_dec_ref(v___y_1227_);
lean_dec(v___y_1226_);
lean_dec_ref(v___y_1225_);
lean_dec(v_ref_1223_);
return v_res_1234_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_1236_; lean_object* v___x_1237_; 
v___x_1236_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg___closed__0));
v___x_1237_ = l_Lean_stringToMessageData(v___x_1236_);
return v___x_1237_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg(lean_object* v_as_1238_, lean_object* v_i_1239_, lean_object* v_j_1240_, lean_object* v_bs_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_){
_start:
{
lean_object* v_zero_1251_; uint8_t v_isZero_1252_; 
v_zero_1251_ = lean_unsigned_to_nat(0u);
v_isZero_1252_ = lean_nat_dec_eq(v_i_1239_, v_zero_1251_);
if (v_isZero_1252_ == 1)
{
lean_object* v___x_1253_; 
lean_dec(v_j_1240_);
lean_dec(v_i_1239_);
v___x_1253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1253_, 0, v_bs_1241_);
return v___x_1253_;
}
else
{
lean_object* v_one_1254_; lean_object* v_n_1255_; lean_object* v_a_1257_; lean_object* v___x_1261_; lean_object* v___x_1262_; uint8_t v_isZero_1263_; 
v_one_1254_ = lean_unsigned_to_nat(1u);
v_n_1255_ = lean_nat_sub(v_i_1239_, v_one_1254_);
lean_dec(v_i_1239_);
v___x_1261_ = lean_array_fget_borrowed(v_as_1238_, v_j_1240_);
v___x_1262_ = l_Lean_TSyntax_getNat(v___x_1261_);
v_isZero_1263_ = lean_nat_dec_eq(v___x_1262_, v_zero_1251_);
if (v_isZero_1263_ == 1)
{
lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v_a_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1273_; 
lean_dec(v___x_1262_);
lean_dec(v_n_1255_);
lean_dec_ref(v_bs_1241_);
lean_dec(v_j_1240_);
v___x_1264_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg___closed__1, &l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg___closed__1_once, _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg___closed__1);
v___x_1265_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1___redArg(v___x_1261_, v___x_1264_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_);
v_a_1266_ = lean_ctor_get(v___x_1265_, 0);
v_isSharedCheck_1273_ = !lean_is_exclusive(v___x_1265_);
if (v_isSharedCheck_1273_ == 0)
{
v___x_1268_ = v___x_1265_;
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_a_1266_);
lean_dec(v___x_1265_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
lean_object* v___x_1271_; 
if (v_isShared_1269_ == 0)
{
v___x_1271_ = v___x_1268_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v_a_1266_);
v___x_1271_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
return v___x_1271_;
}
}
}
else
{
lean_object* v_n_1274_; lean_object* v___x_1275_; 
v_n_1274_ = lean_nat_sub(v___x_1262_, v_one_1254_);
lean_dec(v___x_1262_);
lean_inc(v_j_1240_);
v___x_1275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1275_, 0, v_n_1274_);
lean_ctor_set(v___x_1275_, 1, v_j_1240_);
v_a_1257_ = v___x_1275_;
goto v___jp_1256_;
}
v___jp_1256_:
{
lean_object* v___x_1258_; lean_object* v___x_1259_; 
v___x_1258_ = lean_nat_add(v_j_1240_, v_one_1254_);
lean_dec(v_j_1240_);
v___x_1259_ = lean_array_push(v_bs_1241_, v_a_1257_);
v_i_1239_ = v_n_1255_;
v_j_1240_ = v___x_1258_;
v_bs_1241_ = v___x_1259_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg___boxed(lean_object* v_as_1276_, lean_object* v_i_1277_, lean_object* v_j_1278_, lean_object* v_bs_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_){
_start:
{
lean_object* v_res_1289_; 
v_res_1289_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg(v_as_1276_, v_i_1277_, v_j_1278_, v_bs_1279_, v___y_1280_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_);
lean_dec(v___y_1287_);
lean_dec_ref(v___y_1286_);
lean_dec(v___y_1285_);
lean_dec_ref(v___y_1284_);
lean_dec(v___y_1283_);
lean_dec_ref(v___y_1282_);
lean_dec(v___y_1281_);
lean_dec_ref(v___y_1280_);
lean_dec_ref(v_as_1276_);
return v_res_1289_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11_spec__13___redArg(lean_object* v_as_1290_, lean_object* v_a_1291_, lean_object* v_x_1292_){
_start:
{
lean_object* v_zero_1293_; uint8_t v_isZero_1294_; 
v_zero_1293_ = lean_unsigned_to_nat(0u);
v_isZero_1294_ = lean_nat_dec_eq(v_x_1292_, v_zero_1293_);
if (v_isZero_1294_ == 1)
{
lean_dec(v_x_1292_);
return v_isZero_1294_;
}
else
{
lean_object* v_fst_1295_; lean_object* v_one_1296_; lean_object* v_n_1297_; lean_object* v___x_1298_; lean_object* v_fst_1299_; uint8_t v___x_1300_; 
v_fst_1295_ = lean_ctor_get(v_a_1291_, 0);
v_one_1296_ = lean_unsigned_to_nat(1u);
v_n_1297_ = lean_nat_sub(v_x_1292_, v_one_1296_);
lean_dec(v_x_1292_);
v___x_1298_ = lean_array_fget_borrowed(v_as_1290_, v_n_1297_);
v_fst_1299_ = lean_ctor_get(v___x_1298_, 0);
v___x_1300_ = lean_nat_dec_eq(v_fst_1295_, v_fst_1299_);
if (v___x_1300_ == 0)
{
v_x_1292_ = v_n_1297_;
goto _start;
}
else
{
lean_dec(v_n_1297_);
return v_isZero_1294_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11_spec__13___redArg___boxed(lean_object* v_as_1302_, lean_object* v_a_1303_, lean_object* v_x_1304_){
_start:
{
uint8_t v_res_1305_; lean_object* v_r_1306_; 
v_res_1305_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11_spec__13___redArg(v_as_1302_, v_a_1303_, v_x_1304_);
lean_dec_ref(v_a_1303_);
lean_dec_ref(v_as_1302_);
v_r_1306_ = lean_box(v_res_1305_);
return v_r_1306_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11(lean_object* v_as_1307_, lean_object* v_i_1308_){
_start:
{
lean_object* v___x_1309_; uint8_t v___x_1310_; 
v___x_1309_ = lean_array_get_size(v_as_1307_);
v___x_1310_ = lean_nat_dec_lt(v_i_1308_, v___x_1309_);
if (v___x_1310_ == 0)
{
uint8_t v___x_1311_; 
lean_dec(v_i_1308_);
v___x_1311_ = 1;
return v___x_1311_;
}
else
{
lean_object* v___x_1312_; uint8_t v___x_1313_; 
v___x_1312_ = lean_array_fget_borrowed(v_as_1307_, v_i_1308_);
lean_inc(v_i_1308_);
v___x_1313_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11_spec__13___redArg(v_as_1307_, v___x_1312_, v_i_1308_);
if (v___x_1313_ == 0)
{
lean_dec(v_i_1308_);
return v___x_1313_;
}
else
{
lean_object* v___x_1314_; lean_object* v___x_1315_; 
v___x_1314_ = lean_unsigned_to_nat(1u);
v___x_1315_ = lean_nat_add(v_i_1308_, v___x_1314_);
lean_dec(v_i_1308_);
v_i_1308_ = v___x_1315_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11___boxed(lean_object* v_as_1317_, lean_object* v_i_1318_){
_start:
{
uint8_t v_res_1319_; lean_object* v_r_1320_; 
v_res_1319_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11(v_as_1317_, v_i_1318_);
lean_dec_ref(v_as_1317_);
v_r_1320_ = lean_box(v_res_1319_);
return v_r_1320_;
}
}
LEAN_EXPORT uint8_t l_Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8(lean_object* v_as_1321_){
_start:
{
lean_object* v___x_1322_; uint8_t v___x_1323_; 
v___x_1322_ = lean_unsigned_to_nat(0u);
v___x_1323_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11(v_as_1321_, v___x_1322_);
return v___x_1323_;
}
}
LEAN_EXPORT lean_object* l_Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8___boxed(lean_object* v_as_1324_){
_start:
{
uint8_t v_res_1325_; lean_object* v_r_1326_; 
v_res_1325_ = l_Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8(v_as_1324_);
lean_dec_ref(v_as_1324_);
v_r_1326_ = lean_box(v_res_1325_);
return v_r_1326_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__0(void){
_start:
{
lean_object* v___x_1327_; 
v___x_1327_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1327_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__1(void){
_start:
{
lean_object* v___x_1328_; lean_object* v___x_1329_; 
v___x_1328_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__0, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__0_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__0);
v___x_1329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1329_, 0, v___x_1328_);
return v___x_1329_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__2(void){
_start:
{
lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; 
v___x_1330_ = lean_unsigned_to_nat(0u);
v___x_1331_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__1, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__1_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__1);
v___x_1332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1332_, 0, v___x_1331_);
lean_ctor_set(v___x_1332_, 1, v___x_1330_);
return v___x_1332_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__3(void){
_start:
{
lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; 
v___x_1333_ = lean_unsigned_to_nat(32u);
v___x_1334_ = lean_mk_empty_array_with_capacity(v___x_1333_);
v___x_1335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1335_, 0, v___x_1334_);
return v___x_1335_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__4(void){
_start:
{
size_t v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; 
v___x_1336_ = ((size_t)5ULL);
v___x_1337_ = lean_unsigned_to_nat(0u);
v___x_1338_ = lean_unsigned_to_nat(32u);
v___x_1339_ = lean_mk_empty_array_with_capacity(v___x_1338_);
v___x_1340_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__3, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__3_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__3);
v___x_1341_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1341_, 0, v___x_1340_);
lean_ctor_set(v___x_1341_, 1, v___x_1339_);
lean_ctor_set(v___x_1341_, 2, v___x_1337_);
lean_ctor_set(v___x_1341_, 3, v___x_1337_);
lean_ctor_set_usize(v___x_1341_, 4, v___x_1336_);
return v___x_1341_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__5(void){
_start:
{
lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; 
v___x_1342_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__4, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__4_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__4);
v___x_1343_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__1, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__1_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__1);
v___x_1344_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1344_, 0, v___x_1343_);
lean_ctor_set(v___x_1344_, 1, v___x_1343_);
lean_ctor_set(v___x_1344_, 2, v___x_1343_);
lean_ctor_set(v___x_1344_, 3, v___x_1342_);
return v___x_1344_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__6(void){
_start:
{
lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; 
v___x_1345_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__5, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__5_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__5);
v___x_1346_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__2, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__2_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__2);
v___x_1347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1347_, 0, v___x_1346_);
lean_ctor_set(v___x_1347_, 1, v___x_1345_);
return v___x_1347_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__8(void){
_start:
{
lean_object* v___x_1349_; lean_object* v___x_1350_; 
v___x_1349_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__7));
v___x_1350_ = l_Lean_stringToMessageData(v___x_1349_);
return v___x_1350_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__10(void){
_start:
{
lean_object* v___x_1352_; lean_object* v___x_1353_; 
v___x_1352_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__9));
v___x_1353_ = l_Lean_stringToMessageData(v___x_1352_);
return v___x_1353_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__12(void){
_start:
{
lean_object* v___x_1355_; lean_object* v___x_1356_; 
v___x_1355_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__11));
v___x_1356_ = l_Lean_stringToMessageData(v___x_1355_);
return v___x_1356_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__14(void){
_start:
{
lean_object* v___x_1358_; lean_object* v___x_1359_; 
v___x_1358_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__13));
v___x_1359_ = l_Lean_stringToMessageData(v___x_1358_);
return v___x_1359_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__17(void){
_start:
{
lean_object* v___x_1363_; lean_object* v___x_1364_; 
v___x_1363_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__16));
v___x_1364_ = l_Lean_stringToMessageData(v___x_1363_);
return v___x_1364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__6(uint8_t v___x_1385_, lean_object* v___f_1386_, uint8_t v___x_1387_, lean_object* v_stx_1388_, lean_object* v___x_1389_, lean_object* v___x_1390_, lean_object* v___x_1391_, lean_object* v___x_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_){
_start:
{
lean_object* v___y_1403_; lean_object* v_subgoals_1404_; lean_object* v___y_1405_; lean_object* v___y_1406_; lean_object* v___y_1407_; lean_object* v___y_1408_; lean_object* v___y_1409_; lean_object* v___y_1410_; lean_object* v___y_1411_; lean_object* v___y_1412_; lean_object* v___y_1450_; lean_object* v___y_1451_; lean_object* v___y_1452_; lean_object* v___y_1453_; lean_object* v___y_1454_; lean_object* v___y_1455_; lean_object* v___y_1456_; lean_object* v___y_1457_; lean_object* v___y_1458_; lean_object* v___y_1459_; lean_object* v___y_1464_; lean_object* v___y_1465_; lean_object* v___y_1466_; lean_object* v___y_1467_; lean_object* v___y_1468_; lean_object* v___y_1469_; lean_object* v___y_1470_; lean_object* v___y_1471_; lean_object* v___y_1472_; lean_object* v___y_1473_; lean_object* v___y_1474_; lean_object* v___y_1475_; lean_object* v___y_1476_; lean_object* v___y_1479_; lean_object* v___y_1480_; lean_object* v___y_1481_; lean_object* v___y_1482_; lean_object* v___y_1483_; lean_object* v___y_1484_; lean_object* v___y_1485_; lean_object* v___y_1486_; lean_object* v___y_1487_; lean_object* v___y_1488_; lean_object* v___y_1489_; lean_object* v___y_1490_; lean_object* v___y_1491_; 
if (v___x_1385_ == 0)
{
lean_object* v___x_1493_; 
lean_dec_ref(v___x_1392_);
lean_dec_ref(v___x_1391_);
lean_dec_ref(v___x_1390_);
lean_dec_ref(v___x_1389_);
lean_dec_ref(v___f_1386_);
v___x_1493_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg();
return v___x_1493_;
}
else
{
lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___y_1497_; lean_object* v___y_1498_; lean_object* v___y_1499_; lean_object* v___y_1500_; lean_object* v___y_1501_; lean_object* v___y_1502_; lean_object* v___y_1503_; lean_object* v___y_1504_; lean_object* v___y_1505_; lean_object* v___y_1506_; lean_object* v___y_1512_; lean_object* v___y_1513_; lean_object* v___y_1514_; lean_object* v___y_1515_; lean_object* v___y_1516_; lean_object* v___y_1517_; lean_object* v___y_1518_; lean_object* v___y_1519_; lean_object* v___y_1520_; lean_object* v___y_1521_; lean_object* v___y_1522_; lean_object* v___y_1523_; lean_object* v___y_1524_; lean_object* v___y_1525_; lean_object* v___y_1526_; uint8_t v___y_1527_; lean_object* v___y_1620_; lean_object* v___y_1621_; lean_object* v___y_1622_; lean_object* v___y_1623_; lean_object* v___y_1624_; lean_object* v_occs_1625_; lean_object* v___y_1626_; lean_object* v___y_1627_; lean_object* v___y_1628_; lean_object* v___y_1629_; lean_object* v___y_1630_; lean_object* v___y_1631_; lean_object* v___y_1632_; lean_object* v___y_1633_; lean_object* v___y_1648_; lean_object* v___y_1649_; lean_object* v___y_1650_; lean_object* v___y_1651_; lean_object* v___y_1652_; lean_object* v___y_1653_; lean_object* v___y_1654_; lean_object* v___y_1655_; lean_object* v___y_1656_; lean_object* v___y_1657_; lean_object* v___y_1658_; lean_object* v___y_1659_; lean_object* v___y_1660_; lean_object* v___y_1661_; lean_object* v___y_1666_; lean_object* v___y_1667_; lean_object* v___y_1668_; lean_object* v___y_1669_; lean_object* v___y_1670_; lean_object* v___y_1671_; lean_object* v___y_1672_; lean_object* v___y_1673_; lean_object* v___y_1674_; lean_object* v___y_1675_; lean_object* v___y_1676_; lean_object* v___y_1677_; lean_object* v___y_1678_; lean_object* v___y_1679_; lean_object* v___y_1684_; lean_object* v___y_1685_; lean_object* v___y_1686_; lean_object* v___y_1687_; lean_object* v___y_1688_; lean_object* v___y_1689_; lean_object* v___y_1690_; lean_object* v___y_1691_; lean_object* v___y_1692_; lean_object* v___y_1693_; lean_object* v___y_1694_; lean_object* v___y_1695_; lean_object* v___y_1696_; lean_object* v___y_1697_; lean_object* v___y_1698_; lean_object* v___y_1699_; lean_object* v___y_1700_; lean_object* v___y_1703_; lean_object* v___y_1704_; lean_object* v___y_1705_; lean_object* v___y_1706_; lean_object* v___y_1707_; lean_object* v___y_1708_; lean_object* v___y_1709_; lean_object* v___y_1710_; lean_object* v___y_1711_; lean_object* v___y_1712_; lean_object* v___y_1713_; lean_object* v___y_1714_; lean_object* v___y_1715_; lean_object* v___y_1716_; lean_object* v___y_1717_; lean_object* v___y_1718_; lean_object* v___y_1719_; lean_object* v_occs_1722_; lean_object* v___y_1723_; lean_object* v___y_1724_; lean_object* v___y_1725_; lean_object* v___y_1726_; lean_object* v___y_1727_; lean_object* v___y_1728_; lean_object* v___y_1729_; lean_object* v___y_1730_; lean_object* v___x_1816_; uint8_t v___x_1817_; 
v___x_1494_ = lean_unsigned_to_nat(0u);
v___x_1495_ = lean_unsigned_to_nat(1u);
v___x_1816_ = l_Lean_Syntax_getArg(v_stx_1388_, v___x_1495_);
v___x_1817_ = l_Lean_Syntax_isNone(v___x_1816_);
if (v___x_1817_ == 0)
{
uint8_t v___x_1818_; 
lean_inc(v___x_1816_);
v___x_1818_ = l_Lean_Syntax_matchesNull(v___x_1816_, v___x_1495_);
if (v___x_1818_ == 0)
{
lean_object* v___x_1819_; 
lean_dec(v___x_1816_);
lean_dec_ref(v___x_1392_);
lean_dec_ref(v___x_1391_);
lean_dec_ref(v___x_1390_);
lean_dec_ref(v___x_1389_);
lean_dec_ref(v___f_1386_);
v___x_1819_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg();
return v___x_1819_;
}
else
{
lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; uint8_t v___x_1823_; 
v___x_1820_ = l_Lean_Syntax_getArg(v___x_1816_, v___x_1494_);
lean_dec(v___x_1816_);
v___x_1821_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__27));
lean_inc_ref(v___x_1392_);
lean_inc_ref(v___x_1391_);
lean_inc_ref(v___x_1390_);
lean_inc_ref(v___x_1389_);
v___x_1822_ = l_Lean_Name_mkStr5(v___x_1389_, v___x_1390_, v___x_1391_, v___x_1392_, v___x_1821_);
lean_inc(v___x_1820_);
v___x_1823_ = l_Lean_Syntax_isOfKind(v___x_1820_, v___x_1822_);
lean_dec(v___x_1822_);
if (v___x_1823_ == 0)
{
lean_object* v___x_1824_; 
lean_dec(v___x_1820_);
lean_dec_ref(v___x_1392_);
lean_dec_ref(v___x_1391_);
lean_dec_ref(v___x_1390_);
lean_dec_ref(v___x_1389_);
lean_dec_ref(v___f_1386_);
v___x_1824_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg();
return v___x_1824_;
}
else
{
lean_object* v___x_1825_; lean_object* v_occs_1826_; lean_object* v___x_1827_; 
v___x_1825_ = lean_unsigned_to_nat(3u);
v_occs_1826_ = l_Lean_Syntax_getArg(v___x_1820_, v___x_1825_);
lean_dec(v___x_1820_);
v___x_1827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1827_, 0, v_occs_1826_);
v_occs_1722_ = v___x_1827_;
v___y_1723_ = v___y_1393_;
v___y_1724_ = v___y_1394_;
v___y_1725_ = v___y_1395_;
v___y_1726_ = v___y_1396_;
v___y_1727_ = v___y_1397_;
v___y_1728_ = v___y_1398_;
v___y_1729_ = v___y_1399_;
v___y_1730_ = v___y_1400_;
goto v___jp_1721_;
}
}
}
else
{
lean_object* v___x_1828_; 
lean_dec(v___x_1816_);
v___x_1828_ = lean_box(0);
v_occs_1722_ = v___x_1828_;
v___y_1723_ = v___y_1393_;
v___y_1724_ = v___y_1394_;
v___y_1725_ = v___y_1395_;
v___y_1726_ = v___y_1396_;
v___y_1727_ = v___y_1397_;
v___y_1728_ = v___y_1398_;
v___y_1729_ = v___y_1399_;
v___y_1730_ = v___y_1400_;
goto v___jp_1721_;
}
v___jp_1496_:
{
lean_object* v___x_1507_; uint8_t v___x_1508_; 
v___x_1507_ = lean_array_get_size(v___y_1497_);
v___x_1508_ = lean_nat_dec_eq(v___x_1507_, v___x_1494_);
if (v___x_1508_ == 0)
{
lean_object* v___x_1509_; uint8_t v___x_1510_; 
v___x_1509_ = lean_nat_sub(v___x_1507_, v___x_1495_);
v___x_1510_ = lean_nat_dec_le(v___x_1494_, v___x_1509_);
if (v___x_1510_ == 0)
{
lean_inc(v___x_1509_);
v___y_1479_ = v___y_1505_;
v___y_1480_ = v___x_1509_;
v___y_1481_ = v___y_1497_;
v___y_1482_ = v___y_1501_;
v___y_1483_ = v___y_1504_;
v___y_1484_ = v___y_1502_;
v___y_1485_ = v___y_1503_;
v___y_1486_ = v___y_1500_;
v___y_1487_ = v___x_1507_;
v___y_1488_ = v___y_1498_;
v___y_1489_ = v___y_1499_;
v___y_1490_ = v___y_1506_;
v___y_1491_ = v___x_1509_;
goto v___jp_1478_;
}
else
{
v___y_1479_ = v___y_1505_;
v___y_1480_ = v___x_1509_;
v___y_1481_ = v___y_1497_;
v___y_1482_ = v___y_1501_;
v___y_1483_ = v___y_1504_;
v___y_1484_ = v___y_1502_;
v___y_1485_ = v___y_1503_;
v___y_1486_ = v___y_1500_;
v___y_1487_ = v___x_1507_;
v___y_1488_ = v___y_1498_;
v___y_1489_ = v___y_1499_;
v___y_1490_ = v___y_1506_;
v___y_1491_ = v___x_1494_;
goto v___jp_1478_;
}
}
else
{
v___y_1450_ = v___y_1505_;
v___y_1451_ = v___y_1503_;
v___y_1452_ = v___y_1500_;
v___y_1453_ = v___y_1498_;
v___y_1454_ = v___y_1501_;
v___y_1455_ = v___y_1504_;
v___y_1456_ = v___y_1499_;
v___y_1457_ = v___y_1506_;
v___y_1458_ = v___y_1502_;
v___y_1459_ = v___y_1497_;
goto v___jp_1449_;
}
}
v___jp_1511_:
{
lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; 
v___x_1528_ = l_Lean_Meta_Simp_Context_setMemoize(v___y_1512_, v___y_1527_);
v___x_1529_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__6, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__6_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__6);
lean_inc(v___y_1515_);
lean_inc_ref(v___y_1524_);
v___x_1530_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre___boxed), 11, 2);
lean_closure_set(v___x_1530_, 0, v___y_1524_);
lean_closure_set(v___x_1530_, 1, v___y_1515_);
lean_inc_ref(v___y_1518_);
lean_inc_ref(v___y_1517_);
v___x_1531_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_1531_, 0, v___x_1530_);
lean_ctor_set(v___x_1531_, 1, v___y_1526_);
lean_ctor_set(v___x_1531_, 2, v___y_1517_);
lean_ctor_set(v___x_1531_, 3, v___f_1386_);
lean_ctor_set(v___x_1531_, 4, v___y_1518_);
lean_ctor_set_uint8(v___x_1531_, sizeof(void*)*5, v___x_1387_);
v___x_1532_ = l_Lean_Meta_Simp_main(v___y_1514_, v___x_1528_, v___x_1529_, v___x_1531_, v___y_1522_, v___y_1516_, v___y_1523_, v___y_1525_);
if (lean_obj_tag(v___x_1532_) == 0)
{
lean_object* v_a_1533_; lean_object* v_fst_1534_; lean_object* v___x_1536_; uint8_t v_isShared_1537_; uint8_t v_isSharedCheck_1609_; 
v_a_1533_ = lean_ctor_get(v___x_1532_, 0);
lean_inc(v_a_1533_);
lean_dec_ref_known(v___x_1532_, 1);
v_fst_1534_ = lean_ctor_get(v_a_1533_, 0);
v_isSharedCheck_1609_ = !lean_is_exclusive(v_a_1533_);
if (v_isSharedCheck_1609_ == 0)
{
lean_object* v_unused_1610_; 
v_unused_1610_ = lean_ctor_get(v_a_1533_, 1);
lean_dec(v_unused_1610_);
v___x_1536_ = v_a_1533_;
v_isShared_1537_ = v_isSharedCheck_1609_;
goto v_resetjp_1535_;
}
else
{
lean_inc(v_fst_1534_);
lean_dec(v_a_1533_);
v___x_1536_ = lean_box(0);
v_isShared_1537_ = v_isSharedCheck_1609_;
goto v_resetjp_1535_;
}
v_resetjp_1535_:
{
lean_object* v___x_1538_; 
v___x_1538_ = lean_st_ref_get(v___y_1515_);
lean_dec(v___y_1515_);
if (lean_obj_tag(v___x_1538_) == 0)
{
lean_object* v_subgoals_1539_; lean_object* v___x_1540_; uint8_t v___x_1541_; 
v_subgoals_1539_ = lean_ctor_get(v___x_1538_, 0);
lean_inc_ref(v_subgoals_1539_);
lean_dec_ref_known(v___x_1538_, 1);
v___x_1540_ = lean_array_get_size(v_subgoals_1539_);
v___x_1541_ = lean_nat_dec_eq(v___x_1540_, v___x_1494_);
if (v___x_1541_ == 0)
{
lean_del_object(v___x_1536_);
lean_dec_ref(v___y_1524_);
v___y_1403_ = v_fst_1534_;
v_subgoals_1404_ = v_subgoals_1539_;
v___y_1405_ = v___y_1521_;
v___y_1406_ = v___y_1513_;
v___y_1407_ = v___y_1519_;
v___y_1408_ = v___y_1520_;
v___y_1409_ = v___y_1522_;
v___y_1410_ = v___y_1516_;
v___y_1411_ = v___y_1523_;
v___y_1412_ = v___y_1525_;
goto v___jp_1402_;
}
else
{
lean_object* v_expr_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1546_; 
lean_dec_ref(v_subgoals_1539_);
lean_dec(v_fst_1534_);
v_expr_1542_ = lean_ctor_get(v___y_1524_, 2);
lean_inc_ref(v_expr_1542_);
lean_dec_ref(v___y_1524_);
v___x_1543_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__8, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__8_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__8);
v___x_1544_ = l_Lean_indentExpr(v_expr_1542_);
if (v_isShared_1537_ == 0)
{
lean_ctor_set_tag(v___x_1536_, 7);
lean_ctor_set(v___x_1536_, 1, v___x_1544_);
lean_ctor_set(v___x_1536_, 0, v___x_1543_);
v___x_1546_ = v___x_1536_;
goto v_reusejp_1545_;
}
else
{
lean_object* v_reuseFailAlloc_1556_; 
v_reuseFailAlloc_1556_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1556_, 0, v___x_1543_);
lean_ctor_set(v_reuseFailAlloc_1556_, 1, v___x_1544_);
v___x_1546_ = v_reuseFailAlloc_1556_;
goto v_reusejp_1545_;
}
v_reusejp_1545_:
{
lean_object* v___x_1547_; lean_object* v_a_1548_; lean_object* v___x_1550_; uint8_t v_isShared_1551_; uint8_t v_isSharedCheck_1555_; 
v___x_1547_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg(v___x_1546_, v___y_1522_, v___y_1516_, v___y_1523_, v___y_1525_);
v_a_1548_ = lean_ctor_get(v___x_1547_, 0);
v_isSharedCheck_1555_ = !lean_is_exclusive(v___x_1547_);
if (v_isSharedCheck_1555_ == 0)
{
v___x_1550_ = v___x_1547_;
v_isShared_1551_ = v_isSharedCheck_1555_;
goto v_resetjp_1549_;
}
else
{
lean_inc(v_a_1548_);
lean_dec(v___x_1547_);
v___x_1550_ = lean_box(0);
v_isShared_1551_ = v_isSharedCheck_1555_;
goto v_resetjp_1549_;
}
v_resetjp_1549_:
{
lean_object* v___x_1553_; 
if (v_isShared_1551_ == 0)
{
v___x_1553_ = v___x_1550_;
goto v_reusejp_1552_;
}
else
{
lean_object* v_reuseFailAlloc_1554_; 
v_reuseFailAlloc_1554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1554_, 0, v_a_1548_);
v___x_1553_ = v_reuseFailAlloc_1554_;
goto v_reusejp_1552_;
}
v_reusejp_1552_:
{
return v___x_1553_;
}
}
}
}
}
else
{
lean_object* v_subgoals_1557_; lean_object* v_idx_1558_; lean_object* v_remaining_1559_; uint8_t v___x_1560_; 
v_subgoals_1557_ = lean_ctor_get(v___x_1538_, 0);
lean_inc_ref(v_subgoals_1557_);
v_idx_1558_ = lean_ctor_get(v___x_1538_, 1);
lean_inc(v_idx_1558_);
v_remaining_1559_ = lean_ctor_get(v___x_1538_, 2);
lean_inc(v_remaining_1559_);
lean_dec_ref_known(v___x_1538_, 3);
v___x_1560_ = lean_nat_dec_eq(v_idx_1558_, v___x_1494_);
if (v___x_1560_ == 0)
{
lean_object* v___x_1561_; 
lean_dec_ref(v___y_1524_);
v___x_1561_ = l_List_getLast_x3f___redArg(v_remaining_1559_);
lean_dec(v_remaining_1559_);
if (lean_obj_tag(v___x_1561_) == 1)
{
lean_object* v_val_1562_; lean_object* v___x_1564_; uint8_t v_isShared_1565_; uint8_t v_isSharedCheck_1593_; 
lean_dec_ref(v_subgoals_1557_);
lean_dec(v_fst_1534_);
v_val_1562_ = lean_ctor_get(v___x_1561_, 0);
v_isSharedCheck_1593_ = !lean_is_exclusive(v___x_1561_);
if (v_isSharedCheck_1593_ == 0)
{
v___x_1564_ = v___x_1561_;
v_isShared_1565_ = v_isSharedCheck_1593_;
goto v_resetjp_1563_;
}
else
{
lean_inc(v_val_1562_);
lean_dec(v___x_1561_);
v___x_1564_ = lean_box(0);
v_isShared_1565_ = v_isSharedCheck_1593_;
goto v_resetjp_1563_;
}
v_resetjp_1563_:
{
lean_object* v_fst_1566_; lean_object* v___x_1568_; uint8_t v_isShared_1569_; uint8_t v_isSharedCheck_1591_; 
v_fst_1566_ = lean_ctor_get(v_val_1562_, 0);
v_isSharedCheck_1591_ = !lean_is_exclusive(v_val_1562_);
if (v_isSharedCheck_1591_ == 0)
{
lean_object* v_unused_1592_; 
v_unused_1592_ = lean_ctor_get(v_val_1562_, 1);
lean_dec(v_unused_1592_);
v___x_1568_ = v_val_1562_;
v_isShared_1569_ = v_isSharedCheck_1591_;
goto v_resetjp_1567_;
}
else
{
lean_inc(v_fst_1566_);
lean_dec(v_val_1562_);
v___x_1568_ = lean_box(0);
v_isShared_1569_ = v_isSharedCheck_1591_;
goto v_resetjp_1567_;
}
v_resetjp_1567_:
{
lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1573_; 
v___x_1570_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__10, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__10_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__10);
v___x_1571_ = l_Nat_reprFast(v_idx_1558_);
if (v_isShared_1565_ == 0)
{
lean_ctor_set_tag(v___x_1564_, 3);
lean_ctor_set(v___x_1564_, 0, v___x_1571_);
v___x_1573_ = v___x_1564_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1590_; 
v_reuseFailAlloc_1590_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1590_, 0, v___x_1571_);
v___x_1573_ = v_reuseFailAlloc_1590_;
goto v_reusejp_1572_;
}
v_reusejp_1572_:
{
lean_object* v___x_1574_; lean_object* v___x_1576_; 
v___x_1574_ = l_Lean_MessageData_ofFormat(v___x_1573_);
if (v_isShared_1569_ == 0)
{
lean_ctor_set_tag(v___x_1568_, 7);
lean_ctor_set(v___x_1568_, 1, v___x_1574_);
lean_ctor_set(v___x_1568_, 0, v___x_1570_);
v___x_1576_ = v___x_1568_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1589_; 
v_reuseFailAlloc_1589_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1589_, 0, v___x_1570_);
lean_ctor_set(v_reuseFailAlloc_1589_, 1, v___x_1574_);
v___x_1576_ = v_reuseFailAlloc_1589_;
goto v_reusejp_1575_;
}
v_reusejp_1575_:
{
lean_object* v___x_1577_; lean_object* v___x_1579_; 
v___x_1577_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__12, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__12_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__12);
if (v_isShared_1537_ == 0)
{
lean_ctor_set_tag(v___x_1536_, 7);
lean_ctor_set(v___x_1536_, 1, v___x_1577_);
lean_ctor_set(v___x_1536_, 0, v___x_1576_);
v___x_1579_ = v___x_1536_;
goto v_reusejp_1578_;
}
else
{
lean_object* v_reuseFailAlloc_1588_; 
v_reuseFailAlloc_1588_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1588_, 0, v___x_1576_);
lean_ctor_set(v_reuseFailAlloc_1588_, 1, v___x_1577_);
v___x_1579_ = v_reuseFailAlloc_1588_;
goto v_reusejp_1578_;
}
v_reusejp_1578_:
{
lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; 
v___x_1580_ = lean_nat_add(v_fst_1566_, v___x_1495_);
lean_dec(v_fst_1566_);
v___x_1581_ = l_Nat_reprFast(v___x_1580_);
v___x_1582_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1582_, 0, v___x_1581_);
v___x_1583_ = l_Lean_MessageData_ofFormat(v___x_1582_);
v___x_1584_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1584_, 0, v___x_1579_);
lean_ctor_set(v___x_1584_, 1, v___x_1583_);
v___x_1585_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__14, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__14_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__14);
v___x_1586_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1586_, 0, v___x_1584_);
lean_ctor_set(v___x_1586_, 1, v___x_1585_);
v___x_1587_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg(v___x_1586_, v___y_1522_, v___y_1516_, v___y_1523_, v___y_1525_);
return v___x_1587_;
}
}
}
}
}
}
else
{
lean_dec(v___x_1561_);
lean_dec(v_idx_1558_);
lean_del_object(v___x_1536_);
v___y_1497_ = v_subgoals_1557_;
v___y_1498_ = v_fst_1534_;
v___y_1499_ = v___y_1521_;
v___y_1500_ = v___y_1513_;
v___y_1501_ = v___y_1519_;
v___y_1502_ = v___y_1520_;
v___y_1503_ = v___y_1522_;
v___y_1504_ = v___y_1516_;
v___y_1505_ = v___y_1523_;
v___y_1506_ = v___y_1525_;
goto v___jp_1496_;
}
}
else
{
lean_object* v_expr_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1598_; 
lean_dec(v_remaining_1559_);
lean_dec(v_idx_1558_);
lean_dec_ref(v_subgoals_1557_);
lean_dec(v_fst_1534_);
v_expr_1594_ = lean_ctor_get(v___y_1524_, 2);
lean_inc_ref(v_expr_1594_);
lean_dec_ref(v___y_1524_);
v___x_1595_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__8, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__8_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__8);
v___x_1596_ = l_Lean_indentExpr(v_expr_1594_);
if (v_isShared_1537_ == 0)
{
lean_ctor_set_tag(v___x_1536_, 7);
lean_ctor_set(v___x_1536_, 1, v___x_1596_);
lean_ctor_set(v___x_1536_, 0, v___x_1595_);
v___x_1598_ = v___x_1536_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1608_; 
v_reuseFailAlloc_1608_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1608_, 0, v___x_1595_);
lean_ctor_set(v_reuseFailAlloc_1608_, 1, v___x_1596_);
v___x_1598_ = v_reuseFailAlloc_1608_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
lean_object* v___x_1599_; lean_object* v_a_1600_; lean_object* v___x_1602_; uint8_t v_isShared_1603_; uint8_t v_isSharedCheck_1607_; 
v___x_1599_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg(v___x_1598_, v___y_1522_, v___y_1516_, v___y_1523_, v___y_1525_);
v_a_1600_ = lean_ctor_get(v___x_1599_, 0);
v_isSharedCheck_1607_ = !lean_is_exclusive(v___x_1599_);
if (v_isSharedCheck_1607_ == 0)
{
v___x_1602_ = v___x_1599_;
v_isShared_1603_ = v_isSharedCheck_1607_;
goto v_resetjp_1601_;
}
else
{
lean_inc(v_a_1600_);
lean_dec(v___x_1599_);
v___x_1602_ = lean_box(0);
v_isShared_1603_ = v_isSharedCheck_1607_;
goto v_resetjp_1601_;
}
v_resetjp_1601_:
{
lean_object* v___x_1605_; 
if (v_isShared_1603_ == 0)
{
v___x_1605_ = v___x_1602_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1606_; 
v_reuseFailAlloc_1606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1606_, 0, v_a_1600_);
v___x_1605_ = v_reuseFailAlloc_1606_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
return v___x_1605_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1611_; lean_object* v___x_1613_; uint8_t v_isShared_1614_; uint8_t v_isSharedCheck_1618_; 
lean_dec_ref(v___y_1524_);
lean_dec(v___y_1515_);
v_a_1611_ = lean_ctor_get(v___x_1532_, 0);
v_isSharedCheck_1618_ = !lean_is_exclusive(v___x_1532_);
if (v_isSharedCheck_1618_ == 0)
{
v___x_1613_ = v___x_1532_;
v_isShared_1614_ = v_isSharedCheck_1618_;
goto v_resetjp_1612_;
}
else
{
lean_inc(v_a_1611_);
lean_dec(v___x_1532_);
v___x_1613_ = lean_box(0);
v_isShared_1614_ = v_isSharedCheck_1618_;
goto v_resetjp_1612_;
}
v_resetjp_1612_:
{
lean_object* v___x_1616_; 
if (v_isShared_1614_ == 0)
{
v___x_1616_ = v___x_1613_;
goto v_reusejp_1615_;
}
else
{
lean_object* v_reuseFailAlloc_1617_; 
v_reuseFailAlloc_1617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1617_, 0, v_a_1611_);
v___x_1616_ = v_reuseFailAlloc_1617_;
goto v_reusejp_1615_;
}
v_reusejp_1615_:
{
return v___x_1616_;
}
}
}
}
v___jp_1619_:
{
lean_object* v___x_1634_; lean_object* v___x_1635_; 
lean_inc_ref(v_occs_1625_);
v___x_1634_ = lean_st_mk_ref(v_occs_1625_);
v___x_1635_ = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_getContext___redArg(v___y_1630_, v___y_1632_, v___y_1633_);
if (lean_obj_tag(v___x_1635_) == 0)
{
if (lean_obj_tag(v_occs_1625_) == 0)
{
lean_object* v_a_1636_; 
lean_dec_ref_known(v_occs_1625_, 1);
v_a_1636_ = lean_ctor_get(v___x_1635_, 0);
lean_inc(v_a_1636_);
lean_dec_ref_known(v___x_1635_, 1);
v___y_1512_ = v_a_1636_;
v___y_1513_ = v___y_1627_;
v___y_1514_ = v___y_1620_;
v___y_1515_ = v___x_1634_;
v___y_1516_ = v___y_1631_;
v___y_1517_ = v___y_1622_;
v___y_1518_ = v___y_1623_;
v___y_1519_ = v___y_1628_;
v___y_1520_ = v___y_1629_;
v___y_1521_ = v___y_1626_;
v___y_1522_ = v___y_1630_;
v___y_1523_ = v___y_1632_;
v___y_1524_ = v___y_1621_;
v___y_1525_ = v___y_1633_;
v___y_1526_ = v___y_1624_;
v___y_1527_ = v___x_1387_;
goto v___jp_1511_;
}
else
{
lean_object* v_a_1637_; uint8_t v___x_1638_; 
lean_dec_ref(v_occs_1625_);
v_a_1637_ = lean_ctor_get(v___x_1635_, 0);
lean_inc(v_a_1637_);
lean_dec_ref_known(v___x_1635_, 1);
v___x_1638_ = 0;
v___y_1512_ = v_a_1637_;
v___y_1513_ = v___y_1627_;
v___y_1514_ = v___y_1620_;
v___y_1515_ = v___x_1634_;
v___y_1516_ = v___y_1631_;
v___y_1517_ = v___y_1622_;
v___y_1518_ = v___y_1623_;
v___y_1519_ = v___y_1628_;
v___y_1520_ = v___y_1629_;
v___y_1521_ = v___y_1626_;
v___y_1522_ = v___y_1630_;
v___y_1523_ = v___y_1632_;
v___y_1524_ = v___y_1621_;
v___y_1525_ = v___y_1633_;
v___y_1526_ = v___y_1624_;
v___y_1527_ = v___x_1638_;
goto v___jp_1511_;
}
}
else
{
lean_object* v_a_1639_; lean_object* v___x_1641_; uint8_t v_isShared_1642_; uint8_t v_isSharedCheck_1646_; 
lean_dec(v___x_1634_);
lean_dec_ref(v_occs_1625_);
lean_dec_ref(v___y_1624_);
lean_dec_ref(v___y_1621_);
lean_dec_ref(v___y_1620_);
lean_dec_ref(v___f_1386_);
v_a_1639_ = lean_ctor_get(v___x_1635_, 0);
v_isSharedCheck_1646_ = !lean_is_exclusive(v___x_1635_);
if (v_isSharedCheck_1646_ == 0)
{
v___x_1641_ = v___x_1635_;
v_isShared_1642_ = v_isSharedCheck_1646_;
goto v_resetjp_1640_;
}
else
{
lean_inc(v_a_1639_);
lean_dec(v___x_1635_);
v___x_1641_ = lean_box(0);
v_isShared_1642_ = v_isSharedCheck_1646_;
goto v_resetjp_1640_;
}
v_resetjp_1640_:
{
lean_object* v___x_1644_; 
if (v_isShared_1642_ == 0)
{
v___x_1644_ = v___x_1641_;
goto v_reusejp_1643_;
}
else
{
lean_object* v_reuseFailAlloc_1645_; 
v_reuseFailAlloc_1645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1645_, 0, v_a_1639_);
v___x_1644_ = v_reuseFailAlloc_1645_;
goto v_reusejp_1643_;
}
v_reusejp_1643_:
{
return v___x_1644_;
}
}
}
}
v___jp_1647_:
{
lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; 
v___x_1662_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__15));
v___x_1663_ = lean_array_to_list(v___y_1652_);
v___x_1664_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1664_, 0, v___x_1662_);
lean_ctor_set(v___x_1664_, 1, v___x_1494_);
lean_ctor_set(v___x_1664_, 2, v___x_1663_);
v___y_1620_ = v___y_1648_;
v___y_1621_ = v___y_1649_;
v___y_1622_ = v___y_1650_;
v___y_1623_ = v___y_1651_;
v___y_1624_ = v___y_1653_;
v_occs_1625_ = v___x_1664_;
v___y_1626_ = v___y_1654_;
v___y_1627_ = v___y_1655_;
v___y_1628_ = v___y_1656_;
v___y_1629_ = v___y_1657_;
v___y_1630_ = v___y_1658_;
v___y_1631_ = v___y_1659_;
v___y_1632_ = v___y_1660_;
v___y_1633_ = v___y_1661_;
goto v___jp_1619_;
}
v___jp_1665_:
{
uint8_t v___x_1680_; 
v___x_1680_ = l_Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8(v___y_1679_);
if (v___x_1680_ == 0)
{
lean_object* v___x_1681_; lean_object* v___x_1682_; 
lean_dec_ref(v___y_1679_);
lean_dec_ref(v___y_1677_);
lean_dec_ref(v___y_1676_);
lean_dec_ref(v___y_1667_);
lean_dec_ref(v___f_1386_);
v___x_1681_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__17, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__17_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__17);
v___x_1682_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg(v___x_1681_, v___y_1672_, v___y_1674_, v___y_1673_, v___y_1669_);
return v___x_1682_;
}
else
{
v___y_1648_ = v___y_1667_;
v___y_1649_ = v___y_1676_;
v___y_1650_ = v___y_1668_;
v___y_1651_ = v___y_1671_;
v___y_1652_ = v___y_1679_;
v___y_1653_ = v___y_1677_;
v___y_1654_ = v___y_1670_;
v___y_1655_ = v___y_1675_;
v___y_1656_ = v___y_1666_;
v___y_1657_ = v___y_1678_;
v___y_1658_ = v___y_1672_;
v___y_1659_ = v___y_1674_;
v___y_1660_ = v___y_1673_;
v___y_1661_ = v___y_1669_;
goto v___jp_1647_;
}
}
v___jp_1683_:
{
lean_object* v___x_1701_; 
v___x_1701_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg(v___y_1686_, v___y_1697_, v___y_1696_, v___y_1700_);
lean_dec(v___y_1700_);
lean_dec(v___y_1686_);
v___y_1666_ = v___y_1684_;
v___y_1667_ = v___y_1685_;
v___y_1668_ = v___y_1687_;
v___y_1669_ = v___y_1688_;
v___y_1670_ = v___y_1689_;
v___y_1671_ = v___y_1690_;
v___y_1672_ = v___y_1691_;
v___y_1673_ = v___y_1692_;
v___y_1674_ = v___y_1693_;
v___y_1675_ = v___y_1694_;
v___y_1676_ = v___y_1695_;
v___y_1677_ = v___y_1698_;
v___y_1678_ = v___y_1699_;
v___y_1679_ = v___x_1701_;
goto v___jp_1665_;
}
v___jp_1702_:
{
uint8_t v___x_1720_; 
v___x_1720_ = lean_nat_dec_le(v___y_1719_, v___y_1703_);
if (v___x_1720_ == 0)
{
lean_dec(v___y_1703_);
lean_inc(v___y_1719_);
v___y_1684_ = v___y_1704_;
v___y_1685_ = v___y_1705_;
v___y_1686_ = v___y_1706_;
v___y_1687_ = v___y_1707_;
v___y_1688_ = v___y_1708_;
v___y_1689_ = v___y_1709_;
v___y_1690_ = v___y_1710_;
v___y_1691_ = v___y_1711_;
v___y_1692_ = v___y_1712_;
v___y_1693_ = v___y_1713_;
v___y_1694_ = v___y_1714_;
v___y_1695_ = v___y_1715_;
v___y_1696_ = v___y_1719_;
v___y_1697_ = v___y_1716_;
v___y_1698_ = v___y_1717_;
v___y_1699_ = v___y_1718_;
v___y_1700_ = v___y_1719_;
goto v___jp_1683_;
}
else
{
v___y_1684_ = v___y_1704_;
v___y_1685_ = v___y_1705_;
v___y_1686_ = v___y_1706_;
v___y_1687_ = v___y_1707_;
v___y_1688_ = v___y_1708_;
v___y_1689_ = v___y_1709_;
v___y_1690_ = v___y_1710_;
v___y_1691_ = v___y_1711_;
v___y_1692_ = v___y_1712_;
v___y_1693_ = v___y_1713_;
v___y_1694_ = v___y_1714_;
v___y_1695_ = v___y_1715_;
v___y_1696_ = v___y_1719_;
v___y_1697_ = v___y_1716_;
v___y_1698_ = v___y_1717_;
v___y_1699_ = v___y_1718_;
v___y_1700_ = v___y_1703_;
goto v___jp_1683_;
}
}
v___jp_1721_:
{
lean_object* v_declName_x3f_1731_; lean_object* v_macroStack_1732_; uint8_t v_mayPostpone_1733_; uint8_t v_errToSorry_1734_; lean_object* v_autoBoundImplicitContext_1735_; lean_object* v_autoBoundImplicitForbidden_1736_; lean_object* v_sectionVars_1737_; lean_object* v_sectionFVars_1738_; uint8_t v_implicitLambda_1739_; uint8_t v_heedElabAsElim_1740_; uint8_t v_isNoncomputableSection_1741_; uint8_t v_isMetaSection_1742_; uint8_t v_inPattern_1743_; lean_object* v_tacSnap_x3f_1744_; uint8_t v_saveRecAppSyntax_1745_; uint8_t v_holesAsSyntheticOpaque_1746_; uint8_t v_checkDeprecated_1747_; lean_object* v_fixedTermElabs_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___f_1753_; lean_object* v___f_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; 
v_declName_x3f_1731_ = lean_ctor_get(v___y_1725_, 0);
v_macroStack_1732_ = lean_ctor_get(v___y_1725_, 1);
v_mayPostpone_1733_ = lean_ctor_get_uint8(v___y_1725_, sizeof(void*)*8);
v_errToSorry_1734_ = lean_ctor_get_uint8(v___y_1725_, sizeof(void*)*8 + 1);
v_autoBoundImplicitContext_1735_ = lean_ctor_get(v___y_1725_, 2);
v_autoBoundImplicitForbidden_1736_ = lean_ctor_get(v___y_1725_, 3);
v_sectionVars_1737_ = lean_ctor_get(v___y_1725_, 4);
v_sectionFVars_1738_ = lean_ctor_get(v___y_1725_, 5);
v_implicitLambda_1739_ = lean_ctor_get_uint8(v___y_1725_, sizeof(void*)*8 + 2);
v_heedElabAsElim_1740_ = lean_ctor_get_uint8(v___y_1725_, sizeof(void*)*8 + 3);
v_isNoncomputableSection_1741_ = lean_ctor_get_uint8(v___y_1725_, sizeof(void*)*8 + 4);
v_isMetaSection_1742_ = lean_ctor_get_uint8(v___y_1725_, sizeof(void*)*8 + 5);
v_inPattern_1743_ = lean_ctor_get_uint8(v___y_1725_, sizeof(void*)*8 + 7);
v_tacSnap_x3f_1744_ = lean_ctor_get(v___y_1725_, 6);
v_saveRecAppSyntax_1745_ = lean_ctor_get_uint8(v___y_1725_, sizeof(void*)*8 + 8);
v_holesAsSyntheticOpaque_1746_ = lean_ctor_get_uint8(v___y_1725_, sizeof(void*)*8 + 9);
v_checkDeprecated_1747_ = lean_ctor_get_uint8(v___y_1725_, sizeof(void*)*8 + 10);
v_fixedTermElabs_1748_ = lean_ctor_get(v___y_1725_, 7);
v___x_1749_ = lean_unsigned_to_nat(2u);
v___x_1750_ = l_Lean_Syntax_getArg(v_stx_1388_, v___x_1749_);
v___x_1751_ = lean_box(0);
v___x_1752_ = lean_box(v___x_1387_);
lean_inc(v___x_1750_);
v___f_1753_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__1___boxed), 10, 3);
lean_closure_set(v___f_1753_, 0, v___x_1750_);
lean_closure_set(v___f_1753_, 1, v___x_1751_);
lean_closure_set(v___f_1753_, 2, v___x_1752_);
v___f_1754_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__2___boxed), 9, 2);
lean_closure_set(v___f_1754_, 0, v___x_1750_);
lean_closure_set(v___f_1754_, 1, v___f_1753_);
lean_inc_ref(v_fixedTermElabs_1748_);
lean_inc(v_tacSnap_x3f_1744_);
lean_inc(v_sectionFVars_1738_);
lean_inc(v_sectionVars_1737_);
lean_inc_ref(v_autoBoundImplicitForbidden_1736_);
lean_inc(v_autoBoundImplicitContext_1735_);
lean_inc(v_macroStack_1732_);
lean_inc(v_declName_x3f_1731_);
v___x_1755_ = lean_alloc_ctor(0, 8, 11);
lean_ctor_set(v___x_1755_, 0, v_declName_x3f_1731_);
lean_ctor_set(v___x_1755_, 1, v_macroStack_1732_);
lean_ctor_set(v___x_1755_, 2, v_autoBoundImplicitContext_1735_);
lean_ctor_set(v___x_1755_, 3, v_autoBoundImplicitForbidden_1736_);
lean_ctor_set(v___x_1755_, 4, v_sectionVars_1737_);
lean_ctor_set(v___x_1755_, 5, v_sectionFVars_1738_);
lean_ctor_set(v___x_1755_, 6, v_tacSnap_x3f_1744_);
lean_ctor_set(v___x_1755_, 7, v_fixedTermElabs_1748_);
lean_ctor_set_uint8(v___x_1755_, sizeof(void*)*8, v_mayPostpone_1733_);
lean_ctor_set_uint8(v___x_1755_, sizeof(void*)*8 + 1, v_errToSorry_1734_);
lean_ctor_set_uint8(v___x_1755_, sizeof(void*)*8 + 2, v_implicitLambda_1739_);
lean_ctor_set_uint8(v___x_1755_, sizeof(void*)*8 + 3, v_heedElabAsElim_1740_);
lean_ctor_set_uint8(v___x_1755_, sizeof(void*)*8 + 4, v_isNoncomputableSection_1741_);
lean_ctor_set_uint8(v___x_1755_, sizeof(void*)*8 + 5, v_isMetaSection_1742_);
lean_ctor_set_uint8(v___x_1755_, sizeof(void*)*8 + 6, v___x_1387_);
lean_ctor_set_uint8(v___x_1755_, sizeof(void*)*8 + 7, v_inPattern_1743_);
lean_ctor_set_uint8(v___x_1755_, sizeof(void*)*8 + 8, v_saveRecAppSyntax_1745_);
lean_ctor_set_uint8(v___x_1755_, sizeof(void*)*8 + 9, v_holesAsSyntheticOpaque_1746_);
lean_ctor_set_uint8(v___x_1755_, sizeof(void*)*8 + 10, v_checkDeprecated_1747_);
v___x_1756_ = l_Lean_Elab_Term_withoutModifyingElabMetaStateWithInfo___redArg(v___f_1754_, v___x_1755_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_);
lean_dec_ref_known(v___x_1755_, 8);
if (lean_obj_tag(v___x_1756_) == 0)
{
lean_object* v_a_1757_; lean_object* v___x_1758_; 
v_a_1757_ = lean_ctor_get(v___x_1756_, 0);
lean_inc(v_a_1757_);
lean_dec_ref_known(v___x_1756_, 1);
v___x_1758_ = l_Lean_Elab_Tactic_Conv_getLhs___redArg(v___y_1724_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_);
if (lean_obj_tag(v___x_1758_) == 0)
{
lean_object* v_a_1759_; lean_object* v___x_1760_; lean_object* v___f_1761_; lean_object* v___f_1762_; lean_object* v___f_1763_; 
v_a_1759_ = lean_ctor_get(v___x_1758_, 0);
lean_inc(v_a_1759_);
lean_dec_ref_known(v___x_1758_, 1);
v___x_1760_ = lean_box(v___x_1387_);
v___f_1761_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__3___boxed), 11, 2);
lean_closure_set(v___f_1761_, 0, v___x_1751_);
lean_closure_set(v___f_1761_, 1, v___x_1760_);
v___f_1762_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__18));
v___f_1763_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__19));
if (lean_obj_tag(v_occs_1722_) == 0)
{
lean_object* v___x_1764_; 
lean_dec_ref(v___x_1392_);
lean_dec_ref(v___x_1391_);
lean_dec_ref(v___x_1390_);
lean_dec_ref(v___x_1389_);
v___x_1764_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__22));
v___y_1620_ = v_a_1759_;
v___y_1621_ = v_a_1757_;
v___y_1622_ = v___f_1762_;
v___y_1623_ = v___f_1763_;
v___y_1624_ = v___f_1761_;
v_occs_1625_ = v___x_1764_;
v___y_1626_ = v___y_1723_;
v___y_1627_ = v___y_1724_;
v___y_1628_ = v___y_1725_;
v___y_1629_ = v___y_1726_;
v___y_1630_ = v___y_1727_;
v___y_1631_ = v___y_1728_;
v___y_1632_ = v___y_1729_;
v___y_1633_ = v___y_1730_;
goto v___jp_1619_;
}
else
{
lean_object* v_val_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; uint8_t v___x_1768_; 
v_val_1765_ = lean_ctor_get(v_occs_1722_, 0);
lean_inc_n(v_val_1765_, 2);
lean_dec_ref_known(v_occs_1722_, 1);
v___x_1766_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__23));
lean_inc_ref(v___x_1392_);
lean_inc_ref(v___x_1391_);
lean_inc_ref(v___x_1390_);
lean_inc_ref(v___x_1389_);
v___x_1767_ = l_Lean_Name_mkStr5(v___x_1389_, v___x_1390_, v___x_1391_, v___x_1392_, v___x_1766_);
v___x_1768_ = l_Lean_Syntax_isOfKind(v_val_1765_, v___x_1767_);
lean_dec(v___x_1767_);
if (v___x_1768_ == 0)
{
lean_object* v___x_1769_; lean_object* v___x_1770_; uint8_t v___x_1771_; 
v___x_1769_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__24));
v___x_1770_ = l_Lean_Name_mkStr5(v___x_1389_, v___x_1390_, v___x_1391_, v___x_1392_, v___x_1769_);
lean_inc(v_val_1765_);
v___x_1771_ = l_Lean_Syntax_isOfKind(v_val_1765_, v___x_1770_);
lean_dec(v___x_1770_);
if (v___x_1771_ == 0)
{
lean_object* v___x_1772_; lean_object* v_a_1773_; lean_object* v___x_1775_; uint8_t v_isShared_1776_; uint8_t v_isSharedCheck_1780_; 
lean_dec(v_val_1765_);
lean_dec_ref(v___f_1761_);
lean_dec(v_a_1759_);
lean_dec(v_a_1757_);
lean_dec_ref(v___f_1386_);
v___x_1772_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg();
v_a_1773_ = lean_ctor_get(v___x_1772_, 0);
v_isSharedCheck_1780_ = !lean_is_exclusive(v___x_1772_);
if (v_isSharedCheck_1780_ == 0)
{
v___x_1775_ = v___x_1772_;
v_isShared_1776_ = v_isSharedCheck_1780_;
goto v_resetjp_1774_;
}
else
{
lean_inc(v_a_1773_);
lean_dec(v___x_1772_);
v___x_1775_ = lean_box(0);
v_isShared_1776_ = v_isSharedCheck_1780_;
goto v_resetjp_1774_;
}
v_resetjp_1774_:
{
lean_object* v___x_1778_; 
if (v_isShared_1776_ == 0)
{
v___x_1778_ = v___x_1775_;
goto v_reusejp_1777_;
}
else
{
lean_object* v_reuseFailAlloc_1779_; 
v_reuseFailAlloc_1779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1779_, 0, v_a_1773_);
v___x_1778_ = v_reuseFailAlloc_1779_;
goto v_reusejp_1777_;
}
v_reusejp_1777_:
{
return v___x_1778_;
}
}
}
else
{
lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; 
v___x_1781_ = l_Lean_Syntax_getArg(v_val_1765_, v___x_1494_);
lean_dec(v_val_1765_);
v___x_1782_ = l_Lean_Syntax_getArgs(v___x_1781_);
lean_dec(v___x_1781_);
v___x_1783_ = lean_array_get_size(v___x_1782_);
v___x_1784_ = lean_mk_empty_array_with_capacity(v___x_1783_);
v___x_1785_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg(v___x_1782_, v___x_1783_, v___x_1494_, v___x_1784_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_);
lean_dec_ref(v___x_1782_);
if (lean_obj_tag(v___x_1785_) == 0)
{
lean_object* v_a_1786_; lean_object* v___x_1787_; uint8_t v___x_1788_; 
v_a_1786_ = lean_ctor_get(v___x_1785_, 0);
lean_inc(v_a_1786_);
lean_dec_ref_known(v___x_1785_, 1);
v___x_1787_ = lean_array_get_size(v_a_1786_);
v___x_1788_ = lean_nat_dec_eq(v___x_1787_, v___x_1494_);
if (v___x_1788_ == 0)
{
lean_object* v___x_1789_; uint8_t v___x_1790_; 
v___x_1789_ = lean_nat_sub(v___x_1787_, v___x_1495_);
v___x_1790_ = lean_nat_dec_le(v___x_1494_, v___x_1789_);
if (v___x_1790_ == 0)
{
lean_inc(v___x_1789_);
v___y_1703_ = v___x_1789_;
v___y_1704_ = v___y_1725_;
v___y_1705_ = v_a_1759_;
v___y_1706_ = v___x_1787_;
v___y_1707_ = v___f_1762_;
v___y_1708_ = v___y_1730_;
v___y_1709_ = v___y_1723_;
v___y_1710_ = v___f_1763_;
v___y_1711_ = v___y_1727_;
v___y_1712_ = v___y_1729_;
v___y_1713_ = v___y_1728_;
v___y_1714_ = v___y_1724_;
v___y_1715_ = v_a_1757_;
v___y_1716_ = v_a_1786_;
v___y_1717_ = v___f_1761_;
v___y_1718_ = v___y_1726_;
v___y_1719_ = v___x_1789_;
goto v___jp_1702_;
}
else
{
v___y_1703_ = v___x_1789_;
v___y_1704_ = v___y_1725_;
v___y_1705_ = v_a_1759_;
v___y_1706_ = v___x_1787_;
v___y_1707_ = v___f_1762_;
v___y_1708_ = v___y_1730_;
v___y_1709_ = v___y_1723_;
v___y_1710_ = v___f_1763_;
v___y_1711_ = v___y_1727_;
v___y_1712_ = v___y_1729_;
v___y_1713_ = v___y_1728_;
v___y_1714_ = v___y_1724_;
v___y_1715_ = v_a_1757_;
v___y_1716_ = v_a_1786_;
v___y_1717_ = v___f_1761_;
v___y_1718_ = v___y_1726_;
v___y_1719_ = v___x_1494_;
goto v___jp_1702_;
}
}
else
{
v___y_1666_ = v___y_1725_;
v___y_1667_ = v_a_1759_;
v___y_1668_ = v___f_1762_;
v___y_1669_ = v___y_1730_;
v___y_1670_ = v___y_1723_;
v___y_1671_ = v___f_1763_;
v___y_1672_ = v___y_1727_;
v___y_1673_ = v___y_1729_;
v___y_1674_ = v___y_1728_;
v___y_1675_ = v___y_1724_;
v___y_1676_ = v_a_1757_;
v___y_1677_ = v___f_1761_;
v___y_1678_ = v___y_1726_;
v___y_1679_ = v_a_1786_;
goto v___jp_1665_;
}
}
else
{
lean_object* v_a_1791_; lean_object* v___x_1793_; uint8_t v_isShared_1794_; uint8_t v_isSharedCheck_1798_; 
lean_dec_ref(v___f_1761_);
lean_dec(v_a_1759_);
lean_dec(v_a_1757_);
lean_dec_ref(v___f_1386_);
v_a_1791_ = lean_ctor_get(v___x_1785_, 0);
v_isSharedCheck_1798_ = !lean_is_exclusive(v___x_1785_);
if (v_isSharedCheck_1798_ == 0)
{
v___x_1793_ = v___x_1785_;
v_isShared_1794_ = v_isSharedCheck_1798_;
goto v_resetjp_1792_;
}
else
{
lean_inc(v_a_1791_);
lean_dec(v___x_1785_);
v___x_1793_ = lean_box(0);
v_isShared_1794_ = v_isSharedCheck_1798_;
goto v_resetjp_1792_;
}
v_resetjp_1792_:
{
lean_object* v___x_1796_; 
if (v_isShared_1794_ == 0)
{
v___x_1796_ = v___x_1793_;
goto v_reusejp_1795_;
}
else
{
lean_object* v_reuseFailAlloc_1797_; 
v_reuseFailAlloc_1797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1797_, 0, v_a_1791_);
v___x_1796_ = v_reuseFailAlloc_1797_;
goto v_reusejp_1795_;
}
v_reusejp_1795_:
{
return v___x_1796_;
}
}
}
}
}
else
{
lean_object* v___x_1799_; 
lean_dec(v_val_1765_);
lean_dec_ref(v___x_1392_);
lean_dec_ref(v___x_1391_);
lean_dec_ref(v___x_1390_);
lean_dec_ref(v___x_1389_);
v___x_1799_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__26));
v___y_1620_ = v_a_1759_;
v___y_1621_ = v_a_1757_;
v___y_1622_ = v___f_1762_;
v___y_1623_ = v___f_1763_;
v___y_1624_ = v___f_1761_;
v_occs_1625_ = v___x_1799_;
v___y_1626_ = v___y_1723_;
v___y_1627_ = v___y_1724_;
v___y_1628_ = v___y_1725_;
v___y_1629_ = v___y_1726_;
v___y_1630_ = v___y_1727_;
v___y_1631_ = v___y_1728_;
v___y_1632_ = v___y_1729_;
v___y_1633_ = v___y_1730_;
goto v___jp_1619_;
}
}
}
else
{
lean_object* v_a_1800_; lean_object* v___x_1802_; uint8_t v_isShared_1803_; uint8_t v_isSharedCheck_1807_; 
lean_dec(v_a_1757_);
lean_dec(v_occs_1722_);
lean_dec_ref(v___x_1392_);
lean_dec_ref(v___x_1391_);
lean_dec_ref(v___x_1390_);
lean_dec_ref(v___x_1389_);
lean_dec_ref(v___f_1386_);
v_a_1800_ = lean_ctor_get(v___x_1758_, 0);
v_isSharedCheck_1807_ = !lean_is_exclusive(v___x_1758_);
if (v_isSharedCheck_1807_ == 0)
{
v___x_1802_ = v___x_1758_;
v_isShared_1803_ = v_isSharedCheck_1807_;
goto v_resetjp_1801_;
}
else
{
lean_inc(v_a_1800_);
lean_dec(v___x_1758_);
v___x_1802_ = lean_box(0);
v_isShared_1803_ = v_isSharedCheck_1807_;
goto v_resetjp_1801_;
}
v_resetjp_1801_:
{
lean_object* v___x_1805_; 
if (v_isShared_1803_ == 0)
{
v___x_1805_ = v___x_1802_;
goto v_reusejp_1804_;
}
else
{
lean_object* v_reuseFailAlloc_1806_; 
v_reuseFailAlloc_1806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1806_, 0, v_a_1800_);
v___x_1805_ = v_reuseFailAlloc_1806_;
goto v_reusejp_1804_;
}
v_reusejp_1804_:
{
return v___x_1805_;
}
}
}
}
else
{
lean_object* v_a_1808_; lean_object* v___x_1810_; uint8_t v_isShared_1811_; uint8_t v_isSharedCheck_1815_; 
lean_dec(v_occs_1722_);
lean_dec_ref(v___x_1392_);
lean_dec_ref(v___x_1391_);
lean_dec_ref(v___x_1390_);
lean_dec_ref(v___x_1389_);
lean_dec_ref(v___f_1386_);
v_a_1808_ = lean_ctor_get(v___x_1756_, 0);
v_isSharedCheck_1815_ = !lean_is_exclusive(v___x_1756_);
if (v_isSharedCheck_1815_ == 0)
{
v___x_1810_ = v___x_1756_;
v_isShared_1811_ = v_isSharedCheck_1815_;
goto v_resetjp_1809_;
}
else
{
lean_inc(v_a_1808_);
lean_dec(v___x_1756_);
v___x_1810_ = lean_box(0);
v_isShared_1811_ = v_isSharedCheck_1815_;
goto v_resetjp_1809_;
}
v_resetjp_1809_:
{
lean_object* v___x_1813_; 
if (v_isShared_1811_ == 0)
{
v___x_1813_ = v___x_1810_;
goto v_reusejp_1812_;
}
else
{
lean_object* v_reuseFailAlloc_1814_; 
v_reuseFailAlloc_1814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1814_, 0, v_a_1808_);
v___x_1813_ = v_reuseFailAlloc_1814_;
goto v_reusejp_1812_;
}
v_reusejp_1812_:
{
return v___x_1813_;
}
}
}
}
}
v___jp_1402_:
{
lean_object* v___x_1413_; 
v___x_1413_ = l_Lean_Elab_Tactic_Conv_getRhs___redArg(v___y_1406_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_);
if (lean_obj_tag(v___x_1413_) == 0)
{
lean_object* v_a_1414_; lean_object* v_expr_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; 
v_a_1414_ = lean_ctor_get(v___x_1413_, 0);
lean_inc(v_a_1414_);
lean_dec_ref_known(v___x_1413_, 1);
v_expr_1415_ = lean_ctor_get(v___y_1403_, 0);
v___x_1416_ = l_Lean_Expr_mvarId_x21(v_a_1414_);
lean_dec(v_a_1414_);
lean_inc_ref(v_expr_1415_);
v___x_1417_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3___redArg(v___x_1416_, v_expr_1415_, v___y_1410_);
lean_dec_ref(v___x_1417_);
v___x_1418_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_1406_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_);
if (lean_obj_tag(v___x_1418_) == 0)
{
lean_object* v_a_1419_; lean_object* v___x_1420_; 
v_a_1419_ = lean_ctor_get(v___x_1418_, 0);
lean_inc(v_a_1419_);
lean_dec_ref_known(v___x_1418_, 1);
v___x_1420_ = l_Lean_Meta_Simp_Result_getProof(v___y_1403_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_);
if (lean_obj_tag(v___x_1420_) == 0)
{
lean_object* v_a_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; 
v_a_1421_ = lean_ctor_get(v___x_1420_, 0);
lean_inc(v_a_1421_);
lean_dec_ref_known(v___x_1420_, 1);
v___x_1422_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3___redArg(v_a_1419_, v_a_1421_, v___y_1410_);
lean_dec_ref(v___x_1422_);
v___x_1423_ = lean_array_to_list(v_subgoals_1404_);
v___x_1424_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_1423_, v___y_1406_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_);
return v___x_1424_;
}
else
{
lean_object* v_a_1425_; lean_object* v___x_1427_; uint8_t v_isShared_1428_; uint8_t v_isSharedCheck_1432_; 
lean_dec(v_a_1419_);
lean_dec_ref(v_subgoals_1404_);
v_a_1425_ = lean_ctor_get(v___x_1420_, 0);
v_isSharedCheck_1432_ = !lean_is_exclusive(v___x_1420_);
if (v_isSharedCheck_1432_ == 0)
{
v___x_1427_ = v___x_1420_;
v_isShared_1428_ = v_isSharedCheck_1432_;
goto v_resetjp_1426_;
}
else
{
lean_inc(v_a_1425_);
lean_dec(v___x_1420_);
v___x_1427_ = lean_box(0);
v_isShared_1428_ = v_isSharedCheck_1432_;
goto v_resetjp_1426_;
}
v_resetjp_1426_:
{
lean_object* v___x_1430_; 
if (v_isShared_1428_ == 0)
{
v___x_1430_ = v___x_1427_;
goto v_reusejp_1429_;
}
else
{
lean_object* v_reuseFailAlloc_1431_; 
v_reuseFailAlloc_1431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1431_, 0, v_a_1425_);
v___x_1430_ = v_reuseFailAlloc_1431_;
goto v_reusejp_1429_;
}
v_reusejp_1429_:
{
return v___x_1430_;
}
}
}
}
else
{
lean_object* v_a_1433_; lean_object* v___x_1435_; uint8_t v_isShared_1436_; uint8_t v_isSharedCheck_1440_; 
lean_dec_ref(v_subgoals_1404_);
lean_dec_ref(v___y_1403_);
v_a_1433_ = lean_ctor_get(v___x_1418_, 0);
v_isSharedCheck_1440_ = !lean_is_exclusive(v___x_1418_);
if (v_isSharedCheck_1440_ == 0)
{
v___x_1435_ = v___x_1418_;
v_isShared_1436_ = v_isSharedCheck_1440_;
goto v_resetjp_1434_;
}
else
{
lean_inc(v_a_1433_);
lean_dec(v___x_1418_);
v___x_1435_ = lean_box(0);
v_isShared_1436_ = v_isSharedCheck_1440_;
goto v_resetjp_1434_;
}
v_resetjp_1434_:
{
lean_object* v___x_1438_; 
if (v_isShared_1436_ == 0)
{
v___x_1438_ = v___x_1435_;
goto v_reusejp_1437_;
}
else
{
lean_object* v_reuseFailAlloc_1439_; 
v_reuseFailAlloc_1439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1439_, 0, v_a_1433_);
v___x_1438_ = v_reuseFailAlloc_1439_;
goto v_reusejp_1437_;
}
v_reusejp_1437_:
{
return v___x_1438_;
}
}
}
}
else
{
lean_object* v_a_1441_; lean_object* v___x_1443_; uint8_t v_isShared_1444_; uint8_t v_isSharedCheck_1448_; 
lean_dec_ref(v_subgoals_1404_);
lean_dec_ref(v___y_1403_);
v_a_1441_ = lean_ctor_get(v___x_1413_, 0);
v_isSharedCheck_1448_ = !lean_is_exclusive(v___x_1413_);
if (v_isSharedCheck_1448_ == 0)
{
v___x_1443_ = v___x_1413_;
v_isShared_1444_ = v_isSharedCheck_1448_;
goto v_resetjp_1442_;
}
else
{
lean_inc(v_a_1441_);
lean_dec(v___x_1413_);
v___x_1443_ = lean_box(0);
v_isShared_1444_ = v_isSharedCheck_1448_;
goto v_resetjp_1442_;
}
v_resetjp_1442_:
{
lean_object* v___x_1446_; 
if (v_isShared_1444_ == 0)
{
v___x_1446_ = v___x_1443_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1447_; 
v_reuseFailAlloc_1447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1447_, 0, v_a_1441_);
v___x_1446_ = v_reuseFailAlloc_1447_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
return v___x_1446_;
}
}
}
}
v___jp_1449_:
{
size_t v_sz_1460_; size_t v___x_1461_; lean_object* v___x_1462_; 
v_sz_1460_ = lean_array_size(v___y_1459_);
v___x_1461_ = ((size_t)0ULL);
v___x_1462_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__5(v_sz_1460_, v___x_1461_, v___y_1459_);
v___y_1403_ = v___y_1453_;
v_subgoals_1404_ = v___x_1462_;
v___y_1405_ = v___y_1456_;
v___y_1406_ = v___y_1452_;
v___y_1407_ = v___y_1454_;
v___y_1408_ = v___y_1458_;
v___y_1409_ = v___y_1451_;
v___y_1410_ = v___y_1455_;
v___y_1411_ = v___y_1450_;
v___y_1412_ = v___y_1457_;
goto v___jp_1402_;
}
v___jp_1463_:
{
lean_object* v___x_1477_; 
v___x_1477_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg(v___y_1472_, v___y_1466_, v___y_1465_, v___y_1476_);
lean_dec(v___y_1476_);
lean_dec(v___y_1472_);
v___y_1450_ = v___y_1464_;
v___y_1451_ = v___y_1470_;
v___y_1452_ = v___y_1471_;
v___y_1453_ = v___y_1473_;
v___y_1454_ = v___y_1467_;
v___y_1455_ = v___y_1468_;
v___y_1456_ = v___y_1474_;
v___y_1457_ = v___y_1475_;
v___y_1458_ = v___y_1469_;
v___y_1459_ = v___x_1477_;
goto v___jp_1449_;
}
v___jp_1478_:
{
uint8_t v___x_1492_; 
v___x_1492_ = lean_nat_dec_le(v___y_1491_, v___y_1480_);
if (v___x_1492_ == 0)
{
lean_dec(v___y_1480_);
lean_inc(v___y_1491_);
v___y_1464_ = v___y_1479_;
v___y_1465_ = v___y_1491_;
v___y_1466_ = v___y_1481_;
v___y_1467_ = v___y_1482_;
v___y_1468_ = v___y_1483_;
v___y_1469_ = v___y_1484_;
v___y_1470_ = v___y_1485_;
v___y_1471_ = v___y_1486_;
v___y_1472_ = v___y_1487_;
v___y_1473_ = v___y_1488_;
v___y_1474_ = v___y_1489_;
v___y_1475_ = v___y_1490_;
v___y_1476_ = v___y_1491_;
goto v___jp_1463_;
}
else
{
v___y_1464_ = v___y_1479_;
v___y_1465_ = v___y_1491_;
v___y_1466_ = v___y_1481_;
v___y_1467_ = v___y_1482_;
v___y_1468_ = v___y_1483_;
v___y_1469_ = v___y_1484_;
v___y_1470_ = v___y_1485_;
v___y_1471_ = v___y_1486_;
v___y_1472_ = v___y_1487_;
v___y_1473_ = v___y_1488_;
v___y_1474_ = v___y_1489_;
v___y_1475_ = v___y_1490_;
v___y_1476_ = v___y_1480_;
goto v___jp_1463_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___boxed(lean_object** _args){
lean_object* v___x_1829_ = _args[0];
lean_object* v___f_1830_ = _args[1];
lean_object* v___x_1831_ = _args[2];
lean_object* v_stx_1832_ = _args[3];
lean_object* v___x_1833_ = _args[4];
lean_object* v___x_1834_ = _args[5];
lean_object* v___x_1835_ = _args[6];
lean_object* v___x_1836_ = _args[7];
lean_object* v___y_1837_ = _args[8];
lean_object* v___y_1838_ = _args[9];
lean_object* v___y_1839_ = _args[10];
lean_object* v___y_1840_ = _args[11];
lean_object* v___y_1841_ = _args[12];
lean_object* v___y_1842_ = _args[13];
lean_object* v___y_1843_ = _args[14];
lean_object* v___y_1844_ = _args[15];
lean_object* v___y_1845_ = _args[16];
_start:
{
uint8_t v___x_19458__boxed_1846_; uint8_t v___x_19460__boxed_1847_; lean_object* v_res_1848_; 
v___x_19458__boxed_1846_ = lean_unbox(v___x_1829_);
v___x_19460__boxed_1847_ = lean_unbox(v___x_1831_);
v_res_1848_ = l_Lean_Elab_Tactic_Conv_evalPattern___lam__6(v___x_19458__boxed_1846_, v___f_1830_, v___x_19460__boxed_1847_, v_stx_1832_, v___x_1833_, v___x_1834_, v___x_1835_, v___x_1836_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_);
lean_dec(v___y_1844_);
lean_dec_ref(v___y_1843_);
lean_dec(v___y_1842_);
lean_dec_ref(v___y_1841_);
lean_dec(v___y_1840_);
lean_dec_ref(v___y_1839_);
lean_dec(v___y_1838_);
lean_dec_ref(v___y_1837_);
lean_dec(v_stx_1832_);
return v_res_1848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern(lean_object* v_stx_1861_, lean_object* v_a_1862_, lean_object* v_a_1863_, lean_object* v_a_1864_, lean_object* v_a_1865_, lean_object* v_a_1866_, lean_object* v_a_1867_, lean_object* v_a_1868_, lean_object* v_a_1869_){
_start:
{
lean_object* v___f_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; uint8_t v___x_1877_; uint8_t v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___y_1881_; lean_object* v___x_1882_; 
v___f_1871_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___closed__0));
v___x_1872_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___closed__1));
v___x_1873_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___closed__2));
v___x_1874_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___closed__3));
v___x_1875_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___closed__4));
v___x_1876_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___closed__6));
lean_inc(v_stx_1861_);
v___x_1877_ = l_Lean_Syntax_isOfKind(v_stx_1861_, v___x_1876_);
v___x_1878_ = 1;
v___x_1879_ = lean_box(v___x_1877_);
v___x_1880_ = lean_box(v___x_1878_);
v___y_1881_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___boxed), 17, 8);
lean_closure_set(v___y_1881_, 0, v___x_1879_);
lean_closure_set(v___y_1881_, 1, v___f_1871_);
lean_closure_set(v___y_1881_, 2, v___x_1880_);
lean_closure_set(v___y_1881_, 3, v_stx_1861_);
lean_closure_set(v___y_1881_, 4, v___x_1872_);
lean_closure_set(v___y_1881_, 5, v___x_1873_);
lean_closure_set(v___y_1881_, 6, v___x_1874_);
lean_closure_set(v___y_1881_, 7, v___x_1875_);
v___x_1882_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___y_1881_, v_a_1862_, v_a_1863_, v_a_1864_, v_a_1865_, v_a_1866_, v_a_1867_, v_a_1868_, v_a_1869_);
return v___x_1882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___boxed(lean_object* v_stx_1883_, lean_object* v_a_1884_, lean_object* v_a_1885_, lean_object* v_a_1886_, lean_object* v_a_1887_, lean_object* v_a_1888_, lean_object* v_a_1889_, lean_object* v_a_1890_, lean_object* v_a_1891_, lean_object* v_a_1892_){
_start:
{
lean_object* v_res_1893_; 
v_res_1893_ = l_Lean_Elab_Tactic_Conv_evalPattern(v_stx_1883_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_, v_a_1891_);
lean_dec(v_a_1891_);
lean_dec_ref(v_a_1890_);
lean_dec(v_a_1889_);
lean_dec_ref(v_a_1888_);
lean_dec(v_a_1887_);
lean_dec_ref(v_a_1886_);
lean_dec(v_a_1885_);
lean_dec_ref(v_a_1884_);
return v_res_1893_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1(lean_object* v_00_u03b1_1894_, lean_object* v_ref_1895_, lean_object* v_msg_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_){
_start:
{
lean_object* v___x_1906_; 
v___x_1906_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1___redArg(v_ref_1895_, v_msg_1896_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_);
return v___x_1906_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1___boxed(lean_object* v_00_u03b1_1907_, lean_object* v_ref_1908_, lean_object* v_msg_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_){
_start:
{
lean_object* v_res_1919_; 
v_res_1919_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1(v_00_u03b1_1907_, v_ref_1908_, v_msg_1909_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_);
lean_dec(v___y_1917_);
lean_dec_ref(v___y_1916_);
lean_dec(v___y_1915_);
lean_dec_ref(v___y_1914_);
lean_dec(v___y_1913_);
lean_dec_ref(v___y_1912_);
lean_dec(v___y_1911_);
lean_dec_ref(v___y_1910_);
lean_dec(v_ref_1908_);
return v_res_1919_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3(lean_object* v_mvarId_1920_, lean_object* v_val_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_){
_start:
{
lean_object* v___x_1931_; 
v___x_1931_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3___redArg(v_mvarId_1920_, v_val_1921_, v___y_1927_);
return v___x_1931_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3___boxed(lean_object* v_mvarId_1932_, lean_object* v_val_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_){
_start:
{
lean_object* v_res_1943_; 
v_res_1943_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3(v_mvarId_1932_, v_val_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_);
lean_dec(v___y_1941_);
lean_dec_ref(v___y_1940_);
lean_dec(v___y_1939_);
lean_dec_ref(v___y_1938_);
lean_dec(v___y_1937_);
lean_dec_ref(v___y_1936_);
lean_dec(v___y_1935_);
lean_dec_ref(v___y_1934_);
return v_res_1943_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4(lean_object* v_00_u03b1_1944_, lean_object* v_msg_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_){
_start:
{
lean_object* v___x_1955_; 
v___x_1955_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg(v_msg_1945_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_);
return v___x_1955_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___boxed(lean_object* v_00_u03b1_1956_, lean_object* v_msg_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_){
_start:
{
lean_object* v_res_1967_; 
v_res_1967_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4(v_00_u03b1_1956_, v_msg_1957_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_);
lean_dec(v___y_1965_);
lean_dec_ref(v___y_1964_);
lean_dec(v___y_1963_);
lean_dec_ref(v___y_1962_);
lean_dec(v___y_1961_);
lean_dec_ref(v___y_1960_);
lean_dec(v___y_1959_);
lean_dec_ref(v___y_1958_);
return v_res_1967_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6(lean_object* v_n_1968_, lean_object* v_as_1969_, lean_object* v_lo_1970_, lean_object* v_hi_1971_, lean_object* v_w_1972_, lean_object* v_hlo_1973_, lean_object* v_hhi_1974_){
_start:
{
lean_object* v___x_1975_; 
v___x_1975_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg(v_n_1968_, v_as_1969_, v_lo_1970_, v_hi_1971_);
return v___x_1975_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___boxed(lean_object* v_n_1976_, lean_object* v_as_1977_, lean_object* v_lo_1978_, lean_object* v_hi_1979_, lean_object* v_w_1980_, lean_object* v_hlo_1981_, lean_object* v_hhi_1982_){
_start:
{
lean_object* v_res_1983_; 
v_res_1983_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6(v_n_1976_, v_as_1977_, v_lo_1978_, v_hi_1979_, v_w_1980_, v_hlo_1981_, v_hhi_1982_);
lean_dec(v_hi_1979_);
lean_dec(v_n_1976_);
return v_res_1983_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7(lean_object* v_as_1984_, lean_object* v_i_1985_, lean_object* v_j_1986_, lean_object* v_inv_1987_, lean_object* v_bs_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_){
_start:
{
lean_object* v___x_1998_; 
v___x_1998_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg(v_as_1984_, v_i_1985_, v_j_1986_, v_bs_1988_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_);
return v___x_1998_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___boxed(lean_object* v_as_1999_, lean_object* v_i_2000_, lean_object* v_j_2001_, lean_object* v_inv_2002_, lean_object* v_bs_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_){
_start:
{
lean_object* v_res_2013_; 
v_res_2013_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7(v_as_1999_, v_i_2000_, v_j_2001_, v_inv_2002_, v_bs_2003_, v___y_2004_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_);
lean_dec(v___y_2011_);
lean_dec_ref(v___y_2010_);
lean_dec(v___y_2009_);
lean_dec_ref(v___y_2008_);
lean_dec(v___y_2007_);
lean_dec_ref(v___y_2006_);
lean_dec(v___y_2005_);
lean_dec_ref(v___y_2004_);
lean_dec_ref(v_as_1999_);
return v_res_2013_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9(lean_object* v_n_2014_, lean_object* v_as_2015_, lean_object* v_lo_2016_, lean_object* v_hi_2017_, lean_object* v_w_2018_, lean_object* v_hlo_2019_, lean_object* v_hhi_2020_){
_start:
{
lean_object* v___x_2021_; 
v___x_2021_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg(v_n_2014_, v_as_2015_, v_lo_2016_, v_hi_2017_);
return v___x_2021_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___boxed(lean_object* v_n_2022_, lean_object* v_as_2023_, lean_object* v_lo_2024_, lean_object* v_hi_2025_, lean_object* v_w_2026_, lean_object* v_hlo_2027_, lean_object* v_hhi_2028_){
_start:
{
lean_object* v_res_2029_; 
v_res_2029_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9(v_n_2022_, v_as_2023_, v_lo_2024_, v_hi_2025_, v_w_2026_, v_hlo_2027_, v_hhi_2028_);
lean_dec(v_hi_2025_);
lean_dec(v_n_2022_);
return v_res_2029_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3(lean_object* v_00_u03b2_2030_, lean_object* v_x_2031_, lean_object* v_x_2032_, lean_object* v_x_2033_){
_start:
{
lean_object* v___x_2034_; 
v___x_2034_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3___redArg(v_x_2031_, v_x_2032_, v_x_2033_);
return v___x_2034_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6_spec__8(lean_object* v_n_2035_, lean_object* v_lo_2036_, lean_object* v_hi_2037_, lean_object* v_hhi_2038_, lean_object* v_pivot_2039_, lean_object* v_as_2040_, lean_object* v_i_2041_, lean_object* v_k_2042_, lean_object* v_ilo_2043_, lean_object* v_ik_2044_, lean_object* v_w_2045_){
_start:
{
lean_object* v___x_2046_; 
v___x_2046_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6_spec__8___redArg(v_hi_2037_, v_pivot_2039_, v_as_2040_, v_i_2041_, v_k_2042_);
return v___x_2046_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6_spec__8___boxed(lean_object* v_n_2047_, lean_object* v_lo_2048_, lean_object* v_hi_2049_, lean_object* v_hhi_2050_, lean_object* v_pivot_2051_, lean_object* v_as_2052_, lean_object* v_i_2053_, lean_object* v_k_2054_, lean_object* v_ilo_2055_, lean_object* v_ik_2056_, lean_object* v_w_2057_){
_start:
{
lean_object* v_res_2058_; 
v_res_2058_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6_spec__8(v_n_2047_, v_lo_2048_, v_hi_2049_, v_hhi_2050_, v_pivot_2051_, v_as_2052_, v_i_2053_, v_k_2054_, v_ilo_2055_, v_ik_2056_, v_w_2057_);
lean_dec_ref(v_pivot_2051_);
lean_dec(v_hi_2049_);
lean_dec(v_lo_2048_);
lean_dec(v_n_2047_);
return v_res_2058_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9_spec__13(lean_object* v_n_2059_, lean_object* v_lo_2060_, lean_object* v_hi_2061_, lean_object* v_hhi_2062_, lean_object* v_pivot_2063_, lean_object* v_as_2064_, lean_object* v_i_2065_, lean_object* v_k_2066_, lean_object* v_ilo_2067_, lean_object* v_ik_2068_, lean_object* v_w_2069_){
_start:
{
lean_object* v___x_2070_; 
v___x_2070_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9_spec__13___redArg(v_hi_2061_, v_pivot_2063_, v_as_2064_, v_i_2065_, v_k_2066_);
return v___x_2070_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9_spec__13___boxed(lean_object* v_n_2071_, lean_object* v_lo_2072_, lean_object* v_hi_2073_, lean_object* v_hhi_2074_, lean_object* v_pivot_2075_, lean_object* v_as_2076_, lean_object* v_i_2077_, lean_object* v_k_2078_, lean_object* v_ilo_2079_, lean_object* v_ik_2080_, lean_object* v_w_2081_){
_start:
{
lean_object* v_res_2082_; 
v_res_2082_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9_spec__13(v_n_2071_, v_lo_2072_, v_hi_2073_, v_hhi_2074_, v_pivot_2075_, v_as_2076_, v_i_2077_, v_k_2078_, v_ilo_2079_, v_ik_2080_, v_w_2081_);
lean_dec_ref(v_pivot_2075_);
lean_dec(v_hi_2073_);
lean_dec(v_lo_2072_);
lean_dec(v_n_2071_);
return v_res_2082_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4(lean_object* v_00_u03b2_2083_, lean_object* v_x_2084_, size_t v_x_2085_, size_t v_x_2086_, lean_object* v_x_2087_, lean_object* v_x_2088_){
_start:
{
lean_object* v___x_2089_; 
v___x_2089_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg(v_x_2084_, v_x_2085_, v_x_2086_, v_x_2087_, v_x_2088_);
return v___x_2089_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___boxed(lean_object* v_00_u03b2_2090_, lean_object* v_x_2091_, lean_object* v_x_2092_, lean_object* v_x_2093_, lean_object* v_x_2094_, lean_object* v_x_2095_){
_start:
{
size_t v_x_20576__boxed_2096_; size_t v_x_20577__boxed_2097_; lean_object* v_res_2098_; 
v_x_20576__boxed_2096_ = lean_unbox_usize(v_x_2092_);
lean_dec(v_x_2092_);
v_x_20577__boxed_2097_ = lean_unbox_usize(v_x_2093_);
lean_dec(v_x_2093_);
v_res_2098_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4(v_00_u03b2_2090_, v_x_2091_, v_x_20576__boxed_2096_, v_x_20577__boxed_2097_, v_x_2094_, v_x_2095_);
return v_res_2098_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11_spec__13(lean_object* v_as_2099_, lean_object* v_a_2100_, lean_object* v_x_2101_, lean_object* v_x_2102_){
_start:
{
uint8_t v___x_2103_; 
v___x_2103_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11_spec__13___redArg(v_as_2099_, v_a_2100_, v_x_2101_);
return v___x_2103_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11_spec__13___boxed(lean_object* v_as_2104_, lean_object* v_a_2105_, lean_object* v_x_2106_, lean_object* v_x_2107_){
_start:
{
uint8_t v_res_2108_; lean_object* v_r_2109_; 
v_res_2108_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11_spec__13(v_as_2104_, v_a_2105_, v_x_2106_, v_x_2107_);
lean_dec_ref(v_a_2105_);
lean_dec_ref(v_as_2104_);
v_r_2109_ = lean_box(v_res_2108_);
return v_r_2109_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__12(lean_object* v_00_u03b2_2110_, lean_object* v_n_2111_, lean_object* v_k_2112_, lean_object* v_v_2113_){
_start:
{
lean_object* v___x_2114_; 
v___x_2114_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__12___redArg(v_n_2111_, v_k_2112_, v_v_2113_);
return v___x_2114_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__13(lean_object* v_00_u03b2_2115_, size_t v_depth_2116_, lean_object* v_keys_2117_, lean_object* v_vals_2118_, lean_object* v_heq_2119_, lean_object* v_i_2120_, lean_object* v_entries_2121_){
_start:
{
lean_object* v___x_2122_; 
v___x_2122_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__13___redArg(v_depth_2116_, v_keys_2117_, v_vals_2118_, v_i_2120_, v_entries_2121_);
return v___x_2122_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__13___boxed(lean_object* v_00_u03b2_2123_, lean_object* v_depth_2124_, lean_object* v_keys_2125_, lean_object* v_vals_2126_, lean_object* v_heq_2127_, lean_object* v_i_2128_, lean_object* v_entries_2129_){
_start:
{
size_t v_depth_boxed_2130_; lean_object* v_res_2131_; 
v_depth_boxed_2130_ = lean_unbox_usize(v_depth_2124_);
lean_dec(v_depth_2124_);
v_res_2131_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__13(v_00_u03b2_2123_, v_depth_boxed_2130_, v_keys_2125_, v_vals_2126_, v_heq_2127_, v_i_2128_, v_entries_2129_);
lean_dec_ref(v_vals_2126_);
lean_dec_ref(v_keys_2125_);
return v_res_2131_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__12_spec__16(lean_object* v_00_u03b2_2132_, lean_object* v_x_2133_, lean_object* v_x_2134_, lean_object* v_x_2135_, lean_object* v_x_2136_){
_start:
{
lean_object* v___x_2137_; 
v___x_2137_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__12_spec__16___redArg(v_x_2133_, v_x_2134_, v_x_2135_, v_x_2136_);
return v___x_2137_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1(){
_start:
{
lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; 
v___x_2147_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2148_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___closed__6));
v___x_2149_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___closed__2));
v___x_2150_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalPattern___boxed), 10, 0);
v___x_2151_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2147_, v___x_2148_, v___x_2149_, v___x_2150_);
return v___x_2151_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___boxed(lean_object* v_a_2152_){
_start:
{
lean_object* v_res_2153_; 
v_res_2153_ = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1();
return v_res_2153_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3(){
_start:
{
lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; 
v___x_2180_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___closed__2));
v___x_2181_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__6));
v___x_2182_ = l_Lean_addBuiltinDeclarationRanges(v___x_2180_, v___x_2181_);
return v___x_2182_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___boxed(lean_object* v_a_2183_){
_start:
{
lean_object* v_res_2184_; 
v_res_2184_ = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3();
return v_res_2184_;
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
