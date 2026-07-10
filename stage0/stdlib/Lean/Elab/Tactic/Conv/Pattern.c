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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_bool_not(uint8_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_toHeadIndex(lean_object*);
uint8_t l_Lean_instBEqHeadIndex_beq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEqGuarded(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_st_ref_get(lean_object*);
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
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withoutErrToSorryImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withoutModifyingElabMetaStateWithInfo___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Conv_getLhs___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_TSyntax_getNat(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "positive integer expected"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_47_; lean_object* v___x_48_; uint8_t v___x_49_; uint8_t v___x_50_; 
lean_inc_ref(v_e_41_);
v___x_47_ = l_Lean_Expr_toHeadIndex(v_e_41_);
lean_inc_ref(v_pattern_40_);
v___x_48_ = l_Lean_Expr_toHeadIndex(v_pattern_40_);
v___x_49_ = l_Lean_instBEqHeadIndex_beq(v___x_47_, v___x_48_);
lean_dec(v___x_48_);
lean_dec(v___x_47_);
v___x_50_ = lean_bool_not(v___x_49_);
if (v___x_50_ == 0)
{
lean_object* v___x_51_; 
lean_inc_ref(v_e_41_);
lean_inc_ref(v_pattern_40_);
v___x_51_ = l_Lean_Meta_isExprDefEqGuarded(v_pattern_40_, v_e_41_, v_a_42_, v_a_43_, v_a_44_, v_a_45_);
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
v___x_57_ = l_Lean_Expr_isApp(v_e_41_);
if (v___x_57_ == 0)
{
lean_object* v___x_58_; lean_object* v___x_60_; 
lean_dec_ref(v_e_41_);
lean_dec_ref(v_pattern_40_);
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
v___x_62_ = l_Lean_Expr_appFn_x21(v_e_41_);
v___x_63_ = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_matchPattern_x3f_go_x3f(v_pattern_40_, v___x_62_, v_a_42_, v_a_43_, v_a_44_, v_a_45_);
if (lean_obj_tag(v___x_63_) == 0)
{
lean_object* v_a_64_; 
v_a_64_ = lean_ctor_get(v___x_63_, 0);
lean_inc(v_a_64_);
if (lean_obj_tag(v_a_64_) == 0)
{
lean_dec_ref(v_e_41_);
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
v___x_77_ = l_Lean_Expr_appArg_x21(v_e_41_);
lean_dec_ref(v_e_41_);
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
lean_dec_ref(v_e_41_);
return v___x_63_;
}
}
}
else
{
lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_96_; 
lean_dec_ref(v_pattern_40_);
v___x_92_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_matchPattern_x3f_go_x3f___closed__0));
v___x_93_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_93_, 0, v_e_41_);
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
lean_dec_ref(v_e_41_);
lean_dec_ref(v_pattern_40_);
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
else
{
lean_object* v___x_107_; lean_object* v___x_108_; 
lean_dec_ref(v_e_41_);
lean_dec_ref(v_pattern_40_);
v___x_107_ = lean_box(0);
v___x_108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_108_, 0, v___x_107_);
return v___x_108_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_matchPattern_x3f_go_x3f___boxed(lean_object* v_pattern_109_, lean_object* v_e_110_, lean_object* v_a_111_, lean_object* v_a_112_, lean_object* v_a_113_, lean_object* v_a_114_, lean_object* v_a_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_matchPattern_x3f_go_x3f(v_pattern_109_, v_e_110_, v_a_111_, v_a_112_, v_a_113_, v_a_114_);
lean_dec(v_a_114_);
lean_dec_ref(v_a_113_);
lean_dec(v_a_112_);
lean_dec_ref(v_a_111_);
return v_res_116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Conv_matchPattern_x3f_spec__0___redArg(lean_object* v_k_117_, uint8_t v_allowLevelAssignments_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_){
_start:
{
lean_object* v___x_124_; 
v___x_124_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_118_, v_k_117_, v___y_119_, v___y_120_, v___y_121_, v___y_122_);
if (lean_obj_tag(v___x_124_) == 0)
{
lean_object* v_a_125_; lean_object* v___x_127_; uint8_t v_isShared_128_; uint8_t v_isSharedCheck_132_; 
v_a_125_ = lean_ctor_get(v___x_124_, 0);
v_isSharedCheck_132_ = !lean_is_exclusive(v___x_124_);
if (v_isSharedCheck_132_ == 0)
{
v___x_127_ = v___x_124_;
v_isShared_128_ = v_isSharedCheck_132_;
goto v_resetjp_126_;
}
else
{
lean_inc(v_a_125_);
lean_dec(v___x_124_);
v___x_127_ = lean_box(0);
v_isShared_128_ = v_isSharedCheck_132_;
goto v_resetjp_126_;
}
v_resetjp_126_:
{
lean_object* v___x_130_; 
if (v_isShared_128_ == 0)
{
v___x_130_ = v___x_127_;
goto v_reusejp_129_;
}
else
{
lean_object* v_reuseFailAlloc_131_; 
v_reuseFailAlloc_131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_131_, 0, v_a_125_);
v___x_130_ = v_reuseFailAlloc_131_;
goto v_reusejp_129_;
}
v_reusejp_129_:
{
return v___x_130_;
}
}
}
else
{
lean_object* v_a_133_; lean_object* v___x_135_; uint8_t v_isShared_136_; uint8_t v_isSharedCheck_140_; 
v_a_133_ = lean_ctor_get(v___x_124_, 0);
v_isSharedCheck_140_ = !lean_is_exclusive(v___x_124_);
if (v_isSharedCheck_140_ == 0)
{
v___x_135_ = v___x_124_;
v_isShared_136_ = v_isSharedCheck_140_;
goto v_resetjp_134_;
}
else
{
lean_inc(v_a_133_);
lean_dec(v___x_124_);
v___x_135_ = lean_box(0);
v_isShared_136_ = v_isSharedCheck_140_;
goto v_resetjp_134_;
}
v_resetjp_134_:
{
lean_object* v___x_138_; 
if (v_isShared_136_ == 0)
{
v___x_138_ = v___x_135_;
goto v_reusejp_137_;
}
else
{
lean_object* v_reuseFailAlloc_139_; 
v_reuseFailAlloc_139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_139_, 0, v_a_133_);
v___x_138_ = v_reuseFailAlloc_139_;
goto v_reusejp_137_;
}
v_reusejp_137_:
{
return v___x_138_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Conv_matchPattern_x3f_spec__0___redArg___boxed(lean_object* v_k_141_, lean_object* v_allowLevelAssignments_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_148_; lean_object* v_res_149_; 
v_allowLevelAssignments_boxed_148_ = lean_unbox(v_allowLevelAssignments_142_);
v_res_149_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Conv_matchPattern_x3f_spec__0___redArg(v_k_141_, v_allowLevelAssignments_boxed_148_, v___y_143_, v___y_144_, v___y_145_, v___y_146_);
lean_dec(v___y_146_);
lean_dec_ref(v___y_145_);
lean_dec(v___y_144_);
lean_dec_ref(v___y_143_);
return v_res_149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Conv_matchPattern_x3f_spec__0(lean_object* v_00_u03b1_150_, lean_object* v_k_151_, uint8_t v_allowLevelAssignments_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_){
_start:
{
lean_object* v___x_158_; 
v___x_158_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Conv_matchPattern_x3f_spec__0___redArg(v_k_151_, v_allowLevelAssignments_152_, v___y_153_, v___y_154_, v___y_155_, v___y_156_);
return v___x_158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Conv_matchPattern_x3f_spec__0___boxed(lean_object* v_00_u03b1_159_, lean_object* v_k_160_, lean_object* v_allowLevelAssignments_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_167_; lean_object* v_res_168_; 
v_allowLevelAssignments_boxed_167_ = lean_unbox(v_allowLevelAssignments_161_);
v_res_168_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Conv_matchPattern_x3f_spec__0(v_00_u03b1_159_, v_k_160_, v_allowLevelAssignments_boxed_167_, v___y_162_, v___y_163_, v___y_164_, v___y_165_);
lean_dec(v___y_165_);
lean_dec_ref(v___y_164_);
lean_dec(v___y_163_);
lean_dec_ref(v___y_162_);
return v_res_168_;
}
}
static uint64_t _init_l_Lean_Elab_Tactic_Conv_matchPattern_x3f___lam__0___closed__0(void){
_start:
{
uint8_t v___x_169_; uint64_t v___x_170_; 
v___x_169_ = 2;
v___x_170_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_169_);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_matchPattern_x3f___lam__0(lean_object* v_pattern_171_, lean_object* v_e_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_){
_start:
{
lean_object* v___x_178_; 
v___x_178_ = l_Lean_Meta_openAbstractMVarsResult(v_pattern_171_, v___y_173_, v___y_174_, v___y_175_, v___y_176_);
if (lean_obj_tag(v___x_178_) == 0)
{
lean_object* v_a_179_; lean_object* v_snd_180_; lean_object* v_snd_181_; lean_object* v___x_182_; uint8_t v_foApprox_183_; uint8_t v_ctxApprox_184_; uint8_t v_quasiPatternApprox_185_; uint8_t v_constApprox_186_; uint8_t v_isDefEqStuckEx_187_; uint8_t v_unificationHints_188_; uint8_t v_proofIrrelevance_189_; uint8_t v_assignSyntheticOpaque_190_; uint8_t v_offsetCnstrs_191_; uint8_t v_etaStruct_192_; uint8_t v_univApprox_193_; uint8_t v_iota_194_; uint8_t v_beta_195_; uint8_t v_proj_196_; uint8_t v_zeta_197_; uint8_t v_zetaDelta_198_; uint8_t v_zetaUnused_199_; uint8_t v_zetaHave_200_; lean_object* v___x_202_; uint8_t v_isShared_203_; uint8_t v_isSharedCheck_240_; 
v_a_179_ = lean_ctor_get(v___x_178_, 0);
lean_inc(v_a_179_);
lean_dec_ref_known(v___x_178_, 1);
v_snd_180_ = lean_ctor_get(v_a_179_, 1);
lean_inc(v_snd_180_);
lean_dec(v_a_179_);
v_snd_181_ = lean_ctor_get(v_snd_180_, 1);
lean_inc(v_snd_181_);
lean_dec(v_snd_180_);
v___x_182_ = l_Lean_Meta_Context_config(v___y_173_);
v_foApprox_183_ = lean_ctor_get_uint8(v___x_182_, 0);
v_ctxApprox_184_ = lean_ctor_get_uint8(v___x_182_, 1);
v_quasiPatternApprox_185_ = lean_ctor_get_uint8(v___x_182_, 2);
v_constApprox_186_ = lean_ctor_get_uint8(v___x_182_, 3);
v_isDefEqStuckEx_187_ = lean_ctor_get_uint8(v___x_182_, 4);
v_unificationHints_188_ = lean_ctor_get_uint8(v___x_182_, 5);
v_proofIrrelevance_189_ = lean_ctor_get_uint8(v___x_182_, 6);
v_assignSyntheticOpaque_190_ = lean_ctor_get_uint8(v___x_182_, 7);
v_offsetCnstrs_191_ = lean_ctor_get_uint8(v___x_182_, 8);
v_etaStruct_192_ = lean_ctor_get_uint8(v___x_182_, 10);
v_univApprox_193_ = lean_ctor_get_uint8(v___x_182_, 11);
v_iota_194_ = lean_ctor_get_uint8(v___x_182_, 12);
v_beta_195_ = lean_ctor_get_uint8(v___x_182_, 13);
v_proj_196_ = lean_ctor_get_uint8(v___x_182_, 14);
v_zeta_197_ = lean_ctor_get_uint8(v___x_182_, 15);
v_zetaDelta_198_ = lean_ctor_get_uint8(v___x_182_, 16);
v_zetaUnused_199_ = lean_ctor_get_uint8(v___x_182_, 17);
v_zetaHave_200_ = lean_ctor_get_uint8(v___x_182_, 18);
v_isSharedCheck_240_ = !lean_is_exclusive(v___x_182_);
if (v_isSharedCheck_240_ == 0)
{
v___x_202_ = v___x_182_;
v_isShared_203_ = v_isSharedCheck_240_;
goto v_resetjp_201_;
}
else
{
lean_dec(v___x_182_);
v___x_202_ = lean_box(0);
v_isShared_203_ = v_isSharedCheck_240_;
goto v_resetjp_201_;
}
v_resetjp_201_:
{
uint8_t v_trackZetaDelta_204_; lean_object* v_zetaDeltaSet_205_; lean_object* v_lctx_206_; lean_object* v_localInstances_207_; lean_object* v_defEqCtx_x3f_208_; lean_object* v_synthPendingDepth_209_; lean_object* v_canUnfold_x3f_210_; uint8_t v_univApprox_211_; uint8_t v_inTypeClassResolution_212_; uint8_t v_cacheInferType_213_; uint8_t v___x_214_; lean_object* v_config_216_; 
v_trackZetaDelta_204_ = lean_ctor_get_uint8(v___y_173_, sizeof(void*)*7);
v_zetaDeltaSet_205_ = lean_ctor_get(v___y_173_, 1);
lean_inc(v_zetaDeltaSet_205_);
v_lctx_206_ = lean_ctor_get(v___y_173_, 2);
lean_inc_ref(v_lctx_206_);
v_localInstances_207_ = lean_ctor_get(v___y_173_, 3);
lean_inc_ref(v_localInstances_207_);
v_defEqCtx_x3f_208_ = lean_ctor_get(v___y_173_, 4);
lean_inc(v_defEqCtx_x3f_208_);
v_synthPendingDepth_209_ = lean_ctor_get(v___y_173_, 5);
lean_inc(v_synthPendingDepth_209_);
v_canUnfold_x3f_210_ = lean_ctor_get(v___y_173_, 6);
lean_inc(v_canUnfold_x3f_210_);
v_univApprox_211_ = lean_ctor_get_uint8(v___y_173_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_212_ = lean_ctor_get_uint8(v___y_173_, sizeof(void*)*7 + 2);
v_cacheInferType_213_ = lean_ctor_get_uint8(v___y_173_, sizeof(void*)*7 + 3);
v___x_214_ = 2;
if (v_isShared_203_ == 0)
{
v_config_216_ = v___x_202_;
goto v_reusejp_215_;
}
else
{
lean_object* v_reuseFailAlloc_239_; 
v_reuseFailAlloc_239_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_239_, 0, v_foApprox_183_);
lean_ctor_set_uint8(v_reuseFailAlloc_239_, 1, v_ctxApprox_184_);
lean_ctor_set_uint8(v_reuseFailAlloc_239_, 2, v_quasiPatternApprox_185_);
lean_ctor_set_uint8(v_reuseFailAlloc_239_, 3, v_constApprox_186_);
lean_ctor_set_uint8(v_reuseFailAlloc_239_, 4, v_isDefEqStuckEx_187_);
lean_ctor_set_uint8(v_reuseFailAlloc_239_, 5, v_unificationHints_188_);
lean_ctor_set_uint8(v_reuseFailAlloc_239_, 6, v_proofIrrelevance_189_);
lean_ctor_set_uint8(v_reuseFailAlloc_239_, 7, v_assignSyntheticOpaque_190_);
lean_ctor_set_uint8(v_reuseFailAlloc_239_, 8, v_offsetCnstrs_191_);
lean_ctor_set_uint8(v_reuseFailAlloc_239_, 10, v_etaStruct_192_);
lean_ctor_set_uint8(v_reuseFailAlloc_239_, 11, v_univApprox_193_);
lean_ctor_set_uint8(v_reuseFailAlloc_239_, 12, v_iota_194_);
lean_ctor_set_uint8(v_reuseFailAlloc_239_, 13, v_beta_195_);
lean_ctor_set_uint8(v_reuseFailAlloc_239_, 14, v_proj_196_);
lean_ctor_set_uint8(v_reuseFailAlloc_239_, 15, v_zeta_197_);
lean_ctor_set_uint8(v_reuseFailAlloc_239_, 16, v_zetaDelta_198_);
lean_ctor_set_uint8(v_reuseFailAlloc_239_, 17, v_zetaUnused_199_);
lean_ctor_set_uint8(v_reuseFailAlloc_239_, 18, v_zetaHave_200_);
v_config_216_ = v_reuseFailAlloc_239_;
goto v_reusejp_215_;
}
v_reusejp_215_:
{
uint64_t v___x_217_; lean_object* v___x_219_; uint8_t v_isShared_220_; uint8_t v_isSharedCheck_231_; 
lean_ctor_set_uint8(v_config_216_, 9, v___x_214_);
v___x_217_ = l_Lean_Meta_Context_configKey(v___y_173_);
v_isSharedCheck_231_ = !lean_is_exclusive(v___y_173_);
if (v_isSharedCheck_231_ == 0)
{
lean_object* v_unused_232_; lean_object* v_unused_233_; lean_object* v_unused_234_; lean_object* v_unused_235_; lean_object* v_unused_236_; lean_object* v_unused_237_; lean_object* v_unused_238_; 
v_unused_232_ = lean_ctor_get(v___y_173_, 6);
lean_dec(v_unused_232_);
v_unused_233_ = lean_ctor_get(v___y_173_, 5);
lean_dec(v_unused_233_);
v_unused_234_ = lean_ctor_get(v___y_173_, 4);
lean_dec(v_unused_234_);
v_unused_235_ = lean_ctor_get(v___y_173_, 3);
lean_dec(v_unused_235_);
v_unused_236_ = lean_ctor_get(v___y_173_, 2);
lean_dec(v_unused_236_);
v_unused_237_ = lean_ctor_get(v___y_173_, 1);
lean_dec(v_unused_237_);
v_unused_238_ = lean_ctor_get(v___y_173_, 0);
lean_dec(v_unused_238_);
v___x_219_ = v___y_173_;
v_isShared_220_ = v_isSharedCheck_231_;
goto v_resetjp_218_;
}
else
{
lean_dec(v___y_173_);
v___x_219_ = lean_box(0);
v_isShared_220_ = v_isSharedCheck_231_;
goto v_resetjp_218_;
}
v_resetjp_218_:
{
uint64_t v___x_221_; uint64_t v___x_222_; uint64_t v___x_223_; uint64_t v___x_224_; uint64_t v_key_225_; lean_object* v___x_226_; lean_object* v___x_228_; 
v___x_221_ = 3ULL;
v___x_222_ = lean_uint64_shift_right(v___x_217_, v___x_221_);
v___x_223_ = lean_uint64_shift_left(v___x_222_, v___x_221_);
v___x_224_ = lean_uint64_once(&l_Lean_Elab_Tactic_Conv_matchPattern_x3f___lam__0___closed__0, &l_Lean_Elab_Tactic_Conv_matchPattern_x3f___lam__0___closed__0_once, _init_l_Lean_Elab_Tactic_Conv_matchPattern_x3f___lam__0___closed__0);
v_key_225_ = lean_uint64_lor(v___x_223_, v___x_224_);
v___x_226_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_226_, 0, v_config_216_);
lean_ctor_set_uint64(v___x_226_, sizeof(void*)*1, v_key_225_);
if (v_isShared_220_ == 0)
{
lean_ctor_set(v___x_219_, 0, v___x_226_);
v___x_228_ = v___x_219_;
goto v_reusejp_227_;
}
else
{
lean_object* v_reuseFailAlloc_230_; 
v_reuseFailAlloc_230_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_230_, 0, v___x_226_);
lean_ctor_set(v_reuseFailAlloc_230_, 1, v_zetaDeltaSet_205_);
lean_ctor_set(v_reuseFailAlloc_230_, 2, v_lctx_206_);
lean_ctor_set(v_reuseFailAlloc_230_, 3, v_localInstances_207_);
lean_ctor_set(v_reuseFailAlloc_230_, 4, v_defEqCtx_x3f_208_);
lean_ctor_set(v_reuseFailAlloc_230_, 5, v_synthPendingDepth_209_);
lean_ctor_set(v_reuseFailAlloc_230_, 6, v_canUnfold_x3f_210_);
lean_ctor_set_uint8(v_reuseFailAlloc_230_, sizeof(void*)*7, v_trackZetaDelta_204_);
lean_ctor_set_uint8(v_reuseFailAlloc_230_, sizeof(void*)*7 + 1, v_univApprox_211_);
lean_ctor_set_uint8(v_reuseFailAlloc_230_, sizeof(void*)*7 + 2, v_inTypeClassResolution_212_);
lean_ctor_set_uint8(v_reuseFailAlloc_230_, sizeof(void*)*7 + 3, v_cacheInferType_213_);
v___x_228_ = v_reuseFailAlloc_230_;
goto v_reusejp_227_;
}
v_reusejp_227_:
{
lean_object* v___x_229_; 
v___x_229_ = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_matchPattern_x3f_go_x3f(v_snd_181_, v_e_172_, v___x_228_, v___y_174_, v___y_175_, v___y_176_);
lean_dec_ref(v___x_228_);
return v___x_229_;
}
}
}
}
}
else
{
lean_object* v_a_241_; lean_object* v___x_243_; uint8_t v_isShared_244_; uint8_t v_isSharedCheck_248_; 
lean_dec_ref(v___y_173_);
lean_dec_ref(v_e_172_);
v_a_241_ = lean_ctor_get(v___x_178_, 0);
v_isSharedCheck_248_ = !lean_is_exclusive(v___x_178_);
if (v_isSharedCheck_248_ == 0)
{
v___x_243_ = v___x_178_;
v_isShared_244_ = v_isSharedCheck_248_;
goto v_resetjp_242_;
}
else
{
lean_inc(v_a_241_);
lean_dec(v___x_178_);
v___x_243_ = lean_box(0);
v_isShared_244_ = v_isSharedCheck_248_;
goto v_resetjp_242_;
}
v_resetjp_242_:
{
lean_object* v___x_246_; 
if (v_isShared_244_ == 0)
{
v___x_246_ = v___x_243_;
goto v_reusejp_245_;
}
else
{
lean_object* v_reuseFailAlloc_247_; 
v_reuseFailAlloc_247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_247_, 0, v_a_241_);
v___x_246_ = v_reuseFailAlloc_247_;
goto v_reusejp_245_;
}
v_reusejp_245_:
{
return v___x_246_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_matchPattern_x3f___lam__0___boxed(lean_object* v_pattern_249_, lean_object* v_e_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_){
_start:
{
lean_object* v_res_256_; 
v_res_256_ = l_Lean_Elab_Tactic_Conv_matchPattern_x3f___lam__0(v_pattern_249_, v_e_250_, v___y_251_, v___y_252_, v___y_253_, v___y_254_);
lean_dec(v___y_254_);
lean_dec_ref(v___y_253_);
lean_dec(v___y_252_);
return v_res_256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_matchPattern_x3f(lean_object* v_pattern_257_, lean_object* v_e_258_, lean_object* v_a_259_, lean_object* v_a_260_, lean_object* v_a_261_, lean_object* v_a_262_){
_start:
{
lean_object* v___f_264_; uint8_t v___x_265_; lean_object* v___x_266_; 
v___f_264_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_matchPattern_x3f___lam__0___boxed), 7, 2);
lean_closure_set(v___f_264_, 0, v_pattern_257_);
lean_closure_set(v___f_264_, 1, v_e_258_);
v___x_265_ = 0;
v___x_266_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Conv_matchPattern_x3f_spec__0___redArg(v___f_264_, v___x_265_, v_a_259_, v_a_260_, v_a_261_, v_a_262_);
return v___x_266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_matchPattern_x3f___boxed(lean_object* v_pattern_267_, lean_object* v_e_268_, lean_object* v_a_269_, lean_object* v_a_270_, lean_object* v_a_271_, lean_object* v_a_272_, lean_object* v_a_273_){
_start:
{
lean_object* v_res_274_; 
v_res_274_ = l_Lean_Elab_Tactic_Conv_matchPattern_x3f(v_pattern_267_, v_e_268_, v_a_269_, v_a_270_, v_a_271_, v_a_272_);
lean_dec(v_a_272_);
lean_dec_ref(v_a_271_);
lean_dec(v_a_270_);
lean_dec_ref(v_a_269_);
return v_res_274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorIdx(lean_object* v_x_275_){
_start:
{
if (lean_obj_tag(v_x_275_) == 0)
{
lean_object* v___x_276_; 
v___x_276_ = lean_unsigned_to_nat(0u);
return v___x_276_;
}
else
{
lean_object* v___x_277_; 
v___x_277_ = lean_unsigned_to_nat(1u);
return v___x_277_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorIdx___boxed(lean_object* v_x_278_){
_start:
{
lean_object* v_res_279_; 
v_res_279_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorIdx(v_x_278_);
lean_dec_ref(v_x_278_);
return v_res_279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorElim___redArg(lean_object* v_t_280_, lean_object* v_k_281_){
_start:
{
if (lean_obj_tag(v_t_280_) == 0)
{
lean_object* v_subgoals_282_; lean_object* v___x_283_; 
v_subgoals_282_ = lean_ctor_get(v_t_280_, 0);
lean_inc_ref(v_subgoals_282_);
lean_dec_ref_known(v_t_280_, 1);
v___x_283_ = lean_apply_1(v_k_281_, v_subgoals_282_);
return v___x_283_;
}
else
{
lean_object* v_subgoals_284_; lean_object* v_idx_285_; lean_object* v_remaining_286_; lean_object* v___x_287_; 
v_subgoals_284_ = lean_ctor_get(v_t_280_, 0);
lean_inc_ref(v_subgoals_284_);
v_idx_285_ = lean_ctor_get(v_t_280_, 1);
lean_inc(v_idx_285_);
v_remaining_286_ = lean_ctor_get(v_t_280_, 2);
lean_inc(v_remaining_286_);
lean_dec_ref_known(v_t_280_, 3);
v___x_287_ = lean_apply_3(v_k_281_, v_subgoals_284_, v_idx_285_, v_remaining_286_);
return v___x_287_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorElim(lean_object* v_motive_288_, lean_object* v_ctorIdx_289_, lean_object* v_t_290_, lean_object* v_h_291_, lean_object* v_k_292_){
_start:
{
lean_object* v___x_293_; 
v___x_293_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorElim___redArg(v_t_290_, v_k_292_);
return v___x_293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorElim___boxed(lean_object* v_motive_294_, lean_object* v_ctorIdx_295_, lean_object* v_t_296_, lean_object* v_h_297_, lean_object* v_k_298_){
_start:
{
lean_object* v_res_299_; 
v_res_299_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorElim(v_motive_294_, v_ctorIdx_295_, v_t_296_, v_h_297_, v_k_298_);
lean_dec(v_ctorIdx_295_);
return v_res_299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_all_elim___redArg(lean_object* v_t_300_, lean_object* v_all_301_){
_start:
{
lean_object* v___x_302_; 
v___x_302_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorElim___redArg(v_t_300_, v_all_301_);
return v___x_302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_all_elim(lean_object* v_motive_303_, lean_object* v_t_304_, lean_object* v_h_305_, lean_object* v_all_306_){
_start:
{
lean_object* v___x_307_; 
v___x_307_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorElim___redArg(v_t_304_, v_all_306_);
return v___x_307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_occs_elim___redArg(lean_object* v_t_308_, lean_object* v_occs_309_){
_start:
{
lean_object* v___x_310_; 
v___x_310_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorElim___redArg(v_t_308_, v_occs_309_);
return v___x_310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_occs_elim(lean_object* v_motive_311_, lean_object* v_t_312_, lean_object* v_h_313_, lean_object* v_occs_314_){
_start:
{
lean_object* v___x_315_; 
v___x_315_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorElim___redArg(v_t_312_, v_occs_314_);
return v___x_315_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Conv_PatternMatchState_isDone(lean_object* v_x_316_){
_start:
{
if (lean_obj_tag(v_x_316_) == 0)
{
uint8_t v___x_317_; 
v___x_317_ = 0;
return v___x_317_;
}
else
{
lean_object* v_remaining_318_; uint8_t v___x_319_; 
v_remaining_318_ = lean_ctor_get(v_x_316_, 2);
v___x_319_ = l_List_isEmpty___redArg(v_remaining_318_);
return v___x_319_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_isDone___boxed(lean_object* v_x_320_){
_start:
{
uint8_t v_res_321_; lean_object* v_r_322_; 
v_res_321_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_isDone(v_x_320_);
lean_dec_ref(v_x_320_);
v_r_322_ = lean_box(v_res_321_);
return v_r_322_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Conv_PatternMatchState_isReady(lean_object* v_x_323_){
_start:
{
if (lean_obj_tag(v_x_323_) == 0)
{
uint8_t v___x_324_; 
v___x_324_ = 1;
return v___x_324_;
}
else
{
lean_object* v_remaining_325_; 
v_remaining_325_ = lean_ctor_get(v_x_323_, 2);
if (lean_obj_tag(v_remaining_325_) == 1)
{
lean_object* v_head_326_; lean_object* v_idx_327_; lean_object* v_fst_328_; uint8_t v___x_329_; 
v_head_326_ = lean_ctor_get(v_remaining_325_, 0);
v_idx_327_ = lean_ctor_get(v_x_323_, 1);
v_fst_328_ = lean_ctor_get(v_head_326_, 0);
v___x_329_ = lean_nat_dec_eq(v_idx_327_, v_fst_328_);
return v___x_329_;
}
else
{
uint8_t v___x_330_; 
v___x_330_ = 0;
return v___x_330_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_isReady___boxed(lean_object* v_x_331_){
_start:
{
uint8_t v_res_332_; lean_object* v_r_333_; 
v_res_332_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_isReady(v_x_331_);
lean_dec_ref(v_x_331_);
v_r_333_ = lean_box(v_res_332_);
return v_r_333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_skip(lean_object* v_x_334_){
_start:
{
if (lean_obj_tag(v_x_334_) == 1)
{
lean_object* v_subgoals_335_; lean_object* v_idx_336_; lean_object* v_remaining_337_; lean_object* v___x_339_; uint8_t v_isShared_340_; uint8_t v_isSharedCheck_346_; 
v_subgoals_335_ = lean_ctor_get(v_x_334_, 0);
v_idx_336_ = lean_ctor_get(v_x_334_, 1);
v_remaining_337_ = lean_ctor_get(v_x_334_, 2);
v_isSharedCheck_346_ = !lean_is_exclusive(v_x_334_);
if (v_isSharedCheck_346_ == 0)
{
v___x_339_ = v_x_334_;
v_isShared_340_ = v_isSharedCheck_346_;
goto v_resetjp_338_;
}
else
{
lean_inc(v_remaining_337_);
lean_inc(v_idx_336_);
lean_inc(v_subgoals_335_);
lean_dec(v_x_334_);
v___x_339_ = lean_box(0);
v_isShared_340_ = v_isSharedCheck_346_;
goto v_resetjp_338_;
}
v_resetjp_338_:
{
lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_344_; 
v___x_341_ = lean_unsigned_to_nat(1u);
v___x_342_ = lean_nat_add(v_idx_336_, v___x_341_);
lean_dec(v_idx_336_);
if (v_isShared_340_ == 0)
{
lean_ctor_set(v___x_339_, 1, v___x_342_);
v___x_344_ = v___x_339_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v_subgoals_335_);
lean_ctor_set(v_reuseFailAlloc_345_, 1, v___x_342_);
lean_ctor_set(v_reuseFailAlloc_345_, 2, v_remaining_337_);
v___x_344_ = v_reuseFailAlloc_345_;
goto v_reusejp_343_;
}
v_reusejp_343_:
{
return v___x_344_;
}
}
}
else
{
return v_x_334_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_accept(lean_object* v_mvarId_347_, lean_object* v_x_348_){
_start:
{
if (lean_obj_tag(v_x_348_) == 0)
{
lean_object* v_subgoals_349_; lean_object* v___x_351_; uint8_t v_isShared_352_; uint8_t v_isSharedCheck_357_; 
v_subgoals_349_ = lean_ctor_get(v_x_348_, 0);
v_isSharedCheck_357_ = !lean_is_exclusive(v_x_348_);
if (v_isSharedCheck_357_ == 0)
{
v___x_351_ = v_x_348_;
v_isShared_352_ = v_isSharedCheck_357_;
goto v_resetjp_350_;
}
else
{
lean_inc(v_subgoals_349_);
lean_dec(v_x_348_);
v___x_351_ = lean_box(0);
v_isShared_352_ = v_isSharedCheck_357_;
goto v_resetjp_350_;
}
v_resetjp_350_:
{
lean_object* v___x_353_; lean_object* v___x_355_; 
v___x_353_ = lean_array_push(v_subgoals_349_, v_mvarId_347_);
if (v_isShared_352_ == 0)
{
lean_ctor_set(v___x_351_, 0, v___x_353_);
v___x_355_ = v___x_351_;
goto v_reusejp_354_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v___x_353_);
v___x_355_ = v_reuseFailAlloc_356_;
goto v_reusejp_354_;
}
v_reusejp_354_:
{
return v___x_355_;
}
}
}
else
{
lean_object* v_remaining_358_; 
v_remaining_358_ = lean_ctor_get(v_x_348_, 2);
if (lean_obj_tag(v_remaining_358_) == 1)
{
lean_object* v_head_359_; lean_object* v_subgoals_360_; lean_object* v_idx_361_; lean_object* v___x_363_; uint8_t v_isShared_364_; uint8_t v_isSharedCheck_381_; 
lean_inc_ref(v_remaining_358_);
v_head_359_ = lean_ctor_get(v_remaining_358_, 0);
lean_inc(v_head_359_);
v_subgoals_360_ = lean_ctor_get(v_x_348_, 0);
v_idx_361_ = lean_ctor_get(v_x_348_, 1);
v_isSharedCheck_381_ = !lean_is_exclusive(v_x_348_);
if (v_isSharedCheck_381_ == 0)
{
lean_object* v_unused_382_; 
v_unused_382_ = lean_ctor_get(v_x_348_, 2);
lean_dec(v_unused_382_);
v___x_363_ = v_x_348_;
v_isShared_364_ = v_isSharedCheck_381_;
goto v_resetjp_362_;
}
else
{
lean_inc(v_idx_361_);
lean_inc(v_subgoals_360_);
lean_dec(v_x_348_);
v___x_363_ = lean_box(0);
v_isShared_364_ = v_isSharedCheck_381_;
goto v_resetjp_362_;
}
v_resetjp_362_:
{
lean_object* v_tail_365_; lean_object* v_snd_366_; lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_379_; 
v_tail_365_ = lean_ctor_get(v_remaining_358_, 1);
lean_inc(v_tail_365_);
lean_dec_ref_known(v_remaining_358_, 2);
v_snd_366_ = lean_ctor_get(v_head_359_, 1);
v_isSharedCheck_379_ = !lean_is_exclusive(v_head_359_);
if (v_isSharedCheck_379_ == 0)
{
lean_object* v_unused_380_; 
v_unused_380_ = lean_ctor_get(v_head_359_, 0);
lean_dec(v_unused_380_);
v___x_368_ = v_head_359_;
v_isShared_369_ = v_isSharedCheck_379_;
goto v_resetjp_367_;
}
else
{
lean_inc(v_snd_366_);
lean_dec(v_head_359_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_379_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
lean_object* v___x_371_; 
if (v_isShared_369_ == 0)
{
lean_ctor_set(v___x_368_, 1, v_mvarId_347_);
lean_ctor_set(v___x_368_, 0, v_snd_366_);
v___x_371_ = v___x_368_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v_snd_366_);
lean_ctor_set(v_reuseFailAlloc_378_, 1, v_mvarId_347_);
v___x_371_ = v_reuseFailAlloc_378_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_376_; 
v___x_372_ = lean_array_push(v_subgoals_360_, v___x_371_);
v___x_373_ = lean_unsigned_to_nat(1u);
v___x_374_ = lean_nat_add(v_idx_361_, v___x_373_);
lean_dec(v_idx_361_);
if (v_isShared_364_ == 0)
{
lean_ctor_set(v___x_363_, 2, v_tail_365_);
lean_ctor_set(v___x_363_, 1, v___x_374_);
lean_ctor_set(v___x_363_, 0, v___x_372_);
v___x_376_ = v___x_363_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v___x_372_);
lean_ctor_set(v_reuseFailAlloc_377_, 1, v___x_374_);
lean_ctor_set(v_reuseFailAlloc_377_, 2, v_tail_365_);
v___x_376_ = v_reuseFailAlloc_377_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
return v___x_376_;
}
}
}
}
}
else
{
lean_dec(v_mvarId_347_);
return v_x_348_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre_spec__0___redArg(lean_object* v_as_383_, size_t v_sz_384_, size_t v_i_385_, lean_object* v_b_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_){
_start:
{
uint8_t v___x_392_; 
v___x_392_ = lean_usize_dec_lt(v_i_385_, v_sz_384_);
if (v___x_392_ == 0)
{
lean_object* v___x_393_; 
v___x_393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_393_, 0, v_b_386_);
return v___x_393_;
}
else
{
lean_object* v_a_394_; lean_object* v___x_395_; 
v_a_394_ = lean_array_uget_borrowed(v_as_383_, v_i_385_);
lean_inc(v_a_394_);
v___x_395_ = l_Lean_Meta_mkCongrFun(v_b_386_, v_a_394_, v___y_387_, v___y_388_, v___y_389_, v___y_390_);
if (lean_obj_tag(v___x_395_) == 0)
{
lean_object* v_a_396_; size_t v___x_397_; size_t v___x_398_; 
v_a_396_ = lean_ctor_get(v___x_395_, 0);
lean_inc(v_a_396_);
lean_dec_ref_known(v___x_395_, 1);
v___x_397_ = ((size_t)1ULL);
v___x_398_ = lean_usize_add(v_i_385_, v___x_397_);
v_i_385_ = v___x_398_;
v_b_386_ = v_a_396_;
goto _start;
}
else
{
return v___x_395_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre_spec__0___redArg___boxed(lean_object* v_as_400_, lean_object* v_sz_401_, lean_object* v_i_402_, lean_object* v_b_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_){
_start:
{
size_t v_sz_boxed_409_; size_t v_i_boxed_410_; lean_object* v_res_411_; 
v_sz_boxed_409_ = lean_unbox_usize(v_sz_401_);
lean_dec(v_sz_401_);
v_i_boxed_410_ = lean_unbox_usize(v_i_402_);
lean_dec(v_i_402_);
v_res_411_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre_spec__0___redArg(v_as_400_, v_sz_boxed_409_, v_i_boxed_410_, v_b_403_, v___y_404_, v___y_405_, v___y_406_, v___y_407_);
lean_dec(v___y_407_);
lean_dec_ref(v___y_406_);
lean_dec(v___y_405_);
lean_dec_ref(v___y_404_);
lean_dec_ref(v_as_400_);
return v_res_411_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre(lean_object* v_pattern_414_, lean_object* v_state_415_, lean_object* v_e_416_, lean_object* v_a_417_, lean_object* v_a_418_, lean_object* v_a_419_, lean_object* v_a_420_, lean_object* v_a_421_, lean_object* v_a_422_, lean_object* v_a_423_){
_start:
{
lean_object* v___x_425_; uint8_t v___x_426_; uint8_t v___x_427_; 
v___x_425_ = lean_st_ref_get(v_state_415_);
v___x_426_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_isDone(v___x_425_);
lean_dec(v___x_425_);
v___x_427_ = 1;
if (v___x_426_ == 0)
{
lean_object* v___x_428_; 
v___x_428_ = l_Lean_Elab_Tactic_Conv_matchPattern_x3f(v_pattern_414_, v_e_416_, v_a_420_, v_a_421_, v_a_422_, v_a_423_);
if (lean_obj_tag(v___x_428_) == 0)
{
lean_object* v_a_429_; lean_object* v___x_431_; uint8_t v_isShared_432_; uint8_t v_isSharedCheck_495_; 
v_a_429_ = lean_ctor_get(v___x_428_, 0);
v_isSharedCheck_495_ = !lean_is_exclusive(v___x_428_);
if (v_isSharedCheck_495_ == 0)
{
v___x_431_ = v___x_428_;
v_isShared_432_ = v_isSharedCheck_495_;
goto v_resetjp_430_;
}
else
{
lean_inc(v_a_429_);
lean_dec(v___x_428_);
v___x_431_ = lean_box(0);
v_isShared_432_ = v_isSharedCheck_495_;
goto v_resetjp_430_;
}
v_resetjp_430_:
{
if (lean_obj_tag(v_a_429_) == 1)
{
lean_object* v_val_433_; lean_object* v___x_435_; uint8_t v_isShared_436_; uint8_t v_isSharedCheck_490_; 
v_val_433_ = lean_ctor_get(v_a_429_, 0);
v_isSharedCheck_490_ = !lean_is_exclusive(v_a_429_);
if (v_isSharedCheck_490_ == 0)
{
v___x_435_ = v_a_429_;
v_isShared_436_ = v_isSharedCheck_490_;
goto v_resetjp_434_;
}
else
{
lean_inc(v_val_433_);
lean_dec(v_a_429_);
v___x_435_ = lean_box(0);
v_isShared_436_ = v_isSharedCheck_490_;
goto v_resetjp_434_;
}
v_resetjp_434_:
{
lean_object* v_fst_437_; lean_object* v_snd_438_; lean_object* v___x_439_; uint8_t v___x_440_; 
v_fst_437_ = lean_ctor_get(v_val_433_, 0);
lean_inc(v_fst_437_);
v_snd_438_ = lean_ctor_get(v_val_433_, 1);
lean_inc(v_snd_438_);
lean_dec(v_val_433_);
v___x_439_ = lean_st_ref_get(v_state_415_);
v___x_440_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_isReady(v___x_439_);
lean_dec(v___x_439_);
if (v___x_440_ == 0)
{
lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_446_; 
lean_dec(v_snd_438_);
lean_dec(v_fst_437_);
lean_del_object(v___x_435_);
v___x_441_ = lean_st_ref_take(v_state_415_);
v___x_442_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_skip(v___x_441_);
v___x_443_ = lean_st_ref_set(v_state_415_, v___x_442_);
v___x_444_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre___closed__0));
if (v_isShared_432_ == 0)
{
lean_ctor_set(v___x_431_, 0, v___x_444_);
v___x_446_ = v___x_431_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v___x_444_);
v___x_446_ = v_reuseFailAlloc_447_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
return v___x_446_;
}
}
else
{
lean_object* v___x_448_; lean_object* v___x_449_; 
lean_del_object(v___x_431_);
v___x_448_ = lean_box(0);
v___x_449_ = l_Lean_Elab_Tactic_Conv_mkConvGoalFor(v_fst_437_, v___x_448_, v_a_420_, v_a_421_, v_a_422_, v_a_423_);
if (lean_obj_tag(v___x_449_) == 0)
{
lean_object* v_a_450_; lean_object* v_fst_451_; lean_object* v_snd_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; size_t v_sz_457_; size_t v___x_458_; lean_object* v___x_459_; 
v_a_450_ = lean_ctor_get(v___x_449_, 0);
lean_inc(v_a_450_);
lean_dec_ref_known(v___x_449_, 1);
v_fst_451_ = lean_ctor_get(v_a_450_, 0);
lean_inc(v_fst_451_);
v_snd_452_ = lean_ctor_get(v_a_450_, 1);
lean_inc(v_snd_452_);
lean_dec(v_a_450_);
v___x_453_ = lean_st_ref_take(v_state_415_);
v___x_454_ = l_Lean_Expr_mvarId_x21(v_snd_452_);
v___x_455_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_accept(v___x_454_, v___x_453_);
v___x_456_ = lean_st_ref_set(v_state_415_, v___x_455_);
v_sz_457_ = lean_array_size(v_snd_438_);
v___x_458_ = ((size_t)0ULL);
v___x_459_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre_spec__0___redArg(v_snd_438_, v_sz_457_, v___x_458_, v_snd_452_, v_a_420_, v_a_421_, v_a_422_, v_a_423_);
if (lean_obj_tag(v___x_459_) == 0)
{
lean_object* v_a_460_; lean_object* v___x_462_; uint8_t v_isShared_463_; uint8_t v_isSharedCheck_473_; 
v_a_460_ = lean_ctor_get(v___x_459_, 0);
v_isSharedCheck_473_ = !lean_is_exclusive(v___x_459_);
if (v_isSharedCheck_473_ == 0)
{
v___x_462_ = v___x_459_;
v_isShared_463_ = v_isSharedCheck_473_;
goto v_resetjp_461_;
}
else
{
lean_inc(v_a_460_);
lean_dec(v___x_459_);
v___x_462_ = lean_box(0);
v_isShared_463_ = v_isSharedCheck_473_;
goto v_resetjp_461_;
}
v_resetjp_461_:
{
lean_object* v___x_464_; lean_object* v___x_466_; 
v___x_464_ = l_Lean_mkAppN(v_fst_451_, v_snd_438_);
lean_dec(v_snd_438_);
if (v_isShared_436_ == 0)
{
lean_ctor_set(v___x_435_, 0, v_a_460_);
v___x_466_ = v___x_435_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_472_; 
v_reuseFailAlloc_472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_472_, 0, v_a_460_);
v___x_466_ = v_reuseFailAlloc_472_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_470_; 
v___x_467_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_467_, 0, v___x_464_);
lean_ctor_set(v___x_467_, 1, v___x_466_);
lean_ctor_set_uint8(v___x_467_, sizeof(void*)*2, v___x_427_);
v___x_468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_468_, 0, v___x_467_);
if (v_isShared_463_ == 0)
{
lean_ctor_set(v___x_462_, 0, v___x_468_);
v___x_470_ = v___x_462_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v___x_468_);
v___x_470_ = v_reuseFailAlloc_471_;
goto v_reusejp_469_;
}
v_reusejp_469_:
{
return v___x_470_;
}
}
}
}
else
{
lean_object* v_a_474_; lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_481_; 
lean_dec(v_fst_451_);
lean_dec(v_snd_438_);
lean_del_object(v___x_435_);
v_a_474_ = lean_ctor_get(v___x_459_, 0);
v_isSharedCheck_481_ = !lean_is_exclusive(v___x_459_);
if (v_isSharedCheck_481_ == 0)
{
v___x_476_ = v___x_459_;
v_isShared_477_ = v_isSharedCheck_481_;
goto v_resetjp_475_;
}
else
{
lean_inc(v_a_474_);
lean_dec(v___x_459_);
v___x_476_ = lean_box(0);
v_isShared_477_ = v_isSharedCheck_481_;
goto v_resetjp_475_;
}
v_resetjp_475_:
{
lean_object* v___x_479_; 
if (v_isShared_477_ == 0)
{
v___x_479_ = v___x_476_;
goto v_reusejp_478_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v_a_474_);
v___x_479_ = v_reuseFailAlloc_480_;
goto v_reusejp_478_;
}
v_reusejp_478_:
{
return v___x_479_;
}
}
}
}
else
{
lean_object* v_a_482_; lean_object* v___x_484_; uint8_t v_isShared_485_; uint8_t v_isSharedCheck_489_; 
lean_dec(v_snd_438_);
lean_del_object(v___x_435_);
v_a_482_ = lean_ctor_get(v___x_449_, 0);
v_isSharedCheck_489_ = !lean_is_exclusive(v___x_449_);
if (v_isSharedCheck_489_ == 0)
{
v___x_484_ = v___x_449_;
v_isShared_485_ = v_isSharedCheck_489_;
goto v_resetjp_483_;
}
else
{
lean_inc(v_a_482_);
lean_dec(v___x_449_);
v___x_484_ = lean_box(0);
v_isShared_485_ = v_isSharedCheck_489_;
goto v_resetjp_483_;
}
v_resetjp_483_:
{
lean_object* v___x_487_; 
if (v_isShared_485_ == 0)
{
v___x_487_ = v___x_484_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_488_; 
v_reuseFailAlloc_488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_488_, 0, v_a_482_);
v___x_487_ = v_reuseFailAlloc_488_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
return v___x_487_;
}
}
}
}
}
}
else
{
lean_object* v___x_491_; lean_object* v___x_493_; 
lean_dec(v_a_429_);
v___x_491_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre___closed__0));
if (v_isShared_432_ == 0)
{
lean_ctor_set(v___x_431_, 0, v___x_491_);
v___x_493_ = v___x_431_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v___x_491_);
v___x_493_ = v_reuseFailAlloc_494_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
return v___x_493_;
}
}
}
}
else
{
lean_object* v_a_496_; lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_503_; 
v_a_496_ = lean_ctor_get(v___x_428_, 0);
v_isSharedCheck_503_ = !lean_is_exclusive(v___x_428_);
if (v_isSharedCheck_503_ == 0)
{
v___x_498_ = v___x_428_;
v_isShared_499_ = v_isSharedCheck_503_;
goto v_resetjp_497_;
}
else
{
lean_inc(v_a_496_);
lean_dec(v___x_428_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_503_;
goto v_resetjp_497_;
}
v_resetjp_497_:
{
lean_object* v___x_501_; 
if (v_isShared_499_ == 0)
{
v___x_501_ = v___x_498_;
goto v_reusejp_500_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v_a_496_);
v___x_501_ = v_reuseFailAlloc_502_;
goto v_reusejp_500_;
}
v_reusejp_500_:
{
return v___x_501_;
}
}
}
}
else
{
lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; 
lean_dec_ref(v_pattern_414_);
v___x_504_ = lean_box(0);
v___x_505_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_505_, 0, v_e_416_);
lean_ctor_set(v___x_505_, 1, v___x_504_);
lean_ctor_set_uint8(v___x_505_, sizeof(void*)*2, v___x_427_);
v___x_506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_506_, 0, v___x_505_);
v___x_507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_507_, 0, v___x_506_);
return v___x_507_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre___boxed(lean_object* v_pattern_508_, lean_object* v_state_509_, lean_object* v_e_510_, lean_object* v_a_511_, lean_object* v_a_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v_a_517_, lean_object* v_a_518_){
_start:
{
lean_object* v_res_519_; 
v_res_519_ = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre(v_pattern_508_, v_state_509_, v_e_510_, v_a_511_, v_a_512_, v_a_513_, v_a_514_, v_a_515_, v_a_516_, v_a_517_);
lean_dec(v_a_517_);
lean_dec_ref(v_a_516_);
lean_dec(v_a_515_);
lean_dec_ref(v_a_514_);
lean_dec(v_a_513_);
lean_dec_ref(v_a_512_);
lean_dec(v_a_511_);
lean_dec(v_state_509_);
return v_res_519_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre_spec__0(lean_object* v_as_520_, size_t v_sz_521_, size_t v_i_522_, lean_object* v_b_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_){
_start:
{
lean_object* v___x_532_; 
v___x_532_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre_spec__0___redArg(v_as_520_, v_sz_521_, v_i_522_, v_b_523_, v___y_527_, v___y_528_, v___y_529_, v___y_530_);
return v___x_532_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre_spec__0___boxed(lean_object* v_as_533_, lean_object* v_sz_534_, lean_object* v_i_535_, lean_object* v_b_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_){
_start:
{
size_t v_sz_boxed_545_; size_t v_i_boxed_546_; lean_object* v_res_547_; 
v_sz_boxed_545_ = lean_unbox_usize(v_sz_534_);
lean_dec(v_sz_534_);
v_i_boxed_546_ = lean_unbox_usize(v_i_535_);
lean_dec(v_i_535_);
v_res_547_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre_spec__0(v_as_533_, v_sz_boxed_545_, v_i_boxed_546_, v_b_536_, v___y_537_, v___y_538_, v___y_539_, v___y_540_, v___y_541_, v___y_542_, v___y_543_);
lean_dec(v___y_543_);
lean_dec_ref(v___y_542_);
lean_dec(v___y_541_);
lean_dec_ref(v___y_540_);
lean_dec(v___y_539_);
lean_dec_ref(v___y_538_);
lean_dec(v___y_537_);
lean_dec_ref(v_as_533_);
return v_res_547_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; 
v___x_548_ = lean_box(0);
v___x_549_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_550_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_550_, 0, v___x_549_);
lean_ctor_set(v___x_550_, 1, v___x_548_);
return v___x_550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg(){
_start:
{
lean_object* v___x_552_; lean_object* v___x_553_; 
v___x_552_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg___closed__0);
v___x_553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_553_, 0, v___x_552_);
return v___x_553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg___boxed(lean_object* v___y_554_){
_start:
{
lean_object* v_res_555_; 
v_res_555_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg();
return v_res_555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0(lean_object* v_00_u03b1_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_){
_start:
{
lean_object* v___x_566_; 
v___x_566_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg();
return v___x_566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___boxed(lean_object* v_00_u03b1_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_){
_start:
{
lean_object* v_res_577_; 
v_res_577_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0(v_00_u03b1_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_);
lean_dec(v___y_575_);
lean_dec_ref(v___y_574_);
lean_dec(v___y_573_);
lean_dec_ref(v___y_572_);
lean_dec(v___y_571_);
lean_dec_ref(v___y_570_);
lean_dec(v___y_569_);
lean_dec_ref(v___y_568_);
return v_res_577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__2___redArg(lean_object* v_a_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_){
_start:
{
lean_object* v___x_586_; 
v___x_586_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v_a_578_, v___y_579_, v___y_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_);
return v___x_586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__2___redArg___boxed(lean_object* v_a_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_){
_start:
{
lean_object* v_res_595_; 
v_res_595_ = l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__2___redArg(v_a_587_, v___y_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_);
lean_dec(v___y_593_);
lean_dec_ref(v___y_592_);
lean_dec(v___y_591_);
lean_dec_ref(v___y_590_);
lean_dec(v___y_589_);
lean_dec_ref(v___y_588_);
return v_res_595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__2(lean_object* v_00_u03b1_596_, lean_object* v_a_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_){
_start:
{
lean_object* v___x_605_; 
v___x_605_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v_a_597_, v___y_598_, v___y_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_);
return v___x_605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__2___boxed(lean_object* v_00_u03b1_606_, lean_object* v_a_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_){
_start:
{
lean_object* v_res_615_; 
v_res_615_ = l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__2(v_00_u03b1_606_, v_a_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_);
lean_dec(v___y_613_);
lean_dec_ref(v___y_612_);
lean_dec(v___y_611_);
lean_dec_ref(v___y_610_);
lean_dec(v___y_609_);
lean_dec_ref(v___y_608_);
return v_res_615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__0(lean_object* v_e_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_){
_start:
{
lean_object* v___x_625_; lean_object* v___x_626_; 
v___x_625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_625_, 0, v_e_616_);
v___x_626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_626_, 0, v___x_625_);
return v___x_626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__0___boxed(lean_object* v_e_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_){
_start:
{
lean_object* v_res_636_; 
v_res_636_ = l_Lean_Elab_Tactic_Conv_evalPattern___lam__0(v_e_627_, v___y_628_, v___y_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_, v___y_634_);
lean_dec(v___y_634_);
lean_dec_ref(v___y_633_);
lean_dec(v___y_632_);
lean_dec_ref(v___y_631_);
lean_dec(v___y_630_);
lean_dec_ref(v___y_629_);
lean_dec(v___y_628_);
return v_res_636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__1(lean_object* v___x_637_, lean_object* v___x_638_, uint8_t v___x_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_){
_start:
{
lean_object* v___x_647_; 
v___x_647_ = l_Lean_Elab_Term_elabTerm(v___x_637_, v___x_638_, v___x_639_, v___x_639_, v___y_640_, v___y_641_, v___y_642_, v___y_643_, v___y_644_, v___y_645_);
if (lean_obj_tag(v___x_647_) == 0)
{
lean_object* v_a_648_; lean_object* v___x_649_; 
v_a_648_ = lean_ctor_get(v___x_647_, 0);
lean_inc(v_a_648_);
lean_dec_ref_known(v___x_647_, 1);
v___x_649_ = l_Lean_Meta_abstractMVars(v_a_648_, v___x_639_, v___y_642_, v___y_643_, v___y_644_, v___y_645_);
return v___x_649_;
}
else
{
lean_object* v_a_650_; lean_object* v___x_652_; uint8_t v_isShared_653_; uint8_t v_isSharedCheck_657_; 
v_a_650_ = lean_ctor_get(v___x_647_, 0);
v_isSharedCheck_657_ = !lean_is_exclusive(v___x_647_);
if (v_isSharedCheck_657_ == 0)
{
v___x_652_ = v___x_647_;
v_isShared_653_ = v_isSharedCheck_657_;
goto v_resetjp_651_;
}
else
{
lean_inc(v_a_650_);
lean_dec(v___x_647_);
v___x_652_ = lean_box(0);
v_isShared_653_ = v_isSharedCheck_657_;
goto v_resetjp_651_;
}
v_resetjp_651_:
{
lean_object* v___x_655_; 
if (v_isShared_653_ == 0)
{
v___x_655_ = v___x_652_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_656_; 
v_reuseFailAlloc_656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_656_, 0, v_a_650_);
v___x_655_ = v_reuseFailAlloc_656_;
goto v_reusejp_654_;
}
v_reusejp_654_:
{
return v___x_655_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__1___boxed(lean_object* v___x_658_, lean_object* v___x_659_, lean_object* v___x_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_){
_start:
{
uint8_t v___x_18429__boxed_668_; lean_object* v_res_669_; 
v___x_18429__boxed_668_ = lean_unbox(v___x_660_);
v_res_669_ = l_Lean_Elab_Tactic_Conv_evalPattern___lam__1(v___x_658_, v___x_659_, v___x_18429__boxed_668_, v___y_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_);
lean_dec(v___y_666_);
lean_dec_ref(v___y_665_);
lean_dec(v___y_664_);
lean_dec_ref(v___y_663_);
lean_dec(v___y_662_);
lean_dec_ref(v___y_661_);
return v_res_669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__2(lean_object* v___x_670_, lean_object* v___f_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_){
_start:
{
lean_object* v_fileName_679_; lean_object* v_fileMap_680_; lean_object* v_options_681_; lean_object* v_currRecDepth_682_; lean_object* v_maxRecDepth_683_; lean_object* v_ref_684_; lean_object* v_currNamespace_685_; lean_object* v_openDecls_686_; lean_object* v_initHeartbeats_687_; lean_object* v_maxHeartbeats_688_; lean_object* v_quotContext_689_; lean_object* v_currMacroScope_690_; uint8_t v_diag_691_; lean_object* v_cancelTk_x3f_692_; uint8_t v_suppressElabErrors_693_; lean_object* v_inheritedTraceOptions_694_; lean_object* v___x_696_; uint8_t v_isShared_697_; uint8_t v_isSharedCheck_703_; 
v_fileName_679_ = lean_ctor_get(v___y_676_, 0);
v_fileMap_680_ = lean_ctor_get(v___y_676_, 1);
v_options_681_ = lean_ctor_get(v___y_676_, 2);
v_currRecDepth_682_ = lean_ctor_get(v___y_676_, 3);
v_maxRecDepth_683_ = lean_ctor_get(v___y_676_, 4);
v_ref_684_ = lean_ctor_get(v___y_676_, 5);
v_currNamespace_685_ = lean_ctor_get(v___y_676_, 6);
v_openDecls_686_ = lean_ctor_get(v___y_676_, 7);
v_initHeartbeats_687_ = lean_ctor_get(v___y_676_, 8);
v_maxHeartbeats_688_ = lean_ctor_get(v___y_676_, 9);
v_quotContext_689_ = lean_ctor_get(v___y_676_, 10);
v_currMacroScope_690_ = lean_ctor_get(v___y_676_, 11);
v_diag_691_ = lean_ctor_get_uint8(v___y_676_, sizeof(void*)*14);
v_cancelTk_x3f_692_ = lean_ctor_get(v___y_676_, 12);
v_suppressElabErrors_693_ = lean_ctor_get_uint8(v___y_676_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_694_ = lean_ctor_get(v___y_676_, 13);
v_isSharedCheck_703_ = !lean_is_exclusive(v___y_676_);
if (v_isSharedCheck_703_ == 0)
{
v___x_696_ = v___y_676_;
v_isShared_697_ = v_isSharedCheck_703_;
goto v_resetjp_695_;
}
else
{
lean_inc(v_inheritedTraceOptions_694_);
lean_inc(v_cancelTk_x3f_692_);
lean_inc(v_currMacroScope_690_);
lean_inc(v_quotContext_689_);
lean_inc(v_maxHeartbeats_688_);
lean_inc(v_initHeartbeats_687_);
lean_inc(v_openDecls_686_);
lean_inc(v_currNamespace_685_);
lean_inc(v_ref_684_);
lean_inc(v_maxRecDepth_683_);
lean_inc(v_currRecDepth_682_);
lean_inc(v_options_681_);
lean_inc(v_fileMap_680_);
lean_inc(v_fileName_679_);
lean_dec(v___y_676_);
v___x_696_ = lean_box(0);
v_isShared_697_ = v_isSharedCheck_703_;
goto v_resetjp_695_;
}
v_resetjp_695_:
{
lean_object* v_ref_698_; lean_object* v___x_700_; 
v_ref_698_ = l_Lean_replaceRef(v___x_670_, v_ref_684_);
lean_dec(v_ref_684_);
if (v_isShared_697_ == 0)
{
lean_ctor_set(v___x_696_, 5, v_ref_698_);
v___x_700_ = v___x_696_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v_fileName_679_);
lean_ctor_set(v_reuseFailAlloc_702_, 1, v_fileMap_680_);
lean_ctor_set(v_reuseFailAlloc_702_, 2, v_options_681_);
lean_ctor_set(v_reuseFailAlloc_702_, 3, v_currRecDepth_682_);
lean_ctor_set(v_reuseFailAlloc_702_, 4, v_maxRecDepth_683_);
lean_ctor_set(v_reuseFailAlloc_702_, 5, v_ref_698_);
lean_ctor_set(v_reuseFailAlloc_702_, 6, v_currNamespace_685_);
lean_ctor_set(v_reuseFailAlloc_702_, 7, v_openDecls_686_);
lean_ctor_set(v_reuseFailAlloc_702_, 8, v_initHeartbeats_687_);
lean_ctor_set(v_reuseFailAlloc_702_, 9, v_maxHeartbeats_688_);
lean_ctor_set(v_reuseFailAlloc_702_, 10, v_quotContext_689_);
lean_ctor_set(v_reuseFailAlloc_702_, 11, v_currMacroScope_690_);
lean_ctor_set(v_reuseFailAlloc_702_, 12, v_cancelTk_x3f_692_);
lean_ctor_set(v_reuseFailAlloc_702_, 13, v_inheritedTraceOptions_694_);
lean_ctor_set_uint8(v_reuseFailAlloc_702_, sizeof(void*)*14, v_diag_691_);
lean_ctor_set_uint8(v_reuseFailAlloc_702_, sizeof(void*)*14 + 1, v_suppressElabErrors_693_);
v___x_700_ = v_reuseFailAlloc_702_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
lean_object* v___x_701_; 
v___x_701_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v___f_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___x_700_, v___y_677_);
lean_dec_ref(v___x_700_);
return v___x_701_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__2___boxed(lean_object* v___x_704_, lean_object* v___f_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_){
_start:
{
lean_object* v_res_713_; 
v_res_713_ = l_Lean_Elab_Tactic_Conv_evalPattern___lam__2(v___x_704_, v___f_705_, v___y_706_, v___y_707_, v___y_708_, v___y_709_, v___y_710_, v___y_711_);
lean_dec(v___y_711_);
lean_dec(v___y_709_);
lean_dec_ref(v___y_708_);
lean_dec(v___y_707_);
lean_dec_ref(v___y_706_);
lean_dec(v___x_704_);
return v_res_713_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__3(lean_object* v___x_714_, uint8_t v___x_715_, lean_object* v_e_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_){
_start:
{
lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; 
v___x_725_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_725_, 0, v_e_716_);
lean_ctor_set(v___x_725_, 1, v___x_714_);
lean_ctor_set_uint8(v___x_725_, sizeof(void*)*2, v___x_715_);
v___x_726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_726_, 0, v___x_725_);
v___x_727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_727_, 0, v___x_726_);
return v___x_727_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__3___boxed(lean_object* v___x_728_, lean_object* v___x_729_, lean_object* v_e_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_){
_start:
{
uint8_t v___x_18523__boxed_739_; lean_object* v_res_740_; 
v___x_18523__boxed_739_ = lean_unbox(v___x_729_);
v_res_740_ = l_Lean_Elab_Tactic_Conv_evalPattern___lam__3(v___x_728_, v___x_18523__boxed_739_, v_e_730_, v___y_731_, v___y_732_, v___y_733_, v___y_734_, v___y_735_, v___y_736_, v___y_737_);
lean_dec(v___y_737_);
lean_dec_ref(v___y_736_);
lean_dec(v___y_735_);
lean_dec_ref(v___y_734_);
lean_dec(v___y_733_);
lean_dec_ref(v___y_732_);
lean_dec(v___y_731_);
return v_res_740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__4(lean_object* v___x_741_, lean_object* v_x_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_){
_start:
{
lean_object* v___x_751_; lean_object* v___x_752_; 
v___x_751_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_751_, 0, v___x_741_);
v___x_752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_752_, 0, v___x_751_);
return v___x_752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__4___boxed(lean_object* v___x_753_, lean_object* v_x_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_){
_start:
{
lean_object* v_res_763_; 
v_res_763_ = l_Lean_Elab_Tactic_Conv_evalPattern___lam__4(v___x_753_, v_x_754_, v___y_755_, v___y_756_, v___y_757_, v___y_758_, v___y_759_, v___y_760_, v___y_761_);
lean_dec(v___y_761_);
lean_dec_ref(v___y_760_);
lean_dec(v___y_759_);
lean_dec_ref(v___y_758_);
lean_dec(v___y_757_);
lean_dec_ref(v___y_756_);
lean_dec(v___y_755_);
lean_dec_ref(v_x_754_);
return v_res_763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__5(lean_object* v___x_764_, lean_object* v_x_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_){
_start:
{
lean_object* v___x_774_; 
v___x_774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_774_, 0, v___x_764_);
return v___x_774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__5___boxed(lean_object* v___x_775_, lean_object* v_x_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_){
_start:
{
lean_object* v_res_785_; 
v_res_785_ = l_Lean_Elab_Tactic_Conv_evalPattern___lam__5(v___x_775_, v_x_776_, v___y_777_, v___y_778_, v___y_779_, v___y_780_, v___y_781_, v___y_782_, v___y_783_);
lean_dec(v___y_783_);
lean_dec_ref(v___y_782_);
lean_dec(v___y_781_);
lean_dec_ref(v___y_780_);
lean_dec(v___y_779_);
lean_dec_ref(v___y_778_);
lean_dec(v___y_777_);
lean_dec_ref(v_x_776_);
return v_res_785_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__5(size_t v_sz_786_, size_t v_i_787_, lean_object* v_bs_788_){
_start:
{
uint8_t v___x_789_; 
v___x_789_ = lean_usize_dec_lt(v_i_787_, v_sz_786_);
if (v___x_789_ == 0)
{
return v_bs_788_;
}
else
{
lean_object* v_v_790_; lean_object* v_snd_791_; lean_object* v___x_792_; lean_object* v_bs_x27_793_; size_t v___x_794_; size_t v___x_795_; lean_object* v___x_796_; 
v_v_790_ = lean_array_uget_borrowed(v_bs_788_, v_i_787_);
v_snd_791_ = lean_ctor_get(v_v_790_, 1);
lean_inc(v_snd_791_);
v___x_792_ = lean_unsigned_to_nat(0u);
v_bs_x27_793_ = lean_array_uset(v_bs_788_, v_i_787_, v___x_792_);
v___x_794_ = ((size_t)1ULL);
v___x_795_ = lean_usize_add(v_i_787_, v___x_794_);
v___x_796_ = lean_array_uset(v_bs_x27_793_, v_i_787_, v_snd_791_);
v_i_787_ = v___x_795_;
v_bs_788_ = v___x_796_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__5___boxed(lean_object* v_sz_798_, lean_object* v_i_799_, lean_object* v_bs_800_){
_start:
{
size_t v_sz_boxed_801_; size_t v_i_boxed_802_; lean_object* v_res_803_; 
v_sz_boxed_801_ = lean_unbox_usize(v_sz_798_);
lean_dec(v_sz_798_);
v_i_boxed_802_ = lean_unbox_usize(v_i_799_);
lean_dec(v_i_799_);
v_res_803_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__5(v_sz_boxed_801_, v_i_boxed_802_, v_bs_800_);
return v_res_803_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4_spec__5(lean_object* v_msgData_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_){
_start:
{
lean_object* v___x_810_; lean_object* v_env_811_; lean_object* v___x_812_; lean_object* v_mctx_813_; lean_object* v_lctx_814_; lean_object* v_options_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; 
v___x_810_ = lean_st_ref_get(v___y_808_);
v_env_811_ = lean_ctor_get(v___x_810_, 0);
lean_inc_ref(v_env_811_);
lean_dec(v___x_810_);
v___x_812_ = lean_st_ref_get(v___y_806_);
v_mctx_813_ = lean_ctor_get(v___x_812_, 0);
lean_inc_ref(v_mctx_813_);
lean_dec(v___x_812_);
v_lctx_814_ = lean_ctor_get(v___y_805_, 2);
v_options_815_ = lean_ctor_get(v___y_807_, 2);
lean_inc_ref(v_options_815_);
lean_inc_ref(v_lctx_814_);
v___x_816_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_816_, 0, v_env_811_);
lean_ctor_set(v___x_816_, 1, v_mctx_813_);
lean_ctor_set(v___x_816_, 2, v_lctx_814_);
lean_ctor_set(v___x_816_, 3, v_options_815_);
v___x_817_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_817_, 0, v___x_816_);
lean_ctor_set(v___x_817_, 1, v_msgData_804_);
v___x_818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_818_, 0, v___x_817_);
return v___x_818_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4_spec__5___boxed(lean_object* v_msgData_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_){
_start:
{
lean_object* v_res_825_; 
v_res_825_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4_spec__5(v_msgData_819_, v___y_820_, v___y_821_, v___y_822_, v___y_823_);
lean_dec(v___y_823_);
lean_dec_ref(v___y_822_);
lean_dec(v___y_821_);
lean_dec_ref(v___y_820_);
return v_res_825_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg(lean_object* v_msg_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_){
_start:
{
lean_object* v_ref_832_; lean_object* v___x_833_; lean_object* v_a_834_; lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_842_; 
v_ref_832_ = lean_ctor_get(v___y_829_, 5);
v___x_833_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4_spec__5(v_msg_826_, v___y_827_, v___y_828_, v___y_829_, v___y_830_);
v_a_834_ = lean_ctor_get(v___x_833_, 0);
v_isSharedCheck_842_ = !lean_is_exclusive(v___x_833_);
if (v_isSharedCheck_842_ == 0)
{
v___x_836_ = v___x_833_;
v_isShared_837_ = v_isSharedCheck_842_;
goto v_resetjp_835_;
}
else
{
lean_inc(v_a_834_);
lean_dec(v___x_833_);
v___x_836_ = lean_box(0);
v_isShared_837_ = v_isSharedCheck_842_;
goto v_resetjp_835_;
}
v_resetjp_835_:
{
lean_object* v___x_838_; lean_object* v___x_840_; 
lean_inc(v_ref_832_);
v___x_838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_838_, 0, v_ref_832_);
lean_ctor_set(v___x_838_, 1, v_a_834_);
if (v_isShared_837_ == 0)
{
lean_ctor_set_tag(v___x_836_, 1);
lean_ctor_set(v___x_836_, 0, v___x_838_);
v___x_840_ = v___x_836_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v___x_838_);
v___x_840_ = v_reuseFailAlloc_841_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
return v___x_840_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg___boxed(lean_object* v_msg_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_){
_start:
{
lean_object* v_res_849_; 
v_res_849_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg(v_msg_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_);
lean_dec(v___y_847_);
lean_dec_ref(v___y_846_);
lean_dec(v___y_845_);
lean_dec_ref(v___y_844_);
return v_res_849_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1___redArg(lean_object* v_ref_850_, lean_object* v_msg_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_){
_start:
{
lean_object* v_fileName_861_; lean_object* v_fileMap_862_; lean_object* v_options_863_; lean_object* v_currRecDepth_864_; lean_object* v_maxRecDepth_865_; lean_object* v_ref_866_; lean_object* v_currNamespace_867_; lean_object* v_openDecls_868_; lean_object* v_initHeartbeats_869_; lean_object* v_maxHeartbeats_870_; lean_object* v_quotContext_871_; lean_object* v_currMacroScope_872_; uint8_t v_diag_873_; lean_object* v_cancelTk_x3f_874_; uint8_t v_suppressElabErrors_875_; lean_object* v_inheritedTraceOptions_876_; lean_object* v_ref_877_; lean_object* v___x_878_; lean_object* v___x_879_; 
v_fileName_861_ = lean_ctor_get(v___y_858_, 0);
v_fileMap_862_ = lean_ctor_get(v___y_858_, 1);
v_options_863_ = lean_ctor_get(v___y_858_, 2);
v_currRecDepth_864_ = lean_ctor_get(v___y_858_, 3);
v_maxRecDepth_865_ = lean_ctor_get(v___y_858_, 4);
v_ref_866_ = lean_ctor_get(v___y_858_, 5);
v_currNamespace_867_ = lean_ctor_get(v___y_858_, 6);
v_openDecls_868_ = lean_ctor_get(v___y_858_, 7);
v_initHeartbeats_869_ = lean_ctor_get(v___y_858_, 8);
v_maxHeartbeats_870_ = lean_ctor_get(v___y_858_, 9);
v_quotContext_871_ = lean_ctor_get(v___y_858_, 10);
v_currMacroScope_872_ = lean_ctor_get(v___y_858_, 11);
v_diag_873_ = lean_ctor_get_uint8(v___y_858_, sizeof(void*)*14);
v_cancelTk_x3f_874_ = lean_ctor_get(v___y_858_, 12);
v_suppressElabErrors_875_ = lean_ctor_get_uint8(v___y_858_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_876_ = lean_ctor_get(v___y_858_, 13);
v_ref_877_ = l_Lean_replaceRef(v_ref_850_, v_ref_866_);
lean_inc_ref(v_inheritedTraceOptions_876_);
lean_inc(v_cancelTk_x3f_874_);
lean_inc(v_currMacroScope_872_);
lean_inc(v_quotContext_871_);
lean_inc(v_maxHeartbeats_870_);
lean_inc(v_initHeartbeats_869_);
lean_inc(v_openDecls_868_);
lean_inc(v_currNamespace_867_);
lean_inc(v_maxRecDepth_865_);
lean_inc(v_currRecDepth_864_);
lean_inc_ref(v_options_863_);
lean_inc_ref(v_fileMap_862_);
lean_inc_ref(v_fileName_861_);
v___x_878_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_878_, 0, v_fileName_861_);
lean_ctor_set(v___x_878_, 1, v_fileMap_862_);
lean_ctor_set(v___x_878_, 2, v_options_863_);
lean_ctor_set(v___x_878_, 3, v_currRecDepth_864_);
lean_ctor_set(v___x_878_, 4, v_maxRecDepth_865_);
lean_ctor_set(v___x_878_, 5, v_ref_877_);
lean_ctor_set(v___x_878_, 6, v_currNamespace_867_);
lean_ctor_set(v___x_878_, 7, v_openDecls_868_);
lean_ctor_set(v___x_878_, 8, v_initHeartbeats_869_);
lean_ctor_set(v___x_878_, 9, v_maxHeartbeats_870_);
lean_ctor_set(v___x_878_, 10, v_quotContext_871_);
lean_ctor_set(v___x_878_, 11, v_currMacroScope_872_);
lean_ctor_set(v___x_878_, 12, v_cancelTk_x3f_874_);
lean_ctor_set(v___x_878_, 13, v_inheritedTraceOptions_876_);
lean_ctor_set_uint8(v___x_878_, sizeof(void*)*14, v_diag_873_);
lean_ctor_set_uint8(v___x_878_, sizeof(void*)*14 + 1, v_suppressElabErrors_875_);
v___x_879_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg(v_msg_851_, v___y_856_, v___y_857_, v___x_878_, v___y_859_);
lean_dec_ref_known(v___x_878_, 14);
return v___x_879_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1___redArg___boxed(lean_object* v_ref_880_, lean_object* v_msg_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_){
_start:
{
lean_object* v_res_891_; 
v_res_891_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1___redArg(v_ref_880_, v_msg_881_, v___y_882_, v___y_883_, v___y_884_, v___y_885_, v___y_886_, v___y_887_, v___y_888_, v___y_889_);
lean_dec(v___y_889_);
lean_dec_ref(v___y_888_);
lean_dec(v___y_887_);
lean_dec_ref(v___y_886_);
lean_dec(v___y_885_);
lean_dec_ref(v___y_884_);
lean_dec(v___y_883_);
lean_dec_ref(v___y_882_);
lean_dec(v_ref_880_);
return v_res_891_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_893_; lean_object* v___x_894_; 
v___x_893_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg___closed__0));
v___x_894_ = l_Lean_stringToMessageData(v___x_893_);
return v___x_894_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg(size_t v_sz_895_, size_t v_i_896_, lean_object* v_bs_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_){
_start:
{
uint8_t v___x_907_; 
v___x_907_ = lean_usize_dec_lt(v_i_896_, v_sz_895_);
if (v___x_907_ == 0)
{
lean_object* v___x_908_; 
v___x_908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_908_, 0, v_bs_897_);
return v___x_908_;
}
else
{
lean_object* v_v_909_; lean_object* v___x_910_; lean_object* v_bs_x27_911_; lean_object* v_a_913_; lean_object* v___x_918_; uint8_t v_isZero_919_; 
v_v_909_ = lean_array_uget(v_bs_897_, v_i_896_);
v___x_910_ = lean_unsigned_to_nat(0u);
v_bs_x27_911_ = lean_array_uset(v_bs_897_, v_i_896_, v___x_910_);
v___x_918_ = l_Lean_TSyntax_getNat(v_v_909_);
v_isZero_919_ = lean_nat_dec_eq(v___x_918_, v___x_910_);
if (v_isZero_919_ == 1)
{
lean_object* v___x_920_; lean_object* v___x_921_; 
lean_dec(v___x_918_);
v___x_920_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg___closed__1);
v___x_921_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1___redArg(v_v_909_, v___x_920_, v___y_898_, v___y_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_);
lean_dec(v_v_909_);
if (lean_obj_tag(v___x_921_) == 0)
{
lean_object* v_a_922_; 
v_a_922_ = lean_ctor_get(v___x_921_, 0);
lean_inc(v_a_922_);
lean_dec_ref_known(v___x_921_, 1);
v_a_913_ = v_a_922_;
goto v___jp_912_;
}
else
{
lean_object* v_a_923_; lean_object* v___x_925_; uint8_t v_isShared_926_; uint8_t v_isSharedCheck_930_; 
lean_dec_ref(v_bs_x27_911_);
v_a_923_ = lean_ctor_get(v___x_921_, 0);
v_isSharedCheck_930_ = !lean_is_exclusive(v___x_921_);
if (v_isSharedCheck_930_ == 0)
{
v___x_925_ = v___x_921_;
v_isShared_926_ = v_isSharedCheck_930_;
goto v_resetjp_924_;
}
else
{
lean_inc(v_a_923_);
lean_dec(v___x_921_);
v___x_925_ = lean_box(0);
v_isShared_926_ = v_isSharedCheck_930_;
goto v_resetjp_924_;
}
v_resetjp_924_:
{
lean_object* v___x_928_; 
if (v_isShared_926_ == 0)
{
v___x_928_ = v___x_925_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v_a_923_);
v___x_928_ = v_reuseFailAlloc_929_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
return v___x_928_;
}
}
}
}
else
{
lean_object* v___x_931_; lean_object* v_one_932_; lean_object* v_n_933_; lean_object* v___x_934_; 
lean_dec(v_v_909_);
v___x_931_ = lean_usize_to_nat(v_i_896_);
v_one_932_ = lean_unsigned_to_nat(1u);
v_n_933_ = lean_nat_sub(v___x_918_, v_one_932_);
lean_dec(v___x_918_);
v___x_934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_934_, 0, v_n_933_);
lean_ctor_set(v___x_934_, 1, v___x_931_);
v_a_913_ = v___x_934_;
goto v___jp_912_;
}
v___jp_912_:
{
size_t v___x_914_; size_t v___x_915_; lean_object* v___x_916_; 
v___x_914_ = ((size_t)1ULL);
v___x_915_ = lean_usize_add(v_i_896_, v___x_914_);
v___x_916_ = lean_array_uset(v_bs_x27_911_, v_i_896_, v_a_913_);
v_i_896_ = v___x_915_;
v_bs_897_ = v___x_916_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg___boxed(lean_object* v_sz_935_, lean_object* v_i_936_, lean_object* v_bs_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_){
_start:
{
size_t v_sz_boxed_947_; size_t v_i_boxed_948_; lean_object* v_res_949_; 
v_sz_boxed_947_ = lean_unbox_usize(v_sz_935_);
lean_dec(v_sz_935_);
v_i_boxed_948_ = lean_unbox_usize(v_i_936_);
lean_dec(v_i_936_);
v_res_949_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg(v_sz_boxed_947_, v_i_boxed_948_, v_bs_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_);
lean_dec(v___y_945_);
lean_dec_ref(v___y_944_);
lean_dec(v___y_943_);
lean_dec_ref(v___y_942_);
lean_dec(v___y_941_);
lean_dec_ref(v___y_940_);
lean_dec(v___y_939_);
lean_dec_ref(v___y_938_);
return v_res_949_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6_spec__8___redArg(lean_object* v_hi_950_, lean_object* v_pivot_951_, lean_object* v_as_952_, lean_object* v_i_953_, lean_object* v_k_954_){
_start:
{
uint8_t v___x_955_; 
v___x_955_ = lean_nat_dec_lt(v_k_954_, v_hi_950_);
if (v___x_955_ == 0)
{
lean_object* v___x_956_; lean_object* v___x_957_; 
lean_dec(v_k_954_);
v___x_956_ = lean_array_fswap(v_as_952_, v_i_953_, v_hi_950_);
v___x_957_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_957_, 0, v_i_953_);
lean_ctor_set(v___x_957_, 1, v___x_956_);
return v___x_957_;
}
else
{
lean_object* v___x_958_; lean_object* v_fst_959_; lean_object* v_fst_960_; uint8_t v___x_961_; 
v___x_958_ = lean_array_fget_borrowed(v_as_952_, v_k_954_);
v_fst_959_ = lean_ctor_get(v___x_958_, 0);
v_fst_960_ = lean_ctor_get(v_pivot_951_, 0);
v___x_961_ = lean_nat_dec_lt(v_fst_959_, v_fst_960_);
if (v___x_961_ == 0)
{
lean_object* v___x_962_; lean_object* v___x_963_; 
v___x_962_ = lean_unsigned_to_nat(1u);
v___x_963_ = lean_nat_add(v_k_954_, v___x_962_);
lean_dec(v_k_954_);
v_k_954_ = v___x_963_;
goto _start;
}
else
{
lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; 
v___x_965_ = lean_array_fswap(v_as_952_, v_i_953_, v_k_954_);
v___x_966_ = lean_unsigned_to_nat(1u);
v___x_967_ = lean_nat_add(v_i_953_, v___x_966_);
lean_dec(v_i_953_);
v___x_968_ = lean_nat_add(v_k_954_, v___x_966_);
lean_dec(v_k_954_);
v_as_952_ = v___x_965_;
v_i_953_ = v___x_967_;
v_k_954_ = v___x_968_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6_spec__8___redArg___boxed(lean_object* v_hi_970_, lean_object* v_pivot_971_, lean_object* v_as_972_, lean_object* v_i_973_, lean_object* v_k_974_){
_start:
{
lean_object* v_res_975_; 
v_res_975_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6_spec__8___redArg(v_hi_970_, v_pivot_971_, v_as_972_, v_i_973_, v_k_974_);
lean_dec_ref(v_pivot_971_);
lean_dec(v_hi_970_);
return v_res_975_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg___lam__0(lean_object* v_x1_976_, lean_object* v_x2_977_){
_start:
{
lean_object* v_fst_978_; lean_object* v_fst_979_; uint8_t v___x_980_; 
v_fst_978_ = lean_ctor_get(v_x1_976_, 0);
v_fst_979_ = lean_ctor_get(v_x2_977_, 0);
v___x_980_ = lean_nat_dec_lt(v_fst_978_, v_fst_979_);
return v___x_980_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg___lam__0___boxed(lean_object* v_x1_981_, lean_object* v_x2_982_){
_start:
{
uint8_t v_res_983_; lean_object* v_r_984_; 
v_res_983_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg___lam__0(v_x1_981_, v_x2_982_);
lean_dec_ref(v_x2_982_);
lean_dec_ref(v_x1_981_);
v_r_984_ = lean_box(v_res_983_);
return v_r_984_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg(lean_object* v_n_985_, lean_object* v_as_986_, lean_object* v_lo_987_, lean_object* v_hi_988_){
_start:
{
lean_object* v___y_990_; uint8_t v___x_1000_; 
v___x_1000_ = lean_nat_dec_lt(v_lo_987_, v_hi_988_);
if (v___x_1000_ == 0)
{
lean_dec(v_lo_987_);
return v_as_986_;
}
else
{
lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v_mid_1003_; lean_object* v___y_1005_; lean_object* v___y_1011_; lean_object* v___x_1016_; lean_object* v___x_1017_; uint8_t v___x_1018_; 
v___x_1001_ = lean_nat_add(v_lo_987_, v_hi_988_);
v___x_1002_ = lean_unsigned_to_nat(1u);
v_mid_1003_ = lean_nat_shiftr(v___x_1001_, v___x_1002_);
lean_dec(v___x_1001_);
v___x_1016_ = lean_array_fget_borrowed(v_as_986_, v_mid_1003_);
v___x_1017_ = lean_array_fget_borrowed(v_as_986_, v_lo_987_);
v___x_1018_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg___lam__0(v___x_1016_, v___x_1017_);
if (v___x_1018_ == 0)
{
v___y_1011_ = v_as_986_;
goto v___jp_1010_;
}
else
{
lean_object* v___x_1019_; 
v___x_1019_ = lean_array_fswap(v_as_986_, v_lo_987_, v_mid_1003_);
v___y_1011_ = v___x_1019_;
goto v___jp_1010_;
}
v___jp_1004_:
{
lean_object* v___x_1006_; lean_object* v___x_1007_; uint8_t v___x_1008_; 
v___x_1006_ = lean_array_fget_borrowed(v___y_1005_, v_mid_1003_);
v___x_1007_ = lean_array_fget_borrowed(v___y_1005_, v_hi_988_);
v___x_1008_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg___lam__0(v___x_1006_, v___x_1007_);
if (v___x_1008_ == 0)
{
lean_dec(v_mid_1003_);
v___y_990_ = v___y_1005_;
goto v___jp_989_;
}
else
{
lean_object* v___x_1009_; 
v___x_1009_ = lean_array_fswap(v___y_1005_, v_mid_1003_, v_hi_988_);
lean_dec(v_mid_1003_);
v___y_990_ = v___x_1009_;
goto v___jp_989_;
}
}
v___jp_1010_:
{
lean_object* v___x_1012_; lean_object* v___x_1013_; uint8_t v___x_1014_; 
v___x_1012_ = lean_array_fget_borrowed(v___y_1011_, v_hi_988_);
v___x_1013_ = lean_array_fget_borrowed(v___y_1011_, v_lo_987_);
v___x_1014_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg___lam__0(v___x_1012_, v___x_1013_);
if (v___x_1014_ == 0)
{
v___y_1005_ = v___y_1011_;
goto v___jp_1004_;
}
else
{
lean_object* v___x_1015_; 
v___x_1015_ = lean_array_fswap(v___y_1011_, v_lo_987_, v_hi_988_);
v___y_1005_ = v___x_1015_;
goto v___jp_1004_;
}
}
}
v___jp_989_:
{
lean_object* v_pivot_991_; lean_object* v___x_992_; lean_object* v_fst_993_; lean_object* v_snd_994_; uint8_t v___x_995_; 
v_pivot_991_ = lean_array_fget(v___y_990_, v_hi_988_);
lean_inc_n(v_lo_987_, 2);
v___x_992_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6_spec__8___redArg(v_hi_988_, v_pivot_991_, v___y_990_, v_lo_987_, v_lo_987_);
lean_dec(v_pivot_991_);
v_fst_993_ = lean_ctor_get(v___x_992_, 0);
lean_inc(v_fst_993_);
v_snd_994_ = lean_ctor_get(v___x_992_, 1);
lean_inc(v_snd_994_);
lean_dec_ref(v___x_992_);
v___x_995_ = lean_nat_dec_le(v_hi_988_, v_fst_993_);
if (v___x_995_ == 0)
{
lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; 
v___x_996_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg(v_n_985_, v_snd_994_, v_lo_987_, v_fst_993_);
v___x_997_ = lean_unsigned_to_nat(1u);
v___x_998_ = lean_nat_add(v_fst_993_, v___x_997_);
lean_dec(v_fst_993_);
v_as_986_ = v___x_996_;
v_lo_987_ = v___x_998_;
goto _start;
}
else
{
lean_dec(v_fst_993_);
lean_dec(v_lo_987_);
return v_snd_994_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg___boxed(lean_object* v_n_1020_, lean_object* v_as_1021_, lean_object* v_lo_1022_, lean_object* v_hi_1023_){
_start:
{
lean_object* v_res_1024_; 
v_res_1024_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg(v_n_1020_, v_as_1021_, v_lo_1022_, v_hi_1023_);
lean_dec(v_hi_1023_);
lean_dec(v_n_1020_);
return v_res_1024_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__12_spec__16___redArg(lean_object* v_x_1025_, lean_object* v_x_1026_, lean_object* v_x_1027_, lean_object* v_x_1028_){
_start:
{
lean_object* v_ks_1029_; lean_object* v_vs_1030_; lean_object* v___x_1032_; uint8_t v_isShared_1033_; uint8_t v_isSharedCheck_1054_; 
v_ks_1029_ = lean_ctor_get(v_x_1025_, 0);
v_vs_1030_ = lean_ctor_get(v_x_1025_, 1);
v_isSharedCheck_1054_ = !lean_is_exclusive(v_x_1025_);
if (v_isSharedCheck_1054_ == 0)
{
v___x_1032_ = v_x_1025_;
v_isShared_1033_ = v_isSharedCheck_1054_;
goto v_resetjp_1031_;
}
else
{
lean_inc(v_vs_1030_);
lean_inc(v_ks_1029_);
lean_dec(v_x_1025_);
v___x_1032_ = lean_box(0);
v_isShared_1033_ = v_isSharedCheck_1054_;
goto v_resetjp_1031_;
}
v_resetjp_1031_:
{
lean_object* v___x_1034_; uint8_t v___x_1035_; 
v___x_1034_ = lean_array_get_size(v_ks_1029_);
v___x_1035_ = lean_nat_dec_lt(v_x_1026_, v___x_1034_);
if (v___x_1035_ == 0)
{
lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1039_; 
lean_dec(v_x_1026_);
v___x_1036_ = lean_array_push(v_ks_1029_, v_x_1027_);
v___x_1037_ = lean_array_push(v_vs_1030_, v_x_1028_);
if (v_isShared_1033_ == 0)
{
lean_ctor_set(v___x_1032_, 1, v___x_1037_);
lean_ctor_set(v___x_1032_, 0, v___x_1036_);
v___x_1039_ = v___x_1032_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v___x_1036_);
lean_ctor_set(v_reuseFailAlloc_1040_, 1, v___x_1037_);
v___x_1039_ = v_reuseFailAlloc_1040_;
goto v_reusejp_1038_;
}
v_reusejp_1038_:
{
return v___x_1039_;
}
}
else
{
lean_object* v_k_x27_1041_; uint8_t v___x_1042_; 
v_k_x27_1041_ = lean_array_fget_borrowed(v_ks_1029_, v_x_1026_);
v___x_1042_ = l_Lean_instBEqMVarId_beq(v_x_1027_, v_k_x27_1041_);
if (v___x_1042_ == 0)
{
lean_object* v___x_1044_; 
if (v_isShared_1033_ == 0)
{
v___x_1044_ = v___x_1032_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v_ks_1029_);
lean_ctor_set(v_reuseFailAlloc_1048_, 1, v_vs_1030_);
v___x_1044_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
lean_object* v___x_1045_; lean_object* v___x_1046_; 
v___x_1045_ = lean_unsigned_to_nat(1u);
v___x_1046_ = lean_nat_add(v_x_1026_, v___x_1045_);
lean_dec(v_x_1026_);
v_x_1025_ = v___x_1044_;
v_x_1026_ = v___x_1046_;
goto _start;
}
}
else
{
lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1052_; 
v___x_1049_ = lean_array_fset(v_ks_1029_, v_x_1026_, v_x_1027_);
v___x_1050_ = lean_array_fset(v_vs_1030_, v_x_1026_, v_x_1028_);
lean_dec(v_x_1026_);
if (v_isShared_1033_ == 0)
{
lean_ctor_set(v___x_1032_, 1, v___x_1050_);
lean_ctor_set(v___x_1032_, 0, v___x_1049_);
v___x_1052_ = v___x_1032_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v___x_1049_);
lean_ctor_set(v_reuseFailAlloc_1053_, 1, v___x_1050_);
v___x_1052_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
return v___x_1052_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__12___redArg(lean_object* v_n_1055_, lean_object* v_k_1056_, lean_object* v_v_1057_){
_start:
{
lean_object* v___x_1058_; lean_object* v___x_1059_; 
v___x_1058_ = lean_unsigned_to_nat(0u);
v___x_1059_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__12_spec__16___redArg(v_n_1055_, v___x_1058_, v_k_1056_, v_v_1057_);
return v___x_1059_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_1060_; 
v___x_1060_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1060_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg(lean_object* v_x_1061_, size_t v_x_1062_, size_t v_x_1063_, lean_object* v_x_1064_, lean_object* v_x_1065_){
_start:
{
if (lean_obj_tag(v_x_1061_) == 0)
{
lean_object* v_es_1066_; size_t v___x_1067_; size_t v___x_1068_; lean_object* v_j_1069_; lean_object* v___x_1070_; uint8_t v___x_1071_; 
v_es_1066_ = lean_ctor_get(v_x_1061_, 0);
v___x_1067_ = ((size_t)31ULL);
v___x_1068_ = lean_usize_land(v_x_1062_, v___x_1067_);
v_j_1069_ = lean_usize_to_nat(v___x_1068_);
v___x_1070_ = lean_array_get_size(v_es_1066_);
v___x_1071_ = lean_nat_dec_lt(v_j_1069_, v___x_1070_);
if (v___x_1071_ == 0)
{
lean_dec(v_j_1069_);
lean_dec(v_x_1065_);
lean_dec(v_x_1064_);
return v_x_1061_;
}
else
{
lean_object* v___x_1073_; uint8_t v_isShared_1074_; uint8_t v_isSharedCheck_1110_; 
lean_inc_ref(v_es_1066_);
v_isSharedCheck_1110_ = !lean_is_exclusive(v_x_1061_);
if (v_isSharedCheck_1110_ == 0)
{
lean_object* v_unused_1111_; 
v_unused_1111_ = lean_ctor_get(v_x_1061_, 0);
lean_dec(v_unused_1111_);
v___x_1073_ = v_x_1061_;
v_isShared_1074_ = v_isSharedCheck_1110_;
goto v_resetjp_1072_;
}
else
{
lean_dec(v_x_1061_);
v___x_1073_ = lean_box(0);
v_isShared_1074_ = v_isSharedCheck_1110_;
goto v_resetjp_1072_;
}
v_resetjp_1072_:
{
lean_object* v_v_1075_; lean_object* v___x_1076_; lean_object* v_xs_x27_1077_; lean_object* v___y_1079_; 
v_v_1075_ = lean_array_fget(v_es_1066_, v_j_1069_);
v___x_1076_ = lean_box(0);
v_xs_x27_1077_ = lean_array_fset(v_es_1066_, v_j_1069_, v___x_1076_);
switch(lean_obj_tag(v_v_1075_))
{
case 0:
{
lean_object* v_key_1084_; lean_object* v_val_1085_; lean_object* v___x_1087_; uint8_t v_isShared_1088_; uint8_t v_isSharedCheck_1095_; 
v_key_1084_ = lean_ctor_get(v_v_1075_, 0);
v_val_1085_ = lean_ctor_get(v_v_1075_, 1);
v_isSharedCheck_1095_ = !lean_is_exclusive(v_v_1075_);
if (v_isSharedCheck_1095_ == 0)
{
v___x_1087_ = v_v_1075_;
v_isShared_1088_ = v_isSharedCheck_1095_;
goto v_resetjp_1086_;
}
else
{
lean_inc(v_val_1085_);
lean_inc(v_key_1084_);
lean_dec(v_v_1075_);
v___x_1087_ = lean_box(0);
v_isShared_1088_ = v_isSharedCheck_1095_;
goto v_resetjp_1086_;
}
v_resetjp_1086_:
{
uint8_t v___x_1089_; 
v___x_1089_ = l_Lean_instBEqMVarId_beq(v_x_1064_, v_key_1084_);
if (v___x_1089_ == 0)
{
lean_object* v___x_1090_; lean_object* v___x_1091_; 
lean_del_object(v___x_1087_);
v___x_1090_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1084_, v_val_1085_, v_x_1064_, v_x_1065_);
v___x_1091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1091_, 0, v___x_1090_);
v___y_1079_ = v___x_1091_;
goto v___jp_1078_;
}
else
{
lean_object* v___x_1093_; 
lean_dec(v_val_1085_);
lean_dec(v_key_1084_);
if (v_isShared_1088_ == 0)
{
lean_ctor_set(v___x_1087_, 1, v_x_1065_);
lean_ctor_set(v___x_1087_, 0, v_x_1064_);
v___x_1093_ = v___x_1087_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1094_; 
v_reuseFailAlloc_1094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1094_, 0, v_x_1064_);
lean_ctor_set(v_reuseFailAlloc_1094_, 1, v_x_1065_);
v___x_1093_ = v_reuseFailAlloc_1094_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
v___y_1079_ = v___x_1093_;
goto v___jp_1078_;
}
}
}
}
case 1:
{
lean_object* v_node_1096_; lean_object* v___x_1098_; uint8_t v_isShared_1099_; uint8_t v_isSharedCheck_1108_; 
v_node_1096_ = lean_ctor_get(v_v_1075_, 0);
v_isSharedCheck_1108_ = !lean_is_exclusive(v_v_1075_);
if (v_isSharedCheck_1108_ == 0)
{
v___x_1098_ = v_v_1075_;
v_isShared_1099_ = v_isSharedCheck_1108_;
goto v_resetjp_1097_;
}
else
{
lean_inc(v_node_1096_);
lean_dec(v_v_1075_);
v___x_1098_ = lean_box(0);
v_isShared_1099_ = v_isSharedCheck_1108_;
goto v_resetjp_1097_;
}
v_resetjp_1097_:
{
size_t v___x_1100_; size_t v___x_1101_; size_t v___x_1102_; size_t v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1106_; 
v___x_1100_ = ((size_t)5ULL);
v___x_1101_ = lean_usize_shift_right(v_x_1062_, v___x_1100_);
v___x_1102_ = ((size_t)1ULL);
v___x_1103_ = lean_usize_add(v_x_1063_, v___x_1102_);
v___x_1104_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg(v_node_1096_, v___x_1101_, v___x_1103_, v_x_1064_, v_x_1065_);
if (v_isShared_1099_ == 0)
{
lean_ctor_set(v___x_1098_, 0, v___x_1104_);
v___x_1106_ = v___x_1098_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v___x_1104_);
v___x_1106_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
v___y_1079_ = v___x_1106_;
goto v___jp_1078_;
}
}
}
default: 
{
lean_object* v___x_1109_; 
v___x_1109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1109_, 0, v_x_1064_);
lean_ctor_set(v___x_1109_, 1, v_x_1065_);
v___y_1079_ = v___x_1109_;
goto v___jp_1078_;
}
}
v___jp_1078_:
{
lean_object* v___x_1080_; lean_object* v___x_1082_; 
v___x_1080_ = lean_array_fset(v_xs_x27_1077_, v_j_1069_, v___y_1079_);
lean_dec(v_j_1069_);
if (v_isShared_1074_ == 0)
{
lean_ctor_set(v___x_1073_, 0, v___x_1080_);
v___x_1082_ = v___x_1073_;
goto v_reusejp_1081_;
}
else
{
lean_object* v_reuseFailAlloc_1083_; 
v_reuseFailAlloc_1083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1083_, 0, v___x_1080_);
v___x_1082_ = v_reuseFailAlloc_1083_;
goto v_reusejp_1081_;
}
v_reusejp_1081_:
{
return v___x_1082_;
}
}
}
}
}
else
{
lean_object* v_ks_1112_; lean_object* v_vs_1113_; lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1133_; 
v_ks_1112_ = lean_ctor_get(v_x_1061_, 0);
v_vs_1113_ = lean_ctor_get(v_x_1061_, 1);
v_isSharedCheck_1133_ = !lean_is_exclusive(v_x_1061_);
if (v_isSharedCheck_1133_ == 0)
{
v___x_1115_ = v_x_1061_;
v_isShared_1116_ = v_isSharedCheck_1133_;
goto v_resetjp_1114_;
}
else
{
lean_inc(v_vs_1113_);
lean_inc(v_ks_1112_);
lean_dec(v_x_1061_);
v___x_1115_ = lean_box(0);
v_isShared_1116_ = v_isSharedCheck_1133_;
goto v_resetjp_1114_;
}
v_resetjp_1114_:
{
lean_object* v___x_1118_; 
if (v_isShared_1116_ == 0)
{
v___x_1118_ = v___x_1115_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1132_; 
v_reuseFailAlloc_1132_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1132_, 0, v_ks_1112_);
lean_ctor_set(v_reuseFailAlloc_1132_, 1, v_vs_1113_);
v___x_1118_ = v_reuseFailAlloc_1132_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
lean_object* v_newNode_1119_; uint8_t v___y_1121_; size_t v___x_1127_; uint8_t v___x_1128_; 
v_newNode_1119_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__12___redArg(v___x_1118_, v_x_1064_, v_x_1065_);
v___x_1127_ = ((size_t)7ULL);
v___x_1128_ = lean_usize_dec_le(v___x_1127_, v_x_1063_);
if (v___x_1128_ == 0)
{
lean_object* v___x_1129_; lean_object* v___x_1130_; uint8_t v___x_1131_; 
v___x_1129_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1119_);
v___x_1130_ = lean_unsigned_to_nat(4u);
v___x_1131_ = lean_nat_dec_lt(v___x_1129_, v___x_1130_);
lean_dec(v___x_1129_);
v___y_1121_ = v___x_1131_;
goto v___jp_1120_;
}
else
{
v___y_1121_ = v___x_1128_;
goto v___jp_1120_;
}
v___jp_1120_:
{
if (v___y_1121_ == 0)
{
lean_object* v_ks_1122_; lean_object* v_vs_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; 
v_ks_1122_ = lean_ctor_get(v_newNode_1119_, 0);
lean_inc_ref(v_ks_1122_);
v_vs_1123_ = lean_ctor_get(v_newNode_1119_, 1);
lean_inc_ref(v_vs_1123_);
lean_dec_ref(v_newNode_1119_);
v___x_1124_ = lean_unsigned_to_nat(0u);
v___x_1125_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__0);
v___x_1126_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__13___redArg(v_x_1063_, v_ks_1122_, v_vs_1123_, v___x_1124_, v___x_1125_);
lean_dec_ref(v_vs_1123_);
lean_dec_ref(v_ks_1122_);
return v___x_1126_;
}
else
{
return v_newNode_1119_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__13___redArg(size_t v_depth_1134_, lean_object* v_keys_1135_, lean_object* v_vals_1136_, lean_object* v_i_1137_, lean_object* v_entries_1138_){
_start:
{
lean_object* v___x_1139_; uint8_t v___x_1140_; 
v___x_1139_ = lean_array_get_size(v_keys_1135_);
v___x_1140_ = lean_nat_dec_lt(v_i_1137_, v___x_1139_);
if (v___x_1140_ == 0)
{
lean_dec(v_i_1137_);
return v_entries_1138_;
}
else
{
lean_object* v_k_1141_; lean_object* v_v_1142_; uint64_t v___x_1143_; size_t v_h_1144_; size_t v___x_1145_; lean_object* v___x_1146_; size_t v___x_1147_; size_t v___x_1148_; size_t v___x_1149_; size_t v_h_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; 
v_k_1141_ = lean_array_fget_borrowed(v_keys_1135_, v_i_1137_);
v_v_1142_ = lean_array_fget_borrowed(v_vals_1136_, v_i_1137_);
v___x_1143_ = l_Lean_instHashableMVarId_hash(v_k_1141_);
v_h_1144_ = lean_uint64_to_usize(v___x_1143_);
v___x_1145_ = ((size_t)5ULL);
v___x_1146_ = lean_unsigned_to_nat(1u);
v___x_1147_ = ((size_t)1ULL);
v___x_1148_ = lean_usize_sub(v_depth_1134_, v___x_1147_);
v___x_1149_ = lean_usize_mul(v___x_1145_, v___x_1148_);
v_h_1150_ = lean_usize_shift_right(v_h_1144_, v___x_1149_);
v___x_1151_ = lean_nat_add(v_i_1137_, v___x_1146_);
lean_dec(v_i_1137_);
lean_inc(v_v_1142_);
lean_inc(v_k_1141_);
v___x_1152_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg(v_entries_1138_, v_h_1150_, v_depth_1134_, v_k_1141_, v_v_1142_);
v_i_1137_ = v___x_1151_;
v_entries_1138_ = v___x_1152_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__13___redArg___boxed(lean_object* v_depth_1154_, lean_object* v_keys_1155_, lean_object* v_vals_1156_, lean_object* v_i_1157_, lean_object* v_entries_1158_){
_start:
{
size_t v_depth_boxed_1159_; lean_object* v_res_1160_; 
v_depth_boxed_1159_ = lean_unbox_usize(v_depth_1154_);
lean_dec(v_depth_1154_);
v_res_1160_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__13___redArg(v_depth_boxed_1159_, v_keys_1155_, v_vals_1156_, v_i_1157_, v_entries_1158_);
lean_dec_ref(v_vals_1156_);
lean_dec_ref(v_keys_1155_);
return v_res_1160_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___boxed(lean_object* v_x_1161_, lean_object* v_x_1162_, lean_object* v_x_1163_, lean_object* v_x_1164_, lean_object* v_x_1165_){
_start:
{
size_t v_x_18981__boxed_1166_; size_t v_x_18982__boxed_1167_; lean_object* v_res_1168_; 
v_x_18981__boxed_1166_ = lean_unbox_usize(v_x_1162_);
lean_dec(v_x_1162_);
v_x_18982__boxed_1167_ = lean_unbox_usize(v_x_1163_);
lean_dec(v_x_1163_);
v_res_1168_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg(v_x_1161_, v_x_18981__boxed_1166_, v_x_18982__boxed_1167_, v_x_1164_, v_x_1165_);
return v_res_1168_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3___redArg(lean_object* v_x_1169_, lean_object* v_x_1170_, lean_object* v_x_1171_){
_start:
{
uint64_t v___x_1172_; size_t v___x_1173_; size_t v___x_1174_; lean_object* v___x_1175_; 
v___x_1172_ = l_Lean_instHashableMVarId_hash(v_x_1170_);
v___x_1173_ = lean_uint64_to_usize(v___x_1172_);
v___x_1174_ = ((size_t)1ULL);
v___x_1175_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg(v_x_1169_, v___x_1173_, v___x_1174_, v_x_1170_, v_x_1171_);
return v___x_1175_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3___redArg(lean_object* v_mvarId_1176_, lean_object* v_val_1177_, lean_object* v___y_1178_){
_start:
{
lean_object* v___x_1180_; lean_object* v_mctx_1181_; lean_object* v_cache_1182_; lean_object* v_zetaDeltaFVarIds_1183_; lean_object* v_postponed_1184_; lean_object* v_diag_1185_; lean_object* v___x_1187_; uint8_t v_isShared_1188_; uint8_t v_isSharedCheck_1213_; 
v___x_1180_ = lean_st_ref_take(v___y_1178_);
v_mctx_1181_ = lean_ctor_get(v___x_1180_, 0);
v_cache_1182_ = lean_ctor_get(v___x_1180_, 1);
v_zetaDeltaFVarIds_1183_ = lean_ctor_get(v___x_1180_, 2);
v_postponed_1184_ = lean_ctor_get(v___x_1180_, 3);
v_diag_1185_ = lean_ctor_get(v___x_1180_, 4);
v_isSharedCheck_1213_ = !lean_is_exclusive(v___x_1180_);
if (v_isSharedCheck_1213_ == 0)
{
v___x_1187_ = v___x_1180_;
v_isShared_1188_ = v_isSharedCheck_1213_;
goto v_resetjp_1186_;
}
else
{
lean_inc(v_diag_1185_);
lean_inc(v_postponed_1184_);
lean_inc(v_zetaDeltaFVarIds_1183_);
lean_inc(v_cache_1182_);
lean_inc(v_mctx_1181_);
lean_dec(v___x_1180_);
v___x_1187_ = lean_box(0);
v_isShared_1188_ = v_isSharedCheck_1213_;
goto v_resetjp_1186_;
}
v_resetjp_1186_:
{
lean_object* v_depth_1189_; lean_object* v_levelAssignDepth_1190_; lean_object* v_lmvarCounter_1191_; lean_object* v_mvarCounter_1192_; lean_object* v_lDecls_1193_; lean_object* v_decls_1194_; lean_object* v_userNames_1195_; lean_object* v_lAssignment_1196_; lean_object* v_eAssignment_1197_; lean_object* v_dAssignment_1198_; lean_object* v___x_1200_; uint8_t v_isShared_1201_; uint8_t v_isSharedCheck_1212_; 
v_depth_1189_ = lean_ctor_get(v_mctx_1181_, 0);
v_levelAssignDepth_1190_ = lean_ctor_get(v_mctx_1181_, 1);
v_lmvarCounter_1191_ = lean_ctor_get(v_mctx_1181_, 2);
v_mvarCounter_1192_ = lean_ctor_get(v_mctx_1181_, 3);
v_lDecls_1193_ = lean_ctor_get(v_mctx_1181_, 4);
v_decls_1194_ = lean_ctor_get(v_mctx_1181_, 5);
v_userNames_1195_ = lean_ctor_get(v_mctx_1181_, 6);
v_lAssignment_1196_ = lean_ctor_get(v_mctx_1181_, 7);
v_eAssignment_1197_ = lean_ctor_get(v_mctx_1181_, 8);
v_dAssignment_1198_ = lean_ctor_get(v_mctx_1181_, 9);
v_isSharedCheck_1212_ = !lean_is_exclusive(v_mctx_1181_);
if (v_isSharedCheck_1212_ == 0)
{
v___x_1200_ = v_mctx_1181_;
v_isShared_1201_ = v_isSharedCheck_1212_;
goto v_resetjp_1199_;
}
else
{
lean_inc(v_dAssignment_1198_);
lean_inc(v_eAssignment_1197_);
lean_inc(v_lAssignment_1196_);
lean_inc(v_userNames_1195_);
lean_inc(v_decls_1194_);
lean_inc(v_lDecls_1193_);
lean_inc(v_mvarCounter_1192_);
lean_inc(v_lmvarCounter_1191_);
lean_inc(v_levelAssignDepth_1190_);
lean_inc(v_depth_1189_);
lean_dec(v_mctx_1181_);
v___x_1200_ = lean_box(0);
v_isShared_1201_ = v_isSharedCheck_1212_;
goto v_resetjp_1199_;
}
v_resetjp_1199_:
{
lean_object* v___x_1202_; lean_object* v___x_1204_; 
v___x_1202_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3___redArg(v_eAssignment_1197_, v_mvarId_1176_, v_val_1177_);
if (v_isShared_1201_ == 0)
{
lean_ctor_set(v___x_1200_, 8, v___x_1202_);
v___x_1204_ = v___x_1200_;
goto v_reusejp_1203_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v_depth_1189_);
lean_ctor_set(v_reuseFailAlloc_1211_, 1, v_levelAssignDepth_1190_);
lean_ctor_set(v_reuseFailAlloc_1211_, 2, v_lmvarCounter_1191_);
lean_ctor_set(v_reuseFailAlloc_1211_, 3, v_mvarCounter_1192_);
lean_ctor_set(v_reuseFailAlloc_1211_, 4, v_lDecls_1193_);
lean_ctor_set(v_reuseFailAlloc_1211_, 5, v_decls_1194_);
lean_ctor_set(v_reuseFailAlloc_1211_, 6, v_userNames_1195_);
lean_ctor_set(v_reuseFailAlloc_1211_, 7, v_lAssignment_1196_);
lean_ctor_set(v_reuseFailAlloc_1211_, 8, v___x_1202_);
lean_ctor_set(v_reuseFailAlloc_1211_, 9, v_dAssignment_1198_);
v___x_1204_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1203_;
}
v_reusejp_1203_:
{
lean_object* v___x_1206_; 
if (v_isShared_1188_ == 0)
{
lean_ctor_set(v___x_1187_, 0, v___x_1204_);
v___x_1206_ = v___x_1187_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1210_; 
v_reuseFailAlloc_1210_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1210_, 0, v___x_1204_);
lean_ctor_set(v_reuseFailAlloc_1210_, 1, v_cache_1182_);
lean_ctor_set(v_reuseFailAlloc_1210_, 2, v_zetaDeltaFVarIds_1183_);
lean_ctor_set(v_reuseFailAlloc_1210_, 3, v_postponed_1184_);
lean_ctor_set(v_reuseFailAlloc_1210_, 4, v_diag_1185_);
v___x_1206_ = v_reuseFailAlloc_1210_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; 
v___x_1207_ = lean_st_ref_set(v___y_1178_, v___x_1206_);
v___x_1208_ = lean_box(0);
v___x_1209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1209_, 0, v___x_1208_);
return v___x_1209_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3___redArg___boxed(lean_object* v_mvarId_1214_, lean_object* v_val_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_){
_start:
{
lean_object* v_res_1218_; 
v_res_1218_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3___redArg(v_mvarId_1214_, v_val_1215_, v___y_1216_);
lean_dec(v___y_1216_);
return v_res_1218_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg___lam__0(lean_object* v_x1_1219_, lean_object* v_x2_1220_){
_start:
{
lean_object* v_fst_1221_; lean_object* v_fst_1222_; uint8_t v___x_1223_; 
v_fst_1221_ = lean_ctor_get(v_x1_1219_, 0);
v_fst_1222_ = lean_ctor_get(v_x2_1220_, 0);
v___x_1223_ = lean_nat_dec_lt(v_fst_1221_, v_fst_1222_);
return v___x_1223_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg___lam__0___boxed(lean_object* v_x1_1224_, lean_object* v_x2_1225_){
_start:
{
uint8_t v_res_1226_; lean_object* v_r_1227_; 
v_res_1226_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg___lam__0(v_x1_1224_, v_x2_1225_);
lean_dec_ref(v_x2_1225_);
lean_dec_ref(v_x1_1224_);
v_r_1227_ = lean_box(v_res_1226_);
return v_r_1227_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9_spec__13___redArg(lean_object* v_hi_1228_, lean_object* v_pivot_1229_, lean_object* v_as_1230_, lean_object* v_i_1231_, lean_object* v_k_1232_){
_start:
{
uint8_t v___x_1233_; 
v___x_1233_ = lean_nat_dec_lt(v_k_1232_, v_hi_1228_);
if (v___x_1233_ == 0)
{
lean_object* v___x_1234_; lean_object* v___x_1235_; 
lean_dec(v_k_1232_);
v___x_1234_ = lean_array_fswap(v_as_1230_, v_i_1231_, v_hi_1228_);
v___x_1235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1235_, 0, v_i_1231_);
lean_ctor_set(v___x_1235_, 1, v___x_1234_);
return v___x_1235_;
}
else
{
lean_object* v___x_1236_; lean_object* v_fst_1237_; lean_object* v_fst_1238_; uint8_t v___x_1239_; 
v___x_1236_ = lean_array_fget_borrowed(v_as_1230_, v_k_1232_);
v_fst_1237_ = lean_ctor_get(v___x_1236_, 0);
v_fst_1238_ = lean_ctor_get(v_pivot_1229_, 0);
v___x_1239_ = lean_nat_dec_lt(v_fst_1237_, v_fst_1238_);
if (v___x_1239_ == 0)
{
lean_object* v___x_1240_; lean_object* v___x_1241_; 
v___x_1240_ = lean_unsigned_to_nat(1u);
v___x_1241_ = lean_nat_add(v_k_1232_, v___x_1240_);
lean_dec(v_k_1232_);
v_k_1232_ = v___x_1241_;
goto _start;
}
else
{
lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; 
v___x_1243_ = lean_array_fswap(v_as_1230_, v_i_1231_, v_k_1232_);
v___x_1244_ = lean_unsigned_to_nat(1u);
v___x_1245_ = lean_nat_add(v_i_1231_, v___x_1244_);
lean_dec(v_i_1231_);
v___x_1246_ = lean_nat_add(v_k_1232_, v___x_1244_);
lean_dec(v_k_1232_);
v_as_1230_ = v___x_1243_;
v_i_1231_ = v___x_1245_;
v_k_1232_ = v___x_1246_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9_spec__13___redArg___boxed(lean_object* v_hi_1248_, lean_object* v_pivot_1249_, lean_object* v_as_1250_, lean_object* v_i_1251_, lean_object* v_k_1252_){
_start:
{
lean_object* v_res_1253_; 
v_res_1253_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9_spec__13___redArg(v_hi_1248_, v_pivot_1249_, v_as_1250_, v_i_1251_, v_k_1252_);
lean_dec_ref(v_pivot_1249_);
lean_dec(v_hi_1248_);
return v_res_1253_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg(lean_object* v_n_1254_, lean_object* v_as_1255_, lean_object* v_lo_1256_, lean_object* v_hi_1257_){
_start:
{
lean_object* v___y_1259_; uint8_t v___x_1269_; 
v___x_1269_ = lean_nat_dec_lt(v_lo_1256_, v_hi_1257_);
if (v___x_1269_ == 0)
{
lean_dec(v_lo_1256_);
return v_as_1255_;
}
else
{
lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v_mid_1272_; lean_object* v___y_1274_; lean_object* v___y_1280_; lean_object* v___x_1285_; lean_object* v___x_1286_; uint8_t v___x_1287_; 
v___x_1270_ = lean_nat_add(v_lo_1256_, v_hi_1257_);
v___x_1271_ = lean_unsigned_to_nat(1u);
v_mid_1272_ = lean_nat_shiftr(v___x_1270_, v___x_1271_);
lean_dec(v___x_1270_);
v___x_1285_ = lean_array_fget_borrowed(v_as_1255_, v_mid_1272_);
v___x_1286_ = lean_array_fget_borrowed(v_as_1255_, v_lo_1256_);
v___x_1287_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg___lam__0(v___x_1285_, v___x_1286_);
if (v___x_1287_ == 0)
{
v___y_1280_ = v_as_1255_;
goto v___jp_1279_;
}
else
{
lean_object* v___x_1288_; 
v___x_1288_ = lean_array_fswap(v_as_1255_, v_lo_1256_, v_mid_1272_);
v___y_1280_ = v___x_1288_;
goto v___jp_1279_;
}
v___jp_1273_:
{
lean_object* v___x_1275_; lean_object* v___x_1276_; uint8_t v___x_1277_; 
v___x_1275_ = lean_array_fget_borrowed(v___y_1274_, v_mid_1272_);
v___x_1276_ = lean_array_fget_borrowed(v___y_1274_, v_hi_1257_);
v___x_1277_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg___lam__0(v___x_1275_, v___x_1276_);
if (v___x_1277_ == 0)
{
lean_dec(v_mid_1272_);
v___y_1259_ = v___y_1274_;
goto v___jp_1258_;
}
else
{
lean_object* v___x_1278_; 
v___x_1278_ = lean_array_fswap(v___y_1274_, v_mid_1272_, v_hi_1257_);
lean_dec(v_mid_1272_);
v___y_1259_ = v___x_1278_;
goto v___jp_1258_;
}
}
v___jp_1279_:
{
lean_object* v___x_1281_; lean_object* v___x_1282_; uint8_t v___x_1283_; 
v___x_1281_ = lean_array_fget_borrowed(v___y_1280_, v_hi_1257_);
v___x_1282_ = lean_array_fget_borrowed(v___y_1280_, v_lo_1256_);
v___x_1283_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg___lam__0(v___x_1281_, v___x_1282_);
if (v___x_1283_ == 0)
{
v___y_1274_ = v___y_1280_;
goto v___jp_1273_;
}
else
{
lean_object* v___x_1284_; 
v___x_1284_ = lean_array_fswap(v___y_1280_, v_lo_1256_, v_hi_1257_);
v___y_1274_ = v___x_1284_;
goto v___jp_1273_;
}
}
}
v___jp_1258_:
{
lean_object* v_pivot_1260_; lean_object* v___x_1261_; lean_object* v_fst_1262_; lean_object* v_snd_1263_; uint8_t v___x_1264_; 
v_pivot_1260_ = lean_array_fget(v___y_1259_, v_hi_1257_);
lean_inc_n(v_lo_1256_, 2);
v___x_1261_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9_spec__13___redArg(v_hi_1257_, v_pivot_1260_, v___y_1259_, v_lo_1256_, v_lo_1256_);
lean_dec(v_pivot_1260_);
v_fst_1262_ = lean_ctor_get(v___x_1261_, 0);
lean_inc(v_fst_1262_);
v_snd_1263_ = lean_ctor_get(v___x_1261_, 1);
lean_inc(v_snd_1263_);
lean_dec_ref(v___x_1261_);
v___x_1264_ = lean_nat_dec_le(v_hi_1257_, v_fst_1262_);
if (v___x_1264_ == 0)
{
lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; 
v___x_1265_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg(v_n_1254_, v_snd_1263_, v_lo_1256_, v_fst_1262_);
v___x_1266_ = lean_unsigned_to_nat(1u);
v___x_1267_ = lean_nat_add(v_fst_1262_, v___x_1266_);
lean_dec(v_fst_1262_);
v_as_1255_ = v___x_1265_;
v_lo_1256_ = v___x_1267_;
goto _start;
}
else
{
lean_dec(v_fst_1262_);
lean_dec(v_lo_1256_);
return v_snd_1263_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg___boxed(lean_object* v_n_1289_, lean_object* v_as_1290_, lean_object* v_lo_1291_, lean_object* v_hi_1292_){
_start:
{
lean_object* v_res_1293_; 
v_res_1293_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg(v_n_1289_, v_as_1290_, v_lo_1291_, v_hi_1292_);
lean_dec(v_hi_1292_);
lean_dec(v_n_1289_);
return v_res_1293_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11_spec__13___redArg(lean_object* v_as_1294_, lean_object* v_a_1295_, lean_object* v_x_1296_){
_start:
{
lean_object* v_zero_1297_; uint8_t v_isZero_1298_; 
v_zero_1297_ = lean_unsigned_to_nat(0u);
v_isZero_1298_ = lean_nat_dec_eq(v_x_1296_, v_zero_1297_);
if (v_isZero_1298_ == 1)
{
lean_dec(v_x_1296_);
return v_isZero_1298_;
}
else
{
lean_object* v_fst_1299_; lean_object* v_one_1300_; lean_object* v_n_1301_; lean_object* v___x_1302_; lean_object* v_fst_1303_; uint8_t v___x_1304_; uint8_t v___x_1305_; 
v_fst_1299_ = lean_ctor_get(v_a_1295_, 0);
v_one_1300_ = lean_unsigned_to_nat(1u);
v_n_1301_ = lean_nat_sub(v_x_1296_, v_one_1300_);
lean_dec(v_x_1296_);
v___x_1302_ = lean_array_fget_borrowed(v_as_1294_, v_n_1301_);
v_fst_1303_ = lean_ctor_get(v___x_1302_, 0);
v___x_1304_ = lean_nat_dec_eq(v_fst_1299_, v_fst_1303_);
v___x_1305_ = lean_bool_not(v___x_1304_);
if (v___x_1305_ == 0)
{
lean_dec(v_n_1301_);
return v___x_1305_;
}
else
{
v_x_1296_ = v_n_1301_;
goto _start;
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
v___x_1512_ = lean_array_get_size(v___y_1503_);
v___x_1513_ = lean_nat_dec_eq(v___x_1512_, v___x_1499_);
if (v___x_1513_ == 0)
{
lean_object* v___x_1514_; uint8_t v___x_1515_; 
v___x_1514_ = lean_nat_sub(v___x_1512_, v___x_1500_);
v___x_1515_ = lean_nat_dec_le(v___x_1499_, v___x_1514_);
if (v___x_1515_ == 0)
{
lean_inc(v___x_1514_);
v___y_1484_ = v___y_1507_;
v___y_1485_ = v___y_1510_;
v___y_1486_ = v___x_1514_;
v___y_1487_ = v___y_1509_;
v___y_1488_ = v___y_1503_;
v___y_1489_ = v___y_1506_;
v___y_1490_ = v___y_1508_;
v___y_1491_ = v___y_1505_;
v___y_1492_ = v___x_1512_;
v___y_1493_ = v___y_1502_;
v___y_1494_ = v___y_1511_;
v___y_1495_ = v___y_1504_;
v___y_1496_ = v___x_1514_;
goto v___jp_1483_;
}
else
{
v___y_1484_ = v___y_1507_;
v___y_1485_ = v___y_1510_;
v___y_1486_ = v___x_1514_;
v___y_1487_ = v___y_1509_;
v___y_1488_ = v___y_1503_;
v___y_1489_ = v___y_1506_;
v___y_1490_ = v___y_1508_;
v___y_1491_ = v___y_1505_;
v___y_1492_ = v___x_1512_;
v___y_1493_ = v___y_1502_;
v___y_1494_ = v___y_1511_;
v___y_1495_ = v___y_1504_;
v___y_1496_ = v___x_1499_;
goto v___jp_1483_;
}
}
else
{
v___y_1455_ = v___y_1505_;
v___y_1456_ = v___y_1502_;
v___y_1457_ = v___y_1507_;
v___y_1458_ = v___y_1510_;
v___y_1459_ = v___y_1509_;
v___y_1460_ = v___y_1511_;
v___y_1461_ = v___y_1504_;
v___y_1462_ = v___y_1506_;
v___y_1463_ = v___y_1508_;
v___y_1464_ = v___y_1503_;
goto v___jp_1454_;
}
}
v___jp_1516_:
{
lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; 
v___x_1533_ = l_Lean_Meta_Simp_Context_setMemoize(v___y_1524_, v___y_1532_);
v___x_1534_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__6, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__6_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__6);
lean_inc(v___y_1520_);
lean_inc_ref(v___y_1525_);
v___x_1535_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre___boxed), 11, 2);
lean_closure_set(v___x_1535_, 0, v___y_1525_);
lean_closure_set(v___x_1535_, 1, v___y_1520_);
lean_inc_ref(v___y_1517_);
lean_inc_ref(v___y_1522_);
v___x_1536_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_1536_, 0, v___x_1535_);
lean_ctor_set(v___x_1536_, 1, v___y_1531_);
lean_ctor_set(v___x_1536_, 2, v___y_1522_);
lean_ctor_set(v___x_1536_, 3, v___f_1391_);
lean_ctor_set(v___x_1536_, 4, v___y_1517_);
lean_ctor_set_uint8(v___x_1536_, sizeof(void*)*5, v___x_1392_);
v___x_1537_ = l_Lean_Meta_Simp_main(v___y_1526_, v___x_1533_, v___x_1534_, v___x_1536_, v___y_1528_, v___y_1519_, v___y_1527_, v___y_1530_);
if (lean_obj_tag(v___x_1537_) == 0)
{
lean_object* v_a_1538_; lean_object* v_fst_1539_; lean_object* v___x_1541_; uint8_t v_isShared_1542_; uint8_t v_isSharedCheck_1614_; 
v_a_1538_ = lean_ctor_get(v___x_1537_, 0);
lean_inc(v_a_1538_);
lean_dec_ref_known(v___x_1537_, 1);
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
v___x_1543_ = lean_st_ref_get(v___y_1520_);
lean_dec(v___y_1520_);
if (lean_obj_tag(v___x_1543_) == 0)
{
lean_object* v_subgoals_1544_; lean_object* v___x_1545_; uint8_t v___x_1546_; 
v_subgoals_1544_ = lean_ctor_get(v___x_1543_, 0);
lean_inc_ref(v_subgoals_1544_);
lean_dec_ref_known(v___x_1543_, 1);
v___x_1545_ = lean_array_get_size(v_subgoals_1544_);
v___x_1546_ = lean_nat_dec_eq(v___x_1545_, v___x_1499_);
if (v___x_1546_ == 0)
{
lean_del_object(v___x_1541_);
lean_dec_ref(v___y_1525_);
v___y_1408_ = v_fst_1539_;
v_subgoals_1409_ = v_subgoals_1544_;
v___y_1410_ = v___y_1529_;
v___y_1411_ = v___y_1518_;
v___y_1412_ = v___y_1521_;
v___y_1413_ = v___y_1523_;
v___y_1414_ = v___y_1528_;
v___y_1415_ = v___y_1519_;
v___y_1416_ = v___y_1527_;
v___y_1417_ = v___y_1530_;
goto v___jp_1407_;
}
else
{
lean_object* v_expr_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1551_; 
lean_dec_ref(v_subgoals_1544_);
lean_dec(v_fst_1539_);
v_expr_1547_ = lean_ctor_get(v___y_1525_, 2);
lean_inc_ref(v_expr_1547_);
lean_dec_ref(v___y_1525_);
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
v___x_1552_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg(v___x_1551_, v___y_1528_, v___y_1519_, v___y_1527_, v___y_1530_);
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
lean_dec_ref_known(v___x_1543_, 3);
v___x_1565_ = lean_nat_dec_eq(v_idx_1563_, v___x_1499_);
if (v___x_1565_ == 0)
{
lean_object* v___x_1566_; 
lean_dec_ref(v___y_1525_);
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
v___x_1592_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg(v___x_1591_, v___y_1528_, v___y_1519_, v___y_1527_, v___y_1530_);
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
v___y_1502_ = v_fst_1539_;
v___y_1503_ = v_subgoals_1562_;
v___y_1504_ = v___y_1529_;
v___y_1505_ = v___y_1518_;
v___y_1506_ = v___y_1521_;
v___y_1507_ = v___y_1523_;
v___y_1508_ = v___y_1528_;
v___y_1509_ = v___y_1519_;
v___y_1510_ = v___y_1527_;
v___y_1511_ = v___y_1530_;
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
v_expr_1599_ = lean_ctor_get(v___y_1525_, 2);
lean_inc_ref(v_expr_1599_);
lean_dec_ref(v___y_1525_);
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
v___x_1604_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg(v___x_1603_, v___y_1528_, v___y_1519_, v___y_1527_, v___y_1530_);
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
lean_dec_ref(v___y_1525_);
lean_dec(v___y_1520_);
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
lean_dec_ref_known(v_occs_1630_, 1);
v_a_1641_ = lean_ctor_get(v___x_1640_, 0);
lean_inc(v_a_1641_);
lean_dec_ref_known(v___x_1640_, 1);
v___y_1517_ = v___y_1625_;
v___y_1518_ = v___y_1632_;
v___y_1519_ = v___y_1636_;
v___y_1520_ = v___x_1639_;
v___y_1521_ = v___y_1633_;
v___y_1522_ = v___y_1627_;
v___y_1523_ = v___y_1634_;
v___y_1524_ = v_a_1641_;
v___y_1525_ = v___y_1628_;
v___y_1526_ = v___y_1626_;
v___y_1527_ = v___y_1637_;
v___y_1528_ = v___y_1635_;
v___y_1529_ = v___y_1631_;
v___y_1530_ = v___y_1638_;
v___y_1531_ = v___y_1629_;
v___y_1532_ = v___x_1392_;
goto v___jp_1516_;
}
else
{
lean_object* v_a_1642_; uint8_t v___x_1643_; 
lean_dec_ref(v_occs_1630_);
v_a_1642_ = lean_ctor_get(v___x_1640_, 0);
lean_inc(v_a_1642_);
lean_dec_ref_known(v___x_1640_, 1);
v___x_1643_ = 0;
v___y_1517_ = v___y_1625_;
v___y_1518_ = v___y_1632_;
v___y_1519_ = v___y_1636_;
v___y_1520_ = v___x_1639_;
v___y_1521_ = v___y_1633_;
v___y_1522_ = v___y_1627_;
v___y_1523_ = v___y_1634_;
v___y_1524_ = v_a_1642_;
v___y_1525_ = v___y_1628_;
v___y_1526_ = v___y_1626_;
v___y_1527_ = v___y_1637_;
v___y_1528_ = v___y_1635_;
v___y_1529_ = v___y_1631_;
v___y_1530_ = v___y_1638_;
v___y_1531_ = v___y_1629_;
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
v___x_1668_ = lean_array_to_list(v___y_1655_);
v___x_1669_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1669_, 0, v___x_1667_);
lean_ctor_set(v___x_1669_, 1, v___x_1499_);
lean_ctor_set(v___x_1669_, 2, v___x_1668_);
v___y_1625_ = v___y_1653_;
v___y_1626_ = v___y_1654_;
v___y_1627_ = v___y_1656_;
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
lean_dec_ref(v___y_1683_);
lean_dec_ref(v___y_1680_);
lean_dec_ref(v___y_1678_);
lean_dec_ref(v___f_1391_);
v___x_1686_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__17, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__17_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__17);
v___x_1687_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg(v___x_1686_, v___y_1674_, v___y_1677_, v___y_1679_, v___y_1681_);
return v___x_1687_;
}
else
{
v___y_1653_ = v___y_1671_;
v___y_1654_ = v___y_1680_;
v___y_1655_ = v___y_1684_;
v___y_1656_ = v___y_1676_;
v___y_1657_ = v___y_1678_;
v___y_1658_ = v___y_1683_;
v___y_1659_ = v___y_1682_;
v___y_1660_ = v___y_1672_;
v___y_1661_ = v___y_1673_;
v___y_1662_ = v___y_1675_;
v___y_1663_ = v___y_1674_;
v___y_1664_ = v___y_1677_;
v___y_1665_ = v___y_1679_;
v___y_1666_ = v___y_1681_;
goto v___jp_1652_;
}
}
v___jp_1688_:
{
lean_object* v___x_1706_; 
v___x_1706_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg(v___y_1694_, v___y_1693_, v___y_1704_, v___y_1705_);
lean_dec(v___y_1705_);
lean_dec(v___y_1694_);
v___y_1671_ = v___y_1689_;
v___y_1672_ = v___y_1690_;
v___y_1673_ = v___y_1691_;
v___y_1674_ = v___y_1692_;
v___y_1675_ = v___y_1695_;
v___y_1676_ = v___y_1696_;
v___y_1677_ = v___y_1697_;
v___y_1678_ = v___y_1698_;
v___y_1679_ = v___y_1699_;
v___y_1680_ = v___y_1700_;
v___y_1681_ = v___y_1701_;
v___y_1682_ = v___y_1702_;
v___y_1683_ = v___y_1703_;
v___y_1684_ = v___x_1706_;
goto v___jp_1670_;
}
v___jp_1707_:
{
uint8_t v___x_1725_; 
v___x_1725_ = lean_nat_dec_le(v___y_1724_, v___y_1716_);
if (v___x_1725_ == 0)
{
lean_dec(v___y_1716_);
lean_inc(v___y_1724_);
v___y_1689_ = v___y_1708_;
v___y_1690_ = v___y_1709_;
v___y_1691_ = v___y_1710_;
v___y_1692_ = v___y_1711_;
v___y_1693_ = v___y_1712_;
v___y_1694_ = v___y_1713_;
v___y_1695_ = v___y_1714_;
v___y_1696_ = v___y_1715_;
v___y_1697_ = v___y_1717_;
v___y_1698_ = v___y_1718_;
v___y_1699_ = v___y_1719_;
v___y_1700_ = v___y_1720_;
v___y_1701_ = v___y_1721_;
v___y_1702_ = v___y_1722_;
v___y_1703_ = v___y_1723_;
v___y_1704_ = v___y_1724_;
v___y_1705_ = v___y_1724_;
goto v___jp_1688_;
}
else
{
v___y_1689_ = v___y_1708_;
v___y_1690_ = v___y_1709_;
v___y_1691_ = v___y_1710_;
v___y_1692_ = v___y_1711_;
v___y_1693_ = v___y_1712_;
v___y_1694_ = v___y_1713_;
v___y_1695_ = v___y_1714_;
v___y_1696_ = v___y_1715_;
v___y_1697_ = v___y_1717_;
v___y_1698_ = v___y_1718_;
v___y_1699_ = v___y_1719_;
v___y_1700_ = v___y_1720_;
v___y_1701_ = v___y_1721_;
v___y_1702_ = v___y_1722_;
v___y_1703_ = v___y_1723_;
v___y_1704_ = v___y_1724_;
v___y_1705_ = v___y_1716_;
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
lean_dec_ref_known(v___x_1760_, 8);
if (lean_obj_tag(v___x_1761_) == 0)
{
lean_object* v_a_1762_; lean_object* v___x_1763_; 
v_a_1762_ = lean_ctor_get(v___x_1761_, 0);
lean_inc(v_a_1762_);
lean_dec_ref_known(v___x_1761_, 1);
v___x_1763_ = l_Lean_Elab_Tactic_Conv_getLhs___redArg(v___y_1729_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_);
if (lean_obj_tag(v___x_1763_) == 0)
{
lean_object* v_a_1764_; lean_object* v___x_1765_; lean_object* v___f_1766_; lean_object* v___f_1767_; lean_object* v___f_1768_; 
v_a_1764_ = lean_ctor_get(v___x_1763_, 0);
lean_inc(v_a_1764_);
lean_dec_ref_known(v___x_1763_, 1);
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
v___y_1625_ = v___f_1768_;
v___y_1626_ = v_a_1764_;
v___y_1627_ = v___f_1767_;
v___y_1628_ = v_a_1762_;
v___y_1629_ = v___f_1766_;
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
lean_dec_ref_known(v_occs_1727_, 1);
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
lean_object* v___x_1786_; lean_object* v___x_1787_; size_t v_sz_1788_; size_t v___x_1789_; lean_object* v___x_1790_; 
v___x_1786_ = l_Lean_Syntax_getArg(v_val_1770_, v___x_1499_);
lean_dec(v_val_1770_);
v___x_1787_ = l_Lean_Syntax_getArgs(v___x_1786_);
lean_dec(v___x_1786_);
v_sz_1788_ = lean_array_size(v___x_1787_);
v___x_1789_ = ((size_t)0ULL);
v___x_1790_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg(v_sz_1788_, v___x_1789_, v___x_1787_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_);
if (lean_obj_tag(v___x_1790_) == 0)
{
lean_object* v_a_1791_; lean_object* v___x_1792_; uint8_t v___x_1793_; 
v_a_1791_ = lean_ctor_get(v___x_1790_, 0);
lean_inc(v_a_1791_);
lean_dec_ref_known(v___x_1790_, 1);
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
v___y_1708_ = v___f_1768_;
v___y_1709_ = v___y_1729_;
v___y_1710_ = v___y_1730_;
v___y_1711_ = v___y_1732_;
v___y_1712_ = v_a_1791_;
v___y_1713_ = v___x_1792_;
v___y_1714_ = v___y_1731_;
v___y_1715_ = v___f_1767_;
v___y_1716_ = v___x_1794_;
v___y_1717_ = v___y_1733_;
v___y_1718_ = v_a_1762_;
v___y_1719_ = v___y_1734_;
v___y_1720_ = v_a_1764_;
v___y_1721_ = v___y_1735_;
v___y_1722_ = v___y_1728_;
v___y_1723_ = v___f_1766_;
v___y_1724_ = v___x_1794_;
goto v___jp_1707_;
}
else
{
v___y_1708_ = v___f_1768_;
v___y_1709_ = v___y_1729_;
v___y_1710_ = v___y_1730_;
v___y_1711_ = v___y_1732_;
v___y_1712_ = v_a_1791_;
v___y_1713_ = v___x_1792_;
v___y_1714_ = v___y_1731_;
v___y_1715_ = v___f_1767_;
v___y_1716_ = v___x_1794_;
v___y_1717_ = v___y_1733_;
v___y_1718_ = v_a_1762_;
v___y_1719_ = v___y_1734_;
v___y_1720_ = v_a_1764_;
v___y_1721_ = v___y_1735_;
v___y_1722_ = v___y_1728_;
v___y_1723_ = v___f_1766_;
v___y_1724_ = v___x_1499_;
goto v___jp_1707_;
}
}
else
{
v___y_1671_ = v___f_1768_;
v___y_1672_ = v___y_1729_;
v___y_1673_ = v___y_1730_;
v___y_1674_ = v___y_1732_;
v___y_1675_ = v___y_1731_;
v___y_1676_ = v___f_1767_;
v___y_1677_ = v___y_1733_;
v___y_1678_ = v_a_1762_;
v___y_1679_ = v___y_1734_;
v___y_1680_ = v_a_1764_;
v___y_1681_ = v___y_1735_;
v___y_1682_ = v___y_1728_;
v___y_1683_ = v___f_1766_;
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
v___y_1625_ = v___f_1768_;
v___y_1626_ = v_a_1764_;
v___y_1627_ = v___f_1767_;
v___y_1628_ = v_a_1762_;
v___y_1629_ = v___f_1766_;
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
lean_dec_ref_known(v___x_1418_, 1);
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
lean_dec_ref_known(v___x_1423_, 1);
v___x_1425_ = l_Lean_Meta_Simp_Result_getProof(v___y_1408_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_);
if (lean_obj_tag(v___x_1425_) == 0)
{
lean_object* v_a_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; 
v_a_1426_ = lean_ctor_get(v___x_1425_, 0);
lean_inc(v_a_1426_);
lean_dec_ref_known(v___x_1425_, 1);
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
v___y_1410_ = v___y_1461_;
v___y_1411_ = v___y_1455_;
v___y_1412_ = v___y_1462_;
v___y_1413_ = v___y_1457_;
v___y_1414_ = v___y_1463_;
v___y_1415_ = v___y_1459_;
v___y_1416_ = v___y_1458_;
v___y_1417_ = v___y_1460_;
goto v___jp_1407_;
}
v___jp_1468_:
{
lean_object* v___x_1482_; 
v___x_1482_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg(v___y_1476_, v___y_1472_, v___y_1478_, v___y_1481_);
lean_dec(v___y_1481_);
lean_dec(v___y_1476_);
v___y_1455_ = v___y_1475_;
v___y_1456_ = v___y_1477_;
v___y_1457_ = v___y_1469_;
v___y_1458_ = v___y_1470_;
v___y_1459_ = v___y_1471_;
v___y_1460_ = v___y_1479_;
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
v___y_1475_ = v___y_1491_;
v___y_1476_ = v___y_1492_;
v___y_1477_ = v___y_1493_;
v___y_1478_ = v___y_1496_;
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
v___y_1475_ = v___y_1491_;
v___y_1476_ = v___y_1492_;
v___y_1477_ = v___y_1493_;
v___y_1478_ = v___y_1496_;
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
uint8_t v___x_19448__boxed_1851_; uint8_t v___x_19450__boxed_1852_; lean_object* v_res_1853_; 
v___x_19448__boxed_1851_ = lean_unbox(v___x_1834_);
v___x_19450__boxed_1852_ = lean_unbox(v___x_1836_);
v_res_1853_ = l_Lean_Elab_Tactic_Conv_evalPattern___lam__6(v___x_19448__boxed_1851_, v___f_1835_, v___x_19450__boxed_1852_, v_stx_1837_, v___x_1838_, v___x_1839_, v___x_1840_, v___x_1841_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7(lean_object* v_as_1989_, size_t v_sz_1990_, size_t v_i_1991_, lean_object* v_bs_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_){
_start:
{
lean_object* v___x_2002_; 
v___x_2002_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg(v_sz_1990_, v_i_1991_, v_bs_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_, v___y_2000_);
return v___x_2002_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___boxed(lean_object* v_as_2003_, lean_object* v_sz_2004_, lean_object* v_i_2005_, lean_object* v_bs_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_){
_start:
{
size_t v_sz_boxed_2016_; size_t v_i_boxed_2017_; lean_object* v_res_2018_; 
v_sz_boxed_2016_ = lean_unbox_usize(v_sz_2004_);
lean_dec(v_sz_2004_);
v_i_boxed_2017_ = lean_unbox_usize(v_i_2005_);
lean_dec(v_i_2005_);
v_res_2018_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7(v_as_2003_, v_sz_boxed_2016_, v_i_boxed_2017_, v_bs_2006_, v___y_2007_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_, v___y_2012_, v___y_2013_, v___y_2014_);
lean_dec(v___y_2014_);
lean_dec_ref(v___y_2013_);
lean_dec(v___y_2012_);
lean_dec_ref(v___y_2011_);
lean_dec(v___y_2010_);
lean_dec_ref(v___y_2009_);
lean_dec(v___y_2008_);
lean_dec_ref(v___y_2007_);
lean_dec_ref(v_as_2003_);
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
size_t v_x_20564__boxed_2101_; size_t v_x_20565__boxed_2102_; lean_object* v_res_2103_; 
v_x_20564__boxed_2101_ = lean_unbox_usize(v_x_2097_);
lean_dec(v_x_2097_);
v_x_20565__boxed_2102_ = lean_unbox_usize(v_x_2098_);
lean_dec(v_x_2098_);
v_res_2103_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4(v_00_u03b2_2095_, v_x_2096_, v_x_20564__boxed_2101_, v_x_20565__boxed_2102_, v_x_2099_, v_x_2100_);
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
