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
uint8_t v___x_18429__boxed_667_; lean_object* v_res_668_; 
v___x_18429__boxed_667_ = lean_unbox(v___x_659_);
v_res_668_ = l_Lean_Elab_Tactic_Conv_evalPattern___lam__1(v___x_657_, v___x_658_, v___x_18429__boxed_667_, v___y_660_, v___y_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_);
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
uint8_t v___x_18523__boxed_738_; lean_object* v_res_739_; 
v___x_18523__boxed_738_ = lean_unbox(v___x_728_);
v_res_739_ = l_Lean_Elab_Tactic_Conv_evalPattern___lam__3(v___x_727_, v___x_18523__boxed_738_, v_e_729_, v___y_730_, v___y_731_, v___y_732_, v___y_733_, v___y_734_, v___y_735_, v___y_736_);
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4_spec__5(lean_object* v_msgData_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_){
_start:
{
lean_object* v___x_809_; lean_object* v_env_810_; lean_object* v___x_811_; lean_object* v_mctx_812_; lean_object* v_lctx_813_; lean_object* v_options_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; 
v___x_809_ = lean_st_ref_get(v___y_807_);
v_env_810_ = lean_ctor_get(v___x_809_, 0);
lean_inc_ref(v_env_810_);
lean_dec(v___x_809_);
v___x_811_ = lean_st_ref_get(v___y_805_);
v_mctx_812_ = lean_ctor_get(v___x_811_, 0);
lean_inc_ref(v_mctx_812_);
lean_dec(v___x_811_);
v_lctx_813_ = lean_ctor_get(v___y_804_, 2);
v_options_814_ = lean_ctor_get(v___y_806_, 2);
lean_inc_ref(v_options_814_);
lean_inc_ref(v_lctx_813_);
v___x_815_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_815_, 0, v_env_810_);
lean_ctor_set(v___x_815_, 1, v_mctx_812_);
lean_ctor_set(v___x_815_, 2, v_lctx_813_);
lean_ctor_set(v___x_815_, 3, v_options_814_);
v___x_816_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_816_, 0, v___x_815_);
lean_ctor_set(v___x_816_, 1, v_msgData_803_);
v___x_817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_817_, 0, v___x_816_);
return v___x_817_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4_spec__5___boxed(lean_object* v_msgData_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_){
_start:
{
lean_object* v_res_824_; 
v_res_824_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4_spec__5(v_msgData_818_, v___y_819_, v___y_820_, v___y_821_, v___y_822_);
lean_dec(v___y_822_);
lean_dec_ref(v___y_821_);
lean_dec(v___y_820_);
lean_dec_ref(v___y_819_);
return v_res_824_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg(lean_object* v_msg_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_){
_start:
{
lean_object* v_ref_831_; lean_object* v___x_832_; lean_object* v_a_833_; lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_841_; 
v_ref_831_ = lean_ctor_get(v___y_828_, 5);
v___x_832_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4_spec__5(v_msg_825_, v___y_826_, v___y_827_, v___y_828_, v___y_829_);
v_a_833_ = lean_ctor_get(v___x_832_, 0);
v_isSharedCheck_841_ = !lean_is_exclusive(v___x_832_);
if (v_isSharedCheck_841_ == 0)
{
v___x_835_ = v___x_832_;
v_isShared_836_ = v_isSharedCheck_841_;
goto v_resetjp_834_;
}
else
{
lean_inc(v_a_833_);
lean_dec(v___x_832_);
v___x_835_ = lean_box(0);
v_isShared_836_ = v_isSharedCheck_841_;
goto v_resetjp_834_;
}
v_resetjp_834_:
{
lean_object* v___x_837_; lean_object* v___x_839_; 
lean_inc(v_ref_831_);
v___x_837_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_837_, 0, v_ref_831_);
lean_ctor_set(v___x_837_, 1, v_a_833_);
if (v_isShared_836_ == 0)
{
lean_ctor_set_tag(v___x_835_, 1);
lean_ctor_set(v___x_835_, 0, v___x_837_);
v___x_839_ = v___x_835_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v___x_837_);
v___x_839_ = v_reuseFailAlloc_840_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
return v___x_839_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg___boxed(lean_object* v_msg_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_){
_start:
{
lean_object* v_res_848_; 
v_res_848_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg(v_msg_842_, v___y_843_, v___y_844_, v___y_845_, v___y_846_);
lean_dec(v___y_846_);
lean_dec_ref(v___y_845_);
lean_dec(v___y_844_);
lean_dec_ref(v___y_843_);
return v_res_848_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1___redArg(lean_object* v_ref_849_, lean_object* v_msg_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_){
_start:
{
lean_object* v_fileName_860_; lean_object* v_fileMap_861_; lean_object* v_options_862_; lean_object* v_currRecDepth_863_; lean_object* v_maxRecDepth_864_; lean_object* v_ref_865_; lean_object* v_currNamespace_866_; lean_object* v_openDecls_867_; lean_object* v_initHeartbeats_868_; lean_object* v_maxHeartbeats_869_; lean_object* v_quotContext_870_; lean_object* v_currMacroScope_871_; uint8_t v_diag_872_; lean_object* v_cancelTk_x3f_873_; uint8_t v_suppressElabErrors_874_; lean_object* v_inheritedTraceOptions_875_; lean_object* v_ref_876_; lean_object* v___x_877_; lean_object* v___x_878_; 
v_fileName_860_ = lean_ctor_get(v___y_857_, 0);
v_fileMap_861_ = lean_ctor_get(v___y_857_, 1);
v_options_862_ = lean_ctor_get(v___y_857_, 2);
v_currRecDepth_863_ = lean_ctor_get(v___y_857_, 3);
v_maxRecDepth_864_ = lean_ctor_get(v___y_857_, 4);
v_ref_865_ = lean_ctor_get(v___y_857_, 5);
v_currNamespace_866_ = lean_ctor_get(v___y_857_, 6);
v_openDecls_867_ = lean_ctor_get(v___y_857_, 7);
v_initHeartbeats_868_ = lean_ctor_get(v___y_857_, 8);
v_maxHeartbeats_869_ = lean_ctor_get(v___y_857_, 9);
v_quotContext_870_ = lean_ctor_get(v___y_857_, 10);
v_currMacroScope_871_ = lean_ctor_get(v___y_857_, 11);
v_diag_872_ = lean_ctor_get_uint8(v___y_857_, sizeof(void*)*14);
v_cancelTk_x3f_873_ = lean_ctor_get(v___y_857_, 12);
v_suppressElabErrors_874_ = lean_ctor_get_uint8(v___y_857_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_875_ = lean_ctor_get(v___y_857_, 13);
v_ref_876_ = l_Lean_replaceRef(v_ref_849_, v_ref_865_);
lean_inc_ref(v_inheritedTraceOptions_875_);
lean_inc(v_cancelTk_x3f_873_);
lean_inc(v_currMacroScope_871_);
lean_inc(v_quotContext_870_);
lean_inc(v_maxHeartbeats_869_);
lean_inc(v_initHeartbeats_868_);
lean_inc(v_openDecls_867_);
lean_inc(v_currNamespace_866_);
lean_inc(v_maxRecDepth_864_);
lean_inc(v_currRecDepth_863_);
lean_inc_ref(v_options_862_);
lean_inc_ref(v_fileMap_861_);
lean_inc_ref(v_fileName_860_);
v___x_877_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_877_, 0, v_fileName_860_);
lean_ctor_set(v___x_877_, 1, v_fileMap_861_);
lean_ctor_set(v___x_877_, 2, v_options_862_);
lean_ctor_set(v___x_877_, 3, v_currRecDepth_863_);
lean_ctor_set(v___x_877_, 4, v_maxRecDepth_864_);
lean_ctor_set(v___x_877_, 5, v_ref_876_);
lean_ctor_set(v___x_877_, 6, v_currNamespace_866_);
lean_ctor_set(v___x_877_, 7, v_openDecls_867_);
lean_ctor_set(v___x_877_, 8, v_initHeartbeats_868_);
lean_ctor_set(v___x_877_, 9, v_maxHeartbeats_869_);
lean_ctor_set(v___x_877_, 10, v_quotContext_870_);
lean_ctor_set(v___x_877_, 11, v_currMacroScope_871_);
lean_ctor_set(v___x_877_, 12, v_cancelTk_x3f_873_);
lean_ctor_set(v___x_877_, 13, v_inheritedTraceOptions_875_);
lean_ctor_set_uint8(v___x_877_, sizeof(void*)*14, v_diag_872_);
lean_ctor_set_uint8(v___x_877_, sizeof(void*)*14 + 1, v_suppressElabErrors_874_);
v___x_878_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg(v_msg_850_, v___y_855_, v___y_856_, v___x_877_, v___y_858_);
lean_dec_ref_known(v___x_877_, 14);
return v___x_878_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1___redArg___boxed(lean_object* v_ref_879_, lean_object* v_msg_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_){
_start:
{
lean_object* v_res_890_; 
v_res_890_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1___redArg(v_ref_879_, v_msg_880_, v___y_881_, v___y_882_, v___y_883_, v___y_884_, v___y_885_, v___y_886_, v___y_887_, v___y_888_);
lean_dec(v___y_888_);
lean_dec_ref(v___y_887_);
lean_dec(v___y_886_);
lean_dec_ref(v___y_885_);
lean_dec(v___y_884_);
lean_dec_ref(v___y_883_);
lean_dec(v___y_882_);
lean_dec_ref(v___y_881_);
lean_dec(v_ref_879_);
return v_res_890_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_892_; lean_object* v___x_893_; 
v___x_892_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg___closed__0));
v___x_893_ = l_Lean_stringToMessageData(v___x_892_);
return v___x_893_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg(size_t v_sz_894_, size_t v_i_895_, lean_object* v_bs_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_){
_start:
{
uint8_t v___x_906_; 
v___x_906_ = lean_usize_dec_lt(v_i_895_, v_sz_894_);
if (v___x_906_ == 0)
{
lean_object* v___x_907_; 
v___x_907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_907_, 0, v_bs_896_);
return v___x_907_;
}
else
{
lean_object* v_v_908_; lean_object* v___x_909_; lean_object* v_bs_x27_910_; lean_object* v_a_912_; lean_object* v___x_917_; uint8_t v_isZero_918_; 
v_v_908_ = lean_array_uget(v_bs_896_, v_i_895_);
v___x_909_ = lean_unsigned_to_nat(0u);
v_bs_x27_910_ = lean_array_uset(v_bs_896_, v_i_895_, v___x_909_);
v___x_917_ = l_Lean_TSyntax_getNat(v_v_908_);
v_isZero_918_ = lean_nat_dec_eq(v___x_917_, v___x_909_);
if (v_isZero_918_ == 1)
{
lean_object* v___x_919_; lean_object* v___x_920_; 
lean_dec(v___x_917_);
v___x_919_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg___closed__1);
v___x_920_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1___redArg(v_v_908_, v___x_919_, v___y_897_, v___y_898_, v___y_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_);
lean_dec(v_v_908_);
if (lean_obj_tag(v___x_920_) == 0)
{
lean_object* v_a_921_; 
v_a_921_ = lean_ctor_get(v___x_920_, 0);
lean_inc(v_a_921_);
lean_dec_ref_known(v___x_920_, 1);
v_a_912_ = v_a_921_;
goto v___jp_911_;
}
else
{
lean_object* v_a_922_; lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_929_; 
lean_dec_ref(v_bs_x27_910_);
v_a_922_ = lean_ctor_get(v___x_920_, 0);
v_isSharedCheck_929_ = !lean_is_exclusive(v___x_920_);
if (v_isSharedCheck_929_ == 0)
{
v___x_924_ = v___x_920_;
v_isShared_925_ = v_isSharedCheck_929_;
goto v_resetjp_923_;
}
else
{
lean_inc(v_a_922_);
lean_dec(v___x_920_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_929_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
lean_object* v___x_927_; 
if (v_isShared_925_ == 0)
{
v___x_927_ = v___x_924_;
goto v_reusejp_926_;
}
else
{
lean_object* v_reuseFailAlloc_928_; 
v_reuseFailAlloc_928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_928_, 0, v_a_922_);
v___x_927_ = v_reuseFailAlloc_928_;
goto v_reusejp_926_;
}
v_reusejp_926_:
{
return v___x_927_;
}
}
}
}
else
{
lean_object* v___x_930_; lean_object* v_one_931_; lean_object* v_n_932_; lean_object* v___x_933_; 
lean_dec(v_v_908_);
v___x_930_ = lean_usize_to_nat(v_i_895_);
v_one_931_ = lean_unsigned_to_nat(1u);
v_n_932_ = lean_nat_sub(v___x_917_, v_one_931_);
lean_dec(v___x_917_);
v___x_933_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_933_, 0, v_n_932_);
lean_ctor_set(v___x_933_, 1, v___x_930_);
v_a_912_ = v___x_933_;
goto v___jp_911_;
}
v___jp_911_:
{
size_t v___x_913_; size_t v___x_914_; lean_object* v___x_915_; 
v___x_913_ = ((size_t)1ULL);
v___x_914_ = lean_usize_add(v_i_895_, v___x_913_);
v___x_915_ = lean_array_uset(v_bs_x27_910_, v_i_895_, v_a_912_);
v_i_895_ = v___x_914_;
v_bs_896_ = v___x_915_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg___boxed(lean_object* v_sz_934_, lean_object* v_i_935_, lean_object* v_bs_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_){
_start:
{
size_t v_sz_boxed_946_; size_t v_i_boxed_947_; lean_object* v_res_948_; 
v_sz_boxed_946_ = lean_unbox_usize(v_sz_934_);
lean_dec(v_sz_934_);
v_i_boxed_947_ = lean_unbox_usize(v_i_935_);
lean_dec(v_i_935_);
v_res_948_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg(v_sz_boxed_946_, v_i_boxed_947_, v_bs_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_);
lean_dec(v___y_944_);
lean_dec_ref(v___y_943_);
lean_dec(v___y_942_);
lean_dec_ref(v___y_941_);
lean_dec(v___y_940_);
lean_dec_ref(v___y_939_);
lean_dec(v___y_938_);
lean_dec_ref(v___y_937_);
return v_res_948_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6_spec__8___redArg(lean_object* v_hi_949_, lean_object* v_pivot_950_, lean_object* v_as_951_, lean_object* v_i_952_, lean_object* v_k_953_){
_start:
{
uint8_t v___x_954_; 
v___x_954_ = lean_nat_dec_lt(v_k_953_, v_hi_949_);
if (v___x_954_ == 0)
{
lean_object* v___x_955_; lean_object* v___x_956_; 
lean_dec(v_k_953_);
v___x_955_ = lean_array_fswap(v_as_951_, v_i_952_, v_hi_949_);
v___x_956_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_956_, 0, v_i_952_);
lean_ctor_set(v___x_956_, 1, v___x_955_);
return v___x_956_;
}
else
{
lean_object* v___x_957_; lean_object* v_fst_958_; lean_object* v_fst_959_; uint8_t v___x_960_; 
v___x_957_ = lean_array_fget_borrowed(v_as_951_, v_k_953_);
v_fst_958_ = lean_ctor_get(v___x_957_, 0);
v_fst_959_ = lean_ctor_get(v_pivot_950_, 0);
v___x_960_ = lean_nat_dec_lt(v_fst_958_, v_fst_959_);
if (v___x_960_ == 0)
{
lean_object* v___x_961_; lean_object* v___x_962_; 
v___x_961_ = lean_unsigned_to_nat(1u);
v___x_962_ = lean_nat_add(v_k_953_, v___x_961_);
lean_dec(v_k_953_);
v_k_953_ = v___x_962_;
goto _start;
}
else
{
lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; 
v___x_964_ = lean_array_fswap(v_as_951_, v_i_952_, v_k_953_);
v___x_965_ = lean_unsigned_to_nat(1u);
v___x_966_ = lean_nat_add(v_i_952_, v___x_965_);
lean_dec(v_i_952_);
v___x_967_ = lean_nat_add(v_k_953_, v___x_965_);
lean_dec(v_k_953_);
v_as_951_ = v___x_964_;
v_i_952_ = v___x_966_;
v_k_953_ = v___x_967_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6_spec__8___redArg___boxed(lean_object* v_hi_969_, lean_object* v_pivot_970_, lean_object* v_as_971_, lean_object* v_i_972_, lean_object* v_k_973_){
_start:
{
lean_object* v_res_974_; 
v_res_974_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6_spec__8___redArg(v_hi_969_, v_pivot_970_, v_as_971_, v_i_972_, v_k_973_);
lean_dec_ref(v_pivot_970_);
lean_dec(v_hi_969_);
return v_res_974_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg___lam__0(lean_object* v_x1_975_, lean_object* v_x2_976_){
_start:
{
lean_object* v_fst_977_; lean_object* v_fst_978_; uint8_t v___x_979_; 
v_fst_977_ = lean_ctor_get(v_x1_975_, 0);
v_fst_978_ = lean_ctor_get(v_x2_976_, 0);
v___x_979_ = lean_nat_dec_lt(v_fst_977_, v_fst_978_);
return v___x_979_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg___lam__0___boxed(lean_object* v_x1_980_, lean_object* v_x2_981_){
_start:
{
uint8_t v_res_982_; lean_object* v_r_983_; 
v_res_982_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg___lam__0(v_x1_980_, v_x2_981_);
lean_dec_ref(v_x2_981_);
lean_dec_ref(v_x1_980_);
v_r_983_ = lean_box(v_res_982_);
return v_r_983_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg(lean_object* v_n_984_, lean_object* v_as_985_, lean_object* v_lo_986_, lean_object* v_hi_987_){
_start:
{
lean_object* v___y_989_; uint8_t v___x_999_; 
v___x_999_ = lean_nat_dec_lt(v_lo_986_, v_hi_987_);
if (v___x_999_ == 0)
{
lean_dec(v_lo_986_);
return v_as_985_;
}
else
{
lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v_mid_1002_; lean_object* v___y_1004_; lean_object* v___y_1010_; lean_object* v___x_1015_; lean_object* v___x_1016_; uint8_t v___x_1017_; 
v___x_1000_ = lean_nat_add(v_lo_986_, v_hi_987_);
v___x_1001_ = lean_unsigned_to_nat(1u);
v_mid_1002_ = lean_nat_shiftr(v___x_1000_, v___x_1001_);
lean_dec(v___x_1000_);
v___x_1015_ = lean_array_fget_borrowed(v_as_985_, v_mid_1002_);
v___x_1016_ = lean_array_fget_borrowed(v_as_985_, v_lo_986_);
v___x_1017_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg___lam__0(v___x_1015_, v___x_1016_);
if (v___x_1017_ == 0)
{
v___y_1010_ = v_as_985_;
goto v___jp_1009_;
}
else
{
lean_object* v___x_1018_; 
v___x_1018_ = lean_array_fswap(v_as_985_, v_lo_986_, v_mid_1002_);
v___y_1010_ = v___x_1018_;
goto v___jp_1009_;
}
v___jp_1003_:
{
lean_object* v___x_1005_; lean_object* v___x_1006_; uint8_t v___x_1007_; 
v___x_1005_ = lean_array_fget_borrowed(v___y_1004_, v_mid_1002_);
v___x_1006_ = lean_array_fget_borrowed(v___y_1004_, v_hi_987_);
v___x_1007_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg___lam__0(v___x_1005_, v___x_1006_);
if (v___x_1007_ == 0)
{
lean_dec(v_mid_1002_);
v___y_989_ = v___y_1004_;
goto v___jp_988_;
}
else
{
lean_object* v___x_1008_; 
v___x_1008_ = lean_array_fswap(v___y_1004_, v_mid_1002_, v_hi_987_);
lean_dec(v_mid_1002_);
v___y_989_ = v___x_1008_;
goto v___jp_988_;
}
}
v___jp_1009_:
{
lean_object* v___x_1011_; lean_object* v___x_1012_; uint8_t v___x_1013_; 
v___x_1011_ = lean_array_fget_borrowed(v___y_1010_, v_hi_987_);
v___x_1012_ = lean_array_fget_borrowed(v___y_1010_, v_lo_986_);
v___x_1013_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg___lam__0(v___x_1011_, v___x_1012_);
if (v___x_1013_ == 0)
{
v___y_1004_ = v___y_1010_;
goto v___jp_1003_;
}
else
{
lean_object* v___x_1014_; 
v___x_1014_ = lean_array_fswap(v___y_1010_, v_lo_986_, v_hi_987_);
v___y_1004_ = v___x_1014_;
goto v___jp_1003_;
}
}
}
v___jp_988_:
{
lean_object* v_pivot_990_; lean_object* v___x_991_; lean_object* v_fst_992_; lean_object* v_snd_993_; uint8_t v___x_994_; 
v_pivot_990_ = lean_array_fget(v___y_989_, v_hi_987_);
lean_inc_n(v_lo_986_, 2);
v___x_991_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6_spec__8___redArg(v_hi_987_, v_pivot_990_, v___y_989_, v_lo_986_, v_lo_986_);
lean_dec(v_pivot_990_);
v_fst_992_ = lean_ctor_get(v___x_991_, 0);
lean_inc(v_fst_992_);
v_snd_993_ = lean_ctor_get(v___x_991_, 1);
lean_inc(v_snd_993_);
lean_dec_ref(v___x_991_);
v___x_994_ = lean_nat_dec_le(v_hi_987_, v_fst_992_);
if (v___x_994_ == 0)
{
lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; 
v___x_995_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg(v_n_984_, v_snd_993_, v_lo_986_, v_fst_992_);
v___x_996_ = lean_unsigned_to_nat(1u);
v___x_997_ = lean_nat_add(v_fst_992_, v___x_996_);
lean_dec(v_fst_992_);
v_as_985_ = v___x_995_;
v_lo_986_ = v___x_997_;
goto _start;
}
else
{
lean_dec(v_fst_992_);
lean_dec(v_lo_986_);
return v_snd_993_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg___boxed(lean_object* v_n_1019_, lean_object* v_as_1020_, lean_object* v_lo_1021_, lean_object* v_hi_1022_){
_start:
{
lean_object* v_res_1023_; 
v_res_1023_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg(v_n_1019_, v_as_1020_, v_lo_1021_, v_hi_1022_);
lean_dec(v_hi_1022_);
lean_dec(v_n_1019_);
return v_res_1023_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__12_spec__16___redArg(lean_object* v_x_1024_, lean_object* v_x_1025_, lean_object* v_x_1026_, lean_object* v_x_1027_){
_start:
{
lean_object* v_ks_1028_; lean_object* v_vs_1029_; lean_object* v___x_1031_; uint8_t v_isShared_1032_; uint8_t v_isSharedCheck_1053_; 
v_ks_1028_ = lean_ctor_get(v_x_1024_, 0);
v_vs_1029_ = lean_ctor_get(v_x_1024_, 1);
v_isSharedCheck_1053_ = !lean_is_exclusive(v_x_1024_);
if (v_isSharedCheck_1053_ == 0)
{
v___x_1031_ = v_x_1024_;
v_isShared_1032_ = v_isSharedCheck_1053_;
goto v_resetjp_1030_;
}
else
{
lean_inc(v_vs_1029_);
lean_inc(v_ks_1028_);
lean_dec(v_x_1024_);
v___x_1031_ = lean_box(0);
v_isShared_1032_ = v_isSharedCheck_1053_;
goto v_resetjp_1030_;
}
v_resetjp_1030_:
{
lean_object* v___x_1033_; uint8_t v___x_1034_; 
v___x_1033_ = lean_array_get_size(v_ks_1028_);
v___x_1034_ = lean_nat_dec_lt(v_x_1025_, v___x_1033_);
if (v___x_1034_ == 0)
{
lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1038_; 
lean_dec(v_x_1025_);
v___x_1035_ = lean_array_push(v_ks_1028_, v_x_1026_);
v___x_1036_ = lean_array_push(v_vs_1029_, v_x_1027_);
if (v_isShared_1032_ == 0)
{
lean_ctor_set(v___x_1031_, 1, v___x_1036_);
lean_ctor_set(v___x_1031_, 0, v___x_1035_);
v___x_1038_ = v___x_1031_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v___x_1035_);
lean_ctor_set(v_reuseFailAlloc_1039_, 1, v___x_1036_);
v___x_1038_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
return v___x_1038_;
}
}
else
{
lean_object* v_k_x27_1040_; uint8_t v___x_1041_; 
v_k_x27_1040_ = lean_array_fget_borrowed(v_ks_1028_, v_x_1025_);
v___x_1041_ = l_Lean_instBEqMVarId_beq(v_x_1026_, v_k_x27_1040_);
if (v___x_1041_ == 0)
{
lean_object* v___x_1043_; 
if (v_isShared_1032_ == 0)
{
v___x_1043_ = v___x_1031_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1047_; 
v_reuseFailAlloc_1047_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1047_, 0, v_ks_1028_);
lean_ctor_set(v_reuseFailAlloc_1047_, 1, v_vs_1029_);
v___x_1043_ = v_reuseFailAlloc_1047_;
goto v_reusejp_1042_;
}
v_reusejp_1042_:
{
lean_object* v___x_1044_; lean_object* v___x_1045_; 
v___x_1044_ = lean_unsigned_to_nat(1u);
v___x_1045_ = lean_nat_add(v_x_1025_, v___x_1044_);
lean_dec(v_x_1025_);
v_x_1024_ = v___x_1043_;
v_x_1025_ = v___x_1045_;
goto _start;
}
}
else
{
lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1051_; 
v___x_1048_ = lean_array_fset(v_ks_1028_, v_x_1025_, v_x_1026_);
v___x_1049_ = lean_array_fset(v_vs_1029_, v_x_1025_, v_x_1027_);
lean_dec(v_x_1025_);
if (v_isShared_1032_ == 0)
{
lean_ctor_set(v___x_1031_, 1, v___x_1049_);
lean_ctor_set(v___x_1031_, 0, v___x_1048_);
v___x_1051_ = v___x_1031_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1052_; 
v_reuseFailAlloc_1052_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1052_, 0, v___x_1048_);
lean_ctor_set(v_reuseFailAlloc_1052_, 1, v___x_1049_);
v___x_1051_ = v_reuseFailAlloc_1052_;
goto v_reusejp_1050_;
}
v_reusejp_1050_:
{
return v___x_1051_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__12___redArg(lean_object* v_n_1054_, lean_object* v_k_1055_, lean_object* v_v_1056_){
_start:
{
lean_object* v___x_1057_; lean_object* v___x_1058_; 
v___x_1057_ = lean_unsigned_to_nat(0u);
v___x_1058_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__12_spec__16___redArg(v_n_1054_, v___x_1057_, v_k_1055_, v_v_1056_);
return v___x_1058_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_1059_; 
v___x_1059_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1059_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg(lean_object* v_x_1060_, size_t v_x_1061_, size_t v_x_1062_, lean_object* v_x_1063_, lean_object* v_x_1064_){
_start:
{
if (lean_obj_tag(v_x_1060_) == 0)
{
lean_object* v_es_1065_; size_t v___x_1066_; size_t v___x_1067_; lean_object* v_j_1068_; lean_object* v___x_1069_; uint8_t v___x_1070_; 
v_es_1065_ = lean_ctor_get(v_x_1060_, 0);
v___x_1066_ = ((size_t)31ULL);
v___x_1067_ = lean_usize_land(v_x_1061_, v___x_1066_);
v_j_1068_ = lean_usize_to_nat(v___x_1067_);
v___x_1069_ = lean_array_get_size(v_es_1065_);
v___x_1070_ = lean_nat_dec_lt(v_j_1068_, v___x_1069_);
if (v___x_1070_ == 0)
{
lean_dec(v_j_1068_);
lean_dec(v_x_1064_);
lean_dec(v_x_1063_);
return v_x_1060_;
}
else
{
lean_object* v___x_1072_; uint8_t v_isShared_1073_; uint8_t v_isSharedCheck_1109_; 
lean_inc_ref(v_es_1065_);
v_isSharedCheck_1109_ = !lean_is_exclusive(v_x_1060_);
if (v_isSharedCheck_1109_ == 0)
{
lean_object* v_unused_1110_; 
v_unused_1110_ = lean_ctor_get(v_x_1060_, 0);
lean_dec(v_unused_1110_);
v___x_1072_ = v_x_1060_;
v_isShared_1073_ = v_isSharedCheck_1109_;
goto v_resetjp_1071_;
}
else
{
lean_dec(v_x_1060_);
v___x_1072_ = lean_box(0);
v_isShared_1073_ = v_isSharedCheck_1109_;
goto v_resetjp_1071_;
}
v_resetjp_1071_:
{
lean_object* v_v_1074_; lean_object* v___x_1075_; lean_object* v_xs_x27_1076_; lean_object* v___y_1078_; 
v_v_1074_ = lean_array_fget(v_es_1065_, v_j_1068_);
v___x_1075_ = lean_box(0);
v_xs_x27_1076_ = lean_array_fset(v_es_1065_, v_j_1068_, v___x_1075_);
switch(lean_obj_tag(v_v_1074_))
{
case 0:
{
lean_object* v_key_1083_; lean_object* v_val_1084_; lean_object* v___x_1086_; uint8_t v_isShared_1087_; uint8_t v_isSharedCheck_1094_; 
v_key_1083_ = lean_ctor_get(v_v_1074_, 0);
v_val_1084_ = lean_ctor_get(v_v_1074_, 1);
v_isSharedCheck_1094_ = !lean_is_exclusive(v_v_1074_);
if (v_isSharedCheck_1094_ == 0)
{
v___x_1086_ = v_v_1074_;
v_isShared_1087_ = v_isSharedCheck_1094_;
goto v_resetjp_1085_;
}
else
{
lean_inc(v_val_1084_);
lean_inc(v_key_1083_);
lean_dec(v_v_1074_);
v___x_1086_ = lean_box(0);
v_isShared_1087_ = v_isSharedCheck_1094_;
goto v_resetjp_1085_;
}
v_resetjp_1085_:
{
uint8_t v___x_1088_; 
v___x_1088_ = l_Lean_instBEqMVarId_beq(v_x_1063_, v_key_1083_);
if (v___x_1088_ == 0)
{
lean_object* v___x_1089_; lean_object* v___x_1090_; 
lean_del_object(v___x_1086_);
v___x_1089_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1083_, v_val_1084_, v_x_1063_, v_x_1064_);
v___x_1090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1090_, 0, v___x_1089_);
v___y_1078_ = v___x_1090_;
goto v___jp_1077_;
}
else
{
lean_object* v___x_1092_; 
lean_dec(v_val_1084_);
lean_dec(v_key_1083_);
if (v_isShared_1087_ == 0)
{
lean_ctor_set(v___x_1086_, 1, v_x_1064_);
lean_ctor_set(v___x_1086_, 0, v_x_1063_);
v___x_1092_ = v___x_1086_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v_x_1063_);
lean_ctor_set(v_reuseFailAlloc_1093_, 1, v_x_1064_);
v___x_1092_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1091_;
}
v_reusejp_1091_:
{
v___y_1078_ = v___x_1092_;
goto v___jp_1077_;
}
}
}
}
case 1:
{
lean_object* v_node_1095_; lean_object* v___x_1097_; uint8_t v_isShared_1098_; uint8_t v_isSharedCheck_1107_; 
v_node_1095_ = lean_ctor_get(v_v_1074_, 0);
v_isSharedCheck_1107_ = !lean_is_exclusive(v_v_1074_);
if (v_isSharedCheck_1107_ == 0)
{
v___x_1097_ = v_v_1074_;
v_isShared_1098_ = v_isSharedCheck_1107_;
goto v_resetjp_1096_;
}
else
{
lean_inc(v_node_1095_);
lean_dec(v_v_1074_);
v___x_1097_ = lean_box(0);
v_isShared_1098_ = v_isSharedCheck_1107_;
goto v_resetjp_1096_;
}
v_resetjp_1096_:
{
size_t v___x_1099_; size_t v___x_1100_; size_t v___x_1101_; size_t v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1105_; 
v___x_1099_ = ((size_t)5ULL);
v___x_1100_ = lean_usize_shift_right(v_x_1061_, v___x_1099_);
v___x_1101_ = ((size_t)1ULL);
v___x_1102_ = lean_usize_add(v_x_1062_, v___x_1101_);
v___x_1103_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg(v_node_1095_, v___x_1100_, v___x_1102_, v_x_1063_, v_x_1064_);
if (v_isShared_1098_ == 0)
{
lean_ctor_set(v___x_1097_, 0, v___x_1103_);
v___x_1105_ = v___x_1097_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v___x_1103_);
v___x_1105_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
v___y_1078_ = v___x_1105_;
goto v___jp_1077_;
}
}
}
default: 
{
lean_object* v___x_1108_; 
v___x_1108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1108_, 0, v_x_1063_);
lean_ctor_set(v___x_1108_, 1, v_x_1064_);
v___y_1078_ = v___x_1108_;
goto v___jp_1077_;
}
}
v___jp_1077_:
{
lean_object* v___x_1079_; lean_object* v___x_1081_; 
v___x_1079_ = lean_array_fset(v_xs_x27_1076_, v_j_1068_, v___y_1078_);
lean_dec(v_j_1068_);
if (v_isShared_1073_ == 0)
{
lean_ctor_set(v___x_1072_, 0, v___x_1079_);
v___x_1081_ = v___x_1072_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v___x_1079_);
v___x_1081_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
return v___x_1081_;
}
}
}
}
}
else
{
lean_object* v_ks_1111_; lean_object* v_vs_1112_; lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1132_; 
v_ks_1111_ = lean_ctor_get(v_x_1060_, 0);
v_vs_1112_ = lean_ctor_get(v_x_1060_, 1);
v_isSharedCheck_1132_ = !lean_is_exclusive(v_x_1060_);
if (v_isSharedCheck_1132_ == 0)
{
v___x_1114_ = v_x_1060_;
v_isShared_1115_ = v_isSharedCheck_1132_;
goto v_resetjp_1113_;
}
else
{
lean_inc(v_vs_1112_);
lean_inc(v_ks_1111_);
lean_dec(v_x_1060_);
v___x_1114_ = lean_box(0);
v_isShared_1115_ = v_isSharedCheck_1132_;
goto v_resetjp_1113_;
}
v_resetjp_1113_:
{
lean_object* v___x_1117_; 
if (v_isShared_1115_ == 0)
{
v___x_1117_ = v___x_1114_;
goto v_reusejp_1116_;
}
else
{
lean_object* v_reuseFailAlloc_1131_; 
v_reuseFailAlloc_1131_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1131_, 0, v_ks_1111_);
lean_ctor_set(v_reuseFailAlloc_1131_, 1, v_vs_1112_);
v___x_1117_ = v_reuseFailAlloc_1131_;
goto v_reusejp_1116_;
}
v_reusejp_1116_:
{
lean_object* v_newNode_1118_; uint8_t v___y_1120_; size_t v___x_1126_; uint8_t v___x_1127_; 
v_newNode_1118_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__12___redArg(v___x_1117_, v_x_1063_, v_x_1064_);
v___x_1126_ = ((size_t)7ULL);
v___x_1127_ = lean_usize_dec_le(v___x_1126_, v_x_1062_);
if (v___x_1127_ == 0)
{
lean_object* v___x_1128_; lean_object* v___x_1129_; uint8_t v___x_1130_; 
v___x_1128_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1118_);
v___x_1129_ = lean_unsigned_to_nat(4u);
v___x_1130_ = lean_nat_dec_lt(v___x_1128_, v___x_1129_);
lean_dec(v___x_1128_);
v___y_1120_ = v___x_1130_;
goto v___jp_1119_;
}
else
{
v___y_1120_ = v___x_1127_;
goto v___jp_1119_;
}
v___jp_1119_:
{
if (v___y_1120_ == 0)
{
lean_object* v_ks_1121_; lean_object* v_vs_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; 
v_ks_1121_ = lean_ctor_get(v_newNode_1118_, 0);
lean_inc_ref(v_ks_1121_);
v_vs_1122_ = lean_ctor_get(v_newNode_1118_, 1);
lean_inc_ref(v_vs_1122_);
lean_dec_ref(v_newNode_1118_);
v___x_1123_ = lean_unsigned_to_nat(0u);
v___x_1124_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__0);
v___x_1125_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__13___redArg(v_x_1062_, v_ks_1121_, v_vs_1122_, v___x_1123_, v___x_1124_);
lean_dec_ref(v_vs_1122_);
lean_dec_ref(v_ks_1121_);
return v___x_1125_;
}
else
{
return v_newNode_1118_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__13___redArg(size_t v_depth_1133_, lean_object* v_keys_1134_, lean_object* v_vals_1135_, lean_object* v_i_1136_, lean_object* v_entries_1137_){
_start:
{
lean_object* v___x_1138_; uint8_t v___x_1139_; 
v___x_1138_ = lean_array_get_size(v_keys_1134_);
v___x_1139_ = lean_nat_dec_lt(v_i_1136_, v___x_1138_);
if (v___x_1139_ == 0)
{
lean_dec(v_i_1136_);
return v_entries_1137_;
}
else
{
lean_object* v_k_1140_; lean_object* v_v_1141_; uint64_t v___x_1142_; size_t v_h_1143_; size_t v___x_1144_; lean_object* v___x_1145_; size_t v___x_1146_; size_t v___x_1147_; size_t v___x_1148_; size_t v_h_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; 
v_k_1140_ = lean_array_fget_borrowed(v_keys_1134_, v_i_1136_);
v_v_1141_ = lean_array_fget_borrowed(v_vals_1135_, v_i_1136_);
v___x_1142_ = l_Lean_instHashableMVarId_hash(v_k_1140_);
v_h_1143_ = lean_uint64_to_usize(v___x_1142_);
v___x_1144_ = ((size_t)5ULL);
v___x_1145_ = lean_unsigned_to_nat(1u);
v___x_1146_ = ((size_t)1ULL);
v___x_1147_ = lean_usize_sub(v_depth_1133_, v___x_1146_);
v___x_1148_ = lean_usize_mul(v___x_1144_, v___x_1147_);
v_h_1149_ = lean_usize_shift_right(v_h_1143_, v___x_1148_);
v___x_1150_ = lean_nat_add(v_i_1136_, v___x_1145_);
lean_dec(v_i_1136_);
lean_inc(v_v_1141_);
lean_inc(v_k_1140_);
v___x_1151_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg(v_entries_1137_, v_h_1149_, v_depth_1133_, v_k_1140_, v_v_1141_);
v_i_1136_ = v___x_1150_;
v_entries_1137_ = v___x_1151_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__13___redArg___boxed(lean_object* v_depth_1153_, lean_object* v_keys_1154_, lean_object* v_vals_1155_, lean_object* v_i_1156_, lean_object* v_entries_1157_){
_start:
{
size_t v_depth_boxed_1158_; lean_object* v_res_1159_; 
v_depth_boxed_1158_ = lean_unbox_usize(v_depth_1153_);
lean_dec(v_depth_1153_);
v_res_1159_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__13___redArg(v_depth_boxed_1158_, v_keys_1154_, v_vals_1155_, v_i_1156_, v_entries_1157_);
lean_dec_ref(v_vals_1155_);
lean_dec_ref(v_keys_1154_);
return v_res_1159_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___boxed(lean_object* v_x_1160_, lean_object* v_x_1161_, lean_object* v_x_1162_, lean_object* v_x_1163_, lean_object* v_x_1164_){
_start:
{
size_t v_x_18981__boxed_1165_; size_t v_x_18982__boxed_1166_; lean_object* v_res_1167_; 
v_x_18981__boxed_1165_ = lean_unbox_usize(v_x_1161_);
lean_dec(v_x_1161_);
v_x_18982__boxed_1166_ = lean_unbox_usize(v_x_1162_);
lean_dec(v_x_1162_);
v_res_1167_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg(v_x_1160_, v_x_18981__boxed_1165_, v_x_18982__boxed_1166_, v_x_1163_, v_x_1164_);
return v_res_1167_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3___redArg(lean_object* v_x_1168_, lean_object* v_x_1169_, lean_object* v_x_1170_){
_start:
{
uint64_t v___x_1171_; size_t v___x_1172_; size_t v___x_1173_; lean_object* v___x_1174_; 
v___x_1171_ = l_Lean_instHashableMVarId_hash(v_x_1169_);
v___x_1172_ = lean_uint64_to_usize(v___x_1171_);
v___x_1173_ = ((size_t)1ULL);
v___x_1174_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg(v_x_1168_, v___x_1172_, v___x_1173_, v_x_1169_, v_x_1170_);
return v___x_1174_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3___redArg(lean_object* v_mvarId_1175_, lean_object* v_val_1176_, lean_object* v___y_1177_){
_start:
{
lean_object* v___x_1179_; lean_object* v_mctx_1180_; lean_object* v_cache_1181_; lean_object* v_zetaDeltaFVarIds_1182_; lean_object* v_postponed_1183_; lean_object* v_diag_1184_; lean_object* v___x_1186_; uint8_t v_isShared_1187_; uint8_t v_isSharedCheck_1212_; 
v___x_1179_ = lean_st_ref_take(v___y_1177_);
v_mctx_1180_ = lean_ctor_get(v___x_1179_, 0);
v_cache_1181_ = lean_ctor_get(v___x_1179_, 1);
v_zetaDeltaFVarIds_1182_ = lean_ctor_get(v___x_1179_, 2);
v_postponed_1183_ = lean_ctor_get(v___x_1179_, 3);
v_diag_1184_ = lean_ctor_get(v___x_1179_, 4);
v_isSharedCheck_1212_ = !lean_is_exclusive(v___x_1179_);
if (v_isSharedCheck_1212_ == 0)
{
v___x_1186_ = v___x_1179_;
v_isShared_1187_ = v_isSharedCheck_1212_;
goto v_resetjp_1185_;
}
else
{
lean_inc(v_diag_1184_);
lean_inc(v_postponed_1183_);
lean_inc(v_zetaDeltaFVarIds_1182_);
lean_inc(v_cache_1181_);
lean_inc(v_mctx_1180_);
lean_dec(v___x_1179_);
v___x_1186_ = lean_box(0);
v_isShared_1187_ = v_isSharedCheck_1212_;
goto v_resetjp_1185_;
}
v_resetjp_1185_:
{
lean_object* v_depth_1188_; lean_object* v_levelAssignDepth_1189_; lean_object* v_lmvarCounter_1190_; lean_object* v_mvarCounter_1191_; lean_object* v_lDecls_1192_; lean_object* v_decls_1193_; lean_object* v_userNames_1194_; lean_object* v_lAssignment_1195_; lean_object* v_eAssignment_1196_; lean_object* v_dAssignment_1197_; lean_object* v___x_1199_; uint8_t v_isShared_1200_; uint8_t v_isSharedCheck_1211_; 
v_depth_1188_ = lean_ctor_get(v_mctx_1180_, 0);
v_levelAssignDepth_1189_ = lean_ctor_get(v_mctx_1180_, 1);
v_lmvarCounter_1190_ = lean_ctor_get(v_mctx_1180_, 2);
v_mvarCounter_1191_ = lean_ctor_get(v_mctx_1180_, 3);
v_lDecls_1192_ = lean_ctor_get(v_mctx_1180_, 4);
v_decls_1193_ = lean_ctor_get(v_mctx_1180_, 5);
v_userNames_1194_ = lean_ctor_get(v_mctx_1180_, 6);
v_lAssignment_1195_ = lean_ctor_get(v_mctx_1180_, 7);
v_eAssignment_1196_ = lean_ctor_get(v_mctx_1180_, 8);
v_dAssignment_1197_ = lean_ctor_get(v_mctx_1180_, 9);
v_isSharedCheck_1211_ = !lean_is_exclusive(v_mctx_1180_);
if (v_isSharedCheck_1211_ == 0)
{
v___x_1199_ = v_mctx_1180_;
v_isShared_1200_ = v_isSharedCheck_1211_;
goto v_resetjp_1198_;
}
else
{
lean_inc(v_dAssignment_1197_);
lean_inc(v_eAssignment_1196_);
lean_inc(v_lAssignment_1195_);
lean_inc(v_userNames_1194_);
lean_inc(v_decls_1193_);
lean_inc(v_lDecls_1192_);
lean_inc(v_mvarCounter_1191_);
lean_inc(v_lmvarCounter_1190_);
lean_inc(v_levelAssignDepth_1189_);
lean_inc(v_depth_1188_);
lean_dec(v_mctx_1180_);
v___x_1199_ = lean_box(0);
v_isShared_1200_ = v_isSharedCheck_1211_;
goto v_resetjp_1198_;
}
v_resetjp_1198_:
{
lean_object* v___x_1201_; lean_object* v___x_1203_; 
v___x_1201_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3___redArg(v_eAssignment_1196_, v_mvarId_1175_, v_val_1176_);
if (v_isShared_1200_ == 0)
{
lean_ctor_set(v___x_1199_, 8, v___x_1201_);
v___x_1203_ = v___x_1199_;
goto v_reusejp_1202_;
}
else
{
lean_object* v_reuseFailAlloc_1210_; 
v_reuseFailAlloc_1210_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1210_, 0, v_depth_1188_);
lean_ctor_set(v_reuseFailAlloc_1210_, 1, v_levelAssignDepth_1189_);
lean_ctor_set(v_reuseFailAlloc_1210_, 2, v_lmvarCounter_1190_);
lean_ctor_set(v_reuseFailAlloc_1210_, 3, v_mvarCounter_1191_);
lean_ctor_set(v_reuseFailAlloc_1210_, 4, v_lDecls_1192_);
lean_ctor_set(v_reuseFailAlloc_1210_, 5, v_decls_1193_);
lean_ctor_set(v_reuseFailAlloc_1210_, 6, v_userNames_1194_);
lean_ctor_set(v_reuseFailAlloc_1210_, 7, v_lAssignment_1195_);
lean_ctor_set(v_reuseFailAlloc_1210_, 8, v___x_1201_);
lean_ctor_set(v_reuseFailAlloc_1210_, 9, v_dAssignment_1197_);
v___x_1203_ = v_reuseFailAlloc_1210_;
goto v_reusejp_1202_;
}
v_reusejp_1202_:
{
lean_object* v___x_1205_; 
if (v_isShared_1187_ == 0)
{
lean_ctor_set(v___x_1186_, 0, v___x_1203_);
v___x_1205_ = v___x_1186_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v___x_1203_);
lean_ctor_set(v_reuseFailAlloc_1209_, 1, v_cache_1181_);
lean_ctor_set(v_reuseFailAlloc_1209_, 2, v_zetaDeltaFVarIds_1182_);
lean_ctor_set(v_reuseFailAlloc_1209_, 3, v_postponed_1183_);
lean_ctor_set(v_reuseFailAlloc_1209_, 4, v_diag_1184_);
v___x_1205_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; 
v___x_1206_ = lean_st_ref_set(v___y_1177_, v___x_1205_);
v___x_1207_ = lean_box(0);
v___x_1208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1208_, 0, v___x_1207_);
return v___x_1208_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3___redArg___boxed(lean_object* v_mvarId_1213_, lean_object* v_val_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_){
_start:
{
lean_object* v_res_1217_; 
v_res_1217_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3___redArg(v_mvarId_1213_, v_val_1214_, v___y_1215_);
lean_dec(v___y_1215_);
return v_res_1217_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg___lam__0(lean_object* v_x1_1218_, lean_object* v_x2_1219_){
_start:
{
lean_object* v_fst_1220_; lean_object* v_fst_1221_; uint8_t v___x_1222_; 
v_fst_1220_ = lean_ctor_get(v_x1_1218_, 0);
v_fst_1221_ = lean_ctor_get(v_x2_1219_, 0);
v___x_1222_ = lean_nat_dec_lt(v_fst_1220_, v_fst_1221_);
return v___x_1222_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg___lam__0___boxed(lean_object* v_x1_1223_, lean_object* v_x2_1224_){
_start:
{
uint8_t v_res_1225_; lean_object* v_r_1226_; 
v_res_1225_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg___lam__0(v_x1_1223_, v_x2_1224_);
lean_dec_ref(v_x2_1224_);
lean_dec_ref(v_x1_1223_);
v_r_1226_ = lean_box(v_res_1225_);
return v_r_1226_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9_spec__13___redArg(lean_object* v_hi_1227_, lean_object* v_pivot_1228_, lean_object* v_as_1229_, lean_object* v_i_1230_, lean_object* v_k_1231_){
_start:
{
uint8_t v___x_1232_; 
v___x_1232_ = lean_nat_dec_lt(v_k_1231_, v_hi_1227_);
if (v___x_1232_ == 0)
{
lean_object* v___x_1233_; lean_object* v___x_1234_; 
lean_dec(v_k_1231_);
v___x_1233_ = lean_array_fswap(v_as_1229_, v_i_1230_, v_hi_1227_);
v___x_1234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1234_, 0, v_i_1230_);
lean_ctor_set(v___x_1234_, 1, v___x_1233_);
return v___x_1234_;
}
else
{
lean_object* v___x_1235_; lean_object* v_fst_1236_; lean_object* v_fst_1237_; uint8_t v___x_1238_; 
v___x_1235_ = lean_array_fget_borrowed(v_as_1229_, v_k_1231_);
v_fst_1236_ = lean_ctor_get(v___x_1235_, 0);
v_fst_1237_ = lean_ctor_get(v_pivot_1228_, 0);
v___x_1238_ = lean_nat_dec_lt(v_fst_1236_, v_fst_1237_);
if (v___x_1238_ == 0)
{
lean_object* v___x_1239_; lean_object* v___x_1240_; 
v___x_1239_ = lean_unsigned_to_nat(1u);
v___x_1240_ = lean_nat_add(v_k_1231_, v___x_1239_);
lean_dec(v_k_1231_);
v_k_1231_ = v___x_1240_;
goto _start;
}
else
{
lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; 
v___x_1242_ = lean_array_fswap(v_as_1229_, v_i_1230_, v_k_1231_);
v___x_1243_ = lean_unsigned_to_nat(1u);
v___x_1244_ = lean_nat_add(v_i_1230_, v___x_1243_);
lean_dec(v_i_1230_);
v___x_1245_ = lean_nat_add(v_k_1231_, v___x_1243_);
lean_dec(v_k_1231_);
v_as_1229_ = v___x_1242_;
v_i_1230_ = v___x_1244_;
v_k_1231_ = v___x_1245_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9_spec__13___redArg___boxed(lean_object* v_hi_1247_, lean_object* v_pivot_1248_, lean_object* v_as_1249_, lean_object* v_i_1250_, lean_object* v_k_1251_){
_start:
{
lean_object* v_res_1252_; 
v_res_1252_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9_spec__13___redArg(v_hi_1247_, v_pivot_1248_, v_as_1249_, v_i_1250_, v_k_1251_);
lean_dec_ref(v_pivot_1248_);
lean_dec(v_hi_1247_);
return v_res_1252_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg(lean_object* v_n_1253_, lean_object* v_as_1254_, lean_object* v_lo_1255_, lean_object* v_hi_1256_){
_start:
{
lean_object* v___y_1258_; uint8_t v___x_1268_; 
v___x_1268_ = lean_nat_dec_lt(v_lo_1255_, v_hi_1256_);
if (v___x_1268_ == 0)
{
lean_dec(v_lo_1255_);
return v_as_1254_;
}
else
{
lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v_mid_1271_; lean_object* v___y_1273_; lean_object* v___y_1279_; lean_object* v___x_1284_; lean_object* v___x_1285_; uint8_t v___x_1286_; 
v___x_1269_ = lean_nat_add(v_lo_1255_, v_hi_1256_);
v___x_1270_ = lean_unsigned_to_nat(1u);
v_mid_1271_ = lean_nat_shiftr(v___x_1269_, v___x_1270_);
lean_dec(v___x_1269_);
v___x_1284_ = lean_array_fget_borrowed(v_as_1254_, v_mid_1271_);
v___x_1285_ = lean_array_fget_borrowed(v_as_1254_, v_lo_1255_);
v___x_1286_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg___lam__0(v___x_1284_, v___x_1285_);
if (v___x_1286_ == 0)
{
v___y_1279_ = v_as_1254_;
goto v___jp_1278_;
}
else
{
lean_object* v___x_1287_; 
v___x_1287_ = lean_array_fswap(v_as_1254_, v_lo_1255_, v_mid_1271_);
v___y_1279_ = v___x_1287_;
goto v___jp_1278_;
}
v___jp_1272_:
{
lean_object* v___x_1274_; lean_object* v___x_1275_; uint8_t v___x_1276_; 
v___x_1274_ = lean_array_fget_borrowed(v___y_1273_, v_mid_1271_);
v___x_1275_ = lean_array_fget_borrowed(v___y_1273_, v_hi_1256_);
v___x_1276_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg___lam__0(v___x_1274_, v___x_1275_);
if (v___x_1276_ == 0)
{
lean_dec(v_mid_1271_);
v___y_1258_ = v___y_1273_;
goto v___jp_1257_;
}
else
{
lean_object* v___x_1277_; 
v___x_1277_ = lean_array_fswap(v___y_1273_, v_mid_1271_, v_hi_1256_);
lean_dec(v_mid_1271_);
v___y_1258_ = v___x_1277_;
goto v___jp_1257_;
}
}
v___jp_1278_:
{
lean_object* v___x_1280_; lean_object* v___x_1281_; uint8_t v___x_1282_; 
v___x_1280_ = lean_array_fget_borrowed(v___y_1279_, v_hi_1256_);
v___x_1281_ = lean_array_fget_borrowed(v___y_1279_, v_lo_1255_);
v___x_1282_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg___lam__0(v___x_1280_, v___x_1281_);
if (v___x_1282_ == 0)
{
v___y_1273_ = v___y_1279_;
goto v___jp_1272_;
}
else
{
lean_object* v___x_1283_; 
v___x_1283_ = lean_array_fswap(v___y_1279_, v_lo_1255_, v_hi_1256_);
v___y_1273_ = v___x_1283_;
goto v___jp_1272_;
}
}
}
v___jp_1257_:
{
lean_object* v_pivot_1259_; lean_object* v___x_1260_; lean_object* v_fst_1261_; lean_object* v_snd_1262_; uint8_t v___x_1263_; 
v_pivot_1259_ = lean_array_fget(v___y_1258_, v_hi_1256_);
lean_inc_n(v_lo_1255_, 2);
v___x_1260_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9_spec__13___redArg(v_hi_1256_, v_pivot_1259_, v___y_1258_, v_lo_1255_, v_lo_1255_);
lean_dec(v_pivot_1259_);
v_fst_1261_ = lean_ctor_get(v___x_1260_, 0);
lean_inc(v_fst_1261_);
v_snd_1262_ = lean_ctor_get(v___x_1260_, 1);
lean_inc(v_snd_1262_);
lean_dec_ref(v___x_1260_);
v___x_1263_ = lean_nat_dec_le(v_hi_1256_, v_fst_1261_);
if (v___x_1263_ == 0)
{
lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; 
v___x_1264_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg(v_n_1253_, v_snd_1262_, v_lo_1255_, v_fst_1261_);
v___x_1265_ = lean_unsigned_to_nat(1u);
v___x_1266_ = lean_nat_add(v_fst_1261_, v___x_1265_);
lean_dec(v_fst_1261_);
v_as_1254_ = v___x_1264_;
v_lo_1255_ = v___x_1266_;
goto _start;
}
else
{
lean_dec(v_fst_1261_);
lean_dec(v_lo_1255_);
return v_snd_1262_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg___boxed(lean_object* v_n_1288_, lean_object* v_as_1289_, lean_object* v_lo_1290_, lean_object* v_hi_1291_){
_start:
{
lean_object* v_res_1292_; 
v_res_1292_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg(v_n_1288_, v_as_1289_, v_lo_1290_, v_hi_1291_);
lean_dec(v_hi_1291_);
lean_dec(v_n_1288_);
return v_res_1292_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11_spec__13___redArg(lean_object* v_as_1293_, lean_object* v_a_1294_, lean_object* v_x_1295_){
_start:
{
lean_object* v_zero_1296_; uint8_t v_isZero_1297_; 
v_zero_1296_ = lean_unsigned_to_nat(0u);
v_isZero_1297_ = lean_nat_dec_eq(v_x_1295_, v_zero_1296_);
if (v_isZero_1297_ == 1)
{
lean_dec(v_x_1295_);
return v_isZero_1297_;
}
else
{
lean_object* v_fst_1298_; lean_object* v_one_1299_; lean_object* v_n_1300_; lean_object* v___x_1301_; lean_object* v_fst_1302_; uint8_t v___x_1303_; 
v_fst_1298_ = lean_ctor_get(v_a_1294_, 0);
v_one_1299_ = lean_unsigned_to_nat(1u);
v_n_1300_ = lean_nat_sub(v_x_1295_, v_one_1299_);
lean_dec(v_x_1295_);
v___x_1301_ = lean_array_fget_borrowed(v_as_1293_, v_n_1300_);
v_fst_1302_ = lean_ctor_get(v___x_1301_, 0);
v___x_1303_ = lean_nat_dec_eq(v_fst_1298_, v_fst_1302_);
if (v___x_1303_ == 0)
{
v_x_1295_ = v_n_1300_;
goto _start;
}
else
{
lean_dec(v_n_1300_);
return v_isZero_1297_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11_spec__13___redArg___boxed(lean_object* v_as_1305_, lean_object* v_a_1306_, lean_object* v_x_1307_){
_start:
{
uint8_t v_res_1308_; lean_object* v_r_1309_; 
v_res_1308_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11_spec__13___redArg(v_as_1305_, v_a_1306_, v_x_1307_);
lean_dec_ref(v_a_1306_);
lean_dec_ref(v_as_1305_);
v_r_1309_ = lean_box(v_res_1308_);
return v_r_1309_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11(lean_object* v_as_1310_, lean_object* v_i_1311_){
_start:
{
lean_object* v___x_1312_; uint8_t v___x_1313_; 
v___x_1312_ = lean_array_get_size(v_as_1310_);
v___x_1313_ = lean_nat_dec_lt(v_i_1311_, v___x_1312_);
if (v___x_1313_ == 0)
{
uint8_t v___x_1314_; 
lean_dec(v_i_1311_);
v___x_1314_ = 1;
return v___x_1314_;
}
else
{
lean_object* v___x_1315_; uint8_t v___x_1316_; 
v___x_1315_ = lean_array_fget_borrowed(v_as_1310_, v_i_1311_);
lean_inc(v_i_1311_);
v___x_1316_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11_spec__13___redArg(v_as_1310_, v___x_1315_, v_i_1311_);
if (v___x_1316_ == 0)
{
lean_dec(v_i_1311_);
return v___x_1316_;
}
else
{
lean_object* v___x_1317_; lean_object* v___x_1318_; 
v___x_1317_ = lean_unsigned_to_nat(1u);
v___x_1318_ = lean_nat_add(v_i_1311_, v___x_1317_);
lean_dec(v_i_1311_);
v_i_1311_ = v___x_1318_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11___boxed(lean_object* v_as_1320_, lean_object* v_i_1321_){
_start:
{
uint8_t v_res_1322_; lean_object* v_r_1323_; 
v_res_1322_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11(v_as_1320_, v_i_1321_);
lean_dec_ref(v_as_1320_);
v_r_1323_ = lean_box(v_res_1322_);
return v_r_1323_;
}
}
LEAN_EXPORT uint8_t l_Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8(lean_object* v_as_1324_){
_start:
{
lean_object* v___x_1325_; uint8_t v___x_1326_; 
v___x_1325_ = lean_unsigned_to_nat(0u);
v___x_1326_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11(v_as_1324_, v___x_1325_);
return v___x_1326_;
}
}
LEAN_EXPORT lean_object* l_Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8___boxed(lean_object* v_as_1327_){
_start:
{
uint8_t v_res_1328_; lean_object* v_r_1329_; 
v_res_1328_ = l_Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8(v_as_1327_);
lean_dec_ref(v_as_1327_);
v_r_1329_ = lean_box(v_res_1328_);
return v_r_1329_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__0(void){
_start:
{
lean_object* v___x_1330_; 
v___x_1330_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1330_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__1(void){
_start:
{
lean_object* v___x_1331_; lean_object* v___x_1332_; 
v___x_1331_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__0, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__0_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__0);
v___x_1332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1332_, 0, v___x_1331_);
return v___x_1332_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__2(void){
_start:
{
lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; 
v___x_1333_ = lean_unsigned_to_nat(0u);
v___x_1334_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__1, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__1_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__1);
v___x_1335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1335_, 0, v___x_1334_);
lean_ctor_set(v___x_1335_, 1, v___x_1333_);
return v___x_1335_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__3(void){
_start:
{
lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; 
v___x_1336_ = lean_unsigned_to_nat(32u);
v___x_1337_ = lean_mk_empty_array_with_capacity(v___x_1336_);
v___x_1338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1338_, 0, v___x_1337_);
return v___x_1338_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__4(void){
_start:
{
size_t v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; 
v___x_1339_ = ((size_t)5ULL);
v___x_1340_ = lean_unsigned_to_nat(0u);
v___x_1341_ = lean_unsigned_to_nat(32u);
v___x_1342_ = lean_mk_empty_array_with_capacity(v___x_1341_);
v___x_1343_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__3, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__3_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__3);
v___x_1344_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1344_, 0, v___x_1343_);
lean_ctor_set(v___x_1344_, 1, v___x_1342_);
lean_ctor_set(v___x_1344_, 2, v___x_1340_);
lean_ctor_set(v___x_1344_, 3, v___x_1340_);
lean_ctor_set_usize(v___x_1344_, 4, v___x_1339_);
return v___x_1344_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__5(void){
_start:
{
lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; 
v___x_1345_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__4, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__4_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__4);
v___x_1346_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__1, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__1_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__1);
v___x_1347_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1347_, 0, v___x_1346_);
lean_ctor_set(v___x_1347_, 1, v___x_1346_);
lean_ctor_set(v___x_1347_, 2, v___x_1346_);
lean_ctor_set(v___x_1347_, 3, v___x_1345_);
return v___x_1347_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__6(void){
_start:
{
lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; 
v___x_1348_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__5, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__5_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__5);
v___x_1349_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__2, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__2_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__2);
v___x_1350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1350_, 0, v___x_1349_);
lean_ctor_set(v___x_1350_, 1, v___x_1348_);
return v___x_1350_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__8(void){
_start:
{
lean_object* v___x_1352_; lean_object* v___x_1353_; 
v___x_1352_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__7));
v___x_1353_ = l_Lean_stringToMessageData(v___x_1352_);
return v___x_1353_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__10(void){
_start:
{
lean_object* v___x_1355_; lean_object* v___x_1356_; 
v___x_1355_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__9));
v___x_1356_ = l_Lean_stringToMessageData(v___x_1355_);
return v___x_1356_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__12(void){
_start:
{
lean_object* v___x_1358_; lean_object* v___x_1359_; 
v___x_1358_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__11));
v___x_1359_ = l_Lean_stringToMessageData(v___x_1358_);
return v___x_1359_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__14(void){
_start:
{
lean_object* v___x_1361_; lean_object* v___x_1362_; 
v___x_1361_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__13));
v___x_1362_ = l_Lean_stringToMessageData(v___x_1361_);
return v___x_1362_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__17(void){
_start:
{
lean_object* v___x_1366_; lean_object* v___x_1367_; 
v___x_1366_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__16));
v___x_1367_ = l_Lean_stringToMessageData(v___x_1366_);
return v___x_1367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__6(uint8_t v___x_1388_, lean_object* v___f_1389_, uint8_t v___x_1390_, lean_object* v_stx_1391_, lean_object* v___x_1392_, lean_object* v___x_1393_, lean_object* v___x_1394_, lean_object* v___x_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_){
_start:
{
lean_object* v___y_1406_; lean_object* v_subgoals_1407_; lean_object* v___y_1408_; lean_object* v___y_1409_; lean_object* v___y_1410_; lean_object* v___y_1411_; lean_object* v___y_1412_; lean_object* v___y_1413_; lean_object* v___y_1414_; lean_object* v___y_1415_; lean_object* v___y_1453_; lean_object* v___y_1454_; lean_object* v___y_1455_; lean_object* v___y_1456_; lean_object* v___y_1457_; lean_object* v___y_1458_; lean_object* v___y_1459_; lean_object* v___y_1460_; lean_object* v___y_1461_; lean_object* v___y_1462_; lean_object* v___y_1467_; lean_object* v___y_1468_; lean_object* v___y_1469_; lean_object* v___y_1470_; lean_object* v___y_1471_; lean_object* v___y_1472_; lean_object* v___y_1473_; lean_object* v___y_1474_; lean_object* v___y_1475_; lean_object* v___y_1476_; lean_object* v___y_1477_; lean_object* v___y_1478_; lean_object* v___y_1479_; lean_object* v___y_1482_; lean_object* v___y_1483_; lean_object* v___y_1484_; lean_object* v___y_1485_; lean_object* v___y_1486_; lean_object* v___y_1487_; lean_object* v___y_1488_; lean_object* v___y_1489_; lean_object* v___y_1490_; lean_object* v___y_1491_; lean_object* v___y_1492_; lean_object* v___y_1493_; lean_object* v___y_1494_; 
if (v___x_1388_ == 0)
{
lean_object* v___x_1496_; 
lean_dec_ref(v___x_1395_);
lean_dec_ref(v___x_1394_);
lean_dec_ref(v___x_1393_);
lean_dec_ref(v___x_1392_);
lean_dec_ref(v___f_1389_);
v___x_1496_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg();
return v___x_1496_;
}
else
{
lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___y_1500_; lean_object* v___y_1501_; lean_object* v___y_1502_; lean_object* v___y_1503_; lean_object* v___y_1504_; lean_object* v___y_1505_; lean_object* v___y_1506_; lean_object* v___y_1507_; lean_object* v___y_1508_; lean_object* v___y_1509_; lean_object* v___y_1515_; lean_object* v___y_1516_; lean_object* v___y_1517_; lean_object* v___y_1518_; lean_object* v___y_1519_; lean_object* v___y_1520_; lean_object* v___y_1521_; lean_object* v___y_1522_; lean_object* v___y_1523_; lean_object* v___y_1524_; lean_object* v___y_1525_; lean_object* v___y_1526_; lean_object* v___y_1527_; lean_object* v___y_1528_; lean_object* v___y_1529_; uint8_t v___y_1530_; lean_object* v___y_1623_; lean_object* v___y_1624_; lean_object* v___y_1625_; lean_object* v___y_1626_; lean_object* v___y_1627_; lean_object* v_occs_1628_; lean_object* v___y_1629_; lean_object* v___y_1630_; lean_object* v___y_1631_; lean_object* v___y_1632_; lean_object* v___y_1633_; lean_object* v___y_1634_; lean_object* v___y_1635_; lean_object* v___y_1636_; lean_object* v___y_1651_; lean_object* v___y_1652_; lean_object* v___y_1653_; lean_object* v___y_1654_; lean_object* v___y_1655_; lean_object* v___y_1656_; lean_object* v___y_1657_; lean_object* v___y_1658_; lean_object* v___y_1659_; lean_object* v___y_1660_; lean_object* v___y_1661_; lean_object* v___y_1662_; lean_object* v___y_1663_; lean_object* v___y_1664_; lean_object* v___y_1669_; lean_object* v___y_1670_; lean_object* v___y_1671_; lean_object* v___y_1672_; lean_object* v___y_1673_; lean_object* v___y_1674_; lean_object* v___y_1675_; lean_object* v___y_1676_; lean_object* v___y_1677_; lean_object* v___y_1678_; lean_object* v___y_1679_; lean_object* v___y_1680_; lean_object* v___y_1681_; lean_object* v___y_1682_; lean_object* v___y_1687_; lean_object* v___y_1688_; lean_object* v___y_1689_; lean_object* v___y_1690_; lean_object* v___y_1691_; lean_object* v___y_1692_; lean_object* v___y_1693_; lean_object* v___y_1694_; lean_object* v___y_1695_; lean_object* v___y_1696_; lean_object* v___y_1697_; lean_object* v___y_1698_; lean_object* v___y_1699_; lean_object* v___y_1700_; lean_object* v___y_1701_; lean_object* v___y_1702_; lean_object* v___y_1703_; lean_object* v___y_1706_; lean_object* v___y_1707_; lean_object* v___y_1708_; lean_object* v___y_1709_; lean_object* v___y_1710_; lean_object* v___y_1711_; lean_object* v___y_1712_; lean_object* v___y_1713_; lean_object* v___y_1714_; lean_object* v___y_1715_; lean_object* v___y_1716_; lean_object* v___y_1717_; lean_object* v___y_1718_; lean_object* v___y_1719_; lean_object* v___y_1720_; lean_object* v___y_1721_; lean_object* v___y_1722_; lean_object* v_occs_1725_; lean_object* v___y_1726_; lean_object* v___y_1727_; lean_object* v___y_1728_; lean_object* v___y_1729_; lean_object* v___y_1730_; lean_object* v___y_1731_; lean_object* v___y_1732_; lean_object* v___y_1733_; lean_object* v___x_1819_; uint8_t v___x_1820_; 
v___x_1497_ = lean_unsigned_to_nat(0u);
v___x_1498_ = lean_unsigned_to_nat(1u);
v___x_1819_ = l_Lean_Syntax_getArg(v_stx_1391_, v___x_1498_);
v___x_1820_ = l_Lean_Syntax_isNone(v___x_1819_);
if (v___x_1820_ == 0)
{
uint8_t v___x_1821_; 
lean_inc(v___x_1819_);
v___x_1821_ = l_Lean_Syntax_matchesNull(v___x_1819_, v___x_1498_);
if (v___x_1821_ == 0)
{
lean_object* v___x_1822_; 
lean_dec(v___x_1819_);
lean_dec_ref(v___x_1395_);
lean_dec_ref(v___x_1394_);
lean_dec_ref(v___x_1393_);
lean_dec_ref(v___x_1392_);
lean_dec_ref(v___f_1389_);
v___x_1822_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg();
return v___x_1822_;
}
else
{
lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; uint8_t v___x_1826_; 
v___x_1823_ = l_Lean_Syntax_getArg(v___x_1819_, v___x_1497_);
lean_dec(v___x_1819_);
v___x_1824_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__27));
lean_inc_ref(v___x_1395_);
lean_inc_ref(v___x_1394_);
lean_inc_ref(v___x_1393_);
lean_inc_ref(v___x_1392_);
v___x_1825_ = l_Lean_Name_mkStr5(v___x_1392_, v___x_1393_, v___x_1394_, v___x_1395_, v___x_1824_);
lean_inc(v___x_1823_);
v___x_1826_ = l_Lean_Syntax_isOfKind(v___x_1823_, v___x_1825_);
lean_dec(v___x_1825_);
if (v___x_1826_ == 0)
{
lean_object* v___x_1827_; 
lean_dec(v___x_1823_);
lean_dec_ref(v___x_1395_);
lean_dec_ref(v___x_1394_);
lean_dec_ref(v___x_1393_);
lean_dec_ref(v___x_1392_);
lean_dec_ref(v___f_1389_);
v___x_1827_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg();
return v___x_1827_;
}
else
{
lean_object* v___x_1828_; lean_object* v_occs_1829_; lean_object* v___x_1830_; 
v___x_1828_ = lean_unsigned_to_nat(3u);
v_occs_1829_ = l_Lean_Syntax_getArg(v___x_1823_, v___x_1828_);
lean_dec(v___x_1823_);
v___x_1830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1830_, 0, v_occs_1829_);
v_occs_1725_ = v___x_1830_;
v___y_1726_ = v___y_1396_;
v___y_1727_ = v___y_1397_;
v___y_1728_ = v___y_1398_;
v___y_1729_ = v___y_1399_;
v___y_1730_ = v___y_1400_;
v___y_1731_ = v___y_1401_;
v___y_1732_ = v___y_1402_;
v___y_1733_ = v___y_1403_;
goto v___jp_1724_;
}
}
}
else
{
lean_object* v___x_1831_; 
lean_dec(v___x_1819_);
v___x_1831_ = lean_box(0);
v_occs_1725_ = v___x_1831_;
v___y_1726_ = v___y_1396_;
v___y_1727_ = v___y_1397_;
v___y_1728_ = v___y_1398_;
v___y_1729_ = v___y_1399_;
v___y_1730_ = v___y_1400_;
v___y_1731_ = v___y_1401_;
v___y_1732_ = v___y_1402_;
v___y_1733_ = v___y_1403_;
goto v___jp_1724_;
}
v___jp_1499_:
{
lean_object* v___x_1510_; uint8_t v___x_1511_; 
v___x_1510_ = lean_array_get_size(v___y_1501_);
v___x_1511_ = lean_nat_dec_eq(v___x_1510_, v___x_1497_);
if (v___x_1511_ == 0)
{
lean_object* v___x_1512_; uint8_t v___x_1513_; 
v___x_1512_ = lean_nat_sub(v___x_1510_, v___x_1498_);
v___x_1513_ = lean_nat_dec_le(v___x_1497_, v___x_1512_);
if (v___x_1513_ == 0)
{
lean_inc(v___x_1512_);
v___y_1482_ = v___y_1505_;
v___y_1483_ = v___y_1508_;
v___y_1484_ = v___x_1512_;
v___y_1485_ = v___y_1507_;
v___y_1486_ = v___y_1501_;
v___y_1487_ = v___y_1504_;
v___y_1488_ = v___y_1506_;
v___y_1489_ = v___y_1503_;
v___y_1490_ = v___x_1510_;
v___y_1491_ = v___y_1500_;
v___y_1492_ = v___y_1509_;
v___y_1493_ = v___y_1502_;
v___y_1494_ = v___x_1512_;
goto v___jp_1481_;
}
else
{
v___y_1482_ = v___y_1505_;
v___y_1483_ = v___y_1508_;
v___y_1484_ = v___x_1512_;
v___y_1485_ = v___y_1507_;
v___y_1486_ = v___y_1501_;
v___y_1487_ = v___y_1504_;
v___y_1488_ = v___y_1506_;
v___y_1489_ = v___y_1503_;
v___y_1490_ = v___x_1510_;
v___y_1491_ = v___y_1500_;
v___y_1492_ = v___y_1509_;
v___y_1493_ = v___y_1502_;
v___y_1494_ = v___x_1497_;
goto v___jp_1481_;
}
}
else
{
v___y_1453_ = v___y_1503_;
v___y_1454_ = v___y_1500_;
v___y_1455_ = v___y_1505_;
v___y_1456_ = v___y_1508_;
v___y_1457_ = v___y_1507_;
v___y_1458_ = v___y_1509_;
v___y_1459_ = v___y_1502_;
v___y_1460_ = v___y_1504_;
v___y_1461_ = v___y_1506_;
v___y_1462_ = v___y_1501_;
goto v___jp_1452_;
}
}
v___jp_1514_:
{
lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; 
v___x_1531_ = l_Lean_Meta_Simp_Context_setMemoize(v___y_1522_, v___y_1530_);
v___x_1532_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__6, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__6_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__6);
lean_inc(v___y_1518_);
lean_inc_ref(v___y_1523_);
v___x_1533_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre___boxed), 11, 2);
lean_closure_set(v___x_1533_, 0, v___y_1523_);
lean_closure_set(v___x_1533_, 1, v___y_1518_);
lean_inc_ref(v___y_1515_);
lean_inc_ref(v___y_1520_);
v___x_1534_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_1534_, 0, v___x_1533_);
lean_ctor_set(v___x_1534_, 1, v___y_1529_);
lean_ctor_set(v___x_1534_, 2, v___y_1520_);
lean_ctor_set(v___x_1534_, 3, v___f_1389_);
lean_ctor_set(v___x_1534_, 4, v___y_1515_);
lean_ctor_set_uint8(v___x_1534_, sizeof(void*)*5, v___x_1390_);
v___x_1535_ = l_Lean_Meta_Simp_main(v___y_1524_, v___x_1531_, v___x_1532_, v___x_1534_, v___y_1526_, v___y_1517_, v___y_1525_, v___y_1528_);
if (lean_obj_tag(v___x_1535_) == 0)
{
lean_object* v_a_1536_; lean_object* v_fst_1537_; lean_object* v___x_1539_; uint8_t v_isShared_1540_; uint8_t v_isSharedCheck_1612_; 
v_a_1536_ = lean_ctor_get(v___x_1535_, 0);
lean_inc(v_a_1536_);
lean_dec_ref_known(v___x_1535_, 1);
v_fst_1537_ = lean_ctor_get(v_a_1536_, 0);
v_isSharedCheck_1612_ = !lean_is_exclusive(v_a_1536_);
if (v_isSharedCheck_1612_ == 0)
{
lean_object* v_unused_1613_; 
v_unused_1613_ = lean_ctor_get(v_a_1536_, 1);
lean_dec(v_unused_1613_);
v___x_1539_ = v_a_1536_;
v_isShared_1540_ = v_isSharedCheck_1612_;
goto v_resetjp_1538_;
}
else
{
lean_inc(v_fst_1537_);
lean_dec(v_a_1536_);
v___x_1539_ = lean_box(0);
v_isShared_1540_ = v_isSharedCheck_1612_;
goto v_resetjp_1538_;
}
v_resetjp_1538_:
{
lean_object* v___x_1541_; 
v___x_1541_ = lean_st_ref_get(v___y_1518_);
lean_dec(v___y_1518_);
if (lean_obj_tag(v___x_1541_) == 0)
{
lean_object* v_subgoals_1542_; lean_object* v___x_1543_; uint8_t v___x_1544_; 
v_subgoals_1542_ = lean_ctor_get(v___x_1541_, 0);
lean_inc_ref(v_subgoals_1542_);
lean_dec_ref_known(v___x_1541_, 1);
v___x_1543_ = lean_array_get_size(v_subgoals_1542_);
v___x_1544_ = lean_nat_dec_eq(v___x_1543_, v___x_1497_);
if (v___x_1544_ == 0)
{
lean_del_object(v___x_1539_);
lean_dec_ref(v___y_1523_);
v___y_1406_ = v_fst_1537_;
v_subgoals_1407_ = v_subgoals_1542_;
v___y_1408_ = v___y_1527_;
v___y_1409_ = v___y_1516_;
v___y_1410_ = v___y_1519_;
v___y_1411_ = v___y_1521_;
v___y_1412_ = v___y_1526_;
v___y_1413_ = v___y_1517_;
v___y_1414_ = v___y_1525_;
v___y_1415_ = v___y_1528_;
goto v___jp_1405_;
}
else
{
lean_object* v_expr_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1549_; 
lean_dec_ref(v_subgoals_1542_);
lean_dec(v_fst_1537_);
v_expr_1545_ = lean_ctor_get(v___y_1523_, 2);
lean_inc_ref(v_expr_1545_);
lean_dec_ref(v___y_1523_);
v___x_1546_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__8, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__8_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__8);
v___x_1547_ = l_Lean_indentExpr(v_expr_1545_);
if (v_isShared_1540_ == 0)
{
lean_ctor_set_tag(v___x_1539_, 7);
lean_ctor_set(v___x_1539_, 1, v___x_1547_);
lean_ctor_set(v___x_1539_, 0, v___x_1546_);
v___x_1549_ = v___x_1539_;
goto v_reusejp_1548_;
}
else
{
lean_object* v_reuseFailAlloc_1559_; 
v_reuseFailAlloc_1559_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1559_, 0, v___x_1546_);
lean_ctor_set(v_reuseFailAlloc_1559_, 1, v___x_1547_);
v___x_1549_ = v_reuseFailAlloc_1559_;
goto v_reusejp_1548_;
}
v_reusejp_1548_:
{
lean_object* v___x_1550_; lean_object* v_a_1551_; lean_object* v___x_1553_; uint8_t v_isShared_1554_; uint8_t v_isSharedCheck_1558_; 
v___x_1550_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg(v___x_1549_, v___y_1526_, v___y_1517_, v___y_1525_, v___y_1528_);
v_a_1551_ = lean_ctor_get(v___x_1550_, 0);
v_isSharedCheck_1558_ = !lean_is_exclusive(v___x_1550_);
if (v_isSharedCheck_1558_ == 0)
{
v___x_1553_ = v___x_1550_;
v_isShared_1554_ = v_isSharedCheck_1558_;
goto v_resetjp_1552_;
}
else
{
lean_inc(v_a_1551_);
lean_dec(v___x_1550_);
v___x_1553_ = lean_box(0);
v_isShared_1554_ = v_isSharedCheck_1558_;
goto v_resetjp_1552_;
}
v_resetjp_1552_:
{
lean_object* v___x_1556_; 
if (v_isShared_1554_ == 0)
{
v___x_1556_ = v___x_1553_;
goto v_reusejp_1555_;
}
else
{
lean_object* v_reuseFailAlloc_1557_; 
v_reuseFailAlloc_1557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1557_, 0, v_a_1551_);
v___x_1556_ = v_reuseFailAlloc_1557_;
goto v_reusejp_1555_;
}
v_reusejp_1555_:
{
return v___x_1556_;
}
}
}
}
}
else
{
lean_object* v_subgoals_1560_; lean_object* v_idx_1561_; lean_object* v_remaining_1562_; uint8_t v___x_1563_; 
v_subgoals_1560_ = lean_ctor_get(v___x_1541_, 0);
lean_inc_ref(v_subgoals_1560_);
v_idx_1561_ = lean_ctor_get(v___x_1541_, 1);
lean_inc(v_idx_1561_);
v_remaining_1562_ = lean_ctor_get(v___x_1541_, 2);
lean_inc(v_remaining_1562_);
lean_dec_ref_known(v___x_1541_, 3);
v___x_1563_ = lean_nat_dec_eq(v_idx_1561_, v___x_1497_);
if (v___x_1563_ == 0)
{
lean_object* v___x_1564_; 
lean_dec_ref(v___y_1523_);
v___x_1564_ = l_List_getLast_x3f___redArg(v_remaining_1562_);
lean_dec(v_remaining_1562_);
if (lean_obj_tag(v___x_1564_) == 1)
{
lean_object* v_val_1565_; lean_object* v___x_1567_; uint8_t v_isShared_1568_; uint8_t v_isSharedCheck_1596_; 
lean_dec_ref(v_subgoals_1560_);
lean_dec(v_fst_1537_);
v_val_1565_ = lean_ctor_get(v___x_1564_, 0);
v_isSharedCheck_1596_ = !lean_is_exclusive(v___x_1564_);
if (v_isSharedCheck_1596_ == 0)
{
v___x_1567_ = v___x_1564_;
v_isShared_1568_ = v_isSharedCheck_1596_;
goto v_resetjp_1566_;
}
else
{
lean_inc(v_val_1565_);
lean_dec(v___x_1564_);
v___x_1567_ = lean_box(0);
v_isShared_1568_ = v_isSharedCheck_1596_;
goto v_resetjp_1566_;
}
v_resetjp_1566_:
{
lean_object* v_fst_1569_; lean_object* v___x_1571_; uint8_t v_isShared_1572_; uint8_t v_isSharedCheck_1594_; 
v_fst_1569_ = lean_ctor_get(v_val_1565_, 0);
v_isSharedCheck_1594_ = !lean_is_exclusive(v_val_1565_);
if (v_isSharedCheck_1594_ == 0)
{
lean_object* v_unused_1595_; 
v_unused_1595_ = lean_ctor_get(v_val_1565_, 1);
lean_dec(v_unused_1595_);
v___x_1571_ = v_val_1565_;
v_isShared_1572_ = v_isSharedCheck_1594_;
goto v_resetjp_1570_;
}
else
{
lean_inc(v_fst_1569_);
lean_dec(v_val_1565_);
v___x_1571_ = lean_box(0);
v_isShared_1572_ = v_isSharedCheck_1594_;
goto v_resetjp_1570_;
}
v_resetjp_1570_:
{
lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1576_; 
v___x_1573_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__10, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__10_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__10);
v___x_1574_ = l_Nat_reprFast(v_idx_1561_);
if (v_isShared_1568_ == 0)
{
lean_ctor_set_tag(v___x_1567_, 3);
lean_ctor_set(v___x_1567_, 0, v___x_1574_);
v___x_1576_ = v___x_1567_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1593_; 
v_reuseFailAlloc_1593_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1593_, 0, v___x_1574_);
v___x_1576_ = v_reuseFailAlloc_1593_;
goto v_reusejp_1575_;
}
v_reusejp_1575_:
{
lean_object* v___x_1577_; lean_object* v___x_1579_; 
v___x_1577_ = l_Lean_MessageData_ofFormat(v___x_1576_);
if (v_isShared_1572_ == 0)
{
lean_ctor_set_tag(v___x_1571_, 7);
lean_ctor_set(v___x_1571_, 1, v___x_1577_);
lean_ctor_set(v___x_1571_, 0, v___x_1573_);
v___x_1579_ = v___x_1571_;
goto v_reusejp_1578_;
}
else
{
lean_object* v_reuseFailAlloc_1592_; 
v_reuseFailAlloc_1592_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1592_, 0, v___x_1573_);
lean_ctor_set(v_reuseFailAlloc_1592_, 1, v___x_1577_);
v___x_1579_ = v_reuseFailAlloc_1592_;
goto v_reusejp_1578_;
}
v_reusejp_1578_:
{
lean_object* v___x_1580_; lean_object* v___x_1582_; 
v___x_1580_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__12, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__12_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__12);
if (v_isShared_1540_ == 0)
{
lean_ctor_set_tag(v___x_1539_, 7);
lean_ctor_set(v___x_1539_, 1, v___x_1580_);
lean_ctor_set(v___x_1539_, 0, v___x_1579_);
v___x_1582_ = v___x_1539_;
goto v_reusejp_1581_;
}
else
{
lean_object* v_reuseFailAlloc_1591_; 
v_reuseFailAlloc_1591_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1591_, 0, v___x_1579_);
lean_ctor_set(v_reuseFailAlloc_1591_, 1, v___x_1580_);
v___x_1582_ = v_reuseFailAlloc_1591_;
goto v_reusejp_1581_;
}
v_reusejp_1581_:
{
lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; 
v___x_1583_ = lean_nat_add(v_fst_1569_, v___x_1498_);
lean_dec(v_fst_1569_);
v___x_1584_ = l_Nat_reprFast(v___x_1583_);
v___x_1585_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1585_, 0, v___x_1584_);
v___x_1586_ = l_Lean_MessageData_ofFormat(v___x_1585_);
v___x_1587_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1587_, 0, v___x_1582_);
lean_ctor_set(v___x_1587_, 1, v___x_1586_);
v___x_1588_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__14, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__14_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__14);
v___x_1589_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1589_, 0, v___x_1587_);
lean_ctor_set(v___x_1589_, 1, v___x_1588_);
v___x_1590_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg(v___x_1589_, v___y_1526_, v___y_1517_, v___y_1525_, v___y_1528_);
return v___x_1590_;
}
}
}
}
}
}
else
{
lean_dec(v___x_1564_);
lean_dec(v_idx_1561_);
lean_del_object(v___x_1539_);
v___y_1500_ = v_fst_1537_;
v___y_1501_ = v_subgoals_1560_;
v___y_1502_ = v___y_1527_;
v___y_1503_ = v___y_1516_;
v___y_1504_ = v___y_1519_;
v___y_1505_ = v___y_1521_;
v___y_1506_ = v___y_1526_;
v___y_1507_ = v___y_1517_;
v___y_1508_ = v___y_1525_;
v___y_1509_ = v___y_1528_;
goto v___jp_1499_;
}
}
else
{
lean_object* v_expr_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1601_; 
lean_dec(v_remaining_1562_);
lean_dec(v_idx_1561_);
lean_dec_ref(v_subgoals_1560_);
lean_dec(v_fst_1537_);
v_expr_1597_ = lean_ctor_get(v___y_1523_, 2);
lean_inc_ref(v_expr_1597_);
lean_dec_ref(v___y_1523_);
v___x_1598_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__8, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__8_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__8);
v___x_1599_ = l_Lean_indentExpr(v_expr_1597_);
if (v_isShared_1540_ == 0)
{
lean_ctor_set_tag(v___x_1539_, 7);
lean_ctor_set(v___x_1539_, 1, v___x_1599_);
lean_ctor_set(v___x_1539_, 0, v___x_1598_);
v___x_1601_ = v___x_1539_;
goto v_reusejp_1600_;
}
else
{
lean_object* v_reuseFailAlloc_1611_; 
v_reuseFailAlloc_1611_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v___x_1598_);
lean_ctor_set(v_reuseFailAlloc_1611_, 1, v___x_1599_);
v___x_1601_ = v_reuseFailAlloc_1611_;
goto v_reusejp_1600_;
}
v_reusejp_1600_:
{
lean_object* v___x_1602_; lean_object* v_a_1603_; lean_object* v___x_1605_; uint8_t v_isShared_1606_; uint8_t v_isSharedCheck_1610_; 
v___x_1602_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg(v___x_1601_, v___y_1526_, v___y_1517_, v___y_1525_, v___y_1528_);
v_a_1603_ = lean_ctor_get(v___x_1602_, 0);
v_isSharedCheck_1610_ = !lean_is_exclusive(v___x_1602_);
if (v_isSharedCheck_1610_ == 0)
{
v___x_1605_ = v___x_1602_;
v_isShared_1606_ = v_isSharedCheck_1610_;
goto v_resetjp_1604_;
}
else
{
lean_inc(v_a_1603_);
lean_dec(v___x_1602_);
v___x_1605_ = lean_box(0);
v_isShared_1606_ = v_isSharedCheck_1610_;
goto v_resetjp_1604_;
}
v_resetjp_1604_:
{
lean_object* v___x_1608_; 
if (v_isShared_1606_ == 0)
{
v___x_1608_ = v___x_1605_;
goto v_reusejp_1607_;
}
else
{
lean_object* v_reuseFailAlloc_1609_; 
v_reuseFailAlloc_1609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1609_, 0, v_a_1603_);
v___x_1608_ = v_reuseFailAlloc_1609_;
goto v_reusejp_1607_;
}
v_reusejp_1607_:
{
return v___x_1608_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1614_; lean_object* v___x_1616_; uint8_t v_isShared_1617_; uint8_t v_isSharedCheck_1621_; 
lean_dec_ref(v___y_1523_);
lean_dec(v___y_1518_);
v_a_1614_ = lean_ctor_get(v___x_1535_, 0);
v_isSharedCheck_1621_ = !lean_is_exclusive(v___x_1535_);
if (v_isSharedCheck_1621_ == 0)
{
v___x_1616_ = v___x_1535_;
v_isShared_1617_ = v_isSharedCheck_1621_;
goto v_resetjp_1615_;
}
else
{
lean_inc(v_a_1614_);
lean_dec(v___x_1535_);
v___x_1616_ = lean_box(0);
v_isShared_1617_ = v_isSharedCheck_1621_;
goto v_resetjp_1615_;
}
v_resetjp_1615_:
{
lean_object* v___x_1619_; 
if (v_isShared_1617_ == 0)
{
v___x_1619_ = v___x_1616_;
goto v_reusejp_1618_;
}
else
{
lean_object* v_reuseFailAlloc_1620_; 
v_reuseFailAlloc_1620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1620_, 0, v_a_1614_);
v___x_1619_ = v_reuseFailAlloc_1620_;
goto v_reusejp_1618_;
}
v_reusejp_1618_:
{
return v___x_1619_;
}
}
}
}
v___jp_1622_:
{
lean_object* v___x_1637_; lean_object* v___x_1638_; 
lean_inc_ref(v_occs_1628_);
v___x_1637_ = lean_st_mk_ref(v_occs_1628_);
v___x_1638_ = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_getContext___redArg(v___y_1633_, v___y_1635_, v___y_1636_);
if (lean_obj_tag(v___x_1638_) == 0)
{
if (lean_obj_tag(v_occs_1628_) == 0)
{
lean_object* v_a_1639_; 
lean_dec_ref_known(v_occs_1628_, 1);
v_a_1639_ = lean_ctor_get(v___x_1638_, 0);
lean_inc(v_a_1639_);
lean_dec_ref_known(v___x_1638_, 1);
v___y_1515_ = v___y_1623_;
v___y_1516_ = v___y_1630_;
v___y_1517_ = v___y_1634_;
v___y_1518_ = v___x_1637_;
v___y_1519_ = v___y_1631_;
v___y_1520_ = v___y_1625_;
v___y_1521_ = v___y_1632_;
v___y_1522_ = v_a_1639_;
v___y_1523_ = v___y_1626_;
v___y_1524_ = v___y_1624_;
v___y_1525_ = v___y_1635_;
v___y_1526_ = v___y_1633_;
v___y_1527_ = v___y_1629_;
v___y_1528_ = v___y_1636_;
v___y_1529_ = v___y_1627_;
v___y_1530_ = v___x_1390_;
goto v___jp_1514_;
}
else
{
lean_object* v_a_1640_; uint8_t v___x_1641_; 
lean_dec_ref(v_occs_1628_);
v_a_1640_ = lean_ctor_get(v___x_1638_, 0);
lean_inc(v_a_1640_);
lean_dec_ref_known(v___x_1638_, 1);
v___x_1641_ = 0;
v___y_1515_ = v___y_1623_;
v___y_1516_ = v___y_1630_;
v___y_1517_ = v___y_1634_;
v___y_1518_ = v___x_1637_;
v___y_1519_ = v___y_1631_;
v___y_1520_ = v___y_1625_;
v___y_1521_ = v___y_1632_;
v___y_1522_ = v_a_1640_;
v___y_1523_ = v___y_1626_;
v___y_1524_ = v___y_1624_;
v___y_1525_ = v___y_1635_;
v___y_1526_ = v___y_1633_;
v___y_1527_ = v___y_1629_;
v___y_1528_ = v___y_1636_;
v___y_1529_ = v___y_1627_;
v___y_1530_ = v___x_1641_;
goto v___jp_1514_;
}
}
else
{
lean_object* v_a_1642_; lean_object* v___x_1644_; uint8_t v_isShared_1645_; uint8_t v_isSharedCheck_1649_; 
lean_dec(v___x_1637_);
lean_dec_ref(v_occs_1628_);
lean_dec_ref(v___y_1627_);
lean_dec_ref(v___y_1626_);
lean_dec_ref(v___y_1624_);
lean_dec_ref(v___f_1389_);
v_a_1642_ = lean_ctor_get(v___x_1638_, 0);
v_isSharedCheck_1649_ = !lean_is_exclusive(v___x_1638_);
if (v_isSharedCheck_1649_ == 0)
{
v___x_1644_ = v___x_1638_;
v_isShared_1645_ = v_isSharedCheck_1649_;
goto v_resetjp_1643_;
}
else
{
lean_inc(v_a_1642_);
lean_dec(v___x_1638_);
v___x_1644_ = lean_box(0);
v_isShared_1645_ = v_isSharedCheck_1649_;
goto v_resetjp_1643_;
}
v_resetjp_1643_:
{
lean_object* v___x_1647_; 
if (v_isShared_1645_ == 0)
{
v___x_1647_ = v___x_1644_;
goto v_reusejp_1646_;
}
else
{
lean_object* v_reuseFailAlloc_1648_; 
v_reuseFailAlloc_1648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1648_, 0, v_a_1642_);
v___x_1647_ = v_reuseFailAlloc_1648_;
goto v_reusejp_1646_;
}
v_reusejp_1646_:
{
return v___x_1647_;
}
}
}
}
v___jp_1650_:
{
lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; 
v___x_1665_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__15));
v___x_1666_ = lean_array_to_list(v___y_1653_);
v___x_1667_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1667_, 0, v___x_1665_);
lean_ctor_set(v___x_1667_, 1, v___x_1497_);
lean_ctor_set(v___x_1667_, 2, v___x_1666_);
v___y_1623_ = v___y_1651_;
v___y_1624_ = v___y_1652_;
v___y_1625_ = v___y_1654_;
v___y_1626_ = v___y_1655_;
v___y_1627_ = v___y_1656_;
v_occs_1628_ = v___x_1667_;
v___y_1629_ = v___y_1657_;
v___y_1630_ = v___y_1658_;
v___y_1631_ = v___y_1659_;
v___y_1632_ = v___y_1660_;
v___y_1633_ = v___y_1661_;
v___y_1634_ = v___y_1662_;
v___y_1635_ = v___y_1663_;
v___y_1636_ = v___y_1664_;
goto v___jp_1622_;
}
v___jp_1668_:
{
uint8_t v___x_1683_; 
v___x_1683_ = l_Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8(v___y_1682_);
if (v___x_1683_ == 0)
{
lean_object* v___x_1684_; lean_object* v___x_1685_; 
lean_dec_ref(v___y_1682_);
lean_dec_ref(v___y_1681_);
lean_dec_ref(v___y_1678_);
lean_dec_ref(v___y_1676_);
lean_dec_ref(v___f_1389_);
v___x_1684_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__17, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__17_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__17);
v___x_1685_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg(v___x_1684_, v___y_1672_, v___y_1675_, v___y_1677_, v___y_1679_);
return v___x_1685_;
}
else
{
v___y_1651_ = v___y_1669_;
v___y_1652_ = v___y_1678_;
v___y_1653_ = v___y_1682_;
v___y_1654_ = v___y_1674_;
v___y_1655_ = v___y_1676_;
v___y_1656_ = v___y_1681_;
v___y_1657_ = v___y_1680_;
v___y_1658_ = v___y_1670_;
v___y_1659_ = v___y_1671_;
v___y_1660_ = v___y_1673_;
v___y_1661_ = v___y_1672_;
v___y_1662_ = v___y_1675_;
v___y_1663_ = v___y_1677_;
v___y_1664_ = v___y_1679_;
goto v___jp_1650_;
}
}
v___jp_1686_:
{
lean_object* v___x_1704_; 
v___x_1704_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg(v___y_1692_, v___y_1691_, v___y_1702_, v___y_1703_);
lean_dec(v___y_1703_);
lean_dec(v___y_1692_);
v___y_1669_ = v___y_1687_;
v___y_1670_ = v___y_1688_;
v___y_1671_ = v___y_1689_;
v___y_1672_ = v___y_1690_;
v___y_1673_ = v___y_1693_;
v___y_1674_ = v___y_1694_;
v___y_1675_ = v___y_1695_;
v___y_1676_ = v___y_1696_;
v___y_1677_ = v___y_1697_;
v___y_1678_ = v___y_1698_;
v___y_1679_ = v___y_1699_;
v___y_1680_ = v___y_1700_;
v___y_1681_ = v___y_1701_;
v___y_1682_ = v___x_1704_;
goto v___jp_1668_;
}
v___jp_1705_:
{
uint8_t v___x_1723_; 
v___x_1723_ = lean_nat_dec_le(v___y_1722_, v___y_1714_);
if (v___x_1723_ == 0)
{
lean_dec(v___y_1714_);
lean_inc(v___y_1722_);
v___y_1687_ = v___y_1706_;
v___y_1688_ = v___y_1707_;
v___y_1689_ = v___y_1708_;
v___y_1690_ = v___y_1709_;
v___y_1691_ = v___y_1710_;
v___y_1692_ = v___y_1711_;
v___y_1693_ = v___y_1712_;
v___y_1694_ = v___y_1713_;
v___y_1695_ = v___y_1715_;
v___y_1696_ = v___y_1716_;
v___y_1697_ = v___y_1717_;
v___y_1698_ = v___y_1718_;
v___y_1699_ = v___y_1719_;
v___y_1700_ = v___y_1720_;
v___y_1701_ = v___y_1721_;
v___y_1702_ = v___y_1722_;
v___y_1703_ = v___y_1722_;
goto v___jp_1686_;
}
else
{
v___y_1687_ = v___y_1706_;
v___y_1688_ = v___y_1707_;
v___y_1689_ = v___y_1708_;
v___y_1690_ = v___y_1709_;
v___y_1691_ = v___y_1710_;
v___y_1692_ = v___y_1711_;
v___y_1693_ = v___y_1712_;
v___y_1694_ = v___y_1713_;
v___y_1695_ = v___y_1715_;
v___y_1696_ = v___y_1716_;
v___y_1697_ = v___y_1717_;
v___y_1698_ = v___y_1718_;
v___y_1699_ = v___y_1719_;
v___y_1700_ = v___y_1720_;
v___y_1701_ = v___y_1721_;
v___y_1702_ = v___y_1722_;
v___y_1703_ = v___y_1714_;
goto v___jp_1686_;
}
}
v___jp_1724_:
{
lean_object* v_declName_x3f_1734_; lean_object* v_macroStack_1735_; uint8_t v_mayPostpone_1736_; uint8_t v_errToSorry_1737_; lean_object* v_autoBoundImplicitContext_1738_; lean_object* v_autoBoundImplicitForbidden_1739_; lean_object* v_sectionVars_1740_; lean_object* v_sectionFVars_1741_; uint8_t v_implicitLambda_1742_; uint8_t v_heedElabAsElim_1743_; uint8_t v_isNoncomputableSection_1744_; uint8_t v_isMetaSection_1745_; uint8_t v_inPattern_1746_; lean_object* v_tacSnap_x3f_1747_; uint8_t v_saveRecAppSyntax_1748_; uint8_t v_holesAsSyntheticOpaque_1749_; uint8_t v_checkDeprecated_1750_; lean_object* v_fixedTermElabs_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___f_1756_; lean_object* v___f_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; 
v_declName_x3f_1734_ = lean_ctor_get(v___y_1728_, 0);
v_macroStack_1735_ = lean_ctor_get(v___y_1728_, 1);
v_mayPostpone_1736_ = lean_ctor_get_uint8(v___y_1728_, sizeof(void*)*8);
v_errToSorry_1737_ = lean_ctor_get_uint8(v___y_1728_, sizeof(void*)*8 + 1);
v_autoBoundImplicitContext_1738_ = lean_ctor_get(v___y_1728_, 2);
v_autoBoundImplicitForbidden_1739_ = lean_ctor_get(v___y_1728_, 3);
v_sectionVars_1740_ = lean_ctor_get(v___y_1728_, 4);
v_sectionFVars_1741_ = lean_ctor_get(v___y_1728_, 5);
v_implicitLambda_1742_ = lean_ctor_get_uint8(v___y_1728_, sizeof(void*)*8 + 2);
v_heedElabAsElim_1743_ = lean_ctor_get_uint8(v___y_1728_, sizeof(void*)*8 + 3);
v_isNoncomputableSection_1744_ = lean_ctor_get_uint8(v___y_1728_, sizeof(void*)*8 + 4);
v_isMetaSection_1745_ = lean_ctor_get_uint8(v___y_1728_, sizeof(void*)*8 + 5);
v_inPattern_1746_ = lean_ctor_get_uint8(v___y_1728_, sizeof(void*)*8 + 7);
v_tacSnap_x3f_1747_ = lean_ctor_get(v___y_1728_, 6);
v_saveRecAppSyntax_1748_ = lean_ctor_get_uint8(v___y_1728_, sizeof(void*)*8 + 8);
v_holesAsSyntheticOpaque_1749_ = lean_ctor_get_uint8(v___y_1728_, sizeof(void*)*8 + 9);
v_checkDeprecated_1750_ = lean_ctor_get_uint8(v___y_1728_, sizeof(void*)*8 + 10);
v_fixedTermElabs_1751_ = lean_ctor_get(v___y_1728_, 7);
v___x_1752_ = lean_unsigned_to_nat(2u);
v___x_1753_ = l_Lean_Syntax_getArg(v_stx_1391_, v___x_1752_);
v___x_1754_ = lean_box(0);
v___x_1755_ = lean_box(v___x_1390_);
lean_inc(v___x_1753_);
v___f_1756_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__1___boxed), 10, 3);
lean_closure_set(v___f_1756_, 0, v___x_1753_);
lean_closure_set(v___f_1756_, 1, v___x_1754_);
lean_closure_set(v___f_1756_, 2, v___x_1755_);
v___f_1757_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__2___boxed), 9, 2);
lean_closure_set(v___f_1757_, 0, v___x_1753_);
lean_closure_set(v___f_1757_, 1, v___f_1756_);
lean_inc_ref(v_fixedTermElabs_1751_);
lean_inc(v_tacSnap_x3f_1747_);
lean_inc(v_sectionFVars_1741_);
lean_inc(v_sectionVars_1740_);
lean_inc_ref(v_autoBoundImplicitForbidden_1739_);
lean_inc(v_autoBoundImplicitContext_1738_);
lean_inc(v_macroStack_1735_);
lean_inc(v_declName_x3f_1734_);
v___x_1758_ = lean_alloc_ctor(0, 8, 11);
lean_ctor_set(v___x_1758_, 0, v_declName_x3f_1734_);
lean_ctor_set(v___x_1758_, 1, v_macroStack_1735_);
lean_ctor_set(v___x_1758_, 2, v_autoBoundImplicitContext_1738_);
lean_ctor_set(v___x_1758_, 3, v_autoBoundImplicitForbidden_1739_);
lean_ctor_set(v___x_1758_, 4, v_sectionVars_1740_);
lean_ctor_set(v___x_1758_, 5, v_sectionFVars_1741_);
lean_ctor_set(v___x_1758_, 6, v_tacSnap_x3f_1747_);
lean_ctor_set(v___x_1758_, 7, v_fixedTermElabs_1751_);
lean_ctor_set_uint8(v___x_1758_, sizeof(void*)*8, v_mayPostpone_1736_);
lean_ctor_set_uint8(v___x_1758_, sizeof(void*)*8 + 1, v_errToSorry_1737_);
lean_ctor_set_uint8(v___x_1758_, sizeof(void*)*8 + 2, v_implicitLambda_1742_);
lean_ctor_set_uint8(v___x_1758_, sizeof(void*)*8 + 3, v_heedElabAsElim_1743_);
lean_ctor_set_uint8(v___x_1758_, sizeof(void*)*8 + 4, v_isNoncomputableSection_1744_);
lean_ctor_set_uint8(v___x_1758_, sizeof(void*)*8 + 5, v_isMetaSection_1745_);
lean_ctor_set_uint8(v___x_1758_, sizeof(void*)*8 + 6, v___x_1390_);
lean_ctor_set_uint8(v___x_1758_, sizeof(void*)*8 + 7, v_inPattern_1746_);
lean_ctor_set_uint8(v___x_1758_, sizeof(void*)*8 + 8, v_saveRecAppSyntax_1748_);
lean_ctor_set_uint8(v___x_1758_, sizeof(void*)*8 + 9, v_holesAsSyntheticOpaque_1749_);
lean_ctor_set_uint8(v___x_1758_, sizeof(void*)*8 + 10, v_checkDeprecated_1750_);
v___x_1759_ = l_Lean_Elab_Term_withoutModifyingElabMetaStateWithInfo___redArg(v___f_1757_, v___x_1758_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_);
lean_dec_ref_known(v___x_1758_, 8);
if (lean_obj_tag(v___x_1759_) == 0)
{
lean_object* v_a_1760_; lean_object* v___x_1761_; 
v_a_1760_ = lean_ctor_get(v___x_1759_, 0);
lean_inc(v_a_1760_);
lean_dec_ref_known(v___x_1759_, 1);
v___x_1761_ = l_Lean_Elab_Tactic_Conv_getLhs___redArg(v___y_1727_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_);
if (lean_obj_tag(v___x_1761_) == 0)
{
lean_object* v_a_1762_; lean_object* v___x_1763_; lean_object* v___f_1764_; lean_object* v___f_1765_; lean_object* v___f_1766_; 
v_a_1762_ = lean_ctor_get(v___x_1761_, 0);
lean_inc(v_a_1762_);
lean_dec_ref_known(v___x_1761_, 1);
v___x_1763_ = lean_box(v___x_1390_);
v___f_1764_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__3___boxed), 11, 2);
lean_closure_set(v___f_1764_, 0, v___x_1754_);
lean_closure_set(v___f_1764_, 1, v___x_1763_);
v___f_1765_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__18));
v___f_1766_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__19));
if (lean_obj_tag(v_occs_1725_) == 0)
{
lean_object* v___x_1767_; 
lean_dec_ref(v___x_1395_);
lean_dec_ref(v___x_1394_);
lean_dec_ref(v___x_1393_);
lean_dec_ref(v___x_1392_);
v___x_1767_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__22));
v___y_1623_ = v___f_1766_;
v___y_1624_ = v_a_1762_;
v___y_1625_ = v___f_1765_;
v___y_1626_ = v_a_1760_;
v___y_1627_ = v___f_1764_;
v_occs_1628_ = v___x_1767_;
v___y_1629_ = v___y_1726_;
v___y_1630_ = v___y_1727_;
v___y_1631_ = v___y_1728_;
v___y_1632_ = v___y_1729_;
v___y_1633_ = v___y_1730_;
v___y_1634_ = v___y_1731_;
v___y_1635_ = v___y_1732_;
v___y_1636_ = v___y_1733_;
goto v___jp_1622_;
}
else
{
lean_object* v_val_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; uint8_t v___x_1771_; 
v_val_1768_ = lean_ctor_get(v_occs_1725_, 0);
lean_inc_n(v_val_1768_, 2);
lean_dec_ref_known(v_occs_1725_, 1);
v___x_1769_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__23));
lean_inc_ref(v___x_1395_);
lean_inc_ref(v___x_1394_);
lean_inc_ref(v___x_1393_);
lean_inc_ref(v___x_1392_);
v___x_1770_ = l_Lean_Name_mkStr5(v___x_1392_, v___x_1393_, v___x_1394_, v___x_1395_, v___x_1769_);
v___x_1771_ = l_Lean_Syntax_isOfKind(v_val_1768_, v___x_1770_);
lean_dec(v___x_1770_);
if (v___x_1771_ == 0)
{
lean_object* v___x_1772_; lean_object* v___x_1773_; uint8_t v___x_1774_; 
v___x_1772_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__24));
v___x_1773_ = l_Lean_Name_mkStr5(v___x_1392_, v___x_1393_, v___x_1394_, v___x_1395_, v___x_1772_);
lean_inc(v_val_1768_);
v___x_1774_ = l_Lean_Syntax_isOfKind(v_val_1768_, v___x_1773_);
lean_dec(v___x_1773_);
if (v___x_1774_ == 0)
{
lean_object* v___x_1775_; lean_object* v_a_1776_; lean_object* v___x_1778_; uint8_t v_isShared_1779_; uint8_t v_isSharedCheck_1783_; 
lean_dec(v_val_1768_);
lean_dec_ref(v___f_1764_);
lean_dec(v_a_1762_);
lean_dec(v_a_1760_);
lean_dec_ref(v___f_1389_);
v___x_1775_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg();
v_a_1776_ = lean_ctor_get(v___x_1775_, 0);
v_isSharedCheck_1783_ = !lean_is_exclusive(v___x_1775_);
if (v_isSharedCheck_1783_ == 0)
{
v___x_1778_ = v___x_1775_;
v_isShared_1779_ = v_isSharedCheck_1783_;
goto v_resetjp_1777_;
}
else
{
lean_inc(v_a_1776_);
lean_dec(v___x_1775_);
v___x_1778_ = lean_box(0);
v_isShared_1779_ = v_isSharedCheck_1783_;
goto v_resetjp_1777_;
}
v_resetjp_1777_:
{
lean_object* v___x_1781_; 
if (v_isShared_1779_ == 0)
{
v___x_1781_ = v___x_1778_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1782_; 
v_reuseFailAlloc_1782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1782_, 0, v_a_1776_);
v___x_1781_ = v_reuseFailAlloc_1782_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
return v___x_1781_;
}
}
}
else
{
lean_object* v___x_1784_; lean_object* v___x_1785_; size_t v_sz_1786_; size_t v___x_1787_; lean_object* v___x_1788_; 
v___x_1784_ = l_Lean_Syntax_getArg(v_val_1768_, v___x_1497_);
lean_dec(v_val_1768_);
v___x_1785_ = l_Lean_Syntax_getArgs(v___x_1784_);
lean_dec(v___x_1784_);
v_sz_1786_ = lean_array_size(v___x_1785_);
v___x_1787_ = ((size_t)0ULL);
v___x_1788_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg(v_sz_1786_, v___x_1787_, v___x_1785_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_);
if (lean_obj_tag(v___x_1788_) == 0)
{
lean_object* v_a_1789_; lean_object* v___x_1790_; uint8_t v___x_1791_; 
v_a_1789_ = lean_ctor_get(v___x_1788_, 0);
lean_inc(v_a_1789_);
lean_dec_ref_known(v___x_1788_, 1);
v___x_1790_ = lean_array_get_size(v_a_1789_);
v___x_1791_ = lean_nat_dec_eq(v___x_1790_, v___x_1497_);
if (v___x_1791_ == 0)
{
lean_object* v___x_1792_; uint8_t v___x_1793_; 
v___x_1792_ = lean_nat_sub(v___x_1790_, v___x_1498_);
v___x_1793_ = lean_nat_dec_le(v___x_1497_, v___x_1792_);
if (v___x_1793_ == 0)
{
lean_inc(v___x_1792_);
v___y_1706_ = v___f_1766_;
v___y_1707_ = v___y_1727_;
v___y_1708_ = v___y_1728_;
v___y_1709_ = v___y_1730_;
v___y_1710_ = v_a_1789_;
v___y_1711_ = v___x_1790_;
v___y_1712_ = v___y_1729_;
v___y_1713_ = v___f_1765_;
v___y_1714_ = v___x_1792_;
v___y_1715_ = v___y_1731_;
v___y_1716_ = v_a_1760_;
v___y_1717_ = v___y_1732_;
v___y_1718_ = v_a_1762_;
v___y_1719_ = v___y_1733_;
v___y_1720_ = v___y_1726_;
v___y_1721_ = v___f_1764_;
v___y_1722_ = v___x_1792_;
goto v___jp_1705_;
}
else
{
v___y_1706_ = v___f_1766_;
v___y_1707_ = v___y_1727_;
v___y_1708_ = v___y_1728_;
v___y_1709_ = v___y_1730_;
v___y_1710_ = v_a_1789_;
v___y_1711_ = v___x_1790_;
v___y_1712_ = v___y_1729_;
v___y_1713_ = v___f_1765_;
v___y_1714_ = v___x_1792_;
v___y_1715_ = v___y_1731_;
v___y_1716_ = v_a_1760_;
v___y_1717_ = v___y_1732_;
v___y_1718_ = v_a_1762_;
v___y_1719_ = v___y_1733_;
v___y_1720_ = v___y_1726_;
v___y_1721_ = v___f_1764_;
v___y_1722_ = v___x_1497_;
goto v___jp_1705_;
}
}
else
{
v___y_1669_ = v___f_1766_;
v___y_1670_ = v___y_1727_;
v___y_1671_ = v___y_1728_;
v___y_1672_ = v___y_1730_;
v___y_1673_ = v___y_1729_;
v___y_1674_ = v___f_1765_;
v___y_1675_ = v___y_1731_;
v___y_1676_ = v_a_1760_;
v___y_1677_ = v___y_1732_;
v___y_1678_ = v_a_1762_;
v___y_1679_ = v___y_1733_;
v___y_1680_ = v___y_1726_;
v___y_1681_ = v___f_1764_;
v___y_1682_ = v_a_1789_;
goto v___jp_1668_;
}
}
else
{
lean_object* v_a_1794_; lean_object* v___x_1796_; uint8_t v_isShared_1797_; uint8_t v_isSharedCheck_1801_; 
lean_dec_ref(v___f_1764_);
lean_dec(v_a_1762_);
lean_dec(v_a_1760_);
lean_dec_ref(v___f_1389_);
v_a_1794_ = lean_ctor_get(v___x_1788_, 0);
v_isSharedCheck_1801_ = !lean_is_exclusive(v___x_1788_);
if (v_isSharedCheck_1801_ == 0)
{
v___x_1796_ = v___x_1788_;
v_isShared_1797_ = v_isSharedCheck_1801_;
goto v_resetjp_1795_;
}
else
{
lean_inc(v_a_1794_);
lean_dec(v___x_1788_);
v___x_1796_ = lean_box(0);
v_isShared_1797_ = v_isSharedCheck_1801_;
goto v_resetjp_1795_;
}
v_resetjp_1795_:
{
lean_object* v___x_1799_; 
if (v_isShared_1797_ == 0)
{
v___x_1799_ = v___x_1796_;
goto v_reusejp_1798_;
}
else
{
lean_object* v_reuseFailAlloc_1800_; 
v_reuseFailAlloc_1800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1800_, 0, v_a_1794_);
v___x_1799_ = v_reuseFailAlloc_1800_;
goto v_reusejp_1798_;
}
v_reusejp_1798_:
{
return v___x_1799_;
}
}
}
}
}
else
{
lean_object* v___x_1802_; 
lean_dec(v_val_1768_);
lean_dec_ref(v___x_1395_);
lean_dec_ref(v___x_1394_);
lean_dec_ref(v___x_1393_);
lean_dec_ref(v___x_1392_);
v___x_1802_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__26));
v___y_1623_ = v___f_1766_;
v___y_1624_ = v_a_1762_;
v___y_1625_ = v___f_1765_;
v___y_1626_ = v_a_1760_;
v___y_1627_ = v___f_1764_;
v_occs_1628_ = v___x_1802_;
v___y_1629_ = v___y_1726_;
v___y_1630_ = v___y_1727_;
v___y_1631_ = v___y_1728_;
v___y_1632_ = v___y_1729_;
v___y_1633_ = v___y_1730_;
v___y_1634_ = v___y_1731_;
v___y_1635_ = v___y_1732_;
v___y_1636_ = v___y_1733_;
goto v___jp_1622_;
}
}
}
else
{
lean_object* v_a_1803_; lean_object* v___x_1805_; uint8_t v_isShared_1806_; uint8_t v_isSharedCheck_1810_; 
lean_dec(v_a_1760_);
lean_dec(v_occs_1725_);
lean_dec_ref(v___x_1395_);
lean_dec_ref(v___x_1394_);
lean_dec_ref(v___x_1393_);
lean_dec_ref(v___x_1392_);
lean_dec_ref(v___f_1389_);
v_a_1803_ = lean_ctor_get(v___x_1761_, 0);
v_isSharedCheck_1810_ = !lean_is_exclusive(v___x_1761_);
if (v_isSharedCheck_1810_ == 0)
{
v___x_1805_ = v___x_1761_;
v_isShared_1806_ = v_isSharedCheck_1810_;
goto v_resetjp_1804_;
}
else
{
lean_inc(v_a_1803_);
lean_dec(v___x_1761_);
v___x_1805_ = lean_box(0);
v_isShared_1806_ = v_isSharedCheck_1810_;
goto v_resetjp_1804_;
}
v_resetjp_1804_:
{
lean_object* v___x_1808_; 
if (v_isShared_1806_ == 0)
{
v___x_1808_ = v___x_1805_;
goto v_reusejp_1807_;
}
else
{
lean_object* v_reuseFailAlloc_1809_; 
v_reuseFailAlloc_1809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1809_, 0, v_a_1803_);
v___x_1808_ = v_reuseFailAlloc_1809_;
goto v_reusejp_1807_;
}
v_reusejp_1807_:
{
return v___x_1808_;
}
}
}
}
else
{
lean_object* v_a_1811_; lean_object* v___x_1813_; uint8_t v_isShared_1814_; uint8_t v_isSharedCheck_1818_; 
lean_dec(v_occs_1725_);
lean_dec_ref(v___x_1395_);
lean_dec_ref(v___x_1394_);
lean_dec_ref(v___x_1393_);
lean_dec_ref(v___x_1392_);
lean_dec_ref(v___f_1389_);
v_a_1811_ = lean_ctor_get(v___x_1759_, 0);
v_isSharedCheck_1818_ = !lean_is_exclusive(v___x_1759_);
if (v_isSharedCheck_1818_ == 0)
{
v___x_1813_ = v___x_1759_;
v_isShared_1814_ = v_isSharedCheck_1818_;
goto v_resetjp_1812_;
}
else
{
lean_inc(v_a_1811_);
lean_dec(v___x_1759_);
v___x_1813_ = lean_box(0);
v_isShared_1814_ = v_isSharedCheck_1818_;
goto v_resetjp_1812_;
}
v_resetjp_1812_:
{
lean_object* v___x_1816_; 
if (v_isShared_1814_ == 0)
{
v___x_1816_ = v___x_1813_;
goto v_reusejp_1815_;
}
else
{
lean_object* v_reuseFailAlloc_1817_; 
v_reuseFailAlloc_1817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1817_, 0, v_a_1811_);
v___x_1816_ = v_reuseFailAlloc_1817_;
goto v_reusejp_1815_;
}
v_reusejp_1815_:
{
return v___x_1816_;
}
}
}
}
}
v___jp_1405_:
{
lean_object* v___x_1416_; 
v___x_1416_ = l_Lean_Elab_Tactic_Conv_getRhs___redArg(v___y_1409_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_);
if (lean_obj_tag(v___x_1416_) == 0)
{
lean_object* v_a_1417_; lean_object* v_expr_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; 
v_a_1417_ = lean_ctor_get(v___x_1416_, 0);
lean_inc(v_a_1417_);
lean_dec_ref_known(v___x_1416_, 1);
v_expr_1418_ = lean_ctor_get(v___y_1406_, 0);
v___x_1419_ = l_Lean_Expr_mvarId_x21(v_a_1417_);
lean_dec(v_a_1417_);
lean_inc_ref(v_expr_1418_);
v___x_1420_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3___redArg(v___x_1419_, v_expr_1418_, v___y_1413_);
lean_dec_ref(v___x_1420_);
v___x_1421_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_1409_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_);
if (lean_obj_tag(v___x_1421_) == 0)
{
lean_object* v_a_1422_; lean_object* v___x_1423_; 
v_a_1422_ = lean_ctor_get(v___x_1421_, 0);
lean_inc(v_a_1422_);
lean_dec_ref_known(v___x_1421_, 1);
v___x_1423_ = l_Lean_Meta_Simp_Result_getProof(v___y_1406_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_);
if (lean_obj_tag(v___x_1423_) == 0)
{
lean_object* v_a_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; 
v_a_1424_ = lean_ctor_get(v___x_1423_, 0);
lean_inc(v_a_1424_);
lean_dec_ref_known(v___x_1423_, 1);
v___x_1425_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3___redArg(v_a_1422_, v_a_1424_, v___y_1413_);
lean_dec_ref(v___x_1425_);
v___x_1426_ = lean_array_to_list(v_subgoals_1407_);
v___x_1427_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_1426_, v___y_1409_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_);
return v___x_1427_;
}
else
{
lean_object* v_a_1428_; lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1435_; 
lean_dec(v_a_1422_);
lean_dec_ref(v_subgoals_1407_);
v_a_1428_ = lean_ctor_get(v___x_1423_, 0);
v_isSharedCheck_1435_ = !lean_is_exclusive(v___x_1423_);
if (v_isSharedCheck_1435_ == 0)
{
v___x_1430_ = v___x_1423_;
v_isShared_1431_ = v_isSharedCheck_1435_;
goto v_resetjp_1429_;
}
else
{
lean_inc(v_a_1428_);
lean_dec(v___x_1423_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1435_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
lean_object* v___x_1433_; 
if (v_isShared_1431_ == 0)
{
v___x_1433_ = v___x_1430_;
goto v_reusejp_1432_;
}
else
{
lean_object* v_reuseFailAlloc_1434_; 
v_reuseFailAlloc_1434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1434_, 0, v_a_1428_);
v___x_1433_ = v_reuseFailAlloc_1434_;
goto v_reusejp_1432_;
}
v_reusejp_1432_:
{
return v___x_1433_;
}
}
}
}
else
{
lean_object* v_a_1436_; lean_object* v___x_1438_; uint8_t v_isShared_1439_; uint8_t v_isSharedCheck_1443_; 
lean_dec_ref(v_subgoals_1407_);
lean_dec_ref(v___y_1406_);
v_a_1436_ = lean_ctor_get(v___x_1421_, 0);
v_isSharedCheck_1443_ = !lean_is_exclusive(v___x_1421_);
if (v_isSharedCheck_1443_ == 0)
{
v___x_1438_ = v___x_1421_;
v_isShared_1439_ = v_isSharedCheck_1443_;
goto v_resetjp_1437_;
}
else
{
lean_inc(v_a_1436_);
lean_dec(v___x_1421_);
v___x_1438_ = lean_box(0);
v_isShared_1439_ = v_isSharedCheck_1443_;
goto v_resetjp_1437_;
}
v_resetjp_1437_:
{
lean_object* v___x_1441_; 
if (v_isShared_1439_ == 0)
{
v___x_1441_ = v___x_1438_;
goto v_reusejp_1440_;
}
else
{
lean_object* v_reuseFailAlloc_1442_; 
v_reuseFailAlloc_1442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1442_, 0, v_a_1436_);
v___x_1441_ = v_reuseFailAlloc_1442_;
goto v_reusejp_1440_;
}
v_reusejp_1440_:
{
return v___x_1441_;
}
}
}
}
else
{
lean_object* v_a_1444_; lean_object* v___x_1446_; uint8_t v_isShared_1447_; uint8_t v_isSharedCheck_1451_; 
lean_dec_ref(v_subgoals_1407_);
lean_dec_ref(v___y_1406_);
v_a_1444_ = lean_ctor_get(v___x_1416_, 0);
v_isSharedCheck_1451_ = !lean_is_exclusive(v___x_1416_);
if (v_isSharedCheck_1451_ == 0)
{
v___x_1446_ = v___x_1416_;
v_isShared_1447_ = v_isSharedCheck_1451_;
goto v_resetjp_1445_;
}
else
{
lean_inc(v_a_1444_);
lean_dec(v___x_1416_);
v___x_1446_ = lean_box(0);
v_isShared_1447_ = v_isSharedCheck_1451_;
goto v_resetjp_1445_;
}
v_resetjp_1445_:
{
lean_object* v___x_1449_; 
if (v_isShared_1447_ == 0)
{
v___x_1449_ = v___x_1446_;
goto v_reusejp_1448_;
}
else
{
lean_object* v_reuseFailAlloc_1450_; 
v_reuseFailAlloc_1450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1450_, 0, v_a_1444_);
v___x_1449_ = v_reuseFailAlloc_1450_;
goto v_reusejp_1448_;
}
v_reusejp_1448_:
{
return v___x_1449_;
}
}
}
}
v___jp_1452_:
{
size_t v_sz_1463_; size_t v___x_1464_; lean_object* v___x_1465_; 
v_sz_1463_ = lean_array_size(v___y_1462_);
v___x_1464_ = ((size_t)0ULL);
v___x_1465_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__5(v_sz_1463_, v___x_1464_, v___y_1462_);
v___y_1406_ = v___y_1454_;
v_subgoals_1407_ = v___x_1465_;
v___y_1408_ = v___y_1459_;
v___y_1409_ = v___y_1453_;
v___y_1410_ = v___y_1460_;
v___y_1411_ = v___y_1455_;
v___y_1412_ = v___y_1461_;
v___y_1413_ = v___y_1457_;
v___y_1414_ = v___y_1456_;
v___y_1415_ = v___y_1458_;
goto v___jp_1405_;
}
v___jp_1466_:
{
lean_object* v___x_1480_; 
v___x_1480_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg(v___y_1474_, v___y_1470_, v___y_1476_, v___y_1479_);
lean_dec(v___y_1479_);
lean_dec(v___y_1474_);
v___y_1453_ = v___y_1473_;
v___y_1454_ = v___y_1475_;
v___y_1455_ = v___y_1467_;
v___y_1456_ = v___y_1468_;
v___y_1457_ = v___y_1469_;
v___y_1458_ = v___y_1477_;
v___y_1459_ = v___y_1478_;
v___y_1460_ = v___y_1471_;
v___y_1461_ = v___y_1472_;
v___y_1462_ = v___x_1480_;
goto v___jp_1452_;
}
v___jp_1481_:
{
uint8_t v___x_1495_; 
v___x_1495_ = lean_nat_dec_le(v___y_1494_, v___y_1484_);
if (v___x_1495_ == 0)
{
lean_dec(v___y_1484_);
lean_inc(v___y_1494_);
v___y_1467_ = v___y_1482_;
v___y_1468_ = v___y_1483_;
v___y_1469_ = v___y_1485_;
v___y_1470_ = v___y_1486_;
v___y_1471_ = v___y_1487_;
v___y_1472_ = v___y_1488_;
v___y_1473_ = v___y_1489_;
v___y_1474_ = v___y_1490_;
v___y_1475_ = v___y_1491_;
v___y_1476_ = v___y_1494_;
v___y_1477_ = v___y_1492_;
v___y_1478_ = v___y_1493_;
v___y_1479_ = v___y_1494_;
goto v___jp_1466_;
}
else
{
v___y_1467_ = v___y_1482_;
v___y_1468_ = v___y_1483_;
v___y_1469_ = v___y_1485_;
v___y_1470_ = v___y_1486_;
v___y_1471_ = v___y_1487_;
v___y_1472_ = v___y_1488_;
v___y_1473_ = v___y_1489_;
v___y_1474_ = v___y_1490_;
v___y_1475_ = v___y_1491_;
v___y_1476_ = v___y_1494_;
v___y_1477_ = v___y_1492_;
v___y_1478_ = v___y_1493_;
v___y_1479_ = v___y_1484_;
goto v___jp_1466_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___boxed(lean_object** _args){
lean_object* v___x_1832_ = _args[0];
lean_object* v___f_1833_ = _args[1];
lean_object* v___x_1834_ = _args[2];
lean_object* v_stx_1835_ = _args[3];
lean_object* v___x_1836_ = _args[4];
lean_object* v___x_1837_ = _args[5];
lean_object* v___x_1838_ = _args[6];
lean_object* v___x_1839_ = _args[7];
lean_object* v___y_1840_ = _args[8];
lean_object* v___y_1841_ = _args[9];
lean_object* v___y_1842_ = _args[10];
lean_object* v___y_1843_ = _args[11];
lean_object* v___y_1844_ = _args[12];
lean_object* v___y_1845_ = _args[13];
lean_object* v___y_1846_ = _args[14];
lean_object* v___y_1847_ = _args[15];
lean_object* v___y_1848_ = _args[16];
_start:
{
uint8_t v___x_19446__boxed_1849_; uint8_t v___x_19448__boxed_1850_; lean_object* v_res_1851_; 
v___x_19446__boxed_1849_ = lean_unbox(v___x_1832_);
v___x_19448__boxed_1850_ = lean_unbox(v___x_1834_);
v_res_1851_ = l_Lean_Elab_Tactic_Conv_evalPattern___lam__6(v___x_19446__boxed_1849_, v___f_1833_, v___x_19448__boxed_1850_, v_stx_1835_, v___x_1836_, v___x_1837_, v___x_1838_, v___x_1839_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_, v___y_1847_);
lean_dec(v___y_1847_);
lean_dec_ref(v___y_1846_);
lean_dec(v___y_1845_);
lean_dec_ref(v___y_1844_);
lean_dec(v___y_1843_);
lean_dec_ref(v___y_1842_);
lean_dec(v___y_1841_);
lean_dec_ref(v___y_1840_);
lean_dec(v_stx_1835_);
return v_res_1851_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern(lean_object* v_stx_1864_, lean_object* v_a_1865_, lean_object* v_a_1866_, lean_object* v_a_1867_, lean_object* v_a_1868_, lean_object* v_a_1869_, lean_object* v_a_1870_, lean_object* v_a_1871_, lean_object* v_a_1872_){
_start:
{
lean_object* v___f_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; uint8_t v___x_1880_; uint8_t v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___y_1884_; lean_object* v___x_1885_; 
v___f_1874_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___closed__0));
v___x_1875_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___closed__1));
v___x_1876_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___closed__2));
v___x_1877_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___closed__3));
v___x_1878_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___closed__4));
v___x_1879_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___closed__6));
lean_inc(v_stx_1864_);
v___x_1880_ = l_Lean_Syntax_isOfKind(v_stx_1864_, v___x_1879_);
v___x_1881_ = 1;
v___x_1882_ = lean_box(v___x_1880_);
v___x_1883_ = lean_box(v___x_1881_);
v___y_1884_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___boxed), 17, 8);
lean_closure_set(v___y_1884_, 0, v___x_1882_);
lean_closure_set(v___y_1884_, 1, v___f_1874_);
lean_closure_set(v___y_1884_, 2, v___x_1883_);
lean_closure_set(v___y_1884_, 3, v_stx_1864_);
lean_closure_set(v___y_1884_, 4, v___x_1875_);
lean_closure_set(v___y_1884_, 5, v___x_1876_);
lean_closure_set(v___y_1884_, 6, v___x_1877_);
lean_closure_set(v___y_1884_, 7, v___x_1878_);
v___x_1885_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___y_1884_, v_a_1865_, v_a_1866_, v_a_1867_, v_a_1868_, v_a_1869_, v_a_1870_, v_a_1871_, v_a_1872_);
return v___x_1885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___boxed(lean_object* v_stx_1886_, lean_object* v_a_1887_, lean_object* v_a_1888_, lean_object* v_a_1889_, lean_object* v_a_1890_, lean_object* v_a_1891_, lean_object* v_a_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_){
_start:
{
lean_object* v_res_1896_; 
v_res_1896_ = l_Lean_Elab_Tactic_Conv_evalPattern(v_stx_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_);
lean_dec(v_a_1894_);
lean_dec_ref(v_a_1893_);
lean_dec(v_a_1892_);
lean_dec_ref(v_a_1891_);
lean_dec(v_a_1890_);
lean_dec_ref(v_a_1889_);
lean_dec(v_a_1888_);
lean_dec_ref(v_a_1887_);
return v_res_1896_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1(lean_object* v_00_u03b1_1897_, lean_object* v_ref_1898_, lean_object* v_msg_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_){
_start:
{
lean_object* v___x_1909_; 
v___x_1909_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1___redArg(v_ref_1898_, v_msg_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_);
return v___x_1909_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1___boxed(lean_object* v_00_u03b1_1910_, lean_object* v_ref_1911_, lean_object* v_msg_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_){
_start:
{
lean_object* v_res_1922_; 
v_res_1922_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1(v_00_u03b1_1910_, v_ref_1911_, v_msg_1912_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_, v___y_1918_, v___y_1919_, v___y_1920_);
lean_dec(v___y_1920_);
lean_dec_ref(v___y_1919_);
lean_dec(v___y_1918_);
lean_dec_ref(v___y_1917_);
lean_dec(v___y_1916_);
lean_dec_ref(v___y_1915_);
lean_dec(v___y_1914_);
lean_dec_ref(v___y_1913_);
lean_dec(v_ref_1911_);
return v_res_1922_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3(lean_object* v_mvarId_1923_, lean_object* v_val_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_){
_start:
{
lean_object* v___x_1934_; 
v___x_1934_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3___redArg(v_mvarId_1923_, v_val_1924_, v___y_1930_);
return v___x_1934_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3___boxed(lean_object* v_mvarId_1935_, lean_object* v_val_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_){
_start:
{
lean_object* v_res_1946_; 
v_res_1946_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3(v_mvarId_1935_, v_val_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_);
lean_dec(v___y_1944_);
lean_dec_ref(v___y_1943_);
lean_dec(v___y_1942_);
lean_dec_ref(v___y_1941_);
lean_dec(v___y_1940_);
lean_dec_ref(v___y_1939_);
lean_dec(v___y_1938_);
lean_dec_ref(v___y_1937_);
return v_res_1946_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4(lean_object* v_00_u03b1_1947_, lean_object* v_msg_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_){
_start:
{
lean_object* v___x_1958_; 
v___x_1958_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg(v_msg_1948_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_);
return v___x_1958_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___boxed(lean_object* v_00_u03b1_1959_, lean_object* v_msg_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_){
_start:
{
lean_object* v_res_1970_; 
v_res_1970_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4(v_00_u03b1_1959_, v_msg_1960_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_, v___y_1967_, v___y_1968_);
lean_dec(v___y_1968_);
lean_dec_ref(v___y_1967_);
lean_dec(v___y_1966_);
lean_dec_ref(v___y_1965_);
lean_dec(v___y_1964_);
lean_dec_ref(v___y_1963_);
lean_dec(v___y_1962_);
lean_dec_ref(v___y_1961_);
return v_res_1970_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6(lean_object* v_n_1971_, lean_object* v_as_1972_, lean_object* v_lo_1973_, lean_object* v_hi_1974_, lean_object* v_w_1975_, lean_object* v_hlo_1976_, lean_object* v_hhi_1977_){
_start:
{
lean_object* v___x_1978_; 
v___x_1978_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg(v_n_1971_, v_as_1972_, v_lo_1973_, v_hi_1974_);
return v___x_1978_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___boxed(lean_object* v_n_1979_, lean_object* v_as_1980_, lean_object* v_lo_1981_, lean_object* v_hi_1982_, lean_object* v_w_1983_, lean_object* v_hlo_1984_, lean_object* v_hhi_1985_){
_start:
{
lean_object* v_res_1986_; 
v_res_1986_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6(v_n_1979_, v_as_1980_, v_lo_1981_, v_hi_1982_, v_w_1983_, v_hlo_1984_, v_hhi_1985_);
lean_dec(v_hi_1982_);
lean_dec(v_n_1979_);
return v_res_1986_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7(lean_object* v_as_1987_, size_t v_sz_1988_, size_t v_i_1989_, lean_object* v_bs_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_){
_start:
{
lean_object* v___x_2000_; 
v___x_2000_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg(v_sz_1988_, v_i_1989_, v_bs_1990_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_);
return v___x_2000_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___boxed(lean_object* v_as_2001_, lean_object* v_sz_2002_, lean_object* v_i_2003_, lean_object* v_bs_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_){
_start:
{
size_t v_sz_boxed_2014_; size_t v_i_boxed_2015_; lean_object* v_res_2016_; 
v_sz_boxed_2014_ = lean_unbox_usize(v_sz_2002_);
lean_dec(v_sz_2002_);
v_i_boxed_2015_ = lean_unbox_usize(v_i_2003_);
lean_dec(v_i_2003_);
v_res_2016_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7(v_as_2001_, v_sz_boxed_2014_, v_i_boxed_2015_, v_bs_2004_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_, v___y_2012_);
lean_dec(v___y_2012_);
lean_dec_ref(v___y_2011_);
lean_dec(v___y_2010_);
lean_dec_ref(v___y_2009_);
lean_dec(v___y_2008_);
lean_dec_ref(v___y_2007_);
lean_dec(v___y_2006_);
lean_dec_ref(v___y_2005_);
lean_dec_ref(v_as_2001_);
return v_res_2016_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9(lean_object* v_n_2017_, lean_object* v_as_2018_, lean_object* v_lo_2019_, lean_object* v_hi_2020_, lean_object* v_w_2021_, lean_object* v_hlo_2022_, lean_object* v_hhi_2023_){
_start:
{
lean_object* v___x_2024_; 
v___x_2024_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg(v_n_2017_, v_as_2018_, v_lo_2019_, v_hi_2020_);
return v___x_2024_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___boxed(lean_object* v_n_2025_, lean_object* v_as_2026_, lean_object* v_lo_2027_, lean_object* v_hi_2028_, lean_object* v_w_2029_, lean_object* v_hlo_2030_, lean_object* v_hhi_2031_){
_start:
{
lean_object* v_res_2032_; 
v_res_2032_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9(v_n_2025_, v_as_2026_, v_lo_2027_, v_hi_2028_, v_w_2029_, v_hlo_2030_, v_hhi_2031_);
lean_dec(v_hi_2028_);
lean_dec(v_n_2025_);
return v_res_2032_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3(lean_object* v_00_u03b2_2033_, lean_object* v_x_2034_, lean_object* v_x_2035_, lean_object* v_x_2036_){
_start:
{
lean_object* v___x_2037_; 
v___x_2037_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3___redArg(v_x_2034_, v_x_2035_, v_x_2036_);
return v___x_2037_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6_spec__8(lean_object* v_n_2038_, lean_object* v_lo_2039_, lean_object* v_hi_2040_, lean_object* v_hhi_2041_, lean_object* v_pivot_2042_, lean_object* v_as_2043_, lean_object* v_i_2044_, lean_object* v_k_2045_, lean_object* v_ilo_2046_, lean_object* v_ik_2047_, lean_object* v_w_2048_){
_start:
{
lean_object* v___x_2049_; 
v___x_2049_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6_spec__8___redArg(v_hi_2040_, v_pivot_2042_, v_as_2043_, v_i_2044_, v_k_2045_);
return v___x_2049_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6_spec__8___boxed(lean_object* v_n_2050_, lean_object* v_lo_2051_, lean_object* v_hi_2052_, lean_object* v_hhi_2053_, lean_object* v_pivot_2054_, lean_object* v_as_2055_, lean_object* v_i_2056_, lean_object* v_k_2057_, lean_object* v_ilo_2058_, lean_object* v_ik_2059_, lean_object* v_w_2060_){
_start:
{
lean_object* v_res_2061_; 
v_res_2061_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6_spec__8(v_n_2050_, v_lo_2051_, v_hi_2052_, v_hhi_2053_, v_pivot_2054_, v_as_2055_, v_i_2056_, v_k_2057_, v_ilo_2058_, v_ik_2059_, v_w_2060_);
lean_dec_ref(v_pivot_2054_);
lean_dec(v_hi_2052_);
lean_dec(v_lo_2051_);
lean_dec(v_n_2050_);
return v_res_2061_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9_spec__13(lean_object* v_n_2062_, lean_object* v_lo_2063_, lean_object* v_hi_2064_, lean_object* v_hhi_2065_, lean_object* v_pivot_2066_, lean_object* v_as_2067_, lean_object* v_i_2068_, lean_object* v_k_2069_, lean_object* v_ilo_2070_, lean_object* v_ik_2071_, lean_object* v_w_2072_){
_start:
{
lean_object* v___x_2073_; 
v___x_2073_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9_spec__13___redArg(v_hi_2064_, v_pivot_2066_, v_as_2067_, v_i_2068_, v_k_2069_);
return v___x_2073_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9_spec__13___boxed(lean_object* v_n_2074_, lean_object* v_lo_2075_, lean_object* v_hi_2076_, lean_object* v_hhi_2077_, lean_object* v_pivot_2078_, lean_object* v_as_2079_, lean_object* v_i_2080_, lean_object* v_k_2081_, lean_object* v_ilo_2082_, lean_object* v_ik_2083_, lean_object* v_w_2084_){
_start:
{
lean_object* v_res_2085_; 
v_res_2085_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9_spec__13(v_n_2074_, v_lo_2075_, v_hi_2076_, v_hhi_2077_, v_pivot_2078_, v_as_2079_, v_i_2080_, v_k_2081_, v_ilo_2082_, v_ik_2083_, v_w_2084_);
lean_dec_ref(v_pivot_2078_);
lean_dec(v_hi_2076_);
lean_dec(v_lo_2075_);
lean_dec(v_n_2074_);
return v_res_2085_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4(lean_object* v_00_u03b2_2086_, lean_object* v_x_2087_, size_t v_x_2088_, size_t v_x_2089_, lean_object* v_x_2090_, lean_object* v_x_2091_){
_start:
{
lean_object* v___x_2092_; 
v___x_2092_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg(v_x_2087_, v_x_2088_, v_x_2089_, v_x_2090_, v_x_2091_);
return v___x_2092_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___boxed(lean_object* v_00_u03b2_2093_, lean_object* v_x_2094_, lean_object* v_x_2095_, lean_object* v_x_2096_, lean_object* v_x_2097_, lean_object* v_x_2098_){
_start:
{
size_t v_x_20562__boxed_2099_; size_t v_x_20563__boxed_2100_; lean_object* v_res_2101_; 
v_x_20562__boxed_2099_ = lean_unbox_usize(v_x_2095_);
lean_dec(v_x_2095_);
v_x_20563__boxed_2100_ = lean_unbox_usize(v_x_2096_);
lean_dec(v_x_2096_);
v_res_2101_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4(v_00_u03b2_2093_, v_x_2094_, v_x_20562__boxed_2099_, v_x_20563__boxed_2100_, v_x_2097_, v_x_2098_);
return v_res_2101_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11_spec__13(lean_object* v_as_2102_, lean_object* v_a_2103_, lean_object* v_x_2104_, lean_object* v_x_2105_){
_start:
{
uint8_t v___x_2106_; 
v___x_2106_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11_spec__13___redArg(v_as_2102_, v_a_2103_, v_x_2104_);
return v___x_2106_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11_spec__13___boxed(lean_object* v_as_2107_, lean_object* v_a_2108_, lean_object* v_x_2109_, lean_object* v_x_2110_){
_start:
{
uint8_t v_res_2111_; lean_object* v_r_2112_; 
v_res_2111_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11_spec__13(v_as_2107_, v_a_2108_, v_x_2109_, v_x_2110_);
lean_dec_ref(v_a_2108_);
lean_dec_ref(v_as_2107_);
v_r_2112_ = lean_box(v_res_2111_);
return v_r_2112_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__12(lean_object* v_00_u03b2_2113_, lean_object* v_n_2114_, lean_object* v_k_2115_, lean_object* v_v_2116_){
_start:
{
lean_object* v___x_2117_; 
v___x_2117_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__12___redArg(v_n_2114_, v_k_2115_, v_v_2116_);
return v___x_2117_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__13(lean_object* v_00_u03b2_2118_, size_t v_depth_2119_, lean_object* v_keys_2120_, lean_object* v_vals_2121_, lean_object* v_heq_2122_, lean_object* v_i_2123_, lean_object* v_entries_2124_){
_start:
{
lean_object* v___x_2125_; 
v___x_2125_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__13___redArg(v_depth_2119_, v_keys_2120_, v_vals_2121_, v_i_2123_, v_entries_2124_);
return v___x_2125_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__13___boxed(lean_object* v_00_u03b2_2126_, lean_object* v_depth_2127_, lean_object* v_keys_2128_, lean_object* v_vals_2129_, lean_object* v_heq_2130_, lean_object* v_i_2131_, lean_object* v_entries_2132_){
_start:
{
size_t v_depth_boxed_2133_; lean_object* v_res_2134_; 
v_depth_boxed_2133_ = lean_unbox_usize(v_depth_2127_);
lean_dec(v_depth_2127_);
v_res_2134_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__13(v_00_u03b2_2126_, v_depth_boxed_2133_, v_keys_2128_, v_vals_2129_, v_heq_2130_, v_i_2131_, v_entries_2132_);
lean_dec_ref(v_vals_2129_);
lean_dec_ref(v_keys_2128_);
return v_res_2134_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__12_spec__16(lean_object* v_00_u03b2_2135_, lean_object* v_x_2136_, lean_object* v_x_2137_, lean_object* v_x_2138_, lean_object* v_x_2139_){
_start:
{
lean_object* v___x_2140_; 
v___x_2140_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__12_spec__16___redArg(v_x_2136_, v_x_2137_, v_x_2138_, v_x_2139_);
return v___x_2140_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1(){
_start:
{
lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; 
v___x_2150_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2151_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___closed__6));
v___x_2152_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___closed__2));
v___x_2153_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalPattern___boxed), 10, 0);
v___x_2154_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2150_, v___x_2151_, v___x_2152_, v___x_2153_);
return v___x_2154_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___boxed(lean_object* v_a_2155_){
_start:
{
lean_object* v_res_2156_; 
v_res_2156_ = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1();
return v_res_2156_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3(){
_start:
{
lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; 
v___x_2183_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___closed__2));
v___x_2184_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__6));
v___x_2185_ = l_Lean_addBuiltinDeclarationRanges(v___x_2183_, v___x_2184_);
return v___x_2185_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___boxed(lean_object* v_a_2186_){
_start:
{
lean_object* v_res_2187_; 
v_res_2187_ = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3();
return v_res_2187_;
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
