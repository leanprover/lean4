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
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_matchPattern_x3f___lam__0(lean_object* v_pattern_168_, lean_object* v_e_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_){
_start:
{
lean_object* v___x_175_; 
v___x_175_ = l_Lean_Meta_openAbstractMVarsResult(v_pattern_168_, v___y_170_, v___y_171_, v___y_172_, v___y_173_);
if (lean_obj_tag(v___x_175_) == 0)
{
lean_object* v_a_176_; lean_object* v_snd_177_; lean_object* v_snd_178_; lean_object* v_keyedConfig_179_; uint8_t v_trackZetaDelta_180_; lean_object* v_zetaDeltaSet_181_; lean_object* v_lctx_182_; lean_object* v_localInstances_183_; lean_object* v_defEqCtx_x3f_184_; lean_object* v_synthPendingDepth_185_; lean_object* v_customCanUnfoldPredicate_x3f_186_; uint8_t v_univApprox_187_; uint8_t v_inTypeClassResolution_188_; uint8_t v_cacheInferType_189_; lean_object* v___x_191_; uint8_t v_isShared_192_; uint8_t v_isSharedCheck_199_; 
v_a_176_ = lean_ctor_get(v___x_175_, 0);
lean_inc(v_a_176_);
lean_dec_ref_known(v___x_175_, 1);
v_snd_177_ = lean_ctor_get(v_a_176_, 1);
lean_inc(v_snd_177_);
lean_dec(v_a_176_);
v_snd_178_ = lean_ctor_get(v_snd_177_, 1);
lean_inc(v_snd_178_);
lean_dec(v_snd_177_);
v_keyedConfig_179_ = lean_ctor_get(v___y_170_, 0);
v_trackZetaDelta_180_ = lean_ctor_get_uint8(v___y_170_, sizeof(void*)*7);
v_zetaDeltaSet_181_ = lean_ctor_get(v___y_170_, 1);
v_lctx_182_ = lean_ctor_get(v___y_170_, 2);
v_localInstances_183_ = lean_ctor_get(v___y_170_, 3);
v_defEqCtx_x3f_184_ = lean_ctor_get(v___y_170_, 4);
v_synthPendingDepth_185_ = lean_ctor_get(v___y_170_, 5);
v_customCanUnfoldPredicate_x3f_186_ = lean_ctor_get(v___y_170_, 6);
v_univApprox_187_ = lean_ctor_get_uint8(v___y_170_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_188_ = lean_ctor_get_uint8(v___y_170_, sizeof(void*)*7 + 2);
v_cacheInferType_189_ = lean_ctor_get_uint8(v___y_170_, sizeof(void*)*7 + 3);
v_isSharedCheck_199_ = !lean_is_exclusive(v___y_170_);
if (v_isSharedCheck_199_ == 0)
{
v___x_191_ = v___y_170_;
v_isShared_192_ = v_isSharedCheck_199_;
goto v_resetjp_190_;
}
else
{
lean_inc(v_customCanUnfoldPredicate_x3f_186_);
lean_inc(v_synthPendingDepth_185_);
lean_inc(v_defEqCtx_x3f_184_);
lean_inc(v_localInstances_183_);
lean_inc(v_lctx_182_);
lean_inc(v_zetaDeltaSet_181_);
lean_inc(v_keyedConfig_179_);
lean_dec(v___y_170_);
v___x_191_ = lean_box(0);
v_isShared_192_ = v_isSharedCheck_199_;
goto v_resetjp_190_;
}
v_resetjp_190_:
{
uint8_t v___x_193_; lean_object* v___x_194_; lean_object* v___x_196_; 
v___x_193_ = 2;
v___x_194_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_193_, v_keyedConfig_179_);
if (v_isShared_192_ == 0)
{
lean_ctor_set(v___x_191_, 0, v___x_194_);
v___x_196_ = v___x_191_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v___x_194_);
lean_ctor_set(v_reuseFailAlloc_198_, 1, v_zetaDeltaSet_181_);
lean_ctor_set(v_reuseFailAlloc_198_, 2, v_lctx_182_);
lean_ctor_set(v_reuseFailAlloc_198_, 3, v_localInstances_183_);
lean_ctor_set(v_reuseFailAlloc_198_, 4, v_defEqCtx_x3f_184_);
lean_ctor_set(v_reuseFailAlloc_198_, 5, v_synthPendingDepth_185_);
lean_ctor_set(v_reuseFailAlloc_198_, 6, v_customCanUnfoldPredicate_x3f_186_);
lean_ctor_set_uint8(v_reuseFailAlloc_198_, sizeof(void*)*7, v_trackZetaDelta_180_);
lean_ctor_set_uint8(v_reuseFailAlloc_198_, sizeof(void*)*7 + 1, v_univApprox_187_);
lean_ctor_set_uint8(v_reuseFailAlloc_198_, sizeof(void*)*7 + 2, v_inTypeClassResolution_188_);
lean_ctor_set_uint8(v_reuseFailAlloc_198_, sizeof(void*)*7 + 3, v_cacheInferType_189_);
v___x_196_ = v_reuseFailAlloc_198_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
lean_object* v___x_197_; 
v___x_197_ = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_matchPattern_x3f_go_x3f(v_snd_178_, v_e_169_, v___x_196_, v___y_171_, v___y_172_, v___y_173_);
lean_dec_ref(v___x_196_);
return v___x_197_;
}
}
}
else
{
lean_object* v_a_200_; lean_object* v___x_202_; uint8_t v_isShared_203_; uint8_t v_isSharedCheck_207_; 
lean_dec_ref(v___y_170_);
lean_dec_ref(v_e_169_);
v_a_200_ = lean_ctor_get(v___x_175_, 0);
v_isSharedCheck_207_ = !lean_is_exclusive(v___x_175_);
if (v_isSharedCheck_207_ == 0)
{
v___x_202_ = v___x_175_;
v_isShared_203_ = v_isSharedCheck_207_;
goto v_resetjp_201_;
}
else
{
lean_inc(v_a_200_);
lean_dec(v___x_175_);
v___x_202_ = lean_box(0);
v_isShared_203_ = v_isSharedCheck_207_;
goto v_resetjp_201_;
}
v_resetjp_201_:
{
lean_object* v___x_205_; 
if (v_isShared_203_ == 0)
{
v___x_205_ = v___x_202_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_206_; 
v_reuseFailAlloc_206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_206_, 0, v_a_200_);
v___x_205_ = v_reuseFailAlloc_206_;
goto v_reusejp_204_;
}
v_reusejp_204_:
{
return v___x_205_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_matchPattern_x3f___lam__0___boxed(lean_object* v_pattern_208_, lean_object* v_e_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_){
_start:
{
lean_object* v_res_215_; 
v_res_215_ = l_Lean_Elab_Tactic_Conv_matchPattern_x3f___lam__0(v_pattern_208_, v_e_209_, v___y_210_, v___y_211_, v___y_212_, v___y_213_);
lean_dec(v___y_213_);
lean_dec_ref(v___y_212_);
lean_dec(v___y_211_);
return v_res_215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_matchPattern_x3f(lean_object* v_pattern_216_, lean_object* v_e_217_, lean_object* v_a_218_, lean_object* v_a_219_, lean_object* v_a_220_, lean_object* v_a_221_){
_start:
{
lean_object* v___f_223_; uint8_t v___x_224_; lean_object* v___x_225_; 
v___f_223_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_matchPattern_x3f___lam__0___boxed), 7, 2);
lean_closure_set(v___f_223_, 0, v_pattern_216_);
lean_closure_set(v___f_223_, 1, v_e_217_);
v___x_224_ = 0;
v___x_225_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Conv_matchPattern_x3f_spec__0___redArg(v___f_223_, v___x_224_, v_a_218_, v_a_219_, v_a_220_, v_a_221_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_matchPattern_x3f___boxed(lean_object* v_pattern_226_, lean_object* v_e_227_, lean_object* v_a_228_, lean_object* v_a_229_, lean_object* v_a_230_, lean_object* v_a_231_, lean_object* v_a_232_){
_start:
{
lean_object* v_res_233_; 
v_res_233_ = l_Lean_Elab_Tactic_Conv_matchPattern_x3f(v_pattern_226_, v_e_227_, v_a_228_, v_a_229_, v_a_230_, v_a_231_);
lean_dec(v_a_231_);
lean_dec_ref(v_a_230_);
lean_dec(v_a_229_);
lean_dec_ref(v_a_228_);
return v_res_233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorIdx(lean_object* v_x_234_){
_start:
{
if (lean_obj_tag(v_x_234_) == 0)
{
lean_object* v___x_235_; 
v___x_235_ = lean_unsigned_to_nat(0u);
return v___x_235_;
}
else
{
lean_object* v___x_236_; 
v___x_236_ = lean_unsigned_to_nat(1u);
return v___x_236_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorIdx___boxed(lean_object* v_x_237_){
_start:
{
lean_object* v_res_238_; 
v_res_238_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorIdx(v_x_237_);
lean_dec_ref(v_x_237_);
return v_res_238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorElim___redArg(lean_object* v_t_239_, lean_object* v_k_240_){
_start:
{
if (lean_obj_tag(v_t_239_) == 0)
{
lean_object* v_subgoals_241_; lean_object* v___x_242_; 
v_subgoals_241_ = lean_ctor_get(v_t_239_, 0);
lean_inc_ref(v_subgoals_241_);
lean_dec_ref_known(v_t_239_, 1);
v___x_242_ = lean_apply_1(v_k_240_, v_subgoals_241_);
return v___x_242_;
}
else
{
lean_object* v_subgoals_243_; lean_object* v_idx_244_; lean_object* v_remaining_245_; lean_object* v___x_246_; 
v_subgoals_243_ = lean_ctor_get(v_t_239_, 0);
lean_inc_ref(v_subgoals_243_);
v_idx_244_ = lean_ctor_get(v_t_239_, 1);
lean_inc(v_idx_244_);
v_remaining_245_ = lean_ctor_get(v_t_239_, 2);
lean_inc(v_remaining_245_);
lean_dec_ref_known(v_t_239_, 3);
v___x_246_ = lean_apply_3(v_k_240_, v_subgoals_243_, v_idx_244_, v_remaining_245_);
return v___x_246_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorElim(lean_object* v_motive_247_, lean_object* v_ctorIdx_248_, lean_object* v_t_249_, lean_object* v_h_250_, lean_object* v_k_251_){
_start:
{
lean_object* v___x_252_; 
v___x_252_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorElim___redArg(v_t_249_, v_k_251_);
return v___x_252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorElim___boxed(lean_object* v_motive_253_, lean_object* v_ctorIdx_254_, lean_object* v_t_255_, lean_object* v_h_256_, lean_object* v_k_257_){
_start:
{
lean_object* v_res_258_; 
v_res_258_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorElim(v_motive_253_, v_ctorIdx_254_, v_t_255_, v_h_256_, v_k_257_);
lean_dec(v_ctorIdx_254_);
return v_res_258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_all_elim___redArg(lean_object* v_t_259_, lean_object* v_all_260_){
_start:
{
lean_object* v___x_261_; 
v___x_261_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorElim___redArg(v_t_259_, v_all_260_);
return v___x_261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_all_elim(lean_object* v_motive_262_, lean_object* v_t_263_, lean_object* v_h_264_, lean_object* v_all_265_){
_start:
{
lean_object* v___x_266_; 
v___x_266_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorElim___redArg(v_t_263_, v_all_265_);
return v___x_266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_occs_elim___redArg(lean_object* v_t_267_, lean_object* v_occs_268_){
_start:
{
lean_object* v___x_269_; 
v___x_269_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorElim___redArg(v_t_267_, v_occs_268_);
return v___x_269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_occs_elim(lean_object* v_motive_270_, lean_object* v_t_271_, lean_object* v_h_272_, lean_object* v_occs_273_){
_start:
{
lean_object* v___x_274_; 
v___x_274_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorElim___redArg(v_t_271_, v_occs_273_);
return v___x_274_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Conv_PatternMatchState_isDone(lean_object* v_x_275_){
_start:
{
if (lean_obj_tag(v_x_275_) == 0)
{
uint8_t v___x_276_; 
v___x_276_ = 0;
return v___x_276_;
}
else
{
lean_object* v_remaining_277_; uint8_t v___x_278_; 
v_remaining_277_ = lean_ctor_get(v_x_275_, 2);
v___x_278_ = l_List_isEmpty___redArg(v_remaining_277_);
return v___x_278_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_isDone___boxed(lean_object* v_x_279_){
_start:
{
uint8_t v_res_280_; lean_object* v_r_281_; 
v_res_280_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_isDone(v_x_279_);
lean_dec_ref(v_x_279_);
v_r_281_ = lean_box(v_res_280_);
return v_r_281_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Conv_PatternMatchState_isReady(lean_object* v_x_282_){
_start:
{
if (lean_obj_tag(v_x_282_) == 0)
{
uint8_t v___x_283_; 
v___x_283_ = 1;
return v___x_283_;
}
else
{
lean_object* v_remaining_284_; 
v_remaining_284_ = lean_ctor_get(v_x_282_, 2);
if (lean_obj_tag(v_remaining_284_) == 1)
{
lean_object* v_head_285_; lean_object* v_idx_286_; lean_object* v_fst_287_; uint8_t v___x_288_; 
v_head_285_ = lean_ctor_get(v_remaining_284_, 0);
v_idx_286_ = lean_ctor_get(v_x_282_, 1);
v_fst_287_ = lean_ctor_get(v_head_285_, 0);
v___x_288_ = lean_nat_dec_eq(v_idx_286_, v_fst_287_);
return v___x_288_;
}
else
{
uint8_t v___x_289_; 
v___x_289_ = 0;
return v___x_289_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_isReady___boxed(lean_object* v_x_290_){
_start:
{
uint8_t v_res_291_; lean_object* v_r_292_; 
v_res_291_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_isReady(v_x_290_);
lean_dec_ref(v_x_290_);
v_r_292_ = lean_box(v_res_291_);
return v_r_292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_skip(lean_object* v_x_293_){
_start:
{
if (lean_obj_tag(v_x_293_) == 1)
{
lean_object* v_subgoals_294_; lean_object* v_idx_295_; lean_object* v_remaining_296_; lean_object* v___x_298_; uint8_t v_isShared_299_; uint8_t v_isSharedCheck_305_; 
v_subgoals_294_ = lean_ctor_get(v_x_293_, 0);
v_idx_295_ = lean_ctor_get(v_x_293_, 1);
v_remaining_296_ = lean_ctor_get(v_x_293_, 2);
v_isSharedCheck_305_ = !lean_is_exclusive(v_x_293_);
if (v_isSharedCheck_305_ == 0)
{
v___x_298_ = v_x_293_;
v_isShared_299_ = v_isSharedCheck_305_;
goto v_resetjp_297_;
}
else
{
lean_inc(v_remaining_296_);
lean_inc(v_idx_295_);
lean_inc(v_subgoals_294_);
lean_dec(v_x_293_);
v___x_298_ = lean_box(0);
v_isShared_299_ = v_isSharedCheck_305_;
goto v_resetjp_297_;
}
v_resetjp_297_:
{
lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_303_; 
v___x_300_ = lean_unsigned_to_nat(1u);
v___x_301_ = lean_nat_add(v_idx_295_, v___x_300_);
lean_dec(v_idx_295_);
if (v_isShared_299_ == 0)
{
lean_ctor_set(v___x_298_, 1, v___x_301_);
v___x_303_ = v___x_298_;
goto v_reusejp_302_;
}
else
{
lean_object* v_reuseFailAlloc_304_; 
v_reuseFailAlloc_304_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_304_, 0, v_subgoals_294_);
lean_ctor_set(v_reuseFailAlloc_304_, 1, v___x_301_);
lean_ctor_set(v_reuseFailAlloc_304_, 2, v_remaining_296_);
v___x_303_ = v_reuseFailAlloc_304_;
goto v_reusejp_302_;
}
v_reusejp_302_:
{
return v___x_303_;
}
}
}
else
{
return v_x_293_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_accept(lean_object* v_mvarId_306_, lean_object* v_x_307_){
_start:
{
if (lean_obj_tag(v_x_307_) == 0)
{
lean_object* v_subgoals_308_; lean_object* v___x_310_; uint8_t v_isShared_311_; uint8_t v_isSharedCheck_316_; 
v_subgoals_308_ = lean_ctor_get(v_x_307_, 0);
v_isSharedCheck_316_ = !lean_is_exclusive(v_x_307_);
if (v_isSharedCheck_316_ == 0)
{
v___x_310_ = v_x_307_;
v_isShared_311_ = v_isSharedCheck_316_;
goto v_resetjp_309_;
}
else
{
lean_inc(v_subgoals_308_);
lean_dec(v_x_307_);
v___x_310_ = lean_box(0);
v_isShared_311_ = v_isSharedCheck_316_;
goto v_resetjp_309_;
}
v_resetjp_309_:
{
lean_object* v___x_312_; lean_object* v___x_314_; 
v___x_312_ = lean_array_push(v_subgoals_308_, v_mvarId_306_);
if (v_isShared_311_ == 0)
{
lean_ctor_set(v___x_310_, 0, v___x_312_);
v___x_314_ = v___x_310_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v___x_312_);
v___x_314_ = v_reuseFailAlloc_315_;
goto v_reusejp_313_;
}
v_reusejp_313_:
{
return v___x_314_;
}
}
}
else
{
lean_object* v_remaining_317_; 
v_remaining_317_ = lean_ctor_get(v_x_307_, 2);
if (lean_obj_tag(v_remaining_317_) == 1)
{
lean_object* v_head_318_; lean_object* v_subgoals_319_; lean_object* v_idx_320_; lean_object* v___x_322_; uint8_t v_isShared_323_; uint8_t v_isSharedCheck_340_; 
lean_inc_ref(v_remaining_317_);
v_head_318_ = lean_ctor_get(v_remaining_317_, 0);
lean_inc(v_head_318_);
v_subgoals_319_ = lean_ctor_get(v_x_307_, 0);
v_idx_320_ = lean_ctor_get(v_x_307_, 1);
v_isSharedCheck_340_ = !lean_is_exclusive(v_x_307_);
if (v_isSharedCheck_340_ == 0)
{
lean_object* v_unused_341_; 
v_unused_341_ = lean_ctor_get(v_x_307_, 2);
lean_dec(v_unused_341_);
v___x_322_ = v_x_307_;
v_isShared_323_ = v_isSharedCheck_340_;
goto v_resetjp_321_;
}
else
{
lean_inc(v_idx_320_);
lean_inc(v_subgoals_319_);
lean_dec(v_x_307_);
v___x_322_ = lean_box(0);
v_isShared_323_ = v_isSharedCheck_340_;
goto v_resetjp_321_;
}
v_resetjp_321_:
{
lean_object* v_tail_324_; lean_object* v_snd_325_; lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_338_; 
v_tail_324_ = lean_ctor_get(v_remaining_317_, 1);
lean_inc(v_tail_324_);
lean_dec_ref_known(v_remaining_317_, 2);
v_snd_325_ = lean_ctor_get(v_head_318_, 1);
v_isSharedCheck_338_ = !lean_is_exclusive(v_head_318_);
if (v_isSharedCheck_338_ == 0)
{
lean_object* v_unused_339_; 
v_unused_339_ = lean_ctor_get(v_head_318_, 0);
lean_dec(v_unused_339_);
v___x_327_ = v_head_318_;
v_isShared_328_ = v_isSharedCheck_338_;
goto v_resetjp_326_;
}
else
{
lean_inc(v_snd_325_);
lean_dec(v_head_318_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_338_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
lean_object* v___x_330_; 
if (v_isShared_328_ == 0)
{
lean_ctor_set(v___x_327_, 1, v_mvarId_306_);
lean_ctor_set(v___x_327_, 0, v_snd_325_);
v___x_330_ = v___x_327_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_337_; 
v_reuseFailAlloc_337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_337_, 0, v_snd_325_);
lean_ctor_set(v_reuseFailAlloc_337_, 1, v_mvarId_306_);
v___x_330_ = v_reuseFailAlloc_337_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_335_; 
v___x_331_ = lean_array_push(v_subgoals_319_, v___x_330_);
v___x_332_ = lean_unsigned_to_nat(1u);
v___x_333_ = lean_nat_add(v_idx_320_, v___x_332_);
lean_dec(v_idx_320_);
if (v_isShared_323_ == 0)
{
lean_ctor_set(v___x_322_, 2, v_tail_324_);
lean_ctor_set(v___x_322_, 1, v___x_333_);
lean_ctor_set(v___x_322_, 0, v___x_331_);
v___x_335_ = v___x_322_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v___x_331_);
lean_ctor_set(v_reuseFailAlloc_336_, 1, v___x_333_);
lean_ctor_set(v_reuseFailAlloc_336_, 2, v_tail_324_);
v___x_335_ = v_reuseFailAlloc_336_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
return v___x_335_;
}
}
}
}
}
else
{
lean_dec(v_mvarId_306_);
return v_x_307_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre_spec__0___redArg(lean_object* v_as_342_, size_t v_sz_343_, size_t v_i_344_, lean_object* v_b_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_){
_start:
{
uint8_t v___x_351_; 
v___x_351_ = lean_usize_dec_lt(v_i_344_, v_sz_343_);
if (v___x_351_ == 0)
{
lean_object* v___x_352_; 
v___x_352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_352_, 0, v_b_345_);
return v___x_352_;
}
else
{
lean_object* v_a_353_; lean_object* v___x_354_; 
v_a_353_ = lean_array_uget_borrowed(v_as_342_, v_i_344_);
lean_inc(v_a_353_);
v___x_354_ = l_Lean_Meta_mkCongrFun(v_b_345_, v_a_353_, v___y_346_, v___y_347_, v___y_348_, v___y_349_);
if (lean_obj_tag(v___x_354_) == 0)
{
lean_object* v_a_355_; size_t v___x_356_; size_t v___x_357_; 
v_a_355_ = lean_ctor_get(v___x_354_, 0);
lean_inc(v_a_355_);
lean_dec_ref_known(v___x_354_, 1);
v___x_356_ = ((size_t)1ULL);
v___x_357_ = lean_usize_add(v_i_344_, v___x_356_);
v_i_344_ = v___x_357_;
v_b_345_ = v_a_355_;
goto _start;
}
else
{
return v___x_354_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre_spec__0___redArg___boxed(lean_object* v_as_359_, lean_object* v_sz_360_, lean_object* v_i_361_, lean_object* v_b_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_){
_start:
{
size_t v_sz_boxed_368_; size_t v_i_boxed_369_; lean_object* v_res_370_; 
v_sz_boxed_368_ = lean_unbox_usize(v_sz_360_);
lean_dec(v_sz_360_);
v_i_boxed_369_ = lean_unbox_usize(v_i_361_);
lean_dec(v_i_361_);
v_res_370_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre_spec__0___redArg(v_as_359_, v_sz_boxed_368_, v_i_boxed_369_, v_b_362_, v___y_363_, v___y_364_, v___y_365_, v___y_366_);
lean_dec(v___y_366_);
lean_dec_ref(v___y_365_);
lean_dec(v___y_364_);
lean_dec_ref(v___y_363_);
lean_dec_ref(v_as_359_);
return v_res_370_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre(lean_object* v_pattern_373_, lean_object* v_state_374_, lean_object* v_e_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_, lean_object* v_a_381_, lean_object* v_a_382_){
_start:
{
lean_object* v___x_384_; uint8_t v___x_385_; uint8_t v___x_386_; 
v___x_384_ = lean_st_ref_get(v_state_374_);
v___x_385_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_isDone(v___x_384_);
lean_dec(v___x_384_);
v___x_386_ = 1;
if (v___x_385_ == 0)
{
lean_object* v___x_387_; 
v___x_387_ = l_Lean_Elab_Tactic_Conv_matchPattern_x3f(v_pattern_373_, v_e_375_, v_a_379_, v_a_380_, v_a_381_, v_a_382_);
if (lean_obj_tag(v___x_387_) == 0)
{
lean_object* v_a_388_; lean_object* v___x_390_; uint8_t v_isShared_391_; uint8_t v_isSharedCheck_454_; 
v_a_388_ = lean_ctor_get(v___x_387_, 0);
v_isSharedCheck_454_ = !lean_is_exclusive(v___x_387_);
if (v_isSharedCheck_454_ == 0)
{
v___x_390_ = v___x_387_;
v_isShared_391_ = v_isSharedCheck_454_;
goto v_resetjp_389_;
}
else
{
lean_inc(v_a_388_);
lean_dec(v___x_387_);
v___x_390_ = lean_box(0);
v_isShared_391_ = v_isSharedCheck_454_;
goto v_resetjp_389_;
}
v_resetjp_389_:
{
if (lean_obj_tag(v_a_388_) == 1)
{
lean_object* v_val_392_; lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_449_; 
v_val_392_ = lean_ctor_get(v_a_388_, 0);
v_isSharedCheck_449_ = !lean_is_exclusive(v_a_388_);
if (v_isSharedCheck_449_ == 0)
{
v___x_394_ = v_a_388_;
v_isShared_395_ = v_isSharedCheck_449_;
goto v_resetjp_393_;
}
else
{
lean_inc(v_val_392_);
lean_dec(v_a_388_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_449_;
goto v_resetjp_393_;
}
v_resetjp_393_:
{
lean_object* v_fst_396_; lean_object* v_snd_397_; lean_object* v___x_398_; uint8_t v___x_399_; 
v_fst_396_ = lean_ctor_get(v_val_392_, 0);
lean_inc(v_fst_396_);
v_snd_397_ = lean_ctor_get(v_val_392_, 1);
lean_inc(v_snd_397_);
lean_dec(v_val_392_);
v___x_398_ = lean_st_ref_get(v_state_374_);
v___x_399_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_isReady(v___x_398_);
lean_dec(v___x_398_);
if (v___x_399_ == 0)
{
lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_405_; 
lean_dec(v_snd_397_);
lean_dec(v_fst_396_);
lean_del_object(v___x_394_);
v___x_400_ = lean_st_ref_take(v_state_374_);
v___x_401_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_skip(v___x_400_);
v___x_402_ = lean_st_ref_set(v_state_374_, v___x_401_);
v___x_403_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre___closed__0));
if (v_isShared_391_ == 0)
{
lean_ctor_set(v___x_390_, 0, v___x_403_);
v___x_405_ = v___x_390_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v___x_403_);
v___x_405_ = v_reuseFailAlloc_406_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
return v___x_405_;
}
}
else
{
lean_object* v___x_407_; lean_object* v___x_408_; 
lean_del_object(v___x_390_);
v___x_407_ = lean_box(0);
v___x_408_ = l_Lean_Elab_Tactic_Conv_mkConvGoalFor(v_fst_396_, v___x_407_, v_a_379_, v_a_380_, v_a_381_, v_a_382_);
if (lean_obj_tag(v___x_408_) == 0)
{
lean_object* v_a_409_; lean_object* v_fst_410_; lean_object* v_snd_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; size_t v_sz_416_; size_t v___x_417_; lean_object* v___x_418_; 
v_a_409_ = lean_ctor_get(v___x_408_, 0);
lean_inc(v_a_409_);
lean_dec_ref_known(v___x_408_, 1);
v_fst_410_ = lean_ctor_get(v_a_409_, 0);
lean_inc(v_fst_410_);
v_snd_411_ = lean_ctor_get(v_a_409_, 1);
lean_inc(v_snd_411_);
lean_dec(v_a_409_);
v___x_412_ = lean_st_ref_take(v_state_374_);
v___x_413_ = l_Lean_Expr_mvarId_x21(v_snd_411_);
v___x_414_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_accept(v___x_413_, v___x_412_);
v___x_415_ = lean_st_ref_set(v_state_374_, v___x_414_);
v_sz_416_ = lean_array_size(v_snd_397_);
v___x_417_ = ((size_t)0ULL);
v___x_418_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre_spec__0___redArg(v_snd_397_, v_sz_416_, v___x_417_, v_snd_411_, v_a_379_, v_a_380_, v_a_381_, v_a_382_);
if (lean_obj_tag(v___x_418_) == 0)
{
lean_object* v_a_419_; lean_object* v___x_421_; uint8_t v_isShared_422_; uint8_t v_isSharedCheck_432_; 
v_a_419_ = lean_ctor_get(v___x_418_, 0);
v_isSharedCheck_432_ = !lean_is_exclusive(v___x_418_);
if (v_isSharedCheck_432_ == 0)
{
v___x_421_ = v___x_418_;
v_isShared_422_ = v_isSharedCheck_432_;
goto v_resetjp_420_;
}
else
{
lean_inc(v_a_419_);
lean_dec(v___x_418_);
v___x_421_ = lean_box(0);
v_isShared_422_ = v_isSharedCheck_432_;
goto v_resetjp_420_;
}
v_resetjp_420_:
{
lean_object* v___x_423_; lean_object* v___x_425_; 
v___x_423_ = l_Lean_mkAppN(v_fst_410_, v_snd_397_);
lean_dec(v_snd_397_);
if (v_isShared_395_ == 0)
{
lean_ctor_set(v___x_394_, 0, v_a_419_);
v___x_425_ = v___x_394_;
goto v_reusejp_424_;
}
else
{
lean_object* v_reuseFailAlloc_431_; 
v_reuseFailAlloc_431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_431_, 0, v_a_419_);
v___x_425_ = v_reuseFailAlloc_431_;
goto v_reusejp_424_;
}
v_reusejp_424_:
{
lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_429_; 
v___x_426_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_426_, 0, v___x_423_);
lean_ctor_set(v___x_426_, 1, v___x_425_);
lean_ctor_set_uint8(v___x_426_, sizeof(void*)*2, v___x_386_);
v___x_427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_427_, 0, v___x_426_);
if (v_isShared_422_ == 0)
{
lean_ctor_set(v___x_421_, 0, v___x_427_);
v___x_429_ = v___x_421_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v___x_427_);
v___x_429_ = v_reuseFailAlloc_430_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
return v___x_429_;
}
}
}
}
else
{
lean_object* v_a_433_; lean_object* v___x_435_; uint8_t v_isShared_436_; uint8_t v_isSharedCheck_440_; 
lean_dec(v_fst_410_);
lean_dec(v_snd_397_);
lean_del_object(v___x_394_);
v_a_433_ = lean_ctor_get(v___x_418_, 0);
v_isSharedCheck_440_ = !lean_is_exclusive(v___x_418_);
if (v_isSharedCheck_440_ == 0)
{
v___x_435_ = v___x_418_;
v_isShared_436_ = v_isSharedCheck_440_;
goto v_resetjp_434_;
}
else
{
lean_inc(v_a_433_);
lean_dec(v___x_418_);
v___x_435_ = lean_box(0);
v_isShared_436_ = v_isSharedCheck_440_;
goto v_resetjp_434_;
}
v_resetjp_434_:
{
lean_object* v___x_438_; 
if (v_isShared_436_ == 0)
{
v___x_438_ = v___x_435_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v_a_433_);
v___x_438_ = v_reuseFailAlloc_439_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
return v___x_438_;
}
}
}
}
else
{
lean_object* v_a_441_; lean_object* v___x_443_; uint8_t v_isShared_444_; uint8_t v_isSharedCheck_448_; 
lean_dec(v_snd_397_);
lean_del_object(v___x_394_);
v_a_441_ = lean_ctor_get(v___x_408_, 0);
v_isSharedCheck_448_ = !lean_is_exclusive(v___x_408_);
if (v_isSharedCheck_448_ == 0)
{
v___x_443_ = v___x_408_;
v_isShared_444_ = v_isSharedCheck_448_;
goto v_resetjp_442_;
}
else
{
lean_inc(v_a_441_);
lean_dec(v___x_408_);
v___x_443_ = lean_box(0);
v_isShared_444_ = v_isSharedCheck_448_;
goto v_resetjp_442_;
}
v_resetjp_442_:
{
lean_object* v___x_446_; 
if (v_isShared_444_ == 0)
{
v___x_446_ = v___x_443_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v_a_441_);
v___x_446_ = v_reuseFailAlloc_447_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
return v___x_446_;
}
}
}
}
}
}
else
{
lean_object* v___x_450_; lean_object* v___x_452_; 
lean_dec(v_a_388_);
v___x_450_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre___closed__0));
if (v_isShared_391_ == 0)
{
lean_ctor_set(v___x_390_, 0, v___x_450_);
v___x_452_ = v___x_390_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v___x_450_);
v___x_452_ = v_reuseFailAlloc_453_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
return v___x_452_;
}
}
}
}
else
{
lean_object* v_a_455_; lean_object* v___x_457_; uint8_t v_isShared_458_; uint8_t v_isSharedCheck_462_; 
v_a_455_ = lean_ctor_get(v___x_387_, 0);
v_isSharedCheck_462_ = !lean_is_exclusive(v___x_387_);
if (v_isSharedCheck_462_ == 0)
{
v___x_457_ = v___x_387_;
v_isShared_458_ = v_isSharedCheck_462_;
goto v_resetjp_456_;
}
else
{
lean_inc(v_a_455_);
lean_dec(v___x_387_);
v___x_457_ = lean_box(0);
v_isShared_458_ = v_isSharedCheck_462_;
goto v_resetjp_456_;
}
v_resetjp_456_:
{
lean_object* v___x_460_; 
if (v_isShared_458_ == 0)
{
v___x_460_ = v___x_457_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v_a_455_);
v___x_460_ = v_reuseFailAlloc_461_;
goto v_reusejp_459_;
}
v_reusejp_459_:
{
return v___x_460_;
}
}
}
}
else
{
lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; 
lean_dec_ref(v_pattern_373_);
v___x_463_ = lean_box(0);
v___x_464_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_464_, 0, v_e_375_);
lean_ctor_set(v___x_464_, 1, v___x_463_);
lean_ctor_set_uint8(v___x_464_, sizeof(void*)*2, v___x_386_);
v___x_465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_465_, 0, v___x_464_);
v___x_466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_466_, 0, v___x_465_);
return v___x_466_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre___boxed(lean_object* v_pattern_467_, lean_object* v_state_468_, lean_object* v_e_469_, lean_object* v_a_470_, lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_){
_start:
{
lean_object* v_res_478_; 
v_res_478_ = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre(v_pattern_467_, v_state_468_, v_e_469_, v_a_470_, v_a_471_, v_a_472_, v_a_473_, v_a_474_, v_a_475_, v_a_476_);
lean_dec(v_a_476_);
lean_dec_ref(v_a_475_);
lean_dec(v_a_474_);
lean_dec_ref(v_a_473_);
lean_dec(v_a_472_);
lean_dec_ref(v_a_471_);
lean_dec(v_a_470_);
lean_dec(v_state_468_);
return v_res_478_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre_spec__0(lean_object* v_as_479_, size_t v_sz_480_, size_t v_i_481_, lean_object* v_b_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_){
_start:
{
lean_object* v___x_491_; 
v___x_491_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre_spec__0___redArg(v_as_479_, v_sz_480_, v_i_481_, v_b_482_, v___y_486_, v___y_487_, v___y_488_, v___y_489_);
return v___x_491_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre_spec__0___boxed(lean_object* v_as_492_, lean_object* v_sz_493_, lean_object* v_i_494_, lean_object* v_b_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_){
_start:
{
size_t v_sz_boxed_504_; size_t v_i_boxed_505_; lean_object* v_res_506_; 
v_sz_boxed_504_ = lean_unbox_usize(v_sz_493_);
lean_dec(v_sz_493_);
v_i_boxed_505_ = lean_unbox_usize(v_i_494_);
lean_dec(v_i_494_);
v_res_506_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre_spec__0(v_as_492_, v_sz_boxed_504_, v_i_boxed_505_, v_b_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_);
lean_dec(v___y_502_);
lean_dec_ref(v___y_501_);
lean_dec(v___y_500_);
lean_dec_ref(v___y_499_);
lean_dec(v___y_498_);
lean_dec_ref(v___y_497_);
lean_dec(v___y_496_);
lean_dec_ref(v_as_492_);
return v_res_506_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_507_ = lean_box(0);
v___x_508_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_509_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_509_, 0, v___x_508_);
lean_ctor_set(v___x_509_, 1, v___x_507_);
return v___x_509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg(){
_start:
{
lean_object* v___x_511_; lean_object* v___x_512_; 
v___x_511_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg___closed__0);
v___x_512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_512_, 0, v___x_511_);
return v___x_512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg___boxed(lean_object* v___y_513_){
_start:
{
lean_object* v_res_514_; 
v_res_514_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg();
return v_res_514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0(lean_object* v_00_u03b1_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_){
_start:
{
lean_object* v___x_525_; 
v___x_525_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg();
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___boxed(lean_object* v_00_u03b1_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_){
_start:
{
lean_object* v_res_536_; 
v_res_536_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0(v_00_u03b1_526_, v___y_527_, v___y_528_, v___y_529_, v___y_530_, v___y_531_, v___y_532_, v___y_533_, v___y_534_);
lean_dec(v___y_534_);
lean_dec_ref(v___y_533_);
lean_dec(v___y_532_);
lean_dec_ref(v___y_531_);
lean_dec(v___y_530_);
lean_dec_ref(v___y_529_);
lean_dec(v___y_528_);
lean_dec_ref(v___y_527_);
return v_res_536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__2___redArg(lean_object* v_a_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_){
_start:
{
lean_object* v___x_545_; 
v___x_545_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v_a_537_, v___y_538_, v___y_539_, v___y_540_, v___y_541_, v___y_542_, v___y_543_);
return v___x_545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__2___redArg___boxed(lean_object* v_a_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_){
_start:
{
lean_object* v_res_554_; 
v_res_554_ = l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__2___redArg(v_a_546_, v___y_547_, v___y_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_);
lean_dec(v___y_552_);
lean_dec_ref(v___y_551_);
lean_dec(v___y_550_);
lean_dec_ref(v___y_549_);
lean_dec(v___y_548_);
lean_dec_ref(v___y_547_);
return v_res_554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__2(lean_object* v_00_u03b1_555_, lean_object* v_a_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_){
_start:
{
lean_object* v___x_564_; 
v___x_564_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v_a_556_, v___y_557_, v___y_558_, v___y_559_, v___y_560_, v___y_561_, v___y_562_);
return v___x_564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__2___boxed(lean_object* v_00_u03b1_565_, lean_object* v_a_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_){
_start:
{
lean_object* v_res_574_; 
v_res_574_ = l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__2(v_00_u03b1_565_, v_a_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_, v___y_572_);
lean_dec(v___y_572_);
lean_dec_ref(v___y_571_);
lean_dec(v___y_570_);
lean_dec_ref(v___y_569_);
lean_dec(v___y_568_);
lean_dec_ref(v___y_567_);
return v_res_574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__0(lean_object* v_e_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_){
_start:
{
lean_object* v___x_584_; lean_object* v___x_585_; 
v___x_584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_584_, 0, v_e_575_);
v___x_585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_585_, 0, v___x_584_);
return v___x_585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__0___boxed(lean_object* v_e_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_){
_start:
{
lean_object* v_res_595_; 
v_res_595_ = l_Lean_Elab_Tactic_Conv_evalPattern___lam__0(v_e_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_);
lean_dec(v___y_593_);
lean_dec_ref(v___y_592_);
lean_dec(v___y_591_);
lean_dec_ref(v___y_590_);
lean_dec(v___y_589_);
lean_dec_ref(v___y_588_);
lean_dec(v___y_587_);
return v_res_595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__1(lean_object* v___x_596_, lean_object* v___x_597_, uint8_t v___x_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_){
_start:
{
lean_object* v___x_606_; 
v___x_606_ = l_Lean_Elab_Term_elabTerm(v___x_596_, v___x_597_, v___x_598_, v___x_598_, v___y_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_);
if (lean_obj_tag(v___x_606_) == 0)
{
lean_object* v_a_607_; lean_object* v___x_608_; 
v_a_607_ = lean_ctor_get(v___x_606_, 0);
lean_inc(v_a_607_);
lean_dec_ref_known(v___x_606_, 1);
v___x_608_ = l_Lean_Meta_abstractMVars(v_a_607_, v___x_598_, v___y_601_, v___y_602_, v___y_603_, v___y_604_);
return v___x_608_;
}
else
{
lean_object* v_a_609_; lean_object* v___x_611_; uint8_t v_isShared_612_; uint8_t v_isSharedCheck_616_; 
v_a_609_ = lean_ctor_get(v___x_606_, 0);
v_isSharedCheck_616_ = !lean_is_exclusive(v___x_606_);
if (v_isSharedCheck_616_ == 0)
{
v___x_611_ = v___x_606_;
v_isShared_612_ = v_isSharedCheck_616_;
goto v_resetjp_610_;
}
else
{
lean_inc(v_a_609_);
lean_dec(v___x_606_);
v___x_611_ = lean_box(0);
v_isShared_612_ = v_isSharedCheck_616_;
goto v_resetjp_610_;
}
v_resetjp_610_:
{
lean_object* v___x_614_; 
if (v_isShared_612_ == 0)
{
v___x_614_ = v___x_611_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v_a_609_);
v___x_614_ = v_reuseFailAlloc_615_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
return v___x_614_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__1___boxed(lean_object* v___x_617_, lean_object* v___x_618_, lean_object* v___x_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_){
_start:
{
uint8_t v___x_18429__boxed_627_; lean_object* v_res_628_; 
v___x_18429__boxed_627_ = lean_unbox(v___x_619_);
v_res_628_ = l_Lean_Elab_Tactic_Conv_evalPattern___lam__1(v___x_617_, v___x_618_, v___x_18429__boxed_627_, v___y_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_);
lean_dec(v___y_625_);
lean_dec_ref(v___y_624_);
lean_dec(v___y_623_);
lean_dec_ref(v___y_622_);
lean_dec(v___y_621_);
lean_dec_ref(v___y_620_);
return v_res_628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__2(lean_object* v___x_629_, lean_object* v___f_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_){
_start:
{
lean_object* v_fileName_638_; lean_object* v_fileMap_639_; lean_object* v_options_640_; lean_object* v_currRecDepth_641_; lean_object* v_maxRecDepth_642_; lean_object* v_ref_643_; lean_object* v_currNamespace_644_; lean_object* v_openDecls_645_; lean_object* v_initHeartbeats_646_; lean_object* v_maxHeartbeats_647_; lean_object* v_quotContext_648_; lean_object* v_currMacroScope_649_; uint8_t v_diag_650_; lean_object* v_cancelTk_x3f_651_; uint8_t v_suppressElabErrors_652_; lean_object* v_inheritedTraceOptions_653_; lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_662_; 
v_fileName_638_ = lean_ctor_get(v___y_635_, 0);
v_fileMap_639_ = lean_ctor_get(v___y_635_, 1);
v_options_640_ = lean_ctor_get(v___y_635_, 2);
v_currRecDepth_641_ = lean_ctor_get(v___y_635_, 3);
v_maxRecDepth_642_ = lean_ctor_get(v___y_635_, 4);
v_ref_643_ = lean_ctor_get(v___y_635_, 5);
v_currNamespace_644_ = lean_ctor_get(v___y_635_, 6);
v_openDecls_645_ = lean_ctor_get(v___y_635_, 7);
v_initHeartbeats_646_ = lean_ctor_get(v___y_635_, 8);
v_maxHeartbeats_647_ = lean_ctor_get(v___y_635_, 9);
v_quotContext_648_ = lean_ctor_get(v___y_635_, 10);
v_currMacroScope_649_ = lean_ctor_get(v___y_635_, 11);
v_diag_650_ = lean_ctor_get_uint8(v___y_635_, sizeof(void*)*14);
v_cancelTk_x3f_651_ = lean_ctor_get(v___y_635_, 12);
v_suppressElabErrors_652_ = lean_ctor_get_uint8(v___y_635_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_653_ = lean_ctor_get(v___y_635_, 13);
v_isSharedCheck_662_ = !lean_is_exclusive(v___y_635_);
if (v_isSharedCheck_662_ == 0)
{
v___x_655_ = v___y_635_;
v_isShared_656_ = v_isSharedCheck_662_;
goto v_resetjp_654_;
}
else
{
lean_inc(v_inheritedTraceOptions_653_);
lean_inc(v_cancelTk_x3f_651_);
lean_inc(v_currMacroScope_649_);
lean_inc(v_quotContext_648_);
lean_inc(v_maxHeartbeats_647_);
lean_inc(v_initHeartbeats_646_);
lean_inc(v_openDecls_645_);
lean_inc(v_currNamespace_644_);
lean_inc(v_ref_643_);
lean_inc(v_maxRecDepth_642_);
lean_inc(v_currRecDepth_641_);
lean_inc(v_options_640_);
lean_inc(v_fileMap_639_);
lean_inc(v_fileName_638_);
lean_dec(v___y_635_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_662_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
lean_object* v_ref_657_; lean_object* v___x_659_; 
v_ref_657_ = l_Lean_replaceRef(v___x_629_, v_ref_643_);
lean_dec(v_ref_643_);
if (v_isShared_656_ == 0)
{
lean_ctor_set(v___x_655_, 5, v_ref_657_);
v___x_659_ = v___x_655_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_661_; 
v_reuseFailAlloc_661_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_661_, 0, v_fileName_638_);
lean_ctor_set(v_reuseFailAlloc_661_, 1, v_fileMap_639_);
lean_ctor_set(v_reuseFailAlloc_661_, 2, v_options_640_);
lean_ctor_set(v_reuseFailAlloc_661_, 3, v_currRecDepth_641_);
lean_ctor_set(v_reuseFailAlloc_661_, 4, v_maxRecDepth_642_);
lean_ctor_set(v_reuseFailAlloc_661_, 5, v_ref_657_);
lean_ctor_set(v_reuseFailAlloc_661_, 6, v_currNamespace_644_);
lean_ctor_set(v_reuseFailAlloc_661_, 7, v_openDecls_645_);
lean_ctor_set(v_reuseFailAlloc_661_, 8, v_initHeartbeats_646_);
lean_ctor_set(v_reuseFailAlloc_661_, 9, v_maxHeartbeats_647_);
lean_ctor_set(v_reuseFailAlloc_661_, 10, v_quotContext_648_);
lean_ctor_set(v_reuseFailAlloc_661_, 11, v_currMacroScope_649_);
lean_ctor_set(v_reuseFailAlloc_661_, 12, v_cancelTk_x3f_651_);
lean_ctor_set(v_reuseFailAlloc_661_, 13, v_inheritedTraceOptions_653_);
lean_ctor_set_uint8(v_reuseFailAlloc_661_, sizeof(void*)*14, v_diag_650_);
lean_ctor_set_uint8(v_reuseFailAlloc_661_, sizeof(void*)*14 + 1, v_suppressElabErrors_652_);
v___x_659_ = v_reuseFailAlloc_661_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
lean_object* v___x_660_; 
v___x_660_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v___f_630_, v___y_631_, v___y_632_, v___y_633_, v___y_634_, v___x_659_, v___y_636_);
lean_dec_ref(v___x_659_);
return v___x_660_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__2___boxed(lean_object* v___x_663_, lean_object* v___f_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_){
_start:
{
lean_object* v_res_672_; 
v_res_672_ = l_Lean_Elab_Tactic_Conv_evalPattern___lam__2(v___x_663_, v___f_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_, v___y_670_);
lean_dec(v___y_670_);
lean_dec(v___y_668_);
lean_dec_ref(v___y_667_);
lean_dec(v___y_666_);
lean_dec_ref(v___y_665_);
lean_dec(v___x_663_);
return v_res_672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__3(lean_object* v___x_673_, uint8_t v___x_674_, lean_object* v_e_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_){
_start:
{
lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; 
v___x_684_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_684_, 0, v_e_675_);
lean_ctor_set(v___x_684_, 1, v___x_673_);
lean_ctor_set_uint8(v___x_684_, sizeof(void*)*2, v___x_674_);
v___x_685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_685_, 0, v___x_684_);
v___x_686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_686_, 0, v___x_685_);
return v___x_686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__3___boxed(lean_object* v___x_687_, lean_object* v___x_688_, lean_object* v_e_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_){
_start:
{
uint8_t v___x_18523__boxed_698_; lean_object* v_res_699_; 
v___x_18523__boxed_698_ = lean_unbox(v___x_688_);
v_res_699_ = l_Lean_Elab_Tactic_Conv_evalPattern___lam__3(v___x_687_, v___x_18523__boxed_698_, v_e_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_, v___y_694_, v___y_695_, v___y_696_);
lean_dec(v___y_696_);
lean_dec_ref(v___y_695_);
lean_dec(v___y_694_);
lean_dec_ref(v___y_693_);
lean_dec(v___y_692_);
lean_dec_ref(v___y_691_);
lean_dec(v___y_690_);
return v_res_699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__4(lean_object* v___x_700_, lean_object* v_x_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_){
_start:
{
lean_object* v___x_710_; lean_object* v___x_711_; 
v___x_710_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_710_, 0, v___x_700_);
v___x_711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_711_, 0, v___x_710_);
return v___x_711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__4___boxed(lean_object* v___x_712_, lean_object* v_x_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_){
_start:
{
lean_object* v_res_722_; 
v_res_722_ = l_Lean_Elab_Tactic_Conv_evalPattern___lam__4(v___x_712_, v_x_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_, v___y_720_);
lean_dec(v___y_720_);
lean_dec_ref(v___y_719_);
lean_dec(v___y_718_);
lean_dec_ref(v___y_717_);
lean_dec(v___y_716_);
lean_dec_ref(v___y_715_);
lean_dec(v___y_714_);
lean_dec_ref(v_x_713_);
return v_res_722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__5(lean_object* v___x_723_, lean_object* v_x_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_){
_start:
{
lean_object* v___x_733_; 
v___x_733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_733_, 0, v___x_723_);
return v___x_733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__5___boxed(lean_object* v___x_734_, lean_object* v_x_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_){
_start:
{
lean_object* v_res_744_; 
v_res_744_ = l_Lean_Elab_Tactic_Conv_evalPattern___lam__5(v___x_734_, v_x_735_, v___y_736_, v___y_737_, v___y_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_);
lean_dec(v___y_742_);
lean_dec_ref(v___y_741_);
lean_dec(v___y_740_);
lean_dec_ref(v___y_739_);
lean_dec(v___y_738_);
lean_dec_ref(v___y_737_);
lean_dec(v___y_736_);
lean_dec_ref(v_x_735_);
return v_res_744_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__5(size_t v_sz_745_, size_t v_i_746_, lean_object* v_bs_747_){
_start:
{
uint8_t v___x_748_; 
v___x_748_ = lean_usize_dec_lt(v_i_746_, v_sz_745_);
if (v___x_748_ == 0)
{
return v_bs_747_;
}
else
{
lean_object* v_v_749_; lean_object* v_snd_750_; lean_object* v___x_751_; lean_object* v_bs_x27_752_; size_t v___x_753_; size_t v___x_754_; lean_object* v___x_755_; 
v_v_749_ = lean_array_uget_borrowed(v_bs_747_, v_i_746_);
v_snd_750_ = lean_ctor_get(v_v_749_, 1);
lean_inc(v_snd_750_);
v___x_751_ = lean_unsigned_to_nat(0u);
v_bs_x27_752_ = lean_array_uset(v_bs_747_, v_i_746_, v___x_751_);
v___x_753_ = ((size_t)1ULL);
v___x_754_ = lean_usize_add(v_i_746_, v___x_753_);
v___x_755_ = lean_array_uset(v_bs_x27_752_, v_i_746_, v_snd_750_);
v_i_746_ = v___x_754_;
v_bs_747_ = v___x_755_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__5___boxed(lean_object* v_sz_757_, lean_object* v_i_758_, lean_object* v_bs_759_){
_start:
{
size_t v_sz_boxed_760_; size_t v_i_boxed_761_; lean_object* v_res_762_; 
v_sz_boxed_760_ = lean_unbox_usize(v_sz_757_);
lean_dec(v_sz_757_);
v_i_boxed_761_ = lean_unbox_usize(v_i_758_);
lean_dec(v_i_758_);
v_res_762_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__5(v_sz_boxed_760_, v_i_boxed_761_, v_bs_759_);
return v_res_762_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4_spec__5(lean_object* v_msgData_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_){
_start:
{
lean_object* v___x_769_; lean_object* v_env_770_; lean_object* v___x_771_; lean_object* v_mctx_772_; lean_object* v_lctx_773_; lean_object* v_options_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; 
v___x_769_ = lean_st_ref_get(v___y_767_);
v_env_770_ = lean_ctor_get(v___x_769_, 0);
lean_inc_ref(v_env_770_);
lean_dec(v___x_769_);
v___x_771_ = lean_st_ref_get(v___y_765_);
v_mctx_772_ = lean_ctor_get(v___x_771_, 0);
lean_inc_ref(v_mctx_772_);
lean_dec(v___x_771_);
v_lctx_773_ = lean_ctor_get(v___y_764_, 2);
v_options_774_ = lean_ctor_get(v___y_766_, 2);
lean_inc_ref(v_options_774_);
lean_inc_ref(v_lctx_773_);
v___x_775_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_775_, 0, v_env_770_);
lean_ctor_set(v___x_775_, 1, v_mctx_772_);
lean_ctor_set(v___x_775_, 2, v_lctx_773_);
lean_ctor_set(v___x_775_, 3, v_options_774_);
v___x_776_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_776_, 0, v___x_775_);
lean_ctor_set(v___x_776_, 1, v_msgData_763_);
v___x_777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_777_, 0, v___x_776_);
return v___x_777_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4_spec__5___boxed(lean_object* v_msgData_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_){
_start:
{
lean_object* v_res_784_; 
v_res_784_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4_spec__5(v_msgData_778_, v___y_779_, v___y_780_, v___y_781_, v___y_782_);
lean_dec(v___y_782_);
lean_dec_ref(v___y_781_);
lean_dec(v___y_780_);
lean_dec_ref(v___y_779_);
return v_res_784_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg(lean_object* v_msg_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_){
_start:
{
lean_object* v_ref_791_; lean_object* v___x_792_; lean_object* v_a_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_801_; 
v_ref_791_ = lean_ctor_get(v___y_788_, 5);
v___x_792_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4_spec__5(v_msg_785_, v___y_786_, v___y_787_, v___y_788_, v___y_789_);
v_a_793_ = lean_ctor_get(v___x_792_, 0);
v_isSharedCheck_801_ = !lean_is_exclusive(v___x_792_);
if (v_isSharedCheck_801_ == 0)
{
v___x_795_ = v___x_792_;
v_isShared_796_ = v_isSharedCheck_801_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_a_793_);
lean_dec(v___x_792_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_801_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v___x_797_; lean_object* v___x_799_; 
lean_inc(v_ref_791_);
v___x_797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_797_, 0, v_ref_791_);
lean_ctor_set(v___x_797_, 1, v_a_793_);
if (v_isShared_796_ == 0)
{
lean_ctor_set_tag(v___x_795_, 1);
lean_ctor_set(v___x_795_, 0, v___x_797_);
v___x_799_ = v___x_795_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v___x_797_);
v___x_799_ = v_reuseFailAlloc_800_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
return v___x_799_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg___boxed(lean_object* v_msg_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_){
_start:
{
lean_object* v_res_808_; 
v_res_808_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg(v_msg_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_);
lean_dec(v___y_806_);
lean_dec_ref(v___y_805_);
lean_dec(v___y_804_);
lean_dec_ref(v___y_803_);
return v_res_808_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1___redArg(lean_object* v_ref_809_, lean_object* v_msg_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_){
_start:
{
lean_object* v_fileName_820_; lean_object* v_fileMap_821_; lean_object* v_options_822_; lean_object* v_currRecDepth_823_; lean_object* v_maxRecDepth_824_; lean_object* v_ref_825_; lean_object* v_currNamespace_826_; lean_object* v_openDecls_827_; lean_object* v_initHeartbeats_828_; lean_object* v_maxHeartbeats_829_; lean_object* v_quotContext_830_; lean_object* v_currMacroScope_831_; uint8_t v_diag_832_; lean_object* v_cancelTk_x3f_833_; uint8_t v_suppressElabErrors_834_; lean_object* v_inheritedTraceOptions_835_; lean_object* v_ref_836_; lean_object* v___x_837_; lean_object* v___x_838_; 
v_fileName_820_ = lean_ctor_get(v___y_817_, 0);
v_fileMap_821_ = lean_ctor_get(v___y_817_, 1);
v_options_822_ = lean_ctor_get(v___y_817_, 2);
v_currRecDepth_823_ = lean_ctor_get(v___y_817_, 3);
v_maxRecDepth_824_ = lean_ctor_get(v___y_817_, 4);
v_ref_825_ = lean_ctor_get(v___y_817_, 5);
v_currNamespace_826_ = lean_ctor_get(v___y_817_, 6);
v_openDecls_827_ = lean_ctor_get(v___y_817_, 7);
v_initHeartbeats_828_ = lean_ctor_get(v___y_817_, 8);
v_maxHeartbeats_829_ = lean_ctor_get(v___y_817_, 9);
v_quotContext_830_ = lean_ctor_get(v___y_817_, 10);
v_currMacroScope_831_ = lean_ctor_get(v___y_817_, 11);
v_diag_832_ = lean_ctor_get_uint8(v___y_817_, sizeof(void*)*14);
v_cancelTk_x3f_833_ = lean_ctor_get(v___y_817_, 12);
v_suppressElabErrors_834_ = lean_ctor_get_uint8(v___y_817_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_835_ = lean_ctor_get(v___y_817_, 13);
v_ref_836_ = l_Lean_replaceRef(v_ref_809_, v_ref_825_);
lean_inc_ref(v_inheritedTraceOptions_835_);
lean_inc(v_cancelTk_x3f_833_);
lean_inc(v_currMacroScope_831_);
lean_inc(v_quotContext_830_);
lean_inc(v_maxHeartbeats_829_);
lean_inc(v_initHeartbeats_828_);
lean_inc(v_openDecls_827_);
lean_inc(v_currNamespace_826_);
lean_inc(v_maxRecDepth_824_);
lean_inc(v_currRecDepth_823_);
lean_inc_ref(v_options_822_);
lean_inc_ref(v_fileMap_821_);
lean_inc_ref(v_fileName_820_);
v___x_837_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_837_, 0, v_fileName_820_);
lean_ctor_set(v___x_837_, 1, v_fileMap_821_);
lean_ctor_set(v___x_837_, 2, v_options_822_);
lean_ctor_set(v___x_837_, 3, v_currRecDepth_823_);
lean_ctor_set(v___x_837_, 4, v_maxRecDepth_824_);
lean_ctor_set(v___x_837_, 5, v_ref_836_);
lean_ctor_set(v___x_837_, 6, v_currNamespace_826_);
lean_ctor_set(v___x_837_, 7, v_openDecls_827_);
lean_ctor_set(v___x_837_, 8, v_initHeartbeats_828_);
lean_ctor_set(v___x_837_, 9, v_maxHeartbeats_829_);
lean_ctor_set(v___x_837_, 10, v_quotContext_830_);
lean_ctor_set(v___x_837_, 11, v_currMacroScope_831_);
lean_ctor_set(v___x_837_, 12, v_cancelTk_x3f_833_);
lean_ctor_set(v___x_837_, 13, v_inheritedTraceOptions_835_);
lean_ctor_set_uint8(v___x_837_, sizeof(void*)*14, v_diag_832_);
lean_ctor_set_uint8(v___x_837_, sizeof(void*)*14 + 1, v_suppressElabErrors_834_);
v___x_838_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg(v_msg_810_, v___y_815_, v___y_816_, v___x_837_, v___y_818_);
lean_dec_ref_known(v___x_837_, 14);
return v___x_838_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1___redArg___boxed(lean_object* v_ref_839_, lean_object* v_msg_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_){
_start:
{
lean_object* v_res_850_; 
v_res_850_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1___redArg(v_ref_839_, v_msg_840_, v___y_841_, v___y_842_, v___y_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_, v___y_848_);
lean_dec(v___y_848_);
lean_dec_ref(v___y_847_);
lean_dec(v___y_846_);
lean_dec_ref(v___y_845_);
lean_dec(v___y_844_);
lean_dec_ref(v___y_843_);
lean_dec(v___y_842_);
lean_dec_ref(v___y_841_);
lean_dec(v_ref_839_);
return v_res_850_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_852_; lean_object* v___x_853_; 
v___x_852_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg___closed__0));
v___x_853_ = l_Lean_stringToMessageData(v___x_852_);
return v___x_853_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg(size_t v_sz_854_, size_t v_i_855_, lean_object* v_bs_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_){
_start:
{
uint8_t v___x_866_; 
v___x_866_ = lean_usize_dec_lt(v_i_855_, v_sz_854_);
if (v___x_866_ == 0)
{
lean_object* v___x_867_; 
v___x_867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_867_, 0, v_bs_856_);
return v___x_867_;
}
else
{
lean_object* v_v_868_; lean_object* v___x_869_; lean_object* v_bs_x27_870_; lean_object* v_a_872_; lean_object* v___x_877_; uint8_t v_isZero_878_; 
v_v_868_ = lean_array_uget(v_bs_856_, v_i_855_);
v___x_869_ = lean_unsigned_to_nat(0u);
v_bs_x27_870_ = lean_array_uset(v_bs_856_, v_i_855_, v___x_869_);
v___x_877_ = l_Lean_TSyntax_getNat(v_v_868_);
v_isZero_878_ = lean_nat_dec_eq(v___x_877_, v___x_869_);
if (v_isZero_878_ == 1)
{
lean_object* v___x_879_; lean_object* v___x_880_; 
lean_dec(v___x_877_);
v___x_879_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg___closed__1);
v___x_880_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1___redArg(v_v_868_, v___x_879_, v___y_857_, v___y_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_);
lean_dec(v_v_868_);
if (lean_obj_tag(v___x_880_) == 0)
{
lean_object* v_a_881_; 
v_a_881_ = lean_ctor_get(v___x_880_, 0);
lean_inc(v_a_881_);
lean_dec_ref_known(v___x_880_, 1);
v_a_872_ = v_a_881_;
goto v___jp_871_;
}
else
{
lean_object* v_a_882_; lean_object* v___x_884_; uint8_t v_isShared_885_; uint8_t v_isSharedCheck_889_; 
lean_dec_ref(v_bs_x27_870_);
v_a_882_ = lean_ctor_get(v___x_880_, 0);
v_isSharedCheck_889_ = !lean_is_exclusive(v___x_880_);
if (v_isSharedCheck_889_ == 0)
{
v___x_884_ = v___x_880_;
v_isShared_885_ = v_isSharedCheck_889_;
goto v_resetjp_883_;
}
else
{
lean_inc(v_a_882_);
lean_dec(v___x_880_);
v___x_884_ = lean_box(0);
v_isShared_885_ = v_isSharedCheck_889_;
goto v_resetjp_883_;
}
v_resetjp_883_:
{
lean_object* v___x_887_; 
if (v_isShared_885_ == 0)
{
v___x_887_ = v___x_884_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v_a_882_);
v___x_887_ = v_reuseFailAlloc_888_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
return v___x_887_;
}
}
}
}
else
{
lean_object* v___x_890_; lean_object* v_one_891_; lean_object* v_n_892_; lean_object* v___x_893_; 
lean_dec(v_v_868_);
v___x_890_ = lean_usize_to_nat(v_i_855_);
v_one_891_ = lean_unsigned_to_nat(1u);
v_n_892_ = lean_nat_sub(v___x_877_, v_one_891_);
lean_dec(v___x_877_);
v___x_893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_893_, 0, v_n_892_);
lean_ctor_set(v___x_893_, 1, v___x_890_);
v_a_872_ = v___x_893_;
goto v___jp_871_;
}
v___jp_871_:
{
size_t v___x_873_; size_t v___x_874_; lean_object* v___x_875_; 
v___x_873_ = ((size_t)1ULL);
v___x_874_ = lean_usize_add(v_i_855_, v___x_873_);
v___x_875_ = lean_array_uset(v_bs_x27_870_, v_i_855_, v_a_872_);
v_i_855_ = v___x_874_;
v_bs_856_ = v___x_875_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg___boxed(lean_object* v_sz_894_, lean_object* v_i_895_, lean_object* v_bs_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_){
_start:
{
size_t v_sz_boxed_906_; size_t v_i_boxed_907_; lean_object* v_res_908_; 
v_sz_boxed_906_ = lean_unbox_usize(v_sz_894_);
lean_dec(v_sz_894_);
v_i_boxed_907_ = lean_unbox_usize(v_i_895_);
lean_dec(v_i_895_);
v_res_908_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg(v_sz_boxed_906_, v_i_boxed_907_, v_bs_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_);
lean_dec(v___y_904_);
lean_dec_ref(v___y_903_);
lean_dec(v___y_902_);
lean_dec_ref(v___y_901_);
lean_dec(v___y_900_);
lean_dec_ref(v___y_899_);
lean_dec(v___y_898_);
lean_dec_ref(v___y_897_);
return v_res_908_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6_spec__8___redArg(lean_object* v_hi_909_, lean_object* v_pivot_910_, lean_object* v_as_911_, lean_object* v_i_912_, lean_object* v_k_913_){
_start:
{
uint8_t v___x_914_; 
v___x_914_ = lean_nat_dec_lt(v_k_913_, v_hi_909_);
if (v___x_914_ == 0)
{
lean_object* v___x_915_; lean_object* v___x_916_; 
lean_dec(v_k_913_);
v___x_915_ = lean_array_fswap(v_as_911_, v_i_912_, v_hi_909_);
v___x_916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_916_, 0, v_i_912_);
lean_ctor_set(v___x_916_, 1, v___x_915_);
return v___x_916_;
}
else
{
lean_object* v___x_917_; lean_object* v_fst_918_; lean_object* v_fst_919_; uint8_t v___x_920_; 
v___x_917_ = lean_array_fget_borrowed(v_as_911_, v_k_913_);
v_fst_918_ = lean_ctor_get(v___x_917_, 0);
v_fst_919_ = lean_ctor_get(v_pivot_910_, 0);
v___x_920_ = lean_nat_dec_lt(v_fst_918_, v_fst_919_);
if (v___x_920_ == 0)
{
lean_object* v___x_921_; lean_object* v___x_922_; 
v___x_921_ = lean_unsigned_to_nat(1u);
v___x_922_ = lean_nat_add(v_k_913_, v___x_921_);
lean_dec(v_k_913_);
v_k_913_ = v___x_922_;
goto _start;
}
else
{
lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; 
v___x_924_ = lean_array_fswap(v_as_911_, v_i_912_, v_k_913_);
v___x_925_ = lean_unsigned_to_nat(1u);
v___x_926_ = lean_nat_add(v_i_912_, v___x_925_);
lean_dec(v_i_912_);
v___x_927_ = lean_nat_add(v_k_913_, v___x_925_);
lean_dec(v_k_913_);
v_as_911_ = v___x_924_;
v_i_912_ = v___x_926_;
v_k_913_ = v___x_927_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6_spec__8___redArg___boxed(lean_object* v_hi_929_, lean_object* v_pivot_930_, lean_object* v_as_931_, lean_object* v_i_932_, lean_object* v_k_933_){
_start:
{
lean_object* v_res_934_; 
v_res_934_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6_spec__8___redArg(v_hi_929_, v_pivot_930_, v_as_931_, v_i_932_, v_k_933_);
lean_dec_ref(v_pivot_930_);
lean_dec(v_hi_929_);
return v_res_934_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg___lam__0(lean_object* v_x1_935_, lean_object* v_x2_936_){
_start:
{
lean_object* v_fst_937_; lean_object* v_fst_938_; uint8_t v___x_939_; 
v_fst_937_ = lean_ctor_get(v_x1_935_, 0);
v_fst_938_ = lean_ctor_get(v_x2_936_, 0);
v___x_939_ = lean_nat_dec_lt(v_fst_937_, v_fst_938_);
return v___x_939_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg___lam__0___boxed(lean_object* v_x1_940_, lean_object* v_x2_941_){
_start:
{
uint8_t v_res_942_; lean_object* v_r_943_; 
v_res_942_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg___lam__0(v_x1_940_, v_x2_941_);
lean_dec_ref(v_x2_941_);
lean_dec_ref(v_x1_940_);
v_r_943_ = lean_box(v_res_942_);
return v_r_943_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg(lean_object* v_n_944_, lean_object* v_as_945_, lean_object* v_lo_946_, lean_object* v_hi_947_){
_start:
{
lean_object* v___y_949_; uint8_t v___x_959_; 
v___x_959_ = lean_nat_dec_lt(v_lo_946_, v_hi_947_);
if (v___x_959_ == 0)
{
lean_dec(v_lo_946_);
return v_as_945_;
}
else
{
lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v_mid_962_; lean_object* v___y_964_; lean_object* v___y_970_; lean_object* v___x_975_; lean_object* v___x_976_; uint8_t v___x_977_; 
v___x_960_ = lean_nat_add(v_lo_946_, v_hi_947_);
v___x_961_ = lean_unsigned_to_nat(1u);
v_mid_962_ = lean_nat_shiftr(v___x_960_, v___x_961_);
lean_dec(v___x_960_);
v___x_975_ = lean_array_fget_borrowed(v_as_945_, v_mid_962_);
v___x_976_ = lean_array_fget_borrowed(v_as_945_, v_lo_946_);
v___x_977_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg___lam__0(v___x_975_, v___x_976_);
if (v___x_977_ == 0)
{
v___y_970_ = v_as_945_;
goto v___jp_969_;
}
else
{
lean_object* v___x_978_; 
v___x_978_ = lean_array_fswap(v_as_945_, v_lo_946_, v_mid_962_);
v___y_970_ = v___x_978_;
goto v___jp_969_;
}
v___jp_963_:
{
lean_object* v___x_965_; lean_object* v___x_966_; uint8_t v___x_967_; 
v___x_965_ = lean_array_fget_borrowed(v___y_964_, v_mid_962_);
v___x_966_ = lean_array_fget_borrowed(v___y_964_, v_hi_947_);
v___x_967_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg___lam__0(v___x_965_, v___x_966_);
if (v___x_967_ == 0)
{
lean_dec(v_mid_962_);
v___y_949_ = v___y_964_;
goto v___jp_948_;
}
else
{
lean_object* v___x_968_; 
v___x_968_ = lean_array_fswap(v___y_964_, v_mid_962_, v_hi_947_);
lean_dec(v_mid_962_);
v___y_949_ = v___x_968_;
goto v___jp_948_;
}
}
v___jp_969_:
{
lean_object* v___x_971_; lean_object* v___x_972_; uint8_t v___x_973_; 
v___x_971_ = lean_array_fget_borrowed(v___y_970_, v_hi_947_);
v___x_972_ = lean_array_fget_borrowed(v___y_970_, v_lo_946_);
v___x_973_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg___lam__0(v___x_971_, v___x_972_);
if (v___x_973_ == 0)
{
v___y_964_ = v___y_970_;
goto v___jp_963_;
}
else
{
lean_object* v___x_974_; 
v___x_974_ = lean_array_fswap(v___y_970_, v_lo_946_, v_hi_947_);
v___y_964_ = v___x_974_;
goto v___jp_963_;
}
}
}
v___jp_948_:
{
lean_object* v_pivot_950_; lean_object* v___x_951_; lean_object* v_fst_952_; lean_object* v_snd_953_; uint8_t v___x_954_; 
v_pivot_950_ = lean_array_fget(v___y_949_, v_hi_947_);
lean_inc_n(v_lo_946_, 2);
v___x_951_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6_spec__8___redArg(v_hi_947_, v_pivot_950_, v___y_949_, v_lo_946_, v_lo_946_);
lean_dec(v_pivot_950_);
v_fst_952_ = lean_ctor_get(v___x_951_, 0);
lean_inc(v_fst_952_);
v_snd_953_ = lean_ctor_get(v___x_951_, 1);
lean_inc(v_snd_953_);
lean_dec_ref(v___x_951_);
v___x_954_ = lean_nat_dec_le(v_hi_947_, v_fst_952_);
if (v___x_954_ == 0)
{
lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; 
v___x_955_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg(v_n_944_, v_snd_953_, v_lo_946_, v_fst_952_);
v___x_956_ = lean_unsigned_to_nat(1u);
v___x_957_ = lean_nat_add(v_fst_952_, v___x_956_);
lean_dec(v_fst_952_);
v_as_945_ = v___x_955_;
v_lo_946_ = v___x_957_;
goto _start;
}
else
{
lean_dec(v_fst_952_);
lean_dec(v_lo_946_);
return v_snd_953_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg___boxed(lean_object* v_n_979_, lean_object* v_as_980_, lean_object* v_lo_981_, lean_object* v_hi_982_){
_start:
{
lean_object* v_res_983_; 
v_res_983_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg(v_n_979_, v_as_980_, v_lo_981_, v_hi_982_);
lean_dec(v_hi_982_);
lean_dec(v_n_979_);
return v_res_983_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__12_spec__16___redArg(lean_object* v_x_984_, lean_object* v_x_985_, lean_object* v_x_986_, lean_object* v_x_987_){
_start:
{
lean_object* v_ks_988_; lean_object* v_vs_989_; lean_object* v___x_991_; uint8_t v_isShared_992_; uint8_t v_isSharedCheck_1013_; 
v_ks_988_ = lean_ctor_get(v_x_984_, 0);
v_vs_989_ = lean_ctor_get(v_x_984_, 1);
v_isSharedCheck_1013_ = !lean_is_exclusive(v_x_984_);
if (v_isSharedCheck_1013_ == 0)
{
v___x_991_ = v_x_984_;
v_isShared_992_ = v_isSharedCheck_1013_;
goto v_resetjp_990_;
}
else
{
lean_inc(v_vs_989_);
lean_inc(v_ks_988_);
lean_dec(v_x_984_);
v___x_991_ = lean_box(0);
v_isShared_992_ = v_isSharedCheck_1013_;
goto v_resetjp_990_;
}
v_resetjp_990_:
{
lean_object* v___x_993_; uint8_t v___x_994_; 
v___x_993_ = lean_array_get_size(v_ks_988_);
v___x_994_ = lean_nat_dec_lt(v_x_985_, v___x_993_);
if (v___x_994_ == 0)
{
lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_998_; 
lean_dec(v_x_985_);
v___x_995_ = lean_array_push(v_ks_988_, v_x_986_);
v___x_996_ = lean_array_push(v_vs_989_, v_x_987_);
if (v_isShared_992_ == 0)
{
lean_ctor_set(v___x_991_, 1, v___x_996_);
lean_ctor_set(v___x_991_, 0, v___x_995_);
v___x_998_ = v___x_991_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v___x_995_);
lean_ctor_set(v_reuseFailAlloc_999_, 1, v___x_996_);
v___x_998_ = v_reuseFailAlloc_999_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
return v___x_998_;
}
}
else
{
lean_object* v_k_x27_1000_; uint8_t v___x_1001_; 
v_k_x27_1000_ = lean_array_fget_borrowed(v_ks_988_, v_x_985_);
v___x_1001_ = l_Lean_instBEqMVarId_beq(v_x_986_, v_k_x27_1000_);
if (v___x_1001_ == 0)
{
lean_object* v___x_1003_; 
if (v_isShared_992_ == 0)
{
v___x_1003_ = v___x_991_;
goto v_reusejp_1002_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v_ks_988_);
lean_ctor_set(v_reuseFailAlloc_1007_, 1, v_vs_989_);
v___x_1003_ = v_reuseFailAlloc_1007_;
goto v_reusejp_1002_;
}
v_reusejp_1002_:
{
lean_object* v___x_1004_; lean_object* v___x_1005_; 
v___x_1004_ = lean_unsigned_to_nat(1u);
v___x_1005_ = lean_nat_add(v_x_985_, v___x_1004_);
lean_dec(v_x_985_);
v_x_984_ = v___x_1003_;
v_x_985_ = v___x_1005_;
goto _start;
}
}
else
{
lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1011_; 
v___x_1008_ = lean_array_fset(v_ks_988_, v_x_985_, v_x_986_);
v___x_1009_ = lean_array_fset(v_vs_989_, v_x_985_, v_x_987_);
lean_dec(v_x_985_);
if (v_isShared_992_ == 0)
{
lean_ctor_set(v___x_991_, 1, v___x_1009_);
lean_ctor_set(v___x_991_, 0, v___x_1008_);
v___x_1011_ = v___x_991_;
goto v_reusejp_1010_;
}
else
{
lean_object* v_reuseFailAlloc_1012_; 
v_reuseFailAlloc_1012_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v___x_1008_);
lean_ctor_set(v_reuseFailAlloc_1012_, 1, v___x_1009_);
v___x_1011_ = v_reuseFailAlloc_1012_;
goto v_reusejp_1010_;
}
v_reusejp_1010_:
{
return v___x_1011_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__12___redArg(lean_object* v_n_1014_, lean_object* v_k_1015_, lean_object* v_v_1016_){
_start:
{
lean_object* v___x_1017_; lean_object* v___x_1018_; 
v___x_1017_ = lean_unsigned_to_nat(0u);
v___x_1018_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__12_spec__16___redArg(v_n_1014_, v___x_1017_, v_k_1015_, v_v_1016_);
return v___x_1018_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_1019_; 
v___x_1019_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1019_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg(lean_object* v_x_1020_, size_t v_x_1021_, size_t v_x_1022_, lean_object* v_x_1023_, lean_object* v_x_1024_){
_start:
{
if (lean_obj_tag(v_x_1020_) == 0)
{
lean_object* v_es_1025_; size_t v___x_1026_; size_t v___x_1027_; lean_object* v_j_1028_; lean_object* v___x_1029_; uint8_t v___x_1030_; 
v_es_1025_ = lean_ctor_get(v_x_1020_, 0);
v___x_1026_ = ((size_t)31ULL);
v___x_1027_ = lean_usize_land(v_x_1021_, v___x_1026_);
v_j_1028_ = lean_usize_to_nat(v___x_1027_);
v___x_1029_ = lean_array_get_size(v_es_1025_);
v___x_1030_ = lean_nat_dec_lt(v_j_1028_, v___x_1029_);
if (v___x_1030_ == 0)
{
lean_dec(v_j_1028_);
lean_dec(v_x_1024_);
lean_dec(v_x_1023_);
return v_x_1020_;
}
else
{
lean_object* v___x_1032_; uint8_t v_isShared_1033_; uint8_t v_isSharedCheck_1069_; 
lean_inc_ref(v_es_1025_);
v_isSharedCheck_1069_ = !lean_is_exclusive(v_x_1020_);
if (v_isSharedCheck_1069_ == 0)
{
lean_object* v_unused_1070_; 
v_unused_1070_ = lean_ctor_get(v_x_1020_, 0);
lean_dec(v_unused_1070_);
v___x_1032_ = v_x_1020_;
v_isShared_1033_ = v_isSharedCheck_1069_;
goto v_resetjp_1031_;
}
else
{
lean_dec(v_x_1020_);
v___x_1032_ = lean_box(0);
v_isShared_1033_ = v_isSharedCheck_1069_;
goto v_resetjp_1031_;
}
v_resetjp_1031_:
{
lean_object* v_v_1034_; lean_object* v___x_1035_; lean_object* v_xs_x27_1036_; lean_object* v___y_1038_; 
v_v_1034_ = lean_array_fget(v_es_1025_, v_j_1028_);
v___x_1035_ = lean_box(0);
v_xs_x27_1036_ = lean_array_fset(v_es_1025_, v_j_1028_, v___x_1035_);
switch(lean_obj_tag(v_v_1034_))
{
case 0:
{
lean_object* v_key_1043_; lean_object* v_val_1044_; lean_object* v___x_1046_; uint8_t v_isShared_1047_; uint8_t v_isSharedCheck_1054_; 
v_key_1043_ = lean_ctor_get(v_v_1034_, 0);
v_val_1044_ = lean_ctor_get(v_v_1034_, 1);
v_isSharedCheck_1054_ = !lean_is_exclusive(v_v_1034_);
if (v_isSharedCheck_1054_ == 0)
{
v___x_1046_ = v_v_1034_;
v_isShared_1047_ = v_isSharedCheck_1054_;
goto v_resetjp_1045_;
}
else
{
lean_inc(v_val_1044_);
lean_inc(v_key_1043_);
lean_dec(v_v_1034_);
v___x_1046_ = lean_box(0);
v_isShared_1047_ = v_isSharedCheck_1054_;
goto v_resetjp_1045_;
}
v_resetjp_1045_:
{
uint8_t v___x_1048_; 
v___x_1048_ = l_Lean_instBEqMVarId_beq(v_x_1023_, v_key_1043_);
if (v___x_1048_ == 0)
{
lean_object* v___x_1049_; lean_object* v___x_1050_; 
lean_del_object(v___x_1046_);
v___x_1049_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1043_, v_val_1044_, v_x_1023_, v_x_1024_);
v___x_1050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1050_, 0, v___x_1049_);
v___y_1038_ = v___x_1050_;
goto v___jp_1037_;
}
else
{
lean_object* v___x_1052_; 
lean_dec(v_val_1044_);
lean_dec(v_key_1043_);
if (v_isShared_1047_ == 0)
{
lean_ctor_set(v___x_1046_, 1, v_x_1024_);
lean_ctor_set(v___x_1046_, 0, v_x_1023_);
v___x_1052_ = v___x_1046_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v_x_1023_);
lean_ctor_set(v_reuseFailAlloc_1053_, 1, v_x_1024_);
v___x_1052_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
v___y_1038_ = v___x_1052_;
goto v___jp_1037_;
}
}
}
}
case 1:
{
lean_object* v_node_1055_; lean_object* v___x_1057_; uint8_t v_isShared_1058_; uint8_t v_isSharedCheck_1067_; 
v_node_1055_ = lean_ctor_get(v_v_1034_, 0);
v_isSharedCheck_1067_ = !lean_is_exclusive(v_v_1034_);
if (v_isSharedCheck_1067_ == 0)
{
v___x_1057_ = v_v_1034_;
v_isShared_1058_ = v_isSharedCheck_1067_;
goto v_resetjp_1056_;
}
else
{
lean_inc(v_node_1055_);
lean_dec(v_v_1034_);
v___x_1057_ = lean_box(0);
v_isShared_1058_ = v_isSharedCheck_1067_;
goto v_resetjp_1056_;
}
v_resetjp_1056_:
{
size_t v___x_1059_; size_t v___x_1060_; size_t v___x_1061_; size_t v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1065_; 
v___x_1059_ = ((size_t)5ULL);
v___x_1060_ = lean_usize_shift_right(v_x_1021_, v___x_1059_);
v___x_1061_ = ((size_t)1ULL);
v___x_1062_ = lean_usize_add(v_x_1022_, v___x_1061_);
v___x_1063_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg(v_node_1055_, v___x_1060_, v___x_1062_, v_x_1023_, v_x_1024_);
if (v_isShared_1058_ == 0)
{
lean_ctor_set(v___x_1057_, 0, v___x_1063_);
v___x_1065_ = v___x_1057_;
goto v_reusejp_1064_;
}
else
{
lean_object* v_reuseFailAlloc_1066_; 
v_reuseFailAlloc_1066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1066_, 0, v___x_1063_);
v___x_1065_ = v_reuseFailAlloc_1066_;
goto v_reusejp_1064_;
}
v_reusejp_1064_:
{
v___y_1038_ = v___x_1065_;
goto v___jp_1037_;
}
}
}
default: 
{
lean_object* v___x_1068_; 
v___x_1068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1068_, 0, v_x_1023_);
lean_ctor_set(v___x_1068_, 1, v_x_1024_);
v___y_1038_ = v___x_1068_;
goto v___jp_1037_;
}
}
v___jp_1037_:
{
lean_object* v___x_1039_; lean_object* v___x_1041_; 
v___x_1039_ = lean_array_fset(v_xs_x27_1036_, v_j_1028_, v___y_1038_);
lean_dec(v_j_1028_);
if (v_isShared_1033_ == 0)
{
lean_ctor_set(v___x_1032_, 0, v___x_1039_);
v___x_1041_ = v___x_1032_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v___x_1039_);
v___x_1041_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
return v___x_1041_;
}
}
}
}
}
else
{
lean_object* v_ks_1071_; lean_object* v_vs_1072_; lean_object* v___x_1074_; uint8_t v_isShared_1075_; uint8_t v_isSharedCheck_1092_; 
v_ks_1071_ = lean_ctor_get(v_x_1020_, 0);
v_vs_1072_ = lean_ctor_get(v_x_1020_, 1);
v_isSharedCheck_1092_ = !lean_is_exclusive(v_x_1020_);
if (v_isSharedCheck_1092_ == 0)
{
v___x_1074_ = v_x_1020_;
v_isShared_1075_ = v_isSharedCheck_1092_;
goto v_resetjp_1073_;
}
else
{
lean_inc(v_vs_1072_);
lean_inc(v_ks_1071_);
lean_dec(v_x_1020_);
v___x_1074_ = lean_box(0);
v_isShared_1075_ = v_isSharedCheck_1092_;
goto v_resetjp_1073_;
}
v_resetjp_1073_:
{
lean_object* v___x_1077_; 
if (v_isShared_1075_ == 0)
{
v___x_1077_ = v___x_1074_;
goto v_reusejp_1076_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v_ks_1071_);
lean_ctor_set(v_reuseFailAlloc_1091_, 1, v_vs_1072_);
v___x_1077_ = v_reuseFailAlloc_1091_;
goto v_reusejp_1076_;
}
v_reusejp_1076_:
{
lean_object* v_newNode_1078_; uint8_t v___y_1080_; size_t v___x_1086_; uint8_t v___x_1087_; 
v_newNode_1078_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__12___redArg(v___x_1077_, v_x_1023_, v_x_1024_);
v___x_1086_ = ((size_t)7ULL);
v___x_1087_ = lean_usize_dec_le(v___x_1086_, v_x_1022_);
if (v___x_1087_ == 0)
{
lean_object* v___x_1088_; lean_object* v___x_1089_; uint8_t v___x_1090_; 
v___x_1088_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1078_);
v___x_1089_ = lean_unsigned_to_nat(4u);
v___x_1090_ = lean_nat_dec_lt(v___x_1088_, v___x_1089_);
lean_dec(v___x_1088_);
v___y_1080_ = v___x_1090_;
goto v___jp_1079_;
}
else
{
v___y_1080_ = v___x_1087_;
goto v___jp_1079_;
}
v___jp_1079_:
{
if (v___y_1080_ == 0)
{
lean_object* v_ks_1081_; lean_object* v_vs_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; 
v_ks_1081_ = lean_ctor_get(v_newNode_1078_, 0);
lean_inc_ref(v_ks_1081_);
v_vs_1082_ = lean_ctor_get(v_newNode_1078_, 1);
lean_inc_ref(v_vs_1082_);
lean_dec_ref(v_newNode_1078_);
v___x_1083_ = lean_unsigned_to_nat(0u);
v___x_1084_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__0);
v___x_1085_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__13___redArg(v_x_1022_, v_ks_1081_, v_vs_1082_, v___x_1083_, v___x_1084_);
lean_dec_ref(v_vs_1082_);
lean_dec_ref(v_ks_1081_);
return v___x_1085_;
}
else
{
return v_newNode_1078_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__13___redArg(size_t v_depth_1093_, lean_object* v_keys_1094_, lean_object* v_vals_1095_, lean_object* v_i_1096_, lean_object* v_entries_1097_){
_start:
{
lean_object* v___x_1098_; uint8_t v___x_1099_; 
v___x_1098_ = lean_array_get_size(v_keys_1094_);
v___x_1099_ = lean_nat_dec_lt(v_i_1096_, v___x_1098_);
if (v___x_1099_ == 0)
{
lean_dec(v_i_1096_);
return v_entries_1097_;
}
else
{
lean_object* v_k_1100_; lean_object* v_v_1101_; uint64_t v___x_1102_; size_t v_h_1103_; size_t v___x_1104_; lean_object* v___x_1105_; size_t v___x_1106_; size_t v___x_1107_; size_t v___x_1108_; size_t v_h_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; 
v_k_1100_ = lean_array_fget_borrowed(v_keys_1094_, v_i_1096_);
v_v_1101_ = lean_array_fget_borrowed(v_vals_1095_, v_i_1096_);
v___x_1102_ = l_Lean_instHashableMVarId_hash(v_k_1100_);
v_h_1103_ = lean_uint64_to_usize(v___x_1102_);
v___x_1104_ = ((size_t)5ULL);
v___x_1105_ = lean_unsigned_to_nat(1u);
v___x_1106_ = ((size_t)1ULL);
v___x_1107_ = lean_usize_sub(v_depth_1093_, v___x_1106_);
v___x_1108_ = lean_usize_mul(v___x_1104_, v___x_1107_);
v_h_1109_ = lean_usize_shift_right(v_h_1103_, v___x_1108_);
v___x_1110_ = lean_nat_add(v_i_1096_, v___x_1105_);
lean_dec(v_i_1096_);
lean_inc(v_v_1101_);
lean_inc(v_k_1100_);
v___x_1111_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg(v_entries_1097_, v_h_1109_, v_depth_1093_, v_k_1100_, v_v_1101_);
v_i_1096_ = v___x_1110_;
v_entries_1097_ = v___x_1111_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__13___redArg___boxed(lean_object* v_depth_1113_, lean_object* v_keys_1114_, lean_object* v_vals_1115_, lean_object* v_i_1116_, lean_object* v_entries_1117_){
_start:
{
size_t v_depth_boxed_1118_; lean_object* v_res_1119_; 
v_depth_boxed_1118_ = lean_unbox_usize(v_depth_1113_);
lean_dec(v_depth_1113_);
v_res_1119_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__13___redArg(v_depth_boxed_1118_, v_keys_1114_, v_vals_1115_, v_i_1116_, v_entries_1117_);
lean_dec_ref(v_vals_1115_);
lean_dec_ref(v_keys_1114_);
return v_res_1119_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___boxed(lean_object* v_x_1120_, lean_object* v_x_1121_, lean_object* v_x_1122_, lean_object* v_x_1123_, lean_object* v_x_1124_){
_start:
{
size_t v_x_18981__boxed_1125_; size_t v_x_18982__boxed_1126_; lean_object* v_res_1127_; 
v_x_18981__boxed_1125_ = lean_unbox_usize(v_x_1121_);
lean_dec(v_x_1121_);
v_x_18982__boxed_1126_ = lean_unbox_usize(v_x_1122_);
lean_dec(v_x_1122_);
v_res_1127_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg(v_x_1120_, v_x_18981__boxed_1125_, v_x_18982__boxed_1126_, v_x_1123_, v_x_1124_);
return v_res_1127_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3___redArg(lean_object* v_x_1128_, lean_object* v_x_1129_, lean_object* v_x_1130_){
_start:
{
uint64_t v___x_1131_; size_t v___x_1132_; size_t v___x_1133_; lean_object* v___x_1134_; 
v___x_1131_ = l_Lean_instHashableMVarId_hash(v_x_1129_);
v___x_1132_ = lean_uint64_to_usize(v___x_1131_);
v___x_1133_ = ((size_t)1ULL);
v___x_1134_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg(v_x_1128_, v___x_1132_, v___x_1133_, v_x_1129_, v_x_1130_);
return v___x_1134_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3___redArg(lean_object* v_mvarId_1135_, lean_object* v_val_1136_, lean_object* v___y_1137_){
_start:
{
lean_object* v___x_1139_; lean_object* v_mctx_1140_; lean_object* v_cache_1141_; lean_object* v_zetaDeltaFVarIds_1142_; lean_object* v_postponed_1143_; lean_object* v_diag_1144_; lean_object* v___x_1146_; uint8_t v_isShared_1147_; uint8_t v_isSharedCheck_1172_; 
v___x_1139_ = lean_st_ref_take(v___y_1137_);
v_mctx_1140_ = lean_ctor_get(v___x_1139_, 0);
v_cache_1141_ = lean_ctor_get(v___x_1139_, 1);
v_zetaDeltaFVarIds_1142_ = lean_ctor_get(v___x_1139_, 2);
v_postponed_1143_ = lean_ctor_get(v___x_1139_, 3);
v_diag_1144_ = lean_ctor_get(v___x_1139_, 4);
v_isSharedCheck_1172_ = !lean_is_exclusive(v___x_1139_);
if (v_isSharedCheck_1172_ == 0)
{
v___x_1146_ = v___x_1139_;
v_isShared_1147_ = v_isSharedCheck_1172_;
goto v_resetjp_1145_;
}
else
{
lean_inc(v_diag_1144_);
lean_inc(v_postponed_1143_);
lean_inc(v_zetaDeltaFVarIds_1142_);
lean_inc(v_cache_1141_);
lean_inc(v_mctx_1140_);
lean_dec(v___x_1139_);
v___x_1146_ = lean_box(0);
v_isShared_1147_ = v_isSharedCheck_1172_;
goto v_resetjp_1145_;
}
v_resetjp_1145_:
{
lean_object* v_depth_1148_; lean_object* v_levelAssignDepth_1149_; lean_object* v_lmvarCounter_1150_; lean_object* v_mvarCounter_1151_; lean_object* v_lDecls_1152_; lean_object* v_decls_1153_; lean_object* v_userNames_1154_; lean_object* v_lAssignment_1155_; lean_object* v_eAssignment_1156_; lean_object* v_dAssignment_1157_; lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1171_; 
v_depth_1148_ = lean_ctor_get(v_mctx_1140_, 0);
v_levelAssignDepth_1149_ = lean_ctor_get(v_mctx_1140_, 1);
v_lmvarCounter_1150_ = lean_ctor_get(v_mctx_1140_, 2);
v_mvarCounter_1151_ = lean_ctor_get(v_mctx_1140_, 3);
v_lDecls_1152_ = lean_ctor_get(v_mctx_1140_, 4);
v_decls_1153_ = lean_ctor_get(v_mctx_1140_, 5);
v_userNames_1154_ = lean_ctor_get(v_mctx_1140_, 6);
v_lAssignment_1155_ = lean_ctor_get(v_mctx_1140_, 7);
v_eAssignment_1156_ = lean_ctor_get(v_mctx_1140_, 8);
v_dAssignment_1157_ = lean_ctor_get(v_mctx_1140_, 9);
v_isSharedCheck_1171_ = !lean_is_exclusive(v_mctx_1140_);
if (v_isSharedCheck_1171_ == 0)
{
v___x_1159_ = v_mctx_1140_;
v_isShared_1160_ = v_isSharedCheck_1171_;
goto v_resetjp_1158_;
}
else
{
lean_inc(v_dAssignment_1157_);
lean_inc(v_eAssignment_1156_);
lean_inc(v_lAssignment_1155_);
lean_inc(v_userNames_1154_);
lean_inc(v_decls_1153_);
lean_inc(v_lDecls_1152_);
lean_inc(v_mvarCounter_1151_);
lean_inc(v_lmvarCounter_1150_);
lean_inc(v_levelAssignDepth_1149_);
lean_inc(v_depth_1148_);
lean_dec(v_mctx_1140_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1171_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
lean_object* v___x_1161_; lean_object* v___x_1163_; 
v___x_1161_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3___redArg(v_eAssignment_1156_, v_mvarId_1135_, v_val_1136_);
if (v_isShared_1160_ == 0)
{
lean_ctor_set(v___x_1159_, 8, v___x_1161_);
v___x_1163_ = v___x_1159_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v_depth_1148_);
lean_ctor_set(v_reuseFailAlloc_1170_, 1, v_levelAssignDepth_1149_);
lean_ctor_set(v_reuseFailAlloc_1170_, 2, v_lmvarCounter_1150_);
lean_ctor_set(v_reuseFailAlloc_1170_, 3, v_mvarCounter_1151_);
lean_ctor_set(v_reuseFailAlloc_1170_, 4, v_lDecls_1152_);
lean_ctor_set(v_reuseFailAlloc_1170_, 5, v_decls_1153_);
lean_ctor_set(v_reuseFailAlloc_1170_, 6, v_userNames_1154_);
lean_ctor_set(v_reuseFailAlloc_1170_, 7, v_lAssignment_1155_);
lean_ctor_set(v_reuseFailAlloc_1170_, 8, v___x_1161_);
lean_ctor_set(v_reuseFailAlloc_1170_, 9, v_dAssignment_1157_);
v___x_1163_ = v_reuseFailAlloc_1170_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
lean_object* v___x_1165_; 
if (v_isShared_1147_ == 0)
{
lean_ctor_set(v___x_1146_, 0, v___x_1163_);
v___x_1165_ = v___x_1146_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v___x_1163_);
lean_ctor_set(v_reuseFailAlloc_1169_, 1, v_cache_1141_);
lean_ctor_set(v_reuseFailAlloc_1169_, 2, v_zetaDeltaFVarIds_1142_);
lean_ctor_set(v_reuseFailAlloc_1169_, 3, v_postponed_1143_);
lean_ctor_set(v_reuseFailAlloc_1169_, 4, v_diag_1144_);
v___x_1165_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; 
v___x_1166_ = lean_st_ref_set(v___y_1137_, v___x_1165_);
v___x_1167_ = lean_box(0);
v___x_1168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1168_, 0, v___x_1167_);
return v___x_1168_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3___redArg___boxed(lean_object* v_mvarId_1173_, lean_object* v_val_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_){
_start:
{
lean_object* v_res_1177_; 
v_res_1177_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3___redArg(v_mvarId_1173_, v_val_1174_, v___y_1175_);
lean_dec(v___y_1175_);
return v_res_1177_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg___lam__0(lean_object* v_x1_1178_, lean_object* v_x2_1179_){
_start:
{
lean_object* v_fst_1180_; lean_object* v_fst_1181_; uint8_t v___x_1182_; 
v_fst_1180_ = lean_ctor_get(v_x1_1178_, 0);
v_fst_1181_ = lean_ctor_get(v_x2_1179_, 0);
v___x_1182_ = lean_nat_dec_lt(v_fst_1180_, v_fst_1181_);
return v___x_1182_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg___lam__0___boxed(lean_object* v_x1_1183_, lean_object* v_x2_1184_){
_start:
{
uint8_t v_res_1185_; lean_object* v_r_1186_; 
v_res_1185_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg___lam__0(v_x1_1183_, v_x2_1184_);
lean_dec_ref(v_x2_1184_);
lean_dec_ref(v_x1_1183_);
v_r_1186_ = lean_box(v_res_1185_);
return v_r_1186_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9_spec__13___redArg(lean_object* v_hi_1187_, lean_object* v_pivot_1188_, lean_object* v_as_1189_, lean_object* v_i_1190_, lean_object* v_k_1191_){
_start:
{
uint8_t v___x_1192_; 
v___x_1192_ = lean_nat_dec_lt(v_k_1191_, v_hi_1187_);
if (v___x_1192_ == 0)
{
lean_object* v___x_1193_; lean_object* v___x_1194_; 
lean_dec(v_k_1191_);
v___x_1193_ = lean_array_fswap(v_as_1189_, v_i_1190_, v_hi_1187_);
v___x_1194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1194_, 0, v_i_1190_);
lean_ctor_set(v___x_1194_, 1, v___x_1193_);
return v___x_1194_;
}
else
{
lean_object* v___x_1195_; lean_object* v_fst_1196_; lean_object* v_fst_1197_; uint8_t v___x_1198_; 
v___x_1195_ = lean_array_fget_borrowed(v_as_1189_, v_k_1191_);
v_fst_1196_ = lean_ctor_get(v___x_1195_, 0);
v_fst_1197_ = lean_ctor_get(v_pivot_1188_, 0);
v___x_1198_ = lean_nat_dec_lt(v_fst_1196_, v_fst_1197_);
if (v___x_1198_ == 0)
{
lean_object* v___x_1199_; lean_object* v___x_1200_; 
v___x_1199_ = lean_unsigned_to_nat(1u);
v___x_1200_ = lean_nat_add(v_k_1191_, v___x_1199_);
lean_dec(v_k_1191_);
v_k_1191_ = v___x_1200_;
goto _start;
}
else
{
lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; 
v___x_1202_ = lean_array_fswap(v_as_1189_, v_i_1190_, v_k_1191_);
v___x_1203_ = lean_unsigned_to_nat(1u);
v___x_1204_ = lean_nat_add(v_i_1190_, v___x_1203_);
lean_dec(v_i_1190_);
v___x_1205_ = lean_nat_add(v_k_1191_, v___x_1203_);
lean_dec(v_k_1191_);
v_as_1189_ = v___x_1202_;
v_i_1190_ = v___x_1204_;
v_k_1191_ = v___x_1205_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9_spec__13___redArg___boxed(lean_object* v_hi_1207_, lean_object* v_pivot_1208_, lean_object* v_as_1209_, lean_object* v_i_1210_, lean_object* v_k_1211_){
_start:
{
lean_object* v_res_1212_; 
v_res_1212_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9_spec__13___redArg(v_hi_1207_, v_pivot_1208_, v_as_1209_, v_i_1210_, v_k_1211_);
lean_dec_ref(v_pivot_1208_);
lean_dec(v_hi_1207_);
return v_res_1212_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg(lean_object* v_n_1213_, lean_object* v_as_1214_, lean_object* v_lo_1215_, lean_object* v_hi_1216_){
_start:
{
lean_object* v___y_1218_; uint8_t v___x_1228_; 
v___x_1228_ = lean_nat_dec_lt(v_lo_1215_, v_hi_1216_);
if (v___x_1228_ == 0)
{
lean_dec(v_lo_1215_);
return v_as_1214_;
}
else
{
lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v_mid_1231_; lean_object* v___y_1233_; lean_object* v___y_1239_; lean_object* v___x_1244_; lean_object* v___x_1245_; uint8_t v___x_1246_; 
v___x_1229_ = lean_nat_add(v_lo_1215_, v_hi_1216_);
v___x_1230_ = lean_unsigned_to_nat(1u);
v_mid_1231_ = lean_nat_shiftr(v___x_1229_, v___x_1230_);
lean_dec(v___x_1229_);
v___x_1244_ = lean_array_fget_borrowed(v_as_1214_, v_mid_1231_);
v___x_1245_ = lean_array_fget_borrowed(v_as_1214_, v_lo_1215_);
v___x_1246_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg___lam__0(v___x_1244_, v___x_1245_);
if (v___x_1246_ == 0)
{
v___y_1239_ = v_as_1214_;
goto v___jp_1238_;
}
else
{
lean_object* v___x_1247_; 
v___x_1247_ = lean_array_fswap(v_as_1214_, v_lo_1215_, v_mid_1231_);
v___y_1239_ = v___x_1247_;
goto v___jp_1238_;
}
v___jp_1232_:
{
lean_object* v___x_1234_; lean_object* v___x_1235_; uint8_t v___x_1236_; 
v___x_1234_ = lean_array_fget_borrowed(v___y_1233_, v_mid_1231_);
v___x_1235_ = lean_array_fget_borrowed(v___y_1233_, v_hi_1216_);
v___x_1236_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg___lam__0(v___x_1234_, v___x_1235_);
if (v___x_1236_ == 0)
{
lean_dec(v_mid_1231_);
v___y_1218_ = v___y_1233_;
goto v___jp_1217_;
}
else
{
lean_object* v___x_1237_; 
v___x_1237_ = lean_array_fswap(v___y_1233_, v_mid_1231_, v_hi_1216_);
lean_dec(v_mid_1231_);
v___y_1218_ = v___x_1237_;
goto v___jp_1217_;
}
}
v___jp_1238_:
{
lean_object* v___x_1240_; lean_object* v___x_1241_; uint8_t v___x_1242_; 
v___x_1240_ = lean_array_fget_borrowed(v___y_1239_, v_hi_1216_);
v___x_1241_ = lean_array_fget_borrowed(v___y_1239_, v_lo_1215_);
v___x_1242_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg___lam__0(v___x_1240_, v___x_1241_);
if (v___x_1242_ == 0)
{
v___y_1233_ = v___y_1239_;
goto v___jp_1232_;
}
else
{
lean_object* v___x_1243_; 
v___x_1243_ = lean_array_fswap(v___y_1239_, v_lo_1215_, v_hi_1216_);
v___y_1233_ = v___x_1243_;
goto v___jp_1232_;
}
}
}
v___jp_1217_:
{
lean_object* v_pivot_1219_; lean_object* v___x_1220_; lean_object* v_fst_1221_; lean_object* v_snd_1222_; uint8_t v___x_1223_; 
v_pivot_1219_ = lean_array_fget(v___y_1218_, v_hi_1216_);
lean_inc_n(v_lo_1215_, 2);
v___x_1220_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9_spec__13___redArg(v_hi_1216_, v_pivot_1219_, v___y_1218_, v_lo_1215_, v_lo_1215_);
lean_dec(v_pivot_1219_);
v_fst_1221_ = lean_ctor_get(v___x_1220_, 0);
lean_inc(v_fst_1221_);
v_snd_1222_ = lean_ctor_get(v___x_1220_, 1);
lean_inc(v_snd_1222_);
lean_dec_ref(v___x_1220_);
v___x_1223_ = lean_nat_dec_le(v_hi_1216_, v_fst_1221_);
if (v___x_1223_ == 0)
{
lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; 
v___x_1224_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg(v_n_1213_, v_snd_1222_, v_lo_1215_, v_fst_1221_);
v___x_1225_ = lean_unsigned_to_nat(1u);
v___x_1226_ = lean_nat_add(v_fst_1221_, v___x_1225_);
lean_dec(v_fst_1221_);
v_as_1214_ = v___x_1224_;
v_lo_1215_ = v___x_1226_;
goto _start;
}
else
{
lean_dec(v_fst_1221_);
lean_dec(v_lo_1215_);
return v_snd_1222_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg___boxed(lean_object* v_n_1248_, lean_object* v_as_1249_, lean_object* v_lo_1250_, lean_object* v_hi_1251_){
_start:
{
lean_object* v_res_1252_; 
v_res_1252_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg(v_n_1248_, v_as_1249_, v_lo_1250_, v_hi_1251_);
lean_dec(v_hi_1251_);
lean_dec(v_n_1248_);
return v_res_1252_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11_spec__13___redArg(lean_object* v_as_1253_, lean_object* v_a_1254_, lean_object* v_x_1255_){
_start:
{
lean_object* v_zero_1256_; uint8_t v_isZero_1257_; 
v_zero_1256_ = lean_unsigned_to_nat(0u);
v_isZero_1257_ = lean_nat_dec_eq(v_x_1255_, v_zero_1256_);
if (v_isZero_1257_ == 1)
{
lean_dec(v_x_1255_);
return v_isZero_1257_;
}
else
{
lean_object* v_fst_1258_; lean_object* v_one_1259_; lean_object* v_n_1260_; lean_object* v___x_1261_; lean_object* v_fst_1262_; uint8_t v___x_1263_; 
v_fst_1258_ = lean_ctor_get(v_a_1254_, 0);
v_one_1259_ = lean_unsigned_to_nat(1u);
v_n_1260_ = lean_nat_sub(v_x_1255_, v_one_1259_);
lean_dec(v_x_1255_);
v___x_1261_ = lean_array_fget_borrowed(v_as_1253_, v_n_1260_);
v_fst_1262_ = lean_ctor_get(v___x_1261_, 0);
v___x_1263_ = lean_nat_dec_eq(v_fst_1258_, v_fst_1262_);
if (v___x_1263_ == 0)
{
v_x_1255_ = v_n_1260_;
goto _start;
}
else
{
lean_dec(v_n_1260_);
return v_isZero_1257_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11_spec__13___redArg___boxed(lean_object* v_as_1265_, lean_object* v_a_1266_, lean_object* v_x_1267_){
_start:
{
uint8_t v_res_1268_; lean_object* v_r_1269_; 
v_res_1268_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11_spec__13___redArg(v_as_1265_, v_a_1266_, v_x_1267_);
lean_dec_ref(v_a_1266_);
lean_dec_ref(v_as_1265_);
v_r_1269_ = lean_box(v_res_1268_);
return v_r_1269_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11(lean_object* v_as_1270_, lean_object* v_i_1271_){
_start:
{
lean_object* v___x_1272_; uint8_t v___x_1273_; 
v___x_1272_ = lean_array_get_size(v_as_1270_);
v___x_1273_ = lean_nat_dec_lt(v_i_1271_, v___x_1272_);
if (v___x_1273_ == 0)
{
uint8_t v___x_1274_; 
lean_dec(v_i_1271_);
v___x_1274_ = 1;
return v___x_1274_;
}
else
{
lean_object* v___x_1275_; uint8_t v___x_1276_; 
v___x_1275_ = lean_array_fget_borrowed(v_as_1270_, v_i_1271_);
lean_inc(v_i_1271_);
v___x_1276_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11_spec__13___redArg(v_as_1270_, v___x_1275_, v_i_1271_);
if (v___x_1276_ == 0)
{
lean_dec(v_i_1271_);
return v___x_1276_;
}
else
{
lean_object* v___x_1277_; lean_object* v___x_1278_; 
v___x_1277_ = lean_unsigned_to_nat(1u);
v___x_1278_ = lean_nat_add(v_i_1271_, v___x_1277_);
lean_dec(v_i_1271_);
v_i_1271_ = v___x_1278_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11___boxed(lean_object* v_as_1280_, lean_object* v_i_1281_){
_start:
{
uint8_t v_res_1282_; lean_object* v_r_1283_; 
v_res_1282_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11(v_as_1280_, v_i_1281_);
lean_dec_ref(v_as_1280_);
v_r_1283_ = lean_box(v_res_1282_);
return v_r_1283_;
}
}
LEAN_EXPORT uint8_t l_Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8(lean_object* v_as_1284_){
_start:
{
lean_object* v___x_1285_; uint8_t v___x_1286_; 
v___x_1285_ = lean_unsigned_to_nat(0u);
v___x_1286_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11(v_as_1284_, v___x_1285_);
return v___x_1286_;
}
}
LEAN_EXPORT lean_object* l_Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8___boxed(lean_object* v_as_1287_){
_start:
{
uint8_t v_res_1288_; lean_object* v_r_1289_; 
v_res_1288_ = l_Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8(v_as_1287_);
lean_dec_ref(v_as_1287_);
v_r_1289_ = lean_box(v_res_1288_);
return v_r_1289_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__0(void){
_start:
{
lean_object* v___x_1290_; 
v___x_1290_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1290_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__1(void){
_start:
{
lean_object* v___x_1291_; lean_object* v___x_1292_; 
v___x_1291_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__0, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__0_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__0);
v___x_1292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1292_, 0, v___x_1291_);
return v___x_1292_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__2(void){
_start:
{
lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; 
v___x_1293_ = lean_unsigned_to_nat(0u);
v___x_1294_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__1, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__1_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__1);
v___x_1295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1295_, 0, v___x_1294_);
lean_ctor_set(v___x_1295_, 1, v___x_1293_);
return v___x_1295_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__3(void){
_start:
{
lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; 
v___x_1296_ = lean_unsigned_to_nat(32u);
v___x_1297_ = lean_mk_empty_array_with_capacity(v___x_1296_);
v___x_1298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1298_, 0, v___x_1297_);
return v___x_1298_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__4(void){
_start:
{
size_t v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; 
v___x_1299_ = ((size_t)5ULL);
v___x_1300_ = lean_unsigned_to_nat(0u);
v___x_1301_ = lean_unsigned_to_nat(32u);
v___x_1302_ = lean_mk_empty_array_with_capacity(v___x_1301_);
v___x_1303_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__3, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__3_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__3);
v___x_1304_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1304_, 0, v___x_1303_);
lean_ctor_set(v___x_1304_, 1, v___x_1302_);
lean_ctor_set(v___x_1304_, 2, v___x_1300_);
lean_ctor_set(v___x_1304_, 3, v___x_1300_);
lean_ctor_set_usize(v___x_1304_, 4, v___x_1299_);
return v___x_1304_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__5(void){
_start:
{
lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; 
v___x_1305_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__4, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__4_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__4);
v___x_1306_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__1, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__1_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__1);
v___x_1307_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1307_, 0, v___x_1306_);
lean_ctor_set(v___x_1307_, 1, v___x_1306_);
lean_ctor_set(v___x_1307_, 2, v___x_1306_);
lean_ctor_set(v___x_1307_, 3, v___x_1305_);
return v___x_1307_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__6(void){
_start:
{
lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; 
v___x_1308_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__5, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__5_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__5);
v___x_1309_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__2, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__2_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__2);
v___x_1310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1310_, 0, v___x_1309_);
lean_ctor_set(v___x_1310_, 1, v___x_1308_);
return v___x_1310_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__8(void){
_start:
{
lean_object* v___x_1312_; lean_object* v___x_1313_; 
v___x_1312_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__7));
v___x_1313_ = l_Lean_stringToMessageData(v___x_1312_);
return v___x_1313_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__10(void){
_start:
{
lean_object* v___x_1315_; lean_object* v___x_1316_; 
v___x_1315_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__9));
v___x_1316_ = l_Lean_stringToMessageData(v___x_1315_);
return v___x_1316_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__12(void){
_start:
{
lean_object* v___x_1318_; lean_object* v___x_1319_; 
v___x_1318_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__11));
v___x_1319_ = l_Lean_stringToMessageData(v___x_1318_);
return v___x_1319_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__14(void){
_start:
{
lean_object* v___x_1321_; lean_object* v___x_1322_; 
v___x_1321_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__13));
v___x_1322_ = l_Lean_stringToMessageData(v___x_1321_);
return v___x_1322_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__17(void){
_start:
{
lean_object* v___x_1326_; lean_object* v___x_1327_; 
v___x_1326_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__16));
v___x_1327_ = l_Lean_stringToMessageData(v___x_1326_);
return v___x_1327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__6(uint8_t v___x_1348_, lean_object* v___f_1349_, uint8_t v___x_1350_, lean_object* v_stx_1351_, lean_object* v___x_1352_, lean_object* v___x_1353_, lean_object* v___x_1354_, lean_object* v___x_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_){
_start:
{
lean_object* v___y_1366_; lean_object* v_subgoals_1367_; lean_object* v___y_1368_; lean_object* v___y_1369_; lean_object* v___y_1370_; lean_object* v___y_1371_; lean_object* v___y_1372_; lean_object* v___y_1373_; lean_object* v___y_1374_; lean_object* v___y_1375_; lean_object* v___y_1413_; lean_object* v___y_1414_; lean_object* v___y_1415_; lean_object* v___y_1416_; lean_object* v___y_1417_; lean_object* v___y_1418_; lean_object* v___y_1419_; lean_object* v___y_1420_; lean_object* v___y_1421_; lean_object* v___y_1422_; lean_object* v___y_1427_; lean_object* v___y_1428_; lean_object* v___y_1429_; lean_object* v___y_1430_; lean_object* v___y_1431_; lean_object* v___y_1432_; lean_object* v___y_1433_; lean_object* v___y_1434_; lean_object* v___y_1435_; lean_object* v___y_1436_; lean_object* v___y_1437_; lean_object* v___y_1438_; lean_object* v___y_1439_; lean_object* v___y_1442_; lean_object* v___y_1443_; lean_object* v___y_1444_; lean_object* v___y_1445_; lean_object* v___y_1446_; lean_object* v___y_1447_; lean_object* v___y_1448_; lean_object* v___y_1449_; lean_object* v___y_1450_; lean_object* v___y_1451_; lean_object* v___y_1452_; lean_object* v___y_1453_; lean_object* v___y_1454_; 
if (v___x_1348_ == 0)
{
lean_object* v___x_1456_; 
lean_dec_ref(v___x_1355_);
lean_dec_ref(v___x_1354_);
lean_dec_ref(v___x_1353_);
lean_dec_ref(v___x_1352_);
lean_dec_ref(v___f_1349_);
v___x_1456_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg();
return v___x_1456_;
}
else
{
lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___y_1460_; lean_object* v___y_1461_; lean_object* v___y_1462_; lean_object* v___y_1463_; lean_object* v___y_1464_; lean_object* v___y_1465_; lean_object* v___y_1466_; lean_object* v___y_1467_; lean_object* v___y_1468_; lean_object* v___y_1469_; lean_object* v___y_1475_; lean_object* v___y_1476_; lean_object* v___y_1477_; lean_object* v___y_1478_; lean_object* v___y_1479_; lean_object* v___y_1480_; lean_object* v___y_1481_; lean_object* v___y_1482_; lean_object* v___y_1483_; lean_object* v___y_1484_; lean_object* v___y_1485_; lean_object* v___y_1486_; lean_object* v___y_1487_; lean_object* v___y_1488_; lean_object* v___y_1489_; uint8_t v___y_1490_; lean_object* v___y_1583_; lean_object* v___y_1584_; lean_object* v___y_1585_; lean_object* v___y_1586_; lean_object* v___y_1587_; lean_object* v_occs_1588_; lean_object* v___y_1589_; lean_object* v___y_1590_; lean_object* v___y_1591_; lean_object* v___y_1592_; lean_object* v___y_1593_; lean_object* v___y_1594_; lean_object* v___y_1595_; lean_object* v___y_1596_; lean_object* v___y_1611_; lean_object* v___y_1612_; lean_object* v___y_1613_; lean_object* v___y_1614_; lean_object* v___y_1615_; lean_object* v___y_1616_; lean_object* v___y_1617_; lean_object* v___y_1618_; lean_object* v___y_1619_; lean_object* v___y_1620_; lean_object* v___y_1621_; lean_object* v___y_1622_; lean_object* v___y_1623_; lean_object* v___y_1624_; lean_object* v___y_1629_; lean_object* v___y_1630_; lean_object* v___y_1631_; lean_object* v___y_1632_; lean_object* v___y_1633_; lean_object* v___y_1634_; lean_object* v___y_1635_; lean_object* v___y_1636_; lean_object* v___y_1637_; lean_object* v___y_1638_; lean_object* v___y_1639_; lean_object* v___y_1640_; lean_object* v___y_1641_; lean_object* v___y_1642_; lean_object* v___y_1647_; lean_object* v___y_1648_; lean_object* v___y_1649_; lean_object* v___y_1650_; lean_object* v___y_1651_; lean_object* v___y_1652_; lean_object* v___y_1653_; lean_object* v___y_1654_; lean_object* v___y_1655_; lean_object* v___y_1656_; lean_object* v___y_1657_; lean_object* v___y_1658_; lean_object* v___y_1659_; lean_object* v___y_1660_; lean_object* v___y_1661_; lean_object* v___y_1662_; lean_object* v___y_1663_; lean_object* v___y_1666_; lean_object* v___y_1667_; lean_object* v___y_1668_; lean_object* v___y_1669_; lean_object* v___y_1670_; lean_object* v___y_1671_; lean_object* v___y_1672_; lean_object* v___y_1673_; lean_object* v___y_1674_; lean_object* v___y_1675_; lean_object* v___y_1676_; lean_object* v___y_1677_; lean_object* v___y_1678_; lean_object* v___y_1679_; lean_object* v___y_1680_; lean_object* v___y_1681_; lean_object* v___y_1682_; lean_object* v_occs_1685_; lean_object* v___y_1686_; lean_object* v___y_1687_; lean_object* v___y_1688_; lean_object* v___y_1689_; lean_object* v___y_1690_; lean_object* v___y_1691_; lean_object* v___y_1692_; lean_object* v___y_1693_; lean_object* v___x_1779_; uint8_t v___x_1780_; 
v___x_1457_ = lean_unsigned_to_nat(0u);
v___x_1458_ = lean_unsigned_to_nat(1u);
v___x_1779_ = l_Lean_Syntax_getArg(v_stx_1351_, v___x_1458_);
v___x_1780_ = l_Lean_Syntax_isNone(v___x_1779_);
if (v___x_1780_ == 0)
{
uint8_t v___x_1781_; 
lean_inc(v___x_1779_);
v___x_1781_ = l_Lean_Syntax_matchesNull(v___x_1779_, v___x_1458_);
if (v___x_1781_ == 0)
{
lean_object* v___x_1782_; 
lean_dec(v___x_1779_);
lean_dec_ref(v___x_1355_);
lean_dec_ref(v___x_1354_);
lean_dec_ref(v___x_1353_);
lean_dec_ref(v___x_1352_);
lean_dec_ref(v___f_1349_);
v___x_1782_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg();
return v___x_1782_;
}
else
{
lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; uint8_t v___x_1786_; 
v___x_1783_ = l_Lean_Syntax_getArg(v___x_1779_, v___x_1457_);
lean_dec(v___x_1779_);
v___x_1784_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__27));
lean_inc_ref(v___x_1355_);
lean_inc_ref(v___x_1354_);
lean_inc_ref(v___x_1353_);
lean_inc_ref(v___x_1352_);
v___x_1785_ = l_Lean_Name_mkStr5(v___x_1352_, v___x_1353_, v___x_1354_, v___x_1355_, v___x_1784_);
lean_inc(v___x_1783_);
v___x_1786_ = l_Lean_Syntax_isOfKind(v___x_1783_, v___x_1785_);
lean_dec(v___x_1785_);
if (v___x_1786_ == 0)
{
lean_object* v___x_1787_; 
lean_dec(v___x_1783_);
lean_dec_ref(v___x_1355_);
lean_dec_ref(v___x_1354_);
lean_dec_ref(v___x_1353_);
lean_dec_ref(v___x_1352_);
lean_dec_ref(v___f_1349_);
v___x_1787_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg();
return v___x_1787_;
}
else
{
lean_object* v___x_1788_; lean_object* v_occs_1789_; lean_object* v___x_1790_; 
v___x_1788_ = lean_unsigned_to_nat(3u);
v_occs_1789_ = l_Lean_Syntax_getArg(v___x_1783_, v___x_1788_);
lean_dec(v___x_1783_);
v___x_1790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1790_, 0, v_occs_1789_);
v_occs_1685_ = v___x_1790_;
v___y_1686_ = v___y_1356_;
v___y_1687_ = v___y_1357_;
v___y_1688_ = v___y_1358_;
v___y_1689_ = v___y_1359_;
v___y_1690_ = v___y_1360_;
v___y_1691_ = v___y_1361_;
v___y_1692_ = v___y_1362_;
v___y_1693_ = v___y_1363_;
goto v___jp_1684_;
}
}
}
else
{
lean_object* v___x_1791_; 
lean_dec(v___x_1779_);
v___x_1791_ = lean_box(0);
v_occs_1685_ = v___x_1791_;
v___y_1686_ = v___y_1356_;
v___y_1687_ = v___y_1357_;
v___y_1688_ = v___y_1358_;
v___y_1689_ = v___y_1359_;
v___y_1690_ = v___y_1360_;
v___y_1691_ = v___y_1361_;
v___y_1692_ = v___y_1362_;
v___y_1693_ = v___y_1363_;
goto v___jp_1684_;
}
v___jp_1459_:
{
lean_object* v___x_1470_; uint8_t v___x_1471_; 
v___x_1470_ = lean_array_get_size(v___y_1460_);
v___x_1471_ = lean_nat_dec_eq(v___x_1470_, v___x_1457_);
if (v___x_1471_ == 0)
{
lean_object* v___x_1472_; uint8_t v___x_1473_; 
v___x_1472_ = lean_nat_sub(v___x_1470_, v___x_1458_);
v___x_1473_ = lean_nat_dec_le(v___x_1457_, v___x_1472_);
if (v___x_1473_ == 0)
{
lean_inc(v___x_1472_);
v___y_1442_ = v___y_1460_;
v___y_1443_ = v___x_1470_;
v___y_1444_ = v___y_1461_;
v___y_1445_ = v___y_1469_;
v___y_1446_ = v___y_1468_;
v___y_1447_ = v___y_1462_;
v___y_1448_ = v___y_1466_;
v___y_1449_ = v___y_1464_;
v___y_1450_ = v___y_1467_;
v___y_1451_ = v___y_1465_;
v___y_1452_ = v___y_1463_;
v___y_1453_ = v___x_1472_;
v___y_1454_ = v___x_1472_;
goto v___jp_1441_;
}
else
{
v___y_1442_ = v___y_1460_;
v___y_1443_ = v___x_1470_;
v___y_1444_ = v___y_1461_;
v___y_1445_ = v___y_1469_;
v___y_1446_ = v___y_1468_;
v___y_1447_ = v___y_1462_;
v___y_1448_ = v___y_1466_;
v___y_1449_ = v___y_1464_;
v___y_1450_ = v___y_1467_;
v___y_1451_ = v___y_1465_;
v___y_1452_ = v___y_1463_;
v___y_1453_ = v___x_1472_;
v___y_1454_ = v___x_1457_;
goto v___jp_1441_;
}
}
else
{
v___y_1413_ = v___y_1462_;
v___y_1414_ = v___y_1461_;
v___y_1415_ = v___y_1466_;
v___y_1416_ = v___y_1464_;
v___y_1417_ = v___y_1467_;
v___y_1418_ = v___y_1465_;
v___y_1419_ = v___y_1469_;
v___y_1420_ = v___y_1463_;
v___y_1421_ = v___y_1468_;
v___y_1422_ = v___y_1460_;
goto v___jp_1412_;
}
}
v___jp_1474_:
{
lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; 
v___x_1491_ = l_Lean_Meta_Simp_Context_setMemoize(v___y_1477_, v___y_1490_);
v___x_1492_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__6, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__6_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__6);
lean_inc(v___y_1478_);
lean_inc_ref(v___y_1484_);
v___x_1493_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre___boxed), 11, 2);
lean_closure_set(v___x_1493_, 0, v___y_1484_);
lean_closure_set(v___x_1493_, 1, v___y_1478_);
lean_inc_ref(v___y_1489_);
lean_inc_ref(v___y_1487_);
v___x_1494_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_1494_, 0, v___x_1493_);
lean_ctor_set(v___x_1494_, 1, v___y_1486_);
lean_ctor_set(v___x_1494_, 2, v___y_1487_);
lean_ctor_set(v___x_1494_, 3, v___f_1349_);
lean_ctor_set(v___x_1494_, 4, v___y_1489_);
lean_ctor_set_uint8(v___x_1494_, sizeof(void*)*5, v___x_1350_);
v___x_1495_ = l_Lean_Meta_Simp_main(v___y_1480_, v___x_1491_, v___x_1492_, v___x_1494_, v___y_1488_, v___y_1483_, v___y_1479_, v___y_1481_);
if (lean_obj_tag(v___x_1495_) == 0)
{
lean_object* v_a_1496_; lean_object* v_fst_1497_; lean_object* v___x_1499_; uint8_t v_isShared_1500_; uint8_t v_isSharedCheck_1572_; 
v_a_1496_ = lean_ctor_get(v___x_1495_, 0);
lean_inc(v_a_1496_);
lean_dec_ref_known(v___x_1495_, 1);
v_fst_1497_ = lean_ctor_get(v_a_1496_, 0);
v_isSharedCheck_1572_ = !lean_is_exclusive(v_a_1496_);
if (v_isSharedCheck_1572_ == 0)
{
lean_object* v_unused_1573_; 
v_unused_1573_ = lean_ctor_get(v_a_1496_, 1);
lean_dec(v_unused_1573_);
v___x_1499_ = v_a_1496_;
v_isShared_1500_ = v_isSharedCheck_1572_;
goto v_resetjp_1498_;
}
else
{
lean_inc(v_fst_1497_);
lean_dec(v_a_1496_);
v___x_1499_ = lean_box(0);
v_isShared_1500_ = v_isSharedCheck_1572_;
goto v_resetjp_1498_;
}
v_resetjp_1498_:
{
lean_object* v___x_1501_; 
v___x_1501_ = lean_st_ref_get(v___y_1478_);
lean_dec(v___y_1478_);
if (lean_obj_tag(v___x_1501_) == 0)
{
lean_object* v_subgoals_1502_; lean_object* v___x_1503_; uint8_t v___x_1504_; 
v_subgoals_1502_ = lean_ctor_get(v___x_1501_, 0);
lean_inc_ref(v_subgoals_1502_);
lean_dec_ref_known(v___x_1501_, 1);
v___x_1503_ = lean_array_get_size(v_subgoals_1502_);
v___x_1504_ = lean_nat_dec_eq(v___x_1503_, v___x_1457_);
if (v___x_1504_ == 0)
{
lean_del_object(v___x_1499_);
lean_dec_ref(v___y_1484_);
v___y_1366_ = v_fst_1497_;
v_subgoals_1367_ = v_subgoals_1502_;
v___y_1368_ = v___y_1482_;
v___y_1369_ = v___y_1476_;
v___y_1370_ = v___y_1485_;
v___y_1371_ = v___y_1475_;
v___y_1372_ = v___y_1488_;
v___y_1373_ = v___y_1483_;
v___y_1374_ = v___y_1479_;
v___y_1375_ = v___y_1481_;
goto v___jp_1365_;
}
else
{
lean_object* v_expr_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1509_; 
lean_dec_ref(v_subgoals_1502_);
lean_dec(v_fst_1497_);
v_expr_1505_ = lean_ctor_get(v___y_1484_, 2);
lean_inc_ref(v_expr_1505_);
lean_dec_ref(v___y_1484_);
v___x_1506_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__8, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__8_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__8);
v___x_1507_ = l_Lean_indentExpr(v_expr_1505_);
if (v_isShared_1500_ == 0)
{
lean_ctor_set_tag(v___x_1499_, 7);
lean_ctor_set(v___x_1499_, 1, v___x_1507_);
lean_ctor_set(v___x_1499_, 0, v___x_1506_);
v___x_1509_ = v___x_1499_;
goto v_reusejp_1508_;
}
else
{
lean_object* v_reuseFailAlloc_1519_; 
v_reuseFailAlloc_1519_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1519_, 0, v___x_1506_);
lean_ctor_set(v_reuseFailAlloc_1519_, 1, v___x_1507_);
v___x_1509_ = v_reuseFailAlloc_1519_;
goto v_reusejp_1508_;
}
v_reusejp_1508_:
{
lean_object* v___x_1510_; lean_object* v_a_1511_; lean_object* v___x_1513_; uint8_t v_isShared_1514_; uint8_t v_isSharedCheck_1518_; 
v___x_1510_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg(v___x_1509_, v___y_1488_, v___y_1483_, v___y_1479_, v___y_1481_);
v_a_1511_ = lean_ctor_get(v___x_1510_, 0);
v_isSharedCheck_1518_ = !lean_is_exclusive(v___x_1510_);
if (v_isSharedCheck_1518_ == 0)
{
v___x_1513_ = v___x_1510_;
v_isShared_1514_ = v_isSharedCheck_1518_;
goto v_resetjp_1512_;
}
else
{
lean_inc(v_a_1511_);
lean_dec(v___x_1510_);
v___x_1513_ = lean_box(0);
v_isShared_1514_ = v_isSharedCheck_1518_;
goto v_resetjp_1512_;
}
v_resetjp_1512_:
{
lean_object* v___x_1516_; 
if (v_isShared_1514_ == 0)
{
v___x_1516_ = v___x_1513_;
goto v_reusejp_1515_;
}
else
{
lean_object* v_reuseFailAlloc_1517_; 
v_reuseFailAlloc_1517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1517_, 0, v_a_1511_);
v___x_1516_ = v_reuseFailAlloc_1517_;
goto v_reusejp_1515_;
}
v_reusejp_1515_:
{
return v___x_1516_;
}
}
}
}
}
else
{
lean_object* v_subgoals_1520_; lean_object* v_idx_1521_; lean_object* v_remaining_1522_; uint8_t v___x_1523_; 
v_subgoals_1520_ = lean_ctor_get(v___x_1501_, 0);
lean_inc_ref(v_subgoals_1520_);
v_idx_1521_ = lean_ctor_get(v___x_1501_, 1);
lean_inc(v_idx_1521_);
v_remaining_1522_ = lean_ctor_get(v___x_1501_, 2);
lean_inc(v_remaining_1522_);
lean_dec_ref_known(v___x_1501_, 3);
v___x_1523_ = lean_nat_dec_eq(v_idx_1521_, v___x_1457_);
if (v___x_1523_ == 0)
{
lean_object* v___x_1524_; 
lean_dec_ref(v___y_1484_);
v___x_1524_ = l_List_getLast_x3f___redArg(v_remaining_1522_);
lean_dec(v_remaining_1522_);
if (lean_obj_tag(v___x_1524_) == 1)
{
lean_object* v_val_1525_; lean_object* v___x_1527_; uint8_t v_isShared_1528_; uint8_t v_isSharedCheck_1556_; 
lean_dec_ref(v_subgoals_1520_);
lean_dec(v_fst_1497_);
v_val_1525_ = lean_ctor_get(v___x_1524_, 0);
v_isSharedCheck_1556_ = !lean_is_exclusive(v___x_1524_);
if (v_isSharedCheck_1556_ == 0)
{
v___x_1527_ = v___x_1524_;
v_isShared_1528_ = v_isSharedCheck_1556_;
goto v_resetjp_1526_;
}
else
{
lean_inc(v_val_1525_);
lean_dec(v___x_1524_);
v___x_1527_ = lean_box(0);
v_isShared_1528_ = v_isSharedCheck_1556_;
goto v_resetjp_1526_;
}
v_resetjp_1526_:
{
lean_object* v_fst_1529_; lean_object* v___x_1531_; uint8_t v_isShared_1532_; uint8_t v_isSharedCheck_1554_; 
v_fst_1529_ = lean_ctor_get(v_val_1525_, 0);
v_isSharedCheck_1554_ = !lean_is_exclusive(v_val_1525_);
if (v_isSharedCheck_1554_ == 0)
{
lean_object* v_unused_1555_; 
v_unused_1555_ = lean_ctor_get(v_val_1525_, 1);
lean_dec(v_unused_1555_);
v___x_1531_ = v_val_1525_;
v_isShared_1532_ = v_isSharedCheck_1554_;
goto v_resetjp_1530_;
}
else
{
lean_inc(v_fst_1529_);
lean_dec(v_val_1525_);
v___x_1531_ = lean_box(0);
v_isShared_1532_ = v_isSharedCheck_1554_;
goto v_resetjp_1530_;
}
v_resetjp_1530_:
{
lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1536_; 
v___x_1533_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__10, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__10_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__10);
v___x_1534_ = l_Nat_reprFast(v_idx_1521_);
if (v_isShared_1528_ == 0)
{
lean_ctor_set_tag(v___x_1527_, 3);
lean_ctor_set(v___x_1527_, 0, v___x_1534_);
v___x_1536_ = v___x_1527_;
goto v_reusejp_1535_;
}
else
{
lean_object* v_reuseFailAlloc_1553_; 
v_reuseFailAlloc_1553_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1553_, 0, v___x_1534_);
v___x_1536_ = v_reuseFailAlloc_1553_;
goto v_reusejp_1535_;
}
v_reusejp_1535_:
{
lean_object* v___x_1537_; lean_object* v___x_1539_; 
v___x_1537_ = l_Lean_MessageData_ofFormat(v___x_1536_);
if (v_isShared_1532_ == 0)
{
lean_ctor_set_tag(v___x_1531_, 7);
lean_ctor_set(v___x_1531_, 1, v___x_1537_);
lean_ctor_set(v___x_1531_, 0, v___x_1533_);
v___x_1539_ = v___x_1531_;
goto v_reusejp_1538_;
}
else
{
lean_object* v_reuseFailAlloc_1552_; 
v_reuseFailAlloc_1552_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1552_, 0, v___x_1533_);
lean_ctor_set(v_reuseFailAlloc_1552_, 1, v___x_1537_);
v___x_1539_ = v_reuseFailAlloc_1552_;
goto v_reusejp_1538_;
}
v_reusejp_1538_:
{
lean_object* v___x_1540_; lean_object* v___x_1542_; 
v___x_1540_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__12, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__12_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__12);
if (v_isShared_1500_ == 0)
{
lean_ctor_set_tag(v___x_1499_, 7);
lean_ctor_set(v___x_1499_, 1, v___x_1540_);
lean_ctor_set(v___x_1499_, 0, v___x_1539_);
v___x_1542_ = v___x_1499_;
goto v_reusejp_1541_;
}
else
{
lean_object* v_reuseFailAlloc_1551_; 
v_reuseFailAlloc_1551_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1551_, 0, v___x_1539_);
lean_ctor_set(v_reuseFailAlloc_1551_, 1, v___x_1540_);
v___x_1542_ = v_reuseFailAlloc_1551_;
goto v_reusejp_1541_;
}
v_reusejp_1541_:
{
lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; 
v___x_1543_ = lean_nat_add(v_fst_1529_, v___x_1458_);
lean_dec(v_fst_1529_);
v___x_1544_ = l_Nat_reprFast(v___x_1543_);
v___x_1545_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1545_, 0, v___x_1544_);
v___x_1546_ = l_Lean_MessageData_ofFormat(v___x_1545_);
v___x_1547_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1547_, 0, v___x_1542_);
lean_ctor_set(v___x_1547_, 1, v___x_1546_);
v___x_1548_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__14, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__14_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__14);
v___x_1549_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1549_, 0, v___x_1547_);
lean_ctor_set(v___x_1549_, 1, v___x_1548_);
v___x_1550_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg(v___x_1549_, v___y_1488_, v___y_1483_, v___y_1479_, v___y_1481_);
return v___x_1550_;
}
}
}
}
}
}
else
{
lean_dec(v___x_1524_);
lean_dec(v_idx_1521_);
lean_del_object(v___x_1499_);
v___y_1460_ = v_subgoals_1520_;
v___y_1461_ = v_fst_1497_;
v___y_1462_ = v___y_1482_;
v___y_1463_ = v___y_1476_;
v___y_1464_ = v___y_1485_;
v___y_1465_ = v___y_1475_;
v___y_1466_ = v___y_1488_;
v___y_1467_ = v___y_1483_;
v___y_1468_ = v___y_1479_;
v___y_1469_ = v___y_1481_;
goto v___jp_1459_;
}
}
else
{
lean_object* v_expr_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1561_; 
lean_dec(v_remaining_1522_);
lean_dec(v_idx_1521_);
lean_dec_ref(v_subgoals_1520_);
lean_dec(v_fst_1497_);
v_expr_1557_ = lean_ctor_get(v___y_1484_, 2);
lean_inc_ref(v_expr_1557_);
lean_dec_ref(v___y_1484_);
v___x_1558_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__8, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__8_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__8);
v___x_1559_ = l_Lean_indentExpr(v_expr_1557_);
if (v_isShared_1500_ == 0)
{
lean_ctor_set_tag(v___x_1499_, 7);
lean_ctor_set(v___x_1499_, 1, v___x_1559_);
lean_ctor_set(v___x_1499_, 0, v___x_1558_);
v___x_1561_ = v___x_1499_;
goto v_reusejp_1560_;
}
else
{
lean_object* v_reuseFailAlloc_1571_; 
v_reuseFailAlloc_1571_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1571_, 0, v___x_1558_);
lean_ctor_set(v_reuseFailAlloc_1571_, 1, v___x_1559_);
v___x_1561_ = v_reuseFailAlloc_1571_;
goto v_reusejp_1560_;
}
v_reusejp_1560_:
{
lean_object* v___x_1562_; lean_object* v_a_1563_; lean_object* v___x_1565_; uint8_t v_isShared_1566_; uint8_t v_isSharedCheck_1570_; 
v___x_1562_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg(v___x_1561_, v___y_1488_, v___y_1483_, v___y_1479_, v___y_1481_);
v_a_1563_ = lean_ctor_get(v___x_1562_, 0);
v_isSharedCheck_1570_ = !lean_is_exclusive(v___x_1562_);
if (v_isSharedCheck_1570_ == 0)
{
v___x_1565_ = v___x_1562_;
v_isShared_1566_ = v_isSharedCheck_1570_;
goto v_resetjp_1564_;
}
else
{
lean_inc(v_a_1563_);
lean_dec(v___x_1562_);
v___x_1565_ = lean_box(0);
v_isShared_1566_ = v_isSharedCheck_1570_;
goto v_resetjp_1564_;
}
v_resetjp_1564_:
{
lean_object* v___x_1568_; 
if (v_isShared_1566_ == 0)
{
v___x_1568_ = v___x_1565_;
goto v_reusejp_1567_;
}
else
{
lean_object* v_reuseFailAlloc_1569_; 
v_reuseFailAlloc_1569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1569_, 0, v_a_1563_);
v___x_1568_ = v_reuseFailAlloc_1569_;
goto v_reusejp_1567_;
}
v_reusejp_1567_:
{
return v___x_1568_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1574_; lean_object* v___x_1576_; uint8_t v_isShared_1577_; uint8_t v_isSharedCheck_1581_; 
lean_dec_ref(v___y_1484_);
lean_dec(v___y_1478_);
v_a_1574_ = lean_ctor_get(v___x_1495_, 0);
v_isSharedCheck_1581_ = !lean_is_exclusive(v___x_1495_);
if (v_isSharedCheck_1581_ == 0)
{
v___x_1576_ = v___x_1495_;
v_isShared_1577_ = v_isSharedCheck_1581_;
goto v_resetjp_1575_;
}
else
{
lean_inc(v_a_1574_);
lean_dec(v___x_1495_);
v___x_1576_ = lean_box(0);
v_isShared_1577_ = v_isSharedCheck_1581_;
goto v_resetjp_1575_;
}
v_resetjp_1575_:
{
lean_object* v___x_1579_; 
if (v_isShared_1577_ == 0)
{
v___x_1579_ = v___x_1576_;
goto v_reusejp_1578_;
}
else
{
lean_object* v_reuseFailAlloc_1580_; 
v_reuseFailAlloc_1580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1580_, 0, v_a_1574_);
v___x_1579_ = v_reuseFailAlloc_1580_;
goto v_reusejp_1578_;
}
v_reusejp_1578_:
{
return v___x_1579_;
}
}
}
}
v___jp_1582_:
{
lean_object* v___x_1597_; lean_object* v___x_1598_; 
lean_inc_ref(v_occs_1588_);
v___x_1597_ = lean_st_mk_ref(v_occs_1588_);
v___x_1598_ = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_getContext___redArg(v___y_1593_, v___y_1595_, v___y_1596_);
if (lean_obj_tag(v___x_1598_) == 0)
{
if (lean_obj_tag(v_occs_1588_) == 0)
{
lean_object* v_a_1599_; 
lean_dec_ref_known(v_occs_1588_, 1);
v_a_1599_ = lean_ctor_get(v___x_1598_, 0);
lean_inc(v_a_1599_);
lean_dec_ref_known(v___x_1598_, 1);
v___y_1475_ = v___y_1592_;
v___y_1476_ = v___y_1590_;
v___y_1477_ = v_a_1599_;
v___y_1478_ = v___x_1597_;
v___y_1479_ = v___y_1595_;
v___y_1480_ = v___y_1586_;
v___y_1481_ = v___y_1596_;
v___y_1482_ = v___y_1589_;
v___y_1483_ = v___y_1594_;
v___y_1484_ = v___y_1583_;
v___y_1485_ = v___y_1591_;
v___y_1486_ = v___y_1585_;
v___y_1487_ = v___y_1584_;
v___y_1488_ = v___y_1593_;
v___y_1489_ = v___y_1587_;
v___y_1490_ = v___x_1350_;
goto v___jp_1474_;
}
else
{
lean_object* v_a_1600_; uint8_t v___x_1601_; 
lean_dec_ref(v_occs_1588_);
v_a_1600_ = lean_ctor_get(v___x_1598_, 0);
lean_inc(v_a_1600_);
lean_dec_ref_known(v___x_1598_, 1);
v___x_1601_ = 0;
v___y_1475_ = v___y_1592_;
v___y_1476_ = v___y_1590_;
v___y_1477_ = v_a_1600_;
v___y_1478_ = v___x_1597_;
v___y_1479_ = v___y_1595_;
v___y_1480_ = v___y_1586_;
v___y_1481_ = v___y_1596_;
v___y_1482_ = v___y_1589_;
v___y_1483_ = v___y_1594_;
v___y_1484_ = v___y_1583_;
v___y_1485_ = v___y_1591_;
v___y_1486_ = v___y_1585_;
v___y_1487_ = v___y_1584_;
v___y_1488_ = v___y_1593_;
v___y_1489_ = v___y_1587_;
v___y_1490_ = v___x_1601_;
goto v___jp_1474_;
}
}
else
{
lean_object* v_a_1602_; lean_object* v___x_1604_; uint8_t v_isShared_1605_; uint8_t v_isSharedCheck_1609_; 
lean_dec(v___x_1597_);
lean_dec_ref(v_occs_1588_);
lean_dec_ref(v___y_1586_);
lean_dec_ref(v___y_1585_);
lean_dec_ref(v___y_1583_);
lean_dec_ref(v___f_1349_);
v_a_1602_ = lean_ctor_get(v___x_1598_, 0);
v_isSharedCheck_1609_ = !lean_is_exclusive(v___x_1598_);
if (v_isSharedCheck_1609_ == 0)
{
v___x_1604_ = v___x_1598_;
v_isShared_1605_ = v_isSharedCheck_1609_;
goto v_resetjp_1603_;
}
else
{
lean_inc(v_a_1602_);
lean_dec(v___x_1598_);
v___x_1604_ = lean_box(0);
v_isShared_1605_ = v_isSharedCheck_1609_;
goto v_resetjp_1603_;
}
v_resetjp_1603_:
{
lean_object* v___x_1607_; 
if (v_isShared_1605_ == 0)
{
v___x_1607_ = v___x_1604_;
goto v_reusejp_1606_;
}
else
{
lean_object* v_reuseFailAlloc_1608_; 
v_reuseFailAlloc_1608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1608_, 0, v_a_1602_);
v___x_1607_ = v_reuseFailAlloc_1608_;
goto v_reusejp_1606_;
}
v_reusejp_1606_:
{
return v___x_1607_;
}
}
}
}
v___jp_1610_:
{
lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; 
v___x_1625_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__15));
v___x_1626_ = lean_array_to_list(v___y_1615_);
v___x_1627_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1627_, 0, v___x_1625_);
lean_ctor_set(v___x_1627_, 1, v___x_1457_);
lean_ctor_set(v___x_1627_, 2, v___x_1626_);
v___y_1583_ = v___y_1611_;
v___y_1584_ = v___y_1613_;
v___y_1585_ = v___y_1612_;
v___y_1586_ = v___y_1614_;
v___y_1587_ = v___y_1616_;
v_occs_1588_ = v___x_1627_;
v___y_1589_ = v___y_1617_;
v___y_1590_ = v___y_1618_;
v___y_1591_ = v___y_1619_;
v___y_1592_ = v___y_1620_;
v___y_1593_ = v___y_1621_;
v___y_1594_ = v___y_1622_;
v___y_1595_ = v___y_1623_;
v___y_1596_ = v___y_1624_;
goto v___jp_1582_;
}
v___jp_1628_:
{
uint8_t v___x_1643_; 
v___x_1643_ = l_Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8(v___y_1642_);
if (v___x_1643_ == 0)
{
lean_object* v___x_1644_; lean_object* v___x_1645_; 
lean_dec_ref(v___y_1642_);
lean_dec_ref(v___y_1639_);
lean_dec_ref(v___y_1635_);
lean_dec_ref(v___y_1633_);
lean_dec_ref(v___f_1349_);
v___x_1644_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__17, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__17_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__17);
v___x_1645_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg(v___x_1644_, v___y_1638_, v___y_1630_, v___y_1637_, v___y_1636_);
return v___x_1645_;
}
else
{
v___y_1611_ = v___y_1635_;
v___y_1612_ = v___y_1639_;
v___y_1613_ = v___y_1640_;
v___y_1614_ = v___y_1633_;
v___y_1615_ = v___y_1642_;
v___y_1616_ = v___y_1641_;
v___y_1617_ = v___y_1632_;
v___y_1618_ = v___y_1634_;
v___y_1619_ = v___y_1629_;
v___y_1620_ = v___y_1631_;
v___y_1621_ = v___y_1638_;
v___y_1622_ = v___y_1630_;
v___y_1623_ = v___y_1637_;
v___y_1624_ = v___y_1636_;
goto v___jp_1610_;
}
}
v___jp_1646_:
{
lean_object* v___x_1664_; 
v___x_1664_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg(v___y_1651_, v___y_1648_, v___y_1649_, v___y_1663_);
lean_dec(v___y_1663_);
lean_dec(v___y_1651_);
v___y_1629_ = v___y_1647_;
v___y_1630_ = v___y_1650_;
v___y_1631_ = v___y_1652_;
v___y_1632_ = v___y_1653_;
v___y_1633_ = v___y_1654_;
v___y_1634_ = v___y_1655_;
v___y_1635_ = v___y_1656_;
v___y_1636_ = v___y_1657_;
v___y_1637_ = v___y_1658_;
v___y_1638_ = v___y_1659_;
v___y_1639_ = v___y_1661_;
v___y_1640_ = v___y_1660_;
v___y_1641_ = v___y_1662_;
v___y_1642_ = v___x_1664_;
goto v___jp_1628_;
}
v___jp_1665_:
{
uint8_t v___x_1683_; 
v___x_1683_ = lean_nat_dec_le(v___y_1682_, v___y_1675_);
if (v___x_1683_ == 0)
{
lean_dec(v___y_1675_);
lean_inc(v___y_1682_);
v___y_1647_ = v___y_1666_;
v___y_1648_ = v___y_1667_;
v___y_1649_ = v___y_1682_;
v___y_1650_ = v___y_1668_;
v___y_1651_ = v___y_1669_;
v___y_1652_ = v___y_1670_;
v___y_1653_ = v___y_1671_;
v___y_1654_ = v___y_1672_;
v___y_1655_ = v___y_1673_;
v___y_1656_ = v___y_1674_;
v___y_1657_ = v___y_1676_;
v___y_1658_ = v___y_1677_;
v___y_1659_ = v___y_1678_;
v___y_1660_ = v___y_1680_;
v___y_1661_ = v___y_1679_;
v___y_1662_ = v___y_1681_;
v___y_1663_ = v___y_1682_;
goto v___jp_1646_;
}
else
{
v___y_1647_ = v___y_1666_;
v___y_1648_ = v___y_1667_;
v___y_1649_ = v___y_1682_;
v___y_1650_ = v___y_1668_;
v___y_1651_ = v___y_1669_;
v___y_1652_ = v___y_1670_;
v___y_1653_ = v___y_1671_;
v___y_1654_ = v___y_1672_;
v___y_1655_ = v___y_1673_;
v___y_1656_ = v___y_1674_;
v___y_1657_ = v___y_1676_;
v___y_1658_ = v___y_1677_;
v___y_1659_ = v___y_1678_;
v___y_1660_ = v___y_1680_;
v___y_1661_ = v___y_1679_;
v___y_1662_ = v___y_1681_;
v___y_1663_ = v___y_1675_;
goto v___jp_1646_;
}
}
v___jp_1684_:
{
lean_object* v_declName_x3f_1694_; lean_object* v_macroStack_1695_; uint8_t v_mayPostpone_1696_; uint8_t v_errToSorry_1697_; lean_object* v_autoBoundImplicitContext_1698_; lean_object* v_autoBoundImplicitForbidden_1699_; lean_object* v_sectionVars_1700_; lean_object* v_sectionFVars_1701_; uint8_t v_implicitLambda_1702_; uint8_t v_heedElabAsElim_1703_; uint8_t v_isNoncomputableSection_1704_; uint8_t v_isMetaSection_1705_; uint8_t v_inPattern_1706_; lean_object* v_tacSnap_x3f_1707_; uint8_t v_saveRecAppSyntax_1708_; uint8_t v_holesAsSyntheticOpaque_1709_; uint8_t v_checkDeprecated_1710_; lean_object* v_fixedTermElabs_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___f_1716_; lean_object* v___f_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; 
v_declName_x3f_1694_ = lean_ctor_get(v___y_1688_, 0);
v_macroStack_1695_ = lean_ctor_get(v___y_1688_, 1);
v_mayPostpone_1696_ = lean_ctor_get_uint8(v___y_1688_, sizeof(void*)*8);
v_errToSorry_1697_ = lean_ctor_get_uint8(v___y_1688_, sizeof(void*)*8 + 1);
v_autoBoundImplicitContext_1698_ = lean_ctor_get(v___y_1688_, 2);
v_autoBoundImplicitForbidden_1699_ = lean_ctor_get(v___y_1688_, 3);
v_sectionVars_1700_ = lean_ctor_get(v___y_1688_, 4);
v_sectionFVars_1701_ = lean_ctor_get(v___y_1688_, 5);
v_implicitLambda_1702_ = lean_ctor_get_uint8(v___y_1688_, sizeof(void*)*8 + 2);
v_heedElabAsElim_1703_ = lean_ctor_get_uint8(v___y_1688_, sizeof(void*)*8 + 3);
v_isNoncomputableSection_1704_ = lean_ctor_get_uint8(v___y_1688_, sizeof(void*)*8 + 4);
v_isMetaSection_1705_ = lean_ctor_get_uint8(v___y_1688_, sizeof(void*)*8 + 5);
v_inPattern_1706_ = lean_ctor_get_uint8(v___y_1688_, sizeof(void*)*8 + 7);
v_tacSnap_x3f_1707_ = lean_ctor_get(v___y_1688_, 6);
v_saveRecAppSyntax_1708_ = lean_ctor_get_uint8(v___y_1688_, sizeof(void*)*8 + 8);
v_holesAsSyntheticOpaque_1709_ = lean_ctor_get_uint8(v___y_1688_, sizeof(void*)*8 + 9);
v_checkDeprecated_1710_ = lean_ctor_get_uint8(v___y_1688_, sizeof(void*)*8 + 10);
v_fixedTermElabs_1711_ = lean_ctor_get(v___y_1688_, 7);
v___x_1712_ = lean_unsigned_to_nat(2u);
v___x_1713_ = l_Lean_Syntax_getArg(v_stx_1351_, v___x_1712_);
v___x_1714_ = lean_box(0);
v___x_1715_ = lean_box(v___x_1350_);
lean_inc(v___x_1713_);
v___f_1716_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__1___boxed), 10, 3);
lean_closure_set(v___f_1716_, 0, v___x_1713_);
lean_closure_set(v___f_1716_, 1, v___x_1714_);
lean_closure_set(v___f_1716_, 2, v___x_1715_);
v___f_1717_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__2___boxed), 9, 2);
lean_closure_set(v___f_1717_, 0, v___x_1713_);
lean_closure_set(v___f_1717_, 1, v___f_1716_);
lean_inc_ref(v_fixedTermElabs_1711_);
lean_inc(v_tacSnap_x3f_1707_);
lean_inc(v_sectionFVars_1701_);
lean_inc(v_sectionVars_1700_);
lean_inc_ref(v_autoBoundImplicitForbidden_1699_);
lean_inc(v_autoBoundImplicitContext_1698_);
lean_inc(v_macroStack_1695_);
lean_inc(v_declName_x3f_1694_);
v___x_1718_ = lean_alloc_ctor(0, 8, 11);
lean_ctor_set(v___x_1718_, 0, v_declName_x3f_1694_);
lean_ctor_set(v___x_1718_, 1, v_macroStack_1695_);
lean_ctor_set(v___x_1718_, 2, v_autoBoundImplicitContext_1698_);
lean_ctor_set(v___x_1718_, 3, v_autoBoundImplicitForbidden_1699_);
lean_ctor_set(v___x_1718_, 4, v_sectionVars_1700_);
lean_ctor_set(v___x_1718_, 5, v_sectionFVars_1701_);
lean_ctor_set(v___x_1718_, 6, v_tacSnap_x3f_1707_);
lean_ctor_set(v___x_1718_, 7, v_fixedTermElabs_1711_);
lean_ctor_set_uint8(v___x_1718_, sizeof(void*)*8, v_mayPostpone_1696_);
lean_ctor_set_uint8(v___x_1718_, sizeof(void*)*8 + 1, v_errToSorry_1697_);
lean_ctor_set_uint8(v___x_1718_, sizeof(void*)*8 + 2, v_implicitLambda_1702_);
lean_ctor_set_uint8(v___x_1718_, sizeof(void*)*8 + 3, v_heedElabAsElim_1703_);
lean_ctor_set_uint8(v___x_1718_, sizeof(void*)*8 + 4, v_isNoncomputableSection_1704_);
lean_ctor_set_uint8(v___x_1718_, sizeof(void*)*8 + 5, v_isMetaSection_1705_);
lean_ctor_set_uint8(v___x_1718_, sizeof(void*)*8 + 6, v___x_1350_);
lean_ctor_set_uint8(v___x_1718_, sizeof(void*)*8 + 7, v_inPattern_1706_);
lean_ctor_set_uint8(v___x_1718_, sizeof(void*)*8 + 8, v_saveRecAppSyntax_1708_);
lean_ctor_set_uint8(v___x_1718_, sizeof(void*)*8 + 9, v_holesAsSyntheticOpaque_1709_);
lean_ctor_set_uint8(v___x_1718_, sizeof(void*)*8 + 10, v_checkDeprecated_1710_);
v___x_1719_ = l_Lean_Elab_Term_withoutModifyingElabMetaStateWithInfo___redArg(v___f_1717_, v___x_1718_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_);
lean_dec_ref_known(v___x_1718_, 8);
if (lean_obj_tag(v___x_1719_) == 0)
{
lean_object* v_a_1720_; lean_object* v___x_1721_; 
v_a_1720_ = lean_ctor_get(v___x_1719_, 0);
lean_inc(v_a_1720_);
lean_dec_ref_known(v___x_1719_, 1);
v___x_1721_ = l_Lean_Elab_Tactic_Conv_getLhs___redArg(v___y_1687_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_);
if (lean_obj_tag(v___x_1721_) == 0)
{
lean_object* v_a_1722_; lean_object* v___x_1723_; lean_object* v___f_1724_; lean_object* v___f_1725_; lean_object* v___f_1726_; 
v_a_1722_ = lean_ctor_get(v___x_1721_, 0);
lean_inc(v_a_1722_);
lean_dec_ref_known(v___x_1721_, 1);
v___x_1723_ = lean_box(v___x_1350_);
v___f_1724_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__3___boxed), 11, 2);
lean_closure_set(v___f_1724_, 0, v___x_1714_);
lean_closure_set(v___f_1724_, 1, v___x_1723_);
v___f_1725_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__18));
v___f_1726_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__19));
if (lean_obj_tag(v_occs_1685_) == 0)
{
lean_object* v___x_1727_; 
lean_dec_ref(v___x_1355_);
lean_dec_ref(v___x_1354_);
lean_dec_ref(v___x_1353_);
lean_dec_ref(v___x_1352_);
v___x_1727_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__22));
v___y_1583_ = v_a_1720_;
v___y_1584_ = v___f_1725_;
v___y_1585_ = v___f_1724_;
v___y_1586_ = v_a_1722_;
v___y_1587_ = v___f_1726_;
v_occs_1588_ = v___x_1727_;
v___y_1589_ = v___y_1686_;
v___y_1590_ = v___y_1687_;
v___y_1591_ = v___y_1688_;
v___y_1592_ = v___y_1689_;
v___y_1593_ = v___y_1690_;
v___y_1594_ = v___y_1691_;
v___y_1595_ = v___y_1692_;
v___y_1596_ = v___y_1693_;
goto v___jp_1582_;
}
else
{
lean_object* v_val_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; uint8_t v___x_1731_; 
v_val_1728_ = lean_ctor_get(v_occs_1685_, 0);
lean_inc_n(v_val_1728_, 2);
lean_dec_ref_known(v_occs_1685_, 1);
v___x_1729_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__23));
lean_inc_ref(v___x_1355_);
lean_inc_ref(v___x_1354_);
lean_inc_ref(v___x_1353_);
lean_inc_ref(v___x_1352_);
v___x_1730_ = l_Lean_Name_mkStr5(v___x_1352_, v___x_1353_, v___x_1354_, v___x_1355_, v___x_1729_);
v___x_1731_ = l_Lean_Syntax_isOfKind(v_val_1728_, v___x_1730_);
lean_dec(v___x_1730_);
if (v___x_1731_ == 0)
{
lean_object* v___x_1732_; lean_object* v___x_1733_; uint8_t v___x_1734_; 
v___x_1732_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__24));
v___x_1733_ = l_Lean_Name_mkStr5(v___x_1352_, v___x_1353_, v___x_1354_, v___x_1355_, v___x_1732_);
lean_inc(v_val_1728_);
v___x_1734_ = l_Lean_Syntax_isOfKind(v_val_1728_, v___x_1733_);
lean_dec(v___x_1733_);
if (v___x_1734_ == 0)
{
lean_object* v___x_1735_; lean_object* v_a_1736_; lean_object* v___x_1738_; uint8_t v_isShared_1739_; uint8_t v_isSharedCheck_1743_; 
lean_dec(v_val_1728_);
lean_dec_ref(v___f_1724_);
lean_dec(v_a_1722_);
lean_dec(v_a_1720_);
lean_dec_ref(v___f_1349_);
v___x_1735_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg();
v_a_1736_ = lean_ctor_get(v___x_1735_, 0);
v_isSharedCheck_1743_ = !lean_is_exclusive(v___x_1735_);
if (v_isSharedCheck_1743_ == 0)
{
v___x_1738_ = v___x_1735_;
v_isShared_1739_ = v_isSharedCheck_1743_;
goto v_resetjp_1737_;
}
else
{
lean_inc(v_a_1736_);
lean_dec(v___x_1735_);
v___x_1738_ = lean_box(0);
v_isShared_1739_ = v_isSharedCheck_1743_;
goto v_resetjp_1737_;
}
v_resetjp_1737_:
{
lean_object* v___x_1741_; 
if (v_isShared_1739_ == 0)
{
v___x_1741_ = v___x_1738_;
goto v_reusejp_1740_;
}
else
{
lean_object* v_reuseFailAlloc_1742_; 
v_reuseFailAlloc_1742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1742_, 0, v_a_1736_);
v___x_1741_ = v_reuseFailAlloc_1742_;
goto v_reusejp_1740_;
}
v_reusejp_1740_:
{
return v___x_1741_;
}
}
}
else
{
lean_object* v___x_1744_; lean_object* v___x_1745_; size_t v_sz_1746_; size_t v___x_1747_; lean_object* v___x_1748_; 
v___x_1744_ = l_Lean_Syntax_getArg(v_val_1728_, v___x_1457_);
lean_dec(v_val_1728_);
v___x_1745_ = l_Lean_Syntax_getArgs(v___x_1744_);
lean_dec(v___x_1744_);
v_sz_1746_ = lean_array_size(v___x_1745_);
v___x_1747_ = ((size_t)0ULL);
v___x_1748_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg(v_sz_1746_, v___x_1747_, v___x_1745_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_);
if (lean_obj_tag(v___x_1748_) == 0)
{
lean_object* v_a_1749_; lean_object* v___x_1750_; uint8_t v___x_1751_; 
v_a_1749_ = lean_ctor_get(v___x_1748_, 0);
lean_inc(v_a_1749_);
lean_dec_ref_known(v___x_1748_, 1);
v___x_1750_ = lean_array_get_size(v_a_1749_);
v___x_1751_ = lean_nat_dec_eq(v___x_1750_, v___x_1457_);
if (v___x_1751_ == 0)
{
lean_object* v___x_1752_; uint8_t v___x_1753_; 
v___x_1752_ = lean_nat_sub(v___x_1750_, v___x_1458_);
v___x_1753_ = lean_nat_dec_le(v___x_1457_, v___x_1752_);
if (v___x_1753_ == 0)
{
lean_inc(v___x_1752_);
v___y_1666_ = v___y_1688_;
v___y_1667_ = v_a_1749_;
v___y_1668_ = v___y_1691_;
v___y_1669_ = v___x_1750_;
v___y_1670_ = v___y_1689_;
v___y_1671_ = v___y_1686_;
v___y_1672_ = v_a_1722_;
v___y_1673_ = v___y_1687_;
v___y_1674_ = v_a_1720_;
v___y_1675_ = v___x_1752_;
v___y_1676_ = v___y_1693_;
v___y_1677_ = v___y_1692_;
v___y_1678_ = v___y_1690_;
v___y_1679_ = v___f_1724_;
v___y_1680_ = v___f_1725_;
v___y_1681_ = v___f_1726_;
v___y_1682_ = v___x_1752_;
goto v___jp_1665_;
}
else
{
v___y_1666_ = v___y_1688_;
v___y_1667_ = v_a_1749_;
v___y_1668_ = v___y_1691_;
v___y_1669_ = v___x_1750_;
v___y_1670_ = v___y_1689_;
v___y_1671_ = v___y_1686_;
v___y_1672_ = v_a_1722_;
v___y_1673_ = v___y_1687_;
v___y_1674_ = v_a_1720_;
v___y_1675_ = v___x_1752_;
v___y_1676_ = v___y_1693_;
v___y_1677_ = v___y_1692_;
v___y_1678_ = v___y_1690_;
v___y_1679_ = v___f_1724_;
v___y_1680_ = v___f_1725_;
v___y_1681_ = v___f_1726_;
v___y_1682_ = v___x_1457_;
goto v___jp_1665_;
}
}
else
{
v___y_1629_ = v___y_1688_;
v___y_1630_ = v___y_1691_;
v___y_1631_ = v___y_1689_;
v___y_1632_ = v___y_1686_;
v___y_1633_ = v_a_1722_;
v___y_1634_ = v___y_1687_;
v___y_1635_ = v_a_1720_;
v___y_1636_ = v___y_1693_;
v___y_1637_ = v___y_1692_;
v___y_1638_ = v___y_1690_;
v___y_1639_ = v___f_1724_;
v___y_1640_ = v___f_1725_;
v___y_1641_ = v___f_1726_;
v___y_1642_ = v_a_1749_;
goto v___jp_1628_;
}
}
else
{
lean_object* v_a_1754_; lean_object* v___x_1756_; uint8_t v_isShared_1757_; uint8_t v_isSharedCheck_1761_; 
lean_dec_ref(v___f_1724_);
lean_dec(v_a_1722_);
lean_dec(v_a_1720_);
lean_dec_ref(v___f_1349_);
v_a_1754_ = lean_ctor_get(v___x_1748_, 0);
v_isSharedCheck_1761_ = !lean_is_exclusive(v___x_1748_);
if (v_isSharedCheck_1761_ == 0)
{
v___x_1756_ = v___x_1748_;
v_isShared_1757_ = v_isSharedCheck_1761_;
goto v_resetjp_1755_;
}
else
{
lean_inc(v_a_1754_);
lean_dec(v___x_1748_);
v___x_1756_ = lean_box(0);
v_isShared_1757_ = v_isSharedCheck_1761_;
goto v_resetjp_1755_;
}
v_resetjp_1755_:
{
lean_object* v___x_1759_; 
if (v_isShared_1757_ == 0)
{
v___x_1759_ = v___x_1756_;
goto v_reusejp_1758_;
}
else
{
lean_object* v_reuseFailAlloc_1760_; 
v_reuseFailAlloc_1760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1760_, 0, v_a_1754_);
v___x_1759_ = v_reuseFailAlloc_1760_;
goto v_reusejp_1758_;
}
v_reusejp_1758_:
{
return v___x_1759_;
}
}
}
}
}
else
{
lean_object* v___x_1762_; 
lean_dec(v_val_1728_);
lean_dec_ref(v___x_1355_);
lean_dec_ref(v___x_1354_);
lean_dec_ref(v___x_1353_);
lean_dec_ref(v___x_1352_);
v___x_1762_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__26));
v___y_1583_ = v_a_1720_;
v___y_1584_ = v___f_1725_;
v___y_1585_ = v___f_1724_;
v___y_1586_ = v_a_1722_;
v___y_1587_ = v___f_1726_;
v_occs_1588_ = v___x_1762_;
v___y_1589_ = v___y_1686_;
v___y_1590_ = v___y_1687_;
v___y_1591_ = v___y_1688_;
v___y_1592_ = v___y_1689_;
v___y_1593_ = v___y_1690_;
v___y_1594_ = v___y_1691_;
v___y_1595_ = v___y_1692_;
v___y_1596_ = v___y_1693_;
goto v___jp_1582_;
}
}
}
else
{
lean_object* v_a_1763_; lean_object* v___x_1765_; uint8_t v_isShared_1766_; uint8_t v_isSharedCheck_1770_; 
lean_dec(v_a_1720_);
lean_dec(v_occs_1685_);
lean_dec_ref(v___x_1355_);
lean_dec_ref(v___x_1354_);
lean_dec_ref(v___x_1353_);
lean_dec_ref(v___x_1352_);
lean_dec_ref(v___f_1349_);
v_a_1763_ = lean_ctor_get(v___x_1721_, 0);
v_isSharedCheck_1770_ = !lean_is_exclusive(v___x_1721_);
if (v_isSharedCheck_1770_ == 0)
{
v___x_1765_ = v___x_1721_;
v_isShared_1766_ = v_isSharedCheck_1770_;
goto v_resetjp_1764_;
}
else
{
lean_inc(v_a_1763_);
lean_dec(v___x_1721_);
v___x_1765_ = lean_box(0);
v_isShared_1766_ = v_isSharedCheck_1770_;
goto v_resetjp_1764_;
}
v_resetjp_1764_:
{
lean_object* v___x_1768_; 
if (v_isShared_1766_ == 0)
{
v___x_1768_ = v___x_1765_;
goto v_reusejp_1767_;
}
else
{
lean_object* v_reuseFailAlloc_1769_; 
v_reuseFailAlloc_1769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1769_, 0, v_a_1763_);
v___x_1768_ = v_reuseFailAlloc_1769_;
goto v_reusejp_1767_;
}
v_reusejp_1767_:
{
return v___x_1768_;
}
}
}
}
else
{
lean_object* v_a_1771_; lean_object* v___x_1773_; uint8_t v_isShared_1774_; uint8_t v_isSharedCheck_1778_; 
lean_dec(v_occs_1685_);
lean_dec_ref(v___x_1355_);
lean_dec_ref(v___x_1354_);
lean_dec_ref(v___x_1353_);
lean_dec_ref(v___x_1352_);
lean_dec_ref(v___f_1349_);
v_a_1771_ = lean_ctor_get(v___x_1719_, 0);
v_isSharedCheck_1778_ = !lean_is_exclusive(v___x_1719_);
if (v_isSharedCheck_1778_ == 0)
{
v___x_1773_ = v___x_1719_;
v_isShared_1774_ = v_isSharedCheck_1778_;
goto v_resetjp_1772_;
}
else
{
lean_inc(v_a_1771_);
lean_dec(v___x_1719_);
v___x_1773_ = lean_box(0);
v_isShared_1774_ = v_isSharedCheck_1778_;
goto v_resetjp_1772_;
}
v_resetjp_1772_:
{
lean_object* v___x_1776_; 
if (v_isShared_1774_ == 0)
{
v___x_1776_ = v___x_1773_;
goto v_reusejp_1775_;
}
else
{
lean_object* v_reuseFailAlloc_1777_; 
v_reuseFailAlloc_1777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1777_, 0, v_a_1771_);
v___x_1776_ = v_reuseFailAlloc_1777_;
goto v_reusejp_1775_;
}
v_reusejp_1775_:
{
return v___x_1776_;
}
}
}
}
}
v___jp_1365_:
{
lean_object* v___x_1376_; 
v___x_1376_ = l_Lean_Elab_Tactic_Conv_getRhs___redArg(v___y_1369_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_);
if (lean_obj_tag(v___x_1376_) == 0)
{
lean_object* v_a_1377_; lean_object* v_expr_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; 
v_a_1377_ = lean_ctor_get(v___x_1376_, 0);
lean_inc(v_a_1377_);
lean_dec_ref_known(v___x_1376_, 1);
v_expr_1378_ = lean_ctor_get(v___y_1366_, 0);
v___x_1379_ = l_Lean_Expr_mvarId_x21(v_a_1377_);
lean_dec(v_a_1377_);
lean_inc_ref(v_expr_1378_);
v___x_1380_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3___redArg(v___x_1379_, v_expr_1378_, v___y_1373_);
lean_dec_ref(v___x_1380_);
v___x_1381_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_1369_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_);
if (lean_obj_tag(v___x_1381_) == 0)
{
lean_object* v_a_1382_; lean_object* v___x_1383_; 
v_a_1382_ = lean_ctor_get(v___x_1381_, 0);
lean_inc(v_a_1382_);
lean_dec_ref_known(v___x_1381_, 1);
v___x_1383_ = l_Lean_Meta_Simp_Result_getProof(v___y_1366_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_);
if (lean_obj_tag(v___x_1383_) == 0)
{
lean_object* v_a_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; 
v_a_1384_ = lean_ctor_get(v___x_1383_, 0);
lean_inc(v_a_1384_);
lean_dec_ref_known(v___x_1383_, 1);
v___x_1385_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3___redArg(v_a_1382_, v_a_1384_, v___y_1373_);
lean_dec_ref(v___x_1385_);
v___x_1386_ = lean_array_to_list(v_subgoals_1367_);
v___x_1387_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_1386_, v___y_1369_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_);
return v___x_1387_;
}
else
{
lean_object* v_a_1388_; lean_object* v___x_1390_; uint8_t v_isShared_1391_; uint8_t v_isSharedCheck_1395_; 
lean_dec(v_a_1382_);
lean_dec_ref(v_subgoals_1367_);
v_a_1388_ = lean_ctor_get(v___x_1383_, 0);
v_isSharedCheck_1395_ = !lean_is_exclusive(v___x_1383_);
if (v_isSharedCheck_1395_ == 0)
{
v___x_1390_ = v___x_1383_;
v_isShared_1391_ = v_isSharedCheck_1395_;
goto v_resetjp_1389_;
}
else
{
lean_inc(v_a_1388_);
lean_dec(v___x_1383_);
v___x_1390_ = lean_box(0);
v_isShared_1391_ = v_isSharedCheck_1395_;
goto v_resetjp_1389_;
}
v_resetjp_1389_:
{
lean_object* v___x_1393_; 
if (v_isShared_1391_ == 0)
{
v___x_1393_ = v___x_1390_;
goto v_reusejp_1392_;
}
else
{
lean_object* v_reuseFailAlloc_1394_; 
v_reuseFailAlloc_1394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1394_, 0, v_a_1388_);
v___x_1393_ = v_reuseFailAlloc_1394_;
goto v_reusejp_1392_;
}
v_reusejp_1392_:
{
return v___x_1393_;
}
}
}
}
else
{
lean_object* v_a_1396_; lean_object* v___x_1398_; uint8_t v_isShared_1399_; uint8_t v_isSharedCheck_1403_; 
lean_dec_ref(v_subgoals_1367_);
lean_dec_ref(v___y_1366_);
v_a_1396_ = lean_ctor_get(v___x_1381_, 0);
v_isSharedCheck_1403_ = !lean_is_exclusive(v___x_1381_);
if (v_isSharedCheck_1403_ == 0)
{
v___x_1398_ = v___x_1381_;
v_isShared_1399_ = v_isSharedCheck_1403_;
goto v_resetjp_1397_;
}
else
{
lean_inc(v_a_1396_);
lean_dec(v___x_1381_);
v___x_1398_ = lean_box(0);
v_isShared_1399_ = v_isSharedCheck_1403_;
goto v_resetjp_1397_;
}
v_resetjp_1397_:
{
lean_object* v___x_1401_; 
if (v_isShared_1399_ == 0)
{
v___x_1401_ = v___x_1398_;
goto v_reusejp_1400_;
}
else
{
lean_object* v_reuseFailAlloc_1402_; 
v_reuseFailAlloc_1402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1402_, 0, v_a_1396_);
v___x_1401_ = v_reuseFailAlloc_1402_;
goto v_reusejp_1400_;
}
v_reusejp_1400_:
{
return v___x_1401_;
}
}
}
}
else
{
lean_object* v_a_1404_; lean_object* v___x_1406_; uint8_t v_isShared_1407_; uint8_t v_isSharedCheck_1411_; 
lean_dec_ref(v_subgoals_1367_);
lean_dec_ref(v___y_1366_);
v_a_1404_ = lean_ctor_get(v___x_1376_, 0);
v_isSharedCheck_1411_ = !lean_is_exclusive(v___x_1376_);
if (v_isSharedCheck_1411_ == 0)
{
v___x_1406_ = v___x_1376_;
v_isShared_1407_ = v_isSharedCheck_1411_;
goto v_resetjp_1405_;
}
else
{
lean_inc(v_a_1404_);
lean_dec(v___x_1376_);
v___x_1406_ = lean_box(0);
v_isShared_1407_ = v_isSharedCheck_1411_;
goto v_resetjp_1405_;
}
v_resetjp_1405_:
{
lean_object* v___x_1409_; 
if (v_isShared_1407_ == 0)
{
v___x_1409_ = v___x_1406_;
goto v_reusejp_1408_;
}
else
{
lean_object* v_reuseFailAlloc_1410_; 
v_reuseFailAlloc_1410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1410_, 0, v_a_1404_);
v___x_1409_ = v_reuseFailAlloc_1410_;
goto v_reusejp_1408_;
}
v_reusejp_1408_:
{
return v___x_1409_;
}
}
}
}
v___jp_1412_:
{
size_t v_sz_1423_; size_t v___x_1424_; lean_object* v___x_1425_; 
v_sz_1423_ = lean_array_size(v___y_1422_);
v___x_1424_ = ((size_t)0ULL);
v___x_1425_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__5(v_sz_1423_, v___x_1424_, v___y_1422_);
v___y_1366_ = v___y_1414_;
v_subgoals_1367_ = v___x_1425_;
v___y_1368_ = v___y_1413_;
v___y_1369_ = v___y_1420_;
v___y_1370_ = v___y_1416_;
v___y_1371_ = v___y_1418_;
v___y_1372_ = v___y_1415_;
v___y_1373_ = v___y_1417_;
v___y_1374_ = v___y_1421_;
v___y_1375_ = v___y_1419_;
goto v___jp_1365_;
}
v___jp_1426_:
{
lean_object* v___x_1440_; 
v___x_1440_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg(v___y_1428_, v___y_1427_, v___y_1438_, v___y_1439_);
lean_dec(v___y_1439_);
lean_dec(v___y_1428_);
v___y_1413_ = v___y_1432_;
v___y_1414_ = v___y_1429_;
v___y_1415_ = v___y_1433_;
v___y_1416_ = v___y_1434_;
v___y_1417_ = v___y_1435_;
v___y_1418_ = v___y_1436_;
v___y_1419_ = v___y_1430_;
v___y_1420_ = v___y_1437_;
v___y_1421_ = v___y_1431_;
v___y_1422_ = v___x_1440_;
goto v___jp_1412_;
}
v___jp_1441_:
{
uint8_t v___x_1455_; 
v___x_1455_ = lean_nat_dec_le(v___y_1454_, v___y_1453_);
if (v___x_1455_ == 0)
{
lean_dec(v___y_1453_);
lean_inc(v___y_1454_);
v___y_1427_ = v___y_1442_;
v___y_1428_ = v___y_1443_;
v___y_1429_ = v___y_1444_;
v___y_1430_ = v___y_1445_;
v___y_1431_ = v___y_1446_;
v___y_1432_ = v___y_1447_;
v___y_1433_ = v___y_1448_;
v___y_1434_ = v___y_1449_;
v___y_1435_ = v___y_1450_;
v___y_1436_ = v___y_1451_;
v___y_1437_ = v___y_1452_;
v___y_1438_ = v___y_1454_;
v___y_1439_ = v___y_1454_;
goto v___jp_1426_;
}
else
{
v___y_1427_ = v___y_1442_;
v___y_1428_ = v___y_1443_;
v___y_1429_ = v___y_1444_;
v___y_1430_ = v___y_1445_;
v___y_1431_ = v___y_1446_;
v___y_1432_ = v___y_1447_;
v___y_1433_ = v___y_1448_;
v___y_1434_ = v___y_1449_;
v___y_1435_ = v___y_1450_;
v___y_1436_ = v___y_1451_;
v___y_1437_ = v___y_1452_;
v___y_1438_ = v___y_1454_;
v___y_1439_ = v___y_1453_;
goto v___jp_1426_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___boxed(lean_object** _args){
lean_object* v___x_1792_ = _args[0];
lean_object* v___f_1793_ = _args[1];
lean_object* v___x_1794_ = _args[2];
lean_object* v_stx_1795_ = _args[3];
lean_object* v___x_1796_ = _args[4];
lean_object* v___x_1797_ = _args[5];
lean_object* v___x_1798_ = _args[6];
lean_object* v___x_1799_ = _args[7];
lean_object* v___y_1800_ = _args[8];
lean_object* v___y_1801_ = _args[9];
lean_object* v___y_1802_ = _args[10];
lean_object* v___y_1803_ = _args[11];
lean_object* v___y_1804_ = _args[12];
lean_object* v___y_1805_ = _args[13];
lean_object* v___y_1806_ = _args[14];
lean_object* v___y_1807_ = _args[15];
lean_object* v___y_1808_ = _args[16];
_start:
{
uint8_t v___x_19446__boxed_1809_; uint8_t v___x_19448__boxed_1810_; lean_object* v_res_1811_; 
v___x_19446__boxed_1809_ = lean_unbox(v___x_1792_);
v___x_19448__boxed_1810_ = lean_unbox(v___x_1794_);
v_res_1811_ = l_Lean_Elab_Tactic_Conv_evalPattern___lam__6(v___x_19446__boxed_1809_, v___f_1793_, v___x_19448__boxed_1810_, v_stx_1795_, v___x_1796_, v___x_1797_, v___x_1798_, v___x_1799_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_);
lean_dec(v___y_1807_);
lean_dec_ref(v___y_1806_);
lean_dec(v___y_1805_);
lean_dec_ref(v___y_1804_);
lean_dec(v___y_1803_);
lean_dec_ref(v___y_1802_);
lean_dec(v___y_1801_);
lean_dec_ref(v___y_1800_);
lean_dec(v_stx_1795_);
return v_res_1811_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern(lean_object* v_stx_1824_, lean_object* v_a_1825_, lean_object* v_a_1826_, lean_object* v_a_1827_, lean_object* v_a_1828_, lean_object* v_a_1829_, lean_object* v_a_1830_, lean_object* v_a_1831_, lean_object* v_a_1832_){
_start:
{
lean_object* v___f_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; uint8_t v___x_1840_; uint8_t v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___y_1844_; lean_object* v___x_1845_; 
v___f_1834_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___closed__0));
v___x_1835_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___closed__1));
v___x_1836_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___closed__2));
v___x_1837_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___closed__3));
v___x_1838_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___closed__4));
v___x_1839_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___closed__6));
lean_inc(v_stx_1824_);
v___x_1840_ = l_Lean_Syntax_isOfKind(v_stx_1824_, v___x_1839_);
v___x_1841_ = 1;
v___x_1842_ = lean_box(v___x_1840_);
v___x_1843_ = lean_box(v___x_1841_);
v___y_1844_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___boxed), 17, 8);
lean_closure_set(v___y_1844_, 0, v___x_1842_);
lean_closure_set(v___y_1844_, 1, v___f_1834_);
lean_closure_set(v___y_1844_, 2, v___x_1843_);
lean_closure_set(v___y_1844_, 3, v_stx_1824_);
lean_closure_set(v___y_1844_, 4, v___x_1835_);
lean_closure_set(v___y_1844_, 5, v___x_1836_);
lean_closure_set(v___y_1844_, 6, v___x_1837_);
lean_closure_set(v___y_1844_, 7, v___x_1838_);
v___x_1845_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___y_1844_, v_a_1825_, v_a_1826_, v_a_1827_, v_a_1828_, v_a_1829_, v_a_1830_, v_a_1831_, v_a_1832_);
return v___x_1845_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___boxed(lean_object* v_stx_1846_, lean_object* v_a_1847_, lean_object* v_a_1848_, lean_object* v_a_1849_, lean_object* v_a_1850_, lean_object* v_a_1851_, lean_object* v_a_1852_, lean_object* v_a_1853_, lean_object* v_a_1854_, lean_object* v_a_1855_){
_start:
{
lean_object* v_res_1856_; 
v_res_1856_ = l_Lean_Elab_Tactic_Conv_evalPattern(v_stx_1846_, v_a_1847_, v_a_1848_, v_a_1849_, v_a_1850_, v_a_1851_, v_a_1852_, v_a_1853_, v_a_1854_);
lean_dec(v_a_1854_);
lean_dec_ref(v_a_1853_);
lean_dec(v_a_1852_);
lean_dec_ref(v_a_1851_);
lean_dec(v_a_1850_);
lean_dec_ref(v_a_1849_);
lean_dec(v_a_1848_);
lean_dec_ref(v_a_1847_);
return v_res_1856_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1(lean_object* v_00_u03b1_1857_, lean_object* v_ref_1858_, lean_object* v_msg_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_){
_start:
{
lean_object* v___x_1869_; 
v___x_1869_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1___redArg(v_ref_1858_, v_msg_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_);
return v___x_1869_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1___boxed(lean_object* v_00_u03b1_1870_, lean_object* v_ref_1871_, lean_object* v_msg_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_){
_start:
{
lean_object* v_res_1882_; 
v_res_1882_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1(v_00_u03b1_1870_, v_ref_1871_, v_msg_1872_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_);
lean_dec(v___y_1880_);
lean_dec_ref(v___y_1879_);
lean_dec(v___y_1878_);
lean_dec_ref(v___y_1877_);
lean_dec(v___y_1876_);
lean_dec_ref(v___y_1875_);
lean_dec(v___y_1874_);
lean_dec_ref(v___y_1873_);
lean_dec(v_ref_1871_);
return v_res_1882_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3(lean_object* v_mvarId_1883_, lean_object* v_val_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_){
_start:
{
lean_object* v___x_1894_; 
v___x_1894_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3___redArg(v_mvarId_1883_, v_val_1884_, v___y_1890_);
return v___x_1894_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3___boxed(lean_object* v_mvarId_1895_, lean_object* v_val_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_){
_start:
{
lean_object* v_res_1906_; 
v_res_1906_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3(v_mvarId_1895_, v_val_1896_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_);
lean_dec(v___y_1904_);
lean_dec_ref(v___y_1903_);
lean_dec(v___y_1902_);
lean_dec_ref(v___y_1901_);
lean_dec(v___y_1900_);
lean_dec_ref(v___y_1899_);
lean_dec(v___y_1898_);
lean_dec_ref(v___y_1897_);
return v_res_1906_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4(lean_object* v_00_u03b1_1907_, lean_object* v_msg_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_){
_start:
{
lean_object* v___x_1918_; 
v___x_1918_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg(v_msg_1908_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_);
return v___x_1918_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___boxed(lean_object* v_00_u03b1_1919_, lean_object* v_msg_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_){
_start:
{
lean_object* v_res_1930_; 
v_res_1930_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4(v_00_u03b1_1919_, v_msg_1920_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_);
lean_dec(v___y_1928_);
lean_dec_ref(v___y_1927_);
lean_dec(v___y_1926_);
lean_dec_ref(v___y_1925_);
lean_dec(v___y_1924_);
lean_dec_ref(v___y_1923_);
lean_dec(v___y_1922_);
lean_dec_ref(v___y_1921_);
return v_res_1930_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6(lean_object* v_n_1931_, lean_object* v_as_1932_, lean_object* v_lo_1933_, lean_object* v_hi_1934_, lean_object* v_w_1935_, lean_object* v_hlo_1936_, lean_object* v_hhi_1937_){
_start:
{
lean_object* v___x_1938_; 
v___x_1938_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg(v_n_1931_, v_as_1932_, v_lo_1933_, v_hi_1934_);
return v___x_1938_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___boxed(lean_object* v_n_1939_, lean_object* v_as_1940_, lean_object* v_lo_1941_, lean_object* v_hi_1942_, lean_object* v_w_1943_, lean_object* v_hlo_1944_, lean_object* v_hhi_1945_){
_start:
{
lean_object* v_res_1946_; 
v_res_1946_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6(v_n_1939_, v_as_1940_, v_lo_1941_, v_hi_1942_, v_w_1943_, v_hlo_1944_, v_hhi_1945_);
lean_dec(v_hi_1942_);
lean_dec(v_n_1939_);
return v_res_1946_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7(lean_object* v_as_1947_, size_t v_sz_1948_, size_t v_i_1949_, lean_object* v_bs_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_){
_start:
{
lean_object* v___x_1960_; 
v___x_1960_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg(v_sz_1948_, v_i_1949_, v_bs_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_);
return v___x_1960_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___boxed(lean_object* v_as_1961_, lean_object* v_sz_1962_, lean_object* v_i_1963_, lean_object* v_bs_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_){
_start:
{
size_t v_sz_boxed_1974_; size_t v_i_boxed_1975_; lean_object* v_res_1976_; 
v_sz_boxed_1974_ = lean_unbox_usize(v_sz_1962_);
lean_dec(v_sz_1962_);
v_i_boxed_1975_ = lean_unbox_usize(v_i_1963_);
lean_dec(v_i_1963_);
v_res_1976_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7(v_as_1961_, v_sz_boxed_1974_, v_i_boxed_1975_, v_bs_1964_, v___y_1965_, v___y_1966_, v___y_1967_, v___y_1968_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_);
lean_dec(v___y_1972_);
lean_dec_ref(v___y_1971_);
lean_dec(v___y_1970_);
lean_dec_ref(v___y_1969_);
lean_dec(v___y_1968_);
lean_dec_ref(v___y_1967_);
lean_dec(v___y_1966_);
lean_dec_ref(v___y_1965_);
lean_dec_ref(v_as_1961_);
return v_res_1976_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9(lean_object* v_n_1977_, lean_object* v_as_1978_, lean_object* v_lo_1979_, lean_object* v_hi_1980_, lean_object* v_w_1981_, lean_object* v_hlo_1982_, lean_object* v_hhi_1983_){
_start:
{
lean_object* v___x_1984_; 
v___x_1984_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg(v_n_1977_, v_as_1978_, v_lo_1979_, v_hi_1980_);
return v___x_1984_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___boxed(lean_object* v_n_1985_, lean_object* v_as_1986_, lean_object* v_lo_1987_, lean_object* v_hi_1988_, lean_object* v_w_1989_, lean_object* v_hlo_1990_, lean_object* v_hhi_1991_){
_start:
{
lean_object* v_res_1992_; 
v_res_1992_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9(v_n_1985_, v_as_1986_, v_lo_1987_, v_hi_1988_, v_w_1989_, v_hlo_1990_, v_hhi_1991_);
lean_dec(v_hi_1988_);
lean_dec(v_n_1985_);
return v_res_1992_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3(lean_object* v_00_u03b2_1993_, lean_object* v_x_1994_, lean_object* v_x_1995_, lean_object* v_x_1996_){
_start:
{
lean_object* v___x_1997_; 
v___x_1997_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3___redArg(v_x_1994_, v_x_1995_, v_x_1996_);
return v___x_1997_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6_spec__8(lean_object* v_n_1998_, lean_object* v_lo_1999_, lean_object* v_hi_2000_, lean_object* v_hhi_2001_, lean_object* v_pivot_2002_, lean_object* v_as_2003_, lean_object* v_i_2004_, lean_object* v_k_2005_, lean_object* v_ilo_2006_, lean_object* v_ik_2007_, lean_object* v_w_2008_){
_start:
{
lean_object* v___x_2009_; 
v___x_2009_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6_spec__8___redArg(v_hi_2000_, v_pivot_2002_, v_as_2003_, v_i_2004_, v_k_2005_);
return v___x_2009_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6_spec__8___boxed(lean_object* v_n_2010_, lean_object* v_lo_2011_, lean_object* v_hi_2012_, lean_object* v_hhi_2013_, lean_object* v_pivot_2014_, lean_object* v_as_2015_, lean_object* v_i_2016_, lean_object* v_k_2017_, lean_object* v_ilo_2018_, lean_object* v_ik_2019_, lean_object* v_w_2020_){
_start:
{
lean_object* v_res_2021_; 
v_res_2021_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6_spec__8(v_n_2010_, v_lo_2011_, v_hi_2012_, v_hhi_2013_, v_pivot_2014_, v_as_2015_, v_i_2016_, v_k_2017_, v_ilo_2018_, v_ik_2019_, v_w_2020_);
lean_dec_ref(v_pivot_2014_);
lean_dec(v_hi_2012_);
lean_dec(v_lo_2011_);
lean_dec(v_n_2010_);
return v_res_2021_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9_spec__13(lean_object* v_n_2022_, lean_object* v_lo_2023_, lean_object* v_hi_2024_, lean_object* v_hhi_2025_, lean_object* v_pivot_2026_, lean_object* v_as_2027_, lean_object* v_i_2028_, lean_object* v_k_2029_, lean_object* v_ilo_2030_, lean_object* v_ik_2031_, lean_object* v_w_2032_){
_start:
{
lean_object* v___x_2033_; 
v___x_2033_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9_spec__13___redArg(v_hi_2024_, v_pivot_2026_, v_as_2027_, v_i_2028_, v_k_2029_);
return v___x_2033_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9_spec__13___boxed(lean_object* v_n_2034_, lean_object* v_lo_2035_, lean_object* v_hi_2036_, lean_object* v_hhi_2037_, lean_object* v_pivot_2038_, lean_object* v_as_2039_, lean_object* v_i_2040_, lean_object* v_k_2041_, lean_object* v_ilo_2042_, lean_object* v_ik_2043_, lean_object* v_w_2044_){
_start:
{
lean_object* v_res_2045_; 
v_res_2045_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9_spec__13(v_n_2034_, v_lo_2035_, v_hi_2036_, v_hhi_2037_, v_pivot_2038_, v_as_2039_, v_i_2040_, v_k_2041_, v_ilo_2042_, v_ik_2043_, v_w_2044_);
lean_dec_ref(v_pivot_2038_);
lean_dec(v_hi_2036_);
lean_dec(v_lo_2035_);
lean_dec(v_n_2034_);
return v_res_2045_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4(lean_object* v_00_u03b2_2046_, lean_object* v_x_2047_, size_t v_x_2048_, size_t v_x_2049_, lean_object* v_x_2050_, lean_object* v_x_2051_){
_start:
{
lean_object* v___x_2052_; 
v___x_2052_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg(v_x_2047_, v_x_2048_, v_x_2049_, v_x_2050_, v_x_2051_);
return v___x_2052_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___boxed(lean_object* v_00_u03b2_2053_, lean_object* v_x_2054_, lean_object* v_x_2055_, lean_object* v_x_2056_, lean_object* v_x_2057_, lean_object* v_x_2058_){
_start:
{
size_t v_x_20562__boxed_2059_; size_t v_x_20563__boxed_2060_; lean_object* v_res_2061_; 
v_x_20562__boxed_2059_ = lean_unbox_usize(v_x_2055_);
lean_dec(v_x_2055_);
v_x_20563__boxed_2060_ = lean_unbox_usize(v_x_2056_);
lean_dec(v_x_2056_);
v_res_2061_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4(v_00_u03b2_2053_, v_x_2054_, v_x_20562__boxed_2059_, v_x_20563__boxed_2060_, v_x_2057_, v_x_2058_);
return v_res_2061_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11_spec__13(lean_object* v_as_2062_, lean_object* v_a_2063_, lean_object* v_x_2064_, lean_object* v_x_2065_){
_start:
{
uint8_t v___x_2066_; 
v___x_2066_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11_spec__13___redArg(v_as_2062_, v_a_2063_, v_x_2064_);
return v___x_2066_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11_spec__13___boxed(lean_object* v_as_2067_, lean_object* v_a_2068_, lean_object* v_x_2069_, lean_object* v_x_2070_){
_start:
{
uint8_t v_res_2071_; lean_object* v_r_2072_; 
v_res_2071_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11_spec__13(v_as_2067_, v_a_2068_, v_x_2069_, v_x_2070_);
lean_dec_ref(v_a_2068_);
lean_dec_ref(v_as_2067_);
v_r_2072_ = lean_box(v_res_2071_);
return v_r_2072_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__12(lean_object* v_00_u03b2_2073_, lean_object* v_n_2074_, lean_object* v_k_2075_, lean_object* v_v_2076_){
_start:
{
lean_object* v___x_2077_; 
v___x_2077_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__12___redArg(v_n_2074_, v_k_2075_, v_v_2076_);
return v___x_2077_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__13(lean_object* v_00_u03b2_2078_, size_t v_depth_2079_, lean_object* v_keys_2080_, lean_object* v_vals_2081_, lean_object* v_heq_2082_, lean_object* v_i_2083_, lean_object* v_entries_2084_){
_start:
{
lean_object* v___x_2085_; 
v___x_2085_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__13___redArg(v_depth_2079_, v_keys_2080_, v_vals_2081_, v_i_2083_, v_entries_2084_);
return v___x_2085_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__13___boxed(lean_object* v_00_u03b2_2086_, lean_object* v_depth_2087_, lean_object* v_keys_2088_, lean_object* v_vals_2089_, lean_object* v_heq_2090_, lean_object* v_i_2091_, lean_object* v_entries_2092_){
_start:
{
size_t v_depth_boxed_2093_; lean_object* v_res_2094_; 
v_depth_boxed_2093_ = lean_unbox_usize(v_depth_2087_);
lean_dec(v_depth_2087_);
v_res_2094_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__13(v_00_u03b2_2086_, v_depth_boxed_2093_, v_keys_2088_, v_vals_2089_, v_heq_2090_, v_i_2091_, v_entries_2092_);
lean_dec_ref(v_vals_2089_);
lean_dec_ref(v_keys_2088_);
return v_res_2094_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__12_spec__16(lean_object* v_00_u03b2_2095_, lean_object* v_x_2096_, lean_object* v_x_2097_, lean_object* v_x_2098_, lean_object* v_x_2099_){
_start:
{
lean_object* v___x_2100_; 
v___x_2100_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__12_spec__16___redArg(v_x_2096_, v_x_2097_, v_x_2098_, v_x_2099_);
return v___x_2100_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1(){
_start:
{
lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; 
v___x_2110_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2111_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___closed__6));
v___x_2112_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___closed__2));
v___x_2113_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalPattern___boxed), 10, 0);
v___x_2114_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2110_, v___x_2111_, v___x_2112_, v___x_2113_);
return v___x_2114_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___boxed(lean_object* v_a_2115_){
_start:
{
lean_object* v_res_2116_; 
v_res_2116_ = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1();
return v_res_2116_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3(){
_start:
{
lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; 
v___x_2143_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___closed__2));
v___x_2144_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__6));
v___x_2145_ = l_Lean_addBuiltinDeclarationRanges(v___x_2143_, v___x_2144_);
return v___x_2145_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___boxed(lean_object* v_a_2146_){
_start:
{
lean_object* v_res_2147_; 
v_res_2147_ = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3();
return v_res_2147_;
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
