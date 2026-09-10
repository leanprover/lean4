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
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Expr_toHeadIndex(lean_object*);
uint8_t l_Lean_instBEqHeadIndex_beq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEqGuarded(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
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
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
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
uint8_t l_Lean_Meta_instBEqTransparencyMode_beq(uint8_t, uint8_t);
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
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___y_176_; lean_object* v___x_193_; 
v___x_193_ = l_Lean_Meta_openAbstractMVarsResult(v_pattern_168_, v___y_170_, v___y_171_, v___y_172_, v___y_173_);
if (lean_obj_tag(v___x_193_) == 0)
{
lean_object* v_a_194_; lean_object* v_snd_195_; lean_object* v_snd_196_; lean_object* v___x_197_; uint8_t v_transparency_198_; uint8_t v___x_199_; uint8_t v___x_200_; 
v_a_194_ = lean_ctor_get(v___x_193_, 0);
lean_inc(v_a_194_);
lean_dec_ref_known(v___x_193_, 1);
v_snd_195_ = lean_ctor_get(v_a_194_, 1);
lean_inc(v_snd_195_);
lean_dec(v_a_194_);
v_snd_196_ = lean_ctor_get(v_snd_195_, 1);
lean_inc(v_snd_196_);
lean_dec(v_snd_195_);
v___x_197_ = l_Lean_Meta_Context_config(v___y_170_);
v_transparency_198_ = lean_ctor_get_uint8(v___x_197_, 9);
lean_dec_ref(v___x_197_);
v___x_199_ = 2;
v___x_200_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_198_, v___x_199_);
if (v___x_200_ == 0)
{
lean_object* v_keyedConfig_201_; uint8_t v_trackZetaDelta_202_; lean_object* v_zetaDeltaSet_203_; lean_object* v_lctx_204_; lean_object* v_localInstances_205_; lean_object* v_defEqCtx_x3f_206_; lean_object* v_synthPendingDepth_207_; lean_object* v_customCanUnfoldPredicate_x3f_208_; uint8_t v_univApprox_209_; uint8_t v_inTypeClassResolution_210_; uint8_t v_cacheInferType_211_; lean_object* v___x_213_; uint8_t v_isShared_214_; uint8_t v_isSharedCheck_220_; 
v_keyedConfig_201_ = lean_ctor_get(v___y_170_, 0);
v_trackZetaDelta_202_ = lean_ctor_get_uint8(v___y_170_, sizeof(void*)*7);
v_zetaDeltaSet_203_ = lean_ctor_get(v___y_170_, 1);
v_lctx_204_ = lean_ctor_get(v___y_170_, 2);
v_localInstances_205_ = lean_ctor_get(v___y_170_, 3);
v_defEqCtx_x3f_206_ = lean_ctor_get(v___y_170_, 4);
v_synthPendingDepth_207_ = lean_ctor_get(v___y_170_, 5);
v_customCanUnfoldPredicate_x3f_208_ = lean_ctor_get(v___y_170_, 6);
v_univApprox_209_ = lean_ctor_get_uint8(v___y_170_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_210_ = lean_ctor_get_uint8(v___y_170_, sizeof(void*)*7 + 2);
v_cacheInferType_211_ = lean_ctor_get_uint8(v___y_170_, sizeof(void*)*7 + 3);
v_isSharedCheck_220_ = !lean_is_exclusive(v___y_170_);
if (v_isSharedCheck_220_ == 0)
{
v___x_213_ = v___y_170_;
v_isShared_214_ = v_isSharedCheck_220_;
goto v_resetjp_212_;
}
else
{
lean_inc(v_customCanUnfoldPredicate_x3f_208_);
lean_inc(v_synthPendingDepth_207_);
lean_inc(v_defEqCtx_x3f_206_);
lean_inc(v_localInstances_205_);
lean_inc(v_lctx_204_);
lean_inc(v_zetaDeltaSet_203_);
lean_inc(v_keyedConfig_201_);
lean_dec(v___y_170_);
v___x_213_ = lean_box(0);
v_isShared_214_ = v_isSharedCheck_220_;
goto v_resetjp_212_;
}
v_resetjp_212_:
{
lean_object* v___x_215_; lean_object* v___x_217_; 
v___x_215_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_199_, v_keyedConfig_201_);
if (v_isShared_214_ == 0)
{
lean_ctor_set(v___x_213_, 0, v___x_215_);
v___x_217_ = v___x_213_;
goto v_reusejp_216_;
}
else
{
lean_object* v_reuseFailAlloc_219_; 
v_reuseFailAlloc_219_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_219_, 0, v___x_215_);
lean_ctor_set(v_reuseFailAlloc_219_, 1, v_zetaDeltaSet_203_);
lean_ctor_set(v_reuseFailAlloc_219_, 2, v_lctx_204_);
lean_ctor_set(v_reuseFailAlloc_219_, 3, v_localInstances_205_);
lean_ctor_set(v_reuseFailAlloc_219_, 4, v_defEqCtx_x3f_206_);
lean_ctor_set(v_reuseFailAlloc_219_, 5, v_synthPendingDepth_207_);
lean_ctor_set(v_reuseFailAlloc_219_, 6, v_customCanUnfoldPredicate_x3f_208_);
lean_ctor_set_uint8(v_reuseFailAlloc_219_, sizeof(void*)*7, v_trackZetaDelta_202_);
lean_ctor_set_uint8(v_reuseFailAlloc_219_, sizeof(void*)*7 + 1, v_univApprox_209_);
lean_ctor_set_uint8(v_reuseFailAlloc_219_, sizeof(void*)*7 + 2, v_inTypeClassResolution_210_);
lean_ctor_set_uint8(v_reuseFailAlloc_219_, sizeof(void*)*7 + 3, v_cacheInferType_211_);
v___x_217_ = v_reuseFailAlloc_219_;
goto v_reusejp_216_;
}
v_reusejp_216_:
{
lean_object* v___x_218_; 
v___x_218_ = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_matchPattern_x3f_go_x3f(v_snd_196_, v_e_169_, v___x_217_, v___y_171_, v___y_172_, v___y_173_);
lean_dec_ref(v___x_217_);
v___y_176_ = v___x_218_;
goto v___jp_175_;
}
}
}
else
{
lean_object* v___x_221_; 
v___x_221_ = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_matchPattern_x3f_go_x3f(v_snd_196_, v_e_169_, v___y_170_, v___y_171_, v___y_172_, v___y_173_);
lean_dec_ref(v___y_170_);
v___y_176_ = v___x_221_;
goto v___jp_175_;
}
}
else
{
lean_object* v_a_222_; lean_object* v___x_224_; uint8_t v_isShared_225_; uint8_t v_isSharedCheck_229_; 
lean_dec_ref(v___y_170_);
lean_dec_ref(v_e_169_);
v_a_222_ = lean_ctor_get(v___x_193_, 0);
v_isSharedCheck_229_ = !lean_is_exclusive(v___x_193_);
if (v_isSharedCheck_229_ == 0)
{
v___x_224_ = v___x_193_;
v_isShared_225_ = v_isSharedCheck_229_;
goto v_resetjp_223_;
}
else
{
lean_inc(v_a_222_);
lean_dec(v___x_193_);
v___x_224_ = lean_box(0);
v_isShared_225_ = v_isSharedCheck_229_;
goto v_resetjp_223_;
}
v_resetjp_223_:
{
lean_object* v___x_227_; 
if (v_isShared_225_ == 0)
{
v___x_227_ = v___x_224_;
goto v_reusejp_226_;
}
else
{
lean_object* v_reuseFailAlloc_228_; 
v_reuseFailAlloc_228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_228_, 0, v_a_222_);
v___x_227_ = v_reuseFailAlloc_228_;
goto v_reusejp_226_;
}
v_reusejp_226_:
{
return v___x_227_;
}
}
}
v___jp_175_:
{
if (lean_obj_tag(v___y_176_) == 0)
{
lean_object* v_a_177_; lean_object* v___x_179_; uint8_t v_isShared_180_; uint8_t v_isSharedCheck_184_; 
v_a_177_ = lean_ctor_get(v___y_176_, 0);
v_isSharedCheck_184_ = !lean_is_exclusive(v___y_176_);
if (v_isSharedCheck_184_ == 0)
{
v___x_179_ = v___y_176_;
v_isShared_180_ = v_isSharedCheck_184_;
goto v_resetjp_178_;
}
else
{
lean_inc(v_a_177_);
lean_dec(v___y_176_);
v___x_179_ = lean_box(0);
v_isShared_180_ = v_isSharedCheck_184_;
goto v_resetjp_178_;
}
v_resetjp_178_:
{
lean_object* v___x_182_; 
if (v_isShared_180_ == 0)
{
v___x_182_ = v___x_179_;
goto v_reusejp_181_;
}
else
{
lean_object* v_reuseFailAlloc_183_; 
v_reuseFailAlloc_183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_183_, 0, v_a_177_);
v___x_182_ = v_reuseFailAlloc_183_;
goto v_reusejp_181_;
}
v_reusejp_181_:
{
return v___x_182_;
}
}
}
else
{
lean_object* v_a_185_; lean_object* v___x_187_; uint8_t v_isShared_188_; uint8_t v_isSharedCheck_192_; 
v_a_185_ = lean_ctor_get(v___y_176_, 0);
v_isSharedCheck_192_ = !lean_is_exclusive(v___y_176_);
if (v_isSharedCheck_192_ == 0)
{
v___x_187_ = v___y_176_;
v_isShared_188_ = v_isSharedCheck_192_;
goto v_resetjp_186_;
}
else
{
lean_inc(v_a_185_);
lean_dec(v___y_176_);
v___x_187_ = lean_box(0);
v_isShared_188_ = v_isSharedCheck_192_;
goto v_resetjp_186_;
}
v_resetjp_186_:
{
lean_object* v___x_190_; 
if (v_isShared_188_ == 0)
{
v___x_190_ = v___x_187_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v_a_185_);
v___x_190_ = v_reuseFailAlloc_191_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
return v___x_190_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_matchPattern_x3f___lam__0___boxed(lean_object* v_pattern_230_, lean_object* v_e_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_){
_start:
{
lean_object* v_res_237_; 
v_res_237_ = l_Lean_Elab_Tactic_Conv_matchPattern_x3f___lam__0(v_pattern_230_, v_e_231_, v___y_232_, v___y_233_, v___y_234_, v___y_235_);
lean_dec(v___y_235_);
lean_dec_ref(v___y_234_);
lean_dec(v___y_233_);
return v_res_237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_matchPattern_x3f(lean_object* v_pattern_238_, lean_object* v_e_239_, lean_object* v_a_240_, lean_object* v_a_241_, lean_object* v_a_242_, lean_object* v_a_243_){
_start:
{
lean_object* v___f_245_; uint8_t v___x_246_; lean_object* v___x_247_; 
v___f_245_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_matchPattern_x3f___lam__0___boxed), 7, 2);
lean_closure_set(v___f_245_, 0, v_pattern_238_);
lean_closure_set(v___f_245_, 1, v_e_239_);
v___x_246_ = 0;
v___x_247_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Conv_matchPattern_x3f_spec__0___redArg(v___f_245_, v___x_246_, v_a_240_, v_a_241_, v_a_242_, v_a_243_);
return v___x_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_matchPattern_x3f___boxed(lean_object* v_pattern_248_, lean_object* v_e_249_, lean_object* v_a_250_, lean_object* v_a_251_, lean_object* v_a_252_, lean_object* v_a_253_, lean_object* v_a_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = l_Lean_Elab_Tactic_Conv_matchPattern_x3f(v_pattern_248_, v_e_249_, v_a_250_, v_a_251_, v_a_252_, v_a_253_);
lean_dec(v_a_253_);
lean_dec_ref(v_a_252_);
lean_dec(v_a_251_);
lean_dec_ref(v_a_250_);
return v_res_255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorIdx(lean_object* v_x_256_){
_start:
{
if (lean_obj_tag(v_x_256_) == 0)
{
lean_object* v___x_257_; 
v___x_257_ = lean_unsigned_to_nat(0u);
return v___x_257_;
}
else
{
lean_object* v___x_258_; 
v___x_258_ = lean_unsigned_to_nat(1u);
return v___x_258_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorIdx___boxed(lean_object* v_x_259_){
_start:
{
lean_object* v_res_260_; 
v_res_260_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorIdx(v_x_259_);
lean_dec_ref(v_x_259_);
return v_res_260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorElim___redArg(lean_object* v_t_261_, lean_object* v_k_262_){
_start:
{
if (lean_obj_tag(v_t_261_) == 0)
{
lean_object* v_subgoals_263_; lean_object* v___x_264_; 
v_subgoals_263_ = lean_ctor_get(v_t_261_, 0);
lean_inc_ref(v_subgoals_263_);
lean_dec_ref_known(v_t_261_, 1);
v___x_264_ = lean_apply_1(v_k_262_, v_subgoals_263_);
return v___x_264_;
}
else
{
lean_object* v_subgoals_265_; lean_object* v_idx_266_; lean_object* v_remaining_267_; lean_object* v___x_268_; 
v_subgoals_265_ = lean_ctor_get(v_t_261_, 0);
lean_inc_ref(v_subgoals_265_);
v_idx_266_ = lean_ctor_get(v_t_261_, 1);
lean_inc(v_idx_266_);
v_remaining_267_ = lean_ctor_get(v_t_261_, 2);
lean_inc(v_remaining_267_);
lean_dec_ref_known(v_t_261_, 3);
v___x_268_ = lean_apply_3(v_k_262_, v_subgoals_265_, v_idx_266_, v_remaining_267_);
return v___x_268_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorElim(lean_object* v_motive_269_, lean_object* v_ctorIdx_270_, lean_object* v_t_271_, lean_object* v_h_272_, lean_object* v_k_273_){
_start:
{
lean_object* v___x_274_; 
v___x_274_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorElim___redArg(v_t_271_, v_k_273_);
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorElim___boxed(lean_object* v_motive_275_, lean_object* v_ctorIdx_276_, lean_object* v_t_277_, lean_object* v_h_278_, lean_object* v_k_279_){
_start:
{
lean_object* v_res_280_; 
v_res_280_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorElim(v_motive_275_, v_ctorIdx_276_, v_t_277_, v_h_278_, v_k_279_);
lean_dec(v_ctorIdx_276_);
return v_res_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_all_elim___redArg(lean_object* v_t_281_, lean_object* v_all_282_){
_start:
{
lean_object* v___x_283_; 
v___x_283_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorElim___redArg(v_t_281_, v_all_282_);
return v___x_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_all_elim(lean_object* v_motive_284_, lean_object* v_t_285_, lean_object* v_h_286_, lean_object* v_all_287_){
_start:
{
lean_object* v___x_288_; 
v___x_288_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorElim___redArg(v_t_285_, v_all_287_);
return v___x_288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_occs_elim___redArg(lean_object* v_t_289_, lean_object* v_occs_290_){
_start:
{
lean_object* v___x_291_; 
v___x_291_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorElim___redArg(v_t_289_, v_occs_290_);
return v___x_291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_occs_elim(lean_object* v_motive_292_, lean_object* v_t_293_, lean_object* v_h_294_, lean_object* v_occs_295_){
_start:
{
lean_object* v___x_296_; 
v___x_296_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorElim___redArg(v_t_293_, v_occs_295_);
return v___x_296_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Conv_PatternMatchState_isDone(lean_object* v_x_297_){
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
lean_object* v_remaining_299_; uint8_t v___x_300_; 
v_remaining_299_ = lean_ctor_get(v_x_297_, 2);
v___x_300_ = l_List_isEmpty___redArg(v_remaining_299_);
return v___x_300_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_isDone___boxed(lean_object* v_x_301_){
_start:
{
uint8_t v_res_302_; lean_object* v_r_303_; 
v_res_302_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_isDone(v_x_301_);
lean_dec_ref(v_x_301_);
v_r_303_ = lean_box(v_res_302_);
return v_r_303_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Conv_PatternMatchState_isReady(lean_object* v_x_304_){
_start:
{
if (lean_obj_tag(v_x_304_) == 0)
{
uint8_t v___x_305_; 
v___x_305_ = 1;
return v___x_305_;
}
else
{
lean_object* v_remaining_306_; 
v_remaining_306_ = lean_ctor_get(v_x_304_, 2);
if (lean_obj_tag(v_remaining_306_) == 1)
{
lean_object* v_head_307_; lean_object* v_idx_308_; lean_object* v_fst_309_; uint8_t v___x_310_; 
v_head_307_ = lean_ctor_get(v_remaining_306_, 0);
v_idx_308_ = lean_ctor_get(v_x_304_, 1);
v_fst_309_ = lean_ctor_get(v_head_307_, 0);
v___x_310_ = lean_nat_dec_eq(v_idx_308_, v_fst_309_);
return v___x_310_;
}
else
{
uint8_t v___x_311_; 
v___x_311_ = 0;
return v___x_311_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_isReady___boxed(lean_object* v_x_312_){
_start:
{
uint8_t v_res_313_; lean_object* v_r_314_; 
v_res_313_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_isReady(v_x_312_);
lean_dec_ref(v_x_312_);
v_r_314_ = lean_box(v_res_313_);
return v_r_314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_skip(lean_object* v_x_315_){
_start:
{
if (lean_obj_tag(v_x_315_) == 1)
{
lean_object* v_subgoals_316_; lean_object* v_idx_317_; lean_object* v_remaining_318_; lean_object* v___x_320_; uint8_t v_isShared_321_; uint8_t v_isSharedCheck_327_; 
v_subgoals_316_ = lean_ctor_get(v_x_315_, 0);
v_idx_317_ = lean_ctor_get(v_x_315_, 1);
v_remaining_318_ = lean_ctor_get(v_x_315_, 2);
v_isSharedCheck_327_ = !lean_is_exclusive(v_x_315_);
if (v_isSharedCheck_327_ == 0)
{
v___x_320_ = v_x_315_;
v_isShared_321_ = v_isSharedCheck_327_;
goto v_resetjp_319_;
}
else
{
lean_inc(v_remaining_318_);
lean_inc(v_idx_317_);
lean_inc(v_subgoals_316_);
lean_dec(v_x_315_);
v___x_320_ = lean_box(0);
v_isShared_321_ = v_isSharedCheck_327_;
goto v_resetjp_319_;
}
v_resetjp_319_:
{
lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_325_; 
v___x_322_ = lean_unsigned_to_nat(1u);
v___x_323_ = lean_nat_add(v_idx_317_, v___x_322_);
lean_dec(v_idx_317_);
if (v_isShared_321_ == 0)
{
lean_ctor_set(v___x_320_, 1, v___x_323_);
v___x_325_ = v___x_320_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v_subgoals_316_);
lean_ctor_set(v_reuseFailAlloc_326_, 1, v___x_323_);
lean_ctor_set(v_reuseFailAlloc_326_, 2, v_remaining_318_);
v___x_325_ = v_reuseFailAlloc_326_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
return v___x_325_;
}
}
}
else
{
return v_x_315_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_accept(lean_object* v_mvarId_328_, lean_object* v_x_329_){
_start:
{
if (lean_obj_tag(v_x_329_) == 0)
{
lean_object* v_subgoals_330_; lean_object* v___x_332_; uint8_t v_isShared_333_; uint8_t v_isSharedCheck_338_; 
v_subgoals_330_ = lean_ctor_get(v_x_329_, 0);
v_isSharedCheck_338_ = !lean_is_exclusive(v_x_329_);
if (v_isSharedCheck_338_ == 0)
{
v___x_332_ = v_x_329_;
v_isShared_333_ = v_isSharedCheck_338_;
goto v_resetjp_331_;
}
else
{
lean_inc(v_subgoals_330_);
lean_dec(v_x_329_);
v___x_332_ = lean_box(0);
v_isShared_333_ = v_isSharedCheck_338_;
goto v_resetjp_331_;
}
v_resetjp_331_:
{
lean_object* v___x_334_; lean_object* v___x_336_; 
v___x_334_ = lean_array_push(v_subgoals_330_, v_mvarId_328_);
if (v_isShared_333_ == 0)
{
lean_ctor_set(v___x_332_, 0, v___x_334_);
v___x_336_ = v___x_332_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_337_; 
v_reuseFailAlloc_337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_337_, 0, v___x_334_);
v___x_336_ = v_reuseFailAlloc_337_;
goto v_reusejp_335_;
}
v_reusejp_335_:
{
return v___x_336_;
}
}
}
else
{
lean_object* v_remaining_339_; 
v_remaining_339_ = lean_ctor_get(v_x_329_, 2);
if (lean_obj_tag(v_remaining_339_) == 1)
{
lean_object* v_head_340_; lean_object* v_subgoals_341_; lean_object* v_idx_342_; lean_object* v___x_344_; uint8_t v_isShared_345_; uint8_t v_isSharedCheck_362_; 
lean_inc_ref(v_remaining_339_);
v_head_340_ = lean_ctor_get(v_remaining_339_, 0);
lean_inc(v_head_340_);
v_subgoals_341_ = lean_ctor_get(v_x_329_, 0);
v_idx_342_ = lean_ctor_get(v_x_329_, 1);
v_isSharedCheck_362_ = !lean_is_exclusive(v_x_329_);
if (v_isSharedCheck_362_ == 0)
{
lean_object* v_unused_363_; 
v_unused_363_ = lean_ctor_get(v_x_329_, 2);
lean_dec(v_unused_363_);
v___x_344_ = v_x_329_;
v_isShared_345_ = v_isSharedCheck_362_;
goto v_resetjp_343_;
}
else
{
lean_inc(v_idx_342_);
lean_inc(v_subgoals_341_);
lean_dec(v_x_329_);
v___x_344_ = lean_box(0);
v_isShared_345_ = v_isSharedCheck_362_;
goto v_resetjp_343_;
}
v_resetjp_343_:
{
lean_object* v_tail_346_; lean_object* v_snd_347_; lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_360_; 
v_tail_346_ = lean_ctor_get(v_remaining_339_, 1);
lean_inc(v_tail_346_);
lean_dec_ref_known(v_remaining_339_, 2);
v_snd_347_ = lean_ctor_get(v_head_340_, 1);
v_isSharedCheck_360_ = !lean_is_exclusive(v_head_340_);
if (v_isSharedCheck_360_ == 0)
{
lean_object* v_unused_361_; 
v_unused_361_ = lean_ctor_get(v_head_340_, 0);
lean_dec(v_unused_361_);
v___x_349_ = v_head_340_;
v_isShared_350_ = v_isSharedCheck_360_;
goto v_resetjp_348_;
}
else
{
lean_inc(v_snd_347_);
lean_dec(v_head_340_);
v___x_349_ = lean_box(0);
v_isShared_350_ = v_isSharedCheck_360_;
goto v_resetjp_348_;
}
v_resetjp_348_:
{
lean_object* v___x_352_; 
if (v_isShared_350_ == 0)
{
lean_ctor_set(v___x_349_, 1, v_mvarId_328_);
lean_ctor_set(v___x_349_, 0, v_snd_347_);
v___x_352_ = v___x_349_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_359_; 
v_reuseFailAlloc_359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_359_, 0, v_snd_347_);
lean_ctor_set(v_reuseFailAlloc_359_, 1, v_mvarId_328_);
v___x_352_ = v_reuseFailAlloc_359_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_357_; 
v___x_353_ = lean_array_push(v_subgoals_341_, v___x_352_);
v___x_354_ = lean_unsigned_to_nat(1u);
v___x_355_ = lean_nat_add(v_idx_342_, v___x_354_);
lean_dec(v_idx_342_);
if (v_isShared_345_ == 0)
{
lean_ctor_set(v___x_344_, 2, v_tail_346_);
lean_ctor_set(v___x_344_, 1, v___x_355_);
lean_ctor_set(v___x_344_, 0, v___x_353_);
v___x_357_ = v___x_344_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_358_; 
v_reuseFailAlloc_358_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_358_, 0, v___x_353_);
lean_ctor_set(v_reuseFailAlloc_358_, 1, v___x_355_);
lean_ctor_set(v_reuseFailAlloc_358_, 2, v_tail_346_);
v___x_357_ = v_reuseFailAlloc_358_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
return v___x_357_;
}
}
}
}
}
else
{
lean_dec(v_mvarId_328_);
return v_x_329_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre_spec__0___redArg(lean_object* v_as_364_, size_t v_sz_365_, size_t v_i_366_, lean_object* v_b_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_){
_start:
{
uint8_t v___x_373_; 
v___x_373_ = lean_usize_dec_lt(v_i_366_, v_sz_365_);
if (v___x_373_ == 0)
{
lean_object* v___x_374_; 
v___x_374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_374_, 0, v_b_367_);
return v___x_374_;
}
else
{
lean_object* v_a_375_; lean_object* v___x_376_; 
v_a_375_ = lean_array_uget_borrowed(v_as_364_, v_i_366_);
lean_inc(v_a_375_);
v___x_376_ = l_Lean_Meta_mkCongrFun(v_b_367_, v_a_375_, v___y_368_, v___y_369_, v___y_370_, v___y_371_);
if (lean_obj_tag(v___x_376_) == 0)
{
lean_object* v_a_377_; size_t v___x_378_; size_t v___x_379_; 
v_a_377_ = lean_ctor_get(v___x_376_, 0);
lean_inc(v_a_377_);
lean_dec_ref_known(v___x_376_, 1);
v___x_378_ = ((size_t)1ULL);
v___x_379_ = lean_usize_add(v_i_366_, v___x_378_);
v_i_366_ = v___x_379_;
v_b_367_ = v_a_377_;
goto _start;
}
else
{
return v___x_376_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre_spec__0___redArg___boxed(lean_object* v_as_381_, lean_object* v_sz_382_, lean_object* v_i_383_, lean_object* v_b_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_){
_start:
{
size_t v_sz_boxed_390_; size_t v_i_boxed_391_; lean_object* v_res_392_; 
v_sz_boxed_390_ = lean_unbox_usize(v_sz_382_);
lean_dec(v_sz_382_);
v_i_boxed_391_ = lean_unbox_usize(v_i_383_);
lean_dec(v_i_383_);
v_res_392_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre_spec__0___redArg(v_as_381_, v_sz_boxed_390_, v_i_boxed_391_, v_b_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_);
lean_dec(v___y_388_);
lean_dec_ref(v___y_387_);
lean_dec(v___y_386_);
lean_dec_ref(v___y_385_);
lean_dec_ref(v_as_381_);
return v_res_392_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre(lean_object* v_pattern_395_, lean_object* v_state_396_, lean_object* v_e_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_){
_start:
{
lean_object* v___x_406_; uint8_t v___x_407_; uint8_t v___x_408_; 
v___x_406_ = lean_st_ref_get(v_state_396_);
v___x_407_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_isDone(v___x_406_);
lean_dec(v___x_406_);
v___x_408_ = 1;
if (v___x_407_ == 0)
{
lean_object* v___x_409_; 
v___x_409_ = l_Lean_Elab_Tactic_Conv_matchPattern_x3f(v_pattern_395_, v_e_397_, v_a_401_, v_a_402_, v_a_403_, v_a_404_);
if (lean_obj_tag(v___x_409_) == 0)
{
lean_object* v_a_410_; lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_476_; 
v_a_410_ = lean_ctor_get(v___x_409_, 0);
v_isSharedCheck_476_ = !lean_is_exclusive(v___x_409_);
if (v_isSharedCheck_476_ == 0)
{
v___x_412_ = v___x_409_;
v_isShared_413_ = v_isSharedCheck_476_;
goto v_resetjp_411_;
}
else
{
lean_inc(v_a_410_);
lean_dec(v___x_409_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_476_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
if (lean_obj_tag(v_a_410_) == 1)
{
lean_object* v_val_414_; lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_471_; 
v_val_414_ = lean_ctor_get(v_a_410_, 0);
v_isSharedCheck_471_ = !lean_is_exclusive(v_a_410_);
if (v_isSharedCheck_471_ == 0)
{
v___x_416_ = v_a_410_;
v_isShared_417_ = v_isSharedCheck_471_;
goto v_resetjp_415_;
}
else
{
lean_inc(v_val_414_);
lean_dec(v_a_410_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_471_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
lean_object* v_fst_418_; lean_object* v_snd_419_; lean_object* v___x_420_; uint8_t v___x_421_; 
v_fst_418_ = lean_ctor_get(v_val_414_, 0);
lean_inc(v_fst_418_);
v_snd_419_ = lean_ctor_get(v_val_414_, 1);
lean_inc(v_snd_419_);
lean_dec(v_val_414_);
v___x_420_ = lean_st_ref_get(v_state_396_);
v___x_421_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_isReady(v___x_420_);
lean_dec(v___x_420_);
if (v___x_421_ == 0)
{
lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_427_; 
lean_dec(v_snd_419_);
lean_dec(v_fst_418_);
lean_del_object(v___x_416_);
v___x_422_ = lean_st_ref_take(v_state_396_);
v___x_423_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_skip(v___x_422_);
v___x_424_ = lean_st_ref_put(v_state_396_, v___x_423_);
v___x_425_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre___closed__0));
if (v_isShared_413_ == 0)
{
lean_ctor_set(v___x_412_, 0, v___x_425_);
v___x_427_ = v___x_412_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v___x_425_);
v___x_427_ = v_reuseFailAlloc_428_;
goto v_reusejp_426_;
}
v_reusejp_426_:
{
return v___x_427_;
}
}
else
{
lean_object* v___x_429_; lean_object* v___x_430_; 
lean_del_object(v___x_412_);
v___x_429_ = lean_box(0);
v___x_430_ = l_Lean_Elab_Tactic_Conv_mkConvGoalFor(v_fst_418_, v___x_429_, v_a_401_, v_a_402_, v_a_403_, v_a_404_);
if (lean_obj_tag(v___x_430_) == 0)
{
lean_object* v_a_431_; lean_object* v_fst_432_; lean_object* v_snd_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; size_t v_sz_438_; size_t v___x_439_; lean_object* v___x_440_; 
v_a_431_ = lean_ctor_get(v___x_430_, 0);
lean_inc(v_a_431_);
lean_dec_ref_known(v___x_430_, 1);
v_fst_432_ = lean_ctor_get(v_a_431_, 0);
lean_inc(v_fst_432_);
v_snd_433_ = lean_ctor_get(v_a_431_, 1);
lean_inc(v_snd_433_);
lean_dec(v_a_431_);
v___x_434_ = lean_st_ref_take(v_state_396_);
v___x_435_ = l_Lean_Expr_mvarId_x21(v_snd_433_);
v___x_436_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_accept(v___x_435_, v___x_434_);
v___x_437_ = lean_st_ref_put(v_state_396_, v___x_436_);
v_sz_438_ = lean_array_size(v_snd_419_);
v___x_439_ = ((size_t)0ULL);
v___x_440_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre_spec__0___redArg(v_snd_419_, v_sz_438_, v___x_439_, v_snd_433_, v_a_401_, v_a_402_, v_a_403_, v_a_404_);
if (lean_obj_tag(v___x_440_) == 0)
{
lean_object* v_a_441_; lean_object* v___x_443_; uint8_t v_isShared_444_; uint8_t v_isSharedCheck_454_; 
v_a_441_ = lean_ctor_get(v___x_440_, 0);
v_isSharedCheck_454_ = !lean_is_exclusive(v___x_440_);
if (v_isSharedCheck_454_ == 0)
{
v___x_443_ = v___x_440_;
v_isShared_444_ = v_isSharedCheck_454_;
goto v_resetjp_442_;
}
else
{
lean_inc(v_a_441_);
lean_dec(v___x_440_);
v___x_443_ = lean_box(0);
v_isShared_444_ = v_isSharedCheck_454_;
goto v_resetjp_442_;
}
v_resetjp_442_:
{
lean_object* v___x_445_; lean_object* v___x_447_; 
v___x_445_ = l_Lean_mkAppN(v_fst_432_, v_snd_419_);
lean_dec(v_snd_419_);
if (v_isShared_417_ == 0)
{
lean_ctor_set(v___x_416_, 0, v_a_441_);
v___x_447_ = v___x_416_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v_a_441_);
v___x_447_ = v_reuseFailAlloc_453_;
goto v_reusejp_446_;
}
v_reusejp_446_:
{
lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_451_; 
v___x_448_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_448_, 0, v___x_445_);
lean_ctor_set(v___x_448_, 1, v___x_447_);
lean_ctor_set_uint8(v___x_448_, sizeof(void*)*2, v___x_408_);
v___x_449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_449_, 0, v___x_448_);
if (v_isShared_444_ == 0)
{
lean_ctor_set(v___x_443_, 0, v___x_449_);
v___x_451_ = v___x_443_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v___x_449_);
v___x_451_ = v_reuseFailAlloc_452_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
return v___x_451_;
}
}
}
}
else
{
lean_object* v_a_455_; lean_object* v___x_457_; uint8_t v_isShared_458_; uint8_t v_isSharedCheck_462_; 
lean_dec(v_fst_432_);
lean_dec(v_snd_419_);
lean_del_object(v___x_416_);
v_a_455_ = lean_ctor_get(v___x_440_, 0);
v_isSharedCheck_462_ = !lean_is_exclusive(v___x_440_);
if (v_isSharedCheck_462_ == 0)
{
v___x_457_ = v___x_440_;
v_isShared_458_ = v_isSharedCheck_462_;
goto v_resetjp_456_;
}
else
{
lean_inc(v_a_455_);
lean_dec(v___x_440_);
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
lean_object* v_a_463_; lean_object* v___x_465_; uint8_t v_isShared_466_; uint8_t v_isSharedCheck_470_; 
lean_dec(v_snd_419_);
lean_del_object(v___x_416_);
v_a_463_ = lean_ctor_get(v___x_430_, 0);
v_isSharedCheck_470_ = !lean_is_exclusive(v___x_430_);
if (v_isSharedCheck_470_ == 0)
{
v___x_465_ = v___x_430_;
v_isShared_466_ = v_isSharedCheck_470_;
goto v_resetjp_464_;
}
else
{
lean_inc(v_a_463_);
lean_dec(v___x_430_);
v___x_465_ = lean_box(0);
v_isShared_466_ = v_isSharedCheck_470_;
goto v_resetjp_464_;
}
v_resetjp_464_:
{
lean_object* v___x_468_; 
if (v_isShared_466_ == 0)
{
v___x_468_ = v___x_465_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v_a_463_);
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
}
}
else
{
lean_object* v___x_472_; lean_object* v___x_474_; 
lean_dec(v_a_410_);
v___x_472_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre___closed__0));
if (v_isShared_413_ == 0)
{
lean_ctor_set(v___x_412_, 0, v___x_472_);
v___x_474_ = v___x_412_;
goto v_reusejp_473_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v___x_472_);
v___x_474_ = v_reuseFailAlloc_475_;
goto v_reusejp_473_;
}
v_reusejp_473_:
{
return v___x_474_;
}
}
}
}
else
{
lean_object* v_a_477_; lean_object* v___x_479_; uint8_t v_isShared_480_; uint8_t v_isSharedCheck_484_; 
v_a_477_ = lean_ctor_get(v___x_409_, 0);
v_isSharedCheck_484_ = !lean_is_exclusive(v___x_409_);
if (v_isSharedCheck_484_ == 0)
{
v___x_479_ = v___x_409_;
v_isShared_480_ = v_isSharedCheck_484_;
goto v_resetjp_478_;
}
else
{
lean_inc(v_a_477_);
lean_dec(v___x_409_);
v___x_479_ = lean_box(0);
v_isShared_480_ = v_isSharedCheck_484_;
goto v_resetjp_478_;
}
v_resetjp_478_:
{
lean_object* v___x_482_; 
if (v_isShared_480_ == 0)
{
v___x_482_ = v___x_479_;
goto v_reusejp_481_;
}
else
{
lean_object* v_reuseFailAlloc_483_; 
v_reuseFailAlloc_483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_483_, 0, v_a_477_);
v___x_482_ = v_reuseFailAlloc_483_;
goto v_reusejp_481_;
}
v_reusejp_481_:
{
return v___x_482_;
}
}
}
}
else
{
lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
lean_dec_ref(v_pattern_395_);
v___x_485_ = lean_box(0);
v___x_486_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_486_, 0, v_e_397_);
lean_ctor_set(v___x_486_, 1, v___x_485_);
lean_ctor_set_uint8(v___x_486_, sizeof(void*)*2, v___x_408_);
v___x_487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_487_, 0, v___x_486_);
v___x_488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_488_, 0, v___x_487_);
return v___x_488_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre___boxed(lean_object* v_pattern_489_, lean_object* v_state_490_, lean_object* v_e_491_, lean_object* v_a_492_, lean_object* v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_, lean_object* v_a_497_, lean_object* v_a_498_, lean_object* v_a_499_){
_start:
{
lean_object* v_res_500_; 
v_res_500_ = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre(v_pattern_489_, v_state_490_, v_e_491_, v_a_492_, v_a_493_, v_a_494_, v_a_495_, v_a_496_, v_a_497_, v_a_498_);
lean_dec(v_a_498_);
lean_dec_ref(v_a_497_);
lean_dec(v_a_496_);
lean_dec_ref(v_a_495_);
lean_dec(v_a_494_);
lean_dec_ref(v_a_493_);
lean_dec(v_a_492_);
lean_dec(v_state_490_);
return v_res_500_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre_spec__0(lean_object* v_as_501_, size_t v_sz_502_, size_t v_i_503_, lean_object* v_b_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_){
_start:
{
lean_object* v___x_513_; 
v___x_513_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre_spec__0___redArg(v_as_501_, v_sz_502_, v_i_503_, v_b_504_, v___y_508_, v___y_509_, v___y_510_, v___y_511_);
return v___x_513_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre_spec__0___boxed(lean_object* v_as_514_, lean_object* v_sz_515_, lean_object* v_i_516_, lean_object* v_b_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_){
_start:
{
size_t v_sz_boxed_526_; size_t v_i_boxed_527_; lean_object* v_res_528_; 
v_sz_boxed_526_ = lean_unbox_usize(v_sz_515_);
lean_dec(v_sz_515_);
v_i_boxed_527_ = lean_unbox_usize(v_i_516_);
lean_dec(v_i_516_);
v_res_528_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre_spec__0(v_as_514_, v_sz_boxed_526_, v_i_boxed_527_, v_b_517_, v___y_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_);
lean_dec(v___y_524_);
lean_dec_ref(v___y_523_);
lean_dec(v___y_522_);
lean_dec_ref(v___y_521_);
lean_dec(v___y_520_);
lean_dec_ref(v___y_519_);
lean_dec(v___y_518_);
lean_dec_ref(v_as_514_);
return v_res_528_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_529_ = lean_box(0);
v___x_530_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_531_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_531_, 0, v___x_530_);
lean_ctor_set(v___x_531_, 1, v___x_529_);
return v___x_531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1___redArg(){
_start:
{
lean_object* v___x_533_; lean_object* v___x_534_; 
v___x_533_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1___redArg___closed__0);
v___x_534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_534_, 0, v___x_533_);
return v___x_534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1___redArg___boxed(lean_object* v___y_535_){
_start:
{
lean_object* v_res_536_; 
v_res_536_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1___redArg();
return v_res_536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1(lean_object* v_00_u03b1_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_){
_start:
{
lean_object* v___x_547_; 
v___x_547_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1___redArg();
return v___x_547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1___boxed(lean_object* v_00_u03b1_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_){
_start:
{
lean_object* v_res_558_; 
v_res_558_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1(v_00_u03b1_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_);
lean_dec(v___y_556_);
lean_dec_ref(v___y_555_);
lean_dec(v___y_554_);
lean_dec_ref(v___y_553_);
lean_dec(v___y_552_);
lean_dec_ref(v___y_551_);
lean_dec(v___y_550_);
lean_dec_ref(v___y_549_);
return v_res_558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__2___redArg(lean_object* v_a_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_){
_start:
{
lean_object* v___x_567_; 
v___x_567_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v_a_559_, v___y_560_, v___y_561_, v___y_562_, v___y_563_, v___y_564_, v___y_565_);
return v___x_567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__2___redArg___boxed(lean_object* v_a_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_){
_start:
{
lean_object* v_res_576_; 
v_res_576_ = l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__2___redArg(v_a_568_, v___y_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_, v___y_574_);
lean_dec(v___y_574_);
lean_dec_ref(v___y_573_);
lean_dec(v___y_572_);
lean_dec_ref(v___y_571_);
lean_dec(v___y_570_);
lean_dec_ref(v___y_569_);
return v_res_576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__2(lean_object* v_00_u03b1_577_, lean_object* v_a_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_){
_start:
{
lean_object* v___x_586_; 
v___x_586_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v_a_578_, v___y_579_, v___y_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_);
return v___x_586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__2___boxed(lean_object* v_00_u03b1_587_, lean_object* v_a_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_){
_start:
{
lean_object* v_res_596_; 
v_res_596_ = l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__2(v_00_u03b1_587_, v_a_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_, v___y_594_);
lean_dec(v___y_594_);
lean_dec_ref(v___y_593_);
lean_dec(v___y_592_);
lean_dec_ref(v___y_591_);
lean_dec(v___y_590_);
lean_dec_ref(v___y_589_);
return v_res_596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__0(lean_object* v_e_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_){
_start:
{
lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_606_, 0, v_e_597_);
v___x_607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_607_, 0, v___x_606_);
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__0___boxed(lean_object* v_e_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_){
_start:
{
lean_object* v_res_617_; 
v_res_617_ = l_Lean_Elab_Tactic_Conv_evalPattern___lam__0(v_e_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_);
lean_dec(v___y_615_);
lean_dec_ref(v___y_614_);
lean_dec(v___y_613_);
lean_dec_ref(v___y_612_);
lean_dec(v___y_611_);
lean_dec_ref(v___y_610_);
lean_dec(v___y_609_);
return v_res_617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__1(lean_object* v___x_618_, lean_object* v___x_619_, uint8_t v___x_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_){
_start:
{
lean_object* v___x_628_; 
v___x_628_ = l_Lean_Elab_Term_elabTerm(v___x_618_, v___x_619_, v___x_620_, v___x_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_);
if (lean_obj_tag(v___x_628_) == 0)
{
lean_object* v_a_629_; lean_object* v___x_630_; 
v_a_629_ = lean_ctor_get(v___x_628_, 0);
lean_inc(v_a_629_);
lean_dec_ref_known(v___x_628_, 1);
v___x_630_ = l_Lean_Meta_abstractMVars(v_a_629_, v___x_620_, v___y_623_, v___y_624_, v___y_625_, v___y_626_);
return v___x_630_;
}
else
{
lean_object* v_a_631_; lean_object* v___x_633_; uint8_t v_isShared_634_; uint8_t v_isSharedCheck_638_; 
v_a_631_ = lean_ctor_get(v___x_628_, 0);
v_isSharedCheck_638_ = !lean_is_exclusive(v___x_628_);
if (v_isSharedCheck_638_ == 0)
{
v___x_633_ = v___x_628_;
v_isShared_634_ = v_isSharedCheck_638_;
goto v_resetjp_632_;
}
else
{
lean_inc(v_a_631_);
lean_dec(v___x_628_);
v___x_633_ = lean_box(0);
v_isShared_634_ = v_isSharedCheck_638_;
goto v_resetjp_632_;
}
v_resetjp_632_:
{
lean_object* v___x_636_; 
if (v_isShared_634_ == 0)
{
v___x_636_ = v___x_633_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v_a_631_);
v___x_636_ = v_reuseFailAlloc_637_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
return v___x_636_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__1___boxed(lean_object* v___x_639_, lean_object* v___x_640_, lean_object* v___x_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_){
_start:
{
uint8_t v___x_15280__boxed_649_; lean_object* v_res_650_; 
v___x_15280__boxed_649_ = lean_unbox(v___x_641_);
v_res_650_ = l_Lean_Elab_Tactic_Conv_evalPattern___lam__1(v___x_639_, v___x_640_, v___x_15280__boxed_649_, v___y_642_, v___y_643_, v___y_644_, v___y_645_, v___y_646_, v___y_647_);
lean_dec(v___y_647_);
lean_dec_ref(v___y_646_);
lean_dec(v___y_645_);
lean_dec_ref(v___y_644_);
lean_dec(v___y_643_);
lean_dec_ref(v___y_642_);
return v_res_650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__2(lean_object* v___x_651_, lean_object* v___f_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_){
_start:
{
lean_object* v_toCold_660_; lean_object* v_currRecDepth_661_; lean_object* v_ref_662_; uint8_t v_diag_663_; uint8_t v_suppressElabErrors_664_; lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_673_; 
v_toCold_660_ = lean_ctor_get(v___y_657_, 0);
v_currRecDepth_661_ = lean_ctor_get(v___y_657_, 1);
v_ref_662_ = lean_ctor_get(v___y_657_, 2);
v_diag_663_ = lean_ctor_get_uint8(v___y_657_, sizeof(void*)*3);
v_suppressElabErrors_664_ = lean_ctor_get_uint8(v___y_657_, sizeof(void*)*3 + 1);
v_isSharedCheck_673_ = !lean_is_exclusive(v___y_657_);
if (v_isSharedCheck_673_ == 0)
{
v___x_666_ = v___y_657_;
v_isShared_667_ = v_isSharedCheck_673_;
goto v_resetjp_665_;
}
else
{
lean_inc(v_ref_662_);
lean_inc(v_currRecDepth_661_);
lean_inc(v_toCold_660_);
lean_dec(v___y_657_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_673_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
lean_object* v_ref_668_; lean_object* v___x_670_; 
v_ref_668_ = l_Lean_replaceRef(v___x_651_, v_ref_662_);
lean_dec(v_ref_662_);
if (v_isShared_667_ == 0)
{
lean_ctor_set(v___x_666_, 2, v_ref_668_);
v___x_670_ = v___x_666_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v_toCold_660_);
lean_ctor_set(v_reuseFailAlloc_672_, 1, v_currRecDepth_661_);
lean_ctor_set(v_reuseFailAlloc_672_, 2, v_ref_668_);
lean_ctor_set_uint8(v_reuseFailAlloc_672_, sizeof(void*)*3, v_diag_663_);
lean_ctor_set_uint8(v_reuseFailAlloc_672_, sizeof(void*)*3 + 1, v_suppressElabErrors_664_);
v___x_670_ = v_reuseFailAlloc_672_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
lean_object* v___x_671_; 
v___x_671_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v___f_652_, v___y_653_, v___y_654_, v___y_655_, v___y_656_, v___x_670_, v___y_658_);
lean_dec_ref(v___x_670_);
return v___x_671_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__2___boxed(lean_object* v___x_674_, lean_object* v___f_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_){
_start:
{
lean_object* v_res_683_; 
v_res_683_ = l_Lean_Elab_Tactic_Conv_evalPattern___lam__2(v___x_674_, v___f_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_);
lean_dec(v___y_681_);
lean_dec(v___y_679_);
lean_dec_ref(v___y_678_);
lean_dec(v___y_677_);
lean_dec_ref(v___y_676_);
lean_dec(v___x_674_);
return v_res_683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__3(lean_object* v___x_684_, uint8_t v___x_685_, lean_object* v_e_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_){
_start:
{
lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_695_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_695_, 0, v_e_686_);
lean_ctor_set(v___x_695_, 1, v___x_684_);
lean_ctor_set_uint8(v___x_695_, sizeof(void*)*2, v___x_685_);
v___x_696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_696_, 0, v___x_695_);
v___x_697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_697_, 0, v___x_696_);
return v___x_697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__3___boxed(lean_object* v___x_698_, lean_object* v___x_699_, lean_object* v_e_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_){
_start:
{
uint8_t v___x_15374__boxed_709_; lean_object* v_res_710_; 
v___x_15374__boxed_709_ = lean_unbox(v___x_699_);
v_res_710_ = l_Lean_Elab_Tactic_Conv_evalPattern___lam__3(v___x_698_, v___x_15374__boxed_709_, v_e_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_);
lean_dec(v___y_707_);
lean_dec_ref(v___y_706_);
lean_dec(v___y_705_);
lean_dec_ref(v___y_704_);
lean_dec(v___y_703_);
lean_dec_ref(v___y_702_);
lean_dec(v___y_701_);
return v_res_710_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__4(lean_object* v___x_711_, lean_object* v_x_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_){
_start:
{
lean_object* v___x_721_; lean_object* v___x_722_; 
v___x_721_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_721_, 0, v___x_711_);
v___x_722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_722_, 0, v___x_721_);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__4___boxed(lean_object* v___x_723_, lean_object* v_x_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_){
_start:
{
lean_object* v_res_733_; 
v_res_733_ = l_Lean_Elab_Tactic_Conv_evalPattern___lam__4(v___x_723_, v_x_724_, v___y_725_, v___y_726_, v___y_727_, v___y_728_, v___y_729_, v___y_730_, v___y_731_);
lean_dec(v___y_731_);
lean_dec_ref(v___y_730_);
lean_dec(v___y_729_);
lean_dec_ref(v___y_728_);
lean_dec(v___y_727_);
lean_dec_ref(v___y_726_);
lean_dec(v___y_725_);
lean_dec_ref(v_x_724_);
return v_res_733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__5(lean_object* v___x_734_, lean_object* v_x_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_){
_start:
{
lean_object* v___x_744_; 
v___x_744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_744_, 0, v___x_734_);
return v___x_744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__5___boxed(lean_object* v___x_745_, lean_object* v_x_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_){
_start:
{
lean_object* v_res_755_; 
v_res_755_ = l_Lean_Elab_Tactic_Conv_evalPattern___lam__5(v___x_745_, v_x_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_);
lean_dec(v___y_753_);
lean_dec_ref(v___y_752_);
lean_dec(v___y_751_);
lean_dec_ref(v___y_750_);
lean_dec(v___y_749_);
lean_dec_ref(v___y_748_);
lean_dec(v___y_747_);
lean_dec_ref(v_x_746_);
return v_res_755_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__5(size_t v_sz_756_, size_t v_i_757_, lean_object* v_bs_758_){
_start:
{
uint8_t v___x_759_; 
v___x_759_ = lean_usize_dec_lt(v_i_757_, v_sz_756_);
if (v___x_759_ == 0)
{
return v_bs_758_;
}
else
{
lean_object* v_v_760_; lean_object* v_snd_761_; lean_object* v___x_762_; lean_object* v_bs_x27_763_; size_t v___x_764_; size_t v___x_765_; lean_object* v___x_766_; 
v_v_760_ = lean_array_uget_borrowed(v_bs_758_, v_i_757_);
v_snd_761_ = lean_ctor_get(v_v_760_, 1);
lean_inc(v_snd_761_);
v___x_762_ = lean_unsigned_to_nat(0u);
v_bs_x27_763_ = lean_array_uset(v_bs_758_, v_i_757_, v___x_762_);
v___x_764_ = ((size_t)1ULL);
v___x_765_ = lean_usize_add(v_i_757_, v___x_764_);
v___x_766_ = lean_array_uset(v_bs_x27_763_, v_i_757_, v_snd_761_);
v_i_757_ = v___x_765_;
v_bs_758_ = v___x_766_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__5___boxed(lean_object* v_sz_768_, lean_object* v_i_769_, lean_object* v_bs_770_){
_start:
{
size_t v_sz_boxed_771_; size_t v_i_boxed_772_; lean_object* v_res_773_; 
v_sz_boxed_771_ = lean_unbox_usize(v_sz_768_);
lean_dec(v_sz_768_);
v_i_boxed_772_ = lean_unbox_usize(v_i_769_);
lean_dec(v_i_769_);
v_res_773_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__5(v_sz_boxed_771_, v_i_boxed_772_, v_bs_770_);
return v_res_773_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4_spec__5(lean_object* v_msgData_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_){
_start:
{
lean_object* v___x_780_; lean_object* v_env_781_; lean_object* v___x_782_; lean_object* v_toCold_783_; lean_object* v_mctx_784_; lean_object* v_lctx_785_; lean_object* v_options_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; 
v___x_780_ = lean_st_ref_get(v___y_778_);
v_env_781_ = lean_ctor_get(v___x_780_, 0);
lean_inc_ref(v_env_781_);
lean_dec(v___x_780_);
v___x_782_ = lean_st_ref_get(v___y_776_);
v_toCold_783_ = lean_ctor_get(v___y_777_, 0);
v_mctx_784_ = lean_ctor_get(v___x_782_, 0);
lean_inc_ref(v_mctx_784_);
lean_dec(v___x_782_);
v_lctx_785_ = lean_ctor_get(v___y_775_, 2);
v_options_786_ = lean_ctor_get(v_toCold_783_, 2);
lean_inc_ref(v_options_786_);
lean_inc_ref(v_lctx_785_);
v___x_787_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_787_, 0, v_env_781_);
lean_ctor_set(v___x_787_, 1, v_mctx_784_);
lean_ctor_set(v___x_787_, 2, v_lctx_785_);
lean_ctor_set(v___x_787_, 3, v_options_786_);
v___x_788_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_788_, 0, v___x_787_);
lean_ctor_set(v___x_788_, 1, v_msgData_774_);
v___x_789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_789_, 0, v___x_788_);
return v___x_789_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4_spec__5___boxed(lean_object* v_msgData_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_){
_start:
{
lean_object* v_res_796_; 
v_res_796_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4_spec__5(v_msgData_790_, v___y_791_, v___y_792_, v___y_793_, v___y_794_);
lean_dec(v___y_794_);
lean_dec_ref(v___y_793_);
lean_dec(v___y_792_);
lean_dec_ref(v___y_791_);
return v_res_796_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg(lean_object* v_msg_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_){
_start:
{
lean_object* v_ref_803_; lean_object* v___x_804_; lean_object* v_a_805_; lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_813_; 
v_ref_803_ = lean_ctor_get(v___y_800_, 2);
v___x_804_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4_spec__5(v_msg_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_);
v_a_805_ = lean_ctor_get(v___x_804_, 0);
v_isSharedCheck_813_ = !lean_is_exclusive(v___x_804_);
if (v_isSharedCheck_813_ == 0)
{
v___x_807_ = v___x_804_;
v_isShared_808_ = v_isSharedCheck_813_;
goto v_resetjp_806_;
}
else
{
lean_inc(v_a_805_);
lean_dec(v___x_804_);
v___x_807_ = lean_box(0);
v_isShared_808_ = v_isSharedCheck_813_;
goto v_resetjp_806_;
}
v_resetjp_806_:
{
lean_object* v___x_809_; lean_object* v___x_811_; 
lean_inc(v_ref_803_);
v___x_809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_809_, 0, v_ref_803_);
lean_ctor_set(v___x_809_, 1, v_a_805_);
if (v_isShared_808_ == 0)
{
lean_ctor_set_tag(v___x_807_, 1);
lean_ctor_set(v___x_807_, 0, v___x_809_);
v___x_811_ = v___x_807_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v___x_809_);
v___x_811_ = v_reuseFailAlloc_812_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
return v___x_811_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg___boxed(lean_object* v_msg_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_){
_start:
{
lean_object* v_res_820_; 
v_res_820_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg(v_msg_814_, v___y_815_, v___y_816_, v___y_817_, v___y_818_);
lean_dec(v___y_818_);
lean_dec_ref(v___y_817_);
lean_dec(v___y_816_);
lean_dec_ref(v___y_815_);
return v_res_820_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg(lean_object* v_ref_821_, lean_object* v_msg_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_){
_start:
{
lean_object* v_toCold_832_; lean_object* v_currRecDepth_833_; lean_object* v_ref_834_; uint8_t v_diag_835_; uint8_t v_suppressElabErrors_836_; lean_object* v_ref_837_; lean_object* v___x_838_; lean_object* v___x_839_; 
v_toCold_832_ = lean_ctor_get(v___y_829_, 0);
v_currRecDepth_833_ = lean_ctor_get(v___y_829_, 1);
v_ref_834_ = lean_ctor_get(v___y_829_, 2);
v_diag_835_ = lean_ctor_get_uint8(v___y_829_, sizeof(void*)*3);
v_suppressElabErrors_836_ = lean_ctor_get_uint8(v___y_829_, sizeof(void*)*3 + 1);
v_ref_837_ = l_Lean_replaceRef(v_ref_821_, v_ref_834_);
lean_inc(v_currRecDepth_833_);
lean_inc_ref(v_toCold_832_);
v___x_838_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_838_, 0, v_toCold_832_);
lean_ctor_set(v___x_838_, 1, v_currRecDepth_833_);
lean_ctor_set(v___x_838_, 2, v_ref_837_);
lean_ctor_set_uint8(v___x_838_, sizeof(void*)*3, v_diag_835_);
lean_ctor_set_uint8(v___x_838_, sizeof(void*)*3 + 1, v_suppressElabErrors_836_);
v___x_839_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg(v_msg_822_, v___y_827_, v___y_828_, v___x_838_, v___y_830_);
lean_dec_ref_known(v___x_838_, 3);
return v___x_839_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg___boxed(lean_object* v_ref_840_, lean_object* v_msg_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_){
_start:
{
lean_object* v_res_851_; 
v_res_851_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg(v_ref_840_, v_msg_841_, v___y_842_, v___y_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_);
lean_dec(v___y_849_);
lean_dec_ref(v___y_848_);
lean_dec(v___y_847_);
lean_dec_ref(v___y_846_);
lean_dec(v___y_845_);
lean_dec_ref(v___y_844_);
lean_dec(v___y_843_);
lean_dec_ref(v___y_842_);
lean_dec(v_ref_840_);
return v_res_851_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_853_; lean_object* v___x_854_; 
v___x_853_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg___closed__0));
v___x_854_ = l_Lean_stringToMessageData(v___x_853_);
return v___x_854_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg(size_t v_sz_855_, size_t v_i_856_, lean_object* v_bs_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_){
_start:
{
uint8_t v___x_867_; 
v___x_867_ = lean_usize_dec_lt(v_i_856_, v_sz_855_);
if (v___x_867_ == 0)
{
lean_object* v___x_868_; 
v___x_868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_868_, 0, v_bs_857_);
return v___x_868_;
}
else
{
lean_object* v_v_869_; lean_object* v___x_870_; lean_object* v_bs_x27_871_; lean_object* v_a_873_; lean_object* v___x_878_; uint8_t v_isZero_879_; 
v_v_869_ = lean_array_uget(v_bs_857_, v_i_856_);
v___x_870_ = lean_unsigned_to_nat(0u);
v_bs_x27_871_ = lean_array_uset(v_bs_857_, v_i_856_, v___x_870_);
v___x_878_ = l_Lean_TSyntax_getNat(v_v_869_);
v_isZero_879_ = lean_nat_dec_eq(v___x_878_, v___x_870_);
if (v_isZero_879_ == 1)
{
lean_object* v___x_880_; lean_object* v___x_881_; 
lean_dec(v___x_878_);
v___x_880_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg___closed__1);
v___x_881_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg(v_v_869_, v___x_880_, v___y_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_, v___y_865_);
lean_dec(v_v_869_);
if (lean_obj_tag(v___x_881_) == 0)
{
lean_object* v_a_882_; 
v_a_882_ = lean_ctor_get(v___x_881_, 0);
lean_inc(v_a_882_);
lean_dec_ref_known(v___x_881_, 1);
v_a_873_ = v_a_882_;
goto v___jp_872_;
}
else
{
lean_object* v_a_883_; lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_890_; 
lean_dec_ref(v_bs_x27_871_);
v_a_883_ = lean_ctor_get(v___x_881_, 0);
v_isSharedCheck_890_ = !lean_is_exclusive(v___x_881_);
if (v_isSharedCheck_890_ == 0)
{
v___x_885_ = v___x_881_;
v_isShared_886_ = v_isSharedCheck_890_;
goto v_resetjp_884_;
}
else
{
lean_inc(v_a_883_);
lean_dec(v___x_881_);
v___x_885_ = lean_box(0);
v_isShared_886_ = v_isSharedCheck_890_;
goto v_resetjp_884_;
}
v_resetjp_884_:
{
lean_object* v___x_888_; 
if (v_isShared_886_ == 0)
{
v___x_888_ = v___x_885_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v_a_883_);
v___x_888_ = v_reuseFailAlloc_889_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
return v___x_888_;
}
}
}
}
else
{
lean_object* v___x_891_; lean_object* v_one_892_; lean_object* v_n_893_; lean_object* v___x_894_; 
lean_dec(v_v_869_);
v___x_891_ = lean_usize_to_nat(v_i_856_);
v_one_892_ = lean_unsigned_to_nat(1u);
v_n_893_ = lean_nat_sub(v___x_878_, v_one_892_);
lean_dec(v___x_878_);
v___x_894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_894_, 0, v_n_893_);
lean_ctor_set(v___x_894_, 1, v___x_891_);
v_a_873_ = v___x_894_;
goto v___jp_872_;
}
v___jp_872_:
{
size_t v___x_874_; size_t v___x_875_; lean_object* v___x_876_; 
v___x_874_ = ((size_t)1ULL);
v___x_875_ = lean_usize_add(v_i_856_, v___x_874_);
v___x_876_ = lean_array_uset(v_bs_x27_871_, v_i_856_, v_a_873_);
v_i_856_ = v___x_875_;
v_bs_857_ = v___x_876_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg___boxed(lean_object* v_sz_895_, lean_object* v_i_896_, lean_object* v_bs_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_){
_start:
{
size_t v_sz_boxed_907_; size_t v_i_boxed_908_; lean_object* v_res_909_; 
v_sz_boxed_907_ = lean_unbox_usize(v_sz_895_);
lean_dec(v_sz_895_);
v_i_boxed_908_ = lean_unbox_usize(v_i_896_);
lean_dec(v_i_896_);
v_res_909_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg(v_sz_boxed_907_, v_i_boxed_908_, v_bs_897_, v___y_898_, v___y_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_);
lean_dec(v___y_905_);
lean_dec_ref(v___y_904_);
lean_dec(v___y_903_);
lean_dec_ref(v___y_902_);
lean_dec(v___y_901_);
lean_dec_ref(v___y_900_);
lean_dec(v___y_899_);
lean_dec_ref(v___y_898_);
return v_res_909_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6_spec__8___redArg(lean_object* v_hi_910_, lean_object* v_pivot_911_, lean_object* v_as_912_, lean_object* v_i_913_, lean_object* v_k_914_){
_start:
{
uint8_t v___x_915_; 
v___x_915_ = lean_nat_dec_lt(v_k_914_, v_hi_910_);
if (v___x_915_ == 0)
{
lean_object* v___x_916_; lean_object* v___x_917_; 
lean_dec(v_k_914_);
v___x_916_ = lean_array_fswap(v_as_912_, v_i_913_, v_hi_910_);
v___x_917_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_917_, 0, v_i_913_);
lean_ctor_set(v___x_917_, 1, v___x_916_);
return v___x_917_;
}
else
{
lean_object* v___x_918_; lean_object* v_fst_919_; lean_object* v_fst_920_; uint8_t v___x_921_; 
v___x_918_ = lean_array_fget_borrowed(v_as_912_, v_k_914_);
v_fst_919_ = lean_ctor_get(v___x_918_, 0);
v_fst_920_ = lean_ctor_get(v_pivot_911_, 0);
v___x_921_ = lean_nat_dec_lt(v_fst_919_, v_fst_920_);
if (v___x_921_ == 0)
{
lean_object* v___x_922_; lean_object* v___x_923_; 
v___x_922_ = lean_unsigned_to_nat(1u);
v___x_923_ = lean_nat_add(v_k_914_, v___x_922_);
lean_dec(v_k_914_);
v_k_914_ = v___x_923_;
goto _start;
}
else
{
lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; 
v___x_925_ = lean_array_fswap(v_as_912_, v_i_913_, v_k_914_);
v___x_926_ = lean_unsigned_to_nat(1u);
v___x_927_ = lean_nat_add(v_i_913_, v___x_926_);
lean_dec(v_i_913_);
v___x_928_ = lean_nat_add(v_k_914_, v___x_926_);
lean_dec(v_k_914_);
v_as_912_ = v___x_925_;
v_i_913_ = v___x_927_;
v_k_914_ = v___x_928_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6_spec__8___redArg___boxed(lean_object* v_hi_930_, lean_object* v_pivot_931_, lean_object* v_as_932_, lean_object* v_i_933_, lean_object* v_k_934_){
_start:
{
lean_object* v_res_935_; 
v_res_935_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6_spec__8___redArg(v_hi_930_, v_pivot_931_, v_as_932_, v_i_933_, v_k_934_);
lean_dec_ref(v_pivot_931_);
lean_dec(v_hi_930_);
return v_res_935_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg___lam__0(lean_object* v_x1_936_, lean_object* v_x2_937_){
_start:
{
lean_object* v_fst_938_; lean_object* v_fst_939_; uint8_t v___x_940_; 
v_fst_938_ = lean_ctor_get(v_x1_936_, 0);
v_fst_939_ = lean_ctor_get(v_x2_937_, 0);
v___x_940_ = lean_nat_dec_lt(v_fst_938_, v_fst_939_);
return v___x_940_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg___lam__0___boxed(lean_object* v_x1_941_, lean_object* v_x2_942_){
_start:
{
uint8_t v_res_943_; lean_object* v_r_944_; 
v_res_943_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg___lam__0(v_x1_941_, v_x2_942_);
lean_dec_ref(v_x2_942_);
lean_dec_ref(v_x1_941_);
v_r_944_ = lean_box(v_res_943_);
return v_r_944_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg(lean_object* v_n_945_, lean_object* v_as_946_, lean_object* v_lo_947_, lean_object* v_hi_948_){
_start:
{
lean_object* v___y_950_; uint8_t v___x_960_; 
v___x_960_ = lean_nat_dec_lt(v_lo_947_, v_hi_948_);
if (v___x_960_ == 0)
{
lean_dec(v_lo_947_);
return v_as_946_;
}
else
{
lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v_mid_963_; lean_object* v___y_965_; lean_object* v___y_971_; lean_object* v___x_976_; lean_object* v___x_977_; uint8_t v___x_978_; 
v___x_961_ = lean_nat_add(v_lo_947_, v_hi_948_);
v___x_962_ = lean_unsigned_to_nat(1u);
v_mid_963_ = lean_nat_shiftr(v___x_961_, v___x_962_);
lean_dec(v___x_961_);
v___x_976_ = lean_array_fget_borrowed(v_as_946_, v_mid_963_);
v___x_977_ = lean_array_fget_borrowed(v_as_946_, v_lo_947_);
v___x_978_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg___lam__0(v___x_976_, v___x_977_);
if (v___x_978_ == 0)
{
v___y_971_ = v_as_946_;
goto v___jp_970_;
}
else
{
lean_object* v___x_979_; 
v___x_979_ = lean_array_fswap(v_as_946_, v_lo_947_, v_mid_963_);
v___y_971_ = v___x_979_;
goto v___jp_970_;
}
v___jp_964_:
{
lean_object* v___x_966_; lean_object* v___x_967_; uint8_t v___x_968_; 
v___x_966_ = lean_array_fget_borrowed(v___y_965_, v_mid_963_);
v___x_967_ = lean_array_fget_borrowed(v___y_965_, v_hi_948_);
v___x_968_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg___lam__0(v___x_966_, v___x_967_);
if (v___x_968_ == 0)
{
lean_dec(v_mid_963_);
v___y_950_ = v___y_965_;
goto v___jp_949_;
}
else
{
lean_object* v___x_969_; 
v___x_969_ = lean_array_fswap(v___y_965_, v_mid_963_, v_hi_948_);
lean_dec(v_mid_963_);
v___y_950_ = v___x_969_;
goto v___jp_949_;
}
}
v___jp_970_:
{
lean_object* v___x_972_; lean_object* v___x_973_; uint8_t v___x_974_; 
v___x_972_ = lean_array_fget_borrowed(v___y_971_, v_hi_948_);
v___x_973_ = lean_array_fget_borrowed(v___y_971_, v_lo_947_);
v___x_974_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg___lam__0(v___x_972_, v___x_973_);
if (v___x_974_ == 0)
{
v___y_965_ = v___y_971_;
goto v___jp_964_;
}
else
{
lean_object* v___x_975_; 
v___x_975_ = lean_array_fswap(v___y_971_, v_lo_947_, v_hi_948_);
v___y_965_ = v___x_975_;
goto v___jp_964_;
}
}
}
v___jp_949_:
{
lean_object* v_pivot_951_; lean_object* v___x_952_; lean_object* v_fst_953_; lean_object* v_snd_954_; uint8_t v___x_955_; 
v_pivot_951_ = lean_array_fget(v___y_950_, v_hi_948_);
lean_inc_n(v_lo_947_, 2);
v___x_952_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6_spec__8___redArg(v_hi_948_, v_pivot_951_, v___y_950_, v_lo_947_, v_lo_947_);
lean_dec(v_pivot_951_);
v_fst_953_ = lean_ctor_get(v___x_952_, 0);
lean_inc(v_fst_953_);
v_snd_954_ = lean_ctor_get(v___x_952_, 1);
lean_inc(v_snd_954_);
lean_dec_ref(v___x_952_);
v___x_955_ = lean_nat_dec_le(v_hi_948_, v_fst_953_);
if (v___x_955_ == 0)
{
lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; 
v___x_956_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg(v_n_945_, v_snd_954_, v_lo_947_, v_fst_953_);
v___x_957_ = lean_unsigned_to_nat(1u);
v___x_958_ = lean_nat_add(v_fst_953_, v___x_957_);
lean_dec(v_fst_953_);
v_as_946_ = v___x_956_;
v_lo_947_ = v___x_958_;
goto _start;
}
else
{
lean_dec(v_fst_953_);
lean_dec(v_lo_947_);
return v_snd_954_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg___boxed(lean_object* v_n_980_, lean_object* v_as_981_, lean_object* v_lo_982_, lean_object* v_hi_983_){
_start:
{
lean_object* v_res_984_; 
v_res_984_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg(v_n_980_, v_as_981_, v_lo_982_, v_hi_983_);
lean_dec(v_hi_983_);
lean_dec(v_n_980_);
return v_res_984_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__12_spec__16___redArg(lean_object* v_x_985_, lean_object* v_x_986_, lean_object* v_x_987_, lean_object* v_x_988_){
_start:
{
lean_object* v_ks_989_; lean_object* v_vs_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_1014_; 
v_ks_989_ = lean_ctor_get(v_x_985_, 0);
v_vs_990_ = lean_ctor_get(v_x_985_, 1);
v_isSharedCheck_1014_ = !lean_is_exclusive(v_x_985_);
if (v_isSharedCheck_1014_ == 0)
{
v___x_992_ = v_x_985_;
v_isShared_993_ = v_isSharedCheck_1014_;
goto v_resetjp_991_;
}
else
{
lean_inc(v_vs_990_);
lean_inc(v_ks_989_);
lean_dec(v_x_985_);
v___x_992_ = lean_box(0);
v_isShared_993_ = v_isSharedCheck_1014_;
goto v_resetjp_991_;
}
v_resetjp_991_:
{
lean_object* v___x_994_; uint8_t v___x_995_; 
v___x_994_ = lean_array_get_size(v_ks_989_);
v___x_995_ = lean_nat_dec_lt(v_x_986_, v___x_994_);
if (v___x_995_ == 0)
{
lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_999_; 
lean_dec(v_x_986_);
v___x_996_ = lean_array_push(v_ks_989_, v_x_987_);
v___x_997_ = lean_array_push(v_vs_990_, v_x_988_);
if (v_isShared_993_ == 0)
{
lean_ctor_set(v___x_992_, 1, v___x_997_);
lean_ctor_set(v___x_992_, 0, v___x_996_);
v___x_999_ = v___x_992_;
goto v_reusejp_998_;
}
else
{
lean_object* v_reuseFailAlloc_1000_; 
v_reuseFailAlloc_1000_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1000_, 0, v___x_996_);
lean_ctor_set(v_reuseFailAlloc_1000_, 1, v___x_997_);
v___x_999_ = v_reuseFailAlloc_1000_;
goto v_reusejp_998_;
}
v_reusejp_998_:
{
return v___x_999_;
}
}
else
{
lean_object* v_k_x27_1001_; uint8_t v___x_1002_; 
v_k_x27_1001_ = lean_array_fget_borrowed(v_ks_989_, v_x_986_);
v___x_1002_ = l_Lean_instBEqMVarId_beq(v_x_987_, v_k_x27_1001_);
if (v___x_1002_ == 0)
{
lean_object* v___x_1004_; 
if (v_isShared_993_ == 0)
{
v___x_1004_ = v___x_992_;
goto v_reusejp_1003_;
}
else
{
lean_object* v_reuseFailAlloc_1008_; 
v_reuseFailAlloc_1008_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1008_, 0, v_ks_989_);
lean_ctor_set(v_reuseFailAlloc_1008_, 1, v_vs_990_);
v___x_1004_ = v_reuseFailAlloc_1008_;
goto v_reusejp_1003_;
}
v_reusejp_1003_:
{
lean_object* v___x_1005_; lean_object* v___x_1006_; 
v___x_1005_ = lean_unsigned_to_nat(1u);
v___x_1006_ = lean_nat_add(v_x_986_, v___x_1005_);
lean_dec(v_x_986_);
v_x_985_ = v___x_1004_;
v_x_986_ = v___x_1006_;
goto _start;
}
}
else
{
lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1012_; 
v___x_1009_ = lean_array_fset(v_ks_989_, v_x_986_, v_x_987_);
v___x_1010_ = lean_array_fset(v_vs_990_, v_x_986_, v_x_988_);
lean_dec(v_x_986_);
if (v_isShared_993_ == 0)
{
lean_ctor_set(v___x_992_, 1, v___x_1010_);
lean_ctor_set(v___x_992_, 0, v___x_1009_);
v___x_1012_ = v___x_992_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v___x_1009_);
lean_ctor_set(v_reuseFailAlloc_1013_, 1, v___x_1010_);
v___x_1012_ = v_reuseFailAlloc_1013_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
return v___x_1012_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__12___redArg(lean_object* v_n_1015_, lean_object* v_k_1016_, lean_object* v_v_1017_){
_start:
{
lean_object* v___x_1018_; lean_object* v___x_1019_; 
v___x_1018_ = lean_unsigned_to_nat(0u);
v___x_1019_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__12_spec__16___redArg(v_n_1015_, v___x_1018_, v_k_1016_, v_v_1017_);
return v___x_1019_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_1020_; 
v___x_1020_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1020_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg(lean_object* v_x_1021_, size_t v_x_1022_, size_t v_x_1023_, lean_object* v_x_1024_, lean_object* v_x_1025_){
_start:
{
if (lean_obj_tag(v_x_1021_) == 0)
{
lean_object* v_es_1026_; size_t v___x_1027_; size_t v___x_1028_; lean_object* v_j_1029_; lean_object* v___x_1030_; uint8_t v___x_1031_; 
v_es_1026_ = lean_ctor_get(v_x_1021_, 0);
v___x_1027_ = ((size_t)31ULL);
v___x_1028_ = lean_usize_land(v_x_1022_, v___x_1027_);
v_j_1029_ = lean_usize_to_nat(v___x_1028_);
v___x_1030_ = lean_array_get_size(v_es_1026_);
v___x_1031_ = lean_nat_dec_lt(v_j_1029_, v___x_1030_);
if (v___x_1031_ == 0)
{
lean_dec(v_j_1029_);
lean_dec(v_x_1025_);
lean_dec(v_x_1024_);
return v_x_1021_;
}
else
{
lean_object* v___x_1033_; uint8_t v_isShared_1034_; uint8_t v_isSharedCheck_1070_; 
lean_inc_ref(v_es_1026_);
v_isSharedCheck_1070_ = !lean_is_exclusive(v_x_1021_);
if (v_isSharedCheck_1070_ == 0)
{
lean_object* v_unused_1071_; 
v_unused_1071_ = lean_ctor_get(v_x_1021_, 0);
lean_dec(v_unused_1071_);
v___x_1033_ = v_x_1021_;
v_isShared_1034_ = v_isSharedCheck_1070_;
goto v_resetjp_1032_;
}
else
{
lean_dec(v_x_1021_);
v___x_1033_ = lean_box(0);
v_isShared_1034_ = v_isSharedCheck_1070_;
goto v_resetjp_1032_;
}
v_resetjp_1032_:
{
lean_object* v_v_1035_; lean_object* v___x_1036_; lean_object* v_xs_x27_1037_; lean_object* v___y_1039_; 
v_v_1035_ = lean_array_fget(v_es_1026_, v_j_1029_);
v___x_1036_ = lean_box(0);
v_xs_x27_1037_ = lean_array_fset(v_es_1026_, v_j_1029_, v___x_1036_);
switch(lean_obj_tag(v_v_1035_))
{
case 0:
{
lean_object* v_key_1044_; lean_object* v_val_1045_; lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1055_; 
v_key_1044_ = lean_ctor_get(v_v_1035_, 0);
v_val_1045_ = lean_ctor_get(v_v_1035_, 1);
v_isSharedCheck_1055_ = !lean_is_exclusive(v_v_1035_);
if (v_isSharedCheck_1055_ == 0)
{
v___x_1047_ = v_v_1035_;
v_isShared_1048_ = v_isSharedCheck_1055_;
goto v_resetjp_1046_;
}
else
{
lean_inc(v_val_1045_);
lean_inc(v_key_1044_);
lean_dec(v_v_1035_);
v___x_1047_ = lean_box(0);
v_isShared_1048_ = v_isSharedCheck_1055_;
goto v_resetjp_1046_;
}
v_resetjp_1046_:
{
uint8_t v___x_1049_; 
v___x_1049_ = l_Lean_instBEqMVarId_beq(v_x_1024_, v_key_1044_);
if (v___x_1049_ == 0)
{
lean_object* v___x_1050_; lean_object* v___x_1051_; 
lean_del_object(v___x_1047_);
v___x_1050_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1044_, v_val_1045_, v_x_1024_, v_x_1025_);
v___x_1051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1051_, 0, v___x_1050_);
v___y_1039_ = v___x_1051_;
goto v___jp_1038_;
}
else
{
lean_object* v___x_1053_; 
lean_dec(v_val_1045_);
lean_dec(v_key_1044_);
if (v_isShared_1048_ == 0)
{
lean_ctor_set(v___x_1047_, 1, v_x_1025_);
lean_ctor_set(v___x_1047_, 0, v_x_1024_);
v___x_1053_ = v___x_1047_;
goto v_reusejp_1052_;
}
else
{
lean_object* v_reuseFailAlloc_1054_; 
v_reuseFailAlloc_1054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1054_, 0, v_x_1024_);
lean_ctor_set(v_reuseFailAlloc_1054_, 1, v_x_1025_);
v___x_1053_ = v_reuseFailAlloc_1054_;
goto v_reusejp_1052_;
}
v_reusejp_1052_:
{
v___y_1039_ = v___x_1053_;
goto v___jp_1038_;
}
}
}
}
case 1:
{
lean_object* v_node_1056_; lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1068_; 
v_node_1056_ = lean_ctor_get(v_v_1035_, 0);
v_isSharedCheck_1068_ = !lean_is_exclusive(v_v_1035_);
if (v_isSharedCheck_1068_ == 0)
{
v___x_1058_ = v_v_1035_;
v_isShared_1059_ = v_isSharedCheck_1068_;
goto v_resetjp_1057_;
}
else
{
lean_inc(v_node_1056_);
lean_dec(v_v_1035_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1068_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
size_t v___x_1060_; size_t v___x_1061_; size_t v___x_1062_; size_t v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1066_; 
v___x_1060_ = ((size_t)5ULL);
v___x_1061_ = lean_usize_shift_right(v_x_1022_, v___x_1060_);
v___x_1062_ = ((size_t)1ULL);
v___x_1063_ = lean_usize_add(v_x_1023_, v___x_1062_);
v___x_1064_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg(v_node_1056_, v___x_1061_, v___x_1063_, v_x_1024_, v_x_1025_);
if (v_isShared_1059_ == 0)
{
lean_ctor_set(v___x_1058_, 0, v___x_1064_);
v___x_1066_ = v___x_1058_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1067_; 
v_reuseFailAlloc_1067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1067_, 0, v___x_1064_);
v___x_1066_ = v_reuseFailAlloc_1067_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
v___y_1039_ = v___x_1066_;
goto v___jp_1038_;
}
}
}
default: 
{
lean_object* v___x_1069_; 
v___x_1069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1069_, 0, v_x_1024_);
lean_ctor_set(v___x_1069_, 1, v_x_1025_);
v___y_1039_ = v___x_1069_;
goto v___jp_1038_;
}
}
v___jp_1038_:
{
lean_object* v___x_1040_; lean_object* v___x_1042_; 
v___x_1040_ = lean_array_fset(v_xs_x27_1037_, v_j_1029_, v___y_1039_);
lean_dec(v_j_1029_);
if (v_isShared_1034_ == 0)
{
lean_ctor_set(v___x_1033_, 0, v___x_1040_);
v___x_1042_ = v___x_1033_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v___x_1040_);
v___x_1042_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
return v___x_1042_;
}
}
}
}
}
else
{
lean_object* v_ks_1072_; lean_object* v_vs_1073_; lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1091_; 
v_ks_1072_ = lean_ctor_get(v_x_1021_, 0);
v_vs_1073_ = lean_ctor_get(v_x_1021_, 1);
v_isSharedCheck_1091_ = !lean_is_exclusive(v_x_1021_);
if (v_isSharedCheck_1091_ == 0)
{
v___x_1075_ = v_x_1021_;
v_isShared_1076_ = v_isSharedCheck_1091_;
goto v_resetjp_1074_;
}
else
{
lean_inc(v_vs_1073_);
lean_inc(v_ks_1072_);
lean_dec(v_x_1021_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1091_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
lean_object* v___x_1078_; 
if (v_isShared_1076_ == 0)
{
v___x_1078_ = v___x_1075_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v_ks_1072_);
lean_ctor_set(v_reuseFailAlloc_1090_, 1, v_vs_1073_);
v___x_1078_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
lean_object* v_newNode_1079_; size_t v___x_1080_; uint8_t v___x_1081_; 
v_newNode_1079_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__12___redArg(v___x_1078_, v_x_1024_, v_x_1025_);
v___x_1080_ = ((size_t)7ULL);
v___x_1081_ = lean_usize_dec_le(v___x_1080_, v_x_1023_);
if (v___x_1081_ == 0)
{
lean_object* v___x_1082_; lean_object* v___x_1083_; uint8_t v___x_1084_; 
v___x_1082_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1079_);
v___x_1083_ = lean_unsigned_to_nat(4u);
v___x_1084_ = lean_nat_dec_lt(v___x_1082_, v___x_1083_);
lean_dec(v___x_1082_);
if (v___x_1084_ == 0)
{
lean_object* v_ks_1085_; lean_object* v_vs_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; 
v_ks_1085_ = lean_ctor_get(v_newNode_1079_, 0);
lean_inc_ref(v_ks_1085_);
v_vs_1086_ = lean_ctor_get(v_newNode_1079_, 1);
lean_inc_ref(v_vs_1086_);
lean_dec_ref(v_newNode_1079_);
v___x_1087_ = lean_unsigned_to_nat(0u);
v___x_1088_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__0);
v___x_1089_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__13___redArg(v_x_1023_, v_ks_1085_, v_vs_1086_, v___x_1087_, v___x_1088_);
lean_dec_ref(v_vs_1086_);
lean_dec_ref(v_ks_1085_);
return v___x_1089_;
}
else
{
return v_newNode_1079_;
}
}
else
{
return v_newNode_1079_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__13___redArg(size_t v_depth_1092_, lean_object* v_keys_1093_, lean_object* v_vals_1094_, lean_object* v_i_1095_, lean_object* v_entries_1096_){
_start:
{
lean_object* v___x_1097_; uint8_t v___x_1098_; 
v___x_1097_ = lean_array_get_size(v_keys_1093_);
v___x_1098_ = lean_nat_dec_lt(v_i_1095_, v___x_1097_);
if (v___x_1098_ == 0)
{
lean_dec(v_i_1095_);
return v_entries_1096_;
}
else
{
lean_object* v_k_1099_; lean_object* v_v_1100_; uint64_t v___x_1101_; size_t v_h_1102_; size_t v___x_1103_; lean_object* v___x_1104_; size_t v___x_1105_; size_t v___x_1106_; size_t v___x_1107_; size_t v_h_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; 
v_k_1099_ = lean_array_fget_borrowed(v_keys_1093_, v_i_1095_);
v_v_1100_ = lean_array_fget_borrowed(v_vals_1094_, v_i_1095_);
v___x_1101_ = l_Lean_instHashableMVarId_hash(v_k_1099_);
v_h_1102_ = lean_uint64_to_usize(v___x_1101_);
v___x_1103_ = ((size_t)5ULL);
v___x_1104_ = lean_unsigned_to_nat(1u);
v___x_1105_ = ((size_t)1ULL);
v___x_1106_ = lean_usize_sub(v_depth_1092_, v___x_1105_);
v___x_1107_ = lean_usize_mul(v___x_1103_, v___x_1106_);
v_h_1108_ = lean_usize_shift_right(v_h_1102_, v___x_1107_);
v___x_1109_ = lean_nat_add(v_i_1095_, v___x_1104_);
lean_dec(v_i_1095_);
lean_inc(v_v_1100_);
lean_inc(v_k_1099_);
v___x_1110_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg(v_entries_1096_, v_h_1108_, v_depth_1092_, v_k_1099_, v_v_1100_);
v_i_1095_ = v___x_1109_;
v_entries_1096_ = v___x_1110_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__13___redArg___boxed(lean_object* v_depth_1112_, lean_object* v_keys_1113_, lean_object* v_vals_1114_, lean_object* v_i_1115_, lean_object* v_entries_1116_){
_start:
{
size_t v_depth_boxed_1117_; lean_object* v_res_1118_; 
v_depth_boxed_1117_ = lean_unbox_usize(v_depth_1112_);
lean_dec(v_depth_1112_);
v_res_1118_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__13___redArg(v_depth_boxed_1117_, v_keys_1113_, v_vals_1114_, v_i_1115_, v_entries_1116_);
lean_dec_ref(v_vals_1114_);
lean_dec_ref(v_keys_1113_);
return v_res_1118_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___boxed(lean_object* v_x_1119_, lean_object* v_x_1120_, lean_object* v_x_1121_, lean_object* v_x_1122_, lean_object* v_x_1123_){
_start:
{
size_t v_x_15832__boxed_1124_; size_t v_x_15833__boxed_1125_; lean_object* v_res_1126_; 
v_x_15832__boxed_1124_ = lean_unbox_usize(v_x_1120_);
lean_dec(v_x_1120_);
v_x_15833__boxed_1125_ = lean_unbox_usize(v_x_1121_);
lean_dec(v_x_1121_);
v_res_1126_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg(v_x_1119_, v_x_15832__boxed_1124_, v_x_15833__boxed_1125_, v_x_1122_, v_x_1123_);
return v_res_1126_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3___redArg(lean_object* v_x_1127_, lean_object* v_x_1128_, lean_object* v_x_1129_){
_start:
{
uint64_t v___x_1130_; size_t v___x_1131_; size_t v___x_1132_; lean_object* v___x_1133_; 
v___x_1130_ = l_Lean_instHashableMVarId_hash(v_x_1128_);
v___x_1131_ = lean_uint64_to_usize(v___x_1130_);
v___x_1132_ = ((size_t)1ULL);
v___x_1133_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg(v_x_1127_, v___x_1131_, v___x_1132_, v_x_1128_, v_x_1129_);
return v___x_1133_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3___redArg(lean_object* v_mvarId_1134_, lean_object* v_val_1135_, lean_object* v___y_1136_){
_start:
{
lean_object* v___x_1138_; lean_object* v_mctx_1139_; lean_object* v_cache_1140_; lean_object* v_zetaDeltaFVarIds_1141_; lean_object* v_postponed_1142_; lean_object* v_diag_1143_; lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1172_; 
v___x_1138_ = lean_st_ref_take(v___y_1136_);
v_mctx_1139_ = lean_ctor_get(v___x_1138_, 0);
v_cache_1140_ = lean_ctor_get(v___x_1138_, 1);
v_zetaDeltaFVarIds_1141_ = lean_ctor_get(v___x_1138_, 2);
v_postponed_1142_ = lean_ctor_get(v___x_1138_, 3);
v_diag_1143_ = lean_ctor_get(v___x_1138_, 4);
v_isSharedCheck_1172_ = !lean_is_exclusive(v___x_1138_);
if (v_isSharedCheck_1172_ == 0)
{
v___x_1145_ = v___x_1138_;
v_isShared_1146_ = v_isSharedCheck_1172_;
goto v_resetjp_1144_;
}
else
{
lean_inc(v_diag_1143_);
lean_inc(v_postponed_1142_);
lean_inc(v_zetaDeltaFVarIds_1141_);
lean_inc(v_cache_1140_);
lean_inc(v_mctx_1139_);
lean_dec(v___x_1138_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1172_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
lean_object* v_depth_1147_; lean_object* v_levelAssignDepth_1148_; lean_object* v_lmvarCounter_1149_; lean_object* v_mvarCounter_1150_; lean_object* v_lDecls_1151_; lean_object* v_decls_1152_; lean_object* v_userNames_1153_; lean_object* v_lAssignment_1154_; lean_object* v_eAssignment_1155_; lean_object* v_dAssignment_1156_; lean_object* v_instanceTypedMVars_1157_; lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1171_; 
v_depth_1147_ = lean_ctor_get(v_mctx_1139_, 0);
v_levelAssignDepth_1148_ = lean_ctor_get(v_mctx_1139_, 1);
v_lmvarCounter_1149_ = lean_ctor_get(v_mctx_1139_, 2);
v_mvarCounter_1150_ = lean_ctor_get(v_mctx_1139_, 3);
v_lDecls_1151_ = lean_ctor_get(v_mctx_1139_, 4);
v_decls_1152_ = lean_ctor_get(v_mctx_1139_, 5);
v_userNames_1153_ = lean_ctor_get(v_mctx_1139_, 6);
v_lAssignment_1154_ = lean_ctor_get(v_mctx_1139_, 7);
v_eAssignment_1155_ = lean_ctor_get(v_mctx_1139_, 8);
v_dAssignment_1156_ = lean_ctor_get(v_mctx_1139_, 9);
v_instanceTypedMVars_1157_ = lean_ctor_get(v_mctx_1139_, 10);
v_isSharedCheck_1171_ = !lean_is_exclusive(v_mctx_1139_);
if (v_isSharedCheck_1171_ == 0)
{
v___x_1159_ = v_mctx_1139_;
v_isShared_1160_ = v_isSharedCheck_1171_;
goto v_resetjp_1158_;
}
else
{
lean_inc(v_instanceTypedMVars_1157_);
lean_inc(v_dAssignment_1156_);
lean_inc(v_eAssignment_1155_);
lean_inc(v_lAssignment_1154_);
lean_inc(v_userNames_1153_);
lean_inc(v_decls_1152_);
lean_inc(v_lDecls_1151_);
lean_inc(v_mvarCounter_1150_);
lean_inc(v_lmvarCounter_1149_);
lean_inc(v_levelAssignDepth_1148_);
lean_inc(v_depth_1147_);
lean_dec(v_mctx_1139_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1171_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
lean_object* v___x_1161_; lean_object* v___x_1163_; 
v___x_1161_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3___redArg(v_eAssignment_1155_, v_mvarId_1134_, v_val_1135_);
if (v_isShared_1160_ == 0)
{
lean_ctor_set(v___x_1159_, 8, v___x_1161_);
v___x_1163_ = v___x_1159_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v_depth_1147_);
lean_ctor_set(v_reuseFailAlloc_1170_, 1, v_levelAssignDepth_1148_);
lean_ctor_set(v_reuseFailAlloc_1170_, 2, v_lmvarCounter_1149_);
lean_ctor_set(v_reuseFailAlloc_1170_, 3, v_mvarCounter_1150_);
lean_ctor_set(v_reuseFailAlloc_1170_, 4, v_lDecls_1151_);
lean_ctor_set(v_reuseFailAlloc_1170_, 5, v_decls_1152_);
lean_ctor_set(v_reuseFailAlloc_1170_, 6, v_userNames_1153_);
lean_ctor_set(v_reuseFailAlloc_1170_, 7, v_lAssignment_1154_);
lean_ctor_set(v_reuseFailAlloc_1170_, 8, v___x_1161_);
lean_ctor_set(v_reuseFailAlloc_1170_, 9, v_dAssignment_1156_);
lean_ctor_set(v_reuseFailAlloc_1170_, 10, v_instanceTypedMVars_1157_);
v___x_1163_ = v_reuseFailAlloc_1170_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
lean_object* v___x_1165_; 
if (v_isShared_1146_ == 0)
{
lean_ctor_set(v___x_1145_, 0, v___x_1163_);
v___x_1165_ = v___x_1145_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v___x_1163_);
lean_ctor_set(v_reuseFailAlloc_1169_, 1, v_cache_1140_);
lean_ctor_set(v_reuseFailAlloc_1169_, 2, v_zetaDeltaFVarIds_1141_);
lean_ctor_set(v_reuseFailAlloc_1169_, 3, v_postponed_1142_);
lean_ctor_set(v_reuseFailAlloc_1169_, 4, v_diag_1143_);
v___x_1165_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; 
v___x_1166_ = lean_st_ref_put(v___y_1136_, v___x_1165_);
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
v___x_1456_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1___redArg();
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
v___x_1782_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1___redArg();
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
v___x_1787_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1___redArg();
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
v___y_1442_ = v___y_1463_;
v___y_1443_ = v___y_1465_;
v___y_1444_ = v___x_1470_;
v___y_1445_ = v___y_1469_;
v___y_1446_ = v___y_1466_;
v___y_1447_ = v___y_1468_;
v___y_1448_ = v___y_1462_;
v___y_1449_ = v___y_1464_;
v___y_1450_ = v___y_1467_;
v___y_1451_ = v___y_1460_;
v___y_1452_ = v___y_1461_;
v___y_1453_ = v___x_1472_;
v___y_1454_ = v___x_1472_;
goto v___jp_1441_;
}
else
{
v___y_1442_ = v___y_1463_;
v___y_1443_ = v___y_1465_;
v___y_1444_ = v___x_1470_;
v___y_1445_ = v___y_1469_;
v___y_1446_ = v___y_1466_;
v___y_1447_ = v___y_1468_;
v___y_1448_ = v___y_1462_;
v___y_1449_ = v___y_1464_;
v___y_1450_ = v___y_1467_;
v___y_1451_ = v___y_1460_;
v___y_1452_ = v___y_1461_;
v___y_1453_ = v___x_1472_;
v___y_1454_ = v___x_1457_;
goto v___jp_1441_;
}
}
else
{
v___y_1413_ = v___y_1463_;
v___y_1414_ = v___y_1468_;
v___y_1415_ = v___y_1462_;
v___y_1416_ = v___y_1464_;
v___y_1417_ = v___y_1467_;
v___y_1418_ = v___y_1465_;
v___y_1419_ = v___y_1461_;
v___y_1420_ = v___y_1469_;
v___y_1421_ = v___y_1466_;
v___y_1422_ = v___y_1460_;
goto v___jp_1412_;
}
}
v___jp_1474_:
{
lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; 
v___x_1491_ = l_Lean_Meta_Simp_Context_setMemoize(v___y_1489_, v___y_1490_);
v___x_1492_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__6, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__6_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__6);
lean_inc(v___y_1484_);
lean_inc_ref(v___y_1485_);
v___x_1493_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre___boxed), 11, 2);
lean_closure_set(v___x_1493_, 0, v___y_1485_);
lean_closure_set(v___x_1493_, 1, v___y_1484_);
lean_inc_ref(v___y_1476_);
lean_inc_ref(v___y_1486_);
v___x_1494_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_1494_, 0, v___x_1493_);
lean_ctor_set(v___x_1494_, 1, v___y_1478_);
lean_ctor_set(v___x_1494_, 2, v___y_1486_);
lean_ctor_set(v___x_1494_, 3, v___f_1349_);
lean_ctor_set(v___x_1494_, 4, v___y_1476_);
lean_ctor_set_uint8(v___x_1494_, sizeof(void*)*5, v___x_1350_);
v___x_1495_ = l_Lean_Meta_Simp_main(v___y_1488_, v___x_1491_, v___x_1492_, v___x_1494_, v___y_1487_, v___y_1481_, v___y_1479_, v___y_1477_);
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
v___x_1501_ = lean_st_ref_get(v___y_1484_);
lean_dec(v___y_1484_);
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
lean_dec_ref(v___y_1485_);
v___y_1366_ = v_fst_1497_;
v_subgoals_1367_ = v_subgoals_1502_;
v___y_1368_ = v___y_1480_;
v___y_1369_ = v___y_1482_;
v___y_1370_ = v___y_1483_;
v___y_1371_ = v___y_1475_;
v___y_1372_ = v___y_1487_;
v___y_1373_ = v___y_1481_;
v___y_1374_ = v___y_1479_;
v___y_1375_ = v___y_1477_;
goto v___jp_1365_;
}
else
{
lean_object* v_expr_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1509_; 
lean_dec_ref(v_subgoals_1502_);
lean_dec(v_fst_1497_);
v_expr_1505_ = lean_ctor_get(v___y_1485_, 2);
lean_inc_ref(v_expr_1505_);
lean_dec_ref(v___y_1485_);
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
v___x_1510_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg(v___x_1509_, v___y_1487_, v___y_1481_, v___y_1479_, v___y_1477_);
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
lean_dec_ref(v___y_1485_);
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
v___x_1550_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg(v___x_1549_, v___y_1487_, v___y_1481_, v___y_1479_, v___y_1477_);
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
v___y_1462_ = v___y_1480_;
v___y_1463_ = v___y_1482_;
v___y_1464_ = v___y_1483_;
v___y_1465_ = v___y_1475_;
v___y_1466_ = v___y_1487_;
v___y_1467_ = v___y_1481_;
v___y_1468_ = v___y_1479_;
v___y_1469_ = v___y_1477_;
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
v_expr_1557_ = lean_ctor_get(v___y_1485_, 2);
lean_inc_ref(v_expr_1557_);
lean_dec_ref(v___y_1485_);
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
v___x_1562_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg(v___x_1561_, v___y_1487_, v___y_1481_, v___y_1479_, v___y_1477_);
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
lean_dec_ref(v___y_1485_);
lean_dec(v___y_1484_);
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
v___y_1476_ = v___y_1584_;
v___y_1477_ = v___y_1596_;
v___y_1478_ = v___y_1586_;
v___y_1479_ = v___y_1595_;
v___y_1480_ = v___y_1589_;
v___y_1481_ = v___y_1594_;
v___y_1482_ = v___y_1590_;
v___y_1483_ = v___y_1591_;
v___y_1484_ = v___x_1597_;
v___y_1485_ = v___y_1583_;
v___y_1486_ = v___y_1585_;
v___y_1487_ = v___y_1593_;
v___y_1488_ = v___y_1587_;
v___y_1489_ = v_a_1599_;
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
v___y_1476_ = v___y_1584_;
v___y_1477_ = v___y_1596_;
v___y_1478_ = v___y_1586_;
v___y_1479_ = v___y_1595_;
v___y_1480_ = v___y_1589_;
v___y_1481_ = v___y_1594_;
v___y_1482_ = v___y_1590_;
v___y_1483_ = v___y_1591_;
v___y_1484_ = v___x_1597_;
v___y_1485_ = v___y_1583_;
v___y_1486_ = v___y_1585_;
v___y_1487_ = v___y_1593_;
v___y_1488_ = v___y_1587_;
v___y_1489_ = v_a_1600_;
v___y_1490_ = v___x_1601_;
goto v___jp_1474_;
}
}
else
{
lean_object* v_a_1602_; lean_object* v___x_1604_; uint8_t v_isShared_1605_; uint8_t v_isSharedCheck_1609_; 
lean_dec(v___x_1597_);
lean_dec_ref(v_occs_1588_);
lean_dec_ref(v___y_1587_);
lean_dec_ref(v___y_1586_);
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
v___x_1626_ = lean_array_to_list(v___y_1616_);
v___x_1627_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1627_, 0, v___x_1625_);
lean_ctor_set(v___x_1627_, 1, v___x_1457_);
lean_ctor_set(v___x_1627_, 2, v___x_1626_);
v___y_1583_ = v___y_1611_;
v___y_1584_ = v___y_1612_;
v___y_1585_ = v___y_1614_;
v___y_1586_ = v___y_1613_;
v___y_1587_ = v___y_1615_;
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
lean_dec_ref(v___y_1638_);
lean_dec_ref(v___y_1635_);
lean_dec_ref(v___y_1632_);
lean_dec_ref(v___f_1349_);
v___x_1644_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__17, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__17_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__17);
v___x_1645_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg(v___x_1644_, v___y_1639_, v___y_1640_, v___y_1637_, v___y_1633_);
return v___x_1645_;
}
else
{
v___y_1611_ = v___y_1635_;
v___y_1612_ = v___y_1630_;
v___y_1613_ = v___y_1632_;
v___y_1614_ = v___y_1636_;
v___y_1615_ = v___y_1638_;
v___y_1616_ = v___y_1642_;
v___y_1617_ = v___y_1641_;
v___y_1618_ = v___y_1634_;
v___y_1619_ = v___y_1629_;
v___y_1620_ = v___y_1631_;
v___y_1621_ = v___y_1639_;
v___y_1622_ = v___y_1640_;
v___y_1623_ = v___y_1637_;
v___y_1624_ = v___y_1633_;
goto v___jp_1610_;
}
}
v___jp_1646_:
{
lean_object* v___x_1664_; 
v___x_1664_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg(v___y_1658_, v___y_1662_, v___y_1653_, v___y_1663_);
lean_dec(v___y_1663_);
lean_dec(v___y_1658_);
v___y_1629_ = v___y_1647_;
v___y_1630_ = v___y_1648_;
v___y_1631_ = v___y_1649_;
v___y_1632_ = v___y_1650_;
v___y_1633_ = v___y_1651_;
v___y_1634_ = v___y_1652_;
v___y_1635_ = v___y_1654_;
v___y_1636_ = v___y_1655_;
v___y_1637_ = v___y_1656_;
v___y_1638_ = v___y_1657_;
v___y_1639_ = v___y_1660_;
v___y_1640_ = v___y_1659_;
v___y_1641_ = v___y_1661_;
v___y_1642_ = v___x_1664_;
goto v___jp_1628_;
}
v___jp_1665_:
{
uint8_t v___x_1683_; 
v___x_1683_ = lean_nat_dec_le(v___y_1682_, v___y_1677_);
if (v___x_1683_ == 0)
{
lean_dec(v___y_1677_);
lean_inc(v___y_1682_);
v___y_1647_ = v___y_1666_;
v___y_1648_ = v___y_1667_;
v___y_1649_ = v___y_1668_;
v___y_1650_ = v___y_1669_;
v___y_1651_ = v___y_1670_;
v___y_1652_ = v___y_1671_;
v___y_1653_ = v___y_1682_;
v___y_1654_ = v___y_1672_;
v___y_1655_ = v___y_1673_;
v___y_1656_ = v___y_1674_;
v___y_1657_ = v___y_1675_;
v___y_1658_ = v___y_1676_;
v___y_1659_ = v___y_1679_;
v___y_1660_ = v___y_1678_;
v___y_1661_ = v___y_1681_;
v___y_1662_ = v___y_1680_;
v___y_1663_ = v___y_1682_;
goto v___jp_1646_;
}
else
{
v___y_1647_ = v___y_1666_;
v___y_1648_ = v___y_1667_;
v___y_1649_ = v___y_1668_;
v___y_1650_ = v___y_1669_;
v___y_1651_ = v___y_1670_;
v___y_1652_ = v___y_1671_;
v___y_1653_ = v___y_1682_;
v___y_1654_ = v___y_1672_;
v___y_1655_ = v___y_1673_;
v___y_1656_ = v___y_1674_;
v___y_1657_ = v___y_1675_;
v___y_1658_ = v___y_1676_;
v___y_1659_ = v___y_1679_;
v___y_1660_ = v___y_1678_;
v___y_1661_ = v___y_1681_;
v___y_1662_ = v___y_1680_;
v___y_1663_ = v___y_1677_;
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
v___y_1584_ = v___f_1726_;
v___y_1585_ = v___f_1725_;
v___y_1586_ = v___f_1724_;
v___y_1587_ = v_a_1722_;
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
v___x_1735_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1___redArg();
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
v___y_1667_ = v___f_1726_;
v___y_1668_ = v___y_1689_;
v___y_1669_ = v___f_1724_;
v___y_1670_ = v___y_1693_;
v___y_1671_ = v___y_1687_;
v___y_1672_ = v_a_1720_;
v___y_1673_ = v___f_1725_;
v___y_1674_ = v___y_1692_;
v___y_1675_ = v_a_1722_;
v___y_1676_ = v___x_1750_;
v___y_1677_ = v___x_1752_;
v___y_1678_ = v___y_1690_;
v___y_1679_ = v___y_1691_;
v___y_1680_ = v_a_1749_;
v___y_1681_ = v___y_1686_;
v___y_1682_ = v___x_1752_;
goto v___jp_1665_;
}
else
{
v___y_1666_ = v___y_1688_;
v___y_1667_ = v___f_1726_;
v___y_1668_ = v___y_1689_;
v___y_1669_ = v___f_1724_;
v___y_1670_ = v___y_1693_;
v___y_1671_ = v___y_1687_;
v___y_1672_ = v_a_1720_;
v___y_1673_ = v___f_1725_;
v___y_1674_ = v___y_1692_;
v___y_1675_ = v_a_1722_;
v___y_1676_ = v___x_1750_;
v___y_1677_ = v___x_1752_;
v___y_1678_ = v___y_1690_;
v___y_1679_ = v___y_1691_;
v___y_1680_ = v_a_1749_;
v___y_1681_ = v___y_1686_;
v___y_1682_ = v___x_1457_;
goto v___jp_1665_;
}
}
else
{
v___y_1629_ = v___y_1688_;
v___y_1630_ = v___f_1726_;
v___y_1631_ = v___y_1689_;
v___y_1632_ = v___f_1724_;
v___y_1633_ = v___y_1693_;
v___y_1634_ = v___y_1687_;
v___y_1635_ = v_a_1720_;
v___y_1636_ = v___f_1725_;
v___y_1637_ = v___y_1692_;
v___y_1638_ = v_a_1722_;
v___y_1639_ = v___y_1690_;
v___y_1640_ = v___y_1691_;
v___y_1641_ = v___y_1686_;
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
v___y_1584_ = v___f_1726_;
v___y_1585_ = v___f_1725_;
v___y_1586_ = v___f_1724_;
v___y_1587_ = v_a_1722_;
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
v___y_1366_ = v___y_1419_;
v_subgoals_1367_ = v___x_1425_;
v___y_1368_ = v___y_1415_;
v___y_1369_ = v___y_1413_;
v___y_1370_ = v___y_1416_;
v___y_1371_ = v___y_1418_;
v___y_1372_ = v___y_1421_;
v___y_1373_ = v___y_1417_;
v___y_1374_ = v___y_1414_;
v___y_1375_ = v___y_1420_;
goto v___jp_1365_;
}
v___jp_1426_:
{
lean_object* v___x_1440_; 
v___x_1440_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg(v___y_1429_, v___y_1436_, v___y_1438_, v___y_1439_);
lean_dec(v___y_1439_);
lean_dec(v___y_1429_);
v___y_1413_ = v___y_1427_;
v___y_1414_ = v___y_1432_;
v___y_1415_ = v___y_1433_;
v___y_1416_ = v___y_1434_;
v___y_1417_ = v___y_1435_;
v___y_1418_ = v___y_1428_;
v___y_1419_ = v___y_1437_;
v___y_1420_ = v___y_1430_;
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
uint8_t v___x_16293__boxed_1809_; uint8_t v___x_16295__boxed_1810_; lean_object* v_res_1811_; 
v___x_16293__boxed_1809_ = lean_unbox(v___x_1792_);
v___x_16295__boxed_1810_ = lean_unbox(v___x_1794_);
v_res_1811_ = l_Lean_Elab_Tactic_Conv_evalPattern___lam__6(v___x_16293__boxed_1809_, v___f_1793_, v___x_16295__boxed_1810_, v_stx_1795_, v___x_1796_, v___x_1797_, v___x_1798_, v___x_1799_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_);
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
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0(lean_object* v_00_u03b1_1857_, lean_object* v_ref_1858_, lean_object* v_msg_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_){
_start:
{
lean_object* v___x_1869_; 
v___x_1869_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg(v_ref_1858_, v_msg_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_);
return v___x_1869_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___boxed(lean_object* v_00_u03b1_1870_, lean_object* v_ref_1871_, lean_object* v_msg_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_){
_start:
{
lean_object* v_res_1882_; 
v_res_1882_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0(v_00_u03b1_1870_, v_ref_1871_, v_msg_1872_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_);
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
size_t v_x_17409__boxed_2059_; size_t v_x_17410__boxed_2060_; lean_object* v_res_2061_; 
v_x_17409__boxed_2059_ = lean_unbox_usize(v_x_2055_);
lean_dec(v_x_2055_);
v_x_17410__boxed_2060_ = lean_unbox_usize(v_x_2056_);
lean_dec(v_x_2056_);
v_res_2061_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4(v_00_u03b2_2053_, v_x_2054_, v_x_17409__boxed_2059_, v_x_17410__boxed_2060_, v_x_2057_, v_x_2058_);
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
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Conv_Pattern(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
