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
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withoutErrToSorryImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
lean_object* lean_obj_tag_nat(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 52, .m_capacity = 52, .m_length = 51, .m_data = "`pattern` conv tactic failed, pattern was not found"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__7_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__8;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`pattern` conv tactic failed, pattern was found only "};
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
static const lean_closure_object l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Conv_evalPattern___lam__2___boxed, .m_arity = 10, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__18 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__18_value;
static const lean_closure_object l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Conv_evalPattern___lam__3___boxed, .m_arity = 10, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
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
lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_getContext___redArg(lean_object* v_a_3_, lean_object* v_a_4_, lean_object* v_a_5_){
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
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_getContext___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3_ = stack[0].m_obj;
lean_object* v_a_4_ = stack[1].m_obj;
lean_object* v_a_5_ = stack[2].m_obj;
lean_object* v_res_21_;
v_res_21_ = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_getContext___redArg(v_a_3_, v_a_4_, v_a_5_);
stack->m_obj
 = v_res_21_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_getContext___redArg___boxed(lean_object* v_a_22_, lean_object* v_a_23_, lean_object* v_a_24_, lean_object* v_a_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_getContext___redArg(v_a_22_, v_a_23_, v_a_24_);
lean_dec(v_a_24_);
lean_dec_ref(v_a_23_);
lean_dec_ref(v_a_22_);
return v_res_26_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_getContext(lean_object* v_a_27_, lean_object* v_a_28_, lean_object* v_a_29_, lean_object* v_a_30_){
_start:
{
lean_object* v___x_32_; 
v___x_32_ = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_getContext___redArg(v_a_27_, v_a_29_, v_a_30_);
return v___x_32_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_getContext_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_27_ = stack[0].m_obj;
lean_object* v_a_28_ = stack[1].m_obj;
lean_object* v_a_29_ = stack[2].m_obj;
lean_object* v_a_30_ = stack[3].m_obj;
lean_object* v_res_33_;
v_res_33_ = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_getContext(v_a_27_, v_a_28_, v_a_29_, v_a_30_);
stack->m_obj
 = v_res_33_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_getContext___boxed(lean_object* v_a_34_, lean_object* v_a_35_, lean_object* v_a_36_, lean_object* v_a_37_, lean_object* v_a_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_getContext(v_a_34_, v_a_35_, v_a_36_, v_a_37_);
lean_dec(v_a_37_);
lean_dec_ref(v_a_36_);
lean_dec(v_a_35_);
lean_dec_ref(v_a_34_);
return v_res_39_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_matchPattern_x3f_go_x3f(lean_object* v_pattern_42_, lean_object* v_e_43_, lean_object* v_a_44_, lean_object* v_a_45_, lean_object* v_a_46_, lean_object* v_a_47_){
_start:
{
lean_object* v___x_49_; lean_object* v___x_50_; uint8_t v___x_51_; 
lean_inc_ref(v_e_43_);
v___x_49_ = l_Lean_Expr_toHeadIndex(v_e_43_);
lean_inc_ref(v_pattern_42_);
v___x_50_ = l_Lean_Expr_toHeadIndex(v_pattern_42_);
v___x_51_ = l_Lean_instBEqHeadIndex_beq(v___x_49_, v___x_50_);
lean_dec(v___x_50_);
lean_dec(v___x_49_);
if (v___x_51_ == 0)
{
lean_object* v___x_52_; lean_object* v___x_53_; 
lean_dec_ref(v_e_43_);
lean_dec_ref(v_pattern_42_);
v___x_52_ = lean_box(0);
v___x_53_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_53_, 0, v___x_52_);
return v___x_53_;
}
else
{
lean_object* v___x_54_; 
lean_inc_ref(v_e_43_);
lean_inc_ref(v_pattern_42_);
v___x_54_ = l_Lean_Meta_isExprDefEqGuarded(v_pattern_42_, v_e_43_, v_a_44_, v_a_45_, v_a_46_, v_a_47_);
if (lean_obj_tag(v___x_54_) == 0)
{
lean_object* v_a_55_; lean_object* v___x_57_; uint8_t v_isShared_58_; uint8_t v_isSharedCheck_101_; 
v_a_55_ = lean_ctor_get(v___x_54_, 0);
v_isSharedCheck_101_ = !lean_is_exclusive(v___x_54_);
if (v_isSharedCheck_101_ == 0)
{
v___x_57_ = v___x_54_;
v_isShared_58_ = v_isSharedCheck_101_;
goto v_resetjp_56_;
}
else
{
lean_inc(v_a_55_);
lean_dec(v___x_54_);
v___x_57_ = lean_box(0);
v_isShared_58_ = v_isSharedCheck_101_;
goto v_resetjp_56_;
}
v_resetjp_56_:
{
uint8_t v___x_59_; 
v___x_59_ = lean_unbox(v_a_55_);
lean_dec(v_a_55_);
if (v___x_59_ == 0)
{
uint8_t v___x_60_; 
v___x_60_ = l_Lean_Expr_isApp(v_e_43_);
if (v___x_60_ == 0)
{
lean_object* v___x_61_; lean_object* v___x_63_; 
lean_dec_ref(v_e_43_);
lean_dec_ref(v_pattern_42_);
v___x_61_ = lean_box(0);
if (v_isShared_58_ == 0)
{
lean_ctor_set(v___x_57_, 0, v___x_61_);
v___x_63_ = v___x_57_;
goto v_reusejp_62_;
}
else
{
lean_object* v_reuseFailAlloc_64_; 
v_reuseFailAlloc_64_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_64_, 0, v___x_61_);
v___x_63_ = v_reuseFailAlloc_64_;
goto v_reusejp_62_;
}
v_reusejp_62_:
{
return v___x_63_;
}
}
else
{
lean_object* v___x_65_; lean_object* v___x_66_; 
lean_del_object(v___x_57_);
v___x_65_ = l_Lean_Expr_appFn_x21(v_e_43_);
v___x_66_ = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_matchPattern_x3f_go_x3f(v_pattern_42_, v___x_65_, v_a_44_, v_a_45_, v_a_46_, v_a_47_);
if (lean_obj_tag(v___x_66_) == 0)
{
lean_object* v_a_67_; 
v_a_67_ = lean_ctor_get(v___x_66_, 0);
lean_inc(v_a_67_);
if (lean_obj_tag(v_a_67_) == 0)
{
lean_dec_ref(v_e_43_);
return v___x_66_;
}
else
{
lean_object* v___x_69_; uint8_t v_isShared_70_; uint8_t v_isSharedCheck_93_; 
v_isSharedCheck_93_ = !lean_is_exclusive(v___x_66_);
if (v_isSharedCheck_93_ == 0)
{
lean_object* v_unused_94_; 
v_unused_94_ = lean_ctor_get(v___x_66_, 0);
lean_dec(v_unused_94_);
v___x_69_ = v___x_66_;
v_isShared_70_ = v_isSharedCheck_93_;
goto v_resetjp_68_;
}
else
{
lean_dec(v___x_66_);
v___x_69_ = lean_box(0);
v_isShared_70_ = v_isSharedCheck_93_;
goto v_resetjp_68_;
}
v_resetjp_68_:
{
lean_object* v_val_71_; lean_object* v___x_73_; uint8_t v_isShared_74_; uint8_t v_isSharedCheck_92_; 
v_val_71_ = lean_ctor_get(v_a_67_, 0);
v_isSharedCheck_92_ = !lean_is_exclusive(v_a_67_);
if (v_isSharedCheck_92_ == 0)
{
v___x_73_ = v_a_67_;
v_isShared_74_ = v_isSharedCheck_92_;
goto v_resetjp_72_;
}
else
{
lean_inc(v_val_71_);
lean_dec(v_a_67_);
v___x_73_ = lean_box(0);
v_isShared_74_ = v_isSharedCheck_92_;
goto v_resetjp_72_;
}
v_resetjp_72_:
{
lean_object* v_fst_75_; lean_object* v_snd_76_; lean_object* v___x_78_; uint8_t v_isShared_79_; uint8_t v_isSharedCheck_91_; 
v_fst_75_ = lean_ctor_get(v_val_71_, 0);
v_snd_76_ = lean_ctor_get(v_val_71_, 1);
v_isSharedCheck_91_ = !lean_is_exclusive(v_val_71_);
if (v_isSharedCheck_91_ == 0)
{
v___x_78_ = v_val_71_;
v_isShared_79_ = v_isSharedCheck_91_;
goto v_resetjp_77_;
}
else
{
lean_inc(v_snd_76_);
lean_inc(v_fst_75_);
lean_dec(v_val_71_);
v___x_78_ = lean_box(0);
v_isShared_79_ = v_isSharedCheck_91_;
goto v_resetjp_77_;
}
v_resetjp_77_:
{
lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_83_; 
v___x_80_ = l_Lean_Expr_appArg_x21(v_e_43_);
lean_dec_ref(v_e_43_);
v___x_81_ = lean_array_push(v_snd_76_, v___x_80_);
if (v_isShared_79_ == 0)
{
lean_ctor_set(v___x_78_, 1, v___x_81_);
v___x_83_ = v___x_78_;
goto v_reusejp_82_;
}
else
{
lean_object* v_reuseFailAlloc_90_; 
v_reuseFailAlloc_90_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_90_, 0, v_fst_75_);
lean_ctor_set(v_reuseFailAlloc_90_, 1, v___x_81_);
v___x_83_ = v_reuseFailAlloc_90_;
goto v_reusejp_82_;
}
v_reusejp_82_:
{
lean_object* v___x_85_; 
if (v_isShared_74_ == 0)
{
lean_ctor_set(v___x_73_, 0, v___x_83_);
v___x_85_ = v___x_73_;
goto v_reusejp_84_;
}
else
{
lean_object* v_reuseFailAlloc_89_; 
v_reuseFailAlloc_89_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_89_, 0, v___x_83_);
v___x_85_ = v_reuseFailAlloc_89_;
goto v_reusejp_84_;
}
v_reusejp_84_:
{
lean_object* v___x_87_; 
if (v_isShared_70_ == 0)
{
lean_ctor_set(v___x_69_, 0, v___x_85_);
v___x_87_ = v___x_69_;
goto v_reusejp_86_;
}
else
{
lean_object* v_reuseFailAlloc_88_; 
v_reuseFailAlloc_88_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_88_, 0, v___x_85_);
v___x_87_ = v_reuseFailAlloc_88_;
goto v_reusejp_86_;
}
v_reusejp_86_:
{
return v___x_87_;
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
lean_dec_ref(v_e_43_);
return v___x_66_;
}
}
}
else
{
lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_99_; 
lean_dec_ref(v_pattern_42_);
v___x_95_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_matchPattern_x3f_go_x3f___closed__0));
v___x_96_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_96_, 0, v_e_43_);
lean_ctor_set(v___x_96_, 1, v___x_95_);
v___x_97_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_97_, 0, v___x_96_);
if (v_isShared_58_ == 0)
{
lean_ctor_set(v___x_57_, 0, v___x_97_);
v___x_99_ = v___x_57_;
goto v_reusejp_98_;
}
else
{
lean_object* v_reuseFailAlloc_100_; 
v_reuseFailAlloc_100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_100_, 0, v___x_97_);
v___x_99_ = v_reuseFailAlloc_100_;
goto v_reusejp_98_;
}
v_reusejp_98_:
{
return v___x_99_;
}
}
}
}
else
{
lean_object* v_a_102_; lean_object* v___x_104_; uint8_t v_isShared_105_; uint8_t v_isSharedCheck_109_; 
lean_dec_ref(v_e_43_);
lean_dec_ref(v_pattern_42_);
v_a_102_ = lean_ctor_get(v___x_54_, 0);
v_isSharedCheck_109_ = !lean_is_exclusive(v___x_54_);
if (v_isSharedCheck_109_ == 0)
{
v___x_104_ = v___x_54_;
v_isShared_105_ = v_isSharedCheck_109_;
goto v_resetjp_103_;
}
else
{
lean_inc(v_a_102_);
lean_dec(v___x_54_);
v___x_104_ = lean_box(0);
v_isShared_105_ = v_isSharedCheck_109_;
goto v_resetjp_103_;
}
v_resetjp_103_:
{
lean_object* v___x_107_; 
if (v_isShared_105_ == 0)
{
v___x_107_ = v___x_104_;
goto v_reusejp_106_;
}
else
{
lean_object* v_reuseFailAlloc_108_; 
v_reuseFailAlloc_108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_108_, 0, v_a_102_);
v___x_107_ = v_reuseFailAlloc_108_;
goto v_reusejp_106_;
}
v_reusejp_106_:
{
return v___x_107_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_matchPattern_x3f_go_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_pattern_42_ = stack[0].m_obj;
lean_object* v_e_43_ = stack[1].m_obj;
lean_object* v_a_44_ = stack[2].m_obj;
lean_object* v_a_45_ = stack[3].m_obj;
lean_object* v_a_46_ = stack[4].m_obj;
lean_object* v_a_47_ = stack[5].m_obj;
lean_object* v_res_110_;
v_res_110_ = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_matchPattern_x3f_go_x3f(v_pattern_42_, v_e_43_, v_a_44_, v_a_45_, v_a_46_, v_a_47_);
stack->m_obj
 = v_res_110_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_matchPattern_x3f_go_x3f___boxed(lean_object* v_pattern_111_, lean_object* v_e_112_, lean_object* v_a_113_, lean_object* v_a_114_, lean_object* v_a_115_, lean_object* v_a_116_, lean_object* v_a_117_){
_start:
{
lean_object* v_res_118_; 
v_res_118_ = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_matchPattern_x3f_go_x3f(v_pattern_111_, v_e_112_, v_a_113_, v_a_114_, v_a_115_, v_a_116_);
lean_dec(v_a_116_);
lean_dec_ref(v_a_115_);
lean_dec(v_a_114_);
lean_dec_ref(v_a_113_);
return v_res_118_;
}
}
lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Conv_matchPattern_x3f_spec__0___redArg(lean_object* v_k_119_, uint8_t v_allowLevelAssignments_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_){
_start:
{
lean_object* v___x_126_; 
v___x_126_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_120_, v_k_119_, v___y_121_, v___y_122_, v___y_123_, v___y_124_);
if (lean_obj_tag(v___x_126_) == 0)
{
lean_object* v_a_127_; lean_object* v___x_129_; uint8_t v_isShared_130_; uint8_t v_isSharedCheck_134_; 
v_a_127_ = lean_ctor_get(v___x_126_, 0);
v_isSharedCheck_134_ = !lean_is_exclusive(v___x_126_);
if (v_isSharedCheck_134_ == 0)
{
v___x_129_ = v___x_126_;
v_isShared_130_ = v_isSharedCheck_134_;
goto v_resetjp_128_;
}
else
{
lean_inc(v_a_127_);
lean_dec(v___x_126_);
v___x_129_ = lean_box(0);
v_isShared_130_ = v_isSharedCheck_134_;
goto v_resetjp_128_;
}
v_resetjp_128_:
{
lean_object* v___x_132_; 
if (v_isShared_130_ == 0)
{
v___x_132_ = v___x_129_;
goto v_reusejp_131_;
}
else
{
lean_object* v_reuseFailAlloc_133_; 
v_reuseFailAlloc_133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_133_, 0, v_a_127_);
v___x_132_ = v_reuseFailAlloc_133_;
goto v_reusejp_131_;
}
v_reusejp_131_:
{
return v___x_132_;
}
}
}
else
{
lean_object* v_a_135_; lean_object* v___x_137_; uint8_t v_isShared_138_; uint8_t v_isSharedCheck_142_; 
v_a_135_ = lean_ctor_get(v___x_126_, 0);
v_isSharedCheck_142_ = !lean_is_exclusive(v___x_126_);
if (v_isSharedCheck_142_ == 0)
{
v___x_137_ = v___x_126_;
v_isShared_138_ = v_isSharedCheck_142_;
goto v_resetjp_136_;
}
else
{
lean_inc(v_a_135_);
lean_dec(v___x_126_);
v___x_137_ = lean_box(0);
v_isShared_138_ = v_isSharedCheck_142_;
goto v_resetjp_136_;
}
v_resetjp_136_:
{
lean_object* v___x_140_; 
if (v_isShared_138_ == 0)
{
v___x_140_ = v___x_137_;
goto v_reusejp_139_;
}
else
{
lean_object* v_reuseFailAlloc_141_; 
v_reuseFailAlloc_141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_141_, 0, v_a_135_);
v___x_140_ = v_reuseFailAlloc_141_;
goto v_reusejp_139_;
}
v_reusejp_139_:
{
return v___x_140_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Conv_matchPattern_x3f_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_119_ = stack[0].m_obj;
uint8_t v_allowLevelAssignments_120_ = stack[1].m_num;
lean_object* v___y_121_ = stack[2].m_obj;
lean_object* v___y_122_ = stack[3].m_obj;
lean_object* v___y_123_ = stack[4].m_obj;
lean_object* v___y_124_ = stack[5].m_obj;
lean_object* v_res_143_;
v_res_143_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Conv_matchPattern_x3f_spec__0___redArg(v_k_119_, v_allowLevelAssignments_120_, v___y_121_, v___y_122_, v___y_123_, v___y_124_);
stack->m_obj
 = v_res_143_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Conv_matchPattern_x3f_spec__0___redArg___boxed(lean_object* v_k_144_, lean_object* v_allowLevelAssignments_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_151_; lean_object* v_res_152_; 
v_allowLevelAssignments_boxed_151_ = lean_unbox(v_allowLevelAssignments_145_);
v_res_152_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Conv_matchPattern_x3f_spec__0___redArg(v_k_144_, v_allowLevelAssignments_boxed_151_, v___y_146_, v___y_147_, v___y_148_, v___y_149_);
lean_dec(v___y_149_);
lean_dec_ref(v___y_148_);
lean_dec(v___y_147_);
lean_dec_ref(v___y_146_);
return v_res_152_;
}
}
lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Conv_matchPattern_x3f_spec__0(lean_object* v_00_u03b1_153_, lean_object* v_k_154_, uint8_t v_allowLevelAssignments_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_){
_start:
{
lean_object* v___x_161_; 
v___x_161_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Conv_matchPattern_x3f_spec__0___redArg(v_k_154_, v_allowLevelAssignments_155_, v___y_156_, v___y_157_, v___y_158_, v___y_159_);
return v___x_161_;
}
}
LEAN_EXPORT void l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Conv_matchPattern_x3f_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_154_ = stack[1].m_obj;
uint8_t v_allowLevelAssignments_155_ = stack[2].m_num;
lean_object* v___y_156_ = stack[3].m_obj;
lean_object* v___y_157_ = stack[4].m_obj;
lean_object* v___y_158_ = stack[5].m_obj;
lean_object* v___y_159_ = stack[6].m_obj;
lean_object* v_res_162_;
v_res_162_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Conv_matchPattern_x3f_spec__0(lean_box(0), v_k_154_, v_allowLevelAssignments_155_, v___y_156_, v___y_157_, v___y_158_, v___y_159_);
stack->m_obj
 = v_res_162_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Conv_matchPattern_x3f_spec__0___boxed(lean_object* v_00_u03b1_163_, lean_object* v_k_164_, lean_object* v_allowLevelAssignments_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_171_; lean_object* v_res_172_; 
v_allowLevelAssignments_boxed_171_ = lean_unbox(v_allowLevelAssignments_165_);
v_res_172_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Conv_matchPattern_x3f_spec__0(v_00_u03b1_163_, v_k_164_, v_allowLevelAssignments_boxed_171_, v___y_166_, v___y_167_, v___y_168_, v___y_169_);
lean_dec(v___y_169_);
lean_dec_ref(v___y_168_);
lean_dec(v___y_167_);
lean_dec_ref(v___y_166_);
return v_res_172_;
}
}
lean_object* l_Lean_Elab_Tactic_Conv_matchPattern_x3f___lam__0(lean_object* v_pattern_173_, lean_object* v_e_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_){
_start:
{
lean_object* v___y_181_; lean_object* v___x_198_; 
v___x_198_ = l_Lean_Meta_openAbstractMVarsResult(v_pattern_173_, v___y_175_, v___y_176_, v___y_177_, v___y_178_);
if (lean_obj_tag(v___x_198_) == 0)
{
lean_object* v_a_199_; lean_object* v_snd_200_; lean_object* v_snd_201_; lean_object* v___x_202_; uint8_t v_transparency_203_; uint8_t v___x_204_; uint8_t v___x_205_; 
v_a_199_ = lean_ctor_get(v___x_198_, 0);
lean_inc(v_a_199_);
lean_dec_ref_known(v___x_198_, 1);
v_snd_200_ = lean_ctor_get(v_a_199_, 1);
lean_inc(v_snd_200_);
lean_dec(v_a_199_);
v_snd_201_ = lean_ctor_get(v_snd_200_, 1);
lean_inc(v_snd_201_);
lean_dec(v_snd_200_);
v___x_202_ = l_Lean_Meta_Context_config(v___y_175_);
v_transparency_203_ = lean_ctor_get_uint8(v___x_202_, 9);
lean_dec_ref(v___x_202_);
v___x_204_ = 2;
v___x_205_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_203_, v___x_204_);
if (v___x_205_ == 0)
{
lean_object* v_keyedConfig_206_; uint8_t v_trackZetaDelta_207_; lean_object* v_zetaDeltaSet_208_; lean_object* v_lctx_209_; lean_object* v_localInstances_210_; lean_object* v_defEqCtx_x3f_211_; lean_object* v_synthPendingDepth_212_; lean_object* v_customCanUnfoldPredicate_x3f_213_; uint8_t v_univApprox_214_; uint8_t v_inTypeClassResolution_215_; uint8_t v_cacheInferType_216_; lean_object* v___x_218_; uint8_t v_isShared_219_; uint8_t v_isSharedCheck_225_; 
v_keyedConfig_206_ = lean_ctor_get(v___y_175_, 0);
v_trackZetaDelta_207_ = lean_ctor_get_uint8(v___y_175_, sizeof(void*)*7);
v_zetaDeltaSet_208_ = lean_ctor_get(v___y_175_, 1);
v_lctx_209_ = lean_ctor_get(v___y_175_, 2);
v_localInstances_210_ = lean_ctor_get(v___y_175_, 3);
v_defEqCtx_x3f_211_ = lean_ctor_get(v___y_175_, 4);
v_synthPendingDepth_212_ = lean_ctor_get(v___y_175_, 5);
v_customCanUnfoldPredicate_x3f_213_ = lean_ctor_get(v___y_175_, 6);
v_univApprox_214_ = lean_ctor_get_uint8(v___y_175_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_215_ = lean_ctor_get_uint8(v___y_175_, sizeof(void*)*7 + 2);
v_cacheInferType_216_ = lean_ctor_get_uint8(v___y_175_, sizeof(void*)*7 + 3);
v_isSharedCheck_225_ = !lean_is_exclusive(v___y_175_);
if (v_isSharedCheck_225_ == 0)
{
v___x_218_ = v___y_175_;
v_isShared_219_ = v_isSharedCheck_225_;
goto v_resetjp_217_;
}
else
{
lean_inc(v_customCanUnfoldPredicate_x3f_213_);
lean_inc(v_synthPendingDepth_212_);
lean_inc(v_defEqCtx_x3f_211_);
lean_inc(v_localInstances_210_);
lean_inc(v_lctx_209_);
lean_inc(v_zetaDeltaSet_208_);
lean_inc(v_keyedConfig_206_);
lean_dec(v___y_175_);
v___x_218_ = lean_box(0);
v_isShared_219_ = v_isSharedCheck_225_;
goto v_resetjp_217_;
}
v_resetjp_217_:
{
lean_object* v___x_220_; lean_object* v___x_222_; 
v___x_220_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_204_, v_keyedConfig_206_);
if (v_isShared_219_ == 0)
{
lean_ctor_set(v___x_218_, 0, v___x_220_);
v___x_222_ = v___x_218_;
goto v_reusejp_221_;
}
else
{
lean_object* v_reuseFailAlloc_224_; 
v_reuseFailAlloc_224_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_224_, 0, v___x_220_);
lean_ctor_set(v_reuseFailAlloc_224_, 1, v_zetaDeltaSet_208_);
lean_ctor_set(v_reuseFailAlloc_224_, 2, v_lctx_209_);
lean_ctor_set(v_reuseFailAlloc_224_, 3, v_localInstances_210_);
lean_ctor_set(v_reuseFailAlloc_224_, 4, v_defEqCtx_x3f_211_);
lean_ctor_set(v_reuseFailAlloc_224_, 5, v_synthPendingDepth_212_);
lean_ctor_set(v_reuseFailAlloc_224_, 6, v_customCanUnfoldPredicate_x3f_213_);
lean_ctor_set_uint8(v_reuseFailAlloc_224_, sizeof(void*)*7, v_trackZetaDelta_207_);
lean_ctor_set_uint8(v_reuseFailAlloc_224_, sizeof(void*)*7 + 1, v_univApprox_214_);
lean_ctor_set_uint8(v_reuseFailAlloc_224_, sizeof(void*)*7 + 2, v_inTypeClassResolution_215_);
lean_ctor_set_uint8(v_reuseFailAlloc_224_, sizeof(void*)*7 + 3, v_cacheInferType_216_);
v___x_222_ = v_reuseFailAlloc_224_;
goto v_reusejp_221_;
}
v_reusejp_221_:
{
lean_object* v___x_223_; 
v___x_223_ = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_matchPattern_x3f_go_x3f(v_snd_201_, v_e_174_, v___x_222_, v___y_176_, v___y_177_, v___y_178_);
lean_dec_ref(v___x_222_);
v___y_181_ = v___x_223_;
goto v___jp_180_;
}
}
}
else
{
lean_object* v___x_226_; 
v___x_226_ = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_matchPattern_x3f_go_x3f(v_snd_201_, v_e_174_, v___y_175_, v___y_176_, v___y_177_, v___y_178_);
lean_dec_ref(v___y_175_);
v___y_181_ = v___x_226_;
goto v___jp_180_;
}
}
else
{
lean_object* v_a_227_; lean_object* v___x_229_; uint8_t v_isShared_230_; uint8_t v_isSharedCheck_234_; 
lean_dec_ref(v___y_175_);
lean_dec_ref(v_e_174_);
v_a_227_ = lean_ctor_get(v___x_198_, 0);
v_isSharedCheck_234_ = !lean_is_exclusive(v___x_198_);
if (v_isSharedCheck_234_ == 0)
{
v___x_229_ = v___x_198_;
v_isShared_230_ = v_isSharedCheck_234_;
goto v_resetjp_228_;
}
else
{
lean_inc(v_a_227_);
lean_dec(v___x_198_);
v___x_229_ = lean_box(0);
v_isShared_230_ = v_isSharedCheck_234_;
goto v_resetjp_228_;
}
v_resetjp_228_:
{
lean_object* v___x_232_; 
if (v_isShared_230_ == 0)
{
v___x_232_ = v___x_229_;
goto v_reusejp_231_;
}
else
{
lean_object* v_reuseFailAlloc_233_; 
v_reuseFailAlloc_233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_233_, 0, v_a_227_);
v___x_232_ = v_reuseFailAlloc_233_;
goto v_reusejp_231_;
}
v_reusejp_231_:
{
return v___x_232_;
}
}
}
v___jp_180_:
{
if (lean_obj_tag(v___y_181_) == 0)
{
lean_object* v_a_182_; lean_object* v___x_184_; uint8_t v_isShared_185_; uint8_t v_isSharedCheck_189_; 
v_a_182_ = lean_ctor_get(v___y_181_, 0);
v_isSharedCheck_189_ = !lean_is_exclusive(v___y_181_);
if (v_isSharedCheck_189_ == 0)
{
v___x_184_ = v___y_181_;
v_isShared_185_ = v_isSharedCheck_189_;
goto v_resetjp_183_;
}
else
{
lean_inc(v_a_182_);
lean_dec(v___y_181_);
v___x_184_ = lean_box(0);
v_isShared_185_ = v_isSharedCheck_189_;
goto v_resetjp_183_;
}
v_resetjp_183_:
{
lean_object* v___x_187_; 
if (v_isShared_185_ == 0)
{
v___x_187_ = v___x_184_;
goto v_reusejp_186_;
}
else
{
lean_object* v_reuseFailAlloc_188_; 
v_reuseFailAlloc_188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_188_, 0, v_a_182_);
v___x_187_ = v_reuseFailAlloc_188_;
goto v_reusejp_186_;
}
v_reusejp_186_:
{
return v___x_187_;
}
}
}
else
{
lean_object* v_a_190_; lean_object* v___x_192_; uint8_t v_isShared_193_; uint8_t v_isSharedCheck_197_; 
v_a_190_ = lean_ctor_get(v___y_181_, 0);
v_isSharedCheck_197_ = !lean_is_exclusive(v___y_181_);
if (v_isSharedCheck_197_ == 0)
{
v___x_192_ = v___y_181_;
v_isShared_193_ = v_isSharedCheck_197_;
goto v_resetjp_191_;
}
else
{
lean_inc(v_a_190_);
lean_dec(v___y_181_);
v___x_192_ = lean_box(0);
v_isShared_193_ = v_isSharedCheck_197_;
goto v_resetjp_191_;
}
v_resetjp_191_:
{
lean_object* v___x_195_; 
if (v_isShared_193_ == 0)
{
v___x_195_ = v___x_192_;
goto v_reusejp_194_;
}
else
{
lean_object* v_reuseFailAlloc_196_; 
v_reuseFailAlloc_196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_196_, 0, v_a_190_);
v___x_195_ = v_reuseFailAlloc_196_;
goto v_reusejp_194_;
}
v_reusejp_194_:
{
return v___x_195_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Conv_matchPattern_x3f___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_pattern_173_ = stack[0].m_obj;
lean_object* v_e_174_ = stack[1].m_obj;
lean_object* v___y_175_ = stack[2].m_obj;
lean_object* v___y_176_ = stack[3].m_obj;
lean_object* v___y_177_ = stack[4].m_obj;
lean_object* v___y_178_ = stack[5].m_obj;
lean_object* v_res_235_;
v_res_235_ = l_Lean_Elab_Tactic_Conv_matchPattern_x3f___lam__0(v_pattern_173_, v_e_174_, v___y_175_, v___y_176_, v___y_177_, v___y_178_);
stack->m_obj
 = v_res_235_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_matchPattern_x3f___lam__0___boxed(lean_object* v_pattern_236_, lean_object* v_e_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_){
_start:
{
lean_object* v_res_243_; 
v_res_243_ = l_Lean_Elab_Tactic_Conv_matchPattern_x3f___lam__0(v_pattern_236_, v_e_237_, v___y_238_, v___y_239_, v___y_240_, v___y_241_);
lean_dec(v___y_241_);
lean_dec_ref(v___y_240_);
lean_dec(v___y_239_);
return v_res_243_;
}
}
lean_object* l_Lean_Elab_Tactic_Conv_matchPattern_x3f(lean_object* v_pattern_244_, lean_object* v_e_245_, lean_object* v_a_246_, lean_object* v_a_247_, lean_object* v_a_248_, lean_object* v_a_249_){
_start:
{
lean_object* v___f_251_; uint8_t v___x_252_; lean_object* v___x_253_; 
v___f_251_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_matchPattern_x3f___lam__0___boxed), 7, 2);
lean_closure_set(v___f_251_, 0, v_pattern_244_);
lean_closure_set(v___f_251_, 1, v_e_245_);
v___x_252_ = 0;
v___x_253_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Conv_matchPattern_x3f_spec__0___redArg(v___f_251_, v___x_252_, v_a_246_, v_a_247_, v_a_248_, v_a_249_);
return v___x_253_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Conv_matchPattern_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_pattern_244_ = stack[0].m_obj;
lean_object* v_e_245_ = stack[1].m_obj;
lean_object* v_a_246_ = stack[2].m_obj;
lean_object* v_a_247_ = stack[3].m_obj;
lean_object* v_a_248_ = stack[4].m_obj;
lean_object* v_a_249_ = stack[5].m_obj;
lean_object* v_res_254_;
v_res_254_ = l_Lean_Elab_Tactic_Conv_matchPattern_x3f(v_pattern_244_, v_e_245_, v_a_246_, v_a_247_, v_a_248_, v_a_249_);
stack->m_obj
 = v_res_254_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_matchPattern_x3f___boxed(lean_object* v_pattern_255_, lean_object* v_e_256_, lean_object* v_a_257_, lean_object* v_a_258_, lean_object* v_a_259_, lean_object* v_a_260_, lean_object* v_a_261_){
_start:
{
lean_object* v_res_262_; 
v_res_262_ = l_Lean_Elab_Tactic_Conv_matchPattern_x3f(v_pattern_255_, v_e_256_, v_a_257_, v_a_258_, v_a_259_, v_a_260_);
lean_dec(v_a_260_);
lean_dec_ref(v_a_259_);
lean_dec(v_a_258_);
lean_dec_ref(v_a_257_);
return v_res_262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorIdx___impl(lean_object* v_x_263_){
_start:
{
lean_object* v___x_264_; 
v___x_264_ = lean_obj_tag_nat(v_x_263_);
return v___x_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorIdx___impl___boxed(lean_object* v_x_265_){
_start:
{
lean_object* v_res_266_; 
v_res_266_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorIdx___impl(v_x_265_);
lean_dec_ref(v_x_265_);
return v_res_266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorElim___redArg(lean_object* v_t_267_, lean_object* v_k_268_){
_start:
{
if (lean_obj_tag(v_t_267_) == 0)
{
lean_object* v_subgoals_269_; lean_object* v___x_270_; 
v_subgoals_269_ = lean_ctor_get(v_t_267_, 0);
lean_inc_ref(v_subgoals_269_);
lean_dec_ref_known(v_t_267_, 1);
v___x_270_ = lean_apply_1(v_k_268_, v_subgoals_269_);
return v___x_270_;
}
else
{
lean_object* v_subgoals_271_; lean_object* v_idx_272_; lean_object* v_remaining_273_; lean_object* v___x_274_; 
v_subgoals_271_ = lean_ctor_get(v_t_267_, 0);
lean_inc_ref(v_subgoals_271_);
v_idx_272_ = lean_ctor_get(v_t_267_, 1);
lean_inc(v_idx_272_);
v_remaining_273_ = lean_ctor_get(v_t_267_, 2);
lean_inc(v_remaining_273_);
lean_dec_ref_known(v_t_267_, 3);
v___x_274_ = lean_apply_3(v_k_268_, v_subgoals_271_, v_idx_272_, v_remaining_273_);
return v___x_274_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorElim(lean_object* v_motive_275_, lean_object* v_ctorIdx_276_, lean_object* v_t_277_, lean_object* v_h_278_, lean_object* v_k_279_){
_start:
{
lean_object* v___x_280_; 
v___x_280_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorElim___redArg(v_t_277_, v_k_279_);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorElim___boxed(lean_object* v_motive_281_, lean_object* v_ctorIdx_282_, lean_object* v_t_283_, lean_object* v_h_284_, lean_object* v_k_285_){
_start:
{
lean_object* v_res_286_; 
v_res_286_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorElim(v_motive_281_, v_ctorIdx_282_, v_t_283_, v_h_284_, v_k_285_);
lean_dec(v_ctorIdx_282_);
return v_res_286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_all_elim___redArg(lean_object* v_t_287_, lean_object* v_all_288_){
_start:
{
lean_object* v___x_289_; 
v___x_289_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorElim___redArg(v_t_287_, v_all_288_);
return v___x_289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_all_elim(lean_object* v_motive_290_, lean_object* v_t_291_, lean_object* v_h_292_, lean_object* v_all_293_){
_start:
{
lean_object* v___x_294_; 
v___x_294_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorElim___redArg(v_t_291_, v_all_293_);
return v___x_294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_occs_elim___redArg(lean_object* v_t_295_, lean_object* v_occs_296_){
_start:
{
lean_object* v___x_297_; 
v___x_297_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorElim___redArg(v_t_295_, v_occs_296_);
return v___x_297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_occs_elim(lean_object* v_motive_298_, lean_object* v_t_299_, lean_object* v_h_300_, lean_object* v_occs_301_){
_start:
{
lean_object* v___x_302_; 
v___x_302_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorElim___redArg(v_t_299_, v_occs_301_);
return v___x_302_;
}
}
uint8_t l_Lean_Elab_Tactic_Conv_PatternMatchState_isDone(lean_object* v_x_303_){
_start:
{
if (lean_obj_tag(v_x_303_) == 0)
{
uint8_t v___x_304_; 
v___x_304_ = 0;
return v___x_304_;
}
else
{
lean_object* v_remaining_305_; uint8_t v___x_306_; 
v_remaining_305_ = lean_ctor_get(v_x_303_, 2);
v___x_306_ = l_List_isEmpty___redArg(v_remaining_305_);
return v___x_306_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Conv_PatternMatchState_isDone_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_303_ = stack[0].m_obj;
uint8_t v_res_307_;
v_res_307_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_isDone(v_x_303_);
stack->m_num = v_res_307_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_isDone___boxed(lean_object* v_x_308_){
_start:
{
uint8_t v_res_309_; lean_object* v_r_310_; 
v_res_309_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_isDone(v_x_308_);
lean_dec_ref(v_x_308_);
v_r_310_ = lean_box(v_res_309_);
return v_r_310_;
}
}
uint8_t l_Lean_Elab_Tactic_Conv_PatternMatchState_isReady(lean_object* v_x_311_){
_start:
{
if (lean_obj_tag(v_x_311_) == 0)
{
uint8_t v___x_312_; 
v___x_312_ = 1;
return v___x_312_;
}
else
{
lean_object* v_remaining_313_; 
v_remaining_313_ = lean_ctor_get(v_x_311_, 2);
if (lean_obj_tag(v_remaining_313_) == 1)
{
lean_object* v_head_314_; lean_object* v_idx_315_; lean_object* v_fst_316_; uint8_t v___x_317_; 
v_head_314_ = lean_ctor_get(v_remaining_313_, 0);
v_idx_315_ = lean_ctor_get(v_x_311_, 1);
v_fst_316_ = lean_ctor_get(v_head_314_, 0);
v___x_317_ = lean_nat_dec_eq(v_idx_315_, v_fst_316_);
return v___x_317_;
}
else
{
uint8_t v___x_318_; 
v___x_318_ = 0;
return v___x_318_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Conv_PatternMatchState_isReady_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_311_ = stack[0].m_obj;
uint8_t v_res_319_;
v_res_319_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_isReady(v_x_311_);
stack->m_num = v_res_319_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_isReady___boxed(lean_object* v_x_320_){
_start:
{
uint8_t v_res_321_; lean_object* v_r_322_; 
v_res_321_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_isReady(v_x_320_);
lean_dec_ref(v_x_320_);
v_r_322_ = lean_box(v_res_321_);
return v_r_322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_skip(lean_object* v_x_323_){
_start:
{
if (lean_obj_tag(v_x_323_) == 1)
{
lean_object* v_subgoals_324_; lean_object* v_idx_325_; lean_object* v_remaining_326_; lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_335_; 
v_subgoals_324_ = lean_ctor_get(v_x_323_, 0);
v_idx_325_ = lean_ctor_get(v_x_323_, 1);
v_remaining_326_ = lean_ctor_get(v_x_323_, 2);
v_isSharedCheck_335_ = !lean_is_exclusive(v_x_323_);
if (v_isSharedCheck_335_ == 0)
{
v___x_328_ = v_x_323_;
v_isShared_329_ = v_isSharedCheck_335_;
goto v_resetjp_327_;
}
else
{
lean_inc(v_remaining_326_);
lean_inc(v_idx_325_);
lean_inc(v_subgoals_324_);
lean_dec(v_x_323_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_335_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_333_; 
v___x_330_ = lean_unsigned_to_nat(1u);
v___x_331_ = lean_nat_add(v_idx_325_, v___x_330_);
lean_dec(v_idx_325_);
if (v_isShared_329_ == 0)
{
lean_ctor_set(v___x_328_, 1, v___x_331_);
v___x_333_ = v___x_328_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v_subgoals_324_);
lean_ctor_set(v_reuseFailAlloc_334_, 1, v___x_331_);
lean_ctor_set(v_reuseFailAlloc_334_, 2, v_remaining_326_);
v___x_333_ = v_reuseFailAlloc_334_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
return v___x_333_;
}
}
}
else
{
return v_x_323_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_accept(lean_object* v_mvarId_336_, lean_object* v_x_337_){
_start:
{
if (lean_obj_tag(v_x_337_) == 0)
{
lean_object* v_subgoals_338_; lean_object* v___x_340_; uint8_t v_isShared_341_; uint8_t v_isSharedCheck_346_; 
v_subgoals_338_ = lean_ctor_get(v_x_337_, 0);
v_isSharedCheck_346_ = !lean_is_exclusive(v_x_337_);
if (v_isSharedCheck_346_ == 0)
{
v___x_340_ = v_x_337_;
v_isShared_341_ = v_isSharedCheck_346_;
goto v_resetjp_339_;
}
else
{
lean_inc(v_subgoals_338_);
lean_dec(v_x_337_);
v___x_340_ = lean_box(0);
v_isShared_341_ = v_isSharedCheck_346_;
goto v_resetjp_339_;
}
v_resetjp_339_:
{
lean_object* v___x_342_; lean_object* v___x_344_; 
v___x_342_ = lean_array_push(v_subgoals_338_, v_mvarId_336_);
if (v_isShared_341_ == 0)
{
lean_ctor_set(v___x_340_, 0, v___x_342_);
v___x_344_ = v___x_340_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v___x_342_);
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
lean_object* v_remaining_347_; 
v_remaining_347_ = lean_ctor_get(v_x_337_, 2);
if (lean_obj_tag(v_remaining_347_) == 1)
{
lean_object* v_head_348_; lean_object* v_subgoals_349_; lean_object* v_idx_350_; lean_object* v___x_352_; uint8_t v_isShared_353_; uint8_t v_isSharedCheck_370_; 
lean_inc_ref(v_remaining_347_);
v_head_348_ = lean_ctor_get(v_remaining_347_, 0);
lean_inc(v_head_348_);
v_subgoals_349_ = lean_ctor_get(v_x_337_, 0);
v_idx_350_ = lean_ctor_get(v_x_337_, 1);
v_isSharedCheck_370_ = !lean_is_exclusive(v_x_337_);
if (v_isSharedCheck_370_ == 0)
{
lean_object* v_unused_371_; 
v_unused_371_ = lean_ctor_get(v_x_337_, 2);
lean_dec(v_unused_371_);
v___x_352_ = v_x_337_;
v_isShared_353_ = v_isSharedCheck_370_;
goto v_resetjp_351_;
}
else
{
lean_inc(v_idx_350_);
lean_inc(v_subgoals_349_);
lean_dec(v_x_337_);
v___x_352_ = lean_box(0);
v_isShared_353_ = v_isSharedCheck_370_;
goto v_resetjp_351_;
}
v_resetjp_351_:
{
lean_object* v_tail_354_; lean_object* v_snd_355_; lean_object* v___x_357_; uint8_t v_isShared_358_; uint8_t v_isSharedCheck_368_; 
v_tail_354_ = lean_ctor_get(v_remaining_347_, 1);
lean_inc(v_tail_354_);
lean_dec_ref_known(v_remaining_347_, 2);
v_snd_355_ = lean_ctor_get(v_head_348_, 1);
v_isSharedCheck_368_ = !lean_is_exclusive(v_head_348_);
if (v_isSharedCheck_368_ == 0)
{
lean_object* v_unused_369_; 
v_unused_369_ = lean_ctor_get(v_head_348_, 0);
lean_dec(v_unused_369_);
v___x_357_ = v_head_348_;
v_isShared_358_ = v_isSharedCheck_368_;
goto v_resetjp_356_;
}
else
{
lean_inc(v_snd_355_);
lean_dec(v_head_348_);
v___x_357_ = lean_box(0);
v_isShared_358_ = v_isSharedCheck_368_;
goto v_resetjp_356_;
}
v_resetjp_356_:
{
lean_object* v___x_360_; 
if (v_isShared_358_ == 0)
{
lean_ctor_set(v___x_357_, 1, v_mvarId_336_);
lean_ctor_set(v___x_357_, 0, v_snd_355_);
v___x_360_ = v___x_357_;
goto v_reusejp_359_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v_snd_355_);
lean_ctor_set(v_reuseFailAlloc_367_, 1, v_mvarId_336_);
v___x_360_ = v_reuseFailAlloc_367_;
goto v_reusejp_359_;
}
v_reusejp_359_:
{
lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_365_; 
v___x_361_ = lean_array_push(v_subgoals_349_, v___x_360_);
v___x_362_ = lean_unsigned_to_nat(1u);
v___x_363_ = lean_nat_add(v_idx_350_, v___x_362_);
lean_dec(v_idx_350_);
if (v_isShared_353_ == 0)
{
lean_ctor_set(v___x_352_, 2, v_tail_354_);
lean_ctor_set(v___x_352_, 1, v___x_363_);
lean_ctor_set(v___x_352_, 0, v___x_361_);
v___x_365_ = v___x_352_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v___x_361_);
lean_ctor_set(v_reuseFailAlloc_366_, 1, v___x_363_);
lean_ctor_set(v_reuseFailAlloc_366_, 2, v_tail_354_);
v___x_365_ = v_reuseFailAlloc_366_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
return v___x_365_;
}
}
}
}
}
else
{
lean_dec(v_mvarId_336_);
return v_x_337_;
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre_spec__0___redArg(lean_object* v_as_372_, size_t v_sz_373_, size_t v_i_374_, lean_object* v_b_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_){
_start:
{
uint8_t v___x_381_; 
v___x_381_ = lean_usize_dec_lt(v_i_374_, v_sz_373_);
if (v___x_381_ == 0)
{
lean_object* v___x_382_; 
v___x_382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_382_, 0, v_b_375_);
return v___x_382_;
}
else
{
lean_object* v_a_383_; lean_object* v___x_384_; 
v_a_383_ = lean_array_uget_borrowed(v_as_372_, v_i_374_);
lean_inc(v_a_383_);
v___x_384_ = l_Lean_Meta_mkCongrFun(v_b_375_, v_a_383_, v___y_376_, v___y_377_, v___y_378_, v___y_379_);
if (lean_obj_tag(v___x_384_) == 0)
{
lean_object* v_a_385_; size_t v___x_386_; size_t v___x_387_; 
v_a_385_ = lean_ctor_get(v___x_384_, 0);
lean_inc(v_a_385_);
lean_dec_ref_known(v___x_384_, 1);
v___x_386_ = ((size_t)1ULL);
v___x_387_ = lean_usize_add(v_i_374_, v___x_386_);
v_i_374_ = v___x_387_;
v_b_375_ = v_a_385_;
goto _start;
}
else
{
return v___x_384_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_372_ = stack[0].m_obj;
size_t v_sz_373_ = stack[1].m_num;
size_t v_i_374_ = stack[2].m_num;
lean_object* v_b_375_ = stack[3].m_obj;
lean_object* v___y_376_ = stack[4].m_obj;
lean_object* v___y_377_ = stack[5].m_obj;
lean_object* v___y_378_ = stack[6].m_obj;
lean_object* v___y_379_ = stack[7].m_obj;
lean_object* v_res_389_;
v_res_389_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre_spec__0___redArg(v_as_372_, v_sz_373_, v_i_374_, v_b_375_, v___y_376_, v___y_377_, v___y_378_, v___y_379_);
stack->m_obj
 = v_res_389_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre_spec__0___redArg___boxed(lean_object* v_as_390_, lean_object* v_sz_391_, lean_object* v_i_392_, lean_object* v_b_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_){
_start:
{
size_t v_sz_boxed_399_; size_t v_i_boxed_400_; lean_object* v_res_401_; 
v_sz_boxed_399_ = lean_unbox_usize(v_sz_391_);
lean_dec(v_sz_391_);
v_i_boxed_400_ = lean_unbox_usize(v_i_392_);
lean_dec(v_i_392_);
v_res_401_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre_spec__0___redArg(v_as_390_, v_sz_boxed_399_, v_i_boxed_400_, v_b_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_);
lean_dec(v___y_397_);
lean_dec_ref(v___y_396_);
lean_dec(v___y_395_);
lean_dec_ref(v___y_394_);
lean_dec_ref(v_as_390_);
return v_res_401_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre(lean_object* v_pattern_404_, lean_object* v_state_405_, lean_object* v_e_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_){
_start:
{
lean_object* v___x_415_; uint8_t v___x_416_; uint8_t v___x_417_; 
v___x_415_ = lean_st_ref_get(v_state_405_);
v___x_416_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_isDone(v___x_415_);
lean_dec(v___x_415_);
v___x_417_ = 1;
if (v___x_416_ == 0)
{
lean_object* v___x_418_; 
v___x_418_ = l_Lean_Elab_Tactic_Conv_matchPattern_x3f(v_pattern_404_, v_e_406_, v_a_410_, v_a_411_, v_a_412_, v_a_413_);
if (lean_obj_tag(v___x_418_) == 0)
{
lean_object* v_a_419_; lean_object* v___x_421_; uint8_t v_isShared_422_; uint8_t v_isSharedCheck_485_; 
v_a_419_ = lean_ctor_get(v___x_418_, 0);
v_isSharedCheck_485_ = !lean_is_exclusive(v___x_418_);
if (v_isSharedCheck_485_ == 0)
{
v___x_421_ = v___x_418_;
v_isShared_422_ = v_isSharedCheck_485_;
goto v_resetjp_420_;
}
else
{
lean_inc(v_a_419_);
lean_dec(v___x_418_);
v___x_421_ = lean_box(0);
v_isShared_422_ = v_isSharedCheck_485_;
goto v_resetjp_420_;
}
v_resetjp_420_:
{
if (lean_obj_tag(v_a_419_) == 1)
{
lean_object* v_val_423_; lean_object* v___x_425_; uint8_t v_isShared_426_; uint8_t v_isSharedCheck_480_; 
v_val_423_ = lean_ctor_get(v_a_419_, 0);
v_isSharedCheck_480_ = !lean_is_exclusive(v_a_419_);
if (v_isSharedCheck_480_ == 0)
{
v___x_425_ = v_a_419_;
v_isShared_426_ = v_isSharedCheck_480_;
goto v_resetjp_424_;
}
else
{
lean_inc(v_val_423_);
lean_dec(v_a_419_);
v___x_425_ = lean_box(0);
v_isShared_426_ = v_isSharedCheck_480_;
goto v_resetjp_424_;
}
v_resetjp_424_:
{
lean_object* v_fst_427_; lean_object* v_snd_428_; lean_object* v___x_429_; uint8_t v___x_430_; 
v_fst_427_ = lean_ctor_get(v_val_423_, 0);
lean_inc(v_fst_427_);
v_snd_428_ = lean_ctor_get(v_val_423_, 1);
lean_inc(v_snd_428_);
lean_dec(v_val_423_);
v___x_429_ = lean_st_ref_get(v_state_405_);
v___x_430_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_isReady(v___x_429_);
lean_dec(v___x_429_);
if (v___x_430_ == 0)
{
lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_436_; 
lean_dec(v_snd_428_);
lean_dec(v_fst_427_);
lean_del_object(v___x_425_);
v___x_431_ = lean_st_ref_take(v_state_405_);
v___x_432_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_skip(v___x_431_);
v___x_433_ = lean_st_ref_put(v_state_405_, v___x_432_);
v___x_434_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre___closed__0));
if (v_isShared_422_ == 0)
{
lean_ctor_set(v___x_421_, 0, v___x_434_);
v___x_436_ = v___x_421_;
goto v_reusejp_435_;
}
else
{
lean_object* v_reuseFailAlloc_437_; 
v_reuseFailAlloc_437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_437_, 0, v___x_434_);
v___x_436_ = v_reuseFailAlloc_437_;
goto v_reusejp_435_;
}
v_reusejp_435_:
{
return v___x_436_;
}
}
else
{
lean_object* v___x_438_; lean_object* v___x_439_; 
lean_del_object(v___x_421_);
v___x_438_ = lean_box(0);
v___x_439_ = l_Lean_Elab_Tactic_Conv_mkConvGoalFor(v_fst_427_, v___x_438_, v_a_410_, v_a_411_, v_a_412_, v_a_413_);
if (lean_obj_tag(v___x_439_) == 0)
{
lean_object* v_a_440_; lean_object* v_fst_441_; lean_object* v_snd_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; size_t v_sz_447_; size_t v___x_448_; lean_object* v___x_449_; 
v_a_440_ = lean_ctor_get(v___x_439_, 0);
lean_inc(v_a_440_);
lean_dec_ref_known(v___x_439_, 1);
v_fst_441_ = lean_ctor_get(v_a_440_, 0);
lean_inc(v_fst_441_);
v_snd_442_ = lean_ctor_get(v_a_440_, 1);
lean_inc(v_snd_442_);
lean_dec(v_a_440_);
v___x_443_ = lean_st_ref_take(v_state_405_);
v___x_444_ = l_Lean_Expr_mvarId_x21(v_snd_442_);
v___x_445_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_accept(v___x_444_, v___x_443_);
v___x_446_ = lean_st_ref_put(v_state_405_, v___x_445_);
v_sz_447_ = lean_array_size(v_snd_428_);
v___x_448_ = ((size_t)0ULL);
v___x_449_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre_spec__0___redArg(v_snd_428_, v_sz_447_, v___x_448_, v_snd_442_, v_a_410_, v_a_411_, v_a_412_, v_a_413_);
if (lean_obj_tag(v___x_449_) == 0)
{
lean_object* v_a_450_; lean_object* v___x_452_; uint8_t v_isShared_453_; uint8_t v_isSharedCheck_463_; 
v_a_450_ = lean_ctor_get(v___x_449_, 0);
v_isSharedCheck_463_ = !lean_is_exclusive(v___x_449_);
if (v_isSharedCheck_463_ == 0)
{
v___x_452_ = v___x_449_;
v_isShared_453_ = v_isSharedCheck_463_;
goto v_resetjp_451_;
}
else
{
lean_inc(v_a_450_);
lean_dec(v___x_449_);
v___x_452_ = lean_box(0);
v_isShared_453_ = v_isSharedCheck_463_;
goto v_resetjp_451_;
}
v_resetjp_451_:
{
lean_object* v___x_454_; lean_object* v___x_456_; 
v___x_454_ = l_Lean_mkAppN(v_fst_441_, v_snd_428_);
lean_dec(v_snd_428_);
if (v_isShared_426_ == 0)
{
lean_ctor_set(v___x_425_, 0, v_a_450_);
v___x_456_ = v___x_425_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_462_; 
v_reuseFailAlloc_462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_462_, 0, v_a_450_);
v___x_456_ = v_reuseFailAlloc_462_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_460_; 
v___x_457_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_457_, 0, v___x_454_);
lean_ctor_set(v___x_457_, 1, v___x_456_);
lean_ctor_set_uint8(v___x_457_, sizeof(void*)*2, v___x_417_);
v___x_458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_458_, 0, v___x_457_);
if (v_isShared_453_ == 0)
{
lean_ctor_set(v___x_452_, 0, v___x_458_);
v___x_460_ = v___x_452_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v___x_458_);
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
lean_object* v_a_464_; lean_object* v___x_466_; uint8_t v_isShared_467_; uint8_t v_isSharedCheck_471_; 
lean_dec(v_fst_441_);
lean_dec(v_snd_428_);
lean_del_object(v___x_425_);
v_a_464_ = lean_ctor_get(v___x_449_, 0);
v_isSharedCheck_471_ = !lean_is_exclusive(v___x_449_);
if (v_isSharedCheck_471_ == 0)
{
v___x_466_ = v___x_449_;
v_isShared_467_ = v_isSharedCheck_471_;
goto v_resetjp_465_;
}
else
{
lean_inc(v_a_464_);
lean_dec(v___x_449_);
v___x_466_ = lean_box(0);
v_isShared_467_ = v_isSharedCheck_471_;
goto v_resetjp_465_;
}
v_resetjp_465_:
{
lean_object* v___x_469_; 
if (v_isShared_467_ == 0)
{
v___x_469_ = v___x_466_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v_a_464_);
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
lean_object* v_a_472_; lean_object* v___x_474_; uint8_t v_isShared_475_; uint8_t v_isSharedCheck_479_; 
lean_dec(v_snd_428_);
lean_del_object(v___x_425_);
v_a_472_ = lean_ctor_get(v___x_439_, 0);
v_isSharedCheck_479_ = !lean_is_exclusive(v___x_439_);
if (v_isSharedCheck_479_ == 0)
{
v___x_474_ = v___x_439_;
v_isShared_475_ = v_isSharedCheck_479_;
goto v_resetjp_473_;
}
else
{
lean_inc(v_a_472_);
lean_dec(v___x_439_);
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
}
}
else
{
lean_object* v___x_481_; lean_object* v___x_483_; 
lean_dec(v_a_419_);
v___x_481_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre___closed__0));
if (v_isShared_422_ == 0)
{
lean_ctor_set(v___x_421_, 0, v___x_481_);
v___x_483_ = v___x_421_;
goto v_reusejp_482_;
}
else
{
lean_object* v_reuseFailAlloc_484_; 
v_reuseFailAlloc_484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_484_, 0, v___x_481_);
v___x_483_ = v_reuseFailAlloc_484_;
goto v_reusejp_482_;
}
v_reusejp_482_:
{
return v___x_483_;
}
}
}
}
else
{
lean_object* v_a_486_; lean_object* v___x_488_; uint8_t v_isShared_489_; uint8_t v_isSharedCheck_493_; 
v_a_486_ = lean_ctor_get(v___x_418_, 0);
v_isSharedCheck_493_ = !lean_is_exclusive(v___x_418_);
if (v_isSharedCheck_493_ == 0)
{
v___x_488_ = v___x_418_;
v_isShared_489_ = v_isSharedCheck_493_;
goto v_resetjp_487_;
}
else
{
lean_inc(v_a_486_);
lean_dec(v___x_418_);
v___x_488_ = lean_box(0);
v_isShared_489_ = v_isSharedCheck_493_;
goto v_resetjp_487_;
}
v_resetjp_487_:
{
lean_object* v___x_491_; 
if (v_isShared_489_ == 0)
{
v___x_491_ = v___x_488_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v_a_486_);
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
lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; 
lean_dec_ref(v_pattern_404_);
v___x_494_ = lean_box(0);
v___x_495_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_495_, 0, v_e_406_);
lean_ctor_set(v___x_495_, 1, v___x_494_);
lean_ctor_set_uint8(v___x_495_, sizeof(void*)*2, v___x_417_);
v___x_496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_496_, 0, v___x_495_);
v___x_497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_497_, 0, v___x_496_);
return v___x_497_;
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre_0interp(lean_interpreter_value* stack)
{
lean_object* v_pattern_404_ = stack[0].m_obj;
lean_object* v_state_405_ = stack[1].m_obj;
lean_object* v_e_406_ = stack[2].m_obj;
lean_object* v_a_407_ = stack[3].m_obj;
lean_object* v_a_408_ = stack[4].m_obj;
lean_object* v_a_409_ = stack[5].m_obj;
lean_object* v_a_410_ = stack[6].m_obj;
lean_object* v_a_411_ = stack[7].m_obj;
lean_object* v_a_412_ = stack[8].m_obj;
lean_object* v_a_413_ = stack[9].m_obj;
lean_object* v_res_498_;
v_res_498_ = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre(v_pattern_404_, v_state_405_, v_e_406_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_);
stack->m_obj
 = v_res_498_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre___boxed(lean_object* v_pattern_499_, lean_object* v_state_500_, lean_object* v_e_501_, lean_object* v_a_502_, lean_object* v_a_503_, lean_object* v_a_504_, lean_object* v_a_505_, lean_object* v_a_506_, lean_object* v_a_507_, lean_object* v_a_508_, lean_object* v_a_509_){
_start:
{
lean_object* v_res_510_; 
v_res_510_ = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre(v_pattern_499_, v_state_500_, v_e_501_, v_a_502_, v_a_503_, v_a_504_, v_a_505_, v_a_506_, v_a_507_, v_a_508_);
lean_dec(v_a_508_);
lean_dec_ref(v_a_507_);
lean_dec(v_a_506_);
lean_dec_ref(v_a_505_);
lean_dec(v_a_504_);
lean_dec_ref(v_a_503_);
lean_dec(v_a_502_);
lean_dec(v_state_500_);
return v_res_510_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre_spec__0(lean_object* v_as_511_, size_t v_sz_512_, size_t v_i_513_, lean_object* v_b_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_){
_start:
{
lean_object* v___x_523_; 
v___x_523_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre_spec__0___redArg(v_as_511_, v_sz_512_, v_i_513_, v_b_514_, v___y_518_, v___y_519_, v___y_520_, v___y_521_);
return v___x_523_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_511_ = stack[0].m_obj;
size_t v_sz_512_ = stack[1].m_num;
size_t v_i_513_ = stack[2].m_num;
lean_object* v_b_514_ = stack[3].m_obj;
lean_object* v___y_515_ = stack[4].m_obj;
lean_object* v___y_516_ = stack[5].m_obj;
lean_object* v___y_517_ = stack[6].m_obj;
lean_object* v___y_518_ = stack[7].m_obj;
lean_object* v___y_519_ = stack[8].m_obj;
lean_object* v___y_520_ = stack[9].m_obj;
lean_object* v___y_521_ = stack[10].m_obj;
lean_object* v_res_524_;
v_res_524_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre_spec__0(v_as_511_, v_sz_512_, v_i_513_, v_b_514_, v___y_515_, v___y_516_, v___y_517_, v___y_518_, v___y_519_, v___y_520_, v___y_521_);
stack->m_obj
 = v_res_524_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre_spec__0___boxed(lean_object* v_as_525_, lean_object* v_sz_526_, lean_object* v_i_527_, lean_object* v_b_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_){
_start:
{
size_t v_sz_boxed_537_; size_t v_i_boxed_538_; lean_object* v_res_539_; 
v_sz_boxed_537_ = lean_unbox_usize(v_sz_526_);
lean_dec(v_sz_526_);
v_i_boxed_538_ = lean_unbox_usize(v_i_527_);
lean_dec(v_i_527_);
v_res_539_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre_spec__0(v_as_525_, v_sz_boxed_537_, v_i_boxed_538_, v_b_528_, v___y_529_, v___y_530_, v___y_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_);
lean_dec(v___y_535_);
lean_dec_ref(v___y_534_);
lean_dec(v___y_533_);
lean_dec_ref(v___y_532_);
lean_dec(v___y_531_);
lean_dec_ref(v___y_530_);
lean_dec(v___y_529_);
lean_dec_ref(v_as_525_);
return v_res_539_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_540_ = lean_box(0);
v___x_541_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_542_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_542_, 0, v___x_541_);
lean_ctor_set(v___x_542_, 1, v___x_540_);
return v___x_542_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1___redArg(){
_start:
{
lean_object* v___x_544_; lean_object* v___x_545_; 
v___x_544_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1___redArg___closed__0);
v___x_545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_545_, 0, v___x_544_);
return v___x_545_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_546_;
v_res_546_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1___redArg();
stack->m_obj
 = v_res_546_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1___redArg___boxed(lean_object* v___y_547_){
_start:
{
lean_object* v_res_548_; 
v_res_548_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1___redArg();
return v_res_548_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1(lean_object* v_00_u03b1_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_){
_start:
{
lean_object* v___x_559_; 
v___x_559_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1___redArg();
return v___x_559_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_550_ = stack[1].m_obj;
lean_object* v___y_551_ = stack[2].m_obj;
lean_object* v___y_552_ = stack[3].m_obj;
lean_object* v___y_553_ = stack[4].m_obj;
lean_object* v___y_554_ = stack[5].m_obj;
lean_object* v___y_555_ = stack[6].m_obj;
lean_object* v___y_556_ = stack[7].m_obj;
lean_object* v___y_557_ = stack[8].m_obj;
lean_object* v_res_560_;
v_res_560_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1(lean_box(0), v___y_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_);
stack->m_obj
 = v_res_560_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1___boxed(lean_object* v_00_u03b1_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_){
_start:
{
lean_object* v_res_571_; 
v_res_571_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1(v_00_u03b1_561_, v___y_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_);
lean_dec(v___y_569_);
lean_dec_ref(v___y_568_);
lean_dec(v___y_567_);
lean_dec_ref(v___y_566_);
lean_dec(v___y_565_);
lean_dec_ref(v___y_564_);
lean_dec(v___y_563_);
lean_dec_ref(v___y_562_);
return v_res_571_;
}
}
lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__2___redArg(lean_object* v_a_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_){
_start:
{
lean_object* v___x_580_; 
v___x_580_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v_a_572_, v___y_573_, v___y_574_, v___y_575_, v___y_576_, v___y_577_, v___y_578_);
return v___x_580_;
}
}
LEAN_EXPORT void l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_572_ = stack[0].m_obj;
lean_object* v___y_573_ = stack[1].m_obj;
lean_object* v___y_574_ = stack[2].m_obj;
lean_object* v___y_575_ = stack[3].m_obj;
lean_object* v___y_576_ = stack[4].m_obj;
lean_object* v___y_577_ = stack[5].m_obj;
lean_object* v___y_578_ = stack[6].m_obj;
lean_object* v_res_581_;
v_res_581_ = l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__2___redArg(v_a_572_, v___y_573_, v___y_574_, v___y_575_, v___y_576_, v___y_577_, v___y_578_);
stack->m_obj
 = v_res_581_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__2___redArg___boxed(lean_object* v_a_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_){
_start:
{
lean_object* v_res_590_; 
v_res_590_ = l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__2___redArg(v_a_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_);
lean_dec(v___y_588_);
lean_dec_ref(v___y_587_);
lean_dec(v___y_586_);
lean_dec_ref(v___y_585_);
lean_dec(v___y_584_);
lean_dec_ref(v___y_583_);
return v_res_590_;
}
}
lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__2(lean_object* v_00_u03b1_591_, lean_object* v_a_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_){
_start:
{
lean_object* v___x_600_; 
v___x_600_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v_a_592_, v___y_593_, v___y_594_, v___y_595_, v___y_596_, v___y_597_, v___y_598_);
return v___x_600_;
}
}
LEAN_EXPORT void l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_592_ = stack[1].m_obj;
lean_object* v___y_593_ = stack[2].m_obj;
lean_object* v___y_594_ = stack[3].m_obj;
lean_object* v___y_595_ = stack[4].m_obj;
lean_object* v___y_596_ = stack[5].m_obj;
lean_object* v___y_597_ = stack[6].m_obj;
lean_object* v___y_598_ = stack[7].m_obj;
lean_object* v_res_601_;
v_res_601_ = l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__2(lean_box(0), v_a_592_, v___y_593_, v___y_594_, v___y_595_, v___y_596_, v___y_597_, v___y_598_);
stack->m_obj
 = v_res_601_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__2___boxed(lean_object* v_00_u03b1_602_, lean_object* v_a_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_){
_start:
{
lean_object* v_res_611_; 
v_res_611_ = l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__2(v_00_u03b1_602_, v_a_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_);
lean_dec(v___y_609_);
lean_dec_ref(v___y_608_);
lean_dec(v___y_607_);
lean_dec_ref(v___y_606_);
lean_dec(v___y_605_);
lean_dec_ref(v___y_604_);
return v_res_611_;
}
}
lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__0(lean_object* v_e_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_){
_start:
{
lean_object* v___x_621_; lean_object* v___x_622_; 
v___x_621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_621_, 0, v_e_612_);
v___x_622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_622_, 0, v___x_621_);
return v___x_622_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Conv_evalPattern___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_612_ = stack[0].m_obj;
lean_object* v___y_613_ = stack[1].m_obj;
lean_object* v___y_614_ = stack[2].m_obj;
lean_object* v___y_615_ = stack[3].m_obj;
lean_object* v___y_616_ = stack[4].m_obj;
lean_object* v___y_617_ = stack[5].m_obj;
lean_object* v___y_618_ = stack[6].m_obj;
lean_object* v___y_619_ = stack[7].m_obj;
lean_object* v_res_623_;
v_res_623_ = l_Lean_Elab_Tactic_Conv_evalPattern___lam__0(v_e_612_, v___y_613_, v___y_614_, v___y_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_);
stack->m_obj
 = v_res_623_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__0___boxed(lean_object* v_e_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_){
_start:
{
lean_object* v_res_633_; 
v_res_633_ = l_Lean_Elab_Tactic_Conv_evalPattern___lam__0(v_e_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_, v___y_631_);
lean_dec(v___y_631_);
lean_dec_ref(v___y_630_);
lean_dec(v___y_629_);
lean_dec_ref(v___y_628_);
lean_dec(v___y_627_);
lean_dec_ref(v___y_626_);
lean_dec(v___y_625_);
return v_res_633_;
}
}
lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__1(lean_object* v___x_634_, uint8_t v___x_635_, lean_object* v_e_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_){
_start:
{
lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_645_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_645_, 0, v_e_636_);
lean_ctor_set(v___x_645_, 1, v___x_634_);
lean_ctor_set_uint8(v___x_645_, sizeof(void*)*2, v___x_635_);
v___x_646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_646_, 0, v___x_645_);
v___x_647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_647_, 0, v___x_646_);
return v___x_647_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Conv_evalPattern___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_634_ = stack[0].m_obj;
uint8_t v___x_635_ = stack[1].m_num;
lean_object* v_e_636_ = stack[2].m_obj;
lean_object* v___y_637_ = stack[3].m_obj;
lean_object* v___y_638_ = stack[4].m_obj;
lean_object* v___y_639_ = stack[5].m_obj;
lean_object* v___y_640_ = stack[6].m_obj;
lean_object* v___y_641_ = stack[7].m_obj;
lean_object* v___y_642_ = stack[8].m_obj;
lean_object* v___y_643_ = stack[9].m_obj;
lean_object* v_res_648_;
v_res_648_ = l_Lean_Elab_Tactic_Conv_evalPattern___lam__1(v___x_634_, v___x_635_, v_e_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_, v___y_643_);
stack->m_obj
 = v_res_648_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__1___boxed(lean_object* v___x_649_, lean_object* v___x_650_, lean_object* v_e_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_){
_start:
{
uint8_t v___x_15449__boxed_660_; lean_object* v_res_661_; 
v___x_15449__boxed_660_ = lean_unbox(v___x_650_);
v_res_661_ = l_Lean_Elab_Tactic_Conv_evalPattern___lam__1(v___x_649_, v___x_15449__boxed_660_, v_e_651_, v___y_652_, v___y_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_, v___y_658_);
lean_dec(v___y_658_);
lean_dec_ref(v___y_657_);
lean_dec(v___y_656_);
lean_dec_ref(v___y_655_);
lean_dec(v___y_654_);
lean_dec_ref(v___y_653_);
lean_dec(v___y_652_);
return v_res_661_;
}
}
lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__2(lean_object* v___x_662_, lean_object* v_x_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_){
_start:
{
lean_object* v___x_672_; lean_object* v___x_673_; 
v___x_672_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_672_, 0, v___x_662_);
v___x_673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_673_, 0, v___x_672_);
return v___x_673_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Conv_evalPattern___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_662_ = stack[0].m_obj;
lean_object* v_x_663_ = stack[1].m_obj;
lean_object* v___y_664_ = stack[2].m_obj;
lean_object* v___y_665_ = stack[3].m_obj;
lean_object* v___y_666_ = stack[4].m_obj;
lean_object* v___y_667_ = stack[5].m_obj;
lean_object* v___y_668_ = stack[6].m_obj;
lean_object* v___y_669_ = stack[7].m_obj;
lean_object* v___y_670_ = stack[8].m_obj;
lean_object* v_res_674_;
v_res_674_ = l_Lean_Elab_Tactic_Conv_evalPattern___lam__2(v___x_662_, v_x_663_, v___y_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_, v___y_670_);
stack->m_obj
 = v_res_674_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__2___boxed(lean_object* v___x_675_, lean_object* v_x_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_){
_start:
{
lean_object* v_res_685_; 
v_res_685_ = l_Lean_Elab_Tactic_Conv_evalPattern___lam__2(v___x_675_, v_x_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_);
lean_dec(v___y_683_);
lean_dec_ref(v___y_682_);
lean_dec(v___y_681_);
lean_dec_ref(v___y_680_);
lean_dec(v___y_679_);
lean_dec_ref(v___y_678_);
lean_dec(v___y_677_);
lean_dec_ref(v_x_676_);
return v_res_685_;
}
}
lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__3(lean_object* v___x_686_, lean_object* v_x_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_){
_start:
{
lean_object* v___x_696_; 
v___x_696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_696_, 0, v___x_686_);
return v___x_696_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Conv_evalPattern___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_686_ = stack[0].m_obj;
lean_object* v_x_687_ = stack[1].m_obj;
lean_object* v___y_688_ = stack[2].m_obj;
lean_object* v___y_689_ = stack[3].m_obj;
lean_object* v___y_690_ = stack[4].m_obj;
lean_object* v___y_691_ = stack[5].m_obj;
lean_object* v___y_692_ = stack[6].m_obj;
lean_object* v___y_693_ = stack[7].m_obj;
lean_object* v___y_694_ = stack[8].m_obj;
lean_object* v_res_697_;
v_res_697_ = l_Lean_Elab_Tactic_Conv_evalPattern___lam__3(v___x_686_, v_x_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_, v___y_694_);
stack->m_obj
 = v_res_697_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__3___boxed(lean_object* v___x_698_, lean_object* v_x_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_){
_start:
{
lean_object* v_res_708_; 
v_res_708_ = l_Lean_Elab_Tactic_Conv_evalPattern___lam__3(v___x_698_, v_x_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_, v___y_706_);
lean_dec(v___y_706_);
lean_dec_ref(v___y_705_);
lean_dec(v___y_704_);
lean_dec_ref(v___y_703_);
lean_dec(v___y_702_);
lean_dec_ref(v___y_701_);
lean_dec(v___y_700_);
lean_dec_ref(v_x_699_);
return v_res_708_;
}
}
lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__4(lean_object* v___x_709_, lean_object* v___x_710_, uint8_t v___x_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_){
_start:
{
lean_object* v___x_719_; 
v___x_719_ = l_Lean_Elab_Term_elabTerm(v___x_709_, v___x_710_, v___x_711_, v___x_711_, v___y_712_, v___y_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_);
if (lean_obj_tag(v___x_719_) == 0)
{
lean_object* v_a_720_; lean_object* v___x_721_; 
v_a_720_ = lean_ctor_get(v___x_719_, 0);
lean_inc(v_a_720_);
lean_dec_ref_known(v___x_719_, 1);
v___x_721_ = l_Lean_Meta_abstractMVars(v_a_720_, v___x_711_, v___y_714_, v___y_715_, v___y_716_, v___y_717_);
return v___x_721_;
}
else
{
lean_object* v_a_722_; lean_object* v___x_724_; uint8_t v_isShared_725_; uint8_t v_isSharedCheck_729_; 
v_a_722_ = lean_ctor_get(v___x_719_, 0);
v_isSharedCheck_729_ = !lean_is_exclusive(v___x_719_);
if (v_isSharedCheck_729_ == 0)
{
v___x_724_ = v___x_719_;
v_isShared_725_ = v_isSharedCheck_729_;
goto v_resetjp_723_;
}
else
{
lean_inc(v_a_722_);
lean_dec(v___x_719_);
v___x_724_ = lean_box(0);
v_isShared_725_ = v_isSharedCheck_729_;
goto v_resetjp_723_;
}
v_resetjp_723_:
{
lean_object* v___x_727_; 
if (v_isShared_725_ == 0)
{
v___x_727_ = v___x_724_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v_a_722_);
v___x_727_ = v_reuseFailAlloc_728_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
return v___x_727_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Conv_evalPattern___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_709_ = stack[0].m_obj;
lean_object* v___x_710_ = stack[1].m_obj;
uint8_t v___x_711_ = stack[2].m_num;
lean_object* v___y_712_ = stack[3].m_obj;
lean_object* v___y_713_ = stack[4].m_obj;
lean_object* v___y_714_ = stack[5].m_obj;
lean_object* v___y_715_ = stack[6].m_obj;
lean_object* v___y_716_ = stack[7].m_obj;
lean_object* v___y_717_ = stack[8].m_obj;
lean_object* v_res_730_;
v_res_730_ = l_Lean_Elab_Tactic_Conv_evalPattern___lam__4(v___x_709_, v___x_710_, v___x_711_, v___y_712_, v___y_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_);
stack->m_obj
 = v_res_730_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__4___boxed(lean_object* v___x_731_, lean_object* v___x_732_, lean_object* v___x_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_){
_start:
{
uint8_t v___x_15618__boxed_741_; lean_object* v_res_742_; 
v___x_15618__boxed_741_ = lean_unbox(v___x_733_);
v_res_742_ = l_Lean_Elab_Tactic_Conv_evalPattern___lam__4(v___x_731_, v___x_732_, v___x_15618__boxed_741_, v___y_734_, v___y_735_, v___y_736_, v___y_737_, v___y_738_, v___y_739_);
lean_dec(v___y_739_);
lean_dec_ref(v___y_738_);
lean_dec(v___y_737_);
lean_dec_ref(v___y_736_);
lean_dec(v___y_735_);
lean_dec_ref(v___y_734_);
return v_res_742_;
}
}
lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__5(lean_object* v___x_743_, lean_object* v___f_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_){
_start:
{
lean_object* v_toCold_752_; lean_object* v_currRecDepth_753_; lean_object* v_ref_754_; uint16_t v_optionFlags_755_; uint8_t v_suppressElabErrors_756_; uint8_t v_isRecordingDeps_757_; lean_object* v___x_759_; uint8_t v_isShared_760_; uint8_t v_isSharedCheck_766_; 
v_toCold_752_ = lean_ctor_get(v___y_749_, 0);
v_currRecDepth_753_ = lean_ctor_get(v___y_749_, 1);
v_ref_754_ = lean_ctor_get(v___y_749_, 2);
v_optionFlags_755_ = lean_ctor_get_uint16(v___y_749_, sizeof(void*)*3);
v_suppressElabErrors_756_ = lean_ctor_get_uint8(v___y_749_, sizeof(void*)*3 + 2);
v_isRecordingDeps_757_ = lean_ctor_get_uint8(v___y_749_, sizeof(void*)*3 + 3);
v_isSharedCheck_766_ = !lean_is_exclusive(v___y_749_);
if (v_isSharedCheck_766_ == 0)
{
v___x_759_ = v___y_749_;
v_isShared_760_ = v_isSharedCheck_766_;
goto v_resetjp_758_;
}
else
{
lean_inc(v_ref_754_);
lean_inc(v_currRecDepth_753_);
lean_inc(v_toCold_752_);
lean_dec(v___y_749_);
v___x_759_ = lean_box(0);
v_isShared_760_ = v_isSharedCheck_766_;
goto v_resetjp_758_;
}
v_resetjp_758_:
{
lean_object* v_ref_761_; lean_object* v___x_763_; 
v_ref_761_ = l_Lean_replaceRef(v___x_743_, v_ref_754_);
lean_dec(v_ref_754_);
if (v_isShared_760_ == 0)
{
lean_ctor_set(v___x_759_, 2, v_ref_761_);
v___x_763_ = v___x_759_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v_toCold_752_);
lean_ctor_set(v_reuseFailAlloc_765_, 1, v_currRecDepth_753_);
lean_ctor_set(v_reuseFailAlloc_765_, 2, v_ref_761_);
lean_ctor_set_uint16(v_reuseFailAlloc_765_, sizeof(void*)*3, v_optionFlags_755_);
lean_ctor_set_uint8(v_reuseFailAlloc_765_, sizeof(void*)*3 + 2, v_suppressElabErrors_756_);
lean_ctor_set_uint8(v_reuseFailAlloc_765_, sizeof(void*)*3 + 3, v_isRecordingDeps_757_);
v___x_763_ = v_reuseFailAlloc_765_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
lean_object* v___x_764_; 
v___x_764_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v___f_744_, v___y_745_, v___y_746_, v___y_747_, v___y_748_, v___x_763_, v___y_750_);
lean_dec_ref(v___x_763_);
return v___x_764_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Conv_evalPattern___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_743_ = stack[0].m_obj;
lean_object* v___f_744_ = stack[1].m_obj;
lean_object* v___y_745_ = stack[2].m_obj;
lean_object* v___y_746_ = stack[3].m_obj;
lean_object* v___y_747_ = stack[4].m_obj;
lean_object* v___y_748_ = stack[5].m_obj;
lean_object* v___y_749_ = stack[6].m_obj;
lean_object* v___y_750_ = stack[7].m_obj;
lean_object* v_res_767_;
v_res_767_ = l_Lean_Elab_Tactic_Conv_evalPattern___lam__5(v___x_743_, v___f_744_, v___y_745_, v___y_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_);
stack->m_obj
 = v_res_767_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__5___boxed(lean_object* v___x_768_, lean_object* v___f_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_){
_start:
{
lean_object* v_res_777_; 
v_res_777_ = l_Lean_Elab_Tactic_Conv_evalPattern___lam__5(v___x_768_, v___f_769_, v___y_770_, v___y_771_, v___y_772_, v___y_773_, v___y_774_, v___y_775_);
lean_dec(v___y_775_);
lean_dec(v___y_773_);
lean_dec_ref(v___y_772_);
lean_dec(v___y_771_);
lean_dec_ref(v___y_770_);
lean_dec(v___x_768_);
return v_res_777_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__5(size_t v_sz_778_, size_t v_i_779_, lean_object* v_bs_780_){
_start:
{
uint8_t v___x_781_; 
v___x_781_ = lean_usize_dec_lt(v_i_779_, v_sz_778_);
if (v___x_781_ == 0)
{
return v_bs_780_;
}
else
{
lean_object* v_v_782_; lean_object* v_snd_783_; lean_object* v___x_784_; lean_object* v_bs_x27_785_; size_t v___x_786_; size_t v___x_787_; lean_object* v___x_788_; 
v_v_782_ = lean_array_uget_borrowed(v_bs_780_, v_i_779_);
v_snd_783_ = lean_ctor_get(v_v_782_, 1);
lean_inc(v_snd_783_);
v___x_784_ = lean_unsigned_to_nat(0u);
v_bs_x27_785_ = lean_array_uset(v_bs_780_, v_i_779_, v___x_784_);
v___x_786_ = ((size_t)1ULL);
v___x_787_ = lean_usize_add(v_i_779_, v___x_786_);
v___x_788_ = lean_array_uset(v_bs_x27_785_, v_i_779_, v_snd_783_);
v_i_779_ = v___x_787_;
v_bs_780_ = v___x_788_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__5_0interp(lean_interpreter_value* stack)
{
size_t v_sz_778_ = stack[0].m_num;
size_t v_i_779_ = stack[1].m_num;
lean_object* v_bs_780_ = stack[2].m_obj;
lean_object* v_res_790_;
v_res_790_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__5(v_sz_778_, v_i_779_, v_bs_780_);
stack->m_obj
 = v_res_790_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__5___boxed(lean_object* v_sz_791_, lean_object* v_i_792_, lean_object* v_bs_793_){
_start:
{
size_t v_sz_boxed_794_; size_t v_i_boxed_795_; lean_object* v_res_796_; 
v_sz_boxed_794_ = lean_unbox_usize(v_sz_791_);
lean_dec(v_sz_791_);
v_i_boxed_795_ = lean_unbox_usize(v_i_792_);
lean_dec(v_i_792_);
v_res_796_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__5(v_sz_boxed_794_, v_i_boxed_795_, v_bs_793_);
return v_res_796_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4_spec__5(lean_object* v_msgData_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_){
_start:
{
lean_object* v___x_803_; lean_object* v_env_804_; uint8_t v___x_805_; lean_object* v_env_806_; lean_object* v___x_807_; lean_object* v_toCold_808_; lean_object* v_mctx_809_; lean_object* v_lctx_810_; lean_object* v_options_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; 
v___x_803_ = lean_st_ref_get(v___y_801_);
v_env_804_ = lean_ctor_get(v___x_803_, 0);
lean_inc_ref(v_env_804_);
lean_dec(v___x_803_);
v___x_805_ = 0;
v_env_806_ = l_Lean_Environment_setRecordingDeps(v_env_804_, v___x_805_);
v___x_807_ = lean_st_ref_get(v___y_799_);
v_toCold_808_ = lean_ctor_get(v___y_800_, 0);
v_mctx_809_ = lean_ctor_get(v___x_807_, 0);
lean_inc_ref(v_mctx_809_);
lean_dec(v___x_807_);
v_lctx_810_ = lean_ctor_get(v___y_798_, 2);
v_options_811_ = lean_ctor_get(v_toCold_808_, 2);
lean_inc_ref(v_options_811_);
lean_inc_ref(v_lctx_810_);
v___x_812_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_812_, 0, v_env_806_);
lean_ctor_set(v___x_812_, 1, v_mctx_809_);
lean_ctor_set(v___x_812_, 2, v_lctx_810_);
lean_ctor_set(v___x_812_, 3, v_options_811_);
v___x_813_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_813_, 0, v___x_812_);
lean_ctor_set(v___x_813_, 1, v_msgData_797_);
v___x_814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_814_, 0, v___x_813_);
return v___x_814_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_797_ = stack[0].m_obj;
lean_object* v___y_798_ = stack[1].m_obj;
lean_object* v___y_799_ = stack[2].m_obj;
lean_object* v___y_800_ = stack[3].m_obj;
lean_object* v___y_801_ = stack[4].m_obj;
lean_object* v_res_815_;
v_res_815_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4_spec__5(v_msgData_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_);
stack->m_obj
 = v_res_815_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4_spec__5___boxed(lean_object* v_msgData_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_){
_start:
{
lean_object* v_res_822_; 
v_res_822_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4_spec__5(v_msgData_816_, v___y_817_, v___y_818_, v___y_819_, v___y_820_);
lean_dec(v___y_820_);
lean_dec_ref(v___y_819_);
lean_dec(v___y_818_);
lean_dec_ref(v___y_817_);
return v_res_822_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg(lean_object* v_msg_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_){
_start:
{
lean_object* v_ref_829_; lean_object* v___x_830_; lean_object* v_a_831_; lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_839_; 
v_ref_829_ = lean_ctor_get(v___y_826_, 2);
v___x_830_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4_spec__5(v_msg_823_, v___y_824_, v___y_825_, v___y_826_, v___y_827_);
v_a_831_ = lean_ctor_get(v___x_830_, 0);
v_isSharedCheck_839_ = !lean_is_exclusive(v___x_830_);
if (v_isSharedCheck_839_ == 0)
{
v___x_833_ = v___x_830_;
v_isShared_834_ = v_isSharedCheck_839_;
goto v_resetjp_832_;
}
else
{
lean_inc(v_a_831_);
lean_dec(v___x_830_);
v___x_833_ = lean_box(0);
v_isShared_834_ = v_isSharedCheck_839_;
goto v_resetjp_832_;
}
v_resetjp_832_:
{
lean_object* v___x_835_; lean_object* v___x_837_; 
lean_inc(v_ref_829_);
v___x_835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_835_, 0, v_ref_829_);
lean_ctor_set(v___x_835_, 1, v_a_831_);
if (v_isShared_834_ == 0)
{
lean_ctor_set_tag(v___x_833_, 1);
lean_ctor_set(v___x_833_, 0, v___x_835_);
v___x_837_ = v___x_833_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v___x_835_);
v___x_837_ = v_reuseFailAlloc_838_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
return v___x_837_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_823_ = stack[0].m_obj;
lean_object* v___y_824_ = stack[1].m_obj;
lean_object* v___y_825_ = stack[2].m_obj;
lean_object* v___y_826_ = stack[3].m_obj;
lean_object* v___y_827_ = stack[4].m_obj;
lean_object* v_res_840_;
v_res_840_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg(v_msg_823_, v___y_824_, v___y_825_, v___y_826_, v___y_827_);
stack->m_obj
 = v_res_840_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg___boxed(lean_object* v_msg_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_){
_start:
{
lean_object* v_res_847_; 
v_res_847_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg(v_msg_841_, v___y_842_, v___y_843_, v___y_844_, v___y_845_);
lean_dec(v___y_845_);
lean_dec_ref(v___y_844_);
lean_dec(v___y_843_);
lean_dec_ref(v___y_842_);
return v_res_847_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg(lean_object* v_ref_848_, lean_object* v_msg_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_){
_start:
{
lean_object* v_toCold_859_; lean_object* v_currRecDepth_860_; lean_object* v_ref_861_; uint16_t v_optionFlags_862_; uint8_t v_suppressElabErrors_863_; uint8_t v_isRecordingDeps_864_; lean_object* v_ref_865_; lean_object* v___x_866_; lean_object* v___x_867_; 
v_toCold_859_ = lean_ctor_get(v___y_856_, 0);
v_currRecDepth_860_ = lean_ctor_get(v___y_856_, 1);
v_ref_861_ = lean_ctor_get(v___y_856_, 2);
v_optionFlags_862_ = lean_ctor_get_uint16(v___y_856_, sizeof(void*)*3);
v_suppressElabErrors_863_ = lean_ctor_get_uint8(v___y_856_, sizeof(void*)*3 + 2);
v_isRecordingDeps_864_ = lean_ctor_get_uint8(v___y_856_, sizeof(void*)*3 + 3);
v_ref_865_ = l_Lean_replaceRef(v_ref_848_, v_ref_861_);
lean_inc(v_currRecDepth_860_);
lean_inc_ref(v_toCold_859_);
v___x_866_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_866_, 0, v_toCold_859_);
lean_ctor_set(v___x_866_, 1, v_currRecDepth_860_);
lean_ctor_set(v___x_866_, 2, v_ref_865_);
lean_ctor_set_uint16(v___x_866_, sizeof(void*)*3, v_optionFlags_862_);
lean_ctor_set_uint8(v___x_866_, sizeof(void*)*3 + 2, v_suppressElabErrors_863_);
lean_ctor_set_uint8(v___x_866_, sizeof(void*)*3 + 3, v_isRecordingDeps_864_);
v___x_867_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg(v_msg_849_, v___y_854_, v___y_855_, v___x_866_, v___y_857_);
lean_dec_ref_known(v___x_866_, 3);
return v___x_867_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_848_ = stack[0].m_obj;
lean_object* v_msg_849_ = stack[1].m_obj;
lean_object* v___y_850_ = stack[2].m_obj;
lean_object* v___y_851_ = stack[3].m_obj;
lean_object* v___y_852_ = stack[4].m_obj;
lean_object* v___y_853_ = stack[5].m_obj;
lean_object* v___y_854_ = stack[6].m_obj;
lean_object* v___y_855_ = stack[7].m_obj;
lean_object* v___y_856_ = stack[8].m_obj;
lean_object* v___y_857_ = stack[9].m_obj;
lean_object* v_res_868_;
v_res_868_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg(v_ref_848_, v_msg_849_, v___y_850_, v___y_851_, v___y_852_, v___y_853_, v___y_854_, v___y_855_, v___y_856_, v___y_857_);
stack->m_obj
 = v_res_868_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg___boxed(lean_object* v_ref_869_, lean_object* v_msg_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_){
_start:
{
lean_object* v_res_880_; 
v_res_880_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg(v_ref_869_, v_msg_870_, v___y_871_, v___y_872_, v___y_873_, v___y_874_, v___y_875_, v___y_876_, v___y_877_, v___y_878_);
lean_dec(v___y_878_);
lean_dec_ref(v___y_877_);
lean_dec(v___y_876_);
lean_dec_ref(v___y_875_);
lean_dec(v___y_874_);
lean_dec_ref(v___y_873_);
lean_dec(v___y_872_);
lean_dec_ref(v___y_871_);
lean_dec(v_ref_869_);
return v_res_880_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_882_; lean_object* v___x_883_; 
v___x_882_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg___closed__0));
v___x_883_ = l_Lean_stringToMessageData(v___x_882_);
return v___x_883_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg(size_t v_sz_884_, size_t v_i_885_, lean_object* v_bs_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_){
_start:
{
uint8_t v___x_896_; 
v___x_896_ = lean_usize_dec_lt(v_i_885_, v_sz_884_);
if (v___x_896_ == 0)
{
lean_object* v___x_897_; 
v___x_897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_897_, 0, v_bs_886_);
return v___x_897_;
}
else
{
lean_object* v_v_898_; lean_object* v___x_899_; lean_object* v_bs_x27_900_; lean_object* v_a_902_; lean_object* v___x_907_; uint8_t v_isZero_908_; 
v_v_898_ = lean_array_uget(v_bs_886_, v_i_885_);
v___x_899_ = lean_unsigned_to_nat(0u);
v_bs_x27_900_ = lean_array_uset(v_bs_886_, v_i_885_, v___x_899_);
v___x_907_ = l_Lean_TSyntax_getNat(v_v_898_);
v_isZero_908_ = lean_nat_dec_eq(v___x_907_, v___x_899_);
if (v_isZero_908_ == 1)
{
lean_object* v___x_909_; lean_object* v___x_910_; 
lean_dec(v___x_907_);
v___x_909_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg___closed__1);
v___x_910_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg(v_v_898_, v___x_909_, v___y_887_, v___y_888_, v___y_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_, v___y_894_);
lean_dec(v_v_898_);
if (lean_obj_tag(v___x_910_) == 0)
{
lean_object* v_a_911_; 
v_a_911_ = lean_ctor_get(v___x_910_, 0);
lean_inc(v_a_911_);
lean_dec_ref_known(v___x_910_, 1);
v_a_902_ = v_a_911_;
goto v___jp_901_;
}
else
{
lean_object* v_a_912_; lean_object* v___x_914_; uint8_t v_isShared_915_; uint8_t v_isSharedCheck_919_; 
lean_dec_ref(v_bs_x27_900_);
v_a_912_ = lean_ctor_get(v___x_910_, 0);
v_isSharedCheck_919_ = !lean_is_exclusive(v___x_910_);
if (v_isSharedCheck_919_ == 0)
{
v___x_914_ = v___x_910_;
v_isShared_915_ = v_isSharedCheck_919_;
goto v_resetjp_913_;
}
else
{
lean_inc(v_a_912_);
lean_dec(v___x_910_);
v___x_914_ = lean_box(0);
v_isShared_915_ = v_isSharedCheck_919_;
goto v_resetjp_913_;
}
v_resetjp_913_:
{
lean_object* v___x_917_; 
if (v_isShared_915_ == 0)
{
v___x_917_ = v___x_914_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v_a_912_);
v___x_917_ = v_reuseFailAlloc_918_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
return v___x_917_;
}
}
}
}
else
{
lean_object* v___x_920_; lean_object* v_one_921_; lean_object* v_n_922_; lean_object* v___x_923_; 
lean_dec(v_v_898_);
v___x_920_ = lean_usize_to_nat(v_i_885_);
v_one_921_ = lean_unsigned_to_nat(1u);
v_n_922_ = lean_nat_sub(v___x_907_, v_one_921_);
lean_dec(v___x_907_);
v___x_923_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_923_, 0, v_n_922_);
lean_ctor_set(v___x_923_, 1, v___x_920_);
v_a_902_ = v___x_923_;
goto v___jp_901_;
}
v___jp_901_:
{
size_t v___x_903_; size_t v___x_904_; lean_object* v___x_905_; 
v___x_903_ = ((size_t)1ULL);
v___x_904_ = lean_usize_add(v_i_885_, v___x_903_);
v___x_905_ = lean_array_uset(v_bs_x27_900_, v_i_885_, v_a_902_);
v_i_885_ = v___x_904_;
v_bs_886_ = v___x_905_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_sz_884_ = stack[0].m_num;
size_t v_i_885_ = stack[1].m_num;
lean_object* v_bs_886_ = stack[2].m_obj;
lean_object* v___y_887_ = stack[3].m_obj;
lean_object* v___y_888_ = stack[4].m_obj;
lean_object* v___y_889_ = stack[5].m_obj;
lean_object* v___y_890_ = stack[6].m_obj;
lean_object* v___y_891_ = stack[7].m_obj;
lean_object* v___y_892_ = stack[8].m_obj;
lean_object* v___y_893_ = stack[9].m_obj;
lean_object* v___y_894_ = stack[10].m_obj;
lean_object* v_res_924_;
v_res_924_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg(v_sz_884_, v_i_885_, v_bs_886_, v___y_887_, v___y_888_, v___y_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_, v___y_894_);
stack->m_obj
 = v_res_924_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg___boxed(lean_object* v_sz_925_, lean_object* v_i_926_, lean_object* v_bs_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_){
_start:
{
size_t v_sz_boxed_937_; size_t v_i_boxed_938_; lean_object* v_res_939_; 
v_sz_boxed_937_ = lean_unbox_usize(v_sz_925_);
lean_dec(v_sz_925_);
v_i_boxed_938_ = lean_unbox_usize(v_i_926_);
lean_dec(v_i_926_);
v_res_939_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg(v_sz_boxed_937_, v_i_boxed_938_, v_bs_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_);
lean_dec(v___y_935_);
lean_dec_ref(v___y_934_);
lean_dec(v___y_933_);
lean_dec_ref(v___y_932_);
lean_dec(v___y_931_);
lean_dec_ref(v___y_930_);
lean_dec(v___y_929_);
lean_dec_ref(v___y_928_);
return v_res_939_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6_spec__8___redArg(lean_object* v_hi_940_, lean_object* v_pivot_941_, lean_object* v_as_942_, lean_object* v_i_943_, lean_object* v_k_944_){
_start:
{
uint8_t v___x_945_; 
v___x_945_ = lean_nat_dec_lt(v_k_944_, v_hi_940_);
if (v___x_945_ == 0)
{
lean_object* v___x_946_; lean_object* v___x_947_; 
lean_dec(v_k_944_);
v___x_946_ = lean_array_fswap(v_as_942_, v_i_943_, v_hi_940_);
v___x_947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_947_, 0, v_i_943_);
lean_ctor_set(v___x_947_, 1, v___x_946_);
return v___x_947_;
}
else
{
lean_object* v___x_948_; lean_object* v_fst_949_; lean_object* v_fst_950_; uint8_t v___x_951_; 
v___x_948_ = lean_array_fget_borrowed(v_as_942_, v_k_944_);
v_fst_949_ = lean_ctor_get(v___x_948_, 0);
v_fst_950_ = lean_ctor_get(v_pivot_941_, 0);
v___x_951_ = lean_nat_dec_lt(v_fst_949_, v_fst_950_);
if (v___x_951_ == 0)
{
lean_object* v___x_952_; lean_object* v___x_953_; 
v___x_952_ = lean_unsigned_to_nat(1u);
v___x_953_ = lean_nat_add(v_k_944_, v___x_952_);
lean_dec(v_k_944_);
v_k_944_ = v___x_953_;
goto _start;
}
else
{
lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; 
v___x_955_ = lean_array_fswap(v_as_942_, v_i_943_, v_k_944_);
v___x_956_ = lean_unsigned_to_nat(1u);
v___x_957_ = lean_nat_add(v_i_943_, v___x_956_);
lean_dec(v_i_943_);
v___x_958_ = lean_nat_add(v_k_944_, v___x_956_);
lean_dec(v_k_944_);
v_as_942_ = v___x_955_;
v_i_943_ = v___x_957_;
v_k_944_ = v___x_958_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6_spec__8___redArg___boxed(lean_object* v_hi_960_, lean_object* v_pivot_961_, lean_object* v_as_962_, lean_object* v_i_963_, lean_object* v_k_964_){
_start:
{
lean_object* v_res_965_; 
v_res_965_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6_spec__8___redArg(v_hi_960_, v_pivot_961_, v_as_962_, v_i_963_, v_k_964_);
lean_dec_ref(v_pivot_961_);
lean_dec(v_hi_960_);
return v_res_965_;
}
}
uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg___lam__0(lean_object* v_x1_966_, lean_object* v_x2_967_){
_start:
{
lean_object* v_fst_968_; lean_object* v_fst_969_; uint8_t v___x_970_; 
v_fst_968_ = lean_ctor_get(v_x1_966_, 0);
v_fst_969_ = lean_ctor_get(v_x2_967_, 0);
v___x_970_ = lean_nat_dec_lt(v_fst_968_, v_fst_969_);
return v___x_970_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x1_966_ = stack[0].m_obj;
lean_object* v_x2_967_ = stack[1].m_obj;
uint8_t v_res_971_;
v_res_971_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg___lam__0(v_x1_966_, v_x2_967_);
stack->m_num = v_res_971_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg___lam__0___boxed(lean_object* v_x1_972_, lean_object* v_x2_973_){
_start:
{
uint8_t v_res_974_; lean_object* v_r_975_; 
v_res_974_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg___lam__0(v_x1_972_, v_x2_973_);
lean_dec_ref(v_x2_973_);
lean_dec_ref(v_x1_972_);
v_r_975_ = lean_box(v_res_974_);
return v_r_975_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg(lean_object* v_n_976_, lean_object* v_as_977_, lean_object* v_lo_978_, lean_object* v_hi_979_){
_start:
{
lean_object* v___y_981_; uint8_t v___x_991_; 
v___x_991_ = lean_nat_dec_lt(v_lo_978_, v_hi_979_);
if (v___x_991_ == 0)
{
lean_dec(v_lo_978_);
return v_as_977_;
}
else
{
lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v_mid_994_; lean_object* v___y_996_; lean_object* v___y_1002_; lean_object* v___x_1007_; lean_object* v___x_1008_; uint8_t v___x_1009_; 
v___x_992_ = lean_nat_add(v_lo_978_, v_hi_979_);
v___x_993_ = lean_unsigned_to_nat(1u);
v_mid_994_ = lean_nat_shiftr(v___x_992_, v___x_993_);
lean_dec(v___x_992_);
v___x_1007_ = lean_array_fget_borrowed(v_as_977_, v_mid_994_);
v___x_1008_ = lean_array_fget_borrowed(v_as_977_, v_lo_978_);
v___x_1009_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg___lam__0(v___x_1007_, v___x_1008_);
if (v___x_1009_ == 0)
{
v___y_1002_ = v_as_977_;
goto v___jp_1001_;
}
else
{
lean_object* v___x_1010_; 
v___x_1010_ = lean_array_fswap(v_as_977_, v_lo_978_, v_mid_994_);
v___y_1002_ = v___x_1010_;
goto v___jp_1001_;
}
v___jp_995_:
{
lean_object* v___x_997_; lean_object* v___x_998_; uint8_t v___x_999_; 
v___x_997_ = lean_array_fget_borrowed(v___y_996_, v_mid_994_);
v___x_998_ = lean_array_fget_borrowed(v___y_996_, v_hi_979_);
v___x_999_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg___lam__0(v___x_997_, v___x_998_);
if (v___x_999_ == 0)
{
lean_dec(v_mid_994_);
v___y_981_ = v___y_996_;
goto v___jp_980_;
}
else
{
lean_object* v___x_1000_; 
v___x_1000_ = lean_array_fswap(v___y_996_, v_mid_994_, v_hi_979_);
lean_dec(v_mid_994_);
v___y_981_ = v___x_1000_;
goto v___jp_980_;
}
}
v___jp_1001_:
{
lean_object* v___x_1003_; lean_object* v___x_1004_; uint8_t v___x_1005_; 
v___x_1003_ = lean_array_fget_borrowed(v___y_1002_, v_hi_979_);
v___x_1004_ = lean_array_fget_borrowed(v___y_1002_, v_lo_978_);
v___x_1005_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg___lam__0(v___x_1003_, v___x_1004_);
if (v___x_1005_ == 0)
{
v___y_996_ = v___y_1002_;
goto v___jp_995_;
}
else
{
lean_object* v___x_1006_; 
v___x_1006_ = lean_array_fswap(v___y_1002_, v_lo_978_, v_hi_979_);
v___y_996_ = v___x_1006_;
goto v___jp_995_;
}
}
}
v___jp_980_:
{
lean_object* v_pivot_982_; lean_object* v___x_983_; lean_object* v_fst_984_; lean_object* v_snd_985_; uint8_t v___x_986_; 
v_pivot_982_ = lean_array_fget(v___y_981_, v_hi_979_);
lean_inc_n(v_lo_978_, 2);
v___x_983_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6_spec__8___redArg(v_hi_979_, v_pivot_982_, v___y_981_, v_lo_978_, v_lo_978_);
lean_dec(v_pivot_982_);
v_fst_984_ = lean_ctor_get(v___x_983_, 0);
lean_inc(v_fst_984_);
v_snd_985_ = lean_ctor_get(v___x_983_, 1);
lean_inc(v_snd_985_);
lean_dec_ref(v___x_983_);
v___x_986_ = lean_nat_dec_le(v_hi_979_, v_fst_984_);
if (v___x_986_ == 0)
{
lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; 
v___x_987_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg(v_n_976_, v_snd_985_, v_lo_978_, v_fst_984_);
v___x_988_ = lean_unsigned_to_nat(1u);
v___x_989_ = lean_nat_add(v_fst_984_, v___x_988_);
lean_dec(v_fst_984_);
v_as_977_ = v___x_987_;
v_lo_978_ = v___x_989_;
goto _start;
}
else
{
lean_dec(v_fst_984_);
lean_dec(v_lo_978_);
return v_snd_985_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg___boxed(lean_object* v_n_1011_, lean_object* v_as_1012_, lean_object* v_lo_1013_, lean_object* v_hi_1014_){
_start:
{
lean_object* v_res_1015_; 
v_res_1015_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg(v_n_1011_, v_as_1012_, v_lo_1013_, v_hi_1014_);
lean_dec(v_hi_1014_);
lean_dec(v_n_1011_);
return v_res_1015_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__12_spec__16___redArg(lean_object* v_x_1016_, lean_object* v_x_1017_, lean_object* v_x_1018_, lean_object* v_x_1019_){
_start:
{
lean_object* v_ks_1020_; lean_object* v_vs_1021_; lean_object* v___x_1023_; uint8_t v_isShared_1024_; uint8_t v_isSharedCheck_1045_; 
v_ks_1020_ = lean_ctor_get(v_x_1016_, 0);
v_vs_1021_ = lean_ctor_get(v_x_1016_, 1);
v_isSharedCheck_1045_ = !lean_is_exclusive(v_x_1016_);
if (v_isSharedCheck_1045_ == 0)
{
v___x_1023_ = v_x_1016_;
v_isShared_1024_ = v_isSharedCheck_1045_;
goto v_resetjp_1022_;
}
else
{
lean_inc(v_vs_1021_);
lean_inc(v_ks_1020_);
lean_dec(v_x_1016_);
v___x_1023_ = lean_box(0);
v_isShared_1024_ = v_isSharedCheck_1045_;
goto v_resetjp_1022_;
}
v_resetjp_1022_:
{
lean_object* v___x_1025_; uint8_t v___x_1026_; 
v___x_1025_ = lean_array_get_size(v_ks_1020_);
v___x_1026_ = lean_nat_dec_lt(v_x_1017_, v___x_1025_);
if (v___x_1026_ == 0)
{
lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1030_; 
lean_dec(v_x_1017_);
v___x_1027_ = lean_array_push(v_ks_1020_, v_x_1018_);
v___x_1028_ = lean_array_push(v_vs_1021_, v_x_1019_);
if (v_isShared_1024_ == 0)
{
lean_ctor_set(v___x_1023_, 1, v___x_1028_);
lean_ctor_set(v___x_1023_, 0, v___x_1027_);
v___x_1030_ = v___x_1023_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1031_; 
v_reuseFailAlloc_1031_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1031_, 0, v___x_1027_);
lean_ctor_set(v_reuseFailAlloc_1031_, 1, v___x_1028_);
v___x_1030_ = v_reuseFailAlloc_1031_;
goto v_reusejp_1029_;
}
v_reusejp_1029_:
{
return v___x_1030_;
}
}
else
{
lean_object* v_k_x27_1032_; uint8_t v___x_1033_; 
v_k_x27_1032_ = lean_array_fget_borrowed(v_ks_1020_, v_x_1017_);
v___x_1033_ = l_Lean_instBEqMVarId_beq(v_x_1018_, v_k_x27_1032_);
if (v___x_1033_ == 0)
{
lean_object* v___x_1035_; 
if (v_isShared_1024_ == 0)
{
v___x_1035_ = v___x_1023_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v_ks_1020_);
lean_ctor_set(v_reuseFailAlloc_1039_, 1, v_vs_1021_);
v___x_1035_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1034_;
}
v_reusejp_1034_:
{
lean_object* v___x_1036_; lean_object* v___x_1037_; 
v___x_1036_ = lean_unsigned_to_nat(1u);
v___x_1037_ = lean_nat_add(v_x_1017_, v___x_1036_);
lean_dec(v_x_1017_);
v_x_1016_ = v___x_1035_;
v_x_1017_ = v___x_1037_;
goto _start;
}
}
else
{
lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1043_; 
v___x_1040_ = lean_array_fset(v_ks_1020_, v_x_1017_, v_x_1018_);
v___x_1041_ = lean_array_fset(v_vs_1021_, v_x_1017_, v_x_1019_);
lean_dec(v_x_1017_);
if (v_isShared_1024_ == 0)
{
lean_ctor_set(v___x_1023_, 1, v___x_1041_);
lean_ctor_set(v___x_1023_, 0, v___x_1040_);
v___x_1043_ = v___x_1023_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1044_, 0, v___x_1040_);
lean_ctor_set(v_reuseFailAlloc_1044_, 1, v___x_1041_);
v___x_1043_ = v_reuseFailAlloc_1044_;
goto v_reusejp_1042_;
}
v_reusejp_1042_:
{
return v___x_1043_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__12___redArg(lean_object* v_n_1046_, lean_object* v_k_1047_, lean_object* v_v_1048_){
_start:
{
lean_object* v___x_1049_; lean_object* v___x_1050_; 
v___x_1049_ = lean_unsigned_to_nat(0u);
v___x_1050_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__12_spec__16___redArg(v_n_1046_, v___x_1049_, v_k_1047_, v_v_1048_);
return v___x_1050_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_1051_; 
v___x_1051_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_1051_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg(lean_object* v_x_1052_, size_t v_x_1053_, size_t v_x_1054_, lean_object* v_x_1055_, lean_object* v_x_1056_){
_start:
{
if (lean_obj_tag(v_x_1052_) == 0)
{
lean_object* v_es_1057_; size_t v___x_1058_; size_t v___x_1059_; lean_object* v_j_1060_; lean_object* v___x_1061_; uint8_t v___x_1062_; 
v_es_1057_ = lean_ctor_get(v_x_1052_, 0);
v___x_1058_ = ((size_t)31ULL);
v___x_1059_ = lean_usize_land(v_x_1053_, v___x_1058_);
v_j_1060_ = lean_usize_to_nat(v___x_1059_);
v___x_1061_ = lean_array_get_size(v_es_1057_);
v___x_1062_ = lean_nat_dec_lt(v_j_1060_, v___x_1061_);
if (v___x_1062_ == 0)
{
lean_dec(v_j_1060_);
lean_dec(v_x_1056_);
lean_dec(v_x_1055_);
return v_x_1052_;
}
else
{
lean_object* v___x_1064_; uint8_t v_isShared_1065_; uint8_t v_isSharedCheck_1101_; 
lean_inc_ref(v_es_1057_);
v_isSharedCheck_1101_ = !lean_is_exclusive(v_x_1052_);
if (v_isSharedCheck_1101_ == 0)
{
lean_object* v_unused_1102_; 
v_unused_1102_ = lean_ctor_get(v_x_1052_, 0);
lean_dec(v_unused_1102_);
v___x_1064_ = v_x_1052_;
v_isShared_1065_ = v_isSharedCheck_1101_;
goto v_resetjp_1063_;
}
else
{
lean_dec(v_x_1052_);
v___x_1064_ = lean_box(0);
v_isShared_1065_ = v_isSharedCheck_1101_;
goto v_resetjp_1063_;
}
v_resetjp_1063_:
{
lean_object* v_v_1066_; lean_object* v___x_1067_; lean_object* v_xs_x27_1068_; lean_object* v___y_1070_; 
v_v_1066_ = lean_array_fget(v_es_1057_, v_j_1060_);
v___x_1067_ = lean_box(0);
v_xs_x27_1068_ = lean_array_fset(v_es_1057_, v_j_1060_, v___x_1067_);
switch(lean_obj_tag(v_v_1066_))
{
case 0:
{
lean_object* v_key_1075_; lean_object* v_val_1076_; lean_object* v___x_1078_; uint8_t v_isShared_1079_; uint8_t v_isSharedCheck_1086_; 
v_key_1075_ = lean_ctor_get(v_v_1066_, 0);
v_val_1076_ = lean_ctor_get(v_v_1066_, 1);
v_isSharedCheck_1086_ = !lean_is_exclusive(v_v_1066_);
if (v_isSharedCheck_1086_ == 0)
{
v___x_1078_ = v_v_1066_;
v_isShared_1079_ = v_isSharedCheck_1086_;
goto v_resetjp_1077_;
}
else
{
lean_inc(v_val_1076_);
lean_inc(v_key_1075_);
lean_dec(v_v_1066_);
v___x_1078_ = lean_box(0);
v_isShared_1079_ = v_isSharedCheck_1086_;
goto v_resetjp_1077_;
}
v_resetjp_1077_:
{
uint8_t v___x_1080_; 
v___x_1080_ = l_Lean_instBEqMVarId_beq(v_x_1055_, v_key_1075_);
if (v___x_1080_ == 0)
{
lean_object* v___x_1081_; lean_object* v___x_1082_; 
lean_del_object(v___x_1078_);
v___x_1081_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1075_, v_val_1076_, v_x_1055_, v_x_1056_);
v___x_1082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1082_, 0, v___x_1081_);
v___y_1070_ = v___x_1082_;
goto v___jp_1069_;
}
else
{
lean_object* v___x_1084_; 
lean_dec(v_val_1076_);
lean_dec(v_key_1075_);
if (v_isShared_1079_ == 0)
{
lean_ctor_set(v___x_1078_, 1, v_x_1056_);
lean_ctor_set(v___x_1078_, 0, v_x_1055_);
v___x_1084_ = v___x_1078_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v_x_1055_);
lean_ctor_set(v_reuseFailAlloc_1085_, 1, v_x_1056_);
v___x_1084_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
v___y_1070_ = v___x_1084_;
goto v___jp_1069_;
}
}
}
}
case 1:
{
lean_object* v_node_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1099_; 
v_node_1087_ = lean_ctor_get(v_v_1066_, 0);
v_isSharedCheck_1099_ = !lean_is_exclusive(v_v_1066_);
if (v_isSharedCheck_1099_ == 0)
{
v___x_1089_ = v_v_1066_;
v_isShared_1090_ = v_isSharedCheck_1099_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_node_1087_);
lean_dec(v_v_1066_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1099_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
size_t v___x_1091_; size_t v___x_1092_; size_t v___x_1093_; size_t v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1097_; 
v___x_1091_ = ((size_t)5ULL);
v___x_1092_ = lean_usize_shift_right(v_x_1053_, v___x_1091_);
v___x_1093_ = ((size_t)1ULL);
v___x_1094_ = lean_usize_add(v_x_1054_, v___x_1093_);
v___x_1095_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg(v_node_1087_, v___x_1092_, v___x_1094_, v_x_1055_, v_x_1056_);
if (v_isShared_1090_ == 0)
{
lean_ctor_set(v___x_1089_, 0, v___x_1095_);
v___x_1097_ = v___x_1089_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v___x_1095_);
v___x_1097_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1096_;
}
v_reusejp_1096_:
{
v___y_1070_ = v___x_1097_;
goto v___jp_1069_;
}
}
}
default: 
{
lean_object* v___x_1100_; 
v___x_1100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1100_, 0, v_x_1055_);
lean_ctor_set(v___x_1100_, 1, v_x_1056_);
v___y_1070_ = v___x_1100_;
goto v___jp_1069_;
}
}
v___jp_1069_:
{
lean_object* v___x_1071_; lean_object* v___x_1073_; 
v___x_1071_ = lean_array_fset(v_xs_x27_1068_, v_j_1060_, v___y_1070_);
lean_dec(v_j_1060_);
if (v_isShared_1065_ == 0)
{
lean_ctor_set(v___x_1064_, 0, v___x_1071_);
v___x_1073_ = v___x_1064_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v___x_1071_);
v___x_1073_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1072_;
}
v_reusejp_1072_:
{
return v___x_1073_;
}
}
}
}
}
else
{
lean_object* v_ks_1103_; lean_object* v_vs_1104_; lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1122_; 
v_ks_1103_ = lean_ctor_get(v_x_1052_, 0);
v_vs_1104_ = lean_ctor_get(v_x_1052_, 1);
v_isSharedCheck_1122_ = !lean_is_exclusive(v_x_1052_);
if (v_isSharedCheck_1122_ == 0)
{
v___x_1106_ = v_x_1052_;
v_isShared_1107_ = v_isSharedCheck_1122_;
goto v_resetjp_1105_;
}
else
{
lean_inc(v_vs_1104_);
lean_inc(v_ks_1103_);
lean_dec(v_x_1052_);
v___x_1106_ = lean_box(0);
v_isShared_1107_ = v_isSharedCheck_1122_;
goto v_resetjp_1105_;
}
v_resetjp_1105_:
{
lean_object* v___x_1109_; 
if (v_isShared_1107_ == 0)
{
v___x_1109_ = v___x_1106_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v_ks_1103_);
lean_ctor_set(v_reuseFailAlloc_1121_, 1, v_vs_1104_);
v___x_1109_ = v_reuseFailAlloc_1121_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
lean_object* v_newNode_1110_; size_t v___x_1111_; uint8_t v___x_1112_; 
v_newNode_1110_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__12___redArg(v___x_1109_, v_x_1055_, v_x_1056_);
v___x_1111_ = ((size_t)7ULL);
v___x_1112_ = lean_usize_dec_le(v___x_1111_, v_x_1054_);
if (v___x_1112_ == 0)
{
lean_object* v___x_1113_; lean_object* v___x_1114_; uint8_t v___x_1115_; 
v___x_1113_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1110_);
v___x_1114_ = lean_unsigned_to_nat(4u);
v___x_1115_ = lean_nat_dec_lt(v___x_1113_, v___x_1114_);
lean_dec(v___x_1113_);
if (v___x_1115_ == 0)
{
lean_object* v_ks_1116_; lean_object* v_vs_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; 
v_ks_1116_ = lean_ctor_get(v_newNode_1110_, 0);
lean_inc_ref(v_ks_1116_);
v_vs_1117_ = lean_ctor_get(v_newNode_1110_, 1);
lean_inc_ref(v_vs_1117_);
lean_dec_ref(v_newNode_1110_);
v___x_1118_ = lean_unsigned_to_nat(0u);
v___x_1119_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__0);
v___x_1120_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__13___redArg(v_x_1054_, v_ks_1116_, v_vs_1117_, v___x_1118_, v___x_1119_);
lean_dec_ref(v_vs_1117_);
lean_dec_ref(v_ks_1116_);
return v___x_1120_;
}
else
{
return v_newNode_1110_;
}
}
else
{
return v_newNode_1110_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1052_ = stack[0].m_obj;
size_t v_x_1053_ = stack[1].m_num;
size_t v_x_1054_ = stack[2].m_num;
lean_object* v_x_1055_ = stack[3].m_obj;
lean_object* v_x_1056_ = stack[4].m_obj;
lean_object* v_res_1123_;
v_res_1123_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg(v_x_1052_, v_x_1053_, v_x_1054_, v_x_1055_, v_x_1056_);
stack->m_obj
 = v_res_1123_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__13___redArg(size_t v_depth_1124_, lean_object* v_keys_1125_, lean_object* v_vals_1126_, lean_object* v_i_1127_, lean_object* v_entries_1128_){
_start:
{
lean_object* v___x_1129_; uint8_t v___x_1130_; 
v___x_1129_ = lean_array_get_size(v_keys_1125_);
v___x_1130_ = lean_nat_dec_lt(v_i_1127_, v___x_1129_);
if (v___x_1130_ == 0)
{
lean_dec(v_i_1127_);
return v_entries_1128_;
}
else
{
lean_object* v_k_1131_; lean_object* v_v_1132_; uint64_t v___x_1133_; size_t v_h_1134_; size_t v___x_1135_; lean_object* v___x_1136_; size_t v___x_1137_; size_t v___x_1138_; size_t v___x_1139_; size_t v_h_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; 
v_k_1131_ = lean_array_fget_borrowed(v_keys_1125_, v_i_1127_);
v_v_1132_ = lean_array_fget_borrowed(v_vals_1126_, v_i_1127_);
v___x_1133_ = l_Lean_instHashableMVarId_hash(v_k_1131_);
v_h_1134_ = lean_uint64_to_usize(v___x_1133_);
v___x_1135_ = ((size_t)5ULL);
v___x_1136_ = lean_unsigned_to_nat(1u);
v___x_1137_ = ((size_t)1ULL);
v___x_1138_ = lean_usize_sub(v_depth_1124_, v___x_1137_);
v___x_1139_ = lean_usize_mul(v___x_1135_, v___x_1138_);
v_h_1140_ = lean_usize_shift_right(v_h_1134_, v___x_1139_);
v___x_1141_ = lean_nat_add(v_i_1127_, v___x_1136_);
lean_dec(v_i_1127_);
lean_inc(v_v_1132_);
lean_inc(v_k_1131_);
v___x_1142_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg(v_entries_1128_, v_h_1140_, v_depth_1124_, v_k_1131_, v_v_1132_);
v_i_1127_ = v___x_1141_;
v_entries_1128_ = v___x_1142_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__13___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_1124_ = stack[0].m_num;
lean_object* v_keys_1125_ = stack[1].m_obj;
lean_object* v_vals_1126_ = stack[2].m_obj;
lean_object* v_i_1127_ = stack[3].m_obj;
lean_object* v_entries_1128_ = stack[4].m_obj;
lean_object* v_res_1144_;
v_res_1144_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__13___redArg(v_depth_1124_, v_keys_1125_, v_vals_1126_, v_i_1127_, v_entries_1128_);
stack->m_obj
 = v_res_1144_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__13___redArg___boxed(lean_object* v_depth_1145_, lean_object* v_keys_1146_, lean_object* v_vals_1147_, lean_object* v_i_1148_, lean_object* v_entries_1149_){
_start:
{
size_t v_depth_boxed_1150_; lean_object* v_res_1151_; 
v_depth_boxed_1150_ = lean_unbox_usize(v_depth_1145_);
lean_dec(v_depth_1145_);
v_res_1151_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__13___redArg(v_depth_boxed_1150_, v_keys_1146_, v_vals_1147_, v_i_1148_, v_entries_1149_);
lean_dec_ref(v_vals_1147_);
lean_dec_ref(v_keys_1146_);
return v_res_1151_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___boxed(lean_object* v_x_1152_, lean_object* v_x_1153_, lean_object* v_x_1154_, lean_object* v_x_1155_, lean_object* v_x_1156_){
_start:
{
size_t v_x_16312__boxed_1157_; size_t v_x_16313__boxed_1158_; lean_object* v_res_1159_; 
v_x_16312__boxed_1157_ = lean_unbox_usize(v_x_1153_);
lean_dec(v_x_1153_);
v_x_16313__boxed_1158_ = lean_unbox_usize(v_x_1154_);
lean_dec(v_x_1154_);
v_res_1159_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg(v_x_1152_, v_x_16312__boxed_1157_, v_x_16313__boxed_1158_, v_x_1155_, v_x_1156_);
return v_res_1159_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3___redArg(lean_object* v_x_1160_, lean_object* v_x_1161_, lean_object* v_x_1162_){
_start:
{
uint64_t v___x_1163_; size_t v___x_1164_; size_t v___x_1165_; lean_object* v___x_1166_; 
v___x_1163_ = l_Lean_instHashableMVarId_hash(v_x_1161_);
v___x_1164_ = lean_uint64_to_usize(v___x_1163_);
v___x_1165_ = ((size_t)1ULL);
v___x_1166_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg(v_x_1160_, v___x_1164_, v___x_1165_, v_x_1161_, v_x_1162_);
return v___x_1166_;
}
}
lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3___redArg(lean_object* v_mvarId_1167_, lean_object* v_val_1168_, lean_object* v___y_1169_){
_start:
{
lean_object* v___x_1171_; lean_object* v_mctx_1172_; lean_object* v_cache_1173_; lean_object* v_zetaDeltaFVarIds_1174_; lean_object* v_postponed_1175_; lean_object* v_diag_1176_; lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1206_; 
v___x_1171_ = lean_st_ref_take(v___y_1169_);
v_mctx_1172_ = lean_ctor_get(v___x_1171_, 0);
v_cache_1173_ = lean_ctor_get(v___x_1171_, 1);
v_zetaDeltaFVarIds_1174_ = lean_ctor_get(v___x_1171_, 2);
v_postponed_1175_ = lean_ctor_get(v___x_1171_, 3);
v_diag_1176_ = lean_ctor_get(v___x_1171_, 4);
v_isSharedCheck_1206_ = !lean_is_exclusive(v___x_1171_);
if (v_isSharedCheck_1206_ == 0)
{
v___x_1178_ = v___x_1171_;
v_isShared_1179_ = v_isSharedCheck_1206_;
goto v_resetjp_1177_;
}
else
{
lean_inc(v_diag_1176_);
lean_inc(v_postponed_1175_);
lean_inc(v_zetaDeltaFVarIds_1174_);
lean_inc(v_cache_1173_);
lean_inc(v_mctx_1172_);
lean_dec(v___x_1171_);
v___x_1178_ = lean_box(0);
v_isShared_1179_ = v_isSharedCheck_1206_;
goto v_resetjp_1177_;
}
v_resetjp_1177_:
{
lean_object* v_depth_1180_; lean_object* v_levelAssignDepth_1181_; lean_object* v_lmvarCounter_1182_; lean_object* v_mvarCounter_1183_; lean_object* v_lDecls_1184_; lean_object* v_decls_1185_; lean_object* v_userNames_1186_; lean_object* v_lAssignment_1187_; lean_object* v_eAssignment_1188_; lean_object* v_dAssignment_1189_; lean_object* v_instanceTypedMVars_1190_; lean_object* v_synthNormMemo_1191_; lean_object* v___x_1193_; uint8_t v_isShared_1194_; uint8_t v_isSharedCheck_1205_; 
v_depth_1180_ = lean_ctor_get(v_mctx_1172_, 0);
v_levelAssignDepth_1181_ = lean_ctor_get(v_mctx_1172_, 1);
v_lmvarCounter_1182_ = lean_ctor_get(v_mctx_1172_, 2);
v_mvarCounter_1183_ = lean_ctor_get(v_mctx_1172_, 3);
v_lDecls_1184_ = lean_ctor_get(v_mctx_1172_, 4);
v_decls_1185_ = lean_ctor_get(v_mctx_1172_, 5);
v_userNames_1186_ = lean_ctor_get(v_mctx_1172_, 6);
v_lAssignment_1187_ = lean_ctor_get(v_mctx_1172_, 7);
v_eAssignment_1188_ = lean_ctor_get(v_mctx_1172_, 8);
v_dAssignment_1189_ = lean_ctor_get(v_mctx_1172_, 9);
v_instanceTypedMVars_1190_ = lean_ctor_get(v_mctx_1172_, 10);
v_synthNormMemo_1191_ = lean_ctor_get(v_mctx_1172_, 11);
v_isSharedCheck_1205_ = !lean_is_exclusive(v_mctx_1172_);
if (v_isSharedCheck_1205_ == 0)
{
v___x_1193_ = v_mctx_1172_;
v_isShared_1194_ = v_isSharedCheck_1205_;
goto v_resetjp_1192_;
}
else
{
lean_inc(v_synthNormMemo_1191_);
lean_inc(v_instanceTypedMVars_1190_);
lean_inc(v_dAssignment_1189_);
lean_inc(v_eAssignment_1188_);
lean_inc(v_lAssignment_1187_);
lean_inc(v_userNames_1186_);
lean_inc(v_decls_1185_);
lean_inc(v_lDecls_1184_);
lean_inc(v_mvarCounter_1183_);
lean_inc(v_lmvarCounter_1182_);
lean_inc(v_levelAssignDepth_1181_);
lean_inc(v_depth_1180_);
lean_dec(v_mctx_1172_);
v___x_1193_ = lean_box(0);
v_isShared_1194_ = v_isSharedCheck_1205_;
goto v_resetjp_1192_;
}
v_resetjp_1192_:
{
lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1198_; 
v___x_1195_ = lean_box(0);
v___x_1196_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3___redArg(v_eAssignment_1188_, v_mvarId_1167_, v_val_1168_);
if (v_isShared_1194_ == 0)
{
lean_ctor_set(v___x_1193_, 8, v___x_1196_);
v___x_1198_ = v___x_1193_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v_depth_1180_);
lean_ctor_set(v_reuseFailAlloc_1204_, 1, v_levelAssignDepth_1181_);
lean_ctor_set(v_reuseFailAlloc_1204_, 2, v_lmvarCounter_1182_);
lean_ctor_set(v_reuseFailAlloc_1204_, 3, v_mvarCounter_1183_);
lean_ctor_set(v_reuseFailAlloc_1204_, 4, v_lDecls_1184_);
lean_ctor_set(v_reuseFailAlloc_1204_, 5, v_decls_1185_);
lean_ctor_set(v_reuseFailAlloc_1204_, 6, v_userNames_1186_);
lean_ctor_set(v_reuseFailAlloc_1204_, 7, v_lAssignment_1187_);
lean_ctor_set(v_reuseFailAlloc_1204_, 8, v___x_1196_);
lean_ctor_set(v_reuseFailAlloc_1204_, 9, v_dAssignment_1189_);
lean_ctor_set(v_reuseFailAlloc_1204_, 10, v_instanceTypedMVars_1190_);
lean_ctor_set(v_reuseFailAlloc_1204_, 11, v_synthNormMemo_1191_);
v___x_1198_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
lean_object* v___x_1200_; 
if (v_isShared_1179_ == 0)
{
lean_ctor_set(v___x_1178_, 0, v___x_1198_);
v___x_1200_ = v___x_1178_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v___x_1198_);
lean_ctor_set(v_reuseFailAlloc_1203_, 1, v_cache_1173_);
lean_ctor_set(v_reuseFailAlloc_1203_, 2, v_zetaDeltaFVarIds_1174_);
lean_ctor_set(v_reuseFailAlloc_1203_, 3, v_postponed_1175_);
lean_ctor_set(v_reuseFailAlloc_1203_, 4, v_diag_1176_);
v___x_1200_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1199_;
}
v_reusejp_1199_:
{
lean_object* v___x_1201_; lean_object* v___x_1202_; 
v___x_1201_ = lean_st_ref_put(v___y_1169_, v___x_1200_);
v___x_1202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1202_, 0, v___x_1195_);
return v___x_1202_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1167_ = stack[0].m_obj;
lean_object* v_val_1168_ = stack[1].m_obj;
lean_object* v___y_1169_ = stack[2].m_obj;
lean_object* v_res_1207_;
v_res_1207_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3___redArg(v_mvarId_1167_, v_val_1168_, v___y_1169_);
stack->m_obj
 = v_res_1207_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3___redArg___boxed(lean_object* v_mvarId_1208_, lean_object* v_val_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_){
_start:
{
lean_object* v_res_1212_; 
v_res_1212_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3___redArg(v_mvarId_1208_, v_val_1209_, v___y_1210_);
lean_dec(v___y_1210_);
return v_res_1212_;
}
}
uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg___lam__0(lean_object* v_x1_1213_, lean_object* v_x2_1214_){
_start:
{
lean_object* v_fst_1215_; lean_object* v_fst_1216_; uint8_t v___x_1217_; 
v_fst_1215_ = lean_ctor_get(v_x1_1213_, 0);
v_fst_1216_ = lean_ctor_get(v_x2_1214_, 0);
v___x_1217_ = lean_nat_dec_lt(v_fst_1215_, v_fst_1216_);
return v___x_1217_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x1_1213_ = stack[0].m_obj;
lean_object* v_x2_1214_ = stack[1].m_obj;
uint8_t v_res_1218_;
v_res_1218_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg___lam__0(v_x1_1213_, v_x2_1214_);
stack->m_num = v_res_1218_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg___lam__0___boxed(lean_object* v_x1_1219_, lean_object* v_x2_1220_){
_start:
{
uint8_t v_res_1221_; lean_object* v_r_1222_; 
v_res_1221_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg___lam__0(v_x1_1219_, v_x2_1220_);
lean_dec_ref(v_x2_1220_);
lean_dec_ref(v_x1_1219_);
v_r_1222_ = lean_box(v_res_1221_);
return v_r_1222_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9_spec__13___redArg(lean_object* v_hi_1223_, lean_object* v_pivot_1224_, lean_object* v_as_1225_, lean_object* v_i_1226_, lean_object* v_k_1227_){
_start:
{
uint8_t v___x_1228_; 
v___x_1228_ = lean_nat_dec_lt(v_k_1227_, v_hi_1223_);
if (v___x_1228_ == 0)
{
lean_object* v___x_1229_; lean_object* v___x_1230_; 
lean_dec(v_k_1227_);
v___x_1229_ = lean_array_fswap(v_as_1225_, v_i_1226_, v_hi_1223_);
v___x_1230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1230_, 0, v_i_1226_);
lean_ctor_set(v___x_1230_, 1, v___x_1229_);
return v___x_1230_;
}
else
{
lean_object* v___x_1231_; lean_object* v_fst_1232_; lean_object* v_fst_1233_; uint8_t v___x_1234_; 
v___x_1231_ = lean_array_fget_borrowed(v_as_1225_, v_k_1227_);
v_fst_1232_ = lean_ctor_get(v___x_1231_, 0);
v_fst_1233_ = lean_ctor_get(v_pivot_1224_, 0);
v___x_1234_ = lean_nat_dec_lt(v_fst_1232_, v_fst_1233_);
if (v___x_1234_ == 0)
{
lean_object* v___x_1235_; lean_object* v___x_1236_; 
v___x_1235_ = lean_unsigned_to_nat(1u);
v___x_1236_ = lean_nat_add(v_k_1227_, v___x_1235_);
lean_dec(v_k_1227_);
v_k_1227_ = v___x_1236_;
goto _start;
}
else
{
lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; 
v___x_1238_ = lean_array_fswap(v_as_1225_, v_i_1226_, v_k_1227_);
v___x_1239_ = lean_unsigned_to_nat(1u);
v___x_1240_ = lean_nat_add(v_i_1226_, v___x_1239_);
lean_dec(v_i_1226_);
v___x_1241_ = lean_nat_add(v_k_1227_, v___x_1239_);
lean_dec(v_k_1227_);
v_as_1225_ = v___x_1238_;
v_i_1226_ = v___x_1240_;
v_k_1227_ = v___x_1241_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9_spec__13___redArg___boxed(lean_object* v_hi_1243_, lean_object* v_pivot_1244_, lean_object* v_as_1245_, lean_object* v_i_1246_, lean_object* v_k_1247_){
_start:
{
lean_object* v_res_1248_; 
v_res_1248_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9_spec__13___redArg(v_hi_1243_, v_pivot_1244_, v_as_1245_, v_i_1246_, v_k_1247_);
lean_dec_ref(v_pivot_1244_);
lean_dec(v_hi_1243_);
return v_res_1248_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg(lean_object* v_n_1249_, lean_object* v_as_1250_, lean_object* v_lo_1251_, lean_object* v_hi_1252_){
_start:
{
lean_object* v___y_1254_; uint8_t v___x_1264_; 
v___x_1264_ = lean_nat_dec_lt(v_lo_1251_, v_hi_1252_);
if (v___x_1264_ == 0)
{
lean_dec(v_lo_1251_);
return v_as_1250_;
}
else
{
lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v_mid_1267_; lean_object* v___y_1269_; lean_object* v___y_1275_; lean_object* v___x_1280_; lean_object* v___x_1281_; uint8_t v___x_1282_; 
v___x_1265_ = lean_nat_add(v_lo_1251_, v_hi_1252_);
v___x_1266_ = lean_unsigned_to_nat(1u);
v_mid_1267_ = lean_nat_shiftr(v___x_1265_, v___x_1266_);
lean_dec(v___x_1265_);
v___x_1280_ = lean_array_fget_borrowed(v_as_1250_, v_mid_1267_);
v___x_1281_ = lean_array_fget_borrowed(v_as_1250_, v_lo_1251_);
v___x_1282_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg___lam__0(v___x_1280_, v___x_1281_);
if (v___x_1282_ == 0)
{
v___y_1275_ = v_as_1250_;
goto v___jp_1274_;
}
else
{
lean_object* v___x_1283_; 
v___x_1283_ = lean_array_fswap(v_as_1250_, v_lo_1251_, v_mid_1267_);
v___y_1275_ = v___x_1283_;
goto v___jp_1274_;
}
v___jp_1268_:
{
lean_object* v___x_1270_; lean_object* v___x_1271_; uint8_t v___x_1272_; 
v___x_1270_ = lean_array_fget_borrowed(v___y_1269_, v_mid_1267_);
v___x_1271_ = lean_array_fget_borrowed(v___y_1269_, v_hi_1252_);
v___x_1272_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg___lam__0(v___x_1270_, v___x_1271_);
if (v___x_1272_ == 0)
{
lean_dec(v_mid_1267_);
v___y_1254_ = v___y_1269_;
goto v___jp_1253_;
}
else
{
lean_object* v___x_1273_; 
v___x_1273_ = lean_array_fswap(v___y_1269_, v_mid_1267_, v_hi_1252_);
lean_dec(v_mid_1267_);
v___y_1254_ = v___x_1273_;
goto v___jp_1253_;
}
}
v___jp_1274_:
{
lean_object* v___x_1276_; lean_object* v___x_1277_; uint8_t v___x_1278_; 
v___x_1276_ = lean_array_fget_borrowed(v___y_1275_, v_hi_1252_);
v___x_1277_ = lean_array_fget_borrowed(v___y_1275_, v_lo_1251_);
v___x_1278_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg___lam__0(v___x_1276_, v___x_1277_);
if (v___x_1278_ == 0)
{
v___y_1269_ = v___y_1275_;
goto v___jp_1268_;
}
else
{
lean_object* v___x_1279_; 
v___x_1279_ = lean_array_fswap(v___y_1275_, v_lo_1251_, v_hi_1252_);
v___y_1269_ = v___x_1279_;
goto v___jp_1268_;
}
}
}
v___jp_1253_:
{
lean_object* v_pivot_1255_; lean_object* v___x_1256_; lean_object* v_fst_1257_; lean_object* v_snd_1258_; uint8_t v___x_1259_; 
v_pivot_1255_ = lean_array_fget(v___y_1254_, v_hi_1252_);
lean_inc_n(v_lo_1251_, 2);
v___x_1256_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9_spec__13___redArg(v_hi_1252_, v_pivot_1255_, v___y_1254_, v_lo_1251_, v_lo_1251_);
lean_dec(v_pivot_1255_);
v_fst_1257_ = lean_ctor_get(v___x_1256_, 0);
lean_inc(v_fst_1257_);
v_snd_1258_ = lean_ctor_get(v___x_1256_, 1);
lean_inc(v_snd_1258_);
lean_dec_ref(v___x_1256_);
v___x_1259_ = lean_nat_dec_le(v_hi_1252_, v_fst_1257_);
if (v___x_1259_ == 0)
{
lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; 
v___x_1260_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg(v_n_1249_, v_snd_1258_, v_lo_1251_, v_fst_1257_);
v___x_1261_ = lean_unsigned_to_nat(1u);
v___x_1262_ = lean_nat_add(v_fst_1257_, v___x_1261_);
lean_dec(v_fst_1257_);
v_as_1250_ = v___x_1260_;
v_lo_1251_ = v___x_1262_;
goto _start;
}
else
{
lean_dec(v_fst_1257_);
lean_dec(v_lo_1251_);
return v_snd_1258_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg___boxed(lean_object* v_n_1284_, lean_object* v_as_1285_, lean_object* v_lo_1286_, lean_object* v_hi_1287_){
_start:
{
lean_object* v_res_1288_; 
v_res_1288_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg(v_n_1284_, v_as_1285_, v_lo_1286_, v_hi_1287_);
lean_dec(v_hi_1287_);
lean_dec(v_n_1284_);
return v_res_1288_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11_spec__13___redArg(lean_object* v_as_1289_, lean_object* v_a_1290_, lean_object* v_x_1291_){
_start:
{
lean_object* v_zero_1292_; uint8_t v_isZero_1293_; 
v_zero_1292_ = lean_unsigned_to_nat(0u);
v_isZero_1293_ = lean_nat_dec_eq(v_x_1291_, v_zero_1292_);
if (v_isZero_1293_ == 1)
{
lean_dec(v_x_1291_);
return v_isZero_1293_;
}
else
{
lean_object* v_fst_1294_; lean_object* v_one_1295_; lean_object* v_n_1296_; lean_object* v___x_1297_; lean_object* v_fst_1298_; uint8_t v___x_1299_; 
v_fst_1294_ = lean_ctor_get(v_a_1290_, 0);
v_one_1295_ = lean_unsigned_to_nat(1u);
v_n_1296_ = lean_nat_sub(v_x_1291_, v_one_1295_);
lean_dec(v_x_1291_);
v___x_1297_ = lean_array_fget_borrowed(v_as_1289_, v_n_1296_);
v_fst_1298_ = lean_ctor_get(v___x_1297_, 0);
v___x_1299_ = lean_nat_dec_eq(v_fst_1294_, v_fst_1298_);
if (v___x_1299_ == 0)
{
v_x_1291_ = v_n_1296_;
goto _start;
}
else
{
lean_dec(v_n_1296_);
return v_isZero_1293_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11_spec__13___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1289_ = stack[0].m_obj;
lean_object* v_a_1290_ = stack[1].m_obj;
lean_object* v_x_1291_ = stack[2].m_obj;
uint8_t v_res_1301_;
v_res_1301_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11_spec__13___redArg(v_as_1289_, v_a_1290_, v_x_1291_);
stack->m_num = v_res_1301_;
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
uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11(lean_object* v_as_1307_, lean_object* v_i_1308_){
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1307_ = stack[0].m_obj;
lean_object* v_i_1308_ = stack[1].m_obj;
uint8_t v_res_1317_;
v_res_1317_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11(v_as_1307_, v_i_1308_);
stack->m_num = v_res_1317_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11___boxed(lean_object* v_as_1318_, lean_object* v_i_1319_){
_start:
{
uint8_t v_res_1320_; lean_object* v_r_1321_; 
v_res_1320_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11(v_as_1318_, v_i_1319_);
lean_dec_ref(v_as_1318_);
v_r_1321_ = lean_box(v_res_1320_);
return v_r_1321_;
}
}
uint8_t l_Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8(lean_object* v_as_1322_){
_start:
{
lean_object* v___x_1323_; uint8_t v___x_1324_; 
v___x_1323_ = lean_unsigned_to_nat(0u);
v___x_1324_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11(v_as_1322_, v___x_1323_);
return v___x_1324_;
}
}
LEAN_EXPORT void l_Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1322_ = stack[0].m_obj;
uint8_t v_res_1325_;
v_res_1325_ = l_Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8(v_as_1322_);
stack->m_num = v_res_1325_;
}
LEAN_EXPORT lean_object* l_Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8___boxed(lean_object* v_as_1326_){
_start:
{
uint8_t v_res_1327_; lean_object* v_r_1328_; 
v_res_1327_ = l_Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8(v_as_1326_);
lean_dec_ref(v_as_1326_);
v_r_1328_ = lean_box(v_res_1327_);
return v_r_1328_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__0(void){
_start:
{
lean_object* v___x_1329_; 
v___x_1329_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1329_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__1(void){
_start:
{
lean_object* v___x_1330_; lean_object* v___x_1331_; 
v___x_1330_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__0, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__0_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__0);
v___x_1331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1331_, 0, v___x_1330_);
return v___x_1331_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__2(void){
_start:
{
lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; 
v___x_1332_ = lean_unsigned_to_nat(0u);
v___x_1333_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__1, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__1_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__1);
v___x_1334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1334_, 0, v___x_1333_);
lean_ctor_set(v___x_1334_, 1, v___x_1332_);
return v___x_1334_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__3(void){
_start:
{
lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; 
v___x_1335_ = lean_unsigned_to_nat(32u);
v___x_1336_ = lean_mk_empty_array_with_capacity(v___x_1335_);
v___x_1337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1337_, 0, v___x_1336_);
return v___x_1337_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__4(void){
_start:
{
size_t v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; 
v___x_1338_ = ((size_t)5ULL);
v___x_1339_ = lean_unsigned_to_nat(0u);
v___x_1340_ = lean_unsigned_to_nat(32u);
v___x_1341_ = lean_mk_empty_array_with_capacity(v___x_1340_);
v___x_1342_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__3, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__3_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__3);
v___x_1343_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1343_, 0, v___x_1342_);
lean_ctor_set(v___x_1343_, 1, v___x_1341_);
lean_ctor_set(v___x_1343_, 2, v___x_1339_);
lean_ctor_set(v___x_1343_, 3, v___x_1339_);
lean_ctor_set_usize(v___x_1343_, 4, v___x_1338_);
return v___x_1343_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__5(void){
_start:
{
lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; 
v___x_1344_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__4, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__4_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__4);
v___x_1345_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__1, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__1_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__1);
v___x_1346_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1346_, 0, v___x_1345_);
lean_ctor_set(v___x_1346_, 1, v___x_1345_);
lean_ctor_set(v___x_1346_, 2, v___x_1345_);
lean_ctor_set(v___x_1346_, 3, v___x_1344_);
return v___x_1346_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__6(void){
_start:
{
lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; 
v___x_1347_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__5, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__5_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__5);
v___x_1348_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__2, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__2_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__2);
v___x_1349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1349_, 0, v___x_1348_);
lean_ctor_set(v___x_1349_, 1, v___x_1347_);
return v___x_1349_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__8(void){
_start:
{
lean_object* v___x_1351_; lean_object* v___x_1352_; 
v___x_1351_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__7));
v___x_1352_ = l_Lean_stringToMessageData(v___x_1351_);
return v___x_1352_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__10(void){
_start:
{
lean_object* v___x_1354_; lean_object* v___x_1355_; 
v___x_1354_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__9));
v___x_1355_ = l_Lean_stringToMessageData(v___x_1354_);
return v___x_1355_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__12(void){
_start:
{
lean_object* v___x_1357_; lean_object* v___x_1358_; 
v___x_1357_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__11));
v___x_1358_ = l_Lean_stringToMessageData(v___x_1357_);
return v___x_1358_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__14(void){
_start:
{
lean_object* v___x_1360_; lean_object* v___x_1361_; 
v___x_1360_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__13));
v___x_1361_ = l_Lean_stringToMessageData(v___x_1360_);
return v___x_1361_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__17(void){
_start:
{
lean_object* v___x_1365_; lean_object* v___x_1366_; 
v___x_1365_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__16));
v___x_1366_ = l_Lean_stringToMessageData(v___x_1365_);
return v___x_1366_;
}
}
lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__6(uint8_t v___x_1387_, lean_object* v___f_1388_, uint8_t v___x_1389_, lean_object* v_stx_1390_, lean_object* v___x_1391_, lean_object* v___x_1392_, lean_object* v___x_1393_, lean_object* v___x_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_){
_start:
{
lean_object* v___y_1405_; lean_object* v_subgoals_1406_; lean_object* v___y_1407_; lean_object* v___y_1408_; lean_object* v___y_1409_; lean_object* v___y_1410_; lean_object* v___y_1411_; lean_object* v___y_1412_; lean_object* v___y_1413_; lean_object* v___y_1414_; lean_object* v___y_1452_; lean_object* v___y_1453_; lean_object* v___y_1454_; lean_object* v___y_1455_; lean_object* v___y_1456_; lean_object* v___y_1457_; lean_object* v___y_1458_; lean_object* v___y_1459_; lean_object* v___y_1460_; lean_object* v___y_1461_; lean_object* v___y_1466_; lean_object* v___y_1467_; lean_object* v___y_1468_; lean_object* v___y_1469_; lean_object* v___y_1470_; lean_object* v___y_1471_; lean_object* v___y_1472_; lean_object* v___y_1473_; lean_object* v___y_1474_; lean_object* v___y_1475_; lean_object* v___y_1476_; lean_object* v___y_1477_; lean_object* v___y_1478_; lean_object* v___y_1481_; lean_object* v___y_1482_; lean_object* v___y_1483_; lean_object* v___y_1484_; lean_object* v___y_1485_; lean_object* v___y_1486_; lean_object* v___y_1487_; lean_object* v___y_1488_; lean_object* v___y_1489_; lean_object* v___y_1490_; lean_object* v___y_1491_; lean_object* v___y_1492_; lean_object* v___y_1493_; 
if (v___x_1387_ == 0)
{
lean_object* v___x_1495_; 
lean_dec_ref(v___x_1394_);
lean_dec_ref(v___x_1393_);
lean_dec_ref(v___x_1392_);
lean_dec_ref(v___x_1391_);
lean_dec_ref(v___f_1388_);
v___x_1495_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1___redArg();
return v___x_1495_;
}
else
{
lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___y_1499_; lean_object* v___y_1500_; lean_object* v___y_1501_; lean_object* v___y_1502_; lean_object* v___y_1503_; lean_object* v___y_1504_; lean_object* v___y_1505_; lean_object* v___y_1506_; lean_object* v___y_1507_; lean_object* v___y_1508_; lean_object* v___y_1514_; lean_object* v___y_1515_; lean_object* v___y_1516_; lean_object* v___y_1517_; lean_object* v___y_1518_; lean_object* v___y_1519_; lean_object* v___y_1520_; lean_object* v___y_1521_; lean_object* v___y_1522_; lean_object* v___y_1523_; lean_object* v___y_1524_; lean_object* v___y_1525_; lean_object* v___y_1526_; lean_object* v___y_1527_; lean_object* v___y_1528_; uint8_t v___y_1529_; lean_object* v___y_1622_; lean_object* v___y_1623_; lean_object* v___y_1624_; lean_object* v___y_1625_; lean_object* v___y_1626_; lean_object* v_occs_1627_; lean_object* v___y_1628_; lean_object* v___y_1629_; lean_object* v___y_1630_; lean_object* v___y_1631_; lean_object* v___y_1632_; lean_object* v___y_1633_; lean_object* v___y_1634_; lean_object* v___y_1635_; lean_object* v___y_1650_; lean_object* v___y_1651_; lean_object* v___y_1652_; lean_object* v___y_1653_; lean_object* v___y_1654_; lean_object* v___y_1655_; lean_object* v___y_1656_; lean_object* v___y_1657_; lean_object* v___y_1658_; lean_object* v___y_1659_; lean_object* v___y_1660_; lean_object* v___y_1661_; lean_object* v___y_1662_; lean_object* v___y_1663_; lean_object* v___y_1668_; lean_object* v___y_1669_; lean_object* v___y_1670_; lean_object* v___y_1671_; lean_object* v___y_1672_; lean_object* v___y_1673_; lean_object* v___y_1674_; lean_object* v___y_1675_; lean_object* v___y_1676_; lean_object* v___y_1677_; lean_object* v___y_1678_; lean_object* v___y_1679_; lean_object* v___y_1680_; lean_object* v___y_1681_; lean_object* v___y_1686_; lean_object* v___y_1687_; lean_object* v___y_1688_; lean_object* v___y_1689_; lean_object* v___y_1690_; lean_object* v___y_1691_; lean_object* v___y_1692_; lean_object* v___y_1693_; lean_object* v___y_1694_; lean_object* v___y_1695_; lean_object* v___y_1696_; lean_object* v___y_1697_; lean_object* v___y_1698_; lean_object* v___y_1699_; lean_object* v___y_1700_; lean_object* v___y_1701_; lean_object* v___y_1702_; lean_object* v___y_1705_; lean_object* v___y_1706_; lean_object* v___y_1707_; lean_object* v___y_1708_; lean_object* v___y_1709_; lean_object* v___y_1710_; lean_object* v___y_1711_; lean_object* v___y_1712_; lean_object* v___y_1713_; lean_object* v___y_1714_; lean_object* v___y_1715_; lean_object* v___y_1716_; lean_object* v___y_1717_; lean_object* v___y_1718_; lean_object* v___y_1719_; lean_object* v___y_1720_; lean_object* v___y_1721_; lean_object* v_occs_1724_; lean_object* v___y_1725_; lean_object* v___y_1726_; lean_object* v___y_1727_; lean_object* v___y_1728_; lean_object* v___y_1729_; lean_object* v___y_1730_; lean_object* v___y_1731_; lean_object* v___y_1732_; lean_object* v___x_1819_; uint8_t v___x_1820_; 
v___x_1496_ = lean_unsigned_to_nat(0u);
v___x_1497_ = lean_unsigned_to_nat(1u);
v___x_1819_ = l_Lean_Syntax_getArg(v_stx_1390_, v___x_1497_);
v___x_1820_ = l_Lean_Syntax_isNone(v___x_1819_);
if (v___x_1820_ == 0)
{
uint8_t v___x_1821_; 
lean_inc(v___x_1819_);
v___x_1821_ = l_Lean_Syntax_matchesNull(v___x_1819_, v___x_1497_);
if (v___x_1821_ == 0)
{
lean_object* v___x_1822_; 
lean_dec(v___x_1819_);
lean_dec_ref(v___x_1394_);
lean_dec_ref(v___x_1393_);
lean_dec_ref(v___x_1392_);
lean_dec_ref(v___x_1391_);
lean_dec_ref(v___f_1388_);
v___x_1822_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1___redArg();
return v___x_1822_;
}
else
{
lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; uint8_t v___x_1826_; 
v___x_1823_ = l_Lean_Syntax_getArg(v___x_1819_, v___x_1496_);
lean_dec(v___x_1819_);
v___x_1824_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__27));
lean_inc_ref(v___x_1394_);
lean_inc_ref(v___x_1393_);
lean_inc_ref(v___x_1392_);
lean_inc_ref(v___x_1391_);
v___x_1825_ = l_Lean_Name_mkStr5(v___x_1391_, v___x_1392_, v___x_1393_, v___x_1394_, v___x_1824_);
lean_inc(v___x_1823_);
v___x_1826_ = l_Lean_Syntax_isOfKind(v___x_1823_, v___x_1825_);
lean_dec(v___x_1825_);
if (v___x_1826_ == 0)
{
lean_object* v___x_1827_; 
lean_dec(v___x_1823_);
lean_dec_ref(v___x_1394_);
lean_dec_ref(v___x_1393_);
lean_dec_ref(v___x_1392_);
lean_dec_ref(v___x_1391_);
lean_dec_ref(v___f_1388_);
v___x_1827_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1___redArg();
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
v_occs_1724_ = v___x_1830_;
v___y_1725_ = v___y_1395_;
v___y_1726_ = v___y_1396_;
v___y_1727_ = v___y_1397_;
v___y_1728_ = v___y_1398_;
v___y_1729_ = v___y_1399_;
v___y_1730_ = v___y_1400_;
v___y_1731_ = v___y_1401_;
v___y_1732_ = v___y_1402_;
goto v___jp_1723_;
}
}
}
else
{
lean_object* v___x_1831_; 
lean_dec(v___x_1819_);
v___x_1831_ = lean_box(0);
v_occs_1724_ = v___x_1831_;
v___y_1725_ = v___y_1395_;
v___y_1726_ = v___y_1396_;
v___y_1727_ = v___y_1397_;
v___y_1728_ = v___y_1398_;
v___y_1729_ = v___y_1399_;
v___y_1730_ = v___y_1400_;
v___y_1731_ = v___y_1401_;
v___y_1732_ = v___y_1402_;
goto v___jp_1723_;
}
v___jp_1498_:
{
lean_object* v___x_1509_; uint8_t v___x_1510_; 
v___x_1509_ = lean_array_get_size(v___y_1499_);
v___x_1510_ = lean_nat_dec_eq(v___x_1509_, v___x_1496_);
if (v___x_1510_ == 0)
{
lean_object* v___x_1511_; uint8_t v___x_1512_; 
v___x_1511_ = lean_nat_sub(v___x_1509_, v___x_1497_);
v___x_1512_ = lean_nat_dec_le(v___x_1496_, v___x_1511_);
if (v___x_1512_ == 0)
{
lean_inc(v___x_1511_);
v___y_1481_ = v___y_1504_;
v___y_1482_ = v___y_1499_;
v___y_1483_ = v___y_1502_;
v___y_1484_ = v___y_1505_;
v___y_1485_ = v___y_1501_;
v___y_1486_ = v___y_1503_;
v___y_1487_ = v___y_1506_;
v___y_1488_ = v___x_1511_;
v___y_1489_ = v___y_1500_;
v___y_1490_ = v___x_1509_;
v___y_1491_ = v___y_1507_;
v___y_1492_ = v___y_1508_;
v___y_1493_ = v___x_1511_;
goto v___jp_1480_;
}
else
{
v___y_1481_ = v___y_1504_;
v___y_1482_ = v___y_1499_;
v___y_1483_ = v___y_1502_;
v___y_1484_ = v___y_1505_;
v___y_1485_ = v___y_1501_;
v___y_1486_ = v___y_1503_;
v___y_1487_ = v___y_1506_;
v___y_1488_ = v___x_1511_;
v___y_1489_ = v___y_1500_;
v___y_1490_ = v___x_1509_;
v___y_1491_ = v___y_1507_;
v___y_1492_ = v___y_1508_;
v___y_1493_ = v___x_1496_;
goto v___jp_1480_;
}
}
else
{
v___y_1452_ = v___y_1506_;
v___y_1453_ = v___y_1504_;
v___y_1454_ = v___y_1502_;
v___y_1455_ = v___y_1505_;
v___y_1456_ = v___y_1500_;
v___y_1457_ = v___y_1507_;
v___y_1458_ = v___y_1501_;
v___y_1459_ = v___y_1503_;
v___y_1460_ = v___y_1508_;
v___y_1461_ = v___y_1499_;
goto v___jp_1451_;
}
}
v___jp_1513_:
{
lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; 
v___x_1530_ = l_Lean_Meta_Simp_Context_setMemoize(v___y_1523_, v___y_1529_);
v___x_1531_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__6, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__6_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__6);
lean_inc(v___y_1527_);
lean_inc_ref(v___y_1518_);
v___x_1532_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre___boxed), 11, 2);
lean_closure_set(v___x_1532_, 0, v___y_1518_);
lean_closure_set(v___x_1532_, 1, v___y_1527_);
lean_inc_ref(v___y_1517_);
lean_inc_ref(v___y_1525_);
v___x_1533_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_1533_, 0, v___x_1532_);
lean_ctor_set(v___x_1533_, 1, v___y_1522_);
lean_ctor_set(v___x_1533_, 2, v___y_1525_);
lean_ctor_set(v___x_1533_, 3, v___f_1388_);
lean_ctor_set(v___x_1533_, 4, v___y_1517_);
lean_ctor_set_uint8(v___x_1533_, sizeof(void*)*5, v___x_1389_);
v___x_1534_ = l_Lean_Meta_Simp_main(v___y_1524_, v___x_1530_, v___x_1531_, v___x_1533_, v___y_1526_, v___y_1528_, v___y_1515_, v___y_1514_);
if (lean_obj_tag(v___x_1534_) == 0)
{
lean_object* v_a_1535_; lean_object* v_fst_1536_; lean_object* v___x_1538_; uint8_t v_isShared_1539_; uint8_t v_isSharedCheck_1611_; 
v_a_1535_ = lean_ctor_get(v___x_1534_, 0);
lean_inc(v_a_1535_);
lean_dec_ref_known(v___x_1534_, 1);
v_fst_1536_ = lean_ctor_get(v_a_1535_, 0);
v_isSharedCheck_1611_ = !lean_is_exclusive(v_a_1535_);
if (v_isSharedCheck_1611_ == 0)
{
lean_object* v_unused_1612_; 
v_unused_1612_ = lean_ctor_get(v_a_1535_, 1);
lean_dec(v_unused_1612_);
v___x_1538_ = v_a_1535_;
v_isShared_1539_ = v_isSharedCheck_1611_;
goto v_resetjp_1537_;
}
else
{
lean_inc(v_fst_1536_);
lean_dec(v_a_1535_);
v___x_1538_ = lean_box(0);
v_isShared_1539_ = v_isSharedCheck_1611_;
goto v_resetjp_1537_;
}
v_resetjp_1537_:
{
lean_object* v___x_1540_; 
v___x_1540_ = lean_st_ref_get(v___y_1527_);
lean_dec(v___y_1527_);
if (lean_obj_tag(v___x_1540_) == 0)
{
lean_object* v_subgoals_1541_; lean_object* v___x_1542_; uint8_t v___x_1543_; 
v_subgoals_1541_ = lean_ctor_get(v___x_1540_, 0);
lean_inc_ref(v_subgoals_1541_);
lean_dec_ref_known(v___x_1540_, 1);
v___x_1542_ = lean_array_get_size(v_subgoals_1541_);
v___x_1543_ = lean_nat_dec_eq(v___x_1542_, v___x_1496_);
if (v___x_1543_ == 0)
{
lean_del_object(v___x_1538_);
lean_dec_ref(v___y_1518_);
v___y_1405_ = v_fst_1536_;
v_subgoals_1406_ = v_subgoals_1541_;
v___y_1407_ = v___y_1519_;
v___y_1408_ = v___y_1521_;
v___y_1409_ = v___y_1520_;
v___y_1410_ = v___y_1516_;
v___y_1411_ = v___y_1526_;
v___y_1412_ = v___y_1528_;
v___y_1413_ = v___y_1515_;
v___y_1414_ = v___y_1514_;
goto v___jp_1404_;
}
else
{
lean_object* v_expr_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1548_; 
lean_dec_ref(v_subgoals_1541_);
lean_dec(v_fst_1536_);
v_expr_1544_ = lean_ctor_get(v___y_1518_, 2);
lean_inc_ref(v_expr_1544_);
lean_dec_ref(v___y_1518_);
v___x_1545_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__8, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__8_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__8);
v___x_1546_ = l_Lean_indentExpr(v_expr_1544_);
if (v_isShared_1539_ == 0)
{
lean_ctor_set_tag(v___x_1538_, 7);
lean_ctor_set(v___x_1538_, 1, v___x_1546_);
lean_ctor_set(v___x_1538_, 0, v___x_1545_);
v___x_1548_ = v___x_1538_;
goto v_reusejp_1547_;
}
else
{
lean_object* v_reuseFailAlloc_1558_; 
v_reuseFailAlloc_1558_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1558_, 0, v___x_1545_);
lean_ctor_set(v_reuseFailAlloc_1558_, 1, v___x_1546_);
v___x_1548_ = v_reuseFailAlloc_1558_;
goto v_reusejp_1547_;
}
v_reusejp_1547_:
{
lean_object* v___x_1549_; lean_object* v_a_1550_; lean_object* v___x_1552_; uint8_t v_isShared_1553_; uint8_t v_isSharedCheck_1557_; 
v___x_1549_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg(v___x_1548_, v___y_1526_, v___y_1528_, v___y_1515_, v___y_1514_);
v_a_1550_ = lean_ctor_get(v___x_1549_, 0);
v_isSharedCheck_1557_ = !lean_is_exclusive(v___x_1549_);
if (v_isSharedCheck_1557_ == 0)
{
v___x_1552_ = v___x_1549_;
v_isShared_1553_ = v_isSharedCheck_1557_;
goto v_resetjp_1551_;
}
else
{
lean_inc(v_a_1550_);
lean_dec(v___x_1549_);
v___x_1552_ = lean_box(0);
v_isShared_1553_ = v_isSharedCheck_1557_;
goto v_resetjp_1551_;
}
v_resetjp_1551_:
{
lean_object* v___x_1555_; 
if (v_isShared_1553_ == 0)
{
v___x_1555_ = v___x_1552_;
goto v_reusejp_1554_;
}
else
{
lean_object* v_reuseFailAlloc_1556_; 
v_reuseFailAlloc_1556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1556_, 0, v_a_1550_);
v___x_1555_ = v_reuseFailAlloc_1556_;
goto v_reusejp_1554_;
}
v_reusejp_1554_:
{
return v___x_1555_;
}
}
}
}
}
else
{
lean_object* v_subgoals_1559_; lean_object* v_idx_1560_; lean_object* v_remaining_1561_; uint8_t v___x_1562_; 
v_subgoals_1559_ = lean_ctor_get(v___x_1540_, 0);
lean_inc_ref(v_subgoals_1559_);
v_idx_1560_ = lean_ctor_get(v___x_1540_, 1);
lean_inc(v_idx_1560_);
v_remaining_1561_ = lean_ctor_get(v___x_1540_, 2);
lean_inc(v_remaining_1561_);
lean_dec_ref_known(v___x_1540_, 3);
v___x_1562_ = lean_nat_dec_eq(v_idx_1560_, v___x_1496_);
if (v___x_1562_ == 0)
{
lean_object* v___x_1563_; 
lean_dec_ref(v___y_1518_);
v___x_1563_ = l_List_getLast_x3f___redArg(v_remaining_1561_);
lean_dec(v_remaining_1561_);
if (lean_obj_tag(v___x_1563_) == 1)
{
lean_object* v_val_1564_; lean_object* v___x_1566_; uint8_t v_isShared_1567_; uint8_t v_isSharedCheck_1595_; 
lean_dec_ref(v_subgoals_1559_);
lean_dec(v_fst_1536_);
v_val_1564_ = lean_ctor_get(v___x_1563_, 0);
v_isSharedCheck_1595_ = !lean_is_exclusive(v___x_1563_);
if (v_isSharedCheck_1595_ == 0)
{
v___x_1566_ = v___x_1563_;
v_isShared_1567_ = v_isSharedCheck_1595_;
goto v_resetjp_1565_;
}
else
{
lean_inc(v_val_1564_);
lean_dec(v___x_1563_);
v___x_1566_ = lean_box(0);
v_isShared_1567_ = v_isSharedCheck_1595_;
goto v_resetjp_1565_;
}
v_resetjp_1565_:
{
lean_object* v_fst_1568_; lean_object* v___x_1570_; uint8_t v_isShared_1571_; uint8_t v_isSharedCheck_1593_; 
v_fst_1568_ = lean_ctor_get(v_val_1564_, 0);
v_isSharedCheck_1593_ = !lean_is_exclusive(v_val_1564_);
if (v_isSharedCheck_1593_ == 0)
{
lean_object* v_unused_1594_; 
v_unused_1594_ = lean_ctor_get(v_val_1564_, 1);
lean_dec(v_unused_1594_);
v___x_1570_ = v_val_1564_;
v_isShared_1571_ = v_isSharedCheck_1593_;
goto v_resetjp_1569_;
}
else
{
lean_inc(v_fst_1568_);
lean_dec(v_val_1564_);
v___x_1570_ = lean_box(0);
v_isShared_1571_ = v_isSharedCheck_1593_;
goto v_resetjp_1569_;
}
v_resetjp_1569_:
{
lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1575_; 
v___x_1572_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__10, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__10_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__10);
v___x_1573_ = l_Nat_reprFast(v_idx_1560_);
if (v_isShared_1567_ == 0)
{
lean_ctor_set_tag(v___x_1566_, 3);
lean_ctor_set(v___x_1566_, 0, v___x_1573_);
v___x_1575_ = v___x_1566_;
goto v_reusejp_1574_;
}
else
{
lean_object* v_reuseFailAlloc_1592_; 
v_reuseFailAlloc_1592_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1592_, 0, v___x_1573_);
v___x_1575_ = v_reuseFailAlloc_1592_;
goto v_reusejp_1574_;
}
v_reusejp_1574_:
{
lean_object* v___x_1576_; lean_object* v___x_1578_; 
v___x_1576_ = l_Lean_MessageData_ofFormat(v___x_1575_);
if (v_isShared_1571_ == 0)
{
lean_ctor_set_tag(v___x_1570_, 7);
lean_ctor_set(v___x_1570_, 1, v___x_1576_);
lean_ctor_set(v___x_1570_, 0, v___x_1572_);
v___x_1578_ = v___x_1570_;
goto v_reusejp_1577_;
}
else
{
lean_object* v_reuseFailAlloc_1591_; 
v_reuseFailAlloc_1591_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1591_, 0, v___x_1572_);
lean_ctor_set(v_reuseFailAlloc_1591_, 1, v___x_1576_);
v___x_1578_ = v_reuseFailAlloc_1591_;
goto v_reusejp_1577_;
}
v_reusejp_1577_:
{
lean_object* v___x_1579_; lean_object* v___x_1581_; 
v___x_1579_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__12, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__12_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__12);
if (v_isShared_1539_ == 0)
{
lean_ctor_set_tag(v___x_1538_, 7);
lean_ctor_set(v___x_1538_, 1, v___x_1579_);
lean_ctor_set(v___x_1538_, 0, v___x_1578_);
v___x_1581_ = v___x_1538_;
goto v_reusejp_1580_;
}
else
{
lean_object* v_reuseFailAlloc_1590_; 
v_reuseFailAlloc_1590_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1590_, 0, v___x_1578_);
lean_ctor_set(v_reuseFailAlloc_1590_, 1, v___x_1579_);
v___x_1581_ = v_reuseFailAlloc_1590_;
goto v_reusejp_1580_;
}
v_reusejp_1580_:
{
lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; 
v___x_1582_ = lean_nat_add(v_fst_1568_, v___x_1497_);
lean_dec(v_fst_1568_);
v___x_1583_ = l_Nat_reprFast(v___x_1582_);
v___x_1584_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1584_, 0, v___x_1583_);
v___x_1585_ = l_Lean_MessageData_ofFormat(v___x_1584_);
v___x_1586_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1586_, 0, v___x_1581_);
lean_ctor_set(v___x_1586_, 1, v___x_1585_);
v___x_1587_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__14, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__14_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__14);
v___x_1588_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1588_, 0, v___x_1586_);
lean_ctor_set(v___x_1588_, 1, v___x_1587_);
v___x_1589_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg(v___x_1588_, v___y_1526_, v___y_1528_, v___y_1515_, v___y_1514_);
return v___x_1589_;
}
}
}
}
}
}
else
{
lean_dec(v___x_1563_);
lean_dec(v_idx_1560_);
lean_del_object(v___x_1538_);
v___y_1499_ = v_subgoals_1559_;
v___y_1500_ = v_fst_1536_;
v___y_1501_ = v___y_1519_;
v___y_1502_ = v___y_1521_;
v___y_1503_ = v___y_1520_;
v___y_1504_ = v___y_1516_;
v___y_1505_ = v___y_1526_;
v___y_1506_ = v___y_1528_;
v___y_1507_ = v___y_1515_;
v___y_1508_ = v___y_1514_;
goto v___jp_1498_;
}
}
else
{
lean_object* v_expr_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1600_; 
lean_dec(v_remaining_1561_);
lean_dec(v_idx_1560_);
lean_dec_ref(v_subgoals_1559_);
lean_dec(v_fst_1536_);
v_expr_1596_ = lean_ctor_get(v___y_1518_, 2);
lean_inc_ref(v_expr_1596_);
lean_dec_ref(v___y_1518_);
v___x_1597_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__8, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__8_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__8);
v___x_1598_ = l_Lean_indentExpr(v_expr_1596_);
if (v_isShared_1539_ == 0)
{
lean_ctor_set_tag(v___x_1538_, 7);
lean_ctor_set(v___x_1538_, 1, v___x_1598_);
lean_ctor_set(v___x_1538_, 0, v___x_1597_);
v___x_1600_ = v___x_1538_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v___x_1597_);
lean_ctor_set(v_reuseFailAlloc_1610_, 1, v___x_1598_);
v___x_1600_ = v_reuseFailAlloc_1610_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
lean_object* v___x_1601_; lean_object* v_a_1602_; lean_object* v___x_1604_; uint8_t v_isShared_1605_; uint8_t v_isSharedCheck_1609_; 
v___x_1601_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg(v___x_1600_, v___y_1526_, v___y_1528_, v___y_1515_, v___y_1514_);
v_a_1602_ = lean_ctor_get(v___x_1601_, 0);
v_isSharedCheck_1609_ = !lean_is_exclusive(v___x_1601_);
if (v_isSharedCheck_1609_ == 0)
{
v___x_1604_ = v___x_1601_;
v_isShared_1605_ = v_isSharedCheck_1609_;
goto v_resetjp_1603_;
}
else
{
lean_inc(v_a_1602_);
lean_dec(v___x_1601_);
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
}
}
}
else
{
lean_object* v_a_1613_; lean_object* v___x_1615_; uint8_t v_isShared_1616_; uint8_t v_isSharedCheck_1620_; 
lean_dec(v___y_1527_);
lean_dec_ref(v___y_1518_);
v_a_1613_ = lean_ctor_get(v___x_1534_, 0);
v_isSharedCheck_1620_ = !lean_is_exclusive(v___x_1534_);
if (v_isSharedCheck_1620_ == 0)
{
v___x_1615_ = v___x_1534_;
v_isShared_1616_ = v_isSharedCheck_1620_;
goto v_resetjp_1614_;
}
else
{
lean_inc(v_a_1613_);
lean_dec(v___x_1534_);
v___x_1615_ = lean_box(0);
v_isShared_1616_ = v_isSharedCheck_1620_;
goto v_resetjp_1614_;
}
v_resetjp_1614_:
{
lean_object* v___x_1618_; 
if (v_isShared_1616_ == 0)
{
v___x_1618_ = v___x_1615_;
goto v_reusejp_1617_;
}
else
{
lean_object* v_reuseFailAlloc_1619_; 
v_reuseFailAlloc_1619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1619_, 0, v_a_1613_);
v___x_1618_ = v_reuseFailAlloc_1619_;
goto v_reusejp_1617_;
}
v_reusejp_1617_:
{
return v___x_1618_;
}
}
}
}
v___jp_1621_:
{
lean_object* v___x_1636_; lean_object* v___x_1637_; 
lean_inc_ref(v_occs_1627_);
v___x_1636_ = lean_st_mk_ref(v_occs_1627_);
v___x_1637_ = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_getContext___redArg(v___y_1632_, v___y_1634_, v___y_1635_);
if (lean_obj_tag(v___x_1637_) == 0)
{
if (lean_obj_tag(v_occs_1627_) == 0)
{
lean_object* v_a_1638_; 
lean_dec_ref_known(v_occs_1627_, 1);
v_a_1638_ = lean_ctor_get(v___x_1637_, 0);
lean_inc(v_a_1638_);
lean_dec_ref_known(v___x_1637_, 1);
v___y_1514_ = v___y_1635_;
v___y_1515_ = v___y_1634_;
v___y_1516_ = v___y_1631_;
v___y_1517_ = v___y_1625_;
v___y_1518_ = v___y_1626_;
v___y_1519_ = v___y_1628_;
v___y_1520_ = v___y_1630_;
v___y_1521_ = v___y_1629_;
v___y_1522_ = v___y_1622_;
v___y_1523_ = v_a_1638_;
v___y_1524_ = v___y_1623_;
v___y_1525_ = v___y_1624_;
v___y_1526_ = v___y_1632_;
v___y_1527_ = v___x_1636_;
v___y_1528_ = v___y_1633_;
v___y_1529_ = v___x_1389_;
goto v___jp_1513_;
}
else
{
lean_object* v_a_1639_; uint8_t v___x_1640_; 
lean_dec_ref(v_occs_1627_);
v_a_1639_ = lean_ctor_get(v___x_1637_, 0);
lean_inc(v_a_1639_);
lean_dec_ref_known(v___x_1637_, 1);
v___x_1640_ = 0;
v___y_1514_ = v___y_1635_;
v___y_1515_ = v___y_1634_;
v___y_1516_ = v___y_1631_;
v___y_1517_ = v___y_1625_;
v___y_1518_ = v___y_1626_;
v___y_1519_ = v___y_1628_;
v___y_1520_ = v___y_1630_;
v___y_1521_ = v___y_1629_;
v___y_1522_ = v___y_1622_;
v___y_1523_ = v_a_1639_;
v___y_1524_ = v___y_1623_;
v___y_1525_ = v___y_1624_;
v___y_1526_ = v___y_1632_;
v___y_1527_ = v___x_1636_;
v___y_1528_ = v___y_1633_;
v___y_1529_ = v___x_1640_;
goto v___jp_1513_;
}
}
else
{
lean_object* v_a_1641_; lean_object* v___x_1643_; uint8_t v_isShared_1644_; uint8_t v_isSharedCheck_1648_; 
lean_dec(v___x_1636_);
lean_dec_ref(v_occs_1627_);
lean_dec_ref(v___y_1626_);
lean_dec_ref(v___y_1623_);
lean_dec_ref(v___y_1622_);
lean_dec_ref(v___f_1388_);
v_a_1641_ = lean_ctor_get(v___x_1637_, 0);
v_isSharedCheck_1648_ = !lean_is_exclusive(v___x_1637_);
if (v_isSharedCheck_1648_ == 0)
{
v___x_1643_ = v___x_1637_;
v_isShared_1644_ = v_isSharedCheck_1648_;
goto v_resetjp_1642_;
}
else
{
lean_inc(v_a_1641_);
lean_dec(v___x_1637_);
v___x_1643_ = lean_box(0);
v_isShared_1644_ = v_isSharedCheck_1648_;
goto v_resetjp_1642_;
}
v_resetjp_1642_:
{
lean_object* v___x_1646_; 
if (v_isShared_1644_ == 0)
{
v___x_1646_ = v___x_1643_;
goto v_reusejp_1645_;
}
else
{
lean_object* v_reuseFailAlloc_1647_; 
v_reuseFailAlloc_1647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1647_, 0, v_a_1641_);
v___x_1646_ = v_reuseFailAlloc_1647_;
goto v_reusejp_1645_;
}
v_reusejp_1645_:
{
return v___x_1646_;
}
}
}
}
v___jp_1649_:
{
lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; 
v___x_1664_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__15));
v___x_1665_ = lean_array_to_list(v___y_1654_);
v___x_1666_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1666_, 0, v___x_1664_);
lean_ctor_set(v___x_1666_, 1, v___x_1496_);
lean_ctor_set(v___x_1666_, 2, v___x_1665_);
v___y_1622_ = v___y_1650_;
v___y_1623_ = v___y_1651_;
v___y_1624_ = v___y_1652_;
v___y_1625_ = v___y_1653_;
v___y_1626_ = v___y_1655_;
v_occs_1627_ = v___x_1666_;
v___y_1628_ = v___y_1656_;
v___y_1629_ = v___y_1657_;
v___y_1630_ = v___y_1658_;
v___y_1631_ = v___y_1659_;
v___y_1632_ = v___y_1660_;
v___y_1633_ = v___y_1661_;
v___y_1634_ = v___y_1662_;
v___y_1635_ = v___y_1663_;
goto v___jp_1621_;
}
v___jp_1667_:
{
uint8_t v___x_1682_; 
v___x_1682_ = l_Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8(v___y_1681_);
if (v___x_1682_ == 0)
{
lean_object* v___x_1683_; lean_object* v___x_1684_; 
lean_dec_ref(v___y_1681_);
lean_dec_ref(v___y_1676_);
lean_dec_ref(v___y_1674_);
lean_dec_ref(v___y_1671_);
lean_dec_ref(v___f_1388_);
v___x_1683_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__17, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__17_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__17);
v___x_1684_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg(v___x_1683_, v___y_1677_, v___y_1679_, v___y_1672_, v___y_1673_);
return v___x_1684_;
}
else
{
v___y_1650_ = v___y_1674_;
v___y_1651_ = v___y_1676_;
v___y_1652_ = v___y_1678_;
v___y_1653_ = v___y_1669_;
v___y_1654_ = v___y_1681_;
v___y_1655_ = v___y_1671_;
v___y_1656_ = v___y_1670_;
v___y_1657_ = v___y_1675_;
v___y_1658_ = v___y_1668_;
v___y_1659_ = v___y_1680_;
v___y_1660_ = v___y_1677_;
v___y_1661_ = v___y_1679_;
v___y_1662_ = v___y_1672_;
v___y_1663_ = v___y_1673_;
goto v___jp_1649_;
}
}
v___jp_1685_:
{
lean_object* v___x_1703_; 
v___x_1703_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg(v___y_1699_, v___y_1692_, v___y_1687_, v___y_1702_);
lean_dec(v___y_1702_);
lean_dec(v___y_1699_);
v___y_1668_ = v___y_1686_;
v___y_1669_ = v___y_1688_;
v___y_1670_ = v___y_1689_;
v___y_1671_ = v___y_1690_;
v___y_1672_ = v___y_1691_;
v___y_1673_ = v___y_1693_;
v___y_1674_ = v___y_1694_;
v___y_1675_ = v___y_1695_;
v___y_1676_ = v___y_1696_;
v___y_1677_ = v___y_1697_;
v___y_1678_ = v___y_1698_;
v___y_1679_ = v___y_1700_;
v___y_1680_ = v___y_1701_;
v___y_1681_ = v___x_1703_;
goto v___jp_1667_;
}
v___jp_1704_:
{
uint8_t v___x_1722_; 
v___x_1722_ = lean_nat_dec_le(v___y_1721_, v___y_1718_);
if (v___x_1722_ == 0)
{
lean_dec(v___y_1718_);
lean_inc(v___y_1721_);
v___y_1686_ = v___y_1705_;
v___y_1687_ = v___y_1721_;
v___y_1688_ = v___y_1706_;
v___y_1689_ = v___y_1707_;
v___y_1690_ = v___y_1708_;
v___y_1691_ = v___y_1709_;
v___y_1692_ = v___y_1710_;
v___y_1693_ = v___y_1711_;
v___y_1694_ = v___y_1712_;
v___y_1695_ = v___y_1713_;
v___y_1696_ = v___y_1714_;
v___y_1697_ = v___y_1715_;
v___y_1698_ = v___y_1717_;
v___y_1699_ = v___y_1716_;
v___y_1700_ = v___y_1719_;
v___y_1701_ = v___y_1720_;
v___y_1702_ = v___y_1721_;
goto v___jp_1685_;
}
else
{
v___y_1686_ = v___y_1705_;
v___y_1687_ = v___y_1721_;
v___y_1688_ = v___y_1706_;
v___y_1689_ = v___y_1707_;
v___y_1690_ = v___y_1708_;
v___y_1691_ = v___y_1709_;
v___y_1692_ = v___y_1710_;
v___y_1693_ = v___y_1711_;
v___y_1694_ = v___y_1712_;
v___y_1695_ = v___y_1713_;
v___y_1696_ = v___y_1714_;
v___y_1697_ = v___y_1715_;
v___y_1698_ = v___y_1717_;
v___y_1699_ = v___y_1716_;
v___y_1700_ = v___y_1719_;
v___y_1701_ = v___y_1720_;
v___y_1702_ = v___y_1718_;
goto v___jp_1685_;
}
}
v___jp_1723_:
{
lean_object* v_declName_x3f_1733_; lean_object* v_macroStack_1734_; uint8_t v_mayPostpone_1735_; uint8_t v_errToSorry_1736_; lean_object* v_autoBoundImplicitContext_1737_; lean_object* v_autoBoundImplicitForbidden_1738_; lean_object* v_sectionVars_1739_; lean_object* v_sectionFVars_1740_; uint8_t v_implicitLambda_1741_; uint8_t v_heedElabAsElim_1742_; uint8_t v_isNoncomputableSection_1743_; uint8_t v_isMetaSection_1744_; uint8_t v_inPattern_1745_; lean_object* v_tacSnap_x3f_1746_; uint8_t v_saveRecAppSyntax_1747_; uint8_t v_holesAsSyntheticOpaque_1748_; uint8_t v_checkDeprecated_1749_; lean_object* v_fixedTermElabs_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___f_1755_; lean_object* v___f_1756_; lean_object* v___f_1757_; lean_object* v___x_1758_; lean_object* v___f_1759_; lean_object* v___f_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; 
v_declName_x3f_1733_ = lean_ctor_get(v___y_1727_, 0);
v_macroStack_1734_ = lean_ctor_get(v___y_1727_, 1);
v_mayPostpone_1735_ = lean_ctor_get_uint8(v___y_1727_, sizeof(void*)*8);
v_errToSorry_1736_ = lean_ctor_get_uint8(v___y_1727_, sizeof(void*)*8 + 1);
v_autoBoundImplicitContext_1737_ = lean_ctor_get(v___y_1727_, 2);
v_autoBoundImplicitForbidden_1738_ = lean_ctor_get(v___y_1727_, 3);
v_sectionVars_1739_ = lean_ctor_get(v___y_1727_, 4);
v_sectionFVars_1740_ = lean_ctor_get(v___y_1727_, 5);
v_implicitLambda_1741_ = lean_ctor_get_uint8(v___y_1727_, sizeof(void*)*8 + 2);
v_heedElabAsElim_1742_ = lean_ctor_get_uint8(v___y_1727_, sizeof(void*)*8 + 3);
v_isNoncomputableSection_1743_ = lean_ctor_get_uint8(v___y_1727_, sizeof(void*)*8 + 4);
v_isMetaSection_1744_ = lean_ctor_get_uint8(v___y_1727_, sizeof(void*)*8 + 5);
v_inPattern_1745_ = lean_ctor_get_uint8(v___y_1727_, sizeof(void*)*8 + 7);
v_tacSnap_x3f_1746_ = lean_ctor_get(v___y_1727_, 6);
v_saveRecAppSyntax_1747_ = lean_ctor_get_uint8(v___y_1727_, sizeof(void*)*8 + 8);
v_holesAsSyntheticOpaque_1748_ = lean_ctor_get_uint8(v___y_1727_, sizeof(void*)*8 + 9);
v_checkDeprecated_1749_ = lean_ctor_get_uint8(v___y_1727_, sizeof(void*)*8 + 10);
v_fixedTermElabs_1750_ = lean_ctor_get(v___y_1727_, 7);
v___x_1751_ = lean_unsigned_to_nat(2u);
v___x_1752_ = l_Lean_Syntax_getArg(v_stx_1390_, v___x_1751_);
v___x_1753_ = lean_box(0);
v___x_1754_ = lean_box(v___x_1389_);
v___f_1755_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__1___boxed), 11, 2);
lean_closure_set(v___f_1755_, 0, v___x_1753_);
lean_closure_set(v___f_1755_, 1, v___x_1754_);
v___f_1756_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__18));
v___f_1757_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__19));
v___x_1758_ = lean_box(v___x_1389_);
lean_inc(v___x_1752_);
v___f_1759_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__4___boxed), 10, 3);
lean_closure_set(v___f_1759_, 0, v___x_1752_);
lean_closure_set(v___f_1759_, 1, v___x_1753_);
lean_closure_set(v___f_1759_, 2, v___x_1758_);
v___f_1760_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__5___boxed), 9, 2);
lean_closure_set(v___f_1760_, 0, v___x_1752_);
lean_closure_set(v___f_1760_, 1, v___f_1759_);
lean_inc_ref(v_fixedTermElabs_1750_);
lean_inc(v_tacSnap_x3f_1746_);
lean_inc(v_sectionFVars_1740_);
lean_inc(v_sectionVars_1739_);
lean_inc_ref(v_autoBoundImplicitForbidden_1738_);
lean_inc(v_autoBoundImplicitContext_1737_);
lean_inc(v_macroStack_1734_);
lean_inc(v_declName_x3f_1733_);
v___x_1761_ = lean_alloc_ctor(0, 8, 11);
lean_ctor_set(v___x_1761_, 0, v_declName_x3f_1733_);
lean_ctor_set(v___x_1761_, 1, v_macroStack_1734_);
lean_ctor_set(v___x_1761_, 2, v_autoBoundImplicitContext_1737_);
lean_ctor_set(v___x_1761_, 3, v_autoBoundImplicitForbidden_1738_);
lean_ctor_set(v___x_1761_, 4, v_sectionVars_1739_);
lean_ctor_set(v___x_1761_, 5, v_sectionFVars_1740_);
lean_ctor_set(v___x_1761_, 6, v_tacSnap_x3f_1746_);
lean_ctor_set(v___x_1761_, 7, v_fixedTermElabs_1750_);
lean_ctor_set_uint8(v___x_1761_, sizeof(void*)*8, v_mayPostpone_1735_);
lean_ctor_set_uint8(v___x_1761_, sizeof(void*)*8 + 1, v_errToSorry_1736_);
lean_ctor_set_uint8(v___x_1761_, sizeof(void*)*8 + 2, v_implicitLambda_1741_);
lean_ctor_set_uint8(v___x_1761_, sizeof(void*)*8 + 3, v_heedElabAsElim_1742_);
lean_ctor_set_uint8(v___x_1761_, sizeof(void*)*8 + 4, v_isNoncomputableSection_1743_);
lean_ctor_set_uint8(v___x_1761_, sizeof(void*)*8 + 5, v_isMetaSection_1744_);
lean_ctor_set_uint8(v___x_1761_, sizeof(void*)*8 + 6, v___x_1389_);
lean_ctor_set_uint8(v___x_1761_, sizeof(void*)*8 + 7, v_inPattern_1745_);
lean_ctor_set_uint8(v___x_1761_, sizeof(void*)*8 + 8, v_saveRecAppSyntax_1747_);
lean_ctor_set_uint8(v___x_1761_, sizeof(void*)*8 + 9, v_holesAsSyntheticOpaque_1748_);
lean_ctor_set_uint8(v___x_1761_, sizeof(void*)*8 + 10, v_checkDeprecated_1749_);
v___x_1762_ = l_Lean_Elab_Term_withoutModifyingElabMetaStateWithInfo___redArg(v___f_1760_, v___x_1761_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_);
lean_dec_ref_known(v___x_1761_, 8);
if (lean_obj_tag(v___x_1762_) == 0)
{
lean_object* v_a_1763_; lean_object* v___x_1764_; 
v_a_1763_ = lean_ctor_get(v___x_1762_, 0);
lean_inc(v_a_1763_);
lean_dec_ref_known(v___x_1762_, 1);
v___x_1764_ = l_Lean_Elab_Tactic_Conv_getLhs___redArg(v___y_1726_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_);
if (lean_obj_tag(v___x_1764_) == 0)
{
if (lean_obj_tag(v_occs_1724_) == 0)
{
lean_object* v_a_1765_; lean_object* v___x_1766_; 
lean_dec_ref(v___x_1394_);
lean_dec_ref(v___x_1393_);
lean_dec_ref(v___x_1392_);
lean_dec_ref(v___x_1391_);
v_a_1765_ = lean_ctor_get(v___x_1764_, 0);
lean_inc(v_a_1765_);
lean_dec_ref_known(v___x_1764_, 1);
v___x_1766_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__22));
v___y_1622_ = v___f_1755_;
v___y_1623_ = v_a_1765_;
v___y_1624_ = v___f_1756_;
v___y_1625_ = v___f_1757_;
v___y_1626_ = v_a_1763_;
v_occs_1627_ = v___x_1766_;
v___y_1628_ = v___y_1725_;
v___y_1629_ = v___y_1726_;
v___y_1630_ = v___y_1727_;
v___y_1631_ = v___y_1728_;
v___y_1632_ = v___y_1729_;
v___y_1633_ = v___y_1730_;
v___y_1634_ = v___y_1731_;
v___y_1635_ = v___y_1732_;
goto v___jp_1621_;
}
else
{
lean_object* v_a_1767_; lean_object* v_val_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; uint8_t v___x_1771_; 
v_a_1767_ = lean_ctor_get(v___x_1764_, 0);
lean_inc(v_a_1767_);
lean_dec_ref_known(v___x_1764_, 1);
v_val_1768_ = lean_ctor_get(v_occs_1724_, 0);
lean_inc_n(v_val_1768_, 2);
lean_dec_ref_known(v_occs_1724_, 1);
v___x_1769_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__23));
lean_inc_ref(v___x_1394_);
lean_inc_ref(v___x_1393_);
lean_inc_ref(v___x_1392_);
lean_inc_ref(v___x_1391_);
v___x_1770_ = l_Lean_Name_mkStr5(v___x_1391_, v___x_1392_, v___x_1393_, v___x_1394_, v___x_1769_);
v___x_1771_ = l_Lean_Syntax_isOfKind(v_val_1768_, v___x_1770_);
lean_dec(v___x_1770_);
if (v___x_1771_ == 0)
{
lean_object* v___x_1772_; lean_object* v___x_1773_; uint8_t v___x_1774_; 
v___x_1772_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__24));
v___x_1773_ = l_Lean_Name_mkStr5(v___x_1391_, v___x_1392_, v___x_1393_, v___x_1394_, v___x_1772_);
lean_inc(v_val_1768_);
v___x_1774_ = l_Lean_Syntax_isOfKind(v_val_1768_, v___x_1773_);
lean_dec(v___x_1773_);
if (v___x_1774_ == 0)
{
lean_object* v___x_1775_; lean_object* v_a_1776_; lean_object* v___x_1778_; uint8_t v_isShared_1779_; uint8_t v_isSharedCheck_1783_; 
lean_dec(v_val_1768_);
lean_dec(v_a_1767_);
lean_dec(v_a_1763_);
lean_dec_ref(v___f_1755_);
lean_dec_ref(v___f_1388_);
v___x_1775_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1___redArg();
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
v___x_1784_ = l_Lean_Syntax_getArg(v_val_1768_, v___x_1496_);
lean_dec(v_val_1768_);
v___x_1785_ = l_Lean_Syntax_getArgs(v___x_1784_);
lean_dec(v___x_1784_);
v_sz_1786_ = lean_array_size(v___x_1785_);
v___x_1787_ = ((size_t)0ULL);
v___x_1788_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg(v_sz_1786_, v___x_1787_, v___x_1785_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_);
if (lean_obj_tag(v___x_1788_) == 0)
{
lean_object* v_a_1789_; lean_object* v___x_1790_; uint8_t v___x_1791_; 
v_a_1789_ = lean_ctor_get(v___x_1788_, 0);
lean_inc(v_a_1789_);
lean_dec_ref_known(v___x_1788_, 1);
v___x_1790_ = lean_array_get_size(v_a_1789_);
v___x_1791_ = lean_nat_dec_eq(v___x_1790_, v___x_1496_);
if (v___x_1791_ == 0)
{
lean_object* v___x_1792_; uint8_t v___x_1793_; 
v___x_1792_ = lean_nat_sub(v___x_1790_, v___x_1497_);
v___x_1793_ = lean_nat_dec_le(v___x_1496_, v___x_1792_);
if (v___x_1793_ == 0)
{
lean_inc(v___x_1792_);
v___y_1705_ = v___y_1727_;
v___y_1706_ = v___f_1757_;
v___y_1707_ = v___y_1725_;
v___y_1708_ = v_a_1763_;
v___y_1709_ = v___y_1731_;
v___y_1710_ = v_a_1789_;
v___y_1711_ = v___y_1732_;
v___y_1712_ = v___f_1755_;
v___y_1713_ = v___y_1726_;
v___y_1714_ = v_a_1767_;
v___y_1715_ = v___y_1729_;
v___y_1716_ = v___x_1790_;
v___y_1717_ = v___f_1756_;
v___y_1718_ = v___x_1792_;
v___y_1719_ = v___y_1730_;
v___y_1720_ = v___y_1728_;
v___y_1721_ = v___x_1792_;
goto v___jp_1704_;
}
else
{
v___y_1705_ = v___y_1727_;
v___y_1706_ = v___f_1757_;
v___y_1707_ = v___y_1725_;
v___y_1708_ = v_a_1763_;
v___y_1709_ = v___y_1731_;
v___y_1710_ = v_a_1789_;
v___y_1711_ = v___y_1732_;
v___y_1712_ = v___f_1755_;
v___y_1713_ = v___y_1726_;
v___y_1714_ = v_a_1767_;
v___y_1715_ = v___y_1729_;
v___y_1716_ = v___x_1790_;
v___y_1717_ = v___f_1756_;
v___y_1718_ = v___x_1792_;
v___y_1719_ = v___y_1730_;
v___y_1720_ = v___y_1728_;
v___y_1721_ = v___x_1496_;
goto v___jp_1704_;
}
}
else
{
v___y_1668_ = v___y_1727_;
v___y_1669_ = v___f_1757_;
v___y_1670_ = v___y_1725_;
v___y_1671_ = v_a_1763_;
v___y_1672_ = v___y_1731_;
v___y_1673_ = v___y_1732_;
v___y_1674_ = v___f_1755_;
v___y_1675_ = v___y_1726_;
v___y_1676_ = v_a_1767_;
v___y_1677_ = v___y_1729_;
v___y_1678_ = v___f_1756_;
v___y_1679_ = v___y_1730_;
v___y_1680_ = v___y_1728_;
v___y_1681_ = v_a_1789_;
goto v___jp_1667_;
}
}
else
{
lean_object* v_a_1794_; lean_object* v___x_1796_; uint8_t v_isShared_1797_; uint8_t v_isSharedCheck_1801_; 
lean_dec(v_a_1767_);
lean_dec(v_a_1763_);
lean_dec_ref(v___f_1755_);
lean_dec_ref(v___f_1388_);
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
lean_dec_ref(v___x_1394_);
lean_dec_ref(v___x_1393_);
lean_dec_ref(v___x_1392_);
lean_dec_ref(v___x_1391_);
v___x_1802_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__26));
v___y_1622_ = v___f_1755_;
v___y_1623_ = v_a_1767_;
v___y_1624_ = v___f_1756_;
v___y_1625_ = v___f_1757_;
v___y_1626_ = v_a_1763_;
v_occs_1627_ = v___x_1802_;
v___y_1628_ = v___y_1725_;
v___y_1629_ = v___y_1726_;
v___y_1630_ = v___y_1727_;
v___y_1631_ = v___y_1728_;
v___y_1632_ = v___y_1729_;
v___y_1633_ = v___y_1730_;
v___y_1634_ = v___y_1731_;
v___y_1635_ = v___y_1732_;
goto v___jp_1621_;
}
}
}
else
{
lean_object* v_a_1803_; lean_object* v___x_1805_; uint8_t v_isShared_1806_; uint8_t v_isSharedCheck_1810_; 
lean_dec(v_a_1763_);
lean_dec_ref(v___f_1755_);
lean_dec(v_occs_1724_);
lean_dec_ref(v___x_1394_);
lean_dec_ref(v___x_1393_);
lean_dec_ref(v___x_1392_);
lean_dec_ref(v___x_1391_);
lean_dec_ref(v___f_1388_);
v_a_1803_ = lean_ctor_get(v___x_1764_, 0);
v_isSharedCheck_1810_ = !lean_is_exclusive(v___x_1764_);
if (v_isSharedCheck_1810_ == 0)
{
v___x_1805_ = v___x_1764_;
v_isShared_1806_ = v_isSharedCheck_1810_;
goto v_resetjp_1804_;
}
else
{
lean_inc(v_a_1803_);
lean_dec(v___x_1764_);
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
lean_dec_ref(v___f_1755_);
lean_dec(v_occs_1724_);
lean_dec_ref(v___x_1394_);
lean_dec_ref(v___x_1393_);
lean_dec_ref(v___x_1392_);
lean_dec_ref(v___x_1391_);
lean_dec_ref(v___f_1388_);
v_a_1811_ = lean_ctor_get(v___x_1762_, 0);
v_isSharedCheck_1818_ = !lean_is_exclusive(v___x_1762_);
if (v_isSharedCheck_1818_ == 0)
{
v___x_1813_ = v___x_1762_;
v_isShared_1814_ = v_isSharedCheck_1818_;
goto v_resetjp_1812_;
}
else
{
lean_inc(v_a_1811_);
lean_dec(v___x_1762_);
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
v___jp_1404_:
{
lean_object* v___x_1415_; 
v___x_1415_ = l_Lean_Elab_Tactic_Conv_getRhs___redArg(v___y_1408_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_);
if (lean_obj_tag(v___x_1415_) == 0)
{
lean_object* v_a_1416_; lean_object* v_expr_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; 
v_a_1416_ = lean_ctor_get(v___x_1415_, 0);
lean_inc(v_a_1416_);
lean_dec_ref_known(v___x_1415_, 1);
v_expr_1417_ = lean_ctor_get(v___y_1405_, 0);
v___x_1418_ = l_Lean_Expr_mvarId_x21(v_a_1416_);
lean_dec(v_a_1416_);
lean_inc_ref(v_expr_1417_);
v___x_1419_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3___redArg(v___x_1418_, v_expr_1417_, v___y_1412_);
lean_dec_ref(v___x_1419_);
v___x_1420_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_1408_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_);
if (lean_obj_tag(v___x_1420_) == 0)
{
lean_object* v_a_1421_; lean_object* v___x_1422_; 
v_a_1421_ = lean_ctor_get(v___x_1420_, 0);
lean_inc(v_a_1421_);
lean_dec_ref_known(v___x_1420_, 1);
v___x_1422_ = l_Lean_Meta_Simp_Result_getProof(v___y_1405_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_);
if (lean_obj_tag(v___x_1422_) == 0)
{
lean_object* v_a_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; 
v_a_1423_ = lean_ctor_get(v___x_1422_, 0);
lean_inc(v_a_1423_);
lean_dec_ref_known(v___x_1422_, 1);
v___x_1424_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3___redArg(v_a_1421_, v_a_1423_, v___y_1412_);
lean_dec_ref(v___x_1424_);
v___x_1425_ = lean_array_to_list(v_subgoals_1406_);
v___x_1426_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_1425_, v___y_1408_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_);
return v___x_1426_;
}
else
{
lean_object* v_a_1427_; lean_object* v___x_1429_; uint8_t v_isShared_1430_; uint8_t v_isSharedCheck_1434_; 
lean_dec(v_a_1421_);
lean_dec_ref(v_subgoals_1406_);
v_a_1427_ = lean_ctor_get(v___x_1422_, 0);
v_isSharedCheck_1434_ = !lean_is_exclusive(v___x_1422_);
if (v_isSharedCheck_1434_ == 0)
{
v___x_1429_ = v___x_1422_;
v_isShared_1430_ = v_isSharedCheck_1434_;
goto v_resetjp_1428_;
}
else
{
lean_inc(v_a_1427_);
lean_dec(v___x_1422_);
v___x_1429_ = lean_box(0);
v_isShared_1430_ = v_isSharedCheck_1434_;
goto v_resetjp_1428_;
}
v_resetjp_1428_:
{
lean_object* v___x_1432_; 
if (v_isShared_1430_ == 0)
{
v___x_1432_ = v___x_1429_;
goto v_reusejp_1431_;
}
else
{
lean_object* v_reuseFailAlloc_1433_; 
v_reuseFailAlloc_1433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1433_, 0, v_a_1427_);
v___x_1432_ = v_reuseFailAlloc_1433_;
goto v_reusejp_1431_;
}
v_reusejp_1431_:
{
return v___x_1432_;
}
}
}
}
else
{
lean_object* v_a_1435_; lean_object* v___x_1437_; uint8_t v_isShared_1438_; uint8_t v_isSharedCheck_1442_; 
lean_dec_ref(v_subgoals_1406_);
lean_dec_ref(v___y_1405_);
v_a_1435_ = lean_ctor_get(v___x_1420_, 0);
v_isSharedCheck_1442_ = !lean_is_exclusive(v___x_1420_);
if (v_isSharedCheck_1442_ == 0)
{
v___x_1437_ = v___x_1420_;
v_isShared_1438_ = v_isSharedCheck_1442_;
goto v_resetjp_1436_;
}
else
{
lean_inc(v_a_1435_);
lean_dec(v___x_1420_);
v___x_1437_ = lean_box(0);
v_isShared_1438_ = v_isSharedCheck_1442_;
goto v_resetjp_1436_;
}
v_resetjp_1436_:
{
lean_object* v___x_1440_; 
if (v_isShared_1438_ == 0)
{
v___x_1440_ = v___x_1437_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v_a_1435_);
v___x_1440_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
return v___x_1440_;
}
}
}
}
else
{
lean_object* v_a_1443_; lean_object* v___x_1445_; uint8_t v_isShared_1446_; uint8_t v_isSharedCheck_1450_; 
lean_dec_ref(v_subgoals_1406_);
lean_dec_ref(v___y_1405_);
v_a_1443_ = lean_ctor_get(v___x_1415_, 0);
v_isSharedCheck_1450_ = !lean_is_exclusive(v___x_1415_);
if (v_isSharedCheck_1450_ == 0)
{
v___x_1445_ = v___x_1415_;
v_isShared_1446_ = v_isSharedCheck_1450_;
goto v_resetjp_1444_;
}
else
{
lean_inc(v_a_1443_);
lean_dec(v___x_1415_);
v___x_1445_ = lean_box(0);
v_isShared_1446_ = v_isSharedCheck_1450_;
goto v_resetjp_1444_;
}
v_resetjp_1444_:
{
lean_object* v___x_1448_; 
if (v_isShared_1446_ == 0)
{
v___x_1448_ = v___x_1445_;
goto v_reusejp_1447_;
}
else
{
lean_object* v_reuseFailAlloc_1449_; 
v_reuseFailAlloc_1449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1449_, 0, v_a_1443_);
v___x_1448_ = v_reuseFailAlloc_1449_;
goto v_reusejp_1447_;
}
v_reusejp_1447_:
{
return v___x_1448_;
}
}
}
}
v___jp_1451_:
{
size_t v_sz_1462_; size_t v___x_1463_; lean_object* v___x_1464_; 
v_sz_1462_ = lean_array_size(v___y_1461_);
v___x_1463_ = ((size_t)0ULL);
v___x_1464_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__5(v_sz_1462_, v___x_1463_, v___y_1461_);
v___y_1405_ = v___y_1456_;
v_subgoals_1406_ = v___x_1464_;
v___y_1407_ = v___y_1458_;
v___y_1408_ = v___y_1454_;
v___y_1409_ = v___y_1459_;
v___y_1410_ = v___y_1453_;
v___y_1411_ = v___y_1455_;
v___y_1412_ = v___y_1452_;
v___y_1413_ = v___y_1457_;
v___y_1414_ = v___y_1460_;
goto v___jp_1404_;
}
v___jp_1465_:
{
lean_object* v___x_1479_; 
v___x_1479_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg(v___y_1475_, v___y_1467_, v___y_1473_, v___y_1478_);
lean_dec(v___y_1478_);
lean_dec(v___y_1475_);
v___y_1452_ = v___y_1472_;
v___y_1453_ = v___y_1466_;
v___y_1454_ = v___y_1468_;
v___y_1455_ = v___y_1469_;
v___y_1456_ = v___y_1474_;
v___y_1457_ = v___y_1476_;
v___y_1458_ = v___y_1470_;
v___y_1459_ = v___y_1471_;
v___y_1460_ = v___y_1477_;
v___y_1461_ = v___x_1479_;
goto v___jp_1451_;
}
v___jp_1480_:
{
uint8_t v___x_1494_; 
v___x_1494_ = lean_nat_dec_le(v___y_1493_, v___y_1488_);
if (v___x_1494_ == 0)
{
lean_dec(v___y_1488_);
lean_inc(v___y_1493_);
v___y_1466_ = v___y_1481_;
v___y_1467_ = v___y_1482_;
v___y_1468_ = v___y_1483_;
v___y_1469_ = v___y_1484_;
v___y_1470_ = v___y_1485_;
v___y_1471_ = v___y_1486_;
v___y_1472_ = v___y_1487_;
v___y_1473_ = v___y_1493_;
v___y_1474_ = v___y_1489_;
v___y_1475_ = v___y_1490_;
v___y_1476_ = v___y_1491_;
v___y_1477_ = v___y_1492_;
v___y_1478_ = v___y_1493_;
goto v___jp_1465_;
}
else
{
v___y_1466_ = v___y_1481_;
v___y_1467_ = v___y_1482_;
v___y_1468_ = v___y_1483_;
v___y_1469_ = v___y_1484_;
v___y_1470_ = v___y_1485_;
v___y_1471_ = v___y_1486_;
v___y_1472_ = v___y_1487_;
v___y_1473_ = v___y_1493_;
v___y_1474_ = v___y_1489_;
v___y_1475_ = v___y_1490_;
v___y_1476_ = v___y_1491_;
v___y_1477_ = v___y_1492_;
v___y_1478_ = v___y_1488_;
goto v___jp_1465_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Conv_evalPattern___lam__6_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_1387_ = stack[0].m_num;
lean_object* v___f_1388_ = stack[1].m_obj;
uint8_t v___x_1389_ = stack[2].m_num;
lean_object* v_stx_1390_ = stack[3].m_obj;
lean_object* v___x_1391_ = stack[4].m_obj;
lean_object* v___x_1392_ = stack[5].m_obj;
lean_object* v___x_1393_ = stack[6].m_obj;
lean_object* v___x_1394_ = stack[7].m_obj;
lean_object* v___y_1395_ = stack[8].m_obj;
lean_object* v___y_1396_ = stack[9].m_obj;
lean_object* v___y_1397_ = stack[10].m_obj;
lean_object* v___y_1398_ = stack[11].m_obj;
lean_object* v___y_1399_ = stack[12].m_obj;
lean_object* v___y_1400_ = stack[13].m_obj;
lean_object* v___y_1401_ = stack[14].m_obj;
lean_object* v___y_1402_ = stack[15].m_obj;
lean_object* v_res_1832_;
v_res_1832_ = l_Lean_Elab_Tactic_Conv_evalPattern___lam__6(v___x_1387_, v___f_1388_, v___x_1389_, v_stx_1390_, v___x_1391_, v___x_1392_, v___x_1393_, v___x_1394_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_);
stack->m_obj
 = v_res_1832_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___boxed(lean_object** _args){
lean_object* v___x_1833_ = _args[0];
lean_object* v___f_1834_ = _args[1];
lean_object* v___x_1835_ = _args[2];
lean_object* v_stx_1836_ = _args[3];
lean_object* v___x_1837_ = _args[4];
lean_object* v___x_1838_ = _args[5];
lean_object* v___x_1839_ = _args[6];
lean_object* v___x_1840_ = _args[7];
lean_object* v___y_1841_ = _args[8];
lean_object* v___y_1842_ = _args[9];
lean_object* v___y_1843_ = _args[10];
lean_object* v___y_1844_ = _args[11];
lean_object* v___y_1845_ = _args[12];
lean_object* v___y_1846_ = _args[13];
lean_object* v___y_1847_ = _args[14];
lean_object* v___y_1848_ = _args[15];
lean_object* v___y_1849_ = _args[16];
_start:
{
uint8_t v___x_16950__boxed_1850_; uint8_t v___x_16952__boxed_1851_; lean_object* v_res_1852_; 
v___x_16950__boxed_1850_ = lean_unbox(v___x_1833_);
v___x_16952__boxed_1851_ = lean_unbox(v___x_1835_);
v_res_1852_ = l_Lean_Elab_Tactic_Conv_evalPattern___lam__6(v___x_16950__boxed_1850_, v___f_1834_, v___x_16952__boxed_1851_, v_stx_1836_, v___x_1837_, v___x_1838_, v___x_1839_, v___x_1840_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_, v___y_1847_, v___y_1848_);
lean_dec(v___y_1848_);
lean_dec_ref(v___y_1847_);
lean_dec(v___y_1846_);
lean_dec_ref(v___y_1845_);
lean_dec(v___y_1844_);
lean_dec_ref(v___y_1843_);
lean_dec(v___y_1842_);
lean_dec_ref(v___y_1841_);
lean_dec(v_stx_1836_);
return v_res_1852_;
}
}
lean_object* l_Lean_Elab_Tactic_Conv_evalPattern(lean_object* v_stx_1865_, lean_object* v_a_1866_, lean_object* v_a_1867_, lean_object* v_a_1868_, lean_object* v_a_1869_, lean_object* v_a_1870_, lean_object* v_a_1871_, lean_object* v_a_1872_, lean_object* v_a_1873_){
_start:
{
lean_object* v___f_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; uint8_t v___x_1881_; uint8_t v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___y_1885_; lean_object* v___x_1886_; 
v___f_1875_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___closed__0));
v___x_1876_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___closed__1));
v___x_1877_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___closed__2));
v___x_1878_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___closed__3));
v___x_1879_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___closed__4));
v___x_1880_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___closed__6));
lean_inc(v_stx_1865_);
v___x_1881_ = l_Lean_Syntax_isOfKind(v_stx_1865_, v___x_1880_);
v___x_1882_ = 1;
v___x_1883_ = lean_box(v___x_1881_);
v___x_1884_ = lean_box(v___x_1882_);
v___y_1885_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___boxed), 17, 8);
lean_closure_set(v___y_1885_, 0, v___x_1883_);
lean_closure_set(v___y_1885_, 1, v___f_1875_);
lean_closure_set(v___y_1885_, 2, v___x_1884_);
lean_closure_set(v___y_1885_, 3, v_stx_1865_);
lean_closure_set(v___y_1885_, 4, v___x_1876_);
lean_closure_set(v___y_1885_, 5, v___x_1877_);
lean_closure_set(v___y_1885_, 6, v___x_1878_);
lean_closure_set(v___y_1885_, 7, v___x_1879_);
v___x_1886_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___y_1885_, v_a_1866_, v_a_1867_, v_a_1868_, v_a_1869_, v_a_1870_, v_a_1871_, v_a_1872_, v_a_1873_);
return v___x_1886_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Conv_evalPattern_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_1865_ = stack[0].m_obj;
lean_object* v_a_1866_ = stack[1].m_obj;
lean_object* v_a_1867_ = stack[2].m_obj;
lean_object* v_a_1868_ = stack[3].m_obj;
lean_object* v_a_1869_ = stack[4].m_obj;
lean_object* v_a_1870_ = stack[5].m_obj;
lean_object* v_a_1871_ = stack[6].m_obj;
lean_object* v_a_1872_ = stack[7].m_obj;
lean_object* v_a_1873_ = stack[8].m_obj;
lean_object* v_res_1887_;
v_res_1887_ = l_Lean_Elab_Tactic_Conv_evalPattern(v_stx_1865_, v_a_1866_, v_a_1867_, v_a_1868_, v_a_1869_, v_a_1870_, v_a_1871_, v_a_1872_, v_a_1873_);
stack->m_obj
 = v_res_1887_;
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
lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0(lean_object* v_00_u03b1_1899_, lean_object* v_ref_1900_, lean_object* v_msg_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_){
_start:
{
lean_object* v___x_1911_; 
v___x_1911_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg(v_ref_1900_, v_msg_1901_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_);
return v___x_1911_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1900_ = stack[1].m_obj;
lean_object* v_msg_1901_ = stack[2].m_obj;
lean_object* v___y_1902_ = stack[3].m_obj;
lean_object* v___y_1903_ = stack[4].m_obj;
lean_object* v___y_1904_ = stack[5].m_obj;
lean_object* v___y_1905_ = stack[6].m_obj;
lean_object* v___y_1906_ = stack[7].m_obj;
lean_object* v___y_1907_ = stack[8].m_obj;
lean_object* v___y_1908_ = stack[9].m_obj;
lean_object* v___y_1909_ = stack[10].m_obj;
lean_object* v_res_1912_;
v_res_1912_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0(lean_box(0), v_ref_1900_, v_msg_1901_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_);
stack->m_obj
 = v_res_1912_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___boxed(lean_object* v_00_u03b1_1913_, lean_object* v_ref_1914_, lean_object* v_msg_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_){
_start:
{
lean_object* v_res_1925_; 
v_res_1925_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0(v_00_u03b1_1913_, v_ref_1914_, v_msg_1915_, v___y_1916_, v___y_1917_, v___y_1918_, v___y_1919_, v___y_1920_, v___y_1921_, v___y_1922_, v___y_1923_);
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
lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3(lean_object* v_mvarId_1926_, lean_object* v_val_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_){
_start:
{
lean_object* v___x_1937_; 
v___x_1937_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3___redArg(v_mvarId_1926_, v_val_1927_, v___y_1933_);
return v___x_1937_;
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1926_ = stack[0].m_obj;
lean_object* v_val_1927_ = stack[1].m_obj;
lean_object* v___y_1928_ = stack[2].m_obj;
lean_object* v___y_1929_ = stack[3].m_obj;
lean_object* v___y_1930_ = stack[4].m_obj;
lean_object* v___y_1931_ = stack[5].m_obj;
lean_object* v___y_1932_ = stack[6].m_obj;
lean_object* v___y_1933_ = stack[7].m_obj;
lean_object* v___y_1934_ = stack[8].m_obj;
lean_object* v___y_1935_ = stack[9].m_obj;
lean_object* v_res_1938_;
v_res_1938_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3(v_mvarId_1926_, v_val_1927_, v___y_1928_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_);
stack->m_obj
 = v_res_1938_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3___boxed(lean_object* v_mvarId_1939_, lean_object* v_val_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_){
_start:
{
lean_object* v_res_1950_; 
v_res_1950_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3(v_mvarId_1939_, v_val_1940_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_);
lean_dec(v___y_1948_);
lean_dec_ref(v___y_1947_);
lean_dec(v___y_1946_);
lean_dec_ref(v___y_1945_);
lean_dec(v___y_1944_);
lean_dec_ref(v___y_1943_);
lean_dec(v___y_1942_);
lean_dec_ref(v___y_1941_);
return v_res_1950_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4(lean_object* v_00_u03b1_1951_, lean_object* v_msg_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_){
_start:
{
lean_object* v___x_1962_; 
v___x_1962_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg(v_msg_1952_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_);
return v___x_1962_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1952_ = stack[1].m_obj;
lean_object* v___y_1953_ = stack[2].m_obj;
lean_object* v___y_1954_ = stack[3].m_obj;
lean_object* v___y_1955_ = stack[4].m_obj;
lean_object* v___y_1956_ = stack[5].m_obj;
lean_object* v___y_1957_ = stack[6].m_obj;
lean_object* v___y_1958_ = stack[7].m_obj;
lean_object* v___y_1959_ = stack[8].m_obj;
lean_object* v___y_1960_ = stack[9].m_obj;
lean_object* v_res_1963_;
v_res_1963_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4(lean_box(0), v_msg_1952_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_);
stack->m_obj
 = v_res_1963_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___boxed(lean_object* v_00_u03b1_1964_, lean_object* v_msg_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_){
_start:
{
lean_object* v_res_1975_; 
v_res_1975_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4(v_00_u03b1_1964_, v_msg_1965_, v___y_1966_, v___y_1967_, v___y_1968_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_);
lean_dec(v___y_1973_);
lean_dec_ref(v___y_1972_);
lean_dec(v___y_1971_);
lean_dec_ref(v___y_1970_);
lean_dec(v___y_1969_);
lean_dec_ref(v___y_1968_);
lean_dec(v___y_1967_);
lean_dec_ref(v___y_1966_);
return v_res_1975_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6(lean_object* v_n_1976_, lean_object* v_as_1977_, lean_object* v_lo_1978_, lean_object* v_hi_1979_, lean_object* v_w_1980_, lean_object* v_hlo_1981_, lean_object* v_hhi_1982_){
_start:
{
lean_object* v___x_1983_; 
v___x_1983_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg(v_n_1976_, v_as_1977_, v_lo_1978_, v_hi_1979_);
return v___x_1983_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___boxed(lean_object* v_n_1984_, lean_object* v_as_1985_, lean_object* v_lo_1986_, lean_object* v_hi_1987_, lean_object* v_w_1988_, lean_object* v_hlo_1989_, lean_object* v_hhi_1990_){
_start:
{
lean_object* v_res_1991_; 
v_res_1991_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6(v_n_1984_, v_as_1985_, v_lo_1986_, v_hi_1987_, v_w_1988_, v_hlo_1989_, v_hhi_1990_);
lean_dec(v_hi_1987_);
lean_dec(v_n_1984_);
return v_res_1991_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7(lean_object* v_as_1992_, size_t v_sz_1993_, size_t v_i_1994_, lean_object* v_bs_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_){
_start:
{
lean_object* v___x_2005_; 
v___x_2005_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg(v_sz_1993_, v_i_1994_, v_bs_1995_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_, v___y_2003_);
return v___x_2005_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1992_ = stack[0].m_obj;
size_t v_sz_1993_ = stack[1].m_num;
size_t v_i_1994_ = stack[2].m_num;
lean_object* v_bs_1995_ = stack[3].m_obj;
lean_object* v___y_1996_ = stack[4].m_obj;
lean_object* v___y_1997_ = stack[5].m_obj;
lean_object* v___y_1998_ = stack[6].m_obj;
lean_object* v___y_1999_ = stack[7].m_obj;
lean_object* v___y_2000_ = stack[8].m_obj;
lean_object* v___y_2001_ = stack[9].m_obj;
lean_object* v___y_2002_ = stack[10].m_obj;
lean_object* v___y_2003_ = stack[11].m_obj;
lean_object* v_res_2006_;
v_res_2006_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7(v_as_1992_, v_sz_1993_, v_i_1994_, v_bs_1995_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_, v___y_2003_);
stack->m_obj
 = v_res_2006_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___boxed(lean_object* v_as_2007_, lean_object* v_sz_2008_, lean_object* v_i_2009_, lean_object* v_bs_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_){
_start:
{
size_t v_sz_boxed_2020_; size_t v_i_boxed_2021_; lean_object* v_res_2022_; 
v_sz_boxed_2020_ = lean_unbox_usize(v_sz_2008_);
lean_dec(v_sz_2008_);
v_i_boxed_2021_ = lean_unbox_usize(v_i_2009_);
lean_dec(v_i_2009_);
v_res_2022_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7(v_as_2007_, v_sz_boxed_2020_, v_i_boxed_2021_, v_bs_2010_, v___y_2011_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_);
lean_dec(v___y_2018_);
lean_dec_ref(v___y_2017_);
lean_dec(v___y_2016_);
lean_dec_ref(v___y_2015_);
lean_dec(v___y_2014_);
lean_dec_ref(v___y_2013_);
lean_dec(v___y_2012_);
lean_dec_ref(v___y_2011_);
lean_dec_ref(v_as_2007_);
return v_res_2022_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9(lean_object* v_n_2023_, lean_object* v_as_2024_, lean_object* v_lo_2025_, lean_object* v_hi_2026_, lean_object* v_w_2027_, lean_object* v_hlo_2028_, lean_object* v_hhi_2029_){
_start:
{
lean_object* v___x_2030_; 
v___x_2030_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg(v_n_2023_, v_as_2024_, v_lo_2025_, v_hi_2026_);
return v___x_2030_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___boxed(lean_object* v_n_2031_, lean_object* v_as_2032_, lean_object* v_lo_2033_, lean_object* v_hi_2034_, lean_object* v_w_2035_, lean_object* v_hlo_2036_, lean_object* v_hhi_2037_){
_start:
{
lean_object* v_res_2038_; 
v_res_2038_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9(v_n_2031_, v_as_2032_, v_lo_2033_, v_hi_2034_, v_w_2035_, v_hlo_2036_, v_hhi_2037_);
lean_dec(v_hi_2034_);
lean_dec(v_n_2031_);
return v_res_2038_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3(lean_object* v_00_u03b2_2039_, lean_object* v_x_2040_, lean_object* v_x_2041_, lean_object* v_x_2042_){
_start:
{
lean_object* v___x_2043_; 
v___x_2043_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3___redArg(v_x_2040_, v_x_2041_, v_x_2042_);
return v___x_2043_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6_spec__8(lean_object* v_n_2044_, lean_object* v_lo_2045_, lean_object* v_hi_2046_, lean_object* v_hhi_2047_, lean_object* v_pivot_2048_, lean_object* v_as_2049_, lean_object* v_i_2050_, lean_object* v_k_2051_, lean_object* v_ilo_2052_, lean_object* v_ik_2053_, lean_object* v_w_2054_){
_start:
{
lean_object* v___x_2055_; 
v___x_2055_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6_spec__8___redArg(v_hi_2046_, v_pivot_2048_, v_as_2049_, v_i_2050_, v_k_2051_);
return v___x_2055_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6_spec__8___boxed(lean_object* v_n_2056_, lean_object* v_lo_2057_, lean_object* v_hi_2058_, lean_object* v_hhi_2059_, lean_object* v_pivot_2060_, lean_object* v_as_2061_, lean_object* v_i_2062_, lean_object* v_k_2063_, lean_object* v_ilo_2064_, lean_object* v_ik_2065_, lean_object* v_w_2066_){
_start:
{
lean_object* v_res_2067_; 
v_res_2067_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6_spec__8(v_n_2056_, v_lo_2057_, v_hi_2058_, v_hhi_2059_, v_pivot_2060_, v_as_2061_, v_i_2062_, v_k_2063_, v_ilo_2064_, v_ik_2065_, v_w_2066_);
lean_dec_ref(v_pivot_2060_);
lean_dec(v_hi_2058_);
lean_dec(v_lo_2057_);
lean_dec(v_n_2056_);
return v_res_2067_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9_spec__13(lean_object* v_n_2068_, lean_object* v_lo_2069_, lean_object* v_hi_2070_, lean_object* v_hhi_2071_, lean_object* v_pivot_2072_, lean_object* v_as_2073_, lean_object* v_i_2074_, lean_object* v_k_2075_, lean_object* v_ilo_2076_, lean_object* v_ik_2077_, lean_object* v_w_2078_){
_start:
{
lean_object* v___x_2079_; 
v___x_2079_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9_spec__13___redArg(v_hi_2070_, v_pivot_2072_, v_as_2073_, v_i_2074_, v_k_2075_);
return v___x_2079_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9_spec__13___boxed(lean_object* v_n_2080_, lean_object* v_lo_2081_, lean_object* v_hi_2082_, lean_object* v_hhi_2083_, lean_object* v_pivot_2084_, lean_object* v_as_2085_, lean_object* v_i_2086_, lean_object* v_k_2087_, lean_object* v_ilo_2088_, lean_object* v_ik_2089_, lean_object* v_w_2090_){
_start:
{
lean_object* v_res_2091_; 
v_res_2091_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9_spec__13(v_n_2080_, v_lo_2081_, v_hi_2082_, v_hhi_2083_, v_pivot_2084_, v_as_2085_, v_i_2086_, v_k_2087_, v_ilo_2088_, v_ik_2089_, v_w_2090_);
lean_dec_ref(v_pivot_2084_);
lean_dec(v_hi_2082_);
lean_dec(v_lo_2081_);
lean_dec(v_n_2080_);
return v_res_2091_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4(lean_object* v_00_u03b2_2092_, lean_object* v_x_2093_, size_t v_x_2094_, size_t v_x_2095_, lean_object* v_x_2096_, lean_object* v_x_2097_){
_start:
{
lean_object* v___x_2098_; 
v___x_2098_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg(v_x_2093_, v_x_2094_, v_x_2095_, v_x_2096_, v_x_2097_);
return v___x_2098_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2093_ = stack[1].m_obj;
size_t v_x_2094_ = stack[2].m_num;
size_t v_x_2095_ = stack[3].m_num;
lean_object* v_x_2096_ = stack[4].m_obj;
lean_object* v_x_2097_ = stack[5].m_obj;
lean_object* v_res_2099_;
v_res_2099_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4(lean_box(0), v_x_2093_, v_x_2094_, v_x_2095_, v_x_2096_, v_x_2097_);
stack->m_obj
 = v_res_2099_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___boxed(lean_object* v_00_u03b2_2100_, lean_object* v_x_2101_, lean_object* v_x_2102_, lean_object* v_x_2103_, lean_object* v_x_2104_, lean_object* v_x_2105_){
_start:
{
size_t v_x_18669__boxed_2106_; size_t v_x_18670__boxed_2107_; lean_object* v_res_2108_; 
v_x_18669__boxed_2106_ = lean_unbox_usize(v_x_2102_);
lean_dec(v_x_2102_);
v_x_18670__boxed_2107_ = lean_unbox_usize(v_x_2103_);
lean_dec(v_x_2103_);
v_res_2108_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4(v_00_u03b2_2100_, v_x_2101_, v_x_18669__boxed_2106_, v_x_18670__boxed_2107_, v_x_2104_, v_x_2105_);
return v_res_2108_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11_spec__13(lean_object* v_as_2109_, lean_object* v_a_2110_, lean_object* v_x_2111_, lean_object* v_x_2112_){
_start:
{
uint8_t v___x_2113_; 
v___x_2113_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11_spec__13___redArg(v_as_2109_, v_a_2110_, v_x_2111_);
return v___x_2113_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11_spec__13_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2109_ = stack[0].m_obj;
lean_object* v_a_2110_ = stack[1].m_obj;
lean_object* v_x_2111_ = stack[2].m_obj;
uint8_t v_res_2114_;
v_res_2114_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11_spec__13(v_as_2109_, v_a_2110_, v_x_2111_, lean_box(0));
stack->m_num = v_res_2114_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11_spec__13___boxed(lean_object* v_as_2115_, lean_object* v_a_2116_, lean_object* v_x_2117_, lean_object* v_x_2118_){
_start:
{
uint8_t v_res_2119_; lean_object* v_r_2120_; 
v_res_2119_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11_spec__13(v_as_2115_, v_a_2116_, v_x_2117_, v_x_2118_);
lean_dec_ref(v_a_2116_);
lean_dec_ref(v_as_2115_);
v_r_2120_ = lean_box(v_res_2119_);
return v_r_2120_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__12(lean_object* v_00_u03b2_2121_, lean_object* v_n_2122_, lean_object* v_k_2123_, lean_object* v_v_2124_){
_start:
{
lean_object* v___x_2125_; 
v___x_2125_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__12___redArg(v_n_2122_, v_k_2123_, v_v_2124_);
return v___x_2125_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__13(lean_object* v_00_u03b2_2126_, size_t v_depth_2127_, lean_object* v_keys_2128_, lean_object* v_vals_2129_, lean_object* v_heq_2130_, lean_object* v_i_2131_, lean_object* v_entries_2132_){
_start:
{
lean_object* v___x_2133_; 
v___x_2133_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__13___redArg(v_depth_2127_, v_keys_2128_, v_vals_2129_, v_i_2131_, v_entries_2132_);
return v___x_2133_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__13_0interp(lean_interpreter_value* stack)
{
size_t v_depth_2127_ = stack[1].m_num;
lean_object* v_keys_2128_ = stack[2].m_obj;
lean_object* v_vals_2129_ = stack[3].m_obj;
lean_object* v_i_2131_ = stack[5].m_obj;
lean_object* v_entries_2132_ = stack[6].m_obj;
lean_object* v_res_2134_;
v_res_2134_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__13(lean_box(0), v_depth_2127_, v_keys_2128_, v_vals_2129_, lean_box(0), v_i_2131_, v_entries_2132_);
stack->m_obj
 = v_res_2134_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__13___boxed(lean_object* v_00_u03b2_2135_, lean_object* v_depth_2136_, lean_object* v_keys_2137_, lean_object* v_vals_2138_, lean_object* v_heq_2139_, lean_object* v_i_2140_, lean_object* v_entries_2141_){
_start:
{
size_t v_depth_boxed_2142_; lean_object* v_res_2143_; 
v_depth_boxed_2142_ = lean_unbox_usize(v_depth_2136_);
lean_dec(v_depth_2136_);
v_res_2143_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__13(v_00_u03b2_2135_, v_depth_boxed_2142_, v_keys_2137_, v_vals_2138_, v_heq_2139_, v_i_2140_, v_entries_2141_);
lean_dec_ref(v_vals_2138_);
lean_dec_ref(v_keys_2137_);
return v_res_2143_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__12_spec__16(lean_object* v_00_u03b2_2144_, lean_object* v_x_2145_, lean_object* v_x_2146_, lean_object* v_x_2147_, lean_object* v_x_2148_){
_start:
{
lean_object* v___x_2149_; 
v___x_2149_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__12_spec__16___redArg(v_x_2145_, v_x_2146_, v_x_2147_, v_x_2148_);
return v___x_2149_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1(){
_start:
{
lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; 
v___x_2159_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2160_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___closed__6));
v___x_2161_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___closed__2));
v___x_2162_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalPattern___boxed), 10, 0);
v___x_2163_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2159_, v___x_2160_, v___x_2161_, v___x_2162_);
return v___x_2163_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2164_;
v_res_2164_ = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1();
stack->m_obj
 = v_res_2164_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___boxed(lean_object* v_a_2165_){
_start:
{
lean_object* v_res_2166_; 
v_res_2166_ = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1();
return v_res_2166_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3(){
_start:
{
lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; 
v___x_2193_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___closed__2));
v___x_2194_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__6));
v___x_2195_ = l_Lean_addBuiltinDeclarationRanges(v___x_2193_, v___x_2194_);
return v___x_2195_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2196_;
v_res_2196_ = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3();
stack->m_obj
 = v_res_2196_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___boxed(lean_object* v_a_2197_){
_start:
{
lean_object* v_res_2198_; 
v_res_2198_ = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3();
return v_res_2198_;
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
