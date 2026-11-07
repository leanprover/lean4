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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorIdx___impl(lean_object* v_x_256_){
_start:
{
lean_object* v___x_257_; 
v___x_257_ = lean_obj_tag_nat(v_x_256_);
return v___x_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorIdx___impl___boxed(lean_object* v_x_258_){
_start:
{
lean_object* v_res_259_; 
v_res_259_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorIdx___impl(v_x_258_);
lean_dec_ref(v_x_258_);
return v_res_259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorElim___redArg(lean_object* v_t_260_, lean_object* v_k_261_){
_start:
{
if (lean_obj_tag(v_t_260_) == 0)
{
lean_object* v_subgoals_262_; lean_object* v___x_263_; 
v_subgoals_262_ = lean_ctor_get(v_t_260_, 0);
lean_inc_ref(v_subgoals_262_);
lean_dec_ref_known(v_t_260_, 1);
v___x_263_ = lean_apply_1(v_k_261_, v_subgoals_262_);
return v___x_263_;
}
else
{
lean_object* v_subgoals_264_; lean_object* v_idx_265_; lean_object* v_remaining_266_; lean_object* v___x_267_; 
v_subgoals_264_ = lean_ctor_get(v_t_260_, 0);
lean_inc_ref(v_subgoals_264_);
v_idx_265_ = lean_ctor_get(v_t_260_, 1);
lean_inc(v_idx_265_);
v_remaining_266_ = lean_ctor_get(v_t_260_, 2);
lean_inc(v_remaining_266_);
lean_dec_ref_known(v_t_260_, 3);
v___x_267_ = lean_apply_3(v_k_261_, v_subgoals_264_, v_idx_265_, v_remaining_266_);
return v___x_267_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorElim(lean_object* v_motive_268_, lean_object* v_ctorIdx_269_, lean_object* v_t_270_, lean_object* v_h_271_, lean_object* v_k_272_){
_start:
{
lean_object* v___x_273_; 
v___x_273_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorElim___redArg(v_t_270_, v_k_272_);
return v___x_273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorElim___boxed(lean_object* v_motive_274_, lean_object* v_ctorIdx_275_, lean_object* v_t_276_, lean_object* v_h_277_, lean_object* v_k_278_){
_start:
{
lean_object* v_res_279_; 
v_res_279_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorElim(v_motive_274_, v_ctorIdx_275_, v_t_276_, v_h_277_, v_k_278_);
lean_dec(v_ctorIdx_275_);
return v_res_279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_all_elim___redArg(lean_object* v_t_280_, lean_object* v_all_281_){
_start:
{
lean_object* v___x_282_; 
v___x_282_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorElim___redArg(v_t_280_, v_all_281_);
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_all_elim(lean_object* v_motive_283_, lean_object* v_t_284_, lean_object* v_h_285_, lean_object* v_all_286_){
_start:
{
lean_object* v___x_287_; 
v___x_287_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorElim___redArg(v_t_284_, v_all_286_);
return v___x_287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_occs_elim___redArg(lean_object* v_t_288_, lean_object* v_occs_289_){
_start:
{
lean_object* v___x_290_; 
v___x_290_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorElim___redArg(v_t_288_, v_occs_289_);
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_occs_elim(lean_object* v_motive_291_, lean_object* v_t_292_, lean_object* v_h_293_, lean_object* v_occs_294_){
_start:
{
lean_object* v___x_295_; 
v___x_295_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorElim___redArg(v_t_292_, v_occs_294_);
return v___x_295_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Conv_PatternMatchState_isDone(lean_object* v_x_296_){
_start:
{
if (lean_obj_tag(v_x_296_) == 0)
{
uint8_t v___x_297_; 
v___x_297_ = 0;
return v___x_297_;
}
else
{
lean_object* v_remaining_298_; uint8_t v___x_299_; 
v_remaining_298_ = lean_ctor_get(v_x_296_, 2);
v___x_299_ = l_List_isEmpty___redArg(v_remaining_298_);
return v___x_299_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_isDone___boxed(lean_object* v_x_300_){
_start:
{
uint8_t v_res_301_; lean_object* v_r_302_; 
v_res_301_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_isDone(v_x_300_);
lean_dec_ref(v_x_300_);
v_r_302_ = lean_box(v_res_301_);
return v_r_302_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Conv_PatternMatchState_isReady(lean_object* v_x_303_){
_start:
{
if (lean_obj_tag(v_x_303_) == 0)
{
uint8_t v___x_304_; 
v___x_304_ = 1;
return v___x_304_;
}
else
{
lean_object* v_remaining_305_; 
v_remaining_305_ = lean_ctor_get(v_x_303_, 2);
if (lean_obj_tag(v_remaining_305_) == 1)
{
lean_object* v_head_306_; lean_object* v_idx_307_; lean_object* v_fst_308_; uint8_t v___x_309_; 
v_head_306_ = lean_ctor_get(v_remaining_305_, 0);
v_idx_307_ = lean_ctor_get(v_x_303_, 1);
v_fst_308_ = lean_ctor_get(v_head_306_, 0);
v___x_309_ = lean_nat_dec_eq(v_idx_307_, v_fst_308_);
return v___x_309_;
}
else
{
uint8_t v___x_310_; 
v___x_310_ = 0;
return v___x_310_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_isReady___boxed(lean_object* v_x_311_){
_start:
{
uint8_t v_res_312_; lean_object* v_r_313_; 
v_res_312_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_isReady(v_x_311_);
lean_dec_ref(v_x_311_);
v_r_313_ = lean_box(v_res_312_);
return v_r_313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_skip(lean_object* v_x_314_){
_start:
{
if (lean_obj_tag(v_x_314_) == 1)
{
lean_object* v_subgoals_315_; lean_object* v_idx_316_; lean_object* v_remaining_317_; lean_object* v___x_319_; uint8_t v_isShared_320_; uint8_t v_isSharedCheck_326_; 
v_subgoals_315_ = lean_ctor_get(v_x_314_, 0);
v_idx_316_ = lean_ctor_get(v_x_314_, 1);
v_remaining_317_ = lean_ctor_get(v_x_314_, 2);
v_isSharedCheck_326_ = !lean_is_exclusive(v_x_314_);
if (v_isSharedCheck_326_ == 0)
{
v___x_319_ = v_x_314_;
v_isShared_320_ = v_isSharedCheck_326_;
goto v_resetjp_318_;
}
else
{
lean_inc(v_remaining_317_);
lean_inc(v_idx_316_);
lean_inc(v_subgoals_315_);
lean_dec(v_x_314_);
v___x_319_ = lean_box(0);
v_isShared_320_ = v_isSharedCheck_326_;
goto v_resetjp_318_;
}
v_resetjp_318_:
{
lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_324_; 
v___x_321_ = lean_unsigned_to_nat(1u);
v___x_322_ = lean_nat_add(v_idx_316_, v___x_321_);
lean_dec(v_idx_316_);
if (v_isShared_320_ == 0)
{
lean_ctor_set(v___x_319_, 1, v___x_322_);
v___x_324_ = v___x_319_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_325_; 
v_reuseFailAlloc_325_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_325_, 0, v_subgoals_315_);
lean_ctor_set(v_reuseFailAlloc_325_, 1, v___x_322_);
lean_ctor_set(v_reuseFailAlloc_325_, 2, v_remaining_317_);
v___x_324_ = v_reuseFailAlloc_325_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
return v___x_324_;
}
}
}
else
{
return v_x_314_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_PatternMatchState_accept(lean_object* v_mvarId_327_, lean_object* v_x_328_){
_start:
{
if (lean_obj_tag(v_x_328_) == 0)
{
lean_object* v_subgoals_329_; lean_object* v___x_331_; uint8_t v_isShared_332_; uint8_t v_isSharedCheck_337_; 
v_subgoals_329_ = lean_ctor_get(v_x_328_, 0);
v_isSharedCheck_337_ = !lean_is_exclusive(v_x_328_);
if (v_isSharedCheck_337_ == 0)
{
v___x_331_ = v_x_328_;
v_isShared_332_ = v_isSharedCheck_337_;
goto v_resetjp_330_;
}
else
{
lean_inc(v_subgoals_329_);
lean_dec(v_x_328_);
v___x_331_ = lean_box(0);
v_isShared_332_ = v_isSharedCheck_337_;
goto v_resetjp_330_;
}
v_resetjp_330_:
{
lean_object* v___x_333_; lean_object* v___x_335_; 
v___x_333_ = lean_array_push(v_subgoals_329_, v_mvarId_327_);
if (v_isShared_332_ == 0)
{
lean_ctor_set(v___x_331_, 0, v___x_333_);
v___x_335_ = v___x_331_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v___x_333_);
v___x_335_ = v_reuseFailAlloc_336_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
return v___x_335_;
}
}
}
else
{
lean_object* v_remaining_338_; 
v_remaining_338_ = lean_ctor_get(v_x_328_, 2);
if (lean_obj_tag(v_remaining_338_) == 1)
{
lean_object* v_head_339_; lean_object* v_subgoals_340_; lean_object* v_idx_341_; lean_object* v___x_343_; uint8_t v_isShared_344_; uint8_t v_isSharedCheck_361_; 
lean_inc_ref(v_remaining_338_);
v_head_339_ = lean_ctor_get(v_remaining_338_, 0);
lean_inc(v_head_339_);
v_subgoals_340_ = lean_ctor_get(v_x_328_, 0);
v_idx_341_ = lean_ctor_get(v_x_328_, 1);
v_isSharedCheck_361_ = !lean_is_exclusive(v_x_328_);
if (v_isSharedCheck_361_ == 0)
{
lean_object* v_unused_362_; 
v_unused_362_ = lean_ctor_get(v_x_328_, 2);
lean_dec(v_unused_362_);
v___x_343_ = v_x_328_;
v_isShared_344_ = v_isSharedCheck_361_;
goto v_resetjp_342_;
}
else
{
lean_inc(v_idx_341_);
lean_inc(v_subgoals_340_);
lean_dec(v_x_328_);
v___x_343_ = lean_box(0);
v_isShared_344_ = v_isSharedCheck_361_;
goto v_resetjp_342_;
}
v_resetjp_342_:
{
lean_object* v_tail_345_; lean_object* v_snd_346_; lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_359_; 
v_tail_345_ = lean_ctor_get(v_remaining_338_, 1);
lean_inc(v_tail_345_);
lean_dec_ref_known(v_remaining_338_, 2);
v_snd_346_ = lean_ctor_get(v_head_339_, 1);
v_isSharedCheck_359_ = !lean_is_exclusive(v_head_339_);
if (v_isSharedCheck_359_ == 0)
{
lean_object* v_unused_360_; 
v_unused_360_ = lean_ctor_get(v_head_339_, 0);
lean_dec(v_unused_360_);
v___x_348_ = v_head_339_;
v_isShared_349_ = v_isSharedCheck_359_;
goto v_resetjp_347_;
}
else
{
lean_inc(v_snd_346_);
lean_dec(v_head_339_);
v___x_348_ = lean_box(0);
v_isShared_349_ = v_isSharedCheck_359_;
goto v_resetjp_347_;
}
v_resetjp_347_:
{
lean_object* v___x_351_; 
if (v_isShared_349_ == 0)
{
lean_ctor_set(v___x_348_, 1, v_mvarId_327_);
lean_ctor_set(v___x_348_, 0, v_snd_346_);
v___x_351_ = v___x_348_;
goto v_reusejp_350_;
}
else
{
lean_object* v_reuseFailAlloc_358_; 
v_reuseFailAlloc_358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_358_, 0, v_snd_346_);
lean_ctor_set(v_reuseFailAlloc_358_, 1, v_mvarId_327_);
v___x_351_ = v_reuseFailAlloc_358_;
goto v_reusejp_350_;
}
v_reusejp_350_:
{
lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_356_; 
v___x_352_ = lean_array_push(v_subgoals_340_, v___x_351_);
v___x_353_ = lean_unsigned_to_nat(1u);
v___x_354_ = lean_nat_add(v_idx_341_, v___x_353_);
lean_dec(v_idx_341_);
if (v_isShared_344_ == 0)
{
lean_ctor_set(v___x_343_, 2, v_tail_345_);
lean_ctor_set(v___x_343_, 1, v___x_354_);
lean_ctor_set(v___x_343_, 0, v___x_352_);
v___x_356_ = v___x_343_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v___x_352_);
lean_ctor_set(v_reuseFailAlloc_357_, 1, v___x_354_);
lean_ctor_set(v_reuseFailAlloc_357_, 2, v_tail_345_);
v___x_356_ = v_reuseFailAlloc_357_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
return v___x_356_;
}
}
}
}
}
else
{
lean_dec(v_mvarId_327_);
return v_x_328_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre_spec__0___redArg(lean_object* v_as_363_, size_t v_sz_364_, size_t v_i_365_, lean_object* v_b_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_){
_start:
{
uint8_t v___x_372_; 
v___x_372_ = lean_usize_dec_lt(v_i_365_, v_sz_364_);
if (v___x_372_ == 0)
{
lean_object* v___x_373_; 
v___x_373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_373_, 0, v_b_366_);
return v___x_373_;
}
else
{
lean_object* v_a_374_; lean_object* v___x_375_; 
v_a_374_ = lean_array_uget_borrowed(v_as_363_, v_i_365_);
lean_inc(v_a_374_);
v___x_375_ = l_Lean_Meta_mkCongrFun(v_b_366_, v_a_374_, v___y_367_, v___y_368_, v___y_369_, v___y_370_);
if (lean_obj_tag(v___x_375_) == 0)
{
lean_object* v_a_376_; size_t v___x_377_; size_t v___x_378_; 
v_a_376_ = lean_ctor_get(v___x_375_, 0);
lean_inc(v_a_376_);
lean_dec_ref_known(v___x_375_, 1);
v___x_377_ = ((size_t)1ULL);
v___x_378_ = lean_usize_add(v_i_365_, v___x_377_);
v_i_365_ = v___x_378_;
v_b_366_ = v_a_376_;
goto _start;
}
else
{
return v___x_375_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre_spec__0___redArg___boxed(lean_object* v_as_380_, lean_object* v_sz_381_, lean_object* v_i_382_, lean_object* v_b_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_){
_start:
{
size_t v_sz_boxed_389_; size_t v_i_boxed_390_; lean_object* v_res_391_; 
v_sz_boxed_389_ = lean_unbox_usize(v_sz_381_);
lean_dec(v_sz_381_);
v_i_boxed_390_ = lean_unbox_usize(v_i_382_);
lean_dec(v_i_382_);
v_res_391_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre_spec__0___redArg(v_as_380_, v_sz_boxed_389_, v_i_boxed_390_, v_b_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_);
lean_dec(v___y_387_);
lean_dec_ref(v___y_386_);
lean_dec(v___y_385_);
lean_dec_ref(v___y_384_);
lean_dec_ref(v_as_380_);
return v_res_391_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre(lean_object* v_pattern_394_, lean_object* v_state_395_, lean_object* v_e_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_){
_start:
{
lean_object* v___x_405_; uint8_t v___x_406_; uint8_t v___x_407_; 
v___x_405_ = lean_st_ref_get(v_state_395_);
v___x_406_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_isDone(v___x_405_);
lean_dec(v___x_405_);
v___x_407_ = 1;
if (v___x_406_ == 0)
{
lean_object* v___x_408_; 
v___x_408_ = l_Lean_Elab_Tactic_Conv_matchPattern_x3f(v_pattern_394_, v_e_396_, v_a_400_, v_a_401_, v_a_402_, v_a_403_);
if (lean_obj_tag(v___x_408_) == 0)
{
lean_object* v_a_409_; lean_object* v___x_411_; uint8_t v_isShared_412_; uint8_t v_isSharedCheck_475_; 
v_a_409_ = lean_ctor_get(v___x_408_, 0);
v_isSharedCheck_475_ = !lean_is_exclusive(v___x_408_);
if (v_isSharedCheck_475_ == 0)
{
v___x_411_ = v___x_408_;
v_isShared_412_ = v_isSharedCheck_475_;
goto v_resetjp_410_;
}
else
{
lean_inc(v_a_409_);
lean_dec(v___x_408_);
v___x_411_ = lean_box(0);
v_isShared_412_ = v_isSharedCheck_475_;
goto v_resetjp_410_;
}
v_resetjp_410_:
{
if (lean_obj_tag(v_a_409_) == 1)
{
lean_object* v_val_413_; lean_object* v___x_415_; uint8_t v_isShared_416_; uint8_t v_isSharedCheck_470_; 
v_val_413_ = lean_ctor_get(v_a_409_, 0);
v_isSharedCheck_470_ = !lean_is_exclusive(v_a_409_);
if (v_isSharedCheck_470_ == 0)
{
v___x_415_ = v_a_409_;
v_isShared_416_ = v_isSharedCheck_470_;
goto v_resetjp_414_;
}
else
{
lean_inc(v_val_413_);
lean_dec(v_a_409_);
v___x_415_ = lean_box(0);
v_isShared_416_ = v_isSharedCheck_470_;
goto v_resetjp_414_;
}
v_resetjp_414_:
{
lean_object* v_fst_417_; lean_object* v_snd_418_; lean_object* v___x_419_; uint8_t v___x_420_; 
v_fst_417_ = lean_ctor_get(v_val_413_, 0);
lean_inc(v_fst_417_);
v_snd_418_ = lean_ctor_get(v_val_413_, 1);
lean_inc(v_snd_418_);
lean_dec(v_val_413_);
v___x_419_ = lean_st_ref_get(v_state_395_);
v___x_420_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_isReady(v___x_419_);
lean_dec(v___x_419_);
if (v___x_420_ == 0)
{
lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_426_; 
lean_dec(v_snd_418_);
lean_dec(v_fst_417_);
lean_del_object(v___x_415_);
v___x_421_ = lean_st_ref_take(v_state_395_);
v___x_422_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_skip(v___x_421_);
v___x_423_ = lean_st_ref_put(v_state_395_, v___x_422_);
v___x_424_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre___closed__0));
if (v_isShared_412_ == 0)
{
lean_ctor_set(v___x_411_, 0, v___x_424_);
v___x_426_ = v___x_411_;
goto v_reusejp_425_;
}
else
{
lean_object* v_reuseFailAlloc_427_; 
v_reuseFailAlloc_427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_427_, 0, v___x_424_);
v___x_426_ = v_reuseFailAlloc_427_;
goto v_reusejp_425_;
}
v_reusejp_425_:
{
return v___x_426_;
}
}
else
{
lean_object* v___x_428_; lean_object* v___x_429_; 
lean_del_object(v___x_411_);
v___x_428_ = lean_box(0);
v___x_429_ = l_Lean_Elab_Tactic_Conv_mkConvGoalFor(v_fst_417_, v___x_428_, v_a_400_, v_a_401_, v_a_402_, v_a_403_);
if (lean_obj_tag(v___x_429_) == 0)
{
lean_object* v_a_430_; lean_object* v_fst_431_; lean_object* v_snd_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; size_t v_sz_437_; size_t v___x_438_; lean_object* v___x_439_; 
v_a_430_ = lean_ctor_get(v___x_429_, 0);
lean_inc(v_a_430_);
lean_dec_ref_known(v___x_429_, 1);
v_fst_431_ = lean_ctor_get(v_a_430_, 0);
lean_inc(v_fst_431_);
v_snd_432_ = lean_ctor_get(v_a_430_, 1);
lean_inc(v_snd_432_);
lean_dec(v_a_430_);
v___x_433_ = lean_st_ref_take(v_state_395_);
v___x_434_ = l_Lean_Expr_mvarId_x21(v_snd_432_);
v___x_435_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_accept(v___x_434_, v___x_433_);
v___x_436_ = lean_st_ref_put(v_state_395_, v___x_435_);
v_sz_437_ = lean_array_size(v_snd_418_);
v___x_438_ = ((size_t)0ULL);
v___x_439_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre_spec__0___redArg(v_snd_418_, v_sz_437_, v___x_438_, v_snd_432_, v_a_400_, v_a_401_, v_a_402_, v_a_403_);
if (lean_obj_tag(v___x_439_) == 0)
{
lean_object* v_a_440_; lean_object* v___x_442_; uint8_t v_isShared_443_; uint8_t v_isSharedCheck_453_; 
v_a_440_ = lean_ctor_get(v___x_439_, 0);
v_isSharedCheck_453_ = !lean_is_exclusive(v___x_439_);
if (v_isSharedCheck_453_ == 0)
{
v___x_442_ = v___x_439_;
v_isShared_443_ = v_isSharedCheck_453_;
goto v_resetjp_441_;
}
else
{
lean_inc(v_a_440_);
lean_dec(v___x_439_);
v___x_442_ = lean_box(0);
v_isShared_443_ = v_isSharedCheck_453_;
goto v_resetjp_441_;
}
v_resetjp_441_:
{
lean_object* v___x_444_; lean_object* v___x_446_; 
v___x_444_ = l_Lean_mkAppN(v_fst_431_, v_snd_418_);
lean_dec(v_snd_418_);
if (v_isShared_416_ == 0)
{
lean_ctor_set(v___x_415_, 0, v_a_440_);
v___x_446_ = v___x_415_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v_a_440_);
v___x_446_ = v_reuseFailAlloc_452_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_450_; 
v___x_447_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_447_, 0, v___x_444_);
lean_ctor_set(v___x_447_, 1, v___x_446_);
lean_ctor_set_uint8(v___x_447_, sizeof(void*)*2, v___x_407_);
v___x_448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_448_, 0, v___x_447_);
if (v_isShared_443_ == 0)
{
lean_ctor_set(v___x_442_, 0, v___x_448_);
v___x_450_ = v___x_442_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_451_; 
v_reuseFailAlloc_451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_451_, 0, v___x_448_);
v___x_450_ = v_reuseFailAlloc_451_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
return v___x_450_;
}
}
}
}
else
{
lean_object* v_a_454_; lean_object* v___x_456_; uint8_t v_isShared_457_; uint8_t v_isSharedCheck_461_; 
lean_dec(v_fst_431_);
lean_dec(v_snd_418_);
lean_del_object(v___x_415_);
v_a_454_ = lean_ctor_get(v___x_439_, 0);
v_isSharedCheck_461_ = !lean_is_exclusive(v___x_439_);
if (v_isSharedCheck_461_ == 0)
{
v___x_456_ = v___x_439_;
v_isShared_457_ = v_isSharedCheck_461_;
goto v_resetjp_455_;
}
else
{
lean_inc(v_a_454_);
lean_dec(v___x_439_);
v___x_456_ = lean_box(0);
v_isShared_457_ = v_isSharedCheck_461_;
goto v_resetjp_455_;
}
v_resetjp_455_:
{
lean_object* v___x_459_; 
if (v_isShared_457_ == 0)
{
v___x_459_ = v___x_456_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v_a_454_);
v___x_459_ = v_reuseFailAlloc_460_;
goto v_reusejp_458_;
}
v_reusejp_458_:
{
return v___x_459_;
}
}
}
}
else
{
lean_object* v_a_462_; lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_469_; 
lean_dec(v_snd_418_);
lean_del_object(v___x_415_);
v_a_462_ = lean_ctor_get(v___x_429_, 0);
v_isSharedCheck_469_ = !lean_is_exclusive(v___x_429_);
if (v_isSharedCheck_469_ == 0)
{
v___x_464_ = v___x_429_;
v_isShared_465_ = v_isSharedCheck_469_;
goto v_resetjp_463_;
}
else
{
lean_inc(v_a_462_);
lean_dec(v___x_429_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_469_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
lean_object* v___x_467_; 
if (v_isShared_465_ == 0)
{
v___x_467_ = v___x_464_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v_a_462_);
v___x_467_ = v_reuseFailAlloc_468_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
return v___x_467_;
}
}
}
}
}
}
else
{
lean_object* v___x_471_; lean_object* v___x_473_; 
lean_dec(v_a_409_);
v___x_471_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre___closed__0));
if (v_isShared_412_ == 0)
{
lean_ctor_set(v___x_411_, 0, v___x_471_);
v___x_473_ = v___x_411_;
goto v_reusejp_472_;
}
else
{
lean_object* v_reuseFailAlloc_474_; 
v_reuseFailAlloc_474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_474_, 0, v___x_471_);
v___x_473_ = v_reuseFailAlloc_474_;
goto v_reusejp_472_;
}
v_reusejp_472_:
{
return v___x_473_;
}
}
}
}
else
{
lean_object* v_a_476_; lean_object* v___x_478_; uint8_t v_isShared_479_; uint8_t v_isSharedCheck_483_; 
v_a_476_ = lean_ctor_get(v___x_408_, 0);
v_isSharedCheck_483_ = !lean_is_exclusive(v___x_408_);
if (v_isSharedCheck_483_ == 0)
{
v___x_478_ = v___x_408_;
v_isShared_479_ = v_isSharedCheck_483_;
goto v_resetjp_477_;
}
else
{
lean_inc(v_a_476_);
lean_dec(v___x_408_);
v___x_478_ = lean_box(0);
v_isShared_479_ = v_isSharedCheck_483_;
goto v_resetjp_477_;
}
v_resetjp_477_:
{
lean_object* v___x_481_; 
if (v_isShared_479_ == 0)
{
v___x_481_ = v___x_478_;
goto v_reusejp_480_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_482_, 0, v_a_476_);
v___x_481_ = v_reuseFailAlloc_482_;
goto v_reusejp_480_;
}
v_reusejp_480_:
{
return v___x_481_;
}
}
}
}
else
{
lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; 
lean_dec_ref(v_pattern_394_);
v___x_484_ = lean_box(0);
v___x_485_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_485_, 0, v_e_396_);
lean_ctor_set(v___x_485_, 1, v___x_484_);
lean_ctor_set_uint8(v___x_485_, sizeof(void*)*2, v___x_407_);
v___x_486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_486_, 0, v___x_485_);
v___x_487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_487_, 0, v___x_486_);
return v___x_487_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre___boxed(lean_object* v_pattern_488_, lean_object* v_state_489_, lean_object* v_e_490_, lean_object* v_a_491_, lean_object* v_a_492_, lean_object* v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_, lean_object* v_a_497_, lean_object* v_a_498_){
_start:
{
lean_object* v_res_499_; 
v_res_499_ = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre(v_pattern_488_, v_state_489_, v_e_490_, v_a_491_, v_a_492_, v_a_493_, v_a_494_, v_a_495_, v_a_496_, v_a_497_);
lean_dec(v_a_497_);
lean_dec_ref(v_a_496_);
lean_dec(v_a_495_);
lean_dec_ref(v_a_494_);
lean_dec(v_a_493_);
lean_dec_ref(v_a_492_);
lean_dec(v_a_491_);
lean_dec(v_state_489_);
return v_res_499_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre_spec__0(lean_object* v_as_500_, size_t v_sz_501_, size_t v_i_502_, lean_object* v_b_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_){
_start:
{
lean_object* v___x_512_; 
v___x_512_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre_spec__0___redArg(v_as_500_, v_sz_501_, v_i_502_, v_b_503_, v___y_507_, v___y_508_, v___y_509_, v___y_510_);
return v___x_512_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre_spec__0___boxed(lean_object* v_as_513_, lean_object* v_sz_514_, lean_object* v_i_515_, lean_object* v_b_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_){
_start:
{
size_t v_sz_boxed_525_; size_t v_i_boxed_526_; lean_object* v_res_527_; 
v_sz_boxed_525_ = lean_unbox_usize(v_sz_514_);
lean_dec(v_sz_514_);
v_i_boxed_526_ = lean_unbox_usize(v_i_515_);
lean_dec(v_i_515_);
v_res_527_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre_spec__0(v_as_513_, v_sz_boxed_525_, v_i_boxed_526_, v_b_516_, v___y_517_, v___y_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_, v___y_523_);
lean_dec(v___y_523_);
lean_dec_ref(v___y_522_);
lean_dec(v___y_521_);
lean_dec_ref(v___y_520_);
lean_dec(v___y_519_);
lean_dec_ref(v___y_518_);
lean_dec(v___y_517_);
lean_dec_ref(v_as_513_);
return v_res_527_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; 
v___x_528_ = lean_box(0);
v___x_529_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_530_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_530_, 0, v___x_529_);
lean_ctor_set(v___x_530_, 1, v___x_528_);
return v___x_530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1___redArg(){
_start:
{
lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_532_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1___redArg___closed__0);
v___x_533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_533_, 0, v___x_532_);
return v___x_533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1___redArg___boxed(lean_object* v___y_534_){
_start:
{
lean_object* v_res_535_; 
v_res_535_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1___redArg();
return v_res_535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1(lean_object* v_00_u03b1_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_){
_start:
{
lean_object* v___x_546_; 
v___x_546_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1___redArg();
return v___x_546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1___boxed(lean_object* v_00_u03b1_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_){
_start:
{
lean_object* v_res_557_; 
v_res_557_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1(v_00_u03b1_547_, v___y_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_, v___y_555_);
lean_dec(v___y_555_);
lean_dec_ref(v___y_554_);
lean_dec(v___y_553_);
lean_dec_ref(v___y_552_);
lean_dec(v___y_551_);
lean_dec_ref(v___y_550_);
lean_dec(v___y_549_);
lean_dec_ref(v___y_548_);
return v_res_557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__2___redArg(lean_object* v_a_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_){
_start:
{
lean_object* v___x_566_; 
v___x_566_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v_a_558_, v___y_559_, v___y_560_, v___y_561_, v___y_562_, v___y_563_, v___y_564_);
return v___x_566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__2___redArg___boxed(lean_object* v_a_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_){
_start:
{
lean_object* v_res_575_; 
v_res_575_ = l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__2___redArg(v_a_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_);
lean_dec(v___y_573_);
lean_dec_ref(v___y_572_);
lean_dec(v___y_571_);
lean_dec_ref(v___y_570_);
lean_dec(v___y_569_);
lean_dec_ref(v___y_568_);
return v_res_575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__2(lean_object* v_00_u03b1_576_, lean_object* v_a_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_){
_start:
{
lean_object* v___x_585_; 
v___x_585_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v_a_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_, v___y_582_, v___y_583_);
return v___x_585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__2___boxed(lean_object* v_00_u03b1_586_, lean_object* v_a_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_){
_start:
{
lean_object* v_res_595_; 
v_res_595_ = l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__2(v_00_u03b1_586_, v_a_587_, v___y_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_);
lean_dec(v___y_593_);
lean_dec_ref(v___y_592_);
lean_dec(v___y_591_);
lean_dec_ref(v___y_590_);
lean_dec(v___y_589_);
lean_dec_ref(v___y_588_);
return v_res_595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__0(lean_object* v_e_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_){
_start:
{
lean_object* v___x_605_; lean_object* v___x_606_; 
v___x_605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_605_, 0, v_e_596_);
v___x_606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_606_, 0, v___x_605_);
return v___x_606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__0___boxed(lean_object* v_e_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_){
_start:
{
lean_object* v_res_616_; 
v_res_616_ = l_Lean_Elab_Tactic_Conv_evalPattern___lam__0(v_e_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_, v___y_614_);
lean_dec(v___y_614_);
lean_dec_ref(v___y_613_);
lean_dec(v___y_612_);
lean_dec_ref(v___y_611_);
lean_dec(v___y_610_);
lean_dec_ref(v___y_609_);
lean_dec(v___y_608_);
return v_res_616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__1(lean_object* v___x_617_, uint8_t v___x_618_, lean_object* v_e_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_){
_start:
{
lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; 
v___x_628_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_628_, 0, v_e_619_);
lean_ctor_set(v___x_628_, 1, v___x_617_);
lean_ctor_set_uint8(v___x_628_, sizeof(void*)*2, v___x_618_);
v___x_629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_629_, 0, v___x_628_);
v___x_630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_630_, 0, v___x_629_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__1___boxed(lean_object* v___x_631_, lean_object* v___x_632_, lean_object* v_e_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_){
_start:
{
uint8_t v___x_15299__boxed_642_; lean_object* v_res_643_; 
v___x_15299__boxed_642_ = lean_unbox(v___x_632_);
v_res_643_ = l_Lean_Elab_Tactic_Conv_evalPattern___lam__1(v___x_631_, v___x_15299__boxed_642_, v_e_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_);
lean_dec(v___y_640_);
lean_dec_ref(v___y_639_);
lean_dec(v___y_638_);
lean_dec_ref(v___y_637_);
lean_dec(v___y_636_);
lean_dec_ref(v___y_635_);
lean_dec(v___y_634_);
return v_res_643_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__2(lean_object* v___x_644_, lean_object* v_x_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_){
_start:
{
lean_object* v___x_654_; lean_object* v___x_655_; 
v___x_654_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_654_, 0, v___x_644_);
v___x_655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_655_, 0, v___x_654_);
return v___x_655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__2___boxed(lean_object* v___x_656_, lean_object* v_x_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_){
_start:
{
lean_object* v_res_666_; 
v_res_666_ = l_Lean_Elab_Tactic_Conv_evalPattern___lam__2(v___x_656_, v_x_657_, v___y_658_, v___y_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_, v___y_664_);
lean_dec(v___y_664_);
lean_dec_ref(v___y_663_);
lean_dec(v___y_662_);
lean_dec_ref(v___y_661_);
lean_dec(v___y_660_);
lean_dec_ref(v___y_659_);
lean_dec(v___y_658_);
lean_dec_ref(v_x_657_);
return v_res_666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__3(lean_object* v___x_667_, lean_object* v_x_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_){
_start:
{
lean_object* v___x_677_; 
v___x_677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_677_, 0, v___x_667_);
return v___x_677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__3___boxed(lean_object* v___x_678_, lean_object* v_x_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_){
_start:
{
lean_object* v_res_688_; 
v_res_688_ = l_Lean_Elab_Tactic_Conv_evalPattern___lam__3(v___x_678_, v_x_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
lean_dec(v___y_686_);
lean_dec_ref(v___y_685_);
lean_dec(v___y_684_);
lean_dec_ref(v___y_683_);
lean_dec(v___y_682_);
lean_dec_ref(v___y_681_);
lean_dec(v___y_680_);
lean_dec_ref(v_x_679_);
return v_res_688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__4(lean_object* v___x_689_, lean_object* v___x_690_, uint8_t v___x_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_){
_start:
{
lean_object* v___x_699_; 
v___x_699_ = l_Lean_Elab_Term_elabTerm(v___x_689_, v___x_690_, v___x_691_, v___x_691_, v___y_692_, v___y_693_, v___y_694_, v___y_695_, v___y_696_, v___y_697_);
if (lean_obj_tag(v___x_699_) == 0)
{
lean_object* v_a_700_; lean_object* v___x_701_; 
v_a_700_ = lean_ctor_get(v___x_699_, 0);
lean_inc(v_a_700_);
lean_dec_ref_known(v___x_699_, 1);
v___x_701_ = l_Lean_Meta_abstractMVars(v_a_700_, v___x_691_, v___y_694_, v___y_695_, v___y_696_, v___y_697_);
return v___x_701_;
}
else
{
lean_object* v_a_702_; lean_object* v___x_704_; uint8_t v_isShared_705_; uint8_t v_isSharedCheck_709_; 
v_a_702_ = lean_ctor_get(v___x_699_, 0);
v_isSharedCheck_709_ = !lean_is_exclusive(v___x_699_);
if (v_isSharedCheck_709_ == 0)
{
v___x_704_ = v___x_699_;
v_isShared_705_ = v_isSharedCheck_709_;
goto v_resetjp_703_;
}
else
{
lean_inc(v_a_702_);
lean_dec(v___x_699_);
v___x_704_ = lean_box(0);
v_isShared_705_ = v_isSharedCheck_709_;
goto v_resetjp_703_;
}
v_resetjp_703_:
{
lean_object* v___x_707_; 
if (v_isShared_705_ == 0)
{
v___x_707_ = v___x_704_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_708_; 
v_reuseFailAlloc_708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_708_, 0, v_a_702_);
v___x_707_ = v_reuseFailAlloc_708_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
return v___x_707_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__4___boxed(lean_object* v___x_710_, lean_object* v___x_711_, lean_object* v___x_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_){
_start:
{
uint8_t v___x_15402__boxed_720_; lean_object* v_res_721_; 
v___x_15402__boxed_720_ = lean_unbox(v___x_712_);
v_res_721_ = l_Lean_Elab_Tactic_Conv_evalPattern___lam__4(v___x_710_, v___x_711_, v___x_15402__boxed_720_, v___y_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_);
lean_dec(v___y_718_);
lean_dec_ref(v___y_717_);
lean_dec(v___y_716_);
lean_dec_ref(v___y_715_);
lean_dec(v___y_714_);
lean_dec_ref(v___y_713_);
return v_res_721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__5(lean_object* v___x_722_, lean_object* v___f_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_){
_start:
{
lean_object* v_toCold_731_; lean_object* v_currRecDepth_732_; lean_object* v_ref_733_; uint16_t v_optionFlags_734_; uint8_t v_suppressElabErrors_735_; uint8_t v_checkDeprecated_736_; uint8_t v_isRecordingDeps_737_; lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_746_; 
v_toCold_731_ = lean_ctor_get(v___y_728_, 0);
v_currRecDepth_732_ = lean_ctor_get(v___y_728_, 1);
v_ref_733_ = lean_ctor_get(v___y_728_, 2);
v_optionFlags_734_ = lean_ctor_get_uint16(v___y_728_, sizeof(void*)*3);
v_suppressElabErrors_735_ = lean_ctor_get_uint8(v___y_728_, sizeof(void*)*3 + 2);
v_checkDeprecated_736_ = lean_ctor_get_uint8(v___y_728_, sizeof(void*)*3 + 3);
v_isRecordingDeps_737_ = lean_ctor_get_uint8(v___y_728_, sizeof(void*)*3 + 4);
v_isSharedCheck_746_ = !lean_is_exclusive(v___y_728_);
if (v_isSharedCheck_746_ == 0)
{
v___x_739_ = v___y_728_;
v_isShared_740_ = v_isSharedCheck_746_;
goto v_resetjp_738_;
}
else
{
lean_inc(v_ref_733_);
lean_inc(v_currRecDepth_732_);
lean_inc(v_toCold_731_);
lean_dec(v___y_728_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_746_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
lean_object* v_ref_741_; lean_object* v___x_743_; 
v_ref_741_ = l_Lean_replaceRef(v___x_722_, v_ref_733_);
lean_dec(v_ref_733_);
if (v_isShared_740_ == 0)
{
lean_ctor_set(v___x_739_, 2, v_ref_741_);
v___x_743_ = v___x_739_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v_toCold_731_);
lean_ctor_set(v_reuseFailAlloc_745_, 1, v_currRecDepth_732_);
lean_ctor_set(v_reuseFailAlloc_745_, 2, v_ref_741_);
lean_ctor_set_uint16(v_reuseFailAlloc_745_, sizeof(void*)*3, v_optionFlags_734_);
lean_ctor_set_uint8(v_reuseFailAlloc_745_, sizeof(void*)*3 + 2, v_suppressElabErrors_735_);
lean_ctor_set_uint8(v_reuseFailAlloc_745_, sizeof(void*)*3 + 3, v_checkDeprecated_736_);
lean_ctor_set_uint8(v_reuseFailAlloc_745_, sizeof(void*)*3 + 4, v_isRecordingDeps_737_);
v___x_743_ = v_reuseFailAlloc_745_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
lean_object* v___x_744_; 
v___x_744_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v___f_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_, v___x_743_, v___y_729_);
lean_dec_ref(v___x_743_);
return v___x_744_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__5___boxed(lean_object* v___x_747_, lean_object* v___f_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_){
_start:
{
lean_object* v_res_756_; 
v_res_756_ = l_Lean_Elab_Tactic_Conv_evalPattern___lam__5(v___x_747_, v___f_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_);
lean_dec(v___y_754_);
lean_dec(v___y_752_);
lean_dec_ref(v___y_751_);
lean_dec(v___y_750_);
lean_dec_ref(v___y_749_);
lean_dec(v___x_747_);
return v_res_756_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__5(size_t v_sz_757_, size_t v_i_758_, lean_object* v_bs_759_){
_start:
{
uint8_t v___x_760_; 
v___x_760_ = lean_usize_dec_lt(v_i_758_, v_sz_757_);
if (v___x_760_ == 0)
{
return v_bs_759_;
}
else
{
lean_object* v_v_761_; lean_object* v_snd_762_; lean_object* v___x_763_; lean_object* v_bs_x27_764_; size_t v___x_765_; size_t v___x_766_; lean_object* v___x_767_; 
v_v_761_ = lean_array_uget_borrowed(v_bs_759_, v_i_758_);
v_snd_762_ = lean_ctor_get(v_v_761_, 1);
lean_inc(v_snd_762_);
v___x_763_ = lean_unsigned_to_nat(0u);
v_bs_x27_764_ = lean_array_uset(v_bs_759_, v_i_758_, v___x_763_);
v___x_765_ = ((size_t)1ULL);
v___x_766_ = lean_usize_add(v_i_758_, v___x_765_);
v___x_767_ = lean_array_uset(v_bs_x27_764_, v_i_758_, v_snd_762_);
v_i_758_ = v___x_766_;
v_bs_759_ = v___x_767_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__5___boxed(lean_object* v_sz_769_, lean_object* v_i_770_, lean_object* v_bs_771_){
_start:
{
size_t v_sz_boxed_772_; size_t v_i_boxed_773_; lean_object* v_res_774_; 
v_sz_boxed_772_ = lean_unbox_usize(v_sz_769_);
lean_dec(v_sz_769_);
v_i_boxed_773_ = lean_unbox_usize(v_i_770_);
lean_dec(v_i_770_);
v_res_774_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__5(v_sz_boxed_772_, v_i_boxed_773_, v_bs_771_);
return v_res_774_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4_spec__5(lean_object* v_msgData_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_){
_start:
{
lean_object* v___x_781_; lean_object* v_env_782_; uint8_t v___x_783_; lean_object* v_env_784_; lean_object* v___x_785_; lean_object* v_toCold_786_; lean_object* v_mctx_787_; lean_object* v_lctx_788_; lean_object* v_options_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; 
v___x_781_ = lean_st_ref_get(v___y_779_);
v_env_782_ = lean_ctor_get(v___x_781_, 0);
lean_inc_ref(v_env_782_);
lean_dec(v___x_781_);
v___x_783_ = 0;
v_env_784_ = l_Lean_Environment_setRecordingDeps(v_env_782_, v___x_783_);
v___x_785_ = lean_st_ref_get(v___y_777_);
v_toCold_786_ = lean_ctor_get(v___y_778_, 0);
v_mctx_787_ = lean_ctor_get(v___x_785_, 0);
lean_inc_ref(v_mctx_787_);
lean_dec(v___x_785_);
v_lctx_788_ = lean_ctor_get(v___y_776_, 2);
v_options_789_ = lean_ctor_get(v_toCold_786_, 2);
lean_inc_ref(v_options_789_);
lean_inc_ref(v_lctx_788_);
v___x_790_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_790_, 0, v_env_784_);
lean_ctor_set(v___x_790_, 1, v_mctx_787_);
lean_ctor_set(v___x_790_, 2, v_lctx_788_);
lean_ctor_set(v___x_790_, 3, v_options_789_);
v___x_791_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_791_, 0, v___x_790_);
lean_ctor_set(v___x_791_, 1, v_msgData_775_);
v___x_792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_792_, 0, v___x_791_);
return v___x_792_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4_spec__5___boxed(lean_object* v_msgData_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_){
_start:
{
lean_object* v_res_799_; 
v_res_799_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4_spec__5(v_msgData_793_, v___y_794_, v___y_795_, v___y_796_, v___y_797_);
lean_dec(v___y_797_);
lean_dec_ref(v___y_796_);
lean_dec(v___y_795_);
lean_dec_ref(v___y_794_);
return v_res_799_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg(lean_object* v_msg_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_){
_start:
{
lean_object* v_ref_806_; lean_object* v___x_807_; lean_object* v_a_808_; lean_object* v___x_810_; uint8_t v_isShared_811_; uint8_t v_isSharedCheck_816_; 
v_ref_806_ = lean_ctor_get(v___y_803_, 2);
v___x_807_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4_spec__5(v_msg_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_);
v_a_808_ = lean_ctor_get(v___x_807_, 0);
v_isSharedCheck_816_ = !lean_is_exclusive(v___x_807_);
if (v_isSharedCheck_816_ == 0)
{
v___x_810_ = v___x_807_;
v_isShared_811_ = v_isSharedCheck_816_;
goto v_resetjp_809_;
}
else
{
lean_inc(v_a_808_);
lean_dec(v___x_807_);
v___x_810_ = lean_box(0);
v_isShared_811_ = v_isSharedCheck_816_;
goto v_resetjp_809_;
}
v_resetjp_809_:
{
lean_object* v___x_812_; lean_object* v___x_814_; 
lean_inc(v_ref_806_);
v___x_812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_812_, 0, v_ref_806_);
lean_ctor_set(v___x_812_, 1, v_a_808_);
if (v_isShared_811_ == 0)
{
lean_ctor_set_tag(v___x_810_, 1);
lean_ctor_set(v___x_810_, 0, v___x_812_);
v___x_814_ = v___x_810_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v___x_812_);
v___x_814_ = v_reuseFailAlloc_815_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
return v___x_814_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg___boxed(lean_object* v_msg_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_){
_start:
{
lean_object* v_res_823_; 
v_res_823_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg(v_msg_817_, v___y_818_, v___y_819_, v___y_820_, v___y_821_);
lean_dec(v___y_821_);
lean_dec_ref(v___y_820_);
lean_dec(v___y_819_);
lean_dec_ref(v___y_818_);
return v_res_823_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg(lean_object* v_ref_824_, lean_object* v_msg_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_){
_start:
{
lean_object* v_toCold_835_; lean_object* v_currRecDepth_836_; lean_object* v_ref_837_; uint16_t v_optionFlags_838_; uint8_t v_suppressElabErrors_839_; uint8_t v_checkDeprecated_840_; uint8_t v_isRecordingDeps_841_; lean_object* v_ref_842_; lean_object* v___x_843_; lean_object* v___x_844_; 
v_toCold_835_ = lean_ctor_get(v___y_832_, 0);
v_currRecDepth_836_ = lean_ctor_get(v___y_832_, 1);
v_ref_837_ = lean_ctor_get(v___y_832_, 2);
v_optionFlags_838_ = lean_ctor_get_uint16(v___y_832_, sizeof(void*)*3);
v_suppressElabErrors_839_ = lean_ctor_get_uint8(v___y_832_, sizeof(void*)*3 + 2);
v_checkDeprecated_840_ = lean_ctor_get_uint8(v___y_832_, sizeof(void*)*3 + 3);
v_isRecordingDeps_841_ = lean_ctor_get_uint8(v___y_832_, sizeof(void*)*3 + 4);
v_ref_842_ = l_Lean_replaceRef(v_ref_824_, v_ref_837_);
lean_inc(v_currRecDepth_836_);
lean_inc_ref(v_toCold_835_);
v___x_843_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_843_, 0, v_toCold_835_);
lean_ctor_set(v___x_843_, 1, v_currRecDepth_836_);
lean_ctor_set(v___x_843_, 2, v_ref_842_);
lean_ctor_set_uint16(v___x_843_, sizeof(void*)*3, v_optionFlags_838_);
lean_ctor_set_uint8(v___x_843_, sizeof(void*)*3 + 2, v_suppressElabErrors_839_);
lean_ctor_set_uint8(v___x_843_, sizeof(void*)*3 + 3, v_checkDeprecated_840_);
lean_ctor_set_uint8(v___x_843_, sizeof(void*)*3 + 4, v_isRecordingDeps_841_);
v___x_844_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg(v_msg_825_, v___y_830_, v___y_831_, v___x_843_, v___y_833_);
lean_dec_ref_known(v___x_843_, 3);
return v___x_844_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg___boxed(lean_object* v_ref_845_, lean_object* v_msg_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_){
_start:
{
lean_object* v_res_856_; 
v_res_856_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg(v_ref_845_, v_msg_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_, v___y_851_, v___y_852_, v___y_853_, v___y_854_);
lean_dec(v___y_854_);
lean_dec_ref(v___y_853_);
lean_dec(v___y_852_);
lean_dec_ref(v___y_851_);
lean_dec(v___y_850_);
lean_dec_ref(v___y_849_);
lean_dec(v___y_848_);
lean_dec_ref(v___y_847_);
lean_dec(v_ref_845_);
return v_res_856_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_858_; lean_object* v___x_859_; 
v___x_858_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg___closed__0));
v___x_859_ = l_Lean_stringToMessageData(v___x_858_);
return v___x_859_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg(size_t v_sz_860_, size_t v_i_861_, lean_object* v_bs_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_){
_start:
{
uint8_t v___x_872_; 
v___x_872_ = lean_usize_dec_lt(v_i_861_, v_sz_860_);
if (v___x_872_ == 0)
{
lean_object* v___x_873_; 
v___x_873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_873_, 0, v_bs_862_);
return v___x_873_;
}
else
{
lean_object* v_v_874_; lean_object* v___x_875_; lean_object* v_bs_x27_876_; lean_object* v_a_878_; lean_object* v___x_883_; uint8_t v_isZero_884_; 
v_v_874_ = lean_array_uget(v_bs_862_, v_i_861_);
v___x_875_ = lean_unsigned_to_nat(0u);
v_bs_x27_876_ = lean_array_uset(v_bs_862_, v_i_861_, v___x_875_);
v___x_883_ = l_Lean_TSyntax_getNat(v_v_874_);
v_isZero_884_ = lean_nat_dec_eq(v___x_883_, v___x_875_);
if (v_isZero_884_ == 1)
{
lean_object* v___x_885_; lean_object* v___x_886_; 
lean_dec(v___x_883_);
v___x_885_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg___closed__1);
v___x_886_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg(v_v_874_, v___x_885_, v___y_863_, v___y_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_, v___y_869_, v___y_870_);
lean_dec(v_v_874_);
if (lean_obj_tag(v___x_886_) == 0)
{
lean_object* v_a_887_; 
v_a_887_ = lean_ctor_get(v___x_886_, 0);
lean_inc(v_a_887_);
lean_dec_ref_known(v___x_886_, 1);
v_a_878_ = v_a_887_;
goto v___jp_877_;
}
else
{
lean_object* v_a_888_; lean_object* v___x_890_; uint8_t v_isShared_891_; uint8_t v_isSharedCheck_895_; 
lean_dec_ref(v_bs_x27_876_);
v_a_888_ = lean_ctor_get(v___x_886_, 0);
v_isSharedCheck_895_ = !lean_is_exclusive(v___x_886_);
if (v_isSharedCheck_895_ == 0)
{
v___x_890_ = v___x_886_;
v_isShared_891_ = v_isSharedCheck_895_;
goto v_resetjp_889_;
}
else
{
lean_inc(v_a_888_);
lean_dec(v___x_886_);
v___x_890_ = lean_box(0);
v_isShared_891_ = v_isSharedCheck_895_;
goto v_resetjp_889_;
}
v_resetjp_889_:
{
lean_object* v___x_893_; 
if (v_isShared_891_ == 0)
{
v___x_893_ = v___x_890_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v_a_888_);
v___x_893_ = v_reuseFailAlloc_894_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
return v___x_893_;
}
}
}
}
else
{
lean_object* v___x_896_; lean_object* v_one_897_; lean_object* v_n_898_; lean_object* v___x_899_; 
lean_dec(v_v_874_);
v___x_896_ = lean_usize_to_nat(v_i_861_);
v_one_897_ = lean_unsigned_to_nat(1u);
v_n_898_ = lean_nat_sub(v___x_883_, v_one_897_);
lean_dec(v___x_883_);
v___x_899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_899_, 0, v_n_898_);
lean_ctor_set(v___x_899_, 1, v___x_896_);
v_a_878_ = v___x_899_;
goto v___jp_877_;
}
v___jp_877_:
{
size_t v___x_879_; size_t v___x_880_; lean_object* v___x_881_; 
v___x_879_ = ((size_t)1ULL);
v___x_880_ = lean_usize_add(v_i_861_, v___x_879_);
v___x_881_ = lean_array_uset(v_bs_x27_876_, v_i_861_, v_a_878_);
v_i_861_ = v___x_880_;
v_bs_862_ = v___x_881_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg___boxed(lean_object* v_sz_900_, lean_object* v_i_901_, lean_object* v_bs_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_){
_start:
{
size_t v_sz_boxed_912_; size_t v_i_boxed_913_; lean_object* v_res_914_; 
v_sz_boxed_912_ = lean_unbox_usize(v_sz_900_);
lean_dec(v_sz_900_);
v_i_boxed_913_ = lean_unbox_usize(v_i_901_);
lean_dec(v_i_901_);
v_res_914_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg(v_sz_boxed_912_, v_i_boxed_913_, v_bs_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_);
lean_dec(v___y_910_);
lean_dec_ref(v___y_909_);
lean_dec(v___y_908_);
lean_dec_ref(v___y_907_);
lean_dec(v___y_906_);
lean_dec_ref(v___y_905_);
lean_dec(v___y_904_);
lean_dec_ref(v___y_903_);
return v_res_914_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6_spec__8___redArg(lean_object* v_hi_915_, lean_object* v_pivot_916_, lean_object* v_as_917_, lean_object* v_i_918_, lean_object* v_k_919_){
_start:
{
uint8_t v___x_920_; 
v___x_920_ = lean_nat_dec_lt(v_k_919_, v_hi_915_);
if (v___x_920_ == 0)
{
lean_object* v___x_921_; lean_object* v___x_922_; 
lean_dec(v_k_919_);
v___x_921_ = lean_array_fswap(v_as_917_, v_i_918_, v_hi_915_);
v___x_922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_922_, 0, v_i_918_);
lean_ctor_set(v___x_922_, 1, v___x_921_);
return v___x_922_;
}
else
{
lean_object* v___x_923_; lean_object* v_fst_924_; lean_object* v_fst_925_; uint8_t v___x_926_; 
v___x_923_ = lean_array_fget_borrowed(v_as_917_, v_k_919_);
v_fst_924_ = lean_ctor_get(v___x_923_, 0);
v_fst_925_ = lean_ctor_get(v_pivot_916_, 0);
v___x_926_ = lean_nat_dec_lt(v_fst_924_, v_fst_925_);
if (v___x_926_ == 0)
{
lean_object* v___x_927_; lean_object* v___x_928_; 
v___x_927_ = lean_unsigned_to_nat(1u);
v___x_928_ = lean_nat_add(v_k_919_, v___x_927_);
lean_dec(v_k_919_);
v_k_919_ = v___x_928_;
goto _start;
}
else
{
lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; 
v___x_930_ = lean_array_fswap(v_as_917_, v_i_918_, v_k_919_);
v___x_931_ = lean_unsigned_to_nat(1u);
v___x_932_ = lean_nat_add(v_i_918_, v___x_931_);
lean_dec(v_i_918_);
v___x_933_ = lean_nat_add(v_k_919_, v___x_931_);
lean_dec(v_k_919_);
v_as_917_ = v___x_930_;
v_i_918_ = v___x_932_;
v_k_919_ = v___x_933_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6_spec__8___redArg___boxed(lean_object* v_hi_935_, lean_object* v_pivot_936_, lean_object* v_as_937_, lean_object* v_i_938_, lean_object* v_k_939_){
_start:
{
lean_object* v_res_940_; 
v_res_940_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6_spec__8___redArg(v_hi_935_, v_pivot_936_, v_as_937_, v_i_938_, v_k_939_);
lean_dec_ref(v_pivot_936_);
lean_dec(v_hi_935_);
return v_res_940_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg___lam__0(lean_object* v_x1_941_, lean_object* v_x2_942_){
_start:
{
lean_object* v_fst_943_; lean_object* v_fst_944_; uint8_t v___x_945_; 
v_fst_943_ = lean_ctor_get(v_x1_941_, 0);
v_fst_944_ = lean_ctor_get(v_x2_942_, 0);
v___x_945_ = lean_nat_dec_lt(v_fst_943_, v_fst_944_);
return v___x_945_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg___lam__0___boxed(lean_object* v_x1_946_, lean_object* v_x2_947_){
_start:
{
uint8_t v_res_948_; lean_object* v_r_949_; 
v_res_948_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg___lam__0(v_x1_946_, v_x2_947_);
lean_dec_ref(v_x2_947_);
lean_dec_ref(v_x1_946_);
v_r_949_ = lean_box(v_res_948_);
return v_r_949_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg(lean_object* v_n_950_, lean_object* v_as_951_, lean_object* v_lo_952_, lean_object* v_hi_953_){
_start:
{
lean_object* v___y_955_; uint8_t v___x_965_; 
v___x_965_ = lean_nat_dec_lt(v_lo_952_, v_hi_953_);
if (v___x_965_ == 0)
{
lean_dec(v_lo_952_);
return v_as_951_;
}
else
{
lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v_mid_968_; lean_object* v___y_970_; lean_object* v___y_976_; lean_object* v___x_981_; lean_object* v___x_982_; uint8_t v___x_983_; 
v___x_966_ = lean_nat_add(v_lo_952_, v_hi_953_);
v___x_967_ = lean_unsigned_to_nat(1u);
v_mid_968_ = lean_nat_shiftr(v___x_966_, v___x_967_);
lean_dec(v___x_966_);
v___x_981_ = lean_array_fget_borrowed(v_as_951_, v_mid_968_);
v___x_982_ = lean_array_fget_borrowed(v_as_951_, v_lo_952_);
v___x_983_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg___lam__0(v___x_981_, v___x_982_);
if (v___x_983_ == 0)
{
v___y_976_ = v_as_951_;
goto v___jp_975_;
}
else
{
lean_object* v___x_984_; 
v___x_984_ = lean_array_fswap(v_as_951_, v_lo_952_, v_mid_968_);
v___y_976_ = v___x_984_;
goto v___jp_975_;
}
v___jp_969_:
{
lean_object* v___x_971_; lean_object* v___x_972_; uint8_t v___x_973_; 
v___x_971_ = lean_array_fget_borrowed(v___y_970_, v_mid_968_);
v___x_972_ = lean_array_fget_borrowed(v___y_970_, v_hi_953_);
v___x_973_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg___lam__0(v___x_971_, v___x_972_);
if (v___x_973_ == 0)
{
lean_dec(v_mid_968_);
v___y_955_ = v___y_970_;
goto v___jp_954_;
}
else
{
lean_object* v___x_974_; 
v___x_974_ = lean_array_fswap(v___y_970_, v_mid_968_, v_hi_953_);
lean_dec(v_mid_968_);
v___y_955_ = v___x_974_;
goto v___jp_954_;
}
}
v___jp_975_:
{
lean_object* v___x_977_; lean_object* v___x_978_; uint8_t v___x_979_; 
v___x_977_ = lean_array_fget_borrowed(v___y_976_, v_hi_953_);
v___x_978_ = lean_array_fget_borrowed(v___y_976_, v_lo_952_);
v___x_979_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg___lam__0(v___x_977_, v___x_978_);
if (v___x_979_ == 0)
{
v___y_970_ = v___y_976_;
goto v___jp_969_;
}
else
{
lean_object* v___x_980_; 
v___x_980_ = lean_array_fswap(v___y_976_, v_lo_952_, v_hi_953_);
v___y_970_ = v___x_980_;
goto v___jp_969_;
}
}
}
v___jp_954_:
{
lean_object* v_pivot_956_; lean_object* v___x_957_; lean_object* v_fst_958_; lean_object* v_snd_959_; uint8_t v___x_960_; 
v_pivot_956_ = lean_array_fget(v___y_955_, v_hi_953_);
lean_inc_n(v_lo_952_, 2);
v___x_957_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6_spec__8___redArg(v_hi_953_, v_pivot_956_, v___y_955_, v_lo_952_, v_lo_952_);
lean_dec(v_pivot_956_);
v_fst_958_ = lean_ctor_get(v___x_957_, 0);
lean_inc(v_fst_958_);
v_snd_959_ = lean_ctor_get(v___x_957_, 1);
lean_inc(v_snd_959_);
lean_dec_ref(v___x_957_);
v___x_960_ = lean_nat_dec_le(v_hi_953_, v_fst_958_);
if (v___x_960_ == 0)
{
lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; 
v___x_961_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg(v_n_950_, v_snd_959_, v_lo_952_, v_fst_958_);
v___x_962_ = lean_unsigned_to_nat(1u);
v___x_963_ = lean_nat_add(v_fst_958_, v___x_962_);
lean_dec(v_fst_958_);
v_as_951_ = v___x_961_;
v_lo_952_ = v___x_963_;
goto _start;
}
else
{
lean_dec(v_fst_958_);
lean_dec(v_lo_952_);
return v_snd_959_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg___boxed(lean_object* v_n_985_, lean_object* v_as_986_, lean_object* v_lo_987_, lean_object* v_hi_988_){
_start:
{
lean_object* v_res_989_; 
v_res_989_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg(v_n_985_, v_as_986_, v_lo_987_, v_hi_988_);
lean_dec(v_hi_988_);
lean_dec(v_n_985_);
return v_res_989_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__12_spec__16___redArg(lean_object* v_x_990_, lean_object* v_x_991_, lean_object* v_x_992_, lean_object* v_x_993_){
_start:
{
lean_object* v_ks_994_; lean_object* v_vs_995_; lean_object* v___x_997_; uint8_t v_isShared_998_; uint8_t v_isSharedCheck_1019_; 
v_ks_994_ = lean_ctor_get(v_x_990_, 0);
v_vs_995_ = lean_ctor_get(v_x_990_, 1);
v_isSharedCheck_1019_ = !lean_is_exclusive(v_x_990_);
if (v_isSharedCheck_1019_ == 0)
{
v___x_997_ = v_x_990_;
v_isShared_998_ = v_isSharedCheck_1019_;
goto v_resetjp_996_;
}
else
{
lean_inc(v_vs_995_);
lean_inc(v_ks_994_);
lean_dec(v_x_990_);
v___x_997_ = lean_box(0);
v_isShared_998_ = v_isSharedCheck_1019_;
goto v_resetjp_996_;
}
v_resetjp_996_:
{
lean_object* v___x_999_; uint8_t v___x_1000_; 
v___x_999_ = lean_array_get_size(v_ks_994_);
v___x_1000_ = lean_nat_dec_lt(v_x_991_, v___x_999_);
if (v___x_1000_ == 0)
{
lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1004_; 
lean_dec(v_x_991_);
v___x_1001_ = lean_array_push(v_ks_994_, v_x_992_);
v___x_1002_ = lean_array_push(v_vs_995_, v_x_993_);
if (v_isShared_998_ == 0)
{
lean_ctor_set(v___x_997_, 1, v___x_1002_);
lean_ctor_set(v___x_997_, 0, v___x_1001_);
v___x_1004_ = v___x_997_;
goto v_reusejp_1003_;
}
else
{
lean_object* v_reuseFailAlloc_1005_; 
v_reuseFailAlloc_1005_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1005_, 0, v___x_1001_);
lean_ctor_set(v_reuseFailAlloc_1005_, 1, v___x_1002_);
v___x_1004_ = v_reuseFailAlloc_1005_;
goto v_reusejp_1003_;
}
v_reusejp_1003_:
{
return v___x_1004_;
}
}
else
{
lean_object* v_k_x27_1006_; uint8_t v___x_1007_; 
v_k_x27_1006_ = lean_array_fget_borrowed(v_ks_994_, v_x_991_);
v___x_1007_ = l_Lean_instBEqMVarId_beq(v_x_992_, v_k_x27_1006_);
if (v___x_1007_ == 0)
{
lean_object* v___x_1009_; 
if (v_isShared_998_ == 0)
{
v___x_1009_ = v___x_997_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v_ks_994_);
lean_ctor_set(v_reuseFailAlloc_1013_, 1, v_vs_995_);
v___x_1009_ = v_reuseFailAlloc_1013_;
goto v_reusejp_1008_;
}
v_reusejp_1008_:
{
lean_object* v___x_1010_; lean_object* v___x_1011_; 
v___x_1010_ = lean_unsigned_to_nat(1u);
v___x_1011_ = lean_nat_add(v_x_991_, v___x_1010_);
lean_dec(v_x_991_);
v_x_990_ = v___x_1009_;
v_x_991_ = v___x_1011_;
goto _start;
}
}
else
{
lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1017_; 
v___x_1014_ = lean_array_fset(v_ks_994_, v_x_991_, v_x_992_);
v___x_1015_ = lean_array_fset(v_vs_995_, v_x_991_, v_x_993_);
lean_dec(v_x_991_);
if (v_isShared_998_ == 0)
{
lean_ctor_set(v___x_997_, 1, v___x_1015_);
lean_ctor_set(v___x_997_, 0, v___x_1014_);
v___x_1017_ = v___x_997_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1018_; 
v_reuseFailAlloc_1018_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1018_, 0, v___x_1014_);
lean_ctor_set(v_reuseFailAlloc_1018_, 1, v___x_1015_);
v___x_1017_ = v_reuseFailAlloc_1018_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
return v___x_1017_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__12___redArg(lean_object* v_n_1020_, lean_object* v_k_1021_, lean_object* v_v_1022_){
_start:
{
lean_object* v___x_1023_; lean_object* v___x_1024_; 
v___x_1023_ = lean_unsigned_to_nat(0u);
v___x_1024_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__12_spec__16___redArg(v_n_1020_, v___x_1023_, v_k_1021_, v_v_1022_);
return v___x_1024_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_1025_; 
v___x_1025_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_1025_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg(lean_object* v_x_1026_, size_t v_x_1027_, size_t v_x_1028_, lean_object* v_x_1029_, lean_object* v_x_1030_){
_start:
{
if (lean_obj_tag(v_x_1026_) == 0)
{
lean_object* v_es_1031_; size_t v___x_1032_; size_t v___x_1033_; lean_object* v_j_1034_; lean_object* v___x_1035_; uint8_t v___x_1036_; 
v_es_1031_ = lean_ctor_get(v_x_1026_, 0);
v___x_1032_ = ((size_t)31ULL);
v___x_1033_ = lean_usize_land(v_x_1027_, v___x_1032_);
v_j_1034_ = lean_usize_to_nat(v___x_1033_);
v___x_1035_ = lean_array_get_size(v_es_1031_);
v___x_1036_ = lean_nat_dec_lt(v_j_1034_, v___x_1035_);
if (v___x_1036_ == 0)
{
lean_dec(v_j_1034_);
lean_dec(v_x_1030_);
lean_dec(v_x_1029_);
return v_x_1026_;
}
else
{
lean_object* v___x_1038_; uint8_t v_isShared_1039_; uint8_t v_isSharedCheck_1075_; 
lean_inc_ref(v_es_1031_);
v_isSharedCheck_1075_ = !lean_is_exclusive(v_x_1026_);
if (v_isSharedCheck_1075_ == 0)
{
lean_object* v_unused_1076_; 
v_unused_1076_ = lean_ctor_get(v_x_1026_, 0);
lean_dec(v_unused_1076_);
v___x_1038_ = v_x_1026_;
v_isShared_1039_ = v_isSharedCheck_1075_;
goto v_resetjp_1037_;
}
else
{
lean_dec(v_x_1026_);
v___x_1038_ = lean_box(0);
v_isShared_1039_ = v_isSharedCheck_1075_;
goto v_resetjp_1037_;
}
v_resetjp_1037_:
{
lean_object* v_v_1040_; lean_object* v___x_1041_; lean_object* v_xs_x27_1042_; lean_object* v___y_1044_; 
v_v_1040_ = lean_array_fget(v_es_1031_, v_j_1034_);
v___x_1041_ = lean_box(0);
v_xs_x27_1042_ = lean_array_fset(v_es_1031_, v_j_1034_, v___x_1041_);
switch(lean_obj_tag(v_v_1040_))
{
case 0:
{
lean_object* v_key_1049_; lean_object* v_val_1050_; lean_object* v___x_1052_; uint8_t v_isShared_1053_; uint8_t v_isSharedCheck_1060_; 
v_key_1049_ = lean_ctor_get(v_v_1040_, 0);
v_val_1050_ = lean_ctor_get(v_v_1040_, 1);
v_isSharedCheck_1060_ = !lean_is_exclusive(v_v_1040_);
if (v_isSharedCheck_1060_ == 0)
{
v___x_1052_ = v_v_1040_;
v_isShared_1053_ = v_isSharedCheck_1060_;
goto v_resetjp_1051_;
}
else
{
lean_inc(v_val_1050_);
lean_inc(v_key_1049_);
lean_dec(v_v_1040_);
v___x_1052_ = lean_box(0);
v_isShared_1053_ = v_isSharedCheck_1060_;
goto v_resetjp_1051_;
}
v_resetjp_1051_:
{
uint8_t v___x_1054_; 
v___x_1054_ = l_Lean_instBEqMVarId_beq(v_x_1029_, v_key_1049_);
if (v___x_1054_ == 0)
{
lean_object* v___x_1055_; lean_object* v___x_1056_; 
lean_del_object(v___x_1052_);
v___x_1055_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1049_, v_val_1050_, v_x_1029_, v_x_1030_);
v___x_1056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1056_, 0, v___x_1055_);
v___y_1044_ = v___x_1056_;
goto v___jp_1043_;
}
else
{
lean_object* v___x_1058_; 
lean_dec(v_val_1050_);
lean_dec(v_key_1049_);
if (v_isShared_1053_ == 0)
{
lean_ctor_set(v___x_1052_, 1, v_x_1030_);
lean_ctor_set(v___x_1052_, 0, v_x_1029_);
v___x_1058_ = v___x_1052_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v_x_1029_);
lean_ctor_set(v_reuseFailAlloc_1059_, 1, v_x_1030_);
v___x_1058_ = v_reuseFailAlloc_1059_;
goto v_reusejp_1057_;
}
v_reusejp_1057_:
{
v___y_1044_ = v___x_1058_;
goto v___jp_1043_;
}
}
}
}
case 1:
{
lean_object* v_node_1061_; lean_object* v___x_1063_; uint8_t v_isShared_1064_; uint8_t v_isSharedCheck_1073_; 
v_node_1061_ = lean_ctor_get(v_v_1040_, 0);
v_isSharedCheck_1073_ = !lean_is_exclusive(v_v_1040_);
if (v_isSharedCheck_1073_ == 0)
{
v___x_1063_ = v_v_1040_;
v_isShared_1064_ = v_isSharedCheck_1073_;
goto v_resetjp_1062_;
}
else
{
lean_inc(v_node_1061_);
lean_dec(v_v_1040_);
v___x_1063_ = lean_box(0);
v_isShared_1064_ = v_isSharedCheck_1073_;
goto v_resetjp_1062_;
}
v_resetjp_1062_:
{
size_t v___x_1065_; size_t v___x_1066_; size_t v___x_1067_; size_t v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1071_; 
v___x_1065_ = ((size_t)5ULL);
v___x_1066_ = lean_usize_shift_right(v_x_1027_, v___x_1065_);
v___x_1067_ = ((size_t)1ULL);
v___x_1068_ = lean_usize_add(v_x_1028_, v___x_1067_);
v___x_1069_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg(v_node_1061_, v___x_1066_, v___x_1068_, v_x_1029_, v_x_1030_);
if (v_isShared_1064_ == 0)
{
lean_ctor_set(v___x_1063_, 0, v___x_1069_);
v___x_1071_ = v___x_1063_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1072_; 
v_reuseFailAlloc_1072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1072_, 0, v___x_1069_);
v___x_1071_ = v_reuseFailAlloc_1072_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
v___y_1044_ = v___x_1071_;
goto v___jp_1043_;
}
}
}
default: 
{
lean_object* v___x_1074_; 
v___x_1074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1074_, 0, v_x_1029_);
lean_ctor_set(v___x_1074_, 1, v_x_1030_);
v___y_1044_ = v___x_1074_;
goto v___jp_1043_;
}
}
v___jp_1043_:
{
lean_object* v___x_1045_; lean_object* v___x_1047_; 
v___x_1045_ = lean_array_fset(v_xs_x27_1042_, v_j_1034_, v___y_1044_);
lean_dec(v_j_1034_);
if (v_isShared_1039_ == 0)
{
lean_ctor_set(v___x_1038_, 0, v___x_1045_);
v___x_1047_ = v___x_1038_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v___x_1045_);
v___x_1047_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
return v___x_1047_;
}
}
}
}
}
else
{
lean_object* v_ks_1077_; lean_object* v_vs_1078_; lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1096_; 
v_ks_1077_ = lean_ctor_get(v_x_1026_, 0);
v_vs_1078_ = lean_ctor_get(v_x_1026_, 1);
v_isSharedCheck_1096_ = !lean_is_exclusive(v_x_1026_);
if (v_isSharedCheck_1096_ == 0)
{
v___x_1080_ = v_x_1026_;
v_isShared_1081_ = v_isSharedCheck_1096_;
goto v_resetjp_1079_;
}
else
{
lean_inc(v_vs_1078_);
lean_inc(v_ks_1077_);
lean_dec(v_x_1026_);
v___x_1080_ = lean_box(0);
v_isShared_1081_ = v_isSharedCheck_1096_;
goto v_resetjp_1079_;
}
v_resetjp_1079_:
{
lean_object* v___x_1083_; 
if (v_isShared_1081_ == 0)
{
v___x_1083_ = v___x_1080_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v_ks_1077_);
lean_ctor_set(v_reuseFailAlloc_1095_, 1, v_vs_1078_);
v___x_1083_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
lean_object* v_newNode_1084_; size_t v___x_1085_; uint8_t v___x_1086_; 
v_newNode_1084_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__12___redArg(v___x_1083_, v_x_1029_, v_x_1030_);
v___x_1085_ = ((size_t)7ULL);
v___x_1086_ = lean_usize_dec_le(v___x_1085_, v_x_1028_);
if (v___x_1086_ == 0)
{
lean_object* v___x_1087_; lean_object* v___x_1088_; uint8_t v___x_1089_; 
v___x_1087_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1084_);
v___x_1088_ = lean_unsigned_to_nat(4u);
v___x_1089_ = lean_nat_dec_lt(v___x_1087_, v___x_1088_);
lean_dec(v___x_1087_);
if (v___x_1089_ == 0)
{
lean_object* v_ks_1090_; lean_object* v_vs_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; 
v_ks_1090_ = lean_ctor_get(v_newNode_1084_, 0);
lean_inc_ref(v_ks_1090_);
v_vs_1091_ = lean_ctor_get(v_newNode_1084_, 1);
lean_inc_ref(v_vs_1091_);
lean_dec_ref(v_newNode_1084_);
v___x_1092_ = lean_unsigned_to_nat(0u);
v___x_1093_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__0);
v___x_1094_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__13___redArg(v_x_1028_, v_ks_1090_, v_vs_1091_, v___x_1092_, v___x_1093_);
lean_dec_ref(v_vs_1091_);
lean_dec_ref(v_ks_1090_);
return v___x_1094_;
}
else
{
return v_newNode_1084_;
}
}
else
{
return v_newNode_1084_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__13___redArg(size_t v_depth_1097_, lean_object* v_keys_1098_, lean_object* v_vals_1099_, lean_object* v_i_1100_, lean_object* v_entries_1101_){
_start:
{
lean_object* v___x_1102_; uint8_t v___x_1103_; 
v___x_1102_ = lean_array_get_size(v_keys_1098_);
v___x_1103_ = lean_nat_dec_lt(v_i_1100_, v___x_1102_);
if (v___x_1103_ == 0)
{
lean_dec(v_i_1100_);
return v_entries_1101_;
}
else
{
lean_object* v_k_1104_; lean_object* v_v_1105_; uint64_t v___x_1106_; size_t v_h_1107_; size_t v___x_1108_; lean_object* v___x_1109_; size_t v___x_1110_; size_t v___x_1111_; size_t v___x_1112_; size_t v_h_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; 
v_k_1104_ = lean_array_fget_borrowed(v_keys_1098_, v_i_1100_);
v_v_1105_ = lean_array_fget_borrowed(v_vals_1099_, v_i_1100_);
v___x_1106_ = l_Lean_instHashableMVarId_hash(v_k_1104_);
v_h_1107_ = lean_uint64_to_usize(v___x_1106_);
v___x_1108_ = ((size_t)5ULL);
v___x_1109_ = lean_unsigned_to_nat(1u);
v___x_1110_ = ((size_t)1ULL);
v___x_1111_ = lean_usize_sub(v_depth_1097_, v___x_1110_);
v___x_1112_ = lean_usize_mul(v___x_1108_, v___x_1111_);
v_h_1113_ = lean_usize_shift_right(v_h_1107_, v___x_1112_);
v___x_1114_ = lean_nat_add(v_i_1100_, v___x_1109_);
lean_dec(v_i_1100_);
lean_inc(v_v_1105_);
lean_inc(v_k_1104_);
v___x_1115_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg(v_entries_1101_, v_h_1113_, v_depth_1097_, v_k_1104_, v_v_1105_);
v_i_1100_ = v___x_1114_;
v_entries_1101_ = v___x_1115_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__13___redArg___boxed(lean_object* v_depth_1117_, lean_object* v_keys_1118_, lean_object* v_vals_1119_, lean_object* v_i_1120_, lean_object* v_entries_1121_){
_start:
{
size_t v_depth_boxed_1122_; lean_object* v_res_1123_; 
v_depth_boxed_1122_ = lean_unbox_usize(v_depth_1117_);
lean_dec(v_depth_1117_);
v_res_1123_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__13___redArg(v_depth_boxed_1122_, v_keys_1118_, v_vals_1119_, v_i_1120_, v_entries_1121_);
lean_dec_ref(v_vals_1119_);
lean_dec_ref(v_keys_1118_);
return v_res_1123_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___boxed(lean_object* v_x_1124_, lean_object* v_x_1125_, lean_object* v_x_1126_, lean_object* v_x_1127_, lean_object* v_x_1128_){
_start:
{
size_t v_x_15854__boxed_1129_; size_t v_x_15855__boxed_1130_; lean_object* v_res_1131_; 
v_x_15854__boxed_1129_ = lean_unbox_usize(v_x_1125_);
lean_dec(v_x_1125_);
v_x_15855__boxed_1130_ = lean_unbox_usize(v_x_1126_);
lean_dec(v_x_1126_);
v_res_1131_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg(v_x_1124_, v_x_15854__boxed_1129_, v_x_15855__boxed_1130_, v_x_1127_, v_x_1128_);
return v_res_1131_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3___redArg(lean_object* v_x_1132_, lean_object* v_x_1133_, lean_object* v_x_1134_){
_start:
{
uint64_t v___x_1135_; size_t v___x_1136_; size_t v___x_1137_; lean_object* v___x_1138_; 
v___x_1135_ = l_Lean_instHashableMVarId_hash(v_x_1133_);
v___x_1136_ = lean_uint64_to_usize(v___x_1135_);
v___x_1137_ = ((size_t)1ULL);
v___x_1138_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg(v_x_1132_, v___x_1136_, v___x_1137_, v_x_1133_, v_x_1134_);
return v___x_1138_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3___redArg(lean_object* v_mvarId_1139_, lean_object* v_val_1140_, lean_object* v___y_1141_){
_start:
{
lean_object* v___x_1143_; lean_object* v_mctx_1144_; lean_object* v_cache_1145_; lean_object* v_zetaDeltaFVarIds_1146_; lean_object* v_postponed_1147_; lean_object* v_diag_1148_; lean_object* v___x_1150_; uint8_t v_isShared_1151_; uint8_t v_isSharedCheck_1177_; 
v___x_1143_ = lean_st_ref_take(v___y_1141_);
v_mctx_1144_ = lean_ctor_get(v___x_1143_, 0);
v_cache_1145_ = lean_ctor_get(v___x_1143_, 1);
v_zetaDeltaFVarIds_1146_ = lean_ctor_get(v___x_1143_, 2);
v_postponed_1147_ = lean_ctor_get(v___x_1143_, 3);
v_diag_1148_ = lean_ctor_get(v___x_1143_, 4);
v_isSharedCheck_1177_ = !lean_is_exclusive(v___x_1143_);
if (v_isSharedCheck_1177_ == 0)
{
v___x_1150_ = v___x_1143_;
v_isShared_1151_ = v_isSharedCheck_1177_;
goto v_resetjp_1149_;
}
else
{
lean_inc(v_diag_1148_);
lean_inc(v_postponed_1147_);
lean_inc(v_zetaDeltaFVarIds_1146_);
lean_inc(v_cache_1145_);
lean_inc(v_mctx_1144_);
lean_dec(v___x_1143_);
v___x_1150_ = lean_box(0);
v_isShared_1151_ = v_isSharedCheck_1177_;
goto v_resetjp_1149_;
}
v_resetjp_1149_:
{
lean_object* v_depth_1152_; lean_object* v_levelAssignDepth_1153_; lean_object* v_lmvarCounter_1154_; lean_object* v_mvarCounter_1155_; lean_object* v_lDecls_1156_; lean_object* v_decls_1157_; lean_object* v_userNames_1158_; lean_object* v_lAssignment_1159_; lean_object* v_eAssignment_1160_; lean_object* v_dAssignment_1161_; lean_object* v_instanceTypedMVars_1162_; lean_object* v___x_1164_; uint8_t v_isShared_1165_; uint8_t v_isSharedCheck_1176_; 
v_depth_1152_ = lean_ctor_get(v_mctx_1144_, 0);
v_levelAssignDepth_1153_ = lean_ctor_get(v_mctx_1144_, 1);
v_lmvarCounter_1154_ = lean_ctor_get(v_mctx_1144_, 2);
v_mvarCounter_1155_ = lean_ctor_get(v_mctx_1144_, 3);
v_lDecls_1156_ = lean_ctor_get(v_mctx_1144_, 4);
v_decls_1157_ = lean_ctor_get(v_mctx_1144_, 5);
v_userNames_1158_ = lean_ctor_get(v_mctx_1144_, 6);
v_lAssignment_1159_ = lean_ctor_get(v_mctx_1144_, 7);
v_eAssignment_1160_ = lean_ctor_get(v_mctx_1144_, 8);
v_dAssignment_1161_ = lean_ctor_get(v_mctx_1144_, 9);
v_instanceTypedMVars_1162_ = lean_ctor_get(v_mctx_1144_, 10);
v_isSharedCheck_1176_ = !lean_is_exclusive(v_mctx_1144_);
if (v_isSharedCheck_1176_ == 0)
{
v___x_1164_ = v_mctx_1144_;
v_isShared_1165_ = v_isSharedCheck_1176_;
goto v_resetjp_1163_;
}
else
{
lean_inc(v_instanceTypedMVars_1162_);
lean_inc(v_dAssignment_1161_);
lean_inc(v_eAssignment_1160_);
lean_inc(v_lAssignment_1159_);
lean_inc(v_userNames_1158_);
lean_inc(v_decls_1157_);
lean_inc(v_lDecls_1156_);
lean_inc(v_mvarCounter_1155_);
lean_inc(v_lmvarCounter_1154_);
lean_inc(v_levelAssignDepth_1153_);
lean_inc(v_depth_1152_);
lean_dec(v_mctx_1144_);
v___x_1164_ = lean_box(0);
v_isShared_1165_ = v_isSharedCheck_1176_;
goto v_resetjp_1163_;
}
v_resetjp_1163_:
{
lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1169_; 
v___x_1166_ = lean_box(0);
v___x_1167_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3___redArg(v_eAssignment_1160_, v_mvarId_1139_, v_val_1140_);
if (v_isShared_1165_ == 0)
{
lean_ctor_set(v___x_1164_, 8, v___x_1167_);
v___x_1169_ = v___x_1164_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1175_; 
v_reuseFailAlloc_1175_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1175_, 0, v_depth_1152_);
lean_ctor_set(v_reuseFailAlloc_1175_, 1, v_levelAssignDepth_1153_);
lean_ctor_set(v_reuseFailAlloc_1175_, 2, v_lmvarCounter_1154_);
lean_ctor_set(v_reuseFailAlloc_1175_, 3, v_mvarCounter_1155_);
lean_ctor_set(v_reuseFailAlloc_1175_, 4, v_lDecls_1156_);
lean_ctor_set(v_reuseFailAlloc_1175_, 5, v_decls_1157_);
lean_ctor_set(v_reuseFailAlloc_1175_, 6, v_userNames_1158_);
lean_ctor_set(v_reuseFailAlloc_1175_, 7, v_lAssignment_1159_);
lean_ctor_set(v_reuseFailAlloc_1175_, 8, v___x_1167_);
lean_ctor_set(v_reuseFailAlloc_1175_, 9, v_dAssignment_1161_);
lean_ctor_set(v_reuseFailAlloc_1175_, 10, v_instanceTypedMVars_1162_);
v___x_1169_ = v_reuseFailAlloc_1175_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
lean_object* v___x_1171_; 
if (v_isShared_1151_ == 0)
{
lean_ctor_set(v___x_1150_, 0, v___x_1169_);
v___x_1171_ = v___x_1150_;
goto v_reusejp_1170_;
}
else
{
lean_object* v_reuseFailAlloc_1174_; 
v_reuseFailAlloc_1174_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1174_, 0, v___x_1169_);
lean_ctor_set(v_reuseFailAlloc_1174_, 1, v_cache_1145_);
lean_ctor_set(v_reuseFailAlloc_1174_, 2, v_zetaDeltaFVarIds_1146_);
lean_ctor_set(v_reuseFailAlloc_1174_, 3, v_postponed_1147_);
lean_ctor_set(v_reuseFailAlloc_1174_, 4, v_diag_1148_);
v___x_1171_ = v_reuseFailAlloc_1174_;
goto v_reusejp_1170_;
}
v_reusejp_1170_:
{
lean_object* v___x_1172_; lean_object* v___x_1173_; 
v___x_1172_ = lean_st_ref_put(v___y_1141_, v___x_1171_);
v___x_1173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1173_, 0, v___x_1166_);
return v___x_1173_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3___redArg___boxed(lean_object* v_mvarId_1178_, lean_object* v_val_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_){
_start:
{
lean_object* v_res_1182_; 
v_res_1182_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3___redArg(v_mvarId_1178_, v_val_1179_, v___y_1180_);
lean_dec(v___y_1180_);
return v_res_1182_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg___lam__0(lean_object* v_x1_1183_, lean_object* v_x2_1184_){
_start:
{
lean_object* v_fst_1185_; lean_object* v_fst_1186_; uint8_t v___x_1187_; 
v_fst_1185_ = lean_ctor_get(v_x1_1183_, 0);
v_fst_1186_ = lean_ctor_get(v_x2_1184_, 0);
v___x_1187_ = lean_nat_dec_lt(v_fst_1185_, v_fst_1186_);
return v___x_1187_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg___lam__0___boxed(lean_object* v_x1_1188_, lean_object* v_x2_1189_){
_start:
{
uint8_t v_res_1190_; lean_object* v_r_1191_; 
v_res_1190_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg___lam__0(v_x1_1188_, v_x2_1189_);
lean_dec_ref(v_x2_1189_);
lean_dec_ref(v_x1_1188_);
v_r_1191_ = lean_box(v_res_1190_);
return v_r_1191_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9_spec__13___redArg(lean_object* v_hi_1192_, lean_object* v_pivot_1193_, lean_object* v_as_1194_, lean_object* v_i_1195_, lean_object* v_k_1196_){
_start:
{
uint8_t v___x_1197_; 
v___x_1197_ = lean_nat_dec_lt(v_k_1196_, v_hi_1192_);
if (v___x_1197_ == 0)
{
lean_object* v___x_1198_; lean_object* v___x_1199_; 
lean_dec(v_k_1196_);
v___x_1198_ = lean_array_fswap(v_as_1194_, v_i_1195_, v_hi_1192_);
v___x_1199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1199_, 0, v_i_1195_);
lean_ctor_set(v___x_1199_, 1, v___x_1198_);
return v___x_1199_;
}
else
{
lean_object* v___x_1200_; lean_object* v_fst_1201_; lean_object* v_fst_1202_; uint8_t v___x_1203_; 
v___x_1200_ = lean_array_fget_borrowed(v_as_1194_, v_k_1196_);
v_fst_1201_ = lean_ctor_get(v___x_1200_, 0);
v_fst_1202_ = lean_ctor_get(v_pivot_1193_, 0);
v___x_1203_ = lean_nat_dec_lt(v_fst_1201_, v_fst_1202_);
if (v___x_1203_ == 0)
{
lean_object* v___x_1204_; lean_object* v___x_1205_; 
v___x_1204_ = lean_unsigned_to_nat(1u);
v___x_1205_ = lean_nat_add(v_k_1196_, v___x_1204_);
lean_dec(v_k_1196_);
v_k_1196_ = v___x_1205_;
goto _start;
}
else
{
lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; 
v___x_1207_ = lean_array_fswap(v_as_1194_, v_i_1195_, v_k_1196_);
v___x_1208_ = lean_unsigned_to_nat(1u);
v___x_1209_ = lean_nat_add(v_i_1195_, v___x_1208_);
lean_dec(v_i_1195_);
v___x_1210_ = lean_nat_add(v_k_1196_, v___x_1208_);
lean_dec(v_k_1196_);
v_as_1194_ = v___x_1207_;
v_i_1195_ = v___x_1209_;
v_k_1196_ = v___x_1210_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9_spec__13___redArg___boxed(lean_object* v_hi_1212_, lean_object* v_pivot_1213_, lean_object* v_as_1214_, lean_object* v_i_1215_, lean_object* v_k_1216_){
_start:
{
lean_object* v_res_1217_; 
v_res_1217_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9_spec__13___redArg(v_hi_1212_, v_pivot_1213_, v_as_1214_, v_i_1215_, v_k_1216_);
lean_dec_ref(v_pivot_1213_);
lean_dec(v_hi_1212_);
return v_res_1217_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg(lean_object* v_n_1218_, lean_object* v_as_1219_, lean_object* v_lo_1220_, lean_object* v_hi_1221_){
_start:
{
lean_object* v___y_1223_; uint8_t v___x_1233_; 
v___x_1233_ = lean_nat_dec_lt(v_lo_1220_, v_hi_1221_);
if (v___x_1233_ == 0)
{
lean_dec(v_lo_1220_);
return v_as_1219_;
}
else
{
lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v_mid_1236_; lean_object* v___y_1238_; lean_object* v___y_1244_; lean_object* v___x_1249_; lean_object* v___x_1250_; uint8_t v___x_1251_; 
v___x_1234_ = lean_nat_add(v_lo_1220_, v_hi_1221_);
v___x_1235_ = lean_unsigned_to_nat(1u);
v_mid_1236_ = lean_nat_shiftr(v___x_1234_, v___x_1235_);
lean_dec(v___x_1234_);
v___x_1249_ = lean_array_fget_borrowed(v_as_1219_, v_mid_1236_);
v___x_1250_ = lean_array_fget_borrowed(v_as_1219_, v_lo_1220_);
v___x_1251_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg___lam__0(v___x_1249_, v___x_1250_);
if (v___x_1251_ == 0)
{
v___y_1244_ = v_as_1219_;
goto v___jp_1243_;
}
else
{
lean_object* v___x_1252_; 
v___x_1252_ = lean_array_fswap(v_as_1219_, v_lo_1220_, v_mid_1236_);
v___y_1244_ = v___x_1252_;
goto v___jp_1243_;
}
v___jp_1237_:
{
lean_object* v___x_1239_; lean_object* v___x_1240_; uint8_t v___x_1241_; 
v___x_1239_ = lean_array_fget_borrowed(v___y_1238_, v_mid_1236_);
v___x_1240_ = lean_array_fget_borrowed(v___y_1238_, v_hi_1221_);
v___x_1241_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg___lam__0(v___x_1239_, v___x_1240_);
if (v___x_1241_ == 0)
{
lean_dec(v_mid_1236_);
v___y_1223_ = v___y_1238_;
goto v___jp_1222_;
}
else
{
lean_object* v___x_1242_; 
v___x_1242_ = lean_array_fswap(v___y_1238_, v_mid_1236_, v_hi_1221_);
lean_dec(v_mid_1236_);
v___y_1223_ = v___x_1242_;
goto v___jp_1222_;
}
}
v___jp_1243_:
{
lean_object* v___x_1245_; lean_object* v___x_1246_; uint8_t v___x_1247_; 
v___x_1245_ = lean_array_fget_borrowed(v___y_1244_, v_hi_1221_);
v___x_1246_ = lean_array_fget_borrowed(v___y_1244_, v_lo_1220_);
v___x_1247_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg___lam__0(v___x_1245_, v___x_1246_);
if (v___x_1247_ == 0)
{
v___y_1238_ = v___y_1244_;
goto v___jp_1237_;
}
else
{
lean_object* v___x_1248_; 
v___x_1248_ = lean_array_fswap(v___y_1244_, v_lo_1220_, v_hi_1221_);
v___y_1238_ = v___x_1248_;
goto v___jp_1237_;
}
}
}
v___jp_1222_:
{
lean_object* v_pivot_1224_; lean_object* v___x_1225_; lean_object* v_fst_1226_; lean_object* v_snd_1227_; uint8_t v___x_1228_; 
v_pivot_1224_ = lean_array_fget(v___y_1223_, v_hi_1221_);
lean_inc_n(v_lo_1220_, 2);
v___x_1225_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9_spec__13___redArg(v_hi_1221_, v_pivot_1224_, v___y_1223_, v_lo_1220_, v_lo_1220_);
lean_dec(v_pivot_1224_);
v_fst_1226_ = lean_ctor_get(v___x_1225_, 0);
lean_inc(v_fst_1226_);
v_snd_1227_ = lean_ctor_get(v___x_1225_, 1);
lean_inc(v_snd_1227_);
lean_dec_ref(v___x_1225_);
v___x_1228_ = lean_nat_dec_le(v_hi_1221_, v_fst_1226_);
if (v___x_1228_ == 0)
{
lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; 
v___x_1229_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg(v_n_1218_, v_snd_1227_, v_lo_1220_, v_fst_1226_);
v___x_1230_ = lean_unsigned_to_nat(1u);
v___x_1231_ = lean_nat_add(v_fst_1226_, v___x_1230_);
lean_dec(v_fst_1226_);
v_as_1219_ = v___x_1229_;
v_lo_1220_ = v___x_1231_;
goto _start;
}
else
{
lean_dec(v_fst_1226_);
lean_dec(v_lo_1220_);
return v_snd_1227_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg___boxed(lean_object* v_n_1253_, lean_object* v_as_1254_, lean_object* v_lo_1255_, lean_object* v_hi_1256_){
_start:
{
lean_object* v_res_1257_; 
v_res_1257_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg(v_n_1253_, v_as_1254_, v_lo_1255_, v_hi_1256_);
lean_dec(v_hi_1256_);
lean_dec(v_n_1253_);
return v_res_1257_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11_spec__13___redArg(lean_object* v_as_1258_, lean_object* v_a_1259_, lean_object* v_x_1260_){
_start:
{
lean_object* v_zero_1261_; uint8_t v_isZero_1262_; 
v_zero_1261_ = lean_unsigned_to_nat(0u);
v_isZero_1262_ = lean_nat_dec_eq(v_x_1260_, v_zero_1261_);
if (v_isZero_1262_ == 1)
{
lean_dec(v_x_1260_);
return v_isZero_1262_;
}
else
{
lean_object* v_fst_1263_; lean_object* v_one_1264_; lean_object* v_n_1265_; lean_object* v___x_1266_; lean_object* v_fst_1267_; uint8_t v___x_1268_; 
v_fst_1263_ = lean_ctor_get(v_a_1259_, 0);
v_one_1264_ = lean_unsigned_to_nat(1u);
v_n_1265_ = lean_nat_sub(v_x_1260_, v_one_1264_);
lean_dec(v_x_1260_);
v___x_1266_ = lean_array_fget_borrowed(v_as_1258_, v_n_1265_);
v_fst_1267_ = lean_ctor_get(v___x_1266_, 0);
v___x_1268_ = lean_nat_dec_eq(v_fst_1263_, v_fst_1267_);
if (v___x_1268_ == 0)
{
v_x_1260_ = v_n_1265_;
goto _start;
}
else
{
lean_dec(v_n_1265_);
return v_isZero_1262_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11_spec__13___redArg___boxed(lean_object* v_as_1270_, lean_object* v_a_1271_, lean_object* v_x_1272_){
_start:
{
uint8_t v_res_1273_; lean_object* v_r_1274_; 
v_res_1273_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11_spec__13___redArg(v_as_1270_, v_a_1271_, v_x_1272_);
lean_dec_ref(v_a_1271_);
lean_dec_ref(v_as_1270_);
v_r_1274_ = lean_box(v_res_1273_);
return v_r_1274_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11(lean_object* v_as_1275_, lean_object* v_i_1276_){
_start:
{
lean_object* v___x_1277_; uint8_t v___x_1278_; 
v___x_1277_ = lean_array_get_size(v_as_1275_);
v___x_1278_ = lean_nat_dec_lt(v_i_1276_, v___x_1277_);
if (v___x_1278_ == 0)
{
uint8_t v___x_1279_; 
lean_dec(v_i_1276_);
v___x_1279_ = 1;
return v___x_1279_;
}
else
{
lean_object* v___x_1280_; uint8_t v___x_1281_; 
v___x_1280_ = lean_array_fget_borrowed(v_as_1275_, v_i_1276_);
lean_inc(v_i_1276_);
v___x_1281_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11_spec__13___redArg(v_as_1275_, v___x_1280_, v_i_1276_);
if (v___x_1281_ == 0)
{
lean_dec(v_i_1276_);
return v___x_1281_;
}
else
{
lean_object* v___x_1282_; lean_object* v___x_1283_; 
v___x_1282_ = lean_unsigned_to_nat(1u);
v___x_1283_ = lean_nat_add(v_i_1276_, v___x_1282_);
lean_dec(v_i_1276_);
v_i_1276_ = v___x_1283_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11___boxed(lean_object* v_as_1285_, lean_object* v_i_1286_){
_start:
{
uint8_t v_res_1287_; lean_object* v_r_1288_; 
v_res_1287_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11(v_as_1285_, v_i_1286_);
lean_dec_ref(v_as_1285_);
v_r_1288_ = lean_box(v_res_1287_);
return v_r_1288_;
}
}
LEAN_EXPORT uint8_t l_Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8(lean_object* v_as_1289_){
_start:
{
lean_object* v___x_1290_; uint8_t v___x_1291_; 
v___x_1290_ = lean_unsigned_to_nat(0u);
v___x_1291_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11(v_as_1289_, v___x_1290_);
return v___x_1291_;
}
}
LEAN_EXPORT lean_object* l_Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8___boxed(lean_object* v_as_1292_){
_start:
{
uint8_t v_res_1293_; lean_object* v_r_1294_; 
v_res_1293_ = l_Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8(v_as_1292_);
lean_dec_ref(v_as_1292_);
v_r_1294_ = lean_box(v_res_1293_);
return v_r_1294_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__0(void){
_start:
{
lean_object* v___x_1295_; 
v___x_1295_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1295_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__1(void){
_start:
{
lean_object* v___x_1296_; lean_object* v___x_1297_; 
v___x_1296_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__0, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__0_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__0);
v___x_1297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1297_, 0, v___x_1296_);
return v___x_1297_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__2(void){
_start:
{
lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; 
v___x_1298_ = lean_unsigned_to_nat(0u);
v___x_1299_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__1, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__1_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__1);
v___x_1300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1300_, 0, v___x_1299_);
lean_ctor_set(v___x_1300_, 1, v___x_1298_);
return v___x_1300_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__3(void){
_start:
{
lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; 
v___x_1301_ = lean_unsigned_to_nat(32u);
v___x_1302_ = lean_mk_empty_array_with_capacity(v___x_1301_);
v___x_1303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1303_, 0, v___x_1302_);
return v___x_1303_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__4(void){
_start:
{
size_t v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; 
v___x_1304_ = ((size_t)5ULL);
v___x_1305_ = lean_unsigned_to_nat(0u);
v___x_1306_ = lean_unsigned_to_nat(32u);
v___x_1307_ = lean_mk_empty_array_with_capacity(v___x_1306_);
v___x_1308_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__3, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__3_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__3);
v___x_1309_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1309_, 0, v___x_1308_);
lean_ctor_set(v___x_1309_, 1, v___x_1307_);
lean_ctor_set(v___x_1309_, 2, v___x_1305_);
lean_ctor_set(v___x_1309_, 3, v___x_1305_);
lean_ctor_set_usize(v___x_1309_, 4, v___x_1304_);
return v___x_1309_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__5(void){
_start:
{
lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; 
v___x_1310_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__4, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__4_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__4);
v___x_1311_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__1, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__1_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__1);
v___x_1312_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1312_, 0, v___x_1311_);
lean_ctor_set(v___x_1312_, 1, v___x_1311_);
lean_ctor_set(v___x_1312_, 2, v___x_1311_);
lean_ctor_set(v___x_1312_, 3, v___x_1310_);
return v___x_1312_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__6(void){
_start:
{
lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; 
v___x_1313_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__5, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__5_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__5);
v___x_1314_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__2, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__2_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__2);
v___x_1315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1315_, 0, v___x_1314_);
lean_ctor_set(v___x_1315_, 1, v___x_1313_);
return v___x_1315_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__8(void){
_start:
{
lean_object* v___x_1317_; lean_object* v___x_1318_; 
v___x_1317_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__7));
v___x_1318_ = l_Lean_stringToMessageData(v___x_1317_);
return v___x_1318_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__10(void){
_start:
{
lean_object* v___x_1320_; lean_object* v___x_1321_; 
v___x_1320_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__9));
v___x_1321_ = l_Lean_stringToMessageData(v___x_1320_);
return v___x_1321_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__12(void){
_start:
{
lean_object* v___x_1323_; lean_object* v___x_1324_; 
v___x_1323_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__11));
v___x_1324_ = l_Lean_stringToMessageData(v___x_1323_);
return v___x_1324_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__14(void){
_start:
{
lean_object* v___x_1326_; lean_object* v___x_1327_; 
v___x_1326_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__13));
v___x_1327_ = l_Lean_stringToMessageData(v___x_1326_);
return v___x_1327_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__17(void){
_start:
{
lean_object* v___x_1331_; lean_object* v___x_1332_; 
v___x_1331_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__16));
v___x_1332_ = l_Lean_stringToMessageData(v___x_1331_);
return v___x_1332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__6(uint8_t v___x_1353_, lean_object* v___f_1354_, uint8_t v___x_1355_, lean_object* v_stx_1356_, lean_object* v___x_1357_, lean_object* v___x_1358_, lean_object* v___x_1359_, lean_object* v___x_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_){
_start:
{
lean_object* v___y_1371_; lean_object* v_subgoals_1372_; lean_object* v___y_1373_; lean_object* v___y_1374_; lean_object* v___y_1375_; lean_object* v___y_1376_; lean_object* v___y_1377_; lean_object* v___y_1378_; lean_object* v___y_1379_; lean_object* v___y_1380_; lean_object* v___y_1418_; lean_object* v___y_1419_; lean_object* v___y_1420_; lean_object* v___y_1421_; lean_object* v___y_1422_; lean_object* v___y_1423_; lean_object* v___y_1424_; lean_object* v___y_1425_; lean_object* v___y_1426_; lean_object* v___y_1427_; lean_object* v___y_1432_; lean_object* v___y_1433_; lean_object* v___y_1434_; lean_object* v___y_1435_; lean_object* v___y_1436_; lean_object* v___y_1437_; lean_object* v___y_1438_; lean_object* v___y_1439_; lean_object* v___y_1440_; lean_object* v___y_1441_; lean_object* v___y_1442_; lean_object* v___y_1443_; lean_object* v___y_1444_; lean_object* v___y_1447_; lean_object* v___y_1448_; lean_object* v___y_1449_; lean_object* v___y_1450_; lean_object* v___y_1451_; lean_object* v___y_1452_; lean_object* v___y_1453_; lean_object* v___y_1454_; lean_object* v___y_1455_; lean_object* v___y_1456_; lean_object* v___y_1457_; lean_object* v___y_1458_; lean_object* v___y_1459_; 
if (v___x_1353_ == 0)
{
lean_object* v___x_1461_; 
lean_dec_ref(v___x_1360_);
lean_dec_ref(v___x_1359_);
lean_dec_ref(v___x_1358_);
lean_dec_ref(v___x_1357_);
lean_dec_ref(v___f_1354_);
v___x_1461_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1___redArg();
return v___x_1461_;
}
else
{
lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___y_1465_; lean_object* v___y_1466_; lean_object* v___y_1467_; lean_object* v___y_1468_; lean_object* v___y_1469_; lean_object* v___y_1470_; lean_object* v___y_1471_; lean_object* v___y_1472_; lean_object* v___y_1473_; lean_object* v___y_1474_; lean_object* v___y_1480_; lean_object* v___y_1481_; lean_object* v___y_1482_; lean_object* v___y_1483_; lean_object* v___y_1484_; lean_object* v___y_1485_; lean_object* v___y_1486_; lean_object* v___y_1487_; lean_object* v___y_1488_; lean_object* v___y_1489_; lean_object* v___y_1490_; lean_object* v___y_1491_; lean_object* v___y_1492_; lean_object* v___y_1493_; lean_object* v___y_1494_; uint8_t v___y_1495_; lean_object* v___y_1588_; lean_object* v___y_1589_; lean_object* v___y_1590_; lean_object* v___y_1591_; lean_object* v___y_1592_; lean_object* v_occs_1593_; lean_object* v___y_1594_; lean_object* v___y_1595_; lean_object* v___y_1596_; lean_object* v___y_1597_; lean_object* v___y_1598_; lean_object* v___y_1599_; lean_object* v___y_1600_; lean_object* v___y_1601_; lean_object* v___y_1616_; lean_object* v___y_1617_; lean_object* v___y_1618_; lean_object* v___y_1619_; lean_object* v___y_1620_; lean_object* v___y_1621_; lean_object* v___y_1622_; lean_object* v___y_1623_; lean_object* v___y_1624_; lean_object* v___y_1625_; lean_object* v___y_1626_; lean_object* v___y_1627_; lean_object* v___y_1628_; lean_object* v___y_1629_; lean_object* v___y_1634_; lean_object* v___y_1635_; lean_object* v___y_1636_; lean_object* v___y_1637_; lean_object* v___y_1638_; lean_object* v___y_1639_; lean_object* v___y_1640_; lean_object* v___y_1641_; lean_object* v___y_1642_; lean_object* v___y_1643_; lean_object* v___y_1644_; lean_object* v___y_1645_; lean_object* v___y_1646_; lean_object* v___y_1647_; lean_object* v___y_1652_; lean_object* v___y_1653_; lean_object* v___y_1654_; lean_object* v___y_1655_; lean_object* v___y_1656_; lean_object* v___y_1657_; lean_object* v___y_1658_; lean_object* v___y_1659_; lean_object* v___y_1660_; lean_object* v___y_1661_; lean_object* v___y_1662_; lean_object* v___y_1663_; lean_object* v___y_1664_; lean_object* v___y_1665_; lean_object* v___y_1666_; lean_object* v___y_1667_; lean_object* v___y_1668_; lean_object* v___y_1671_; lean_object* v___y_1672_; lean_object* v___y_1673_; lean_object* v___y_1674_; lean_object* v___y_1675_; lean_object* v___y_1676_; lean_object* v___y_1677_; lean_object* v___y_1678_; lean_object* v___y_1679_; lean_object* v___y_1680_; lean_object* v___y_1681_; lean_object* v___y_1682_; lean_object* v___y_1683_; lean_object* v___y_1684_; lean_object* v___y_1685_; lean_object* v___y_1686_; lean_object* v___y_1687_; lean_object* v_occs_1690_; lean_object* v___y_1691_; lean_object* v___y_1692_; lean_object* v___y_1693_; lean_object* v___y_1694_; lean_object* v___y_1695_; lean_object* v___y_1696_; lean_object* v___y_1697_; lean_object* v___y_1698_; lean_object* v___x_1784_; uint8_t v___x_1785_; 
v___x_1462_ = lean_unsigned_to_nat(0u);
v___x_1463_ = lean_unsigned_to_nat(1u);
v___x_1784_ = l_Lean_Syntax_getArg(v_stx_1356_, v___x_1463_);
v___x_1785_ = l_Lean_Syntax_isNone(v___x_1784_);
if (v___x_1785_ == 0)
{
uint8_t v___x_1786_; 
lean_inc(v___x_1784_);
v___x_1786_ = l_Lean_Syntax_matchesNull(v___x_1784_, v___x_1463_);
if (v___x_1786_ == 0)
{
lean_object* v___x_1787_; 
lean_dec(v___x_1784_);
lean_dec_ref(v___x_1360_);
lean_dec_ref(v___x_1359_);
lean_dec_ref(v___x_1358_);
lean_dec_ref(v___x_1357_);
lean_dec_ref(v___f_1354_);
v___x_1787_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1___redArg();
return v___x_1787_;
}
else
{
lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; uint8_t v___x_1791_; 
v___x_1788_ = l_Lean_Syntax_getArg(v___x_1784_, v___x_1462_);
lean_dec(v___x_1784_);
v___x_1789_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__27));
lean_inc_ref(v___x_1360_);
lean_inc_ref(v___x_1359_);
lean_inc_ref(v___x_1358_);
lean_inc_ref(v___x_1357_);
v___x_1790_ = l_Lean_Name_mkStr5(v___x_1357_, v___x_1358_, v___x_1359_, v___x_1360_, v___x_1789_);
lean_inc(v___x_1788_);
v___x_1791_ = l_Lean_Syntax_isOfKind(v___x_1788_, v___x_1790_);
lean_dec(v___x_1790_);
if (v___x_1791_ == 0)
{
lean_object* v___x_1792_; 
lean_dec(v___x_1788_);
lean_dec_ref(v___x_1360_);
lean_dec_ref(v___x_1359_);
lean_dec_ref(v___x_1358_);
lean_dec_ref(v___x_1357_);
lean_dec_ref(v___f_1354_);
v___x_1792_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1___redArg();
return v___x_1792_;
}
else
{
lean_object* v___x_1793_; lean_object* v_occs_1794_; lean_object* v___x_1795_; 
v___x_1793_ = lean_unsigned_to_nat(3u);
v_occs_1794_ = l_Lean_Syntax_getArg(v___x_1788_, v___x_1793_);
lean_dec(v___x_1788_);
v___x_1795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1795_, 0, v_occs_1794_);
v_occs_1690_ = v___x_1795_;
v___y_1691_ = v___y_1361_;
v___y_1692_ = v___y_1362_;
v___y_1693_ = v___y_1363_;
v___y_1694_ = v___y_1364_;
v___y_1695_ = v___y_1365_;
v___y_1696_ = v___y_1366_;
v___y_1697_ = v___y_1367_;
v___y_1698_ = v___y_1368_;
goto v___jp_1689_;
}
}
}
else
{
lean_object* v___x_1796_; 
lean_dec(v___x_1784_);
v___x_1796_ = lean_box(0);
v_occs_1690_ = v___x_1796_;
v___y_1691_ = v___y_1361_;
v___y_1692_ = v___y_1362_;
v___y_1693_ = v___y_1363_;
v___y_1694_ = v___y_1364_;
v___y_1695_ = v___y_1365_;
v___y_1696_ = v___y_1366_;
v___y_1697_ = v___y_1367_;
v___y_1698_ = v___y_1368_;
goto v___jp_1689_;
}
v___jp_1464_:
{
lean_object* v___x_1475_; uint8_t v___x_1476_; 
v___x_1475_ = lean_array_get_size(v___y_1466_);
v___x_1476_ = lean_nat_dec_eq(v___x_1475_, v___x_1462_);
if (v___x_1476_ == 0)
{
lean_object* v___x_1477_; uint8_t v___x_1478_; 
v___x_1477_ = lean_nat_sub(v___x_1475_, v___x_1463_);
v___x_1478_ = lean_nat_dec_le(v___x_1462_, v___x_1477_);
if (v___x_1478_ == 0)
{
lean_inc(v___x_1477_);
v___y_1447_ = v___y_1471_;
v___y_1448_ = v___y_1466_;
v___y_1449_ = v___y_1473_;
v___y_1450_ = v___y_1468_;
v___y_1451_ = v___y_1467_;
v___y_1452_ = v___y_1474_;
v___y_1453_ = v___y_1469_;
v___y_1454_ = v___y_1472_;
v___y_1455_ = v___y_1470_;
v___y_1456_ = v___x_1475_;
v___y_1457_ = v___y_1465_;
v___y_1458_ = v___x_1477_;
v___y_1459_ = v___x_1477_;
goto v___jp_1446_;
}
else
{
v___y_1447_ = v___y_1471_;
v___y_1448_ = v___y_1466_;
v___y_1449_ = v___y_1473_;
v___y_1450_ = v___y_1468_;
v___y_1451_ = v___y_1467_;
v___y_1452_ = v___y_1474_;
v___y_1453_ = v___y_1469_;
v___y_1454_ = v___y_1472_;
v___y_1455_ = v___y_1470_;
v___y_1456_ = v___x_1475_;
v___y_1457_ = v___y_1465_;
v___y_1458_ = v___x_1477_;
v___y_1459_ = v___x_1462_;
goto v___jp_1446_;
}
}
else
{
v___y_1418_ = v___y_1470_;
v___y_1419_ = v___y_1465_;
v___y_1420_ = v___y_1471_;
v___y_1421_ = v___y_1473_;
v___y_1422_ = v___y_1468_;
v___y_1423_ = v___y_1467_;
v___y_1424_ = v___y_1474_;
v___y_1425_ = v___y_1469_;
v___y_1426_ = v___y_1472_;
v___y_1427_ = v___y_1466_;
goto v___jp_1417_;
}
}
v___jp_1479_:
{
lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; 
v___x_1496_ = l_Lean_Meta_Simp_Context_setMemoize(v___y_1484_, v___y_1495_);
v___x_1497_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__6, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__6_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__6);
lean_inc(v___y_1483_);
lean_inc_ref(v___y_1482_);
v___x_1498_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre___boxed), 11, 2);
lean_closure_set(v___x_1498_, 0, v___y_1482_);
lean_closure_set(v___x_1498_, 1, v___y_1483_);
lean_inc_ref(v___y_1491_);
lean_inc_ref(v___y_1488_);
v___x_1499_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_1499_, 0, v___x_1498_);
lean_ctor_set(v___x_1499_, 1, v___y_1481_);
lean_ctor_set(v___x_1499_, 2, v___y_1488_);
lean_ctor_set(v___x_1499_, 3, v___f_1354_);
lean_ctor_set(v___x_1499_, 4, v___y_1491_);
lean_ctor_set_uint8(v___x_1499_, sizeof(void*)*5, v___x_1355_);
v___x_1500_ = l_Lean_Meta_Simp_main(v___y_1490_, v___x_1496_, v___x_1497_, v___x_1499_, v___y_1492_, v___y_1489_, v___y_1494_, v___y_1485_);
if (lean_obj_tag(v___x_1500_) == 0)
{
lean_object* v_a_1501_; lean_object* v_fst_1502_; lean_object* v___x_1504_; uint8_t v_isShared_1505_; uint8_t v_isSharedCheck_1577_; 
v_a_1501_ = lean_ctor_get(v___x_1500_, 0);
lean_inc(v_a_1501_);
lean_dec_ref_known(v___x_1500_, 1);
v_fst_1502_ = lean_ctor_get(v_a_1501_, 0);
v_isSharedCheck_1577_ = !lean_is_exclusive(v_a_1501_);
if (v_isSharedCheck_1577_ == 0)
{
lean_object* v_unused_1578_; 
v_unused_1578_ = lean_ctor_get(v_a_1501_, 1);
lean_dec(v_unused_1578_);
v___x_1504_ = v_a_1501_;
v_isShared_1505_ = v_isSharedCheck_1577_;
goto v_resetjp_1503_;
}
else
{
lean_inc(v_fst_1502_);
lean_dec(v_a_1501_);
v___x_1504_ = lean_box(0);
v_isShared_1505_ = v_isSharedCheck_1577_;
goto v_resetjp_1503_;
}
v_resetjp_1503_:
{
lean_object* v___x_1506_; 
v___x_1506_ = lean_st_ref_get(v___y_1483_);
lean_dec(v___y_1483_);
if (lean_obj_tag(v___x_1506_) == 0)
{
lean_object* v_subgoals_1507_; lean_object* v___x_1508_; uint8_t v___x_1509_; 
v_subgoals_1507_ = lean_ctor_get(v___x_1506_, 0);
lean_inc_ref(v_subgoals_1507_);
lean_dec_ref_known(v___x_1506_, 1);
v___x_1508_ = lean_array_get_size(v_subgoals_1507_);
v___x_1509_ = lean_nat_dec_eq(v___x_1508_, v___x_1462_);
if (v___x_1509_ == 0)
{
lean_del_object(v___x_1504_);
lean_dec_ref(v___y_1482_);
v___y_1371_ = v_fst_1502_;
v_subgoals_1372_ = v_subgoals_1507_;
v___y_1373_ = v___y_1486_;
v___y_1374_ = v___y_1487_;
v___y_1375_ = v___y_1493_;
v___y_1376_ = v___y_1480_;
v___y_1377_ = v___y_1492_;
v___y_1378_ = v___y_1489_;
v___y_1379_ = v___y_1494_;
v___y_1380_ = v___y_1485_;
goto v___jp_1370_;
}
else
{
lean_object* v_expr_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1514_; 
lean_dec_ref(v_subgoals_1507_);
lean_dec(v_fst_1502_);
v_expr_1510_ = lean_ctor_get(v___y_1482_, 2);
lean_inc_ref(v_expr_1510_);
lean_dec_ref(v___y_1482_);
v___x_1511_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__8, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__8_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__8);
v___x_1512_ = l_Lean_indentExpr(v_expr_1510_);
if (v_isShared_1505_ == 0)
{
lean_ctor_set_tag(v___x_1504_, 7);
lean_ctor_set(v___x_1504_, 1, v___x_1512_);
lean_ctor_set(v___x_1504_, 0, v___x_1511_);
v___x_1514_ = v___x_1504_;
goto v_reusejp_1513_;
}
else
{
lean_object* v_reuseFailAlloc_1524_; 
v_reuseFailAlloc_1524_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1524_, 0, v___x_1511_);
lean_ctor_set(v_reuseFailAlloc_1524_, 1, v___x_1512_);
v___x_1514_ = v_reuseFailAlloc_1524_;
goto v_reusejp_1513_;
}
v_reusejp_1513_:
{
lean_object* v___x_1515_; lean_object* v_a_1516_; lean_object* v___x_1518_; uint8_t v_isShared_1519_; uint8_t v_isSharedCheck_1523_; 
v___x_1515_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg(v___x_1514_, v___y_1492_, v___y_1489_, v___y_1494_, v___y_1485_);
v_a_1516_ = lean_ctor_get(v___x_1515_, 0);
v_isSharedCheck_1523_ = !lean_is_exclusive(v___x_1515_);
if (v_isSharedCheck_1523_ == 0)
{
v___x_1518_ = v___x_1515_;
v_isShared_1519_ = v_isSharedCheck_1523_;
goto v_resetjp_1517_;
}
else
{
lean_inc(v_a_1516_);
lean_dec(v___x_1515_);
v___x_1518_ = lean_box(0);
v_isShared_1519_ = v_isSharedCheck_1523_;
goto v_resetjp_1517_;
}
v_resetjp_1517_:
{
lean_object* v___x_1521_; 
if (v_isShared_1519_ == 0)
{
v___x_1521_ = v___x_1518_;
goto v_reusejp_1520_;
}
else
{
lean_object* v_reuseFailAlloc_1522_; 
v_reuseFailAlloc_1522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1522_, 0, v_a_1516_);
v___x_1521_ = v_reuseFailAlloc_1522_;
goto v_reusejp_1520_;
}
v_reusejp_1520_:
{
return v___x_1521_;
}
}
}
}
}
else
{
lean_object* v_subgoals_1525_; lean_object* v_idx_1526_; lean_object* v_remaining_1527_; uint8_t v___x_1528_; 
v_subgoals_1525_ = lean_ctor_get(v___x_1506_, 0);
lean_inc_ref(v_subgoals_1525_);
v_idx_1526_ = lean_ctor_get(v___x_1506_, 1);
lean_inc(v_idx_1526_);
v_remaining_1527_ = lean_ctor_get(v___x_1506_, 2);
lean_inc(v_remaining_1527_);
lean_dec_ref_known(v___x_1506_, 3);
v___x_1528_ = lean_nat_dec_eq(v_idx_1526_, v___x_1462_);
if (v___x_1528_ == 0)
{
lean_object* v___x_1529_; 
lean_dec_ref(v___y_1482_);
v___x_1529_ = l_List_getLast_x3f___redArg(v_remaining_1527_);
lean_dec(v_remaining_1527_);
if (lean_obj_tag(v___x_1529_) == 1)
{
lean_object* v_val_1530_; lean_object* v___x_1532_; uint8_t v_isShared_1533_; uint8_t v_isSharedCheck_1561_; 
lean_dec_ref(v_subgoals_1525_);
lean_dec(v_fst_1502_);
v_val_1530_ = lean_ctor_get(v___x_1529_, 0);
v_isSharedCheck_1561_ = !lean_is_exclusive(v___x_1529_);
if (v_isSharedCheck_1561_ == 0)
{
v___x_1532_ = v___x_1529_;
v_isShared_1533_ = v_isSharedCheck_1561_;
goto v_resetjp_1531_;
}
else
{
lean_inc(v_val_1530_);
lean_dec(v___x_1529_);
v___x_1532_ = lean_box(0);
v_isShared_1533_ = v_isSharedCheck_1561_;
goto v_resetjp_1531_;
}
v_resetjp_1531_:
{
lean_object* v_fst_1534_; lean_object* v___x_1536_; uint8_t v_isShared_1537_; uint8_t v_isSharedCheck_1559_; 
v_fst_1534_ = lean_ctor_get(v_val_1530_, 0);
v_isSharedCheck_1559_ = !lean_is_exclusive(v_val_1530_);
if (v_isSharedCheck_1559_ == 0)
{
lean_object* v_unused_1560_; 
v_unused_1560_ = lean_ctor_get(v_val_1530_, 1);
lean_dec(v_unused_1560_);
v___x_1536_ = v_val_1530_;
v_isShared_1537_ = v_isSharedCheck_1559_;
goto v_resetjp_1535_;
}
else
{
lean_inc(v_fst_1534_);
lean_dec(v_val_1530_);
v___x_1536_ = lean_box(0);
v_isShared_1537_ = v_isSharedCheck_1559_;
goto v_resetjp_1535_;
}
v_resetjp_1535_:
{
lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1541_; 
v___x_1538_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__10, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__10_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__10);
v___x_1539_ = l_Nat_reprFast(v_idx_1526_);
if (v_isShared_1533_ == 0)
{
lean_ctor_set_tag(v___x_1532_, 3);
lean_ctor_set(v___x_1532_, 0, v___x_1539_);
v___x_1541_ = v___x_1532_;
goto v_reusejp_1540_;
}
else
{
lean_object* v_reuseFailAlloc_1558_; 
v_reuseFailAlloc_1558_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1558_, 0, v___x_1539_);
v___x_1541_ = v_reuseFailAlloc_1558_;
goto v_reusejp_1540_;
}
v_reusejp_1540_:
{
lean_object* v___x_1542_; lean_object* v___x_1544_; 
v___x_1542_ = l_Lean_MessageData_ofFormat(v___x_1541_);
if (v_isShared_1537_ == 0)
{
lean_ctor_set_tag(v___x_1536_, 7);
lean_ctor_set(v___x_1536_, 1, v___x_1542_);
lean_ctor_set(v___x_1536_, 0, v___x_1538_);
v___x_1544_ = v___x_1536_;
goto v_reusejp_1543_;
}
else
{
lean_object* v_reuseFailAlloc_1557_; 
v_reuseFailAlloc_1557_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1557_, 0, v___x_1538_);
lean_ctor_set(v_reuseFailAlloc_1557_, 1, v___x_1542_);
v___x_1544_ = v_reuseFailAlloc_1557_;
goto v_reusejp_1543_;
}
v_reusejp_1543_:
{
lean_object* v___x_1545_; lean_object* v___x_1547_; 
v___x_1545_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__12, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__12_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__12);
if (v_isShared_1505_ == 0)
{
lean_ctor_set_tag(v___x_1504_, 7);
lean_ctor_set(v___x_1504_, 1, v___x_1545_);
lean_ctor_set(v___x_1504_, 0, v___x_1544_);
v___x_1547_ = v___x_1504_;
goto v_reusejp_1546_;
}
else
{
lean_object* v_reuseFailAlloc_1556_; 
v_reuseFailAlloc_1556_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1556_, 0, v___x_1544_);
lean_ctor_set(v_reuseFailAlloc_1556_, 1, v___x_1545_);
v___x_1547_ = v_reuseFailAlloc_1556_;
goto v_reusejp_1546_;
}
v_reusejp_1546_:
{
lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; 
v___x_1548_ = lean_nat_add(v_fst_1534_, v___x_1463_);
lean_dec(v_fst_1534_);
v___x_1549_ = l_Nat_reprFast(v___x_1548_);
v___x_1550_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1550_, 0, v___x_1549_);
v___x_1551_ = l_Lean_MessageData_ofFormat(v___x_1550_);
v___x_1552_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1552_, 0, v___x_1547_);
lean_ctor_set(v___x_1552_, 1, v___x_1551_);
v___x_1553_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__14, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__14_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__14);
v___x_1554_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1554_, 0, v___x_1552_);
lean_ctor_set(v___x_1554_, 1, v___x_1553_);
v___x_1555_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg(v___x_1554_, v___y_1492_, v___y_1489_, v___y_1494_, v___y_1485_);
return v___x_1555_;
}
}
}
}
}
}
else
{
lean_dec(v___x_1529_);
lean_dec(v_idx_1526_);
lean_del_object(v___x_1504_);
v___y_1465_ = v_fst_1502_;
v___y_1466_ = v_subgoals_1525_;
v___y_1467_ = v___y_1486_;
v___y_1468_ = v___y_1487_;
v___y_1469_ = v___y_1493_;
v___y_1470_ = v___y_1480_;
v___y_1471_ = v___y_1492_;
v___y_1472_ = v___y_1489_;
v___y_1473_ = v___y_1494_;
v___y_1474_ = v___y_1485_;
goto v___jp_1464_;
}
}
else
{
lean_object* v_expr_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1566_; 
lean_dec(v_remaining_1527_);
lean_dec(v_idx_1526_);
lean_dec_ref(v_subgoals_1525_);
lean_dec(v_fst_1502_);
v_expr_1562_ = lean_ctor_get(v___y_1482_, 2);
lean_inc_ref(v_expr_1562_);
lean_dec_ref(v___y_1482_);
v___x_1563_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__8, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__8_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__8);
v___x_1564_ = l_Lean_indentExpr(v_expr_1562_);
if (v_isShared_1505_ == 0)
{
lean_ctor_set_tag(v___x_1504_, 7);
lean_ctor_set(v___x_1504_, 1, v___x_1564_);
lean_ctor_set(v___x_1504_, 0, v___x_1563_);
v___x_1566_ = v___x_1504_;
goto v_reusejp_1565_;
}
else
{
lean_object* v_reuseFailAlloc_1576_; 
v_reuseFailAlloc_1576_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1576_, 0, v___x_1563_);
lean_ctor_set(v_reuseFailAlloc_1576_, 1, v___x_1564_);
v___x_1566_ = v_reuseFailAlloc_1576_;
goto v_reusejp_1565_;
}
v_reusejp_1565_:
{
lean_object* v___x_1567_; lean_object* v_a_1568_; lean_object* v___x_1570_; uint8_t v_isShared_1571_; uint8_t v_isSharedCheck_1575_; 
v___x_1567_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg(v___x_1566_, v___y_1492_, v___y_1489_, v___y_1494_, v___y_1485_);
v_a_1568_ = lean_ctor_get(v___x_1567_, 0);
v_isSharedCheck_1575_ = !lean_is_exclusive(v___x_1567_);
if (v_isSharedCheck_1575_ == 0)
{
v___x_1570_ = v___x_1567_;
v_isShared_1571_ = v_isSharedCheck_1575_;
goto v_resetjp_1569_;
}
else
{
lean_inc(v_a_1568_);
lean_dec(v___x_1567_);
v___x_1570_ = lean_box(0);
v_isShared_1571_ = v_isSharedCheck_1575_;
goto v_resetjp_1569_;
}
v_resetjp_1569_:
{
lean_object* v___x_1573_; 
if (v_isShared_1571_ == 0)
{
v___x_1573_ = v___x_1570_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1574_; 
v_reuseFailAlloc_1574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1574_, 0, v_a_1568_);
v___x_1573_ = v_reuseFailAlloc_1574_;
goto v_reusejp_1572_;
}
v_reusejp_1572_:
{
return v___x_1573_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1579_; lean_object* v___x_1581_; uint8_t v_isShared_1582_; uint8_t v_isSharedCheck_1586_; 
lean_dec(v___y_1483_);
lean_dec_ref(v___y_1482_);
v_a_1579_ = lean_ctor_get(v___x_1500_, 0);
v_isSharedCheck_1586_ = !lean_is_exclusive(v___x_1500_);
if (v_isSharedCheck_1586_ == 0)
{
v___x_1581_ = v___x_1500_;
v_isShared_1582_ = v_isSharedCheck_1586_;
goto v_resetjp_1580_;
}
else
{
lean_inc(v_a_1579_);
lean_dec(v___x_1500_);
v___x_1581_ = lean_box(0);
v_isShared_1582_ = v_isSharedCheck_1586_;
goto v_resetjp_1580_;
}
v_resetjp_1580_:
{
lean_object* v___x_1584_; 
if (v_isShared_1582_ == 0)
{
v___x_1584_ = v___x_1581_;
goto v_reusejp_1583_;
}
else
{
lean_object* v_reuseFailAlloc_1585_; 
v_reuseFailAlloc_1585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1585_, 0, v_a_1579_);
v___x_1584_ = v_reuseFailAlloc_1585_;
goto v_reusejp_1583_;
}
v_reusejp_1583_:
{
return v___x_1584_;
}
}
}
}
v___jp_1587_:
{
lean_object* v___x_1602_; lean_object* v___x_1603_; 
lean_inc_ref(v_occs_1593_);
v___x_1602_ = lean_st_mk_ref(v_occs_1593_);
v___x_1603_ = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_getContext___redArg(v___y_1598_, v___y_1600_, v___y_1601_);
if (lean_obj_tag(v___x_1603_) == 0)
{
if (lean_obj_tag(v_occs_1593_) == 0)
{
lean_object* v_a_1604_; 
lean_dec_ref_known(v_occs_1593_, 1);
v_a_1604_ = lean_ctor_get(v___x_1603_, 0);
lean_inc(v_a_1604_);
lean_dec_ref_known(v___x_1603_, 1);
v___y_1480_ = v___y_1597_;
v___y_1481_ = v___y_1588_;
v___y_1482_ = v___y_1589_;
v___y_1483_ = v___x_1602_;
v___y_1484_ = v_a_1604_;
v___y_1485_ = v___y_1601_;
v___y_1486_ = v___y_1594_;
v___y_1487_ = v___y_1595_;
v___y_1488_ = v___y_1590_;
v___y_1489_ = v___y_1599_;
v___y_1490_ = v___y_1591_;
v___y_1491_ = v___y_1592_;
v___y_1492_ = v___y_1598_;
v___y_1493_ = v___y_1596_;
v___y_1494_ = v___y_1600_;
v___y_1495_ = v___x_1355_;
goto v___jp_1479_;
}
else
{
lean_object* v_a_1605_; uint8_t v___x_1606_; 
lean_dec_ref(v_occs_1593_);
v_a_1605_ = lean_ctor_get(v___x_1603_, 0);
lean_inc(v_a_1605_);
lean_dec_ref_known(v___x_1603_, 1);
v___x_1606_ = 0;
v___y_1480_ = v___y_1597_;
v___y_1481_ = v___y_1588_;
v___y_1482_ = v___y_1589_;
v___y_1483_ = v___x_1602_;
v___y_1484_ = v_a_1605_;
v___y_1485_ = v___y_1601_;
v___y_1486_ = v___y_1594_;
v___y_1487_ = v___y_1595_;
v___y_1488_ = v___y_1590_;
v___y_1489_ = v___y_1599_;
v___y_1490_ = v___y_1591_;
v___y_1491_ = v___y_1592_;
v___y_1492_ = v___y_1598_;
v___y_1493_ = v___y_1596_;
v___y_1494_ = v___y_1600_;
v___y_1495_ = v___x_1606_;
goto v___jp_1479_;
}
}
else
{
lean_object* v_a_1607_; lean_object* v___x_1609_; uint8_t v_isShared_1610_; uint8_t v_isSharedCheck_1614_; 
lean_dec(v___x_1602_);
lean_dec_ref(v_occs_1593_);
lean_dec_ref(v___y_1591_);
lean_dec_ref(v___y_1589_);
lean_dec_ref(v___y_1588_);
lean_dec_ref(v___f_1354_);
v_a_1607_ = lean_ctor_get(v___x_1603_, 0);
v_isSharedCheck_1614_ = !lean_is_exclusive(v___x_1603_);
if (v_isSharedCheck_1614_ == 0)
{
v___x_1609_ = v___x_1603_;
v_isShared_1610_ = v_isSharedCheck_1614_;
goto v_resetjp_1608_;
}
else
{
lean_inc(v_a_1607_);
lean_dec(v___x_1603_);
v___x_1609_ = lean_box(0);
v_isShared_1610_ = v_isSharedCheck_1614_;
goto v_resetjp_1608_;
}
v_resetjp_1608_:
{
lean_object* v___x_1612_; 
if (v_isShared_1610_ == 0)
{
v___x_1612_ = v___x_1609_;
goto v_reusejp_1611_;
}
else
{
lean_object* v_reuseFailAlloc_1613_; 
v_reuseFailAlloc_1613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1613_, 0, v_a_1607_);
v___x_1612_ = v_reuseFailAlloc_1613_;
goto v_reusejp_1611_;
}
v_reusejp_1611_:
{
return v___x_1612_;
}
}
}
}
v___jp_1615_:
{
lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; 
v___x_1630_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__15));
v___x_1631_ = lean_array_to_list(v___y_1616_);
v___x_1632_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1632_, 0, v___x_1630_);
lean_ctor_set(v___x_1632_, 1, v___x_1462_);
lean_ctor_set(v___x_1632_, 2, v___x_1631_);
v___y_1588_ = v___y_1617_;
v___y_1589_ = v___y_1618_;
v___y_1590_ = v___y_1619_;
v___y_1591_ = v___y_1620_;
v___y_1592_ = v___y_1621_;
v_occs_1593_ = v___x_1632_;
v___y_1594_ = v___y_1622_;
v___y_1595_ = v___y_1623_;
v___y_1596_ = v___y_1624_;
v___y_1597_ = v___y_1625_;
v___y_1598_ = v___y_1626_;
v___y_1599_ = v___y_1627_;
v___y_1600_ = v___y_1628_;
v___y_1601_ = v___y_1629_;
goto v___jp_1587_;
}
v___jp_1633_:
{
uint8_t v___x_1648_; 
v___x_1648_ = l_Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8(v___y_1647_);
if (v___x_1648_ == 0)
{
lean_object* v___x_1649_; lean_object* v___x_1650_; 
lean_dec_ref(v___y_1647_);
lean_dec_ref(v___y_1645_);
lean_dec_ref(v___y_1636_);
lean_dec_ref(v___y_1635_);
lean_dec_ref(v___f_1354_);
v___x_1649_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__17, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__17_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__17);
v___x_1650_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg(v___x_1649_, v___y_1637_, v___y_1644_, v___y_1641_, v___y_1639_);
return v___x_1650_;
}
else
{
v___y_1616_ = v___y_1647_;
v___y_1617_ = v___y_1635_;
v___y_1618_ = v___y_1636_;
v___y_1619_ = v___y_1642_;
v___y_1620_ = v___y_1645_;
v___y_1621_ = v___y_1646_;
v___y_1622_ = v___y_1640_;
v___y_1623_ = v___y_1638_;
v___y_1624_ = v___y_1643_;
v___y_1625_ = v___y_1634_;
v___y_1626_ = v___y_1637_;
v___y_1627_ = v___y_1644_;
v___y_1628_ = v___y_1641_;
v___y_1629_ = v___y_1639_;
goto v___jp_1615_;
}
}
v___jp_1651_:
{
lean_object* v___x_1669_; 
v___x_1669_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg(v___y_1663_, v___y_1658_, v___y_1664_, v___y_1668_);
lean_dec(v___y_1668_);
lean_dec(v___y_1663_);
v___y_1634_ = v___y_1652_;
v___y_1635_ = v___y_1653_;
v___y_1636_ = v___y_1654_;
v___y_1637_ = v___y_1655_;
v___y_1638_ = v___y_1656_;
v___y_1639_ = v___y_1657_;
v___y_1640_ = v___y_1659_;
v___y_1641_ = v___y_1660_;
v___y_1642_ = v___y_1665_;
v___y_1643_ = v___y_1662_;
v___y_1644_ = v___y_1661_;
v___y_1645_ = v___y_1666_;
v___y_1646_ = v___y_1667_;
v___y_1647_ = v___x_1669_;
goto v___jp_1633_;
}
v___jp_1670_:
{
uint8_t v___x_1688_; 
v___x_1688_ = lean_nat_dec_le(v___y_1687_, v___y_1671_);
if (v___x_1688_ == 0)
{
lean_dec(v___y_1671_);
lean_inc(v___y_1687_);
v___y_1652_ = v___y_1672_;
v___y_1653_ = v___y_1673_;
v___y_1654_ = v___y_1674_;
v___y_1655_ = v___y_1675_;
v___y_1656_ = v___y_1676_;
v___y_1657_ = v___y_1677_;
v___y_1658_ = v___y_1678_;
v___y_1659_ = v___y_1679_;
v___y_1660_ = v___y_1680_;
v___y_1661_ = v___y_1682_;
v___y_1662_ = v___y_1683_;
v___y_1663_ = v___y_1684_;
v___y_1664_ = v___y_1687_;
v___y_1665_ = v___y_1681_;
v___y_1666_ = v___y_1685_;
v___y_1667_ = v___y_1686_;
v___y_1668_ = v___y_1687_;
goto v___jp_1651_;
}
else
{
v___y_1652_ = v___y_1672_;
v___y_1653_ = v___y_1673_;
v___y_1654_ = v___y_1674_;
v___y_1655_ = v___y_1675_;
v___y_1656_ = v___y_1676_;
v___y_1657_ = v___y_1677_;
v___y_1658_ = v___y_1678_;
v___y_1659_ = v___y_1679_;
v___y_1660_ = v___y_1680_;
v___y_1661_ = v___y_1682_;
v___y_1662_ = v___y_1683_;
v___y_1663_ = v___y_1684_;
v___y_1664_ = v___y_1687_;
v___y_1665_ = v___y_1681_;
v___y_1666_ = v___y_1685_;
v___y_1667_ = v___y_1686_;
v___y_1668_ = v___y_1671_;
goto v___jp_1651_;
}
}
v___jp_1689_:
{
lean_object* v_declName_x3f_1699_; lean_object* v_macroStack_1700_; uint8_t v_mayPostpone_1701_; uint8_t v_errToSorry_1702_; lean_object* v_autoBoundImplicitContext_1703_; lean_object* v_autoBoundImplicitForbidden_1704_; lean_object* v_sectionVars_1705_; lean_object* v_sectionFVars_1706_; uint8_t v_implicitLambda_1707_; uint8_t v_heedElabAsElim_1708_; uint8_t v_isNoncomputableSection_1709_; uint8_t v_isMetaSection_1710_; uint8_t v_inPattern_1711_; lean_object* v_tacSnap_x3f_1712_; uint8_t v_saveRecAppSyntax_1713_; uint8_t v_holesAsSyntheticOpaque_1714_; lean_object* v_fixedTermElabs_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___f_1720_; lean_object* v___f_1721_; lean_object* v___f_1722_; lean_object* v___x_1723_; lean_object* v___f_1724_; lean_object* v___f_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; 
v_declName_x3f_1699_ = lean_ctor_get(v___y_1693_, 0);
v_macroStack_1700_ = lean_ctor_get(v___y_1693_, 1);
v_mayPostpone_1701_ = lean_ctor_get_uint8(v___y_1693_, sizeof(void*)*8);
v_errToSorry_1702_ = lean_ctor_get_uint8(v___y_1693_, sizeof(void*)*8 + 1);
v_autoBoundImplicitContext_1703_ = lean_ctor_get(v___y_1693_, 2);
v_autoBoundImplicitForbidden_1704_ = lean_ctor_get(v___y_1693_, 3);
v_sectionVars_1705_ = lean_ctor_get(v___y_1693_, 4);
v_sectionFVars_1706_ = lean_ctor_get(v___y_1693_, 5);
v_implicitLambda_1707_ = lean_ctor_get_uint8(v___y_1693_, sizeof(void*)*8 + 2);
v_heedElabAsElim_1708_ = lean_ctor_get_uint8(v___y_1693_, sizeof(void*)*8 + 3);
v_isNoncomputableSection_1709_ = lean_ctor_get_uint8(v___y_1693_, sizeof(void*)*8 + 4);
v_isMetaSection_1710_ = lean_ctor_get_uint8(v___y_1693_, sizeof(void*)*8 + 5);
v_inPattern_1711_ = lean_ctor_get_uint8(v___y_1693_, sizeof(void*)*8 + 7);
v_tacSnap_x3f_1712_ = lean_ctor_get(v___y_1693_, 6);
v_saveRecAppSyntax_1713_ = lean_ctor_get_uint8(v___y_1693_, sizeof(void*)*8 + 8);
v_holesAsSyntheticOpaque_1714_ = lean_ctor_get_uint8(v___y_1693_, sizeof(void*)*8 + 9);
v_fixedTermElabs_1715_ = lean_ctor_get(v___y_1693_, 7);
v___x_1716_ = lean_unsigned_to_nat(2u);
v___x_1717_ = l_Lean_Syntax_getArg(v_stx_1356_, v___x_1716_);
v___x_1718_ = lean_box(0);
v___x_1719_ = lean_box(v___x_1355_);
v___f_1720_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__1___boxed), 11, 2);
lean_closure_set(v___f_1720_, 0, v___x_1718_);
lean_closure_set(v___f_1720_, 1, v___x_1719_);
v___f_1721_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__18));
v___f_1722_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__19));
v___x_1723_ = lean_box(v___x_1355_);
lean_inc(v___x_1717_);
v___f_1724_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__4___boxed), 10, 3);
lean_closure_set(v___f_1724_, 0, v___x_1717_);
lean_closure_set(v___f_1724_, 1, v___x_1718_);
lean_closure_set(v___f_1724_, 2, v___x_1723_);
v___f_1725_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__5___boxed), 9, 2);
lean_closure_set(v___f_1725_, 0, v___x_1717_);
lean_closure_set(v___f_1725_, 1, v___f_1724_);
lean_inc_ref(v_fixedTermElabs_1715_);
lean_inc(v_tacSnap_x3f_1712_);
lean_inc(v_sectionFVars_1706_);
lean_inc(v_sectionVars_1705_);
lean_inc_ref(v_autoBoundImplicitForbidden_1704_);
lean_inc(v_autoBoundImplicitContext_1703_);
lean_inc(v_macroStack_1700_);
lean_inc(v_declName_x3f_1699_);
v___x_1726_ = lean_alloc_ctor(0, 8, 10);
lean_ctor_set(v___x_1726_, 0, v_declName_x3f_1699_);
lean_ctor_set(v___x_1726_, 1, v_macroStack_1700_);
lean_ctor_set(v___x_1726_, 2, v_autoBoundImplicitContext_1703_);
lean_ctor_set(v___x_1726_, 3, v_autoBoundImplicitForbidden_1704_);
lean_ctor_set(v___x_1726_, 4, v_sectionVars_1705_);
lean_ctor_set(v___x_1726_, 5, v_sectionFVars_1706_);
lean_ctor_set(v___x_1726_, 6, v_tacSnap_x3f_1712_);
lean_ctor_set(v___x_1726_, 7, v_fixedTermElabs_1715_);
lean_ctor_set_uint8(v___x_1726_, sizeof(void*)*8, v_mayPostpone_1701_);
lean_ctor_set_uint8(v___x_1726_, sizeof(void*)*8 + 1, v_errToSorry_1702_);
lean_ctor_set_uint8(v___x_1726_, sizeof(void*)*8 + 2, v_implicitLambda_1707_);
lean_ctor_set_uint8(v___x_1726_, sizeof(void*)*8 + 3, v_heedElabAsElim_1708_);
lean_ctor_set_uint8(v___x_1726_, sizeof(void*)*8 + 4, v_isNoncomputableSection_1709_);
lean_ctor_set_uint8(v___x_1726_, sizeof(void*)*8 + 5, v_isMetaSection_1710_);
lean_ctor_set_uint8(v___x_1726_, sizeof(void*)*8 + 6, v___x_1355_);
lean_ctor_set_uint8(v___x_1726_, sizeof(void*)*8 + 7, v_inPattern_1711_);
lean_ctor_set_uint8(v___x_1726_, sizeof(void*)*8 + 8, v_saveRecAppSyntax_1713_);
lean_ctor_set_uint8(v___x_1726_, sizeof(void*)*8 + 9, v_holesAsSyntheticOpaque_1714_);
v___x_1727_ = l_Lean_Elab_Term_withoutModifyingElabMetaStateWithInfo___redArg(v___f_1725_, v___x_1726_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_);
lean_dec_ref_known(v___x_1726_, 8);
if (lean_obj_tag(v___x_1727_) == 0)
{
lean_object* v_a_1728_; lean_object* v___x_1729_; 
v_a_1728_ = lean_ctor_get(v___x_1727_, 0);
lean_inc(v_a_1728_);
lean_dec_ref_known(v___x_1727_, 1);
v___x_1729_ = l_Lean_Elab_Tactic_Conv_getLhs___redArg(v___y_1692_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_);
if (lean_obj_tag(v___x_1729_) == 0)
{
if (lean_obj_tag(v_occs_1690_) == 0)
{
lean_object* v_a_1730_; lean_object* v___x_1731_; 
lean_dec_ref(v___x_1360_);
lean_dec_ref(v___x_1359_);
lean_dec_ref(v___x_1358_);
lean_dec_ref(v___x_1357_);
v_a_1730_ = lean_ctor_get(v___x_1729_, 0);
lean_inc(v_a_1730_);
lean_dec_ref_known(v___x_1729_, 1);
v___x_1731_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__22));
v___y_1588_ = v___f_1720_;
v___y_1589_ = v_a_1728_;
v___y_1590_ = v___f_1721_;
v___y_1591_ = v_a_1730_;
v___y_1592_ = v___f_1722_;
v_occs_1593_ = v___x_1731_;
v___y_1594_ = v___y_1691_;
v___y_1595_ = v___y_1692_;
v___y_1596_ = v___y_1693_;
v___y_1597_ = v___y_1694_;
v___y_1598_ = v___y_1695_;
v___y_1599_ = v___y_1696_;
v___y_1600_ = v___y_1697_;
v___y_1601_ = v___y_1698_;
goto v___jp_1587_;
}
else
{
lean_object* v_a_1732_; lean_object* v_val_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; uint8_t v___x_1736_; 
v_a_1732_ = lean_ctor_get(v___x_1729_, 0);
lean_inc(v_a_1732_);
lean_dec_ref_known(v___x_1729_, 1);
v_val_1733_ = lean_ctor_get(v_occs_1690_, 0);
lean_inc_n(v_val_1733_, 2);
lean_dec_ref_known(v_occs_1690_, 1);
v___x_1734_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__23));
lean_inc_ref(v___x_1360_);
lean_inc_ref(v___x_1359_);
lean_inc_ref(v___x_1358_);
lean_inc_ref(v___x_1357_);
v___x_1735_ = l_Lean_Name_mkStr5(v___x_1357_, v___x_1358_, v___x_1359_, v___x_1360_, v___x_1734_);
v___x_1736_ = l_Lean_Syntax_isOfKind(v_val_1733_, v___x_1735_);
lean_dec(v___x_1735_);
if (v___x_1736_ == 0)
{
lean_object* v___x_1737_; lean_object* v___x_1738_; uint8_t v___x_1739_; 
v___x_1737_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__24));
v___x_1738_ = l_Lean_Name_mkStr5(v___x_1357_, v___x_1358_, v___x_1359_, v___x_1360_, v___x_1737_);
lean_inc(v_val_1733_);
v___x_1739_ = l_Lean_Syntax_isOfKind(v_val_1733_, v___x_1738_);
lean_dec(v___x_1738_);
if (v___x_1739_ == 0)
{
lean_object* v___x_1740_; lean_object* v_a_1741_; lean_object* v___x_1743_; uint8_t v_isShared_1744_; uint8_t v_isSharedCheck_1748_; 
lean_dec(v_val_1733_);
lean_dec(v_a_1732_);
lean_dec(v_a_1728_);
lean_dec_ref(v___f_1720_);
lean_dec_ref(v___f_1354_);
v___x_1740_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1___redArg();
v_a_1741_ = lean_ctor_get(v___x_1740_, 0);
v_isSharedCheck_1748_ = !lean_is_exclusive(v___x_1740_);
if (v_isSharedCheck_1748_ == 0)
{
v___x_1743_ = v___x_1740_;
v_isShared_1744_ = v_isSharedCheck_1748_;
goto v_resetjp_1742_;
}
else
{
lean_inc(v_a_1741_);
lean_dec(v___x_1740_);
v___x_1743_ = lean_box(0);
v_isShared_1744_ = v_isSharedCheck_1748_;
goto v_resetjp_1742_;
}
v_resetjp_1742_:
{
lean_object* v___x_1746_; 
if (v_isShared_1744_ == 0)
{
v___x_1746_ = v___x_1743_;
goto v_reusejp_1745_;
}
else
{
lean_object* v_reuseFailAlloc_1747_; 
v_reuseFailAlloc_1747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1747_, 0, v_a_1741_);
v___x_1746_ = v_reuseFailAlloc_1747_;
goto v_reusejp_1745_;
}
v_reusejp_1745_:
{
return v___x_1746_;
}
}
}
else
{
lean_object* v___x_1749_; lean_object* v___x_1750_; size_t v_sz_1751_; size_t v___x_1752_; lean_object* v___x_1753_; 
v___x_1749_ = l_Lean_Syntax_getArg(v_val_1733_, v___x_1462_);
lean_dec(v_val_1733_);
v___x_1750_ = l_Lean_Syntax_getArgs(v___x_1749_);
lean_dec(v___x_1749_);
v_sz_1751_ = lean_array_size(v___x_1750_);
v___x_1752_ = ((size_t)0ULL);
v___x_1753_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg(v_sz_1751_, v___x_1752_, v___x_1750_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_);
if (lean_obj_tag(v___x_1753_) == 0)
{
lean_object* v_a_1754_; lean_object* v___x_1755_; uint8_t v___x_1756_; 
v_a_1754_ = lean_ctor_get(v___x_1753_, 0);
lean_inc(v_a_1754_);
lean_dec_ref_known(v___x_1753_, 1);
v___x_1755_ = lean_array_get_size(v_a_1754_);
v___x_1756_ = lean_nat_dec_eq(v___x_1755_, v___x_1462_);
if (v___x_1756_ == 0)
{
lean_object* v___x_1757_; uint8_t v___x_1758_; 
v___x_1757_ = lean_nat_sub(v___x_1755_, v___x_1463_);
v___x_1758_ = lean_nat_dec_le(v___x_1462_, v___x_1757_);
if (v___x_1758_ == 0)
{
lean_inc(v___x_1757_);
v___y_1671_ = v___x_1757_;
v___y_1672_ = v___y_1694_;
v___y_1673_ = v___f_1720_;
v___y_1674_ = v_a_1728_;
v___y_1675_ = v___y_1695_;
v___y_1676_ = v___y_1692_;
v___y_1677_ = v___y_1698_;
v___y_1678_ = v_a_1754_;
v___y_1679_ = v___y_1691_;
v___y_1680_ = v___y_1697_;
v___y_1681_ = v___f_1721_;
v___y_1682_ = v___y_1696_;
v___y_1683_ = v___y_1693_;
v___y_1684_ = v___x_1755_;
v___y_1685_ = v_a_1732_;
v___y_1686_ = v___f_1722_;
v___y_1687_ = v___x_1757_;
goto v___jp_1670_;
}
else
{
v___y_1671_ = v___x_1757_;
v___y_1672_ = v___y_1694_;
v___y_1673_ = v___f_1720_;
v___y_1674_ = v_a_1728_;
v___y_1675_ = v___y_1695_;
v___y_1676_ = v___y_1692_;
v___y_1677_ = v___y_1698_;
v___y_1678_ = v_a_1754_;
v___y_1679_ = v___y_1691_;
v___y_1680_ = v___y_1697_;
v___y_1681_ = v___f_1721_;
v___y_1682_ = v___y_1696_;
v___y_1683_ = v___y_1693_;
v___y_1684_ = v___x_1755_;
v___y_1685_ = v_a_1732_;
v___y_1686_ = v___f_1722_;
v___y_1687_ = v___x_1462_;
goto v___jp_1670_;
}
}
else
{
v___y_1634_ = v___y_1694_;
v___y_1635_ = v___f_1720_;
v___y_1636_ = v_a_1728_;
v___y_1637_ = v___y_1695_;
v___y_1638_ = v___y_1692_;
v___y_1639_ = v___y_1698_;
v___y_1640_ = v___y_1691_;
v___y_1641_ = v___y_1697_;
v___y_1642_ = v___f_1721_;
v___y_1643_ = v___y_1693_;
v___y_1644_ = v___y_1696_;
v___y_1645_ = v_a_1732_;
v___y_1646_ = v___f_1722_;
v___y_1647_ = v_a_1754_;
goto v___jp_1633_;
}
}
else
{
lean_object* v_a_1759_; lean_object* v___x_1761_; uint8_t v_isShared_1762_; uint8_t v_isSharedCheck_1766_; 
lean_dec(v_a_1732_);
lean_dec(v_a_1728_);
lean_dec_ref(v___f_1720_);
lean_dec_ref(v___f_1354_);
v_a_1759_ = lean_ctor_get(v___x_1753_, 0);
v_isSharedCheck_1766_ = !lean_is_exclusive(v___x_1753_);
if (v_isSharedCheck_1766_ == 0)
{
v___x_1761_ = v___x_1753_;
v_isShared_1762_ = v_isSharedCheck_1766_;
goto v_resetjp_1760_;
}
else
{
lean_inc(v_a_1759_);
lean_dec(v___x_1753_);
v___x_1761_ = lean_box(0);
v_isShared_1762_ = v_isSharedCheck_1766_;
goto v_resetjp_1760_;
}
v_resetjp_1760_:
{
lean_object* v___x_1764_; 
if (v_isShared_1762_ == 0)
{
v___x_1764_ = v___x_1761_;
goto v_reusejp_1763_;
}
else
{
lean_object* v_reuseFailAlloc_1765_; 
v_reuseFailAlloc_1765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1765_, 0, v_a_1759_);
v___x_1764_ = v_reuseFailAlloc_1765_;
goto v_reusejp_1763_;
}
v_reusejp_1763_:
{
return v___x_1764_;
}
}
}
}
}
else
{
lean_object* v___x_1767_; 
lean_dec(v_val_1733_);
lean_dec_ref(v___x_1360_);
lean_dec_ref(v___x_1359_);
lean_dec_ref(v___x_1358_);
lean_dec_ref(v___x_1357_);
v___x_1767_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__26));
v___y_1588_ = v___f_1720_;
v___y_1589_ = v_a_1728_;
v___y_1590_ = v___f_1721_;
v___y_1591_ = v_a_1732_;
v___y_1592_ = v___f_1722_;
v_occs_1593_ = v___x_1767_;
v___y_1594_ = v___y_1691_;
v___y_1595_ = v___y_1692_;
v___y_1596_ = v___y_1693_;
v___y_1597_ = v___y_1694_;
v___y_1598_ = v___y_1695_;
v___y_1599_ = v___y_1696_;
v___y_1600_ = v___y_1697_;
v___y_1601_ = v___y_1698_;
goto v___jp_1587_;
}
}
}
else
{
lean_object* v_a_1768_; lean_object* v___x_1770_; uint8_t v_isShared_1771_; uint8_t v_isSharedCheck_1775_; 
lean_dec(v_a_1728_);
lean_dec_ref(v___f_1720_);
lean_dec(v_occs_1690_);
lean_dec_ref(v___x_1360_);
lean_dec_ref(v___x_1359_);
lean_dec_ref(v___x_1358_);
lean_dec_ref(v___x_1357_);
lean_dec_ref(v___f_1354_);
v_a_1768_ = lean_ctor_get(v___x_1729_, 0);
v_isSharedCheck_1775_ = !lean_is_exclusive(v___x_1729_);
if (v_isSharedCheck_1775_ == 0)
{
v___x_1770_ = v___x_1729_;
v_isShared_1771_ = v_isSharedCheck_1775_;
goto v_resetjp_1769_;
}
else
{
lean_inc(v_a_1768_);
lean_dec(v___x_1729_);
v___x_1770_ = lean_box(0);
v_isShared_1771_ = v_isSharedCheck_1775_;
goto v_resetjp_1769_;
}
v_resetjp_1769_:
{
lean_object* v___x_1773_; 
if (v_isShared_1771_ == 0)
{
v___x_1773_ = v___x_1770_;
goto v_reusejp_1772_;
}
else
{
lean_object* v_reuseFailAlloc_1774_; 
v_reuseFailAlloc_1774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1774_, 0, v_a_1768_);
v___x_1773_ = v_reuseFailAlloc_1774_;
goto v_reusejp_1772_;
}
v_reusejp_1772_:
{
return v___x_1773_;
}
}
}
}
else
{
lean_object* v_a_1776_; lean_object* v___x_1778_; uint8_t v_isShared_1779_; uint8_t v_isSharedCheck_1783_; 
lean_dec_ref(v___f_1720_);
lean_dec(v_occs_1690_);
lean_dec_ref(v___x_1360_);
lean_dec_ref(v___x_1359_);
lean_dec_ref(v___x_1358_);
lean_dec_ref(v___x_1357_);
lean_dec_ref(v___f_1354_);
v_a_1776_ = lean_ctor_get(v___x_1727_, 0);
v_isSharedCheck_1783_ = !lean_is_exclusive(v___x_1727_);
if (v_isSharedCheck_1783_ == 0)
{
v___x_1778_ = v___x_1727_;
v_isShared_1779_ = v_isSharedCheck_1783_;
goto v_resetjp_1777_;
}
else
{
lean_inc(v_a_1776_);
lean_dec(v___x_1727_);
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
}
}
v___jp_1370_:
{
lean_object* v___x_1381_; 
v___x_1381_ = l_Lean_Elab_Tactic_Conv_getRhs___redArg(v___y_1374_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_);
if (lean_obj_tag(v___x_1381_) == 0)
{
lean_object* v_a_1382_; lean_object* v_expr_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; 
v_a_1382_ = lean_ctor_get(v___x_1381_, 0);
lean_inc(v_a_1382_);
lean_dec_ref_known(v___x_1381_, 1);
v_expr_1383_ = lean_ctor_get(v___y_1371_, 0);
v___x_1384_ = l_Lean_Expr_mvarId_x21(v_a_1382_);
lean_dec(v_a_1382_);
lean_inc_ref(v_expr_1383_);
v___x_1385_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3___redArg(v___x_1384_, v_expr_1383_, v___y_1378_);
lean_dec_ref(v___x_1385_);
v___x_1386_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_1374_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_);
if (lean_obj_tag(v___x_1386_) == 0)
{
lean_object* v_a_1387_; lean_object* v___x_1388_; 
v_a_1387_ = lean_ctor_get(v___x_1386_, 0);
lean_inc(v_a_1387_);
lean_dec_ref_known(v___x_1386_, 1);
v___x_1388_ = l_Lean_Meta_Simp_Result_getProof(v___y_1371_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_);
if (lean_obj_tag(v___x_1388_) == 0)
{
lean_object* v_a_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; 
v_a_1389_ = lean_ctor_get(v___x_1388_, 0);
lean_inc(v_a_1389_);
lean_dec_ref_known(v___x_1388_, 1);
v___x_1390_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3___redArg(v_a_1387_, v_a_1389_, v___y_1378_);
lean_dec_ref(v___x_1390_);
v___x_1391_ = lean_array_to_list(v_subgoals_1372_);
v___x_1392_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_1391_, v___y_1374_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_);
return v___x_1392_;
}
else
{
lean_object* v_a_1393_; lean_object* v___x_1395_; uint8_t v_isShared_1396_; uint8_t v_isSharedCheck_1400_; 
lean_dec(v_a_1387_);
lean_dec_ref(v_subgoals_1372_);
v_a_1393_ = lean_ctor_get(v___x_1388_, 0);
v_isSharedCheck_1400_ = !lean_is_exclusive(v___x_1388_);
if (v_isSharedCheck_1400_ == 0)
{
v___x_1395_ = v___x_1388_;
v_isShared_1396_ = v_isSharedCheck_1400_;
goto v_resetjp_1394_;
}
else
{
lean_inc(v_a_1393_);
lean_dec(v___x_1388_);
v___x_1395_ = lean_box(0);
v_isShared_1396_ = v_isSharedCheck_1400_;
goto v_resetjp_1394_;
}
v_resetjp_1394_:
{
lean_object* v___x_1398_; 
if (v_isShared_1396_ == 0)
{
v___x_1398_ = v___x_1395_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v_a_1393_);
v___x_1398_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
return v___x_1398_;
}
}
}
}
else
{
lean_object* v_a_1401_; lean_object* v___x_1403_; uint8_t v_isShared_1404_; uint8_t v_isSharedCheck_1408_; 
lean_dec_ref(v_subgoals_1372_);
lean_dec_ref(v___y_1371_);
v_a_1401_ = lean_ctor_get(v___x_1386_, 0);
v_isSharedCheck_1408_ = !lean_is_exclusive(v___x_1386_);
if (v_isSharedCheck_1408_ == 0)
{
v___x_1403_ = v___x_1386_;
v_isShared_1404_ = v_isSharedCheck_1408_;
goto v_resetjp_1402_;
}
else
{
lean_inc(v_a_1401_);
lean_dec(v___x_1386_);
v___x_1403_ = lean_box(0);
v_isShared_1404_ = v_isSharedCheck_1408_;
goto v_resetjp_1402_;
}
v_resetjp_1402_:
{
lean_object* v___x_1406_; 
if (v_isShared_1404_ == 0)
{
v___x_1406_ = v___x_1403_;
goto v_reusejp_1405_;
}
else
{
lean_object* v_reuseFailAlloc_1407_; 
v_reuseFailAlloc_1407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1407_, 0, v_a_1401_);
v___x_1406_ = v_reuseFailAlloc_1407_;
goto v_reusejp_1405_;
}
v_reusejp_1405_:
{
return v___x_1406_;
}
}
}
}
else
{
lean_object* v_a_1409_; lean_object* v___x_1411_; uint8_t v_isShared_1412_; uint8_t v_isSharedCheck_1416_; 
lean_dec_ref(v_subgoals_1372_);
lean_dec_ref(v___y_1371_);
v_a_1409_ = lean_ctor_get(v___x_1381_, 0);
v_isSharedCheck_1416_ = !lean_is_exclusive(v___x_1381_);
if (v_isSharedCheck_1416_ == 0)
{
v___x_1411_ = v___x_1381_;
v_isShared_1412_ = v_isSharedCheck_1416_;
goto v_resetjp_1410_;
}
else
{
lean_inc(v_a_1409_);
lean_dec(v___x_1381_);
v___x_1411_ = lean_box(0);
v_isShared_1412_ = v_isSharedCheck_1416_;
goto v_resetjp_1410_;
}
v_resetjp_1410_:
{
lean_object* v___x_1414_; 
if (v_isShared_1412_ == 0)
{
v___x_1414_ = v___x_1411_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v_a_1409_);
v___x_1414_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
return v___x_1414_;
}
}
}
}
v___jp_1417_:
{
size_t v_sz_1428_; size_t v___x_1429_; lean_object* v___x_1430_; 
v_sz_1428_ = lean_array_size(v___y_1427_);
v___x_1429_ = ((size_t)0ULL);
v___x_1430_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__5(v_sz_1428_, v___x_1429_, v___y_1427_);
v___y_1371_ = v___y_1419_;
v_subgoals_1372_ = v___x_1430_;
v___y_1373_ = v___y_1423_;
v___y_1374_ = v___y_1422_;
v___y_1375_ = v___y_1425_;
v___y_1376_ = v___y_1418_;
v___y_1377_ = v___y_1420_;
v___y_1378_ = v___y_1426_;
v___y_1379_ = v___y_1421_;
v___y_1380_ = v___y_1424_;
goto v___jp_1370_;
}
v___jp_1431_:
{
lean_object* v___x_1445_; 
v___x_1445_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg(v___y_1442_, v___y_1433_, v___y_1436_, v___y_1444_);
lean_dec(v___y_1444_);
lean_dec(v___y_1442_);
v___y_1418_ = v___y_1441_;
v___y_1419_ = v___y_1443_;
v___y_1420_ = v___y_1432_;
v___y_1421_ = v___y_1434_;
v___y_1422_ = v___y_1435_;
v___y_1423_ = v___y_1437_;
v___y_1424_ = v___y_1438_;
v___y_1425_ = v___y_1439_;
v___y_1426_ = v___y_1440_;
v___y_1427_ = v___x_1445_;
goto v___jp_1417_;
}
v___jp_1446_:
{
uint8_t v___x_1460_; 
v___x_1460_ = lean_nat_dec_le(v___y_1459_, v___y_1458_);
if (v___x_1460_ == 0)
{
lean_dec(v___y_1458_);
lean_inc(v___y_1459_);
v___y_1432_ = v___y_1447_;
v___y_1433_ = v___y_1448_;
v___y_1434_ = v___y_1449_;
v___y_1435_ = v___y_1450_;
v___y_1436_ = v___y_1459_;
v___y_1437_ = v___y_1451_;
v___y_1438_ = v___y_1452_;
v___y_1439_ = v___y_1453_;
v___y_1440_ = v___y_1454_;
v___y_1441_ = v___y_1455_;
v___y_1442_ = v___y_1456_;
v___y_1443_ = v___y_1457_;
v___y_1444_ = v___y_1459_;
goto v___jp_1431_;
}
else
{
v___y_1432_ = v___y_1447_;
v___y_1433_ = v___y_1448_;
v___y_1434_ = v___y_1449_;
v___y_1435_ = v___y_1450_;
v___y_1436_ = v___y_1459_;
v___y_1437_ = v___y_1451_;
v___y_1438_ = v___y_1452_;
v___y_1439_ = v___y_1453_;
v___y_1440_ = v___y_1454_;
v___y_1441_ = v___y_1455_;
v___y_1442_ = v___y_1456_;
v___y_1443_ = v___y_1457_;
v___y_1444_ = v___y_1458_;
goto v___jp_1431_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___boxed(lean_object** _args){
lean_object* v___x_1797_ = _args[0];
lean_object* v___f_1798_ = _args[1];
lean_object* v___x_1799_ = _args[2];
lean_object* v_stx_1800_ = _args[3];
lean_object* v___x_1801_ = _args[4];
lean_object* v___x_1802_ = _args[5];
lean_object* v___x_1803_ = _args[6];
lean_object* v___x_1804_ = _args[7];
lean_object* v___y_1805_ = _args[8];
lean_object* v___y_1806_ = _args[9];
lean_object* v___y_1807_ = _args[10];
lean_object* v___y_1808_ = _args[11];
lean_object* v___y_1809_ = _args[12];
lean_object* v___y_1810_ = _args[13];
lean_object* v___y_1811_ = _args[14];
lean_object* v___y_1812_ = _args[15];
lean_object* v___y_1813_ = _args[16];
_start:
{
uint8_t v___x_16315__boxed_1814_; uint8_t v___x_16317__boxed_1815_; lean_object* v_res_1816_; 
v___x_16315__boxed_1814_ = lean_unbox(v___x_1797_);
v___x_16317__boxed_1815_ = lean_unbox(v___x_1799_);
v_res_1816_ = l_Lean_Elab_Tactic_Conv_evalPattern___lam__6(v___x_16315__boxed_1814_, v___f_1798_, v___x_16317__boxed_1815_, v_stx_1800_, v___x_1801_, v___x_1802_, v___x_1803_, v___x_1804_, v___y_1805_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_, v___y_1812_);
lean_dec(v___y_1812_);
lean_dec_ref(v___y_1811_);
lean_dec(v___y_1810_);
lean_dec_ref(v___y_1809_);
lean_dec(v___y_1808_);
lean_dec_ref(v___y_1807_);
lean_dec(v___y_1806_);
lean_dec_ref(v___y_1805_);
lean_dec(v_stx_1800_);
return v_res_1816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern(lean_object* v_stx_1829_, lean_object* v_a_1830_, lean_object* v_a_1831_, lean_object* v_a_1832_, lean_object* v_a_1833_, lean_object* v_a_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_){
_start:
{
lean_object* v___f_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; uint8_t v___x_1845_; uint8_t v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___y_1849_; lean_object* v___x_1850_; 
v___f_1839_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___closed__0));
v___x_1840_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___closed__1));
v___x_1841_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___closed__2));
v___x_1842_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___closed__3));
v___x_1843_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___closed__4));
v___x_1844_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___closed__6));
lean_inc(v_stx_1829_);
v___x_1845_ = l_Lean_Syntax_isOfKind(v_stx_1829_, v___x_1844_);
v___x_1846_ = 1;
v___x_1847_ = lean_box(v___x_1845_);
v___x_1848_ = lean_box(v___x_1846_);
v___y_1849_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___boxed), 17, 8);
lean_closure_set(v___y_1849_, 0, v___x_1847_);
lean_closure_set(v___y_1849_, 1, v___f_1839_);
lean_closure_set(v___y_1849_, 2, v___x_1848_);
lean_closure_set(v___y_1849_, 3, v_stx_1829_);
lean_closure_set(v___y_1849_, 4, v___x_1840_);
lean_closure_set(v___y_1849_, 5, v___x_1841_);
lean_closure_set(v___y_1849_, 6, v___x_1842_);
lean_closure_set(v___y_1849_, 7, v___x_1843_);
v___x_1850_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___y_1849_, v_a_1830_, v_a_1831_, v_a_1832_, v_a_1833_, v_a_1834_, v_a_1835_, v_a_1836_, v_a_1837_);
return v___x_1850_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___boxed(lean_object* v_stx_1851_, lean_object* v_a_1852_, lean_object* v_a_1853_, lean_object* v_a_1854_, lean_object* v_a_1855_, lean_object* v_a_1856_, lean_object* v_a_1857_, lean_object* v_a_1858_, lean_object* v_a_1859_, lean_object* v_a_1860_){
_start:
{
lean_object* v_res_1861_; 
v_res_1861_ = l_Lean_Elab_Tactic_Conv_evalPattern(v_stx_1851_, v_a_1852_, v_a_1853_, v_a_1854_, v_a_1855_, v_a_1856_, v_a_1857_, v_a_1858_, v_a_1859_);
lean_dec(v_a_1859_);
lean_dec_ref(v_a_1858_);
lean_dec(v_a_1857_);
lean_dec_ref(v_a_1856_);
lean_dec(v_a_1855_);
lean_dec_ref(v_a_1854_);
lean_dec(v_a_1853_);
lean_dec_ref(v_a_1852_);
return v_res_1861_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0(lean_object* v_00_u03b1_1862_, lean_object* v_ref_1863_, lean_object* v_msg_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_){
_start:
{
lean_object* v___x_1874_; 
v___x_1874_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg(v_ref_1863_, v_msg_1864_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_, v___y_1872_);
return v___x_1874_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___boxed(lean_object* v_00_u03b1_1875_, lean_object* v_ref_1876_, lean_object* v_msg_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_){
_start:
{
lean_object* v_res_1887_; 
v_res_1887_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0(v_00_u03b1_1875_, v_ref_1876_, v_msg_1877_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_);
lean_dec(v___y_1885_);
lean_dec_ref(v___y_1884_);
lean_dec(v___y_1883_);
lean_dec_ref(v___y_1882_);
lean_dec(v___y_1881_);
lean_dec_ref(v___y_1880_);
lean_dec(v___y_1879_);
lean_dec_ref(v___y_1878_);
lean_dec(v_ref_1876_);
return v_res_1887_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3(lean_object* v_mvarId_1888_, lean_object* v_val_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_){
_start:
{
lean_object* v___x_1899_; 
v___x_1899_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3___redArg(v_mvarId_1888_, v_val_1889_, v___y_1895_);
return v___x_1899_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3___boxed(lean_object* v_mvarId_1900_, lean_object* v_val_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_){
_start:
{
lean_object* v_res_1911_; 
v_res_1911_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3(v_mvarId_1900_, v_val_1901_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_);
lean_dec(v___y_1909_);
lean_dec_ref(v___y_1908_);
lean_dec(v___y_1907_);
lean_dec_ref(v___y_1906_);
lean_dec(v___y_1905_);
lean_dec_ref(v___y_1904_);
lean_dec(v___y_1903_);
lean_dec_ref(v___y_1902_);
return v_res_1911_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4(lean_object* v_00_u03b1_1912_, lean_object* v_msg_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_){
_start:
{
lean_object* v___x_1923_; 
v___x_1923_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg(v_msg_1913_, v___y_1918_, v___y_1919_, v___y_1920_, v___y_1921_);
return v___x_1923_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___boxed(lean_object* v_00_u03b1_1924_, lean_object* v_msg_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_){
_start:
{
lean_object* v_res_1935_; 
v_res_1935_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4(v_00_u03b1_1924_, v_msg_1925_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_);
lean_dec(v___y_1933_);
lean_dec_ref(v___y_1932_);
lean_dec(v___y_1931_);
lean_dec_ref(v___y_1930_);
lean_dec(v___y_1929_);
lean_dec_ref(v___y_1928_);
lean_dec(v___y_1927_);
lean_dec_ref(v___y_1926_);
return v_res_1935_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6(lean_object* v_n_1936_, lean_object* v_as_1937_, lean_object* v_lo_1938_, lean_object* v_hi_1939_, lean_object* v_w_1940_, lean_object* v_hlo_1941_, lean_object* v_hhi_1942_){
_start:
{
lean_object* v___x_1943_; 
v___x_1943_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg(v_n_1936_, v_as_1937_, v_lo_1938_, v_hi_1939_);
return v___x_1943_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___boxed(lean_object* v_n_1944_, lean_object* v_as_1945_, lean_object* v_lo_1946_, lean_object* v_hi_1947_, lean_object* v_w_1948_, lean_object* v_hlo_1949_, lean_object* v_hhi_1950_){
_start:
{
lean_object* v_res_1951_; 
v_res_1951_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6(v_n_1944_, v_as_1945_, v_lo_1946_, v_hi_1947_, v_w_1948_, v_hlo_1949_, v_hhi_1950_);
lean_dec(v_hi_1947_);
lean_dec(v_n_1944_);
return v_res_1951_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7(lean_object* v_as_1952_, size_t v_sz_1953_, size_t v_i_1954_, lean_object* v_bs_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_){
_start:
{
lean_object* v___x_1965_; 
v___x_1965_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg(v_sz_1953_, v_i_1954_, v_bs_1955_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_);
return v___x_1965_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___boxed(lean_object* v_as_1966_, lean_object* v_sz_1967_, lean_object* v_i_1968_, lean_object* v_bs_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_){
_start:
{
size_t v_sz_boxed_1979_; size_t v_i_boxed_1980_; lean_object* v_res_1981_; 
v_sz_boxed_1979_ = lean_unbox_usize(v_sz_1967_);
lean_dec(v_sz_1967_);
v_i_boxed_1980_ = lean_unbox_usize(v_i_1968_);
lean_dec(v_i_1968_);
v_res_1981_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7(v_as_1966_, v_sz_boxed_1979_, v_i_boxed_1980_, v_bs_1969_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_);
lean_dec(v___y_1977_);
lean_dec_ref(v___y_1976_);
lean_dec(v___y_1975_);
lean_dec_ref(v___y_1974_);
lean_dec(v___y_1973_);
lean_dec_ref(v___y_1972_);
lean_dec(v___y_1971_);
lean_dec_ref(v___y_1970_);
lean_dec_ref(v_as_1966_);
return v_res_1981_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9(lean_object* v_n_1982_, lean_object* v_as_1983_, lean_object* v_lo_1984_, lean_object* v_hi_1985_, lean_object* v_w_1986_, lean_object* v_hlo_1987_, lean_object* v_hhi_1988_){
_start:
{
lean_object* v___x_1989_; 
v___x_1989_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg(v_n_1982_, v_as_1983_, v_lo_1984_, v_hi_1985_);
return v___x_1989_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___boxed(lean_object* v_n_1990_, lean_object* v_as_1991_, lean_object* v_lo_1992_, lean_object* v_hi_1993_, lean_object* v_w_1994_, lean_object* v_hlo_1995_, lean_object* v_hhi_1996_){
_start:
{
lean_object* v_res_1997_; 
v_res_1997_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9(v_n_1990_, v_as_1991_, v_lo_1992_, v_hi_1993_, v_w_1994_, v_hlo_1995_, v_hhi_1996_);
lean_dec(v_hi_1993_);
lean_dec(v_n_1990_);
return v_res_1997_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3(lean_object* v_00_u03b2_1998_, lean_object* v_x_1999_, lean_object* v_x_2000_, lean_object* v_x_2001_){
_start:
{
lean_object* v___x_2002_; 
v___x_2002_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3___redArg(v_x_1999_, v_x_2000_, v_x_2001_);
return v___x_2002_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6_spec__8(lean_object* v_n_2003_, lean_object* v_lo_2004_, lean_object* v_hi_2005_, lean_object* v_hhi_2006_, lean_object* v_pivot_2007_, lean_object* v_as_2008_, lean_object* v_i_2009_, lean_object* v_k_2010_, lean_object* v_ilo_2011_, lean_object* v_ik_2012_, lean_object* v_w_2013_){
_start:
{
lean_object* v___x_2014_; 
v___x_2014_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6_spec__8___redArg(v_hi_2005_, v_pivot_2007_, v_as_2008_, v_i_2009_, v_k_2010_);
return v___x_2014_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6_spec__8___boxed(lean_object* v_n_2015_, lean_object* v_lo_2016_, lean_object* v_hi_2017_, lean_object* v_hhi_2018_, lean_object* v_pivot_2019_, lean_object* v_as_2020_, lean_object* v_i_2021_, lean_object* v_k_2022_, lean_object* v_ilo_2023_, lean_object* v_ik_2024_, lean_object* v_w_2025_){
_start:
{
lean_object* v_res_2026_; 
v_res_2026_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6_spec__8(v_n_2015_, v_lo_2016_, v_hi_2017_, v_hhi_2018_, v_pivot_2019_, v_as_2020_, v_i_2021_, v_k_2022_, v_ilo_2023_, v_ik_2024_, v_w_2025_);
lean_dec_ref(v_pivot_2019_);
lean_dec(v_hi_2017_);
lean_dec(v_lo_2016_);
lean_dec(v_n_2015_);
return v_res_2026_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9_spec__13(lean_object* v_n_2027_, lean_object* v_lo_2028_, lean_object* v_hi_2029_, lean_object* v_hhi_2030_, lean_object* v_pivot_2031_, lean_object* v_as_2032_, lean_object* v_i_2033_, lean_object* v_k_2034_, lean_object* v_ilo_2035_, lean_object* v_ik_2036_, lean_object* v_w_2037_){
_start:
{
lean_object* v___x_2038_; 
v___x_2038_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9_spec__13___redArg(v_hi_2029_, v_pivot_2031_, v_as_2032_, v_i_2033_, v_k_2034_);
return v___x_2038_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9_spec__13___boxed(lean_object* v_n_2039_, lean_object* v_lo_2040_, lean_object* v_hi_2041_, lean_object* v_hhi_2042_, lean_object* v_pivot_2043_, lean_object* v_as_2044_, lean_object* v_i_2045_, lean_object* v_k_2046_, lean_object* v_ilo_2047_, lean_object* v_ik_2048_, lean_object* v_w_2049_){
_start:
{
lean_object* v_res_2050_; 
v_res_2050_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9_spec__13(v_n_2039_, v_lo_2040_, v_hi_2041_, v_hhi_2042_, v_pivot_2043_, v_as_2044_, v_i_2045_, v_k_2046_, v_ilo_2047_, v_ik_2048_, v_w_2049_);
lean_dec_ref(v_pivot_2043_);
lean_dec(v_hi_2041_);
lean_dec(v_lo_2040_);
lean_dec(v_n_2039_);
return v_res_2050_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4(lean_object* v_00_u03b2_2051_, lean_object* v_x_2052_, size_t v_x_2053_, size_t v_x_2054_, lean_object* v_x_2055_, lean_object* v_x_2056_){
_start:
{
lean_object* v___x_2057_; 
v___x_2057_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg(v_x_2052_, v_x_2053_, v_x_2054_, v_x_2055_, v_x_2056_);
return v___x_2057_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___boxed(lean_object* v_00_u03b2_2058_, lean_object* v_x_2059_, lean_object* v_x_2060_, lean_object* v_x_2061_, lean_object* v_x_2062_, lean_object* v_x_2063_){
_start:
{
size_t v_x_17433__boxed_2064_; size_t v_x_17434__boxed_2065_; lean_object* v_res_2066_; 
v_x_17433__boxed_2064_ = lean_unbox_usize(v_x_2060_);
lean_dec(v_x_2060_);
v_x_17434__boxed_2065_ = lean_unbox_usize(v_x_2061_);
lean_dec(v_x_2061_);
v_res_2066_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4(v_00_u03b2_2058_, v_x_2059_, v_x_17433__boxed_2064_, v_x_17434__boxed_2065_, v_x_2062_, v_x_2063_);
return v_res_2066_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11_spec__13(lean_object* v_as_2067_, lean_object* v_a_2068_, lean_object* v_x_2069_, lean_object* v_x_2070_){
_start:
{
uint8_t v___x_2071_; 
v___x_2071_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11_spec__13___redArg(v_as_2067_, v_a_2068_, v_x_2069_);
return v___x_2071_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11_spec__13___boxed(lean_object* v_as_2072_, lean_object* v_a_2073_, lean_object* v_x_2074_, lean_object* v_x_2075_){
_start:
{
uint8_t v_res_2076_; lean_object* v_r_2077_; 
v_res_2076_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11_spec__13(v_as_2072_, v_a_2073_, v_x_2074_, v_x_2075_);
lean_dec_ref(v_a_2073_);
lean_dec_ref(v_as_2072_);
v_r_2077_ = lean_box(v_res_2076_);
return v_r_2077_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__12(lean_object* v_00_u03b2_2078_, lean_object* v_n_2079_, lean_object* v_k_2080_, lean_object* v_v_2081_){
_start:
{
lean_object* v___x_2082_; 
v___x_2082_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__12___redArg(v_n_2079_, v_k_2080_, v_v_2081_);
return v___x_2082_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__13(lean_object* v_00_u03b2_2083_, size_t v_depth_2084_, lean_object* v_keys_2085_, lean_object* v_vals_2086_, lean_object* v_heq_2087_, lean_object* v_i_2088_, lean_object* v_entries_2089_){
_start:
{
lean_object* v___x_2090_; 
v___x_2090_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__13___redArg(v_depth_2084_, v_keys_2085_, v_vals_2086_, v_i_2088_, v_entries_2089_);
return v___x_2090_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__13___boxed(lean_object* v_00_u03b2_2091_, lean_object* v_depth_2092_, lean_object* v_keys_2093_, lean_object* v_vals_2094_, lean_object* v_heq_2095_, lean_object* v_i_2096_, lean_object* v_entries_2097_){
_start:
{
size_t v_depth_boxed_2098_; lean_object* v_res_2099_; 
v_depth_boxed_2098_ = lean_unbox_usize(v_depth_2092_);
lean_dec(v_depth_2092_);
v_res_2099_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__13(v_00_u03b2_2091_, v_depth_boxed_2098_, v_keys_2093_, v_vals_2094_, v_heq_2095_, v_i_2096_, v_entries_2097_);
lean_dec_ref(v_vals_2094_);
lean_dec_ref(v_keys_2093_);
return v_res_2099_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__12_spec__16(lean_object* v_00_u03b2_2100_, lean_object* v_x_2101_, lean_object* v_x_2102_, lean_object* v_x_2103_, lean_object* v_x_2104_){
_start:
{
lean_object* v___x_2105_; 
v___x_2105_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__12_spec__16___redArg(v_x_2101_, v_x_2102_, v_x_2103_, v_x_2104_);
return v___x_2105_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1(){
_start:
{
lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; 
v___x_2115_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2116_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___closed__6));
v___x_2117_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___closed__2));
v___x_2118_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalPattern___boxed), 10, 0);
v___x_2119_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2115_, v___x_2116_, v___x_2117_, v___x_2118_);
return v___x_2119_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___boxed(lean_object* v_a_2120_){
_start:
{
lean_object* v_res_2121_; 
v_res_2121_ = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1();
return v_res_2121_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3(){
_start:
{
lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; 
v___x_2148_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___closed__2));
v___x_2149_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__6));
v___x_2150_ = l_Lean_addBuiltinDeclarationRanges(v___x_2148_, v___x_2149_);
return v___x_2150_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___boxed(lean_object* v_a_2151_){
_start:
{
lean_object* v_res_2152_; 
v_res_2152_ = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3();
return v_res_2152_;
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
