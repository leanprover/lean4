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
uint8_t v___x_15366__boxed_642_; lean_object* v_res_643_; 
v___x_15366__boxed_642_ = lean_unbox(v___x_632_);
v_res_643_ = l_Lean_Elab_Tactic_Conv_evalPattern___lam__1(v___x_631_, v___x_15366__boxed_642_, v_e_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_);
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
uint8_t v___x_15469__boxed_720_; lean_object* v_res_721_; 
v___x_15469__boxed_720_ = lean_unbox(v___x_712_);
v_res_721_ = l_Lean_Elab_Tactic_Conv_evalPattern___lam__4(v___x_710_, v___x_711_, v___x_15469__boxed_720_, v___y_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_);
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
lean_object* v_toCold_731_; lean_object* v_currRecDepth_732_; lean_object* v_ref_733_; uint16_t v_optionFlags_734_; uint8_t v_suppressElabErrors_735_; uint8_t v_isRecordingDeps_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_745_; 
v_toCold_731_ = lean_ctor_get(v___y_728_, 0);
v_currRecDepth_732_ = lean_ctor_get(v___y_728_, 1);
v_ref_733_ = lean_ctor_get(v___y_728_, 2);
v_optionFlags_734_ = lean_ctor_get_uint16(v___y_728_, sizeof(void*)*3);
v_suppressElabErrors_735_ = lean_ctor_get_uint8(v___y_728_, sizeof(void*)*3 + 2);
v_isRecordingDeps_736_ = lean_ctor_get_uint8(v___y_728_, sizeof(void*)*3 + 3);
v_isSharedCheck_745_ = !lean_is_exclusive(v___y_728_);
if (v_isSharedCheck_745_ == 0)
{
v___x_738_ = v___y_728_;
v_isShared_739_ = v_isSharedCheck_745_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_ref_733_);
lean_inc(v_currRecDepth_732_);
lean_inc(v_toCold_731_);
lean_dec(v___y_728_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_745_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v_ref_740_; lean_object* v___x_742_; 
v_ref_740_ = l_Lean_replaceRef(v___x_722_, v_ref_733_);
lean_dec(v_ref_733_);
if (v_isShared_739_ == 0)
{
lean_ctor_set(v___x_738_, 2, v_ref_740_);
v___x_742_ = v___x_738_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v_toCold_731_);
lean_ctor_set(v_reuseFailAlloc_744_, 1, v_currRecDepth_732_);
lean_ctor_set(v_reuseFailAlloc_744_, 2, v_ref_740_);
lean_ctor_set_uint16(v_reuseFailAlloc_744_, sizeof(void*)*3, v_optionFlags_734_);
lean_ctor_set_uint8(v_reuseFailAlloc_744_, sizeof(void*)*3 + 2, v_suppressElabErrors_735_);
lean_ctor_set_uint8(v_reuseFailAlloc_744_, sizeof(void*)*3 + 3, v_isRecordingDeps_736_);
v___x_742_ = v_reuseFailAlloc_744_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
lean_object* v___x_743_; 
v___x_743_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v___f_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_, v___x_742_, v___y_729_);
lean_dec_ref(v___x_742_);
return v___x_743_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__5___boxed(lean_object* v___x_746_, lean_object* v___f_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_){
_start:
{
lean_object* v_res_755_; 
v_res_755_ = l_Lean_Elab_Tactic_Conv_evalPattern___lam__5(v___x_746_, v___f_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_);
lean_dec(v___y_753_);
lean_dec(v___y_751_);
lean_dec_ref(v___y_750_);
lean_dec(v___y_749_);
lean_dec_ref(v___y_748_);
lean_dec(v___x_746_);
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
lean_object* v___x_780_; lean_object* v_env_781_; uint8_t v___x_782_; lean_object* v_env_783_; lean_object* v___x_784_; lean_object* v_toCold_785_; lean_object* v_mctx_786_; lean_object* v_lctx_787_; lean_object* v_options_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; 
v___x_780_ = lean_st_ref_get(v___y_778_);
v_env_781_ = lean_ctor_get(v___x_780_, 0);
lean_inc_ref(v_env_781_);
lean_dec(v___x_780_);
v___x_782_ = 0;
v_env_783_ = l_Lean_Environment_setRecordingDeps(v_env_781_, v___x_782_);
v___x_784_ = lean_st_ref_get(v___y_776_);
v_toCold_785_ = lean_ctor_get(v___y_777_, 0);
v_mctx_786_ = lean_ctor_get(v___x_784_, 0);
lean_inc_ref(v_mctx_786_);
lean_dec(v___x_784_);
v_lctx_787_ = lean_ctor_get(v___y_775_, 2);
v_options_788_ = lean_ctor_get(v_toCold_785_, 2);
lean_inc_ref(v_options_788_);
lean_inc_ref(v_lctx_787_);
v___x_789_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_789_, 0, v_env_783_);
lean_ctor_set(v___x_789_, 1, v_mctx_786_);
lean_ctor_set(v___x_789_, 2, v_lctx_787_);
lean_ctor_set(v___x_789_, 3, v_options_788_);
v___x_790_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_790_, 0, v___x_789_);
lean_ctor_set(v___x_790_, 1, v_msgData_774_);
v___x_791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_791_, 0, v___x_790_);
return v___x_791_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4_spec__5___boxed(lean_object* v_msgData_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_){
_start:
{
lean_object* v_res_798_; 
v_res_798_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4_spec__5(v_msgData_792_, v___y_793_, v___y_794_, v___y_795_, v___y_796_);
lean_dec(v___y_796_);
lean_dec_ref(v___y_795_);
lean_dec(v___y_794_);
lean_dec_ref(v___y_793_);
return v_res_798_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg(lean_object* v_msg_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_){
_start:
{
lean_object* v_ref_805_; lean_object* v___x_806_; lean_object* v_a_807_; lean_object* v___x_809_; uint8_t v_isShared_810_; uint8_t v_isSharedCheck_815_; 
v_ref_805_ = lean_ctor_get(v___y_802_, 2);
v___x_806_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4_spec__5(v_msg_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_);
v_a_807_ = lean_ctor_get(v___x_806_, 0);
v_isSharedCheck_815_ = !lean_is_exclusive(v___x_806_);
if (v_isSharedCheck_815_ == 0)
{
v___x_809_ = v___x_806_;
v_isShared_810_ = v_isSharedCheck_815_;
goto v_resetjp_808_;
}
else
{
lean_inc(v_a_807_);
lean_dec(v___x_806_);
v___x_809_ = lean_box(0);
v_isShared_810_ = v_isSharedCheck_815_;
goto v_resetjp_808_;
}
v_resetjp_808_:
{
lean_object* v___x_811_; lean_object* v___x_813_; 
lean_inc(v_ref_805_);
v___x_811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_811_, 0, v_ref_805_);
lean_ctor_set(v___x_811_, 1, v_a_807_);
if (v_isShared_810_ == 0)
{
lean_ctor_set_tag(v___x_809_, 1);
lean_ctor_set(v___x_809_, 0, v___x_811_);
v___x_813_ = v___x_809_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v___x_811_);
v___x_813_ = v_reuseFailAlloc_814_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
return v___x_813_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg___boxed(lean_object* v_msg_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_){
_start:
{
lean_object* v_res_822_; 
v_res_822_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg(v_msg_816_, v___y_817_, v___y_818_, v___y_819_, v___y_820_);
lean_dec(v___y_820_);
lean_dec_ref(v___y_819_);
lean_dec(v___y_818_);
lean_dec_ref(v___y_817_);
return v_res_822_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg(lean_object* v_ref_823_, lean_object* v_msg_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_){
_start:
{
lean_object* v_toCold_834_; lean_object* v_currRecDepth_835_; lean_object* v_ref_836_; uint16_t v_optionFlags_837_; uint8_t v_suppressElabErrors_838_; uint8_t v_isRecordingDeps_839_; lean_object* v_ref_840_; lean_object* v___x_841_; lean_object* v___x_842_; 
v_toCold_834_ = lean_ctor_get(v___y_831_, 0);
v_currRecDepth_835_ = lean_ctor_get(v___y_831_, 1);
v_ref_836_ = lean_ctor_get(v___y_831_, 2);
v_optionFlags_837_ = lean_ctor_get_uint16(v___y_831_, sizeof(void*)*3);
v_suppressElabErrors_838_ = lean_ctor_get_uint8(v___y_831_, sizeof(void*)*3 + 2);
v_isRecordingDeps_839_ = lean_ctor_get_uint8(v___y_831_, sizeof(void*)*3 + 3);
v_ref_840_ = l_Lean_replaceRef(v_ref_823_, v_ref_836_);
lean_inc(v_currRecDepth_835_);
lean_inc_ref(v_toCold_834_);
v___x_841_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_841_, 0, v_toCold_834_);
lean_ctor_set(v___x_841_, 1, v_currRecDepth_835_);
lean_ctor_set(v___x_841_, 2, v_ref_840_);
lean_ctor_set_uint16(v___x_841_, sizeof(void*)*3, v_optionFlags_837_);
lean_ctor_set_uint8(v___x_841_, sizeof(void*)*3 + 2, v_suppressElabErrors_838_);
lean_ctor_set_uint8(v___x_841_, sizeof(void*)*3 + 3, v_isRecordingDeps_839_);
v___x_842_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg(v_msg_824_, v___y_829_, v___y_830_, v___x_841_, v___y_832_);
lean_dec_ref_known(v___x_841_, 3);
return v___x_842_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg___boxed(lean_object* v_ref_843_, lean_object* v_msg_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_){
_start:
{
lean_object* v_res_854_; 
v_res_854_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg(v_ref_843_, v_msg_844_, v___y_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_, v___y_851_, v___y_852_);
lean_dec(v___y_852_);
lean_dec_ref(v___y_851_);
lean_dec(v___y_850_);
lean_dec_ref(v___y_849_);
lean_dec(v___y_848_);
lean_dec_ref(v___y_847_);
lean_dec(v___y_846_);
lean_dec_ref(v___y_845_);
lean_dec(v_ref_843_);
return v_res_854_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_856_; lean_object* v___x_857_; 
v___x_856_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg___closed__0));
v___x_857_ = l_Lean_stringToMessageData(v___x_856_);
return v___x_857_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg(size_t v_sz_858_, size_t v_i_859_, lean_object* v_bs_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_){
_start:
{
uint8_t v___x_870_; 
v___x_870_ = lean_usize_dec_lt(v_i_859_, v_sz_858_);
if (v___x_870_ == 0)
{
lean_object* v___x_871_; 
v___x_871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_871_, 0, v_bs_860_);
return v___x_871_;
}
else
{
lean_object* v_v_872_; lean_object* v___x_873_; lean_object* v_bs_x27_874_; lean_object* v_a_876_; lean_object* v___x_881_; uint8_t v_isZero_882_; 
v_v_872_ = lean_array_uget(v_bs_860_, v_i_859_);
v___x_873_ = lean_unsigned_to_nat(0u);
v_bs_x27_874_ = lean_array_uset(v_bs_860_, v_i_859_, v___x_873_);
v___x_881_ = l_Lean_TSyntax_getNat(v_v_872_);
v_isZero_882_ = lean_nat_dec_eq(v___x_881_, v___x_873_);
if (v_isZero_882_ == 1)
{
lean_object* v___x_883_; lean_object* v___x_884_; 
lean_dec(v___x_881_);
v___x_883_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg___closed__1);
v___x_884_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg(v_v_872_, v___x_883_, v___y_861_, v___y_862_, v___y_863_, v___y_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_);
lean_dec(v_v_872_);
if (lean_obj_tag(v___x_884_) == 0)
{
lean_object* v_a_885_; 
v_a_885_ = lean_ctor_get(v___x_884_, 0);
lean_inc(v_a_885_);
lean_dec_ref_known(v___x_884_, 1);
v_a_876_ = v_a_885_;
goto v___jp_875_;
}
else
{
lean_object* v_a_886_; lean_object* v___x_888_; uint8_t v_isShared_889_; uint8_t v_isSharedCheck_893_; 
lean_dec_ref(v_bs_x27_874_);
v_a_886_ = lean_ctor_get(v___x_884_, 0);
v_isSharedCheck_893_ = !lean_is_exclusive(v___x_884_);
if (v_isSharedCheck_893_ == 0)
{
v___x_888_ = v___x_884_;
v_isShared_889_ = v_isSharedCheck_893_;
goto v_resetjp_887_;
}
else
{
lean_inc(v_a_886_);
lean_dec(v___x_884_);
v___x_888_ = lean_box(0);
v_isShared_889_ = v_isSharedCheck_893_;
goto v_resetjp_887_;
}
v_resetjp_887_:
{
lean_object* v___x_891_; 
if (v_isShared_889_ == 0)
{
v___x_891_ = v___x_888_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v_a_886_);
v___x_891_ = v_reuseFailAlloc_892_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
return v___x_891_;
}
}
}
}
else
{
lean_object* v___x_894_; lean_object* v_one_895_; lean_object* v_n_896_; lean_object* v___x_897_; 
lean_dec(v_v_872_);
v___x_894_ = lean_usize_to_nat(v_i_859_);
v_one_895_ = lean_unsigned_to_nat(1u);
v_n_896_ = lean_nat_sub(v___x_881_, v_one_895_);
lean_dec(v___x_881_);
v___x_897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_897_, 0, v_n_896_);
lean_ctor_set(v___x_897_, 1, v___x_894_);
v_a_876_ = v___x_897_;
goto v___jp_875_;
}
v___jp_875_:
{
size_t v___x_877_; size_t v___x_878_; lean_object* v___x_879_; 
v___x_877_ = ((size_t)1ULL);
v___x_878_ = lean_usize_add(v_i_859_, v___x_877_);
v___x_879_ = lean_array_uset(v_bs_x27_874_, v_i_859_, v_a_876_);
v_i_859_ = v___x_878_;
v_bs_860_ = v___x_879_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg___boxed(lean_object* v_sz_898_, lean_object* v_i_899_, lean_object* v_bs_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_){
_start:
{
size_t v_sz_boxed_910_; size_t v_i_boxed_911_; lean_object* v_res_912_; 
v_sz_boxed_910_ = lean_unbox_usize(v_sz_898_);
lean_dec(v_sz_898_);
v_i_boxed_911_ = lean_unbox_usize(v_i_899_);
lean_dec(v_i_899_);
v_res_912_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg(v_sz_boxed_910_, v_i_boxed_911_, v_bs_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_);
lean_dec(v___y_908_);
lean_dec_ref(v___y_907_);
lean_dec(v___y_906_);
lean_dec_ref(v___y_905_);
lean_dec(v___y_904_);
lean_dec_ref(v___y_903_);
lean_dec(v___y_902_);
lean_dec_ref(v___y_901_);
return v_res_912_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6_spec__8___redArg(lean_object* v_hi_913_, lean_object* v_pivot_914_, lean_object* v_as_915_, lean_object* v_i_916_, lean_object* v_k_917_){
_start:
{
uint8_t v___x_918_; 
v___x_918_ = lean_nat_dec_lt(v_k_917_, v_hi_913_);
if (v___x_918_ == 0)
{
lean_object* v___x_919_; lean_object* v___x_920_; 
lean_dec(v_k_917_);
v___x_919_ = lean_array_fswap(v_as_915_, v_i_916_, v_hi_913_);
v___x_920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_920_, 0, v_i_916_);
lean_ctor_set(v___x_920_, 1, v___x_919_);
return v___x_920_;
}
else
{
lean_object* v___x_921_; lean_object* v_fst_922_; lean_object* v_fst_923_; uint8_t v___x_924_; 
v___x_921_ = lean_array_fget_borrowed(v_as_915_, v_k_917_);
v_fst_922_ = lean_ctor_get(v___x_921_, 0);
v_fst_923_ = lean_ctor_get(v_pivot_914_, 0);
v___x_924_ = lean_nat_dec_lt(v_fst_922_, v_fst_923_);
if (v___x_924_ == 0)
{
lean_object* v___x_925_; lean_object* v___x_926_; 
v___x_925_ = lean_unsigned_to_nat(1u);
v___x_926_ = lean_nat_add(v_k_917_, v___x_925_);
lean_dec(v_k_917_);
v_k_917_ = v___x_926_;
goto _start;
}
else
{
lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; 
v___x_928_ = lean_array_fswap(v_as_915_, v_i_916_, v_k_917_);
v___x_929_ = lean_unsigned_to_nat(1u);
v___x_930_ = lean_nat_add(v_i_916_, v___x_929_);
lean_dec(v_i_916_);
v___x_931_ = lean_nat_add(v_k_917_, v___x_929_);
lean_dec(v_k_917_);
v_as_915_ = v___x_928_;
v_i_916_ = v___x_930_;
v_k_917_ = v___x_931_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6_spec__8___redArg___boxed(lean_object* v_hi_933_, lean_object* v_pivot_934_, lean_object* v_as_935_, lean_object* v_i_936_, lean_object* v_k_937_){
_start:
{
lean_object* v_res_938_; 
v_res_938_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6_spec__8___redArg(v_hi_933_, v_pivot_934_, v_as_935_, v_i_936_, v_k_937_);
lean_dec_ref(v_pivot_934_);
lean_dec(v_hi_933_);
return v_res_938_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg___lam__0(lean_object* v_x1_939_, lean_object* v_x2_940_){
_start:
{
lean_object* v_fst_941_; lean_object* v_fst_942_; uint8_t v___x_943_; 
v_fst_941_ = lean_ctor_get(v_x1_939_, 0);
v_fst_942_ = lean_ctor_get(v_x2_940_, 0);
v___x_943_ = lean_nat_dec_lt(v_fst_941_, v_fst_942_);
return v___x_943_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg___lam__0___boxed(lean_object* v_x1_944_, lean_object* v_x2_945_){
_start:
{
uint8_t v_res_946_; lean_object* v_r_947_; 
v_res_946_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg___lam__0(v_x1_944_, v_x2_945_);
lean_dec_ref(v_x2_945_);
lean_dec_ref(v_x1_944_);
v_r_947_ = lean_box(v_res_946_);
return v_r_947_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg(lean_object* v_n_948_, lean_object* v_as_949_, lean_object* v_lo_950_, lean_object* v_hi_951_){
_start:
{
lean_object* v___y_953_; uint8_t v___x_963_; 
v___x_963_ = lean_nat_dec_lt(v_lo_950_, v_hi_951_);
if (v___x_963_ == 0)
{
lean_dec(v_lo_950_);
return v_as_949_;
}
else
{
lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v_mid_966_; lean_object* v___y_968_; lean_object* v___y_974_; lean_object* v___x_979_; lean_object* v___x_980_; uint8_t v___x_981_; 
v___x_964_ = lean_nat_add(v_lo_950_, v_hi_951_);
v___x_965_ = lean_unsigned_to_nat(1u);
v_mid_966_ = lean_nat_shiftr(v___x_964_, v___x_965_);
lean_dec(v___x_964_);
v___x_979_ = lean_array_fget_borrowed(v_as_949_, v_mid_966_);
v___x_980_ = lean_array_fget_borrowed(v_as_949_, v_lo_950_);
v___x_981_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg___lam__0(v___x_979_, v___x_980_);
if (v___x_981_ == 0)
{
v___y_974_ = v_as_949_;
goto v___jp_973_;
}
else
{
lean_object* v___x_982_; 
v___x_982_ = lean_array_fswap(v_as_949_, v_lo_950_, v_mid_966_);
v___y_974_ = v___x_982_;
goto v___jp_973_;
}
v___jp_967_:
{
lean_object* v___x_969_; lean_object* v___x_970_; uint8_t v___x_971_; 
v___x_969_ = lean_array_fget_borrowed(v___y_968_, v_mid_966_);
v___x_970_ = lean_array_fget_borrowed(v___y_968_, v_hi_951_);
v___x_971_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg___lam__0(v___x_969_, v___x_970_);
if (v___x_971_ == 0)
{
lean_dec(v_mid_966_);
v___y_953_ = v___y_968_;
goto v___jp_952_;
}
else
{
lean_object* v___x_972_; 
v___x_972_ = lean_array_fswap(v___y_968_, v_mid_966_, v_hi_951_);
lean_dec(v_mid_966_);
v___y_953_ = v___x_972_;
goto v___jp_952_;
}
}
v___jp_973_:
{
lean_object* v___x_975_; lean_object* v___x_976_; uint8_t v___x_977_; 
v___x_975_ = lean_array_fget_borrowed(v___y_974_, v_hi_951_);
v___x_976_ = lean_array_fget_borrowed(v___y_974_, v_lo_950_);
v___x_977_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg___lam__0(v___x_975_, v___x_976_);
if (v___x_977_ == 0)
{
v___y_968_ = v___y_974_;
goto v___jp_967_;
}
else
{
lean_object* v___x_978_; 
v___x_978_ = lean_array_fswap(v___y_974_, v_lo_950_, v_hi_951_);
v___y_968_ = v___x_978_;
goto v___jp_967_;
}
}
}
v___jp_952_:
{
lean_object* v_pivot_954_; lean_object* v___x_955_; lean_object* v_fst_956_; lean_object* v_snd_957_; uint8_t v___x_958_; 
v_pivot_954_ = lean_array_fget(v___y_953_, v_hi_951_);
lean_inc_n(v_lo_950_, 2);
v___x_955_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6_spec__8___redArg(v_hi_951_, v_pivot_954_, v___y_953_, v_lo_950_, v_lo_950_);
lean_dec(v_pivot_954_);
v_fst_956_ = lean_ctor_get(v___x_955_, 0);
lean_inc(v_fst_956_);
v_snd_957_ = lean_ctor_get(v___x_955_, 1);
lean_inc(v_snd_957_);
lean_dec_ref(v___x_955_);
v___x_958_ = lean_nat_dec_le(v_hi_951_, v_fst_956_);
if (v___x_958_ == 0)
{
lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; 
v___x_959_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg(v_n_948_, v_snd_957_, v_lo_950_, v_fst_956_);
v___x_960_ = lean_unsigned_to_nat(1u);
v___x_961_ = lean_nat_add(v_fst_956_, v___x_960_);
lean_dec(v_fst_956_);
v_as_949_ = v___x_959_;
v_lo_950_ = v___x_961_;
goto _start;
}
else
{
lean_dec(v_fst_956_);
lean_dec(v_lo_950_);
return v_snd_957_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg___boxed(lean_object* v_n_983_, lean_object* v_as_984_, lean_object* v_lo_985_, lean_object* v_hi_986_){
_start:
{
lean_object* v_res_987_; 
v_res_987_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg(v_n_983_, v_as_984_, v_lo_985_, v_hi_986_);
lean_dec(v_hi_986_);
lean_dec(v_n_983_);
return v_res_987_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__12_spec__16___redArg(lean_object* v_x_988_, lean_object* v_x_989_, lean_object* v_x_990_, lean_object* v_x_991_){
_start:
{
lean_object* v_ks_992_; lean_object* v_vs_993_; lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1017_; 
v_ks_992_ = lean_ctor_get(v_x_988_, 0);
v_vs_993_ = lean_ctor_get(v_x_988_, 1);
v_isSharedCheck_1017_ = !lean_is_exclusive(v_x_988_);
if (v_isSharedCheck_1017_ == 0)
{
v___x_995_ = v_x_988_;
v_isShared_996_ = v_isSharedCheck_1017_;
goto v_resetjp_994_;
}
else
{
lean_inc(v_vs_993_);
lean_inc(v_ks_992_);
lean_dec(v_x_988_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1017_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
lean_object* v___x_997_; uint8_t v___x_998_; 
v___x_997_ = lean_array_get_size(v_ks_992_);
v___x_998_ = lean_nat_dec_lt(v_x_989_, v___x_997_);
if (v___x_998_ == 0)
{
lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1002_; 
lean_dec(v_x_989_);
v___x_999_ = lean_array_push(v_ks_992_, v_x_990_);
v___x_1000_ = lean_array_push(v_vs_993_, v_x_991_);
if (v_isShared_996_ == 0)
{
lean_ctor_set(v___x_995_, 1, v___x_1000_);
lean_ctor_set(v___x_995_, 0, v___x_999_);
v___x_1002_ = v___x_995_;
goto v_reusejp_1001_;
}
else
{
lean_object* v_reuseFailAlloc_1003_; 
v_reuseFailAlloc_1003_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1003_, 0, v___x_999_);
lean_ctor_set(v_reuseFailAlloc_1003_, 1, v___x_1000_);
v___x_1002_ = v_reuseFailAlloc_1003_;
goto v_reusejp_1001_;
}
v_reusejp_1001_:
{
return v___x_1002_;
}
}
else
{
lean_object* v_k_x27_1004_; uint8_t v___x_1005_; 
v_k_x27_1004_ = lean_array_fget_borrowed(v_ks_992_, v_x_989_);
v___x_1005_ = l_Lean_instBEqMVarId_beq(v_x_990_, v_k_x27_1004_);
if (v___x_1005_ == 0)
{
lean_object* v___x_1007_; 
if (v_isShared_996_ == 0)
{
v___x_1007_ = v___x_995_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1011_; 
v_reuseFailAlloc_1011_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1011_, 0, v_ks_992_);
lean_ctor_set(v_reuseFailAlloc_1011_, 1, v_vs_993_);
v___x_1007_ = v_reuseFailAlloc_1011_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
lean_object* v___x_1008_; lean_object* v___x_1009_; 
v___x_1008_ = lean_unsigned_to_nat(1u);
v___x_1009_ = lean_nat_add(v_x_989_, v___x_1008_);
lean_dec(v_x_989_);
v_x_988_ = v___x_1007_;
v_x_989_ = v___x_1009_;
goto _start;
}
}
else
{
lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1015_; 
v___x_1012_ = lean_array_fset(v_ks_992_, v_x_989_, v_x_990_);
v___x_1013_ = lean_array_fset(v_vs_993_, v_x_989_, v_x_991_);
lean_dec(v_x_989_);
if (v_isShared_996_ == 0)
{
lean_ctor_set(v___x_995_, 1, v___x_1013_);
lean_ctor_set(v___x_995_, 0, v___x_1012_);
v___x_1015_ = v___x_995_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v___x_1012_);
lean_ctor_set(v_reuseFailAlloc_1016_, 1, v___x_1013_);
v___x_1015_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
return v___x_1015_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__12___redArg(lean_object* v_n_1018_, lean_object* v_k_1019_, lean_object* v_v_1020_){
_start:
{
lean_object* v___x_1021_; lean_object* v___x_1022_; 
v___x_1021_ = lean_unsigned_to_nat(0u);
v___x_1022_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__12_spec__16___redArg(v_n_1018_, v___x_1021_, v_k_1019_, v_v_1020_);
return v___x_1022_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_1023_; 
v___x_1023_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_1023_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg(lean_object* v_x_1024_, size_t v_x_1025_, size_t v_x_1026_, lean_object* v_x_1027_, lean_object* v_x_1028_){
_start:
{
if (lean_obj_tag(v_x_1024_) == 0)
{
lean_object* v_es_1029_; size_t v___x_1030_; size_t v___x_1031_; lean_object* v_j_1032_; lean_object* v___x_1033_; uint8_t v___x_1034_; 
v_es_1029_ = lean_ctor_get(v_x_1024_, 0);
v___x_1030_ = ((size_t)31ULL);
v___x_1031_ = lean_usize_land(v_x_1025_, v___x_1030_);
v_j_1032_ = lean_usize_to_nat(v___x_1031_);
v___x_1033_ = lean_array_get_size(v_es_1029_);
v___x_1034_ = lean_nat_dec_lt(v_j_1032_, v___x_1033_);
if (v___x_1034_ == 0)
{
lean_dec(v_j_1032_);
lean_dec(v_x_1028_);
lean_dec(v_x_1027_);
return v_x_1024_;
}
else
{
lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1073_; 
lean_inc_ref(v_es_1029_);
v_isSharedCheck_1073_ = !lean_is_exclusive(v_x_1024_);
if (v_isSharedCheck_1073_ == 0)
{
lean_object* v_unused_1074_; 
v_unused_1074_ = lean_ctor_get(v_x_1024_, 0);
lean_dec(v_unused_1074_);
v___x_1036_ = v_x_1024_;
v_isShared_1037_ = v_isSharedCheck_1073_;
goto v_resetjp_1035_;
}
else
{
lean_dec(v_x_1024_);
v___x_1036_ = lean_box(0);
v_isShared_1037_ = v_isSharedCheck_1073_;
goto v_resetjp_1035_;
}
v_resetjp_1035_:
{
lean_object* v_v_1038_; lean_object* v___x_1039_; lean_object* v_xs_x27_1040_; lean_object* v___y_1042_; 
v_v_1038_ = lean_array_fget(v_es_1029_, v_j_1032_);
v___x_1039_ = lean_box(0);
v_xs_x27_1040_ = lean_array_fset(v_es_1029_, v_j_1032_, v___x_1039_);
switch(lean_obj_tag(v_v_1038_))
{
case 0:
{
lean_object* v_key_1047_; lean_object* v_val_1048_; lean_object* v___x_1050_; uint8_t v_isShared_1051_; uint8_t v_isSharedCheck_1058_; 
v_key_1047_ = lean_ctor_get(v_v_1038_, 0);
v_val_1048_ = lean_ctor_get(v_v_1038_, 1);
v_isSharedCheck_1058_ = !lean_is_exclusive(v_v_1038_);
if (v_isSharedCheck_1058_ == 0)
{
v___x_1050_ = v_v_1038_;
v_isShared_1051_ = v_isSharedCheck_1058_;
goto v_resetjp_1049_;
}
else
{
lean_inc(v_val_1048_);
lean_inc(v_key_1047_);
lean_dec(v_v_1038_);
v___x_1050_ = lean_box(0);
v_isShared_1051_ = v_isSharedCheck_1058_;
goto v_resetjp_1049_;
}
v_resetjp_1049_:
{
uint8_t v___x_1052_; 
v___x_1052_ = l_Lean_instBEqMVarId_beq(v_x_1027_, v_key_1047_);
if (v___x_1052_ == 0)
{
lean_object* v___x_1053_; lean_object* v___x_1054_; 
lean_del_object(v___x_1050_);
v___x_1053_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1047_, v_val_1048_, v_x_1027_, v_x_1028_);
v___x_1054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1054_, 0, v___x_1053_);
v___y_1042_ = v___x_1054_;
goto v___jp_1041_;
}
else
{
lean_object* v___x_1056_; 
lean_dec(v_val_1048_);
lean_dec(v_key_1047_);
if (v_isShared_1051_ == 0)
{
lean_ctor_set(v___x_1050_, 1, v_x_1028_);
lean_ctor_set(v___x_1050_, 0, v_x_1027_);
v___x_1056_ = v___x_1050_;
goto v_reusejp_1055_;
}
else
{
lean_object* v_reuseFailAlloc_1057_; 
v_reuseFailAlloc_1057_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1057_, 0, v_x_1027_);
lean_ctor_set(v_reuseFailAlloc_1057_, 1, v_x_1028_);
v___x_1056_ = v_reuseFailAlloc_1057_;
goto v_reusejp_1055_;
}
v_reusejp_1055_:
{
v___y_1042_ = v___x_1056_;
goto v___jp_1041_;
}
}
}
}
case 1:
{
lean_object* v_node_1059_; lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1071_; 
v_node_1059_ = lean_ctor_get(v_v_1038_, 0);
v_isSharedCheck_1071_ = !lean_is_exclusive(v_v_1038_);
if (v_isSharedCheck_1071_ == 0)
{
v___x_1061_ = v_v_1038_;
v_isShared_1062_ = v_isSharedCheck_1071_;
goto v_resetjp_1060_;
}
else
{
lean_inc(v_node_1059_);
lean_dec(v_v_1038_);
v___x_1061_ = lean_box(0);
v_isShared_1062_ = v_isSharedCheck_1071_;
goto v_resetjp_1060_;
}
v_resetjp_1060_:
{
size_t v___x_1063_; size_t v___x_1064_; size_t v___x_1065_; size_t v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1069_; 
v___x_1063_ = ((size_t)5ULL);
v___x_1064_ = lean_usize_shift_right(v_x_1025_, v___x_1063_);
v___x_1065_ = ((size_t)1ULL);
v___x_1066_ = lean_usize_add(v_x_1026_, v___x_1065_);
v___x_1067_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg(v_node_1059_, v___x_1064_, v___x_1066_, v_x_1027_, v_x_1028_);
if (v_isShared_1062_ == 0)
{
lean_ctor_set(v___x_1061_, 0, v___x_1067_);
v___x_1069_ = v___x_1061_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v___x_1067_);
v___x_1069_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
v___y_1042_ = v___x_1069_;
goto v___jp_1041_;
}
}
}
default: 
{
lean_object* v___x_1072_; 
v___x_1072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1072_, 0, v_x_1027_);
lean_ctor_set(v___x_1072_, 1, v_x_1028_);
v___y_1042_ = v___x_1072_;
goto v___jp_1041_;
}
}
v___jp_1041_:
{
lean_object* v___x_1043_; lean_object* v___x_1045_; 
v___x_1043_ = lean_array_fset(v_xs_x27_1040_, v_j_1032_, v___y_1042_);
lean_dec(v_j_1032_);
if (v_isShared_1037_ == 0)
{
lean_ctor_set(v___x_1036_, 0, v___x_1043_);
v___x_1045_ = v___x_1036_;
goto v_reusejp_1044_;
}
else
{
lean_object* v_reuseFailAlloc_1046_; 
v_reuseFailAlloc_1046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1046_, 0, v___x_1043_);
v___x_1045_ = v_reuseFailAlloc_1046_;
goto v_reusejp_1044_;
}
v_reusejp_1044_:
{
return v___x_1045_;
}
}
}
}
}
else
{
lean_object* v_ks_1075_; lean_object* v_vs_1076_; lean_object* v___x_1078_; uint8_t v_isShared_1079_; uint8_t v_isSharedCheck_1094_; 
v_ks_1075_ = lean_ctor_get(v_x_1024_, 0);
v_vs_1076_ = lean_ctor_get(v_x_1024_, 1);
v_isSharedCheck_1094_ = !lean_is_exclusive(v_x_1024_);
if (v_isSharedCheck_1094_ == 0)
{
v___x_1078_ = v_x_1024_;
v_isShared_1079_ = v_isSharedCheck_1094_;
goto v_resetjp_1077_;
}
else
{
lean_inc(v_vs_1076_);
lean_inc(v_ks_1075_);
lean_dec(v_x_1024_);
v___x_1078_ = lean_box(0);
v_isShared_1079_ = v_isSharedCheck_1094_;
goto v_resetjp_1077_;
}
v_resetjp_1077_:
{
lean_object* v___x_1081_; 
if (v_isShared_1079_ == 0)
{
v___x_1081_ = v___x_1078_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v_ks_1075_);
lean_ctor_set(v_reuseFailAlloc_1093_, 1, v_vs_1076_);
v___x_1081_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
lean_object* v_newNode_1082_; size_t v___x_1083_; uint8_t v___x_1084_; 
v_newNode_1082_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__12___redArg(v___x_1081_, v_x_1027_, v_x_1028_);
v___x_1083_ = ((size_t)7ULL);
v___x_1084_ = lean_usize_dec_le(v___x_1083_, v_x_1026_);
if (v___x_1084_ == 0)
{
lean_object* v___x_1085_; lean_object* v___x_1086_; uint8_t v___x_1087_; 
v___x_1085_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1082_);
v___x_1086_ = lean_unsigned_to_nat(4u);
v___x_1087_ = lean_nat_dec_lt(v___x_1085_, v___x_1086_);
lean_dec(v___x_1085_);
if (v___x_1087_ == 0)
{
lean_object* v_ks_1088_; lean_object* v_vs_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; 
v_ks_1088_ = lean_ctor_get(v_newNode_1082_, 0);
lean_inc_ref(v_ks_1088_);
v_vs_1089_ = lean_ctor_get(v_newNode_1082_, 1);
lean_inc_ref(v_vs_1089_);
lean_dec_ref(v_newNode_1082_);
v___x_1090_ = lean_unsigned_to_nat(0u);
v___x_1091_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__0);
v___x_1092_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__13___redArg(v_x_1026_, v_ks_1088_, v_vs_1089_, v___x_1090_, v___x_1091_);
lean_dec_ref(v_vs_1089_);
lean_dec_ref(v_ks_1088_);
return v___x_1092_;
}
else
{
return v_newNode_1082_;
}
}
else
{
return v_newNode_1082_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__13___redArg(size_t v_depth_1095_, lean_object* v_keys_1096_, lean_object* v_vals_1097_, lean_object* v_i_1098_, lean_object* v_entries_1099_){
_start:
{
lean_object* v___x_1100_; uint8_t v___x_1101_; 
v___x_1100_ = lean_array_get_size(v_keys_1096_);
v___x_1101_ = lean_nat_dec_lt(v_i_1098_, v___x_1100_);
if (v___x_1101_ == 0)
{
lean_dec(v_i_1098_);
return v_entries_1099_;
}
else
{
lean_object* v_k_1102_; lean_object* v_v_1103_; uint64_t v___x_1104_; size_t v_h_1105_; size_t v___x_1106_; lean_object* v___x_1107_; size_t v___x_1108_; size_t v___x_1109_; size_t v___x_1110_; size_t v_h_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; 
v_k_1102_ = lean_array_fget_borrowed(v_keys_1096_, v_i_1098_);
v_v_1103_ = lean_array_fget_borrowed(v_vals_1097_, v_i_1098_);
v___x_1104_ = l_Lean_instHashableMVarId_hash(v_k_1102_);
v_h_1105_ = lean_uint64_to_usize(v___x_1104_);
v___x_1106_ = ((size_t)5ULL);
v___x_1107_ = lean_unsigned_to_nat(1u);
v___x_1108_ = ((size_t)1ULL);
v___x_1109_ = lean_usize_sub(v_depth_1095_, v___x_1108_);
v___x_1110_ = lean_usize_mul(v___x_1106_, v___x_1109_);
v_h_1111_ = lean_usize_shift_right(v_h_1105_, v___x_1110_);
v___x_1112_ = lean_nat_add(v_i_1098_, v___x_1107_);
lean_dec(v_i_1098_);
lean_inc(v_v_1103_);
lean_inc(v_k_1102_);
v___x_1113_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg(v_entries_1099_, v_h_1111_, v_depth_1095_, v_k_1102_, v_v_1103_);
v_i_1098_ = v___x_1112_;
v_entries_1099_ = v___x_1113_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__13___redArg___boxed(lean_object* v_depth_1115_, lean_object* v_keys_1116_, lean_object* v_vals_1117_, lean_object* v_i_1118_, lean_object* v_entries_1119_){
_start:
{
size_t v_depth_boxed_1120_; lean_object* v_res_1121_; 
v_depth_boxed_1120_ = lean_unbox_usize(v_depth_1115_);
lean_dec(v_depth_1115_);
v_res_1121_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__13___redArg(v_depth_boxed_1120_, v_keys_1116_, v_vals_1117_, v_i_1118_, v_entries_1119_);
lean_dec_ref(v_vals_1117_);
lean_dec_ref(v_keys_1116_);
return v_res_1121_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___boxed(lean_object* v_x_1122_, lean_object* v_x_1123_, lean_object* v_x_1124_, lean_object* v_x_1125_, lean_object* v_x_1126_){
_start:
{
size_t v_x_15921__boxed_1127_; size_t v_x_15922__boxed_1128_; lean_object* v_res_1129_; 
v_x_15921__boxed_1127_ = lean_unbox_usize(v_x_1123_);
lean_dec(v_x_1123_);
v_x_15922__boxed_1128_ = lean_unbox_usize(v_x_1124_);
lean_dec(v_x_1124_);
v_res_1129_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg(v_x_1122_, v_x_15921__boxed_1127_, v_x_15922__boxed_1128_, v_x_1125_, v_x_1126_);
return v_res_1129_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3___redArg(lean_object* v_x_1130_, lean_object* v_x_1131_, lean_object* v_x_1132_){
_start:
{
uint64_t v___x_1133_; size_t v___x_1134_; size_t v___x_1135_; lean_object* v___x_1136_; 
v___x_1133_ = l_Lean_instHashableMVarId_hash(v_x_1131_);
v___x_1134_ = lean_uint64_to_usize(v___x_1133_);
v___x_1135_ = ((size_t)1ULL);
v___x_1136_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg(v_x_1130_, v___x_1134_, v___x_1135_, v_x_1131_, v_x_1132_);
return v___x_1136_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3___redArg(lean_object* v_mvarId_1137_, lean_object* v_val_1138_, lean_object* v___y_1139_){
_start:
{
lean_object* v___x_1141_; lean_object* v_mctx_1142_; lean_object* v_cache_1143_; lean_object* v_zetaDeltaFVarIds_1144_; lean_object* v_postponed_1145_; lean_object* v_diag_1146_; lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1175_; 
v___x_1141_ = lean_st_ref_take(v___y_1139_);
v_mctx_1142_ = lean_ctor_get(v___x_1141_, 0);
v_cache_1143_ = lean_ctor_get(v___x_1141_, 1);
v_zetaDeltaFVarIds_1144_ = lean_ctor_get(v___x_1141_, 2);
v_postponed_1145_ = lean_ctor_get(v___x_1141_, 3);
v_diag_1146_ = lean_ctor_get(v___x_1141_, 4);
v_isSharedCheck_1175_ = !lean_is_exclusive(v___x_1141_);
if (v_isSharedCheck_1175_ == 0)
{
v___x_1148_ = v___x_1141_;
v_isShared_1149_ = v_isSharedCheck_1175_;
goto v_resetjp_1147_;
}
else
{
lean_inc(v_diag_1146_);
lean_inc(v_postponed_1145_);
lean_inc(v_zetaDeltaFVarIds_1144_);
lean_inc(v_cache_1143_);
lean_inc(v_mctx_1142_);
lean_dec(v___x_1141_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1175_;
goto v_resetjp_1147_;
}
v_resetjp_1147_:
{
lean_object* v_depth_1150_; lean_object* v_levelAssignDepth_1151_; lean_object* v_lmvarCounter_1152_; lean_object* v_mvarCounter_1153_; lean_object* v_lDecls_1154_; lean_object* v_decls_1155_; lean_object* v_userNames_1156_; lean_object* v_lAssignment_1157_; lean_object* v_eAssignment_1158_; lean_object* v_dAssignment_1159_; lean_object* v_instanceTypedMVars_1160_; lean_object* v___x_1162_; uint8_t v_isShared_1163_; uint8_t v_isSharedCheck_1174_; 
v_depth_1150_ = lean_ctor_get(v_mctx_1142_, 0);
v_levelAssignDepth_1151_ = lean_ctor_get(v_mctx_1142_, 1);
v_lmvarCounter_1152_ = lean_ctor_get(v_mctx_1142_, 2);
v_mvarCounter_1153_ = lean_ctor_get(v_mctx_1142_, 3);
v_lDecls_1154_ = lean_ctor_get(v_mctx_1142_, 4);
v_decls_1155_ = lean_ctor_get(v_mctx_1142_, 5);
v_userNames_1156_ = lean_ctor_get(v_mctx_1142_, 6);
v_lAssignment_1157_ = lean_ctor_get(v_mctx_1142_, 7);
v_eAssignment_1158_ = lean_ctor_get(v_mctx_1142_, 8);
v_dAssignment_1159_ = lean_ctor_get(v_mctx_1142_, 9);
v_instanceTypedMVars_1160_ = lean_ctor_get(v_mctx_1142_, 10);
v_isSharedCheck_1174_ = !lean_is_exclusive(v_mctx_1142_);
if (v_isSharedCheck_1174_ == 0)
{
v___x_1162_ = v_mctx_1142_;
v_isShared_1163_ = v_isSharedCheck_1174_;
goto v_resetjp_1161_;
}
else
{
lean_inc(v_instanceTypedMVars_1160_);
lean_inc(v_dAssignment_1159_);
lean_inc(v_eAssignment_1158_);
lean_inc(v_lAssignment_1157_);
lean_inc(v_userNames_1156_);
lean_inc(v_decls_1155_);
lean_inc(v_lDecls_1154_);
lean_inc(v_mvarCounter_1153_);
lean_inc(v_lmvarCounter_1152_);
lean_inc(v_levelAssignDepth_1151_);
lean_inc(v_depth_1150_);
lean_dec(v_mctx_1142_);
v___x_1162_ = lean_box(0);
v_isShared_1163_ = v_isSharedCheck_1174_;
goto v_resetjp_1161_;
}
v_resetjp_1161_:
{
lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1167_; 
v___x_1164_ = lean_box(0);
v___x_1165_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3___redArg(v_eAssignment_1158_, v_mvarId_1137_, v_val_1138_);
if (v_isShared_1163_ == 0)
{
lean_ctor_set(v___x_1162_, 8, v___x_1165_);
v___x_1167_ = v___x_1162_;
goto v_reusejp_1166_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v_depth_1150_);
lean_ctor_set(v_reuseFailAlloc_1173_, 1, v_levelAssignDepth_1151_);
lean_ctor_set(v_reuseFailAlloc_1173_, 2, v_lmvarCounter_1152_);
lean_ctor_set(v_reuseFailAlloc_1173_, 3, v_mvarCounter_1153_);
lean_ctor_set(v_reuseFailAlloc_1173_, 4, v_lDecls_1154_);
lean_ctor_set(v_reuseFailAlloc_1173_, 5, v_decls_1155_);
lean_ctor_set(v_reuseFailAlloc_1173_, 6, v_userNames_1156_);
lean_ctor_set(v_reuseFailAlloc_1173_, 7, v_lAssignment_1157_);
lean_ctor_set(v_reuseFailAlloc_1173_, 8, v___x_1165_);
lean_ctor_set(v_reuseFailAlloc_1173_, 9, v_dAssignment_1159_);
lean_ctor_set(v_reuseFailAlloc_1173_, 10, v_instanceTypedMVars_1160_);
v___x_1167_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1166_;
}
v_reusejp_1166_:
{
lean_object* v___x_1169_; 
if (v_isShared_1149_ == 0)
{
lean_ctor_set(v___x_1148_, 0, v___x_1167_);
v___x_1169_ = v___x_1148_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1172_; 
v_reuseFailAlloc_1172_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1172_, 0, v___x_1167_);
lean_ctor_set(v_reuseFailAlloc_1172_, 1, v_cache_1143_);
lean_ctor_set(v_reuseFailAlloc_1172_, 2, v_zetaDeltaFVarIds_1144_);
lean_ctor_set(v_reuseFailAlloc_1172_, 3, v_postponed_1145_);
lean_ctor_set(v_reuseFailAlloc_1172_, 4, v_diag_1146_);
v___x_1169_ = v_reuseFailAlloc_1172_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
lean_object* v___x_1170_; lean_object* v___x_1171_; 
v___x_1170_ = lean_st_ref_put(v___y_1139_, v___x_1169_);
v___x_1171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1171_, 0, v___x_1164_);
return v___x_1171_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3___redArg___boxed(lean_object* v_mvarId_1176_, lean_object* v_val_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_){
_start:
{
lean_object* v_res_1180_; 
v_res_1180_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3___redArg(v_mvarId_1176_, v_val_1177_, v___y_1178_);
lean_dec(v___y_1178_);
return v_res_1180_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg___lam__0(lean_object* v_x1_1181_, lean_object* v_x2_1182_){
_start:
{
lean_object* v_fst_1183_; lean_object* v_fst_1184_; uint8_t v___x_1185_; 
v_fst_1183_ = lean_ctor_get(v_x1_1181_, 0);
v_fst_1184_ = lean_ctor_get(v_x2_1182_, 0);
v___x_1185_ = lean_nat_dec_lt(v_fst_1183_, v_fst_1184_);
return v___x_1185_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg___lam__0___boxed(lean_object* v_x1_1186_, lean_object* v_x2_1187_){
_start:
{
uint8_t v_res_1188_; lean_object* v_r_1189_; 
v_res_1188_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg___lam__0(v_x1_1186_, v_x2_1187_);
lean_dec_ref(v_x2_1187_);
lean_dec_ref(v_x1_1186_);
v_r_1189_ = lean_box(v_res_1188_);
return v_r_1189_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9_spec__13___redArg(lean_object* v_hi_1190_, lean_object* v_pivot_1191_, lean_object* v_as_1192_, lean_object* v_i_1193_, lean_object* v_k_1194_){
_start:
{
uint8_t v___x_1195_; 
v___x_1195_ = lean_nat_dec_lt(v_k_1194_, v_hi_1190_);
if (v___x_1195_ == 0)
{
lean_object* v___x_1196_; lean_object* v___x_1197_; 
lean_dec(v_k_1194_);
v___x_1196_ = lean_array_fswap(v_as_1192_, v_i_1193_, v_hi_1190_);
v___x_1197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1197_, 0, v_i_1193_);
lean_ctor_set(v___x_1197_, 1, v___x_1196_);
return v___x_1197_;
}
else
{
lean_object* v___x_1198_; lean_object* v_fst_1199_; lean_object* v_fst_1200_; uint8_t v___x_1201_; 
v___x_1198_ = lean_array_fget_borrowed(v_as_1192_, v_k_1194_);
v_fst_1199_ = lean_ctor_get(v___x_1198_, 0);
v_fst_1200_ = lean_ctor_get(v_pivot_1191_, 0);
v___x_1201_ = lean_nat_dec_lt(v_fst_1199_, v_fst_1200_);
if (v___x_1201_ == 0)
{
lean_object* v___x_1202_; lean_object* v___x_1203_; 
v___x_1202_ = lean_unsigned_to_nat(1u);
v___x_1203_ = lean_nat_add(v_k_1194_, v___x_1202_);
lean_dec(v_k_1194_);
v_k_1194_ = v___x_1203_;
goto _start;
}
else
{
lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; 
v___x_1205_ = lean_array_fswap(v_as_1192_, v_i_1193_, v_k_1194_);
v___x_1206_ = lean_unsigned_to_nat(1u);
v___x_1207_ = lean_nat_add(v_i_1193_, v___x_1206_);
lean_dec(v_i_1193_);
v___x_1208_ = lean_nat_add(v_k_1194_, v___x_1206_);
lean_dec(v_k_1194_);
v_as_1192_ = v___x_1205_;
v_i_1193_ = v___x_1207_;
v_k_1194_ = v___x_1208_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9_spec__13___redArg___boxed(lean_object* v_hi_1210_, lean_object* v_pivot_1211_, lean_object* v_as_1212_, lean_object* v_i_1213_, lean_object* v_k_1214_){
_start:
{
lean_object* v_res_1215_; 
v_res_1215_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9_spec__13___redArg(v_hi_1210_, v_pivot_1211_, v_as_1212_, v_i_1213_, v_k_1214_);
lean_dec_ref(v_pivot_1211_);
lean_dec(v_hi_1210_);
return v_res_1215_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg(lean_object* v_n_1216_, lean_object* v_as_1217_, lean_object* v_lo_1218_, lean_object* v_hi_1219_){
_start:
{
lean_object* v___y_1221_; uint8_t v___x_1231_; 
v___x_1231_ = lean_nat_dec_lt(v_lo_1218_, v_hi_1219_);
if (v___x_1231_ == 0)
{
lean_dec(v_lo_1218_);
return v_as_1217_;
}
else
{
lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v_mid_1234_; lean_object* v___y_1236_; lean_object* v___y_1242_; lean_object* v___x_1247_; lean_object* v___x_1248_; uint8_t v___x_1249_; 
v___x_1232_ = lean_nat_add(v_lo_1218_, v_hi_1219_);
v___x_1233_ = lean_unsigned_to_nat(1u);
v_mid_1234_ = lean_nat_shiftr(v___x_1232_, v___x_1233_);
lean_dec(v___x_1232_);
v___x_1247_ = lean_array_fget_borrowed(v_as_1217_, v_mid_1234_);
v___x_1248_ = lean_array_fget_borrowed(v_as_1217_, v_lo_1218_);
v___x_1249_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg___lam__0(v___x_1247_, v___x_1248_);
if (v___x_1249_ == 0)
{
v___y_1242_ = v_as_1217_;
goto v___jp_1241_;
}
else
{
lean_object* v___x_1250_; 
v___x_1250_ = lean_array_fswap(v_as_1217_, v_lo_1218_, v_mid_1234_);
v___y_1242_ = v___x_1250_;
goto v___jp_1241_;
}
v___jp_1235_:
{
lean_object* v___x_1237_; lean_object* v___x_1238_; uint8_t v___x_1239_; 
v___x_1237_ = lean_array_fget_borrowed(v___y_1236_, v_mid_1234_);
v___x_1238_ = lean_array_fget_borrowed(v___y_1236_, v_hi_1219_);
v___x_1239_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg___lam__0(v___x_1237_, v___x_1238_);
if (v___x_1239_ == 0)
{
lean_dec(v_mid_1234_);
v___y_1221_ = v___y_1236_;
goto v___jp_1220_;
}
else
{
lean_object* v___x_1240_; 
v___x_1240_ = lean_array_fswap(v___y_1236_, v_mid_1234_, v_hi_1219_);
lean_dec(v_mid_1234_);
v___y_1221_ = v___x_1240_;
goto v___jp_1220_;
}
}
v___jp_1241_:
{
lean_object* v___x_1243_; lean_object* v___x_1244_; uint8_t v___x_1245_; 
v___x_1243_ = lean_array_fget_borrowed(v___y_1242_, v_hi_1219_);
v___x_1244_ = lean_array_fget_borrowed(v___y_1242_, v_lo_1218_);
v___x_1245_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg___lam__0(v___x_1243_, v___x_1244_);
if (v___x_1245_ == 0)
{
v___y_1236_ = v___y_1242_;
goto v___jp_1235_;
}
else
{
lean_object* v___x_1246_; 
v___x_1246_ = lean_array_fswap(v___y_1242_, v_lo_1218_, v_hi_1219_);
v___y_1236_ = v___x_1246_;
goto v___jp_1235_;
}
}
}
v___jp_1220_:
{
lean_object* v_pivot_1222_; lean_object* v___x_1223_; lean_object* v_fst_1224_; lean_object* v_snd_1225_; uint8_t v___x_1226_; 
v_pivot_1222_ = lean_array_fget(v___y_1221_, v_hi_1219_);
lean_inc_n(v_lo_1218_, 2);
v___x_1223_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9_spec__13___redArg(v_hi_1219_, v_pivot_1222_, v___y_1221_, v_lo_1218_, v_lo_1218_);
lean_dec(v_pivot_1222_);
v_fst_1224_ = lean_ctor_get(v___x_1223_, 0);
lean_inc(v_fst_1224_);
v_snd_1225_ = lean_ctor_get(v___x_1223_, 1);
lean_inc(v_snd_1225_);
lean_dec_ref(v___x_1223_);
v___x_1226_ = lean_nat_dec_le(v_hi_1219_, v_fst_1224_);
if (v___x_1226_ == 0)
{
lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; 
v___x_1227_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg(v_n_1216_, v_snd_1225_, v_lo_1218_, v_fst_1224_);
v___x_1228_ = lean_unsigned_to_nat(1u);
v___x_1229_ = lean_nat_add(v_fst_1224_, v___x_1228_);
lean_dec(v_fst_1224_);
v_as_1217_ = v___x_1227_;
v_lo_1218_ = v___x_1229_;
goto _start;
}
else
{
lean_dec(v_fst_1224_);
lean_dec(v_lo_1218_);
return v_snd_1225_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg___boxed(lean_object* v_n_1251_, lean_object* v_as_1252_, lean_object* v_lo_1253_, lean_object* v_hi_1254_){
_start:
{
lean_object* v_res_1255_; 
v_res_1255_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg(v_n_1251_, v_as_1252_, v_lo_1253_, v_hi_1254_);
lean_dec(v_hi_1254_);
lean_dec(v_n_1251_);
return v_res_1255_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11_spec__13___redArg(lean_object* v_as_1256_, lean_object* v_a_1257_, lean_object* v_x_1258_){
_start:
{
lean_object* v_zero_1259_; uint8_t v_isZero_1260_; 
v_zero_1259_ = lean_unsigned_to_nat(0u);
v_isZero_1260_ = lean_nat_dec_eq(v_x_1258_, v_zero_1259_);
if (v_isZero_1260_ == 1)
{
lean_dec(v_x_1258_);
return v_isZero_1260_;
}
else
{
lean_object* v_fst_1261_; lean_object* v_one_1262_; lean_object* v_n_1263_; lean_object* v___x_1264_; lean_object* v_fst_1265_; uint8_t v___x_1266_; 
v_fst_1261_ = lean_ctor_get(v_a_1257_, 0);
v_one_1262_ = lean_unsigned_to_nat(1u);
v_n_1263_ = lean_nat_sub(v_x_1258_, v_one_1262_);
lean_dec(v_x_1258_);
v___x_1264_ = lean_array_fget_borrowed(v_as_1256_, v_n_1263_);
v_fst_1265_ = lean_ctor_get(v___x_1264_, 0);
v___x_1266_ = lean_nat_dec_eq(v_fst_1261_, v_fst_1265_);
if (v___x_1266_ == 0)
{
v_x_1258_ = v_n_1263_;
goto _start;
}
else
{
lean_dec(v_n_1263_);
return v_isZero_1260_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11_spec__13___redArg___boxed(lean_object* v_as_1268_, lean_object* v_a_1269_, lean_object* v_x_1270_){
_start:
{
uint8_t v_res_1271_; lean_object* v_r_1272_; 
v_res_1271_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11_spec__13___redArg(v_as_1268_, v_a_1269_, v_x_1270_);
lean_dec_ref(v_a_1269_);
lean_dec_ref(v_as_1268_);
v_r_1272_ = lean_box(v_res_1271_);
return v_r_1272_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11(lean_object* v_as_1273_, lean_object* v_i_1274_){
_start:
{
lean_object* v___x_1275_; uint8_t v___x_1276_; 
v___x_1275_ = lean_array_get_size(v_as_1273_);
v___x_1276_ = lean_nat_dec_lt(v_i_1274_, v___x_1275_);
if (v___x_1276_ == 0)
{
uint8_t v___x_1277_; 
lean_dec(v_i_1274_);
v___x_1277_ = 1;
return v___x_1277_;
}
else
{
lean_object* v___x_1278_; uint8_t v___x_1279_; 
v___x_1278_ = lean_array_fget_borrowed(v_as_1273_, v_i_1274_);
lean_inc(v_i_1274_);
v___x_1279_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11_spec__13___redArg(v_as_1273_, v___x_1278_, v_i_1274_);
if (v___x_1279_ == 0)
{
lean_dec(v_i_1274_);
return v___x_1279_;
}
else
{
lean_object* v___x_1280_; lean_object* v___x_1281_; 
v___x_1280_ = lean_unsigned_to_nat(1u);
v___x_1281_ = lean_nat_add(v_i_1274_, v___x_1280_);
lean_dec(v_i_1274_);
v_i_1274_ = v___x_1281_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11___boxed(lean_object* v_as_1283_, lean_object* v_i_1284_){
_start:
{
uint8_t v_res_1285_; lean_object* v_r_1286_; 
v_res_1285_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11(v_as_1283_, v_i_1284_);
lean_dec_ref(v_as_1283_);
v_r_1286_ = lean_box(v_res_1285_);
return v_r_1286_;
}
}
LEAN_EXPORT uint8_t l_Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8(lean_object* v_as_1287_){
_start:
{
lean_object* v___x_1288_; uint8_t v___x_1289_; 
v___x_1288_ = lean_unsigned_to_nat(0u);
v___x_1289_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11(v_as_1287_, v___x_1288_);
return v___x_1289_;
}
}
LEAN_EXPORT lean_object* l_Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8___boxed(lean_object* v_as_1290_){
_start:
{
uint8_t v_res_1291_; lean_object* v_r_1292_; 
v_res_1291_ = l_Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8(v_as_1290_);
lean_dec_ref(v_as_1290_);
v_r_1292_ = lean_box(v_res_1291_);
return v_r_1292_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__0(void){
_start:
{
lean_object* v___x_1293_; 
v___x_1293_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1293_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__1(void){
_start:
{
lean_object* v___x_1294_; lean_object* v___x_1295_; 
v___x_1294_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__0, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__0_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__0);
v___x_1295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1295_, 0, v___x_1294_);
return v___x_1295_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__2(void){
_start:
{
lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; 
v___x_1296_ = lean_unsigned_to_nat(0u);
v___x_1297_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__1, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__1_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__1);
v___x_1298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1298_, 0, v___x_1297_);
lean_ctor_set(v___x_1298_, 1, v___x_1296_);
return v___x_1298_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__3(void){
_start:
{
lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; 
v___x_1299_ = lean_unsigned_to_nat(32u);
v___x_1300_ = lean_mk_empty_array_with_capacity(v___x_1299_);
v___x_1301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1301_, 0, v___x_1300_);
return v___x_1301_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__4(void){
_start:
{
size_t v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; 
v___x_1302_ = ((size_t)5ULL);
v___x_1303_ = lean_unsigned_to_nat(0u);
v___x_1304_ = lean_unsigned_to_nat(32u);
v___x_1305_ = lean_mk_empty_array_with_capacity(v___x_1304_);
v___x_1306_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__3, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__3_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__3);
v___x_1307_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1307_, 0, v___x_1306_);
lean_ctor_set(v___x_1307_, 1, v___x_1305_);
lean_ctor_set(v___x_1307_, 2, v___x_1303_);
lean_ctor_set(v___x_1307_, 3, v___x_1303_);
lean_ctor_set_usize(v___x_1307_, 4, v___x_1302_);
return v___x_1307_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__5(void){
_start:
{
lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; 
v___x_1308_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__4, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__4_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__4);
v___x_1309_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__1, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__1_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__1);
v___x_1310_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1310_, 0, v___x_1309_);
lean_ctor_set(v___x_1310_, 1, v___x_1309_);
lean_ctor_set(v___x_1310_, 2, v___x_1309_);
lean_ctor_set(v___x_1310_, 3, v___x_1308_);
return v___x_1310_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__6(void){
_start:
{
lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; 
v___x_1311_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__5, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__5_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__5);
v___x_1312_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__2, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__2_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__2);
v___x_1313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1313_, 0, v___x_1312_);
lean_ctor_set(v___x_1313_, 1, v___x_1311_);
return v___x_1313_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__8(void){
_start:
{
lean_object* v___x_1315_; lean_object* v___x_1316_; 
v___x_1315_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__7));
v___x_1316_ = l_Lean_stringToMessageData(v___x_1315_);
return v___x_1316_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__10(void){
_start:
{
lean_object* v___x_1318_; lean_object* v___x_1319_; 
v___x_1318_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__9));
v___x_1319_ = l_Lean_stringToMessageData(v___x_1318_);
return v___x_1319_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__12(void){
_start:
{
lean_object* v___x_1321_; lean_object* v___x_1322_; 
v___x_1321_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__11));
v___x_1322_ = l_Lean_stringToMessageData(v___x_1321_);
return v___x_1322_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__14(void){
_start:
{
lean_object* v___x_1324_; lean_object* v___x_1325_; 
v___x_1324_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__13));
v___x_1325_ = l_Lean_stringToMessageData(v___x_1324_);
return v___x_1325_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__17(void){
_start:
{
lean_object* v___x_1329_; lean_object* v___x_1330_; 
v___x_1329_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__16));
v___x_1330_ = l_Lean_stringToMessageData(v___x_1329_);
return v___x_1330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__6(uint8_t v___x_1351_, lean_object* v___f_1352_, uint8_t v___x_1353_, lean_object* v_stx_1354_, lean_object* v___x_1355_, lean_object* v___x_1356_, lean_object* v___x_1357_, lean_object* v___x_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_){
_start:
{
lean_object* v___y_1369_; lean_object* v_subgoals_1370_; lean_object* v___y_1371_; lean_object* v___y_1372_; lean_object* v___y_1373_; lean_object* v___y_1374_; lean_object* v___y_1375_; lean_object* v___y_1376_; lean_object* v___y_1377_; lean_object* v___y_1378_; lean_object* v___y_1416_; lean_object* v___y_1417_; lean_object* v___y_1418_; lean_object* v___y_1419_; lean_object* v___y_1420_; lean_object* v___y_1421_; lean_object* v___y_1422_; lean_object* v___y_1423_; lean_object* v___y_1424_; lean_object* v___y_1425_; lean_object* v___y_1430_; lean_object* v___y_1431_; lean_object* v___y_1432_; lean_object* v___y_1433_; lean_object* v___y_1434_; lean_object* v___y_1435_; lean_object* v___y_1436_; lean_object* v___y_1437_; lean_object* v___y_1438_; lean_object* v___y_1439_; lean_object* v___y_1440_; lean_object* v___y_1441_; lean_object* v___y_1442_; lean_object* v___y_1445_; lean_object* v___y_1446_; lean_object* v___y_1447_; lean_object* v___y_1448_; lean_object* v___y_1449_; lean_object* v___y_1450_; lean_object* v___y_1451_; lean_object* v___y_1452_; lean_object* v___y_1453_; lean_object* v___y_1454_; lean_object* v___y_1455_; lean_object* v___y_1456_; lean_object* v___y_1457_; 
if (v___x_1351_ == 0)
{
lean_object* v___x_1459_; 
lean_dec_ref(v___x_1358_);
lean_dec_ref(v___x_1357_);
lean_dec_ref(v___x_1356_);
lean_dec_ref(v___x_1355_);
lean_dec_ref(v___f_1352_);
v___x_1459_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1___redArg();
return v___x_1459_;
}
else
{
lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___y_1463_; lean_object* v___y_1464_; lean_object* v___y_1465_; lean_object* v___y_1466_; lean_object* v___y_1467_; lean_object* v___y_1468_; lean_object* v___y_1469_; lean_object* v___y_1470_; lean_object* v___y_1471_; lean_object* v___y_1472_; lean_object* v___y_1478_; lean_object* v___y_1479_; lean_object* v___y_1480_; lean_object* v___y_1481_; lean_object* v___y_1482_; lean_object* v___y_1483_; lean_object* v___y_1484_; lean_object* v___y_1485_; lean_object* v___y_1486_; lean_object* v___y_1487_; lean_object* v___y_1488_; lean_object* v___y_1489_; lean_object* v___y_1490_; lean_object* v___y_1491_; lean_object* v___y_1492_; uint8_t v___y_1493_; lean_object* v___y_1586_; lean_object* v___y_1587_; lean_object* v___y_1588_; lean_object* v___y_1589_; lean_object* v___y_1590_; lean_object* v_occs_1591_; lean_object* v___y_1592_; lean_object* v___y_1593_; lean_object* v___y_1594_; lean_object* v___y_1595_; lean_object* v___y_1596_; lean_object* v___y_1597_; lean_object* v___y_1598_; lean_object* v___y_1599_; lean_object* v___y_1614_; lean_object* v___y_1615_; lean_object* v___y_1616_; lean_object* v___y_1617_; lean_object* v___y_1618_; lean_object* v___y_1619_; lean_object* v___y_1620_; lean_object* v___y_1621_; lean_object* v___y_1622_; lean_object* v___y_1623_; lean_object* v___y_1624_; lean_object* v___y_1625_; lean_object* v___y_1626_; lean_object* v___y_1627_; lean_object* v___y_1632_; lean_object* v___y_1633_; lean_object* v___y_1634_; lean_object* v___y_1635_; lean_object* v___y_1636_; lean_object* v___y_1637_; lean_object* v___y_1638_; lean_object* v___y_1639_; lean_object* v___y_1640_; lean_object* v___y_1641_; lean_object* v___y_1642_; lean_object* v___y_1643_; lean_object* v___y_1644_; lean_object* v___y_1645_; lean_object* v___y_1650_; lean_object* v___y_1651_; lean_object* v___y_1652_; lean_object* v___y_1653_; lean_object* v___y_1654_; lean_object* v___y_1655_; lean_object* v___y_1656_; lean_object* v___y_1657_; lean_object* v___y_1658_; lean_object* v___y_1659_; lean_object* v___y_1660_; lean_object* v___y_1661_; lean_object* v___y_1662_; lean_object* v___y_1663_; lean_object* v___y_1664_; lean_object* v___y_1665_; lean_object* v___y_1666_; lean_object* v___y_1669_; lean_object* v___y_1670_; lean_object* v___y_1671_; lean_object* v___y_1672_; lean_object* v___y_1673_; lean_object* v___y_1674_; lean_object* v___y_1675_; lean_object* v___y_1676_; lean_object* v___y_1677_; lean_object* v___y_1678_; lean_object* v___y_1679_; lean_object* v___y_1680_; lean_object* v___y_1681_; lean_object* v___y_1682_; lean_object* v___y_1683_; lean_object* v___y_1684_; lean_object* v___y_1685_; lean_object* v_occs_1688_; lean_object* v___y_1689_; lean_object* v___y_1690_; lean_object* v___y_1691_; lean_object* v___y_1692_; lean_object* v___y_1693_; lean_object* v___y_1694_; lean_object* v___y_1695_; lean_object* v___y_1696_; lean_object* v___x_1783_; uint8_t v___x_1784_; 
v___x_1460_ = lean_unsigned_to_nat(0u);
v___x_1461_ = lean_unsigned_to_nat(1u);
v___x_1783_ = l_Lean_Syntax_getArg(v_stx_1354_, v___x_1461_);
v___x_1784_ = l_Lean_Syntax_isNone(v___x_1783_);
if (v___x_1784_ == 0)
{
uint8_t v___x_1785_; 
lean_inc(v___x_1783_);
v___x_1785_ = l_Lean_Syntax_matchesNull(v___x_1783_, v___x_1461_);
if (v___x_1785_ == 0)
{
lean_object* v___x_1786_; 
lean_dec(v___x_1783_);
lean_dec_ref(v___x_1358_);
lean_dec_ref(v___x_1357_);
lean_dec_ref(v___x_1356_);
lean_dec_ref(v___x_1355_);
lean_dec_ref(v___f_1352_);
v___x_1786_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1___redArg();
return v___x_1786_;
}
else
{
lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; uint8_t v___x_1790_; 
v___x_1787_ = l_Lean_Syntax_getArg(v___x_1783_, v___x_1460_);
lean_dec(v___x_1783_);
v___x_1788_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__27));
lean_inc_ref(v___x_1358_);
lean_inc_ref(v___x_1357_);
lean_inc_ref(v___x_1356_);
lean_inc_ref(v___x_1355_);
v___x_1789_ = l_Lean_Name_mkStr5(v___x_1355_, v___x_1356_, v___x_1357_, v___x_1358_, v___x_1788_);
lean_inc(v___x_1787_);
v___x_1790_ = l_Lean_Syntax_isOfKind(v___x_1787_, v___x_1789_);
lean_dec(v___x_1789_);
if (v___x_1790_ == 0)
{
lean_object* v___x_1791_; 
lean_dec(v___x_1787_);
lean_dec_ref(v___x_1358_);
lean_dec_ref(v___x_1357_);
lean_dec_ref(v___x_1356_);
lean_dec_ref(v___x_1355_);
lean_dec_ref(v___f_1352_);
v___x_1791_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1___redArg();
return v___x_1791_;
}
else
{
lean_object* v___x_1792_; lean_object* v_occs_1793_; lean_object* v___x_1794_; 
v___x_1792_ = lean_unsigned_to_nat(3u);
v_occs_1793_ = l_Lean_Syntax_getArg(v___x_1787_, v___x_1792_);
lean_dec(v___x_1787_);
v___x_1794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1794_, 0, v_occs_1793_);
v_occs_1688_ = v___x_1794_;
v___y_1689_ = v___y_1359_;
v___y_1690_ = v___y_1360_;
v___y_1691_ = v___y_1361_;
v___y_1692_ = v___y_1362_;
v___y_1693_ = v___y_1363_;
v___y_1694_ = v___y_1364_;
v___y_1695_ = v___y_1365_;
v___y_1696_ = v___y_1366_;
goto v___jp_1687_;
}
}
}
else
{
lean_object* v___x_1795_; 
lean_dec(v___x_1783_);
v___x_1795_ = lean_box(0);
v_occs_1688_ = v___x_1795_;
v___y_1689_ = v___y_1359_;
v___y_1690_ = v___y_1360_;
v___y_1691_ = v___y_1361_;
v___y_1692_ = v___y_1362_;
v___y_1693_ = v___y_1363_;
v___y_1694_ = v___y_1364_;
v___y_1695_ = v___y_1365_;
v___y_1696_ = v___y_1366_;
goto v___jp_1687_;
}
v___jp_1462_:
{
lean_object* v___x_1473_; uint8_t v___x_1474_; 
v___x_1473_ = lean_array_get_size(v___y_1464_);
v___x_1474_ = lean_nat_dec_eq(v___x_1473_, v___x_1460_);
if (v___x_1474_ == 0)
{
lean_object* v___x_1475_; uint8_t v___x_1476_; 
v___x_1475_ = lean_nat_sub(v___x_1473_, v___x_1461_);
v___x_1476_ = lean_nat_dec_le(v___x_1460_, v___x_1475_);
if (v___x_1476_ == 0)
{
lean_inc(v___x_1475_);
v___y_1445_ = v___y_1469_;
v___y_1446_ = v___x_1473_;
v___y_1447_ = v___y_1463_;
v___y_1448_ = v___y_1470_;
v___y_1449_ = v___y_1468_;
v___y_1450_ = v___y_1464_;
v___y_1451_ = v___y_1466_;
v___y_1452_ = v___y_1472_;
v___y_1453_ = v___y_1471_;
v___y_1454_ = v___x_1475_;
v___y_1455_ = v___y_1467_;
v___y_1456_ = v___y_1465_;
v___y_1457_ = v___x_1475_;
goto v___jp_1444_;
}
else
{
v___y_1445_ = v___y_1469_;
v___y_1446_ = v___x_1473_;
v___y_1447_ = v___y_1463_;
v___y_1448_ = v___y_1470_;
v___y_1449_ = v___y_1468_;
v___y_1450_ = v___y_1464_;
v___y_1451_ = v___y_1466_;
v___y_1452_ = v___y_1472_;
v___y_1453_ = v___y_1471_;
v___y_1454_ = v___x_1475_;
v___y_1455_ = v___y_1467_;
v___y_1456_ = v___y_1465_;
v___y_1457_ = v___x_1460_;
goto v___jp_1444_;
}
}
else
{
v___y_1416_ = v___y_1469_;
v___y_1417_ = v___y_1466_;
v___y_1418_ = v___y_1472_;
v___y_1419_ = v___y_1463_;
v___y_1420_ = v___y_1471_;
v___y_1421_ = v___y_1470_;
v___y_1422_ = v___y_1468_;
v___y_1423_ = v___y_1467_;
v___y_1424_ = v___y_1465_;
v___y_1425_ = v___y_1464_;
goto v___jp_1415_;
}
}
v___jp_1477_:
{
lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; 
v___x_1494_ = l_Lean_Meta_Simp_Context_setMemoize(v___y_1483_, v___y_1493_);
v___x_1495_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__6, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__6_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__6);
lean_inc(v___y_1485_);
lean_inc_ref(v___y_1492_);
v___x_1496_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre___boxed), 11, 2);
lean_closure_set(v___x_1496_, 0, v___y_1492_);
lean_closure_set(v___x_1496_, 1, v___y_1485_);
lean_inc_ref(v___y_1479_);
lean_inc_ref(v___y_1480_);
v___x_1497_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_1497_, 0, v___x_1496_);
lean_ctor_set(v___x_1497_, 1, v___y_1478_);
lean_ctor_set(v___x_1497_, 2, v___y_1480_);
lean_ctor_set(v___x_1497_, 3, v___f_1352_);
lean_ctor_set(v___x_1497_, 4, v___y_1479_);
lean_ctor_set_uint8(v___x_1497_, sizeof(void*)*5, v___x_1353_);
v___x_1498_ = l_Lean_Meta_Simp_main(v___y_1490_, v___x_1494_, v___x_1495_, v___x_1497_, v___y_1481_, v___y_1482_, v___y_1488_, v___y_1484_);
if (lean_obj_tag(v___x_1498_) == 0)
{
lean_object* v_a_1499_; lean_object* v_fst_1500_; lean_object* v___x_1502_; uint8_t v_isShared_1503_; uint8_t v_isSharedCheck_1575_; 
v_a_1499_ = lean_ctor_get(v___x_1498_, 0);
lean_inc(v_a_1499_);
lean_dec_ref_known(v___x_1498_, 1);
v_fst_1500_ = lean_ctor_get(v_a_1499_, 0);
v_isSharedCheck_1575_ = !lean_is_exclusive(v_a_1499_);
if (v_isSharedCheck_1575_ == 0)
{
lean_object* v_unused_1576_; 
v_unused_1576_ = lean_ctor_get(v_a_1499_, 1);
lean_dec(v_unused_1576_);
v___x_1502_ = v_a_1499_;
v_isShared_1503_ = v_isSharedCheck_1575_;
goto v_resetjp_1501_;
}
else
{
lean_inc(v_fst_1500_);
lean_dec(v_a_1499_);
v___x_1502_ = lean_box(0);
v_isShared_1503_ = v_isSharedCheck_1575_;
goto v_resetjp_1501_;
}
v_resetjp_1501_:
{
lean_object* v___x_1504_; 
v___x_1504_ = lean_st_ref_get(v___y_1485_);
lean_dec(v___y_1485_);
if (lean_obj_tag(v___x_1504_) == 0)
{
lean_object* v_subgoals_1505_; lean_object* v___x_1506_; uint8_t v___x_1507_; 
v_subgoals_1505_ = lean_ctor_get(v___x_1504_, 0);
lean_inc_ref(v_subgoals_1505_);
lean_dec_ref_known(v___x_1504_, 1);
v___x_1506_ = lean_array_get_size(v_subgoals_1505_);
v___x_1507_ = lean_nat_dec_eq(v___x_1506_, v___x_1460_);
if (v___x_1507_ == 0)
{
lean_del_object(v___x_1502_);
lean_dec_ref(v___y_1492_);
v___y_1369_ = v_fst_1500_;
v_subgoals_1370_ = v_subgoals_1505_;
v___y_1371_ = v___y_1487_;
v___y_1372_ = v___y_1489_;
v___y_1373_ = v___y_1491_;
v___y_1374_ = v___y_1486_;
v___y_1375_ = v___y_1481_;
v___y_1376_ = v___y_1482_;
v___y_1377_ = v___y_1488_;
v___y_1378_ = v___y_1484_;
goto v___jp_1368_;
}
else
{
lean_object* v_expr_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1512_; 
lean_dec_ref(v_subgoals_1505_);
lean_dec(v_fst_1500_);
v_expr_1508_ = lean_ctor_get(v___y_1492_, 2);
lean_inc_ref(v_expr_1508_);
lean_dec_ref(v___y_1492_);
v___x_1509_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__8, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__8_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__8);
v___x_1510_ = l_Lean_indentExpr(v_expr_1508_);
if (v_isShared_1503_ == 0)
{
lean_ctor_set_tag(v___x_1502_, 7);
lean_ctor_set(v___x_1502_, 1, v___x_1510_);
lean_ctor_set(v___x_1502_, 0, v___x_1509_);
v___x_1512_ = v___x_1502_;
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
v___x_1513_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg(v___x_1512_, v___y_1481_, v___y_1482_, v___y_1488_, v___y_1484_);
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
else
{
lean_object* v_subgoals_1523_; lean_object* v_idx_1524_; lean_object* v_remaining_1525_; uint8_t v___x_1526_; 
v_subgoals_1523_ = lean_ctor_get(v___x_1504_, 0);
lean_inc_ref(v_subgoals_1523_);
v_idx_1524_ = lean_ctor_get(v___x_1504_, 1);
lean_inc(v_idx_1524_);
v_remaining_1525_ = lean_ctor_get(v___x_1504_, 2);
lean_inc(v_remaining_1525_);
lean_dec_ref_known(v___x_1504_, 3);
v___x_1526_ = lean_nat_dec_eq(v_idx_1524_, v___x_1460_);
if (v___x_1526_ == 0)
{
lean_object* v___x_1527_; 
lean_dec_ref(v___y_1492_);
v___x_1527_ = l_List_getLast_x3f___redArg(v_remaining_1525_);
lean_dec(v_remaining_1525_);
if (lean_obj_tag(v___x_1527_) == 1)
{
lean_object* v_val_1528_; lean_object* v___x_1530_; uint8_t v_isShared_1531_; uint8_t v_isSharedCheck_1559_; 
lean_dec_ref(v_subgoals_1523_);
lean_dec(v_fst_1500_);
v_val_1528_ = lean_ctor_get(v___x_1527_, 0);
v_isSharedCheck_1559_ = !lean_is_exclusive(v___x_1527_);
if (v_isSharedCheck_1559_ == 0)
{
v___x_1530_ = v___x_1527_;
v_isShared_1531_ = v_isSharedCheck_1559_;
goto v_resetjp_1529_;
}
else
{
lean_inc(v_val_1528_);
lean_dec(v___x_1527_);
v___x_1530_ = lean_box(0);
v_isShared_1531_ = v_isSharedCheck_1559_;
goto v_resetjp_1529_;
}
v_resetjp_1529_:
{
lean_object* v_fst_1532_; lean_object* v___x_1534_; uint8_t v_isShared_1535_; uint8_t v_isSharedCheck_1557_; 
v_fst_1532_ = lean_ctor_get(v_val_1528_, 0);
v_isSharedCheck_1557_ = !lean_is_exclusive(v_val_1528_);
if (v_isSharedCheck_1557_ == 0)
{
lean_object* v_unused_1558_; 
v_unused_1558_ = lean_ctor_get(v_val_1528_, 1);
lean_dec(v_unused_1558_);
v___x_1534_ = v_val_1528_;
v_isShared_1535_ = v_isSharedCheck_1557_;
goto v_resetjp_1533_;
}
else
{
lean_inc(v_fst_1532_);
lean_dec(v_val_1528_);
v___x_1534_ = lean_box(0);
v_isShared_1535_ = v_isSharedCheck_1557_;
goto v_resetjp_1533_;
}
v_resetjp_1533_:
{
lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1539_; 
v___x_1536_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__10, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__10_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__10);
v___x_1537_ = l_Nat_reprFast(v_idx_1524_);
if (v_isShared_1531_ == 0)
{
lean_ctor_set_tag(v___x_1530_, 3);
lean_ctor_set(v___x_1530_, 0, v___x_1537_);
v___x_1539_ = v___x_1530_;
goto v_reusejp_1538_;
}
else
{
lean_object* v_reuseFailAlloc_1556_; 
v_reuseFailAlloc_1556_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1556_, 0, v___x_1537_);
v___x_1539_ = v_reuseFailAlloc_1556_;
goto v_reusejp_1538_;
}
v_reusejp_1538_:
{
lean_object* v___x_1540_; lean_object* v___x_1542_; 
v___x_1540_ = l_Lean_MessageData_ofFormat(v___x_1539_);
if (v_isShared_1535_ == 0)
{
lean_ctor_set_tag(v___x_1534_, 7);
lean_ctor_set(v___x_1534_, 1, v___x_1540_);
lean_ctor_set(v___x_1534_, 0, v___x_1536_);
v___x_1542_ = v___x_1534_;
goto v_reusejp_1541_;
}
else
{
lean_object* v_reuseFailAlloc_1555_; 
v_reuseFailAlloc_1555_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1555_, 0, v___x_1536_);
lean_ctor_set(v_reuseFailAlloc_1555_, 1, v___x_1540_);
v___x_1542_ = v_reuseFailAlloc_1555_;
goto v_reusejp_1541_;
}
v_reusejp_1541_:
{
lean_object* v___x_1543_; lean_object* v___x_1545_; 
v___x_1543_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__12, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__12_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__12);
if (v_isShared_1503_ == 0)
{
lean_ctor_set_tag(v___x_1502_, 7);
lean_ctor_set(v___x_1502_, 1, v___x_1543_);
lean_ctor_set(v___x_1502_, 0, v___x_1542_);
v___x_1545_ = v___x_1502_;
goto v_reusejp_1544_;
}
else
{
lean_object* v_reuseFailAlloc_1554_; 
v_reuseFailAlloc_1554_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1554_, 0, v___x_1542_);
lean_ctor_set(v_reuseFailAlloc_1554_, 1, v___x_1543_);
v___x_1545_ = v_reuseFailAlloc_1554_;
goto v_reusejp_1544_;
}
v_reusejp_1544_:
{
lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; 
v___x_1546_ = lean_nat_add(v_fst_1532_, v___x_1461_);
lean_dec(v_fst_1532_);
v___x_1547_ = l_Nat_reprFast(v___x_1546_);
v___x_1548_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1548_, 0, v___x_1547_);
v___x_1549_ = l_Lean_MessageData_ofFormat(v___x_1548_);
v___x_1550_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1550_, 0, v___x_1545_);
lean_ctor_set(v___x_1550_, 1, v___x_1549_);
v___x_1551_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__14, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__14_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__14);
v___x_1552_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1552_, 0, v___x_1550_);
lean_ctor_set(v___x_1552_, 1, v___x_1551_);
v___x_1553_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg(v___x_1552_, v___y_1481_, v___y_1482_, v___y_1488_, v___y_1484_);
return v___x_1553_;
}
}
}
}
}
}
else
{
lean_dec(v___x_1527_);
lean_dec(v_idx_1524_);
lean_del_object(v___x_1502_);
v___y_1463_ = v_fst_1500_;
v___y_1464_ = v_subgoals_1523_;
v___y_1465_ = v___y_1487_;
v___y_1466_ = v___y_1489_;
v___y_1467_ = v___y_1491_;
v___y_1468_ = v___y_1486_;
v___y_1469_ = v___y_1481_;
v___y_1470_ = v___y_1482_;
v___y_1471_ = v___y_1488_;
v___y_1472_ = v___y_1484_;
goto v___jp_1462_;
}
}
else
{
lean_object* v_expr_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1564_; 
lean_dec(v_remaining_1525_);
lean_dec(v_idx_1524_);
lean_dec_ref(v_subgoals_1523_);
lean_dec(v_fst_1500_);
v_expr_1560_ = lean_ctor_get(v___y_1492_, 2);
lean_inc_ref(v_expr_1560_);
lean_dec_ref(v___y_1492_);
v___x_1561_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__8, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__8_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__8);
v___x_1562_ = l_Lean_indentExpr(v_expr_1560_);
if (v_isShared_1503_ == 0)
{
lean_ctor_set_tag(v___x_1502_, 7);
lean_ctor_set(v___x_1502_, 1, v___x_1562_);
lean_ctor_set(v___x_1502_, 0, v___x_1561_);
v___x_1564_ = v___x_1502_;
goto v_reusejp_1563_;
}
else
{
lean_object* v_reuseFailAlloc_1574_; 
v_reuseFailAlloc_1574_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1574_, 0, v___x_1561_);
lean_ctor_set(v_reuseFailAlloc_1574_, 1, v___x_1562_);
v___x_1564_ = v_reuseFailAlloc_1574_;
goto v_reusejp_1563_;
}
v_reusejp_1563_:
{
lean_object* v___x_1565_; lean_object* v_a_1566_; lean_object* v___x_1568_; uint8_t v_isShared_1569_; uint8_t v_isSharedCheck_1573_; 
v___x_1565_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg(v___x_1564_, v___y_1481_, v___y_1482_, v___y_1488_, v___y_1484_);
v_a_1566_ = lean_ctor_get(v___x_1565_, 0);
v_isSharedCheck_1573_ = !lean_is_exclusive(v___x_1565_);
if (v_isSharedCheck_1573_ == 0)
{
v___x_1568_ = v___x_1565_;
v_isShared_1569_ = v_isSharedCheck_1573_;
goto v_resetjp_1567_;
}
else
{
lean_inc(v_a_1566_);
lean_dec(v___x_1565_);
v___x_1568_ = lean_box(0);
v_isShared_1569_ = v_isSharedCheck_1573_;
goto v_resetjp_1567_;
}
v_resetjp_1567_:
{
lean_object* v___x_1571_; 
if (v_isShared_1569_ == 0)
{
v___x_1571_ = v___x_1568_;
goto v_reusejp_1570_;
}
else
{
lean_object* v_reuseFailAlloc_1572_; 
v_reuseFailAlloc_1572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1572_, 0, v_a_1566_);
v___x_1571_ = v_reuseFailAlloc_1572_;
goto v_reusejp_1570_;
}
v_reusejp_1570_:
{
return v___x_1571_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1577_; lean_object* v___x_1579_; uint8_t v_isShared_1580_; uint8_t v_isSharedCheck_1584_; 
lean_dec_ref(v___y_1492_);
lean_dec(v___y_1485_);
v_a_1577_ = lean_ctor_get(v___x_1498_, 0);
v_isSharedCheck_1584_ = !lean_is_exclusive(v___x_1498_);
if (v_isSharedCheck_1584_ == 0)
{
v___x_1579_ = v___x_1498_;
v_isShared_1580_ = v_isSharedCheck_1584_;
goto v_resetjp_1578_;
}
else
{
lean_inc(v_a_1577_);
lean_dec(v___x_1498_);
v___x_1579_ = lean_box(0);
v_isShared_1580_ = v_isSharedCheck_1584_;
goto v_resetjp_1578_;
}
v_resetjp_1578_:
{
lean_object* v___x_1582_; 
if (v_isShared_1580_ == 0)
{
v___x_1582_ = v___x_1579_;
goto v_reusejp_1581_;
}
else
{
lean_object* v_reuseFailAlloc_1583_; 
v_reuseFailAlloc_1583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1583_, 0, v_a_1577_);
v___x_1582_ = v_reuseFailAlloc_1583_;
goto v_reusejp_1581_;
}
v_reusejp_1581_:
{
return v___x_1582_;
}
}
}
}
v___jp_1585_:
{
lean_object* v___x_1600_; lean_object* v___x_1601_; 
lean_inc_ref(v_occs_1591_);
v___x_1600_ = lean_st_mk_ref(v_occs_1591_);
v___x_1601_ = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_getContext___redArg(v___y_1596_, v___y_1598_, v___y_1599_);
if (lean_obj_tag(v___x_1601_) == 0)
{
if (lean_obj_tag(v_occs_1591_) == 0)
{
lean_object* v_a_1602_; 
lean_dec_ref_known(v_occs_1591_, 1);
v_a_1602_ = lean_ctor_get(v___x_1601_, 0);
lean_inc(v_a_1602_);
lean_dec_ref_known(v___x_1601_, 1);
v___y_1478_ = v___y_1586_;
v___y_1479_ = v___y_1587_;
v___y_1480_ = v___y_1589_;
v___y_1481_ = v___y_1596_;
v___y_1482_ = v___y_1597_;
v___y_1483_ = v_a_1602_;
v___y_1484_ = v___y_1599_;
v___y_1485_ = v___x_1600_;
v___y_1486_ = v___y_1595_;
v___y_1487_ = v___y_1592_;
v___y_1488_ = v___y_1598_;
v___y_1489_ = v___y_1593_;
v___y_1490_ = v___y_1588_;
v___y_1491_ = v___y_1594_;
v___y_1492_ = v___y_1590_;
v___y_1493_ = v___x_1353_;
goto v___jp_1477_;
}
else
{
lean_object* v_a_1603_; uint8_t v___x_1604_; 
lean_dec_ref(v_occs_1591_);
v_a_1603_ = lean_ctor_get(v___x_1601_, 0);
lean_inc(v_a_1603_);
lean_dec_ref_known(v___x_1601_, 1);
v___x_1604_ = 0;
v___y_1478_ = v___y_1586_;
v___y_1479_ = v___y_1587_;
v___y_1480_ = v___y_1589_;
v___y_1481_ = v___y_1596_;
v___y_1482_ = v___y_1597_;
v___y_1483_ = v_a_1603_;
v___y_1484_ = v___y_1599_;
v___y_1485_ = v___x_1600_;
v___y_1486_ = v___y_1595_;
v___y_1487_ = v___y_1592_;
v___y_1488_ = v___y_1598_;
v___y_1489_ = v___y_1593_;
v___y_1490_ = v___y_1588_;
v___y_1491_ = v___y_1594_;
v___y_1492_ = v___y_1590_;
v___y_1493_ = v___x_1604_;
goto v___jp_1477_;
}
}
else
{
lean_object* v_a_1605_; lean_object* v___x_1607_; uint8_t v_isShared_1608_; uint8_t v_isSharedCheck_1612_; 
lean_dec(v___x_1600_);
lean_dec_ref(v_occs_1591_);
lean_dec_ref(v___y_1590_);
lean_dec_ref(v___y_1588_);
lean_dec_ref(v___y_1586_);
lean_dec_ref(v___f_1352_);
v_a_1605_ = lean_ctor_get(v___x_1601_, 0);
v_isSharedCheck_1612_ = !lean_is_exclusive(v___x_1601_);
if (v_isSharedCheck_1612_ == 0)
{
v___x_1607_ = v___x_1601_;
v_isShared_1608_ = v_isSharedCheck_1612_;
goto v_resetjp_1606_;
}
else
{
lean_inc(v_a_1605_);
lean_dec(v___x_1601_);
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
v___jp_1613_:
{
lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; 
v___x_1628_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__15));
v___x_1629_ = lean_array_to_list(v___y_1619_);
v___x_1630_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1630_, 0, v___x_1628_);
lean_ctor_set(v___x_1630_, 1, v___x_1460_);
lean_ctor_set(v___x_1630_, 2, v___x_1629_);
v___y_1586_ = v___y_1614_;
v___y_1587_ = v___y_1615_;
v___y_1588_ = v___y_1616_;
v___y_1589_ = v___y_1617_;
v___y_1590_ = v___y_1618_;
v_occs_1591_ = v___x_1630_;
v___y_1592_ = v___y_1620_;
v___y_1593_ = v___y_1621_;
v___y_1594_ = v___y_1622_;
v___y_1595_ = v___y_1623_;
v___y_1596_ = v___y_1624_;
v___y_1597_ = v___y_1625_;
v___y_1598_ = v___y_1626_;
v___y_1599_ = v___y_1627_;
goto v___jp_1585_;
}
v___jp_1631_:
{
uint8_t v___x_1646_; 
v___x_1646_ = l_Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8(v___y_1645_);
if (v___x_1646_ == 0)
{
lean_object* v___x_1647_; lean_object* v___x_1648_; 
lean_dec_ref(v___y_1645_);
lean_dec_ref(v___y_1642_);
lean_dec_ref(v___y_1639_);
lean_dec_ref(v___y_1633_);
lean_dec_ref(v___f_1352_);
v___x_1647_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__17, &l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__17_once, _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__17);
v___x_1648_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg(v___x_1647_, v___y_1638_, v___y_1641_, v___y_1632_, v___y_1640_);
return v___x_1648_;
}
else
{
v___y_1614_ = v___y_1633_;
v___y_1615_ = v___y_1634_;
v___y_1616_ = v___y_1639_;
v___y_1617_ = v___y_1635_;
v___y_1618_ = v___y_1642_;
v___y_1619_ = v___y_1645_;
v___y_1620_ = v___y_1637_;
v___y_1621_ = v___y_1636_;
v___y_1622_ = v___y_1644_;
v___y_1623_ = v___y_1643_;
v___y_1624_ = v___y_1638_;
v___y_1625_ = v___y_1641_;
v___y_1626_ = v___y_1632_;
v___y_1627_ = v___y_1640_;
goto v___jp_1613_;
}
}
v___jp_1649_:
{
lean_object* v___x_1667_; 
v___x_1667_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg(v___y_1652_, v___y_1654_, v___y_1657_, v___y_1666_);
lean_dec(v___y_1666_);
lean_dec(v___y_1652_);
v___y_1632_ = v___y_1650_;
v___y_1633_ = v___y_1651_;
v___y_1634_ = v___y_1653_;
v___y_1635_ = v___y_1655_;
v___y_1636_ = v___y_1656_;
v___y_1637_ = v___y_1658_;
v___y_1638_ = v___y_1659_;
v___y_1639_ = v___y_1660_;
v___y_1640_ = v___y_1661_;
v___y_1641_ = v___y_1662_;
v___y_1642_ = v___y_1664_;
v___y_1643_ = v___y_1663_;
v___y_1644_ = v___y_1665_;
v___y_1645_ = v___x_1667_;
goto v___jp_1631_;
}
v___jp_1668_:
{
uint8_t v___x_1686_; 
v___x_1686_ = lean_nat_dec_le(v___y_1685_, v___y_1683_);
if (v___x_1686_ == 0)
{
lean_dec(v___y_1683_);
lean_inc(v___y_1685_);
v___y_1650_ = v___y_1669_;
v___y_1651_ = v___y_1670_;
v___y_1652_ = v___y_1671_;
v___y_1653_ = v___y_1672_;
v___y_1654_ = v___y_1673_;
v___y_1655_ = v___y_1674_;
v___y_1656_ = v___y_1675_;
v___y_1657_ = v___y_1685_;
v___y_1658_ = v___y_1676_;
v___y_1659_ = v___y_1677_;
v___y_1660_ = v___y_1678_;
v___y_1661_ = v___y_1679_;
v___y_1662_ = v___y_1680_;
v___y_1663_ = v___y_1682_;
v___y_1664_ = v___y_1681_;
v___y_1665_ = v___y_1684_;
v___y_1666_ = v___y_1685_;
goto v___jp_1649_;
}
else
{
v___y_1650_ = v___y_1669_;
v___y_1651_ = v___y_1670_;
v___y_1652_ = v___y_1671_;
v___y_1653_ = v___y_1672_;
v___y_1654_ = v___y_1673_;
v___y_1655_ = v___y_1674_;
v___y_1656_ = v___y_1675_;
v___y_1657_ = v___y_1685_;
v___y_1658_ = v___y_1676_;
v___y_1659_ = v___y_1677_;
v___y_1660_ = v___y_1678_;
v___y_1661_ = v___y_1679_;
v___y_1662_ = v___y_1680_;
v___y_1663_ = v___y_1682_;
v___y_1664_ = v___y_1681_;
v___y_1665_ = v___y_1684_;
v___y_1666_ = v___y_1683_;
goto v___jp_1649_;
}
}
v___jp_1687_:
{
lean_object* v_declName_x3f_1697_; lean_object* v_macroStack_1698_; uint8_t v_mayPostpone_1699_; uint8_t v_errToSorry_1700_; lean_object* v_autoBoundImplicitContext_1701_; lean_object* v_autoBoundImplicitForbidden_1702_; lean_object* v_sectionVars_1703_; lean_object* v_sectionFVars_1704_; uint8_t v_implicitLambda_1705_; uint8_t v_heedElabAsElim_1706_; uint8_t v_isNoncomputableSection_1707_; uint8_t v_isMetaSection_1708_; uint8_t v_inPattern_1709_; lean_object* v_tacSnap_x3f_1710_; uint8_t v_saveRecAppSyntax_1711_; uint8_t v_holesAsSyntheticOpaque_1712_; uint8_t v_checkDeprecated_1713_; lean_object* v_fixedTermElabs_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___f_1719_; lean_object* v___f_1720_; lean_object* v___f_1721_; lean_object* v___x_1722_; lean_object* v___f_1723_; lean_object* v___f_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; 
v_declName_x3f_1697_ = lean_ctor_get(v___y_1691_, 0);
v_macroStack_1698_ = lean_ctor_get(v___y_1691_, 1);
v_mayPostpone_1699_ = lean_ctor_get_uint8(v___y_1691_, sizeof(void*)*8);
v_errToSorry_1700_ = lean_ctor_get_uint8(v___y_1691_, sizeof(void*)*8 + 1);
v_autoBoundImplicitContext_1701_ = lean_ctor_get(v___y_1691_, 2);
v_autoBoundImplicitForbidden_1702_ = lean_ctor_get(v___y_1691_, 3);
v_sectionVars_1703_ = lean_ctor_get(v___y_1691_, 4);
v_sectionFVars_1704_ = lean_ctor_get(v___y_1691_, 5);
v_implicitLambda_1705_ = lean_ctor_get_uint8(v___y_1691_, sizeof(void*)*8 + 2);
v_heedElabAsElim_1706_ = lean_ctor_get_uint8(v___y_1691_, sizeof(void*)*8 + 3);
v_isNoncomputableSection_1707_ = lean_ctor_get_uint8(v___y_1691_, sizeof(void*)*8 + 4);
v_isMetaSection_1708_ = lean_ctor_get_uint8(v___y_1691_, sizeof(void*)*8 + 5);
v_inPattern_1709_ = lean_ctor_get_uint8(v___y_1691_, sizeof(void*)*8 + 7);
v_tacSnap_x3f_1710_ = lean_ctor_get(v___y_1691_, 6);
v_saveRecAppSyntax_1711_ = lean_ctor_get_uint8(v___y_1691_, sizeof(void*)*8 + 8);
v_holesAsSyntheticOpaque_1712_ = lean_ctor_get_uint8(v___y_1691_, sizeof(void*)*8 + 9);
v_checkDeprecated_1713_ = lean_ctor_get_uint8(v___y_1691_, sizeof(void*)*8 + 10);
v_fixedTermElabs_1714_ = lean_ctor_get(v___y_1691_, 7);
v___x_1715_ = lean_unsigned_to_nat(2u);
v___x_1716_ = l_Lean_Syntax_getArg(v_stx_1354_, v___x_1715_);
v___x_1717_ = lean_box(0);
v___x_1718_ = lean_box(v___x_1353_);
v___f_1719_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__1___boxed), 11, 2);
lean_closure_set(v___f_1719_, 0, v___x_1717_);
lean_closure_set(v___f_1719_, 1, v___x_1718_);
v___f_1720_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__18));
v___f_1721_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__19));
v___x_1722_ = lean_box(v___x_1353_);
lean_inc(v___x_1716_);
v___f_1723_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__4___boxed), 10, 3);
lean_closure_set(v___f_1723_, 0, v___x_1716_);
lean_closure_set(v___f_1723_, 1, v___x_1717_);
lean_closure_set(v___f_1723_, 2, v___x_1722_);
v___f_1724_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__5___boxed), 9, 2);
lean_closure_set(v___f_1724_, 0, v___x_1716_);
lean_closure_set(v___f_1724_, 1, v___f_1723_);
lean_inc_ref(v_fixedTermElabs_1714_);
lean_inc(v_tacSnap_x3f_1710_);
lean_inc(v_sectionFVars_1704_);
lean_inc(v_sectionVars_1703_);
lean_inc_ref(v_autoBoundImplicitForbidden_1702_);
lean_inc(v_autoBoundImplicitContext_1701_);
lean_inc(v_macroStack_1698_);
lean_inc(v_declName_x3f_1697_);
v___x_1725_ = lean_alloc_ctor(0, 8, 11);
lean_ctor_set(v___x_1725_, 0, v_declName_x3f_1697_);
lean_ctor_set(v___x_1725_, 1, v_macroStack_1698_);
lean_ctor_set(v___x_1725_, 2, v_autoBoundImplicitContext_1701_);
lean_ctor_set(v___x_1725_, 3, v_autoBoundImplicitForbidden_1702_);
lean_ctor_set(v___x_1725_, 4, v_sectionVars_1703_);
lean_ctor_set(v___x_1725_, 5, v_sectionFVars_1704_);
lean_ctor_set(v___x_1725_, 6, v_tacSnap_x3f_1710_);
lean_ctor_set(v___x_1725_, 7, v_fixedTermElabs_1714_);
lean_ctor_set_uint8(v___x_1725_, sizeof(void*)*8, v_mayPostpone_1699_);
lean_ctor_set_uint8(v___x_1725_, sizeof(void*)*8 + 1, v_errToSorry_1700_);
lean_ctor_set_uint8(v___x_1725_, sizeof(void*)*8 + 2, v_implicitLambda_1705_);
lean_ctor_set_uint8(v___x_1725_, sizeof(void*)*8 + 3, v_heedElabAsElim_1706_);
lean_ctor_set_uint8(v___x_1725_, sizeof(void*)*8 + 4, v_isNoncomputableSection_1707_);
lean_ctor_set_uint8(v___x_1725_, sizeof(void*)*8 + 5, v_isMetaSection_1708_);
lean_ctor_set_uint8(v___x_1725_, sizeof(void*)*8 + 6, v___x_1353_);
lean_ctor_set_uint8(v___x_1725_, sizeof(void*)*8 + 7, v_inPattern_1709_);
lean_ctor_set_uint8(v___x_1725_, sizeof(void*)*8 + 8, v_saveRecAppSyntax_1711_);
lean_ctor_set_uint8(v___x_1725_, sizeof(void*)*8 + 9, v_holesAsSyntheticOpaque_1712_);
lean_ctor_set_uint8(v___x_1725_, sizeof(void*)*8 + 10, v_checkDeprecated_1713_);
v___x_1726_ = l_Lean_Elab_Term_withoutModifyingElabMetaStateWithInfo___redArg(v___f_1724_, v___x_1725_, v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_);
lean_dec_ref_known(v___x_1725_, 8);
if (lean_obj_tag(v___x_1726_) == 0)
{
lean_object* v_a_1727_; lean_object* v___x_1728_; 
v_a_1727_ = lean_ctor_get(v___x_1726_, 0);
lean_inc(v_a_1727_);
lean_dec_ref_known(v___x_1726_, 1);
v___x_1728_ = l_Lean_Elab_Tactic_Conv_getLhs___redArg(v___y_1690_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_);
if (lean_obj_tag(v___x_1728_) == 0)
{
if (lean_obj_tag(v_occs_1688_) == 0)
{
lean_object* v_a_1729_; lean_object* v___x_1730_; 
lean_dec_ref(v___x_1358_);
lean_dec_ref(v___x_1357_);
lean_dec_ref(v___x_1356_);
lean_dec_ref(v___x_1355_);
v_a_1729_ = lean_ctor_get(v___x_1728_, 0);
lean_inc(v_a_1729_);
lean_dec_ref_known(v___x_1728_, 1);
v___x_1730_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__22));
v___y_1586_ = v___f_1719_;
v___y_1587_ = v___f_1721_;
v___y_1588_ = v_a_1729_;
v___y_1589_ = v___f_1720_;
v___y_1590_ = v_a_1727_;
v_occs_1591_ = v___x_1730_;
v___y_1592_ = v___y_1689_;
v___y_1593_ = v___y_1690_;
v___y_1594_ = v___y_1691_;
v___y_1595_ = v___y_1692_;
v___y_1596_ = v___y_1693_;
v___y_1597_ = v___y_1694_;
v___y_1598_ = v___y_1695_;
v___y_1599_ = v___y_1696_;
goto v___jp_1585_;
}
else
{
lean_object* v_a_1731_; lean_object* v_val_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; uint8_t v___x_1735_; 
v_a_1731_ = lean_ctor_get(v___x_1728_, 0);
lean_inc(v_a_1731_);
lean_dec_ref_known(v___x_1728_, 1);
v_val_1732_ = lean_ctor_get(v_occs_1688_, 0);
lean_inc_n(v_val_1732_, 2);
lean_dec_ref_known(v_occs_1688_, 1);
v___x_1733_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__23));
lean_inc_ref(v___x_1358_);
lean_inc_ref(v___x_1357_);
lean_inc_ref(v___x_1356_);
lean_inc_ref(v___x_1355_);
v___x_1734_ = l_Lean_Name_mkStr5(v___x_1355_, v___x_1356_, v___x_1357_, v___x_1358_, v___x_1733_);
v___x_1735_ = l_Lean_Syntax_isOfKind(v_val_1732_, v___x_1734_);
lean_dec(v___x_1734_);
if (v___x_1735_ == 0)
{
lean_object* v___x_1736_; lean_object* v___x_1737_; uint8_t v___x_1738_; 
v___x_1736_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__24));
v___x_1737_ = l_Lean_Name_mkStr5(v___x_1355_, v___x_1356_, v___x_1357_, v___x_1358_, v___x_1736_);
lean_inc(v_val_1732_);
v___x_1738_ = l_Lean_Syntax_isOfKind(v_val_1732_, v___x_1737_);
lean_dec(v___x_1737_);
if (v___x_1738_ == 0)
{
lean_object* v___x_1739_; lean_object* v_a_1740_; lean_object* v___x_1742_; uint8_t v_isShared_1743_; uint8_t v_isSharedCheck_1747_; 
lean_dec(v_val_1732_);
lean_dec(v_a_1731_);
lean_dec(v_a_1727_);
lean_dec_ref(v___f_1719_);
lean_dec_ref(v___f_1352_);
v___x_1739_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1___redArg();
v_a_1740_ = lean_ctor_get(v___x_1739_, 0);
v_isSharedCheck_1747_ = !lean_is_exclusive(v___x_1739_);
if (v_isSharedCheck_1747_ == 0)
{
v___x_1742_ = v___x_1739_;
v_isShared_1743_ = v_isSharedCheck_1747_;
goto v_resetjp_1741_;
}
else
{
lean_inc(v_a_1740_);
lean_dec(v___x_1739_);
v___x_1742_ = lean_box(0);
v_isShared_1743_ = v_isSharedCheck_1747_;
goto v_resetjp_1741_;
}
v_resetjp_1741_:
{
lean_object* v___x_1745_; 
if (v_isShared_1743_ == 0)
{
v___x_1745_ = v___x_1742_;
goto v_reusejp_1744_;
}
else
{
lean_object* v_reuseFailAlloc_1746_; 
v_reuseFailAlloc_1746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1746_, 0, v_a_1740_);
v___x_1745_ = v_reuseFailAlloc_1746_;
goto v_reusejp_1744_;
}
v_reusejp_1744_:
{
return v___x_1745_;
}
}
}
else
{
lean_object* v___x_1748_; lean_object* v___x_1749_; size_t v_sz_1750_; size_t v___x_1751_; lean_object* v___x_1752_; 
v___x_1748_ = l_Lean_Syntax_getArg(v_val_1732_, v___x_1460_);
lean_dec(v_val_1732_);
v___x_1749_ = l_Lean_Syntax_getArgs(v___x_1748_);
lean_dec(v___x_1748_);
v_sz_1750_ = lean_array_size(v___x_1749_);
v___x_1751_ = ((size_t)0ULL);
v___x_1752_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg(v_sz_1750_, v___x_1751_, v___x_1749_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_);
if (lean_obj_tag(v___x_1752_) == 0)
{
lean_object* v_a_1753_; lean_object* v___x_1754_; uint8_t v___x_1755_; 
v_a_1753_ = lean_ctor_get(v___x_1752_, 0);
lean_inc(v_a_1753_);
lean_dec_ref_known(v___x_1752_, 1);
v___x_1754_ = lean_array_get_size(v_a_1753_);
v___x_1755_ = lean_nat_dec_eq(v___x_1754_, v___x_1460_);
if (v___x_1755_ == 0)
{
lean_object* v___x_1756_; uint8_t v___x_1757_; 
v___x_1756_ = lean_nat_sub(v___x_1754_, v___x_1461_);
v___x_1757_ = lean_nat_dec_le(v___x_1460_, v___x_1756_);
if (v___x_1757_ == 0)
{
lean_inc(v___x_1756_);
v___y_1669_ = v___y_1695_;
v___y_1670_ = v___f_1719_;
v___y_1671_ = v___x_1754_;
v___y_1672_ = v___f_1721_;
v___y_1673_ = v_a_1753_;
v___y_1674_ = v___f_1720_;
v___y_1675_ = v___y_1690_;
v___y_1676_ = v___y_1689_;
v___y_1677_ = v___y_1693_;
v___y_1678_ = v_a_1731_;
v___y_1679_ = v___y_1696_;
v___y_1680_ = v___y_1694_;
v___y_1681_ = v_a_1727_;
v___y_1682_ = v___y_1692_;
v___y_1683_ = v___x_1756_;
v___y_1684_ = v___y_1691_;
v___y_1685_ = v___x_1756_;
goto v___jp_1668_;
}
else
{
v___y_1669_ = v___y_1695_;
v___y_1670_ = v___f_1719_;
v___y_1671_ = v___x_1754_;
v___y_1672_ = v___f_1721_;
v___y_1673_ = v_a_1753_;
v___y_1674_ = v___f_1720_;
v___y_1675_ = v___y_1690_;
v___y_1676_ = v___y_1689_;
v___y_1677_ = v___y_1693_;
v___y_1678_ = v_a_1731_;
v___y_1679_ = v___y_1696_;
v___y_1680_ = v___y_1694_;
v___y_1681_ = v_a_1727_;
v___y_1682_ = v___y_1692_;
v___y_1683_ = v___x_1756_;
v___y_1684_ = v___y_1691_;
v___y_1685_ = v___x_1460_;
goto v___jp_1668_;
}
}
else
{
v___y_1632_ = v___y_1695_;
v___y_1633_ = v___f_1719_;
v___y_1634_ = v___f_1721_;
v___y_1635_ = v___f_1720_;
v___y_1636_ = v___y_1690_;
v___y_1637_ = v___y_1689_;
v___y_1638_ = v___y_1693_;
v___y_1639_ = v_a_1731_;
v___y_1640_ = v___y_1696_;
v___y_1641_ = v___y_1694_;
v___y_1642_ = v_a_1727_;
v___y_1643_ = v___y_1692_;
v___y_1644_ = v___y_1691_;
v___y_1645_ = v_a_1753_;
goto v___jp_1631_;
}
}
else
{
lean_object* v_a_1758_; lean_object* v___x_1760_; uint8_t v_isShared_1761_; uint8_t v_isSharedCheck_1765_; 
lean_dec(v_a_1731_);
lean_dec(v_a_1727_);
lean_dec_ref(v___f_1719_);
lean_dec_ref(v___f_1352_);
v_a_1758_ = lean_ctor_get(v___x_1752_, 0);
v_isSharedCheck_1765_ = !lean_is_exclusive(v___x_1752_);
if (v_isSharedCheck_1765_ == 0)
{
v___x_1760_ = v___x_1752_;
v_isShared_1761_ = v_isSharedCheck_1765_;
goto v_resetjp_1759_;
}
else
{
lean_inc(v_a_1758_);
lean_dec(v___x_1752_);
v___x_1760_ = lean_box(0);
v_isShared_1761_ = v_isSharedCheck_1765_;
goto v_resetjp_1759_;
}
v_resetjp_1759_:
{
lean_object* v___x_1763_; 
if (v_isShared_1761_ == 0)
{
v___x_1763_ = v___x_1760_;
goto v_reusejp_1762_;
}
else
{
lean_object* v_reuseFailAlloc_1764_; 
v_reuseFailAlloc_1764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1764_, 0, v_a_1758_);
v___x_1763_ = v_reuseFailAlloc_1764_;
goto v_reusejp_1762_;
}
v_reusejp_1762_:
{
return v___x_1763_;
}
}
}
}
}
else
{
lean_object* v___x_1766_; 
lean_dec(v_val_1732_);
lean_dec_ref(v___x_1358_);
lean_dec_ref(v___x_1357_);
lean_dec_ref(v___x_1356_);
lean_dec_ref(v___x_1355_);
v___x_1766_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__26));
v___y_1586_ = v___f_1719_;
v___y_1587_ = v___f_1721_;
v___y_1588_ = v_a_1731_;
v___y_1589_ = v___f_1720_;
v___y_1590_ = v_a_1727_;
v_occs_1591_ = v___x_1766_;
v___y_1592_ = v___y_1689_;
v___y_1593_ = v___y_1690_;
v___y_1594_ = v___y_1691_;
v___y_1595_ = v___y_1692_;
v___y_1596_ = v___y_1693_;
v___y_1597_ = v___y_1694_;
v___y_1598_ = v___y_1695_;
v___y_1599_ = v___y_1696_;
goto v___jp_1585_;
}
}
}
else
{
lean_object* v_a_1767_; lean_object* v___x_1769_; uint8_t v_isShared_1770_; uint8_t v_isSharedCheck_1774_; 
lean_dec(v_a_1727_);
lean_dec_ref(v___f_1719_);
lean_dec(v_occs_1688_);
lean_dec_ref(v___x_1358_);
lean_dec_ref(v___x_1357_);
lean_dec_ref(v___x_1356_);
lean_dec_ref(v___x_1355_);
lean_dec_ref(v___f_1352_);
v_a_1767_ = lean_ctor_get(v___x_1728_, 0);
v_isSharedCheck_1774_ = !lean_is_exclusive(v___x_1728_);
if (v_isSharedCheck_1774_ == 0)
{
v___x_1769_ = v___x_1728_;
v_isShared_1770_ = v_isSharedCheck_1774_;
goto v_resetjp_1768_;
}
else
{
lean_inc(v_a_1767_);
lean_dec(v___x_1728_);
v___x_1769_ = lean_box(0);
v_isShared_1770_ = v_isSharedCheck_1774_;
goto v_resetjp_1768_;
}
v_resetjp_1768_:
{
lean_object* v___x_1772_; 
if (v_isShared_1770_ == 0)
{
v___x_1772_ = v___x_1769_;
goto v_reusejp_1771_;
}
else
{
lean_object* v_reuseFailAlloc_1773_; 
v_reuseFailAlloc_1773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1773_, 0, v_a_1767_);
v___x_1772_ = v_reuseFailAlloc_1773_;
goto v_reusejp_1771_;
}
v_reusejp_1771_:
{
return v___x_1772_;
}
}
}
}
else
{
lean_object* v_a_1775_; lean_object* v___x_1777_; uint8_t v_isShared_1778_; uint8_t v_isSharedCheck_1782_; 
lean_dec_ref(v___f_1719_);
lean_dec(v_occs_1688_);
lean_dec_ref(v___x_1358_);
lean_dec_ref(v___x_1357_);
lean_dec_ref(v___x_1356_);
lean_dec_ref(v___x_1355_);
lean_dec_ref(v___f_1352_);
v_a_1775_ = lean_ctor_get(v___x_1726_, 0);
v_isSharedCheck_1782_ = !lean_is_exclusive(v___x_1726_);
if (v_isSharedCheck_1782_ == 0)
{
v___x_1777_ = v___x_1726_;
v_isShared_1778_ = v_isSharedCheck_1782_;
goto v_resetjp_1776_;
}
else
{
lean_inc(v_a_1775_);
lean_dec(v___x_1726_);
v___x_1777_ = lean_box(0);
v_isShared_1778_ = v_isSharedCheck_1782_;
goto v_resetjp_1776_;
}
v_resetjp_1776_:
{
lean_object* v___x_1780_; 
if (v_isShared_1778_ == 0)
{
v___x_1780_ = v___x_1777_;
goto v_reusejp_1779_;
}
else
{
lean_object* v_reuseFailAlloc_1781_; 
v_reuseFailAlloc_1781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1781_, 0, v_a_1775_);
v___x_1780_ = v_reuseFailAlloc_1781_;
goto v_reusejp_1779_;
}
v_reusejp_1779_:
{
return v___x_1780_;
}
}
}
}
}
v___jp_1368_:
{
lean_object* v___x_1379_; 
v___x_1379_ = l_Lean_Elab_Tactic_Conv_getRhs___redArg(v___y_1372_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_);
if (lean_obj_tag(v___x_1379_) == 0)
{
lean_object* v_a_1380_; lean_object* v_expr_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; 
v_a_1380_ = lean_ctor_get(v___x_1379_, 0);
lean_inc(v_a_1380_);
lean_dec_ref_known(v___x_1379_, 1);
v_expr_1381_ = lean_ctor_get(v___y_1369_, 0);
v___x_1382_ = l_Lean_Expr_mvarId_x21(v_a_1380_);
lean_dec(v_a_1380_);
lean_inc_ref(v_expr_1381_);
v___x_1383_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3___redArg(v___x_1382_, v_expr_1381_, v___y_1376_);
lean_dec_ref(v___x_1383_);
v___x_1384_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_1372_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_);
if (lean_obj_tag(v___x_1384_) == 0)
{
lean_object* v_a_1385_; lean_object* v___x_1386_; 
v_a_1385_ = lean_ctor_get(v___x_1384_, 0);
lean_inc(v_a_1385_);
lean_dec_ref_known(v___x_1384_, 1);
v___x_1386_ = l_Lean_Meta_Simp_Result_getProof(v___y_1369_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_);
if (lean_obj_tag(v___x_1386_) == 0)
{
lean_object* v_a_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; 
v_a_1387_ = lean_ctor_get(v___x_1386_, 0);
lean_inc(v_a_1387_);
lean_dec_ref_known(v___x_1386_, 1);
v___x_1388_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3___redArg(v_a_1385_, v_a_1387_, v___y_1376_);
lean_dec_ref(v___x_1388_);
v___x_1389_ = lean_array_to_list(v_subgoals_1370_);
v___x_1390_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_1389_, v___y_1372_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_);
return v___x_1390_;
}
else
{
lean_object* v_a_1391_; lean_object* v___x_1393_; uint8_t v_isShared_1394_; uint8_t v_isSharedCheck_1398_; 
lean_dec(v_a_1385_);
lean_dec_ref(v_subgoals_1370_);
v_a_1391_ = lean_ctor_get(v___x_1386_, 0);
v_isSharedCheck_1398_ = !lean_is_exclusive(v___x_1386_);
if (v_isSharedCheck_1398_ == 0)
{
v___x_1393_ = v___x_1386_;
v_isShared_1394_ = v_isSharedCheck_1398_;
goto v_resetjp_1392_;
}
else
{
lean_inc(v_a_1391_);
lean_dec(v___x_1386_);
v___x_1393_ = lean_box(0);
v_isShared_1394_ = v_isSharedCheck_1398_;
goto v_resetjp_1392_;
}
v_resetjp_1392_:
{
lean_object* v___x_1396_; 
if (v_isShared_1394_ == 0)
{
v___x_1396_ = v___x_1393_;
goto v_reusejp_1395_;
}
else
{
lean_object* v_reuseFailAlloc_1397_; 
v_reuseFailAlloc_1397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1397_, 0, v_a_1391_);
v___x_1396_ = v_reuseFailAlloc_1397_;
goto v_reusejp_1395_;
}
v_reusejp_1395_:
{
return v___x_1396_;
}
}
}
}
else
{
lean_object* v_a_1399_; lean_object* v___x_1401_; uint8_t v_isShared_1402_; uint8_t v_isSharedCheck_1406_; 
lean_dec_ref(v_subgoals_1370_);
lean_dec_ref(v___y_1369_);
v_a_1399_ = lean_ctor_get(v___x_1384_, 0);
v_isSharedCheck_1406_ = !lean_is_exclusive(v___x_1384_);
if (v_isSharedCheck_1406_ == 0)
{
v___x_1401_ = v___x_1384_;
v_isShared_1402_ = v_isSharedCheck_1406_;
goto v_resetjp_1400_;
}
else
{
lean_inc(v_a_1399_);
lean_dec(v___x_1384_);
v___x_1401_ = lean_box(0);
v_isShared_1402_ = v_isSharedCheck_1406_;
goto v_resetjp_1400_;
}
v_resetjp_1400_:
{
lean_object* v___x_1404_; 
if (v_isShared_1402_ == 0)
{
v___x_1404_ = v___x_1401_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1405_; 
v_reuseFailAlloc_1405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1405_, 0, v_a_1399_);
v___x_1404_ = v_reuseFailAlloc_1405_;
goto v_reusejp_1403_;
}
v_reusejp_1403_:
{
return v___x_1404_;
}
}
}
}
else
{
lean_object* v_a_1407_; lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1414_; 
lean_dec_ref(v_subgoals_1370_);
lean_dec_ref(v___y_1369_);
v_a_1407_ = lean_ctor_get(v___x_1379_, 0);
v_isSharedCheck_1414_ = !lean_is_exclusive(v___x_1379_);
if (v_isSharedCheck_1414_ == 0)
{
v___x_1409_ = v___x_1379_;
v_isShared_1410_ = v_isSharedCheck_1414_;
goto v_resetjp_1408_;
}
else
{
lean_inc(v_a_1407_);
lean_dec(v___x_1379_);
v___x_1409_ = lean_box(0);
v_isShared_1410_ = v_isSharedCheck_1414_;
goto v_resetjp_1408_;
}
v_resetjp_1408_:
{
lean_object* v___x_1412_; 
if (v_isShared_1410_ == 0)
{
v___x_1412_ = v___x_1409_;
goto v_reusejp_1411_;
}
else
{
lean_object* v_reuseFailAlloc_1413_; 
v_reuseFailAlloc_1413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1413_, 0, v_a_1407_);
v___x_1412_ = v_reuseFailAlloc_1413_;
goto v_reusejp_1411_;
}
v_reusejp_1411_:
{
return v___x_1412_;
}
}
}
}
v___jp_1415_:
{
size_t v_sz_1426_; size_t v___x_1427_; lean_object* v___x_1428_; 
v_sz_1426_ = lean_array_size(v___y_1425_);
v___x_1427_ = ((size_t)0ULL);
v___x_1428_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__5(v_sz_1426_, v___x_1427_, v___y_1425_);
v___y_1369_ = v___y_1419_;
v_subgoals_1370_ = v___x_1428_;
v___y_1371_ = v___y_1424_;
v___y_1372_ = v___y_1417_;
v___y_1373_ = v___y_1423_;
v___y_1374_ = v___y_1422_;
v___y_1375_ = v___y_1416_;
v___y_1376_ = v___y_1421_;
v___y_1377_ = v___y_1420_;
v___y_1378_ = v___y_1418_;
goto v___jp_1368_;
}
v___jp_1429_:
{
lean_object* v___x_1443_; 
v___x_1443_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg(v___y_1431_, v___y_1436_, v___y_1435_, v___y_1442_);
lean_dec(v___y_1442_);
lean_dec(v___y_1431_);
v___y_1416_ = v___y_1430_;
v___y_1417_ = v___y_1437_;
v___y_1418_ = v___y_1438_;
v___y_1419_ = v___y_1432_;
v___y_1420_ = v___y_1439_;
v___y_1421_ = v___y_1433_;
v___y_1422_ = v___y_1434_;
v___y_1423_ = v___y_1440_;
v___y_1424_ = v___y_1441_;
v___y_1425_ = v___x_1443_;
goto v___jp_1415_;
}
v___jp_1444_:
{
uint8_t v___x_1458_; 
v___x_1458_ = lean_nat_dec_le(v___y_1457_, v___y_1454_);
if (v___x_1458_ == 0)
{
lean_dec(v___y_1454_);
lean_inc(v___y_1457_);
v___y_1430_ = v___y_1445_;
v___y_1431_ = v___y_1446_;
v___y_1432_ = v___y_1447_;
v___y_1433_ = v___y_1448_;
v___y_1434_ = v___y_1449_;
v___y_1435_ = v___y_1457_;
v___y_1436_ = v___y_1450_;
v___y_1437_ = v___y_1451_;
v___y_1438_ = v___y_1452_;
v___y_1439_ = v___y_1453_;
v___y_1440_ = v___y_1455_;
v___y_1441_ = v___y_1456_;
v___y_1442_ = v___y_1457_;
goto v___jp_1429_;
}
else
{
v___y_1430_ = v___y_1445_;
v___y_1431_ = v___y_1446_;
v___y_1432_ = v___y_1447_;
v___y_1433_ = v___y_1448_;
v___y_1434_ = v___y_1449_;
v___y_1435_ = v___y_1457_;
v___y_1436_ = v___y_1450_;
v___y_1437_ = v___y_1451_;
v___y_1438_ = v___y_1452_;
v___y_1439_ = v___y_1453_;
v___y_1440_ = v___y_1455_;
v___y_1441_ = v___y_1456_;
v___y_1442_ = v___y_1454_;
goto v___jp_1429_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___boxed(lean_object** _args){
lean_object* v___x_1796_ = _args[0];
lean_object* v___f_1797_ = _args[1];
lean_object* v___x_1798_ = _args[2];
lean_object* v_stx_1799_ = _args[3];
lean_object* v___x_1800_ = _args[4];
lean_object* v___x_1801_ = _args[5];
lean_object* v___x_1802_ = _args[6];
lean_object* v___x_1803_ = _args[7];
lean_object* v___y_1804_ = _args[8];
lean_object* v___y_1805_ = _args[9];
lean_object* v___y_1806_ = _args[10];
lean_object* v___y_1807_ = _args[11];
lean_object* v___y_1808_ = _args[12];
lean_object* v___y_1809_ = _args[13];
lean_object* v___y_1810_ = _args[14];
lean_object* v___y_1811_ = _args[15];
lean_object* v___y_1812_ = _args[16];
_start:
{
uint8_t v___x_16382__boxed_1813_; uint8_t v___x_16384__boxed_1814_; lean_object* v_res_1815_; 
v___x_16382__boxed_1813_ = lean_unbox(v___x_1796_);
v___x_16384__boxed_1814_ = lean_unbox(v___x_1798_);
v_res_1815_ = l_Lean_Elab_Tactic_Conv_evalPattern___lam__6(v___x_16382__boxed_1813_, v___f_1797_, v___x_16384__boxed_1814_, v_stx_1799_, v___x_1800_, v___x_1801_, v___x_1802_, v___x_1803_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_);
lean_dec(v___y_1811_);
lean_dec_ref(v___y_1810_);
lean_dec(v___y_1809_);
lean_dec_ref(v___y_1808_);
lean_dec(v___y_1807_);
lean_dec_ref(v___y_1806_);
lean_dec(v___y_1805_);
lean_dec_ref(v___y_1804_);
lean_dec(v_stx_1799_);
return v_res_1815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern(lean_object* v_stx_1828_, lean_object* v_a_1829_, lean_object* v_a_1830_, lean_object* v_a_1831_, lean_object* v_a_1832_, lean_object* v_a_1833_, lean_object* v_a_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_){
_start:
{
lean_object* v___f_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; uint8_t v___x_1844_; uint8_t v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___y_1848_; lean_object* v___x_1849_; 
v___f_1838_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___closed__0));
v___x_1839_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___closed__1));
v___x_1840_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___closed__2));
v___x_1841_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___closed__3));
v___x_1842_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___closed__4));
v___x_1843_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___closed__6));
lean_inc(v_stx_1828_);
v___x_1844_ = l_Lean_Syntax_isOfKind(v_stx_1828_, v___x_1843_);
v___x_1845_ = 1;
v___x_1846_ = lean_box(v___x_1844_);
v___x_1847_ = lean_box(v___x_1845_);
v___y_1848_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___boxed), 17, 8);
lean_closure_set(v___y_1848_, 0, v___x_1846_);
lean_closure_set(v___y_1848_, 1, v___f_1838_);
lean_closure_set(v___y_1848_, 2, v___x_1847_);
lean_closure_set(v___y_1848_, 3, v_stx_1828_);
lean_closure_set(v___y_1848_, 4, v___x_1839_);
lean_closure_set(v___y_1848_, 5, v___x_1840_);
lean_closure_set(v___y_1848_, 6, v___x_1841_);
lean_closure_set(v___y_1848_, 7, v___x_1842_);
v___x_1849_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___y_1848_, v_a_1829_, v_a_1830_, v_a_1831_, v_a_1832_, v_a_1833_, v_a_1834_, v_a_1835_, v_a_1836_);
return v___x_1849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___boxed(lean_object* v_stx_1850_, lean_object* v_a_1851_, lean_object* v_a_1852_, lean_object* v_a_1853_, lean_object* v_a_1854_, lean_object* v_a_1855_, lean_object* v_a_1856_, lean_object* v_a_1857_, lean_object* v_a_1858_, lean_object* v_a_1859_){
_start:
{
lean_object* v_res_1860_; 
v_res_1860_ = l_Lean_Elab_Tactic_Conv_evalPattern(v_stx_1850_, v_a_1851_, v_a_1852_, v_a_1853_, v_a_1854_, v_a_1855_, v_a_1856_, v_a_1857_, v_a_1858_);
lean_dec(v_a_1858_);
lean_dec_ref(v_a_1857_);
lean_dec(v_a_1856_);
lean_dec_ref(v_a_1855_);
lean_dec(v_a_1854_);
lean_dec_ref(v_a_1853_);
lean_dec(v_a_1852_);
lean_dec_ref(v_a_1851_);
return v_res_1860_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0(lean_object* v_00_u03b1_1861_, lean_object* v_ref_1862_, lean_object* v_msg_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_){
_start:
{
lean_object* v___x_1873_; 
v___x_1873_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg(v_ref_1862_, v_msg_1863_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_);
return v___x_1873_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___boxed(lean_object* v_00_u03b1_1874_, lean_object* v_ref_1875_, lean_object* v_msg_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_){
_start:
{
lean_object* v_res_1886_; 
v_res_1886_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0(v_00_u03b1_1874_, v_ref_1875_, v_msg_1876_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_);
lean_dec(v___y_1884_);
lean_dec_ref(v___y_1883_);
lean_dec(v___y_1882_);
lean_dec_ref(v___y_1881_);
lean_dec(v___y_1880_);
lean_dec_ref(v___y_1879_);
lean_dec(v___y_1878_);
lean_dec_ref(v___y_1877_);
lean_dec(v_ref_1875_);
return v_res_1886_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3(lean_object* v_mvarId_1887_, lean_object* v_val_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_){
_start:
{
lean_object* v___x_1898_; 
v___x_1898_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3___redArg(v_mvarId_1887_, v_val_1888_, v___y_1894_);
return v___x_1898_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3___boxed(lean_object* v_mvarId_1899_, lean_object* v_val_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_){
_start:
{
lean_object* v_res_1910_; 
v_res_1910_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3(v_mvarId_1899_, v_val_1900_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_);
lean_dec(v___y_1908_);
lean_dec_ref(v___y_1907_);
lean_dec(v___y_1906_);
lean_dec_ref(v___y_1905_);
lean_dec(v___y_1904_);
lean_dec_ref(v___y_1903_);
lean_dec(v___y_1902_);
lean_dec_ref(v___y_1901_);
return v_res_1910_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4(lean_object* v_00_u03b1_1911_, lean_object* v_msg_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_){
_start:
{
lean_object* v___x_1922_; 
v___x_1922_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg(v_msg_1912_, v___y_1917_, v___y_1918_, v___y_1919_, v___y_1920_);
return v___x_1922_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___boxed(lean_object* v_00_u03b1_1923_, lean_object* v_msg_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_){
_start:
{
lean_object* v_res_1934_; 
v_res_1934_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4(v_00_u03b1_1923_, v_msg_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_);
lean_dec(v___y_1932_);
lean_dec_ref(v___y_1931_);
lean_dec(v___y_1930_);
lean_dec_ref(v___y_1929_);
lean_dec(v___y_1928_);
lean_dec_ref(v___y_1927_);
lean_dec(v___y_1926_);
lean_dec_ref(v___y_1925_);
return v_res_1934_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6(lean_object* v_n_1935_, lean_object* v_as_1936_, lean_object* v_lo_1937_, lean_object* v_hi_1938_, lean_object* v_w_1939_, lean_object* v_hlo_1940_, lean_object* v_hhi_1941_){
_start:
{
lean_object* v___x_1942_; 
v___x_1942_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg(v_n_1935_, v_as_1936_, v_lo_1937_, v_hi_1938_);
return v___x_1942_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___boxed(lean_object* v_n_1943_, lean_object* v_as_1944_, lean_object* v_lo_1945_, lean_object* v_hi_1946_, lean_object* v_w_1947_, lean_object* v_hlo_1948_, lean_object* v_hhi_1949_){
_start:
{
lean_object* v_res_1950_; 
v_res_1950_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6(v_n_1943_, v_as_1944_, v_lo_1945_, v_hi_1946_, v_w_1947_, v_hlo_1948_, v_hhi_1949_);
lean_dec(v_hi_1946_);
lean_dec(v_n_1943_);
return v_res_1950_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7(lean_object* v_as_1951_, size_t v_sz_1952_, size_t v_i_1953_, lean_object* v_bs_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_){
_start:
{
lean_object* v___x_1964_; 
v___x_1964_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg(v_sz_1952_, v_i_1953_, v_bs_1954_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_);
return v___x_1964_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___boxed(lean_object* v_as_1965_, lean_object* v_sz_1966_, lean_object* v_i_1967_, lean_object* v_bs_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_){
_start:
{
size_t v_sz_boxed_1978_; size_t v_i_boxed_1979_; lean_object* v_res_1980_; 
v_sz_boxed_1978_ = lean_unbox_usize(v_sz_1966_);
lean_dec(v_sz_1966_);
v_i_boxed_1979_ = lean_unbox_usize(v_i_1967_);
lean_dec(v_i_1967_);
v_res_1980_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7(v_as_1965_, v_sz_boxed_1978_, v_i_boxed_1979_, v_bs_1968_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_);
lean_dec(v___y_1976_);
lean_dec_ref(v___y_1975_);
lean_dec(v___y_1974_);
lean_dec_ref(v___y_1973_);
lean_dec(v___y_1972_);
lean_dec_ref(v___y_1971_);
lean_dec(v___y_1970_);
lean_dec_ref(v___y_1969_);
lean_dec_ref(v_as_1965_);
return v_res_1980_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9(lean_object* v_n_1981_, lean_object* v_as_1982_, lean_object* v_lo_1983_, lean_object* v_hi_1984_, lean_object* v_w_1985_, lean_object* v_hlo_1986_, lean_object* v_hhi_1987_){
_start:
{
lean_object* v___x_1988_; 
v___x_1988_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg(v_n_1981_, v_as_1982_, v_lo_1983_, v_hi_1984_);
return v___x_1988_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___boxed(lean_object* v_n_1989_, lean_object* v_as_1990_, lean_object* v_lo_1991_, lean_object* v_hi_1992_, lean_object* v_w_1993_, lean_object* v_hlo_1994_, lean_object* v_hhi_1995_){
_start:
{
lean_object* v_res_1996_; 
v_res_1996_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9(v_n_1989_, v_as_1990_, v_lo_1991_, v_hi_1992_, v_w_1993_, v_hlo_1994_, v_hhi_1995_);
lean_dec(v_hi_1992_);
lean_dec(v_n_1989_);
return v_res_1996_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3(lean_object* v_00_u03b2_1997_, lean_object* v_x_1998_, lean_object* v_x_1999_, lean_object* v_x_2000_){
_start:
{
lean_object* v___x_2001_; 
v___x_2001_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3___redArg(v_x_1998_, v_x_1999_, v_x_2000_);
return v___x_2001_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6_spec__8(lean_object* v_n_2002_, lean_object* v_lo_2003_, lean_object* v_hi_2004_, lean_object* v_hhi_2005_, lean_object* v_pivot_2006_, lean_object* v_as_2007_, lean_object* v_i_2008_, lean_object* v_k_2009_, lean_object* v_ilo_2010_, lean_object* v_ik_2011_, lean_object* v_w_2012_){
_start:
{
lean_object* v___x_2013_; 
v___x_2013_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6_spec__8___redArg(v_hi_2004_, v_pivot_2006_, v_as_2007_, v_i_2008_, v_k_2009_);
return v___x_2013_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6_spec__8___boxed(lean_object* v_n_2014_, lean_object* v_lo_2015_, lean_object* v_hi_2016_, lean_object* v_hhi_2017_, lean_object* v_pivot_2018_, lean_object* v_as_2019_, lean_object* v_i_2020_, lean_object* v_k_2021_, lean_object* v_ilo_2022_, lean_object* v_ik_2023_, lean_object* v_w_2024_){
_start:
{
lean_object* v_res_2025_; 
v_res_2025_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6_spec__8(v_n_2014_, v_lo_2015_, v_hi_2016_, v_hhi_2017_, v_pivot_2018_, v_as_2019_, v_i_2020_, v_k_2021_, v_ilo_2022_, v_ik_2023_, v_w_2024_);
lean_dec_ref(v_pivot_2018_);
lean_dec(v_hi_2016_);
lean_dec(v_lo_2015_);
lean_dec(v_n_2014_);
return v_res_2025_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9_spec__13(lean_object* v_n_2026_, lean_object* v_lo_2027_, lean_object* v_hi_2028_, lean_object* v_hhi_2029_, lean_object* v_pivot_2030_, lean_object* v_as_2031_, lean_object* v_i_2032_, lean_object* v_k_2033_, lean_object* v_ilo_2034_, lean_object* v_ik_2035_, lean_object* v_w_2036_){
_start:
{
lean_object* v___x_2037_; 
v___x_2037_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9_spec__13___redArg(v_hi_2028_, v_pivot_2030_, v_as_2031_, v_i_2032_, v_k_2033_);
return v___x_2037_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9_spec__13___boxed(lean_object* v_n_2038_, lean_object* v_lo_2039_, lean_object* v_hi_2040_, lean_object* v_hhi_2041_, lean_object* v_pivot_2042_, lean_object* v_as_2043_, lean_object* v_i_2044_, lean_object* v_k_2045_, lean_object* v_ilo_2046_, lean_object* v_ik_2047_, lean_object* v_w_2048_){
_start:
{
lean_object* v_res_2049_; 
v_res_2049_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9_spec__13(v_n_2038_, v_lo_2039_, v_hi_2040_, v_hhi_2041_, v_pivot_2042_, v_as_2043_, v_i_2044_, v_k_2045_, v_ilo_2046_, v_ik_2047_, v_w_2048_);
lean_dec_ref(v_pivot_2042_);
lean_dec(v_hi_2040_);
lean_dec(v_lo_2039_);
lean_dec(v_n_2038_);
return v_res_2049_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4(lean_object* v_00_u03b2_2050_, lean_object* v_x_2051_, size_t v_x_2052_, size_t v_x_2053_, lean_object* v_x_2054_, lean_object* v_x_2055_){
_start:
{
lean_object* v___x_2056_; 
v___x_2056_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg(v_x_2051_, v_x_2052_, v_x_2053_, v_x_2054_, v_x_2055_);
return v___x_2056_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___boxed(lean_object* v_00_u03b2_2057_, lean_object* v_x_2058_, lean_object* v_x_2059_, lean_object* v_x_2060_, lean_object* v_x_2061_, lean_object* v_x_2062_){
_start:
{
size_t v_x_17500__boxed_2063_; size_t v_x_17501__boxed_2064_; lean_object* v_res_2065_; 
v_x_17500__boxed_2063_ = lean_unbox_usize(v_x_2059_);
lean_dec(v_x_2059_);
v_x_17501__boxed_2064_ = lean_unbox_usize(v_x_2060_);
lean_dec(v_x_2060_);
v_res_2065_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4(v_00_u03b2_2057_, v_x_2058_, v_x_17500__boxed_2063_, v_x_17501__boxed_2064_, v_x_2061_, v_x_2062_);
return v_res_2065_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11_spec__13(lean_object* v_as_2066_, lean_object* v_a_2067_, lean_object* v_x_2068_, lean_object* v_x_2069_){
_start:
{
uint8_t v___x_2070_; 
v___x_2070_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11_spec__13___redArg(v_as_2066_, v_a_2067_, v_x_2068_);
return v___x_2070_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11_spec__13___boxed(lean_object* v_as_2071_, lean_object* v_a_2072_, lean_object* v_x_2073_, lean_object* v_x_2074_){
_start:
{
uint8_t v_res_2075_; lean_object* v_r_2076_; 
v_res_2075_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11_spec__13(v_as_2071_, v_a_2072_, v_x_2073_, v_x_2074_);
lean_dec_ref(v_a_2072_);
lean_dec_ref(v_as_2071_);
v_r_2076_ = lean_box(v_res_2075_);
return v_r_2076_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__12(lean_object* v_00_u03b2_2077_, lean_object* v_n_2078_, lean_object* v_k_2079_, lean_object* v_v_2080_){
_start:
{
lean_object* v___x_2081_; 
v___x_2081_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__12___redArg(v_n_2078_, v_k_2079_, v_v_2080_);
return v___x_2081_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__13(lean_object* v_00_u03b2_2082_, size_t v_depth_2083_, lean_object* v_keys_2084_, lean_object* v_vals_2085_, lean_object* v_heq_2086_, lean_object* v_i_2087_, lean_object* v_entries_2088_){
_start:
{
lean_object* v___x_2089_; 
v___x_2089_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__13___redArg(v_depth_2083_, v_keys_2084_, v_vals_2085_, v_i_2087_, v_entries_2088_);
return v___x_2089_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__13___boxed(lean_object* v_00_u03b2_2090_, lean_object* v_depth_2091_, lean_object* v_keys_2092_, lean_object* v_vals_2093_, lean_object* v_heq_2094_, lean_object* v_i_2095_, lean_object* v_entries_2096_){
_start:
{
size_t v_depth_boxed_2097_; lean_object* v_res_2098_; 
v_depth_boxed_2097_ = lean_unbox_usize(v_depth_2091_);
lean_dec(v_depth_2091_);
v_res_2098_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__13(v_00_u03b2_2090_, v_depth_boxed_2097_, v_keys_2092_, v_vals_2093_, v_heq_2094_, v_i_2095_, v_entries_2096_);
lean_dec_ref(v_vals_2093_);
lean_dec_ref(v_keys_2092_);
return v_res_2098_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__12_spec__16(lean_object* v_00_u03b2_2099_, lean_object* v_x_2100_, lean_object* v_x_2101_, lean_object* v_x_2102_, lean_object* v_x_2103_){
_start:
{
lean_object* v___x_2104_; 
v___x_2104_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__12_spec__16___redArg(v_x_2100_, v_x_2101_, v_x_2102_, v_x_2103_);
return v___x_2104_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1(){
_start:
{
lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; 
v___x_2114_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2115_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalPattern___closed__6));
v___x_2116_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___closed__2));
v___x_2117_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalPattern___boxed), 10, 0);
v___x_2118_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2114_, v___x_2115_, v___x_2116_, v___x_2117_);
return v___x_2118_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___boxed(lean_object* v_a_2119_){
_start:
{
lean_object* v_res_2120_; 
v_res_2120_ = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1();
return v_res_2120_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3(){
_start:
{
lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; 
v___x_2147_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___closed__2));
v___x_2148_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__6));
v___x_2149_ = l_Lean_addBuiltinDeclarationRanges(v___x_2147_, v___x_2148_);
return v___x_2149_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___boxed(lean_object* v_a_2150_){
_start:
{
lean_object* v_res_2151_; 
v_res_2151_ = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3();
return v_res_2151_;
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
