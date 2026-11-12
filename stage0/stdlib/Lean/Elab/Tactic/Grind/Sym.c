// Lean compiler output
// Module: Lean.Elab.Tactic.Grind.Sym
// Imports: import Lean.Elab.Tactic.Grind.Basic import Lean.Elab.Tactic.Grind.SimprocDSL import Lean.Meta.Sym.Grind import Lean.Meta.Sym.Simp.Variant import Lean.Meta.Sym.Simp.Rewrite import Lean.Meta.Sym.Simp.EvalGround import Lean.Meta.Sym.Simp.Goal import Lean.Meta.Sym.Simp.Attr import Lean.Meta.Sym.Simp.ControlFlow import Lean.Meta.Sym.Simp.Forall import Lean.Meta.Tactic.Apply import Lean.Elab.Tactic.Location import Lean.Elab.SyntheticMVars
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
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint64_t l_Lean_Elab_Tactic_Grind_instHashableSimpCacheKey_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Lean_Elab_Tactic_Grind_instBEqSimpCacheKey_beq(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_ensureSym___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
extern lean_object* l_Lean_Meta_tactic_hygienic;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_intros___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_liftSymM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_Meta_Grind_Goal_internalizeAll___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_getSymSimpVariant_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_elabSymSimproc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_elabSymDischarger(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_dischargeNone___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Meta_Sym_Simp_Theorems_insert(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_Theorems_rewrite(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_Result_withContextDependent(lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_mkEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_mkSymSimpDischarger___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_simp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_simpArrowTelescope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_simpControl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_getSymSimpTheorems___redArg(lean_object*);
lean_object* l___private_Lean_Meta_Sym_Simp_EvalGround_0__Lean_Meta_Sym_Simp_evalGroundCore___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_SimpM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* l_Lean_LocalContext_findFromUserName_x3f(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_mkTheoremFromExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_realizeGlobalConstNoOverload(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_mkTheoremsFromDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Environment_findAsync_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_AsyncConstantInfo_toConstantInfo(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO___redArg();
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_instMonadTermElabM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_instMonadTermElabM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_instMonadGrindTacticM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_instMonadGrindTacticM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Linter_checkDeprecatedAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Elab_Tactic_Grind_withMainContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVars(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_mkBackwardRuleFromExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_internalize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_toNat(lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_apply___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_byContra_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_intro1Core(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_exfalso(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFalse(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_saveState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_SavedState_restore___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_mkBackwardRuleFromDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshBinderNameForTactic___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_introN___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__1___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__1___redArg___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "binderIdent"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__1___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__1___redArg___closed__1_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__1___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__1___redArg___closed__2_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(37, 194, 68, 106, 254, 181, 31, 191)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__1___redArg___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__1___redArg___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__1___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "h"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__1___redArg___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__1___redArg___closed__3_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__1___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__1___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(176, 181, 207, 77, 197, 87, 68, 121)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__1___redArg___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__1___redArg___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__1___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__1___redArg___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__1___redArg___closed__5_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__1___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__1___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__1___redArg___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__1___redArg___closed__6_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__1___redArg(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "`intro` failed"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore___closed__1;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "`intro` failed, no binders to introduce"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "symIntro"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___closed__4_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___closed__2_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___closed__4_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___closed__3_value),LEAN_SCALAR_PTR_LITERAL(29, 177, 203, 220, 6, 189, 203, 250)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___closed__4_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "token"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___closed__5_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___closed__6_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___closed__5_value),LEAN_SCALAR_PTR_LITERAL(89, 149, 26, 37, 31, 104, 89, 130)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___closed__6_value),LEAN_SCALAR_PTR_LITERAL(234, 149, 90, 50, 108, 230, 18, 172)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___closed__7_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___closed__8_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___closed__5_value),LEAN_SCALAR_PTR_LITERAL(89, 149, 26, 37, 31, 104, 89, 130)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___closed__9_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___closed__8_value),LEAN_SCALAR_PTR_LITERAL(97, 134, 219, 90, 90, 45, 96, 32)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___closed__9 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___closed__9_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro__1___closed__1_value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro__1___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro__1___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro__1___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(216, 59, 67, 7, 118, 215, 141, 75)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro__1___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro__1___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro__1___closed__4_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 58, 227, 168, 195, 28, 19, 75)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro__1___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro__1___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro__1___closed__5_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___closed__2_value),LEAN_SCALAR_PTR_LITERAL(243, 88, 6, 248, 93, 59, 25, 68)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro__1___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro__1___closed__6_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Sym"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro__1___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro__1___closed__7_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro__1___closed__6_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(14, 249, 158, 186, 145, 195, 187, 23)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro__1___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro__1___closed__8_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro__1___closed__8_value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(55, 189, 172, 192, 50, 135, 68, 111)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro__1___closed__9 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro__1___closed__9_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro__1___closed__9_value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(202, 134, 96, 207, 7, 76, 78, 141)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro__1___closed__10 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro__1___closed__10_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro__1___closed__10_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(8, 233, 248, 222, 11, 248, 200, 242)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro__1___closed__11 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro__1___closed__11_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro__1___closed__11_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___closed__1_value),LEAN_SCALAR_PTR_LITERAL(245, 106, 116, 218, 92, 67, 38, 89)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro__1___closed__12 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro__1___closed__12_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro__1___closed__12_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___closed__2_value),LEAN_SCALAR_PTR_LITERAL(99, 106, 132, 22, 50, 105, 182, 49)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro__1___closed__13 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro__1___closed__13_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "evalSymIntro"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro__1___closed__14 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro__1___closed__14_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro__1___closed__13_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(80, 149, 109, 100, 17, 3, 240, 42)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro__1___closed__15 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro__1___closed__15_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro__1___boxed(lean_object*);
static const lean_array_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntrosCore___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntrosCore___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntrosCore___redArg___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntrosCore___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "`intros` failed"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntrosCore___redArg___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntrosCore___redArg___closed__1_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntrosCore___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntrosCore___redArg___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntrosCore___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntrosCore___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntrosCore(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntrosCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntros___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "symIntros"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntros___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntros___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntros___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntros___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntros___redArg___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntros___redArg___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntros___redArg___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntros___redArg___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntros___redArg___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___closed__2_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntros___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntros___redArg___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntros___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(51, 175, 114, 140, 112, 61, 143, 32)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntros___redArg___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntros___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntros___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntros___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntros(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntros___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntros___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntros__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "evalSymIntros"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntros___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntros__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntros___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntros__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntros___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntros__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro__1___closed__13_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntros___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntros__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(11, 50, 79, 89, 204, 3, 67, 70)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntros___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntros__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntros___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntros__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntros___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntros__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntros___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntros__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2_spec__5___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2_spec__5(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm___lam__0(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3_spec__5_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3_spec__6___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3_spec__6(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "`apply` failed, rule is not applicable"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___lam__0___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___lam__0___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___lam__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "symApply"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___closed__2_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___closed__0_value),LEAN_SCALAR_PTR_LITERAL(79, 244, 96, 104, 113, 83, 151, 74)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "evalSymApply"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro__1___closed__13_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 76, 198, 160, 61, 155, 125, 159)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "symInternalize"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___closed__2_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(249, 99, 88, 106, 108, 255, 121, 14)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "evalSymInternalize"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro__1___closed__13_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(28, 80, 70, 92, 195, 181, 237, 108)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "symInternalizeAll"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___closed__2_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 177, 44, 29, 183, 33, 46, 54)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "evalSymInternalizeAll"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro__1___closed__13_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(155, 156, 163, 183, 131, 232, 47, 217)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll__1___boxed(lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "`by_contra` failed"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___redArg___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___redArg___closed__1;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "`by_contra` failed, target is already `False`"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___redArg___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___redArg___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___redArg___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "symByContra"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___closed__2_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 214, 28, 119, 209, 102, 217, 193)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "evalSymByContra"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro__1___closed__13_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(201, 178, 189, 218, 163, 141, 72, 213)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_trivialSimproc___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_trivialSimproc___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_trivialSimproc___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_trivialSimproc___redArg();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_trivialSimproc___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_trivialSimproc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_trivialSimproc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabOptSimproc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabOptSimproc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabOptDischarger___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_Simp_dischargeNone___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabOptDischarger___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabOptDischarger___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabOptDischarger(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabOptDischarger___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__0_spec__0___closed__0;
static const lean_closure_object l_panic___at___00Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__0_spec__0___closed__1 = (const lean_object*)&l_panic___at___00Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__0_spec__0___closed__1_value;
static const lean_closure_object l_panic___at___00Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__0_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__0_spec__0___closed__2 = (const lean_object*)&l_panic___at___00Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__0_spec__0___closed__2_value;
static const lean_closure_object l_panic___at___00Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__0_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__0_spec__0___closed__3 = (const lean_object*)&l_panic___at___00Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__0_spec__0___closed__3_value;
static const lean_closure_object l_panic___at___00Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__0_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__0_spec__0___closed__4 = (const lean_object*)&l_panic___at___00Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__0_spec__0___closed__4_value;
static const lean_closure_object l_panic___at___00Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__0_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Term_instMonadTermElabM___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__0_spec__0___closed__5 = (const lean_object*)&l_panic___at___00Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__0_spec__0___closed__5_value;
static const lean_closure_object l_panic___at___00Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__0_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Term_instMonadTermElabM___lam__1___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__0_spec__0___closed__6 = (const lean_object*)&l_panic___at___00Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__0_spec__0___closed__6_value;
static const lean_closure_object l_panic___at___00Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__0_spec__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Grind_instMonadGrindTacticM___lam__0___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__0_spec__0___closed__7 = (const lean_object*)&l_panic___at___00Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__0_spec__0___closed__7_value;
static const lean_closure_object l_panic___at___00Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__0_spec__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Grind_instMonadGrindTacticM___lam__1___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__0_spec__0___closed__8 = (const lean_object*)&l_panic___at___00Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__0_spec__0___closed__8_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Lean.MonadEnv"};
static const lean_object* l_Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__0___closed__0 = (const lean_object*)&l_Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__0___closed__0_value;
static const lean_string_object l_Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Lean.isDefn\?"};
static const lean_object* l_Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__0___closed__1 = (const lean_object*)&l_Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__0___closed__1_value;
static const lean_string_object l_Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__0___closed__2 = (const lean_object*)&l_Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__0___closed__2_value;
static lean_once_cell_t l_Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems___closed__0_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems___closed__0_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___closed__0;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___closed__1;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkSimpDefaultMethods___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_Simp_simp___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkSimpDefaultMethods___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkSimpDefaultMethods___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkSimpDefaultMethods___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkSimpDefaultMethods___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkSimpDefaultMethods___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkSimpDefaultMethods___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkSimpDefaultMethods___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkSimpDefaultMethods___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkSimpDefaultMethods___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkSimpDefaultMethods___lam__0___boxed, .m_arity = 12, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkSimpDefaultMethods___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkSimpDefaultMethods___closed__0_value;
static const lean_closure_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkSimpDefaultMethods___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkSimpDefaultMethods___lam__1___boxed, .m_arity = 12, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkSimpDefaultMethods___closed__0_value)} };
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkSimpDefaultMethods___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkSimpDefaultMethods___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkSimpDefaultMethods___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(255) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkSimpDefaultMethods___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkSimpDefaultMethods___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkSimpDefaultMethods(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkSimpDefaultMethods___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_defaultDischargerConfig(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkDefaultDischarger___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkDefaultDischarger___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkDefaultDischarger(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkDefaultDischarger___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabSimpVariant___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "unknown Sym.simp variant `"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabSimpVariant___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabSimpVariant___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabSimpVariant___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabSimpVariant___closed__1;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabSimpVariant___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabSimpVariant___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabSimpVariant___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabSimpVariant___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabSimpVariant___closed__3;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabSimpVariant___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(100000) << 1) | 1)),((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabSimpVariant___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabSimpVariant___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabSimpVariant(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabSimpVariant___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__2_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__4(uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__2_spec__3_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__2___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__3___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "`Sym.simp` made no progress"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__1;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "symSimp"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___closed__2_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__3_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__2_value),LEAN_SCALAR_PTR_LITERAL(162, 109, 151, 25, 234, 136, 56, 252)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__3_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__4;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__5;
static const lean_array_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__2_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__2_spec__3_spec__7(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "evalSymSimp"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro__1___closed__13_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(171, 49, 43, 242, 120, 141, 167, 110)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp__1___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__0(lean_object* v_opts_1_, lean_object* v_opt_2_){
_start:
{
lean_object* v_name_3_; lean_object* v_defValue_4_; lean_object* v_map_5_; lean_object* v___x_6_; 
v_name_3_ = lean_ctor_get(v_opt_2_, 0);
v_defValue_4_ = lean_ctor_get(v_opt_2_, 1);
v_map_5_ = lean_ctor_get(v_opts_1_, 0);
v___x_6_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_5_, v_name_3_);
if (lean_obj_tag(v___x_6_) == 0)
{
uint8_t v___x_7_; 
v___x_7_ = lean_unbox(v_defValue_4_);
return v___x_7_;
}
else
{
lean_object* v_val_8_; 
v_val_8_ = lean_ctor_get(v___x_6_, 0);
lean_inc(v_val_8_);
lean_dec_ref_known(v___x_6_, 1);
if (lean_obj_tag(v_val_8_) == 1)
{
uint8_t v_v_9_; 
v_v_9_ = lean_ctor_get_uint8(v_val_8_, 0);
lean_dec_ref_known(v_val_8_, 0);
return v_v_9_;
}
else
{
uint8_t v___x_10_; 
lean_dec(v_val_8_);
v___x_10_ = lean_unbox(v_defValue_4_);
return v___x_10_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__0___boxed(lean_object* v_opts_11_, lean_object* v_opt_12_){
_start:
{
uint8_t v_res_13_; lean_object* v_r_14_; 
v_res_13_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__0(v_opts_11_, v_opt_12_);
lean_dec_ref(v_opt_12_);
lean_dec_ref(v_opts_11_);
v_r_14_ = lean_box(v_res_13_);
return v_r_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__2_spec__2(lean_object* v_msgData_15_, lean_object* v___y_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_){
_start:
{
lean_object* v___x_21_; lean_object* v_env_22_; uint8_t v___x_23_; lean_object* v_env_24_; lean_object* v___x_25_; lean_object* v_toCold_26_; lean_object* v_mctx_27_; lean_object* v_lctx_28_; lean_object* v_options_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; 
v___x_21_ = lean_st_ref_get(v___y_19_);
v_env_22_ = lean_ctor_get(v___x_21_, 0);
lean_inc_ref(v_env_22_);
lean_dec(v___x_21_);
v___x_23_ = 0;
v_env_24_ = l_Lean_Environment_setRecordingDeps(v_env_22_, v___x_23_);
v___x_25_ = lean_st_ref_get(v___y_17_);
v_toCold_26_ = lean_ctor_get(v___y_18_, 0);
v_mctx_27_ = lean_ctor_get(v___x_25_, 0);
lean_inc_ref(v_mctx_27_);
lean_dec(v___x_25_);
v_lctx_28_ = lean_ctor_get(v___y_16_, 2);
v_options_29_ = lean_ctor_get(v_toCold_26_, 2);
lean_inc_ref(v_options_29_);
lean_inc_ref(v_lctx_28_);
v___x_30_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_30_, 0, v_env_24_);
lean_ctor_set(v___x_30_, 1, v_mctx_27_);
lean_ctor_set(v___x_30_, 2, v_lctx_28_);
lean_ctor_set(v___x_30_, 3, v_options_29_);
v___x_31_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_31_, 0, v___x_30_);
lean_ctor_set(v___x_31_, 1, v_msgData_15_);
v___x_32_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_32_, 0, v___x_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__2_spec__2___boxed(lean_object* v_msgData_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__2_spec__2(v_msgData_33_, v___y_34_, v___y_35_, v___y_36_, v___y_37_);
lean_dec(v___y_37_);
lean_dec_ref(v___y_36_);
lean_dec(v___y_35_);
lean_dec_ref(v___y_34_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__2___redArg(lean_object* v_msg_40_, lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_){
_start:
{
lean_object* v_ref_46_; lean_object* v___x_47_; lean_object* v_a_48_; lean_object* v___x_50_; uint8_t v_isShared_51_; uint8_t v_isSharedCheck_56_; 
v_ref_46_ = lean_ctor_get(v___y_43_, 2);
v___x_47_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__2_spec__2(v_msg_40_, v___y_41_, v___y_42_, v___y_43_, v___y_44_);
v_a_48_ = lean_ctor_get(v___x_47_, 0);
v_isSharedCheck_56_ = !lean_is_exclusive(v___x_47_);
if (v_isSharedCheck_56_ == 0)
{
v___x_50_ = v___x_47_;
v_isShared_51_ = v_isSharedCheck_56_;
goto v_resetjp_49_;
}
else
{
lean_inc(v_a_48_);
lean_dec(v___x_47_);
v___x_50_ = lean_box(0);
v_isShared_51_ = v_isSharedCheck_56_;
goto v_resetjp_49_;
}
v_resetjp_49_:
{
lean_object* v___x_52_; lean_object* v___x_54_; 
lean_inc(v_ref_46_);
v___x_52_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_52_, 0, v_ref_46_);
lean_ctor_set(v___x_52_, 1, v_a_48_);
if (v_isShared_51_ == 0)
{
lean_ctor_set_tag(v___x_50_, 1);
lean_ctor_set(v___x_50_, 0, v___x_52_);
v___x_54_ = v___x_50_;
goto v_reusejp_53_;
}
else
{
lean_object* v_reuseFailAlloc_55_; 
v_reuseFailAlloc_55_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_55_, 0, v___x_52_);
v___x_54_ = v_reuseFailAlloc_55_;
goto v_reusejp_53_;
}
v_reusejp_53_:
{
return v___x_54_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__2___redArg___boxed(lean_object* v_msg_57_, lean_object* v___y_58_, lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_, lean_object* v___y_62_){
_start:
{
lean_object* v_res_63_; 
v_res_63_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__2___redArg(v_msg_57_, v___y_58_, v___y_59_, v___y_60_, v___y_61_);
lean_dec(v___y_61_);
lean_dec_ref(v___y_60_);
lean_dec(v___y_59_);
lean_dec_ref(v___y_58_);
return v_res_63_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__1___redArg(size_t v_sz_75_, size_t v_i_76_, lean_object* v_bs_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_){
_start:
{
uint8_t v___x_82_; 
v___x_82_ = lean_usize_dec_lt(v_i_76_, v_sz_75_);
if (v___x_82_ == 0)
{
lean_object* v___x_83_; 
v___x_83_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_83_, 0, v_bs_77_);
return v___x_83_;
}
else
{
lean_object* v_v_84_; lean_object* v___x_85_; lean_object* v_bs_x27_86_; lean_object* v_a_88_; lean_object* v___y_94_; lean_object* v___x_104_; uint8_t v___x_105_; 
v_v_84_ = lean_array_uget(v_bs_77_, v_i_76_);
v___x_85_ = lean_unsigned_to_nat(0u);
v_bs_x27_86_ = lean_array_uset(v_bs_77_, v_i_76_, v___x_85_);
v___x_104_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__1___redArg___closed__2));
lean_inc(v_v_84_);
v___x_105_ = l_Lean_Syntax_isOfKind(v_v_84_, v___x_104_);
if (v___x_105_ == 0)
{
lean_object* v___x_106_; lean_object* v___x_107_; 
lean_dec(v_v_84_);
v___x_106_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__1___redArg___closed__4));
v___x_107_ = l_Lean_Meta_mkFreshBinderNameForTactic___redArg(v___x_106_, v___y_78_, v___y_79_, v___y_80_);
v___y_94_ = v___x_107_;
goto v___jp_93_;
}
else
{
lean_object* v___x_108_; lean_object* v___x_109_; uint8_t v___x_110_; 
v___x_108_ = l_Lean_Syntax_getArg(v_v_84_, v___x_85_);
lean_dec(v_v_84_);
v___x_109_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__1___redArg___closed__6));
lean_inc(v___x_108_);
v___x_110_ = l_Lean_Syntax_isOfKind(v___x_108_, v___x_109_);
if (v___x_110_ == 0)
{
lean_object* v___x_111_; lean_object* v___x_112_; 
lean_dec(v___x_108_);
v___x_111_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__1___redArg___closed__4));
v___x_112_ = l_Lean_Meta_mkFreshBinderNameForTactic___redArg(v___x_111_, v___y_78_, v___y_79_, v___y_80_);
v___y_94_ = v___x_112_;
goto v___jp_93_;
}
else
{
lean_object* v___x_113_; 
v___x_113_ = l_Lean_TSyntax_getId(v___x_108_);
lean_dec(v___x_108_);
v_a_88_ = v___x_113_;
goto v___jp_87_;
}
}
v___jp_87_:
{
size_t v___x_89_; size_t v___x_90_; lean_object* v___x_91_; 
v___x_89_ = ((size_t)1ULL);
v___x_90_ = lean_usize_add(v_i_76_, v___x_89_);
v___x_91_ = lean_array_uset(v_bs_x27_86_, v_i_76_, v_a_88_);
v_i_76_ = v___x_90_;
v_bs_77_ = v___x_91_;
goto _start;
}
v___jp_93_:
{
if (lean_obj_tag(v___y_94_) == 0)
{
lean_object* v_a_95_; 
v_a_95_ = lean_ctor_get(v___y_94_, 0);
lean_inc(v_a_95_);
lean_dec_ref_known(v___y_94_, 1);
v_a_88_ = v_a_95_;
goto v___jp_87_;
}
else
{
lean_object* v_a_96_; lean_object* v___x_98_; uint8_t v_isShared_99_; uint8_t v_isSharedCheck_103_; 
lean_dec_ref(v_bs_x27_86_);
v_a_96_ = lean_ctor_get(v___y_94_, 0);
v_isSharedCheck_103_ = !lean_is_exclusive(v___y_94_);
if (v_isSharedCheck_103_ == 0)
{
v___x_98_ = v___y_94_;
v_isShared_99_ = v_isSharedCheck_103_;
goto v_resetjp_97_;
}
else
{
lean_inc(v_a_96_);
lean_dec(v___y_94_);
v___x_98_ = lean_box(0);
v_isShared_99_ = v_isSharedCheck_103_;
goto v_resetjp_97_;
}
v_resetjp_97_:
{
lean_object* v___x_101_; 
if (v_isShared_99_ == 0)
{
v___x_101_ = v___x_98_;
goto v_reusejp_100_;
}
else
{
lean_object* v_reuseFailAlloc_102_; 
v_reuseFailAlloc_102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_102_, 0, v_a_96_);
v___x_101_ = v_reuseFailAlloc_102_;
goto v_reusejp_100_;
}
v_reusejp_100_:
{
return v___x_101_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__1___redArg___boxed(lean_object* v_sz_114_, lean_object* v_i_115_, lean_object* v_bs_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_){
_start:
{
size_t v_sz_boxed_121_; size_t v_i_boxed_122_; lean_object* v_res_123_; 
v_sz_boxed_121_ = lean_unbox_usize(v_sz_114_);
lean_dec(v_sz_114_);
v_i_boxed_122_ = lean_unbox_usize(v_i_115_);
lean_dec(v_i_115_);
v_res_123_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__1___redArg(v_sz_boxed_121_, v_i_boxed_122_, v_bs_116_, v___y_117_, v___y_118_, v___y_119_);
lean_dec(v___y_119_);
lean_dec_ref(v___y_118_);
lean_dec_ref(v___y_117_);
return v_res_123_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore___closed__1(void){
_start:
{
lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_125_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore___closed__0));
v___x_126_ = l_Lean_stringToMessageData(v___x_125_);
return v___x_126_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore___closed__3(void){
_start:
{
lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_128_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore___closed__2));
v___x_129_ = l_Lean_stringToMessageData(v___x_128_);
return v___x_129_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore(uint8_t v_internalize_130_, lean_object* v_ids_131_, lean_object* v_a_132_, lean_object* v_a_133_, lean_object* v_a_134_, lean_object* v_a_135_, lean_object* v_a_136_, lean_object* v_a_137_, lean_object* v_a_138_, lean_object* v_a_139_){
_start:
{
lean_object* v_goal_142_; lean_object* v___y_143_; lean_object* v___y_144_; lean_object* v___y_145_; lean_object* v___y_146_; lean_object* v___y_147_; lean_object* v_goal_152_; lean_object* v___y_153_; lean_object* v___y_154_; lean_object* v___y_155_; lean_object* v___y_156_; lean_object* v___y_157_; lean_object* v___y_158_; lean_object* v___x_170_; 
v___x_170_ = l_Lean_Elab_Tactic_Grind_ensureSym___redArg(v_a_132_, v_a_136_, v_a_137_, v_a_138_, v_a_139_);
if (lean_obj_tag(v___x_170_) == 0)
{
lean_object* v___x_171_; lean_object* v___x_172_; uint8_t v___x_173_; lean_object* v___x_174_; 
lean_dec_ref_known(v___x_170_, 1);
v___x_171_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_138_);
v___x_172_ = l_Lean_Meta_tactic_hygienic;
v___x_173_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__0(v___x_171_, v___x_172_);
lean_dec_ref(v___x_171_);
v___x_174_ = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(v_a_133_, v_a_136_, v_a_137_, v_a_138_, v_a_139_);
if (lean_obj_tag(v___x_174_) == 0)
{
lean_object* v_a_175_; lean_object* v___x_176_; lean_object* v___x_177_; uint8_t v___x_178_; 
v_a_175_ = lean_ctor_get(v___x_174_, 0);
lean_inc(v_a_175_);
lean_dec_ref_known(v___x_174_, 1);
v___x_176_ = lean_array_get_size(v_ids_131_);
v___x_177_ = lean_unsigned_to_nat(0u);
v___x_178_ = lean_nat_dec_eq(v___x_176_, v___x_177_);
if (v___x_178_ == 0)
{
size_t v_sz_179_; size_t v___x_180_; lean_object* v___x_181_; 
v_sz_179_ = lean_array_size(v_ids_131_);
v___x_180_ = ((size_t)0ULL);
v___x_181_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__1___redArg(v_sz_179_, v___x_180_, v_ids_131_, v_a_136_, v_a_138_, v_a_139_);
if (lean_obj_tag(v___x_181_) == 0)
{
lean_object* v_a_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
v_a_182_ = lean_ctor_get(v___x_181_, 0);
lean_inc(v_a_182_);
lean_dec_ref_known(v___x_181_, 1);
v___x_183_ = lean_box(v___x_173_);
v___x_184_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Goal_intros___boxed), 10, 3);
lean_closure_set(v___x_184_, 0, v_a_175_);
lean_closure_set(v___x_184_, 1, v_a_182_);
lean_closure_set(v___x_184_, 2, v___x_183_);
v___x_185_ = l_Lean_Elab_Tactic_Grind_liftSymM___redArg(v___x_184_, v_a_132_, v_a_133_, v_a_136_, v_a_137_, v_a_138_, v_a_139_);
if (lean_obj_tag(v___x_185_) == 0)
{
lean_object* v_a_186_; 
v_a_186_ = lean_ctor_get(v___x_185_, 0);
lean_inc(v_a_186_);
lean_dec_ref_known(v___x_185_, 1);
if (lean_obj_tag(v_a_186_) == 0)
{
lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v_a_189_; lean_object* v___x_191_; uint8_t v_isShared_192_; uint8_t v_isSharedCheck_196_; 
v___x_187_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore___closed__1, &l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore___closed__1);
v___x_188_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__2___redArg(v___x_187_, v_a_136_, v_a_137_, v_a_138_, v_a_139_);
v_a_189_ = lean_ctor_get(v___x_188_, 0);
v_isSharedCheck_196_ = !lean_is_exclusive(v___x_188_);
if (v_isSharedCheck_196_ == 0)
{
v___x_191_ = v___x_188_;
v_isShared_192_ = v_isSharedCheck_196_;
goto v_resetjp_190_;
}
else
{
lean_inc(v_a_189_);
lean_dec(v___x_188_);
v___x_191_ = lean_box(0);
v_isShared_192_ = v_isSharedCheck_196_;
goto v_resetjp_190_;
}
v_resetjp_190_:
{
lean_object* v___x_194_; 
if (v_isShared_192_ == 0)
{
v___x_194_ = v___x_191_;
goto v_reusejp_193_;
}
else
{
lean_object* v_reuseFailAlloc_195_; 
v_reuseFailAlloc_195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_195_, 0, v_a_189_);
v___x_194_ = v_reuseFailAlloc_195_;
goto v_reusejp_193_;
}
v_reusejp_193_:
{
return v___x_194_;
}
}
}
else
{
lean_object* v_goal_197_; 
v_goal_197_ = lean_ctor_get(v_a_186_, 1);
lean_inc_ref(v_goal_197_);
lean_dec_ref_known(v_a_186_, 2);
v_goal_152_ = v_goal_197_;
v___y_153_ = v_a_132_;
v___y_154_ = v_a_133_;
v___y_155_ = v_a_136_;
v___y_156_ = v_a_137_;
v___y_157_ = v_a_138_;
v___y_158_ = v_a_139_;
goto v___jp_151_;
}
}
else
{
lean_object* v_a_198_; lean_object* v___x_200_; uint8_t v_isShared_201_; uint8_t v_isSharedCheck_205_; 
v_a_198_ = lean_ctor_get(v___x_185_, 0);
v_isSharedCheck_205_ = !lean_is_exclusive(v___x_185_);
if (v_isSharedCheck_205_ == 0)
{
v___x_200_ = v___x_185_;
v_isShared_201_ = v_isSharedCheck_205_;
goto v_resetjp_199_;
}
else
{
lean_inc(v_a_198_);
lean_dec(v___x_185_);
v___x_200_ = lean_box(0);
v_isShared_201_ = v_isSharedCheck_205_;
goto v_resetjp_199_;
}
v_resetjp_199_:
{
lean_object* v___x_203_; 
if (v_isShared_201_ == 0)
{
v___x_203_ = v___x_200_;
goto v_reusejp_202_;
}
else
{
lean_object* v_reuseFailAlloc_204_; 
v_reuseFailAlloc_204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_204_, 0, v_a_198_);
v___x_203_ = v_reuseFailAlloc_204_;
goto v_reusejp_202_;
}
v_reusejp_202_:
{
return v___x_203_;
}
}
}
}
else
{
lean_object* v_a_206_; lean_object* v___x_208_; uint8_t v_isShared_209_; uint8_t v_isSharedCheck_213_; 
lean_dec(v_a_175_);
v_a_206_ = lean_ctor_get(v___x_181_, 0);
v_isSharedCheck_213_ = !lean_is_exclusive(v___x_181_);
if (v_isSharedCheck_213_ == 0)
{
v___x_208_ = v___x_181_;
v_isShared_209_ = v_isSharedCheck_213_;
goto v_resetjp_207_;
}
else
{
lean_inc(v_a_206_);
lean_dec(v___x_181_);
v___x_208_ = lean_box(0);
v_isShared_209_ = v_isSharedCheck_213_;
goto v_resetjp_207_;
}
v_resetjp_207_:
{
lean_object* v___x_211_; 
if (v_isShared_209_ == 0)
{
v___x_211_ = v___x_208_;
goto v_reusejp_210_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v_a_206_);
v___x_211_ = v_reuseFailAlloc_212_;
goto v_reusejp_210_;
}
v_reusejp_210_:
{
return v___x_211_;
}
}
}
}
else
{
lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; 
lean_dec_ref(v_ids_131_);
v___x_214_ = lean_unsigned_to_nat(1u);
v___x_215_ = lean_box(v___x_173_);
v___x_216_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Goal_introN___boxed), 10, 3);
lean_closure_set(v___x_216_, 0, v_a_175_);
lean_closure_set(v___x_216_, 1, v___x_214_);
lean_closure_set(v___x_216_, 2, v___x_215_);
v___x_217_ = l_Lean_Elab_Tactic_Grind_liftSymM___redArg(v___x_216_, v_a_132_, v_a_133_, v_a_136_, v_a_137_, v_a_138_, v_a_139_);
if (lean_obj_tag(v___x_217_) == 0)
{
lean_object* v_a_218_; 
v_a_218_ = lean_ctor_get(v___x_217_, 0);
lean_inc(v_a_218_);
lean_dec_ref_known(v___x_217_, 1);
if (lean_obj_tag(v_a_218_) == 0)
{
lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v_a_221_; lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_228_; 
v___x_219_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore___closed__3, &l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore___closed__3);
v___x_220_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__2___redArg(v___x_219_, v_a_136_, v_a_137_, v_a_138_, v_a_139_);
v_a_221_ = lean_ctor_get(v___x_220_, 0);
v_isSharedCheck_228_ = !lean_is_exclusive(v___x_220_);
if (v_isSharedCheck_228_ == 0)
{
v___x_223_ = v___x_220_;
v_isShared_224_ = v_isSharedCheck_228_;
goto v_resetjp_222_;
}
else
{
lean_inc(v_a_221_);
lean_dec(v___x_220_);
v___x_223_ = lean_box(0);
v_isShared_224_ = v_isSharedCheck_228_;
goto v_resetjp_222_;
}
v_resetjp_222_:
{
lean_object* v___x_226_; 
if (v_isShared_224_ == 0)
{
v___x_226_ = v___x_223_;
goto v_reusejp_225_;
}
else
{
lean_object* v_reuseFailAlloc_227_; 
v_reuseFailAlloc_227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_227_, 0, v_a_221_);
v___x_226_ = v_reuseFailAlloc_227_;
goto v_reusejp_225_;
}
v_reusejp_225_:
{
return v___x_226_;
}
}
}
else
{
lean_object* v_goal_229_; 
v_goal_229_ = lean_ctor_get(v_a_218_, 1);
lean_inc_ref(v_goal_229_);
lean_dec_ref_known(v_a_218_, 2);
v_goal_152_ = v_goal_229_;
v___y_153_ = v_a_132_;
v___y_154_ = v_a_133_;
v___y_155_ = v_a_136_;
v___y_156_ = v_a_137_;
v___y_157_ = v_a_138_;
v___y_158_ = v_a_139_;
goto v___jp_151_;
}
}
else
{
lean_object* v_a_230_; lean_object* v___x_232_; uint8_t v_isShared_233_; uint8_t v_isSharedCheck_237_; 
v_a_230_ = lean_ctor_get(v___x_217_, 0);
v_isSharedCheck_237_ = !lean_is_exclusive(v___x_217_);
if (v_isSharedCheck_237_ == 0)
{
v___x_232_ = v___x_217_;
v_isShared_233_ = v_isSharedCheck_237_;
goto v_resetjp_231_;
}
else
{
lean_inc(v_a_230_);
lean_dec(v___x_217_);
v___x_232_ = lean_box(0);
v_isShared_233_ = v_isSharedCheck_237_;
goto v_resetjp_231_;
}
v_resetjp_231_:
{
lean_object* v___x_235_; 
if (v_isShared_233_ == 0)
{
v___x_235_ = v___x_232_;
goto v_reusejp_234_;
}
else
{
lean_object* v_reuseFailAlloc_236_; 
v_reuseFailAlloc_236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_236_, 0, v_a_230_);
v___x_235_ = v_reuseFailAlloc_236_;
goto v_reusejp_234_;
}
v_reusejp_234_:
{
return v___x_235_;
}
}
}
}
}
else
{
lean_object* v_a_238_; lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_245_; 
lean_dec_ref(v_ids_131_);
v_a_238_ = lean_ctor_get(v___x_174_, 0);
v_isSharedCheck_245_ = !lean_is_exclusive(v___x_174_);
if (v_isSharedCheck_245_ == 0)
{
v___x_240_ = v___x_174_;
v_isShared_241_ = v_isSharedCheck_245_;
goto v_resetjp_239_;
}
else
{
lean_inc(v_a_238_);
lean_dec(v___x_174_);
v___x_240_ = lean_box(0);
v_isShared_241_ = v_isSharedCheck_245_;
goto v_resetjp_239_;
}
v_resetjp_239_:
{
lean_object* v___x_243_; 
if (v_isShared_241_ == 0)
{
v___x_243_ = v___x_240_;
goto v_reusejp_242_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v_a_238_);
v___x_243_ = v_reuseFailAlloc_244_;
goto v_reusejp_242_;
}
v_reusejp_242_:
{
return v___x_243_;
}
}
}
}
else
{
lean_dec_ref(v_ids_131_);
return v___x_170_;
}
v___jp_141_:
{
lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_148_ = lean_box(0);
v___x_149_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_149_, 0, v_goal_142_);
lean_ctor_set(v___x_149_, 1, v___x_148_);
v___x_150_ = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(v___x_149_, v___y_143_, v___y_144_, v___y_145_, v___y_146_, v___y_147_);
return v___x_150_;
}
v___jp_151_:
{
if (v_internalize_130_ == 0)
{
v_goal_142_ = v_goal_152_;
v___y_143_ = v___y_154_;
v___y_144_ = v___y_155_;
v___y_145_ = v___y_156_;
v___y_146_ = v___y_157_;
v___y_147_ = v___y_158_;
goto v___jp_141_;
}
else
{
lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_159_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Goal_internalizeAll___boxed), 11, 1);
lean_closure_set(v___x_159_, 0, v_goal_152_);
v___x_160_ = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(v___x_159_, v___y_153_, v___y_154_, v___y_155_, v___y_156_, v___y_157_, v___y_158_);
if (lean_obj_tag(v___x_160_) == 0)
{
lean_object* v_a_161_; 
v_a_161_ = lean_ctor_get(v___x_160_, 0);
lean_inc(v_a_161_);
lean_dec_ref_known(v___x_160_, 1);
v_goal_142_ = v_a_161_;
v___y_143_ = v___y_154_;
v___y_144_ = v___y_155_;
v___y_145_ = v___y_156_;
v___y_146_ = v___y_157_;
v___y_147_ = v___y_158_;
goto v___jp_141_;
}
else
{
lean_object* v_a_162_; lean_object* v___x_164_; uint8_t v_isShared_165_; uint8_t v_isSharedCheck_169_; 
v_a_162_ = lean_ctor_get(v___x_160_, 0);
v_isSharedCheck_169_ = !lean_is_exclusive(v___x_160_);
if (v_isSharedCheck_169_ == 0)
{
v___x_164_ = v___x_160_;
v_isShared_165_ = v_isSharedCheck_169_;
goto v_resetjp_163_;
}
else
{
lean_inc(v_a_162_);
lean_dec(v___x_160_);
v___x_164_ = lean_box(0);
v_isShared_165_ = v_isSharedCheck_169_;
goto v_resetjp_163_;
}
v_resetjp_163_:
{
lean_object* v___x_167_; 
if (v_isShared_165_ == 0)
{
v___x_167_ = v___x_164_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_168_; 
v_reuseFailAlloc_168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_168_, 0, v_a_162_);
v___x_167_ = v_reuseFailAlloc_168_;
goto v_reusejp_166_;
}
v_reusejp_166_:
{
return v___x_167_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore___boxed(lean_object* v_internalize_246_, lean_object* v_ids_247_, lean_object* v_a_248_, lean_object* v_a_249_, lean_object* v_a_250_, lean_object* v_a_251_, lean_object* v_a_252_, lean_object* v_a_253_, lean_object* v_a_254_, lean_object* v_a_255_, lean_object* v_a_256_){
_start:
{
uint8_t v_internalize_boxed_257_; lean_object* v_res_258_; 
v_internalize_boxed_257_ = lean_unbox(v_internalize_246_);
v_res_258_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore(v_internalize_boxed_257_, v_ids_247_, v_a_248_, v_a_249_, v_a_250_, v_a_251_, v_a_252_, v_a_253_, v_a_254_, v_a_255_);
lean_dec(v_a_255_);
lean_dec_ref(v_a_254_);
lean_dec(v_a_253_);
lean_dec_ref(v_a_252_);
lean_dec(v_a_251_);
lean_dec_ref(v_a_250_);
lean_dec(v_a_249_);
lean_dec_ref(v_a_248_);
return v_res_258_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__1(size_t v_sz_259_, size_t v_i_260_, lean_object* v_bs_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_){
_start:
{
lean_object* v___x_271_; 
v___x_271_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__1___redArg(v_sz_259_, v_i_260_, v_bs_261_, v___y_266_, v___y_268_, v___y_269_);
return v___x_271_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__1___boxed(lean_object* v_sz_272_, lean_object* v_i_273_, lean_object* v_bs_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_){
_start:
{
size_t v_sz_boxed_284_; size_t v_i_boxed_285_; lean_object* v_res_286_; 
v_sz_boxed_284_ = lean_unbox_usize(v_sz_272_);
lean_dec(v_sz_272_);
v_i_boxed_285_ = lean_unbox_usize(v_i_273_);
lean_dec(v_i_273_);
v_res_286_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__1(v_sz_boxed_284_, v_i_boxed_285_, v_bs_274_, v___y_275_, v___y_276_, v___y_277_, v___y_278_, v___y_279_, v___y_280_, v___y_281_, v___y_282_);
lean_dec(v___y_282_);
lean_dec_ref(v___y_281_);
lean_dec(v___y_280_);
lean_dec_ref(v___y_279_);
lean_dec(v___y_278_);
lean_dec_ref(v___y_277_);
lean_dec(v___y_276_);
lean_dec_ref(v___y_275_);
return v_res_286_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__2(lean_object* v_00_u03b1_287_, lean_object* v_msg_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_){
_start:
{
lean_object* v___x_298_; 
v___x_298_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__2___redArg(v_msg_288_, v___y_293_, v___y_294_, v___y_295_, v___y_296_);
return v___x_298_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__2___boxed(lean_object* v_00_u03b1_299_, lean_object* v_msg_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__2(v_00_u03b1_299_, v_msg_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_, v___y_305_, v___y_306_, v___y_307_, v___y_308_);
lean_dec(v___y_308_);
lean_dec_ref(v___y_307_);
lean_dec(v___y_306_);
lean_dec_ref(v___y_305_);
lean_dec(v___y_304_);
lean_dec_ref(v___y_303_);
lean_dec(v___y_302_);
lean_dec_ref(v___y_301_);
return v_res_310_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_311_ = lean_box(0);
v___x_312_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_313_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_313_, 0, v___x_312_);
lean_ctor_set(v___x_313_, 1, v___x_311_);
return v___x_313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro_spec__0___redArg(){
_start:
{
lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_315_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro_spec__0___redArg___closed__0);
v___x_316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_316_, 0, v___x_315_);
return v___x_316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro_spec__0___redArg___boxed(lean_object* v___y_317_){
_start:
{
lean_object* v_res_318_; 
v_res_318_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro_spec__0___redArg();
return v_res_318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro_spec__0(lean_object* v_00_u03b1_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_){
_start:
{
lean_object* v___x_329_; 
v___x_329_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro_spec__0___redArg();
return v___x_329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro_spec__0___boxed(lean_object* v_00_u03b1_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_){
_start:
{
lean_object* v_res_340_; 
v_res_340_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro_spec__0(v_00_u03b1_330_, v___y_331_, v___y_332_, v___y_333_, v___y_334_, v___y_335_, v___y_336_, v___y_337_, v___y_338_);
lean_dec(v___y_338_);
lean_dec_ref(v___y_337_);
lean_dec(v___y_336_);
lean_dec_ref(v___y_335_);
lean_dec(v___y_334_);
lean_dec_ref(v___y_333_);
lean_dec(v___y_332_);
lean_dec_ref(v___y_331_);
return v_res_340_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro(lean_object* v_stx_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_){
_start:
{
lean_object* v___x_370_; uint8_t v___x_371_; 
v___x_370_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___closed__4));
lean_inc(v_stx_360_);
v___x_371_ = l_Lean_Syntax_isOfKind(v_stx_360_, v___x_370_);
if (v___x_371_ == 0)
{
lean_object* v___x_372_; 
lean_dec(v_stx_360_);
v___x_372_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro_spec__0___redArg();
return v___x_372_;
}
else
{
lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; uint8_t v___x_376_; 
v___x_373_ = lean_unsigned_to_nat(0u);
v___x_374_ = lean_unsigned_to_nat(1u);
v___x_375_ = l_Lean_Syntax_getArg(v_stx_360_, v___x_374_);
lean_inc(v___x_375_);
v___x_376_ = l_Lean_Syntax_matchesNull(v___x_375_, v___x_373_);
if (v___x_376_ == 0)
{
lean_object* v___x_377_; uint8_t v___x_378_; 
v___x_377_ = lean_unsigned_to_nat(5u);
lean_inc(v___x_375_);
v___x_378_ = l_Lean_Syntax_matchesNull(v___x_375_, v___x_377_);
if (v___x_378_ == 0)
{
lean_object* v___x_379_; 
lean_dec(v___x_375_);
lean_dec(v_stx_360_);
v___x_379_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro_spec__0___redArg();
return v___x_379_;
}
else
{
lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; uint8_t v___x_384_; 
v___x_380_ = lean_unsigned_to_nat(2u);
v___x_381_ = lean_unsigned_to_nat(3u);
v___x_382_ = l_Lean_Syntax_getArg(v___x_375_, v___x_381_);
lean_dec(v___x_375_);
v___x_383_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___closed__7));
lean_inc(v___x_382_);
v___x_384_ = l_Lean_Syntax_isOfKind(v___x_382_, v___x_383_);
if (v___x_384_ == 0)
{
lean_object* v___x_385_; uint8_t v___x_386_; 
v___x_385_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___closed__9));
v___x_386_ = l_Lean_Syntax_isOfKind(v___x_382_, v___x_385_);
if (v___x_386_ == 0)
{
lean_object* v___x_387_; 
lean_dec(v_stx_360_);
v___x_387_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro_spec__0___redArg();
return v___x_387_;
}
else
{
lean_object* v___x_388_; lean_object* v_ids_389_; lean_object* v___x_390_; 
v___x_388_ = l_Lean_Syntax_getArg(v_stx_360_, v___x_380_);
lean_dec(v_stx_360_);
v_ids_389_ = l_Lean_Syntax_getArgs(v___x_388_);
lean_dec(v___x_388_);
v___x_390_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore(v___x_371_, v_ids_389_, v_a_361_, v_a_362_, v_a_363_, v_a_364_, v_a_365_, v_a_366_, v_a_367_, v_a_368_);
return v___x_390_;
}
}
else
{
lean_object* v___x_391_; lean_object* v_ids_392_; lean_object* v___x_393_; 
lean_dec(v___x_382_);
v___x_391_ = l_Lean_Syntax_getArg(v_stx_360_, v___x_380_);
lean_dec(v_stx_360_);
v_ids_392_ = l_Lean_Syntax_getArgs(v___x_391_);
lean_dec(v___x_391_);
v___x_393_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore(v___x_376_, v_ids_392_, v_a_361_, v_a_362_, v_a_363_, v_a_364_, v_a_365_, v_a_366_, v_a_367_, v_a_368_);
return v___x_393_;
}
}
}
else
{
lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v_ids_396_; lean_object* v___x_397_; 
lean_dec(v___x_375_);
v___x_394_ = lean_unsigned_to_nat(2u);
v___x_395_ = l_Lean_Syntax_getArg(v_stx_360_, v___x_394_);
lean_dec(v_stx_360_);
v_ids_396_ = l_Lean_Syntax_getArgs(v___x_395_);
lean_dec(v___x_395_);
v___x_397_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore(v___x_371_, v_ids_396_, v_a_361_, v_a_362_, v_a_363_, v_a_364_, v_a_365_, v_a_366_, v_a_367_, v_a_368_);
return v___x_397_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___boxed(lean_object* v_stx_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_){
_start:
{
lean_object* v_res_408_; 
v_res_408_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro(v_stx_398_, v_a_399_, v_a_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_, v_a_406_);
lean_dec(v_a_406_);
lean_dec_ref(v_a_405_);
lean_dec(v_a_404_);
lean_dec_ref(v_a_403_);
lean_dec(v_a_402_);
lean_dec_ref(v_a_401_);
lean_dec(v_a_400_);
lean_dec_ref(v_a_399_);
return v_res_408_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro__1(){
_start:
{
lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_450_ = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
v___x_451_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___closed__4));
v___x_452_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro__1___closed__15));
v___x_453_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___boxed), 10, 0);
v___x_454_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_450_, v___x_451_, v___x_452_, v___x_453_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro__1___boxed(lean_object* v_a_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro__1();
return v_res_456_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntrosCore___redArg___closed__2(void){
_start:
{
lean_object* v___x_460_; lean_object* v___x_461_; 
v___x_460_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntrosCore___redArg___closed__1));
v___x_461_ = l_Lean_stringToMessageData(v___x_460_);
return v___x_461_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntrosCore___redArg(uint8_t v_internalize_462_, lean_object* v_a_463_, lean_object* v_a_464_, lean_object* v_a_465_, lean_object* v_a_466_, lean_object* v_a_467_, lean_object* v_a_468_){
_start:
{
lean_object* v_goal_471_; lean_object* v___y_472_; lean_object* v___y_473_; lean_object* v___y_474_; lean_object* v___y_475_; lean_object* v___y_476_; lean_object* v___x_480_; 
v___x_480_ = l_Lean_Elab_Tactic_Grind_ensureSym___redArg(v_a_463_, v_a_465_, v_a_466_, v_a_467_, v_a_468_);
if (lean_obj_tag(v___x_480_) == 0)
{
lean_object* v___x_481_; lean_object* v___x_482_; uint8_t v___x_483_; lean_object* v___x_484_; 
lean_dec_ref_known(v___x_480_, 1);
v___x_481_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_467_);
v___x_482_ = l_Lean_Meta_tactic_hygienic;
v___x_483_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__0(v___x_481_, v___x_482_);
lean_dec_ref(v___x_481_);
v___x_484_ = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(v_a_464_, v_a_465_, v_a_466_, v_a_467_, v_a_468_);
if (lean_obj_tag(v___x_484_) == 0)
{
lean_object* v_a_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; 
v_a_485_ = lean_ctor_get(v___x_484_, 0);
lean_inc(v_a_485_);
lean_dec_ref_known(v___x_484_, 1);
v___x_486_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntrosCore___redArg___closed__0));
v___x_487_ = lean_box(v___x_483_);
v___x_488_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Goal_intros___boxed), 10, 3);
lean_closure_set(v___x_488_, 0, v_a_485_);
lean_closure_set(v___x_488_, 1, v___x_486_);
lean_closure_set(v___x_488_, 2, v___x_487_);
v___x_489_ = l_Lean_Elab_Tactic_Grind_liftSymM___redArg(v___x_488_, v_a_463_, v_a_464_, v_a_465_, v_a_466_, v_a_467_, v_a_468_);
if (lean_obj_tag(v___x_489_) == 0)
{
lean_object* v_a_490_; 
v_a_490_ = lean_ctor_get(v___x_489_, 0);
lean_inc(v_a_490_);
lean_dec_ref_known(v___x_489_, 1);
if (lean_obj_tag(v_a_490_) == 0)
{
lean_object* v___x_491_; lean_object* v___x_492_; 
v___x_491_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntrosCore___redArg___closed__2, &l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntrosCore___redArg___closed__2_once, _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntrosCore___redArg___closed__2);
v___x_492_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__2___redArg(v___x_491_, v_a_465_, v_a_466_, v_a_467_, v_a_468_);
return v___x_492_;
}
else
{
if (v_internalize_462_ == 0)
{
lean_object* v_goal_493_; 
v_goal_493_ = lean_ctor_get(v_a_490_, 1);
lean_inc_ref(v_goal_493_);
lean_dec_ref_known(v_a_490_, 2);
v_goal_471_ = v_goal_493_;
v___y_472_ = v_a_464_;
v___y_473_ = v_a_465_;
v___y_474_ = v_a_466_;
v___y_475_ = v_a_467_;
v___y_476_ = v_a_468_;
goto v___jp_470_;
}
else
{
lean_object* v_goal_494_; lean_object* v___x_495_; lean_object* v___x_496_; 
v_goal_494_ = lean_ctor_get(v_a_490_, 1);
lean_inc_ref(v_goal_494_);
lean_dec_ref_known(v_a_490_, 2);
v___x_495_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Goal_internalizeAll___boxed), 11, 1);
lean_closure_set(v___x_495_, 0, v_goal_494_);
v___x_496_ = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(v___x_495_, v_a_463_, v_a_464_, v_a_465_, v_a_466_, v_a_467_, v_a_468_);
if (lean_obj_tag(v___x_496_) == 0)
{
lean_object* v_a_497_; 
v_a_497_ = lean_ctor_get(v___x_496_, 0);
lean_inc(v_a_497_);
lean_dec_ref_known(v___x_496_, 1);
v_goal_471_ = v_a_497_;
v___y_472_ = v_a_464_;
v___y_473_ = v_a_465_;
v___y_474_ = v_a_466_;
v___y_475_ = v_a_467_;
v___y_476_ = v_a_468_;
goto v___jp_470_;
}
else
{
lean_object* v_a_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_505_; 
v_a_498_ = lean_ctor_get(v___x_496_, 0);
v_isSharedCheck_505_ = !lean_is_exclusive(v___x_496_);
if (v_isSharedCheck_505_ == 0)
{
v___x_500_ = v___x_496_;
v_isShared_501_ = v_isSharedCheck_505_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_a_498_);
lean_dec(v___x_496_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_505_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
lean_object* v___x_503_; 
if (v_isShared_501_ == 0)
{
v___x_503_ = v___x_500_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v_a_498_);
v___x_503_ = v_reuseFailAlloc_504_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
return v___x_503_;
}
}
}
}
}
}
else
{
lean_object* v_a_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_513_; 
v_a_506_ = lean_ctor_get(v___x_489_, 0);
v_isSharedCheck_513_ = !lean_is_exclusive(v___x_489_);
if (v_isSharedCheck_513_ == 0)
{
v___x_508_ = v___x_489_;
v_isShared_509_ = v_isSharedCheck_513_;
goto v_resetjp_507_;
}
else
{
lean_inc(v_a_506_);
lean_dec(v___x_489_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_513_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
lean_object* v___x_511_; 
if (v_isShared_509_ == 0)
{
v___x_511_ = v___x_508_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_512_; 
v_reuseFailAlloc_512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_512_, 0, v_a_506_);
v___x_511_ = v_reuseFailAlloc_512_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
return v___x_511_;
}
}
}
}
else
{
lean_object* v_a_514_; lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_521_; 
v_a_514_ = lean_ctor_get(v___x_484_, 0);
v_isSharedCheck_521_ = !lean_is_exclusive(v___x_484_);
if (v_isSharedCheck_521_ == 0)
{
v___x_516_ = v___x_484_;
v_isShared_517_ = v_isSharedCheck_521_;
goto v_resetjp_515_;
}
else
{
lean_inc(v_a_514_);
lean_dec(v___x_484_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_521_;
goto v_resetjp_515_;
}
v_resetjp_515_:
{
lean_object* v___x_519_; 
if (v_isShared_517_ == 0)
{
v___x_519_ = v___x_516_;
goto v_reusejp_518_;
}
else
{
lean_object* v_reuseFailAlloc_520_; 
v_reuseFailAlloc_520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_520_, 0, v_a_514_);
v___x_519_ = v_reuseFailAlloc_520_;
goto v_reusejp_518_;
}
v_reusejp_518_:
{
return v___x_519_;
}
}
}
}
else
{
return v___x_480_;
}
v___jp_470_:
{
lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; 
v___x_477_ = lean_box(0);
v___x_478_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_478_, 0, v_goal_471_);
lean_ctor_set(v___x_478_, 1, v___x_477_);
v___x_479_ = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(v___x_478_, v___y_472_, v___y_473_, v___y_474_, v___y_475_, v___y_476_);
return v___x_479_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntrosCore___redArg___boxed(lean_object* v_internalize_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_, lean_object* v_a_526_, lean_object* v_a_527_, lean_object* v_a_528_, lean_object* v_a_529_){
_start:
{
uint8_t v_internalize_boxed_530_; lean_object* v_res_531_; 
v_internalize_boxed_530_ = lean_unbox(v_internalize_522_);
v_res_531_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntrosCore___redArg(v_internalize_boxed_530_, v_a_523_, v_a_524_, v_a_525_, v_a_526_, v_a_527_, v_a_528_);
lean_dec(v_a_528_);
lean_dec_ref(v_a_527_);
lean_dec(v_a_526_);
lean_dec_ref(v_a_525_);
lean_dec(v_a_524_);
lean_dec_ref(v_a_523_);
return v_res_531_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntrosCore(uint8_t v_internalize_532_, lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_a_535_, lean_object* v_a_536_, lean_object* v_a_537_, lean_object* v_a_538_, lean_object* v_a_539_, lean_object* v_a_540_){
_start:
{
lean_object* v___x_542_; 
v___x_542_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntrosCore___redArg(v_internalize_532_, v_a_533_, v_a_534_, v_a_537_, v_a_538_, v_a_539_, v_a_540_);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntrosCore___boxed(lean_object* v_internalize_543_, lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_, lean_object* v_a_547_, lean_object* v_a_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_){
_start:
{
uint8_t v_internalize_boxed_553_; lean_object* v_res_554_; 
v_internalize_boxed_553_ = lean_unbox(v_internalize_543_);
v_res_554_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntrosCore(v_internalize_boxed_553_, v_a_544_, v_a_545_, v_a_546_, v_a_547_, v_a_548_, v_a_549_, v_a_550_, v_a_551_);
lean_dec(v_a_551_);
lean_dec_ref(v_a_550_);
lean_dec(v_a_549_);
lean_dec_ref(v_a_548_);
lean_dec(v_a_547_);
lean_dec_ref(v_a_546_);
lean_dec(v_a_545_);
lean_dec_ref(v_a_544_);
return v_res_554_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntros___redArg(lean_object* v_stx_562_, lean_object* v_a_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_){
_start:
{
lean_object* v___x_570_; uint8_t v___x_571_; 
v___x_570_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntros___redArg___closed__1));
lean_inc(v_stx_562_);
v___x_571_ = l_Lean_Syntax_isOfKind(v_stx_562_, v___x_570_);
if (v___x_571_ == 0)
{
lean_object* v___x_572_; 
lean_dec(v_stx_562_);
v___x_572_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro_spec__0___redArg();
return v___x_572_;
}
else
{
lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; uint8_t v___x_576_; 
v___x_573_ = lean_unsigned_to_nat(0u);
v___x_574_ = lean_unsigned_to_nat(1u);
v___x_575_ = l_Lean_Syntax_getArg(v_stx_562_, v___x_574_);
lean_dec(v_stx_562_);
lean_inc(v___x_575_);
v___x_576_ = l_Lean_Syntax_matchesNull(v___x_575_, v___x_573_);
if (v___x_576_ == 0)
{
lean_object* v___x_577_; uint8_t v___x_578_; 
v___x_577_ = lean_unsigned_to_nat(5u);
lean_inc(v___x_575_);
v___x_578_ = l_Lean_Syntax_matchesNull(v___x_575_, v___x_577_);
if (v___x_578_ == 0)
{
lean_object* v___x_579_; 
lean_dec(v___x_575_);
v___x_579_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro_spec__0___redArg();
return v___x_579_;
}
else
{
lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; uint8_t v___x_583_; 
v___x_580_ = lean_unsigned_to_nat(3u);
v___x_581_ = l_Lean_Syntax_getArg(v___x_575_, v___x_580_);
lean_dec(v___x_575_);
v___x_582_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___closed__7));
lean_inc(v___x_581_);
v___x_583_ = l_Lean_Syntax_isOfKind(v___x_581_, v___x_582_);
if (v___x_583_ == 0)
{
lean_object* v___x_584_; uint8_t v___x_585_; 
v___x_584_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___closed__9));
v___x_585_ = l_Lean_Syntax_isOfKind(v___x_581_, v___x_584_);
if (v___x_585_ == 0)
{
lean_object* v___x_586_; 
v___x_586_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro_spec__0___redArg();
return v___x_586_;
}
else
{
lean_object* v___x_587_; 
v___x_587_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntrosCore___redArg(v___x_571_, v_a_563_, v_a_564_, v_a_565_, v_a_566_, v_a_567_, v_a_568_);
return v___x_587_;
}
}
else
{
lean_object* v___x_588_; 
lean_dec(v___x_581_);
v___x_588_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntrosCore___redArg(v___x_576_, v_a_563_, v_a_564_, v_a_565_, v_a_566_, v_a_567_, v_a_568_);
return v___x_588_;
}
}
}
else
{
lean_object* v___x_589_; 
lean_dec(v___x_575_);
v___x_589_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntrosCore___redArg(v___x_571_, v_a_563_, v_a_564_, v_a_565_, v_a_566_, v_a_567_, v_a_568_);
return v___x_589_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntros___redArg___boxed(lean_object* v_stx_590_, lean_object* v_a_591_, lean_object* v_a_592_, lean_object* v_a_593_, lean_object* v_a_594_, lean_object* v_a_595_, lean_object* v_a_596_, lean_object* v_a_597_){
_start:
{
lean_object* v_res_598_; 
v_res_598_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntros___redArg(v_stx_590_, v_a_591_, v_a_592_, v_a_593_, v_a_594_, v_a_595_, v_a_596_);
lean_dec(v_a_596_);
lean_dec_ref(v_a_595_);
lean_dec(v_a_594_);
lean_dec_ref(v_a_593_);
lean_dec(v_a_592_);
lean_dec_ref(v_a_591_);
return v_res_598_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntros(lean_object* v_stx_599_, lean_object* v_a_600_, lean_object* v_a_601_, lean_object* v_a_602_, lean_object* v_a_603_, lean_object* v_a_604_, lean_object* v_a_605_, lean_object* v_a_606_, lean_object* v_a_607_){
_start:
{
lean_object* v___x_609_; 
v___x_609_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntros___redArg(v_stx_599_, v_a_600_, v_a_601_, v_a_604_, v_a_605_, v_a_606_, v_a_607_);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntros___boxed(lean_object* v_stx_610_, lean_object* v_a_611_, lean_object* v_a_612_, lean_object* v_a_613_, lean_object* v_a_614_, lean_object* v_a_615_, lean_object* v_a_616_, lean_object* v_a_617_, lean_object* v_a_618_, lean_object* v_a_619_){
_start:
{
lean_object* v_res_620_; 
v_res_620_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntros(v_stx_610_, v_a_611_, v_a_612_, v_a_613_, v_a_614_, v_a_615_, v_a_616_, v_a_617_, v_a_618_);
lean_dec(v_a_618_);
lean_dec_ref(v_a_617_);
lean_dec(v_a_616_);
lean_dec_ref(v_a_615_);
lean_dec(v_a_614_);
lean_dec_ref(v_a_613_);
lean_dec(v_a_612_);
lean_dec_ref(v_a_611_);
return v_res_620_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntros___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntros__1(){
_start:
{
lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; 
v___x_626_ = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
v___x_627_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntros___redArg___closed__1));
v___x_628_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntros___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntros__1___closed__1));
v___x_629_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntros___boxed), 10, 0);
v___x_630_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_626_, v___x_627_, v___x_628_, v___x_629_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntros___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntros__1___boxed(lean_object* v_a_631_){
_start:
{
lean_object* v_res_632_; 
v_res_632_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntros___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntros__1();
return v_res_632_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_633_, lean_object* v_vals_634_, lean_object* v_i_635_, lean_object* v_k_636_){
_start:
{
lean_object* v___x_637_; uint8_t v___x_638_; 
v___x_637_ = lean_array_get_size(v_keys_633_);
v___x_638_ = lean_nat_dec_lt(v_i_635_, v___x_637_);
if (v___x_638_ == 0)
{
lean_object* v___x_639_; 
lean_dec(v_i_635_);
v___x_639_ = lean_box(0);
return v___x_639_;
}
else
{
lean_object* v_k_x27_640_; uint8_t v___x_641_; 
v_k_x27_640_ = lean_array_fget_borrowed(v_keys_633_, v_i_635_);
v___x_641_ = lean_name_eq(v_k_636_, v_k_x27_640_);
if (v___x_641_ == 0)
{
lean_object* v___x_642_; lean_object* v___x_643_; 
v___x_642_ = lean_unsigned_to_nat(1u);
v___x_643_ = lean_nat_add(v_i_635_, v___x_642_);
lean_dec(v_i_635_);
v_i_635_ = v___x_643_;
goto _start;
}
else
{
lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_645_ = lean_array_fget_borrowed(v_vals_634_, v_i_635_);
lean_dec(v_i_635_);
lean_inc(v___x_645_);
v___x_646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_646_, 0, v___x_645_);
return v___x_646_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_647_, lean_object* v_vals_648_, lean_object* v_i_649_, lean_object* v_k_650_){
_start:
{
lean_object* v_res_651_; 
v_res_651_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0_spec__0_spec__1___redArg(v_keys_647_, v_vals_648_, v_i_649_, v_k_650_);
lean_dec(v_k_650_);
lean_dec_ref(v_vals_648_);
lean_dec_ref(v_keys_647_);
return v_res_651_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0_spec__0___redArg(lean_object* v_x_652_, size_t v_x_653_, lean_object* v_x_654_){
_start:
{
if (lean_obj_tag(v_x_652_) == 0)
{
lean_object* v_es_655_; lean_object* v___x_656_; size_t v___x_657_; size_t v___x_658_; lean_object* v_j_659_; lean_object* v___x_660_; 
v_es_655_ = lean_ctor_get(v_x_652_, 0);
v___x_656_ = lean_box(2);
v___x_657_ = ((size_t)31ULL);
v___x_658_ = lean_usize_land(v_x_653_, v___x_657_);
v_j_659_ = lean_usize_to_nat(v___x_658_);
v___x_660_ = lean_array_get_borrowed(v___x_656_, v_es_655_, v_j_659_);
lean_dec(v_j_659_);
switch(lean_obj_tag(v___x_660_))
{
case 0:
{
lean_object* v_key_661_; lean_object* v_val_662_; uint8_t v___x_663_; 
v_key_661_ = lean_ctor_get(v___x_660_, 0);
v_val_662_ = lean_ctor_get(v___x_660_, 1);
v___x_663_ = lean_name_eq(v_x_654_, v_key_661_);
if (v___x_663_ == 0)
{
lean_object* v___x_664_; 
v___x_664_ = lean_box(0);
return v___x_664_;
}
else
{
lean_object* v___x_665_; 
lean_inc(v_val_662_);
v___x_665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_665_, 0, v_val_662_);
return v___x_665_;
}
}
case 1:
{
lean_object* v_node_666_; size_t v___x_667_; size_t v___x_668_; 
v_node_666_ = lean_ctor_get(v___x_660_, 0);
v___x_667_ = ((size_t)5ULL);
v___x_668_ = lean_usize_shift_right(v_x_653_, v___x_667_);
v_x_652_ = v_node_666_;
v_x_653_ = v___x_668_;
goto _start;
}
default: 
{
lean_object* v___x_670_; 
v___x_670_ = lean_box(0);
return v___x_670_;
}
}
}
else
{
lean_object* v_ks_671_; lean_object* v_vs_672_; lean_object* v___x_673_; lean_object* v___x_674_; 
v_ks_671_ = lean_ctor_get(v_x_652_, 0);
v_vs_672_ = lean_ctor_get(v_x_652_, 1);
v___x_673_ = lean_unsigned_to_nat(0u);
v___x_674_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0_spec__0_spec__1___redArg(v_ks_671_, v_vs_672_, v___x_673_, v_x_654_);
return v___x_674_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0_spec__0___redArg___boxed(lean_object* v_x_675_, lean_object* v_x_676_, lean_object* v_x_677_){
_start:
{
size_t v_x_1945__boxed_678_; lean_object* v_res_679_; 
v_x_1945__boxed_678_ = lean_unbox_usize(v_x_676_);
lean_dec(v_x_676_);
v_res_679_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0_spec__0___redArg(v_x_675_, v_x_1945__boxed_678_, v_x_677_);
lean_dec(v_x_677_);
lean_dec_ref(v_x_675_);
return v_res_679_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0___redArg(lean_object* v_x_680_, lean_object* v_x_681_){
_start:
{
uint64_t v___y_683_; 
if (lean_obj_tag(v_x_681_) == 0)
{
uint64_t v___x_686_; 
v___x_686_ = 1723ULL;
v___y_683_ = v___x_686_;
goto v___jp_682_;
}
else
{
uint64_t v_hash_687_; 
v_hash_687_ = lean_ctor_get_uint64(v_x_681_, sizeof(void*)*2);
v___y_683_ = v_hash_687_;
goto v___jp_682_;
}
v___jp_682_:
{
size_t v___x_684_; lean_object* v___x_685_; 
v___x_684_ = lean_uint64_to_usize(v___y_683_);
v___x_685_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0_spec__0___redArg(v_x_680_, v___x_684_, v_x_681_);
return v___x_685_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0___redArg___boxed(lean_object* v_x_688_, lean_object* v_x_689_){
_start:
{
lean_object* v_res_690_; 
v_res_690_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0___redArg(v_x_688_, v_x_689_);
lean_dec(v_x_689_);
lean_dec_ref(v_x_688_);
return v_res_690_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2_spec__4_spec__5___redArg(lean_object* v_x_691_, lean_object* v_x_692_, lean_object* v_x_693_, lean_object* v_x_694_){
_start:
{
lean_object* v_ks_695_; lean_object* v_vs_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_720_; 
v_ks_695_ = lean_ctor_get(v_x_691_, 0);
v_vs_696_ = lean_ctor_get(v_x_691_, 1);
v_isSharedCheck_720_ = !lean_is_exclusive(v_x_691_);
if (v_isSharedCheck_720_ == 0)
{
v___x_698_ = v_x_691_;
v_isShared_699_ = v_isSharedCheck_720_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_vs_696_);
lean_inc(v_ks_695_);
lean_dec(v_x_691_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_720_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v___x_700_; uint8_t v___x_701_; 
v___x_700_ = lean_array_get_size(v_ks_695_);
v___x_701_ = lean_nat_dec_lt(v_x_692_, v___x_700_);
if (v___x_701_ == 0)
{
lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_705_; 
lean_dec(v_x_692_);
v___x_702_ = lean_array_push(v_ks_695_, v_x_693_);
v___x_703_ = lean_array_push(v_vs_696_, v_x_694_);
if (v_isShared_699_ == 0)
{
lean_ctor_set(v___x_698_, 1, v___x_703_);
lean_ctor_set(v___x_698_, 0, v___x_702_);
v___x_705_ = v___x_698_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v___x_702_);
lean_ctor_set(v_reuseFailAlloc_706_, 1, v___x_703_);
v___x_705_ = v_reuseFailAlloc_706_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
return v___x_705_;
}
}
else
{
lean_object* v_k_x27_707_; uint8_t v___x_708_; 
v_k_x27_707_ = lean_array_fget_borrowed(v_ks_695_, v_x_692_);
v___x_708_ = lean_name_eq(v_x_693_, v_k_x27_707_);
if (v___x_708_ == 0)
{
lean_object* v___x_710_; 
if (v_isShared_699_ == 0)
{
v___x_710_ = v___x_698_;
goto v_reusejp_709_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v_ks_695_);
lean_ctor_set(v_reuseFailAlloc_714_, 1, v_vs_696_);
v___x_710_ = v_reuseFailAlloc_714_;
goto v_reusejp_709_;
}
v_reusejp_709_:
{
lean_object* v___x_711_; lean_object* v___x_712_; 
v___x_711_ = lean_unsigned_to_nat(1u);
v___x_712_ = lean_nat_add(v_x_692_, v___x_711_);
lean_dec(v_x_692_);
v_x_691_ = v___x_710_;
v_x_692_ = v___x_712_;
goto _start;
}
}
else
{
lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_718_; 
v___x_715_ = lean_array_fset(v_ks_695_, v_x_692_, v_x_693_);
v___x_716_ = lean_array_fset(v_vs_696_, v_x_692_, v_x_694_);
lean_dec(v_x_692_);
if (v_isShared_699_ == 0)
{
lean_ctor_set(v___x_698_, 1, v___x_716_);
lean_ctor_set(v___x_698_, 0, v___x_715_);
v___x_718_ = v___x_698_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v___x_715_);
lean_ctor_set(v_reuseFailAlloc_719_, 1, v___x_716_);
v___x_718_ = v_reuseFailAlloc_719_;
goto v_reusejp_717_;
}
v_reusejp_717_:
{
return v___x_718_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2_spec__4___redArg(lean_object* v_n_721_, lean_object* v_k_722_, lean_object* v_v_723_){
_start:
{
lean_object* v___x_724_; lean_object* v___x_725_; 
v___x_724_ = lean_unsigned_to_nat(0u);
v___x_725_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2_spec__4_spec__5___redArg(v_n_721_, v___x_724_, v_k_722_, v_v_723_);
return v___x_725_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_726_; 
v___x_726_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_726_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2___redArg(lean_object* v_x_727_, size_t v_x_728_, size_t v_x_729_, lean_object* v_x_730_, lean_object* v_x_731_){
_start:
{
if (lean_obj_tag(v_x_727_) == 0)
{
lean_object* v_es_732_; size_t v___x_733_; size_t v___x_734_; lean_object* v_j_735_; lean_object* v___x_736_; uint8_t v___x_737_; 
v_es_732_ = lean_ctor_get(v_x_727_, 0);
v___x_733_ = ((size_t)31ULL);
v___x_734_ = lean_usize_land(v_x_728_, v___x_733_);
v_j_735_ = lean_usize_to_nat(v___x_734_);
v___x_736_ = lean_array_get_size(v_es_732_);
v___x_737_ = lean_nat_dec_lt(v_j_735_, v___x_736_);
if (v___x_737_ == 0)
{
lean_dec(v_j_735_);
lean_dec(v_x_731_);
lean_dec(v_x_730_);
return v_x_727_;
}
else
{
lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_776_; 
lean_inc_ref(v_es_732_);
v_isSharedCheck_776_ = !lean_is_exclusive(v_x_727_);
if (v_isSharedCheck_776_ == 0)
{
lean_object* v_unused_777_; 
v_unused_777_ = lean_ctor_get(v_x_727_, 0);
lean_dec(v_unused_777_);
v___x_739_ = v_x_727_;
v_isShared_740_ = v_isSharedCheck_776_;
goto v_resetjp_738_;
}
else
{
lean_dec(v_x_727_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_776_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
lean_object* v_v_741_; lean_object* v___x_742_; lean_object* v_xs_x27_743_; lean_object* v___y_745_; 
v_v_741_ = lean_array_fget(v_es_732_, v_j_735_);
v___x_742_ = lean_box(0);
v_xs_x27_743_ = lean_array_fset(v_es_732_, v_j_735_, v___x_742_);
switch(lean_obj_tag(v_v_741_))
{
case 0:
{
lean_object* v_key_750_; lean_object* v_val_751_; lean_object* v___x_753_; uint8_t v_isShared_754_; uint8_t v_isSharedCheck_761_; 
v_key_750_ = lean_ctor_get(v_v_741_, 0);
v_val_751_ = lean_ctor_get(v_v_741_, 1);
v_isSharedCheck_761_ = !lean_is_exclusive(v_v_741_);
if (v_isSharedCheck_761_ == 0)
{
v___x_753_ = v_v_741_;
v_isShared_754_ = v_isSharedCheck_761_;
goto v_resetjp_752_;
}
else
{
lean_inc(v_val_751_);
lean_inc(v_key_750_);
lean_dec(v_v_741_);
v___x_753_ = lean_box(0);
v_isShared_754_ = v_isSharedCheck_761_;
goto v_resetjp_752_;
}
v_resetjp_752_:
{
uint8_t v___x_755_; 
v___x_755_ = lean_name_eq(v_x_730_, v_key_750_);
if (v___x_755_ == 0)
{
lean_object* v___x_756_; lean_object* v___x_757_; 
lean_del_object(v___x_753_);
v___x_756_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_750_, v_val_751_, v_x_730_, v_x_731_);
v___x_757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_757_, 0, v___x_756_);
v___y_745_ = v___x_757_;
goto v___jp_744_;
}
else
{
lean_object* v___x_759_; 
lean_dec(v_val_751_);
lean_dec(v_key_750_);
if (v_isShared_754_ == 0)
{
lean_ctor_set(v___x_753_, 1, v_x_731_);
lean_ctor_set(v___x_753_, 0, v_x_730_);
v___x_759_ = v___x_753_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v_x_730_);
lean_ctor_set(v_reuseFailAlloc_760_, 1, v_x_731_);
v___x_759_ = v_reuseFailAlloc_760_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
v___y_745_ = v___x_759_;
goto v___jp_744_;
}
}
}
}
case 1:
{
lean_object* v_node_762_; lean_object* v___x_764_; uint8_t v_isShared_765_; uint8_t v_isSharedCheck_774_; 
v_node_762_ = lean_ctor_get(v_v_741_, 0);
v_isSharedCheck_774_ = !lean_is_exclusive(v_v_741_);
if (v_isSharedCheck_774_ == 0)
{
v___x_764_ = v_v_741_;
v_isShared_765_ = v_isSharedCheck_774_;
goto v_resetjp_763_;
}
else
{
lean_inc(v_node_762_);
lean_dec(v_v_741_);
v___x_764_ = lean_box(0);
v_isShared_765_ = v_isSharedCheck_774_;
goto v_resetjp_763_;
}
v_resetjp_763_:
{
size_t v___x_766_; size_t v___x_767_; size_t v___x_768_; size_t v___x_769_; lean_object* v___x_770_; lean_object* v___x_772_; 
v___x_766_ = ((size_t)5ULL);
v___x_767_ = lean_usize_shift_right(v_x_728_, v___x_766_);
v___x_768_ = ((size_t)1ULL);
v___x_769_ = lean_usize_add(v_x_729_, v___x_768_);
v___x_770_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2___redArg(v_node_762_, v___x_767_, v___x_769_, v_x_730_, v_x_731_);
if (v_isShared_765_ == 0)
{
lean_ctor_set(v___x_764_, 0, v___x_770_);
v___x_772_ = v___x_764_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v___x_770_);
v___x_772_ = v_reuseFailAlloc_773_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
v___y_745_ = v___x_772_;
goto v___jp_744_;
}
}
}
default: 
{
lean_object* v___x_775_; 
v___x_775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_775_, 0, v_x_730_);
lean_ctor_set(v___x_775_, 1, v_x_731_);
v___y_745_ = v___x_775_;
goto v___jp_744_;
}
}
v___jp_744_:
{
lean_object* v___x_746_; lean_object* v___x_748_; 
v___x_746_ = lean_array_fset(v_xs_x27_743_, v_j_735_, v___y_745_);
lean_dec(v_j_735_);
if (v_isShared_740_ == 0)
{
lean_ctor_set(v___x_739_, 0, v___x_746_);
v___x_748_ = v___x_739_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_749_; 
v_reuseFailAlloc_749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_749_, 0, v___x_746_);
v___x_748_ = v_reuseFailAlloc_749_;
goto v_reusejp_747_;
}
v_reusejp_747_:
{
return v___x_748_;
}
}
}
}
}
else
{
lean_object* v_ks_778_; lean_object* v_vs_779_; lean_object* v___x_781_; uint8_t v_isShared_782_; uint8_t v_isSharedCheck_797_; 
v_ks_778_ = lean_ctor_get(v_x_727_, 0);
v_vs_779_ = lean_ctor_get(v_x_727_, 1);
v_isSharedCheck_797_ = !lean_is_exclusive(v_x_727_);
if (v_isSharedCheck_797_ == 0)
{
v___x_781_ = v_x_727_;
v_isShared_782_ = v_isSharedCheck_797_;
goto v_resetjp_780_;
}
else
{
lean_inc(v_vs_779_);
lean_inc(v_ks_778_);
lean_dec(v_x_727_);
v___x_781_ = lean_box(0);
v_isShared_782_ = v_isSharedCheck_797_;
goto v_resetjp_780_;
}
v_resetjp_780_:
{
lean_object* v___x_784_; 
if (v_isShared_782_ == 0)
{
v___x_784_ = v___x_781_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v_ks_778_);
lean_ctor_set(v_reuseFailAlloc_796_, 1, v_vs_779_);
v___x_784_ = v_reuseFailAlloc_796_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
lean_object* v_newNode_785_; size_t v___x_786_; uint8_t v___x_787_; 
v_newNode_785_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2_spec__4___redArg(v___x_784_, v_x_730_, v_x_731_);
v___x_786_ = ((size_t)7ULL);
v___x_787_ = lean_usize_dec_le(v___x_786_, v_x_729_);
if (v___x_787_ == 0)
{
lean_object* v___x_788_; lean_object* v___x_789_; uint8_t v___x_790_; 
v___x_788_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_785_);
v___x_789_ = lean_unsigned_to_nat(4u);
v___x_790_ = lean_nat_dec_lt(v___x_788_, v___x_789_);
lean_dec(v___x_788_);
if (v___x_790_ == 0)
{
lean_object* v_ks_791_; lean_object* v_vs_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; 
v_ks_791_ = lean_ctor_get(v_newNode_785_, 0);
lean_inc_ref(v_ks_791_);
v_vs_792_ = lean_ctor_get(v_newNode_785_, 1);
lean_inc_ref(v_vs_792_);
lean_dec_ref(v_newNode_785_);
v___x_793_ = lean_unsigned_to_nat(0u);
v___x_794_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2___redArg___closed__0);
v___x_795_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2_spec__5___redArg(v_x_729_, v_ks_791_, v_vs_792_, v___x_793_, v___x_794_);
lean_dec_ref(v_vs_792_);
lean_dec_ref(v_ks_791_);
return v___x_795_;
}
else
{
return v_newNode_785_;
}
}
else
{
return v_newNode_785_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2_spec__5___redArg(size_t v_depth_798_, lean_object* v_keys_799_, lean_object* v_vals_800_, lean_object* v_i_801_, lean_object* v_entries_802_){
_start:
{
lean_object* v___x_803_; uint8_t v___x_804_; 
v___x_803_ = lean_array_get_size(v_keys_799_);
v___x_804_ = lean_nat_dec_lt(v_i_801_, v___x_803_);
if (v___x_804_ == 0)
{
lean_dec(v_i_801_);
return v_entries_802_;
}
else
{
lean_object* v_k_805_; lean_object* v_v_806_; uint64_t v___y_808_; 
v_k_805_ = lean_array_fget_borrowed(v_keys_799_, v_i_801_);
v_v_806_ = lean_array_fget_borrowed(v_vals_800_, v_i_801_);
if (lean_obj_tag(v_k_805_) == 0)
{
uint64_t v___x_819_; 
v___x_819_ = 1723ULL;
v___y_808_ = v___x_819_;
goto v___jp_807_;
}
else
{
uint64_t v_hash_820_; 
v_hash_820_ = lean_ctor_get_uint64(v_k_805_, sizeof(void*)*2);
v___y_808_ = v_hash_820_;
goto v___jp_807_;
}
v___jp_807_:
{
size_t v_h_809_; size_t v___x_810_; lean_object* v___x_811_; size_t v___x_812_; size_t v___x_813_; size_t v___x_814_; size_t v_h_815_; lean_object* v___x_816_; lean_object* v___x_817_; 
v_h_809_ = lean_uint64_to_usize(v___y_808_);
v___x_810_ = ((size_t)5ULL);
v___x_811_ = lean_unsigned_to_nat(1u);
v___x_812_ = ((size_t)1ULL);
v___x_813_ = lean_usize_sub(v_depth_798_, v___x_812_);
v___x_814_ = lean_usize_mul(v___x_810_, v___x_813_);
v_h_815_ = lean_usize_shift_right(v_h_809_, v___x_814_);
v___x_816_ = lean_nat_add(v_i_801_, v___x_811_);
lean_dec(v_i_801_);
lean_inc(v_v_806_);
lean_inc(v_k_805_);
v___x_817_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2___redArg(v_entries_802_, v_h_815_, v_depth_798_, v_k_805_, v_v_806_);
v_i_801_ = v___x_816_;
v_entries_802_ = v___x_817_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_depth_821_, lean_object* v_keys_822_, lean_object* v_vals_823_, lean_object* v_i_824_, lean_object* v_entries_825_){
_start:
{
size_t v_depth_boxed_826_; lean_object* v_res_827_; 
v_depth_boxed_826_ = lean_unbox_usize(v_depth_821_);
lean_dec(v_depth_821_);
v_res_827_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2_spec__5___redArg(v_depth_boxed_826_, v_keys_822_, v_vals_823_, v_i_824_, v_entries_825_);
lean_dec_ref(v_vals_823_);
lean_dec_ref(v_keys_822_);
return v_res_827_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2___redArg___boxed(lean_object* v_x_828_, lean_object* v_x_829_, lean_object* v_x_830_, lean_object* v_x_831_, lean_object* v_x_832_){
_start:
{
size_t v_x_2086__boxed_833_; size_t v_x_2087__boxed_834_; lean_object* v_res_835_; 
v_x_2086__boxed_833_ = lean_unbox_usize(v_x_829_);
lean_dec(v_x_829_);
v_x_2087__boxed_834_ = lean_unbox_usize(v_x_830_);
lean_dec(v_x_830_);
v_res_835_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2___redArg(v_x_828_, v_x_2086__boxed_833_, v_x_2087__boxed_834_, v_x_831_, v_x_832_);
return v_res_835_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1___redArg(lean_object* v_x_836_, lean_object* v_x_837_, lean_object* v_x_838_){
_start:
{
uint64_t v___y_840_; 
if (lean_obj_tag(v_x_837_) == 0)
{
uint64_t v___x_844_; 
v___x_844_ = 1723ULL;
v___y_840_ = v___x_844_;
goto v___jp_839_;
}
else
{
uint64_t v_hash_845_; 
v_hash_845_ = lean_ctor_get_uint64(v_x_837_, sizeof(void*)*2);
v___y_840_ = v_hash_845_;
goto v___jp_839_;
}
v___jp_839_:
{
size_t v___x_841_; size_t v___x_842_; lean_object* v___x_843_; 
v___x_841_ = lean_uint64_to_usize(v___y_840_);
v___x_842_ = ((size_t)1ULL);
v___x_843_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2___redArg(v_x_836_, v___x_841_, v___x_842_, v_x_837_, v_x_838_);
return v___x_843_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule___redArg(lean_object* v_declName_846_, lean_object* v_a_847_, lean_object* v_a_848_, lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_){
_start:
{
lean_object* v___x_853_; lean_object* v_cache_854_; lean_object* v_backwardRuleName_855_; lean_object* v___x_856_; 
v___x_853_ = lean_st_ref_get(v_a_847_);
v_cache_854_ = lean_ctor_get(v___x_853_, 3);
lean_inc_ref(v_cache_854_);
lean_dec(v___x_853_);
v_backwardRuleName_855_ = lean_ctor_get(v_cache_854_, 0);
lean_inc_ref(v_backwardRuleName_855_);
lean_dec_ref(v_cache_854_);
v___x_856_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0___redArg(v_backwardRuleName_855_, v_declName_846_);
lean_dec_ref(v_backwardRuleName_855_);
if (lean_obj_tag(v___x_856_) == 1)
{
lean_object* v_val_857_; lean_object* v___x_859_; uint8_t v_isShared_860_; uint8_t v_isSharedCheck_864_; 
lean_dec(v_declName_846_);
v_val_857_ = lean_ctor_get(v___x_856_, 0);
v_isSharedCheck_864_ = !lean_is_exclusive(v___x_856_);
if (v_isSharedCheck_864_ == 0)
{
v___x_859_ = v___x_856_;
v_isShared_860_ = v_isSharedCheck_864_;
goto v_resetjp_858_;
}
else
{
lean_inc(v_val_857_);
lean_dec(v___x_856_);
v___x_859_ = lean_box(0);
v_isShared_860_ = v_isSharedCheck_864_;
goto v_resetjp_858_;
}
v_resetjp_858_:
{
lean_object* v___x_862_; 
if (v_isShared_860_ == 0)
{
lean_ctor_set_tag(v___x_859_, 0);
v___x_862_ = v___x_859_;
goto v_reusejp_861_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v_val_857_);
v___x_862_ = v_reuseFailAlloc_863_;
goto v_reusejp_861_;
}
v_reusejp_861_:
{
return v___x_862_;
}
}
}
else
{
lean_object* v___x_865_; lean_object* v___x_866_; 
lean_dec(v___x_856_);
v___x_865_ = lean_box(0);
lean_inc(v_declName_846_);
v___x_866_ = l_Lean_Meta_Sym_mkBackwardRuleFromDecl(v_declName_846_, v___x_865_, v_a_848_, v_a_849_, v_a_850_, v_a_851_);
if (lean_obj_tag(v___x_866_) == 0)
{
lean_object* v_a_867_; lean_object* v___x_869_; uint8_t v_isShared_870_; uint8_t v_isSharedCheck_899_; 
v_a_867_ = lean_ctor_get(v___x_866_, 0);
v_isSharedCheck_899_ = !lean_is_exclusive(v___x_866_);
if (v_isSharedCheck_899_ == 0)
{
v___x_869_ = v___x_866_;
v_isShared_870_ = v_isSharedCheck_899_;
goto v_resetjp_868_;
}
else
{
lean_inc(v_a_867_);
lean_dec(v___x_866_);
v___x_869_ = lean_box(0);
v_isShared_870_ = v_isSharedCheck_899_;
goto v_resetjp_868_;
}
v_resetjp_868_:
{
lean_object* v___x_871_; lean_object* v_cache_872_; lean_object* v_symState_873_; lean_object* v_grindState_874_; lean_object* v_goals_875_; lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_898_; 
v___x_871_ = lean_st_ref_take(v_a_847_);
v_cache_872_ = lean_ctor_get(v___x_871_, 3);
v_symState_873_ = lean_ctor_get(v___x_871_, 0);
v_grindState_874_ = lean_ctor_get(v___x_871_, 1);
v_goals_875_ = lean_ctor_get(v___x_871_, 2);
v_isSharedCheck_898_ = !lean_is_exclusive(v___x_871_);
if (v_isSharedCheck_898_ == 0)
{
v___x_877_ = v___x_871_;
v_isShared_878_ = v_isSharedCheck_898_;
goto v_resetjp_876_;
}
else
{
lean_inc(v_cache_872_);
lean_inc(v_goals_875_);
lean_inc(v_grindState_874_);
lean_inc(v_symState_873_);
lean_dec(v___x_871_);
v___x_877_ = lean_box(0);
v_isShared_878_ = v_isSharedCheck_898_;
goto v_resetjp_876_;
}
v_resetjp_876_:
{
lean_object* v_backwardRuleName_879_; lean_object* v_backwardRuleSyntax_880_; lean_object* v_simpState_881_; lean_object* v_dsimpState_882_; lean_object* v___x_884_; uint8_t v_isShared_885_; uint8_t v_isSharedCheck_897_; 
v_backwardRuleName_879_ = lean_ctor_get(v_cache_872_, 0);
v_backwardRuleSyntax_880_ = lean_ctor_get(v_cache_872_, 1);
v_simpState_881_ = lean_ctor_get(v_cache_872_, 2);
v_dsimpState_882_ = lean_ctor_get(v_cache_872_, 3);
v_isSharedCheck_897_ = !lean_is_exclusive(v_cache_872_);
if (v_isSharedCheck_897_ == 0)
{
v___x_884_ = v_cache_872_;
v_isShared_885_ = v_isSharedCheck_897_;
goto v_resetjp_883_;
}
else
{
lean_inc(v_dsimpState_882_);
lean_inc(v_simpState_881_);
lean_inc(v_backwardRuleSyntax_880_);
lean_inc(v_backwardRuleName_879_);
lean_dec(v_cache_872_);
v___x_884_ = lean_box(0);
v_isShared_885_ = v_isSharedCheck_897_;
goto v_resetjp_883_;
}
v_resetjp_883_:
{
lean_object* v___x_886_; lean_object* v___x_888_; 
lean_inc(v_a_867_);
v___x_886_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1___redArg(v_backwardRuleName_879_, v_declName_846_, v_a_867_);
if (v_isShared_885_ == 0)
{
lean_ctor_set(v___x_884_, 0, v___x_886_);
v___x_888_ = v___x_884_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v___x_886_);
lean_ctor_set(v_reuseFailAlloc_896_, 1, v_backwardRuleSyntax_880_);
lean_ctor_set(v_reuseFailAlloc_896_, 2, v_simpState_881_);
lean_ctor_set(v_reuseFailAlloc_896_, 3, v_dsimpState_882_);
v___x_888_ = v_reuseFailAlloc_896_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
lean_object* v___x_890_; 
if (v_isShared_878_ == 0)
{
lean_ctor_set(v___x_877_, 3, v___x_888_);
v___x_890_ = v___x_877_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v_symState_873_);
lean_ctor_set(v_reuseFailAlloc_895_, 1, v_grindState_874_);
lean_ctor_set(v_reuseFailAlloc_895_, 2, v_goals_875_);
lean_ctor_set(v_reuseFailAlloc_895_, 3, v___x_888_);
v___x_890_ = v_reuseFailAlloc_895_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
lean_object* v___x_891_; lean_object* v___x_893_; 
v___x_891_ = lean_st_ref_put(v_a_847_, v___x_890_);
if (v_isShared_870_ == 0)
{
v___x_893_ = v___x_869_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v_a_867_);
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
}
}
}
else
{
lean_dec(v_declName_846_);
return v___x_866_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule___redArg___boxed(lean_object* v_declName_900_, lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_, lean_object* v_a_904_, lean_object* v_a_905_, lean_object* v_a_906_){
_start:
{
lean_object* v_res_907_; 
v_res_907_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule___redArg(v_declName_900_, v_a_901_, v_a_902_, v_a_903_, v_a_904_, v_a_905_);
lean_dec(v_a_905_);
lean_dec_ref(v_a_904_);
lean_dec(v_a_903_);
lean_dec_ref(v_a_902_);
lean_dec(v_a_901_);
return v_res_907_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule(lean_object* v_declName_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_, lean_object* v_a_914_, lean_object* v_a_915_, lean_object* v_a_916_){
_start:
{
lean_object* v___x_918_; 
v___x_918_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule___redArg(v_declName_908_, v_a_910_, v_a_913_, v_a_914_, v_a_915_, v_a_916_);
return v___x_918_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule___boxed(lean_object* v_declName_919_, lean_object* v_a_920_, lean_object* v_a_921_, lean_object* v_a_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_, lean_object* v_a_928_){
_start:
{
lean_object* v_res_929_; 
v_res_929_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule(v_declName_919_, v_a_920_, v_a_921_, v_a_922_, v_a_923_, v_a_924_, v_a_925_, v_a_926_, v_a_927_);
lean_dec(v_a_927_);
lean_dec_ref(v_a_926_);
lean_dec(v_a_925_);
lean_dec_ref(v_a_924_);
lean_dec(v_a_923_);
lean_dec_ref(v_a_922_);
lean_dec(v_a_921_);
lean_dec_ref(v_a_920_);
return v_res_929_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0(lean_object* v_00_u03b2_930_, lean_object* v_x_931_, lean_object* v_x_932_){
_start:
{
lean_object* v___x_933_; 
v___x_933_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0___redArg(v_x_931_, v_x_932_);
return v___x_933_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0___boxed(lean_object* v_00_u03b2_934_, lean_object* v_x_935_, lean_object* v_x_936_){
_start:
{
lean_object* v_res_937_; 
v_res_937_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0(v_00_u03b2_934_, v_x_935_, v_x_936_);
lean_dec(v_x_936_);
lean_dec_ref(v_x_935_);
return v_res_937_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1(lean_object* v_00_u03b2_938_, lean_object* v_x_939_, lean_object* v_x_940_, lean_object* v_x_941_){
_start:
{
lean_object* v___x_942_; 
v___x_942_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1___redArg(v_x_939_, v_x_940_, v_x_941_);
return v___x_942_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0_spec__0(lean_object* v_00_u03b2_943_, lean_object* v_x_944_, size_t v_x_945_, lean_object* v_x_946_){
_start:
{
lean_object* v___x_947_; 
v___x_947_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0_spec__0___redArg(v_x_944_, v_x_945_, v_x_946_);
return v___x_947_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0_spec__0___boxed(lean_object* v_00_u03b2_948_, lean_object* v_x_949_, lean_object* v_x_950_, lean_object* v_x_951_){
_start:
{
size_t v_x_2357__boxed_952_; lean_object* v_res_953_; 
v_x_2357__boxed_952_ = lean_unbox_usize(v_x_950_);
lean_dec(v_x_950_);
v_res_953_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0_spec__0(v_00_u03b2_948_, v_x_949_, v_x_2357__boxed_952_, v_x_951_);
lean_dec(v_x_951_);
lean_dec_ref(v_x_949_);
return v_res_953_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2(lean_object* v_00_u03b2_954_, lean_object* v_x_955_, size_t v_x_956_, size_t v_x_957_, lean_object* v_x_958_, lean_object* v_x_959_){
_start:
{
lean_object* v___x_960_; 
v___x_960_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2___redArg(v_x_955_, v_x_956_, v_x_957_, v_x_958_, v_x_959_);
return v___x_960_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2___boxed(lean_object* v_00_u03b2_961_, lean_object* v_x_962_, lean_object* v_x_963_, lean_object* v_x_964_, lean_object* v_x_965_, lean_object* v_x_966_){
_start:
{
size_t v_x_2368__boxed_967_; size_t v_x_2369__boxed_968_; lean_object* v_res_969_; 
v_x_2368__boxed_967_ = lean_unbox_usize(v_x_963_);
lean_dec(v_x_963_);
v_x_2369__boxed_968_ = lean_unbox_usize(v_x_964_);
lean_dec(v_x_964_);
v_res_969_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2(v_00_u03b2_961_, v_x_962_, v_x_2368__boxed_967_, v_x_2369__boxed_968_, v_x_965_, v_x_966_);
return v_res_969_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_970_, lean_object* v_keys_971_, lean_object* v_vals_972_, lean_object* v_heq_973_, lean_object* v_i_974_, lean_object* v_k_975_){
_start:
{
lean_object* v___x_976_; 
v___x_976_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0_spec__0_spec__1___redArg(v_keys_971_, v_vals_972_, v_i_974_, v_k_975_);
return v___x_976_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_977_, lean_object* v_keys_978_, lean_object* v_vals_979_, lean_object* v_heq_980_, lean_object* v_i_981_, lean_object* v_k_982_){
_start:
{
lean_object* v_res_983_; 
v_res_983_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0_spec__0_spec__1(v_00_u03b2_977_, v_keys_978_, v_vals_979_, v_heq_980_, v_i_981_, v_k_982_);
lean_dec(v_k_982_);
lean_dec_ref(v_vals_979_);
lean_dec_ref(v_keys_978_);
return v_res_983_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_984_, lean_object* v_n_985_, lean_object* v_k_986_, lean_object* v_v_987_){
_start:
{
lean_object* v___x_988_; 
v___x_988_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2_spec__4___redArg(v_n_985_, v_k_986_, v_v_987_);
return v___x_988_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_989_, size_t v_depth_990_, lean_object* v_keys_991_, lean_object* v_vals_992_, lean_object* v_heq_993_, lean_object* v_i_994_, lean_object* v_entries_995_){
_start:
{
lean_object* v___x_996_; 
v___x_996_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2_spec__5___redArg(v_depth_990_, v_keys_991_, v_vals_992_, v_i_994_, v_entries_995_);
return v___x_996_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_997_, lean_object* v_depth_998_, lean_object* v_keys_999_, lean_object* v_vals_1000_, lean_object* v_heq_1001_, lean_object* v_i_1002_, lean_object* v_entries_1003_){
_start:
{
size_t v_depth_boxed_1004_; lean_object* v_res_1005_; 
v_depth_boxed_1004_ = lean_unbox_usize(v_depth_998_);
lean_dec(v_depth_998_);
v_res_1005_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2_spec__5(v_00_u03b2_997_, v_depth_boxed_1004_, v_keys_999_, v_vals_1000_, v_heq_1001_, v_i_1002_, v_entries_1003_);
lean_dec_ref(v_vals_1000_);
lean_dec_ref(v_keys_999_);
return v_res_1005_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_1006_, lean_object* v_x_1007_, lean_object* v_x_1008_, lean_object* v_x_1009_, lean_object* v_x_1010_){
_start:
{
lean_object* v___x_1011_; 
v___x_1011_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2_spec__4_spec__5___redArg(v_x_1007_, v_x_1008_, v_x_1009_, v_x_1010_);
return v___x_1011_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__1___redArg(lean_object* v_e_1012_, lean_object* v___y_1013_){
_start:
{
uint8_t v___x_1015_; 
v___x_1015_ = l_Lean_Expr_hasMVar(v_e_1012_);
if (v___x_1015_ == 0)
{
lean_object* v___x_1016_; 
v___x_1016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1016_, 0, v_e_1012_);
return v___x_1016_;
}
else
{
lean_object* v___x_1017_; lean_object* v_mctx_1018_; lean_object* v___x_1019_; lean_object* v_fst_1020_; lean_object* v_snd_1021_; lean_object* v___x_1022_; lean_object* v_cache_1023_; lean_object* v_zetaDeltaFVarIds_1024_; lean_object* v_postponed_1025_; lean_object* v_diag_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1035_; 
v___x_1017_ = lean_st_ref_get(v___y_1013_);
v_mctx_1018_ = lean_ctor_get(v___x_1017_, 0);
lean_inc_ref(v_mctx_1018_);
lean_dec(v___x_1017_);
v___x_1019_ = l_Lean_instantiateMVarsCore(v_mctx_1018_, v_e_1012_);
v_fst_1020_ = lean_ctor_get(v___x_1019_, 0);
lean_inc(v_fst_1020_);
v_snd_1021_ = lean_ctor_get(v___x_1019_, 1);
lean_inc(v_snd_1021_);
lean_dec_ref(v___x_1019_);
v___x_1022_ = lean_st_ref_take(v___y_1013_);
v_cache_1023_ = lean_ctor_get(v___x_1022_, 1);
v_zetaDeltaFVarIds_1024_ = lean_ctor_get(v___x_1022_, 2);
v_postponed_1025_ = lean_ctor_get(v___x_1022_, 3);
v_diag_1026_ = lean_ctor_get(v___x_1022_, 4);
v_isSharedCheck_1035_ = !lean_is_exclusive(v___x_1022_);
if (v_isSharedCheck_1035_ == 0)
{
lean_object* v_unused_1036_; 
v_unused_1036_ = lean_ctor_get(v___x_1022_, 0);
lean_dec(v_unused_1036_);
v___x_1028_ = v___x_1022_;
v_isShared_1029_ = v_isSharedCheck_1035_;
goto v_resetjp_1027_;
}
else
{
lean_inc(v_diag_1026_);
lean_inc(v_postponed_1025_);
lean_inc(v_zetaDeltaFVarIds_1024_);
lean_inc(v_cache_1023_);
lean_dec(v___x_1022_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1035_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
lean_object* v___x_1031_; 
if (v_isShared_1029_ == 0)
{
lean_ctor_set(v___x_1028_, 0, v_snd_1021_);
v___x_1031_ = v___x_1028_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v_snd_1021_);
lean_ctor_set(v_reuseFailAlloc_1034_, 1, v_cache_1023_);
lean_ctor_set(v_reuseFailAlloc_1034_, 2, v_zetaDeltaFVarIds_1024_);
lean_ctor_set(v_reuseFailAlloc_1034_, 3, v_postponed_1025_);
lean_ctor_set(v_reuseFailAlloc_1034_, 4, v_diag_1026_);
v___x_1031_ = v_reuseFailAlloc_1034_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
lean_object* v___x_1032_; lean_object* v___x_1033_; 
v___x_1032_ = lean_st_ref_put(v___y_1013_, v___x_1031_);
v___x_1033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1033_, 0, v_fst_1020_);
return v___x_1033_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__1___redArg___boxed(lean_object* v_e_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_){
_start:
{
lean_object* v_res_1040_; 
v_res_1040_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__1___redArg(v_e_1037_, v___y_1038_);
lean_dec(v___y_1038_);
return v_res_1040_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__1(lean_object* v_e_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_){
_start:
{
lean_object* v___x_1051_; 
v___x_1051_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__1___redArg(v_e_1041_, v___y_1047_);
return v___x_1051_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__1___boxed(lean_object* v_e_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_){
_start:
{
lean_object* v_res_1062_; 
v_res_1062_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__1(v_e_1052_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_);
lean_dec(v___y_1060_);
lean_dec_ref(v___y_1059_);
lean_dec(v___y_1058_);
lean_dec_ref(v___y_1057_);
lean_dec(v___y_1056_);
lean_dec_ref(v___y_1055_);
lean_dec(v___y_1054_);
lean_dec_ref(v___y_1053_);
return v_res_1062_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm___lam__0(lean_object* v_term_1063_, lean_object* v___x_1064_, uint8_t v___x_1065_, uint8_t v___x_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_){
_start:
{
lean_object* v___x_1076_; 
v___x_1076_ = l_Lean_Elab_Term_elabTerm(v_term_1063_, v___x_1064_, v___x_1065_, v___x_1065_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_);
if (lean_obj_tag(v___x_1076_) == 0)
{
lean_object* v_a_1077_; uint8_t v___x_1078_; lean_object* v___x_1079_; 
v_a_1077_ = lean_ctor_get(v___x_1076_, 0);
lean_inc(v_a_1077_);
lean_dec_ref_known(v___x_1076_, 1);
v___x_1078_ = 1;
v___x_1079_ = l_Lean_Elab_Term_synthesizeSyntheticMVars(v___x_1078_, v___x_1066_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_);
if (lean_obj_tag(v___x_1079_) == 0)
{
lean_object* v___x_1080_; 
lean_dec_ref_known(v___x_1079_, 1);
v___x_1080_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__1___redArg(v_a_1077_, v___y_1072_);
return v___x_1080_;
}
else
{
lean_object* v_a_1081_; lean_object* v___x_1083_; uint8_t v_isShared_1084_; uint8_t v_isSharedCheck_1088_; 
lean_dec(v_a_1077_);
v_a_1081_ = lean_ctor_get(v___x_1079_, 0);
v_isSharedCheck_1088_ = !lean_is_exclusive(v___x_1079_);
if (v_isSharedCheck_1088_ == 0)
{
v___x_1083_ = v___x_1079_;
v_isShared_1084_ = v_isSharedCheck_1088_;
goto v_resetjp_1082_;
}
else
{
lean_inc(v_a_1081_);
lean_dec(v___x_1079_);
v___x_1083_ = lean_box(0);
v_isShared_1084_ = v_isSharedCheck_1088_;
goto v_resetjp_1082_;
}
v_resetjp_1082_:
{
lean_object* v___x_1086_; 
if (v_isShared_1084_ == 0)
{
v___x_1086_ = v___x_1083_;
goto v_reusejp_1085_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v_a_1081_);
v___x_1086_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1085_;
}
v_reusejp_1085_:
{
return v___x_1086_;
}
}
}
}
else
{
return v___x_1076_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm___lam__0___boxed(lean_object* v_term_1089_, lean_object* v___x_1090_, lean_object* v___x_1091_, lean_object* v___x_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_){
_start:
{
uint8_t v___x_3669__boxed_1102_; uint8_t v___x_3670__boxed_1103_; lean_object* v_res_1104_; 
v___x_3669__boxed_1102_ = lean_unbox(v___x_1091_);
v___x_3670__boxed_1103_ = lean_unbox(v___x_1092_);
v_res_1104_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm___lam__0(v_term_1089_, v___x_1090_, v___x_3669__boxed_1102_, v___x_3670__boxed_1103_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_);
lean_dec(v___y_1100_);
lean_dec_ref(v___y_1099_);
lean_dec(v___y_1098_);
lean_dec_ref(v___y_1097_);
lean_dec(v___y_1096_);
lean_dec_ref(v___y_1095_);
lean_dec(v___y_1094_);
lean_dec_ref(v___y_1093_);
return v_res_1104_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3_spec__5_spec__6___redArg(lean_object* v_x_1105_, lean_object* v_x_1106_, lean_object* v_x_1107_, lean_object* v_x_1108_){
_start:
{
lean_object* v_ks_1109_; lean_object* v_vs_1110_; lean_object* v___x_1112_; uint8_t v_isShared_1113_; uint8_t v_isSharedCheck_1142_; 
v_ks_1109_ = lean_ctor_get(v_x_1105_, 0);
v_vs_1110_ = lean_ctor_get(v_x_1105_, 1);
v_isSharedCheck_1142_ = !lean_is_exclusive(v_x_1105_);
if (v_isSharedCheck_1142_ == 0)
{
v___x_1112_ = v_x_1105_;
v_isShared_1113_ = v_isSharedCheck_1142_;
goto v_resetjp_1111_;
}
else
{
lean_inc(v_vs_1110_);
lean_inc(v_ks_1109_);
lean_dec(v_x_1105_);
v___x_1112_ = lean_box(0);
v_isShared_1113_ = v_isSharedCheck_1142_;
goto v_resetjp_1111_;
}
v_resetjp_1111_:
{
lean_object* v___x_1121_; uint8_t v___x_1122_; 
v___x_1121_ = lean_array_get_size(v_ks_1109_);
v___x_1122_ = lean_nat_dec_lt(v_x_1106_, v___x_1121_);
if (v___x_1122_ == 0)
{
lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; 
lean_del_object(v___x_1112_);
lean_dec(v_x_1106_);
v___x_1123_ = lean_array_push(v_ks_1109_, v_x_1107_);
v___x_1124_ = lean_array_push(v_vs_1110_, v_x_1108_);
v___x_1125_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1125_, 0, v___x_1123_);
lean_ctor_set(v___x_1125_, 1, v___x_1124_);
return v___x_1125_;
}
else
{
lean_object* v_fst_1126_; lean_object* v_snd_1127_; lean_object* v_k_x27_1128_; lean_object* v_fst_1129_; lean_object* v_snd_1130_; lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1141_; 
v_fst_1126_ = lean_ctor_get(v_x_1107_, 0);
v_snd_1127_ = lean_ctor_get(v_x_1107_, 1);
v_k_x27_1128_ = lean_array_fget(v_ks_1109_, v_x_1106_);
v_fst_1129_ = lean_ctor_get(v_k_x27_1128_, 0);
v_snd_1130_ = lean_ctor_get(v_k_x27_1128_, 1);
v_isSharedCheck_1141_ = !lean_is_exclusive(v_k_x27_1128_);
if (v_isSharedCheck_1141_ == 0)
{
v___x_1132_ = v_k_x27_1128_;
v_isShared_1133_ = v_isSharedCheck_1141_;
goto v_resetjp_1131_;
}
else
{
lean_inc(v_snd_1130_);
lean_inc(v_fst_1129_);
lean_dec(v_k_x27_1128_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1141_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
uint8_t v___x_1134_; 
v___x_1134_ = lean_nat_dec_eq(v_fst_1126_, v_fst_1129_);
lean_dec(v_fst_1129_);
if (v___x_1134_ == 0)
{
lean_del_object(v___x_1132_);
lean_dec(v_snd_1130_);
goto v___jp_1114_;
}
else
{
uint8_t v___x_1135_; 
v___x_1135_ = lean_nat_dec_eq(v_snd_1127_, v_snd_1130_);
lean_dec(v_snd_1130_);
if (v___x_1135_ == 0)
{
lean_del_object(v___x_1132_);
goto v___jp_1114_;
}
else
{
lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1139_; 
lean_del_object(v___x_1112_);
v___x_1136_ = lean_array_fset(v_ks_1109_, v_x_1106_, v_x_1107_);
v___x_1137_ = lean_array_fset(v_vs_1110_, v_x_1106_, v_x_1108_);
lean_dec(v_x_1106_);
if (v_isShared_1133_ == 0)
{
lean_ctor_set_tag(v___x_1132_, 1);
lean_ctor_set(v___x_1132_, 1, v___x_1137_);
lean_ctor_set(v___x_1132_, 0, v___x_1136_);
v___x_1139_ = v___x_1132_;
goto v_reusejp_1138_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v___x_1136_);
lean_ctor_set(v_reuseFailAlloc_1140_, 1, v___x_1137_);
v___x_1139_ = v_reuseFailAlloc_1140_;
goto v_reusejp_1138_;
}
v_reusejp_1138_:
{
return v___x_1139_;
}
}
}
}
}
v___jp_1114_:
{
lean_object* v___x_1116_; 
if (v_isShared_1113_ == 0)
{
v___x_1116_ = v___x_1112_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v_ks_1109_);
lean_ctor_set(v_reuseFailAlloc_1120_, 1, v_vs_1110_);
v___x_1116_ = v_reuseFailAlloc_1120_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
lean_object* v___x_1117_; lean_object* v___x_1118_; 
v___x_1117_ = lean_unsigned_to_nat(1u);
v___x_1118_ = lean_nat_add(v_x_1106_, v___x_1117_);
lean_dec(v_x_1106_);
v_x_1105_ = v___x_1116_;
v_x_1106_ = v___x_1118_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3_spec__5___redArg(lean_object* v_n_1143_, lean_object* v_k_1144_, lean_object* v_v_1145_){
_start:
{
lean_object* v___x_1146_; lean_object* v___x_1147_; 
v___x_1146_ = lean_unsigned_to_nat(0u);
v___x_1147_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3_spec__5_spec__6___redArg(v_n_1143_, v___x_1146_, v_k_1144_, v_v_1145_);
return v___x_1147_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3___redArg(lean_object* v_x_1148_, size_t v_x_1149_, size_t v_x_1150_, lean_object* v_x_1151_, lean_object* v_x_1152_){
_start:
{
if (lean_obj_tag(v_x_1148_) == 0)
{
lean_object* v_es_1153_; size_t v___x_1154_; size_t v___x_1155_; lean_object* v_j_1156_; lean_object* v___x_1157_; uint8_t v___x_1158_; 
v_es_1153_ = lean_ctor_get(v_x_1148_, 0);
v___x_1154_ = ((size_t)31ULL);
v___x_1155_ = lean_usize_land(v_x_1149_, v___x_1154_);
v_j_1156_ = lean_usize_to_nat(v___x_1155_);
v___x_1157_ = lean_array_get_size(v_es_1153_);
v___x_1158_ = lean_nat_dec_lt(v_j_1156_, v___x_1157_);
if (v___x_1158_ == 0)
{
lean_dec(v_j_1156_);
lean_dec(v_x_1152_);
lean_dec_ref(v_x_1151_);
return v_x_1148_;
}
else
{
lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1203_; 
lean_inc_ref(v_es_1153_);
v_isSharedCheck_1203_ = !lean_is_exclusive(v_x_1148_);
if (v_isSharedCheck_1203_ == 0)
{
lean_object* v_unused_1204_; 
v_unused_1204_ = lean_ctor_get(v_x_1148_, 0);
lean_dec(v_unused_1204_);
v___x_1160_ = v_x_1148_;
v_isShared_1161_ = v_isSharedCheck_1203_;
goto v_resetjp_1159_;
}
else
{
lean_dec(v_x_1148_);
v___x_1160_ = lean_box(0);
v_isShared_1161_ = v_isSharedCheck_1203_;
goto v_resetjp_1159_;
}
v_resetjp_1159_:
{
lean_object* v_v_1162_; lean_object* v___x_1163_; lean_object* v_xs_x27_1164_; lean_object* v___y_1166_; 
v_v_1162_ = lean_array_fget(v_es_1153_, v_j_1156_);
v___x_1163_ = lean_box(0);
v_xs_x27_1164_ = lean_array_fset(v_es_1153_, v_j_1156_, v___x_1163_);
switch(lean_obj_tag(v_v_1162_))
{
case 0:
{
lean_object* v_key_1171_; lean_object* v_val_1172_; lean_object* v___x_1174_; uint8_t v_isShared_1175_; uint8_t v_isSharedCheck_1188_; 
v_key_1171_ = lean_ctor_get(v_v_1162_, 0);
v_val_1172_ = lean_ctor_get(v_v_1162_, 1);
v_isSharedCheck_1188_ = !lean_is_exclusive(v_v_1162_);
if (v_isSharedCheck_1188_ == 0)
{
v___x_1174_ = v_v_1162_;
v_isShared_1175_ = v_isSharedCheck_1188_;
goto v_resetjp_1173_;
}
else
{
lean_inc(v_val_1172_);
lean_inc(v_key_1171_);
lean_dec(v_v_1162_);
v___x_1174_ = lean_box(0);
v_isShared_1175_ = v_isSharedCheck_1188_;
goto v_resetjp_1173_;
}
v_resetjp_1173_:
{
lean_object* v_fst_1179_; lean_object* v_snd_1180_; lean_object* v_fst_1181_; lean_object* v_snd_1182_; uint8_t v___x_1183_; 
v_fst_1179_ = lean_ctor_get(v_x_1151_, 0);
v_snd_1180_ = lean_ctor_get(v_x_1151_, 1);
v_fst_1181_ = lean_ctor_get(v_key_1171_, 0);
v_snd_1182_ = lean_ctor_get(v_key_1171_, 1);
v___x_1183_ = lean_nat_dec_eq(v_fst_1179_, v_fst_1181_);
if (v___x_1183_ == 0)
{
lean_del_object(v___x_1174_);
goto v___jp_1176_;
}
else
{
uint8_t v___x_1184_; 
v___x_1184_ = lean_nat_dec_eq(v_snd_1180_, v_snd_1182_);
if (v___x_1184_ == 0)
{
lean_del_object(v___x_1174_);
goto v___jp_1176_;
}
else
{
lean_object* v___x_1186_; 
lean_dec(v_val_1172_);
lean_dec(v_key_1171_);
if (v_isShared_1175_ == 0)
{
lean_ctor_set(v___x_1174_, 1, v_x_1152_);
lean_ctor_set(v___x_1174_, 0, v_x_1151_);
v___x_1186_ = v___x_1174_;
goto v_reusejp_1185_;
}
else
{
lean_object* v_reuseFailAlloc_1187_; 
v_reuseFailAlloc_1187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1187_, 0, v_x_1151_);
lean_ctor_set(v_reuseFailAlloc_1187_, 1, v_x_1152_);
v___x_1186_ = v_reuseFailAlloc_1187_;
goto v_reusejp_1185_;
}
v_reusejp_1185_:
{
v___y_1166_ = v___x_1186_;
goto v___jp_1165_;
}
}
}
v___jp_1176_:
{
lean_object* v___x_1177_; lean_object* v___x_1178_; 
v___x_1177_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1171_, v_val_1172_, v_x_1151_, v_x_1152_);
v___x_1178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1178_, 0, v___x_1177_);
v___y_1166_ = v___x_1178_;
goto v___jp_1165_;
}
}
}
case 1:
{
lean_object* v_node_1189_; lean_object* v___x_1191_; uint8_t v_isShared_1192_; uint8_t v_isSharedCheck_1201_; 
v_node_1189_ = lean_ctor_get(v_v_1162_, 0);
v_isSharedCheck_1201_ = !lean_is_exclusive(v_v_1162_);
if (v_isSharedCheck_1201_ == 0)
{
v___x_1191_ = v_v_1162_;
v_isShared_1192_ = v_isSharedCheck_1201_;
goto v_resetjp_1190_;
}
else
{
lean_inc(v_node_1189_);
lean_dec(v_v_1162_);
v___x_1191_ = lean_box(0);
v_isShared_1192_ = v_isSharedCheck_1201_;
goto v_resetjp_1190_;
}
v_resetjp_1190_:
{
size_t v___x_1193_; size_t v___x_1194_; size_t v___x_1195_; size_t v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1199_; 
v___x_1193_ = ((size_t)5ULL);
v___x_1194_ = lean_usize_shift_right(v_x_1149_, v___x_1193_);
v___x_1195_ = ((size_t)1ULL);
v___x_1196_ = lean_usize_add(v_x_1150_, v___x_1195_);
v___x_1197_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3___redArg(v_node_1189_, v___x_1194_, v___x_1196_, v_x_1151_, v_x_1152_);
if (v_isShared_1192_ == 0)
{
lean_ctor_set(v___x_1191_, 0, v___x_1197_);
v___x_1199_ = v___x_1191_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v___x_1197_);
v___x_1199_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
v___y_1166_ = v___x_1199_;
goto v___jp_1165_;
}
}
}
default: 
{
lean_object* v___x_1202_; 
v___x_1202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1202_, 0, v_x_1151_);
lean_ctor_set(v___x_1202_, 1, v_x_1152_);
v___y_1166_ = v___x_1202_;
goto v___jp_1165_;
}
}
v___jp_1165_:
{
lean_object* v___x_1167_; lean_object* v___x_1169_; 
v___x_1167_ = lean_array_fset(v_xs_x27_1164_, v_j_1156_, v___y_1166_);
lean_dec(v_j_1156_);
if (v_isShared_1161_ == 0)
{
lean_ctor_set(v___x_1160_, 0, v___x_1167_);
v___x_1169_ = v___x_1160_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v___x_1167_);
v___x_1169_ = v_reuseFailAlloc_1170_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
return v___x_1169_;
}
}
}
}
}
else
{
lean_object* v_ks_1205_; lean_object* v_vs_1206_; lean_object* v___x_1208_; uint8_t v_isShared_1209_; uint8_t v_isSharedCheck_1224_; 
v_ks_1205_ = lean_ctor_get(v_x_1148_, 0);
v_vs_1206_ = lean_ctor_get(v_x_1148_, 1);
v_isSharedCheck_1224_ = !lean_is_exclusive(v_x_1148_);
if (v_isSharedCheck_1224_ == 0)
{
v___x_1208_ = v_x_1148_;
v_isShared_1209_ = v_isSharedCheck_1224_;
goto v_resetjp_1207_;
}
else
{
lean_inc(v_vs_1206_);
lean_inc(v_ks_1205_);
lean_dec(v_x_1148_);
v___x_1208_ = lean_box(0);
v_isShared_1209_ = v_isSharedCheck_1224_;
goto v_resetjp_1207_;
}
v_resetjp_1207_:
{
lean_object* v___x_1211_; 
if (v_isShared_1209_ == 0)
{
v___x_1211_ = v___x_1208_;
goto v_reusejp_1210_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v_ks_1205_);
lean_ctor_set(v_reuseFailAlloc_1223_, 1, v_vs_1206_);
v___x_1211_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1210_;
}
v_reusejp_1210_:
{
lean_object* v_newNode_1212_; size_t v___x_1213_; uint8_t v___x_1214_; 
v_newNode_1212_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3_spec__5___redArg(v___x_1211_, v_x_1151_, v_x_1152_);
v___x_1213_ = ((size_t)7ULL);
v___x_1214_ = lean_usize_dec_le(v___x_1213_, v_x_1150_);
if (v___x_1214_ == 0)
{
lean_object* v___x_1215_; lean_object* v___x_1216_; uint8_t v___x_1217_; 
v___x_1215_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1212_);
v___x_1216_ = lean_unsigned_to_nat(4u);
v___x_1217_ = lean_nat_dec_lt(v___x_1215_, v___x_1216_);
lean_dec(v___x_1215_);
if (v___x_1217_ == 0)
{
lean_object* v_ks_1218_; lean_object* v_vs_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; 
v_ks_1218_ = lean_ctor_get(v_newNode_1212_, 0);
lean_inc_ref(v_ks_1218_);
v_vs_1219_ = lean_ctor_get(v_newNode_1212_, 1);
lean_inc_ref(v_vs_1219_);
lean_dec_ref(v_newNode_1212_);
v___x_1220_ = lean_unsigned_to_nat(0u);
v___x_1221_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2___redArg___closed__0);
v___x_1222_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3_spec__6___redArg(v_x_1150_, v_ks_1218_, v_vs_1219_, v___x_1220_, v___x_1221_);
lean_dec_ref(v_vs_1219_);
lean_dec_ref(v_ks_1218_);
return v___x_1222_;
}
else
{
return v_newNode_1212_;
}
}
else
{
return v_newNode_1212_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3_spec__6___redArg(size_t v_depth_1225_, lean_object* v_keys_1226_, lean_object* v_vals_1227_, lean_object* v_i_1228_, lean_object* v_entries_1229_){
_start:
{
lean_object* v___x_1230_; uint8_t v___x_1231_; 
v___x_1230_ = lean_array_get_size(v_keys_1226_);
v___x_1231_ = lean_nat_dec_lt(v_i_1228_, v___x_1230_);
if (v___x_1231_ == 0)
{
lean_dec(v_i_1228_);
return v_entries_1229_;
}
else
{
lean_object* v_k_1232_; lean_object* v_fst_1233_; lean_object* v_snd_1234_; lean_object* v_v_1235_; uint64_t v___x_1236_; uint64_t v___x_1237_; uint64_t v___x_1238_; size_t v_h_1239_; size_t v___x_1240_; lean_object* v___x_1241_; size_t v___x_1242_; size_t v___x_1243_; size_t v___x_1244_; size_t v_h_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; 
v_k_1232_ = lean_array_fget_borrowed(v_keys_1226_, v_i_1228_);
v_fst_1233_ = lean_ctor_get(v_k_1232_, 0);
v_snd_1234_ = lean_ctor_get(v_k_1232_, 1);
v_v_1235_ = lean_array_fget_borrowed(v_vals_1227_, v_i_1228_);
v___x_1236_ = lean_uint64_of_nat(v_fst_1233_);
v___x_1237_ = lean_uint64_of_nat(v_snd_1234_);
v___x_1238_ = lean_uint64_mix_hash(v___x_1236_, v___x_1237_);
v_h_1239_ = lean_uint64_to_usize(v___x_1238_);
v___x_1240_ = ((size_t)5ULL);
v___x_1241_ = lean_unsigned_to_nat(1u);
v___x_1242_ = ((size_t)1ULL);
v___x_1243_ = lean_usize_sub(v_depth_1225_, v___x_1242_);
v___x_1244_ = lean_usize_mul(v___x_1240_, v___x_1243_);
v_h_1245_ = lean_usize_shift_right(v_h_1239_, v___x_1244_);
v___x_1246_ = lean_nat_add(v_i_1228_, v___x_1241_);
lean_dec(v_i_1228_);
lean_inc(v_v_1235_);
lean_inc(v_k_1232_);
v___x_1247_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3___redArg(v_entries_1229_, v_h_1245_, v_depth_1225_, v_k_1232_, v_v_1235_);
v_i_1228_ = v___x_1246_;
v_entries_1229_ = v___x_1247_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_depth_1249_, lean_object* v_keys_1250_, lean_object* v_vals_1251_, lean_object* v_i_1252_, lean_object* v_entries_1253_){
_start:
{
size_t v_depth_boxed_1254_; lean_object* v_res_1255_; 
v_depth_boxed_1254_ = lean_unbox_usize(v_depth_1249_);
lean_dec(v_depth_1249_);
v_res_1255_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3_spec__6___redArg(v_depth_boxed_1254_, v_keys_1250_, v_vals_1251_, v_i_1252_, v_entries_1253_);
lean_dec_ref(v_vals_1251_);
lean_dec_ref(v_keys_1250_);
return v_res_1255_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3___redArg___boxed(lean_object* v_x_1256_, lean_object* v_x_1257_, lean_object* v_x_1258_, lean_object* v_x_1259_, lean_object* v_x_1260_){
_start:
{
size_t v_x_3828__boxed_1261_; size_t v_x_3829__boxed_1262_; lean_object* v_res_1263_; 
v_x_3828__boxed_1261_ = lean_unbox_usize(v_x_1257_);
lean_dec(v_x_1257_);
v_x_3829__boxed_1262_ = lean_unbox_usize(v_x_1258_);
lean_dec(v_x_1258_);
v_res_1263_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3___redArg(v_x_1256_, v_x_3828__boxed_1261_, v_x_3829__boxed_1262_, v_x_1259_, v_x_1260_);
return v_res_1263_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2___redArg(lean_object* v_x_1264_, lean_object* v_x_1265_, lean_object* v_x_1266_){
_start:
{
lean_object* v_fst_1267_; lean_object* v_snd_1268_; uint64_t v___x_1269_; uint64_t v___x_1270_; uint64_t v___x_1271_; size_t v___x_1272_; size_t v___x_1273_; lean_object* v___x_1274_; 
v_fst_1267_ = lean_ctor_get(v_x_1265_, 0);
v_snd_1268_ = lean_ctor_get(v_x_1265_, 1);
v___x_1269_ = lean_uint64_of_nat(v_fst_1267_);
v___x_1270_ = lean_uint64_of_nat(v_snd_1268_);
v___x_1271_ = lean_uint64_mix_hash(v___x_1269_, v___x_1270_);
v___x_1272_ = lean_uint64_to_usize(v___x_1271_);
v___x_1273_ = ((size_t)1ULL);
v___x_1274_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3___redArg(v_x_1264_, v___x_1272_, v___x_1273_, v_x_1265_, v_x_1266_);
return v___x_1274_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0_spec__0_spec__2___redArg(lean_object* v_keys_1275_, lean_object* v_vals_1276_, lean_object* v_i_1277_, lean_object* v_k_1278_){
_start:
{
lean_object* v___x_1283_; uint8_t v___x_1284_; 
v___x_1283_ = lean_array_get_size(v_keys_1275_);
v___x_1284_ = lean_nat_dec_lt(v_i_1277_, v___x_1283_);
if (v___x_1284_ == 0)
{
lean_object* v___x_1285_; 
lean_dec(v_i_1277_);
v___x_1285_ = lean_box(0);
return v___x_1285_;
}
else
{
lean_object* v_fst_1286_; lean_object* v_snd_1287_; lean_object* v_k_x27_1288_; lean_object* v_fst_1289_; lean_object* v_snd_1290_; uint8_t v___x_1291_; 
v_fst_1286_ = lean_ctor_get(v_k_1278_, 0);
v_snd_1287_ = lean_ctor_get(v_k_1278_, 1);
v_k_x27_1288_ = lean_array_fget_borrowed(v_keys_1275_, v_i_1277_);
v_fst_1289_ = lean_ctor_get(v_k_x27_1288_, 0);
v_snd_1290_ = lean_ctor_get(v_k_x27_1288_, 1);
v___x_1291_ = lean_nat_dec_eq(v_fst_1286_, v_fst_1289_);
if (v___x_1291_ == 0)
{
goto v___jp_1279_;
}
else
{
uint8_t v___x_1292_; 
v___x_1292_ = lean_nat_dec_eq(v_snd_1287_, v_snd_1290_);
if (v___x_1292_ == 0)
{
goto v___jp_1279_;
}
else
{
lean_object* v___x_1293_; lean_object* v___x_1294_; 
v___x_1293_ = lean_array_fget_borrowed(v_vals_1276_, v_i_1277_);
lean_dec(v_i_1277_);
lean_inc(v___x_1293_);
v___x_1294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1294_, 0, v___x_1293_);
return v___x_1294_;
}
}
}
v___jp_1279_:
{
lean_object* v___x_1280_; lean_object* v___x_1281_; 
v___x_1280_ = lean_unsigned_to_nat(1u);
v___x_1281_ = lean_nat_add(v_i_1277_, v___x_1280_);
lean_dec(v_i_1277_);
v_i_1277_ = v___x_1281_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_keys_1295_, lean_object* v_vals_1296_, lean_object* v_i_1297_, lean_object* v_k_1298_){
_start:
{
lean_object* v_res_1299_; 
v_res_1299_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0_spec__0_spec__2___redArg(v_keys_1295_, v_vals_1296_, v_i_1297_, v_k_1298_);
lean_dec_ref(v_k_1298_);
lean_dec_ref(v_vals_1296_);
lean_dec_ref(v_keys_1295_);
return v_res_1299_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0_spec__0___redArg(lean_object* v_x_1300_, size_t v_x_1301_, lean_object* v_x_1302_){
_start:
{
if (lean_obj_tag(v_x_1300_) == 0)
{
lean_object* v_es_1303_; lean_object* v___x_1304_; size_t v___x_1305_; size_t v___x_1306_; lean_object* v_j_1307_; lean_object* v___x_1308_; 
v_es_1303_ = lean_ctor_get(v_x_1300_, 0);
v___x_1304_ = lean_box(2);
v___x_1305_ = ((size_t)31ULL);
v___x_1306_ = lean_usize_land(v_x_1301_, v___x_1305_);
v_j_1307_ = lean_usize_to_nat(v___x_1306_);
v___x_1308_ = lean_array_get_borrowed(v___x_1304_, v_es_1303_, v_j_1307_);
lean_dec(v_j_1307_);
switch(lean_obj_tag(v___x_1308_))
{
case 0:
{
lean_object* v_key_1309_; lean_object* v_val_1310_; lean_object* v_fst_1311_; lean_object* v_snd_1312_; lean_object* v_fst_1313_; lean_object* v_snd_1314_; uint8_t v___x_1315_; 
v_key_1309_ = lean_ctor_get(v___x_1308_, 0);
v_val_1310_ = lean_ctor_get(v___x_1308_, 1);
v_fst_1311_ = lean_ctor_get(v_x_1302_, 0);
v_snd_1312_ = lean_ctor_get(v_x_1302_, 1);
v_fst_1313_ = lean_ctor_get(v_key_1309_, 0);
v_snd_1314_ = lean_ctor_get(v_key_1309_, 1);
v___x_1315_ = lean_nat_dec_eq(v_fst_1311_, v_fst_1313_);
if (v___x_1315_ == 0)
{
lean_object* v___x_1316_; 
v___x_1316_ = lean_box(0);
return v___x_1316_;
}
else
{
uint8_t v___x_1317_; 
v___x_1317_ = lean_nat_dec_eq(v_snd_1312_, v_snd_1314_);
if (v___x_1317_ == 0)
{
lean_object* v___x_1318_; 
v___x_1318_ = lean_box(0);
return v___x_1318_;
}
else
{
lean_object* v___x_1319_; 
lean_inc(v_val_1310_);
v___x_1319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1319_, 0, v_val_1310_);
return v___x_1319_;
}
}
}
case 1:
{
lean_object* v_node_1320_; size_t v___x_1321_; size_t v___x_1322_; 
v_node_1320_ = lean_ctor_get(v___x_1308_, 0);
v___x_1321_ = ((size_t)5ULL);
v___x_1322_ = lean_usize_shift_right(v_x_1301_, v___x_1321_);
v_x_1300_ = v_node_1320_;
v_x_1301_ = v___x_1322_;
goto _start;
}
default: 
{
lean_object* v___x_1324_; 
v___x_1324_ = lean_box(0);
return v___x_1324_;
}
}
}
else
{
lean_object* v_ks_1325_; lean_object* v_vs_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; 
v_ks_1325_ = lean_ctor_get(v_x_1300_, 0);
v_vs_1326_ = lean_ctor_get(v_x_1300_, 1);
v___x_1327_ = lean_unsigned_to_nat(0u);
v___x_1328_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0_spec__0_spec__2___redArg(v_ks_1325_, v_vs_1326_, v___x_1327_, v_x_1302_);
return v___x_1328_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0_spec__0___redArg___boxed(lean_object* v_x_1329_, lean_object* v_x_1330_, lean_object* v_x_1331_){
_start:
{
size_t v_x_4047__boxed_1332_; lean_object* v_res_1333_; 
v_x_4047__boxed_1332_ = lean_unbox_usize(v_x_1330_);
lean_dec(v_x_1330_);
v_res_1333_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0_spec__0___redArg(v_x_1329_, v_x_4047__boxed_1332_, v_x_1331_);
lean_dec_ref(v_x_1331_);
lean_dec_ref(v_x_1329_);
return v_res_1333_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0___redArg(lean_object* v_x_1334_, lean_object* v_x_1335_){
_start:
{
lean_object* v_fst_1336_; lean_object* v_snd_1337_; uint64_t v___x_1338_; uint64_t v___x_1339_; uint64_t v___x_1340_; size_t v___x_1341_; lean_object* v___x_1342_; 
v_fst_1336_ = lean_ctor_get(v_x_1335_, 0);
v_snd_1337_ = lean_ctor_get(v_x_1335_, 1);
v___x_1338_ = lean_uint64_of_nat(v_fst_1336_);
v___x_1339_ = lean_uint64_of_nat(v_snd_1337_);
v___x_1340_ = lean_uint64_mix_hash(v___x_1338_, v___x_1339_);
v___x_1341_ = lean_uint64_to_usize(v___x_1340_);
v___x_1342_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0_spec__0___redArg(v_x_1334_, v___x_1341_, v_x_1335_);
return v___x_1342_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0___redArg___boxed(lean_object* v_x_1343_, lean_object* v_x_1344_){
_start:
{
lean_object* v_res_1345_; 
v_res_1345_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0___redArg(v_x_1343_, v_x_1344_);
lean_dec_ref(v_x_1344_);
lean_dec_ref(v_x_1343_);
return v_res_1345_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm(lean_object* v_term_1346_, lean_object* v_a_1347_, lean_object* v_a_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_){
_start:
{
uint8_t v___x_1356_; lean_object* v___y_1358_; lean_object* v___y_1359_; lean_object* v___y_1424_; lean_object* v___x_1428_; 
v___x_1356_ = 0;
v___x_1428_ = l_Lean_Syntax_getPos_x3f(v_term_1346_, v___x_1356_);
if (lean_obj_tag(v___x_1428_) == 0)
{
lean_object* v___x_1429_; 
v___x_1429_ = lean_unsigned_to_nat(0u);
v___y_1424_ = v___x_1429_;
goto v___jp_1423_;
}
else
{
lean_object* v_val_1430_; 
v_val_1430_ = lean_ctor_get(v___x_1428_, 0);
lean_inc(v_val_1430_);
lean_dec_ref_known(v___x_1428_, 1);
v___y_1424_ = v_val_1430_;
goto v___jp_1423_;
}
v___jp_1357_:
{
lean_object* v_pos_1360_; lean_object* v___x_1361_; lean_object* v_cache_1362_; lean_object* v_backwardRuleSyntax_1363_; lean_object* v___x_1364_; 
v_pos_1360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_pos_1360_, 0, v___y_1358_);
lean_ctor_set(v_pos_1360_, 1, v___y_1359_);
v___x_1361_ = lean_st_ref_get(v_a_1348_);
v_cache_1362_ = lean_ctor_get(v___x_1361_, 3);
lean_inc_ref(v_cache_1362_);
lean_dec(v___x_1361_);
v_backwardRuleSyntax_1363_ = lean_ctor_get(v_cache_1362_, 1);
lean_inc_ref(v_backwardRuleSyntax_1363_);
lean_dec_ref(v_cache_1362_);
v___x_1364_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0___redArg(v_backwardRuleSyntax_1363_, v_pos_1360_);
lean_dec_ref(v_backwardRuleSyntax_1363_);
if (lean_obj_tag(v___x_1364_) == 1)
{
lean_object* v_val_1365_; lean_object* v___x_1367_; uint8_t v_isShared_1368_; uint8_t v_isSharedCheck_1372_; 
lean_dec_ref_known(v_pos_1360_, 2);
lean_dec(v_term_1346_);
v_val_1365_ = lean_ctor_get(v___x_1364_, 0);
v_isSharedCheck_1372_ = !lean_is_exclusive(v___x_1364_);
if (v_isSharedCheck_1372_ == 0)
{
v___x_1367_ = v___x_1364_;
v_isShared_1368_ = v_isSharedCheck_1372_;
goto v_resetjp_1366_;
}
else
{
lean_inc(v_val_1365_);
lean_dec(v___x_1364_);
v___x_1367_ = lean_box(0);
v_isShared_1368_ = v_isSharedCheck_1372_;
goto v_resetjp_1366_;
}
v_resetjp_1366_:
{
lean_object* v___x_1370_; 
if (v_isShared_1368_ == 0)
{
lean_ctor_set_tag(v___x_1367_, 0);
v___x_1370_ = v___x_1367_;
goto v_reusejp_1369_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v_val_1365_);
v___x_1370_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1369_;
}
v_reusejp_1369_:
{
return v___x_1370_;
}
}
}
else
{
lean_object* v___x_1373_; uint8_t v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___f_1377_; lean_object* v___x_1378_; 
lean_dec(v___x_1364_);
v___x_1373_ = lean_box(0);
v___x_1374_ = 1;
v___x_1375_ = lean_box(v___x_1374_);
v___x_1376_ = lean_box(v___x_1356_);
v___f_1377_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm___lam__0___boxed), 13, 4);
lean_closure_set(v___f_1377_, 0, v_term_1346_);
lean_closure_set(v___f_1377_, 1, v___x_1373_);
lean_closure_set(v___f_1377_, 2, v___x_1375_);
lean_closure_set(v___f_1377_, 3, v___x_1376_);
v___x_1378_ = l_Lean_Elab_Tactic_Grind_withMainContext___redArg(v___f_1377_, v_a_1347_, v_a_1348_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_);
if (lean_obj_tag(v___x_1378_) == 0)
{
lean_object* v_a_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; 
v_a_1379_ = lean_ctor_get(v___x_1378_, 0);
lean_inc(v_a_1379_);
lean_dec_ref_known(v___x_1378_, 1);
v___x_1380_ = lean_box(0);
v___x_1381_ = l_Lean_Meta_Sym_mkBackwardRuleFromExpr(v_a_1379_, v___x_1380_, v___x_1373_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_);
if (lean_obj_tag(v___x_1381_) == 0)
{
lean_object* v_a_1382_; lean_object* v___x_1384_; uint8_t v_isShared_1385_; uint8_t v_isSharedCheck_1414_; 
v_a_1382_ = lean_ctor_get(v___x_1381_, 0);
v_isSharedCheck_1414_ = !lean_is_exclusive(v___x_1381_);
if (v_isSharedCheck_1414_ == 0)
{
v___x_1384_ = v___x_1381_;
v_isShared_1385_ = v_isSharedCheck_1414_;
goto v_resetjp_1383_;
}
else
{
lean_inc(v_a_1382_);
lean_dec(v___x_1381_);
v___x_1384_ = lean_box(0);
v_isShared_1385_ = v_isSharedCheck_1414_;
goto v_resetjp_1383_;
}
v_resetjp_1383_:
{
lean_object* v___x_1386_; lean_object* v_cache_1387_; lean_object* v_symState_1388_; lean_object* v_grindState_1389_; lean_object* v_goals_1390_; lean_object* v___x_1392_; uint8_t v_isShared_1393_; uint8_t v_isSharedCheck_1413_; 
v___x_1386_ = lean_st_ref_take(v_a_1348_);
v_cache_1387_ = lean_ctor_get(v___x_1386_, 3);
v_symState_1388_ = lean_ctor_get(v___x_1386_, 0);
v_grindState_1389_ = lean_ctor_get(v___x_1386_, 1);
v_goals_1390_ = lean_ctor_get(v___x_1386_, 2);
v_isSharedCheck_1413_ = !lean_is_exclusive(v___x_1386_);
if (v_isSharedCheck_1413_ == 0)
{
v___x_1392_ = v___x_1386_;
v_isShared_1393_ = v_isSharedCheck_1413_;
goto v_resetjp_1391_;
}
else
{
lean_inc(v_cache_1387_);
lean_inc(v_goals_1390_);
lean_inc(v_grindState_1389_);
lean_inc(v_symState_1388_);
lean_dec(v___x_1386_);
v___x_1392_ = lean_box(0);
v_isShared_1393_ = v_isSharedCheck_1413_;
goto v_resetjp_1391_;
}
v_resetjp_1391_:
{
lean_object* v_backwardRuleName_1394_; lean_object* v_backwardRuleSyntax_1395_; lean_object* v_simpState_1396_; lean_object* v_dsimpState_1397_; lean_object* v___x_1399_; uint8_t v_isShared_1400_; uint8_t v_isSharedCheck_1412_; 
v_backwardRuleName_1394_ = lean_ctor_get(v_cache_1387_, 0);
v_backwardRuleSyntax_1395_ = lean_ctor_get(v_cache_1387_, 1);
v_simpState_1396_ = lean_ctor_get(v_cache_1387_, 2);
v_dsimpState_1397_ = lean_ctor_get(v_cache_1387_, 3);
v_isSharedCheck_1412_ = !lean_is_exclusive(v_cache_1387_);
if (v_isSharedCheck_1412_ == 0)
{
v___x_1399_ = v_cache_1387_;
v_isShared_1400_ = v_isSharedCheck_1412_;
goto v_resetjp_1398_;
}
else
{
lean_inc(v_dsimpState_1397_);
lean_inc(v_simpState_1396_);
lean_inc(v_backwardRuleSyntax_1395_);
lean_inc(v_backwardRuleName_1394_);
lean_dec(v_cache_1387_);
v___x_1399_ = lean_box(0);
v_isShared_1400_ = v_isSharedCheck_1412_;
goto v_resetjp_1398_;
}
v_resetjp_1398_:
{
lean_object* v___x_1401_; lean_object* v___x_1403_; 
lean_inc(v_a_1382_);
v___x_1401_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2___redArg(v_backwardRuleSyntax_1395_, v_pos_1360_, v_a_1382_);
if (v_isShared_1400_ == 0)
{
lean_ctor_set(v___x_1399_, 1, v___x_1401_);
v___x_1403_ = v___x_1399_;
goto v_reusejp_1402_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v_backwardRuleName_1394_);
lean_ctor_set(v_reuseFailAlloc_1411_, 1, v___x_1401_);
lean_ctor_set(v_reuseFailAlloc_1411_, 2, v_simpState_1396_);
lean_ctor_set(v_reuseFailAlloc_1411_, 3, v_dsimpState_1397_);
v___x_1403_ = v_reuseFailAlloc_1411_;
goto v_reusejp_1402_;
}
v_reusejp_1402_:
{
lean_object* v___x_1405_; 
if (v_isShared_1393_ == 0)
{
lean_ctor_set(v___x_1392_, 3, v___x_1403_);
v___x_1405_ = v___x_1392_;
goto v_reusejp_1404_;
}
else
{
lean_object* v_reuseFailAlloc_1410_; 
v_reuseFailAlloc_1410_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1410_, 0, v_symState_1388_);
lean_ctor_set(v_reuseFailAlloc_1410_, 1, v_grindState_1389_);
lean_ctor_set(v_reuseFailAlloc_1410_, 2, v_goals_1390_);
lean_ctor_set(v_reuseFailAlloc_1410_, 3, v___x_1403_);
v___x_1405_ = v_reuseFailAlloc_1410_;
goto v_reusejp_1404_;
}
v_reusejp_1404_:
{
lean_object* v___x_1406_; lean_object* v___x_1408_; 
v___x_1406_ = lean_st_ref_put(v_a_1348_, v___x_1405_);
if (v_isShared_1385_ == 0)
{
v___x_1408_ = v___x_1384_;
goto v_reusejp_1407_;
}
else
{
lean_object* v_reuseFailAlloc_1409_; 
v_reuseFailAlloc_1409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1409_, 0, v_a_1382_);
v___x_1408_ = v_reuseFailAlloc_1409_;
goto v_reusejp_1407_;
}
v_reusejp_1407_:
{
return v___x_1408_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_pos_1360_, 2);
return v___x_1381_;
}
}
else
{
lean_object* v_a_1415_; lean_object* v___x_1417_; uint8_t v_isShared_1418_; uint8_t v_isSharedCheck_1422_; 
lean_dec_ref_known(v_pos_1360_, 2);
v_a_1415_ = lean_ctor_get(v___x_1378_, 0);
v_isSharedCheck_1422_ = !lean_is_exclusive(v___x_1378_);
if (v_isSharedCheck_1422_ == 0)
{
v___x_1417_ = v___x_1378_;
v_isShared_1418_ = v_isSharedCheck_1422_;
goto v_resetjp_1416_;
}
else
{
lean_inc(v_a_1415_);
lean_dec(v___x_1378_);
v___x_1417_ = lean_box(0);
v_isShared_1418_ = v_isSharedCheck_1422_;
goto v_resetjp_1416_;
}
v_resetjp_1416_:
{
lean_object* v___x_1420_; 
if (v_isShared_1418_ == 0)
{
v___x_1420_ = v___x_1417_;
goto v_reusejp_1419_;
}
else
{
lean_object* v_reuseFailAlloc_1421_; 
v_reuseFailAlloc_1421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1421_, 0, v_a_1415_);
v___x_1420_ = v_reuseFailAlloc_1421_;
goto v_reusejp_1419_;
}
v_reusejp_1419_:
{
return v___x_1420_;
}
}
}
}
}
v___jp_1423_:
{
lean_object* v___x_1425_; 
v___x_1425_ = l_Lean_Syntax_getTailPos_x3f(v_term_1346_, v___x_1356_);
if (lean_obj_tag(v___x_1425_) == 0)
{
lean_object* v___x_1426_; 
v___x_1426_ = lean_unsigned_to_nat(0u);
v___y_1358_ = v___y_1424_;
v___y_1359_ = v___x_1426_;
goto v___jp_1357_;
}
else
{
lean_object* v_val_1427_; 
v_val_1427_ = lean_ctor_get(v___x_1425_, 0);
lean_inc(v_val_1427_);
lean_dec_ref_known(v___x_1425_, 1);
v___y_1358_ = v___y_1424_;
v___y_1359_ = v_val_1427_;
goto v___jp_1357_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm___boxed(lean_object* v_term_1431_, lean_object* v_a_1432_, lean_object* v_a_1433_, lean_object* v_a_1434_, lean_object* v_a_1435_, lean_object* v_a_1436_, lean_object* v_a_1437_, lean_object* v_a_1438_, lean_object* v_a_1439_, lean_object* v_a_1440_){
_start:
{
lean_object* v_res_1441_; 
v_res_1441_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm(v_term_1431_, v_a_1432_, v_a_1433_, v_a_1434_, v_a_1435_, v_a_1436_, v_a_1437_, v_a_1438_, v_a_1439_);
lean_dec(v_a_1439_);
lean_dec_ref(v_a_1438_);
lean_dec(v_a_1437_);
lean_dec_ref(v_a_1436_);
lean_dec(v_a_1435_);
lean_dec_ref(v_a_1434_);
lean_dec(v_a_1433_);
lean_dec_ref(v_a_1432_);
return v_res_1441_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0(lean_object* v_00_u03b2_1442_, lean_object* v_x_1443_, lean_object* v_x_1444_){
_start:
{
lean_object* v___x_1445_; 
v___x_1445_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0___redArg(v_x_1443_, v_x_1444_);
return v___x_1445_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0___boxed(lean_object* v_00_u03b2_1446_, lean_object* v_x_1447_, lean_object* v_x_1448_){
_start:
{
lean_object* v_res_1449_; 
v_res_1449_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0(v_00_u03b2_1446_, v_x_1447_, v_x_1448_);
lean_dec_ref(v_x_1448_);
lean_dec_ref(v_x_1447_);
return v_res_1449_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2(lean_object* v_00_u03b2_1450_, lean_object* v_x_1451_, lean_object* v_x_1452_, lean_object* v_x_1453_){
_start:
{
lean_object* v___x_1454_; 
v___x_1454_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2___redArg(v_x_1451_, v_x_1452_, v_x_1453_);
return v___x_1454_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0_spec__0(lean_object* v_00_u03b2_1455_, lean_object* v_x_1456_, size_t v_x_1457_, lean_object* v_x_1458_){
_start:
{
lean_object* v___x_1459_; 
v___x_1459_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0_spec__0___redArg(v_x_1456_, v_x_1457_, v_x_1458_);
return v___x_1459_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1460_, lean_object* v_x_1461_, lean_object* v_x_1462_, lean_object* v_x_1463_){
_start:
{
size_t v_x_4274__boxed_1464_; lean_object* v_res_1465_; 
v_x_4274__boxed_1464_ = lean_unbox_usize(v_x_1462_);
lean_dec(v_x_1462_);
v_res_1465_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0_spec__0(v_00_u03b2_1460_, v_x_1461_, v_x_4274__boxed_1464_, v_x_1463_);
lean_dec_ref(v_x_1463_);
lean_dec_ref(v_x_1461_);
return v_res_1465_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3(lean_object* v_00_u03b2_1466_, lean_object* v_x_1467_, size_t v_x_1468_, size_t v_x_1469_, lean_object* v_x_1470_, lean_object* v_x_1471_){
_start:
{
lean_object* v___x_1472_; 
v___x_1472_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3___redArg(v_x_1467_, v_x_1468_, v_x_1469_, v_x_1470_, v_x_1471_);
return v___x_1472_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3___boxed(lean_object* v_00_u03b2_1473_, lean_object* v_x_1474_, lean_object* v_x_1475_, lean_object* v_x_1476_, lean_object* v_x_1477_, lean_object* v_x_1478_){
_start:
{
size_t v_x_4285__boxed_1479_; size_t v_x_4286__boxed_1480_; lean_object* v_res_1481_; 
v_x_4285__boxed_1479_ = lean_unbox_usize(v_x_1475_);
lean_dec(v_x_1475_);
v_x_4286__boxed_1480_ = lean_unbox_usize(v_x_1476_);
lean_dec(v_x_1476_);
v_res_1481_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3(v_00_u03b2_1473_, v_x_1474_, v_x_4285__boxed_1479_, v_x_4286__boxed_1480_, v_x_1477_, v_x_1478_);
return v_res_1481_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1482_, lean_object* v_keys_1483_, lean_object* v_vals_1484_, lean_object* v_heq_1485_, lean_object* v_i_1486_, lean_object* v_k_1487_){
_start:
{
lean_object* v___x_1488_; 
v___x_1488_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0_spec__0_spec__2___redArg(v_keys_1483_, v_vals_1484_, v_i_1486_, v_k_1487_);
return v___x_1488_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1489_, lean_object* v_keys_1490_, lean_object* v_vals_1491_, lean_object* v_heq_1492_, lean_object* v_i_1493_, lean_object* v_k_1494_){
_start:
{
lean_object* v_res_1495_; 
v_res_1495_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0_spec__0_spec__2(v_00_u03b2_1489_, v_keys_1490_, v_vals_1491_, v_heq_1492_, v_i_1493_, v_k_1494_);
lean_dec_ref(v_k_1494_);
lean_dec_ref(v_vals_1491_);
lean_dec_ref(v_keys_1490_);
return v_res_1495_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_1496_, lean_object* v_n_1497_, lean_object* v_k_1498_, lean_object* v_v_1499_){
_start:
{
lean_object* v___x_1500_; 
v___x_1500_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3_spec__5___redArg(v_n_1497_, v_k_1498_, v_v_1499_);
return v___x_1500_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3_spec__6(lean_object* v_00_u03b2_1501_, size_t v_depth_1502_, lean_object* v_keys_1503_, lean_object* v_vals_1504_, lean_object* v_heq_1505_, lean_object* v_i_1506_, lean_object* v_entries_1507_){
_start:
{
lean_object* v___x_1508_; 
v___x_1508_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3_spec__6___redArg(v_depth_1502_, v_keys_1503_, v_vals_1504_, v_i_1506_, v_entries_1507_);
return v___x_1508_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3_spec__6___boxed(lean_object* v_00_u03b2_1509_, lean_object* v_depth_1510_, lean_object* v_keys_1511_, lean_object* v_vals_1512_, lean_object* v_heq_1513_, lean_object* v_i_1514_, lean_object* v_entries_1515_){
_start:
{
size_t v_depth_boxed_1516_; lean_object* v_res_1517_; 
v_depth_boxed_1516_ = lean_unbox_usize(v_depth_1510_);
lean_dec(v_depth_1510_);
v_res_1517_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3_spec__6(v_00_u03b2_1509_, v_depth_boxed_1516_, v_keys_1511_, v_vals_1512_, v_heq_1513_, v_i_1514_, v_entries_1515_);
lean_dec_ref(v_vals_1512_);
lean_dec_ref(v_keys_1511_);
return v_res_1517_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3_spec__5_spec__6(lean_object* v_00_u03b2_1518_, lean_object* v_x_1519_, lean_object* v_x_1520_, lean_object* v_x_1521_, lean_object* v_x_1522_){
_start:
{
lean_object* v___x_1523_; 
v___x_1523_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3_spec__5_spec__6___redArg(v_x_1519_, v_x_1520_, v_x_1521_, v_x_1522_);
return v___x_1523_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply_spec__0___redArg___lam__0(lean_object* v_x_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_){
_start:
{
lean_object* v___x_1534_; 
lean_inc(v___y_1528_);
lean_inc_ref(v___y_1527_);
lean_inc(v___y_1526_);
lean_inc_ref(v___y_1525_);
v___x_1534_ = lean_apply_9(v_x_1524_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_, lean_box(0));
return v___x_1534_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply_spec__0___redArg___lam__0___boxed(lean_object* v_x_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_){
_start:
{
lean_object* v_res_1545_; 
v_res_1545_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply_spec__0___redArg___lam__0(v_x_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_);
lean_dec(v___y_1539_);
lean_dec_ref(v___y_1538_);
lean_dec(v___y_1537_);
lean_dec_ref(v___y_1536_);
return v_res_1545_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply_spec__0___redArg(lean_object* v_mvarId_1546_, lean_object* v_x_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_){
_start:
{
lean_object* v___f_1557_; lean_object* v___x_1558_; 
lean_inc(v___y_1551_);
lean_inc_ref(v___y_1550_);
lean_inc(v___y_1549_);
lean_inc_ref(v___y_1548_);
v___f_1557_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply_spec__0___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_1557_, 0, v_x_1547_);
lean_closure_set(v___f_1557_, 1, v___y_1548_);
lean_closure_set(v___f_1557_, 2, v___y_1549_);
lean_closure_set(v___f_1557_, 3, v___y_1550_);
lean_closure_set(v___f_1557_, 4, v___y_1551_);
v___x_1558_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1546_, v___f_1557_, v___y_1552_, v___y_1553_, v___y_1554_, v___y_1555_);
if (lean_obj_tag(v___x_1558_) == 0)
{
return v___x_1558_;
}
else
{
lean_object* v_a_1559_; lean_object* v___x_1561_; uint8_t v_isShared_1562_; uint8_t v_isSharedCheck_1566_; 
v_a_1559_ = lean_ctor_get(v___x_1558_, 0);
v_isSharedCheck_1566_ = !lean_is_exclusive(v___x_1558_);
if (v_isSharedCheck_1566_ == 0)
{
v___x_1561_ = v___x_1558_;
v_isShared_1562_ = v_isSharedCheck_1566_;
goto v_resetjp_1560_;
}
else
{
lean_inc(v_a_1559_);
lean_dec(v___x_1558_);
v___x_1561_ = lean_box(0);
v_isShared_1562_ = v_isSharedCheck_1566_;
goto v_resetjp_1560_;
}
v_resetjp_1560_:
{
lean_object* v___x_1564_; 
if (v_isShared_1562_ == 0)
{
v___x_1564_ = v___x_1561_;
goto v_reusejp_1563_;
}
else
{
lean_object* v_reuseFailAlloc_1565_; 
v_reuseFailAlloc_1565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1565_, 0, v_a_1559_);
v___x_1564_ = v_reuseFailAlloc_1565_;
goto v_reusejp_1563_;
}
v_reusejp_1563_:
{
return v___x_1564_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply_spec__0___redArg___boxed(lean_object* v_mvarId_1567_, lean_object* v_x_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_){
_start:
{
lean_object* v_res_1578_; 
v_res_1578_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply_spec__0___redArg(v_mvarId_1567_, v_x_1568_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_);
lean_dec(v___y_1576_);
lean_dec_ref(v___y_1575_);
lean_dec(v___y_1574_);
lean_dec_ref(v___y_1573_);
lean_dec(v___y_1572_);
lean_dec_ref(v___y_1571_);
lean_dec(v___y_1570_);
lean_dec_ref(v___y_1569_);
return v_res_1578_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply_spec__0(lean_object* v_00_u03b1_1579_, lean_object* v_mvarId_1580_, lean_object* v_x_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_){
_start:
{
lean_object* v___x_1591_; 
v___x_1591_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply_spec__0___redArg(v_mvarId_1580_, v_x_1581_, v___y_1582_, v___y_1583_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_);
return v___x_1591_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply_spec__0___boxed(lean_object* v_00_u03b1_1592_, lean_object* v_mvarId_1593_, lean_object* v_x_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_){
_start:
{
lean_object* v_res_1604_; 
v_res_1604_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply_spec__0(v_00_u03b1_1592_, v_mvarId_1593_, v_x_1594_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_);
lean_dec(v___y_1602_);
lean_dec_ref(v___y_1601_);
lean_dec(v___y_1600_);
lean_dec_ref(v___y_1599_);
lean_dec(v___y_1598_);
lean_dec_ref(v___y_1597_);
lean_dec(v___y_1596_);
lean_dec_ref(v___y_1595_);
return v_res_1604_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1606_; lean_object* v___x_1607_; 
v___x_1606_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___lam__0___closed__0));
v___x_1607_ = l_Lean_stringToMessageData(v___x_1606_);
return v___x_1607_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___lam__0(lean_object* v_a_1608_, lean_object* v_rule_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_){
_start:
{
lean_object* v___x_1619_; lean_object* v___x_1620_; 
v___x_1619_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Goal_apply___boxed), 9, 2);
lean_closure_set(v___x_1619_, 0, v_a_1608_);
lean_closure_set(v___x_1619_, 1, v_rule_1609_);
v___x_1620_ = l_Lean_Elab_Tactic_Grind_liftSymM___redArg(v___x_1619_, v___y_1610_, v___y_1611_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_);
if (lean_obj_tag(v___x_1620_) == 0)
{
lean_object* v_a_1621_; 
v_a_1621_ = lean_ctor_get(v___x_1620_, 0);
lean_inc(v_a_1621_);
lean_dec_ref_known(v___x_1620_, 1);
if (lean_obj_tag(v_a_1621_) == 0)
{
lean_object* v___x_1622_; lean_object* v___x_1623_; 
v___x_1622_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___lam__0___closed__1, &l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___lam__0___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___lam__0___closed__1);
v___x_1623_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__2___redArg(v___x_1622_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_);
return v___x_1623_;
}
else
{
lean_object* v_subgoals_1624_; lean_object* v___x_1625_; 
v_subgoals_1624_ = lean_ctor_get(v_a_1621_, 0);
lean_inc(v_subgoals_1624_);
lean_dec_ref_known(v_a_1621_, 1);
v___x_1625_ = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(v_subgoals_1624_, v___y_1611_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_);
return v___x_1625_;
}
}
else
{
lean_object* v_a_1626_; lean_object* v___x_1628_; uint8_t v_isShared_1629_; uint8_t v_isSharedCheck_1633_; 
v_a_1626_ = lean_ctor_get(v___x_1620_, 0);
v_isSharedCheck_1633_ = !lean_is_exclusive(v___x_1620_);
if (v_isSharedCheck_1633_ == 0)
{
v___x_1628_ = v___x_1620_;
v_isShared_1629_ = v_isSharedCheck_1633_;
goto v_resetjp_1627_;
}
else
{
lean_inc(v_a_1626_);
lean_dec(v___x_1620_);
v___x_1628_ = lean_box(0);
v_isShared_1629_ = v_isSharedCheck_1633_;
goto v_resetjp_1627_;
}
v_resetjp_1627_:
{
lean_object* v___x_1631_; 
if (v_isShared_1629_ == 0)
{
v___x_1631_ = v___x_1628_;
goto v_reusejp_1630_;
}
else
{
lean_object* v_reuseFailAlloc_1632_; 
v_reuseFailAlloc_1632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1632_, 0, v_a_1626_);
v___x_1631_ = v_reuseFailAlloc_1632_;
goto v_reusejp_1630_;
}
v_reusejp_1630_:
{
return v___x_1631_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___lam__0___boxed(lean_object* v_a_1634_, lean_object* v_rule_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_){
_start:
{
lean_object* v_res_1645_; 
v_res_1645_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___lam__0(v_a_1634_, v_rule_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_);
lean_dec(v___y_1643_);
lean_dec_ref(v___y_1642_);
lean_dec(v___y_1641_);
lean_dec_ref(v___y_1640_);
lean_dec(v___y_1639_);
lean_dec_ref(v___y_1638_);
lean_dec(v___y_1637_);
lean_dec_ref(v___y_1636_);
return v_res_1645_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___lam__1(uint8_t v___x_1646_, lean_object* v___x_1647_, lean_object* v___f_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_){
_start:
{
if (v___x_1646_ == 0)
{
lean_object* v___x_1658_; 
v___x_1658_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm(v___x_1647_, v___y_1649_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_);
if (lean_obj_tag(v___x_1658_) == 0)
{
lean_object* v_a_1659_; lean_object* v___x_1660_; 
v_a_1659_ = lean_ctor_get(v___x_1658_, 0);
lean_inc(v_a_1659_);
lean_dec_ref_known(v___x_1658_, 1);
lean_inc(v___y_1656_);
lean_inc_ref(v___y_1655_);
lean_inc(v___y_1654_);
lean_inc_ref(v___y_1653_);
lean_inc(v___y_1652_);
lean_inc_ref(v___y_1651_);
lean_inc(v___y_1650_);
lean_inc_ref(v___y_1649_);
v___x_1660_ = lean_apply_10(v___f_1648_, v_a_1659_, v___y_1649_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_, lean_box(0));
return v___x_1660_;
}
else
{
lean_object* v_a_1661_; lean_object* v___x_1663_; uint8_t v_isShared_1664_; uint8_t v_isSharedCheck_1668_; 
lean_dec_ref(v___f_1648_);
v_a_1661_ = lean_ctor_get(v___x_1658_, 0);
v_isSharedCheck_1668_ = !lean_is_exclusive(v___x_1658_);
if (v_isSharedCheck_1668_ == 0)
{
v___x_1663_ = v___x_1658_;
v_isShared_1664_ = v_isSharedCheck_1668_;
goto v_resetjp_1662_;
}
else
{
lean_inc(v_a_1661_);
lean_dec(v___x_1658_);
v___x_1663_ = lean_box(0);
v_isShared_1664_ = v_isSharedCheck_1668_;
goto v_resetjp_1662_;
}
v_resetjp_1662_:
{
lean_object* v___x_1666_; 
if (v_isShared_1664_ == 0)
{
v___x_1666_ = v___x_1663_;
goto v_reusejp_1665_;
}
else
{
lean_object* v_reuseFailAlloc_1667_; 
v_reuseFailAlloc_1667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1667_, 0, v_a_1661_);
v___x_1666_ = v_reuseFailAlloc_1667_;
goto v_reusejp_1665_;
}
v_reusejp_1665_:
{
return v___x_1666_;
}
}
}
}
else
{
lean_object* v___x_1669_; 
v___x_1669_ = l_Lean_Elab_Tactic_Grind_saveState___redArg(v___y_1650_, v___y_1652_, v___y_1654_, v___y_1656_);
if (lean_obj_tag(v___x_1669_) == 0)
{
lean_object* v_a_1670_; lean_object* v___x_1672_; uint8_t v_isShared_1673_; uint8_t v_isSharedCheck_1706_; 
v_a_1670_ = lean_ctor_get(v___x_1669_, 0);
v_isSharedCheck_1706_ = !lean_is_exclusive(v___x_1669_);
if (v_isSharedCheck_1706_ == 0)
{
v___x_1672_ = v___x_1669_;
v_isShared_1673_ = v_isSharedCheck_1706_;
goto v_resetjp_1671_;
}
else
{
lean_inc(v_a_1670_);
lean_dec(v___x_1669_);
v___x_1672_ = lean_box(0);
v_isShared_1673_ = v_isSharedCheck_1706_;
goto v_resetjp_1671_;
}
v_resetjp_1671_:
{
lean_object* v_a_1675_; lean_object* v___x_1696_; 
lean_inc(v___x_1647_);
v___x_1696_ = l_Lean_realizeGlobalConstNoOverload(v___x_1647_, v___y_1655_, v___y_1656_);
if (lean_obj_tag(v___x_1696_) == 0)
{
lean_object* v_a_1697_; lean_object* v___x_1698_; 
v_a_1697_ = lean_ctor_get(v___x_1696_, 0);
lean_inc_n(v_a_1697_, 2);
lean_dec_ref_known(v___x_1696_, 1);
v___x_1698_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule___redArg(v_a_1697_, v___y_1650_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_);
if (lean_obj_tag(v___x_1698_) == 0)
{
lean_object* v_a_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; 
v_a_1699_ = lean_ctor_get(v___x_1698_, 0);
lean_inc(v_a_1699_);
lean_dec_ref_known(v___x_1698_, 1);
v___x_1700_ = lean_box(1);
v___x_1701_ = l_Lean_Linter_checkDeprecatedAt(v___x_1647_, v_a_1697_, v___x_1700_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_);
if (lean_obj_tag(v___x_1701_) == 0)
{
lean_object* v___x_1702_; 
lean_dec_ref_known(v___x_1701_, 1);
lean_del_object(v___x_1672_);
lean_dec(v_a_1670_);
lean_dec(v___x_1647_);
lean_inc(v___y_1656_);
lean_inc_ref(v___y_1655_);
lean_inc(v___y_1654_);
lean_inc_ref(v___y_1653_);
lean_inc(v___y_1652_);
lean_inc_ref(v___y_1651_);
lean_inc(v___y_1650_);
lean_inc_ref(v___y_1649_);
v___x_1702_ = lean_apply_10(v___f_1648_, v_a_1699_, v___y_1649_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_, lean_box(0));
return v___x_1702_;
}
else
{
lean_object* v_a_1703_; 
lean_dec(v_a_1699_);
v_a_1703_ = lean_ctor_get(v___x_1701_, 0);
lean_inc(v_a_1703_);
lean_dec_ref_known(v___x_1701_, 1);
v_a_1675_ = v_a_1703_;
goto v___jp_1674_;
}
}
else
{
lean_object* v_a_1704_; 
lean_dec(v_a_1697_);
v_a_1704_ = lean_ctor_get(v___x_1698_, 0);
lean_inc(v_a_1704_);
lean_dec_ref_known(v___x_1698_, 1);
v_a_1675_ = v_a_1704_;
goto v___jp_1674_;
}
}
else
{
lean_object* v_a_1705_; 
v_a_1705_ = lean_ctor_get(v___x_1696_, 0);
lean_inc(v_a_1705_);
lean_dec_ref_known(v___x_1696_, 1);
v_a_1675_ = v_a_1705_;
goto v___jp_1674_;
}
v___jp_1674_:
{
uint8_t v___x_1676_; 
v___x_1676_ = l_Lean_Exception_isInterrupt(v_a_1675_);
if (v___x_1676_ == 0)
{
uint8_t v___x_1677_; 
lean_inc_ref(v_a_1675_);
v___x_1677_ = l_Lean_Exception_isRuntime(v_a_1675_);
if (v___x_1677_ == 0)
{
lean_object* v___x_1678_; 
lean_dec_ref(v_a_1675_);
lean_del_object(v___x_1672_);
v___x_1678_ = l_Lean_Elab_Tactic_Grind_SavedState_restore___redArg(v_a_1670_, v___x_1677_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_);
if (lean_obj_tag(v___x_1678_) == 0)
{
lean_object* v___x_1679_; 
lean_dec_ref_known(v___x_1678_, 1);
v___x_1679_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm(v___x_1647_, v___y_1649_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_);
if (lean_obj_tag(v___x_1679_) == 0)
{
lean_object* v_a_1680_; lean_object* v___x_1681_; 
v_a_1680_ = lean_ctor_get(v___x_1679_, 0);
lean_inc(v_a_1680_);
lean_dec_ref_known(v___x_1679_, 1);
lean_inc(v___y_1656_);
lean_inc_ref(v___y_1655_);
lean_inc(v___y_1654_);
lean_inc_ref(v___y_1653_);
lean_inc(v___y_1652_);
lean_inc_ref(v___y_1651_);
lean_inc(v___y_1650_);
lean_inc_ref(v___y_1649_);
v___x_1681_ = lean_apply_10(v___f_1648_, v_a_1680_, v___y_1649_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_, lean_box(0));
return v___x_1681_;
}
else
{
lean_object* v_a_1682_; lean_object* v___x_1684_; uint8_t v_isShared_1685_; uint8_t v_isSharedCheck_1689_; 
lean_dec_ref(v___f_1648_);
v_a_1682_ = lean_ctor_get(v___x_1679_, 0);
v_isSharedCheck_1689_ = !lean_is_exclusive(v___x_1679_);
if (v_isSharedCheck_1689_ == 0)
{
v___x_1684_ = v___x_1679_;
v_isShared_1685_ = v_isSharedCheck_1689_;
goto v_resetjp_1683_;
}
else
{
lean_inc(v_a_1682_);
lean_dec(v___x_1679_);
v___x_1684_ = lean_box(0);
v_isShared_1685_ = v_isSharedCheck_1689_;
goto v_resetjp_1683_;
}
v_resetjp_1683_:
{
lean_object* v___x_1687_; 
if (v_isShared_1685_ == 0)
{
v___x_1687_ = v___x_1684_;
goto v_reusejp_1686_;
}
else
{
lean_object* v_reuseFailAlloc_1688_; 
v_reuseFailAlloc_1688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1688_, 0, v_a_1682_);
v___x_1687_ = v_reuseFailAlloc_1688_;
goto v_reusejp_1686_;
}
v_reusejp_1686_:
{
return v___x_1687_;
}
}
}
}
else
{
lean_dec_ref(v___f_1648_);
lean_dec(v___x_1647_);
return v___x_1678_;
}
}
else
{
lean_object* v___x_1691_; 
lean_dec(v_a_1670_);
lean_dec_ref(v___f_1648_);
lean_dec(v___x_1647_);
if (v_isShared_1673_ == 0)
{
lean_ctor_set_tag(v___x_1672_, 1);
lean_ctor_set(v___x_1672_, 0, v_a_1675_);
v___x_1691_ = v___x_1672_;
goto v_reusejp_1690_;
}
else
{
lean_object* v_reuseFailAlloc_1692_; 
v_reuseFailAlloc_1692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1692_, 0, v_a_1675_);
v___x_1691_ = v_reuseFailAlloc_1692_;
goto v_reusejp_1690_;
}
v_reusejp_1690_:
{
return v___x_1691_;
}
}
}
else
{
lean_object* v___x_1694_; 
lean_dec(v_a_1670_);
lean_dec_ref(v___f_1648_);
lean_dec(v___x_1647_);
if (v_isShared_1673_ == 0)
{
lean_ctor_set_tag(v___x_1672_, 1);
lean_ctor_set(v___x_1672_, 0, v_a_1675_);
v___x_1694_ = v___x_1672_;
goto v_reusejp_1693_;
}
else
{
lean_object* v_reuseFailAlloc_1695_; 
v_reuseFailAlloc_1695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1695_, 0, v_a_1675_);
v___x_1694_ = v_reuseFailAlloc_1695_;
goto v_reusejp_1693_;
}
v_reusejp_1693_:
{
return v___x_1694_;
}
}
}
}
}
else
{
lean_object* v_a_1707_; lean_object* v___x_1709_; uint8_t v_isShared_1710_; uint8_t v_isSharedCheck_1714_; 
lean_dec_ref(v___f_1648_);
lean_dec(v___x_1647_);
v_a_1707_ = lean_ctor_get(v___x_1669_, 0);
v_isSharedCheck_1714_ = !lean_is_exclusive(v___x_1669_);
if (v_isSharedCheck_1714_ == 0)
{
v___x_1709_ = v___x_1669_;
v_isShared_1710_ = v_isSharedCheck_1714_;
goto v_resetjp_1708_;
}
else
{
lean_inc(v_a_1707_);
lean_dec(v___x_1669_);
v___x_1709_ = lean_box(0);
v_isShared_1710_ = v_isSharedCheck_1714_;
goto v_resetjp_1708_;
}
v_resetjp_1708_:
{
lean_object* v___x_1712_; 
if (v_isShared_1710_ == 0)
{
v___x_1712_ = v___x_1709_;
goto v_reusejp_1711_;
}
else
{
lean_object* v_reuseFailAlloc_1713_; 
v_reuseFailAlloc_1713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1713_, 0, v_a_1707_);
v___x_1712_ = v_reuseFailAlloc_1713_;
goto v_reusejp_1711_;
}
v_reusejp_1711_:
{
return v___x_1712_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___lam__1___boxed(lean_object* v___x_1715_, lean_object* v___x_1716_, lean_object* v___f_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_){
_start:
{
uint8_t v___x_3495__boxed_1727_; lean_object* v_res_1728_; 
v___x_3495__boxed_1727_ = lean_unbox(v___x_1715_);
v_res_1728_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___lam__1(v___x_3495__boxed_1727_, v___x_1716_, v___f_1717_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_);
lean_dec(v___y_1725_);
lean_dec_ref(v___y_1724_);
lean_dec(v___y_1723_);
lean_dec_ref(v___y_1722_);
lean_dec(v___y_1721_);
lean_dec_ref(v___y_1720_);
lean_dec(v___y_1719_);
lean_dec_ref(v___y_1718_);
return v_res_1728_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply(lean_object* v_stx_1736_, lean_object* v_a_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_, lean_object* v_a_1741_, lean_object* v_a_1742_, lean_object* v_a_1743_, lean_object* v_a_1744_){
_start:
{
lean_object* v___x_1746_; 
v___x_1746_ = l_Lean_Elab_Tactic_Grind_ensureSym___redArg(v_a_1737_, v_a_1741_, v_a_1742_, v_a_1743_, v_a_1744_);
if (lean_obj_tag(v___x_1746_) == 0)
{
lean_object* v___x_1747_; uint8_t v___x_1748_; 
lean_dec_ref_known(v___x_1746_, 1);
v___x_1747_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___closed__1));
lean_inc(v_stx_1736_);
v___x_1748_ = l_Lean_Syntax_isOfKind(v_stx_1736_, v___x_1747_);
if (v___x_1748_ == 0)
{
lean_object* v___x_1749_; 
lean_dec(v_stx_1736_);
v___x_1749_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro_spec__0___redArg();
return v___x_1749_;
}
else
{
lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; 
v___x_1750_ = lean_unsigned_to_nat(1u);
v___x_1751_ = l_Lean_Syntax_getArg(v_stx_1736_, v___x_1750_);
lean_dec(v_stx_1736_);
v___x_1752_ = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(v_a_1738_, v_a_1741_, v_a_1742_, v_a_1743_, v_a_1744_);
if (lean_obj_tag(v___x_1752_) == 0)
{
lean_object* v_a_1753_; lean_object* v_mvarId_1754_; lean_object* v___f_1755_; lean_object* v___x_1756_; uint8_t v___x_1757_; lean_object* v___x_1758_; lean_object* v___y_1759_; lean_object* v___x_1760_; 
v_a_1753_ = lean_ctor_get(v___x_1752_, 0);
lean_inc(v_a_1753_);
lean_dec_ref_known(v___x_1752_, 1);
v_mvarId_1754_ = lean_ctor_get(v_a_1753_, 1);
lean_inc(v_mvarId_1754_);
v___f_1755_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___lam__0___boxed), 11, 1);
lean_closure_set(v___f_1755_, 0, v_a_1753_);
v___x_1756_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__1___redArg___closed__6));
lean_inc(v___x_1751_);
v___x_1757_ = l_Lean_Syntax_isOfKind(v___x_1751_, v___x_1756_);
v___x_1758_ = lean_box(v___x_1757_);
v___y_1759_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___lam__1___boxed), 12, 3);
lean_closure_set(v___y_1759_, 0, v___x_1758_);
lean_closure_set(v___y_1759_, 1, v___x_1751_);
lean_closure_set(v___y_1759_, 2, v___f_1755_);
v___x_1760_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply_spec__0___redArg(v_mvarId_1754_, v___y_1759_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_, v_a_1741_, v_a_1742_, v_a_1743_, v_a_1744_);
return v___x_1760_;
}
else
{
lean_object* v_a_1761_; lean_object* v___x_1763_; uint8_t v_isShared_1764_; uint8_t v_isSharedCheck_1768_; 
lean_dec(v___x_1751_);
v_a_1761_ = lean_ctor_get(v___x_1752_, 0);
v_isSharedCheck_1768_ = !lean_is_exclusive(v___x_1752_);
if (v_isSharedCheck_1768_ == 0)
{
v___x_1763_ = v___x_1752_;
v_isShared_1764_ = v_isSharedCheck_1768_;
goto v_resetjp_1762_;
}
else
{
lean_inc(v_a_1761_);
lean_dec(v___x_1752_);
v___x_1763_ = lean_box(0);
v_isShared_1764_ = v_isSharedCheck_1768_;
goto v_resetjp_1762_;
}
v_resetjp_1762_:
{
lean_object* v___x_1766_; 
if (v_isShared_1764_ == 0)
{
v___x_1766_ = v___x_1763_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v_a_1761_);
v___x_1766_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
return v___x_1766_;
}
}
}
}
}
else
{
lean_dec(v_stx_1736_);
return v___x_1746_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___boxed(lean_object* v_stx_1769_, lean_object* v_a_1770_, lean_object* v_a_1771_, lean_object* v_a_1772_, lean_object* v_a_1773_, lean_object* v_a_1774_, lean_object* v_a_1775_, lean_object* v_a_1776_, lean_object* v_a_1777_, lean_object* v_a_1778_){
_start:
{
lean_object* v_res_1779_; 
v_res_1779_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply(v_stx_1769_, v_a_1770_, v_a_1771_, v_a_1772_, v_a_1773_, v_a_1774_, v_a_1775_, v_a_1776_, v_a_1777_);
lean_dec(v_a_1777_);
lean_dec_ref(v_a_1776_);
lean_dec(v_a_1775_);
lean_dec_ref(v_a_1774_);
lean_dec(v_a_1773_);
lean_dec_ref(v_a_1772_);
lean_dec(v_a_1771_);
lean_dec_ref(v_a_1770_);
return v_res_1779_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply__1(){
_start:
{
lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; 
v___x_1785_ = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
v___x_1786_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___closed__1));
v___x_1787_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply__1___closed__1));
v___x_1788_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___boxed), 10, 0);
v___x_1789_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1785_, v___x_1786_, v___x_1787_, v___x_1788_);
return v___x_1789_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply__1___boxed(lean_object* v_a_1790_){
_start:
{
lean_object* v_res_1791_; 
v_res_1791_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply__1();
return v_res_1791_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize___redArg(lean_object* v_stx_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_, lean_object* v_a_1795_, lean_object* v_a_1796_, lean_object* v_a_1797_, lean_object* v_a_1798_){
_start:
{
lean_object* v___x_1800_; 
v___x_1800_ = l_Lean_Elab_Tactic_Grind_ensureSym___redArg(v_a_1793_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_);
if (lean_obj_tag(v___x_1800_) == 0)
{
lean_object* v___x_1801_; 
lean_dec_ref_known(v___x_1800_, 1);
v___x_1801_ = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(v_a_1794_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_);
if (lean_obj_tag(v___x_1801_) == 0)
{
lean_object* v_a_1802_; lean_object* v___y_1804_; lean_object* v___x_1819_; lean_object* v___x_1820_; uint8_t v___x_1821_; 
v_a_1802_ = lean_ctor_get(v___x_1801_, 0);
lean_inc(v_a_1802_);
lean_dec_ref_known(v___x_1801_, 1);
v___x_1819_ = lean_unsigned_to_nat(1u);
v___x_1820_ = l_Lean_Syntax_getArg(v_stx_1792_, v___x_1819_);
v___x_1821_ = l_Lean_Syntax_isNone(v___x_1820_);
if (v___x_1821_ == 0)
{
lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; 
v___x_1822_ = lean_unsigned_to_nat(0u);
v___x_1823_ = l_Lean_Syntax_getArg(v___x_1820_, v___x_1822_);
lean_dec(v___x_1820_);
v___x_1824_ = l_Lean_Syntax_toNat(v___x_1823_);
lean_dec(v___x_1823_);
v___y_1804_ = v___x_1824_;
goto v___jp_1803_;
}
else
{
lean_dec(v___x_1820_);
v___y_1804_ = v___x_1819_;
goto v___jp_1803_;
}
v___jp_1803_:
{
lean_object* v___x_1805_; lean_object* v___x_1806_; 
v___x_1805_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Goal_internalize___boxed), 12, 2);
lean_closure_set(v___x_1805_, 0, v_a_1802_);
lean_closure_set(v___x_1805_, 1, v___y_1804_);
v___x_1806_ = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(v___x_1805_, v_a_1793_, v_a_1794_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_);
if (lean_obj_tag(v___x_1806_) == 0)
{
lean_object* v_a_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; 
v_a_1807_ = lean_ctor_get(v___x_1806_, 0);
lean_inc(v_a_1807_);
lean_dec_ref_known(v___x_1806_, 1);
v___x_1808_ = lean_box(0);
v___x_1809_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1809_, 0, v_a_1807_);
lean_ctor_set(v___x_1809_, 1, v___x_1808_);
v___x_1810_ = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(v___x_1809_, v_a_1794_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_);
return v___x_1810_;
}
else
{
lean_object* v_a_1811_; lean_object* v___x_1813_; uint8_t v_isShared_1814_; uint8_t v_isSharedCheck_1818_; 
v_a_1811_ = lean_ctor_get(v___x_1806_, 0);
v_isSharedCheck_1818_ = !lean_is_exclusive(v___x_1806_);
if (v_isSharedCheck_1818_ == 0)
{
v___x_1813_ = v___x_1806_;
v_isShared_1814_ = v_isSharedCheck_1818_;
goto v_resetjp_1812_;
}
else
{
lean_inc(v_a_1811_);
lean_dec(v___x_1806_);
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
else
{
lean_object* v_a_1825_; lean_object* v___x_1827_; uint8_t v_isShared_1828_; uint8_t v_isSharedCheck_1832_; 
v_a_1825_ = lean_ctor_get(v___x_1801_, 0);
v_isSharedCheck_1832_ = !lean_is_exclusive(v___x_1801_);
if (v_isSharedCheck_1832_ == 0)
{
v___x_1827_ = v___x_1801_;
v_isShared_1828_ = v_isSharedCheck_1832_;
goto v_resetjp_1826_;
}
else
{
lean_inc(v_a_1825_);
lean_dec(v___x_1801_);
v___x_1827_ = lean_box(0);
v_isShared_1828_ = v_isSharedCheck_1832_;
goto v_resetjp_1826_;
}
v_resetjp_1826_:
{
lean_object* v___x_1830_; 
if (v_isShared_1828_ == 0)
{
v___x_1830_ = v___x_1827_;
goto v_reusejp_1829_;
}
else
{
lean_object* v_reuseFailAlloc_1831_; 
v_reuseFailAlloc_1831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1831_, 0, v_a_1825_);
v___x_1830_ = v_reuseFailAlloc_1831_;
goto v_reusejp_1829_;
}
v_reusejp_1829_:
{
return v___x_1830_;
}
}
}
}
else
{
return v___x_1800_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize___redArg___boxed(lean_object* v_stx_1833_, lean_object* v_a_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_, lean_object* v_a_1838_, lean_object* v_a_1839_, lean_object* v_a_1840_){
_start:
{
lean_object* v_res_1841_; 
v_res_1841_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize___redArg(v_stx_1833_, v_a_1834_, v_a_1835_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_);
lean_dec(v_a_1839_);
lean_dec_ref(v_a_1838_);
lean_dec(v_a_1837_);
lean_dec_ref(v_a_1836_);
lean_dec(v_a_1835_);
lean_dec_ref(v_a_1834_);
lean_dec(v_stx_1833_);
return v_res_1841_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize(lean_object* v_stx_1842_, lean_object* v_a_1843_, lean_object* v_a_1844_, lean_object* v_a_1845_, lean_object* v_a_1846_, lean_object* v_a_1847_, lean_object* v_a_1848_, lean_object* v_a_1849_, lean_object* v_a_1850_){
_start:
{
lean_object* v___x_1852_; 
v___x_1852_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize___redArg(v_stx_1842_, v_a_1843_, v_a_1844_, v_a_1847_, v_a_1848_, v_a_1849_, v_a_1850_);
return v___x_1852_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize___boxed(lean_object* v_stx_1853_, lean_object* v_a_1854_, lean_object* v_a_1855_, lean_object* v_a_1856_, lean_object* v_a_1857_, lean_object* v_a_1858_, lean_object* v_a_1859_, lean_object* v_a_1860_, lean_object* v_a_1861_, lean_object* v_a_1862_){
_start:
{
lean_object* v_res_1863_; 
v_res_1863_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize(v_stx_1853_, v_a_1854_, v_a_1855_, v_a_1856_, v_a_1857_, v_a_1858_, v_a_1859_, v_a_1860_, v_a_1861_);
lean_dec(v_a_1861_);
lean_dec_ref(v_a_1860_);
lean_dec(v_a_1859_);
lean_dec_ref(v_a_1858_);
lean_dec(v_a_1857_);
lean_dec_ref(v_a_1856_);
lean_dec(v_a_1855_);
lean_dec_ref(v_a_1854_);
lean_dec(v_stx_1853_);
return v_res_1863_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize__1(){
_start:
{
lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; 
v___x_1876_ = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
v___x_1877_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize__1___closed__1));
v___x_1878_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize__1___closed__3));
v___x_1879_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize___boxed), 10, 0);
v___x_1880_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1876_, v___x_1877_, v___x_1878_, v___x_1879_);
return v___x_1880_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize__1___boxed(lean_object* v_a_1881_){
_start:
{
lean_object* v_res_1882_; 
v_res_1882_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize__1();
return v_res_1882_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll___redArg(lean_object* v_a_1883_, lean_object* v_a_1884_, lean_object* v_a_1885_, lean_object* v_a_1886_, lean_object* v_a_1887_, lean_object* v_a_1888_){
_start:
{
lean_object* v___x_1890_; 
v___x_1890_ = l_Lean_Elab_Tactic_Grind_ensureSym___redArg(v_a_1883_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_);
if (lean_obj_tag(v___x_1890_) == 0)
{
lean_object* v___x_1891_; 
lean_dec_ref_known(v___x_1890_, 1);
v___x_1891_ = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_);
if (lean_obj_tag(v___x_1891_) == 0)
{
lean_object* v_a_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; 
v_a_1892_ = lean_ctor_get(v___x_1891_, 0);
lean_inc(v_a_1892_);
lean_dec_ref_known(v___x_1891_, 1);
v___x_1893_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Goal_internalizeAll___boxed), 11, 1);
lean_closure_set(v___x_1893_, 0, v_a_1892_);
v___x_1894_ = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(v___x_1893_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_);
if (lean_obj_tag(v___x_1894_) == 0)
{
lean_object* v_a_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; 
v_a_1895_ = lean_ctor_get(v___x_1894_, 0);
lean_inc(v_a_1895_);
lean_dec_ref_known(v___x_1894_, 1);
v___x_1896_ = lean_box(0);
v___x_1897_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1897_, 0, v_a_1895_);
lean_ctor_set(v___x_1897_, 1, v___x_1896_);
v___x_1898_ = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(v___x_1897_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_);
return v___x_1898_;
}
else
{
lean_object* v_a_1899_; lean_object* v___x_1901_; uint8_t v_isShared_1902_; uint8_t v_isSharedCheck_1906_; 
v_a_1899_ = lean_ctor_get(v___x_1894_, 0);
v_isSharedCheck_1906_ = !lean_is_exclusive(v___x_1894_);
if (v_isSharedCheck_1906_ == 0)
{
v___x_1901_ = v___x_1894_;
v_isShared_1902_ = v_isSharedCheck_1906_;
goto v_resetjp_1900_;
}
else
{
lean_inc(v_a_1899_);
lean_dec(v___x_1894_);
v___x_1901_ = lean_box(0);
v_isShared_1902_ = v_isSharedCheck_1906_;
goto v_resetjp_1900_;
}
v_resetjp_1900_:
{
lean_object* v___x_1904_; 
if (v_isShared_1902_ == 0)
{
v___x_1904_ = v___x_1901_;
goto v_reusejp_1903_;
}
else
{
lean_object* v_reuseFailAlloc_1905_; 
v_reuseFailAlloc_1905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1905_, 0, v_a_1899_);
v___x_1904_ = v_reuseFailAlloc_1905_;
goto v_reusejp_1903_;
}
v_reusejp_1903_:
{
return v___x_1904_;
}
}
}
}
else
{
lean_object* v_a_1907_; lean_object* v___x_1909_; uint8_t v_isShared_1910_; uint8_t v_isSharedCheck_1914_; 
v_a_1907_ = lean_ctor_get(v___x_1891_, 0);
v_isSharedCheck_1914_ = !lean_is_exclusive(v___x_1891_);
if (v_isSharedCheck_1914_ == 0)
{
v___x_1909_ = v___x_1891_;
v_isShared_1910_ = v_isSharedCheck_1914_;
goto v_resetjp_1908_;
}
else
{
lean_inc(v_a_1907_);
lean_dec(v___x_1891_);
v___x_1909_ = lean_box(0);
v_isShared_1910_ = v_isSharedCheck_1914_;
goto v_resetjp_1908_;
}
v_resetjp_1908_:
{
lean_object* v___x_1912_; 
if (v_isShared_1910_ == 0)
{
v___x_1912_ = v___x_1909_;
goto v_reusejp_1911_;
}
else
{
lean_object* v_reuseFailAlloc_1913_; 
v_reuseFailAlloc_1913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1913_, 0, v_a_1907_);
v___x_1912_ = v_reuseFailAlloc_1913_;
goto v_reusejp_1911_;
}
v_reusejp_1911_:
{
return v___x_1912_;
}
}
}
}
else
{
return v___x_1890_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll___redArg___boxed(lean_object* v_a_1915_, lean_object* v_a_1916_, lean_object* v_a_1917_, lean_object* v_a_1918_, lean_object* v_a_1919_, lean_object* v_a_1920_, lean_object* v_a_1921_){
_start:
{
lean_object* v_res_1922_; 
v_res_1922_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll___redArg(v_a_1915_, v_a_1916_, v_a_1917_, v_a_1918_, v_a_1919_, v_a_1920_);
lean_dec(v_a_1920_);
lean_dec_ref(v_a_1919_);
lean_dec(v_a_1918_);
lean_dec_ref(v_a_1917_);
lean_dec(v_a_1916_);
lean_dec_ref(v_a_1915_);
return v_res_1922_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll(lean_object* v_x_1923_, lean_object* v_a_1924_, lean_object* v_a_1925_, lean_object* v_a_1926_, lean_object* v_a_1927_, lean_object* v_a_1928_, lean_object* v_a_1929_, lean_object* v_a_1930_, lean_object* v_a_1931_){
_start:
{
lean_object* v___x_1933_; 
v___x_1933_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll___redArg(v_a_1924_, v_a_1925_, v_a_1928_, v_a_1929_, v_a_1930_, v_a_1931_);
return v___x_1933_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll___boxed(lean_object* v_x_1934_, lean_object* v_a_1935_, lean_object* v_a_1936_, lean_object* v_a_1937_, lean_object* v_a_1938_, lean_object* v_a_1939_, lean_object* v_a_1940_, lean_object* v_a_1941_, lean_object* v_a_1942_, lean_object* v_a_1943_){
_start:
{
lean_object* v_res_1944_; 
v_res_1944_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll(v_x_1934_, v_a_1935_, v_a_1936_, v_a_1937_, v_a_1938_, v_a_1939_, v_a_1940_, v_a_1941_, v_a_1942_);
lean_dec(v_a_1942_);
lean_dec_ref(v_a_1941_);
lean_dec(v_a_1940_);
lean_dec_ref(v_a_1939_);
lean_dec(v_a_1938_);
lean_dec_ref(v_a_1937_);
lean_dec(v_a_1936_);
lean_dec_ref(v_a_1935_);
lean_dec(v_x_1934_);
return v_res_1944_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll__1(){
_start:
{
lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; 
v___x_1957_ = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
v___x_1958_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll__1___closed__1));
v___x_1959_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll__1___closed__3));
v___x_1960_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll___boxed), 10, 0);
v___x_1961_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1957_, v___x_1958_, v___x_1959_, v___x_1960_);
return v___x_1961_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll__1___boxed(lean_object* v_a_1962_){
_start:
{
lean_object* v_res_1963_; 
v_res_1963_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll__1();
return v_res_1963_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___redArg___closed__1(void){
_start:
{
lean_object* v___x_1965_; lean_object* v___x_1966_; 
v___x_1965_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___redArg___closed__0));
v___x_1966_ = l_Lean_stringToMessageData(v___x_1965_);
return v___x_1966_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___redArg___closed__3(void){
_start:
{
lean_object* v___x_1968_; lean_object* v___x_1969_; 
v___x_1968_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___redArg___closed__2));
v___x_1969_ = l_Lean_stringToMessageData(v___x_1968_);
return v___x_1969_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___redArg(lean_object* v_a_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_){
_start:
{
lean_object* v___x_1977_; 
v___x_1977_ = l_Lean_Elab_Tactic_Grind_ensureSym___redArg(v_a_1970_, v_a_1972_, v_a_1973_, v_a_1974_, v_a_1975_);
if (lean_obj_tag(v___x_1977_) == 0)
{
lean_object* v___x_1978_; 
lean_dec_ref_known(v___x_1977_, 1);
v___x_1978_ = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_, v_a_1975_);
if (lean_obj_tag(v___x_1978_) == 0)
{
lean_object* v_a_1979_; lean_object* v_toGoalState_1980_; lean_object* v_mvarId_1981_; lean_object* v___x_1983_; uint8_t v_isShared_1984_; uint8_t v_isSharedCheck_2083_; 
v_a_1979_ = lean_ctor_get(v___x_1978_, 0);
lean_inc(v_a_1979_);
lean_dec_ref_known(v___x_1978_, 1);
v_toGoalState_1980_ = lean_ctor_get(v_a_1979_, 0);
v_mvarId_1981_ = lean_ctor_get(v_a_1979_, 1);
v_isSharedCheck_2083_ = !lean_is_exclusive(v_a_1979_);
if (v_isSharedCheck_2083_ == 0)
{
v___x_1983_ = v_a_1979_;
v_isShared_1984_ = v_isSharedCheck_2083_;
goto v_resetjp_1982_;
}
else
{
lean_inc(v_mvarId_1981_);
lean_inc(v_toGoalState_1980_);
lean_dec(v_a_1979_);
v___x_1983_ = lean_box(0);
v_isShared_1984_ = v_isSharedCheck_2083_;
goto v_resetjp_1982_;
}
v_resetjp_1982_:
{
lean_object* v_mvarId_1986_; lean_object* v___y_1987_; lean_object* v___y_1988_; lean_object* v___y_1989_; lean_object* v___y_1990_; lean_object* v___y_1991_; lean_object* v___y_1992_; lean_object* v___x_2042_; 
lean_inc(v_mvarId_1981_);
v___x_2042_ = l_Lean_MVarId_getType(v_mvarId_1981_, v_a_1972_, v_a_1973_, v_a_1974_, v_a_1975_);
if (lean_obj_tag(v___x_2042_) == 0)
{
lean_object* v_a_2043_; lean_object* v___y_2045_; lean_object* v___y_2046_; lean_object* v___y_2047_; lean_object* v___y_2048_; lean_object* v___y_2049_; lean_object* v___y_2050_; uint8_t v___x_2072_; 
v_a_2043_ = lean_ctor_get(v___x_2042_, 0);
lean_inc(v_a_2043_);
lean_dec_ref_known(v___x_2042_, 1);
v___x_2072_ = l_Lean_Expr_isFalse(v_a_2043_);
if (v___x_2072_ == 0)
{
v___y_2045_ = v_a_1970_;
v___y_2046_ = v_a_1971_;
v___y_2047_ = v_a_1972_;
v___y_2048_ = v_a_1973_;
v___y_2049_ = v_a_1974_;
v___y_2050_ = v_a_1975_;
goto v___jp_2044_;
}
else
{
lean_object* v___x_2073_; lean_object* v___x_2074_; 
lean_dec(v_a_2043_);
lean_del_object(v___x_1983_);
lean_dec(v_mvarId_1981_);
lean_dec_ref(v_toGoalState_1980_);
v___x_2073_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___redArg___closed__3, &l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___redArg___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___redArg___closed__3);
v___x_2074_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__2___redArg(v___x_2073_, v_a_1972_, v_a_1973_, v_a_1974_, v_a_1975_);
return v___x_2074_;
}
v___jp_2044_:
{
lean_object* v___x_2051_; 
v___x_2051_ = l_Lean_Meta_isProp(v_a_2043_, v___y_2047_, v___y_2048_, v___y_2049_, v___y_2050_);
if (lean_obj_tag(v___x_2051_) == 0)
{
lean_object* v_a_2052_; uint8_t v___x_2053_; 
v_a_2052_ = lean_ctor_get(v___x_2051_, 0);
lean_inc(v_a_2052_);
lean_dec_ref_known(v___x_2051_, 1);
v___x_2053_ = lean_unbox(v_a_2052_);
lean_dec(v_a_2052_);
if (v___x_2053_ == 0)
{
lean_object* v___x_2054_; 
v___x_2054_ = l_Lean_MVarId_exfalso(v_mvarId_1981_, v___y_2047_, v___y_2048_, v___y_2049_, v___y_2050_);
if (lean_obj_tag(v___x_2054_) == 0)
{
lean_object* v_a_2055_; 
v_a_2055_ = lean_ctor_get(v___x_2054_, 0);
lean_inc(v_a_2055_);
lean_dec_ref_known(v___x_2054_, 1);
v_mvarId_1986_ = v_a_2055_;
v___y_1987_ = v___y_2045_;
v___y_1988_ = v___y_2046_;
v___y_1989_ = v___y_2047_;
v___y_1990_ = v___y_2048_;
v___y_1991_ = v___y_2049_;
v___y_1992_ = v___y_2050_;
goto v___jp_1985_;
}
else
{
lean_object* v_a_2056_; lean_object* v___x_2058_; uint8_t v_isShared_2059_; uint8_t v_isSharedCheck_2063_; 
lean_del_object(v___x_1983_);
lean_dec_ref(v_toGoalState_1980_);
v_a_2056_ = lean_ctor_get(v___x_2054_, 0);
v_isSharedCheck_2063_ = !lean_is_exclusive(v___x_2054_);
if (v_isSharedCheck_2063_ == 0)
{
v___x_2058_ = v___x_2054_;
v_isShared_2059_ = v_isSharedCheck_2063_;
goto v_resetjp_2057_;
}
else
{
lean_inc(v_a_2056_);
lean_dec(v___x_2054_);
v___x_2058_ = lean_box(0);
v_isShared_2059_ = v_isSharedCheck_2063_;
goto v_resetjp_2057_;
}
v_resetjp_2057_:
{
lean_object* v___x_2061_; 
if (v_isShared_2059_ == 0)
{
v___x_2061_ = v___x_2058_;
goto v_reusejp_2060_;
}
else
{
lean_object* v_reuseFailAlloc_2062_; 
v_reuseFailAlloc_2062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2062_, 0, v_a_2056_);
v___x_2061_ = v_reuseFailAlloc_2062_;
goto v_reusejp_2060_;
}
v_reusejp_2060_:
{
return v___x_2061_;
}
}
}
}
else
{
v_mvarId_1986_ = v_mvarId_1981_;
v___y_1987_ = v___y_2045_;
v___y_1988_ = v___y_2046_;
v___y_1989_ = v___y_2047_;
v___y_1990_ = v___y_2048_;
v___y_1991_ = v___y_2049_;
v___y_1992_ = v___y_2050_;
goto v___jp_1985_;
}
}
else
{
lean_object* v_a_2064_; lean_object* v___x_2066_; uint8_t v_isShared_2067_; uint8_t v_isSharedCheck_2071_; 
lean_del_object(v___x_1983_);
lean_dec(v_mvarId_1981_);
lean_dec_ref(v_toGoalState_1980_);
v_a_2064_ = lean_ctor_get(v___x_2051_, 0);
v_isSharedCheck_2071_ = !lean_is_exclusive(v___x_2051_);
if (v_isSharedCheck_2071_ == 0)
{
v___x_2066_ = v___x_2051_;
v_isShared_2067_ = v_isSharedCheck_2071_;
goto v_resetjp_2065_;
}
else
{
lean_inc(v_a_2064_);
lean_dec(v___x_2051_);
v___x_2066_ = lean_box(0);
v_isShared_2067_ = v_isSharedCheck_2071_;
goto v_resetjp_2065_;
}
v_resetjp_2065_:
{
lean_object* v___x_2069_; 
if (v_isShared_2067_ == 0)
{
v___x_2069_ = v___x_2066_;
goto v_reusejp_2068_;
}
else
{
lean_object* v_reuseFailAlloc_2070_; 
v_reuseFailAlloc_2070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2070_, 0, v_a_2064_);
v___x_2069_ = v_reuseFailAlloc_2070_;
goto v_reusejp_2068_;
}
v_reusejp_2068_:
{
return v___x_2069_;
}
}
}
}
}
else
{
lean_object* v_a_2075_; lean_object* v___x_2077_; uint8_t v_isShared_2078_; uint8_t v_isSharedCheck_2082_; 
lean_del_object(v___x_1983_);
lean_dec(v_mvarId_1981_);
lean_dec_ref(v_toGoalState_1980_);
v_a_2075_ = lean_ctor_get(v___x_2042_, 0);
v_isSharedCheck_2082_ = !lean_is_exclusive(v___x_2042_);
if (v_isSharedCheck_2082_ == 0)
{
v___x_2077_ = v___x_2042_;
v_isShared_2078_ = v_isSharedCheck_2082_;
goto v_resetjp_2076_;
}
else
{
lean_inc(v_a_2075_);
lean_dec(v___x_2042_);
v___x_2077_ = lean_box(0);
v_isShared_2078_ = v_isSharedCheck_2082_;
goto v_resetjp_2076_;
}
v_resetjp_2076_:
{
lean_object* v___x_2080_; 
if (v_isShared_2078_ == 0)
{
v___x_2080_ = v___x_2077_;
goto v_reusejp_2079_;
}
else
{
lean_object* v_reuseFailAlloc_2081_; 
v_reuseFailAlloc_2081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2081_, 0, v_a_2075_);
v___x_2080_ = v_reuseFailAlloc_2081_;
goto v_reusejp_2079_;
}
v_reusejp_2079_:
{
return v___x_2080_;
}
}
}
v___jp_1985_:
{
lean_object* v___x_1993_; 
v___x_1993_ = l_Lean_MVarId_byContra_x3f(v_mvarId_1986_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_);
if (lean_obj_tag(v___x_1993_) == 0)
{
lean_object* v_a_1994_; 
v_a_1994_ = lean_ctor_get(v___x_1993_, 0);
lean_inc(v_a_1994_);
lean_dec_ref_known(v___x_1993_, 1);
if (lean_obj_tag(v_a_1994_) == 1)
{
lean_object* v_val_1995_; uint8_t v___x_1996_; lean_object* v___x_1997_; 
v_val_1995_ = lean_ctor_get(v_a_1994_, 0);
lean_inc(v_val_1995_);
lean_dec_ref_known(v_a_1994_, 1);
v___x_1996_ = 0;
v___x_1997_ = l_Lean_Meta_intro1Core(v_val_1995_, v___x_1996_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_);
if (lean_obj_tag(v___x_1997_) == 0)
{
lean_object* v_a_1998_; lean_object* v_snd_1999_; lean_object* v___x_2001_; uint8_t v_isShared_2002_; uint8_t v_isSharedCheck_2022_; 
v_a_1998_ = lean_ctor_get(v___x_1997_, 0);
lean_inc(v_a_1998_);
lean_dec_ref_known(v___x_1997_, 1);
v_snd_1999_ = lean_ctor_get(v_a_1998_, 1);
v_isSharedCheck_2022_ = !lean_is_exclusive(v_a_1998_);
if (v_isSharedCheck_2022_ == 0)
{
lean_object* v_unused_2023_; 
v_unused_2023_ = lean_ctor_get(v_a_1998_, 0);
lean_dec(v_unused_2023_);
v___x_2001_ = v_a_1998_;
v_isShared_2002_ = v_isSharedCheck_2022_;
goto v_resetjp_2000_;
}
else
{
lean_inc(v_snd_1999_);
lean_dec(v_a_1998_);
v___x_2001_ = lean_box(0);
v_isShared_2002_ = v_isSharedCheck_2022_;
goto v_resetjp_2000_;
}
v_resetjp_2000_:
{
lean_object* v___x_2004_; 
if (v_isShared_1984_ == 0)
{
lean_ctor_set(v___x_1983_, 1, v_snd_1999_);
v___x_2004_ = v___x_1983_;
goto v_reusejp_2003_;
}
else
{
lean_object* v_reuseFailAlloc_2021_; 
v_reuseFailAlloc_2021_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2021_, 0, v_toGoalState_1980_);
lean_ctor_set(v_reuseFailAlloc_2021_, 1, v_snd_1999_);
v___x_2004_ = v_reuseFailAlloc_2021_;
goto v_reusejp_2003_;
}
v_reusejp_2003_:
{
lean_object* v___x_2005_; lean_object* v___x_2006_; 
v___x_2005_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Goal_internalizeAll___boxed), 11, 1);
lean_closure_set(v___x_2005_, 0, v___x_2004_);
v___x_2006_ = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(v___x_2005_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_);
if (lean_obj_tag(v___x_2006_) == 0)
{
lean_object* v_a_2007_; lean_object* v___x_2008_; lean_object* v___x_2010_; 
v_a_2007_ = lean_ctor_get(v___x_2006_, 0);
lean_inc(v_a_2007_);
lean_dec_ref_known(v___x_2006_, 1);
v___x_2008_ = lean_box(0);
if (v_isShared_2002_ == 0)
{
lean_ctor_set_tag(v___x_2001_, 1);
lean_ctor_set(v___x_2001_, 1, v___x_2008_);
lean_ctor_set(v___x_2001_, 0, v_a_2007_);
v___x_2010_ = v___x_2001_;
goto v_reusejp_2009_;
}
else
{
lean_object* v_reuseFailAlloc_2012_; 
v_reuseFailAlloc_2012_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2012_, 0, v_a_2007_);
lean_ctor_set(v_reuseFailAlloc_2012_, 1, v___x_2008_);
v___x_2010_ = v_reuseFailAlloc_2012_;
goto v_reusejp_2009_;
}
v_reusejp_2009_:
{
lean_object* v___x_2011_; 
v___x_2011_ = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(v___x_2010_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_);
return v___x_2011_;
}
}
else
{
lean_object* v_a_2013_; lean_object* v___x_2015_; uint8_t v_isShared_2016_; uint8_t v_isSharedCheck_2020_; 
lean_del_object(v___x_2001_);
v_a_2013_ = lean_ctor_get(v___x_2006_, 0);
v_isSharedCheck_2020_ = !lean_is_exclusive(v___x_2006_);
if (v_isSharedCheck_2020_ == 0)
{
v___x_2015_ = v___x_2006_;
v_isShared_2016_ = v_isSharedCheck_2020_;
goto v_resetjp_2014_;
}
else
{
lean_inc(v_a_2013_);
lean_dec(v___x_2006_);
v___x_2015_ = lean_box(0);
v_isShared_2016_ = v_isSharedCheck_2020_;
goto v_resetjp_2014_;
}
v_resetjp_2014_:
{
lean_object* v___x_2018_; 
if (v_isShared_2016_ == 0)
{
v___x_2018_ = v___x_2015_;
goto v_reusejp_2017_;
}
else
{
lean_object* v_reuseFailAlloc_2019_; 
v_reuseFailAlloc_2019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2019_, 0, v_a_2013_);
v___x_2018_ = v_reuseFailAlloc_2019_;
goto v_reusejp_2017_;
}
v_reusejp_2017_:
{
return v___x_2018_;
}
}
}
}
}
}
else
{
lean_object* v_a_2024_; lean_object* v___x_2026_; uint8_t v_isShared_2027_; uint8_t v_isSharedCheck_2031_; 
lean_del_object(v___x_1983_);
lean_dec_ref(v_toGoalState_1980_);
v_a_2024_ = lean_ctor_get(v___x_1997_, 0);
v_isSharedCheck_2031_ = !lean_is_exclusive(v___x_1997_);
if (v_isSharedCheck_2031_ == 0)
{
v___x_2026_ = v___x_1997_;
v_isShared_2027_ = v_isSharedCheck_2031_;
goto v_resetjp_2025_;
}
else
{
lean_inc(v_a_2024_);
lean_dec(v___x_1997_);
v___x_2026_ = lean_box(0);
v_isShared_2027_ = v_isSharedCheck_2031_;
goto v_resetjp_2025_;
}
v_resetjp_2025_:
{
lean_object* v___x_2029_; 
if (v_isShared_2027_ == 0)
{
v___x_2029_ = v___x_2026_;
goto v_reusejp_2028_;
}
else
{
lean_object* v_reuseFailAlloc_2030_; 
v_reuseFailAlloc_2030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2030_, 0, v_a_2024_);
v___x_2029_ = v_reuseFailAlloc_2030_;
goto v_reusejp_2028_;
}
v_reusejp_2028_:
{
return v___x_2029_;
}
}
}
}
else
{
lean_object* v___x_2032_; lean_object* v___x_2033_; 
lean_dec(v_a_1994_);
lean_del_object(v___x_1983_);
lean_dec_ref(v_toGoalState_1980_);
v___x_2032_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___redArg___closed__1, &l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___redArg___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___redArg___closed__1);
v___x_2033_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__2___redArg(v___x_2032_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_);
return v___x_2033_;
}
}
else
{
lean_object* v_a_2034_; lean_object* v___x_2036_; uint8_t v_isShared_2037_; uint8_t v_isSharedCheck_2041_; 
lean_del_object(v___x_1983_);
lean_dec_ref(v_toGoalState_1980_);
v_a_2034_ = lean_ctor_get(v___x_1993_, 0);
v_isSharedCheck_2041_ = !lean_is_exclusive(v___x_1993_);
if (v_isSharedCheck_2041_ == 0)
{
v___x_2036_ = v___x_1993_;
v_isShared_2037_ = v_isSharedCheck_2041_;
goto v_resetjp_2035_;
}
else
{
lean_inc(v_a_2034_);
lean_dec(v___x_1993_);
v___x_2036_ = lean_box(0);
v_isShared_2037_ = v_isSharedCheck_2041_;
goto v_resetjp_2035_;
}
v_resetjp_2035_:
{
lean_object* v___x_2039_; 
if (v_isShared_2037_ == 0)
{
v___x_2039_ = v___x_2036_;
goto v_reusejp_2038_;
}
else
{
lean_object* v_reuseFailAlloc_2040_; 
v_reuseFailAlloc_2040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2040_, 0, v_a_2034_);
v___x_2039_ = v_reuseFailAlloc_2040_;
goto v_reusejp_2038_;
}
v_reusejp_2038_:
{
return v___x_2039_;
}
}
}
}
}
}
else
{
lean_object* v_a_2084_; lean_object* v___x_2086_; uint8_t v_isShared_2087_; uint8_t v_isSharedCheck_2091_; 
v_a_2084_ = lean_ctor_get(v___x_1978_, 0);
v_isSharedCheck_2091_ = !lean_is_exclusive(v___x_1978_);
if (v_isSharedCheck_2091_ == 0)
{
v___x_2086_ = v___x_1978_;
v_isShared_2087_ = v_isSharedCheck_2091_;
goto v_resetjp_2085_;
}
else
{
lean_inc(v_a_2084_);
lean_dec(v___x_1978_);
v___x_2086_ = lean_box(0);
v_isShared_2087_ = v_isSharedCheck_2091_;
goto v_resetjp_2085_;
}
v_resetjp_2085_:
{
lean_object* v___x_2089_; 
if (v_isShared_2087_ == 0)
{
v___x_2089_ = v___x_2086_;
goto v_reusejp_2088_;
}
else
{
lean_object* v_reuseFailAlloc_2090_; 
v_reuseFailAlloc_2090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2090_, 0, v_a_2084_);
v___x_2089_ = v_reuseFailAlloc_2090_;
goto v_reusejp_2088_;
}
v_reusejp_2088_:
{
return v___x_2089_;
}
}
}
}
else
{
return v___x_1977_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___redArg___boxed(lean_object* v_a_2092_, lean_object* v_a_2093_, lean_object* v_a_2094_, lean_object* v_a_2095_, lean_object* v_a_2096_, lean_object* v_a_2097_, lean_object* v_a_2098_){
_start:
{
lean_object* v_res_2099_; 
v_res_2099_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___redArg(v_a_2092_, v_a_2093_, v_a_2094_, v_a_2095_, v_a_2096_, v_a_2097_);
lean_dec(v_a_2097_);
lean_dec_ref(v_a_2096_);
lean_dec(v_a_2095_);
lean_dec_ref(v_a_2094_);
lean_dec(v_a_2093_);
lean_dec_ref(v_a_2092_);
return v_res_2099_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra(lean_object* v_x_2100_, lean_object* v_a_2101_, lean_object* v_a_2102_, lean_object* v_a_2103_, lean_object* v_a_2104_, lean_object* v_a_2105_, lean_object* v_a_2106_, lean_object* v_a_2107_, lean_object* v_a_2108_){
_start:
{
lean_object* v___x_2110_; 
v___x_2110_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___redArg(v_a_2101_, v_a_2102_, v_a_2105_, v_a_2106_, v_a_2107_, v_a_2108_);
return v___x_2110_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___boxed(lean_object* v_x_2111_, lean_object* v_a_2112_, lean_object* v_a_2113_, lean_object* v_a_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_, lean_object* v_a_2119_, lean_object* v_a_2120_){
_start:
{
lean_object* v_res_2121_; 
v_res_2121_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra(v_x_2111_, v_a_2112_, v_a_2113_, v_a_2114_, v_a_2115_, v_a_2116_, v_a_2117_, v_a_2118_, v_a_2119_);
lean_dec(v_a_2119_);
lean_dec_ref(v_a_2118_);
lean_dec(v_a_2117_);
lean_dec_ref(v_a_2116_);
lean_dec(v_a_2115_);
lean_dec_ref(v_a_2114_);
lean_dec(v_a_2113_);
lean_dec_ref(v_a_2112_);
lean_dec(v_x_2111_);
return v_res_2121_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra__1(){
_start:
{
lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; 
v___x_2134_ = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
v___x_2135_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra__1___closed__1));
v___x_2136_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra__1___closed__3));
v___x_2137_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___boxed), 10, 0);
v___x_2138_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2134_, v___x_2135_, v___x_2136_, v___x_2137_);
return v___x_2138_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra__1___boxed(lean_object* v_a_2139_){
_start:
{
lean_object* v_res_2140_; 
v_res_2140_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra__1();
return v_res_2140_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_trivialSimproc___redArg(){
_start:
{
lean_object* v___x_2144_; lean_object* v___x_2145_; 
v___x_2144_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_trivialSimproc___redArg___closed__0));
v___x_2145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2145_, 0, v___x_2144_);
return v___x_2145_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_trivialSimproc___redArg___boxed(lean_object* v_a_2146_){
_start:
{
lean_object* v_res_2147_; 
v_res_2147_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_trivialSimproc___redArg();
return v_res_2147_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_trivialSimproc(lean_object* v_x_2148_, lean_object* v_a_2149_, lean_object* v_a_2150_, lean_object* v_a_2151_, lean_object* v_a_2152_, lean_object* v_a_2153_, lean_object* v_a_2154_, lean_object* v_a_2155_, lean_object* v_a_2156_, lean_object* v_a_2157_){
_start:
{
lean_object* v___x_2159_; 
v___x_2159_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_trivialSimproc___redArg();
return v___x_2159_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_trivialSimproc___boxed(lean_object* v_x_2160_, lean_object* v_a_2161_, lean_object* v_a_2162_, lean_object* v_a_2163_, lean_object* v_a_2164_, lean_object* v_a_2165_, lean_object* v_a_2166_, lean_object* v_a_2167_, lean_object* v_a_2168_, lean_object* v_a_2169_, lean_object* v_a_2170_){
_start:
{
lean_object* v_res_2171_; 
v_res_2171_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_trivialSimproc(v_x_2160_, v_a_2161_, v_a_2162_, v_a_2163_, v_a_2164_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_, v_a_2169_);
lean_dec(v_a_2169_);
lean_dec_ref(v_a_2168_);
lean_dec(v_a_2167_);
lean_dec_ref(v_a_2166_);
lean_dec(v_a_2165_);
lean_dec_ref(v_a_2164_);
lean_dec(v_a_2163_);
lean_dec_ref(v_a_2162_);
lean_dec(v_a_2161_);
lean_dec_ref(v_x_2160_);
return v_res_2171_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabOptSimproc(lean_object* v_stx_x3f_2172_, lean_object* v_a_2173_, lean_object* v_a_2174_, lean_object* v_a_2175_, lean_object* v_a_2176_, lean_object* v_a_2177_, lean_object* v_a_2178_, lean_object* v_a_2179_, lean_object* v_a_2180_){
_start:
{
if (lean_obj_tag(v_stx_x3f_2172_) == 1)
{
lean_object* v_val_2182_; lean_object* v___x_2183_; 
v_val_2182_ = lean_ctor_get(v_stx_x3f_2172_, 0);
lean_inc(v_val_2182_);
lean_dec_ref_known(v_stx_x3f_2172_, 1);
v___x_2183_ = l_Lean_Elab_Tactic_Grind_elabSymSimproc(v_val_2182_, v_a_2173_, v_a_2174_, v_a_2175_, v_a_2176_, v_a_2177_, v_a_2178_, v_a_2179_, v_a_2180_);
return v___x_2183_;
}
else
{
lean_object* v___x_2184_; lean_object* v___x_2185_; 
lean_dec(v_stx_x3f_2172_);
v___x_2184_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_trivialSimproc___boxed), 11, 0);
v___x_2185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2185_, 0, v___x_2184_);
return v___x_2185_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabOptSimproc___boxed(lean_object* v_stx_x3f_2186_, lean_object* v_a_2187_, lean_object* v_a_2188_, lean_object* v_a_2189_, lean_object* v_a_2190_, lean_object* v_a_2191_, lean_object* v_a_2192_, lean_object* v_a_2193_, lean_object* v_a_2194_, lean_object* v_a_2195_){
_start:
{
lean_object* v_res_2196_; 
v_res_2196_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabOptSimproc(v_stx_x3f_2186_, v_a_2187_, v_a_2188_, v_a_2189_, v_a_2190_, v_a_2191_, v_a_2192_, v_a_2193_, v_a_2194_);
lean_dec(v_a_2194_);
lean_dec_ref(v_a_2193_);
lean_dec(v_a_2192_);
lean_dec_ref(v_a_2191_);
lean_dec(v_a_2190_);
lean_dec_ref(v_a_2189_);
lean_dec(v_a_2188_);
lean_dec_ref(v_a_2187_);
return v_res_2196_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabOptDischarger(lean_object* v_stx_x3f_2198_, lean_object* v_a_2199_, lean_object* v_a_2200_, lean_object* v_a_2201_, lean_object* v_a_2202_, lean_object* v_a_2203_, lean_object* v_a_2204_, lean_object* v_a_2205_, lean_object* v_a_2206_){
_start:
{
if (lean_obj_tag(v_stx_x3f_2198_) == 1)
{
lean_object* v_val_2208_; lean_object* v___x_2209_; 
v_val_2208_ = lean_ctor_get(v_stx_x3f_2198_, 0);
lean_inc(v_val_2208_);
lean_dec_ref_known(v_stx_x3f_2198_, 1);
v___x_2209_ = l_Lean_Elab_Tactic_Grind_elabSymDischarger(v_val_2208_, v_a_2199_, v_a_2200_, v_a_2201_, v_a_2202_, v_a_2203_, v_a_2204_, v_a_2205_, v_a_2206_);
return v___x_2209_;
}
else
{
lean_object* v___x_2210_; lean_object* v___x_2211_; 
lean_dec(v_stx_x3f_2198_);
v___x_2210_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabOptDischarger___closed__0));
v___x_2211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2211_, 0, v___x_2210_);
return v___x_2211_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabOptDischarger___boxed(lean_object* v_stx_x3f_2212_, lean_object* v_a_2213_, lean_object* v_a_2214_, lean_object* v_a_2215_, lean_object* v_a_2216_, lean_object* v_a_2217_, lean_object* v_a_2218_, lean_object* v_a_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_){
_start:
{
lean_object* v_res_2222_; 
v_res_2222_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabOptDischarger(v_stx_x3f_2212_, v_a_2213_, v_a_2214_, v_a_2215_, v_a_2216_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_);
lean_dec(v_a_2220_);
lean_dec_ref(v_a_2219_);
lean_dec(v_a_2218_);
lean_dec_ref(v_a_2217_);
lean_dec(v_a_2216_);
lean_dec_ref(v_a_2215_);
lean_dec(v_a_2214_);
lean_dec_ref(v_a_2213_);
return v_res_2222_;
}
}
static lean_object* _init_l_panic___at___00Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2223_; 
v___x_2223_ = l_instMonadEIO___redArg();
return v___x_2223_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__0_spec__0(lean_object* v_msg_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_){
_start:
{
lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v_toApplicative_2244_; lean_object* v___x_2246_; uint8_t v_isShared_2247_; uint8_t v_isSharedCheck_2365_; 
v___x_2242_ = lean_obj_once(&l_panic___at___00Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__0_spec__0___closed__0, &l_panic___at___00Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__0_spec__0___closed__0_once, _init_l_panic___at___00Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__0_spec__0___closed__0);
v___x_2243_ = l_StateRefT_x27_instMonad___redArg(v___x_2242_);
v_toApplicative_2244_ = lean_ctor_get(v___x_2243_, 0);
v_isSharedCheck_2365_ = !lean_is_exclusive(v___x_2243_);
if (v_isSharedCheck_2365_ == 0)
{
lean_object* v_unused_2366_; 
v_unused_2366_ = lean_ctor_get(v___x_2243_, 1);
lean_dec(v_unused_2366_);
v___x_2246_ = v___x_2243_;
v_isShared_2247_ = v_isSharedCheck_2365_;
goto v_resetjp_2245_;
}
else
{
lean_inc(v_toApplicative_2244_);
lean_dec(v___x_2243_);
v___x_2246_ = lean_box(0);
v_isShared_2247_ = v_isSharedCheck_2365_;
goto v_resetjp_2245_;
}
v_resetjp_2245_:
{
lean_object* v_toFunctor_2248_; lean_object* v_toSeq_2249_; lean_object* v_toSeqLeft_2250_; lean_object* v_toSeqRight_2251_; lean_object* v___x_2253_; uint8_t v_isShared_2254_; uint8_t v_isSharedCheck_2363_; 
v_toFunctor_2248_ = lean_ctor_get(v_toApplicative_2244_, 0);
v_toSeq_2249_ = lean_ctor_get(v_toApplicative_2244_, 2);
v_toSeqLeft_2250_ = lean_ctor_get(v_toApplicative_2244_, 3);
v_toSeqRight_2251_ = lean_ctor_get(v_toApplicative_2244_, 4);
v_isSharedCheck_2363_ = !lean_is_exclusive(v_toApplicative_2244_);
if (v_isSharedCheck_2363_ == 0)
{
lean_object* v_unused_2364_; 
v_unused_2364_ = lean_ctor_get(v_toApplicative_2244_, 1);
lean_dec(v_unused_2364_);
v___x_2253_ = v_toApplicative_2244_;
v_isShared_2254_ = v_isSharedCheck_2363_;
goto v_resetjp_2252_;
}
else
{
lean_inc(v_toSeqRight_2251_);
lean_inc(v_toSeqLeft_2250_);
lean_inc(v_toSeq_2249_);
lean_inc(v_toFunctor_2248_);
lean_dec(v_toApplicative_2244_);
v___x_2253_ = lean_box(0);
v_isShared_2254_ = v_isSharedCheck_2363_;
goto v_resetjp_2252_;
}
v_resetjp_2252_:
{
lean_object* v___f_2255_; lean_object* v___f_2256_; lean_object* v___f_2257_; lean_object* v___f_2258_; lean_object* v___x_2259_; lean_object* v___f_2260_; lean_object* v___f_2261_; lean_object* v___f_2262_; lean_object* v___x_2264_; 
v___f_2255_ = ((lean_object*)(l_panic___at___00Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__0_spec__0___closed__1));
v___f_2256_ = ((lean_object*)(l_panic___at___00Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__0_spec__0___closed__2));
lean_inc_ref(v_toFunctor_2248_);
v___f_2257_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2257_, 0, v_toFunctor_2248_);
v___f_2258_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2258_, 0, v_toFunctor_2248_);
v___x_2259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2259_, 0, v___f_2257_);
lean_ctor_set(v___x_2259_, 1, v___f_2258_);
v___f_2260_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2260_, 0, v_toSeqRight_2251_);
v___f_2261_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2261_, 0, v_toSeqLeft_2250_);
v___f_2262_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2262_, 0, v_toSeq_2249_);
if (v_isShared_2254_ == 0)
{
lean_ctor_set(v___x_2253_, 4, v___f_2260_);
lean_ctor_set(v___x_2253_, 3, v___f_2261_);
lean_ctor_set(v___x_2253_, 2, v___f_2262_);
lean_ctor_set(v___x_2253_, 1, v___f_2255_);
lean_ctor_set(v___x_2253_, 0, v___x_2259_);
v___x_2264_ = v___x_2253_;
goto v_reusejp_2263_;
}
else
{
lean_object* v_reuseFailAlloc_2362_; 
v_reuseFailAlloc_2362_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2362_, 0, v___x_2259_);
lean_ctor_set(v_reuseFailAlloc_2362_, 1, v___f_2255_);
lean_ctor_set(v_reuseFailAlloc_2362_, 2, v___f_2262_);
lean_ctor_set(v_reuseFailAlloc_2362_, 3, v___f_2261_);
lean_ctor_set(v_reuseFailAlloc_2362_, 4, v___f_2260_);
v___x_2264_ = v_reuseFailAlloc_2362_;
goto v_reusejp_2263_;
}
v_reusejp_2263_:
{
lean_object* v___x_2266_; 
if (v_isShared_2247_ == 0)
{
lean_ctor_set(v___x_2246_, 1, v___f_2256_);
lean_ctor_set(v___x_2246_, 0, v___x_2264_);
v___x_2266_ = v___x_2246_;
goto v_reusejp_2265_;
}
else
{
lean_object* v_reuseFailAlloc_2361_; 
v_reuseFailAlloc_2361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2361_, 0, v___x_2264_);
lean_ctor_set(v_reuseFailAlloc_2361_, 1, v___f_2256_);
v___x_2266_ = v_reuseFailAlloc_2361_;
goto v_reusejp_2265_;
}
v_reusejp_2265_:
{
lean_object* v___x_2267_; lean_object* v_toApplicative_2268_; lean_object* v___x_2270_; uint8_t v_isShared_2271_; uint8_t v_isSharedCheck_2359_; 
v___x_2267_ = l_StateRefT_x27_instMonad___redArg(v___x_2266_);
v_toApplicative_2268_ = lean_ctor_get(v___x_2267_, 0);
v_isSharedCheck_2359_ = !lean_is_exclusive(v___x_2267_);
if (v_isSharedCheck_2359_ == 0)
{
lean_object* v_unused_2360_; 
v_unused_2360_ = lean_ctor_get(v___x_2267_, 1);
lean_dec(v_unused_2360_);
v___x_2270_ = v___x_2267_;
v_isShared_2271_ = v_isSharedCheck_2359_;
goto v_resetjp_2269_;
}
else
{
lean_inc(v_toApplicative_2268_);
lean_dec(v___x_2267_);
v___x_2270_ = lean_box(0);
v_isShared_2271_ = v_isSharedCheck_2359_;
goto v_resetjp_2269_;
}
v_resetjp_2269_:
{
lean_object* v_toFunctor_2272_; lean_object* v_toSeq_2273_; lean_object* v_toSeqLeft_2274_; lean_object* v_toSeqRight_2275_; lean_object* v___x_2277_; uint8_t v_isShared_2278_; uint8_t v_isSharedCheck_2357_; 
v_toFunctor_2272_ = lean_ctor_get(v_toApplicative_2268_, 0);
v_toSeq_2273_ = lean_ctor_get(v_toApplicative_2268_, 2);
v_toSeqLeft_2274_ = lean_ctor_get(v_toApplicative_2268_, 3);
v_toSeqRight_2275_ = lean_ctor_get(v_toApplicative_2268_, 4);
v_isSharedCheck_2357_ = !lean_is_exclusive(v_toApplicative_2268_);
if (v_isSharedCheck_2357_ == 0)
{
lean_object* v_unused_2358_; 
v_unused_2358_ = lean_ctor_get(v_toApplicative_2268_, 1);
lean_dec(v_unused_2358_);
v___x_2277_ = v_toApplicative_2268_;
v_isShared_2278_ = v_isSharedCheck_2357_;
goto v_resetjp_2276_;
}
else
{
lean_inc(v_toSeqRight_2275_);
lean_inc(v_toSeqLeft_2274_);
lean_inc(v_toSeq_2273_);
lean_inc(v_toFunctor_2272_);
lean_dec(v_toApplicative_2268_);
v___x_2277_ = lean_box(0);
v_isShared_2278_ = v_isSharedCheck_2357_;
goto v_resetjp_2276_;
}
v_resetjp_2276_:
{
lean_object* v___f_2279_; lean_object* v___f_2280_; lean_object* v___f_2281_; lean_object* v___f_2282_; lean_object* v___x_2283_; lean_object* v___f_2284_; lean_object* v___f_2285_; lean_object* v___f_2286_; lean_object* v___x_2288_; 
v___f_2279_ = ((lean_object*)(l_panic___at___00Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__0_spec__0___closed__3));
v___f_2280_ = ((lean_object*)(l_panic___at___00Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__0_spec__0___closed__4));
lean_inc_ref(v_toFunctor_2272_);
v___f_2281_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2281_, 0, v_toFunctor_2272_);
v___f_2282_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2282_, 0, v_toFunctor_2272_);
v___x_2283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2283_, 0, v___f_2281_);
lean_ctor_set(v___x_2283_, 1, v___f_2282_);
v___f_2284_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2284_, 0, v_toSeqRight_2275_);
v___f_2285_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2285_, 0, v_toSeqLeft_2274_);
v___f_2286_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2286_, 0, v_toSeq_2273_);
if (v_isShared_2278_ == 0)
{
lean_ctor_set(v___x_2277_, 4, v___f_2284_);
lean_ctor_set(v___x_2277_, 3, v___f_2285_);
lean_ctor_set(v___x_2277_, 2, v___f_2286_);
lean_ctor_set(v___x_2277_, 1, v___f_2279_);
lean_ctor_set(v___x_2277_, 0, v___x_2283_);
v___x_2288_ = v___x_2277_;
goto v_reusejp_2287_;
}
else
{
lean_object* v_reuseFailAlloc_2356_; 
v_reuseFailAlloc_2356_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2356_, 0, v___x_2283_);
lean_ctor_set(v_reuseFailAlloc_2356_, 1, v___f_2279_);
lean_ctor_set(v_reuseFailAlloc_2356_, 2, v___f_2286_);
lean_ctor_set(v_reuseFailAlloc_2356_, 3, v___f_2285_);
lean_ctor_set(v_reuseFailAlloc_2356_, 4, v___f_2284_);
v___x_2288_ = v_reuseFailAlloc_2356_;
goto v_reusejp_2287_;
}
v_reusejp_2287_:
{
lean_object* v___x_2290_; 
if (v_isShared_2271_ == 0)
{
lean_ctor_set(v___x_2270_, 1, v___f_2280_);
lean_ctor_set(v___x_2270_, 0, v___x_2288_);
v___x_2290_ = v___x_2270_;
goto v_reusejp_2289_;
}
else
{
lean_object* v_reuseFailAlloc_2355_; 
v_reuseFailAlloc_2355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2355_, 0, v___x_2288_);
lean_ctor_set(v_reuseFailAlloc_2355_, 1, v___f_2280_);
v___x_2290_ = v_reuseFailAlloc_2355_;
goto v_reusejp_2289_;
}
v_reusejp_2289_:
{
lean_object* v___x_2291_; lean_object* v_toApplicative_2292_; lean_object* v___x_2294_; uint8_t v_isShared_2295_; uint8_t v_isSharedCheck_2353_; 
v___x_2291_ = l_StateRefT_x27_instMonad___redArg(v___x_2290_);
v_toApplicative_2292_ = lean_ctor_get(v___x_2291_, 0);
v_isSharedCheck_2353_ = !lean_is_exclusive(v___x_2291_);
if (v_isSharedCheck_2353_ == 0)
{
lean_object* v_unused_2354_; 
v_unused_2354_ = lean_ctor_get(v___x_2291_, 1);
lean_dec(v_unused_2354_);
v___x_2294_ = v___x_2291_;
v_isShared_2295_ = v_isSharedCheck_2353_;
goto v_resetjp_2293_;
}
else
{
lean_inc(v_toApplicative_2292_);
lean_dec(v___x_2291_);
v___x_2294_ = lean_box(0);
v_isShared_2295_ = v_isSharedCheck_2353_;
goto v_resetjp_2293_;
}
v_resetjp_2293_:
{
lean_object* v_toFunctor_2296_; lean_object* v_toSeq_2297_; lean_object* v_toSeqLeft_2298_; lean_object* v_toSeqRight_2299_; lean_object* v___x_2301_; uint8_t v_isShared_2302_; uint8_t v_isSharedCheck_2351_; 
v_toFunctor_2296_ = lean_ctor_get(v_toApplicative_2292_, 0);
v_toSeq_2297_ = lean_ctor_get(v_toApplicative_2292_, 2);
v_toSeqLeft_2298_ = lean_ctor_get(v_toApplicative_2292_, 3);
v_toSeqRight_2299_ = lean_ctor_get(v_toApplicative_2292_, 4);
v_isSharedCheck_2351_ = !lean_is_exclusive(v_toApplicative_2292_);
if (v_isSharedCheck_2351_ == 0)
{
lean_object* v_unused_2352_; 
v_unused_2352_ = lean_ctor_get(v_toApplicative_2292_, 1);
lean_dec(v_unused_2352_);
v___x_2301_ = v_toApplicative_2292_;
v_isShared_2302_ = v_isSharedCheck_2351_;
goto v_resetjp_2300_;
}
else
{
lean_inc(v_toSeqRight_2299_);
lean_inc(v_toSeqLeft_2298_);
lean_inc(v_toSeq_2297_);
lean_inc(v_toFunctor_2296_);
lean_dec(v_toApplicative_2292_);
v___x_2301_ = lean_box(0);
v_isShared_2302_ = v_isSharedCheck_2351_;
goto v_resetjp_2300_;
}
v_resetjp_2300_:
{
lean_object* v___f_2303_; lean_object* v___f_2304_; lean_object* v___f_2305_; lean_object* v___f_2306_; lean_object* v___x_2307_; lean_object* v___f_2308_; lean_object* v___f_2309_; lean_object* v___f_2310_; lean_object* v___x_2312_; 
v___f_2303_ = ((lean_object*)(l_panic___at___00Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__0_spec__0___closed__5));
v___f_2304_ = ((lean_object*)(l_panic___at___00Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__0_spec__0___closed__6));
lean_inc_ref(v_toFunctor_2296_);
v___f_2305_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2305_, 0, v_toFunctor_2296_);
v___f_2306_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2306_, 0, v_toFunctor_2296_);
v___x_2307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2307_, 0, v___f_2305_);
lean_ctor_set(v___x_2307_, 1, v___f_2306_);
v___f_2308_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2308_, 0, v_toSeqRight_2299_);
v___f_2309_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2309_, 0, v_toSeqLeft_2298_);
v___f_2310_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2310_, 0, v_toSeq_2297_);
if (v_isShared_2302_ == 0)
{
lean_ctor_set(v___x_2301_, 4, v___f_2308_);
lean_ctor_set(v___x_2301_, 3, v___f_2309_);
lean_ctor_set(v___x_2301_, 2, v___f_2310_);
lean_ctor_set(v___x_2301_, 1, v___f_2303_);
lean_ctor_set(v___x_2301_, 0, v___x_2307_);
v___x_2312_ = v___x_2301_;
goto v_reusejp_2311_;
}
else
{
lean_object* v_reuseFailAlloc_2350_; 
v_reuseFailAlloc_2350_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2350_, 0, v___x_2307_);
lean_ctor_set(v_reuseFailAlloc_2350_, 1, v___f_2303_);
lean_ctor_set(v_reuseFailAlloc_2350_, 2, v___f_2310_);
lean_ctor_set(v_reuseFailAlloc_2350_, 3, v___f_2309_);
lean_ctor_set(v_reuseFailAlloc_2350_, 4, v___f_2308_);
v___x_2312_ = v_reuseFailAlloc_2350_;
goto v_reusejp_2311_;
}
v_reusejp_2311_:
{
lean_object* v___x_2314_; 
if (v_isShared_2295_ == 0)
{
lean_ctor_set(v___x_2294_, 1, v___f_2304_);
lean_ctor_set(v___x_2294_, 0, v___x_2312_);
v___x_2314_ = v___x_2294_;
goto v_reusejp_2313_;
}
else
{
lean_object* v_reuseFailAlloc_2349_; 
v_reuseFailAlloc_2349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2349_, 0, v___x_2312_);
lean_ctor_set(v_reuseFailAlloc_2349_, 1, v___f_2304_);
v___x_2314_ = v_reuseFailAlloc_2349_;
goto v_reusejp_2313_;
}
v_reusejp_2313_:
{
lean_object* v___x_2315_; lean_object* v_toApplicative_2316_; lean_object* v___x_2318_; uint8_t v_isShared_2319_; uint8_t v_isSharedCheck_2347_; 
v___x_2315_ = l_StateRefT_x27_instMonad___redArg(v___x_2314_);
v_toApplicative_2316_ = lean_ctor_get(v___x_2315_, 0);
v_isSharedCheck_2347_ = !lean_is_exclusive(v___x_2315_);
if (v_isSharedCheck_2347_ == 0)
{
lean_object* v_unused_2348_; 
v_unused_2348_ = lean_ctor_get(v___x_2315_, 1);
lean_dec(v_unused_2348_);
v___x_2318_ = v___x_2315_;
v_isShared_2319_ = v_isSharedCheck_2347_;
goto v_resetjp_2317_;
}
else
{
lean_inc(v_toApplicative_2316_);
lean_dec(v___x_2315_);
v___x_2318_ = lean_box(0);
v_isShared_2319_ = v_isSharedCheck_2347_;
goto v_resetjp_2317_;
}
v_resetjp_2317_:
{
lean_object* v_toFunctor_2320_; lean_object* v_toSeq_2321_; lean_object* v_toSeqLeft_2322_; lean_object* v_toSeqRight_2323_; lean_object* v___x_2325_; uint8_t v_isShared_2326_; uint8_t v_isSharedCheck_2345_; 
v_toFunctor_2320_ = lean_ctor_get(v_toApplicative_2316_, 0);
v_toSeq_2321_ = lean_ctor_get(v_toApplicative_2316_, 2);
v_toSeqLeft_2322_ = lean_ctor_get(v_toApplicative_2316_, 3);
v_toSeqRight_2323_ = lean_ctor_get(v_toApplicative_2316_, 4);
v_isSharedCheck_2345_ = !lean_is_exclusive(v_toApplicative_2316_);
if (v_isSharedCheck_2345_ == 0)
{
lean_object* v_unused_2346_; 
v_unused_2346_ = lean_ctor_get(v_toApplicative_2316_, 1);
lean_dec(v_unused_2346_);
v___x_2325_ = v_toApplicative_2316_;
v_isShared_2326_ = v_isSharedCheck_2345_;
goto v_resetjp_2324_;
}
else
{
lean_inc(v_toSeqRight_2323_);
lean_inc(v_toSeqLeft_2322_);
lean_inc(v_toSeq_2321_);
lean_inc(v_toFunctor_2320_);
lean_dec(v_toApplicative_2316_);
v___x_2325_ = lean_box(0);
v_isShared_2326_ = v_isSharedCheck_2345_;
goto v_resetjp_2324_;
}
v_resetjp_2324_:
{
lean_object* v___f_2327_; lean_object* v___f_2328_; lean_object* v___f_2329_; lean_object* v___f_2330_; lean_object* v___x_2331_; lean_object* v___f_2332_; lean_object* v___f_2333_; lean_object* v___f_2334_; lean_object* v___x_2336_; 
v___f_2327_ = ((lean_object*)(l_panic___at___00Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__0_spec__0___closed__7));
v___f_2328_ = ((lean_object*)(l_panic___at___00Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__0_spec__0___closed__8));
lean_inc_ref(v_toFunctor_2320_);
v___f_2329_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2329_, 0, v_toFunctor_2320_);
v___f_2330_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2330_, 0, v_toFunctor_2320_);
v___x_2331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2331_, 0, v___f_2329_);
lean_ctor_set(v___x_2331_, 1, v___f_2330_);
v___f_2332_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2332_, 0, v_toSeqRight_2323_);
v___f_2333_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2333_, 0, v_toSeqLeft_2322_);
v___f_2334_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2334_, 0, v_toSeq_2321_);
if (v_isShared_2326_ == 0)
{
lean_ctor_set(v___x_2325_, 4, v___f_2332_);
lean_ctor_set(v___x_2325_, 3, v___f_2333_);
lean_ctor_set(v___x_2325_, 2, v___f_2334_);
lean_ctor_set(v___x_2325_, 1, v___f_2327_);
lean_ctor_set(v___x_2325_, 0, v___x_2331_);
v___x_2336_ = v___x_2325_;
goto v_reusejp_2335_;
}
else
{
lean_object* v_reuseFailAlloc_2344_; 
v_reuseFailAlloc_2344_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2344_, 0, v___x_2331_);
lean_ctor_set(v_reuseFailAlloc_2344_, 1, v___f_2327_);
lean_ctor_set(v_reuseFailAlloc_2344_, 2, v___f_2334_);
lean_ctor_set(v_reuseFailAlloc_2344_, 3, v___f_2333_);
lean_ctor_set(v_reuseFailAlloc_2344_, 4, v___f_2332_);
v___x_2336_ = v_reuseFailAlloc_2344_;
goto v_reusejp_2335_;
}
v_reusejp_2335_:
{
lean_object* v___x_2338_; 
if (v_isShared_2319_ == 0)
{
lean_ctor_set(v___x_2318_, 1, v___f_2328_);
lean_ctor_set(v___x_2318_, 0, v___x_2336_);
v___x_2338_ = v___x_2318_;
goto v_reusejp_2337_;
}
else
{
lean_object* v_reuseFailAlloc_2343_; 
v_reuseFailAlloc_2343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2343_, 0, v___x_2336_);
lean_ctor_set(v_reuseFailAlloc_2343_, 1, v___f_2328_);
v___x_2338_ = v_reuseFailAlloc_2343_;
goto v_reusejp_2337_;
}
v_reusejp_2337_:
{
lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_3363__overap_2341_; lean_object* v___x_2342_; 
v___x_2339_ = lean_box(0);
v___x_2340_ = l_instInhabitedOfMonad___redArg(v___x_2338_, v___x_2339_);
v___x_3363__overap_2341_ = lean_panic_fn_borrowed(v___x_2340_, v_msg_2232_);
lean_dec(v___x_2340_);
lean_inc(v___y_2240_);
lean_inc_ref(v___y_2239_);
lean_inc(v___y_2238_);
lean_inc_ref(v___y_2237_);
lean_inc(v___y_2236_);
lean_inc_ref(v___y_2235_);
lean_inc(v___y_2234_);
lean_inc_ref(v___y_2233_);
v___x_2342_ = lean_apply_9(v___x_3363__overap_2341_, v___y_2233_, v___y_2234_, v___y_2235_, v___y_2236_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_, lean_box(0));
return v___x_2342_;
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__0_spec__0___boxed(lean_object* v_msg_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_){
_start:
{
lean_object* v_res_2377_; 
v_res_2377_ = l_panic___at___00Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__0_spec__0(v_msg_2367_, v___y_2368_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_, v___y_2373_, v___y_2374_, v___y_2375_);
lean_dec(v___y_2375_);
lean_dec_ref(v___y_2374_);
lean_dec(v___y_2373_);
lean_dec_ref(v___y_2372_);
lean_dec(v___y_2371_);
lean_dec_ref(v___y_2370_);
lean_dec(v___y_2369_);
lean_dec_ref(v___y_2368_);
return v_res_2377_;
}
}
static lean_object* _init_l_Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; 
v___x_2381_ = ((lean_object*)(l_Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__0___closed__2));
v___x_2382_ = lean_unsigned_to_nat(11u);
v___x_2383_ = lean_unsigned_to_nat(115u);
v___x_2384_ = ((lean_object*)(l_Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__0___closed__1));
v___x_2385_ = ((lean_object*)(l_Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__0___closed__0));
v___x_2386_ = l_mkPanicMessageWithDecl(v___x_2385_, v___x_2384_, v___x_2383_, v___x_2382_, v___x_2381_);
return v___x_2386_;
}
}
LEAN_EXPORT lean_object* l_Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__0(lean_object* v_constName_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_){
_start:
{
lean_object* v___x_2397_; lean_object* v_env_2401_; uint8_t v___x_2402_; lean_object* v___x_2403_; 
v___x_2397_ = lean_st_ref_get(v___y_2395_);
v_env_2401_ = lean_ctor_get(v___x_2397_, 0);
lean_inc_ref(v_env_2401_);
lean_dec(v___x_2397_);
v___x_2402_ = 0;
v___x_2403_ = l_Lean_Environment_findAsync_x3f(v_env_2401_, v_constName_2387_, v___x_2402_);
if (lean_obj_tag(v___x_2403_) == 1)
{
lean_object* v_val_2404_; lean_object* v___x_2406_; uint8_t v_isShared_2407_; uint8_t v_isSharedCheck_2423_; 
v_val_2404_ = lean_ctor_get(v___x_2403_, 0);
v_isSharedCheck_2423_ = !lean_is_exclusive(v___x_2403_);
if (v_isSharedCheck_2423_ == 0)
{
v___x_2406_ = v___x_2403_;
v_isShared_2407_ = v_isSharedCheck_2423_;
goto v_resetjp_2405_;
}
else
{
lean_inc(v_val_2404_);
lean_dec(v___x_2403_);
v___x_2406_ = lean_box(0);
v_isShared_2407_ = v_isSharedCheck_2423_;
goto v_resetjp_2405_;
}
v_resetjp_2405_:
{
uint8_t v_kind_2408_; 
v_kind_2408_ = lean_ctor_get_uint8(v_val_2404_, sizeof(void*)*3);
if (v_kind_2408_ == 0)
{
lean_object* v___x_2409_; 
v___x_2409_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_2404_);
if (lean_obj_tag(v___x_2409_) == 1)
{
lean_object* v_val_2410_; lean_object* v___x_2412_; uint8_t v_isShared_2413_; uint8_t v_isSharedCheck_2420_; 
v_val_2410_ = lean_ctor_get(v___x_2409_, 0);
v_isSharedCheck_2420_ = !lean_is_exclusive(v___x_2409_);
if (v_isSharedCheck_2420_ == 0)
{
v___x_2412_ = v___x_2409_;
v_isShared_2413_ = v_isSharedCheck_2420_;
goto v_resetjp_2411_;
}
else
{
lean_inc(v_val_2410_);
lean_dec(v___x_2409_);
v___x_2412_ = lean_box(0);
v_isShared_2413_ = v_isSharedCheck_2420_;
goto v_resetjp_2411_;
}
v_resetjp_2411_:
{
lean_object* v___x_2415_; 
if (v_isShared_2407_ == 0)
{
lean_ctor_set(v___x_2406_, 0, v_val_2410_);
v___x_2415_ = v___x_2406_;
goto v_reusejp_2414_;
}
else
{
lean_object* v_reuseFailAlloc_2419_; 
v_reuseFailAlloc_2419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2419_, 0, v_val_2410_);
v___x_2415_ = v_reuseFailAlloc_2419_;
goto v_reusejp_2414_;
}
v_reusejp_2414_:
{
lean_object* v___x_2417_; 
if (v_isShared_2413_ == 0)
{
lean_ctor_set_tag(v___x_2412_, 0);
lean_ctor_set(v___x_2412_, 0, v___x_2415_);
v___x_2417_ = v___x_2412_;
goto v_reusejp_2416_;
}
else
{
lean_object* v_reuseFailAlloc_2418_; 
v_reuseFailAlloc_2418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2418_, 0, v___x_2415_);
v___x_2417_ = v_reuseFailAlloc_2418_;
goto v_reusejp_2416_;
}
v_reusejp_2416_:
{
return v___x_2417_;
}
}
}
}
else
{
lean_object* v___x_2421_; lean_object* v___x_2422_; 
lean_dec_ref(v___x_2409_);
lean_del_object(v___x_2406_);
v___x_2421_ = lean_obj_once(&l_Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__0___closed__3, &l_Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__0___closed__3_once, _init_l_Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__0___closed__3);
v___x_2422_ = l_panic___at___00Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__0_spec__0(v___x_2421_, v___y_2388_, v___y_2389_, v___y_2390_, v___y_2391_, v___y_2392_, v___y_2393_, v___y_2394_, v___y_2395_);
return v___x_2422_;
}
}
else
{
lean_del_object(v___x_2406_);
lean_dec(v_val_2404_);
goto v___jp_2398_;
}
}
}
else
{
lean_dec(v___x_2403_);
goto v___jp_2398_;
}
v___jp_2398_:
{
lean_object* v___x_2399_; lean_object* v___x_2400_; 
v___x_2399_ = lean_box(0);
v___x_2400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2400_, 0, v___x_2399_);
return v___x_2400_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__0___boxed(lean_object* v_constName_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_){
_start:
{
lean_object* v_res_2434_; 
v_res_2434_ = l_Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__0(v_constName_2424_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_);
lean_dec(v___y_2432_);
lean_dec_ref(v___y_2431_);
lean_dec(v___y_2430_);
lean_dec_ref(v___y_2429_);
lean_dec(v___y_2428_);
lean_dec_ref(v___y_2427_);
lean_dec(v___y_2426_);
lean_dec_ref(v___y_2425_);
return v_res_2434_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__1(lean_object* v___x_2435_, lean_object* v_as_2436_, size_t v_sz_2437_, size_t v_i_2438_, lean_object* v_b_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_){
_start:
{
lean_object* v_a_2450_; uint8_t v___x_2454_; 
v___x_2454_ = lean_usize_dec_lt(v_i_2438_, v_sz_2437_);
if (v___x_2454_ == 0)
{
lean_object* v___x_2455_; 
v___x_2455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2455_, 0, v_b_2439_);
return v___x_2455_;
}
else
{
lean_object* v_fst_2456_; lean_object* v_snd_2457_; lean_object* v___x_2459_; uint8_t v_isShared_2460_; uint8_t v_isSharedCheck_2540_; 
v_fst_2456_ = lean_ctor_get(v_b_2439_, 0);
v_snd_2457_ = lean_ctor_get(v_b_2439_, 1);
v_isSharedCheck_2540_ = !lean_is_exclusive(v_b_2439_);
if (v_isSharedCheck_2540_ == 0)
{
v___x_2459_ = v_b_2439_;
v_isShared_2460_ = v_isSharedCheck_2540_;
goto v_resetjp_2458_;
}
else
{
lean_inc(v_snd_2457_);
lean_inc(v_fst_2456_);
lean_dec(v_b_2439_);
v___x_2459_ = lean_box(0);
v_isShared_2460_ = v_isSharedCheck_2540_;
goto v_resetjp_2458_;
}
v_resetjp_2458_:
{
lean_object* v_a_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; 
v_a_2461_ = lean_array_uget_borrowed(v_as_2436_, v_i_2438_);
v___x_2462_ = l_Lean_TSyntax_getId(v_a_2461_);
v___x_2463_ = l_Lean_LocalContext_findFromUserName_x3f(v___x_2435_, v___x_2462_);
lean_dec(v___x_2462_);
if (lean_obj_tag(v___x_2463_) == 1)
{
lean_object* v_val_2464_; lean_object* v___x_2466_; uint8_t v_isShared_2467_; uint8_t v_isSharedCheck_2488_; 
v_val_2464_ = lean_ctor_get(v___x_2463_, 0);
v_isSharedCheck_2488_ = !lean_is_exclusive(v___x_2463_);
if (v_isSharedCheck_2488_ == 0)
{
v___x_2466_ = v___x_2463_;
v_isShared_2467_ = v_isSharedCheck_2488_;
goto v_resetjp_2465_;
}
else
{
lean_inc(v_val_2464_);
lean_dec(v___x_2463_);
v___x_2466_ = lean_box(0);
v_isShared_2467_ = v_isSharedCheck_2488_;
goto v_resetjp_2465_;
}
v_resetjp_2465_:
{
lean_object* v___x_2468_; lean_object* v___x_2470_; 
v___x_2468_ = l_Lean_LocalDecl_fvarId(v_val_2464_);
if (v_isShared_2467_ == 0)
{
lean_ctor_set(v___x_2466_, 0, v___x_2468_);
v___x_2470_ = v___x_2466_;
goto v_reusejp_2469_;
}
else
{
lean_object* v_reuseFailAlloc_2487_; 
v_reuseFailAlloc_2487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2487_, 0, v___x_2468_);
v___x_2470_ = v_reuseFailAlloc_2487_;
goto v_reusejp_2469_;
}
v_reusejp_2469_:
{
lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; 
v___x_2471_ = lean_array_push(v_fst_2456_, v___x_2470_);
v___x_2472_ = l_Lean_LocalDecl_toExpr(v_val_2464_);
v___x_2473_ = l_Lean_Meta_Sym_Simp_mkTheoremFromExpr(v___x_2472_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_);
if (lean_obj_tag(v___x_2473_) == 0)
{
lean_object* v_a_2474_; lean_object* v___x_2475_; lean_object* v___x_2477_; 
v_a_2474_ = lean_ctor_get(v___x_2473_, 0);
lean_inc(v_a_2474_);
lean_dec_ref_known(v___x_2473_, 1);
v___x_2475_ = lean_array_push(v_snd_2457_, v_a_2474_);
if (v_isShared_2460_ == 0)
{
lean_ctor_set(v___x_2459_, 1, v___x_2475_);
lean_ctor_set(v___x_2459_, 0, v___x_2471_);
v___x_2477_ = v___x_2459_;
goto v_reusejp_2476_;
}
else
{
lean_object* v_reuseFailAlloc_2478_; 
v_reuseFailAlloc_2478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2478_, 0, v___x_2471_);
lean_ctor_set(v_reuseFailAlloc_2478_, 1, v___x_2475_);
v___x_2477_ = v_reuseFailAlloc_2478_;
goto v_reusejp_2476_;
}
v_reusejp_2476_:
{
v_a_2450_ = v___x_2477_;
goto v___jp_2449_;
}
}
else
{
lean_object* v_a_2479_; lean_object* v___x_2481_; uint8_t v_isShared_2482_; uint8_t v_isSharedCheck_2486_; 
lean_dec_ref(v___x_2471_);
lean_del_object(v___x_2459_);
lean_dec(v_snd_2457_);
v_a_2479_ = lean_ctor_get(v___x_2473_, 0);
v_isSharedCheck_2486_ = !lean_is_exclusive(v___x_2473_);
if (v_isSharedCheck_2486_ == 0)
{
v___x_2481_ = v___x_2473_;
v_isShared_2482_ = v_isSharedCheck_2486_;
goto v_resetjp_2480_;
}
else
{
lean_inc(v_a_2479_);
lean_dec(v___x_2473_);
v___x_2481_ = lean_box(0);
v_isShared_2482_ = v_isSharedCheck_2486_;
goto v_resetjp_2480_;
}
v_resetjp_2480_:
{
lean_object* v___x_2484_; 
if (v_isShared_2482_ == 0)
{
v___x_2484_ = v___x_2481_;
goto v_reusejp_2483_;
}
else
{
lean_object* v_reuseFailAlloc_2485_; 
v_reuseFailAlloc_2485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2485_, 0, v_a_2479_);
v___x_2484_ = v_reuseFailAlloc_2485_;
goto v_reusejp_2483_;
}
v_reusejp_2483_:
{
return v___x_2484_;
}
}
}
}
}
}
else
{
lean_object* v___x_2489_; 
lean_dec(v___x_2463_);
lean_inc(v_a_2461_);
v___x_2489_ = l_Lean_realizeGlobalConstNoOverload(v_a_2461_, v___y_2446_, v___y_2447_);
if (lean_obj_tag(v___x_2489_) == 0)
{
lean_object* v_a_2490_; lean_object* v___y_2492_; lean_object* v___y_2493_; lean_object* v___y_2494_; lean_object* v___y_2495_; lean_object* v___x_2512_; 
v_a_2490_ = lean_ctor_get(v___x_2489_, 0);
lean_inc_n(v_a_2490_, 2);
lean_dec_ref_known(v___x_2489_, 1);
v___x_2512_ = l_Lean_isDefn_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__0(v_a_2490_, v___y_2440_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_);
if (lean_obj_tag(v___x_2512_) == 0)
{
lean_object* v_a_2513_; 
v_a_2513_ = lean_ctor_get(v___x_2512_, 0);
lean_inc(v_a_2513_);
lean_dec_ref_known(v___x_2512_, 1);
if (lean_obj_tag(v_a_2513_) == 0)
{
lean_object* v___x_2514_; lean_object* v___x_2515_; 
v___x_2514_ = lean_box(1);
lean_inc(v_a_2490_);
v___x_2515_ = l_Lean_Linter_checkDeprecatedAt(v_a_2461_, v_a_2490_, v___x_2514_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_);
if (lean_obj_tag(v___x_2515_) == 0)
{
lean_dec_ref_known(v___x_2515_, 1);
v___y_2492_ = v___y_2444_;
v___y_2493_ = v___y_2445_;
v___y_2494_ = v___y_2446_;
v___y_2495_ = v___y_2447_;
goto v___jp_2491_;
}
else
{
lean_object* v_a_2516_; lean_object* v___x_2518_; uint8_t v_isShared_2519_; uint8_t v_isSharedCheck_2523_; 
lean_dec(v_a_2490_);
lean_del_object(v___x_2459_);
lean_dec(v_snd_2457_);
lean_dec(v_fst_2456_);
v_a_2516_ = lean_ctor_get(v___x_2515_, 0);
v_isSharedCheck_2523_ = !lean_is_exclusive(v___x_2515_);
if (v_isSharedCheck_2523_ == 0)
{
v___x_2518_ = v___x_2515_;
v_isShared_2519_ = v_isSharedCheck_2523_;
goto v_resetjp_2517_;
}
else
{
lean_inc(v_a_2516_);
lean_dec(v___x_2515_);
v___x_2518_ = lean_box(0);
v_isShared_2519_ = v_isSharedCheck_2523_;
goto v_resetjp_2517_;
}
v_resetjp_2517_:
{
lean_object* v___x_2521_; 
if (v_isShared_2519_ == 0)
{
v___x_2521_ = v___x_2518_;
goto v_reusejp_2520_;
}
else
{
lean_object* v_reuseFailAlloc_2522_; 
v_reuseFailAlloc_2522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2522_, 0, v_a_2516_);
v___x_2521_ = v_reuseFailAlloc_2522_;
goto v_reusejp_2520_;
}
v_reusejp_2520_:
{
return v___x_2521_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_2513_, 1);
v___y_2492_ = v___y_2444_;
v___y_2493_ = v___y_2445_;
v___y_2494_ = v___y_2446_;
v___y_2495_ = v___y_2447_;
goto v___jp_2491_;
}
}
else
{
lean_object* v_a_2524_; lean_object* v___x_2526_; uint8_t v_isShared_2527_; uint8_t v_isSharedCheck_2531_; 
lean_dec(v_a_2490_);
lean_del_object(v___x_2459_);
lean_dec(v_snd_2457_);
lean_dec(v_fst_2456_);
v_a_2524_ = lean_ctor_get(v___x_2512_, 0);
v_isSharedCheck_2531_ = !lean_is_exclusive(v___x_2512_);
if (v_isSharedCheck_2531_ == 0)
{
v___x_2526_ = v___x_2512_;
v_isShared_2527_ = v_isSharedCheck_2531_;
goto v_resetjp_2525_;
}
else
{
lean_inc(v_a_2524_);
lean_dec(v___x_2512_);
v___x_2526_ = lean_box(0);
v_isShared_2527_ = v_isSharedCheck_2531_;
goto v_resetjp_2525_;
}
v_resetjp_2525_:
{
lean_object* v___x_2529_; 
if (v_isShared_2527_ == 0)
{
v___x_2529_ = v___x_2526_;
goto v_reusejp_2528_;
}
else
{
lean_object* v_reuseFailAlloc_2530_; 
v_reuseFailAlloc_2530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2530_, 0, v_a_2524_);
v___x_2529_ = v_reuseFailAlloc_2530_;
goto v_reusejp_2528_;
}
v_reusejp_2528_:
{
return v___x_2529_;
}
}
}
v___jp_2491_:
{
lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; 
lean_inc(v_a_2490_);
v___x_2496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2496_, 0, v_a_2490_);
v___x_2497_ = lean_array_push(v_fst_2456_, v___x_2496_);
v___x_2498_ = l_Lean_Meta_Sym_Simp_mkTheoremsFromDecl(v_a_2490_, v___y_2492_, v___y_2493_, v___y_2494_, v___y_2495_);
if (lean_obj_tag(v___x_2498_) == 0)
{
lean_object* v_a_2499_; lean_object* v___x_2500_; lean_object* v___x_2502_; 
v_a_2499_ = lean_ctor_get(v___x_2498_, 0);
lean_inc(v_a_2499_);
lean_dec_ref_known(v___x_2498_, 1);
v___x_2500_ = l_Array_append___redArg(v_snd_2457_, v_a_2499_);
lean_dec(v_a_2499_);
if (v_isShared_2460_ == 0)
{
lean_ctor_set(v___x_2459_, 1, v___x_2500_);
lean_ctor_set(v___x_2459_, 0, v___x_2497_);
v___x_2502_ = v___x_2459_;
goto v_reusejp_2501_;
}
else
{
lean_object* v_reuseFailAlloc_2503_; 
v_reuseFailAlloc_2503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2503_, 0, v___x_2497_);
lean_ctor_set(v_reuseFailAlloc_2503_, 1, v___x_2500_);
v___x_2502_ = v_reuseFailAlloc_2503_;
goto v_reusejp_2501_;
}
v_reusejp_2501_:
{
v_a_2450_ = v___x_2502_;
goto v___jp_2449_;
}
}
else
{
lean_object* v_a_2504_; lean_object* v___x_2506_; uint8_t v_isShared_2507_; uint8_t v_isSharedCheck_2511_; 
lean_dec_ref(v___x_2497_);
lean_del_object(v___x_2459_);
lean_dec(v_snd_2457_);
v_a_2504_ = lean_ctor_get(v___x_2498_, 0);
v_isSharedCheck_2511_ = !lean_is_exclusive(v___x_2498_);
if (v_isSharedCheck_2511_ == 0)
{
v___x_2506_ = v___x_2498_;
v_isShared_2507_ = v_isSharedCheck_2511_;
goto v_resetjp_2505_;
}
else
{
lean_inc(v_a_2504_);
lean_dec(v___x_2498_);
v___x_2506_ = lean_box(0);
v_isShared_2507_ = v_isSharedCheck_2511_;
goto v_resetjp_2505_;
}
v_resetjp_2505_:
{
lean_object* v___x_2509_; 
if (v_isShared_2507_ == 0)
{
v___x_2509_ = v___x_2506_;
goto v_reusejp_2508_;
}
else
{
lean_object* v_reuseFailAlloc_2510_; 
v_reuseFailAlloc_2510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2510_, 0, v_a_2504_);
v___x_2509_ = v_reuseFailAlloc_2510_;
goto v_reusejp_2508_;
}
v_reusejp_2508_:
{
return v___x_2509_;
}
}
}
}
}
else
{
lean_object* v_a_2532_; lean_object* v___x_2534_; uint8_t v_isShared_2535_; uint8_t v_isSharedCheck_2539_; 
lean_del_object(v___x_2459_);
lean_dec(v_snd_2457_);
lean_dec(v_fst_2456_);
v_a_2532_ = lean_ctor_get(v___x_2489_, 0);
v_isSharedCheck_2539_ = !lean_is_exclusive(v___x_2489_);
if (v_isSharedCheck_2539_ == 0)
{
v___x_2534_ = v___x_2489_;
v_isShared_2535_ = v_isSharedCheck_2539_;
goto v_resetjp_2533_;
}
else
{
lean_inc(v_a_2532_);
lean_dec(v___x_2489_);
v___x_2534_ = lean_box(0);
v_isShared_2535_ = v_isSharedCheck_2539_;
goto v_resetjp_2533_;
}
v_resetjp_2533_:
{
lean_object* v___x_2537_; 
if (v_isShared_2535_ == 0)
{
v___x_2537_ = v___x_2534_;
goto v_reusejp_2536_;
}
else
{
lean_object* v_reuseFailAlloc_2538_; 
v_reuseFailAlloc_2538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2538_, 0, v_a_2532_);
v___x_2537_ = v_reuseFailAlloc_2538_;
goto v_reusejp_2536_;
}
v_reusejp_2536_:
{
return v___x_2537_;
}
}
}
}
}
}
v___jp_2449_:
{
size_t v___x_2451_; size_t v___x_2452_; 
v___x_2451_ = ((size_t)1ULL);
v___x_2452_ = lean_usize_add(v_i_2438_, v___x_2451_);
v_i_2438_ = v___x_2452_;
v_b_2439_ = v_a_2450_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__1___boxed(lean_object* v___x_2541_, lean_object* v_as_2542_, lean_object* v_sz_2543_, lean_object* v_i_2544_, lean_object* v_b_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_){
_start:
{
size_t v_sz_boxed_2555_; size_t v_i_boxed_2556_; lean_object* v_res_2557_; 
v_sz_boxed_2555_ = lean_unbox_usize(v_sz_2543_);
lean_dec(v_sz_2543_);
v_i_boxed_2556_ = lean_unbox_usize(v_i_2544_);
lean_dec(v_i_2544_);
v_res_2557_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__1(v___x_2541_, v_as_2542_, v_sz_boxed_2555_, v_i_boxed_2556_, v_b_2545_, v___y_2546_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_, v___y_2553_);
lean_dec(v___y_2553_);
lean_dec_ref(v___y_2552_);
lean_dec(v___y_2551_);
lean_dec_ref(v___y_2550_);
lean_dec(v___y_2549_);
lean_dec_ref(v___y_2548_);
lean_dec(v___y_2547_);
lean_dec_ref(v___y_2546_);
lean_dec_ref(v_as_2542_);
lean_dec_ref(v___x_2541_);
return v_res_2557_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems(lean_object* v_ids_x3f_2562_, lean_object* v_a_2563_, lean_object* v_a_2564_, lean_object* v_a_2565_, lean_object* v_a_2566_, lean_object* v_a_2567_, lean_object* v_a_2568_, lean_object* v_a_2569_, lean_object* v_a_2570_){
_start:
{
if (lean_obj_tag(v_ids_x3f_2562_) == 1)
{
lean_object* v_val_2572_; lean_object* v_lctx_2573_; lean_object* v___x_2574_; size_t v_sz_2575_; size_t v___x_2576_; lean_object* v___x_2577_; 
v_val_2572_ = lean_ctor_get(v_ids_x3f_2562_, 0);
v_lctx_2573_ = lean_ctor_get(v_a_2567_, 2);
v___x_2574_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems___closed__1));
v_sz_2575_ = lean_array_size(v_val_2572_);
v___x_2576_ = ((size_t)0ULL);
v___x_2577_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__1(v_lctx_2573_, v_val_2572_, v_sz_2575_, v___x_2576_, v___x_2574_, v_a_2563_, v_a_2564_, v_a_2565_, v_a_2566_, v_a_2567_, v_a_2568_, v_a_2569_, v_a_2570_);
if (lean_obj_tag(v___x_2577_) == 0)
{
lean_object* v_a_2578_; lean_object* v___x_2580_; uint8_t v_isShared_2581_; uint8_t v_isSharedCheck_2594_; 
v_a_2578_ = lean_ctor_get(v___x_2577_, 0);
v_isSharedCheck_2594_ = !lean_is_exclusive(v___x_2577_);
if (v_isSharedCheck_2594_ == 0)
{
v___x_2580_ = v___x_2577_;
v_isShared_2581_ = v_isSharedCheck_2594_;
goto v_resetjp_2579_;
}
else
{
lean_inc(v_a_2578_);
lean_dec(v___x_2577_);
v___x_2580_ = lean_box(0);
v_isShared_2581_ = v_isSharedCheck_2594_;
goto v_resetjp_2579_;
}
v_resetjp_2579_:
{
lean_object* v_fst_2582_; lean_object* v_snd_2583_; lean_object* v___x_2585_; uint8_t v_isShared_2586_; uint8_t v_isSharedCheck_2593_; 
v_fst_2582_ = lean_ctor_get(v_a_2578_, 0);
v_snd_2583_ = lean_ctor_get(v_a_2578_, 1);
v_isSharedCheck_2593_ = !lean_is_exclusive(v_a_2578_);
if (v_isSharedCheck_2593_ == 0)
{
v___x_2585_ = v_a_2578_;
v_isShared_2586_ = v_isSharedCheck_2593_;
goto v_resetjp_2584_;
}
else
{
lean_inc(v_snd_2583_);
lean_inc(v_fst_2582_);
lean_dec(v_a_2578_);
v___x_2585_ = lean_box(0);
v_isShared_2586_ = v_isSharedCheck_2593_;
goto v_resetjp_2584_;
}
v_resetjp_2584_:
{
lean_object* v___x_2588_; 
if (v_isShared_2586_ == 0)
{
v___x_2588_ = v___x_2585_;
goto v_reusejp_2587_;
}
else
{
lean_object* v_reuseFailAlloc_2592_; 
v_reuseFailAlloc_2592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2592_, 0, v_fst_2582_);
lean_ctor_set(v_reuseFailAlloc_2592_, 1, v_snd_2583_);
v___x_2588_ = v_reuseFailAlloc_2592_;
goto v_reusejp_2587_;
}
v_reusejp_2587_:
{
lean_object* v___x_2590_; 
if (v_isShared_2581_ == 0)
{
lean_ctor_set(v___x_2580_, 0, v___x_2588_);
v___x_2590_ = v___x_2580_;
goto v_reusejp_2589_;
}
else
{
lean_object* v_reuseFailAlloc_2591_; 
v_reuseFailAlloc_2591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2591_, 0, v___x_2588_);
v___x_2590_ = v_reuseFailAlloc_2591_;
goto v_reusejp_2589_;
}
v_reusejp_2589_:
{
return v___x_2590_;
}
}
}
}
}
else
{
return v___x_2577_;
}
}
else
{
lean_object* v___x_2595_; lean_object* v___x_2596_; 
v___x_2595_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems___closed__1));
v___x_2596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2596_, 0, v___x_2595_);
return v___x_2596_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems___boxed(lean_object* v_ids_x3f_2597_, lean_object* v_a_2598_, lean_object* v_a_2599_, lean_object* v_a_2600_, lean_object* v_a_2601_, lean_object* v_a_2602_, lean_object* v_a_2603_, lean_object* v_a_2604_, lean_object* v_a_2605_, lean_object* v_a_2606_){
_start:
{
lean_object* v_res_2607_; 
v_res_2607_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems(v_ids_x3f_2597_, v_a_2598_, v_a_2599_, v_a_2600_, v_a_2601_, v_a_2602_, v_a_2603_, v_a_2604_, v_a_2605_);
lean_dec(v_a_2605_);
lean_dec_ref(v_a_2604_);
lean_dec(v_a_2603_);
lean_dec_ref(v_a_2602_);
lean_dec(v_a_2601_);
lean_dec_ref(v_a_2600_);
lean_dec(v_a_2599_);
lean_dec_ref(v_a_2598_);
lean_dec(v_ids_x3f_2597_);
return v_res_2607_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___lam__0(lean_object* v_post_2608_, lean_object* v_a_2609_, lean_object* v_d_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_){
_start:
{
lean_object* v___x_2622_; 
lean_inc(v___y_2620_);
lean_inc_ref(v___y_2619_);
lean_inc(v___y_2618_);
lean_inc_ref(v___y_2617_);
lean_inc(v___y_2616_);
lean_inc_ref(v___y_2615_);
lean_inc(v___y_2614_);
lean_inc_ref(v___y_2613_);
lean_inc(v___y_2612_);
lean_inc_ref(v___y_2611_);
v___x_2622_ = lean_apply_11(v_post_2608_, v___y_2611_, v___y_2612_, v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_, v___y_2617_, v___y_2618_, v___y_2619_, v___y_2620_, lean_box(0));
if (lean_obj_tag(v___x_2622_) == 0)
{
lean_object* v_a_2623_; 
v_a_2623_ = lean_ctor_get(v___x_2622_, 0);
lean_inc(v_a_2623_);
if (lean_obj_tag(v_a_2623_) == 0)
{
uint8_t v_done_2624_; 
v_done_2624_ = lean_ctor_get_uint8(v_a_2623_, 0);
if (v_done_2624_ == 0)
{
uint8_t v_contextDependent_2625_; lean_object* v___x_2626_; 
lean_dec_ref_known(v___x_2622_, 1);
v_contextDependent_2625_ = lean_ctor_get_uint8(v_a_2623_, 1);
lean_dec_ref_known(v_a_2623_, 0);
v___x_2626_ = l_Lean_Meta_Sym_Simp_Theorems_rewrite(v_a_2609_, v_d_2610_, v___y_2611_, v___y_2612_, v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_, v___y_2617_, v___y_2618_, v___y_2619_, v___y_2620_);
lean_dec(v___y_2620_);
lean_dec_ref(v___y_2619_);
lean_dec(v___y_2618_);
lean_dec_ref(v___y_2617_);
lean_dec(v___y_2616_);
lean_dec_ref(v___y_2615_);
lean_dec(v___y_2614_);
lean_dec_ref(v___y_2613_);
lean_dec(v___y_2612_);
if (lean_obj_tag(v___x_2626_) == 0)
{
lean_object* v_a_2627_; uint8_t v___y_2629_; 
v_a_2627_ = lean_ctor_get(v___x_2626_, 0);
if (v_contextDependent_2625_ == 0)
{
return v___x_2626_;
}
else
{
if (lean_obj_tag(v_a_2627_) == 0)
{
uint8_t v_contextDependent_2639_; 
v_contextDependent_2639_ = lean_ctor_get_uint8(v_a_2627_, 1);
v___y_2629_ = v_contextDependent_2639_;
goto v___jp_2628_;
}
else
{
uint8_t v_contextDependent_2640_; 
v_contextDependent_2640_ = lean_ctor_get_uint8(v_a_2627_, sizeof(void*)*2 + 1);
v___y_2629_ = v_contextDependent_2640_;
goto v___jp_2628_;
}
}
v___jp_2628_:
{
if (v___y_2629_ == 0)
{
lean_object* v___x_2631_; uint8_t v_isShared_2632_; uint8_t v_isSharedCheck_2637_; 
lean_inc(v_a_2627_);
v_isSharedCheck_2637_ = !lean_is_exclusive(v___x_2626_);
if (v_isSharedCheck_2637_ == 0)
{
lean_object* v_unused_2638_; 
v_unused_2638_ = lean_ctor_get(v___x_2626_, 0);
lean_dec(v_unused_2638_);
v___x_2631_ = v___x_2626_;
v_isShared_2632_ = v_isSharedCheck_2637_;
goto v_resetjp_2630_;
}
else
{
lean_dec(v___x_2626_);
v___x_2631_ = lean_box(0);
v_isShared_2632_ = v_isSharedCheck_2637_;
goto v_resetjp_2630_;
}
v_resetjp_2630_:
{
lean_object* v___x_2633_; lean_object* v___x_2635_; 
v___x_2633_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_2627_);
if (v_isShared_2632_ == 0)
{
lean_ctor_set(v___x_2631_, 0, v___x_2633_);
v___x_2635_ = v___x_2631_;
goto v_reusejp_2634_;
}
else
{
lean_object* v_reuseFailAlloc_2636_; 
v_reuseFailAlloc_2636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2636_, 0, v___x_2633_);
v___x_2635_ = v_reuseFailAlloc_2636_;
goto v_reusejp_2634_;
}
v_reusejp_2634_:
{
return v___x_2635_;
}
}
}
else
{
return v___x_2626_;
}
}
}
else
{
return v___x_2626_;
}
}
else
{
lean_dec_ref_known(v_a_2623_, 0);
lean_dec(v___y_2620_);
lean_dec_ref(v___y_2619_);
lean_dec(v___y_2618_);
lean_dec_ref(v___y_2617_);
lean_dec(v___y_2616_);
lean_dec_ref(v___y_2615_);
lean_dec(v___y_2614_);
lean_dec_ref(v___y_2613_);
lean_dec(v___y_2612_);
lean_dec_ref(v___y_2611_);
lean_dec_ref(v_d_2610_);
return v___x_2622_;
}
}
else
{
uint8_t v_done_2641_; 
v_done_2641_ = lean_ctor_get_uint8(v_a_2623_, sizeof(void*)*2);
if (v_done_2641_ == 0)
{
lean_object* v_e_x27_2642_; lean_object* v_proof_2643_; uint8_t v_contextDependent_2644_; lean_object* v___x_2646_; uint8_t v_isShared_2647_; uint8_t v_isSharedCheck_2694_; 
lean_dec_ref_known(v___x_2622_, 1);
v_e_x27_2642_ = lean_ctor_get(v_a_2623_, 0);
v_proof_2643_ = lean_ctor_get(v_a_2623_, 1);
v_contextDependent_2644_ = lean_ctor_get_uint8(v_a_2623_, sizeof(void*)*2 + 1);
v_isSharedCheck_2694_ = !lean_is_exclusive(v_a_2623_);
if (v_isSharedCheck_2694_ == 0)
{
v___x_2646_ = v_a_2623_;
v_isShared_2647_ = v_isSharedCheck_2694_;
goto v_resetjp_2645_;
}
else
{
lean_inc(v_proof_2643_);
lean_inc(v_e_x27_2642_);
lean_dec(v_a_2623_);
v___x_2646_ = lean_box(0);
v_isShared_2647_ = v_isSharedCheck_2694_;
goto v_resetjp_2645_;
}
v_resetjp_2645_:
{
lean_object* v___x_2648_; 
lean_inc_ref(v_e_x27_2642_);
v___x_2648_ = l_Lean_Meta_Sym_Simp_Theorems_rewrite(v_a_2609_, v_d_2610_, v_e_x27_2642_, v___y_2612_, v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_, v___y_2617_, v___y_2618_, v___y_2619_, v___y_2620_);
lean_dec(v___y_2614_);
lean_dec_ref(v___y_2613_);
lean_dec(v___y_2612_);
if (lean_obj_tag(v___x_2648_) == 0)
{
lean_object* v_a_2649_; lean_object* v___x_2651_; uint8_t v_isShared_2652_; uint8_t v_isSharedCheck_2693_; 
v_a_2649_ = lean_ctor_get(v___x_2648_, 0);
v_isSharedCheck_2693_ = !lean_is_exclusive(v___x_2648_);
if (v_isSharedCheck_2693_ == 0)
{
v___x_2651_ = v___x_2648_;
v_isShared_2652_ = v_isSharedCheck_2693_;
goto v_resetjp_2650_;
}
else
{
lean_inc(v_a_2649_);
lean_dec(v___x_2648_);
v___x_2651_ = lean_box(0);
v_isShared_2652_ = v_isSharedCheck_2693_;
goto v_resetjp_2650_;
}
v_resetjp_2650_:
{
if (lean_obj_tag(v_a_2649_) == 0)
{
uint8_t v_done_2653_; uint8_t v_contextDependent_2654_; uint8_t v___y_2656_; 
lean_dec(v___y_2620_);
lean_dec_ref(v___y_2619_);
lean_dec(v___y_2618_);
lean_dec_ref(v___y_2617_);
lean_dec(v___y_2616_);
lean_dec_ref(v___y_2615_);
lean_dec_ref(v___y_2611_);
v_done_2653_ = lean_ctor_get_uint8(v_a_2649_, 0);
v_contextDependent_2654_ = lean_ctor_get_uint8(v_a_2649_, 1);
lean_dec_ref_known(v_a_2649_, 0);
if (v_contextDependent_2644_ == 0)
{
v___y_2656_ = v_contextDependent_2654_;
goto v___jp_2655_;
}
else
{
v___y_2656_ = v_contextDependent_2644_;
goto v___jp_2655_;
}
v___jp_2655_:
{
lean_object* v___x_2658_; 
if (v_isShared_2647_ == 0)
{
v___x_2658_ = v___x_2646_;
goto v_reusejp_2657_;
}
else
{
lean_object* v_reuseFailAlloc_2662_; 
v_reuseFailAlloc_2662_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2662_, 0, v_e_x27_2642_);
lean_ctor_set(v_reuseFailAlloc_2662_, 1, v_proof_2643_);
v___x_2658_ = v_reuseFailAlloc_2662_;
goto v_reusejp_2657_;
}
v_reusejp_2657_:
{
lean_object* v___x_2660_; 
lean_ctor_set_uint8(v___x_2658_, sizeof(void*)*2, v_done_2653_);
lean_ctor_set_uint8(v___x_2658_, sizeof(void*)*2 + 1, v___y_2656_);
if (v_isShared_2652_ == 0)
{
lean_ctor_set(v___x_2651_, 0, v___x_2658_);
v___x_2660_ = v___x_2651_;
goto v_reusejp_2659_;
}
else
{
lean_object* v_reuseFailAlloc_2661_; 
v_reuseFailAlloc_2661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2661_, 0, v___x_2658_);
v___x_2660_ = v_reuseFailAlloc_2661_;
goto v_reusejp_2659_;
}
v_reusejp_2659_:
{
return v___x_2660_;
}
}
}
}
else
{
lean_object* v_e_x27_2663_; lean_object* v_proof_2664_; uint8_t v_done_2665_; uint8_t v_contextDependent_2666_; lean_object* v___x_2668_; uint8_t v_isShared_2669_; uint8_t v_isSharedCheck_2692_; 
lean_del_object(v___x_2651_);
lean_del_object(v___x_2646_);
v_e_x27_2663_ = lean_ctor_get(v_a_2649_, 0);
v_proof_2664_ = lean_ctor_get(v_a_2649_, 1);
v_done_2665_ = lean_ctor_get_uint8(v_a_2649_, sizeof(void*)*2);
v_contextDependent_2666_ = lean_ctor_get_uint8(v_a_2649_, sizeof(void*)*2 + 1);
v_isSharedCheck_2692_ = !lean_is_exclusive(v_a_2649_);
if (v_isSharedCheck_2692_ == 0)
{
v___x_2668_ = v_a_2649_;
v_isShared_2669_ = v_isSharedCheck_2692_;
goto v_resetjp_2667_;
}
else
{
lean_inc(v_proof_2664_);
lean_inc(v_e_x27_2663_);
lean_dec(v_a_2649_);
v___x_2668_ = lean_box(0);
v_isShared_2669_ = v_isSharedCheck_2692_;
goto v_resetjp_2667_;
}
v_resetjp_2667_:
{
lean_object* v___x_2670_; 
lean_inc_ref(v_e_x27_2663_);
v___x_2670_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_2611_, v_e_x27_2642_, v_proof_2643_, v_e_x27_2663_, v_proof_2664_, v___y_2615_, v___y_2616_, v___y_2617_, v___y_2618_, v___y_2619_, v___y_2620_);
lean_dec(v___y_2620_);
lean_dec_ref(v___y_2619_);
lean_dec(v___y_2618_);
lean_dec_ref(v___y_2617_);
lean_dec(v___y_2616_);
lean_dec_ref(v___y_2615_);
if (lean_obj_tag(v___x_2670_) == 0)
{
lean_object* v_a_2671_; lean_object* v___x_2673_; uint8_t v_isShared_2674_; uint8_t v_isSharedCheck_2683_; 
v_a_2671_ = lean_ctor_get(v___x_2670_, 0);
v_isSharedCheck_2683_ = !lean_is_exclusive(v___x_2670_);
if (v_isSharedCheck_2683_ == 0)
{
v___x_2673_ = v___x_2670_;
v_isShared_2674_ = v_isSharedCheck_2683_;
goto v_resetjp_2672_;
}
else
{
lean_inc(v_a_2671_);
lean_dec(v___x_2670_);
v___x_2673_ = lean_box(0);
v_isShared_2674_ = v_isSharedCheck_2683_;
goto v_resetjp_2672_;
}
v_resetjp_2672_:
{
uint8_t v___y_2676_; 
if (v_contextDependent_2644_ == 0)
{
v___y_2676_ = v_contextDependent_2666_;
goto v___jp_2675_;
}
else
{
v___y_2676_ = v_contextDependent_2644_;
goto v___jp_2675_;
}
v___jp_2675_:
{
lean_object* v___x_2678_; 
if (v_isShared_2669_ == 0)
{
lean_ctor_set(v___x_2668_, 1, v_a_2671_);
v___x_2678_ = v___x_2668_;
goto v_reusejp_2677_;
}
else
{
lean_object* v_reuseFailAlloc_2682_; 
v_reuseFailAlloc_2682_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2682_, 0, v_e_x27_2663_);
lean_ctor_set(v_reuseFailAlloc_2682_, 1, v_a_2671_);
lean_ctor_set_uint8(v_reuseFailAlloc_2682_, sizeof(void*)*2, v_done_2665_);
v___x_2678_ = v_reuseFailAlloc_2682_;
goto v_reusejp_2677_;
}
v_reusejp_2677_:
{
lean_object* v___x_2680_; 
lean_ctor_set_uint8(v___x_2678_, sizeof(void*)*2 + 1, v___y_2676_);
if (v_isShared_2674_ == 0)
{
lean_ctor_set(v___x_2673_, 0, v___x_2678_);
v___x_2680_ = v___x_2673_;
goto v_reusejp_2679_;
}
else
{
lean_object* v_reuseFailAlloc_2681_; 
v_reuseFailAlloc_2681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2681_, 0, v___x_2678_);
v___x_2680_ = v_reuseFailAlloc_2681_;
goto v_reusejp_2679_;
}
v_reusejp_2679_:
{
return v___x_2680_;
}
}
}
}
}
else
{
lean_object* v_a_2684_; lean_object* v___x_2686_; uint8_t v_isShared_2687_; uint8_t v_isSharedCheck_2691_; 
lean_del_object(v___x_2668_);
lean_dec_ref(v_e_x27_2663_);
v_a_2684_ = lean_ctor_get(v___x_2670_, 0);
v_isSharedCheck_2691_ = !lean_is_exclusive(v___x_2670_);
if (v_isSharedCheck_2691_ == 0)
{
v___x_2686_ = v___x_2670_;
v_isShared_2687_ = v_isSharedCheck_2691_;
goto v_resetjp_2685_;
}
else
{
lean_inc(v_a_2684_);
lean_dec(v___x_2670_);
v___x_2686_ = lean_box(0);
v_isShared_2687_ = v_isSharedCheck_2691_;
goto v_resetjp_2685_;
}
v_resetjp_2685_:
{
lean_object* v___x_2689_; 
if (v_isShared_2687_ == 0)
{
v___x_2689_ = v___x_2686_;
goto v_reusejp_2688_;
}
else
{
lean_object* v_reuseFailAlloc_2690_; 
v_reuseFailAlloc_2690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2690_, 0, v_a_2684_);
v___x_2689_ = v_reuseFailAlloc_2690_;
goto v_reusejp_2688_;
}
v_reusejp_2688_:
{
return v___x_2689_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_2646_);
lean_dec_ref(v_proof_2643_);
lean_dec_ref(v_e_x27_2642_);
lean_dec(v___y_2620_);
lean_dec_ref(v___y_2619_);
lean_dec(v___y_2618_);
lean_dec_ref(v___y_2617_);
lean_dec(v___y_2616_);
lean_dec_ref(v___y_2615_);
lean_dec_ref(v___y_2611_);
return v___x_2648_;
}
}
}
else
{
lean_dec_ref_known(v_a_2623_, 2);
lean_dec(v___y_2620_);
lean_dec_ref(v___y_2619_);
lean_dec(v___y_2618_);
lean_dec_ref(v___y_2617_);
lean_dec(v___y_2616_);
lean_dec_ref(v___y_2615_);
lean_dec(v___y_2614_);
lean_dec_ref(v___y_2613_);
lean_dec(v___y_2612_);
lean_dec_ref(v___y_2611_);
lean_dec_ref(v_d_2610_);
return v___x_2622_;
}
}
}
else
{
lean_dec(v___y_2620_);
lean_dec_ref(v___y_2619_);
lean_dec(v___y_2618_);
lean_dec_ref(v___y_2617_);
lean_dec(v___y_2616_);
lean_dec_ref(v___y_2615_);
lean_dec(v___y_2614_);
lean_dec_ref(v___y_2613_);
lean_dec(v___y_2612_);
lean_dec_ref(v___y_2611_);
lean_dec_ref(v_d_2610_);
return v___x_2622_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___lam__0___boxed(lean_object* v_post_2695_, lean_object* v_a_2696_, lean_object* v_d_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_){
_start:
{
lean_object* v_res_2709_; 
v_res_2709_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___lam__0(v_post_2695_, v_a_2696_, v_d_2697_, v___y_2698_, v___y_2699_, v___y_2700_, v___y_2701_, v___y_2702_, v___y_2703_, v___y_2704_, v___y_2705_, v___y_2706_, v___y_2707_);
lean_dec_ref(v_a_2696_);
return v_res_2709_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems_spec__0___redArg(lean_object* v_as_2710_, size_t v_sz_2711_, size_t v_i_2712_, lean_object* v_b_2713_){
_start:
{
uint8_t v___x_2715_; 
v___x_2715_ = lean_usize_dec_lt(v_i_2712_, v_sz_2711_);
if (v___x_2715_ == 0)
{
lean_object* v___x_2716_; 
v___x_2716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2716_, 0, v_b_2713_);
return v___x_2716_;
}
else
{
lean_object* v_a_2717_; lean_object* v___x_2718_; size_t v___x_2719_; size_t v___x_2720_; 
v_a_2717_ = lean_array_uget_borrowed(v_as_2710_, v_i_2712_);
lean_inc(v_a_2717_);
v___x_2718_ = l_Lean_Meta_Sym_Simp_Theorems_insert(v_b_2713_, v_a_2717_);
v___x_2719_ = ((size_t)1ULL);
v___x_2720_ = lean_usize_add(v_i_2712_, v___x_2719_);
v_i_2712_ = v___x_2720_;
v_b_2713_ = v___x_2718_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems_spec__0___redArg___boxed(lean_object* v_as_2722_, lean_object* v_sz_2723_, lean_object* v_i_2724_, lean_object* v_b_2725_, lean_object* v___y_2726_){
_start:
{
size_t v_sz_boxed_2727_; size_t v_i_boxed_2728_; lean_object* v_res_2729_; 
v_sz_boxed_2727_ = lean_unbox_usize(v_sz_2723_);
lean_dec(v_sz_2723_);
v_i_boxed_2728_ = lean_unbox_usize(v_i_2724_);
lean_dec(v_i_2724_);
v_res_2729_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems_spec__0___redArg(v_as_2722_, v_sz_boxed_2727_, v_i_boxed_2728_, v_b_2725_);
lean_dec_ref(v_as_2722_);
return v_res_2729_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___closed__0(void){
_start:
{
lean_object* v___x_2730_; 
v___x_2730_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_2730_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___closed__1(void){
_start:
{
lean_object* v___x_2731_; lean_object* v___x_2732_; 
v___x_2731_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___closed__0, &l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___closed__0_once, _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___closed__0);
v___x_2732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2732_, 0, v___x_2731_);
return v___x_2732_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___closed__2(void){
_start:
{
lean_object* v___x_2733_; lean_object* v_thms_2734_; 
v___x_2733_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___closed__1, &l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___closed__1);
v_thms_2734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_thms_2734_, 0, v___x_2733_);
lean_ctor_set(v_thms_2734_, 1, v___x_2733_);
return v_thms_2734_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems(lean_object* v_post_2735_, lean_object* v_extraThms_2736_, lean_object* v_d_2737_, lean_object* v_a_2738_, lean_object* v_a_2739_, lean_object* v_a_2740_, lean_object* v_a_2741_, lean_object* v_a_2742_, lean_object* v_a_2743_, lean_object* v_a_2744_, lean_object* v_a_2745_){
_start:
{
lean_object* v___x_2747_; lean_object* v___x_2748_; uint8_t v___x_2749_; 
v___x_2747_ = lean_array_get_size(v_extraThms_2736_);
v___x_2748_ = lean_unsigned_to_nat(0u);
v___x_2749_ = lean_nat_dec_eq(v___x_2747_, v___x_2748_);
if (v___x_2749_ == 0)
{
lean_object* v_thms_2750_; size_t v_sz_2751_; size_t v___x_2752_; lean_object* v___x_2753_; 
v_thms_2750_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___closed__2, &l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___closed__2_once, _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___closed__2);
v_sz_2751_ = lean_array_size(v_extraThms_2736_);
v___x_2752_ = ((size_t)0ULL);
v___x_2753_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems_spec__0___redArg(v_extraThms_2736_, v_sz_2751_, v___x_2752_, v_thms_2750_);
if (lean_obj_tag(v___x_2753_) == 0)
{
lean_object* v_a_2754_; lean_object* v___x_2756_; uint8_t v_isShared_2757_; uint8_t v_isSharedCheck_2762_; 
v_a_2754_ = lean_ctor_get(v___x_2753_, 0);
v_isSharedCheck_2762_ = !lean_is_exclusive(v___x_2753_);
if (v_isSharedCheck_2762_ == 0)
{
v___x_2756_ = v___x_2753_;
v_isShared_2757_ = v_isSharedCheck_2762_;
goto v_resetjp_2755_;
}
else
{
lean_inc(v_a_2754_);
lean_dec(v___x_2753_);
v___x_2756_ = lean_box(0);
v_isShared_2757_ = v_isSharedCheck_2762_;
goto v_resetjp_2755_;
}
v_resetjp_2755_:
{
lean_object* v___f_2758_; lean_object* v___x_2760_; 
v___f_2758_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___lam__0___boxed), 14, 3);
lean_closure_set(v___f_2758_, 0, v_post_2735_);
lean_closure_set(v___f_2758_, 1, v_a_2754_);
lean_closure_set(v___f_2758_, 2, v_d_2737_);
if (v_isShared_2757_ == 0)
{
lean_ctor_set(v___x_2756_, 0, v___f_2758_);
v___x_2760_ = v___x_2756_;
goto v_reusejp_2759_;
}
else
{
lean_object* v_reuseFailAlloc_2761_; 
v_reuseFailAlloc_2761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2761_, 0, v___f_2758_);
v___x_2760_ = v_reuseFailAlloc_2761_;
goto v_reusejp_2759_;
}
v_reusejp_2759_:
{
return v___x_2760_;
}
}
}
else
{
lean_object* v_a_2763_; lean_object* v___x_2765_; uint8_t v_isShared_2766_; uint8_t v_isSharedCheck_2770_; 
lean_dec_ref(v_d_2737_);
lean_dec_ref(v_post_2735_);
v_a_2763_ = lean_ctor_get(v___x_2753_, 0);
v_isSharedCheck_2770_ = !lean_is_exclusive(v___x_2753_);
if (v_isSharedCheck_2770_ == 0)
{
v___x_2765_ = v___x_2753_;
v_isShared_2766_ = v_isSharedCheck_2770_;
goto v_resetjp_2764_;
}
else
{
lean_inc(v_a_2763_);
lean_dec(v___x_2753_);
v___x_2765_ = lean_box(0);
v_isShared_2766_ = v_isSharedCheck_2770_;
goto v_resetjp_2764_;
}
v_resetjp_2764_:
{
lean_object* v___x_2768_; 
if (v_isShared_2766_ == 0)
{
v___x_2768_ = v___x_2765_;
goto v_reusejp_2767_;
}
else
{
lean_object* v_reuseFailAlloc_2769_; 
v_reuseFailAlloc_2769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2769_, 0, v_a_2763_);
v___x_2768_ = v_reuseFailAlloc_2769_;
goto v_reusejp_2767_;
}
v_reusejp_2767_:
{
return v___x_2768_;
}
}
}
}
else
{
lean_object* v___x_2771_; 
lean_dec_ref(v_d_2737_);
v___x_2771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2771_, 0, v_post_2735_);
return v___x_2771_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___boxed(lean_object* v_post_2772_, lean_object* v_extraThms_2773_, lean_object* v_d_2774_, lean_object* v_a_2775_, lean_object* v_a_2776_, lean_object* v_a_2777_, lean_object* v_a_2778_, lean_object* v_a_2779_, lean_object* v_a_2780_, lean_object* v_a_2781_, lean_object* v_a_2782_, lean_object* v_a_2783_){
_start:
{
lean_object* v_res_2784_; 
v_res_2784_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems(v_post_2772_, v_extraThms_2773_, v_d_2774_, v_a_2775_, v_a_2776_, v_a_2777_, v_a_2778_, v_a_2779_, v_a_2780_, v_a_2781_, v_a_2782_);
lean_dec(v_a_2782_);
lean_dec_ref(v_a_2781_);
lean_dec(v_a_2780_);
lean_dec_ref(v_a_2779_);
lean_dec(v_a_2778_);
lean_dec_ref(v_a_2777_);
lean_dec(v_a_2776_);
lean_dec_ref(v_a_2775_);
lean_dec_ref(v_extraThms_2773_);
return v_res_2784_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems_spec__0(lean_object* v_as_2785_, size_t v_sz_2786_, size_t v_i_2787_, lean_object* v_b_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_){
_start:
{
lean_object* v___x_2798_; 
v___x_2798_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems_spec__0___redArg(v_as_2785_, v_sz_2786_, v_i_2787_, v_b_2788_);
return v___x_2798_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems_spec__0___boxed(lean_object* v_as_2799_, lean_object* v_sz_2800_, lean_object* v_i_2801_, lean_object* v_b_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_){
_start:
{
size_t v_sz_boxed_2812_; size_t v_i_boxed_2813_; lean_object* v_res_2814_; 
v_sz_boxed_2812_ = lean_unbox_usize(v_sz_2800_);
lean_dec(v_sz_2800_);
v_i_boxed_2813_ = lean_unbox_usize(v_i_2801_);
lean_dec(v_i_2801_);
v_res_2814_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems_spec__0(v_as_2799_, v_sz_boxed_2812_, v_i_boxed_2813_, v_b_2802_, v___y_2803_, v___y_2804_, v___y_2805_, v___y_2806_, v___y_2807_, v___y_2808_, v___y_2809_, v___y_2810_);
lean_dec(v___y_2810_);
lean_dec_ref(v___y_2809_);
lean_dec(v___y_2808_);
lean_dec_ref(v___y_2807_);
lean_dec(v___y_2806_);
lean_dec_ref(v___y_2805_);
lean_dec(v___y_2804_);
lean_dec_ref(v___y_2803_);
lean_dec_ref(v_as_2799_);
return v_res_2814_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkSimpDefaultMethods___lam__0(lean_object* v_x_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_){
_start:
{
lean_object* v___x_2828_; lean_object* v___x_2829_; 
v___x_2828_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkSimpDefaultMethods___lam__0___closed__0));
v___x_2829_ = l_Lean_Meta_Sym_Simp_simpArrowTelescope(v___x_2828_, v___y_2817_, v___y_2818_, v___y_2819_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_);
return v___x_2829_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkSimpDefaultMethods___lam__0___boxed(lean_object* v_x_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_){
_start:
{
lean_object* v_res_2842_; 
v_res_2842_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkSimpDefaultMethods___lam__0(v_x_2830_, v___y_2831_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_, v___y_2840_);
lean_dec(v___y_2840_);
lean_dec_ref(v___y_2839_);
lean_dec(v___y_2838_);
lean_dec_ref(v___y_2837_);
lean_dec(v___y_2836_);
lean_dec_ref(v___y_2835_);
lean_dec(v___y_2834_);
lean_dec_ref(v___y_2833_);
lean_dec(v___y_2832_);
return v_res_2842_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkSimpDefaultMethods___lam__1(lean_object* v___f_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_){
_start:
{
lean_object* v___x_2855_; lean_object* v___x_2856_; 
v___x_2855_ = lean_box(0);
lean_inc_ref(v___y_2844_);
v___x_2856_ = l_Lean_Meta_Sym_Simp_simpControl(v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_);
if (lean_obj_tag(v___x_2856_) == 0)
{
lean_object* v_a_2857_; 
v_a_2857_ = lean_ctor_get(v___x_2856_, 0);
lean_inc(v_a_2857_);
if (lean_obj_tag(v_a_2857_) == 0)
{
uint8_t v_done_2858_; 
v_done_2858_ = lean_ctor_get_uint8(v_a_2857_, 0);
if (v_done_2858_ == 0)
{
uint8_t v_contextDependent_2859_; lean_object* v___x_2860_; 
lean_dec_ref_known(v___x_2856_, 1);
v_contextDependent_2859_ = lean_ctor_get_uint8(v_a_2857_, 1);
lean_dec_ref_known(v_a_2857_, 0);
v___x_2860_ = lean_apply_12(v___f_2843_, v___x_2855_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_, lean_box(0));
if (lean_obj_tag(v___x_2860_) == 0)
{
lean_object* v_a_2861_; uint8_t v___y_2863_; 
v_a_2861_ = lean_ctor_get(v___x_2860_, 0);
lean_inc(v_a_2861_);
if (v_contextDependent_2859_ == 0)
{
lean_dec(v_a_2861_);
return v___x_2860_;
}
else
{
if (lean_obj_tag(v_a_2861_) == 0)
{
uint8_t v_contextDependent_2873_; 
v_contextDependent_2873_ = lean_ctor_get_uint8(v_a_2861_, 1);
v___y_2863_ = v_contextDependent_2873_;
goto v___jp_2862_;
}
else
{
uint8_t v_contextDependent_2874_; 
v_contextDependent_2874_ = lean_ctor_get_uint8(v_a_2861_, sizeof(void*)*2 + 1);
v___y_2863_ = v_contextDependent_2874_;
goto v___jp_2862_;
}
}
v___jp_2862_:
{
if (v___y_2863_ == 0)
{
lean_object* v___x_2865_; uint8_t v_isShared_2866_; uint8_t v_isSharedCheck_2871_; 
v_isSharedCheck_2871_ = !lean_is_exclusive(v___x_2860_);
if (v_isSharedCheck_2871_ == 0)
{
lean_object* v_unused_2872_; 
v_unused_2872_ = lean_ctor_get(v___x_2860_, 0);
lean_dec(v_unused_2872_);
v___x_2865_ = v___x_2860_;
v_isShared_2866_ = v_isSharedCheck_2871_;
goto v_resetjp_2864_;
}
else
{
lean_dec(v___x_2860_);
v___x_2865_ = lean_box(0);
v_isShared_2866_ = v_isSharedCheck_2871_;
goto v_resetjp_2864_;
}
v_resetjp_2864_:
{
lean_object* v___x_2867_; lean_object* v___x_2869_; 
v___x_2867_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_2861_);
if (v_isShared_2866_ == 0)
{
lean_ctor_set(v___x_2865_, 0, v___x_2867_);
v___x_2869_ = v___x_2865_;
goto v_reusejp_2868_;
}
else
{
lean_object* v_reuseFailAlloc_2870_; 
v_reuseFailAlloc_2870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2870_, 0, v___x_2867_);
v___x_2869_ = v_reuseFailAlloc_2870_;
goto v_reusejp_2868_;
}
v_reusejp_2868_:
{
return v___x_2869_;
}
}
}
else
{
lean_dec(v_a_2861_);
return v___x_2860_;
}
}
}
else
{
return v___x_2860_;
}
}
else
{
lean_dec_ref_known(v_a_2857_, 0);
lean_dec(v___y_2853_);
lean_dec_ref(v___y_2852_);
lean_dec(v___y_2851_);
lean_dec_ref(v___y_2850_);
lean_dec(v___y_2849_);
lean_dec_ref(v___y_2848_);
lean_dec(v___y_2847_);
lean_dec_ref(v___y_2846_);
lean_dec(v___y_2845_);
lean_dec_ref(v___y_2844_);
lean_dec_ref(v___f_2843_);
return v___x_2856_;
}
}
else
{
uint8_t v_done_2875_; 
v_done_2875_ = lean_ctor_get_uint8(v_a_2857_, sizeof(void*)*2);
if (v_done_2875_ == 0)
{
lean_object* v_e_x27_2876_; lean_object* v_proof_2877_; uint8_t v_contextDependent_2878_; lean_object* v___x_2880_; uint8_t v_isShared_2881_; uint8_t v_isSharedCheck_2928_; 
lean_dec_ref_known(v___x_2856_, 1);
v_e_x27_2876_ = lean_ctor_get(v_a_2857_, 0);
v_proof_2877_ = lean_ctor_get(v_a_2857_, 1);
v_contextDependent_2878_ = lean_ctor_get_uint8(v_a_2857_, sizeof(void*)*2 + 1);
v_isSharedCheck_2928_ = !lean_is_exclusive(v_a_2857_);
if (v_isSharedCheck_2928_ == 0)
{
v___x_2880_ = v_a_2857_;
v_isShared_2881_ = v_isSharedCheck_2928_;
goto v_resetjp_2879_;
}
else
{
lean_inc(v_proof_2877_);
lean_inc(v_e_x27_2876_);
lean_dec(v_a_2857_);
v___x_2880_ = lean_box(0);
v_isShared_2881_ = v_isSharedCheck_2928_;
goto v_resetjp_2879_;
}
v_resetjp_2879_:
{
lean_object* v___x_2882_; 
lean_inc(v___y_2853_);
lean_inc_ref(v___y_2852_);
lean_inc(v___y_2851_);
lean_inc_ref(v___y_2850_);
lean_inc(v___y_2849_);
lean_inc_ref(v___y_2848_);
lean_inc_ref(v_e_x27_2876_);
v___x_2882_ = lean_apply_12(v___f_2843_, v___x_2855_, v_e_x27_2876_, v___y_2845_, v___y_2846_, v___y_2847_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_, lean_box(0));
if (lean_obj_tag(v___x_2882_) == 0)
{
lean_object* v_a_2883_; lean_object* v___x_2885_; uint8_t v_isShared_2886_; uint8_t v_isSharedCheck_2927_; 
v_a_2883_ = lean_ctor_get(v___x_2882_, 0);
v_isSharedCheck_2927_ = !lean_is_exclusive(v___x_2882_);
if (v_isSharedCheck_2927_ == 0)
{
v___x_2885_ = v___x_2882_;
v_isShared_2886_ = v_isSharedCheck_2927_;
goto v_resetjp_2884_;
}
else
{
lean_inc(v_a_2883_);
lean_dec(v___x_2882_);
v___x_2885_ = lean_box(0);
v_isShared_2886_ = v_isSharedCheck_2927_;
goto v_resetjp_2884_;
}
v_resetjp_2884_:
{
if (lean_obj_tag(v_a_2883_) == 0)
{
uint8_t v_done_2887_; uint8_t v_contextDependent_2888_; uint8_t v___y_2890_; 
lean_dec(v___y_2853_);
lean_dec_ref(v___y_2852_);
lean_dec(v___y_2851_);
lean_dec_ref(v___y_2850_);
lean_dec(v___y_2849_);
lean_dec_ref(v___y_2848_);
lean_dec_ref(v___y_2844_);
v_done_2887_ = lean_ctor_get_uint8(v_a_2883_, 0);
v_contextDependent_2888_ = lean_ctor_get_uint8(v_a_2883_, 1);
lean_dec_ref_known(v_a_2883_, 0);
if (v_contextDependent_2878_ == 0)
{
v___y_2890_ = v_contextDependent_2888_;
goto v___jp_2889_;
}
else
{
v___y_2890_ = v_contextDependent_2878_;
goto v___jp_2889_;
}
v___jp_2889_:
{
lean_object* v___x_2892_; 
if (v_isShared_2881_ == 0)
{
v___x_2892_ = v___x_2880_;
goto v_reusejp_2891_;
}
else
{
lean_object* v_reuseFailAlloc_2896_; 
v_reuseFailAlloc_2896_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2896_, 0, v_e_x27_2876_);
lean_ctor_set(v_reuseFailAlloc_2896_, 1, v_proof_2877_);
v___x_2892_ = v_reuseFailAlloc_2896_;
goto v_reusejp_2891_;
}
v_reusejp_2891_:
{
lean_object* v___x_2894_; 
lean_ctor_set_uint8(v___x_2892_, sizeof(void*)*2, v_done_2887_);
lean_ctor_set_uint8(v___x_2892_, sizeof(void*)*2 + 1, v___y_2890_);
if (v_isShared_2886_ == 0)
{
lean_ctor_set(v___x_2885_, 0, v___x_2892_);
v___x_2894_ = v___x_2885_;
goto v_reusejp_2893_;
}
else
{
lean_object* v_reuseFailAlloc_2895_; 
v_reuseFailAlloc_2895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2895_, 0, v___x_2892_);
v___x_2894_ = v_reuseFailAlloc_2895_;
goto v_reusejp_2893_;
}
v_reusejp_2893_:
{
return v___x_2894_;
}
}
}
}
else
{
lean_object* v_e_x27_2897_; lean_object* v_proof_2898_; uint8_t v_done_2899_; uint8_t v_contextDependent_2900_; lean_object* v___x_2902_; uint8_t v_isShared_2903_; uint8_t v_isSharedCheck_2926_; 
lean_del_object(v___x_2885_);
lean_del_object(v___x_2880_);
v_e_x27_2897_ = lean_ctor_get(v_a_2883_, 0);
v_proof_2898_ = lean_ctor_get(v_a_2883_, 1);
v_done_2899_ = lean_ctor_get_uint8(v_a_2883_, sizeof(void*)*2);
v_contextDependent_2900_ = lean_ctor_get_uint8(v_a_2883_, sizeof(void*)*2 + 1);
v_isSharedCheck_2926_ = !lean_is_exclusive(v_a_2883_);
if (v_isSharedCheck_2926_ == 0)
{
v___x_2902_ = v_a_2883_;
v_isShared_2903_ = v_isSharedCheck_2926_;
goto v_resetjp_2901_;
}
else
{
lean_inc(v_proof_2898_);
lean_inc(v_e_x27_2897_);
lean_dec(v_a_2883_);
v___x_2902_ = lean_box(0);
v_isShared_2903_ = v_isSharedCheck_2926_;
goto v_resetjp_2901_;
}
v_resetjp_2901_:
{
lean_object* v___x_2904_; 
lean_inc_ref(v_e_x27_2897_);
v___x_2904_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_2844_, v_e_x27_2876_, v_proof_2877_, v_e_x27_2897_, v_proof_2898_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_);
lean_dec(v___y_2853_);
lean_dec_ref(v___y_2852_);
lean_dec(v___y_2851_);
lean_dec_ref(v___y_2850_);
lean_dec(v___y_2849_);
lean_dec_ref(v___y_2848_);
if (lean_obj_tag(v___x_2904_) == 0)
{
lean_object* v_a_2905_; lean_object* v___x_2907_; uint8_t v_isShared_2908_; uint8_t v_isSharedCheck_2917_; 
v_a_2905_ = lean_ctor_get(v___x_2904_, 0);
v_isSharedCheck_2917_ = !lean_is_exclusive(v___x_2904_);
if (v_isSharedCheck_2917_ == 0)
{
v___x_2907_ = v___x_2904_;
v_isShared_2908_ = v_isSharedCheck_2917_;
goto v_resetjp_2906_;
}
else
{
lean_inc(v_a_2905_);
lean_dec(v___x_2904_);
v___x_2907_ = lean_box(0);
v_isShared_2908_ = v_isSharedCheck_2917_;
goto v_resetjp_2906_;
}
v_resetjp_2906_:
{
uint8_t v___y_2910_; 
if (v_contextDependent_2878_ == 0)
{
v___y_2910_ = v_contextDependent_2900_;
goto v___jp_2909_;
}
else
{
v___y_2910_ = v_contextDependent_2878_;
goto v___jp_2909_;
}
v___jp_2909_:
{
lean_object* v___x_2912_; 
if (v_isShared_2903_ == 0)
{
lean_ctor_set(v___x_2902_, 1, v_a_2905_);
v___x_2912_ = v___x_2902_;
goto v_reusejp_2911_;
}
else
{
lean_object* v_reuseFailAlloc_2916_; 
v_reuseFailAlloc_2916_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2916_, 0, v_e_x27_2897_);
lean_ctor_set(v_reuseFailAlloc_2916_, 1, v_a_2905_);
lean_ctor_set_uint8(v_reuseFailAlloc_2916_, sizeof(void*)*2, v_done_2899_);
v___x_2912_ = v_reuseFailAlloc_2916_;
goto v_reusejp_2911_;
}
v_reusejp_2911_:
{
lean_object* v___x_2914_; 
lean_ctor_set_uint8(v___x_2912_, sizeof(void*)*2 + 1, v___y_2910_);
if (v_isShared_2908_ == 0)
{
lean_ctor_set(v___x_2907_, 0, v___x_2912_);
v___x_2914_ = v___x_2907_;
goto v_reusejp_2913_;
}
else
{
lean_object* v_reuseFailAlloc_2915_; 
v_reuseFailAlloc_2915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2915_, 0, v___x_2912_);
v___x_2914_ = v_reuseFailAlloc_2915_;
goto v_reusejp_2913_;
}
v_reusejp_2913_:
{
return v___x_2914_;
}
}
}
}
}
else
{
lean_object* v_a_2918_; lean_object* v___x_2920_; uint8_t v_isShared_2921_; uint8_t v_isSharedCheck_2925_; 
lean_del_object(v___x_2902_);
lean_dec_ref(v_e_x27_2897_);
v_a_2918_ = lean_ctor_get(v___x_2904_, 0);
v_isSharedCheck_2925_ = !lean_is_exclusive(v___x_2904_);
if (v_isSharedCheck_2925_ == 0)
{
v___x_2920_ = v___x_2904_;
v_isShared_2921_ = v_isSharedCheck_2925_;
goto v_resetjp_2919_;
}
else
{
lean_inc(v_a_2918_);
lean_dec(v___x_2904_);
v___x_2920_ = lean_box(0);
v_isShared_2921_ = v_isSharedCheck_2925_;
goto v_resetjp_2919_;
}
v_resetjp_2919_:
{
lean_object* v___x_2923_; 
if (v_isShared_2921_ == 0)
{
v___x_2923_ = v___x_2920_;
goto v_reusejp_2922_;
}
else
{
lean_object* v_reuseFailAlloc_2924_; 
v_reuseFailAlloc_2924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2924_, 0, v_a_2918_);
v___x_2923_ = v_reuseFailAlloc_2924_;
goto v_reusejp_2922_;
}
v_reusejp_2922_:
{
return v___x_2923_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_2880_);
lean_dec_ref(v_proof_2877_);
lean_dec_ref(v_e_x27_2876_);
lean_dec(v___y_2853_);
lean_dec_ref(v___y_2852_);
lean_dec(v___y_2851_);
lean_dec_ref(v___y_2850_);
lean_dec(v___y_2849_);
lean_dec_ref(v___y_2848_);
lean_dec_ref(v___y_2844_);
return v___x_2882_;
}
}
}
else
{
lean_dec_ref_known(v_a_2857_, 2);
lean_dec(v___y_2853_);
lean_dec_ref(v___y_2852_);
lean_dec(v___y_2851_);
lean_dec_ref(v___y_2850_);
lean_dec(v___y_2849_);
lean_dec_ref(v___y_2848_);
lean_dec(v___y_2847_);
lean_dec_ref(v___y_2846_);
lean_dec(v___y_2845_);
lean_dec_ref(v___y_2844_);
lean_dec_ref(v___f_2843_);
return v___x_2856_;
}
}
}
else
{
lean_dec(v___y_2853_);
lean_dec_ref(v___y_2852_);
lean_dec(v___y_2851_);
lean_dec_ref(v___y_2850_);
lean_dec(v___y_2849_);
lean_dec_ref(v___y_2848_);
lean_dec(v___y_2847_);
lean_dec_ref(v___y_2846_);
lean_dec(v___y_2845_);
lean_dec_ref(v___y_2844_);
lean_dec_ref(v___f_2843_);
return v___x_2856_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkSimpDefaultMethods___lam__1___boxed(lean_object* v___f_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_){
_start:
{
lean_object* v_res_2941_; 
v_res_2941_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkSimpDefaultMethods___lam__1(v___f_2929_, v___y_2930_, v___y_2931_, v___y_2932_, v___y_2933_, v___y_2934_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_, v___y_2939_);
return v_res_2941_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkSimpDefaultMethods___lam__2(lean_object* v___x_2942_, lean_object* v_a_2943_, lean_object* v_d_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_){
_start:
{
lean_object* v___x_2956_; 
v___x_2956_ = l___private_Lean_Meta_Sym_Simp_EvalGround_0__Lean_Meta_Sym_Simp_evalGroundCore___redArg(v___y_2945_, v___x_2942_, v___y_2949_, v___y_2950_, v___y_2951_, v___y_2952_, v___y_2953_, v___y_2954_);
if (lean_obj_tag(v___x_2956_) == 0)
{
lean_object* v_a_2957_; 
v_a_2957_ = lean_ctor_get(v___x_2956_, 0);
lean_inc(v_a_2957_);
if (lean_obj_tag(v_a_2957_) == 0)
{
uint8_t v_done_2958_; 
v_done_2958_ = lean_ctor_get_uint8(v_a_2957_, 0);
if (v_done_2958_ == 0)
{
uint8_t v_contextDependent_2959_; lean_object* v___x_2960_; 
lean_dec_ref_known(v___x_2956_, 1);
v_contextDependent_2959_ = lean_ctor_get_uint8(v_a_2957_, 1);
lean_dec_ref_known(v_a_2957_, 0);
v___x_2960_ = l_Lean_Meta_Sym_Simp_Theorems_rewrite(v_a_2943_, v_d_2944_, v___y_2945_, v___y_2946_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_, v___y_2951_, v___y_2952_, v___y_2953_, v___y_2954_);
if (lean_obj_tag(v___x_2960_) == 0)
{
lean_object* v_a_2961_; uint8_t v___y_2963_; 
v_a_2961_ = lean_ctor_get(v___x_2960_, 0);
if (v_contextDependent_2959_ == 0)
{
return v___x_2960_;
}
else
{
if (lean_obj_tag(v_a_2961_) == 0)
{
uint8_t v_contextDependent_2973_; 
v_contextDependent_2973_ = lean_ctor_get_uint8(v_a_2961_, 1);
v___y_2963_ = v_contextDependent_2973_;
goto v___jp_2962_;
}
else
{
uint8_t v_contextDependent_2974_; 
v_contextDependent_2974_ = lean_ctor_get_uint8(v_a_2961_, sizeof(void*)*2 + 1);
v___y_2963_ = v_contextDependent_2974_;
goto v___jp_2962_;
}
}
v___jp_2962_:
{
if (v___y_2963_ == 0)
{
lean_object* v___x_2965_; uint8_t v_isShared_2966_; uint8_t v_isSharedCheck_2971_; 
lean_inc(v_a_2961_);
v_isSharedCheck_2971_ = !lean_is_exclusive(v___x_2960_);
if (v_isSharedCheck_2971_ == 0)
{
lean_object* v_unused_2972_; 
v_unused_2972_ = lean_ctor_get(v___x_2960_, 0);
lean_dec(v_unused_2972_);
v___x_2965_ = v___x_2960_;
v_isShared_2966_ = v_isSharedCheck_2971_;
goto v_resetjp_2964_;
}
else
{
lean_dec(v___x_2960_);
v___x_2965_ = lean_box(0);
v_isShared_2966_ = v_isSharedCheck_2971_;
goto v_resetjp_2964_;
}
v_resetjp_2964_:
{
lean_object* v___x_2967_; lean_object* v___x_2969_; 
v___x_2967_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_2961_);
if (v_isShared_2966_ == 0)
{
lean_ctor_set(v___x_2965_, 0, v___x_2967_);
v___x_2969_ = v___x_2965_;
goto v_reusejp_2968_;
}
else
{
lean_object* v_reuseFailAlloc_2970_; 
v_reuseFailAlloc_2970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2970_, 0, v___x_2967_);
v___x_2969_ = v_reuseFailAlloc_2970_;
goto v_reusejp_2968_;
}
v_reusejp_2968_:
{
return v___x_2969_;
}
}
}
else
{
return v___x_2960_;
}
}
}
else
{
return v___x_2960_;
}
}
else
{
lean_dec_ref_known(v_a_2957_, 0);
lean_dec_ref(v___y_2945_);
lean_dec_ref(v_d_2944_);
return v___x_2956_;
}
}
else
{
uint8_t v_done_2975_; 
v_done_2975_ = lean_ctor_get_uint8(v_a_2957_, sizeof(void*)*2);
if (v_done_2975_ == 0)
{
lean_object* v_e_x27_2976_; lean_object* v_proof_2977_; uint8_t v_contextDependent_2978_; lean_object* v___x_2980_; uint8_t v_isShared_2981_; uint8_t v_isSharedCheck_3028_; 
lean_dec_ref_known(v___x_2956_, 1);
v_e_x27_2976_ = lean_ctor_get(v_a_2957_, 0);
v_proof_2977_ = lean_ctor_get(v_a_2957_, 1);
v_contextDependent_2978_ = lean_ctor_get_uint8(v_a_2957_, sizeof(void*)*2 + 1);
v_isSharedCheck_3028_ = !lean_is_exclusive(v_a_2957_);
if (v_isSharedCheck_3028_ == 0)
{
v___x_2980_ = v_a_2957_;
v_isShared_2981_ = v_isSharedCheck_3028_;
goto v_resetjp_2979_;
}
else
{
lean_inc(v_proof_2977_);
lean_inc(v_e_x27_2976_);
lean_dec(v_a_2957_);
v___x_2980_ = lean_box(0);
v_isShared_2981_ = v_isSharedCheck_3028_;
goto v_resetjp_2979_;
}
v_resetjp_2979_:
{
lean_object* v___x_2982_; 
lean_inc_ref(v_e_x27_2976_);
v___x_2982_ = l_Lean_Meta_Sym_Simp_Theorems_rewrite(v_a_2943_, v_d_2944_, v_e_x27_2976_, v___y_2946_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_, v___y_2951_, v___y_2952_, v___y_2953_, v___y_2954_);
if (lean_obj_tag(v___x_2982_) == 0)
{
lean_object* v_a_2983_; lean_object* v___x_2985_; uint8_t v_isShared_2986_; uint8_t v_isSharedCheck_3027_; 
v_a_2983_ = lean_ctor_get(v___x_2982_, 0);
v_isSharedCheck_3027_ = !lean_is_exclusive(v___x_2982_);
if (v_isSharedCheck_3027_ == 0)
{
v___x_2985_ = v___x_2982_;
v_isShared_2986_ = v_isSharedCheck_3027_;
goto v_resetjp_2984_;
}
else
{
lean_inc(v_a_2983_);
lean_dec(v___x_2982_);
v___x_2985_ = lean_box(0);
v_isShared_2986_ = v_isSharedCheck_3027_;
goto v_resetjp_2984_;
}
v_resetjp_2984_:
{
if (lean_obj_tag(v_a_2983_) == 0)
{
uint8_t v_done_2987_; uint8_t v_contextDependent_2988_; uint8_t v___y_2990_; 
lean_dec_ref(v___y_2945_);
v_done_2987_ = lean_ctor_get_uint8(v_a_2983_, 0);
v_contextDependent_2988_ = lean_ctor_get_uint8(v_a_2983_, 1);
lean_dec_ref_known(v_a_2983_, 0);
if (v_contextDependent_2978_ == 0)
{
v___y_2990_ = v_contextDependent_2988_;
goto v___jp_2989_;
}
else
{
v___y_2990_ = v_contextDependent_2978_;
goto v___jp_2989_;
}
v___jp_2989_:
{
lean_object* v___x_2992_; 
if (v_isShared_2981_ == 0)
{
v___x_2992_ = v___x_2980_;
goto v_reusejp_2991_;
}
else
{
lean_object* v_reuseFailAlloc_2996_; 
v_reuseFailAlloc_2996_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2996_, 0, v_e_x27_2976_);
lean_ctor_set(v_reuseFailAlloc_2996_, 1, v_proof_2977_);
v___x_2992_ = v_reuseFailAlloc_2996_;
goto v_reusejp_2991_;
}
v_reusejp_2991_:
{
lean_object* v___x_2994_; 
lean_ctor_set_uint8(v___x_2992_, sizeof(void*)*2, v_done_2987_);
lean_ctor_set_uint8(v___x_2992_, sizeof(void*)*2 + 1, v___y_2990_);
if (v_isShared_2986_ == 0)
{
lean_ctor_set(v___x_2985_, 0, v___x_2992_);
v___x_2994_ = v___x_2985_;
goto v_reusejp_2993_;
}
else
{
lean_object* v_reuseFailAlloc_2995_; 
v_reuseFailAlloc_2995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2995_, 0, v___x_2992_);
v___x_2994_ = v_reuseFailAlloc_2995_;
goto v_reusejp_2993_;
}
v_reusejp_2993_:
{
return v___x_2994_;
}
}
}
}
else
{
lean_object* v_e_x27_2997_; lean_object* v_proof_2998_; uint8_t v_done_2999_; uint8_t v_contextDependent_3000_; lean_object* v___x_3002_; uint8_t v_isShared_3003_; uint8_t v_isSharedCheck_3026_; 
lean_del_object(v___x_2985_);
lean_del_object(v___x_2980_);
v_e_x27_2997_ = lean_ctor_get(v_a_2983_, 0);
v_proof_2998_ = lean_ctor_get(v_a_2983_, 1);
v_done_2999_ = lean_ctor_get_uint8(v_a_2983_, sizeof(void*)*2);
v_contextDependent_3000_ = lean_ctor_get_uint8(v_a_2983_, sizeof(void*)*2 + 1);
v_isSharedCheck_3026_ = !lean_is_exclusive(v_a_2983_);
if (v_isSharedCheck_3026_ == 0)
{
v___x_3002_ = v_a_2983_;
v_isShared_3003_ = v_isSharedCheck_3026_;
goto v_resetjp_3001_;
}
else
{
lean_inc(v_proof_2998_);
lean_inc(v_e_x27_2997_);
lean_dec(v_a_2983_);
v___x_3002_ = lean_box(0);
v_isShared_3003_ = v_isSharedCheck_3026_;
goto v_resetjp_3001_;
}
v_resetjp_3001_:
{
lean_object* v___x_3004_; 
lean_inc_ref(v_e_x27_2997_);
v___x_3004_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_2945_, v_e_x27_2976_, v_proof_2977_, v_e_x27_2997_, v_proof_2998_, v___y_2949_, v___y_2950_, v___y_2951_, v___y_2952_, v___y_2953_, v___y_2954_);
if (lean_obj_tag(v___x_3004_) == 0)
{
lean_object* v_a_3005_; lean_object* v___x_3007_; uint8_t v_isShared_3008_; uint8_t v_isSharedCheck_3017_; 
v_a_3005_ = lean_ctor_get(v___x_3004_, 0);
v_isSharedCheck_3017_ = !lean_is_exclusive(v___x_3004_);
if (v_isSharedCheck_3017_ == 0)
{
v___x_3007_ = v___x_3004_;
v_isShared_3008_ = v_isSharedCheck_3017_;
goto v_resetjp_3006_;
}
else
{
lean_inc(v_a_3005_);
lean_dec(v___x_3004_);
v___x_3007_ = lean_box(0);
v_isShared_3008_ = v_isSharedCheck_3017_;
goto v_resetjp_3006_;
}
v_resetjp_3006_:
{
uint8_t v___y_3010_; 
if (v_contextDependent_2978_ == 0)
{
v___y_3010_ = v_contextDependent_3000_;
goto v___jp_3009_;
}
else
{
v___y_3010_ = v_contextDependent_2978_;
goto v___jp_3009_;
}
v___jp_3009_:
{
lean_object* v___x_3012_; 
if (v_isShared_3003_ == 0)
{
lean_ctor_set(v___x_3002_, 1, v_a_3005_);
v___x_3012_ = v___x_3002_;
goto v_reusejp_3011_;
}
else
{
lean_object* v_reuseFailAlloc_3016_; 
v_reuseFailAlloc_3016_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_3016_, 0, v_e_x27_2997_);
lean_ctor_set(v_reuseFailAlloc_3016_, 1, v_a_3005_);
lean_ctor_set_uint8(v_reuseFailAlloc_3016_, sizeof(void*)*2, v_done_2999_);
v___x_3012_ = v_reuseFailAlloc_3016_;
goto v_reusejp_3011_;
}
v_reusejp_3011_:
{
lean_object* v___x_3014_; 
lean_ctor_set_uint8(v___x_3012_, sizeof(void*)*2 + 1, v___y_3010_);
if (v_isShared_3008_ == 0)
{
lean_ctor_set(v___x_3007_, 0, v___x_3012_);
v___x_3014_ = v___x_3007_;
goto v_reusejp_3013_;
}
else
{
lean_object* v_reuseFailAlloc_3015_; 
v_reuseFailAlloc_3015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3015_, 0, v___x_3012_);
v___x_3014_ = v_reuseFailAlloc_3015_;
goto v_reusejp_3013_;
}
v_reusejp_3013_:
{
return v___x_3014_;
}
}
}
}
}
else
{
lean_object* v_a_3018_; lean_object* v___x_3020_; uint8_t v_isShared_3021_; uint8_t v_isSharedCheck_3025_; 
lean_del_object(v___x_3002_);
lean_dec_ref(v_e_x27_2997_);
v_a_3018_ = lean_ctor_get(v___x_3004_, 0);
v_isSharedCheck_3025_ = !lean_is_exclusive(v___x_3004_);
if (v_isSharedCheck_3025_ == 0)
{
v___x_3020_ = v___x_3004_;
v_isShared_3021_ = v_isSharedCheck_3025_;
goto v_resetjp_3019_;
}
else
{
lean_inc(v_a_3018_);
lean_dec(v___x_3004_);
v___x_3020_ = lean_box(0);
v_isShared_3021_ = v_isSharedCheck_3025_;
goto v_resetjp_3019_;
}
v_resetjp_3019_:
{
lean_object* v___x_3023_; 
if (v_isShared_3021_ == 0)
{
v___x_3023_ = v___x_3020_;
goto v_reusejp_3022_;
}
else
{
lean_object* v_reuseFailAlloc_3024_; 
v_reuseFailAlloc_3024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3024_, 0, v_a_3018_);
v___x_3023_ = v_reuseFailAlloc_3024_;
goto v_reusejp_3022_;
}
v_reusejp_3022_:
{
return v___x_3023_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_2980_);
lean_dec_ref(v_proof_2977_);
lean_dec_ref(v_e_x27_2976_);
lean_dec_ref(v___y_2945_);
return v___x_2982_;
}
}
}
else
{
lean_dec_ref_known(v_a_2957_, 2);
lean_dec_ref(v___y_2945_);
lean_dec_ref(v_d_2944_);
return v___x_2956_;
}
}
}
else
{
lean_dec_ref(v___y_2945_);
lean_dec_ref(v_d_2944_);
return v___x_2956_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkSimpDefaultMethods___lam__2___boxed(lean_object* v___x_3029_, lean_object* v_a_3030_, lean_object* v_d_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_){
_start:
{
lean_object* v_res_3043_; 
v_res_3043_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkSimpDefaultMethods___lam__2(v___x_3029_, v_a_3030_, v_d_3031_, v___y_3032_, v___y_3033_, v___y_3034_, v___y_3035_, v___y_3036_, v___y_3037_, v___y_3038_, v___y_3039_, v___y_3040_, v___y_3041_);
lean_dec(v___y_3041_);
lean_dec_ref(v___y_3040_);
lean_dec(v___y_3039_);
lean_dec_ref(v___y_3038_);
lean_dec(v___y_3037_);
lean_dec_ref(v___y_3036_);
lean_dec(v___y_3035_);
lean_dec_ref(v___y_3034_);
lean_dec(v___y_3033_);
lean_dec_ref(v_a_3030_);
lean_dec_ref(v___x_3029_);
return v_res_3043_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkSimpDefaultMethods(lean_object* v_extraThms_3050_, lean_object* v_d_3051_, lean_object* v_a_3052_, lean_object* v_a_3053_, lean_object* v_a_3054_, lean_object* v_a_3055_, lean_object* v_a_3056_, lean_object* v_a_3057_, lean_object* v_a_3058_, lean_object* v_a_3059_){
_start:
{
lean_object* v___f_3061_; lean_object* v___x_3062_; 
v___f_3061_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkSimpDefaultMethods___closed__1));
v___x_3062_ = l_Lean_Meta_Sym_Simp_getSymSimpTheorems___redArg(v_a_3059_);
if (lean_obj_tag(v___x_3062_) == 0)
{
lean_object* v_a_3063_; lean_object* v___x_3064_; lean_object* v___f_3065_; lean_object* v___x_3066_; 
v_a_3063_ = lean_ctor_get(v___x_3062_, 0);
lean_inc(v_a_3063_);
lean_dec_ref_known(v___x_3062_, 1);
v___x_3064_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkSimpDefaultMethods___closed__2));
lean_inc_ref(v_d_3051_);
v___f_3065_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkSimpDefaultMethods___lam__2___boxed), 14, 3);
lean_closure_set(v___f_3065_, 0, v___x_3064_);
lean_closure_set(v___f_3065_, 1, v_a_3063_);
lean_closure_set(v___f_3065_, 2, v_d_3051_);
v___x_3066_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems(v___f_3065_, v_extraThms_3050_, v_d_3051_, v_a_3052_, v_a_3053_, v_a_3054_, v_a_3055_, v_a_3056_, v_a_3057_, v_a_3058_, v_a_3059_);
if (lean_obj_tag(v___x_3066_) == 0)
{
lean_object* v_a_3067_; lean_object* v___x_3069_; uint8_t v_isShared_3070_; uint8_t v_isSharedCheck_3075_; 
v_a_3067_ = lean_ctor_get(v___x_3066_, 0);
v_isSharedCheck_3075_ = !lean_is_exclusive(v___x_3066_);
if (v_isSharedCheck_3075_ == 0)
{
v___x_3069_ = v___x_3066_;
v_isShared_3070_ = v_isSharedCheck_3075_;
goto v_resetjp_3068_;
}
else
{
lean_inc(v_a_3067_);
lean_dec(v___x_3066_);
v___x_3069_ = lean_box(0);
v_isShared_3070_ = v_isSharedCheck_3075_;
goto v_resetjp_3068_;
}
v_resetjp_3068_:
{
lean_object* v___x_3071_; lean_object* v___x_3073_; 
v___x_3071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3071_, 0, v___f_3061_);
lean_ctor_set(v___x_3071_, 1, v_a_3067_);
if (v_isShared_3070_ == 0)
{
lean_ctor_set(v___x_3069_, 0, v___x_3071_);
v___x_3073_ = v___x_3069_;
goto v_reusejp_3072_;
}
else
{
lean_object* v_reuseFailAlloc_3074_; 
v_reuseFailAlloc_3074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3074_, 0, v___x_3071_);
v___x_3073_ = v_reuseFailAlloc_3074_;
goto v_reusejp_3072_;
}
v_reusejp_3072_:
{
return v___x_3073_;
}
}
}
else
{
lean_object* v_a_3076_; lean_object* v___x_3078_; uint8_t v_isShared_3079_; uint8_t v_isSharedCheck_3083_; 
v_a_3076_ = lean_ctor_get(v___x_3066_, 0);
v_isSharedCheck_3083_ = !lean_is_exclusive(v___x_3066_);
if (v_isSharedCheck_3083_ == 0)
{
v___x_3078_ = v___x_3066_;
v_isShared_3079_ = v_isSharedCheck_3083_;
goto v_resetjp_3077_;
}
else
{
lean_inc(v_a_3076_);
lean_dec(v___x_3066_);
v___x_3078_ = lean_box(0);
v_isShared_3079_ = v_isSharedCheck_3083_;
goto v_resetjp_3077_;
}
v_resetjp_3077_:
{
lean_object* v___x_3081_; 
if (v_isShared_3079_ == 0)
{
v___x_3081_ = v___x_3078_;
goto v_reusejp_3080_;
}
else
{
lean_object* v_reuseFailAlloc_3082_; 
v_reuseFailAlloc_3082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3082_, 0, v_a_3076_);
v___x_3081_ = v_reuseFailAlloc_3082_;
goto v_reusejp_3080_;
}
v_reusejp_3080_:
{
return v___x_3081_;
}
}
}
}
else
{
lean_object* v_a_3084_; lean_object* v___x_3086_; uint8_t v_isShared_3087_; uint8_t v_isSharedCheck_3091_; 
lean_dec_ref(v_d_3051_);
v_a_3084_ = lean_ctor_get(v___x_3062_, 0);
v_isSharedCheck_3091_ = !lean_is_exclusive(v___x_3062_);
if (v_isSharedCheck_3091_ == 0)
{
v___x_3086_ = v___x_3062_;
v_isShared_3087_ = v_isSharedCheck_3091_;
goto v_resetjp_3085_;
}
else
{
lean_inc(v_a_3084_);
lean_dec(v___x_3062_);
v___x_3086_ = lean_box(0);
v_isShared_3087_ = v_isSharedCheck_3091_;
goto v_resetjp_3085_;
}
v_resetjp_3085_:
{
lean_object* v___x_3089_; 
if (v_isShared_3087_ == 0)
{
v___x_3089_ = v___x_3086_;
goto v_reusejp_3088_;
}
else
{
lean_object* v_reuseFailAlloc_3090_; 
v_reuseFailAlloc_3090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3090_, 0, v_a_3084_);
v___x_3089_ = v_reuseFailAlloc_3090_;
goto v_reusejp_3088_;
}
v_reusejp_3088_:
{
return v___x_3089_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkSimpDefaultMethods___boxed(lean_object* v_extraThms_3092_, lean_object* v_d_3093_, lean_object* v_a_3094_, lean_object* v_a_3095_, lean_object* v_a_3096_, lean_object* v_a_3097_, lean_object* v_a_3098_, lean_object* v_a_3099_, lean_object* v_a_3100_, lean_object* v_a_3101_, lean_object* v_a_3102_){
_start:
{
lean_object* v_res_3103_; 
v_res_3103_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkSimpDefaultMethods(v_extraThms_3092_, v_d_3093_, v_a_3094_, v_a_3095_, v_a_3096_, v_a_3097_, v_a_3098_, v_a_3099_, v_a_3100_, v_a_3101_);
lean_dec(v_a_3101_);
lean_dec_ref(v_a_3100_);
lean_dec(v_a_3099_);
lean_dec_ref(v_a_3098_);
lean_dec(v_a_3097_);
lean_dec_ref(v_a_3096_);
lean_dec(v_a_3095_);
lean_dec_ref(v_a_3094_);
lean_dec_ref(v_extraThms_3092_);
return v_res_3103_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_defaultDischargerConfig(lean_object* v_cfg_3104_){
_start:
{
uint8_t v_trace_3105_; uint8_t v_markInstances_3106_; uint8_t v_lax_3107_; uint8_t v_suggestions_3108_; uint8_t v_locals_3109_; lean_object* v_branches_3110_; lean_object* v_splits_3111_; uint8_t v_matchEqs_3112_; uint8_t v_splitMatch_3113_; uint8_t v_splitIte_3114_; uint8_t v_splitIndPred_3115_; uint8_t v_splitImp_3116_; lean_object* v_canonHeartbeats_3117_; uint8_t v_ext_3118_; uint8_t v_extAll_3119_; uint8_t v_etaStruct_3120_; uint8_t v_funext_3121_; uint8_t v_lookahead_3122_; uint8_t v_verbose_3123_; uint8_t v_clean_3124_; uint8_t v_qlia_3125_; uint8_t v_mbtc_3126_; uint8_t v_zetaDelta_3127_; uint8_t v_zeta_3128_; uint8_t v_distrib_3129_; lean_object* v_maxChar_3130_; uint8_t v_ring_3131_; lean_object* v_ringSteps_3132_; lean_object* v_ringMaxDegree_3133_; uint8_t v_linarith_3134_; uint8_t v_lia_3135_; lean_object* v_liaSteps_3136_; lean_object* v_liaReorders_3137_; lean_object* v_liaReorderCases_3138_; uint8_t v_hom_3139_; uint8_t v_ac_3140_; lean_object* v_acSteps_3141_; lean_object* v_exp_3142_; uint8_t v_abstractProof_3143_; uint8_t v_inj_3144_; uint8_t v_order_3145_; lean_object* v_min_3146_; lean_object* v_detailed_3147_; uint8_t v_useSorry_3148_; uint8_t v_revert_3149_; uint8_t v_funCC_3150_; uint8_t v_reducible_3151_; lean_object* v_maxSuggestions_3152_; lean_object* v___x_3154_; uint8_t v_isShared_3155_; uint8_t v_isSharedCheck_3161_; 
v_trace_3105_ = lean_ctor_get_uint8(v_cfg_3104_, sizeof(void*)*18);
v_markInstances_3106_ = lean_ctor_get_uint8(v_cfg_3104_, sizeof(void*)*18 + 1);
v_lax_3107_ = lean_ctor_get_uint8(v_cfg_3104_, sizeof(void*)*18 + 2);
v_suggestions_3108_ = lean_ctor_get_uint8(v_cfg_3104_, sizeof(void*)*18 + 3);
v_locals_3109_ = lean_ctor_get_uint8(v_cfg_3104_, sizeof(void*)*18 + 4);
v_branches_3110_ = lean_ctor_get(v_cfg_3104_, 0);
v_splits_3111_ = lean_ctor_get(v_cfg_3104_, 1);
v_matchEqs_3112_ = lean_ctor_get_uint8(v_cfg_3104_, sizeof(void*)*18 + 5);
v_splitMatch_3113_ = lean_ctor_get_uint8(v_cfg_3104_, sizeof(void*)*18 + 6);
v_splitIte_3114_ = lean_ctor_get_uint8(v_cfg_3104_, sizeof(void*)*18 + 7);
v_splitIndPred_3115_ = lean_ctor_get_uint8(v_cfg_3104_, sizeof(void*)*18 + 8);
v_splitImp_3116_ = lean_ctor_get_uint8(v_cfg_3104_, sizeof(void*)*18 + 9);
v_canonHeartbeats_3117_ = lean_ctor_get(v_cfg_3104_, 6);
v_ext_3118_ = lean_ctor_get_uint8(v_cfg_3104_, sizeof(void*)*18 + 10);
v_extAll_3119_ = lean_ctor_get_uint8(v_cfg_3104_, sizeof(void*)*18 + 11);
v_etaStruct_3120_ = lean_ctor_get_uint8(v_cfg_3104_, sizeof(void*)*18 + 12);
v_funext_3121_ = lean_ctor_get_uint8(v_cfg_3104_, sizeof(void*)*18 + 13);
v_lookahead_3122_ = lean_ctor_get_uint8(v_cfg_3104_, sizeof(void*)*18 + 14);
v_verbose_3123_ = lean_ctor_get_uint8(v_cfg_3104_, sizeof(void*)*18 + 15);
v_clean_3124_ = lean_ctor_get_uint8(v_cfg_3104_, sizeof(void*)*18 + 16);
v_qlia_3125_ = lean_ctor_get_uint8(v_cfg_3104_, sizeof(void*)*18 + 17);
v_mbtc_3126_ = lean_ctor_get_uint8(v_cfg_3104_, sizeof(void*)*18 + 18);
v_zetaDelta_3127_ = lean_ctor_get_uint8(v_cfg_3104_, sizeof(void*)*18 + 19);
v_zeta_3128_ = lean_ctor_get_uint8(v_cfg_3104_, sizeof(void*)*18 + 20);
v_distrib_3129_ = lean_ctor_get_uint8(v_cfg_3104_, sizeof(void*)*18 + 21);
v_maxChar_3130_ = lean_ctor_get(v_cfg_3104_, 7);
v_ring_3131_ = lean_ctor_get_uint8(v_cfg_3104_, sizeof(void*)*18 + 22);
v_ringSteps_3132_ = lean_ctor_get(v_cfg_3104_, 8);
v_ringMaxDegree_3133_ = lean_ctor_get(v_cfg_3104_, 9);
v_linarith_3134_ = lean_ctor_get_uint8(v_cfg_3104_, sizeof(void*)*18 + 23);
v_lia_3135_ = lean_ctor_get_uint8(v_cfg_3104_, sizeof(void*)*18 + 24);
v_liaSteps_3136_ = lean_ctor_get(v_cfg_3104_, 10);
v_liaReorders_3137_ = lean_ctor_get(v_cfg_3104_, 11);
v_liaReorderCases_3138_ = lean_ctor_get(v_cfg_3104_, 12);
v_hom_3139_ = lean_ctor_get_uint8(v_cfg_3104_, sizeof(void*)*18 + 25);
v_ac_3140_ = lean_ctor_get_uint8(v_cfg_3104_, sizeof(void*)*18 + 26);
v_acSteps_3141_ = lean_ctor_get(v_cfg_3104_, 13);
v_exp_3142_ = lean_ctor_get(v_cfg_3104_, 14);
v_abstractProof_3143_ = lean_ctor_get_uint8(v_cfg_3104_, sizeof(void*)*18 + 27);
v_inj_3144_ = lean_ctor_get_uint8(v_cfg_3104_, sizeof(void*)*18 + 28);
v_order_3145_ = lean_ctor_get_uint8(v_cfg_3104_, sizeof(void*)*18 + 29);
v_min_3146_ = lean_ctor_get(v_cfg_3104_, 15);
v_detailed_3147_ = lean_ctor_get(v_cfg_3104_, 16);
v_useSorry_3148_ = lean_ctor_get_uint8(v_cfg_3104_, sizeof(void*)*18 + 30);
v_revert_3149_ = lean_ctor_get_uint8(v_cfg_3104_, sizeof(void*)*18 + 31);
v_funCC_3150_ = lean_ctor_get_uint8(v_cfg_3104_, sizeof(void*)*18 + 32);
v_reducible_3151_ = lean_ctor_get_uint8(v_cfg_3104_, sizeof(void*)*18 + 33);
v_maxSuggestions_3152_ = lean_ctor_get(v_cfg_3104_, 17);
v_isSharedCheck_3161_ = !lean_is_exclusive(v_cfg_3104_);
if (v_isSharedCheck_3161_ == 0)
{
lean_object* v_unused_3162_; lean_object* v_unused_3163_; lean_object* v_unused_3164_; lean_object* v_unused_3165_; 
v_unused_3162_ = lean_ctor_get(v_cfg_3104_, 5);
lean_dec(v_unused_3162_);
v_unused_3163_ = lean_ctor_get(v_cfg_3104_, 4);
lean_dec(v_unused_3163_);
v_unused_3164_ = lean_ctor_get(v_cfg_3104_, 3);
lean_dec(v_unused_3164_);
v_unused_3165_ = lean_ctor_get(v_cfg_3104_, 2);
lean_dec(v_unused_3165_);
v___x_3154_ = v_cfg_3104_;
v_isShared_3155_ = v_isSharedCheck_3161_;
goto v_resetjp_3153_;
}
else
{
lean_inc(v_maxSuggestions_3152_);
lean_inc(v_detailed_3147_);
lean_inc(v_min_3146_);
lean_inc(v_exp_3142_);
lean_inc(v_acSteps_3141_);
lean_inc(v_liaReorderCases_3138_);
lean_inc(v_liaReorders_3137_);
lean_inc(v_liaSteps_3136_);
lean_inc(v_ringMaxDegree_3133_);
lean_inc(v_ringSteps_3132_);
lean_inc(v_maxChar_3130_);
lean_inc(v_canonHeartbeats_3117_);
lean_inc(v_splits_3111_);
lean_inc(v_branches_3110_);
lean_dec(v_cfg_3104_);
v___x_3154_ = lean_box(0);
v_isShared_3155_ = v_isSharedCheck_3161_;
goto v_resetjp_3153_;
}
v_resetjp_3153_:
{
lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3159_; 
v___x_3156_ = lean_unsigned_to_nat(1u);
v___x_3157_ = lean_unsigned_to_nat(20u);
if (v_isShared_3155_ == 0)
{
lean_ctor_set(v___x_3154_, 5, v___x_3157_);
lean_ctor_set(v___x_3154_, 4, v___x_3156_);
lean_ctor_set(v___x_3154_, 3, v___x_3156_);
lean_ctor_set(v___x_3154_, 2, v___x_3156_);
v___x_3159_ = v___x_3154_;
goto v_reusejp_3158_;
}
else
{
lean_object* v_reuseFailAlloc_3160_; 
v_reuseFailAlloc_3160_ = lean_alloc_ctor(0, 18, 34);
lean_ctor_set(v_reuseFailAlloc_3160_, 0, v_branches_3110_);
lean_ctor_set(v_reuseFailAlloc_3160_, 1, v_splits_3111_);
lean_ctor_set(v_reuseFailAlloc_3160_, 2, v___x_3156_);
lean_ctor_set(v_reuseFailAlloc_3160_, 3, v___x_3156_);
lean_ctor_set(v_reuseFailAlloc_3160_, 4, v___x_3156_);
lean_ctor_set(v_reuseFailAlloc_3160_, 5, v___x_3157_);
lean_ctor_set(v_reuseFailAlloc_3160_, 6, v_canonHeartbeats_3117_);
lean_ctor_set(v_reuseFailAlloc_3160_, 7, v_maxChar_3130_);
lean_ctor_set(v_reuseFailAlloc_3160_, 8, v_ringSteps_3132_);
lean_ctor_set(v_reuseFailAlloc_3160_, 9, v_ringMaxDegree_3133_);
lean_ctor_set(v_reuseFailAlloc_3160_, 10, v_liaSteps_3136_);
lean_ctor_set(v_reuseFailAlloc_3160_, 11, v_liaReorders_3137_);
lean_ctor_set(v_reuseFailAlloc_3160_, 12, v_liaReorderCases_3138_);
lean_ctor_set(v_reuseFailAlloc_3160_, 13, v_acSteps_3141_);
lean_ctor_set(v_reuseFailAlloc_3160_, 14, v_exp_3142_);
lean_ctor_set(v_reuseFailAlloc_3160_, 15, v_min_3146_);
lean_ctor_set(v_reuseFailAlloc_3160_, 16, v_detailed_3147_);
lean_ctor_set(v_reuseFailAlloc_3160_, 17, v_maxSuggestions_3152_);
lean_ctor_set_uint8(v_reuseFailAlloc_3160_, sizeof(void*)*18, v_trace_3105_);
lean_ctor_set_uint8(v_reuseFailAlloc_3160_, sizeof(void*)*18 + 1, v_markInstances_3106_);
lean_ctor_set_uint8(v_reuseFailAlloc_3160_, sizeof(void*)*18 + 2, v_lax_3107_);
lean_ctor_set_uint8(v_reuseFailAlloc_3160_, sizeof(void*)*18 + 3, v_suggestions_3108_);
lean_ctor_set_uint8(v_reuseFailAlloc_3160_, sizeof(void*)*18 + 4, v_locals_3109_);
lean_ctor_set_uint8(v_reuseFailAlloc_3160_, sizeof(void*)*18 + 5, v_matchEqs_3112_);
lean_ctor_set_uint8(v_reuseFailAlloc_3160_, sizeof(void*)*18 + 6, v_splitMatch_3113_);
lean_ctor_set_uint8(v_reuseFailAlloc_3160_, sizeof(void*)*18 + 7, v_splitIte_3114_);
lean_ctor_set_uint8(v_reuseFailAlloc_3160_, sizeof(void*)*18 + 8, v_splitIndPred_3115_);
lean_ctor_set_uint8(v_reuseFailAlloc_3160_, sizeof(void*)*18 + 9, v_splitImp_3116_);
lean_ctor_set_uint8(v_reuseFailAlloc_3160_, sizeof(void*)*18 + 10, v_ext_3118_);
lean_ctor_set_uint8(v_reuseFailAlloc_3160_, sizeof(void*)*18 + 11, v_extAll_3119_);
lean_ctor_set_uint8(v_reuseFailAlloc_3160_, sizeof(void*)*18 + 12, v_etaStruct_3120_);
lean_ctor_set_uint8(v_reuseFailAlloc_3160_, sizeof(void*)*18 + 13, v_funext_3121_);
lean_ctor_set_uint8(v_reuseFailAlloc_3160_, sizeof(void*)*18 + 14, v_lookahead_3122_);
lean_ctor_set_uint8(v_reuseFailAlloc_3160_, sizeof(void*)*18 + 15, v_verbose_3123_);
lean_ctor_set_uint8(v_reuseFailAlloc_3160_, sizeof(void*)*18 + 16, v_clean_3124_);
lean_ctor_set_uint8(v_reuseFailAlloc_3160_, sizeof(void*)*18 + 17, v_qlia_3125_);
lean_ctor_set_uint8(v_reuseFailAlloc_3160_, sizeof(void*)*18 + 18, v_mbtc_3126_);
lean_ctor_set_uint8(v_reuseFailAlloc_3160_, sizeof(void*)*18 + 19, v_zetaDelta_3127_);
lean_ctor_set_uint8(v_reuseFailAlloc_3160_, sizeof(void*)*18 + 20, v_zeta_3128_);
lean_ctor_set_uint8(v_reuseFailAlloc_3160_, sizeof(void*)*18 + 21, v_distrib_3129_);
lean_ctor_set_uint8(v_reuseFailAlloc_3160_, sizeof(void*)*18 + 22, v_ring_3131_);
lean_ctor_set_uint8(v_reuseFailAlloc_3160_, sizeof(void*)*18 + 23, v_linarith_3134_);
lean_ctor_set_uint8(v_reuseFailAlloc_3160_, sizeof(void*)*18 + 24, v_lia_3135_);
lean_ctor_set_uint8(v_reuseFailAlloc_3160_, sizeof(void*)*18 + 25, v_hom_3139_);
lean_ctor_set_uint8(v_reuseFailAlloc_3160_, sizeof(void*)*18 + 26, v_ac_3140_);
lean_ctor_set_uint8(v_reuseFailAlloc_3160_, sizeof(void*)*18 + 27, v_abstractProof_3143_);
lean_ctor_set_uint8(v_reuseFailAlloc_3160_, sizeof(void*)*18 + 28, v_inj_3144_);
lean_ctor_set_uint8(v_reuseFailAlloc_3160_, sizeof(void*)*18 + 29, v_order_3145_);
lean_ctor_set_uint8(v_reuseFailAlloc_3160_, sizeof(void*)*18 + 30, v_useSorry_3148_);
lean_ctor_set_uint8(v_reuseFailAlloc_3160_, sizeof(void*)*18 + 31, v_revert_3149_);
lean_ctor_set_uint8(v_reuseFailAlloc_3160_, sizeof(void*)*18 + 32, v_funCC_3150_);
lean_ctor_set_uint8(v_reuseFailAlloc_3160_, sizeof(void*)*18 + 33, v_reducible_3151_);
v___x_3159_ = v_reuseFailAlloc_3160_;
goto v_reusejp_3158_;
}
v_reusejp_3158_:
{
return v___x_3159_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkDefaultDischarger___redArg(lean_object* v_goal_3166_, lean_object* v_a_3167_, lean_object* v_a_3168_, lean_object* v_a_3169_){
_start:
{
lean_object* v_simp_3171_; lean_object* v_simpMethods_3172_; lean_object* v_symSimpMethods_3173_; lean_object* v_symDSimpMethods_3174_; lean_object* v_config_3175_; lean_object* v_identity_3176_; lean_object* v_activeSolvers_3177_; lean_object* v_anchorRefs_x3f_3178_; uint8_t v_anchors_3179_; uint8_t v_cheapCases_3180_; uint8_t v_reportMVarIssue_3181_; lean_object* v_splitSource_3182_; lean_object* v_ematchDiagSource_3183_; lean_object* v_symPrios_3184_; lean_object* v_extensions_3185_; uint8_t v_debug_3186_; uint8_t v_ematchDiag_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; 
v_simp_3171_ = lean_ctor_get(v_a_3168_, 0);
v_simpMethods_3172_ = lean_ctor_get(v_a_3168_, 1);
v_symSimpMethods_3173_ = lean_ctor_get(v_a_3168_, 2);
v_symDSimpMethods_3174_ = lean_ctor_get(v_a_3168_, 3);
v_config_3175_ = lean_ctor_get(v_a_3168_, 4);
v_identity_3176_ = lean_ctor_get(v_a_3168_, 5);
v_activeSolvers_3177_ = lean_ctor_get(v_a_3168_, 6);
v_anchorRefs_x3f_3178_ = lean_ctor_get(v_a_3168_, 7);
v_anchors_3179_ = lean_ctor_get_uint8(v_a_3168_, sizeof(void*)*12);
v_cheapCases_3180_ = lean_ctor_get_uint8(v_a_3168_, sizeof(void*)*12 + 1);
v_reportMVarIssue_3181_ = lean_ctor_get_uint8(v_a_3168_, sizeof(void*)*12 + 2);
v_splitSource_3182_ = lean_ctor_get(v_a_3168_, 8);
v_ematchDiagSource_3183_ = lean_ctor_get(v_a_3168_, 9);
v_symPrios_3184_ = lean_ctor_get(v_a_3168_, 10);
v_extensions_3185_ = lean_ctor_get(v_a_3168_, 11);
v_debug_3186_ = lean_ctor_get_uint8(v_a_3168_, sizeof(void*)*12 + 3);
v_ematchDiag_3187_ = lean_ctor_get_uint8(v_a_3168_, sizeof(void*)*12 + 4);
lean_inc_ref(v_config_3175_);
v___x_3188_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_defaultDischargerConfig(v_config_3175_);
lean_inc_ref(v_extensions_3185_);
lean_inc_ref(v_symPrios_3184_);
lean_inc(v_ematchDiagSource_3183_);
lean_inc(v_splitSource_3182_);
lean_inc(v_anchorRefs_x3f_3178_);
lean_inc_ref(v_activeSolvers_3177_);
lean_inc(v_identity_3176_);
lean_inc_ref(v_symDSimpMethods_3174_);
lean_inc_ref(v_symSimpMethods_3173_);
lean_inc_ref(v_simpMethods_3172_);
lean_inc_ref(v_simp_3171_);
v___x_3189_ = lean_alloc_ctor(0, 12, 5);
lean_ctor_set(v___x_3189_, 0, v_simp_3171_);
lean_ctor_set(v___x_3189_, 1, v_simpMethods_3172_);
lean_ctor_set(v___x_3189_, 2, v_symSimpMethods_3173_);
lean_ctor_set(v___x_3189_, 3, v_symDSimpMethods_3174_);
lean_ctor_set(v___x_3189_, 4, v___x_3188_);
lean_ctor_set(v___x_3189_, 5, v_identity_3176_);
lean_ctor_set(v___x_3189_, 6, v_activeSolvers_3177_);
lean_ctor_set(v___x_3189_, 7, v_anchorRefs_x3f_3178_);
lean_ctor_set(v___x_3189_, 8, v_splitSource_3182_);
lean_ctor_set(v___x_3189_, 9, v_ematchDiagSource_3183_);
lean_ctor_set(v___x_3189_, 10, v_symPrios_3184_);
lean_ctor_set(v___x_3189_, 11, v_extensions_3185_);
lean_ctor_set_uint8(v___x_3189_, sizeof(void*)*12, v_anchors_3179_);
lean_ctor_set_uint8(v___x_3189_, sizeof(void*)*12 + 1, v_cheapCases_3180_);
lean_ctor_set_uint8(v___x_3189_, sizeof(void*)*12 + 2, v_reportMVarIssue_3181_);
lean_ctor_set_uint8(v___x_3189_, sizeof(void*)*12 + 3, v_debug_3186_);
lean_ctor_set_uint8(v___x_3189_, sizeof(void*)*12 + 4, v_ematchDiag_3187_);
v___x_3190_ = l_Lean_Meta_Grind_Goal_mkSymSimpDischarger___redArg(v_goal_3166_, v_a_3167_, v___x_3189_, v_a_3169_);
lean_dec_ref_known(v___x_3189_, 12);
return v___x_3190_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkDefaultDischarger___redArg___boxed(lean_object* v_goal_3191_, lean_object* v_a_3192_, lean_object* v_a_3193_, lean_object* v_a_3194_, lean_object* v_a_3195_){
_start:
{
lean_object* v_res_3196_; 
v_res_3196_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkDefaultDischarger___redArg(v_goal_3191_, v_a_3192_, v_a_3193_, v_a_3194_);
lean_dec(v_a_3194_);
lean_dec_ref(v_a_3193_);
lean_dec(v_a_3192_);
return v_res_3196_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkDefaultDischarger(lean_object* v_goal_3197_, lean_object* v_a_3198_, lean_object* v_a_3199_, lean_object* v_a_3200_, lean_object* v_a_3201_, lean_object* v_a_3202_, lean_object* v_a_3203_, lean_object* v_a_3204_, lean_object* v_a_3205_, lean_object* v_a_3206_){
_start:
{
lean_object* v___x_3208_; 
v___x_3208_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkDefaultDischarger___redArg(v_goal_3197_, v_a_3198_, v_a_3199_, v_a_3200_);
return v___x_3208_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkDefaultDischarger___boxed(lean_object* v_goal_3209_, lean_object* v_a_3210_, lean_object* v_a_3211_, lean_object* v_a_3212_, lean_object* v_a_3213_, lean_object* v_a_3214_, lean_object* v_a_3215_, lean_object* v_a_3216_, lean_object* v_a_3217_, lean_object* v_a_3218_, lean_object* v_a_3219_){
_start:
{
lean_object* v_res_3220_; 
v_res_3220_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkDefaultDischarger(v_goal_3209_, v_a_3210_, v_a_3211_, v_a_3212_, v_a_3213_, v_a_3214_, v_a_3215_, v_a_3216_, v_a_3217_, v_a_3218_);
lean_dec(v_a_3218_);
lean_dec_ref(v_a_3217_);
lean_dec(v_a_3216_);
lean_dec_ref(v_a_3215_);
lean_dec(v_a_3214_);
lean_dec_ref(v_a_3213_);
lean_dec(v_a_3212_);
lean_dec_ref(v_a_3211_);
lean_dec(v_a_3210_);
return v_res_3220_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabSimpVariant___closed__1(void){
_start:
{
lean_object* v___x_3222_; lean_object* v___x_3223_; 
v___x_3222_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabSimpVariant___closed__0));
v___x_3223_ = l_Lean_stringToMessageData(v___x_3222_);
return v___x_3223_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabSimpVariant___closed__3(void){
_start:
{
lean_object* v___x_3225_; lean_object* v___x_3226_; 
v___x_3225_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabSimpVariant___closed__2));
v___x_3226_ = l_Lean_stringToMessageData(v___x_3225_);
return v___x_3226_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabSimpVariant(lean_object* v_variantName_3230_, lean_object* v_extraThms_3231_, lean_object* v_a_3232_, lean_object* v_a_3233_, lean_object* v_a_3234_, lean_object* v_a_3235_, lean_object* v_a_3236_, lean_object* v_a_3237_, lean_object* v_a_3238_, lean_object* v_a_3239_){
_start:
{
uint8_t v___x_3241_; 
v___x_3241_ = l_Lean_Name_isAnonymous(v_variantName_3230_);
if (v___x_3241_ == 0)
{
lean_object* v___x_3242_; lean_object* v_env_3243_; lean_object* v___x_3244_; 
v___x_3242_ = lean_st_ref_get(v_a_3239_);
v_env_3243_ = lean_ctor_get(v___x_3242_, 0);
lean_inc_ref(v_env_3243_);
lean_dec(v___x_3242_);
v___x_3244_ = l_Lean_Meta_Sym_Simp_getSymSimpVariant_x3f(v_env_3243_, v_variantName_3230_);
if (lean_obj_tag(v___x_3244_) == 1)
{
lean_object* v_val_3245_; lean_object* v_pre_x3f_3246_; lean_object* v_post_x3f_3247_; lean_object* v_discharger_x3f_3248_; lean_object* v_config_3249_; lean_object* v___x_3250_; 
lean_dec(v_variantName_3230_);
v_val_3245_ = lean_ctor_get(v___x_3244_, 0);
lean_inc(v_val_3245_);
lean_dec_ref_known(v___x_3244_, 1);
v_pre_x3f_3246_ = lean_ctor_get(v_val_3245_, 0);
lean_inc(v_pre_x3f_3246_);
v_post_x3f_3247_ = lean_ctor_get(v_val_3245_, 1);
lean_inc(v_post_x3f_3247_);
v_discharger_x3f_3248_ = lean_ctor_get(v_val_3245_, 2);
lean_inc(v_discharger_x3f_3248_);
v_config_3249_ = lean_ctor_get(v_val_3245_, 3);
lean_inc_ref(v_config_3249_);
lean_dec(v_val_3245_);
v___x_3250_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabOptSimproc(v_pre_x3f_3246_, v_a_3232_, v_a_3233_, v_a_3234_, v_a_3235_, v_a_3236_, v_a_3237_, v_a_3238_, v_a_3239_);
if (lean_obj_tag(v___x_3250_) == 0)
{
lean_object* v_a_3251_; lean_object* v___x_3252_; 
v_a_3251_ = lean_ctor_get(v___x_3250_, 0);
lean_inc(v_a_3251_);
lean_dec_ref_known(v___x_3250_, 1);
v___x_3252_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabOptSimproc(v_post_x3f_3247_, v_a_3232_, v_a_3233_, v_a_3234_, v_a_3235_, v_a_3236_, v_a_3237_, v_a_3238_, v_a_3239_);
if (lean_obj_tag(v___x_3252_) == 0)
{
lean_object* v_a_3253_; lean_object* v___x_3254_; 
v_a_3253_ = lean_ctor_get(v___x_3252_, 0);
lean_inc(v_a_3253_);
lean_dec_ref_known(v___x_3252_, 1);
v___x_3254_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabOptDischarger(v_discharger_x3f_3248_, v_a_3232_, v_a_3233_, v_a_3234_, v_a_3235_, v_a_3236_, v_a_3237_, v_a_3238_, v_a_3239_);
if (lean_obj_tag(v___x_3254_) == 0)
{
lean_object* v_a_3255_; lean_object* v___x_3256_; 
v_a_3255_ = lean_ctor_get(v___x_3254_, 0);
lean_inc(v_a_3255_);
lean_dec_ref_known(v___x_3254_, 1);
v___x_3256_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems(v_a_3253_, v_extraThms_3231_, v_a_3255_, v_a_3232_, v_a_3233_, v_a_3234_, v_a_3235_, v_a_3236_, v_a_3237_, v_a_3238_, v_a_3239_);
if (lean_obj_tag(v___x_3256_) == 0)
{
lean_object* v_a_3257_; lean_object* v___x_3259_; uint8_t v_isShared_3260_; uint8_t v_isSharedCheck_3266_; 
v_a_3257_ = lean_ctor_get(v___x_3256_, 0);
v_isSharedCheck_3266_ = !lean_is_exclusive(v___x_3256_);
if (v_isSharedCheck_3266_ == 0)
{
v___x_3259_ = v___x_3256_;
v_isShared_3260_ = v_isSharedCheck_3266_;
goto v_resetjp_3258_;
}
else
{
lean_inc(v_a_3257_);
lean_dec(v___x_3256_);
v___x_3259_ = lean_box(0);
v_isShared_3260_ = v_isSharedCheck_3266_;
goto v_resetjp_3258_;
}
v_resetjp_3258_:
{
lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3264_; 
v___x_3261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3261_, 0, v_a_3251_);
lean_ctor_set(v___x_3261_, 1, v_a_3257_);
v___x_3262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3262_, 0, v___x_3261_);
lean_ctor_set(v___x_3262_, 1, v_config_3249_);
if (v_isShared_3260_ == 0)
{
lean_ctor_set(v___x_3259_, 0, v___x_3262_);
v___x_3264_ = v___x_3259_;
goto v_reusejp_3263_;
}
else
{
lean_object* v_reuseFailAlloc_3265_; 
v_reuseFailAlloc_3265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3265_, 0, v___x_3262_);
v___x_3264_ = v_reuseFailAlloc_3265_;
goto v_reusejp_3263_;
}
v_reusejp_3263_:
{
return v___x_3264_;
}
}
}
else
{
lean_object* v_a_3267_; lean_object* v___x_3269_; uint8_t v_isShared_3270_; uint8_t v_isSharedCheck_3274_; 
lean_dec(v_a_3251_);
lean_dec_ref(v_config_3249_);
v_a_3267_ = lean_ctor_get(v___x_3256_, 0);
v_isSharedCheck_3274_ = !lean_is_exclusive(v___x_3256_);
if (v_isSharedCheck_3274_ == 0)
{
v___x_3269_ = v___x_3256_;
v_isShared_3270_ = v_isSharedCheck_3274_;
goto v_resetjp_3268_;
}
else
{
lean_inc(v_a_3267_);
lean_dec(v___x_3256_);
v___x_3269_ = lean_box(0);
v_isShared_3270_ = v_isSharedCheck_3274_;
goto v_resetjp_3268_;
}
v_resetjp_3268_:
{
lean_object* v___x_3272_; 
if (v_isShared_3270_ == 0)
{
v___x_3272_ = v___x_3269_;
goto v_reusejp_3271_;
}
else
{
lean_object* v_reuseFailAlloc_3273_; 
v_reuseFailAlloc_3273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3273_, 0, v_a_3267_);
v___x_3272_ = v_reuseFailAlloc_3273_;
goto v_reusejp_3271_;
}
v_reusejp_3271_:
{
return v___x_3272_;
}
}
}
}
else
{
lean_object* v_a_3275_; lean_object* v___x_3277_; uint8_t v_isShared_3278_; uint8_t v_isSharedCheck_3282_; 
lean_dec(v_a_3253_);
lean_dec(v_a_3251_);
lean_dec_ref(v_config_3249_);
v_a_3275_ = lean_ctor_get(v___x_3254_, 0);
v_isSharedCheck_3282_ = !lean_is_exclusive(v___x_3254_);
if (v_isSharedCheck_3282_ == 0)
{
v___x_3277_ = v___x_3254_;
v_isShared_3278_ = v_isSharedCheck_3282_;
goto v_resetjp_3276_;
}
else
{
lean_inc(v_a_3275_);
lean_dec(v___x_3254_);
v___x_3277_ = lean_box(0);
v_isShared_3278_ = v_isSharedCheck_3282_;
goto v_resetjp_3276_;
}
v_resetjp_3276_:
{
lean_object* v___x_3280_; 
if (v_isShared_3278_ == 0)
{
v___x_3280_ = v___x_3277_;
goto v_reusejp_3279_;
}
else
{
lean_object* v_reuseFailAlloc_3281_; 
v_reuseFailAlloc_3281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3281_, 0, v_a_3275_);
v___x_3280_ = v_reuseFailAlloc_3281_;
goto v_reusejp_3279_;
}
v_reusejp_3279_:
{
return v___x_3280_;
}
}
}
}
else
{
lean_object* v_a_3283_; lean_object* v___x_3285_; uint8_t v_isShared_3286_; uint8_t v_isSharedCheck_3290_; 
lean_dec(v_a_3251_);
lean_dec_ref(v_config_3249_);
lean_dec(v_discharger_x3f_3248_);
v_a_3283_ = lean_ctor_get(v___x_3252_, 0);
v_isSharedCheck_3290_ = !lean_is_exclusive(v___x_3252_);
if (v_isSharedCheck_3290_ == 0)
{
v___x_3285_ = v___x_3252_;
v_isShared_3286_ = v_isSharedCheck_3290_;
goto v_resetjp_3284_;
}
else
{
lean_inc(v_a_3283_);
lean_dec(v___x_3252_);
v___x_3285_ = lean_box(0);
v_isShared_3286_ = v_isSharedCheck_3290_;
goto v_resetjp_3284_;
}
v_resetjp_3284_:
{
lean_object* v___x_3288_; 
if (v_isShared_3286_ == 0)
{
v___x_3288_ = v___x_3285_;
goto v_reusejp_3287_;
}
else
{
lean_object* v_reuseFailAlloc_3289_; 
v_reuseFailAlloc_3289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3289_, 0, v_a_3283_);
v___x_3288_ = v_reuseFailAlloc_3289_;
goto v_reusejp_3287_;
}
v_reusejp_3287_:
{
return v___x_3288_;
}
}
}
}
else
{
lean_object* v_a_3291_; lean_object* v___x_3293_; uint8_t v_isShared_3294_; uint8_t v_isSharedCheck_3298_; 
lean_dec_ref(v_config_3249_);
lean_dec(v_discharger_x3f_3248_);
lean_dec(v_post_x3f_3247_);
v_a_3291_ = lean_ctor_get(v___x_3250_, 0);
v_isSharedCheck_3298_ = !lean_is_exclusive(v___x_3250_);
if (v_isSharedCheck_3298_ == 0)
{
v___x_3293_ = v___x_3250_;
v_isShared_3294_ = v_isSharedCheck_3298_;
goto v_resetjp_3292_;
}
else
{
lean_inc(v_a_3291_);
lean_dec(v___x_3250_);
v___x_3293_ = lean_box(0);
v_isShared_3294_ = v_isSharedCheck_3298_;
goto v_resetjp_3292_;
}
v_resetjp_3292_:
{
lean_object* v___x_3296_; 
if (v_isShared_3294_ == 0)
{
v___x_3296_ = v___x_3293_;
goto v_reusejp_3295_;
}
else
{
lean_object* v_reuseFailAlloc_3297_; 
v_reuseFailAlloc_3297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3297_, 0, v_a_3291_);
v___x_3296_ = v_reuseFailAlloc_3297_;
goto v_reusejp_3295_;
}
v_reusejp_3295_:
{
return v___x_3296_;
}
}
}
}
else
{
lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; 
lean_dec(v___x_3244_);
v___x_3299_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabSimpVariant___closed__1, &l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabSimpVariant___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabSimpVariant___closed__1);
v___x_3300_ = l_Lean_MessageData_ofName(v_variantName_3230_);
v___x_3301_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3301_, 0, v___x_3299_);
lean_ctor_set(v___x_3301_, 1, v___x_3300_);
v___x_3302_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabSimpVariant___closed__3, &l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabSimpVariant___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabSimpVariant___closed__3);
v___x_3303_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3303_, 0, v___x_3301_);
lean_ctor_set(v___x_3303_, 1, v___x_3302_);
v___x_3304_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__2___redArg(v___x_3303_, v_a_3236_, v_a_3237_, v_a_3238_, v_a_3239_);
return v___x_3304_;
}
}
else
{
lean_object* v___x_3305_; 
lean_dec(v_variantName_3230_);
v___x_3305_ = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(v_a_3233_, v_a_3236_, v_a_3237_, v_a_3238_, v_a_3239_);
if (lean_obj_tag(v___x_3305_) == 0)
{
lean_object* v_a_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; 
v_a_3306_ = lean_ctor_get(v___x_3305_, 0);
lean_inc(v_a_3306_);
lean_dec_ref_known(v___x_3305_, 1);
v___x_3307_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkDefaultDischarger___boxed), 11, 1);
lean_closure_set(v___x_3307_, 0, v_a_3306_);
v___x_3308_ = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(v___x_3307_, v_a_3232_, v_a_3233_, v_a_3236_, v_a_3237_, v_a_3238_, v_a_3239_);
if (lean_obj_tag(v___x_3308_) == 0)
{
lean_object* v_a_3309_; lean_object* v___x_3310_; 
v_a_3309_ = lean_ctor_get(v___x_3308_, 0);
lean_inc(v_a_3309_);
lean_dec_ref_known(v___x_3308_, 1);
v___x_3310_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkSimpDefaultMethods(v_extraThms_3231_, v_a_3309_, v_a_3232_, v_a_3233_, v_a_3234_, v_a_3235_, v_a_3236_, v_a_3237_, v_a_3238_, v_a_3239_);
if (lean_obj_tag(v___x_3310_) == 0)
{
lean_object* v_a_3311_; lean_object* v___x_3313_; uint8_t v_isShared_3314_; uint8_t v_isSharedCheck_3320_; 
v_a_3311_ = lean_ctor_get(v___x_3310_, 0);
v_isSharedCheck_3320_ = !lean_is_exclusive(v___x_3310_);
if (v_isSharedCheck_3320_ == 0)
{
v___x_3313_ = v___x_3310_;
v_isShared_3314_ = v_isSharedCheck_3320_;
goto v_resetjp_3312_;
}
else
{
lean_inc(v_a_3311_);
lean_dec(v___x_3310_);
v___x_3313_ = lean_box(0);
v_isShared_3314_ = v_isSharedCheck_3320_;
goto v_resetjp_3312_;
}
v_resetjp_3312_:
{
lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3318_; 
v___x_3315_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabSimpVariant___closed__4));
v___x_3316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3316_, 0, v_a_3311_);
lean_ctor_set(v___x_3316_, 1, v___x_3315_);
if (v_isShared_3314_ == 0)
{
lean_ctor_set(v___x_3313_, 0, v___x_3316_);
v___x_3318_ = v___x_3313_;
goto v_reusejp_3317_;
}
else
{
lean_object* v_reuseFailAlloc_3319_; 
v_reuseFailAlloc_3319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3319_, 0, v___x_3316_);
v___x_3318_ = v_reuseFailAlloc_3319_;
goto v_reusejp_3317_;
}
v_reusejp_3317_:
{
return v___x_3318_;
}
}
}
else
{
lean_object* v_a_3321_; lean_object* v___x_3323_; uint8_t v_isShared_3324_; uint8_t v_isSharedCheck_3328_; 
v_a_3321_ = lean_ctor_get(v___x_3310_, 0);
v_isSharedCheck_3328_ = !lean_is_exclusive(v___x_3310_);
if (v_isSharedCheck_3328_ == 0)
{
v___x_3323_ = v___x_3310_;
v_isShared_3324_ = v_isSharedCheck_3328_;
goto v_resetjp_3322_;
}
else
{
lean_inc(v_a_3321_);
lean_dec(v___x_3310_);
v___x_3323_ = lean_box(0);
v_isShared_3324_ = v_isSharedCheck_3328_;
goto v_resetjp_3322_;
}
v_resetjp_3322_:
{
lean_object* v___x_3326_; 
if (v_isShared_3324_ == 0)
{
v___x_3326_ = v___x_3323_;
goto v_reusejp_3325_;
}
else
{
lean_object* v_reuseFailAlloc_3327_; 
v_reuseFailAlloc_3327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3327_, 0, v_a_3321_);
v___x_3326_ = v_reuseFailAlloc_3327_;
goto v_reusejp_3325_;
}
v_reusejp_3325_:
{
return v___x_3326_;
}
}
}
}
else
{
lean_object* v_a_3329_; lean_object* v___x_3331_; uint8_t v_isShared_3332_; uint8_t v_isSharedCheck_3336_; 
v_a_3329_ = lean_ctor_get(v___x_3308_, 0);
v_isSharedCheck_3336_ = !lean_is_exclusive(v___x_3308_);
if (v_isSharedCheck_3336_ == 0)
{
v___x_3331_ = v___x_3308_;
v_isShared_3332_ = v_isSharedCheck_3336_;
goto v_resetjp_3330_;
}
else
{
lean_inc(v_a_3329_);
lean_dec(v___x_3308_);
v___x_3331_ = lean_box(0);
v_isShared_3332_ = v_isSharedCheck_3336_;
goto v_resetjp_3330_;
}
v_resetjp_3330_:
{
lean_object* v___x_3334_; 
if (v_isShared_3332_ == 0)
{
v___x_3334_ = v___x_3331_;
goto v_reusejp_3333_;
}
else
{
lean_object* v_reuseFailAlloc_3335_; 
v_reuseFailAlloc_3335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3335_, 0, v_a_3329_);
v___x_3334_ = v_reuseFailAlloc_3335_;
goto v_reusejp_3333_;
}
v_reusejp_3333_:
{
return v___x_3334_;
}
}
}
}
else
{
lean_object* v_a_3337_; lean_object* v___x_3339_; uint8_t v_isShared_3340_; uint8_t v_isSharedCheck_3344_; 
v_a_3337_ = lean_ctor_get(v___x_3305_, 0);
v_isSharedCheck_3344_ = !lean_is_exclusive(v___x_3305_);
if (v_isSharedCheck_3344_ == 0)
{
v___x_3339_ = v___x_3305_;
v_isShared_3340_ = v_isSharedCheck_3344_;
goto v_resetjp_3338_;
}
else
{
lean_inc(v_a_3337_);
lean_dec(v___x_3305_);
v___x_3339_ = lean_box(0);
v_isShared_3340_ = v_isSharedCheck_3344_;
goto v_resetjp_3338_;
}
v_resetjp_3338_:
{
lean_object* v___x_3342_; 
if (v_isShared_3340_ == 0)
{
v___x_3342_ = v___x_3339_;
goto v_reusejp_3341_;
}
else
{
lean_object* v_reuseFailAlloc_3343_; 
v_reuseFailAlloc_3343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3343_, 0, v_a_3337_);
v___x_3342_ = v_reuseFailAlloc_3343_;
goto v_reusejp_3341_;
}
v_reusejp_3341_:
{
return v___x_3342_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabSimpVariant___boxed(lean_object* v_variantName_3345_, lean_object* v_extraThms_3346_, lean_object* v_a_3347_, lean_object* v_a_3348_, lean_object* v_a_3349_, lean_object* v_a_3350_, lean_object* v_a_3351_, lean_object* v_a_3352_, lean_object* v_a_3353_, lean_object* v_a_3354_, lean_object* v_a_3355_){
_start:
{
lean_object* v_res_3356_; 
v_res_3356_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabSimpVariant(v_variantName_3345_, v_extraThms_3346_, v_a_3347_, v_a_3348_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_, v_a_3353_, v_a_3354_);
lean_dec(v_a_3354_);
lean_dec_ref(v_a_3353_);
lean_dec(v_a_3352_);
lean_dec_ref(v_a_3351_);
lean_dec(v_a_3350_);
lean_dec_ref(v_a_3349_);
lean_dec(v_a_3348_);
lean_dec_ref(v_a_3347_);
lean_dec_ref(v_extraThms_3346_);
return v_res_3356_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__0___redArg___lam__0(lean_object* v_x_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_, lean_object* v___y_3360_, lean_object* v___y_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_){
_start:
{
lean_object* v___x_3368_; 
lean_inc(v___y_3362_);
lean_inc_ref(v___y_3361_);
lean_inc(v___y_3360_);
lean_inc_ref(v___y_3359_);
lean_inc(v___y_3358_);
v___x_3368_ = lean_apply_10(v_x_3357_, v___y_3358_, v___y_3359_, v___y_3360_, v___y_3361_, v___y_3362_, v___y_3363_, v___y_3364_, v___y_3365_, v___y_3366_, lean_box(0));
return v___x_3368_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__0___redArg___lam__0___boxed(lean_object* v_x_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_){
_start:
{
lean_object* v_res_3380_; 
v_res_3380_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__0___redArg___lam__0(v_x_3369_, v___y_3370_, v___y_3371_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_, v___y_3376_, v___y_3377_, v___y_3378_);
lean_dec(v___y_3374_);
lean_dec_ref(v___y_3373_);
lean_dec(v___y_3372_);
lean_dec_ref(v___y_3371_);
lean_dec(v___y_3370_);
return v_res_3380_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__0___redArg(lean_object* v_mvarId_3381_, lean_object* v_x_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_){
_start:
{
lean_object* v___f_3393_; lean_object* v___x_3394_; 
lean_inc(v___y_3387_);
lean_inc_ref(v___y_3386_);
lean_inc(v___y_3385_);
lean_inc_ref(v___y_3384_);
lean_inc(v___y_3383_);
v___f_3393_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__0___redArg___lam__0___boxed), 11, 6);
lean_closure_set(v___f_3393_, 0, v_x_3382_);
lean_closure_set(v___f_3393_, 1, v___y_3383_);
lean_closure_set(v___f_3393_, 2, v___y_3384_);
lean_closure_set(v___f_3393_, 3, v___y_3385_);
lean_closure_set(v___f_3393_, 4, v___y_3386_);
lean_closure_set(v___f_3393_, 5, v___y_3387_);
v___x_3394_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_3381_, v___f_3393_, v___y_3388_, v___y_3389_, v___y_3390_, v___y_3391_);
if (lean_obj_tag(v___x_3394_) == 0)
{
return v___x_3394_;
}
else
{
lean_object* v_a_3395_; lean_object* v___x_3397_; uint8_t v_isShared_3398_; uint8_t v_isSharedCheck_3402_; 
v_a_3395_ = lean_ctor_get(v___x_3394_, 0);
v_isSharedCheck_3402_ = !lean_is_exclusive(v___x_3394_);
if (v_isSharedCheck_3402_ == 0)
{
v___x_3397_ = v___x_3394_;
v_isShared_3398_ = v_isSharedCheck_3402_;
goto v_resetjp_3396_;
}
else
{
lean_inc(v_a_3395_);
lean_dec(v___x_3394_);
v___x_3397_ = lean_box(0);
v_isShared_3398_ = v_isSharedCheck_3402_;
goto v_resetjp_3396_;
}
v_resetjp_3396_:
{
lean_object* v___x_3400_; 
if (v_isShared_3398_ == 0)
{
v___x_3400_ = v___x_3397_;
goto v_reusejp_3399_;
}
else
{
lean_object* v_reuseFailAlloc_3401_; 
v_reuseFailAlloc_3401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3401_, 0, v_a_3395_);
v___x_3400_ = v_reuseFailAlloc_3401_;
goto v_reusejp_3399_;
}
v_reusejp_3399_:
{
return v___x_3400_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__0___redArg___boxed(lean_object* v_mvarId_3403_, lean_object* v_x_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_){
_start:
{
lean_object* v_res_3415_; 
v_res_3415_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__0___redArg(v_mvarId_3403_, v_x_3404_, v___y_3405_, v___y_3406_, v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_, v___y_3412_, v___y_3413_);
lean_dec(v___y_3413_);
lean_dec_ref(v___y_3412_);
lean_dec(v___y_3411_);
lean_dec_ref(v___y_3410_);
lean_dec(v___y_3409_);
lean_dec_ref(v___y_3408_);
lean_dec(v___y_3407_);
lean_dec_ref(v___y_3406_);
lean_dec(v___y_3405_);
return v_res_3415_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__0(lean_object* v_00_u03b1_3416_, lean_object* v_mvarId_3417_, lean_object* v_x_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_){
_start:
{
lean_object* v___x_3429_; 
v___x_3429_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__0___redArg(v_mvarId_3417_, v_x_3418_, v___y_3419_, v___y_3420_, v___y_3421_, v___y_3422_, v___y_3423_, v___y_3424_, v___y_3425_, v___y_3426_, v___y_3427_);
return v___x_3429_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__0___boxed(lean_object* v_00_u03b1_3430_, lean_object* v_mvarId_3431_, lean_object* v_x_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_){
_start:
{
lean_object* v_res_3443_; 
v_res_3443_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__0(v_00_u03b1_3430_, v_mvarId_3431_, v_x_3432_, v___y_3433_, v___y_3434_, v___y_3435_, v___y_3436_, v___y_3437_, v___y_3438_, v___y_3439_, v___y_3440_, v___y_3441_);
lean_dec(v___y_3441_);
lean_dec_ref(v___y_3440_);
lean_dec(v___y_3439_);
lean_dec_ref(v___y_3438_);
lean_dec(v___y_3437_);
lean_dec_ref(v___y_3436_);
lean_dec(v___y_3435_);
lean_dec_ref(v___y_3434_);
lean_dec(v___y_3433_);
return v_res_3443_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__0(lean_object* v_mvarId_3444_, lean_object* v_fst_3445_, lean_object* v_snd_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_, lean_object* v___y_3451_, lean_object* v___y_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_){
_start:
{
lean_object* v___x_3458_; 
v___x_3458_ = l_Lean_MVarId_getType(v_mvarId_3444_, v___y_3453_, v___y_3454_, v___y_3455_, v___y_3456_);
if (lean_obj_tag(v___x_3458_) == 0)
{
lean_object* v_a_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; 
v_a_3459_ = lean_ctor_get(v___x_3458_, 0);
lean_inc(v_a_3459_);
lean_dec_ref_known(v___x_3458_, 1);
v___x_3460_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simp___boxed), 11, 1);
lean_closure_set(v___x_3460_, 0, v_a_3459_);
v___x_3461_ = l_Lean_Meta_Sym_Simp_SimpM_run___redArg(v___x_3460_, v_fst_3445_, v_snd_3446_, v___y_3447_, v___y_3451_, v___y_3452_, v___y_3453_, v___y_3454_, v___y_3455_, v___y_3456_);
return v___x_3461_;
}
else
{
lean_object* v_a_3462_; lean_object* v___x_3464_; uint8_t v_isShared_3465_; uint8_t v_isSharedCheck_3469_; 
lean_dec_ref(v___y_3447_);
lean_dec_ref(v_snd_3446_);
lean_dec_ref(v_fst_3445_);
v_a_3462_ = lean_ctor_get(v___x_3458_, 0);
v_isSharedCheck_3469_ = !lean_is_exclusive(v___x_3458_);
if (v_isSharedCheck_3469_ == 0)
{
v___x_3464_ = v___x_3458_;
v_isShared_3465_ = v_isSharedCheck_3469_;
goto v_resetjp_3463_;
}
else
{
lean_inc(v_a_3462_);
lean_dec(v___x_3458_);
v___x_3464_ = lean_box(0);
v_isShared_3465_ = v_isSharedCheck_3469_;
goto v_resetjp_3463_;
}
v_resetjp_3463_:
{
lean_object* v___x_3467_; 
if (v_isShared_3465_ == 0)
{
v___x_3467_ = v___x_3464_;
goto v_reusejp_3466_;
}
else
{
lean_object* v_reuseFailAlloc_3468_; 
v_reuseFailAlloc_3468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3468_, 0, v_a_3462_);
v___x_3467_ = v_reuseFailAlloc_3468_;
goto v_reusejp_3466_;
}
v_reusejp_3466_:
{
return v___x_3467_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__0___boxed(lean_object* v_mvarId_3470_, lean_object* v_fst_3471_, lean_object* v_snd_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_, lean_object* v___y_3478_, lean_object* v___y_3479_, lean_object* v___y_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_){
_start:
{
lean_object* v_res_3484_; 
v_res_3484_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__0(v_mvarId_3470_, v_fst_3471_, v_snd_3472_, v___y_3473_, v___y_3474_, v___y_3475_, v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_, v___y_3480_, v___y_3481_, v___y_3482_);
lean_dec(v___y_3482_);
lean_dec_ref(v___y_3481_);
lean_dec(v___y_3480_);
lean_dec_ref(v___y_3479_);
lean_dec(v___y_3478_);
lean_dec_ref(v___y_3477_);
lean_dec(v___y_3476_);
lean_dec_ref(v___y_3475_);
lean_dec(v___y_3474_);
return v_res_3484_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__1(lean_object* v_fst_3485_, lean_object* v_mvarId_3486_, lean_object* v___y_3487_, lean_object* v___y_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_){
_start:
{
lean_object* v___x_3497_; 
v___x_3497_ = l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult(v_fst_3485_, v_mvarId_3486_, v___y_3490_, v___y_3491_, v___y_3492_, v___y_3493_, v___y_3494_, v___y_3495_);
return v___x_3497_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__1___boxed(lean_object* v_fst_3498_, lean_object* v_mvarId_3499_, lean_object* v___y_3500_, lean_object* v___y_3501_, lean_object* v___y_3502_, lean_object* v___y_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_){
_start:
{
lean_object* v_res_3510_; 
v_res_3510_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__1(v_fst_3498_, v_mvarId_3499_, v___y_3500_, v___y_3501_, v___y_3502_, v___y_3503_, v___y_3504_, v___y_3505_, v___y_3506_, v___y_3507_, v___y_3508_);
lean_dec(v___y_3508_);
lean_dec_ref(v___y_3507_);
lean_dec(v___y_3506_);
lean_dec_ref(v___y_3505_);
lean_dec(v___y_3504_);
lean_dec_ref(v___y_3503_);
lean_dec(v___y_3502_);
lean_dec_ref(v___y_3501_);
lean_dec(v___y_3500_);
return v_res_3510_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__2_spec__5___redArg(lean_object* v_a_3511_, lean_object* v_x_3512_){
_start:
{
if (lean_obj_tag(v_x_3512_) == 0)
{
lean_object* v___x_3513_; 
v___x_3513_ = lean_box(0);
return v___x_3513_;
}
else
{
lean_object* v_key_3514_; lean_object* v_value_3515_; lean_object* v_tail_3516_; uint8_t v___x_3517_; 
v_key_3514_ = lean_ctor_get(v_x_3512_, 0);
v_value_3515_ = lean_ctor_get(v_x_3512_, 1);
v_tail_3516_ = lean_ctor_get(v_x_3512_, 2);
v___x_3517_ = l_Lean_Elab_Tactic_Grind_instBEqSimpCacheKey_beq(v_key_3514_, v_a_3511_);
if (v___x_3517_ == 0)
{
v_x_3512_ = v_tail_3516_;
goto _start;
}
else
{
lean_object* v___x_3519_; 
lean_inc(v_value_3515_);
v___x_3519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3519_, 0, v_value_3515_);
return v___x_3519_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__2_spec__5___redArg___boxed(lean_object* v_a_3520_, lean_object* v_x_3521_){
_start:
{
lean_object* v_res_3522_; 
v_res_3522_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__2_spec__5___redArg(v_a_3520_, v_x_3521_);
lean_dec(v_x_3521_);
lean_dec_ref(v_a_3520_);
return v_res_3522_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__2___redArg(lean_object* v_m_3523_, lean_object* v_a_3524_){
_start:
{
lean_object* v_buckets_3525_; lean_object* v___x_3526_; uint64_t v___x_3527_; uint64_t v___x_3528_; uint64_t v___x_3529_; uint64_t v_fold_3530_; uint64_t v___x_3531_; uint64_t v___x_3532_; uint64_t v___x_3533_; size_t v___x_3534_; size_t v___x_3535_; size_t v___x_3536_; size_t v___x_3537_; size_t v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; 
v_buckets_3525_ = lean_ctor_get(v_m_3523_, 1);
v___x_3526_ = lean_array_get_size(v_buckets_3525_);
v___x_3527_ = l_Lean_Elab_Tactic_Grind_instHashableSimpCacheKey_hash(v_a_3524_);
v___x_3528_ = 32ULL;
v___x_3529_ = lean_uint64_shift_right(v___x_3527_, v___x_3528_);
v_fold_3530_ = lean_uint64_xor(v___x_3527_, v___x_3529_);
v___x_3531_ = 16ULL;
v___x_3532_ = lean_uint64_shift_right(v_fold_3530_, v___x_3531_);
v___x_3533_ = lean_uint64_xor(v_fold_3530_, v___x_3532_);
v___x_3534_ = lean_uint64_to_usize(v___x_3533_);
v___x_3535_ = lean_usize_of_nat(v___x_3526_);
v___x_3536_ = ((size_t)1ULL);
v___x_3537_ = lean_usize_sub(v___x_3535_, v___x_3536_);
v___x_3538_ = lean_usize_land(v___x_3534_, v___x_3537_);
v___x_3539_ = lean_array_uget_borrowed(v_buckets_3525_, v___x_3538_);
v___x_3540_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__2_spec__5___redArg(v_a_3524_, v___x_3539_);
return v___x_3540_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__2___redArg___boxed(lean_object* v_m_3541_, lean_object* v_a_3542_){
_start:
{
lean_object* v_res_3543_; 
v_res_3543_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__2___redArg(v_m_3541_, v_a_3542_);
lean_dec_ref(v_a_3542_);
lean_dec_ref(v_m_3541_);
return v_res_3543_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__4(uint8_t v___x_3544_, uint8_t v___x_3545_, lean_object* v_as_3546_, size_t v_i_3547_, size_t v_stop_3548_, lean_object* v_b_3549_){
_start:
{
lean_object* v___y_3551_; uint8_t v___x_3555_; 
v___x_3555_ = lean_usize_dec_eq(v_i_3547_, v_stop_3548_);
if (v___x_3555_ == 0)
{
lean_object* v_fst_3556_; uint8_t v___x_3557_; 
v_fst_3556_ = lean_ctor_get(v_b_3549_, 0);
v___x_3557_ = lean_unbox(v_fst_3556_);
if (v___x_3557_ == 0)
{
lean_object* v_snd_3558_; lean_object* v___x_3560_; uint8_t v_isShared_3561_; uint8_t v_isSharedCheck_3566_; 
v_snd_3558_ = lean_ctor_get(v_b_3549_, 1);
v_isSharedCheck_3566_ = !lean_is_exclusive(v_b_3549_);
if (v_isSharedCheck_3566_ == 0)
{
lean_object* v_unused_3567_; 
v_unused_3567_ = lean_ctor_get(v_b_3549_, 0);
lean_dec(v_unused_3567_);
v___x_3560_ = v_b_3549_;
v_isShared_3561_ = v_isSharedCheck_3566_;
goto v_resetjp_3559_;
}
else
{
lean_inc(v_snd_3558_);
lean_dec(v_b_3549_);
v___x_3560_ = lean_box(0);
v_isShared_3561_ = v_isSharedCheck_3566_;
goto v_resetjp_3559_;
}
v_resetjp_3559_:
{
lean_object* v___x_3562_; lean_object* v___x_3564_; 
v___x_3562_ = lean_box(v___x_3544_);
if (v_isShared_3561_ == 0)
{
lean_ctor_set(v___x_3560_, 0, v___x_3562_);
v___x_3564_ = v___x_3560_;
goto v_reusejp_3563_;
}
else
{
lean_object* v_reuseFailAlloc_3565_; 
v_reuseFailAlloc_3565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3565_, 0, v___x_3562_);
lean_ctor_set(v_reuseFailAlloc_3565_, 1, v_snd_3558_);
v___x_3564_ = v_reuseFailAlloc_3565_;
goto v_reusejp_3563_;
}
v_reusejp_3563_:
{
v___y_3551_ = v___x_3564_;
goto v___jp_3550_;
}
}
}
else
{
lean_object* v_snd_3568_; lean_object* v___x_3570_; uint8_t v_isShared_3571_; uint8_t v_isSharedCheck_3578_; 
v_snd_3568_ = lean_ctor_get(v_b_3549_, 1);
v_isSharedCheck_3578_ = !lean_is_exclusive(v_b_3549_);
if (v_isSharedCheck_3578_ == 0)
{
lean_object* v_unused_3579_; 
v_unused_3579_ = lean_ctor_get(v_b_3549_, 0);
lean_dec(v_unused_3579_);
v___x_3570_ = v_b_3549_;
v_isShared_3571_ = v_isSharedCheck_3578_;
goto v_resetjp_3569_;
}
else
{
lean_inc(v_snd_3568_);
lean_dec(v_b_3549_);
v___x_3570_ = lean_box(0);
v_isShared_3571_ = v_isSharedCheck_3578_;
goto v_resetjp_3569_;
}
v_resetjp_3569_:
{
lean_object* v___x_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3576_; 
v___x_3572_ = lean_array_uget_borrowed(v_as_3546_, v_i_3547_);
lean_inc(v___x_3572_);
v___x_3573_ = lean_array_push(v_snd_3568_, v___x_3572_);
v___x_3574_ = lean_box(v___x_3545_);
if (v_isShared_3571_ == 0)
{
lean_ctor_set(v___x_3570_, 1, v___x_3573_);
lean_ctor_set(v___x_3570_, 0, v___x_3574_);
v___x_3576_ = v___x_3570_;
goto v_reusejp_3575_;
}
else
{
lean_object* v_reuseFailAlloc_3577_; 
v_reuseFailAlloc_3577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3577_, 0, v___x_3574_);
lean_ctor_set(v_reuseFailAlloc_3577_, 1, v___x_3573_);
v___x_3576_ = v_reuseFailAlloc_3577_;
goto v_reusejp_3575_;
}
v_reusejp_3575_:
{
v___y_3551_ = v___x_3576_;
goto v___jp_3550_;
}
}
}
}
else
{
return v_b_3549_;
}
v___jp_3550_:
{
size_t v___x_3552_; size_t v___x_3553_; 
v___x_3552_ = ((size_t)1ULL);
v___x_3553_ = lean_usize_add(v_i_3547_, v___x_3552_);
v_i_3547_ = v___x_3553_;
v_b_3549_ = v___y_3551_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__4___boxed(lean_object* v___x_3580_, lean_object* v___x_3581_, lean_object* v_as_3582_, lean_object* v_i_3583_, lean_object* v_stop_3584_, lean_object* v_b_3585_){
_start:
{
uint8_t v___x_7542__boxed_3586_; uint8_t v___x_7543__boxed_3587_; size_t v_i_boxed_3588_; size_t v_stop_boxed_3589_; lean_object* v_res_3590_; 
v___x_7542__boxed_3586_ = lean_unbox(v___x_3580_);
v___x_7543__boxed_3587_ = lean_unbox(v___x_3581_);
v_i_boxed_3588_ = lean_unbox_usize(v_i_3583_);
lean_dec(v_i_3583_);
v_stop_boxed_3589_ = lean_unbox_usize(v_stop_3584_);
lean_dec(v_stop_3584_);
v_res_3590_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__4(v___x_7542__boxed_3586_, v___x_7543__boxed_3587_, v_as_3582_, v_i_boxed_3588_, v_stop_boxed_3589_, v_b_3585_);
lean_dec_ref(v_as_3582_);
return v_res_3590_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__3___redArg(lean_object* v_a_3591_, lean_object* v_b_3592_, lean_object* v_x_3593_){
_start:
{
if (lean_obj_tag(v_x_3593_) == 0)
{
lean_dec(v_b_3592_);
lean_dec_ref(v_a_3591_);
return v_x_3593_;
}
else
{
lean_object* v_key_3594_; lean_object* v_value_3595_; lean_object* v_tail_3596_; lean_object* v___x_3598_; uint8_t v_isShared_3599_; uint8_t v_isSharedCheck_3608_; 
v_key_3594_ = lean_ctor_get(v_x_3593_, 0);
v_value_3595_ = lean_ctor_get(v_x_3593_, 1);
v_tail_3596_ = lean_ctor_get(v_x_3593_, 2);
v_isSharedCheck_3608_ = !lean_is_exclusive(v_x_3593_);
if (v_isSharedCheck_3608_ == 0)
{
v___x_3598_ = v_x_3593_;
v_isShared_3599_ = v_isSharedCheck_3608_;
goto v_resetjp_3597_;
}
else
{
lean_inc(v_tail_3596_);
lean_inc(v_value_3595_);
lean_inc(v_key_3594_);
lean_dec(v_x_3593_);
v___x_3598_ = lean_box(0);
v_isShared_3599_ = v_isSharedCheck_3608_;
goto v_resetjp_3597_;
}
v_resetjp_3597_:
{
uint8_t v___x_3600_; 
v___x_3600_ = l_Lean_Elab_Tactic_Grind_instBEqSimpCacheKey_beq(v_key_3594_, v_a_3591_);
if (v___x_3600_ == 0)
{
lean_object* v___x_3601_; lean_object* v___x_3603_; 
v___x_3601_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__3___redArg(v_a_3591_, v_b_3592_, v_tail_3596_);
if (v_isShared_3599_ == 0)
{
lean_ctor_set(v___x_3598_, 2, v___x_3601_);
v___x_3603_ = v___x_3598_;
goto v_reusejp_3602_;
}
else
{
lean_object* v_reuseFailAlloc_3604_; 
v_reuseFailAlloc_3604_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3604_, 0, v_key_3594_);
lean_ctor_set(v_reuseFailAlloc_3604_, 1, v_value_3595_);
lean_ctor_set(v_reuseFailAlloc_3604_, 2, v___x_3601_);
v___x_3603_ = v_reuseFailAlloc_3604_;
goto v_reusejp_3602_;
}
v_reusejp_3602_:
{
return v___x_3603_;
}
}
else
{
lean_object* v___x_3606_; 
lean_dec(v_value_3595_);
lean_dec(v_key_3594_);
if (v_isShared_3599_ == 0)
{
lean_ctor_set(v___x_3598_, 1, v_b_3592_);
lean_ctor_set(v___x_3598_, 0, v_a_3591_);
v___x_3606_ = v___x_3598_;
goto v_reusejp_3605_;
}
else
{
lean_object* v_reuseFailAlloc_3607_; 
v_reuseFailAlloc_3607_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3607_, 0, v_a_3591_);
lean_ctor_set(v_reuseFailAlloc_3607_, 1, v_b_3592_);
lean_ctor_set(v_reuseFailAlloc_3607_, 2, v_tail_3596_);
v___x_3606_ = v_reuseFailAlloc_3607_;
goto v_reusejp_3605_;
}
v_reusejp_3605_:
{
return v___x_3606_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__2_spec__3_spec__7___redArg(lean_object* v_x_3609_, lean_object* v_x_3610_){
_start:
{
if (lean_obj_tag(v_x_3610_) == 0)
{
return v_x_3609_;
}
else
{
lean_object* v_key_3611_; lean_object* v_value_3612_; lean_object* v_tail_3613_; lean_object* v___x_3615_; uint8_t v_isShared_3616_; uint8_t v_isSharedCheck_3636_; 
v_key_3611_ = lean_ctor_get(v_x_3610_, 0);
v_value_3612_ = lean_ctor_get(v_x_3610_, 1);
v_tail_3613_ = lean_ctor_get(v_x_3610_, 2);
v_isSharedCheck_3636_ = !lean_is_exclusive(v_x_3610_);
if (v_isSharedCheck_3636_ == 0)
{
v___x_3615_ = v_x_3610_;
v_isShared_3616_ = v_isSharedCheck_3636_;
goto v_resetjp_3614_;
}
else
{
lean_inc(v_tail_3613_);
lean_inc(v_value_3612_);
lean_inc(v_key_3611_);
lean_dec(v_x_3610_);
v___x_3615_ = lean_box(0);
v_isShared_3616_ = v_isSharedCheck_3636_;
goto v_resetjp_3614_;
}
v_resetjp_3614_:
{
lean_object* v___x_3617_; uint64_t v___x_3618_; uint64_t v___x_3619_; uint64_t v___x_3620_; uint64_t v_fold_3621_; uint64_t v___x_3622_; uint64_t v___x_3623_; uint64_t v___x_3624_; size_t v___x_3625_; size_t v___x_3626_; size_t v___x_3627_; size_t v___x_3628_; size_t v___x_3629_; lean_object* v___x_3630_; lean_object* v___x_3632_; 
v___x_3617_ = lean_array_get_size(v_x_3609_);
v___x_3618_ = l_Lean_Elab_Tactic_Grind_instHashableSimpCacheKey_hash(v_key_3611_);
v___x_3619_ = 32ULL;
v___x_3620_ = lean_uint64_shift_right(v___x_3618_, v___x_3619_);
v_fold_3621_ = lean_uint64_xor(v___x_3618_, v___x_3620_);
v___x_3622_ = 16ULL;
v___x_3623_ = lean_uint64_shift_right(v_fold_3621_, v___x_3622_);
v___x_3624_ = lean_uint64_xor(v_fold_3621_, v___x_3623_);
v___x_3625_ = lean_uint64_to_usize(v___x_3624_);
v___x_3626_ = lean_usize_of_nat(v___x_3617_);
v___x_3627_ = ((size_t)1ULL);
v___x_3628_ = lean_usize_sub(v___x_3626_, v___x_3627_);
v___x_3629_ = lean_usize_land(v___x_3625_, v___x_3628_);
v___x_3630_ = lean_array_uget_borrowed(v_x_3609_, v___x_3629_);
lean_inc(v___x_3630_);
if (v_isShared_3616_ == 0)
{
lean_ctor_set(v___x_3615_, 2, v___x_3630_);
v___x_3632_ = v___x_3615_;
goto v_reusejp_3631_;
}
else
{
lean_object* v_reuseFailAlloc_3635_; 
v_reuseFailAlloc_3635_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3635_, 0, v_key_3611_);
lean_ctor_set(v_reuseFailAlloc_3635_, 1, v_value_3612_);
lean_ctor_set(v_reuseFailAlloc_3635_, 2, v___x_3630_);
v___x_3632_ = v_reuseFailAlloc_3635_;
goto v_reusejp_3631_;
}
v_reusejp_3631_:
{
lean_object* v___x_3633_; 
v___x_3633_ = lean_array_uset(v_x_3609_, v___x_3629_, v___x_3632_);
v_x_3609_ = v___x_3633_;
v_x_3610_ = v_tail_3613_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__2_spec__3___redArg(lean_object* v_i_3637_, lean_object* v_source_3638_, lean_object* v_target_3639_){
_start:
{
lean_object* v___x_3640_; uint8_t v___x_3641_; 
v___x_3640_ = lean_array_get_size(v_source_3638_);
v___x_3641_ = lean_nat_dec_lt(v_i_3637_, v___x_3640_);
if (v___x_3641_ == 0)
{
lean_dec_ref(v_source_3638_);
lean_dec(v_i_3637_);
return v_target_3639_;
}
else
{
lean_object* v_es_3642_; lean_object* v___x_3643_; lean_object* v_source_3644_; lean_object* v_target_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; 
v_es_3642_ = lean_array_fget(v_source_3638_, v_i_3637_);
v___x_3643_ = lean_box(0);
v_source_3644_ = lean_array_fset(v_source_3638_, v_i_3637_, v___x_3643_);
v_target_3645_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__2_spec__3_spec__7___redArg(v_target_3639_, v_es_3642_);
v___x_3646_ = lean_unsigned_to_nat(1u);
v___x_3647_ = lean_nat_add(v_i_3637_, v___x_3646_);
lean_dec(v_i_3637_);
v_i_3637_ = v___x_3647_;
v_source_3638_ = v_source_3644_;
v_target_3639_ = v_target_3645_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__2___redArg(lean_object* v_data_3649_){
_start:
{
lean_object* v___x_3650_; lean_object* v___x_3651_; lean_object* v_nbuckets_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; 
v___x_3650_ = lean_array_get_size(v_data_3649_);
v___x_3651_ = lean_unsigned_to_nat(2u);
v_nbuckets_3652_ = lean_nat_mul(v___x_3650_, v___x_3651_);
v___x_3653_ = lean_unsigned_to_nat(0u);
v___x_3654_ = lean_box(0);
v___x_3655_ = lean_mk_array(v_nbuckets_3652_, v___x_3654_);
v___x_3656_ = lean_array_propagate_mark(v_data_3649_, v___x_3655_);
v___x_3657_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__2_spec__3___redArg(v___x_3653_, v_data_3649_, v___x_3656_);
return v___x_3657_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__1___redArg(lean_object* v_a_3658_, lean_object* v_x_3659_){
_start:
{
if (lean_obj_tag(v_x_3659_) == 0)
{
uint8_t v___x_3660_; 
v___x_3660_ = 0;
return v___x_3660_;
}
else
{
lean_object* v_key_3661_; lean_object* v_tail_3662_; uint8_t v___x_3663_; 
v_key_3661_ = lean_ctor_get(v_x_3659_, 0);
v_tail_3662_ = lean_ctor_get(v_x_3659_, 2);
v___x_3663_ = l_Lean_Elab_Tactic_Grind_instBEqSimpCacheKey_beq(v_key_3661_, v_a_3658_);
if (v___x_3663_ == 0)
{
v_x_3659_ = v_tail_3662_;
goto _start;
}
else
{
return v___x_3663_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__1___redArg___boxed(lean_object* v_a_3665_, lean_object* v_x_3666_){
_start:
{
uint8_t v_res_3667_; lean_object* v_r_3668_; 
v_res_3667_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__1___redArg(v_a_3665_, v_x_3666_);
lean_dec(v_x_3666_);
lean_dec_ref(v_a_3665_);
v_r_3668_ = lean_box(v_res_3667_);
return v_r_3668_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1___redArg(lean_object* v_m_3669_, lean_object* v_a_3670_, lean_object* v_b_3671_){
_start:
{
lean_object* v_size_3672_; lean_object* v_buckets_3673_; lean_object* v___x_3675_; uint8_t v_isShared_3676_; uint8_t v_isSharedCheck_3716_; 
v_size_3672_ = lean_ctor_get(v_m_3669_, 0);
v_buckets_3673_ = lean_ctor_get(v_m_3669_, 1);
v_isSharedCheck_3716_ = !lean_is_exclusive(v_m_3669_);
if (v_isSharedCheck_3716_ == 0)
{
v___x_3675_ = v_m_3669_;
v_isShared_3676_ = v_isSharedCheck_3716_;
goto v_resetjp_3674_;
}
else
{
lean_inc(v_buckets_3673_);
lean_inc(v_size_3672_);
lean_dec(v_m_3669_);
v___x_3675_ = lean_box(0);
v_isShared_3676_ = v_isSharedCheck_3716_;
goto v_resetjp_3674_;
}
v_resetjp_3674_:
{
lean_object* v___x_3677_; uint64_t v___x_3678_; uint64_t v___x_3679_; uint64_t v___x_3680_; uint64_t v_fold_3681_; uint64_t v___x_3682_; uint64_t v___x_3683_; uint64_t v___x_3684_; size_t v___x_3685_; size_t v___x_3686_; size_t v___x_3687_; size_t v___x_3688_; size_t v___x_3689_; lean_object* v_bkt_3690_; uint8_t v___x_3691_; 
v___x_3677_ = lean_array_get_size(v_buckets_3673_);
v___x_3678_ = l_Lean_Elab_Tactic_Grind_instHashableSimpCacheKey_hash(v_a_3670_);
v___x_3679_ = 32ULL;
v___x_3680_ = lean_uint64_shift_right(v___x_3678_, v___x_3679_);
v_fold_3681_ = lean_uint64_xor(v___x_3678_, v___x_3680_);
v___x_3682_ = 16ULL;
v___x_3683_ = lean_uint64_shift_right(v_fold_3681_, v___x_3682_);
v___x_3684_ = lean_uint64_xor(v_fold_3681_, v___x_3683_);
v___x_3685_ = lean_uint64_to_usize(v___x_3684_);
v___x_3686_ = lean_usize_of_nat(v___x_3677_);
v___x_3687_ = ((size_t)1ULL);
v___x_3688_ = lean_usize_sub(v___x_3686_, v___x_3687_);
v___x_3689_ = lean_usize_land(v___x_3685_, v___x_3688_);
v_bkt_3690_ = lean_array_uget_borrowed(v_buckets_3673_, v___x_3689_);
v___x_3691_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__1___redArg(v_a_3670_, v_bkt_3690_);
if (v___x_3691_ == 0)
{
lean_object* v___x_3692_; lean_object* v_size_x27_3693_; lean_object* v___x_3694_; lean_object* v_buckets_x27_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; uint8_t v___x_3701_; 
v___x_3692_ = lean_unsigned_to_nat(1u);
v_size_x27_3693_ = lean_nat_add(v_size_3672_, v___x_3692_);
lean_dec(v_size_3672_);
lean_inc(v_bkt_3690_);
v___x_3694_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3694_, 0, v_a_3670_);
lean_ctor_set(v___x_3694_, 1, v_b_3671_);
lean_ctor_set(v___x_3694_, 2, v_bkt_3690_);
v_buckets_x27_3695_ = lean_array_uset(v_buckets_3673_, v___x_3689_, v___x_3694_);
v___x_3696_ = lean_unsigned_to_nat(4u);
v___x_3697_ = lean_nat_mul(v_size_x27_3693_, v___x_3696_);
v___x_3698_ = lean_unsigned_to_nat(3u);
v___x_3699_ = lean_nat_div(v___x_3697_, v___x_3698_);
lean_dec(v___x_3697_);
v___x_3700_ = lean_array_get_size(v_buckets_x27_3695_);
v___x_3701_ = lean_nat_dec_le(v___x_3699_, v___x_3700_);
lean_dec(v___x_3699_);
if (v___x_3701_ == 0)
{
lean_object* v_val_3702_; lean_object* v___x_3704_; 
v_val_3702_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__2___redArg(v_buckets_x27_3695_);
if (v_isShared_3676_ == 0)
{
lean_ctor_set(v___x_3675_, 1, v_val_3702_);
lean_ctor_set(v___x_3675_, 0, v_size_x27_3693_);
v___x_3704_ = v___x_3675_;
goto v_reusejp_3703_;
}
else
{
lean_object* v_reuseFailAlloc_3705_; 
v_reuseFailAlloc_3705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3705_, 0, v_size_x27_3693_);
lean_ctor_set(v_reuseFailAlloc_3705_, 1, v_val_3702_);
v___x_3704_ = v_reuseFailAlloc_3705_;
goto v_reusejp_3703_;
}
v_reusejp_3703_:
{
return v___x_3704_;
}
}
else
{
lean_object* v___x_3707_; 
if (v_isShared_3676_ == 0)
{
lean_ctor_set(v___x_3675_, 1, v_buckets_x27_3695_);
lean_ctor_set(v___x_3675_, 0, v_size_x27_3693_);
v___x_3707_ = v___x_3675_;
goto v_reusejp_3706_;
}
else
{
lean_object* v_reuseFailAlloc_3708_; 
v_reuseFailAlloc_3708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3708_, 0, v_size_x27_3693_);
lean_ctor_set(v_reuseFailAlloc_3708_, 1, v_buckets_x27_3695_);
v___x_3707_ = v_reuseFailAlloc_3708_;
goto v_reusejp_3706_;
}
v_reusejp_3706_:
{
return v___x_3707_;
}
}
}
else
{
lean_object* v___x_3709_; lean_object* v_buckets_x27_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3714_; 
lean_inc(v_bkt_3690_);
v___x_3709_ = lean_box(0);
v_buckets_x27_3710_ = lean_array_uset(v_buckets_3673_, v___x_3689_, v___x_3709_);
v___x_3711_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__3___redArg(v_a_3670_, v_b_3671_, v_bkt_3690_);
v___x_3712_ = lean_array_uset(v_buckets_x27_3710_, v___x_3689_, v___x_3711_);
if (v_isShared_3676_ == 0)
{
lean_ctor_set(v___x_3675_, 1, v___x_3712_);
v___x_3714_ = v___x_3675_;
goto v_reusejp_3713_;
}
else
{
lean_object* v_reuseFailAlloc_3715_; 
v_reuseFailAlloc_3715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3715_, 0, v_size_3672_);
lean_ctor_set(v_reuseFailAlloc_3715_, 1, v___x_3712_);
v___x_3714_ = v_reuseFailAlloc_3715_;
goto v_reusejp_3713_;
}
v_reusejp_3713_:
{
return v___x_3714_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__3(size_t v_sz_3717_, size_t v_i_3718_, lean_object* v_bs_3719_){
_start:
{
uint8_t v___x_3720_; 
v___x_3720_ = lean_usize_dec_lt(v_i_3718_, v_sz_3717_);
if (v___x_3720_ == 0)
{
lean_object* v___x_3721_; 
v___x_3721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3721_, 0, v_bs_3719_);
return v___x_3721_;
}
else
{
lean_object* v_v_3722_; lean_object* v___x_3723_; lean_object* v_bs_x27_3724_; size_t v___x_3725_; size_t v___x_3726_; lean_object* v___x_3727_; 
v_v_3722_ = lean_array_uget(v_bs_3719_, v_i_3718_);
v___x_3723_ = lean_unsigned_to_nat(0u);
v_bs_x27_3724_ = lean_array_uset(v_bs_3719_, v_i_3718_, v___x_3723_);
v___x_3725_ = ((size_t)1ULL);
v___x_3726_ = lean_usize_add(v_i_3718_, v___x_3725_);
v___x_3727_ = lean_array_uset(v_bs_x27_3724_, v_i_3718_, v_v_3722_);
v_i_3718_ = v___x_3726_;
v_bs_3719_ = v___x_3727_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__3___boxed(lean_object* v_sz_3729_, lean_object* v_i_3730_, lean_object* v_bs_3731_){
_start:
{
size_t v_sz_boxed_3732_; size_t v_i_boxed_3733_; lean_object* v_res_3734_; 
v_sz_boxed_3732_ = lean_unbox_usize(v_sz_3729_);
lean_dec(v_sz_3729_);
v_i_boxed_3733_ = lean_unbox_usize(v_i_3730_);
lean_dec(v_i_3730_);
v_res_3734_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__3(v_sz_boxed_3732_, v_i_boxed_3733_, v_bs_3731_);
return v_res_3734_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__1(void){
_start:
{
lean_object* v___x_3736_; lean_object* v___x_3737_; 
v___x_3736_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__0));
v___x_3737_ = l_Lean_stringToMessageData(v___x_3736_);
return v___x_3737_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__4(void){
_start:
{
lean_object* v___x_3745_; lean_object* v___x_3746_; 
v___x_3745_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___closed__0, &l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___closed__0_once, _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___closed__0);
v___x_3746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3746_, 0, v___x_3745_);
return v___x_3746_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__5(void){
_start:
{
lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; 
v___x_3747_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__4, &l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__4_once, _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__4);
v___x_3748_ = lean_unsigned_to_nat(0u);
v___x_3749_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3749_, 0, v___x_3748_);
lean_ctor_set(v___x_3749_, 1, v___x_3747_);
lean_ctor_set(v___x_3749_, 2, v___x_3747_);
lean_ctor_set(v___x_3749_, 3, v___x_3747_);
return v___x_3749_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2(lean_object* v_stx_3752_, lean_object* v___y_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_){
_start:
{
lean_object* v___y_3763_; lean_object* v___y_3764_; lean_object* v___y_3765_; lean_object* v___y_3766_; lean_object* v___y_3767_; lean_object* v___y_3768_; lean_object* v___y_3769_; lean_object* v___y_3770_; lean_object* v___y_3771_; lean_object* v___y_3772_; lean_object* v___y_3773_; lean_object* v___y_3774_; lean_object* v___x_3870_; 
v___x_3870_ = l_Lean_Elab_Tactic_Grind_ensureSym___redArg(v___y_3753_, v___y_3757_, v___y_3758_, v___y_3759_, v___y_3760_);
if (lean_obj_tag(v___x_3870_) == 0)
{
lean_object* v___x_3872_; uint8_t v_isShared_3873_; uint8_t v_isSharedCheck_3981_; 
v_isSharedCheck_3981_ = !lean_is_exclusive(v___x_3870_);
if (v_isSharedCheck_3981_ == 0)
{
lean_object* v_unused_3982_; 
v_unused_3982_ = lean_ctor_get(v___x_3870_, 0);
lean_dec(v_unused_3982_);
v___x_3872_ = v___x_3870_;
v_isShared_3873_ = v_isSharedCheck_3981_;
goto v_resetjp_3871_;
}
else
{
lean_dec(v___x_3870_);
v___x_3872_ = lean_box(0);
v_isShared_3873_ = v_isSharedCheck_3981_;
goto v_resetjp_3871_;
}
v_resetjp_3871_:
{
lean_object* v___x_3874_; uint8_t v___x_3875_; 
v___x_3874_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__3));
lean_inc(v_stx_3752_);
v___x_3875_ = l_Lean_Syntax_isOfKind(v_stx_3752_, v___x_3874_);
if (v___x_3875_ == 0)
{
lean_object* v___x_3876_; 
lean_del_object(v___x_3872_);
lean_dec(v_stx_3752_);
v___x_3876_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro_spec__0___redArg();
return v___x_3876_;
}
else
{
lean_object* v___x_3877_; lean_object* v___y_3879_; lean_object* v___y_3880_; lean_object* v___y_3881_; lean_object* v___y_3882_; lean_object* v___y_3883_; lean_object* v___y_3884_; lean_object* v___y_3885_; lean_object* v___y_3886_; lean_object* v___y_3887_; lean_object* v___y_3888_; lean_object* v___y_3915_; lean_object* v_extraIds_3916_; lean_object* v___y_3917_; lean_object* v___y_3918_; lean_object* v___y_3919_; lean_object* v___y_3920_; lean_object* v___y_3921_; lean_object* v___y_3922_; lean_object* v___y_3923_; lean_object* v___y_3924_; lean_object* v___y_3929_; lean_object* v___y_3930_; lean_object* v___y_3931_; lean_object* v___y_3932_; lean_object* v___y_3933_; lean_object* v___y_3934_; lean_object* v___y_3935_; lean_object* v___y_3936_; lean_object* v___y_3937_; lean_object* v___y_3938_; lean_object* v___x_3943_; lean_object* v_variantId_x3f_3945_; lean_object* v___y_3946_; lean_object* v___y_3947_; lean_object* v___y_3948_; lean_object* v___y_3949_; lean_object* v___y_3950_; lean_object* v___y_3951_; lean_object* v___y_3952_; lean_object* v___y_3953_; lean_object* v___x_3972_; uint8_t v___x_3973_; 
v___x_3877_ = lean_unsigned_to_nat(0u);
v___x_3943_ = lean_unsigned_to_nat(1u);
v___x_3972_ = l_Lean_Syntax_getArg(v_stx_3752_, v___x_3943_);
v___x_3973_ = l_Lean_Syntax_isNone(v___x_3972_);
if (v___x_3973_ == 0)
{
uint8_t v___x_3974_; 
lean_inc(v___x_3972_);
v___x_3974_ = l_Lean_Syntax_matchesNull(v___x_3972_, v___x_3943_);
if (v___x_3974_ == 0)
{
lean_object* v___x_3975_; 
lean_dec(v___x_3972_);
lean_del_object(v___x_3872_);
lean_dec(v_stx_3752_);
v___x_3975_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro_spec__0___redArg();
return v___x_3975_;
}
else
{
lean_object* v___x_3976_; lean_object* v___x_3978_; 
v___x_3976_ = l_Lean_Syntax_getArg(v___x_3972_, v___x_3877_);
lean_dec(v___x_3972_);
if (v_isShared_3873_ == 0)
{
lean_ctor_set_tag(v___x_3872_, 1);
lean_ctor_set(v___x_3872_, 0, v___x_3976_);
v___x_3978_ = v___x_3872_;
goto v_reusejp_3977_;
}
else
{
lean_object* v_reuseFailAlloc_3979_; 
v_reuseFailAlloc_3979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3979_, 0, v___x_3976_);
v___x_3978_ = v_reuseFailAlloc_3979_;
goto v_reusejp_3977_;
}
v_reusejp_3977_:
{
v_variantId_x3f_3945_ = v___x_3978_;
v___y_3946_ = v___y_3753_;
v___y_3947_ = v___y_3754_;
v___y_3948_ = v___y_3755_;
v___y_3949_ = v___y_3756_;
v___y_3950_ = v___y_3757_;
v___y_3951_ = v___y_3758_;
v___y_3952_ = v___y_3759_;
v___y_3953_ = v___y_3760_;
goto v___jp_3944_;
}
}
}
else
{
lean_object* v___x_3980_; 
lean_dec(v___x_3972_);
lean_del_object(v___x_3872_);
v___x_3980_ = lean_box(0);
v_variantId_x3f_3945_ = v___x_3980_;
v___y_3946_ = v___y_3753_;
v___y_3947_ = v___y_3754_;
v___y_3948_ = v___y_3755_;
v___y_3949_ = v___y_3756_;
v___y_3950_ = v___y_3757_;
v___y_3951_ = v___y_3758_;
v___y_3952_ = v___y_3759_;
v___y_3953_ = v___y_3760_;
goto v___jp_3944_;
}
v___jp_3878_:
{
lean_object* v___x_3889_; 
v___x_3889_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems(v___y_3879_, v___y_3887_, v___y_3883_, v___y_3884_, v___y_3885_, v___y_3882_, v___y_3880_, v___y_3886_, v___y_3881_);
lean_dec(v___y_3879_);
if (lean_obj_tag(v___x_3889_) == 0)
{
lean_object* v_a_3890_; lean_object* v_fst_3891_; lean_object* v_snd_3892_; lean_object* v___x_3894_; uint8_t v_isShared_3895_; uint8_t v_isSharedCheck_3905_; 
v_a_3890_ = lean_ctor_get(v___x_3889_, 0);
lean_inc(v_a_3890_);
lean_dec_ref_known(v___x_3889_, 1);
v_fst_3891_ = lean_ctor_get(v_a_3890_, 0);
v_snd_3892_ = lean_ctor_get(v_a_3890_, 1);
v_isSharedCheck_3905_ = !lean_is_exclusive(v_a_3890_);
if (v_isSharedCheck_3905_ == 0)
{
v___x_3894_ = v_a_3890_;
v_isShared_3895_ = v_isSharedCheck_3905_;
goto v_resetjp_3893_;
}
else
{
lean_inc(v_snd_3892_);
lean_inc(v_fst_3891_);
lean_dec(v_a_3890_);
v___x_3894_ = lean_box(0);
v_isShared_3895_ = v_isSharedCheck_3905_;
goto v_resetjp_3893_;
}
v_resetjp_3893_:
{
lean_object* v___x_3897_; 
lean_inc(v___y_3888_);
if (v_isShared_3895_ == 0)
{
lean_ctor_set(v___x_3894_, 1, v_fst_3891_);
lean_ctor_set(v___x_3894_, 0, v___y_3888_);
v___x_3897_ = v___x_3894_;
goto v_reusejp_3896_;
}
else
{
lean_object* v_reuseFailAlloc_3904_; 
v_reuseFailAlloc_3904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3904_, 0, v___y_3888_);
lean_ctor_set(v_reuseFailAlloc_3904_, 1, v_fst_3891_);
v___x_3897_ = v_reuseFailAlloc_3904_;
goto v_reusejp_3896_;
}
v_reusejp_3896_:
{
lean_object* v___x_3898_; lean_object* v_cache_3899_; lean_object* v_simpState_3900_; lean_object* v___x_3901_; 
v___x_3898_ = lean_st_ref_get(v___y_3883_);
v_cache_3899_ = lean_ctor_get(v___x_3898_, 3);
lean_inc_ref(v_cache_3899_);
lean_dec(v___x_3898_);
v_simpState_3900_ = lean_ctor_get(v_cache_3899_, 2);
lean_inc_ref(v_simpState_3900_);
lean_dec_ref(v_cache_3899_);
v___x_3901_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__2___redArg(v_simpState_3900_, v___x_3897_);
lean_dec_ref(v_simpState_3900_);
if (lean_obj_tag(v___x_3901_) == 0)
{
lean_object* v___x_3902_; 
v___x_3902_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__5, &l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__5);
v___y_3763_ = v___y_3880_;
v___y_3764_ = v___y_3881_;
v___y_3765_ = v___y_3882_;
v___y_3766_ = v___y_3883_;
v___y_3767_ = v___x_3897_;
v___y_3768_ = v___y_3884_;
v___y_3769_ = v_snd_3892_;
v___y_3770_ = v___y_3885_;
v___y_3771_ = v___y_3886_;
v___y_3772_ = v___y_3887_;
v___y_3773_ = v___y_3888_;
v___y_3774_ = v___x_3902_;
goto v___jp_3762_;
}
else
{
lean_object* v_val_3903_; 
v_val_3903_ = lean_ctor_get(v___x_3901_, 0);
lean_inc(v_val_3903_);
lean_dec_ref_known(v___x_3901_, 1);
v___y_3763_ = v___y_3880_;
v___y_3764_ = v___y_3881_;
v___y_3765_ = v___y_3882_;
v___y_3766_ = v___y_3883_;
v___y_3767_ = v___x_3897_;
v___y_3768_ = v___y_3884_;
v___y_3769_ = v_snd_3892_;
v___y_3770_ = v___y_3885_;
v___y_3771_ = v___y_3886_;
v___y_3772_ = v___y_3887_;
v___y_3773_ = v___y_3888_;
v___y_3774_ = v_val_3903_;
goto v___jp_3762_;
}
}
}
}
else
{
lean_object* v_a_3906_; lean_object* v___x_3908_; uint8_t v_isShared_3909_; uint8_t v_isSharedCheck_3913_; 
lean_dec(v___y_3888_);
v_a_3906_ = lean_ctor_get(v___x_3889_, 0);
v_isSharedCheck_3913_ = !lean_is_exclusive(v___x_3889_);
if (v_isSharedCheck_3913_ == 0)
{
v___x_3908_ = v___x_3889_;
v_isShared_3909_ = v_isSharedCheck_3913_;
goto v_resetjp_3907_;
}
else
{
lean_inc(v_a_3906_);
lean_dec(v___x_3889_);
v___x_3908_ = lean_box(0);
v_isShared_3909_ = v_isSharedCheck_3913_;
goto v_resetjp_3907_;
}
v_resetjp_3907_:
{
lean_object* v___x_3911_; 
if (v_isShared_3909_ == 0)
{
v___x_3911_ = v___x_3908_;
goto v_reusejp_3910_;
}
else
{
lean_object* v_reuseFailAlloc_3912_; 
v_reuseFailAlloc_3912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3912_, 0, v_a_3906_);
v___x_3911_ = v_reuseFailAlloc_3912_;
goto v_reusejp_3910_;
}
v_reusejp_3910_:
{
return v___x_3911_;
}
}
}
}
v___jp_3914_:
{
if (lean_obj_tag(v___y_3915_) == 0)
{
lean_object* v___x_3925_; 
v___x_3925_ = lean_box(0);
v___y_3879_ = v_extraIds_3916_;
v___y_3880_ = v___y_3922_;
v___y_3881_ = v___y_3924_;
v___y_3882_ = v___y_3921_;
v___y_3883_ = v___y_3918_;
v___y_3884_ = v___y_3919_;
v___y_3885_ = v___y_3920_;
v___y_3886_ = v___y_3923_;
v___y_3887_ = v___y_3917_;
v___y_3888_ = v___x_3925_;
goto v___jp_3878_;
}
else
{
lean_object* v_val_3926_; lean_object* v___x_3927_; 
v_val_3926_ = lean_ctor_get(v___y_3915_, 0);
lean_inc(v_val_3926_);
lean_dec_ref_known(v___y_3915_, 1);
v___x_3927_ = l_Lean_TSyntax_getId(v_val_3926_);
lean_dec(v_val_3926_);
v___y_3879_ = v_extraIds_3916_;
v___y_3880_ = v___y_3922_;
v___y_3881_ = v___y_3924_;
v___y_3882_ = v___y_3921_;
v___y_3883_ = v___y_3918_;
v___y_3884_ = v___y_3919_;
v___y_3885_ = v___y_3920_;
v___y_3886_ = v___y_3923_;
v___y_3887_ = v___y_3917_;
v___y_3888_ = v___x_3927_;
goto v___jp_3878_;
}
}
v___jp_3928_:
{
size_t v_sz_3939_; size_t v___x_3940_; lean_object* v___x_3941_; 
v_sz_3939_ = lean_array_size(v___y_3938_);
v___x_3940_ = ((size_t)0ULL);
v___x_3941_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__3(v_sz_3939_, v___x_3940_, v___y_3938_);
if (lean_obj_tag(v___x_3941_) == 0)
{
lean_object* v___x_3942_; 
lean_dec(v___y_3931_);
v___x_3942_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro_spec__0___redArg();
return v___x_3942_;
}
else
{
v___y_3915_ = v___y_3931_;
v_extraIds_3916_ = v___x_3941_;
v___y_3917_ = v___y_3930_;
v___y_3918_ = v___y_3937_;
v___y_3919_ = v___y_3935_;
v___y_3920_ = v___y_3934_;
v___y_3921_ = v___y_3936_;
v___y_3922_ = v___y_3929_;
v___y_3923_ = v___y_3933_;
v___y_3924_ = v___y_3932_;
goto v___jp_3914_;
}
}
v___jp_3944_:
{
lean_object* v___x_3954_; lean_object* v___x_3955_; uint8_t v___x_3956_; 
v___x_3954_ = lean_unsigned_to_nat(2u);
v___x_3955_ = l_Lean_Syntax_getArg(v_stx_3752_, v___x_3954_);
lean_dec(v_stx_3752_);
v___x_3956_ = l_Lean_Syntax_isNone(v___x_3955_);
if (v___x_3956_ == 0)
{
lean_object* v___x_3957_; uint8_t v___x_3958_; 
v___x_3957_ = lean_unsigned_to_nat(3u);
lean_inc(v___x_3955_);
v___x_3958_ = l_Lean_Syntax_matchesNull(v___x_3955_, v___x_3957_);
if (v___x_3958_ == 0)
{
lean_object* v___x_3959_; 
lean_dec(v___x_3955_);
lean_dec(v_variantId_x3f_3945_);
v___x_3959_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro_spec__0___redArg();
return v___x_3959_;
}
else
{
lean_object* v___x_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; uint8_t v___x_3964_; 
v___x_3960_ = l_Lean_Syntax_getArg(v___x_3955_, v___x_3943_);
lean_dec(v___x_3955_);
v___x_3961_ = l_Lean_Syntax_getArgs(v___x_3960_);
lean_dec(v___x_3960_);
v___x_3962_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__6));
v___x_3963_ = lean_array_get_size(v___x_3961_);
v___x_3964_ = lean_nat_dec_lt(v___x_3877_, v___x_3963_);
if (v___x_3964_ == 0)
{
lean_dec_ref(v___x_3961_);
v___y_3929_ = v___y_3951_;
v___y_3930_ = v___y_3946_;
v___y_3931_ = v_variantId_x3f_3945_;
v___y_3932_ = v___y_3953_;
v___y_3933_ = v___y_3952_;
v___y_3934_ = v___y_3949_;
v___y_3935_ = v___y_3948_;
v___y_3936_ = v___y_3950_;
v___y_3937_ = v___y_3947_;
v___y_3938_ = v___x_3962_;
goto v___jp_3928_;
}
else
{
lean_object* v___x_3965_; lean_object* v___x_3966_; size_t v___x_3967_; size_t v___x_3968_; lean_object* v___x_3969_; lean_object* v_snd_3970_; 
v___x_3965_ = lean_box(v___x_3964_);
v___x_3966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3966_, 0, v___x_3965_);
lean_ctor_set(v___x_3966_, 1, v___x_3962_);
v___x_3967_ = ((size_t)0ULL);
v___x_3968_ = lean_usize_of_nat(v___x_3963_);
v___x_3969_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__4(v___x_3958_, v___x_3956_, v___x_3961_, v___x_3967_, v___x_3968_, v___x_3966_);
lean_dec_ref(v___x_3961_);
v_snd_3970_ = lean_ctor_get(v___x_3969_, 1);
lean_inc(v_snd_3970_);
lean_dec_ref(v___x_3969_);
v___y_3929_ = v___y_3951_;
v___y_3930_ = v___y_3946_;
v___y_3931_ = v_variantId_x3f_3945_;
v___y_3932_ = v___y_3953_;
v___y_3933_ = v___y_3952_;
v___y_3934_ = v___y_3949_;
v___y_3935_ = v___y_3948_;
v___y_3936_ = v___y_3950_;
v___y_3937_ = v___y_3947_;
v___y_3938_ = v_snd_3970_;
goto v___jp_3928_;
}
}
}
else
{
lean_object* v___x_3971_; 
lean_dec(v___x_3955_);
v___x_3971_ = lean_box(0);
v___y_3915_ = v_variantId_x3f_3945_;
v_extraIds_3916_ = v___x_3971_;
v___y_3917_ = v___y_3946_;
v___y_3918_ = v___y_3947_;
v___y_3919_ = v___y_3948_;
v___y_3920_ = v___y_3949_;
v___y_3921_ = v___y_3950_;
v___y_3922_ = v___y_3951_;
v___y_3923_ = v___y_3952_;
v___y_3924_ = v___y_3953_;
goto v___jp_3914_;
}
}
}
}
}
else
{
lean_dec(v_stx_3752_);
return v___x_3870_;
}
v___jp_3762_:
{
lean_object* v___x_3775_; 
v___x_3775_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabSimpVariant(v___y_3773_, v___y_3769_, v___y_3772_, v___y_3766_, v___y_3768_, v___y_3770_, v___y_3765_, v___y_3763_, v___y_3771_, v___y_3764_);
lean_dec_ref(v___y_3769_);
if (lean_obj_tag(v___x_3775_) == 0)
{
lean_object* v_a_3776_; lean_object* v_fst_3777_; lean_object* v_snd_3778_; lean_object* v___x_3779_; 
v_a_3776_ = lean_ctor_get(v___x_3775_, 0);
lean_inc(v_a_3776_);
lean_dec_ref_known(v___x_3775_, 1);
v_fst_3777_ = lean_ctor_get(v_a_3776_, 0);
lean_inc(v_fst_3777_);
v_snd_3778_ = lean_ctor_get(v_a_3776_, 1);
lean_inc(v_snd_3778_);
lean_dec(v_a_3776_);
v___x_3779_ = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(v___y_3766_, v___y_3765_, v___y_3763_, v___y_3771_, v___y_3764_);
if (lean_obj_tag(v___x_3779_) == 0)
{
lean_object* v_a_3780_; lean_object* v_toGoalState_3781_; lean_object* v_mvarId_3782_; lean_object* v___x_3784_; uint8_t v_isShared_3785_; uint8_t v_isSharedCheck_3853_; 
v_a_3780_ = lean_ctor_get(v___x_3779_, 0);
lean_inc(v_a_3780_);
lean_dec_ref_known(v___x_3779_, 1);
v_toGoalState_3781_ = lean_ctor_get(v_a_3780_, 0);
v_mvarId_3782_ = lean_ctor_get(v_a_3780_, 1);
v_isSharedCheck_3853_ = !lean_is_exclusive(v_a_3780_);
if (v_isSharedCheck_3853_ == 0)
{
v___x_3784_ = v_a_3780_;
v_isShared_3785_ = v_isSharedCheck_3853_;
goto v_resetjp_3783_;
}
else
{
lean_inc(v_mvarId_3782_);
lean_inc(v_toGoalState_3781_);
lean_dec(v_a_3780_);
v___x_3784_ = lean_box(0);
v_isShared_3785_ = v_isSharedCheck_3853_;
goto v_resetjp_3783_;
}
v_resetjp_3783_:
{
lean_object* v___f_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; 
lean_inc_n(v_mvarId_3782_, 2);
v___f_3786_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__0___boxed), 14, 4);
lean_closure_set(v___f_3786_, 0, v_mvarId_3782_);
lean_closure_set(v___f_3786_, 1, v_fst_3777_);
lean_closure_set(v___f_3786_, 2, v_snd_3778_);
lean_closure_set(v___f_3786_, 3, v___y_3774_);
v___x_3787_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__0___boxed), 13, 3);
lean_closure_set(v___x_3787_, 0, lean_box(0));
lean_closure_set(v___x_3787_, 1, v_mvarId_3782_);
lean_closure_set(v___x_3787_, 2, v___f_3786_);
v___x_3788_ = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(v___x_3787_, v___y_3772_, v___y_3766_, v___y_3765_, v___y_3763_, v___y_3771_, v___y_3764_);
if (lean_obj_tag(v___x_3788_) == 0)
{
lean_object* v_a_3789_; lean_object* v_fst_3790_; lean_object* v_snd_3791_; lean_object* v___x_3793_; uint8_t v_isShared_3794_; uint8_t v_isSharedCheck_3844_; 
v_a_3789_ = lean_ctor_get(v___x_3788_, 0);
lean_inc(v_a_3789_);
lean_dec_ref_known(v___x_3788_, 1);
v_fst_3790_ = lean_ctor_get(v_a_3789_, 0);
v_snd_3791_ = lean_ctor_get(v_a_3789_, 1);
v_isSharedCheck_3844_ = !lean_is_exclusive(v_a_3789_);
if (v_isSharedCheck_3844_ == 0)
{
v___x_3793_ = v_a_3789_;
v_isShared_3794_ = v_isSharedCheck_3844_;
goto v_resetjp_3792_;
}
else
{
lean_inc(v_snd_3791_);
lean_inc(v_fst_3790_);
lean_dec(v_a_3789_);
v___x_3793_ = lean_box(0);
v_isShared_3794_ = v_isSharedCheck_3844_;
goto v_resetjp_3792_;
}
v_resetjp_3792_:
{
lean_object* v___f_3795_; lean_object* v___x_3796_; lean_object* v_cache_3797_; lean_object* v_symState_3798_; lean_object* v_grindState_3799_; lean_object* v_goals_3800_; lean_object* v___x_3802_; uint8_t v_isShared_3803_; uint8_t v_isSharedCheck_3843_; 
v___f_3795_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__1___boxed), 12, 2);
lean_closure_set(v___f_3795_, 0, v_fst_3790_);
lean_closure_set(v___f_3795_, 1, v_mvarId_3782_);
v___x_3796_ = lean_st_ref_take(v___y_3766_);
v_cache_3797_ = lean_ctor_get(v___x_3796_, 3);
v_symState_3798_ = lean_ctor_get(v___x_3796_, 0);
v_grindState_3799_ = lean_ctor_get(v___x_3796_, 1);
v_goals_3800_ = lean_ctor_get(v___x_3796_, 2);
v_isSharedCheck_3843_ = !lean_is_exclusive(v___x_3796_);
if (v_isSharedCheck_3843_ == 0)
{
v___x_3802_ = v___x_3796_;
v_isShared_3803_ = v_isSharedCheck_3843_;
goto v_resetjp_3801_;
}
else
{
lean_inc(v_cache_3797_);
lean_inc(v_goals_3800_);
lean_inc(v_grindState_3799_);
lean_inc(v_symState_3798_);
lean_dec(v___x_3796_);
v___x_3802_ = lean_box(0);
v_isShared_3803_ = v_isSharedCheck_3843_;
goto v_resetjp_3801_;
}
v_resetjp_3801_:
{
lean_object* v_backwardRuleName_3804_; lean_object* v_backwardRuleSyntax_3805_; lean_object* v_simpState_3806_; lean_object* v_dsimpState_3807_; lean_object* v___x_3809_; uint8_t v_isShared_3810_; uint8_t v_isSharedCheck_3842_; 
v_backwardRuleName_3804_ = lean_ctor_get(v_cache_3797_, 0);
v_backwardRuleSyntax_3805_ = lean_ctor_get(v_cache_3797_, 1);
v_simpState_3806_ = lean_ctor_get(v_cache_3797_, 2);
v_dsimpState_3807_ = lean_ctor_get(v_cache_3797_, 3);
v_isSharedCheck_3842_ = !lean_is_exclusive(v_cache_3797_);
if (v_isSharedCheck_3842_ == 0)
{
v___x_3809_ = v_cache_3797_;
v_isShared_3810_ = v_isSharedCheck_3842_;
goto v_resetjp_3808_;
}
else
{
lean_inc(v_dsimpState_3807_);
lean_inc(v_simpState_3806_);
lean_inc(v_backwardRuleSyntax_3805_);
lean_inc(v_backwardRuleName_3804_);
lean_dec(v_cache_3797_);
v___x_3809_ = lean_box(0);
v_isShared_3810_ = v_isSharedCheck_3842_;
goto v_resetjp_3808_;
}
v_resetjp_3808_:
{
lean_object* v___x_3811_; lean_object* v___x_3813_; 
v___x_3811_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1___redArg(v_simpState_3806_, v___y_3767_, v_snd_3791_);
if (v_isShared_3810_ == 0)
{
lean_ctor_set(v___x_3809_, 2, v___x_3811_);
v___x_3813_ = v___x_3809_;
goto v_reusejp_3812_;
}
else
{
lean_object* v_reuseFailAlloc_3841_; 
v_reuseFailAlloc_3841_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3841_, 0, v_backwardRuleName_3804_);
lean_ctor_set(v_reuseFailAlloc_3841_, 1, v_backwardRuleSyntax_3805_);
lean_ctor_set(v_reuseFailAlloc_3841_, 2, v___x_3811_);
lean_ctor_set(v_reuseFailAlloc_3841_, 3, v_dsimpState_3807_);
v___x_3813_ = v_reuseFailAlloc_3841_;
goto v_reusejp_3812_;
}
v_reusejp_3812_:
{
lean_object* v___x_3815_; 
if (v_isShared_3803_ == 0)
{
lean_ctor_set(v___x_3802_, 3, v___x_3813_);
v___x_3815_ = v___x_3802_;
goto v_reusejp_3814_;
}
else
{
lean_object* v_reuseFailAlloc_3840_; 
v_reuseFailAlloc_3840_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3840_, 0, v_symState_3798_);
lean_ctor_set(v_reuseFailAlloc_3840_, 1, v_grindState_3799_);
lean_ctor_set(v_reuseFailAlloc_3840_, 2, v_goals_3800_);
lean_ctor_set(v_reuseFailAlloc_3840_, 3, v___x_3813_);
v___x_3815_ = v_reuseFailAlloc_3840_;
goto v_reusejp_3814_;
}
v_reusejp_3814_:
{
lean_object* v___x_3816_; lean_object* v___x_3817_; 
v___x_3816_ = lean_st_ref_put(v___y_3766_, v___x_3815_);
v___x_3817_ = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(v___f_3795_, v___y_3772_, v___y_3766_, v___y_3765_, v___y_3763_, v___y_3771_, v___y_3764_);
if (lean_obj_tag(v___x_3817_) == 0)
{
lean_object* v_a_3818_; 
v_a_3818_ = lean_ctor_get(v___x_3817_, 0);
lean_inc(v_a_3818_);
lean_dec_ref_known(v___x_3817_, 1);
switch(lean_obj_tag(v_a_3818_))
{
case 0:
{
lean_object* v___x_3819_; lean_object* v___x_3820_; 
lean_del_object(v___x_3793_);
lean_del_object(v___x_3784_);
lean_dec_ref(v_toGoalState_3781_);
v___x_3819_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__1, &l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__1);
v___x_3820_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__2___redArg(v___x_3819_, v___y_3765_, v___y_3763_, v___y_3771_, v___y_3764_);
return v___x_3820_;
}
case 1:
{
lean_object* v___x_3821_; lean_object* v___x_3822_; 
lean_del_object(v___x_3793_);
lean_del_object(v___x_3784_);
lean_dec_ref(v_toGoalState_3781_);
v___x_3821_ = lean_box(0);
v___x_3822_ = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(v___x_3821_, v___y_3766_, v___y_3765_, v___y_3763_, v___y_3771_, v___y_3764_);
return v___x_3822_;
}
default: 
{
lean_object* v_mvarId_3823_; lean_object* v___x_3825_; 
v_mvarId_3823_ = lean_ctor_get(v_a_3818_, 0);
lean_inc(v_mvarId_3823_);
lean_dec_ref_known(v_a_3818_, 1);
if (v_isShared_3785_ == 0)
{
lean_ctor_set(v___x_3784_, 1, v_mvarId_3823_);
v___x_3825_ = v___x_3784_;
goto v_reusejp_3824_;
}
else
{
lean_object* v_reuseFailAlloc_3831_; 
v_reuseFailAlloc_3831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3831_, 0, v_toGoalState_3781_);
lean_ctor_set(v_reuseFailAlloc_3831_, 1, v_mvarId_3823_);
v___x_3825_ = v_reuseFailAlloc_3831_;
goto v_reusejp_3824_;
}
v_reusejp_3824_:
{
lean_object* v___x_3826_; lean_object* v___x_3828_; 
v___x_3826_ = lean_box(0);
if (v_isShared_3794_ == 0)
{
lean_ctor_set_tag(v___x_3793_, 1);
lean_ctor_set(v___x_3793_, 1, v___x_3826_);
lean_ctor_set(v___x_3793_, 0, v___x_3825_);
v___x_3828_ = v___x_3793_;
goto v_reusejp_3827_;
}
else
{
lean_object* v_reuseFailAlloc_3830_; 
v_reuseFailAlloc_3830_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3830_, 0, v___x_3825_);
lean_ctor_set(v_reuseFailAlloc_3830_, 1, v___x_3826_);
v___x_3828_ = v_reuseFailAlloc_3830_;
goto v_reusejp_3827_;
}
v_reusejp_3827_:
{
lean_object* v___x_3829_; 
v___x_3829_ = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(v___x_3828_, v___y_3766_, v___y_3765_, v___y_3763_, v___y_3771_, v___y_3764_);
return v___x_3829_;
}
}
}
}
}
else
{
lean_object* v_a_3832_; lean_object* v___x_3834_; uint8_t v_isShared_3835_; uint8_t v_isSharedCheck_3839_; 
lean_del_object(v___x_3793_);
lean_del_object(v___x_3784_);
lean_dec_ref(v_toGoalState_3781_);
v_a_3832_ = lean_ctor_get(v___x_3817_, 0);
v_isSharedCheck_3839_ = !lean_is_exclusive(v___x_3817_);
if (v_isSharedCheck_3839_ == 0)
{
v___x_3834_ = v___x_3817_;
v_isShared_3835_ = v_isSharedCheck_3839_;
goto v_resetjp_3833_;
}
else
{
lean_inc(v_a_3832_);
lean_dec(v___x_3817_);
v___x_3834_ = lean_box(0);
v_isShared_3835_ = v_isSharedCheck_3839_;
goto v_resetjp_3833_;
}
v_resetjp_3833_:
{
lean_object* v___x_3837_; 
if (v_isShared_3835_ == 0)
{
v___x_3837_ = v___x_3834_;
goto v_reusejp_3836_;
}
else
{
lean_object* v_reuseFailAlloc_3838_; 
v_reuseFailAlloc_3838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3838_, 0, v_a_3832_);
v___x_3837_ = v_reuseFailAlloc_3838_;
goto v_reusejp_3836_;
}
v_reusejp_3836_:
{
return v___x_3837_;
}
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
lean_object* v_a_3845_; lean_object* v___x_3847_; uint8_t v_isShared_3848_; uint8_t v_isSharedCheck_3852_; 
lean_del_object(v___x_3784_);
lean_dec(v_mvarId_3782_);
lean_dec_ref(v_toGoalState_3781_);
lean_dec_ref(v___y_3767_);
v_a_3845_ = lean_ctor_get(v___x_3788_, 0);
v_isSharedCheck_3852_ = !lean_is_exclusive(v___x_3788_);
if (v_isSharedCheck_3852_ == 0)
{
v___x_3847_ = v___x_3788_;
v_isShared_3848_ = v_isSharedCheck_3852_;
goto v_resetjp_3846_;
}
else
{
lean_inc(v_a_3845_);
lean_dec(v___x_3788_);
v___x_3847_ = lean_box(0);
v_isShared_3848_ = v_isSharedCheck_3852_;
goto v_resetjp_3846_;
}
v_resetjp_3846_:
{
lean_object* v___x_3850_; 
if (v_isShared_3848_ == 0)
{
v___x_3850_ = v___x_3847_;
goto v_reusejp_3849_;
}
else
{
lean_object* v_reuseFailAlloc_3851_; 
v_reuseFailAlloc_3851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3851_, 0, v_a_3845_);
v___x_3850_ = v_reuseFailAlloc_3851_;
goto v_reusejp_3849_;
}
v_reusejp_3849_:
{
return v___x_3850_;
}
}
}
}
}
else
{
lean_object* v_a_3854_; lean_object* v___x_3856_; uint8_t v_isShared_3857_; uint8_t v_isSharedCheck_3861_; 
lean_dec(v_snd_3778_);
lean_dec(v_fst_3777_);
lean_dec_ref(v___y_3774_);
lean_dec_ref(v___y_3767_);
v_a_3854_ = lean_ctor_get(v___x_3779_, 0);
v_isSharedCheck_3861_ = !lean_is_exclusive(v___x_3779_);
if (v_isSharedCheck_3861_ == 0)
{
v___x_3856_ = v___x_3779_;
v_isShared_3857_ = v_isSharedCheck_3861_;
goto v_resetjp_3855_;
}
else
{
lean_inc(v_a_3854_);
lean_dec(v___x_3779_);
v___x_3856_ = lean_box(0);
v_isShared_3857_ = v_isSharedCheck_3861_;
goto v_resetjp_3855_;
}
v_resetjp_3855_:
{
lean_object* v___x_3859_; 
if (v_isShared_3857_ == 0)
{
v___x_3859_ = v___x_3856_;
goto v_reusejp_3858_;
}
else
{
lean_object* v_reuseFailAlloc_3860_; 
v_reuseFailAlloc_3860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3860_, 0, v_a_3854_);
v___x_3859_ = v_reuseFailAlloc_3860_;
goto v_reusejp_3858_;
}
v_reusejp_3858_:
{
return v___x_3859_;
}
}
}
}
else
{
lean_object* v_a_3862_; lean_object* v___x_3864_; uint8_t v_isShared_3865_; uint8_t v_isSharedCheck_3869_; 
lean_dec_ref(v___y_3774_);
lean_dec_ref(v___y_3767_);
v_a_3862_ = lean_ctor_get(v___x_3775_, 0);
v_isSharedCheck_3869_ = !lean_is_exclusive(v___x_3775_);
if (v_isSharedCheck_3869_ == 0)
{
v___x_3864_ = v___x_3775_;
v_isShared_3865_ = v_isSharedCheck_3869_;
goto v_resetjp_3863_;
}
else
{
lean_inc(v_a_3862_);
lean_dec(v___x_3775_);
v___x_3864_ = lean_box(0);
v_isShared_3865_ = v_isSharedCheck_3869_;
goto v_resetjp_3863_;
}
v_resetjp_3863_:
{
lean_object* v___x_3867_; 
if (v_isShared_3865_ == 0)
{
v___x_3867_ = v___x_3864_;
goto v_reusejp_3866_;
}
else
{
lean_object* v_reuseFailAlloc_3868_; 
v_reuseFailAlloc_3868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3868_, 0, v_a_3862_);
v___x_3867_ = v_reuseFailAlloc_3868_;
goto v_reusejp_3866_;
}
v_reusejp_3866_:
{
return v___x_3867_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___boxed(lean_object* v_stx_3983_, lean_object* v___y_3984_, lean_object* v___y_3985_, lean_object* v___y_3986_, lean_object* v___y_3987_, lean_object* v___y_3988_, lean_object* v___y_3989_, lean_object* v___y_3990_, lean_object* v___y_3991_, lean_object* v___y_3992_){
_start:
{
lean_object* v_res_3993_; 
v_res_3993_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2(v_stx_3983_, v___y_3984_, v___y_3985_, v___y_3986_, v___y_3987_, v___y_3988_, v___y_3989_, v___y_3990_, v___y_3991_);
lean_dec(v___y_3991_);
lean_dec_ref(v___y_3990_);
lean_dec(v___y_3989_);
lean_dec_ref(v___y_3988_);
lean_dec(v___y_3987_);
lean_dec_ref(v___y_3986_);
lean_dec(v___y_3985_);
lean_dec_ref(v___y_3984_);
return v_res_3993_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp(lean_object* v_stx_3994_, lean_object* v_a_3995_, lean_object* v_a_3996_, lean_object* v_a_3997_, lean_object* v_a_3998_, lean_object* v_a_3999_, lean_object* v_a_4000_, lean_object* v_a_4001_, lean_object* v_a_4002_){
_start:
{
lean_object* v___f_4004_; lean_object* v___x_4005_; 
v___f_4004_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___boxed), 10, 1);
lean_closure_set(v___f_4004_, 0, v_stx_3994_);
v___x_4005_ = l_Lean_Elab_Tactic_Grind_withMainContext___redArg(v___f_4004_, v_a_3995_, v_a_3996_, v_a_3997_, v_a_3998_, v_a_3999_, v_a_4000_, v_a_4001_, v_a_4002_);
return v___x_4005_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___boxed(lean_object* v_stx_4006_, lean_object* v_a_4007_, lean_object* v_a_4008_, lean_object* v_a_4009_, lean_object* v_a_4010_, lean_object* v_a_4011_, lean_object* v_a_4012_, lean_object* v_a_4013_, lean_object* v_a_4014_, lean_object* v_a_4015_){
_start:
{
lean_object* v_res_4016_; 
v_res_4016_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp(v_stx_4006_, v_a_4007_, v_a_4008_, v_a_4009_, v_a_4010_, v_a_4011_, v_a_4012_, v_a_4013_, v_a_4014_);
lean_dec(v_a_4014_);
lean_dec_ref(v_a_4013_);
lean_dec(v_a_4012_);
lean_dec_ref(v_a_4011_);
lean_dec(v_a_4010_);
lean_dec_ref(v_a_4009_);
lean_dec(v_a_4008_);
lean_dec_ref(v_a_4007_);
return v_res_4016_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1(lean_object* v_00_u03b2_4017_, lean_object* v_m_4018_, lean_object* v_a_4019_, lean_object* v_b_4020_){
_start:
{
lean_object* v___x_4021_; 
v___x_4021_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1___redArg(v_m_4018_, v_a_4019_, v_b_4020_);
return v___x_4021_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__2(lean_object* v_00_u03b2_4022_, lean_object* v_m_4023_, lean_object* v_a_4024_){
_start:
{
lean_object* v___x_4025_; 
v___x_4025_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__2___redArg(v_m_4023_, v_a_4024_);
return v___x_4025_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__2___boxed(lean_object* v_00_u03b2_4026_, lean_object* v_m_4027_, lean_object* v_a_4028_){
_start:
{
lean_object* v_res_4029_; 
v_res_4029_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__2(v_00_u03b2_4026_, v_m_4027_, v_a_4028_);
lean_dec_ref(v_a_4028_);
lean_dec_ref(v_m_4027_);
return v_res_4029_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__1(lean_object* v_00_u03b2_4030_, lean_object* v_a_4031_, lean_object* v_x_4032_){
_start:
{
uint8_t v___x_4033_; 
v___x_4033_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__1___redArg(v_a_4031_, v_x_4032_);
return v___x_4033_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__1___boxed(lean_object* v_00_u03b2_4034_, lean_object* v_a_4035_, lean_object* v_x_4036_){
_start:
{
uint8_t v_res_4037_; lean_object* v_r_4038_; 
v_res_4037_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__1(v_00_u03b2_4034_, v_a_4035_, v_x_4036_);
lean_dec(v_x_4036_);
lean_dec_ref(v_a_4035_);
v_r_4038_ = lean_box(v_res_4037_);
return v_r_4038_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__2(lean_object* v_00_u03b2_4039_, lean_object* v_data_4040_){
_start:
{
lean_object* v___x_4041_; 
v___x_4041_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__2___redArg(v_data_4040_);
return v___x_4041_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__3(lean_object* v_00_u03b2_4042_, lean_object* v_a_4043_, lean_object* v_b_4044_, lean_object* v_x_4045_){
_start:
{
lean_object* v___x_4046_; 
v___x_4046_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__3___redArg(v_a_4043_, v_b_4044_, v_x_4045_);
return v___x_4046_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__2_spec__5(lean_object* v_00_u03b2_4047_, lean_object* v_a_4048_, lean_object* v_x_4049_){
_start:
{
lean_object* v___x_4050_; 
v___x_4050_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__2_spec__5___redArg(v_a_4048_, v_x_4049_);
return v___x_4050_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__2_spec__5___boxed(lean_object* v_00_u03b2_4051_, lean_object* v_a_4052_, lean_object* v_x_4053_){
_start:
{
lean_object* v_res_4054_; 
v_res_4054_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__2_spec__5(v_00_u03b2_4051_, v_a_4052_, v_x_4053_);
lean_dec(v_x_4053_);
lean_dec_ref(v_a_4052_);
return v_res_4054_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_4055_, lean_object* v_i_4056_, lean_object* v_source_4057_, lean_object* v_target_4058_){
_start:
{
lean_object* v___x_4059_; 
v___x_4059_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__2_spec__3___redArg(v_i_4056_, v_source_4057_, v_target_4058_);
return v___x_4059_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__2_spec__3_spec__7(lean_object* v_00_u03b2_4060_, lean_object* v_x_4061_, lean_object* v_x_4062_){
_start:
{
lean_object* v___x_4063_; 
v___x_4063_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__2_spec__3_spec__7___redArg(v_x_4061_, v_x_4062_);
return v___x_4063_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp__1(){
_start:
{
lean_object* v___x_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; lean_object* v___x_4073_; 
v___x_4069_ = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
v___x_4070_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__3));
v___x_4071_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp__1___closed__1));
v___x_4072_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___boxed), 10, 0);
v___x_4073_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4069_, v___x_4070_, v___x_4071_, v___x_4072_);
return v___x_4073_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp__1___boxed(lean_object* v_a_4074_){
_start:
{
lean_object* v_res_4075_; 
v_res_4075_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp__1();
return v_res_4075_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Grind_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Grind_SimprocDSL(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Grind(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Variant(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Rewrite(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_EvalGround(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Goal(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Attr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_ControlFlow(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Forall(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Apply(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Location(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_SyntheticMVars(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Grind_Sym(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_Tactic_Grind_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Grind_SimprocDSL(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Grind(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_Variant(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_Rewrite(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_EvalGround(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_Goal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_ControlFlow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_Forall(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Apply(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Location(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_SyntheticMVars(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntros___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntros__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Grind_Sym(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Tactic_Grind_Basic(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Grind_SimprocDSL(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Grind(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_Variant(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_Rewrite(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_EvalGround(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_Goal(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_Attr(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_ControlFlow(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_Forall(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Apply(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Location(uint8_t builtin);
lean_object* initialize_Lean_Elab_SyntheticMVars(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Grind_Sym(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_Grind_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Grind_SimprocDSL(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Grind(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_Variant(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_Rewrite(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_EvalGround(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_Goal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_ControlFlow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_Forall(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Apply(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Location(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_SyntheticMVars(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Grind_Sym(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Grind_Sym(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Grind_Sym(builtin);
}
#ifdef __cplusplus
}
#endif
