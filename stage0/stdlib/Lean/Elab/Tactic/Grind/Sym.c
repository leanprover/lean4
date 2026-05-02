// Lean compiler output
// Module: Lean.Elab.Tactic.Grind.Sym
// Imports: import Lean.Elab.Tactic.Grind.Basic import Lean.Elab.Tactic.Grind.SimprocDSL import Lean.Meta.Sym.Grind import Lean.Meta.Sym.Simp.Variant import Lean.Meta.Sym.Simp.Rewrite import Lean.Meta.Sym.Simp.EvalGround import Lean.Meta.Sym.Simp.Goal import Lean.Meta.Sym.Simp.Attr import Lean.Meta.Sym.Simp.ControlFlow import Lean.Meta.Sym.Simp.Forall import Lean.Meta.Tactic.Apply import Lean.Elab.SyntheticMVars
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
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint64_t l_Lean_Elab_Tactic_Grind_instHashableSimpCacheKey_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_of_nat(lean_object*);
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
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_intros___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_internalizeAll___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_getSymSimpVariant_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_elabSymSimproc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Meta_Sym_Simp_Theorems_insert(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_dischargeNone___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_Theorems_rewrite(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_Result_withContextDependent(lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_getSymSimpTheorems___redArg(lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_evalGround___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_simp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_simpArrowTelescope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_simpControl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_SimpM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* l_Lean_LocalContext_findFromUserName_x3f(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_mkTheoremFromExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_realizeGlobalConstNoOverload(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_mkTheoremFromDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Elab_Tactic_Grind_withMainContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Meta_mkFreshBinderNameForTactic___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_byContra_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_intro1Core(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_exfalso(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFalse(lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_saveState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_SavedState_restore___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Meta_Sym_mkBackwardRuleFromDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_introN___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_ensureSym_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_ensureSym_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_ensureSym_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_ensureSym_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_ensureSym___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "tactic is only available in `sym =>` mode"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_ensureSym___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_ensureSym___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_ensureSym___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_ensureSym___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_ensureSym(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_ensureSym___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_ensureSym_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_ensureSym_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_liftSymM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_liftSymM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_liftSymM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_liftSymM___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_liftSymM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_liftSymM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__0___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__0___redArg___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "binderIdent"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__0___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__0___redArg___closed__1_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__0___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__0___redArg___closed__2_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(37, 194, 68, 106, 254, 181, 31, 191)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__0___redArg___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__0___redArg___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__0___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "h"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__0___redArg___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__0___redArg___closed__3_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__0___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__0___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(176, 181, 207, 77, 197, 87, 68, 121)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__0___redArg___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__0___redArg___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__0___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__0___redArg___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__0___redArg___closed__5_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__0___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__0___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__0___redArg___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__0___redArg___closed__6_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__0___redArg(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
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
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro__1___closed__1_value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
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
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro__1___closed__9_value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(202, 134, 96, 207, 7, 76, 78, 141)}};
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
static const lean_array_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntrosCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntrosCore___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntrosCore___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntrosCore___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "`intros` failed"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntrosCore___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntrosCore___closed__1_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntrosCore___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntrosCore___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntrosCore(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntrosCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntros___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "symIntros"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntros___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntros___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntros___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntros___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntros___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntros___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntros___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntros___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntros___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___closed__2_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntros___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntros___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntros___closed__0_value),LEAN_SCALAR_PTR_LITERAL(51, 175, 114, 140, 112, 61, 143, 32)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntros___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntros___closed__1_value;
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
static lean_once_cell_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0___redArg___closed__0;
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
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3___redArg___closed__0;
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
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "symInternalize"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "symInternalizeAll"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "symByContra"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__0___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems___closed__0_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems___closed__0_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_Simp_dischargeNone___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___closed__0;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkDefaultMethods___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkDefaultMethods___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkDefaultMethods___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_Simp_simp___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkDefaultMethods___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkDefaultMethods___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkDefaultMethods___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkDefaultMethods___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkDefaultMethods___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkDefaultMethods___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkDefaultMethods___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkDefaultMethods___lam__0___boxed, .m_arity = 12, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkDefaultMethods___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkDefaultMethods___closed__0_value;
static const lean_closure_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkDefaultMethods___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkDefaultMethods___lam__2___boxed, .m_arity = 12, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkDefaultMethods___closed__0_value)} };
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkDefaultMethods___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkDefaultMethods___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkDefaultMethods(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkDefaultMethods___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabVariant___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "unknown Sym.simp variant `"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabVariant___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabVariant___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabVariant___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabVariant___closed__1;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabVariant___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabVariant___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabVariant___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabVariant___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabVariant___closed__3;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabVariant___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(100000) << 1) | 1)),((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabVariant___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabVariant___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabVariant(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabVariant___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___closed__2_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__3_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__2_value),LEAN_SCALAR_PTR_LITERAL(162, 109, 151, 25, 234, 136, 56, 252)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__3_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__4;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__5;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__6;
static const lean_array_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__7_value;
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_ensureSym_spec__0_spec__0(lean_object* v_msgData_1_, lean_object* v___y_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_){
_start:
{
lean_object* v___x_7_; lean_object* v_env_8_; lean_object* v___x_9_; lean_object* v_mctx_10_; lean_object* v_lctx_11_; lean_object* v_options_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; 
v___x_7_ = lean_st_ref_get(v___y_5_);
v_env_8_ = lean_ctor_get(v___x_7_, 0);
lean_inc_ref(v_env_8_);
lean_dec(v___x_7_);
v___x_9_ = lean_st_ref_get(v___y_3_);
v_mctx_10_ = lean_ctor_get(v___x_9_, 0);
lean_inc_ref(v_mctx_10_);
lean_dec(v___x_9_);
v_lctx_11_ = lean_ctor_get(v___y_2_, 2);
v_options_12_ = lean_ctor_get(v___y_4_, 2);
lean_inc_ref(v_options_12_);
lean_inc_ref(v_lctx_11_);
v___x_13_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_13_, 0, v_env_8_);
lean_ctor_set(v___x_13_, 1, v_mctx_10_);
lean_ctor_set(v___x_13_, 2, v_lctx_11_);
lean_ctor_set(v___x_13_, 3, v_options_12_);
v___x_14_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_14_, 0, v___x_13_);
lean_ctor_set(v___x_14_, 1, v_msgData_1_);
v___x_15_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_15_, 0, v___x_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_ensureSym_spec__0_spec__0___boxed(lean_object* v_msgData_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_ensureSym_spec__0_spec__0(v_msgData_16_, v___y_17_, v___y_18_, v___y_19_, v___y_20_);
lean_dec(v___y_20_);
lean_dec_ref(v___y_19_);
lean_dec(v___y_18_);
lean_dec_ref(v___y_17_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_ensureSym_spec__0___redArg(lean_object* v_msg_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_){
_start:
{
lean_object* v_ref_29_; lean_object* v___x_30_; lean_object* v_a_31_; lean_object* v___x_33_; uint8_t v_isShared_34_; uint8_t v_isSharedCheck_39_; 
v_ref_29_ = lean_ctor_get(v___y_26_, 5);
v___x_30_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_ensureSym_spec__0_spec__0(v_msg_23_, v___y_24_, v___y_25_, v___y_26_, v___y_27_);
v_a_31_ = lean_ctor_get(v___x_30_, 0);
v_isSharedCheck_39_ = !lean_is_exclusive(v___x_30_);
if (v_isSharedCheck_39_ == 0)
{
v___x_33_ = v___x_30_;
v_isShared_34_ = v_isSharedCheck_39_;
goto v_resetjp_32_;
}
else
{
lean_inc(v_a_31_);
lean_dec(v___x_30_);
v___x_33_ = lean_box(0);
v_isShared_34_ = v_isSharedCheck_39_;
goto v_resetjp_32_;
}
v_resetjp_32_:
{
lean_object* v___x_35_; lean_object* v___x_37_; 
lean_inc(v_ref_29_);
v___x_35_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_35_, 0, v_ref_29_);
lean_ctor_set(v___x_35_, 1, v_a_31_);
if (v_isShared_34_ == 0)
{
lean_ctor_set_tag(v___x_33_, 1);
lean_ctor_set(v___x_33_, 0, v___x_35_);
v___x_37_ = v___x_33_;
goto v_reusejp_36_;
}
else
{
lean_object* v_reuseFailAlloc_38_; 
v_reuseFailAlloc_38_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_38_, 0, v___x_35_);
v___x_37_ = v_reuseFailAlloc_38_;
goto v_reusejp_36_;
}
v_reusejp_36_:
{
return v___x_37_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_ensureSym_spec__0___redArg___boxed(lean_object* v_msg_40_, lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_ensureSym_spec__0___redArg(v_msg_40_, v___y_41_, v___y_42_, v___y_43_, v___y_44_);
lean_dec(v___y_44_);
lean_dec_ref(v___y_43_);
lean_dec(v___y_42_);
lean_dec_ref(v___y_41_);
return v_res_46_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_ensureSym___closed__1(void){
_start:
{
lean_object* v___x_48_; lean_object* v___x_49_; 
v___x_48_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_ensureSym___closed__0));
v___x_49_ = l_Lean_stringToMessageData(v___x_48_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_ensureSym(lean_object* v_a_50_, lean_object* v_a_51_, lean_object* v_a_52_, lean_object* v_a_53_, lean_object* v_a_54_, lean_object* v_a_55_, lean_object* v_a_56_, lean_object* v_a_57_){
_start:
{
uint8_t v_sym_59_; 
v_sym_59_ = lean_ctor_get_uint8(v_a_50_, sizeof(void*)*5);
if (v_sym_59_ == 0)
{
lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_60_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_ensureSym___closed__1, &l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_ensureSym___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_ensureSym___closed__1);
v___x_61_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_ensureSym_spec__0___redArg(v___x_60_, v_a_54_, v_a_55_, v_a_56_, v_a_57_);
return v___x_61_;
}
else
{
lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_62_ = lean_box(0);
v___x_63_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_63_, 0, v___x_62_);
return v___x_63_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_ensureSym___boxed(lean_object* v_a_64_, lean_object* v_a_65_, lean_object* v_a_66_, lean_object* v_a_67_, lean_object* v_a_68_, lean_object* v_a_69_, lean_object* v_a_70_, lean_object* v_a_71_, lean_object* v_a_72_){
_start:
{
lean_object* v_res_73_; 
v_res_73_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_ensureSym(v_a_64_, v_a_65_, v_a_66_, v_a_67_, v_a_68_, v_a_69_, v_a_70_, v_a_71_);
lean_dec(v_a_71_);
lean_dec_ref(v_a_70_);
lean_dec(v_a_69_);
lean_dec_ref(v_a_68_);
lean_dec(v_a_67_);
lean_dec_ref(v_a_66_);
lean_dec(v_a_65_);
lean_dec_ref(v_a_64_);
return v_res_73_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_ensureSym_spec__0(lean_object* v_00_u03b1_74_, lean_object* v_msg_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_){
_start:
{
lean_object* v___x_85_; 
v___x_85_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_ensureSym_spec__0___redArg(v_msg_75_, v___y_80_, v___y_81_, v___y_82_, v___y_83_);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_ensureSym_spec__0___boxed(lean_object* v_00_u03b1_86_, lean_object* v_msg_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_){
_start:
{
lean_object* v_res_97_; 
v_res_97_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_ensureSym_spec__0(v_00_u03b1_86_, v_msg_87_, v___y_88_, v___y_89_, v___y_90_, v___y_91_, v___y_92_, v___y_93_, v___y_94_, v___y_95_);
lean_dec(v___y_95_);
lean_dec_ref(v___y_94_);
lean_dec(v___y_93_);
lean_dec_ref(v___y_92_);
lean_dec(v___y_91_);
lean_dec_ref(v___y_90_);
lean_dec(v___y_89_);
lean_dec_ref(v___y_88_);
return v_res_97_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_liftSymM___redArg___lam__0(lean_object* v_k_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_){
_start:
{
lean_object* v___x_109_; 
lean_inc(v___y_107_);
lean_inc_ref(v___y_106_);
lean_inc(v___y_105_);
lean_inc_ref(v___y_104_);
lean_inc(v___y_103_);
lean_inc_ref(v___y_102_);
v___x_109_ = lean_apply_7(v_k_98_, v___y_102_, v___y_103_, v___y_104_, v___y_105_, v___y_106_, v___y_107_, lean_box(0));
return v___x_109_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_liftSymM___redArg___lam__0___boxed(lean_object* v_k_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_){
_start:
{
lean_object* v_res_121_; 
v_res_121_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_liftSymM___redArg___lam__0(v_k_110_, v___y_111_, v___y_112_, v___y_113_, v___y_114_, v___y_115_, v___y_116_, v___y_117_, v___y_118_, v___y_119_);
lean_dec(v___y_119_);
lean_dec_ref(v___y_118_);
lean_dec(v___y_117_);
lean_dec_ref(v___y_116_);
lean_dec(v___y_115_);
lean_dec_ref(v___y_114_);
lean_dec(v___y_113_);
lean_dec_ref(v___y_112_);
lean_dec(v___y_111_);
return v_res_121_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_liftSymM___redArg(lean_object* v_k_122_, lean_object* v_a_123_, lean_object* v_a_124_, lean_object* v_a_125_, lean_object* v_a_126_, lean_object* v_a_127_, lean_object* v_a_128_){
_start:
{
lean_object* v___f_130_; lean_object* v___x_131_; 
v___f_130_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_liftSymM___redArg___lam__0___boxed), 11, 1);
lean_closure_set(v___f_130_, 0, v_k_122_);
v___x_131_ = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(v___f_130_, v_a_123_, v_a_124_, v_a_125_, v_a_126_, v_a_127_, v_a_128_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_liftSymM___redArg___boxed(lean_object* v_k_132_, lean_object* v_a_133_, lean_object* v_a_134_, lean_object* v_a_135_, lean_object* v_a_136_, lean_object* v_a_137_, lean_object* v_a_138_, lean_object* v_a_139_){
_start:
{
lean_object* v_res_140_; 
v_res_140_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_liftSymM___redArg(v_k_132_, v_a_133_, v_a_134_, v_a_135_, v_a_136_, v_a_137_, v_a_138_);
lean_dec(v_a_138_);
lean_dec_ref(v_a_137_);
lean_dec(v_a_136_);
lean_dec_ref(v_a_135_);
lean_dec(v_a_134_);
lean_dec_ref(v_a_133_);
return v_res_140_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_liftSymM(lean_object* v_00_u03b1_141_, lean_object* v_k_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_, lean_object* v_a_150_){
_start:
{
lean_object* v___x_152_; 
v___x_152_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_liftSymM___redArg(v_k_142_, v_a_143_, v_a_144_, v_a_147_, v_a_148_, v_a_149_, v_a_150_);
return v___x_152_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_liftSymM___boxed(lean_object* v_00_u03b1_153_, lean_object* v_k_154_, lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_, lean_object* v_a_160_, lean_object* v_a_161_, lean_object* v_a_162_, lean_object* v_a_163_){
_start:
{
lean_object* v_res_164_; 
v_res_164_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_liftSymM(v_00_u03b1_153_, v_k_154_, v_a_155_, v_a_156_, v_a_157_, v_a_158_, v_a_159_, v_a_160_, v_a_161_, v_a_162_);
lean_dec(v_a_162_);
lean_dec_ref(v_a_161_);
lean_dec(v_a_160_);
lean_dec_ref(v_a_159_);
lean_dec(v_a_158_);
lean_dec_ref(v_a_157_);
lean_dec(v_a_156_);
lean_dec_ref(v_a_155_);
return v_res_164_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__0___redArg(size_t v_sz_176_, size_t v_i_177_, lean_object* v_bs_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_){
_start:
{
uint8_t v___x_183_; 
v___x_183_ = lean_usize_dec_lt(v_i_177_, v_sz_176_);
if (v___x_183_ == 0)
{
lean_object* v___x_184_; 
v___x_184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_184_, 0, v_bs_178_);
return v___x_184_;
}
else
{
lean_object* v_v_185_; lean_object* v___x_186_; lean_object* v_bs_x27_187_; lean_object* v_a_189_; lean_object* v___y_195_; lean_object* v___x_205_; uint8_t v___x_206_; 
v_v_185_ = lean_array_uget(v_bs_178_, v_i_177_);
v___x_186_ = lean_unsigned_to_nat(0u);
v_bs_x27_187_ = lean_array_uset(v_bs_178_, v_i_177_, v___x_186_);
v___x_205_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__0___redArg___closed__2));
lean_inc(v_v_185_);
v___x_206_ = l_Lean_Syntax_isOfKind(v_v_185_, v___x_205_);
if (v___x_206_ == 0)
{
lean_object* v___x_207_; lean_object* v___x_208_; 
lean_dec(v_v_185_);
v___x_207_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__0___redArg___closed__4));
v___x_208_ = l_Lean_Meta_mkFreshBinderNameForTactic___redArg(v___x_207_, v___y_179_, v___y_180_, v___y_181_);
v___y_195_ = v___x_208_;
goto v___jp_194_;
}
else
{
lean_object* v___x_209_; lean_object* v___x_210_; uint8_t v___x_211_; 
v___x_209_ = l_Lean_Syntax_getArg(v_v_185_, v___x_186_);
lean_dec(v_v_185_);
v___x_210_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__0___redArg___closed__6));
lean_inc(v___x_209_);
v___x_211_ = l_Lean_Syntax_isOfKind(v___x_209_, v___x_210_);
if (v___x_211_ == 0)
{
lean_object* v___x_212_; lean_object* v___x_213_; 
lean_dec(v___x_209_);
v___x_212_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__0___redArg___closed__4));
v___x_213_ = l_Lean_Meta_mkFreshBinderNameForTactic___redArg(v___x_212_, v___y_179_, v___y_180_, v___y_181_);
v___y_195_ = v___x_213_;
goto v___jp_194_;
}
else
{
lean_object* v___x_214_; 
v___x_214_ = l_Lean_TSyntax_getId(v___x_209_);
lean_dec(v___x_209_);
v_a_189_ = v___x_214_;
goto v___jp_188_;
}
}
v___jp_188_:
{
size_t v___x_190_; size_t v___x_191_; lean_object* v___x_192_; 
v___x_190_ = ((size_t)1ULL);
v___x_191_ = lean_usize_add(v_i_177_, v___x_190_);
v___x_192_ = lean_array_uset(v_bs_x27_187_, v_i_177_, v_a_189_);
v_i_177_ = v___x_191_;
v_bs_178_ = v___x_192_;
goto _start;
}
v___jp_194_:
{
if (lean_obj_tag(v___y_195_) == 0)
{
lean_object* v_a_196_; 
v_a_196_ = lean_ctor_get(v___y_195_, 0);
lean_inc(v_a_196_);
lean_dec_ref(v___y_195_);
v_a_189_ = v_a_196_;
goto v___jp_188_;
}
else
{
lean_object* v_a_197_; lean_object* v___x_199_; uint8_t v_isShared_200_; uint8_t v_isSharedCheck_204_; 
lean_dec_ref(v_bs_x27_187_);
v_a_197_ = lean_ctor_get(v___y_195_, 0);
v_isSharedCheck_204_ = !lean_is_exclusive(v___y_195_);
if (v_isSharedCheck_204_ == 0)
{
v___x_199_ = v___y_195_;
v_isShared_200_ = v_isSharedCheck_204_;
goto v_resetjp_198_;
}
else
{
lean_inc(v_a_197_);
lean_dec(v___y_195_);
v___x_199_ = lean_box(0);
v_isShared_200_ = v_isSharedCheck_204_;
goto v_resetjp_198_;
}
v_resetjp_198_:
{
lean_object* v___x_202_; 
if (v_isShared_200_ == 0)
{
v___x_202_ = v___x_199_;
goto v_reusejp_201_;
}
else
{
lean_object* v_reuseFailAlloc_203_; 
v_reuseFailAlloc_203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_203_, 0, v_a_197_);
v___x_202_ = v_reuseFailAlloc_203_;
goto v_reusejp_201_;
}
v_reusejp_201_:
{
return v___x_202_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__0___redArg___boxed(lean_object* v_sz_215_, lean_object* v_i_216_, lean_object* v_bs_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_){
_start:
{
size_t v_sz_boxed_222_; size_t v_i_boxed_223_; lean_object* v_res_224_; 
v_sz_boxed_222_ = lean_unbox_usize(v_sz_215_);
lean_dec(v_sz_215_);
v_i_boxed_223_ = lean_unbox_usize(v_i_216_);
lean_dec(v_i_216_);
v_res_224_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__0___redArg(v_sz_boxed_222_, v_i_boxed_223_, v_bs_217_, v___y_218_, v___y_219_, v___y_220_);
lean_dec(v___y_220_);
lean_dec_ref(v___y_219_);
lean_dec_ref(v___y_218_);
return v_res_224_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore___closed__1(void){
_start:
{
lean_object* v___x_226_; lean_object* v___x_227_; 
v___x_226_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore___closed__0));
v___x_227_ = l_Lean_stringToMessageData(v___x_226_);
return v___x_227_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore___closed__3(void){
_start:
{
lean_object* v___x_229_; lean_object* v___x_230_; 
v___x_229_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore___closed__2));
v___x_230_ = l_Lean_stringToMessageData(v___x_229_);
return v___x_230_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore(uint8_t v_internalize_231_, lean_object* v_ids_232_, lean_object* v_a_233_, lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_, lean_object* v_a_239_, lean_object* v_a_240_){
_start:
{
lean_object* v_goal_243_; lean_object* v___y_244_; lean_object* v___y_245_; lean_object* v___y_246_; lean_object* v___y_247_; lean_object* v___y_248_; lean_object* v_goal_253_; lean_object* v___y_254_; lean_object* v___y_255_; lean_object* v___y_256_; lean_object* v___y_257_; lean_object* v___y_258_; lean_object* v___y_259_; lean_object* v___x_271_; 
v___x_271_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_ensureSym(v_a_233_, v_a_234_, v_a_235_, v_a_236_, v_a_237_, v_a_238_, v_a_239_, v_a_240_);
if (lean_obj_tag(v___x_271_) == 0)
{
lean_object* v___x_272_; 
lean_dec_ref(v___x_271_);
v___x_272_ = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(v_a_234_, v_a_237_, v_a_238_, v_a_239_, v_a_240_);
if (lean_obj_tag(v___x_272_) == 0)
{
lean_object* v_a_273_; lean_object* v___x_274_; lean_object* v___x_275_; uint8_t v___x_276_; 
v_a_273_ = lean_ctor_get(v___x_272_, 0);
lean_inc(v_a_273_);
lean_dec_ref(v___x_272_);
v___x_274_ = lean_array_get_size(v_ids_232_);
v___x_275_ = lean_unsigned_to_nat(0u);
v___x_276_ = lean_nat_dec_eq(v___x_274_, v___x_275_);
if (v___x_276_ == 0)
{
size_t v_sz_277_; size_t v___x_278_; lean_object* v___x_279_; 
v_sz_277_ = lean_array_size(v_ids_232_);
v___x_278_ = ((size_t)0ULL);
v___x_279_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__0___redArg(v_sz_277_, v___x_278_, v_ids_232_, v_a_237_, v_a_239_, v_a_240_);
if (lean_obj_tag(v___x_279_) == 0)
{
lean_object* v_a_280_; lean_object* v___x_281_; lean_object* v___x_282_; 
v_a_280_ = lean_ctor_get(v___x_279_, 0);
lean_inc(v_a_280_);
lean_dec_ref(v___x_279_);
v___x_281_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Goal_intros___boxed), 9, 2);
lean_closure_set(v___x_281_, 0, v_a_273_);
lean_closure_set(v___x_281_, 1, v_a_280_);
v___x_282_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_liftSymM___redArg(v___x_281_, v_a_233_, v_a_234_, v_a_237_, v_a_238_, v_a_239_, v_a_240_);
if (lean_obj_tag(v___x_282_) == 0)
{
lean_object* v_a_283_; 
v_a_283_ = lean_ctor_get(v___x_282_, 0);
lean_inc(v_a_283_);
lean_dec_ref(v___x_282_);
if (lean_obj_tag(v_a_283_) == 0)
{
lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v_a_286_; lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_293_; 
v___x_284_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore___closed__1, &l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore___closed__1);
v___x_285_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_ensureSym_spec__0___redArg(v___x_284_, v_a_237_, v_a_238_, v_a_239_, v_a_240_);
v_a_286_ = lean_ctor_get(v___x_285_, 0);
v_isSharedCheck_293_ = !lean_is_exclusive(v___x_285_);
if (v_isSharedCheck_293_ == 0)
{
v___x_288_ = v___x_285_;
v_isShared_289_ = v_isSharedCheck_293_;
goto v_resetjp_287_;
}
else
{
lean_inc(v_a_286_);
lean_dec(v___x_285_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_293_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
lean_object* v___x_291_; 
if (v_isShared_289_ == 0)
{
v___x_291_ = v___x_288_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v_a_286_);
v___x_291_ = v_reuseFailAlloc_292_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
return v___x_291_;
}
}
}
else
{
lean_object* v_goal_294_; 
v_goal_294_ = lean_ctor_get(v_a_283_, 1);
lean_inc_ref(v_goal_294_);
lean_dec_ref(v_a_283_);
v_goal_253_ = v_goal_294_;
v___y_254_ = v_a_233_;
v___y_255_ = v_a_234_;
v___y_256_ = v_a_237_;
v___y_257_ = v_a_238_;
v___y_258_ = v_a_239_;
v___y_259_ = v_a_240_;
goto v___jp_252_;
}
}
else
{
lean_object* v_a_295_; lean_object* v___x_297_; uint8_t v_isShared_298_; uint8_t v_isSharedCheck_302_; 
v_a_295_ = lean_ctor_get(v___x_282_, 0);
v_isSharedCheck_302_ = !lean_is_exclusive(v___x_282_);
if (v_isSharedCheck_302_ == 0)
{
v___x_297_ = v___x_282_;
v_isShared_298_ = v_isSharedCheck_302_;
goto v_resetjp_296_;
}
else
{
lean_inc(v_a_295_);
lean_dec(v___x_282_);
v___x_297_ = lean_box(0);
v_isShared_298_ = v_isSharedCheck_302_;
goto v_resetjp_296_;
}
v_resetjp_296_:
{
lean_object* v___x_300_; 
if (v_isShared_298_ == 0)
{
v___x_300_ = v___x_297_;
goto v_reusejp_299_;
}
else
{
lean_object* v_reuseFailAlloc_301_; 
v_reuseFailAlloc_301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_301_, 0, v_a_295_);
v___x_300_ = v_reuseFailAlloc_301_;
goto v_reusejp_299_;
}
v_reusejp_299_:
{
return v___x_300_;
}
}
}
}
else
{
lean_object* v_a_303_; lean_object* v___x_305_; uint8_t v_isShared_306_; uint8_t v_isSharedCheck_310_; 
lean_dec(v_a_273_);
v_a_303_ = lean_ctor_get(v___x_279_, 0);
v_isSharedCheck_310_ = !lean_is_exclusive(v___x_279_);
if (v_isSharedCheck_310_ == 0)
{
v___x_305_ = v___x_279_;
v_isShared_306_ = v_isSharedCheck_310_;
goto v_resetjp_304_;
}
else
{
lean_inc(v_a_303_);
lean_dec(v___x_279_);
v___x_305_ = lean_box(0);
v_isShared_306_ = v_isSharedCheck_310_;
goto v_resetjp_304_;
}
v_resetjp_304_:
{
lean_object* v___x_308_; 
if (v_isShared_306_ == 0)
{
v___x_308_ = v___x_305_;
goto v_reusejp_307_;
}
else
{
lean_object* v_reuseFailAlloc_309_; 
v_reuseFailAlloc_309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_309_, 0, v_a_303_);
v___x_308_ = v_reuseFailAlloc_309_;
goto v_reusejp_307_;
}
v_reusejp_307_:
{
return v___x_308_;
}
}
}
}
else
{
lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
lean_dec_ref(v_ids_232_);
v___x_311_ = lean_unsigned_to_nat(1u);
v___x_312_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Goal_introN___boxed), 9, 2);
lean_closure_set(v___x_312_, 0, v_a_273_);
lean_closure_set(v___x_312_, 1, v___x_311_);
v___x_313_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_liftSymM___redArg(v___x_312_, v_a_233_, v_a_234_, v_a_237_, v_a_238_, v_a_239_, v_a_240_);
if (lean_obj_tag(v___x_313_) == 0)
{
lean_object* v_a_314_; 
v_a_314_ = lean_ctor_get(v___x_313_, 0);
lean_inc(v_a_314_);
lean_dec_ref(v___x_313_);
if (lean_obj_tag(v_a_314_) == 0)
{
lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v_a_317_; lean_object* v___x_319_; uint8_t v_isShared_320_; uint8_t v_isSharedCheck_324_; 
v___x_315_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore___closed__3, &l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore___closed__3);
v___x_316_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_ensureSym_spec__0___redArg(v___x_315_, v_a_237_, v_a_238_, v_a_239_, v_a_240_);
v_a_317_ = lean_ctor_get(v___x_316_, 0);
v_isSharedCheck_324_ = !lean_is_exclusive(v___x_316_);
if (v_isSharedCheck_324_ == 0)
{
v___x_319_ = v___x_316_;
v_isShared_320_ = v_isSharedCheck_324_;
goto v_resetjp_318_;
}
else
{
lean_inc(v_a_317_);
lean_dec(v___x_316_);
v___x_319_ = lean_box(0);
v_isShared_320_ = v_isSharedCheck_324_;
goto v_resetjp_318_;
}
v_resetjp_318_:
{
lean_object* v___x_322_; 
if (v_isShared_320_ == 0)
{
v___x_322_ = v___x_319_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_323_; 
v_reuseFailAlloc_323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_323_, 0, v_a_317_);
v___x_322_ = v_reuseFailAlloc_323_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
return v___x_322_;
}
}
}
else
{
lean_object* v_goal_325_; 
v_goal_325_ = lean_ctor_get(v_a_314_, 1);
lean_inc_ref(v_goal_325_);
lean_dec_ref(v_a_314_);
v_goal_253_ = v_goal_325_;
v___y_254_ = v_a_233_;
v___y_255_ = v_a_234_;
v___y_256_ = v_a_237_;
v___y_257_ = v_a_238_;
v___y_258_ = v_a_239_;
v___y_259_ = v_a_240_;
goto v___jp_252_;
}
}
else
{
lean_object* v_a_326_; lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_333_; 
v_a_326_ = lean_ctor_get(v___x_313_, 0);
v_isSharedCheck_333_ = !lean_is_exclusive(v___x_313_);
if (v_isSharedCheck_333_ == 0)
{
v___x_328_ = v___x_313_;
v_isShared_329_ = v_isSharedCheck_333_;
goto v_resetjp_327_;
}
else
{
lean_inc(v_a_326_);
lean_dec(v___x_313_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_333_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
lean_object* v___x_331_; 
if (v_isShared_329_ == 0)
{
v___x_331_ = v___x_328_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v_a_326_);
v___x_331_ = v_reuseFailAlloc_332_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
return v___x_331_;
}
}
}
}
}
else
{
lean_object* v_a_334_; lean_object* v___x_336_; uint8_t v_isShared_337_; uint8_t v_isSharedCheck_341_; 
lean_dec_ref(v_ids_232_);
v_a_334_ = lean_ctor_get(v___x_272_, 0);
v_isSharedCheck_341_ = !lean_is_exclusive(v___x_272_);
if (v_isSharedCheck_341_ == 0)
{
v___x_336_ = v___x_272_;
v_isShared_337_ = v_isSharedCheck_341_;
goto v_resetjp_335_;
}
else
{
lean_inc(v_a_334_);
lean_dec(v___x_272_);
v___x_336_ = lean_box(0);
v_isShared_337_ = v_isSharedCheck_341_;
goto v_resetjp_335_;
}
v_resetjp_335_:
{
lean_object* v___x_339_; 
if (v_isShared_337_ == 0)
{
v___x_339_ = v___x_336_;
goto v_reusejp_338_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v_a_334_);
v___x_339_ = v_reuseFailAlloc_340_;
goto v_reusejp_338_;
}
v_reusejp_338_:
{
return v___x_339_;
}
}
}
}
else
{
lean_dec_ref(v_ids_232_);
return v___x_271_;
}
v___jp_242_:
{
lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; 
v___x_249_ = lean_box(0);
v___x_250_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_250_, 0, v_goal_243_);
lean_ctor_set(v___x_250_, 1, v___x_249_);
v___x_251_ = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(v___x_250_, v___y_244_, v___y_245_, v___y_246_, v___y_247_, v___y_248_);
return v___x_251_;
}
v___jp_252_:
{
if (v_internalize_231_ == 0)
{
v_goal_243_ = v_goal_253_;
v___y_244_ = v___y_255_;
v___y_245_ = v___y_256_;
v___y_246_ = v___y_257_;
v___y_247_ = v___y_258_;
v___y_248_ = v___y_259_;
goto v___jp_242_;
}
else
{
lean_object* v___x_260_; lean_object* v___x_261_; 
v___x_260_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Goal_internalizeAll___boxed), 11, 1);
lean_closure_set(v___x_260_, 0, v_goal_253_);
v___x_261_ = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(v___x_260_, v___y_254_, v___y_255_, v___y_256_, v___y_257_, v___y_258_, v___y_259_);
if (lean_obj_tag(v___x_261_) == 0)
{
lean_object* v_a_262_; 
v_a_262_ = lean_ctor_get(v___x_261_, 0);
lean_inc(v_a_262_);
lean_dec_ref(v___x_261_);
v_goal_243_ = v_a_262_;
v___y_244_ = v___y_255_;
v___y_245_ = v___y_256_;
v___y_246_ = v___y_257_;
v___y_247_ = v___y_258_;
v___y_248_ = v___y_259_;
goto v___jp_242_;
}
else
{
lean_object* v_a_263_; lean_object* v___x_265_; uint8_t v_isShared_266_; uint8_t v_isSharedCheck_270_; 
v_a_263_ = lean_ctor_get(v___x_261_, 0);
v_isSharedCheck_270_ = !lean_is_exclusive(v___x_261_);
if (v_isSharedCheck_270_ == 0)
{
v___x_265_ = v___x_261_;
v_isShared_266_ = v_isSharedCheck_270_;
goto v_resetjp_264_;
}
else
{
lean_inc(v_a_263_);
lean_dec(v___x_261_);
v___x_265_ = lean_box(0);
v_isShared_266_ = v_isSharedCheck_270_;
goto v_resetjp_264_;
}
v_resetjp_264_:
{
lean_object* v___x_268_; 
if (v_isShared_266_ == 0)
{
v___x_268_ = v___x_265_;
goto v_reusejp_267_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_269_, 0, v_a_263_);
v___x_268_ = v_reuseFailAlloc_269_;
goto v_reusejp_267_;
}
v_reusejp_267_:
{
return v___x_268_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore___boxed(lean_object* v_internalize_342_, lean_object* v_ids_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_a_352_){
_start:
{
uint8_t v_internalize_boxed_353_; lean_object* v_res_354_; 
v_internalize_boxed_353_ = lean_unbox(v_internalize_342_);
v_res_354_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore(v_internalize_boxed_353_, v_ids_343_, v_a_344_, v_a_345_, v_a_346_, v_a_347_, v_a_348_, v_a_349_, v_a_350_, v_a_351_);
lean_dec(v_a_351_);
lean_dec_ref(v_a_350_);
lean_dec(v_a_349_);
lean_dec_ref(v_a_348_);
lean_dec(v_a_347_);
lean_dec_ref(v_a_346_);
lean_dec(v_a_345_);
lean_dec_ref(v_a_344_);
return v_res_354_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__0(size_t v_sz_355_, size_t v_i_356_, lean_object* v_bs_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_){
_start:
{
lean_object* v___x_367_; 
v___x_367_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__0___redArg(v_sz_355_, v_i_356_, v_bs_357_, v___y_362_, v___y_364_, v___y_365_);
return v___x_367_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__0___boxed(lean_object* v_sz_368_, lean_object* v_i_369_, lean_object* v_bs_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_){
_start:
{
size_t v_sz_boxed_380_; size_t v_i_boxed_381_; lean_object* v_res_382_; 
v_sz_boxed_380_ = lean_unbox_usize(v_sz_368_);
lean_dec(v_sz_368_);
v_i_boxed_381_ = lean_unbox_usize(v_i_369_);
lean_dec(v_i_369_);
v_res_382_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__0(v_sz_boxed_380_, v_i_boxed_381_, v_bs_370_, v___y_371_, v___y_372_, v___y_373_, v___y_374_, v___y_375_, v___y_376_, v___y_377_, v___y_378_);
lean_dec(v___y_378_);
lean_dec_ref(v___y_377_);
lean_dec(v___y_376_);
lean_dec_ref(v___y_375_);
lean_dec(v___y_374_);
lean_dec_ref(v___y_373_);
lean_dec(v___y_372_);
lean_dec_ref(v___y_371_);
return v_res_382_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; 
v___x_383_ = lean_box(0);
v___x_384_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_385_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_385_, 0, v___x_384_);
lean_ctor_set(v___x_385_, 1, v___x_383_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro_spec__0___redArg(){
_start:
{
lean_object* v___x_387_; lean_object* v___x_388_; 
v___x_387_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro_spec__0___redArg___closed__0);
v___x_388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_388_, 0, v___x_387_);
return v___x_388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro_spec__0___redArg___boxed(lean_object* v___y_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro_spec__0___redArg();
return v_res_390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro_spec__0(lean_object* v_00_u03b1_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_){
_start:
{
lean_object* v___x_401_; 
v___x_401_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro_spec__0___redArg();
return v___x_401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro_spec__0___boxed(lean_object* v_00_u03b1_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_){
_start:
{
lean_object* v_res_412_; 
v_res_412_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro_spec__0(v_00_u03b1_402_, v___y_403_, v___y_404_, v___y_405_, v___y_406_, v___y_407_, v___y_408_, v___y_409_, v___y_410_);
lean_dec(v___y_410_);
lean_dec_ref(v___y_409_);
lean_dec(v___y_408_);
lean_dec_ref(v___y_407_);
lean_dec(v___y_406_);
lean_dec_ref(v___y_405_);
lean_dec(v___y_404_);
lean_dec_ref(v___y_403_);
return v_res_412_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro(lean_object* v_stx_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_){
_start:
{
lean_object* v___x_442_; uint8_t v___x_443_; 
v___x_442_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___closed__4));
lean_inc(v_stx_432_);
v___x_443_ = l_Lean_Syntax_isOfKind(v_stx_432_, v___x_442_);
if (v___x_443_ == 0)
{
lean_object* v___x_444_; 
lean_dec(v_stx_432_);
v___x_444_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro_spec__0___redArg();
return v___x_444_;
}
else
{
lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; uint8_t v___x_448_; 
v___x_445_ = lean_unsigned_to_nat(0u);
v___x_446_ = lean_unsigned_to_nat(1u);
v___x_447_ = l_Lean_Syntax_getArg(v_stx_432_, v___x_446_);
lean_inc(v___x_447_);
v___x_448_ = l_Lean_Syntax_matchesNull(v___x_447_, v___x_445_);
if (v___x_448_ == 0)
{
lean_object* v___x_449_; uint8_t v___x_450_; 
v___x_449_ = lean_unsigned_to_nat(5u);
lean_inc(v___x_447_);
v___x_450_ = l_Lean_Syntax_matchesNull(v___x_447_, v___x_449_);
if (v___x_450_ == 0)
{
lean_object* v___x_451_; 
lean_dec(v___x_447_);
lean_dec(v_stx_432_);
v___x_451_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro_spec__0___redArg();
return v___x_451_;
}
else
{
lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; uint8_t v___x_456_; 
v___x_452_ = lean_unsigned_to_nat(2u);
v___x_453_ = lean_unsigned_to_nat(3u);
v___x_454_ = l_Lean_Syntax_getArg(v___x_447_, v___x_453_);
lean_dec(v___x_447_);
v___x_455_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___closed__7));
lean_inc(v___x_454_);
v___x_456_ = l_Lean_Syntax_isOfKind(v___x_454_, v___x_455_);
if (v___x_456_ == 0)
{
lean_object* v___x_457_; uint8_t v___x_458_; 
v___x_457_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___closed__9));
v___x_458_ = l_Lean_Syntax_isOfKind(v___x_454_, v___x_457_);
if (v___x_458_ == 0)
{
lean_object* v___x_459_; 
lean_dec(v_stx_432_);
v___x_459_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro_spec__0___redArg();
return v___x_459_;
}
else
{
lean_object* v___x_460_; lean_object* v_ids_461_; lean_object* v___x_462_; 
v___x_460_ = l_Lean_Syntax_getArg(v_stx_432_, v___x_452_);
lean_dec(v_stx_432_);
v_ids_461_ = l_Lean_Syntax_getArgs(v___x_460_);
lean_dec(v___x_460_);
v___x_462_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore(v___x_443_, v_ids_461_, v_a_433_, v_a_434_, v_a_435_, v_a_436_, v_a_437_, v_a_438_, v_a_439_, v_a_440_);
return v___x_462_;
}
}
else
{
lean_object* v___x_463_; lean_object* v_ids_464_; lean_object* v___x_465_; 
lean_dec(v___x_454_);
v___x_463_ = l_Lean_Syntax_getArg(v_stx_432_, v___x_452_);
lean_dec(v_stx_432_);
v_ids_464_ = l_Lean_Syntax_getArgs(v___x_463_);
lean_dec(v___x_463_);
v___x_465_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore(v___x_448_, v_ids_464_, v_a_433_, v_a_434_, v_a_435_, v_a_436_, v_a_437_, v_a_438_, v_a_439_, v_a_440_);
return v___x_465_;
}
}
}
else
{
lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v_ids_468_; lean_object* v___x_469_; 
lean_dec(v___x_447_);
v___x_466_ = lean_unsigned_to_nat(2u);
v___x_467_ = l_Lean_Syntax_getArg(v_stx_432_, v___x_466_);
lean_dec(v_stx_432_);
v_ids_468_ = l_Lean_Syntax_getArgs(v___x_467_);
lean_dec(v___x_467_);
v___x_469_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore(v___x_443_, v_ids_468_, v_a_433_, v_a_434_, v_a_435_, v_a_436_, v_a_437_, v_a_438_, v_a_439_, v_a_440_);
return v___x_469_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___boxed(lean_object* v_stx_470_, lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_, lean_object* v_a_479_){
_start:
{
lean_object* v_res_480_; 
v_res_480_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro(v_stx_470_, v_a_471_, v_a_472_, v_a_473_, v_a_474_, v_a_475_, v_a_476_, v_a_477_, v_a_478_);
lean_dec(v_a_478_);
lean_dec_ref(v_a_477_);
lean_dec(v_a_476_);
lean_dec_ref(v_a_475_);
lean_dec(v_a_474_);
lean_dec_ref(v_a_473_);
lean_dec(v_a_472_);
lean_dec_ref(v_a_471_);
return v_res_480_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro__1(){
_start:
{
lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; 
v___x_522_ = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
v___x_523_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___closed__4));
v___x_524_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro__1___closed__15));
v___x_525_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___boxed), 10, 0);
v___x_526_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_522_, v___x_523_, v___x_524_, v___x_525_);
return v___x_526_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro__1___boxed(lean_object* v_a_527_){
_start:
{
lean_object* v_res_528_; 
v_res_528_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro__1();
return v_res_528_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntrosCore___closed__2(void){
_start:
{
lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_532_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntrosCore___closed__1));
v___x_533_ = l_Lean_stringToMessageData(v___x_532_);
return v___x_533_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntrosCore(uint8_t v_internalize_534_, lean_object* v_a_535_, lean_object* v_a_536_, lean_object* v_a_537_, lean_object* v_a_538_, lean_object* v_a_539_, lean_object* v_a_540_, lean_object* v_a_541_, lean_object* v_a_542_){
_start:
{
lean_object* v_goal_545_; lean_object* v___y_546_; lean_object* v___y_547_; lean_object* v___y_548_; lean_object* v___y_549_; lean_object* v___y_550_; lean_object* v___x_554_; 
v___x_554_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_ensureSym(v_a_535_, v_a_536_, v_a_537_, v_a_538_, v_a_539_, v_a_540_, v_a_541_, v_a_542_);
if (lean_obj_tag(v___x_554_) == 0)
{
lean_object* v___x_555_; 
lean_dec_ref(v___x_554_);
v___x_555_ = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(v_a_536_, v_a_539_, v_a_540_, v_a_541_, v_a_542_);
if (lean_obj_tag(v___x_555_) == 0)
{
lean_object* v_a_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; 
v_a_556_ = lean_ctor_get(v___x_555_, 0);
lean_inc(v_a_556_);
lean_dec_ref(v___x_555_);
v___x_557_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntrosCore___closed__0));
v___x_558_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Goal_intros___boxed), 9, 2);
lean_closure_set(v___x_558_, 0, v_a_556_);
lean_closure_set(v___x_558_, 1, v___x_557_);
v___x_559_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_liftSymM___redArg(v___x_558_, v_a_535_, v_a_536_, v_a_539_, v_a_540_, v_a_541_, v_a_542_);
if (lean_obj_tag(v___x_559_) == 0)
{
lean_object* v_a_560_; 
v_a_560_ = lean_ctor_get(v___x_559_, 0);
lean_inc(v_a_560_);
lean_dec_ref(v___x_559_);
if (lean_obj_tag(v_a_560_) == 0)
{
lean_object* v___x_561_; lean_object* v___x_562_; 
v___x_561_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntrosCore___closed__2, &l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntrosCore___closed__2_once, _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntrosCore___closed__2);
v___x_562_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_ensureSym_spec__0___redArg(v___x_561_, v_a_539_, v_a_540_, v_a_541_, v_a_542_);
return v___x_562_;
}
else
{
if (v_internalize_534_ == 0)
{
lean_object* v_goal_563_; 
v_goal_563_ = lean_ctor_get(v_a_560_, 1);
lean_inc_ref(v_goal_563_);
lean_dec_ref(v_a_560_);
v_goal_545_ = v_goal_563_;
v___y_546_ = v_a_536_;
v___y_547_ = v_a_539_;
v___y_548_ = v_a_540_;
v___y_549_ = v_a_541_;
v___y_550_ = v_a_542_;
goto v___jp_544_;
}
else
{
lean_object* v_goal_564_; lean_object* v___x_565_; lean_object* v___x_566_; 
v_goal_564_ = lean_ctor_get(v_a_560_, 1);
lean_inc_ref(v_goal_564_);
lean_dec_ref(v_a_560_);
v___x_565_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Goal_internalizeAll___boxed), 11, 1);
lean_closure_set(v___x_565_, 0, v_goal_564_);
v___x_566_ = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(v___x_565_, v_a_535_, v_a_536_, v_a_539_, v_a_540_, v_a_541_, v_a_542_);
if (lean_obj_tag(v___x_566_) == 0)
{
lean_object* v_a_567_; 
v_a_567_ = lean_ctor_get(v___x_566_, 0);
lean_inc(v_a_567_);
lean_dec_ref(v___x_566_);
v_goal_545_ = v_a_567_;
v___y_546_ = v_a_536_;
v___y_547_ = v_a_539_;
v___y_548_ = v_a_540_;
v___y_549_ = v_a_541_;
v___y_550_ = v_a_542_;
goto v___jp_544_;
}
else
{
lean_object* v_a_568_; lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_575_; 
v_a_568_ = lean_ctor_get(v___x_566_, 0);
v_isSharedCheck_575_ = !lean_is_exclusive(v___x_566_);
if (v_isSharedCheck_575_ == 0)
{
v___x_570_ = v___x_566_;
v_isShared_571_ = v_isSharedCheck_575_;
goto v_resetjp_569_;
}
else
{
lean_inc(v_a_568_);
lean_dec(v___x_566_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_575_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
lean_object* v___x_573_; 
if (v_isShared_571_ == 0)
{
v___x_573_ = v___x_570_;
goto v_reusejp_572_;
}
else
{
lean_object* v_reuseFailAlloc_574_; 
v_reuseFailAlloc_574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_574_, 0, v_a_568_);
v___x_573_ = v_reuseFailAlloc_574_;
goto v_reusejp_572_;
}
v_reusejp_572_:
{
return v___x_573_;
}
}
}
}
}
}
else
{
lean_object* v_a_576_; lean_object* v___x_578_; uint8_t v_isShared_579_; uint8_t v_isSharedCheck_583_; 
v_a_576_ = lean_ctor_get(v___x_559_, 0);
v_isSharedCheck_583_ = !lean_is_exclusive(v___x_559_);
if (v_isSharedCheck_583_ == 0)
{
v___x_578_ = v___x_559_;
v_isShared_579_ = v_isSharedCheck_583_;
goto v_resetjp_577_;
}
else
{
lean_inc(v_a_576_);
lean_dec(v___x_559_);
v___x_578_ = lean_box(0);
v_isShared_579_ = v_isSharedCheck_583_;
goto v_resetjp_577_;
}
v_resetjp_577_:
{
lean_object* v___x_581_; 
if (v_isShared_579_ == 0)
{
v___x_581_ = v___x_578_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v_a_576_);
v___x_581_ = v_reuseFailAlloc_582_;
goto v_reusejp_580_;
}
v_reusejp_580_:
{
return v___x_581_;
}
}
}
}
else
{
lean_object* v_a_584_; lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_591_; 
v_a_584_ = lean_ctor_get(v___x_555_, 0);
v_isSharedCheck_591_ = !lean_is_exclusive(v___x_555_);
if (v_isSharedCheck_591_ == 0)
{
v___x_586_ = v___x_555_;
v_isShared_587_ = v_isSharedCheck_591_;
goto v_resetjp_585_;
}
else
{
lean_inc(v_a_584_);
lean_dec(v___x_555_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_591_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
lean_object* v___x_589_; 
if (v_isShared_587_ == 0)
{
v___x_589_ = v___x_586_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v_a_584_);
v___x_589_ = v_reuseFailAlloc_590_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
return v___x_589_;
}
}
}
}
else
{
return v___x_554_;
}
v___jp_544_:
{
lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; 
v___x_551_ = lean_box(0);
v___x_552_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_552_, 0, v_goal_545_);
lean_ctor_set(v___x_552_, 1, v___x_551_);
v___x_553_ = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(v___x_552_, v___y_546_, v___y_547_, v___y_548_, v___y_549_, v___y_550_);
return v___x_553_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntrosCore___boxed(lean_object* v_internalize_592_, lean_object* v_a_593_, lean_object* v_a_594_, lean_object* v_a_595_, lean_object* v_a_596_, lean_object* v_a_597_, lean_object* v_a_598_, lean_object* v_a_599_, lean_object* v_a_600_, lean_object* v_a_601_){
_start:
{
uint8_t v_internalize_boxed_602_; lean_object* v_res_603_; 
v_internalize_boxed_602_ = lean_unbox(v_internalize_592_);
v_res_603_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntrosCore(v_internalize_boxed_602_, v_a_593_, v_a_594_, v_a_595_, v_a_596_, v_a_597_, v_a_598_, v_a_599_, v_a_600_);
lean_dec(v_a_600_);
lean_dec_ref(v_a_599_);
lean_dec(v_a_598_);
lean_dec_ref(v_a_597_);
lean_dec(v_a_596_);
lean_dec_ref(v_a_595_);
lean_dec(v_a_594_);
lean_dec_ref(v_a_593_);
return v_res_603_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntros(lean_object* v_stx_611_, lean_object* v_a_612_, lean_object* v_a_613_, lean_object* v_a_614_, lean_object* v_a_615_, lean_object* v_a_616_, lean_object* v_a_617_, lean_object* v_a_618_, lean_object* v_a_619_){
_start:
{
lean_object* v___x_621_; uint8_t v___x_622_; 
v___x_621_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntros___closed__1));
lean_inc(v_stx_611_);
v___x_622_ = l_Lean_Syntax_isOfKind(v_stx_611_, v___x_621_);
if (v___x_622_ == 0)
{
lean_object* v___x_623_; 
lean_dec(v_stx_611_);
v___x_623_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro_spec__0___redArg();
return v___x_623_;
}
else
{
lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; uint8_t v___x_627_; 
v___x_624_ = lean_unsigned_to_nat(0u);
v___x_625_ = lean_unsigned_to_nat(1u);
v___x_626_ = l_Lean_Syntax_getArg(v_stx_611_, v___x_625_);
lean_dec(v_stx_611_);
lean_inc(v___x_626_);
v___x_627_ = l_Lean_Syntax_matchesNull(v___x_626_, v___x_624_);
if (v___x_627_ == 0)
{
lean_object* v___x_628_; uint8_t v___x_629_; 
v___x_628_ = lean_unsigned_to_nat(5u);
lean_inc(v___x_626_);
v___x_629_ = l_Lean_Syntax_matchesNull(v___x_626_, v___x_628_);
if (v___x_629_ == 0)
{
lean_object* v___x_630_; 
lean_dec(v___x_626_);
v___x_630_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro_spec__0___redArg();
return v___x_630_;
}
else
{
lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; uint8_t v___x_634_; 
v___x_631_ = lean_unsigned_to_nat(3u);
v___x_632_ = l_Lean_Syntax_getArg(v___x_626_, v___x_631_);
lean_dec(v___x_626_);
v___x_633_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___closed__7));
lean_inc(v___x_632_);
v___x_634_ = l_Lean_Syntax_isOfKind(v___x_632_, v___x_633_);
if (v___x_634_ == 0)
{
lean_object* v___x_635_; uint8_t v___x_636_; 
v___x_635_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___closed__9));
v___x_636_ = l_Lean_Syntax_isOfKind(v___x_632_, v___x_635_);
if (v___x_636_ == 0)
{
lean_object* v___x_637_; 
v___x_637_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro_spec__0___redArg();
return v___x_637_;
}
else
{
lean_object* v___x_638_; 
v___x_638_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntrosCore(v___x_622_, v_a_612_, v_a_613_, v_a_614_, v_a_615_, v_a_616_, v_a_617_, v_a_618_, v_a_619_);
return v___x_638_;
}
}
else
{
lean_object* v___x_639_; 
lean_dec(v___x_632_);
v___x_639_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntrosCore(v___x_627_, v_a_612_, v_a_613_, v_a_614_, v_a_615_, v_a_616_, v_a_617_, v_a_618_, v_a_619_);
return v___x_639_;
}
}
}
else
{
lean_object* v___x_640_; 
lean_dec(v___x_626_);
v___x_640_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntrosCore(v___x_622_, v_a_612_, v_a_613_, v_a_614_, v_a_615_, v_a_616_, v_a_617_, v_a_618_, v_a_619_);
return v___x_640_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntros___boxed(lean_object* v_stx_641_, lean_object* v_a_642_, lean_object* v_a_643_, lean_object* v_a_644_, lean_object* v_a_645_, lean_object* v_a_646_, lean_object* v_a_647_, lean_object* v_a_648_, lean_object* v_a_649_, lean_object* v_a_650_){
_start:
{
lean_object* v_res_651_; 
v_res_651_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntros(v_stx_641_, v_a_642_, v_a_643_, v_a_644_, v_a_645_, v_a_646_, v_a_647_, v_a_648_, v_a_649_);
lean_dec(v_a_649_);
lean_dec_ref(v_a_648_);
lean_dec(v_a_647_);
lean_dec_ref(v_a_646_);
lean_dec(v_a_645_);
lean_dec_ref(v_a_644_);
lean_dec(v_a_643_);
lean_dec_ref(v_a_642_);
return v_res_651_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntros___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntros__1(){
_start:
{
lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; 
v___x_657_ = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
v___x_658_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntros___closed__1));
v___x_659_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntros___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntros__1___closed__1));
v___x_660_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntros___boxed), 10, 0);
v___x_661_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_657_, v___x_658_, v___x_659_, v___x_660_);
return v___x_661_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntros___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntros__1___boxed(lean_object* v_a_662_){
_start:
{
lean_object* v_res_663_; 
v_res_663_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntros___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntros__1();
return v_res_663_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_664_, lean_object* v_vals_665_, lean_object* v_i_666_, lean_object* v_k_667_){
_start:
{
lean_object* v___x_668_; uint8_t v___x_669_; 
v___x_668_ = lean_array_get_size(v_keys_664_);
v___x_669_ = lean_nat_dec_lt(v_i_666_, v___x_668_);
if (v___x_669_ == 0)
{
lean_object* v___x_670_; 
lean_dec(v_i_666_);
v___x_670_ = lean_box(0);
return v___x_670_;
}
else
{
lean_object* v_k_x27_671_; uint8_t v___x_672_; 
v_k_x27_671_ = lean_array_fget_borrowed(v_keys_664_, v_i_666_);
v___x_672_ = lean_name_eq(v_k_667_, v_k_x27_671_);
if (v___x_672_ == 0)
{
lean_object* v___x_673_; lean_object* v___x_674_; 
v___x_673_ = lean_unsigned_to_nat(1u);
v___x_674_ = lean_nat_add(v_i_666_, v___x_673_);
lean_dec(v_i_666_);
v_i_666_ = v___x_674_;
goto _start;
}
else
{
lean_object* v___x_676_; lean_object* v___x_677_; 
v___x_676_ = lean_array_fget_borrowed(v_vals_665_, v_i_666_);
lean_dec(v_i_666_);
lean_inc(v___x_676_);
v___x_677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_677_, 0, v___x_676_);
return v___x_677_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_678_, lean_object* v_vals_679_, lean_object* v_i_680_, lean_object* v_k_681_){
_start:
{
lean_object* v_res_682_; 
v_res_682_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0_spec__0_spec__1___redArg(v_keys_678_, v_vals_679_, v_i_680_, v_k_681_);
lean_dec(v_k_681_);
lean_dec_ref(v_vals_679_);
lean_dec_ref(v_keys_678_);
return v_res_682_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0_spec__0___redArg___closed__0(void){
_start:
{
size_t v___x_683_; size_t v___x_684_; size_t v___x_685_; 
v___x_683_ = ((size_t)5ULL);
v___x_684_ = ((size_t)1ULL);
v___x_685_ = lean_usize_shift_left(v___x_684_, v___x_683_);
return v___x_685_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_686_; size_t v___x_687_; size_t v___x_688_; 
v___x_686_ = ((size_t)1ULL);
v___x_687_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0_spec__0___redArg___closed__0);
v___x_688_ = lean_usize_sub(v___x_687_, v___x_686_);
return v___x_688_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0_spec__0___redArg(lean_object* v_x_689_, size_t v_x_690_, lean_object* v_x_691_){
_start:
{
if (lean_obj_tag(v_x_689_) == 0)
{
lean_object* v_es_692_; lean_object* v___x_693_; size_t v___x_694_; size_t v___x_695_; size_t v___x_696_; lean_object* v_j_697_; lean_object* v___x_698_; 
v_es_692_ = lean_ctor_get(v_x_689_, 0);
v___x_693_ = lean_box(2);
v___x_694_ = ((size_t)5ULL);
v___x_695_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0_spec__0___redArg___closed__1);
v___x_696_ = lean_usize_land(v_x_690_, v___x_695_);
v_j_697_ = lean_usize_to_nat(v___x_696_);
v___x_698_ = lean_array_get_borrowed(v___x_693_, v_es_692_, v_j_697_);
lean_dec(v_j_697_);
switch(lean_obj_tag(v___x_698_))
{
case 0:
{
lean_object* v_key_699_; lean_object* v_val_700_; uint8_t v___x_701_; 
v_key_699_ = lean_ctor_get(v___x_698_, 0);
v_val_700_ = lean_ctor_get(v___x_698_, 1);
v___x_701_ = lean_name_eq(v_x_691_, v_key_699_);
if (v___x_701_ == 0)
{
lean_object* v___x_702_; 
v___x_702_ = lean_box(0);
return v___x_702_;
}
else
{
lean_object* v___x_703_; 
lean_inc(v_val_700_);
v___x_703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_703_, 0, v_val_700_);
return v___x_703_;
}
}
case 1:
{
lean_object* v_node_704_; size_t v___x_705_; 
v_node_704_ = lean_ctor_get(v___x_698_, 0);
v___x_705_ = lean_usize_shift_right(v_x_690_, v___x_694_);
v_x_689_ = v_node_704_;
v_x_690_ = v___x_705_;
goto _start;
}
default: 
{
lean_object* v___x_707_; 
v___x_707_ = lean_box(0);
return v___x_707_;
}
}
}
else
{
lean_object* v_ks_708_; lean_object* v_vs_709_; lean_object* v___x_710_; lean_object* v___x_711_; 
v_ks_708_ = lean_ctor_get(v_x_689_, 0);
v_vs_709_ = lean_ctor_get(v_x_689_, 1);
v___x_710_ = lean_unsigned_to_nat(0u);
v___x_711_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0_spec__0_spec__1___redArg(v_ks_708_, v_vs_709_, v___x_710_, v_x_691_);
return v___x_711_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0_spec__0___redArg___boxed(lean_object* v_x_712_, lean_object* v_x_713_, lean_object* v_x_714_){
_start:
{
size_t v_x_1917__boxed_715_; lean_object* v_res_716_; 
v_x_1917__boxed_715_ = lean_unbox_usize(v_x_713_);
lean_dec(v_x_713_);
v_res_716_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0_spec__0___redArg(v_x_712_, v_x_1917__boxed_715_, v_x_714_);
lean_dec(v_x_714_);
lean_dec_ref(v_x_712_);
return v_res_716_;
}
}
static uint64_t _init_l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_717_; uint64_t v___x_718_; 
v___x_717_ = lean_unsigned_to_nat(1723u);
v___x_718_ = lean_uint64_of_nat(v___x_717_);
return v___x_718_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0___redArg(lean_object* v_x_719_, lean_object* v_x_720_){
_start:
{
uint64_t v___y_722_; 
if (lean_obj_tag(v_x_720_) == 0)
{
uint64_t v___x_725_; 
v___x_725_ = lean_uint64_once(&l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0___redArg___closed__0);
v___y_722_ = v___x_725_;
goto v___jp_721_;
}
else
{
uint64_t v_hash_726_; 
v_hash_726_ = lean_ctor_get_uint64(v_x_720_, sizeof(void*)*2);
v___y_722_ = v_hash_726_;
goto v___jp_721_;
}
v___jp_721_:
{
size_t v___x_723_; lean_object* v___x_724_; 
v___x_723_ = lean_uint64_to_usize(v___y_722_);
v___x_724_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0_spec__0___redArg(v_x_719_, v___x_723_, v_x_720_);
return v___x_724_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0___redArg___boxed(lean_object* v_x_727_, lean_object* v_x_728_){
_start:
{
lean_object* v_res_729_; 
v_res_729_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0___redArg(v_x_727_, v_x_728_);
lean_dec(v_x_728_);
lean_dec_ref(v_x_727_);
return v_res_729_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2_spec__4_spec__5___redArg(lean_object* v_x_730_, lean_object* v_x_731_, lean_object* v_x_732_, lean_object* v_x_733_){
_start:
{
lean_object* v_ks_734_; lean_object* v_vs_735_; lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_759_; 
v_ks_734_ = lean_ctor_get(v_x_730_, 0);
v_vs_735_ = lean_ctor_get(v_x_730_, 1);
v_isSharedCheck_759_ = !lean_is_exclusive(v_x_730_);
if (v_isSharedCheck_759_ == 0)
{
v___x_737_ = v_x_730_;
v_isShared_738_ = v_isSharedCheck_759_;
goto v_resetjp_736_;
}
else
{
lean_inc(v_vs_735_);
lean_inc(v_ks_734_);
lean_dec(v_x_730_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_759_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
lean_object* v___x_739_; uint8_t v___x_740_; 
v___x_739_ = lean_array_get_size(v_ks_734_);
v___x_740_ = lean_nat_dec_lt(v_x_731_, v___x_739_);
if (v___x_740_ == 0)
{
lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_744_; 
lean_dec(v_x_731_);
v___x_741_ = lean_array_push(v_ks_734_, v_x_732_);
v___x_742_ = lean_array_push(v_vs_735_, v_x_733_);
if (v_isShared_738_ == 0)
{
lean_ctor_set(v___x_737_, 1, v___x_742_);
lean_ctor_set(v___x_737_, 0, v___x_741_);
v___x_744_ = v___x_737_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v___x_741_);
lean_ctor_set(v_reuseFailAlloc_745_, 1, v___x_742_);
v___x_744_ = v_reuseFailAlloc_745_;
goto v_reusejp_743_;
}
v_reusejp_743_:
{
return v___x_744_;
}
}
else
{
lean_object* v_k_x27_746_; uint8_t v___x_747_; 
v_k_x27_746_ = lean_array_fget_borrowed(v_ks_734_, v_x_731_);
v___x_747_ = lean_name_eq(v_x_732_, v_k_x27_746_);
if (v___x_747_ == 0)
{
lean_object* v___x_749_; 
if (v_isShared_738_ == 0)
{
v___x_749_ = v___x_737_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v_ks_734_);
lean_ctor_set(v_reuseFailAlloc_753_, 1, v_vs_735_);
v___x_749_ = v_reuseFailAlloc_753_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
lean_object* v___x_750_; lean_object* v___x_751_; 
v___x_750_ = lean_unsigned_to_nat(1u);
v___x_751_ = lean_nat_add(v_x_731_, v___x_750_);
lean_dec(v_x_731_);
v_x_730_ = v___x_749_;
v_x_731_ = v___x_751_;
goto _start;
}
}
else
{
lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_757_; 
v___x_754_ = lean_array_fset(v_ks_734_, v_x_731_, v_x_732_);
v___x_755_ = lean_array_fset(v_vs_735_, v_x_731_, v_x_733_);
lean_dec(v_x_731_);
if (v_isShared_738_ == 0)
{
lean_ctor_set(v___x_737_, 1, v___x_755_);
lean_ctor_set(v___x_737_, 0, v___x_754_);
v___x_757_ = v___x_737_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v___x_754_);
lean_ctor_set(v_reuseFailAlloc_758_, 1, v___x_755_);
v___x_757_ = v_reuseFailAlloc_758_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
return v___x_757_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2_spec__4___redArg(lean_object* v_n_760_, lean_object* v_k_761_, lean_object* v_v_762_){
_start:
{
lean_object* v___x_763_; lean_object* v___x_764_; 
v___x_763_ = lean_unsigned_to_nat(0u);
v___x_764_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2_spec__4_spec__5___redArg(v_n_760_, v___x_763_, v_k_761_, v_v_762_);
return v___x_764_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_765_; 
v___x_765_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_765_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2___redArg(lean_object* v_x_766_, size_t v_x_767_, size_t v_x_768_, lean_object* v_x_769_, lean_object* v_x_770_){
_start:
{
if (lean_obj_tag(v_x_766_) == 0)
{
lean_object* v_es_771_; size_t v___x_772_; size_t v___x_773_; size_t v___x_774_; size_t v___x_775_; lean_object* v_j_776_; lean_object* v___x_777_; uint8_t v___x_778_; 
v_es_771_ = lean_ctor_get(v_x_766_, 0);
v___x_772_ = ((size_t)5ULL);
v___x_773_ = ((size_t)1ULL);
v___x_774_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0_spec__0___redArg___closed__1);
v___x_775_ = lean_usize_land(v_x_767_, v___x_774_);
v_j_776_ = lean_usize_to_nat(v___x_775_);
v___x_777_ = lean_array_get_size(v_es_771_);
v___x_778_ = lean_nat_dec_lt(v_j_776_, v___x_777_);
if (v___x_778_ == 0)
{
lean_dec(v_j_776_);
lean_dec(v_x_770_);
lean_dec(v_x_769_);
return v_x_766_;
}
else
{
lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_815_; 
lean_inc_ref(v_es_771_);
v_isSharedCheck_815_ = !lean_is_exclusive(v_x_766_);
if (v_isSharedCheck_815_ == 0)
{
lean_object* v_unused_816_; 
v_unused_816_ = lean_ctor_get(v_x_766_, 0);
lean_dec(v_unused_816_);
v___x_780_ = v_x_766_;
v_isShared_781_ = v_isSharedCheck_815_;
goto v_resetjp_779_;
}
else
{
lean_dec(v_x_766_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_815_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v_v_782_; lean_object* v___x_783_; lean_object* v_xs_x27_784_; lean_object* v___y_786_; 
v_v_782_ = lean_array_fget(v_es_771_, v_j_776_);
v___x_783_ = lean_box(0);
v_xs_x27_784_ = lean_array_fset(v_es_771_, v_j_776_, v___x_783_);
switch(lean_obj_tag(v_v_782_))
{
case 0:
{
lean_object* v_key_791_; lean_object* v_val_792_; lean_object* v___x_794_; uint8_t v_isShared_795_; uint8_t v_isSharedCheck_802_; 
v_key_791_ = lean_ctor_get(v_v_782_, 0);
v_val_792_ = lean_ctor_get(v_v_782_, 1);
v_isSharedCheck_802_ = !lean_is_exclusive(v_v_782_);
if (v_isSharedCheck_802_ == 0)
{
v___x_794_ = v_v_782_;
v_isShared_795_ = v_isSharedCheck_802_;
goto v_resetjp_793_;
}
else
{
lean_inc(v_val_792_);
lean_inc(v_key_791_);
lean_dec(v_v_782_);
v___x_794_ = lean_box(0);
v_isShared_795_ = v_isSharedCheck_802_;
goto v_resetjp_793_;
}
v_resetjp_793_:
{
uint8_t v___x_796_; 
v___x_796_ = lean_name_eq(v_x_769_, v_key_791_);
if (v___x_796_ == 0)
{
lean_object* v___x_797_; lean_object* v___x_798_; 
lean_del_object(v___x_794_);
v___x_797_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_791_, v_val_792_, v_x_769_, v_x_770_);
v___x_798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_798_, 0, v___x_797_);
v___y_786_ = v___x_798_;
goto v___jp_785_;
}
else
{
lean_object* v___x_800_; 
lean_dec(v_val_792_);
lean_dec(v_key_791_);
if (v_isShared_795_ == 0)
{
lean_ctor_set(v___x_794_, 1, v_x_770_);
lean_ctor_set(v___x_794_, 0, v_x_769_);
v___x_800_ = v___x_794_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v_x_769_);
lean_ctor_set(v_reuseFailAlloc_801_, 1, v_x_770_);
v___x_800_ = v_reuseFailAlloc_801_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
v___y_786_ = v___x_800_;
goto v___jp_785_;
}
}
}
}
case 1:
{
lean_object* v_node_803_; lean_object* v___x_805_; uint8_t v_isShared_806_; uint8_t v_isSharedCheck_813_; 
v_node_803_ = lean_ctor_get(v_v_782_, 0);
v_isSharedCheck_813_ = !lean_is_exclusive(v_v_782_);
if (v_isSharedCheck_813_ == 0)
{
v___x_805_ = v_v_782_;
v_isShared_806_ = v_isSharedCheck_813_;
goto v_resetjp_804_;
}
else
{
lean_inc(v_node_803_);
lean_dec(v_v_782_);
v___x_805_ = lean_box(0);
v_isShared_806_ = v_isSharedCheck_813_;
goto v_resetjp_804_;
}
v_resetjp_804_:
{
size_t v___x_807_; size_t v___x_808_; lean_object* v___x_809_; lean_object* v___x_811_; 
v___x_807_ = lean_usize_shift_right(v_x_767_, v___x_772_);
v___x_808_ = lean_usize_add(v_x_768_, v___x_773_);
v___x_809_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2___redArg(v_node_803_, v___x_807_, v___x_808_, v_x_769_, v_x_770_);
if (v_isShared_806_ == 0)
{
lean_ctor_set(v___x_805_, 0, v___x_809_);
v___x_811_ = v___x_805_;
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
v___y_786_ = v___x_811_;
goto v___jp_785_;
}
}
}
default: 
{
lean_object* v___x_814_; 
v___x_814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_814_, 0, v_x_769_);
lean_ctor_set(v___x_814_, 1, v_x_770_);
v___y_786_ = v___x_814_;
goto v___jp_785_;
}
}
v___jp_785_:
{
lean_object* v___x_787_; lean_object* v___x_789_; 
v___x_787_ = lean_array_fset(v_xs_x27_784_, v_j_776_, v___y_786_);
lean_dec(v_j_776_);
if (v_isShared_781_ == 0)
{
lean_ctor_set(v___x_780_, 0, v___x_787_);
v___x_789_ = v___x_780_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v___x_787_);
v___x_789_ = v_reuseFailAlloc_790_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
return v___x_789_;
}
}
}
}
}
else
{
lean_object* v_ks_817_; lean_object* v_vs_818_; lean_object* v___x_820_; uint8_t v_isShared_821_; uint8_t v_isSharedCheck_838_; 
v_ks_817_ = lean_ctor_get(v_x_766_, 0);
v_vs_818_ = lean_ctor_get(v_x_766_, 1);
v_isSharedCheck_838_ = !lean_is_exclusive(v_x_766_);
if (v_isSharedCheck_838_ == 0)
{
v___x_820_ = v_x_766_;
v_isShared_821_ = v_isSharedCheck_838_;
goto v_resetjp_819_;
}
else
{
lean_inc(v_vs_818_);
lean_inc(v_ks_817_);
lean_dec(v_x_766_);
v___x_820_ = lean_box(0);
v_isShared_821_ = v_isSharedCheck_838_;
goto v_resetjp_819_;
}
v_resetjp_819_:
{
lean_object* v___x_823_; 
if (v_isShared_821_ == 0)
{
v___x_823_ = v___x_820_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v_ks_817_);
lean_ctor_set(v_reuseFailAlloc_837_, 1, v_vs_818_);
v___x_823_ = v_reuseFailAlloc_837_;
goto v_reusejp_822_;
}
v_reusejp_822_:
{
lean_object* v_newNode_824_; uint8_t v___y_826_; size_t v___x_832_; uint8_t v___x_833_; 
v_newNode_824_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2_spec__4___redArg(v___x_823_, v_x_769_, v_x_770_);
v___x_832_ = ((size_t)7ULL);
v___x_833_ = lean_usize_dec_le(v___x_832_, v_x_768_);
if (v___x_833_ == 0)
{
lean_object* v___x_834_; lean_object* v___x_835_; uint8_t v___x_836_; 
v___x_834_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_824_);
v___x_835_ = lean_unsigned_to_nat(4u);
v___x_836_ = lean_nat_dec_lt(v___x_834_, v___x_835_);
lean_dec(v___x_834_);
v___y_826_ = v___x_836_;
goto v___jp_825_;
}
else
{
v___y_826_ = v___x_833_;
goto v___jp_825_;
}
v___jp_825_:
{
if (v___y_826_ == 0)
{
lean_object* v_ks_827_; lean_object* v_vs_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; 
v_ks_827_ = lean_ctor_get(v_newNode_824_, 0);
lean_inc_ref(v_ks_827_);
v_vs_828_ = lean_ctor_get(v_newNode_824_, 1);
lean_inc_ref(v_vs_828_);
lean_dec_ref(v_newNode_824_);
v___x_829_ = lean_unsigned_to_nat(0u);
v___x_830_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2___redArg___closed__0);
v___x_831_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2_spec__5___redArg(v_x_768_, v_ks_827_, v_vs_828_, v___x_829_, v___x_830_);
lean_dec_ref(v_vs_828_);
lean_dec_ref(v_ks_827_);
return v___x_831_;
}
else
{
return v_newNode_824_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2_spec__5___redArg(size_t v_depth_839_, lean_object* v_keys_840_, lean_object* v_vals_841_, lean_object* v_i_842_, lean_object* v_entries_843_){
_start:
{
lean_object* v___x_844_; uint8_t v___x_845_; 
v___x_844_ = lean_array_get_size(v_keys_840_);
v___x_845_ = lean_nat_dec_lt(v_i_842_, v___x_844_);
if (v___x_845_ == 0)
{
lean_dec(v_i_842_);
return v_entries_843_;
}
else
{
lean_object* v_k_846_; lean_object* v_v_847_; uint64_t v___y_849_; 
v_k_846_ = lean_array_fget_borrowed(v_keys_840_, v_i_842_);
v_v_847_ = lean_array_fget_borrowed(v_vals_841_, v_i_842_);
if (lean_obj_tag(v_k_846_) == 0)
{
uint64_t v___x_860_; 
v___x_860_ = lean_uint64_once(&l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0___redArg___closed__0);
v___y_849_ = v___x_860_;
goto v___jp_848_;
}
else
{
uint64_t v_hash_861_; 
v_hash_861_ = lean_ctor_get_uint64(v_k_846_, sizeof(void*)*2);
v___y_849_ = v_hash_861_;
goto v___jp_848_;
}
v___jp_848_:
{
size_t v_h_850_; size_t v___x_851_; lean_object* v___x_852_; size_t v___x_853_; size_t v___x_854_; size_t v___x_855_; size_t v_h_856_; lean_object* v___x_857_; lean_object* v___x_858_; 
v_h_850_ = lean_uint64_to_usize(v___y_849_);
v___x_851_ = ((size_t)5ULL);
v___x_852_ = lean_unsigned_to_nat(1u);
v___x_853_ = ((size_t)1ULL);
v___x_854_ = lean_usize_sub(v_depth_839_, v___x_853_);
v___x_855_ = lean_usize_mul(v___x_851_, v___x_854_);
v_h_856_ = lean_usize_shift_right(v_h_850_, v___x_855_);
v___x_857_ = lean_nat_add(v_i_842_, v___x_852_);
lean_dec(v_i_842_);
lean_inc(v_v_847_);
lean_inc(v_k_846_);
v___x_858_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2___redArg(v_entries_843_, v_h_856_, v_depth_839_, v_k_846_, v_v_847_);
v_i_842_ = v___x_857_;
v_entries_843_ = v___x_858_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_depth_862_, lean_object* v_keys_863_, lean_object* v_vals_864_, lean_object* v_i_865_, lean_object* v_entries_866_){
_start:
{
size_t v_depth_boxed_867_; lean_object* v_res_868_; 
v_depth_boxed_867_ = lean_unbox_usize(v_depth_862_);
lean_dec(v_depth_862_);
v_res_868_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2_spec__5___redArg(v_depth_boxed_867_, v_keys_863_, v_vals_864_, v_i_865_, v_entries_866_);
lean_dec_ref(v_vals_864_);
lean_dec_ref(v_keys_863_);
return v_res_868_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2___redArg___boxed(lean_object* v_x_869_, lean_object* v_x_870_, lean_object* v_x_871_, lean_object* v_x_872_, lean_object* v_x_873_){
_start:
{
size_t v_x_2079__boxed_874_; size_t v_x_2080__boxed_875_; lean_object* v_res_876_; 
v_x_2079__boxed_874_ = lean_unbox_usize(v_x_870_);
lean_dec(v_x_870_);
v_x_2080__boxed_875_ = lean_unbox_usize(v_x_871_);
lean_dec(v_x_871_);
v_res_876_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2___redArg(v_x_869_, v_x_2079__boxed_874_, v_x_2080__boxed_875_, v_x_872_, v_x_873_);
return v_res_876_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1___redArg(lean_object* v_x_877_, lean_object* v_x_878_, lean_object* v_x_879_){
_start:
{
uint64_t v___y_881_; 
if (lean_obj_tag(v_x_878_) == 0)
{
uint64_t v___x_885_; 
v___x_885_ = lean_uint64_once(&l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0___redArg___closed__0);
v___y_881_ = v___x_885_;
goto v___jp_880_;
}
else
{
uint64_t v_hash_886_; 
v_hash_886_ = lean_ctor_get_uint64(v_x_878_, sizeof(void*)*2);
v___y_881_ = v_hash_886_;
goto v___jp_880_;
}
v___jp_880_:
{
size_t v___x_882_; size_t v___x_883_; lean_object* v___x_884_; 
v___x_882_ = lean_uint64_to_usize(v___y_881_);
v___x_883_ = ((size_t)1ULL);
v___x_884_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2___redArg(v_x_877_, v___x_882_, v___x_883_, v_x_878_, v_x_879_);
return v___x_884_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule___redArg(lean_object* v_declName_887_, lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_){
_start:
{
lean_object* v___x_894_; lean_object* v_cache_895_; lean_object* v_backwardRuleName_896_; lean_object* v___x_897_; 
v___x_894_ = lean_st_ref_get(v_a_888_);
v_cache_895_ = lean_ctor_get(v___x_894_, 3);
lean_inc_ref(v_cache_895_);
lean_dec(v___x_894_);
v_backwardRuleName_896_ = lean_ctor_get(v_cache_895_, 0);
lean_inc_ref(v_backwardRuleName_896_);
lean_dec_ref(v_cache_895_);
v___x_897_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0___redArg(v_backwardRuleName_896_, v_declName_887_);
lean_dec_ref(v_backwardRuleName_896_);
if (lean_obj_tag(v___x_897_) == 1)
{
lean_object* v_val_898_; lean_object* v___x_900_; uint8_t v_isShared_901_; uint8_t v_isSharedCheck_905_; 
lean_dec(v_declName_887_);
v_val_898_ = lean_ctor_get(v___x_897_, 0);
v_isSharedCheck_905_ = !lean_is_exclusive(v___x_897_);
if (v_isSharedCheck_905_ == 0)
{
v___x_900_ = v___x_897_;
v_isShared_901_ = v_isSharedCheck_905_;
goto v_resetjp_899_;
}
else
{
lean_inc(v_val_898_);
lean_dec(v___x_897_);
v___x_900_ = lean_box(0);
v_isShared_901_ = v_isSharedCheck_905_;
goto v_resetjp_899_;
}
v_resetjp_899_:
{
lean_object* v___x_903_; 
if (v_isShared_901_ == 0)
{
lean_ctor_set_tag(v___x_900_, 0);
v___x_903_ = v___x_900_;
goto v_reusejp_902_;
}
else
{
lean_object* v_reuseFailAlloc_904_; 
v_reuseFailAlloc_904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_904_, 0, v_val_898_);
v___x_903_ = v_reuseFailAlloc_904_;
goto v_reusejp_902_;
}
v_reusejp_902_:
{
return v___x_903_;
}
}
}
else
{
lean_object* v___x_906_; lean_object* v___x_907_; 
lean_dec(v___x_897_);
v___x_906_ = lean_box(0);
lean_inc(v_declName_887_);
v___x_907_ = l_Lean_Meta_Sym_mkBackwardRuleFromDecl(v_declName_887_, v___x_906_, v_a_889_, v_a_890_, v_a_891_, v_a_892_);
if (lean_obj_tag(v___x_907_) == 0)
{
lean_object* v_a_908_; lean_object* v___x_910_; uint8_t v_isShared_911_; uint8_t v_isSharedCheck_939_; 
v_a_908_ = lean_ctor_get(v___x_907_, 0);
v_isSharedCheck_939_ = !lean_is_exclusive(v___x_907_);
if (v_isSharedCheck_939_ == 0)
{
v___x_910_ = v___x_907_;
v_isShared_911_ = v_isSharedCheck_939_;
goto v_resetjp_909_;
}
else
{
lean_inc(v_a_908_);
lean_dec(v___x_907_);
v___x_910_ = lean_box(0);
v_isShared_911_ = v_isSharedCheck_939_;
goto v_resetjp_909_;
}
v_resetjp_909_:
{
lean_object* v___x_912_; lean_object* v_cache_913_; lean_object* v_symState_914_; lean_object* v_grindState_915_; lean_object* v_goals_916_; lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_938_; 
v___x_912_ = lean_st_ref_take(v_a_888_);
v_cache_913_ = lean_ctor_get(v___x_912_, 3);
v_symState_914_ = lean_ctor_get(v___x_912_, 0);
v_grindState_915_ = lean_ctor_get(v___x_912_, 1);
v_goals_916_ = lean_ctor_get(v___x_912_, 2);
v_isSharedCheck_938_ = !lean_is_exclusive(v___x_912_);
if (v_isSharedCheck_938_ == 0)
{
v___x_918_ = v___x_912_;
v_isShared_919_ = v_isSharedCheck_938_;
goto v_resetjp_917_;
}
else
{
lean_inc(v_cache_913_);
lean_inc(v_goals_916_);
lean_inc(v_grindState_915_);
lean_inc(v_symState_914_);
lean_dec(v___x_912_);
v___x_918_ = lean_box(0);
v_isShared_919_ = v_isSharedCheck_938_;
goto v_resetjp_917_;
}
v_resetjp_917_:
{
lean_object* v_backwardRuleName_920_; lean_object* v_backwardRuleSyntax_921_; lean_object* v_simpState_922_; lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_937_; 
v_backwardRuleName_920_ = lean_ctor_get(v_cache_913_, 0);
v_backwardRuleSyntax_921_ = lean_ctor_get(v_cache_913_, 1);
v_simpState_922_ = lean_ctor_get(v_cache_913_, 2);
v_isSharedCheck_937_ = !lean_is_exclusive(v_cache_913_);
if (v_isSharedCheck_937_ == 0)
{
v___x_924_ = v_cache_913_;
v_isShared_925_ = v_isSharedCheck_937_;
goto v_resetjp_923_;
}
else
{
lean_inc(v_simpState_922_);
lean_inc(v_backwardRuleSyntax_921_);
lean_inc(v_backwardRuleName_920_);
lean_dec(v_cache_913_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_937_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
lean_object* v___x_926_; lean_object* v___x_928_; 
lean_inc(v_a_908_);
v___x_926_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1___redArg(v_backwardRuleName_920_, v_declName_887_, v_a_908_);
if (v_isShared_925_ == 0)
{
lean_ctor_set(v___x_924_, 0, v___x_926_);
v___x_928_ = v___x_924_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v___x_926_);
lean_ctor_set(v_reuseFailAlloc_936_, 1, v_backwardRuleSyntax_921_);
lean_ctor_set(v_reuseFailAlloc_936_, 2, v_simpState_922_);
v___x_928_ = v_reuseFailAlloc_936_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
lean_object* v___x_930_; 
if (v_isShared_919_ == 0)
{
lean_ctor_set(v___x_918_, 3, v___x_928_);
v___x_930_ = v___x_918_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v_symState_914_);
lean_ctor_set(v_reuseFailAlloc_935_, 1, v_grindState_915_);
lean_ctor_set(v_reuseFailAlloc_935_, 2, v_goals_916_);
lean_ctor_set(v_reuseFailAlloc_935_, 3, v___x_928_);
v___x_930_ = v_reuseFailAlloc_935_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
lean_object* v___x_931_; lean_object* v___x_933_; 
v___x_931_ = lean_st_ref_set(v_a_888_, v___x_930_);
if (v_isShared_911_ == 0)
{
v___x_933_ = v___x_910_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_934_; 
v_reuseFailAlloc_934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_934_, 0, v_a_908_);
v___x_933_ = v_reuseFailAlloc_934_;
goto v_reusejp_932_;
}
v_reusejp_932_:
{
return v___x_933_;
}
}
}
}
}
}
}
else
{
lean_dec(v_declName_887_);
return v___x_907_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule___redArg___boxed(lean_object* v_declName_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_){
_start:
{
lean_object* v_res_947_; 
v_res_947_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule___redArg(v_declName_940_, v_a_941_, v_a_942_, v_a_943_, v_a_944_, v_a_945_);
lean_dec(v_a_945_);
lean_dec_ref(v_a_944_);
lean_dec(v_a_943_);
lean_dec_ref(v_a_942_);
lean_dec(v_a_941_);
return v_res_947_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule(lean_object* v_declName_948_, lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_){
_start:
{
lean_object* v___x_958_; 
v___x_958_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule___redArg(v_declName_948_, v_a_950_, v_a_953_, v_a_954_, v_a_955_, v_a_956_);
return v___x_958_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule___boxed(lean_object* v_declName_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_, lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_){
_start:
{
lean_object* v_res_969_; 
v_res_969_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule(v_declName_959_, v_a_960_, v_a_961_, v_a_962_, v_a_963_, v_a_964_, v_a_965_, v_a_966_, v_a_967_);
lean_dec(v_a_967_);
lean_dec_ref(v_a_966_);
lean_dec(v_a_965_);
lean_dec_ref(v_a_964_);
lean_dec(v_a_963_);
lean_dec_ref(v_a_962_);
lean_dec(v_a_961_);
lean_dec_ref(v_a_960_);
return v_res_969_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0(lean_object* v_00_u03b2_970_, lean_object* v_x_971_, lean_object* v_x_972_){
_start:
{
lean_object* v___x_973_; 
v___x_973_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0___redArg(v_x_971_, v_x_972_);
return v___x_973_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0___boxed(lean_object* v_00_u03b2_974_, lean_object* v_x_975_, lean_object* v_x_976_){
_start:
{
lean_object* v_res_977_; 
v_res_977_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0(v_00_u03b2_974_, v_x_975_, v_x_976_);
lean_dec(v_x_976_);
lean_dec_ref(v_x_975_);
return v_res_977_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1(lean_object* v_00_u03b2_978_, lean_object* v_x_979_, lean_object* v_x_980_, lean_object* v_x_981_){
_start:
{
lean_object* v___x_982_; 
v___x_982_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1___redArg(v_x_979_, v_x_980_, v_x_981_);
return v___x_982_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0_spec__0(lean_object* v_00_u03b2_983_, lean_object* v_x_984_, size_t v_x_985_, lean_object* v_x_986_){
_start:
{
lean_object* v___x_987_; 
v___x_987_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0_spec__0___redArg(v_x_984_, v_x_985_, v_x_986_);
return v___x_987_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0_spec__0___boxed(lean_object* v_00_u03b2_988_, lean_object* v_x_989_, lean_object* v_x_990_, lean_object* v_x_991_){
_start:
{
size_t v_x_2357__boxed_992_; lean_object* v_res_993_; 
v_x_2357__boxed_992_ = lean_unbox_usize(v_x_990_);
lean_dec(v_x_990_);
v_res_993_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0_spec__0(v_00_u03b2_988_, v_x_989_, v_x_2357__boxed_992_, v_x_991_);
lean_dec(v_x_991_);
lean_dec_ref(v_x_989_);
return v_res_993_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2(lean_object* v_00_u03b2_994_, lean_object* v_x_995_, size_t v_x_996_, size_t v_x_997_, lean_object* v_x_998_, lean_object* v_x_999_){
_start:
{
lean_object* v___x_1000_; 
v___x_1000_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2___redArg(v_x_995_, v_x_996_, v_x_997_, v_x_998_, v_x_999_);
return v___x_1000_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1001_, lean_object* v_x_1002_, lean_object* v_x_1003_, lean_object* v_x_1004_, lean_object* v_x_1005_, lean_object* v_x_1006_){
_start:
{
size_t v_x_2368__boxed_1007_; size_t v_x_2369__boxed_1008_; lean_object* v_res_1009_; 
v_x_2368__boxed_1007_ = lean_unbox_usize(v_x_1003_);
lean_dec(v_x_1003_);
v_x_2369__boxed_1008_ = lean_unbox_usize(v_x_1004_);
lean_dec(v_x_1004_);
v_res_1009_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2(v_00_u03b2_1001_, v_x_1002_, v_x_2368__boxed_1007_, v_x_2369__boxed_1008_, v_x_1005_, v_x_1006_);
return v_res_1009_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1010_, lean_object* v_keys_1011_, lean_object* v_vals_1012_, lean_object* v_heq_1013_, lean_object* v_i_1014_, lean_object* v_k_1015_){
_start:
{
lean_object* v___x_1016_; 
v___x_1016_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0_spec__0_spec__1___redArg(v_keys_1011_, v_vals_1012_, v_i_1014_, v_k_1015_);
return v___x_1016_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1017_, lean_object* v_keys_1018_, lean_object* v_vals_1019_, lean_object* v_heq_1020_, lean_object* v_i_1021_, lean_object* v_k_1022_){
_start:
{
lean_object* v_res_1023_; 
v_res_1023_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0_spec__0_spec__1(v_00_u03b2_1017_, v_keys_1018_, v_vals_1019_, v_heq_1020_, v_i_1021_, v_k_1022_);
lean_dec(v_k_1022_);
lean_dec_ref(v_vals_1019_);
lean_dec_ref(v_keys_1018_);
return v_res_1023_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_1024_, lean_object* v_n_1025_, lean_object* v_k_1026_, lean_object* v_v_1027_){
_start:
{
lean_object* v___x_1028_; 
v___x_1028_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2_spec__4___redArg(v_n_1025_, v_k_1026_, v_v_1027_);
return v___x_1028_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_1029_, size_t v_depth_1030_, lean_object* v_keys_1031_, lean_object* v_vals_1032_, lean_object* v_heq_1033_, lean_object* v_i_1034_, lean_object* v_entries_1035_){
_start:
{
lean_object* v___x_1036_; 
v___x_1036_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2_spec__5___redArg(v_depth_1030_, v_keys_1031_, v_vals_1032_, v_i_1034_, v_entries_1035_);
return v___x_1036_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1037_, lean_object* v_depth_1038_, lean_object* v_keys_1039_, lean_object* v_vals_1040_, lean_object* v_heq_1041_, lean_object* v_i_1042_, lean_object* v_entries_1043_){
_start:
{
size_t v_depth_boxed_1044_; lean_object* v_res_1045_; 
v_depth_boxed_1044_ = lean_unbox_usize(v_depth_1038_);
lean_dec(v_depth_1038_);
v_res_1045_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2_spec__5(v_00_u03b2_1037_, v_depth_boxed_1044_, v_keys_1039_, v_vals_1040_, v_heq_1041_, v_i_1042_, v_entries_1043_);
lean_dec_ref(v_vals_1040_);
lean_dec_ref(v_keys_1039_);
return v_res_1045_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_1046_, lean_object* v_x_1047_, lean_object* v_x_1048_, lean_object* v_x_1049_, lean_object* v_x_1050_){
_start:
{
lean_object* v___x_1051_; 
v___x_1051_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2_spec__4_spec__5___redArg(v_x_1047_, v_x_1048_, v_x_1049_, v_x_1050_);
return v___x_1051_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__1___redArg(lean_object* v_e_1052_, lean_object* v___y_1053_){
_start:
{
uint8_t v___x_1055_; 
v___x_1055_ = l_Lean_Expr_hasMVar(v_e_1052_);
if (v___x_1055_ == 0)
{
lean_object* v___x_1056_; 
v___x_1056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1056_, 0, v_e_1052_);
return v___x_1056_;
}
else
{
lean_object* v___x_1057_; lean_object* v_mctx_1058_; lean_object* v___x_1059_; lean_object* v_fst_1060_; lean_object* v_snd_1061_; lean_object* v___x_1062_; lean_object* v_cache_1063_; lean_object* v_zetaDeltaFVarIds_1064_; lean_object* v_postponed_1065_; lean_object* v_diag_1066_; lean_object* v___x_1068_; uint8_t v_isShared_1069_; uint8_t v_isSharedCheck_1075_; 
v___x_1057_ = lean_st_ref_get(v___y_1053_);
v_mctx_1058_ = lean_ctor_get(v___x_1057_, 0);
lean_inc_ref(v_mctx_1058_);
lean_dec(v___x_1057_);
v___x_1059_ = l_Lean_instantiateMVarsCore(v_mctx_1058_, v_e_1052_);
v_fst_1060_ = lean_ctor_get(v___x_1059_, 0);
lean_inc(v_fst_1060_);
v_snd_1061_ = lean_ctor_get(v___x_1059_, 1);
lean_inc(v_snd_1061_);
lean_dec_ref(v___x_1059_);
v___x_1062_ = lean_st_ref_take(v___y_1053_);
v_cache_1063_ = lean_ctor_get(v___x_1062_, 1);
v_zetaDeltaFVarIds_1064_ = lean_ctor_get(v___x_1062_, 2);
v_postponed_1065_ = lean_ctor_get(v___x_1062_, 3);
v_diag_1066_ = lean_ctor_get(v___x_1062_, 4);
v_isSharedCheck_1075_ = !lean_is_exclusive(v___x_1062_);
if (v_isSharedCheck_1075_ == 0)
{
lean_object* v_unused_1076_; 
v_unused_1076_ = lean_ctor_get(v___x_1062_, 0);
lean_dec(v_unused_1076_);
v___x_1068_ = v___x_1062_;
v_isShared_1069_ = v_isSharedCheck_1075_;
goto v_resetjp_1067_;
}
else
{
lean_inc(v_diag_1066_);
lean_inc(v_postponed_1065_);
lean_inc(v_zetaDeltaFVarIds_1064_);
lean_inc(v_cache_1063_);
lean_dec(v___x_1062_);
v___x_1068_ = lean_box(0);
v_isShared_1069_ = v_isSharedCheck_1075_;
goto v_resetjp_1067_;
}
v_resetjp_1067_:
{
lean_object* v___x_1071_; 
if (v_isShared_1069_ == 0)
{
lean_ctor_set(v___x_1068_, 0, v_snd_1061_);
v___x_1071_ = v___x_1068_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v_snd_1061_);
lean_ctor_set(v_reuseFailAlloc_1074_, 1, v_cache_1063_);
lean_ctor_set(v_reuseFailAlloc_1074_, 2, v_zetaDeltaFVarIds_1064_);
lean_ctor_set(v_reuseFailAlloc_1074_, 3, v_postponed_1065_);
lean_ctor_set(v_reuseFailAlloc_1074_, 4, v_diag_1066_);
v___x_1071_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
lean_object* v___x_1072_; lean_object* v___x_1073_; 
v___x_1072_ = lean_st_ref_set(v___y_1053_, v___x_1071_);
v___x_1073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1073_, 0, v_fst_1060_);
return v___x_1073_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__1___redArg___boxed(lean_object* v_e_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_){
_start:
{
lean_object* v_res_1080_; 
v_res_1080_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__1___redArg(v_e_1077_, v___y_1078_);
lean_dec(v___y_1078_);
return v_res_1080_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__1(lean_object* v_e_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_){
_start:
{
lean_object* v___x_1091_; 
v___x_1091_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__1___redArg(v_e_1081_, v___y_1087_);
return v___x_1091_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__1___boxed(lean_object* v_e_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_){
_start:
{
lean_object* v_res_1102_; 
v_res_1102_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__1(v_e_1092_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_);
lean_dec(v___y_1100_);
lean_dec_ref(v___y_1099_);
lean_dec(v___y_1098_);
lean_dec_ref(v___y_1097_);
lean_dec(v___y_1096_);
lean_dec_ref(v___y_1095_);
lean_dec(v___y_1094_);
lean_dec_ref(v___y_1093_);
return v_res_1102_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm___lam__0(lean_object* v_term_1103_, lean_object* v___x_1104_, uint8_t v___x_1105_, uint8_t v___x_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_){
_start:
{
lean_object* v___x_1116_; 
v___x_1116_ = l_Lean_Elab_Term_elabTerm(v_term_1103_, v___x_1104_, v___x_1105_, v___x_1105_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_);
if (lean_obj_tag(v___x_1116_) == 0)
{
lean_object* v_a_1117_; uint8_t v___x_1118_; lean_object* v___x_1119_; 
v_a_1117_ = lean_ctor_get(v___x_1116_, 0);
lean_inc(v_a_1117_);
lean_dec_ref(v___x_1116_);
v___x_1118_ = 1;
v___x_1119_ = l_Lean_Elab_Term_synthesizeSyntheticMVars(v___x_1118_, v___x_1106_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_);
if (lean_obj_tag(v___x_1119_) == 0)
{
lean_object* v___x_1120_; 
lean_dec_ref(v___x_1119_);
v___x_1120_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__1___redArg(v_a_1117_, v___y_1112_);
return v___x_1120_;
}
else
{
lean_object* v_a_1121_; lean_object* v___x_1123_; uint8_t v_isShared_1124_; uint8_t v_isSharedCheck_1128_; 
lean_dec(v_a_1117_);
v_a_1121_ = lean_ctor_get(v___x_1119_, 0);
v_isSharedCheck_1128_ = !lean_is_exclusive(v___x_1119_);
if (v_isSharedCheck_1128_ == 0)
{
v___x_1123_ = v___x_1119_;
v_isShared_1124_ = v_isSharedCheck_1128_;
goto v_resetjp_1122_;
}
else
{
lean_inc(v_a_1121_);
lean_dec(v___x_1119_);
v___x_1123_ = lean_box(0);
v_isShared_1124_ = v_isSharedCheck_1128_;
goto v_resetjp_1122_;
}
v_resetjp_1122_:
{
lean_object* v___x_1126_; 
if (v_isShared_1124_ == 0)
{
v___x_1126_ = v___x_1123_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v_a_1121_);
v___x_1126_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
return v___x_1126_;
}
}
}
}
else
{
return v___x_1116_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm___lam__0___boxed(lean_object* v_term_1129_, lean_object* v___x_1130_, lean_object* v___x_1131_, lean_object* v___x_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_){
_start:
{
uint8_t v___x_3479__boxed_1142_; uint8_t v___x_3480__boxed_1143_; lean_object* v_res_1144_; 
v___x_3479__boxed_1142_ = lean_unbox(v___x_1131_);
v___x_3480__boxed_1143_ = lean_unbox(v___x_1132_);
v_res_1144_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm___lam__0(v_term_1129_, v___x_1130_, v___x_3479__boxed_1142_, v___x_3480__boxed_1143_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_);
lean_dec(v___y_1140_);
lean_dec_ref(v___y_1139_);
lean_dec(v___y_1138_);
lean_dec_ref(v___y_1137_);
lean_dec(v___y_1136_);
lean_dec_ref(v___y_1135_);
lean_dec(v___y_1134_);
lean_dec_ref(v___y_1133_);
return v_res_1144_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3_spec__5_spec__6___redArg(lean_object* v_x_1145_, lean_object* v_x_1146_, lean_object* v_x_1147_, lean_object* v_x_1148_){
_start:
{
lean_object* v_ks_1149_; lean_object* v_vs_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1179_; 
v_ks_1149_ = lean_ctor_get(v_x_1145_, 0);
v_vs_1150_ = lean_ctor_get(v_x_1145_, 1);
v_isSharedCheck_1179_ = !lean_is_exclusive(v_x_1145_);
if (v_isSharedCheck_1179_ == 0)
{
v___x_1152_ = v_x_1145_;
v_isShared_1153_ = v_isSharedCheck_1179_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_vs_1150_);
lean_inc(v_ks_1149_);
lean_dec(v_x_1145_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1179_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
uint8_t v___y_1155_; lean_object* v___x_1167_; uint8_t v___x_1168_; 
v___x_1167_ = lean_array_get_size(v_ks_1149_);
v___x_1168_ = lean_nat_dec_lt(v_x_1146_, v___x_1167_);
if (v___x_1168_ == 0)
{
lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; 
lean_del_object(v___x_1152_);
lean_dec(v_x_1146_);
v___x_1169_ = lean_array_push(v_ks_1149_, v_x_1147_);
v___x_1170_ = lean_array_push(v_vs_1150_, v_x_1148_);
v___x_1171_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1171_, 0, v___x_1169_);
lean_ctor_set(v___x_1171_, 1, v___x_1170_);
return v___x_1171_;
}
else
{
lean_object* v_fst_1172_; lean_object* v_snd_1173_; lean_object* v_k_x27_1174_; lean_object* v_fst_1175_; lean_object* v_snd_1176_; uint8_t v___x_1177_; 
v_fst_1172_ = lean_ctor_get(v_x_1147_, 0);
v_snd_1173_ = lean_ctor_get(v_x_1147_, 1);
v_k_x27_1174_ = lean_array_fget_borrowed(v_ks_1149_, v_x_1146_);
v_fst_1175_ = lean_ctor_get(v_k_x27_1174_, 0);
v_snd_1176_ = lean_ctor_get(v_k_x27_1174_, 1);
v___x_1177_ = lean_nat_dec_eq(v_fst_1172_, v_fst_1175_);
if (v___x_1177_ == 0)
{
v___y_1155_ = v___x_1177_;
goto v___jp_1154_;
}
else
{
uint8_t v___x_1178_; 
v___x_1178_ = lean_nat_dec_eq(v_snd_1173_, v_snd_1176_);
v___y_1155_ = v___x_1178_;
goto v___jp_1154_;
}
}
v___jp_1154_:
{
if (v___y_1155_ == 0)
{
lean_object* v___x_1157_; 
if (v_isShared_1153_ == 0)
{
v___x_1157_ = v___x_1152_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v_ks_1149_);
lean_ctor_set(v_reuseFailAlloc_1161_, 1, v_vs_1150_);
v___x_1157_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
lean_object* v___x_1158_; lean_object* v___x_1159_; 
v___x_1158_ = lean_unsigned_to_nat(1u);
v___x_1159_ = lean_nat_add(v_x_1146_, v___x_1158_);
lean_dec(v_x_1146_);
v_x_1145_ = v___x_1157_;
v_x_1146_ = v___x_1159_;
goto _start;
}
}
else
{
lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1165_; 
v___x_1162_ = lean_array_fset(v_ks_1149_, v_x_1146_, v_x_1147_);
v___x_1163_ = lean_array_fset(v_vs_1150_, v_x_1146_, v_x_1148_);
lean_dec(v_x_1146_);
if (v_isShared_1153_ == 0)
{
lean_ctor_set(v___x_1152_, 1, v___x_1163_);
lean_ctor_set(v___x_1152_, 0, v___x_1162_);
v___x_1165_ = v___x_1152_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v___x_1162_);
lean_ctor_set(v_reuseFailAlloc_1166_, 1, v___x_1163_);
v___x_1165_ = v_reuseFailAlloc_1166_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
return v___x_1165_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3_spec__5___redArg(lean_object* v_n_1180_, lean_object* v_k_1181_, lean_object* v_v_1182_){
_start:
{
lean_object* v___x_1183_; lean_object* v___x_1184_; 
v___x_1183_ = lean_unsigned_to_nat(0u);
v___x_1184_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3_spec__5_spec__6___redArg(v_n_1180_, v___x_1183_, v_k_1181_, v_v_1182_);
return v___x_1184_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_1185_; 
v___x_1185_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1185_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3___redArg(lean_object* v_x_1186_, size_t v_x_1187_, size_t v_x_1188_, lean_object* v_x_1189_, lean_object* v_x_1190_){
_start:
{
if (lean_obj_tag(v_x_1186_) == 0)
{
lean_object* v_es_1191_; size_t v___x_1192_; size_t v___x_1193_; size_t v___x_1194_; size_t v___x_1195_; lean_object* v_j_1196_; lean_object* v___x_1197_; uint8_t v___x_1198_; 
v_es_1191_ = lean_ctor_get(v_x_1186_, 0);
v___x_1192_ = ((size_t)5ULL);
v___x_1193_ = ((size_t)1ULL);
v___x_1194_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0_spec__0___redArg___closed__1);
v___x_1195_ = lean_usize_land(v_x_1187_, v___x_1194_);
v_j_1196_ = lean_usize_to_nat(v___x_1195_);
v___x_1197_ = lean_array_get_size(v_es_1191_);
v___x_1198_ = lean_nat_dec_lt(v_j_1196_, v___x_1197_);
if (v___x_1198_ == 0)
{
lean_dec(v_j_1196_);
lean_dec(v_x_1190_);
lean_dec_ref(v_x_1189_);
return v_x_1186_;
}
else
{
lean_object* v___x_1200_; uint8_t v_isShared_1201_; uint8_t v_isSharedCheck_1242_; 
lean_inc_ref(v_es_1191_);
v_isSharedCheck_1242_ = !lean_is_exclusive(v_x_1186_);
if (v_isSharedCheck_1242_ == 0)
{
lean_object* v_unused_1243_; 
v_unused_1243_ = lean_ctor_get(v_x_1186_, 0);
lean_dec(v_unused_1243_);
v___x_1200_ = v_x_1186_;
v_isShared_1201_ = v_isSharedCheck_1242_;
goto v_resetjp_1199_;
}
else
{
lean_dec(v_x_1186_);
v___x_1200_ = lean_box(0);
v_isShared_1201_ = v_isSharedCheck_1242_;
goto v_resetjp_1199_;
}
v_resetjp_1199_:
{
lean_object* v_v_1202_; lean_object* v___x_1203_; lean_object* v_xs_x27_1204_; lean_object* v___y_1206_; 
v_v_1202_ = lean_array_fget(v_es_1191_, v_j_1196_);
v___x_1203_ = lean_box(0);
v_xs_x27_1204_ = lean_array_fset(v_es_1191_, v_j_1196_, v___x_1203_);
switch(lean_obj_tag(v_v_1202_))
{
case 0:
{
lean_object* v_key_1211_; lean_object* v_val_1212_; lean_object* v___x_1214_; uint8_t v_isShared_1215_; uint8_t v_isSharedCheck_1229_; 
v_key_1211_ = lean_ctor_get(v_v_1202_, 0);
v_val_1212_ = lean_ctor_get(v_v_1202_, 1);
v_isSharedCheck_1229_ = !lean_is_exclusive(v_v_1202_);
if (v_isSharedCheck_1229_ == 0)
{
v___x_1214_ = v_v_1202_;
v_isShared_1215_ = v_isSharedCheck_1229_;
goto v_resetjp_1213_;
}
else
{
lean_inc(v_val_1212_);
lean_inc(v_key_1211_);
lean_dec(v_v_1202_);
v___x_1214_ = lean_box(0);
v_isShared_1215_ = v_isSharedCheck_1229_;
goto v_resetjp_1213_;
}
v_resetjp_1213_:
{
uint8_t v___y_1217_; lean_object* v_fst_1223_; lean_object* v_snd_1224_; lean_object* v_fst_1225_; lean_object* v_snd_1226_; uint8_t v___x_1227_; 
v_fst_1223_ = lean_ctor_get(v_x_1189_, 0);
v_snd_1224_ = lean_ctor_get(v_x_1189_, 1);
v_fst_1225_ = lean_ctor_get(v_key_1211_, 0);
v_snd_1226_ = lean_ctor_get(v_key_1211_, 1);
v___x_1227_ = lean_nat_dec_eq(v_fst_1223_, v_fst_1225_);
if (v___x_1227_ == 0)
{
v___y_1217_ = v___x_1227_;
goto v___jp_1216_;
}
else
{
uint8_t v___x_1228_; 
v___x_1228_ = lean_nat_dec_eq(v_snd_1224_, v_snd_1226_);
v___y_1217_ = v___x_1228_;
goto v___jp_1216_;
}
v___jp_1216_:
{
if (v___y_1217_ == 0)
{
lean_object* v___x_1218_; lean_object* v___x_1219_; 
lean_del_object(v___x_1214_);
v___x_1218_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1211_, v_val_1212_, v_x_1189_, v_x_1190_);
v___x_1219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1219_, 0, v___x_1218_);
v___y_1206_ = v___x_1219_;
goto v___jp_1205_;
}
else
{
lean_object* v___x_1221_; 
lean_dec(v_val_1212_);
lean_dec(v_key_1211_);
if (v_isShared_1215_ == 0)
{
lean_ctor_set(v___x_1214_, 1, v_x_1190_);
lean_ctor_set(v___x_1214_, 0, v_x_1189_);
v___x_1221_ = v___x_1214_;
goto v_reusejp_1220_;
}
else
{
lean_object* v_reuseFailAlloc_1222_; 
v_reuseFailAlloc_1222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1222_, 0, v_x_1189_);
lean_ctor_set(v_reuseFailAlloc_1222_, 1, v_x_1190_);
v___x_1221_ = v_reuseFailAlloc_1222_;
goto v_reusejp_1220_;
}
v_reusejp_1220_:
{
v___y_1206_ = v___x_1221_;
goto v___jp_1205_;
}
}
}
}
}
case 1:
{
lean_object* v_node_1230_; lean_object* v___x_1232_; uint8_t v_isShared_1233_; uint8_t v_isSharedCheck_1240_; 
v_node_1230_ = lean_ctor_get(v_v_1202_, 0);
v_isSharedCheck_1240_ = !lean_is_exclusive(v_v_1202_);
if (v_isSharedCheck_1240_ == 0)
{
v___x_1232_ = v_v_1202_;
v_isShared_1233_ = v_isSharedCheck_1240_;
goto v_resetjp_1231_;
}
else
{
lean_inc(v_node_1230_);
lean_dec(v_v_1202_);
v___x_1232_ = lean_box(0);
v_isShared_1233_ = v_isSharedCheck_1240_;
goto v_resetjp_1231_;
}
v_resetjp_1231_:
{
size_t v___x_1234_; size_t v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1238_; 
v___x_1234_ = lean_usize_shift_right(v_x_1187_, v___x_1192_);
v___x_1235_ = lean_usize_add(v_x_1188_, v___x_1193_);
v___x_1236_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3___redArg(v_node_1230_, v___x_1234_, v___x_1235_, v_x_1189_, v_x_1190_);
if (v_isShared_1233_ == 0)
{
lean_ctor_set(v___x_1232_, 0, v___x_1236_);
v___x_1238_ = v___x_1232_;
goto v_reusejp_1237_;
}
else
{
lean_object* v_reuseFailAlloc_1239_; 
v_reuseFailAlloc_1239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1239_, 0, v___x_1236_);
v___x_1238_ = v_reuseFailAlloc_1239_;
goto v_reusejp_1237_;
}
v_reusejp_1237_:
{
v___y_1206_ = v___x_1238_;
goto v___jp_1205_;
}
}
}
default: 
{
lean_object* v___x_1241_; 
v___x_1241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1241_, 0, v_x_1189_);
lean_ctor_set(v___x_1241_, 1, v_x_1190_);
v___y_1206_ = v___x_1241_;
goto v___jp_1205_;
}
}
v___jp_1205_:
{
lean_object* v___x_1207_; lean_object* v___x_1209_; 
v___x_1207_ = lean_array_fset(v_xs_x27_1204_, v_j_1196_, v___y_1206_);
lean_dec(v_j_1196_);
if (v_isShared_1201_ == 0)
{
lean_ctor_set(v___x_1200_, 0, v___x_1207_);
v___x_1209_ = v___x_1200_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1210_; 
v_reuseFailAlloc_1210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1210_, 0, v___x_1207_);
v___x_1209_ = v_reuseFailAlloc_1210_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
return v___x_1209_;
}
}
}
}
}
else
{
lean_object* v_ks_1244_; lean_object* v_vs_1245_; lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1265_; 
v_ks_1244_ = lean_ctor_get(v_x_1186_, 0);
v_vs_1245_ = lean_ctor_get(v_x_1186_, 1);
v_isSharedCheck_1265_ = !lean_is_exclusive(v_x_1186_);
if (v_isSharedCheck_1265_ == 0)
{
v___x_1247_ = v_x_1186_;
v_isShared_1248_ = v_isSharedCheck_1265_;
goto v_resetjp_1246_;
}
else
{
lean_inc(v_vs_1245_);
lean_inc(v_ks_1244_);
lean_dec(v_x_1186_);
v___x_1247_ = lean_box(0);
v_isShared_1248_ = v_isSharedCheck_1265_;
goto v_resetjp_1246_;
}
v_resetjp_1246_:
{
lean_object* v___x_1250_; 
if (v_isShared_1248_ == 0)
{
v___x_1250_ = v___x_1247_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1264_; 
v_reuseFailAlloc_1264_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1264_, 0, v_ks_1244_);
lean_ctor_set(v_reuseFailAlloc_1264_, 1, v_vs_1245_);
v___x_1250_ = v_reuseFailAlloc_1264_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
lean_object* v_newNode_1251_; uint8_t v___y_1253_; size_t v___x_1259_; uint8_t v___x_1260_; 
v_newNode_1251_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3_spec__5___redArg(v___x_1250_, v_x_1189_, v_x_1190_);
v___x_1259_ = ((size_t)7ULL);
v___x_1260_ = lean_usize_dec_le(v___x_1259_, v_x_1188_);
if (v___x_1260_ == 0)
{
lean_object* v___x_1261_; lean_object* v___x_1262_; uint8_t v___x_1263_; 
v___x_1261_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1251_);
v___x_1262_ = lean_unsigned_to_nat(4u);
v___x_1263_ = lean_nat_dec_lt(v___x_1261_, v___x_1262_);
lean_dec(v___x_1261_);
v___y_1253_ = v___x_1263_;
goto v___jp_1252_;
}
else
{
v___y_1253_ = v___x_1260_;
goto v___jp_1252_;
}
v___jp_1252_:
{
if (v___y_1253_ == 0)
{
lean_object* v_ks_1254_; lean_object* v_vs_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; 
v_ks_1254_ = lean_ctor_get(v_newNode_1251_, 0);
lean_inc_ref(v_ks_1254_);
v_vs_1255_ = lean_ctor_get(v_newNode_1251_, 1);
lean_inc_ref(v_vs_1255_);
lean_dec_ref(v_newNode_1251_);
v___x_1256_ = lean_unsigned_to_nat(0u);
v___x_1257_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3___redArg___closed__0);
v___x_1258_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3_spec__6___redArg(v_x_1188_, v_ks_1254_, v_vs_1255_, v___x_1256_, v___x_1257_);
lean_dec_ref(v_vs_1255_);
lean_dec_ref(v_ks_1254_);
return v___x_1258_;
}
else
{
return v_newNode_1251_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3_spec__6___redArg(size_t v_depth_1266_, lean_object* v_keys_1267_, lean_object* v_vals_1268_, lean_object* v_i_1269_, lean_object* v_entries_1270_){
_start:
{
lean_object* v___x_1271_; uint8_t v___x_1272_; 
v___x_1271_ = lean_array_get_size(v_keys_1267_);
v___x_1272_ = lean_nat_dec_lt(v_i_1269_, v___x_1271_);
if (v___x_1272_ == 0)
{
lean_dec(v_i_1269_);
return v_entries_1270_;
}
else
{
lean_object* v_k_1273_; lean_object* v_fst_1274_; lean_object* v_snd_1275_; lean_object* v_v_1276_; uint64_t v___x_1277_; uint64_t v___x_1278_; uint64_t v___x_1279_; size_t v_h_1280_; size_t v___x_1281_; lean_object* v___x_1282_; size_t v___x_1283_; size_t v___x_1284_; size_t v___x_1285_; size_t v_h_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; 
v_k_1273_ = lean_array_fget_borrowed(v_keys_1267_, v_i_1269_);
v_fst_1274_ = lean_ctor_get(v_k_1273_, 0);
v_snd_1275_ = lean_ctor_get(v_k_1273_, 1);
v_v_1276_ = lean_array_fget_borrowed(v_vals_1268_, v_i_1269_);
v___x_1277_ = lean_uint64_of_nat(v_fst_1274_);
v___x_1278_ = lean_uint64_of_nat(v_snd_1275_);
v___x_1279_ = lean_uint64_mix_hash(v___x_1277_, v___x_1278_);
v_h_1280_ = lean_uint64_to_usize(v___x_1279_);
v___x_1281_ = ((size_t)5ULL);
v___x_1282_ = lean_unsigned_to_nat(1u);
v___x_1283_ = ((size_t)1ULL);
v___x_1284_ = lean_usize_sub(v_depth_1266_, v___x_1283_);
v___x_1285_ = lean_usize_mul(v___x_1281_, v___x_1284_);
v_h_1286_ = lean_usize_shift_right(v_h_1280_, v___x_1285_);
v___x_1287_ = lean_nat_add(v_i_1269_, v___x_1282_);
lean_dec(v_i_1269_);
lean_inc(v_v_1276_);
lean_inc(v_k_1273_);
v___x_1288_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3___redArg(v_entries_1270_, v_h_1286_, v_depth_1266_, v_k_1273_, v_v_1276_);
v_i_1269_ = v___x_1287_;
v_entries_1270_ = v___x_1288_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_depth_1290_, lean_object* v_keys_1291_, lean_object* v_vals_1292_, lean_object* v_i_1293_, lean_object* v_entries_1294_){
_start:
{
size_t v_depth_boxed_1295_; lean_object* v_res_1296_; 
v_depth_boxed_1295_ = lean_unbox_usize(v_depth_1290_);
lean_dec(v_depth_1290_);
v_res_1296_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3_spec__6___redArg(v_depth_boxed_1295_, v_keys_1291_, v_vals_1292_, v_i_1293_, v_entries_1294_);
lean_dec_ref(v_vals_1292_);
lean_dec_ref(v_keys_1291_);
return v_res_1296_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3___redArg___boxed(lean_object* v_x_1297_, lean_object* v_x_1298_, lean_object* v_x_1299_, lean_object* v_x_1300_, lean_object* v_x_1301_){
_start:
{
size_t v_x_3639__boxed_1302_; size_t v_x_3640__boxed_1303_; lean_object* v_res_1304_; 
v_x_3639__boxed_1302_ = lean_unbox_usize(v_x_1298_);
lean_dec(v_x_1298_);
v_x_3640__boxed_1303_ = lean_unbox_usize(v_x_1299_);
lean_dec(v_x_1299_);
v_res_1304_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3___redArg(v_x_1297_, v_x_3639__boxed_1302_, v_x_3640__boxed_1303_, v_x_1300_, v_x_1301_);
return v_res_1304_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2___redArg(lean_object* v_x_1305_, lean_object* v_x_1306_, lean_object* v_x_1307_){
_start:
{
lean_object* v_fst_1308_; lean_object* v_snd_1309_; uint64_t v___x_1310_; uint64_t v___x_1311_; uint64_t v___x_1312_; size_t v___x_1313_; size_t v___x_1314_; lean_object* v___x_1315_; 
v_fst_1308_ = lean_ctor_get(v_x_1306_, 0);
v_snd_1309_ = lean_ctor_get(v_x_1306_, 1);
v___x_1310_ = lean_uint64_of_nat(v_fst_1308_);
v___x_1311_ = lean_uint64_of_nat(v_snd_1309_);
v___x_1312_ = lean_uint64_mix_hash(v___x_1310_, v___x_1311_);
v___x_1313_ = lean_uint64_to_usize(v___x_1312_);
v___x_1314_ = ((size_t)1ULL);
v___x_1315_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3___redArg(v_x_1305_, v___x_1313_, v___x_1314_, v_x_1306_, v_x_1307_);
return v___x_1315_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0_spec__0_spec__2___redArg(lean_object* v_keys_1316_, lean_object* v_vals_1317_, lean_object* v_i_1318_, lean_object* v_k_1319_){
_start:
{
uint8_t v___y_1321_; lean_object* v___x_1327_; uint8_t v___x_1328_; 
v___x_1327_ = lean_array_get_size(v_keys_1316_);
v___x_1328_ = lean_nat_dec_lt(v_i_1318_, v___x_1327_);
if (v___x_1328_ == 0)
{
lean_object* v___x_1329_; 
lean_dec(v_i_1318_);
v___x_1329_ = lean_box(0);
return v___x_1329_;
}
else
{
lean_object* v_fst_1330_; lean_object* v_snd_1331_; lean_object* v_k_x27_1332_; lean_object* v_fst_1333_; lean_object* v_snd_1334_; uint8_t v___x_1335_; 
v_fst_1330_ = lean_ctor_get(v_k_1319_, 0);
v_snd_1331_ = lean_ctor_get(v_k_1319_, 1);
v_k_x27_1332_ = lean_array_fget_borrowed(v_keys_1316_, v_i_1318_);
v_fst_1333_ = lean_ctor_get(v_k_x27_1332_, 0);
v_snd_1334_ = lean_ctor_get(v_k_x27_1332_, 1);
v___x_1335_ = lean_nat_dec_eq(v_fst_1330_, v_fst_1333_);
if (v___x_1335_ == 0)
{
v___y_1321_ = v___x_1335_;
goto v___jp_1320_;
}
else
{
uint8_t v___x_1336_; 
v___x_1336_ = lean_nat_dec_eq(v_snd_1331_, v_snd_1334_);
v___y_1321_ = v___x_1336_;
goto v___jp_1320_;
}
}
v___jp_1320_:
{
if (v___y_1321_ == 0)
{
lean_object* v___x_1322_; lean_object* v___x_1323_; 
v___x_1322_ = lean_unsigned_to_nat(1u);
v___x_1323_ = lean_nat_add(v_i_1318_, v___x_1322_);
lean_dec(v_i_1318_);
v_i_1318_ = v___x_1323_;
goto _start;
}
else
{
lean_object* v___x_1325_; lean_object* v___x_1326_; 
v___x_1325_ = lean_array_fget_borrowed(v_vals_1317_, v_i_1318_);
lean_dec(v_i_1318_);
lean_inc(v___x_1325_);
v___x_1326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1326_, 0, v___x_1325_);
return v___x_1326_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_keys_1337_, lean_object* v_vals_1338_, lean_object* v_i_1339_, lean_object* v_k_1340_){
_start:
{
lean_object* v_res_1341_; 
v_res_1341_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0_spec__0_spec__2___redArg(v_keys_1337_, v_vals_1338_, v_i_1339_, v_k_1340_);
lean_dec_ref(v_k_1340_);
lean_dec_ref(v_vals_1338_);
lean_dec_ref(v_keys_1337_);
return v_res_1341_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0_spec__0___redArg(lean_object* v_x_1342_, size_t v_x_1343_, lean_object* v_x_1344_){
_start:
{
if (lean_obj_tag(v_x_1342_) == 0)
{
lean_object* v_es_1345_; lean_object* v___x_1346_; size_t v___x_1347_; size_t v___x_1348_; size_t v___x_1349_; lean_object* v_j_1350_; lean_object* v___x_1351_; 
v_es_1345_ = lean_ctor_get(v_x_1342_, 0);
v___x_1346_ = lean_box(2);
v___x_1347_ = ((size_t)5ULL);
v___x_1348_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0_spec__0___redArg___closed__1);
v___x_1349_ = lean_usize_land(v_x_1343_, v___x_1348_);
v_j_1350_ = lean_usize_to_nat(v___x_1349_);
v___x_1351_ = lean_array_get_borrowed(v___x_1346_, v_es_1345_, v_j_1350_);
lean_dec(v_j_1350_);
switch(lean_obj_tag(v___x_1351_))
{
case 0:
{
lean_object* v_key_1352_; lean_object* v_val_1353_; uint8_t v___y_1355_; lean_object* v_fst_1358_; lean_object* v_snd_1359_; lean_object* v_fst_1360_; lean_object* v_snd_1361_; uint8_t v___x_1362_; 
v_key_1352_ = lean_ctor_get(v___x_1351_, 0);
v_val_1353_ = lean_ctor_get(v___x_1351_, 1);
v_fst_1358_ = lean_ctor_get(v_x_1344_, 0);
v_snd_1359_ = lean_ctor_get(v_x_1344_, 1);
v_fst_1360_ = lean_ctor_get(v_key_1352_, 0);
v_snd_1361_ = lean_ctor_get(v_key_1352_, 1);
v___x_1362_ = lean_nat_dec_eq(v_fst_1358_, v_fst_1360_);
if (v___x_1362_ == 0)
{
v___y_1355_ = v___x_1362_;
goto v___jp_1354_;
}
else
{
uint8_t v___x_1363_; 
v___x_1363_ = lean_nat_dec_eq(v_snd_1359_, v_snd_1361_);
v___y_1355_ = v___x_1363_;
goto v___jp_1354_;
}
v___jp_1354_:
{
if (v___y_1355_ == 0)
{
lean_object* v___x_1356_; 
v___x_1356_ = lean_box(0);
return v___x_1356_;
}
else
{
lean_object* v___x_1357_; 
lean_inc(v_val_1353_);
v___x_1357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1357_, 0, v_val_1353_);
return v___x_1357_;
}
}
}
case 1:
{
lean_object* v_node_1364_; size_t v___x_1365_; 
v_node_1364_ = lean_ctor_get(v___x_1351_, 0);
v___x_1365_ = lean_usize_shift_right(v_x_1343_, v___x_1347_);
v_x_1342_ = v_node_1364_;
v_x_1343_ = v___x_1365_;
goto _start;
}
default: 
{
lean_object* v___x_1367_; 
v___x_1367_ = lean_box(0);
return v___x_1367_;
}
}
}
else
{
lean_object* v_ks_1368_; lean_object* v_vs_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; 
v_ks_1368_ = lean_ctor_get(v_x_1342_, 0);
v_vs_1369_ = lean_ctor_get(v_x_1342_, 1);
v___x_1370_ = lean_unsigned_to_nat(0u);
v___x_1371_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0_spec__0_spec__2___redArg(v_ks_1368_, v_vs_1369_, v___x_1370_, v_x_1344_);
return v___x_1371_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0_spec__0___redArg___boxed(lean_object* v_x_1372_, lean_object* v_x_1373_, lean_object* v_x_1374_){
_start:
{
size_t v_x_3873__boxed_1375_; lean_object* v_res_1376_; 
v_x_3873__boxed_1375_ = lean_unbox_usize(v_x_1373_);
lean_dec(v_x_1373_);
v_res_1376_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0_spec__0___redArg(v_x_1372_, v_x_3873__boxed_1375_, v_x_1374_);
lean_dec_ref(v_x_1374_);
lean_dec_ref(v_x_1372_);
return v_res_1376_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0___redArg(lean_object* v_x_1377_, lean_object* v_x_1378_){
_start:
{
lean_object* v_fst_1379_; lean_object* v_snd_1380_; uint64_t v___x_1381_; uint64_t v___x_1382_; uint64_t v___x_1383_; size_t v___x_1384_; lean_object* v___x_1385_; 
v_fst_1379_ = lean_ctor_get(v_x_1378_, 0);
v_snd_1380_ = lean_ctor_get(v_x_1378_, 1);
v___x_1381_ = lean_uint64_of_nat(v_fst_1379_);
v___x_1382_ = lean_uint64_of_nat(v_snd_1380_);
v___x_1383_ = lean_uint64_mix_hash(v___x_1381_, v___x_1382_);
v___x_1384_ = lean_uint64_to_usize(v___x_1383_);
v___x_1385_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0_spec__0___redArg(v_x_1377_, v___x_1384_, v_x_1378_);
return v___x_1385_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0___redArg___boxed(lean_object* v_x_1386_, lean_object* v_x_1387_){
_start:
{
lean_object* v_res_1388_; 
v_res_1388_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0___redArg(v_x_1386_, v_x_1387_);
lean_dec_ref(v_x_1387_);
lean_dec_ref(v_x_1386_);
return v_res_1388_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm(lean_object* v_term_1389_, lean_object* v_a_1390_, lean_object* v_a_1391_, lean_object* v_a_1392_, lean_object* v_a_1393_, lean_object* v_a_1394_, lean_object* v_a_1395_, lean_object* v_a_1396_, lean_object* v_a_1397_){
_start:
{
uint8_t v___x_1399_; lean_object* v___y_1401_; lean_object* v___y_1402_; lean_object* v___y_1466_; lean_object* v___x_1470_; 
v___x_1399_ = 0;
v___x_1470_ = l_Lean_Syntax_getPos_x3f(v_term_1389_, v___x_1399_);
if (lean_obj_tag(v___x_1470_) == 0)
{
lean_object* v___x_1471_; 
v___x_1471_ = lean_unsigned_to_nat(0u);
v___y_1466_ = v___x_1471_;
goto v___jp_1465_;
}
else
{
lean_object* v_val_1472_; 
v_val_1472_ = lean_ctor_get(v___x_1470_, 0);
lean_inc(v_val_1472_);
lean_dec_ref(v___x_1470_);
v___y_1466_ = v_val_1472_;
goto v___jp_1465_;
}
v___jp_1400_:
{
lean_object* v___x_1403_; lean_object* v_cache_1404_; lean_object* v_backwardRuleSyntax_1405_; lean_object* v_pos_1406_; lean_object* v___x_1407_; 
v___x_1403_ = lean_st_ref_get(v_a_1391_);
v_cache_1404_ = lean_ctor_get(v___x_1403_, 3);
lean_inc_ref(v_cache_1404_);
lean_dec(v___x_1403_);
v_backwardRuleSyntax_1405_ = lean_ctor_get(v_cache_1404_, 1);
lean_inc_ref(v_backwardRuleSyntax_1405_);
lean_dec_ref(v_cache_1404_);
v_pos_1406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_pos_1406_, 0, v___y_1401_);
lean_ctor_set(v_pos_1406_, 1, v___y_1402_);
v___x_1407_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0___redArg(v_backwardRuleSyntax_1405_, v_pos_1406_);
lean_dec_ref(v_backwardRuleSyntax_1405_);
if (lean_obj_tag(v___x_1407_) == 1)
{
lean_object* v_val_1408_; lean_object* v___x_1410_; uint8_t v_isShared_1411_; uint8_t v_isSharedCheck_1415_; 
lean_dec_ref(v_pos_1406_);
lean_dec(v_term_1389_);
v_val_1408_ = lean_ctor_get(v___x_1407_, 0);
v_isSharedCheck_1415_ = !lean_is_exclusive(v___x_1407_);
if (v_isSharedCheck_1415_ == 0)
{
v___x_1410_ = v___x_1407_;
v_isShared_1411_ = v_isSharedCheck_1415_;
goto v_resetjp_1409_;
}
else
{
lean_inc(v_val_1408_);
lean_dec(v___x_1407_);
v___x_1410_ = lean_box(0);
v_isShared_1411_ = v_isSharedCheck_1415_;
goto v_resetjp_1409_;
}
v_resetjp_1409_:
{
lean_object* v___x_1413_; 
if (v_isShared_1411_ == 0)
{
lean_ctor_set_tag(v___x_1410_, 0);
v___x_1413_ = v___x_1410_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v_val_1408_);
v___x_1413_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
return v___x_1413_;
}
}
}
else
{
lean_object* v___x_1416_; uint8_t v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___f_1420_; lean_object* v___x_1421_; 
lean_dec(v___x_1407_);
v___x_1416_ = lean_box(0);
v___x_1417_ = 1;
v___x_1418_ = lean_box(v___x_1417_);
v___x_1419_ = lean_box(v___x_1399_);
v___f_1420_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm___lam__0___boxed), 13, 4);
lean_closure_set(v___f_1420_, 0, v_term_1389_);
lean_closure_set(v___f_1420_, 1, v___x_1416_);
lean_closure_set(v___f_1420_, 2, v___x_1418_);
lean_closure_set(v___f_1420_, 3, v___x_1419_);
v___x_1421_ = l_Lean_Elab_Tactic_Grind_withMainContext___redArg(v___f_1420_, v_a_1390_, v_a_1391_, v_a_1392_, v_a_1393_, v_a_1394_, v_a_1395_, v_a_1396_, v_a_1397_);
if (lean_obj_tag(v___x_1421_) == 0)
{
lean_object* v_a_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; 
v_a_1422_ = lean_ctor_get(v___x_1421_, 0);
lean_inc(v_a_1422_);
lean_dec_ref(v___x_1421_);
v___x_1423_ = lean_box(0);
v___x_1424_ = l_Lean_Meta_Sym_mkBackwardRuleFromExpr(v_a_1422_, v___x_1423_, v___x_1416_, v_a_1394_, v_a_1395_, v_a_1396_, v_a_1397_);
if (lean_obj_tag(v___x_1424_) == 0)
{
lean_object* v_a_1425_; lean_object* v___x_1427_; uint8_t v_isShared_1428_; uint8_t v_isSharedCheck_1456_; 
v_a_1425_ = lean_ctor_get(v___x_1424_, 0);
v_isSharedCheck_1456_ = !lean_is_exclusive(v___x_1424_);
if (v_isSharedCheck_1456_ == 0)
{
v___x_1427_ = v___x_1424_;
v_isShared_1428_ = v_isSharedCheck_1456_;
goto v_resetjp_1426_;
}
else
{
lean_inc(v_a_1425_);
lean_dec(v___x_1424_);
v___x_1427_ = lean_box(0);
v_isShared_1428_ = v_isSharedCheck_1456_;
goto v_resetjp_1426_;
}
v_resetjp_1426_:
{
lean_object* v___x_1429_; lean_object* v_cache_1430_; lean_object* v_symState_1431_; lean_object* v_grindState_1432_; lean_object* v_goals_1433_; lean_object* v___x_1435_; uint8_t v_isShared_1436_; uint8_t v_isSharedCheck_1455_; 
v___x_1429_ = lean_st_ref_take(v_a_1391_);
v_cache_1430_ = lean_ctor_get(v___x_1429_, 3);
v_symState_1431_ = lean_ctor_get(v___x_1429_, 0);
v_grindState_1432_ = lean_ctor_get(v___x_1429_, 1);
v_goals_1433_ = lean_ctor_get(v___x_1429_, 2);
v_isSharedCheck_1455_ = !lean_is_exclusive(v___x_1429_);
if (v_isSharedCheck_1455_ == 0)
{
v___x_1435_ = v___x_1429_;
v_isShared_1436_ = v_isSharedCheck_1455_;
goto v_resetjp_1434_;
}
else
{
lean_inc(v_cache_1430_);
lean_inc(v_goals_1433_);
lean_inc(v_grindState_1432_);
lean_inc(v_symState_1431_);
lean_dec(v___x_1429_);
v___x_1435_ = lean_box(0);
v_isShared_1436_ = v_isSharedCheck_1455_;
goto v_resetjp_1434_;
}
v_resetjp_1434_:
{
lean_object* v_backwardRuleName_1437_; lean_object* v_backwardRuleSyntax_1438_; lean_object* v_simpState_1439_; lean_object* v___x_1441_; uint8_t v_isShared_1442_; uint8_t v_isSharedCheck_1454_; 
v_backwardRuleName_1437_ = lean_ctor_get(v_cache_1430_, 0);
v_backwardRuleSyntax_1438_ = lean_ctor_get(v_cache_1430_, 1);
v_simpState_1439_ = lean_ctor_get(v_cache_1430_, 2);
v_isSharedCheck_1454_ = !lean_is_exclusive(v_cache_1430_);
if (v_isSharedCheck_1454_ == 0)
{
v___x_1441_ = v_cache_1430_;
v_isShared_1442_ = v_isSharedCheck_1454_;
goto v_resetjp_1440_;
}
else
{
lean_inc(v_simpState_1439_);
lean_inc(v_backwardRuleSyntax_1438_);
lean_inc(v_backwardRuleName_1437_);
lean_dec(v_cache_1430_);
v___x_1441_ = lean_box(0);
v_isShared_1442_ = v_isSharedCheck_1454_;
goto v_resetjp_1440_;
}
v_resetjp_1440_:
{
lean_object* v___x_1443_; lean_object* v___x_1445_; 
lean_inc(v_a_1425_);
v___x_1443_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2___redArg(v_backwardRuleSyntax_1438_, v_pos_1406_, v_a_1425_);
if (v_isShared_1442_ == 0)
{
lean_ctor_set(v___x_1441_, 1, v___x_1443_);
v___x_1445_ = v___x_1441_;
goto v_reusejp_1444_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v_backwardRuleName_1437_);
lean_ctor_set(v_reuseFailAlloc_1453_, 1, v___x_1443_);
lean_ctor_set(v_reuseFailAlloc_1453_, 2, v_simpState_1439_);
v___x_1445_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1444_;
}
v_reusejp_1444_:
{
lean_object* v___x_1447_; 
if (v_isShared_1436_ == 0)
{
lean_ctor_set(v___x_1435_, 3, v___x_1445_);
v___x_1447_ = v___x_1435_;
goto v_reusejp_1446_;
}
else
{
lean_object* v_reuseFailAlloc_1452_; 
v_reuseFailAlloc_1452_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1452_, 0, v_symState_1431_);
lean_ctor_set(v_reuseFailAlloc_1452_, 1, v_grindState_1432_);
lean_ctor_set(v_reuseFailAlloc_1452_, 2, v_goals_1433_);
lean_ctor_set(v_reuseFailAlloc_1452_, 3, v___x_1445_);
v___x_1447_ = v_reuseFailAlloc_1452_;
goto v_reusejp_1446_;
}
v_reusejp_1446_:
{
lean_object* v___x_1448_; lean_object* v___x_1450_; 
v___x_1448_ = lean_st_ref_set(v_a_1391_, v___x_1447_);
if (v_isShared_1428_ == 0)
{
v___x_1450_ = v___x_1427_;
goto v_reusejp_1449_;
}
else
{
lean_object* v_reuseFailAlloc_1451_; 
v_reuseFailAlloc_1451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1451_, 0, v_a_1425_);
v___x_1450_ = v_reuseFailAlloc_1451_;
goto v_reusejp_1449_;
}
v_reusejp_1449_:
{
return v___x_1450_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_pos_1406_);
return v___x_1424_;
}
}
else
{
lean_object* v_a_1457_; lean_object* v___x_1459_; uint8_t v_isShared_1460_; uint8_t v_isSharedCheck_1464_; 
lean_dec_ref(v_pos_1406_);
v_a_1457_ = lean_ctor_get(v___x_1421_, 0);
v_isSharedCheck_1464_ = !lean_is_exclusive(v___x_1421_);
if (v_isSharedCheck_1464_ == 0)
{
v___x_1459_ = v___x_1421_;
v_isShared_1460_ = v_isSharedCheck_1464_;
goto v_resetjp_1458_;
}
else
{
lean_inc(v_a_1457_);
lean_dec(v___x_1421_);
v___x_1459_ = lean_box(0);
v_isShared_1460_ = v_isSharedCheck_1464_;
goto v_resetjp_1458_;
}
v_resetjp_1458_:
{
lean_object* v___x_1462_; 
if (v_isShared_1460_ == 0)
{
v___x_1462_ = v___x_1459_;
goto v_reusejp_1461_;
}
else
{
lean_object* v_reuseFailAlloc_1463_; 
v_reuseFailAlloc_1463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1463_, 0, v_a_1457_);
v___x_1462_ = v_reuseFailAlloc_1463_;
goto v_reusejp_1461_;
}
v_reusejp_1461_:
{
return v___x_1462_;
}
}
}
}
}
v___jp_1465_:
{
lean_object* v___x_1467_; 
v___x_1467_ = l_Lean_Syntax_getTailPos_x3f(v_term_1389_, v___x_1399_);
if (lean_obj_tag(v___x_1467_) == 0)
{
lean_object* v___x_1468_; 
v___x_1468_ = lean_unsigned_to_nat(0u);
v___y_1401_ = v___y_1466_;
v___y_1402_ = v___x_1468_;
goto v___jp_1400_;
}
else
{
lean_object* v_val_1469_; 
v_val_1469_ = lean_ctor_get(v___x_1467_, 0);
lean_inc(v_val_1469_);
lean_dec_ref(v___x_1467_);
v___y_1401_ = v___y_1466_;
v___y_1402_ = v_val_1469_;
goto v___jp_1400_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm___boxed(lean_object* v_term_1473_, lean_object* v_a_1474_, lean_object* v_a_1475_, lean_object* v_a_1476_, lean_object* v_a_1477_, lean_object* v_a_1478_, lean_object* v_a_1479_, lean_object* v_a_1480_, lean_object* v_a_1481_, lean_object* v_a_1482_){
_start:
{
lean_object* v_res_1483_; 
v_res_1483_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm(v_term_1473_, v_a_1474_, v_a_1475_, v_a_1476_, v_a_1477_, v_a_1478_, v_a_1479_, v_a_1480_, v_a_1481_);
lean_dec(v_a_1481_);
lean_dec_ref(v_a_1480_);
lean_dec(v_a_1479_);
lean_dec_ref(v_a_1478_);
lean_dec(v_a_1477_);
lean_dec_ref(v_a_1476_);
lean_dec(v_a_1475_);
lean_dec_ref(v_a_1474_);
return v_res_1483_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0(lean_object* v_00_u03b2_1484_, lean_object* v_x_1485_, lean_object* v_x_1486_){
_start:
{
lean_object* v___x_1487_; 
v___x_1487_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0___redArg(v_x_1485_, v_x_1486_);
return v___x_1487_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0___boxed(lean_object* v_00_u03b2_1488_, lean_object* v_x_1489_, lean_object* v_x_1490_){
_start:
{
lean_object* v_res_1491_; 
v_res_1491_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0(v_00_u03b2_1488_, v_x_1489_, v_x_1490_);
lean_dec_ref(v_x_1490_);
lean_dec_ref(v_x_1489_);
return v_res_1491_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2(lean_object* v_00_u03b2_1492_, lean_object* v_x_1493_, lean_object* v_x_1494_, lean_object* v_x_1495_){
_start:
{
lean_object* v___x_1496_; 
v___x_1496_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2___redArg(v_x_1493_, v_x_1494_, v_x_1495_);
return v___x_1496_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0_spec__0(lean_object* v_00_u03b2_1497_, lean_object* v_x_1498_, size_t v_x_1499_, lean_object* v_x_1500_){
_start:
{
lean_object* v___x_1501_; 
v___x_1501_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0_spec__0___redArg(v_x_1498_, v_x_1499_, v_x_1500_);
return v___x_1501_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1502_, lean_object* v_x_1503_, lean_object* v_x_1504_, lean_object* v_x_1505_){
_start:
{
size_t v_x_4104__boxed_1506_; lean_object* v_res_1507_; 
v_x_4104__boxed_1506_ = lean_unbox_usize(v_x_1504_);
lean_dec(v_x_1504_);
v_res_1507_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0_spec__0(v_00_u03b2_1502_, v_x_1503_, v_x_4104__boxed_1506_, v_x_1505_);
lean_dec_ref(v_x_1505_);
lean_dec_ref(v_x_1503_);
return v_res_1507_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3(lean_object* v_00_u03b2_1508_, lean_object* v_x_1509_, size_t v_x_1510_, size_t v_x_1511_, lean_object* v_x_1512_, lean_object* v_x_1513_){
_start:
{
lean_object* v___x_1514_; 
v___x_1514_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3___redArg(v_x_1509_, v_x_1510_, v_x_1511_, v_x_1512_, v_x_1513_);
return v___x_1514_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3___boxed(lean_object* v_00_u03b2_1515_, lean_object* v_x_1516_, lean_object* v_x_1517_, lean_object* v_x_1518_, lean_object* v_x_1519_, lean_object* v_x_1520_){
_start:
{
size_t v_x_4115__boxed_1521_; size_t v_x_4116__boxed_1522_; lean_object* v_res_1523_; 
v_x_4115__boxed_1521_ = lean_unbox_usize(v_x_1517_);
lean_dec(v_x_1517_);
v_x_4116__boxed_1522_ = lean_unbox_usize(v_x_1518_);
lean_dec(v_x_1518_);
v_res_1523_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3(v_00_u03b2_1515_, v_x_1516_, v_x_4115__boxed_1521_, v_x_4116__boxed_1522_, v_x_1519_, v_x_1520_);
return v_res_1523_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1524_, lean_object* v_keys_1525_, lean_object* v_vals_1526_, lean_object* v_heq_1527_, lean_object* v_i_1528_, lean_object* v_k_1529_){
_start:
{
lean_object* v___x_1530_; 
v___x_1530_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0_spec__0_spec__2___redArg(v_keys_1525_, v_vals_1526_, v_i_1528_, v_k_1529_);
return v___x_1530_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1531_, lean_object* v_keys_1532_, lean_object* v_vals_1533_, lean_object* v_heq_1534_, lean_object* v_i_1535_, lean_object* v_k_1536_){
_start:
{
lean_object* v_res_1537_; 
v_res_1537_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0_spec__0_spec__2(v_00_u03b2_1531_, v_keys_1532_, v_vals_1533_, v_heq_1534_, v_i_1535_, v_k_1536_);
lean_dec_ref(v_k_1536_);
lean_dec_ref(v_vals_1533_);
lean_dec_ref(v_keys_1532_);
return v_res_1537_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_1538_, lean_object* v_n_1539_, lean_object* v_k_1540_, lean_object* v_v_1541_){
_start:
{
lean_object* v___x_1542_; 
v___x_1542_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3_spec__5___redArg(v_n_1539_, v_k_1540_, v_v_1541_);
return v___x_1542_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3_spec__6(lean_object* v_00_u03b2_1543_, size_t v_depth_1544_, lean_object* v_keys_1545_, lean_object* v_vals_1546_, lean_object* v_heq_1547_, lean_object* v_i_1548_, lean_object* v_entries_1549_){
_start:
{
lean_object* v___x_1550_; 
v___x_1550_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3_spec__6___redArg(v_depth_1544_, v_keys_1545_, v_vals_1546_, v_i_1548_, v_entries_1549_);
return v___x_1550_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3_spec__6___boxed(lean_object* v_00_u03b2_1551_, lean_object* v_depth_1552_, lean_object* v_keys_1553_, lean_object* v_vals_1554_, lean_object* v_heq_1555_, lean_object* v_i_1556_, lean_object* v_entries_1557_){
_start:
{
size_t v_depth_boxed_1558_; lean_object* v_res_1559_; 
v_depth_boxed_1558_ = lean_unbox_usize(v_depth_1552_);
lean_dec(v_depth_1552_);
v_res_1559_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3_spec__6(v_00_u03b2_1551_, v_depth_boxed_1558_, v_keys_1553_, v_vals_1554_, v_heq_1555_, v_i_1556_, v_entries_1557_);
lean_dec_ref(v_vals_1554_);
lean_dec_ref(v_keys_1553_);
return v_res_1559_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3_spec__5_spec__6(lean_object* v_00_u03b2_1560_, lean_object* v_x_1561_, lean_object* v_x_1562_, lean_object* v_x_1563_, lean_object* v_x_1564_){
_start:
{
lean_object* v___x_1565_; 
v___x_1565_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3_spec__5_spec__6___redArg(v_x_1561_, v_x_1562_, v_x_1563_, v_x_1564_);
return v___x_1565_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply_spec__0___redArg___lam__0(lean_object* v_x_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_){
_start:
{
lean_object* v___x_1576_; 
lean_inc(v___y_1570_);
lean_inc_ref(v___y_1569_);
lean_inc(v___y_1568_);
lean_inc_ref(v___y_1567_);
v___x_1576_ = lean_apply_9(v_x_1566_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_, lean_box(0));
return v___x_1576_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply_spec__0___redArg___lam__0___boxed(lean_object* v_x_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_){
_start:
{
lean_object* v_res_1587_; 
v_res_1587_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply_spec__0___redArg___lam__0(v_x_1577_, v___y_1578_, v___y_1579_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_, v___y_1585_);
lean_dec(v___y_1581_);
lean_dec_ref(v___y_1580_);
lean_dec(v___y_1579_);
lean_dec_ref(v___y_1578_);
return v_res_1587_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply_spec__0___redArg(lean_object* v_mvarId_1588_, lean_object* v_x_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_){
_start:
{
lean_object* v___f_1599_; lean_object* v___x_1600_; 
lean_inc(v___y_1593_);
lean_inc_ref(v___y_1592_);
lean_inc(v___y_1591_);
lean_inc_ref(v___y_1590_);
v___f_1599_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply_spec__0___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_1599_, 0, v_x_1589_);
lean_closure_set(v___f_1599_, 1, v___y_1590_);
lean_closure_set(v___f_1599_, 2, v___y_1591_);
lean_closure_set(v___f_1599_, 3, v___y_1592_);
lean_closure_set(v___f_1599_, 4, v___y_1593_);
v___x_1600_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1588_, v___f_1599_, v___y_1594_, v___y_1595_, v___y_1596_, v___y_1597_);
if (lean_obj_tag(v___x_1600_) == 0)
{
return v___x_1600_;
}
else
{
lean_object* v_a_1601_; lean_object* v___x_1603_; uint8_t v_isShared_1604_; uint8_t v_isSharedCheck_1608_; 
v_a_1601_ = lean_ctor_get(v___x_1600_, 0);
v_isSharedCheck_1608_ = !lean_is_exclusive(v___x_1600_);
if (v_isSharedCheck_1608_ == 0)
{
v___x_1603_ = v___x_1600_;
v_isShared_1604_ = v_isSharedCheck_1608_;
goto v_resetjp_1602_;
}
else
{
lean_inc(v_a_1601_);
lean_dec(v___x_1600_);
v___x_1603_ = lean_box(0);
v_isShared_1604_ = v_isSharedCheck_1608_;
goto v_resetjp_1602_;
}
v_resetjp_1602_:
{
lean_object* v___x_1606_; 
if (v_isShared_1604_ == 0)
{
v___x_1606_ = v___x_1603_;
goto v_reusejp_1605_;
}
else
{
lean_object* v_reuseFailAlloc_1607_; 
v_reuseFailAlloc_1607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1607_, 0, v_a_1601_);
v___x_1606_ = v_reuseFailAlloc_1607_;
goto v_reusejp_1605_;
}
v_reusejp_1605_:
{
return v___x_1606_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply_spec__0___redArg___boxed(lean_object* v_mvarId_1609_, lean_object* v_x_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_){
_start:
{
lean_object* v_res_1620_; 
v_res_1620_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply_spec__0___redArg(v_mvarId_1609_, v_x_1610_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_);
lean_dec(v___y_1618_);
lean_dec_ref(v___y_1617_);
lean_dec(v___y_1616_);
lean_dec_ref(v___y_1615_);
lean_dec(v___y_1614_);
lean_dec_ref(v___y_1613_);
lean_dec(v___y_1612_);
lean_dec_ref(v___y_1611_);
return v_res_1620_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply_spec__0(lean_object* v_00_u03b1_1621_, lean_object* v_mvarId_1622_, lean_object* v_x_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_){
_start:
{
lean_object* v___x_1633_; 
v___x_1633_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply_spec__0___redArg(v_mvarId_1622_, v_x_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_);
return v___x_1633_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply_spec__0___boxed(lean_object* v_00_u03b1_1634_, lean_object* v_mvarId_1635_, lean_object* v_x_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_){
_start:
{
lean_object* v_res_1646_; 
v_res_1646_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply_spec__0(v_00_u03b1_1634_, v_mvarId_1635_, v_x_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_);
lean_dec(v___y_1644_);
lean_dec_ref(v___y_1643_);
lean_dec(v___y_1642_);
lean_dec_ref(v___y_1641_);
lean_dec(v___y_1640_);
lean_dec_ref(v___y_1639_);
lean_dec(v___y_1638_);
lean_dec_ref(v___y_1637_);
return v_res_1646_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1648_; lean_object* v___x_1649_; 
v___x_1648_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___lam__0___closed__0));
v___x_1649_ = l_Lean_stringToMessageData(v___x_1648_);
return v___x_1649_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___lam__0(lean_object* v_a_1650_, lean_object* v_rule_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_){
_start:
{
lean_object* v___x_1661_; lean_object* v___x_1662_; 
v___x_1661_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Goal_apply___boxed), 9, 2);
lean_closure_set(v___x_1661_, 0, v_a_1650_);
lean_closure_set(v___x_1661_, 1, v_rule_1651_);
v___x_1662_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_liftSymM___redArg(v___x_1661_, v___y_1652_, v___y_1653_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_);
if (lean_obj_tag(v___x_1662_) == 0)
{
lean_object* v_a_1663_; 
v_a_1663_ = lean_ctor_get(v___x_1662_, 0);
lean_inc(v_a_1663_);
lean_dec_ref(v___x_1662_);
if (lean_obj_tag(v_a_1663_) == 0)
{
lean_object* v___x_1664_; lean_object* v___x_1665_; 
v___x_1664_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___lam__0___closed__1, &l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___lam__0___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___lam__0___closed__1);
v___x_1665_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_ensureSym_spec__0___redArg(v___x_1664_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_);
return v___x_1665_;
}
else
{
lean_object* v_subgoals_1666_; lean_object* v___x_1667_; 
v_subgoals_1666_ = lean_ctor_get(v_a_1663_, 0);
lean_inc(v_subgoals_1666_);
lean_dec_ref(v_a_1663_);
v___x_1667_ = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(v_subgoals_1666_, v___y_1653_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_);
return v___x_1667_;
}
}
else
{
lean_object* v_a_1668_; lean_object* v___x_1670_; uint8_t v_isShared_1671_; uint8_t v_isSharedCheck_1675_; 
v_a_1668_ = lean_ctor_get(v___x_1662_, 0);
v_isSharedCheck_1675_ = !lean_is_exclusive(v___x_1662_);
if (v_isSharedCheck_1675_ == 0)
{
v___x_1670_ = v___x_1662_;
v_isShared_1671_ = v_isSharedCheck_1675_;
goto v_resetjp_1669_;
}
else
{
lean_inc(v_a_1668_);
lean_dec(v___x_1662_);
v___x_1670_ = lean_box(0);
v_isShared_1671_ = v_isSharedCheck_1675_;
goto v_resetjp_1669_;
}
v_resetjp_1669_:
{
lean_object* v___x_1673_; 
if (v_isShared_1671_ == 0)
{
v___x_1673_ = v___x_1670_;
goto v_reusejp_1672_;
}
else
{
lean_object* v_reuseFailAlloc_1674_; 
v_reuseFailAlloc_1674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1674_, 0, v_a_1668_);
v___x_1673_ = v_reuseFailAlloc_1674_;
goto v_reusejp_1672_;
}
v_reusejp_1672_:
{
return v___x_1673_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___lam__0___boxed(lean_object* v_a_1676_, lean_object* v_rule_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_){
_start:
{
lean_object* v_res_1687_; 
v_res_1687_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___lam__0(v_a_1676_, v_rule_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_);
lean_dec(v___y_1685_);
lean_dec_ref(v___y_1684_);
lean_dec(v___y_1683_);
lean_dec_ref(v___y_1682_);
lean_dec(v___y_1681_);
lean_dec_ref(v___y_1680_);
lean_dec(v___y_1679_);
lean_dec_ref(v___y_1678_);
return v_res_1687_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___lam__1(uint8_t v___x_1688_, lean_object* v___x_1689_, lean_object* v___f_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_){
_start:
{
if (v___x_1688_ == 0)
{
lean_object* v___x_1700_; 
v___x_1700_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm(v___x_1689_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_);
if (lean_obj_tag(v___x_1700_) == 0)
{
lean_object* v_a_1701_; lean_object* v___x_1702_; 
v_a_1701_ = lean_ctor_get(v___x_1700_, 0);
lean_inc(v_a_1701_);
lean_dec_ref(v___x_1700_);
lean_inc(v___y_1698_);
lean_inc_ref(v___y_1697_);
lean_inc(v___y_1696_);
lean_inc_ref(v___y_1695_);
lean_inc(v___y_1694_);
lean_inc_ref(v___y_1693_);
lean_inc(v___y_1692_);
lean_inc_ref(v___y_1691_);
v___x_1702_ = lean_apply_10(v___f_1690_, v_a_1701_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_, lean_box(0));
return v___x_1702_;
}
else
{
lean_object* v_a_1703_; lean_object* v___x_1705_; uint8_t v_isShared_1706_; uint8_t v_isSharedCheck_1710_; 
lean_dec_ref(v___f_1690_);
v_a_1703_ = lean_ctor_get(v___x_1700_, 0);
v_isSharedCheck_1710_ = !lean_is_exclusive(v___x_1700_);
if (v_isSharedCheck_1710_ == 0)
{
v___x_1705_ = v___x_1700_;
v_isShared_1706_ = v_isSharedCheck_1710_;
goto v_resetjp_1704_;
}
else
{
lean_inc(v_a_1703_);
lean_dec(v___x_1700_);
v___x_1705_ = lean_box(0);
v_isShared_1706_ = v_isSharedCheck_1710_;
goto v_resetjp_1704_;
}
v_resetjp_1704_:
{
lean_object* v___x_1708_; 
if (v_isShared_1706_ == 0)
{
v___x_1708_ = v___x_1705_;
goto v_reusejp_1707_;
}
else
{
lean_object* v_reuseFailAlloc_1709_; 
v_reuseFailAlloc_1709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1709_, 0, v_a_1703_);
v___x_1708_ = v_reuseFailAlloc_1709_;
goto v_reusejp_1707_;
}
v_reusejp_1707_:
{
return v___x_1708_;
}
}
}
}
else
{
lean_object* v___x_1711_; 
v___x_1711_ = l_Lean_Elab_Tactic_Grind_saveState___redArg(v___y_1692_, v___y_1694_, v___y_1696_, v___y_1698_);
if (lean_obj_tag(v___x_1711_) == 0)
{
lean_object* v_a_1712_; lean_object* v___x_1714_; uint8_t v_isShared_1715_; uint8_t v_isSharedCheck_1745_; 
v_a_1712_ = lean_ctor_get(v___x_1711_, 0);
v_isSharedCheck_1745_ = !lean_is_exclusive(v___x_1711_);
if (v_isSharedCheck_1745_ == 0)
{
v___x_1714_ = v___x_1711_;
v_isShared_1715_ = v_isSharedCheck_1745_;
goto v_resetjp_1713_;
}
else
{
lean_inc(v_a_1712_);
lean_dec(v___x_1711_);
v___x_1714_ = lean_box(0);
v_isShared_1715_ = v_isSharedCheck_1745_;
goto v_resetjp_1713_;
}
v_resetjp_1713_:
{
lean_object* v___y_1717_; uint8_t v___y_1718_; lean_object* v_a_1735_; lean_object* v___x_1738_; 
lean_inc(v___x_1689_);
v___x_1738_ = l_Lean_realizeGlobalConstNoOverload(v___x_1689_, v___y_1697_, v___y_1698_);
if (lean_obj_tag(v___x_1738_) == 0)
{
lean_object* v_a_1739_; lean_object* v___x_1740_; 
v_a_1739_ = lean_ctor_get(v___x_1738_, 0);
lean_inc(v_a_1739_);
lean_dec_ref(v___x_1738_);
v___x_1740_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule___redArg(v_a_1739_, v___y_1692_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_);
if (lean_obj_tag(v___x_1740_) == 0)
{
lean_object* v_a_1741_; lean_object* v___x_1742_; 
lean_del_object(v___x_1714_);
lean_dec(v_a_1712_);
lean_dec(v___x_1689_);
v_a_1741_ = lean_ctor_get(v___x_1740_, 0);
lean_inc(v_a_1741_);
lean_dec_ref(v___x_1740_);
lean_inc(v___y_1698_);
lean_inc_ref(v___y_1697_);
lean_inc(v___y_1696_);
lean_inc_ref(v___y_1695_);
lean_inc(v___y_1694_);
lean_inc_ref(v___y_1693_);
lean_inc(v___y_1692_);
lean_inc_ref(v___y_1691_);
v___x_1742_ = lean_apply_10(v___f_1690_, v_a_1741_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_, lean_box(0));
return v___x_1742_;
}
else
{
lean_object* v_a_1743_; 
v_a_1743_ = lean_ctor_get(v___x_1740_, 0);
lean_inc(v_a_1743_);
lean_dec_ref(v___x_1740_);
v_a_1735_ = v_a_1743_;
goto v___jp_1734_;
}
}
else
{
lean_object* v_a_1744_; 
v_a_1744_ = lean_ctor_get(v___x_1738_, 0);
lean_inc(v_a_1744_);
lean_dec_ref(v___x_1738_);
v_a_1735_ = v_a_1744_;
goto v___jp_1734_;
}
v___jp_1716_:
{
if (v___y_1718_ == 0)
{
lean_object* v___x_1719_; 
lean_dec_ref(v___y_1717_);
lean_del_object(v___x_1714_);
v___x_1719_ = l_Lean_Elab_Tactic_Grind_SavedState_restore___redArg(v_a_1712_, v___y_1718_, v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_);
if (lean_obj_tag(v___x_1719_) == 0)
{
lean_object* v___x_1720_; 
lean_dec_ref(v___x_1719_);
v___x_1720_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm(v___x_1689_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_);
if (lean_obj_tag(v___x_1720_) == 0)
{
lean_object* v_a_1721_; lean_object* v___x_1722_; 
v_a_1721_ = lean_ctor_get(v___x_1720_, 0);
lean_inc(v_a_1721_);
lean_dec_ref(v___x_1720_);
lean_inc(v___y_1698_);
lean_inc_ref(v___y_1697_);
lean_inc(v___y_1696_);
lean_inc_ref(v___y_1695_);
lean_inc(v___y_1694_);
lean_inc_ref(v___y_1693_);
lean_inc(v___y_1692_);
lean_inc_ref(v___y_1691_);
v___x_1722_ = lean_apply_10(v___f_1690_, v_a_1721_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_, lean_box(0));
return v___x_1722_;
}
else
{
lean_object* v_a_1723_; lean_object* v___x_1725_; uint8_t v_isShared_1726_; uint8_t v_isSharedCheck_1730_; 
lean_dec_ref(v___f_1690_);
v_a_1723_ = lean_ctor_get(v___x_1720_, 0);
v_isSharedCheck_1730_ = !lean_is_exclusive(v___x_1720_);
if (v_isSharedCheck_1730_ == 0)
{
v___x_1725_ = v___x_1720_;
v_isShared_1726_ = v_isSharedCheck_1730_;
goto v_resetjp_1724_;
}
else
{
lean_inc(v_a_1723_);
lean_dec(v___x_1720_);
v___x_1725_ = lean_box(0);
v_isShared_1726_ = v_isSharedCheck_1730_;
goto v_resetjp_1724_;
}
v_resetjp_1724_:
{
lean_object* v___x_1728_; 
if (v_isShared_1726_ == 0)
{
v___x_1728_ = v___x_1725_;
goto v_reusejp_1727_;
}
else
{
lean_object* v_reuseFailAlloc_1729_; 
v_reuseFailAlloc_1729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1729_, 0, v_a_1723_);
v___x_1728_ = v_reuseFailAlloc_1729_;
goto v_reusejp_1727_;
}
v_reusejp_1727_:
{
return v___x_1728_;
}
}
}
}
else
{
lean_dec_ref(v___f_1690_);
lean_dec(v___x_1689_);
return v___x_1719_;
}
}
else
{
lean_object* v___x_1732_; 
lean_dec(v_a_1712_);
lean_dec_ref(v___f_1690_);
lean_dec(v___x_1689_);
if (v_isShared_1715_ == 0)
{
lean_ctor_set_tag(v___x_1714_, 1);
lean_ctor_set(v___x_1714_, 0, v___y_1717_);
v___x_1732_ = v___x_1714_;
goto v_reusejp_1731_;
}
else
{
lean_object* v_reuseFailAlloc_1733_; 
v_reuseFailAlloc_1733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1733_, 0, v___y_1717_);
v___x_1732_ = v_reuseFailAlloc_1733_;
goto v_reusejp_1731_;
}
v_reusejp_1731_:
{
return v___x_1732_;
}
}
}
v___jp_1734_:
{
uint8_t v___x_1736_; 
v___x_1736_ = l_Lean_Exception_isInterrupt(v_a_1735_);
if (v___x_1736_ == 0)
{
uint8_t v___x_1737_; 
lean_inc_ref(v_a_1735_);
v___x_1737_ = l_Lean_Exception_isRuntime(v_a_1735_);
v___y_1717_ = v_a_1735_;
v___y_1718_ = v___x_1737_;
goto v___jp_1716_;
}
else
{
v___y_1717_ = v_a_1735_;
v___y_1718_ = v___x_1736_;
goto v___jp_1716_;
}
}
}
}
else
{
lean_object* v_a_1746_; lean_object* v___x_1748_; uint8_t v_isShared_1749_; uint8_t v_isSharedCheck_1753_; 
lean_dec_ref(v___f_1690_);
lean_dec(v___x_1689_);
v_a_1746_ = lean_ctor_get(v___x_1711_, 0);
v_isSharedCheck_1753_ = !lean_is_exclusive(v___x_1711_);
if (v_isSharedCheck_1753_ == 0)
{
v___x_1748_ = v___x_1711_;
v_isShared_1749_ = v_isSharedCheck_1753_;
goto v_resetjp_1747_;
}
else
{
lean_inc(v_a_1746_);
lean_dec(v___x_1711_);
v___x_1748_ = lean_box(0);
v_isShared_1749_ = v_isSharedCheck_1753_;
goto v_resetjp_1747_;
}
v_resetjp_1747_:
{
lean_object* v___x_1751_; 
if (v_isShared_1749_ == 0)
{
v___x_1751_ = v___x_1748_;
goto v_reusejp_1750_;
}
else
{
lean_object* v_reuseFailAlloc_1752_; 
v_reuseFailAlloc_1752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1752_, 0, v_a_1746_);
v___x_1751_ = v_reuseFailAlloc_1752_;
goto v_reusejp_1750_;
}
v_reusejp_1750_:
{
return v___x_1751_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___lam__1___boxed(lean_object* v___x_1754_, lean_object* v___x_1755_, lean_object* v___f_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_){
_start:
{
uint8_t v___x_3542__boxed_1766_; lean_object* v_res_1767_; 
v___x_3542__boxed_1766_ = lean_unbox(v___x_1754_);
v_res_1767_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___lam__1(v___x_3542__boxed_1766_, v___x_1755_, v___f_1756_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_);
lean_dec(v___y_1764_);
lean_dec_ref(v___y_1763_);
lean_dec(v___y_1762_);
lean_dec_ref(v___y_1761_);
lean_dec(v___y_1760_);
lean_dec_ref(v___y_1759_);
lean_dec(v___y_1758_);
lean_dec_ref(v___y_1757_);
return v_res_1767_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply(lean_object* v_stx_1775_, lean_object* v_a_1776_, lean_object* v_a_1777_, lean_object* v_a_1778_, lean_object* v_a_1779_, lean_object* v_a_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_){
_start:
{
lean_object* v___x_1785_; 
v___x_1785_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_ensureSym(v_a_1776_, v_a_1777_, v_a_1778_, v_a_1779_, v_a_1780_, v_a_1781_, v_a_1782_, v_a_1783_);
if (lean_obj_tag(v___x_1785_) == 0)
{
lean_object* v___x_1786_; uint8_t v___x_1787_; 
lean_dec_ref(v___x_1785_);
v___x_1786_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___closed__1));
lean_inc(v_stx_1775_);
v___x_1787_ = l_Lean_Syntax_isOfKind(v_stx_1775_, v___x_1786_);
if (v___x_1787_ == 0)
{
lean_object* v___x_1788_; 
lean_dec(v_stx_1775_);
v___x_1788_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro_spec__0___redArg();
return v___x_1788_;
}
else
{
lean_object* v___x_1789_; 
v___x_1789_ = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(v_a_1777_, v_a_1780_, v_a_1781_, v_a_1782_, v_a_1783_);
if (lean_obj_tag(v___x_1789_) == 0)
{
lean_object* v_a_1790_; lean_object* v_mvarId_1791_; lean_object* v___f_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; uint8_t v___x_1796_; lean_object* v___x_1797_; lean_object* v___y_1798_; lean_object* v___x_1799_; 
v_a_1790_ = lean_ctor_get(v___x_1789_, 0);
lean_inc(v_a_1790_);
lean_dec_ref(v___x_1789_);
v_mvarId_1791_ = lean_ctor_get(v_a_1790_, 1);
lean_inc(v_mvarId_1791_);
v___f_1792_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___lam__0___boxed), 11, 1);
lean_closure_set(v___f_1792_, 0, v_a_1790_);
v___x_1793_ = lean_unsigned_to_nat(1u);
v___x_1794_ = l_Lean_Syntax_getArg(v_stx_1775_, v___x_1793_);
lean_dec(v_stx_1775_);
v___x_1795_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__0___redArg___closed__6));
lean_inc(v___x_1794_);
v___x_1796_ = l_Lean_Syntax_isOfKind(v___x_1794_, v___x_1795_);
v___x_1797_ = lean_box(v___x_1796_);
v___y_1798_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___lam__1___boxed), 12, 3);
lean_closure_set(v___y_1798_, 0, v___x_1797_);
lean_closure_set(v___y_1798_, 1, v___x_1794_);
lean_closure_set(v___y_1798_, 2, v___f_1792_);
v___x_1799_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply_spec__0___redArg(v_mvarId_1791_, v___y_1798_, v_a_1776_, v_a_1777_, v_a_1778_, v_a_1779_, v_a_1780_, v_a_1781_, v_a_1782_, v_a_1783_);
return v___x_1799_;
}
else
{
lean_object* v_a_1800_; lean_object* v___x_1802_; uint8_t v_isShared_1803_; uint8_t v_isSharedCheck_1807_; 
lean_dec(v_stx_1775_);
v_a_1800_ = lean_ctor_get(v___x_1789_, 0);
v_isSharedCheck_1807_ = !lean_is_exclusive(v___x_1789_);
if (v_isSharedCheck_1807_ == 0)
{
v___x_1802_ = v___x_1789_;
v_isShared_1803_ = v_isSharedCheck_1807_;
goto v_resetjp_1801_;
}
else
{
lean_inc(v_a_1800_);
lean_dec(v___x_1789_);
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
}
else
{
lean_dec(v_stx_1775_);
return v___x_1785_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___boxed(lean_object* v_stx_1808_, lean_object* v_a_1809_, lean_object* v_a_1810_, lean_object* v_a_1811_, lean_object* v_a_1812_, lean_object* v_a_1813_, lean_object* v_a_1814_, lean_object* v_a_1815_, lean_object* v_a_1816_, lean_object* v_a_1817_){
_start:
{
lean_object* v_res_1818_; 
v_res_1818_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply(v_stx_1808_, v_a_1809_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_, v_a_1814_, v_a_1815_, v_a_1816_);
lean_dec(v_a_1816_);
lean_dec_ref(v_a_1815_);
lean_dec(v_a_1814_);
lean_dec_ref(v_a_1813_);
lean_dec(v_a_1812_);
lean_dec_ref(v_a_1811_);
lean_dec(v_a_1810_);
lean_dec_ref(v_a_1809_);
return v_res_1818_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply__1(){
_start:
{
lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; 
v___x_1824_ = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
v___x_1825_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___closed__1));
v___x_1826_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply__1___closed__1));
v___x_1827_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___boxed), 10, 0);
v___x_1828_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1824_, v___x_1825_, v___x_1826_, v___x_1827_);
return v___x_1828_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply__1___boxed(lean_object* v_a_1829_){
_start:
{
lean_object* v_res_1830_; 
v_res_1830_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply__1();
return v_res_1830_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize(lean_object* v_stx_1831_, lean_object* v_a_1832_, lean_object* v_a_1833_, lean_object* v_a_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_, lean_object* v_a_1838_, lean_object* v_a_1839_){
_start:
{
lean_object* v___x_1841_; 
v___x_1841_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_ensureSym(v_a_1832_, v_a_1833_, v_a_1834_, v_a_1835_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_);
if (lean_obj_tag(v___x_1841_) == 0)
{
lean_object* v___x_1842_; 
lean_dec_ref(v___x_1841_);
v___x_1842_ = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(v_a_1833_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_);
if (lean_obj_tag(v___x_1842_) == 0)
{
lean_object* v_a_1843_; lean_object* v___y_1845_; lean_object* v___x_1860_; lean_object* v___x_1861_; uint8_t v___x_1862_; 
v_a_1843_ = lean_ctor_get(v___x_1842_, 0);
lean_inc(v_a_1843_);
lean_dec_ref(v___x_1842_);
v___x_1860_ = lean_unsigned_to_nat(1u);
v___x_1861_ = l_Lean_Syntax_getArg(v_stx_1831_, v___x_1860_);
v___x_1862_ = l_Lean_Syntax_isNone(v___x_1861_);
if (v___x_1862_ == 0)
{
lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; 
v___x_1863_ = lean_unsigned_to_nat(0u);
v___x_1864_ = l_Lean_Syntax_getArg(v___x_1861_, v___x_1863_);
lean_dec(v___x_1861_);
v___x_1865_ = l_Lean_Syntax_toNat(v___x_1864_);
lean_dec(v___x_1864_);
v___y_1845_ = v___x_1865_;
goto v___jp_1844_;
}
else
{
lean_dec(v___x_1861_);
v___y_1845_ = v___x_1860_;
goto v___jp_1844_;
}
v___jp_1844_:
{
lean_object* v___x_1846_; lean_object* v___x_1847_; 
v___x_1846_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Goal_internalize___boxed), 12, 2);
lean_closure_set(v___x_1846_, 0, v_a_1843_);
lean_closure_set(v___x_1846_, 1, v___y_1845_);
v___x_1847_ = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(v___x_1846_, v_a_1832_, v_a_1833_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_);
if (lean_obj_tag(v___x_1847_) == 0)
{
lean_object* v_a_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; 
v_a_1848_ = lean_ctor_get(v___x_1847_, 0);
lean_inc(v_a_1848_);
lean_dec_ref(v___x_1847_);
v___x_1849_ = lean_box(0);
v___x_1850_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1850_, 0, v_a_1848_);
lean_ctor_set(v___x_1850_, 1, v___x_1849_);
v___x_1851_ = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(v___x_1850_, v_a_1833_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_);
return v___x_1851_;
}
else
{
lean_object* v_a_1852_; lean_object* v___x_1854_; uint8_t v_isShared_1855_; uint8_t v_isSharedCheck_1859_; 
v_a_1852_ = lean_ctor_get(v___x_1847_, 0);
v_isSharedCheck_1859_ = !lean_is_exclusive(v___x_1847_);
if (v_isSharedCheck_1859_ == 0)
{
v___x_1854_ = v___x_1847_;
v_isShared_1855_ = v_isSharedCheck_1859_;
goto v_resetjp_1853_;
}
else
{
lean_inc(v_a_1852_);
lean_dec(v___x_1847_);
v___x_1854_ = lean_box(0);
v_isShared_1855_ = v_isSharedCheck_1859_;
goto v_resetjp_1853_;
}
v_resetjp_1853_:
{
lean_object* v___x_1857_; 
if (v_isShared_1855_ == 0)
{
v___x_1857_ = v___x_1854_;
goto v_reusejp_1856_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v_a_1852_);
v___x_1857_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1856_;
}
v_reusejp_1856_:
{
return v___x_1857_;
}
}
}
}
}
else
{
lean_object* v_a_1866_; lean_object* v___x_1868_; uint8_t v_isShared_1869_; uint8_t v_isSharedCheck_1873_; 
v_a_1866_ = lean_ctor_get(v___x_1842_, 0);
v_isSharedCheck_1873_ = !lean_is_exclusive(v___x_1842_);
if (v_isSharedCheck_1873_ == 0)
{
v___x_1868_ = v___x_1842_;
v_isShared_1869_ = v_isSharedCheck_1873_;
goto v_resetjp_1867_;
}
else
{
lean_inc(v_a_1866_);
lean_dec(v___x_1842_);
v___x_1868_ = lean_box(0);
v_isShared_1869_ = v_isSharedCheck_1873_;
goto v_resetjp_1867_;
}
v_resetjp_1867_:
{
lean_object* v___x_1871_; 
if (v_isShared_1869_ == 0)
{
v___x_1871_ = v___x_1868_;
goto v_reusejp_1870_;
}
else
{
lean_object* v_reuseFailAlloc_1872_; 
v_reuseFailAlloc_1872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1872_, 0, v_a_1866_);
v___x_1871_ = v_reuseFailAlloc_1872_;
goto v_reusejp_1870_;
}
v_reusejp_1870_:
{
return v___x_1871_;
}
}
}
}
else
{
return v___x_1841_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize___boxed(lean_object* v_stx_1874_, lean_object* v_a_1875_, lean_object* v_a_1876_, lean_object* v_a_1877_, lean_object* v_a_1878_, lean_object* v_a_1879_, lean_object* v_a_1880_, lean_object* v_a_1881_, lean_object* v_a_1882_, lean_object* v_a_1883_){
_start:
{
lean_object* v_res_1884_; 
v_res_1884_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize(v_stx_1874_, v_a_1875_, v_a_1876_, v_a_1877_, v_a_1878_, v_a_1879_, v_a_1880_, v_a_1881_, v_a_1882_);
lean_dec(v_a_1882_);
lean_dec_ref(v_a_1881_);
lean_dec(v_a_1880_);
lean_dec_ref(v_a_1879_);
lean_dec(v_a_1878_);
lean_dec_ref(v_a_1877_);
lean_dec(v_a_1876_);
lean_dec_ref(v_a_1875_);
lean_dec(v_stx_1874_);
return v_res_1884_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize__1(){
_start:
{
lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; 
v___x_1897_ = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
v___x_1898_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize__1___closed__1));
v___x_1899_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize__1___closed__3));
v___x_1900_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize___boxed), 10, 0);
v___x_1901_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1897_, v___x_1898_, v___x_1899_, v___x_1900_);
return v___x_1901_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize__1___boxed(lean_object* v_a_1902_){
_start:
{
lean_object* v_res_1903_; 
v_res_1903_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize__1();
return v_res_1903_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll___redArg(lean_object* v_a_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_, lean_object* v_a_1907_, lean_object* v_a_1908_, lean_object* v_a_1909_, lean_object* v_a_1910_, lean_object* v_a_1911_){
_start:
{
lean_object* v___x_1913_; 
v___x_1913_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_ensureSym(v_a_1904_, v_a_1905_, v_a_1906_, v_a_1907_, v_a_1908_, v_a_1909_, v_a_1910_, v_a_1911_);
if (lean_obj_tag(v___x_1913_) == 0)
{
lean_object* v___x_1914_; 
lean_dec_ref(v___x_1913_);
v___x_1914_ = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(v_a_1905_, v_a_1908_, v_a_1909_, v_a_1910_, v_a_1911_);
if (lean_obj_tag(v___x_1914_) == 0)
{
lean_object* v_a_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; 
v_a_1915_ = lean_ctor_get(v___x_1914_, 0);
lean_inc(v_a_1915_);
lean_dec_ref(v___x_1914_);
v___x_1916_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Goal_internalizeAll___boxed), 11, 1);
lean_closure_set(v___x_1916_, 0, v_a_1915_);
v___x_1917_ = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(v___x_1916_, v_a_1904_, v_a_1905_, v_a_1908_, v_a_1909_, v_a_1910_, v_a_1911_);
if (lean_obj_tag(v___x_1917_) == 0)
{
lean_object* v_a_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; 
v_a_1918_ = lean_ctor_get(v___x_1917_, 0);
lean_inc(v_a_1918_);
lean_dec_ref(v___x_1917_);
v___x_1919_ = lean_box(0);
v___x_1920_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1920_, 0, v_a_1918_);
lean_ctor_set(v___x_1920_, 1, v___x_1919_);
v___x_1921_ = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(v___x_1920_, v_a_1905_, v_a_1908_, v_a_1909_, v_a_1910_, v_a_1911_);
return v___x_1921_;
}
else
{
lean_object* v_a_1922_; lean_object* v___x_1924_; uint8_t v_isShared_1925_; uint8_t v_isSharedCheck_1929_; 
v_a_1922_ = lean_ctor_get(v___x_1917_, 0);
v_isSharedCheck_1929_ = !lean_is_exclusive(v___x_1917_);
if (v_isSharedCheck_1929_ == 0)
{
v___x_1924_ = v___x_1917_;
v_isShared_1925_ = v_isSharedCheck_1929_;
goto v_resetjp_1923_;
}
else
{
lean_inc(v_a_1922_);
lean_dec(v___x_1917_);
v___x_1924_ = lean_box(0);
v_isShared_1925_ = v_isSharedCheck_1929_;
goto v_resetjp_1923_;
}
v_resetjp_1923_:
{
lean_object* v___x_1927_; 
if (v_isShared_1925_ == 0)
{
v___x_1927_ = v___x_1924_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v_a_1922_);
v___x_1927_ = v_reuseFailAlloc_1928_;
goto v_reusejp_1926_;
}
v_reusejp_1926_:
{
return v___x_1927_;
}
}
}
}
else
{
lean_object* v_a_1930_; lean_object* v___x_1932_; uint8_t v_isShared_1933_; uint8_t v_isSharedCheck_1937_; 
v_a_1930_ = lean_ctor_get(v___x_1914_, 0);
v_isSharedCheck_1937_ = !lean_is_exclusive(v___x_1914_);
if (v_isSharedCheck_1937_ == 0)
{
v___x_1932_ = v___x_1914_;
v_isShared_1933_ = v_isSharedCheck_1937_;
goto v_resetjp_1931_;
}
else
{
lean_inc(v_a_1930_);
lean_dec(v___x_1914_);
v___x_1932_ = lean_box(0);
v_isShared_1933_ = v_isSharedCheck_1937_;
goto v_resetjp_1931_;
}
v_resetjp_1931_:
{
lean_object* v___x_1935_; 
if (v_isShared_1933_ == 0)
{
v___x_1935_ = v___x_1932_;
goto v_reusejp_1934_;
}
else
{
lean_object* v_reuseFailAlloc_1936_; 
v_reuseFailAlloc_1936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1936_, 0, v_a_1930_);
v___x_1935_ = v_reuseFailAlloc_1936_;
goto v_reusejp_1934_;
}
v_reusejp_1934_:
{
return v___x_1935_;
}
}
}
}
else
{
return v___x_1913_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll___redArg___boxed(lean_object* v_a_1938_, lean_object* v_a_1939_, lean_object* v_a_1940_, lean_object* v_a_1941_, lean_object* v_a_1942_, lean_object* v_a_1943_, lean_object* v_a_1944_, lean_object* v_a_1945_, lean_object* v_a_1946_){
_start:
{
lean_object* v_res_1947_; 
v_res_1947_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll___redArg(v_a_1938_, v_a_1939_, v_a_1940_, v_a_1941_, v_a_1942_, v_a_1943_, v_a_1944_, v_a_1945_);
lean_dec(v_a_1945_);
lean_dec_ref(v_a_1944_);
lean_dec(v_a_1943_);
lean_dec_ref(v_a_1942_);
lean_dec(v_a_1941_);
lean_dec_ref(v_a_1940_);
lean_dec(v_a_1939_);
lean_dec_ref(v_a_1938_);
return v_res_1947_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll(lean_object* v_x_1948_, lean_object* v_a_1949_, lean_object* v_a_1950_, lean_object* v_a_1951_, lean_object* v_a_1952_, lean_object* v_a_1953_, lean_object* v_a_1954_, lean_object* v_a_1955_, lean_object* v_a_1956_){
_start:
{
lean_object* v___x_1958_; 
v___x_1958_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll___redArg(v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_, v_a_1954_, v_a_1955_, v_a_1956_);
return v___x_1958_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll___boxed(lean_object* v_x_1959_, lean_object* v_a_1960_, lean_object* v_a_1961_, lean_object* v_a_1962_, lean_object* v_a_1963_, lean_object* v_a_1964_, lean_object* v_a_1965_, lean_object* v_a_1966_, lean_object* v_a_1967_, lean_object* v_a_1968_){
_start:
{
lean_object* v_res_1969_; 
v_res_1969_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll(v_x_1959_, v_a_1960_, v_a_1961_, v_a_1962_, v_a_1963_, v_a_1964_, v_a_1965_, v_a_1966_, v_a_1967_);
lean_dec(v_a_1967_);
lean_dec_ref(v_a_1966_);
lean_dec(v_a_1965_);
lean_dec_ref(v_a_1964_);
lean_dec(v_a_1963_);
lean_dec_ref(v_a_1962_);
lean_dec(v_a_1961_);
lean_dec_ref(v_a_1960_);
lean_dec(v_x_1959_);
return v_res_1969_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll__1(){
_start:
{
lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; 
v___x_1982_ = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
v___x_1983_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll__1___closed__1));
v___x_1984_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll__1___closed__3));
v___x_1985_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll___boxed), 10, 0);
v___x_1986_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1982_, v___x_1983_, v___x_1984_, v___x_1985_);
return v___x_1986_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll__1___boxed(lean_object* v_a_1987_){
_start:
{
lean_object* v_res_1988_; 
v_res_1988_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll__1();
return v_res_1988_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___redArg___closed__1(void){
_start:
{
lean_object* v___x_1990_; lean_object* v___x_1991_; 
v___x_1990_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___redArg___closed__0));
v___x_1991_ = l_Lean_stringToMessageData(v___x_1990_);
return v___x_1991_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___redArg___closed__3(void){
_start:
{
lean_object* v___x_1993_; lean_object* v___x_1994_; 
v___x_1993_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___redArg___closed__2));
v___x_1994_ = l_Lean_stringToMessageData(v___x_1993_);
return v___x_1994_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___redArg(lean_object* v_a_1995_, lean_object* v_a_1996_, lean_object* v_a_1997_, lean_object* v_a_1998_, lean_object* v_a_1999_, lean_object* v_a_2000_, lean_object* v_a_2001_, lean_object* v_a_2002_){
_start:
{
lean_object* v___x_2004_; 
v___x_2004_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_ensureSym(v_a_1995_, v_a_1996_, v_a_1997_, v_a_1998_, v_a_1999_, v_a_2000_, v_a_2001_, v_a_2002_);
if (lean_obj_tag(v___x_2004_) == 0)
{
lean_object* v___x_2005_; 
lean_dec_ref(v___x_2004_);
v___x_2005_ = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(v_a_1996_, v_a_1999_, v_a_2000_, v_a_2001_, v_a_2002_);
if (lean_obj_tag(v___x_2005_) == 0)
{
lean_object* v_a_2006_; lean_object* v_toGoalState_2007_; lean_object* v_mvarId_2008_; lean_object* v___x_2010_; uint8_t v_isShared_2011_; uint8_t v_isSharedCheck_2110_; 
v_a_2006_ = lean_ctor_get(v___x_2005_, 0);
lean_inc(v_a_2006_);
lean_dec_ref(v___x_2005_);
v_toGoalState_2007_ = lean_ctor_get(v_a_2006_, 0);
v_mvarId_2008_ = lean_ctor_get(v_a_2006_, 1);
v_isSharedCheck_2110_ = !lean_is_exclusive(v_a_2006_);
if (v_isSharedCheck_2110_ == 0)
{
v___x_2010_ = v_a_2006_;
v_isShared_2011_ = v_isSharedCheck_2110_;
goto v_resetjp_2009_;
}
else
{
lean_inc(v_mvarId_2008_);
lean_inc(v_toGoalState_2007_);
lean_dec(v_a_2006_);
v___x_2010_ = lean_box(0);
v_isShared_2011_ = v_isSharedCheck_2110_;
goto v_resetjp_2009_;
}
v_resetjp_2009_:
{
lean_object* v_mvarId_2013_; lean_object* v___y_2014_; lean_object* v___y_2015_; lean_object* v___y_2016_; lean_object* v___y_2017_; lean_object* v___y_2018_; lean_object* v___y_2019_; lean_object* v___x_2069_; 
lean_inc(v_mvarId_2008_);
v___x_2069_ = l_Lean_MVarId_getType(v_mvarId_2008_, v_a_1999_, v_a_2000_, v_a_2001_, v_a_2002_);
if (lean_obj_tag(v___x_2069_) == 0)
{
lean_object* v_a_2070_; lean_object* v___y_2072_; lean_object* v___y_2073_; lean_object* v___y_2074_; lean_object* v___y_2075_; lean_object* v___y_2076_; lean_object* v___y_2077_; uint8_t v___x_2099_; 
v_a_2070_ = lean_ctor_get(v___x_2069_, 0);
lean_inc_n(v_a_2070_, 2);
lean_dec_ref(v___x_2069_);
v___x_2099_ = l_Lean_Expr_isFalse(v_a_2070_);
if (v___x_2099_ == 0)
{
v___y_2072_ = v_a_1995_;
v___y_2073_ = v_a_1996_;
v___y_2074_ = v_a_1999_;
v___y_2075_ = v_a_2000_;
v___y_2076_ = v_a_2001_;
v___y_2077_ = v_a_2002_;
goto v___jp_2071_;
}
else
{
lean_object* v___x_2100_; lean_object* v___x_2101_; 
lean_dec(v_a_2070_);
lean_del_object(v___x_2010_);
lean_dec(v_mvarId_2008_);
lean_dec_ref(v_toGoalState_2007_);
v___x_2100_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___redArg___closed__3, &l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___redArg___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___redArg___closed__3);
v___x_2101_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_ensureSym_spec__0___redArg(v___x_2100_, v_a_1999_, v_a_2000_, v_a_2001_, v_a_2002_);
return v___x_2101_;
}
v___jp_2071_:
{
lean_object* v___x_2078_; 
v___x_2078_ = l_Lean_Meta_isProp(v_a_2070_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_);
if (lean_obj_tag(v___x_2078_) == 0)
{
lean_object* v_a_2079_; uint8_t v___x_2080_; 
v_a_2079_ = lean_ctor_get(v___x_2078_, 0);
lean_inc(v_a_2079_);
lean_dec_ref(v___x_2078_);
v___x_2080_ = lean_unbox(v_a_2079_);
lean_dec(v_a_2079_);
if (v___x_2080_ == 0)
{
lean_object* v___x_2081_; 
v___x_2081_ = l_Lean_MVarId_exfalso(v_mvarId_2008_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_);
if (lean_obj_tag(v___x_2081_) == 0)
{
lean_object* v_a_2082_; 
v_a_2082_ = lean_ctor_get(v___x_2081_, 0);
lean_inc(v_a_2082_);
lean_dec_ref(v___x_2081_);
v_mvarId_2013_ = v_a_2082_;
v___y_2014_ = v___y_2072_;
v___y_2015_ = v___y_2073_;
v___y_2016_ = v___y_2074_;
v___y_2017_ = v___y_2075_;
v___y_2018_ = v___y_2076_;
v___y_2019_ = v___y_2077_;
goto v___jp_2012_;
}
else
{
lean_object* v_a_2083_; lean_object* v___x_2085_; uint8_t v_isShared_2086_; uint8_t v_isSharedCheck_2090_; 
lean_del_object(v___x_2010_);
lean_dec_ref(v_toGoalState_2007_);
v_a_2083_ = lean_ctor_get(v___x_2081_, 0);
v_isSharedCheck_2090_ = !lean_is_exclusive(v___x_2081_);
if (v_isSharedCheck_2090_ == 0)
{
v___x_2085_ = v___x_2081_;
v_isShared_2086_ = v_isSharedCheck_2090_;
goto v_resetjp_2084_;
}
else
{
lean_inc(v_a_2083_);
lean_dec(v___x_2081_);
v___x_2085_ = lean_box(0);
v_isShared_2086_ = v_isSharedCheck_2090_;
goto v_resetjp_2084_;
}
v_resetjp_2084_:
{
lean_object* v___x_2088_; 
if (v_isShared_2086_ == 0)
{
v___x_2088_ = v___x_2085_;
goto v_reusejp_2087_;
}
else
{
lean_object* v_reuseFailAlloc_2089_; 
v_reuseFailAlloc_2089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2089_, 0, v_a_2083_);
v___x_2088_ = v_reuseFailAlloc_2089_;
goto v_reusejp_2087_;
}
v_reusejp_2087_:
{
return v___x_2088_;
}
}
}
}
else
{
v_mvarId_2013_ = v_mvarId_2008_;
v___y_2014_ = v___y_2072_;
v___y_2015_ = v___y_2073_;
v___y_2016_ = v___y_2074_;
v___y_2017_ = v___y_2075_;
v___y_2018_ = v___y_2076_;
v___y_2019_ = v___y_2077_;
goto v___jp_2012_;
}
}
else
{
lean_object* v_a_2091_; lean_object* v___x_2093_; uint8_t v_isShared_2094_; uint8_t v_isSharedCheck_2098_; 
lean_del_object(v___x_2010_);
lean_dec(v_mvarId_2008_);
lean_dec_ref(v_toGoalState_2007_);
v_a_2091_ = lean_ctor_get(v___x_2078_, 0);
v_isSharedCheck_2098_ = !lean_is_exclusive(v___x_2078_);
if (v_isSharedCheck_2098_ == 0)
{
v___x_2093_ = v___x_2078_;
v_isShared_2094_ = v_isSharedCheck_2098_;
goto v_resetjp_2092_;
}
else
{
lean_inc(v_a_2091_);
lean_dec(v___x_2078_);
v___x_2093_ = lean_box(0);
v_isShared_2094_ = v_isSharedCheck_2098_;
goto v_resetjp_2092_;
}
v_resetjp_2092_:
{
lean_object* v___x_2096_; 
if (v_isShared_2094_ == 0)
{
v___x_2096_ = v___x_2093_;
goto v_reusejp_2095_;
}
else
{
lean_object* v_reuseFailAlloc_2097_; 
v_reuseFailAlloc_2097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2097_, 0, v_a_2091_);
v___x_2096_ = v_reuseFailAlloc_2097_;
goto v_reusejp_2095_;
}
v_reusejp_2095_:
{
return v___x_2096_;
}
}
}
}
}
else
{
lean_object* v_a_2102_; lean_object* v___x_2104_; uint8_t v_isShared_2105_; uint8_t v_isSharedCheck_2109_; 
lean_del_object(v___x_2010_);
lean_dec(v_mvarId_2008_);
lean_dec_ref(v_toGoalState_2007_);
v_a_2102_ = lean_ctor_get(v___x_2069_, 0);
v_isSharedCheck_2109_ = !lean_is_exclusive(v___x_2069_);
if (v_isSharedCheck_2109_ == 0)
{
v___x_2104_ = v___x_2069_;
v_isShared_2105_ = v_isSharedCheck_2109_;
goto v_resetjp_2103_;
}
else
{
lean_inc(v_a_2102_);
lean_dec(v___x_2069_);
v___x_2104_ = lean_box(0);
v_isShared_2105_ = v_isSharedCheck_2109_;
goto v_resetjp_2103_;
}
v_resetjp_2103_:
{
lean_object* v___x_2107_; 
if (v_isShared_2105_ == 0)
{
v___x_2107_ = v___x_2104_;
goto v_reusejp_2106_;
}
else
{
lean_object* v_reuseFailAlloc_2108_; 
v_reuseFailAlloc_2108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2108_, 0, v_a_2102_);
v___x_2107_ = v_reuseFailAlloc_2108_;
goto v_reusejp_2106_;
}
v_reusejp_2106_:
{
return v___x_2107_;
}
}
}
v___jp_2012_:
{
lean_object* v___x_2020_; 
v___x_2020_ = l_Lean_MVarId_byContra_x3f(v_mvarId_2013_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_);
if (lean_obj_tag(v___x_2020_) == 0)
{
lean_object* v_a_2021_; 
v_a_2021_ = lean_ctor_get(v___x_2020_, 0);
lean_inc(v_a_2021_);
lean_dec_ref(v___x_2020_);
if (lean_obj_tag(v_a_2021_) == 1)
{
lean_object* v_val_2022_; uint8_t v___x_2023_; lean_object* v___x_2024_; 
v_val_2022_ = lean_ctor_get(v_a_2021_, 0);
lean_inc(v_val_2022_);
lean_dec_ref(v_a_2021_);
v___x_2023_ = 0;
v___x_2024_ = l_Lean_Meta_intro1Core(v_val_2022_, v___x_2023_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_);
if (lean_obj_tag(v___x_2024_) == 0)
{
lean_object* v_a_2025_; lean_object* v_snd_2026_; lean_object* v___x_2028_; uint8_t v_isShared_2029_; uint8_t v_isSharedCheck_2049_; 
v_a_2025_ = lean_ctor_get(v___x_2024_, 0);
lean_inc(v_a_2025_);
lean_dec_ref(v___x_2024_);
v_snd_2026_ = lean_ctor_get(v_a_2025_, 1);
v_isSharedCheck_2049_ = !lean_is_exclusive(v_a_2025_);
if (v_isSharedCheck_2049_ == 0)
{
lean_object* v_unused_2050_; 
v_unused_2050_ = lean_ctor_get(v_a_2025_, 0);
lean_dec(v_unused_2050_);
v___x_2028_ = v_a_2025_;
v_isShared_2029_ = v_isSharedCheck_2049_;
goto v_resetjp_2027_;
}
else
{
lean_inc(v_snd_2026_);
lean_dec(v_a_2025_);
v___x_2028_ = lean_box(0);
v_isShared_2029_ = v_isSharedCheck_2049_;
goto v_resetjp_2027_;
}
v_resetjp_2027_:
{
lean_object* v___x_2031_; 
if (v_isShared_2011_ == 0)
{
lean_ctor_set(v___x_2010_, 1, v_snd_2026_);
v___x_2031_ = v___x_2010_;
goto v_reusejp_2030_;
}
else
{
lean_object* v_reuseFailAlloc_2048_; 
v_reuseFailAlloc_2048_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2048_, 0, v_toGoalState_2007_);
lean_ctor_set(v_reuseFailAlloc_2048_, 1, v_snd_2026_);
v___x_2031_ = v_reuseFailAlloc_2048_;
goto v_reusejp_2030_;
}
v_reusejp_2030_:
{
lean_object* v___x_2032_; lean_object* v___x_2033_; 
v___x_2032_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Goal_internalizeAll___boxed), 11, 1);
lean_closure_set(v___x_2032_, 0, v___x_2031_);
v___x_2033_ = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(v___x_2032_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_);
if (lean_obj_tag(v___x_2033_) == 0)
{
lean_object* v_a_2034_; lean_object* v___x_2035_; lean_object* v___x_2037_; 
v_a_2034_ = lean_ctor_get(v___x_2033_, 0);
lean_inc(v_a_2034_);
lean_dec_ref(v___x_2033_);
v___x_2035_ = lean_box(0);
if (v_isShared_2029_ == 0)
{
lean_ctor_set_tag(v___x_2028_, 1);
lean_ctor_set(v___x_2028_, 1, v___x_2035_);
lean_ctor_set(v___x_2028_, 0, v_a_2034_);
v___x_2037_ = v___x_2028_;
goto v_reusejp_2036_;
}
else
{
lean_object* v_reuseFailAlloc_2039_; 
v_reuseFailAlloc_2039_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2039_, 0, v_a_2034_);
lean_ctor_set(v_reuseFailAlloc_2039_, 1, v___x_2035_);
v___x_2037_ = v_reuseFailAlloc_2039_;
goto v_reusejp_2036_;
}
v_reusejp_2036_:
{
lean_object* v___x_2038_; 
v___x_2038_ = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(v___x_2037_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_);
return v___x_2038_;
}
}
else
{
lean_object* v_a_2040_; lean_object* v___x_2042_; uint8_t v_isShared_2043_; uint8_t v_isSharedCheck_2047_; 
lean_del_object(v___x_2028_);
v_a_2040_ = lean_ctor_get(v___x_2033_, 0);
v_isSharedCheck_2047_ = !lean_is_exclusive(v___x_2033_);
if (v_isSharedCheck_2047_ == 0)
{
v___x_2042_ = v___x_2033_;
v_isShared_2043_ = v_isSharedCheck_2047_;
goto v_resetjp_2041_;
}
else
{
lean_inc(v_a_2040_);
lean_dec(v___x_2033_);
v___x_2042_ = lean_box(0);
v_isShared_2043_ = v_isSharedCheck_2047_;
goto v_resetjp_2041_;
}
v_resetjp_2041_:
{
lean_object* v___x_2045_; 
if (v_isShared_2043_ == 0)
{
v___x_2045_ = v___x_2042_;
goto v_reusejp_2044_;
}
else
{
lean_object* v_reuseFailAlloc_2046_; 
v_reuseFailAlloc_2046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2046_, 0, v_a_2040_);
v___x_2045_ = v_reuseFailAlloc_2046_;
goto v_reusejp_2044_;
}
v_reusejp_2044_:
{
return v___x_2045_;
}
}
}
}
}
}
else
{
lean_object* v_a_2051_; lean_object* v___x_2053_; uint8_t v_isShared_2054_; uint8_t v_isSharedCheck_2058_; 
lean_del_object(v___x_2010_);
lean_dec_ref(v_toGoalState_2007_);
v_a_2051_ = lean_ctor_get(v___x_2024_, 0);
v_isSharedCheck_2058_ = !lean_is_exclusive(v___x_2024_);
if (v_isSharedCheck_2058_ == 0)
{
v___x_2053_ = v___x_2024_;
v_isShared_2054_ = v_isSharedCheck_2058_;
goto v_resetjp_2052_;
}
else
{
lean_inc(v_a_2051_);
lean_dec(v___x_2024_);
v___x_2053_ = lean_box(0);
v_isShared_2054_ = v_isSharedCheck_2058_;
goto v_resetjp_2052_;
}
v_resetjp_2052_:
{
lean_object* v___x_2056_; 
if (v_isShared_2054_ == 0)
{
v___x_2056_ = v___x_2053_;
goto v_reusejp_2055_;
}
else
{
lean_object* v_reuseFailAlloc_2057_; 
v_reuseFailAlloc_2057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2057_, 0, v_a_2051_);
v___x_2056_ = v_reuseFailAlloc_2057_;
goto v_reusejp_2055_;
}
v_reusejp_2055_:
{
return v___x_2056_;
}
}
}
}
else
{
lean_object* v___x_2059_; lean_object* v___x_2060_; 
lean_dec(v_a_2021_);
lean_del_object(v___x_2010_);
lean_dec_ref(v_toGoalState_2007_);
v___x_2059_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___redArg___closed__1, &l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___redArg___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___redArg___closed__1);
v___x_2060_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_ensureSym_spec__0___redArg(v___x_2059_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_);
return v___x_2060_;
}
}
else
{
lean_object* v_a_2061_; lean_object* v___x_2063_; uint8_t v_isShared_2064_; uint8_t v_isSharedCheck_2068_; 
lean_del_object(v___x_2010_);
lean_dec_ref(v_toGoalState_2007_);
v_a_2061_ = lean_ctor_get(v___x_2020_, 0);
v_isSharedCheck_2068_ = !lean_is_exclusive(v___x_2020_);
if (v_isSharedCheck_2068_ == 0)
{
v___x_2063_ = v___x_2020_;
v_isShared_2064_ = v_isSharedCheck_2068_;
goto v_resetjp_2062_;
}
else
{
lean_inc(v_a_2061_);
lean_dec(v___x_2020_);
v___x_2063_ = lean_box(0);
v_isShared_2064_ = v_isSharedCheck_2068_;
goto v_resetjp_2062_;
}
v_resetjp_2062_:
{
lean_object* v___x_2066_; 
if (v_isShared_2064_ == 0)
{
v___x_2066_ = v___x_2063_;
goto v_reusejp_2065_;
}
else
{
lean_object* v_reuseFailAlloc_2067_; 
v_reuseFailAlloc_2067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2067_, 0, v_a_2061_);
v___x_2066_ = v_reuseFailAlloc_2067_;
goto v_reusejp_2065_;
}
v_reusejp_2065_:
{
return v___x_2066_;
}
}
}
}
}
}
else
{
lean_object* v_a_2111_; lean_object* v___x_2113_; uint8_t v_isShared_2114_; uint8_t v_isSharedCheck_2118_; 
v_a_2111_ = lean_ctor_get(v___x_2005_, 0);
v_isSharedCheck_2118_ = !lean_is_exclusive(v___x_2005_);
if (v_isSharedCheck_2118_ == 0)
{
v___x_2113_ = v___x_2005_;
v_isShared_2114_ = v_isSharedCheck_2118_;
goto v_resetjp_2112_;
}
else
{
lean_inc(v_a_2111_);
lean_dec(v___x_2005_);
v___x_2113_ = lean_box(0);
v_isShared_2114_ = v_isSharedCheck_2118_;
goto v_resetjp_2112_;
}
v_resetjp_2112_:
{
lean_object* v___x_2116_; 
if (v_isShared_2114_ == 0)
{
v___x_2116_ = v___x_2113_;
goto v_reusejp_2115_;
}
else
{
lean_object* v_reuseFailAlloc_2117_; 
v_reuseFailAlloc_2117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2117_, 0, v_a_2111_);
v___x_2116_ = v_reuseFailAlloc_2117_;
goto v_reusejp_2115_;
}
v_reusejp_2115_:
{
return v___x_2116_;
}
}
}
}
else
{
return v___x_2004_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___redArg___boxed(lean_object* v_a_2119_, lean_object* v_a_2120_, lean_object* v_a_2121_, lean_object* v_a_2122_, lean_object* v_a_2123_, lean_object* v_a_2124_, lean_object* v_a_2125_, lean_object* v_a_2126_, lean_object* v_a_2127_){
_start:
{
lean_object* v_res_2128_; 
v_res_2128_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___redArg(v_a_2119_, v_a_2120_, v_a_2121_, v_a_2122_, v_a_2123_, v_a_2124_, v_a_2125_, v_a_2126_);
lean_dec(v_a_2126_);
lean_dec_ref(v_a_2125_);
lean_dec(v_a_2124_);
lean_dec_ref(v_a_2123_);
lean_dec(v_a_2122_);
lean_dec_ref(v_a_2121_);
lean_dec(v_a_2120_);
lean_dec_ref(v_a_2119_);
return v_res_2128_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra(lean_object* v_x_2129_, lean_object* v_a_2130_, lean_object* v_a_2131_, lean_object* v_a_2132_, lean_object* v_a_2133_, lean_object* v_a_2134_, lean_object* v_a_2135_, lean_object* v_a_2136_, lean_object* v_a_2137_){
_start:
{
lean_object* v___x_2139_; 
v___x_2139_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___redArg(v_a_2130_, v_a_2131_, v_a_2132_, v_a_2133_, v_a_2134_, v_a_2135_, v_a_2136_, v_a_2137_);
return v___x_2139_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___boxed(lean_object* v_x_2140_, lean_object* v_a_2141_, lean_object* v_a_2142_, lean_object* v_a_2143_, lean_object* v_a_2144_, lean_object* v_a_2145_, lean_object* v_a_2146_, lean_object* v_a_2147_, lean_object* v_a_2148_, lean_object* v_a_2149_){
_start:
{
lean_object* v_res_2150_; 
v_res_2150_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra(v_x_2140_, v_a_2141_, v_a_2142_, v_a_2143_, v_a_2144_, v_a_2145_, v_a_2146_, v_a_2147_, v_a_2148_);
lean_dec(v_a_2148_);
lean_dec_ref(v_a_2147_);
lean_dec(v_a_2146_);
lean_dec_ref(v_a_2145_);
lean_dec(v_a_2144_);
lean_dec_ref(v_a_2143_);
lean_dec(v_a_2142_);
lean_dec_ref(v_a_2141_);
lean_dec(v_x_2140_);
return v_res_2150_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra__1(){
_start:
{
lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; 
v___x_2163_ = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
v___x_2164_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra__1___closed__1));
v___x_2165_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra__1___closed__3));
v___x_2166_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___boxed), 10, 0);
v___x_2167_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2163_, v___x_2164_, v___x_2165_, v___x_2166_);
return v___x_2167_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra__1___boxed(lean_object* v_a_2168_){
_start:
{
lean_object* v_res_2169_; 
v_res_2169_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra__1();
return v_res_2169_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_trivialSimproc___redArg(){
_start:
{
lean_object* v___x_2173_; lean_object* v___x_2174_; 
v___x_2173_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_trivialSimproc___redArg___closed__0));
v___x_2174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2174_, 0, v___x_2173_);
return v___x_2174_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_trivialSimproc___redArg___boxed(lean_object* v_a_2175_){
_start:
{
lean_object* v_res_2176_; 
v_res_2176_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_trivialSimproc___redArg();
return v_res_2176_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_trivialSimproc(lean_object* v_x_2177_, lean_object* v_a_2178_, lean_object* v_a_2179_, lean_object* v_a_2180_, lean_object* v_a_2181_, lean_object* v_a_2182_, lean_object* v_a_2183_, lean_object* v_a_2184_, lean_object* v_a_2185_, lean_object* v_a_2186_){
_start:
{
lean_object* v___x_2188_; 
v___x_2188_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_trivialSimproc___redArg();
return v___x_2188_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_trivialSimproc___boxed(lean_object* v_x_2189_, lean_object* v_a_2190_, lean_object* v_a_2191_, lean_object* v_a_2192_, lean_object* v_a_2193_, lean_object* v_a_2194_, lean_object* v_a_2195_, lean_object* v_a_2196_, lean_object* v_a_2197_, lean_object* v_a_2198_, lean_object* v_a_2199_){
_start:
{
lean_object* v_res_2200_; 
v_res_2200_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_trivialSimproc(v_x_2189_, v_a_2190_, v_a_2191_, v_a_2192_, v_a_2193_, v_a_2194_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_);
lean_dec(v_a_2198_);
lean_dec_ref(v_a_2197_);
lean_dec(v_a_2196_);
lean_dec_ref(v_a_2195_);
lean_dec(v_a_2194_);
lean_dec_ref(v_a_2193_);
lean_dec(v_a_2192_);
lean_dec_ref(v_a_2191_);
lean_dec(v_a_2190_);
lean_dec_ref(v_x_2189_);
return v_res_2200_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabOptSimproc(lean_object* v_stx_x3f_2201_, lean_object* v_a_2202_, lean_object* v_a_2203_, lean_object* v_a_2204_, lean_object* v_a_2205_, lean_object* v_a_2206_, lean_object* v_a_2207_, lean_object* v_a_2208_, lean_object* v_a_2209_){
_start:
{
if (lean_obj_tag(v_stx_x3f_2201_) == 1)
{
lean_object* v_val_2211_; lean_object* v___x_2212_; 
v_val_2211_ = lean_ctor_get(v_stx_x3f_2201_, 0);
lean_inc(v_val_2211_);
lean_dec_ref(v_stx_x3f_2201_);
v___x_2212_ = l_Lean_Elab_Tactic_Grind_elabSymSimproc(v_val_2211_, v_a_2202_, v_a_2203_, v_a_2204_, v_a_2205_, v_a_2206_, v_a_2207_, v_a_2208_, v_a_2209_);
return v___x_2212_;
}
else
{
lean_object* v___x_2213_; lean_object* v___x_2214_; 
lean_dec(v_stx_x3f_2201_);
v___x_2213_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_trivialSimproc___boxed), 11, 0);
v___x_2214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2214_, 0, v___x_2213_);
return v___x_2214_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabOptSimproc___boxed(lean_object* v_stx_x3f_2215_, lean_object* v_a_2216_, lean_object* v_a_2217_, lean_object* v_a_2218_, lean_object* v_a_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_, lean_object* v_a_2222_, lean_object* v_a_2223_, lean_object* v_a_2224_){
_start:
{
lean_object* v_res_2225_; 
v_res_2225_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabOptSimproc(v_stx_x3f_2215_, v_a_2216_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_, v_a_2222_, v_a_2223_);
lean_dec(v_a_2223_);
lean_dec_ref(v_a_2222_);
lean_dec(v_a_2221_);
lean_dec_ref(v_a_2220_);
lean_dec(v_a_2219_);
lean_dec_ref(v_a_2218_);
lean_dec(v_a_2217_);
lean_dec_ref(v_a_2216_);
return v_res_2225_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__0___redArg(lean_object* v___x_2226_, lean_object* v_as_2227_, size_t v_sz_2228_, size_t v_i_2229_, lean_object* v_b_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_){
_start:
{
lean_object* v_a_2237_; uint8_t v___x_2241_; 
v___x_2241_ = lean_usize_dec_lt(v_i_2229_, v_sz_2228_);
if (v___x_2241_ == 0)
{
lean_object* v___x_2242_; 
v___x_2242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2242_, 0, v_b_2230_);
return v___x_2242_;
}
else
{
lean_object* v_fst_2243_; lean_object* v_snd_2244_; lean_object* v___x_2246_; uint8_t v_isShared_2247_; uint8_t v_isSharedCheck_2302_; 
v_fst_2243_ = lean_ctor_get(v_b_2230_, 0);
v_snd_2244_ = lean_ctor_get(v_b_2230_, 1);
v_isSharedCheck_2302_ = !lean_is_exclusive(v_b_2230_);
if (v_isSharedCheck_2302_ == 0)
{
v___x_2246_ = v_b_2230_;
v_isShared_2247_ = v_isSharedCheck_2302_;
goto v_resetjp_2245_;
}
else
{
lean_inc(v_snd_2244_);
lean_inc(v_fst_2243_);
lean_dec(v_b_2230_);
v___x_2246_ = lean_box(0);
v_isShared_2247_ = v_isSharedCheck_2302_;
goto v_resetjp_2245_;
}
v_resetjp_2245_:
{
lean_object* v_a_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; 
v_a_2248_ = lean_array_uget_borrowed(v_as_2227_, v_i_2229_);
v___x_2249_ = l_Lean_TSyntax_getId(v_a_2248_);
v___x_2250_ = l_Lean_LocalContext_findFromUserName_x3f(v___x_2226_, v___x_2249_);
lean_dec(v___x_2249_);
if (lean_obj_tag(v___x_2250_) == 1)
{
lean_object* v_val_2251_; lean_object* v___x_2253_; uint8_t v_isShared_2254_; uint8_t v_isSharedCheck_2275_; 
v_val_2251_ = lean_ctor_get(v___x_2250_, 0);
v_isSharedCheck_2275_ = !lean_is_exclusive(v___x_2250_);
if (v_isSharedCheck_2275_ == 0)
{
v___x_2253_ = v___x_2250_;
v_isShared_2254_ = v_isSharedCheck_2275_;
goto v_resetjp_2252_;
}
else
{
lean_inc(v_val_2251_);
lean_dec(v___x_2250_);
v___x_2253_ = lean_box(0);
v_isShared_2254_ = v_isSharedCheck_2275_;
goto v_resetjp_2252_;
}
v_resetjp_2252_:
{
lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; 
v___x_2255_ = l_Lean_LocalDecl_fvarId(v_val_2251_);
v___x_2256_ = l_Lean_LocalDecl_toExpr(v_val_2251_);
v___x_2257_ = l_Lean_Meta_Sym_Simp_mkTheoremFromExpr(v___x_2256_, v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_);
if (lean_obj_tag(v___x_2257_) == 0)
{
lean_object* v_a_2258_; lean_object* v___x_2260_; 
v_a_2258_ = lean_ctor_get(v___x_2257_, 0);
lean_inc(v_a_2258_);
lean_dec_ref(v___x_2257_);
if (v_isShared_2254_ == 0)
{
lean_ctor_set(v___x_2253_, 0, v___x_2255_);
v___x_2260_ = v___x_2253_;
goto v_reusejp_2259_;
}
else
{
lean_object* v_reuseFailAlloc_2266_; 
v_reuseFailAlloc_2266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2266_, 0, v___x_2255_);
v___x_2260_ = v_reuseFailAlloc_2266_;
goto v_reusejp_2259_;
}
v_reusejp_2259_:
{
lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2264_; 
v___x_2261_ = lean_array_push(v_fst_2243_, v___x_2260_);
v___x_2262_ = lean_array_push(v_snd_2244_, v_a_2258_);
if (v_isShared_2247_ == 0)
{
lean_ctor_set(v___x_2246_, 1, v___x_2262_);
lean_ctor_set(v___x_2246_, 0, v___x_2261_);
v___x_2264_ = v___x_2246_;
goto v_reusejp_2263_;
}
else
{
lean_object* v_reuseFailAlloc_2265_; 
v_reuseFailAlloc_2265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2265_, 0, v___x_2261_);
lean_ctor_set(v_reuseFailAlloc_2265_, 1, v___x_2262_);
v___x_2264_ = v_reuseFailAlloc_2265_;
goto v_reusejp_2263_;
}
v_reusejp_2263_:
{
v_a_2237_ = v___x_2264_;
goto v___jp_2236_;
}
}
}
else
{
lean_object* v_a_2267_; lean_object* v___x_2269_; uint8_t v_isShared_2270_; uint8_t v_isSharedCheck_2274_; 
lean_dec(v___x_2255_);
lean_del_object(v___x_2253_);
lean_del_object(v___x_2246_);
lean_dec(v_snd_2244_);
lean_dec(v_fst_2243_);
v_a_2267_ = lean_ctor_get(v___x_2257_, 0);
v_isSharedCheck_2274_ = !lean_is_exclusive(v___x_2257_);
if (v_isSharedCheck_2274_ == 0)
{
v___x_2269_ = v___x_2257_;
v_isShared_2270_ = v_isSharedCheck_2274_;
goto v_resetjp_2268_;
}
else
{
lean_inc(v_a_2267_);
lean_dec(v___x_2257_);
v___x_2269_ = lean_box(0);
v_isShared_2270_ = v_isSharedCheck_2274_;
goto v_resetjp_2268_;
}
v_resetjp_2268_:
{
lean_object* v___x_2272_; 
if (v_isShared_2270_ == 0)
{
v___x_2272_ = v___x_2269_;
goto v_reusejp_2271_;
}
else
{
lean_object* v_reuseFailAlloc_2273_; 
v_reuseFailAlloc_2273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2273_, 0, v_a_2267_);
v___x_2272_ = v_reuseFailAlloc_2273_;
goto v_reusejp_2271_;
}
v_reusejp_2271_:
{
return v___x_2272_;
}
}
}
}
}
else
{
lean_object* v___x_2276_; 
lean_dec(v___x_2250_);
lean_inc(v_a_2248_);
v___x_2276_ = l_Lean_realizeGlobalConstNoOverload(v_a_2248_, v___y_2233_, v___y_2234_);
if (lean_obj_tag(v___x_2276_) == 0)
{
lean_object* v_a_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; 
v_a_2277_ = lean_ctor_get(v___x_2276_, 0);
lean_inc_n(v_a_2277_, 2);
lean_dec_ref(v___x_2276_);
v___x_2278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2278_, 0, v_a_2277_);
v___x_2279_ = l_Lean_Meta_Sym_Simp_mkTheoremFromDecl(v_a_2277_, v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_);
if (lean_obj_tag(v___x_2279_) == 0)
{
lean_object* v_a_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2284_; 
v_a_2280_ = lean_ctor_get(v___x_2279_, 0);
lean_inc(v_a_2280_);
lean_dec_ref(v___x_2279_);
v___x_2281_ = lean_array_push(v_fst_2243_, v___x_2278_);
v___x_2282_ = lean_array_push(v_snd_2244_, v_a_2280_);
if (v_isShared_2247_ == 0)
{
lean_ctor_set(v___x_2246_, 1, v___x_2282_);
lean_ctor_set(v___x_2246_, 0, v___x_2281_);
v___x_2284_ = v___x_2246_;
goto v_reusejp_2283_;
}
else
{
lean_object* v_reuseFailAlloc_2285_; 
v_reuseFailAlloc_2285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2285_, 0, v___x_2281_);
lean_ctor_set(v_reuseFailAlloc_2285_, 1, v___x_2282_);
v___x_2284_ = v_reuseFailAlloc_2285_;
goto v_reusejp_2283_;
}
v_reusejp_2283_:
{
v_a_2237_ = v___x_2284_;
goto v___jp_2236_;
}
}
else
{
lean_object* v_a_2286_; lean_object* v___x_2288_; uint8_t v_isShared_2289_; uint8_t v_isSharedCheck_2293_; 
lean_dec_ref(v___x_2278_);
lean_del_object(v___x_2246_);
lean_dec(v_snd_2244_);
lean_dec(v_fst_2243_);
v_a_2286_ = lean_ctor_get(v___x_2279_, 0);
v_isSharedCheck_2293_ = !lean_is_exclusive(v___x_2279_);
if (v_isSharedCheck_2293_ == 0)
{
v___x_2288_ = v___x_2279_;
v_isShared_2289_ = v_isSharedCheck_2293_;
goto v_resetjp_2287_;
}
else
{
lean_inc(v_a_2286_);
lean_dec(v___x_2279_);
v___x_2288_ = lean_box(0);
v_isShared_2289_ = v_isSharedCheck_2293_;
goto v_resetjp_2287_;
}
v_resetjp_2287_:
{
lean_object* v___x_2291_; 
if (v_isShared_2289_ == 0)
{
v___x_2291_ = v___x_2288_;
goto v_reusejp_2290_;
}
else
{
lean_object* v_reuseFailAlloc_2292_; 
v_reuseFailAlloc_2292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2292_, 0, v_a_2286_);
v___x_2291_ = v_reuseFailAlloc_2292_;
goto v_reusejp_2290_;
}
v_reusejp_2290_:
{
return v___x_2291_;
}
}
}
}
else
{
lean_object* v_a_2294_; lean_object* v___x_2296_; uint8_t v_isShared_2297_; uint8_t v_isSharedCheck_2301_; 
lean_del_object(v___x_2246_);
lean_dec(v_snd_2244_);
lean_dec(v_fst_2243_);
v_a_2294_ = lean_ctor_get(v___x_2276_, 0);
v_isSharedCheck_2301_ = !lean_is_exclusive(v___x_2276_);
if (v_isSharedCheck_2301_ == 0)
{
v___x_2296_ = v___x_2276_;
v_isShared_2297_ = v_isSharedCheck_2301_;
goto v_resetjp_2295_;
}
else
{
lean_inc(v_a_2294_);
lean_dec(v___x_2276_);
v___x_2296_ = lean_box(0);
v_isShared_2297_ = v_isSharedCheck_2301_;
goto v_resetjp_2295_;
}
v_resetjp_2295_:
{
lean_object* v___x_2299_; 
if (v_isShared_2297_ == 0)
{
v___x_2299_ = v___x_2296_;
goto v_reusejp_2298_;
}
else
{
lean_object* v_reuseFailAlloc_2300_; 
v_reuseFailAlloc_2300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2300_, 0, v_a_2294_);
v___x_2299_ = v_reuseFailAlloc_2300_;
goto v_reusejp_2298_;
}
v_reusejp_2298_:
{
return v___x_2299_;
}
}
}
}
}
}
v___jp_2236_:
{
size_t v___x_2238_; size_t v___x_2239_; 
v___x_2238_ = ((size_t)1ULL);
v___x_2239_ = lean_usize_add(v_i_2229_, v___x_2238_);
v_i_2229_ = v___x_2239_;
v_b_2230_ = v_a_2237_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__0___redArg___boxed(lean_object* v___x_2303_, lean_object* v_as_2304_, lean_object* v_sz_2305_, lean_object* v_i_2306_, lean_object* v_b_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_){
_start:
{
size_t v_sz_boxed_2313_; size_t v_i_boxed_2314_; lean_object* v_res_2315_; 
v_sz_boxed_2313_ = lean_unbox_usize(v_sz_2305_);
lean_dec(v_sz_2305_);
v_i_boxed_2314_ = lean_unbox_usize(v_i_2306_);
lean_dec(v_i_2306_);
v_res_2315_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__0___redArg(v___x_2303_, v_as_2304_, v_sz_boxed_2313_, v_i_boxed_2314_, v_b_2307_, v___y_2308_, v___y_2309_, v___y_2310_, v___y_2311_);
lean_dec(v___y_2311_);
lean_dec_ref(v___y_2310_);
lean_dec(v___y_2309_);
lean_dec_ref(v___y_2308_);
lean_dec_ref(v_as_2304_);
lean_dec_ref(v___x_2303_);
return v_res_2315_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems(lean_object* v_ids_x3f_2320_, lean_object* v_a_2321_, lean_object* v_a_2322_, lean_object* v_a_2323_, lean_object* v_a_2324_, lean_object* v_a_2325_, lean_object* v_a_2326_, lean_object* v_a_2327_, lean_object* v_a_2328_){
_start:
{
if (lean_obj_tag(v_ids_x3f_2320_) == 1)
{
lean_object* v_val_2330_; lean_object* v_lctx_2331_; lean_object* v___x_2332_; size_t v_sz_2333_; size_t v___x_2334_; lean_object* v___x_2335_; 
v_val_2330_ = lean_ctor_get(v_ids_x3f_2320_, 0);
v_lctx_2331_ = lean_ctor_get(v_a_2325_, 2);
v___x_2332_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems___closed__1));
v_sz_2333_ = lean_array_size(v_val_2330_);
v___x_2334_ = ((size_t)0ULL);
v___x_2335_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__0___redArg(v_lctx_2331_, v_val_2330_, v_sz_2333_, v___x_2334_, v___x_2332_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_);
if (lean_obj_tag(v___x_2335_) == 0)
{
lean_object* v_a_2336_; lean_object* v___x_2338_; uint8_t v_isShared_2339_; uint8_t v_isSharedCheck_2352_; 
v_a_2336_ = lean_ctor_get(v___x_2335_, 0);
v_isSharedCheck_2352_ = !lean_is_exclusive(v___x_2335_);
if (v_isSharedCheck_2352_ == 0)
{
v___x_2338_ = v___x_2335_;
v_isShared_2339_ = v_isSharedCheck_2352_;
goto v_resetjp_2337_;
}
else
{
lean_inc(v_a_2336_);
lean_dec(v___x_2335_);
v___x_2338_ = lean_box(0);
v_isShared_2339_ = v_isSharedCheck_2352_;
goto v_resetjp_2337_;
}
v_resetjp_2337_:
{
lean_object* v_fst_2340_; lean_object* v_snd_2341_; lean_object* v___x_2343_; uint8_t v_isShared_2344_; uint8_t v_isSharedCheck_2351_; 
v_fst_2340_ = lean_ctor_get(v_a_2336_, 0);
v_snd_2341_ = lean_ctor_get(v_a_2336_, 1);
v_isSharedCheck_2351_ = !lean_is_exclusive(v_a_2336_);
if (v_isSharedCheck_2351_ == 0)
{
v___x_2343_ = v_a_2336_;
v_isShared_2344_ = v_isSharedCheck_2351_;
goto v_resetjp_2342_;
}
else
{
lean_inc(v_snd_2341_);
lean_inc(v_fst_2340_);
lean_dec(v_a_2336_);
v___x_2343_ = lean_box(0);
v_isShared_2344_ = v_isSharedCheck_2351_;
goto v_resetjp_2342_;
}
v_resetjp_2342_:
{
lean_object* v___x_2346_; 
if (v_isShared_2344_ == 0)
{
v___x_2346_ = v___x_2343_;
goto v_reusejp_2345_;
}
else
{
lean_object* v_reuseFailAlloc_2350_; 
v_reuseFailAlloc_2350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2350_, 0, v_fst_2340_);
lean_ctor_set(v_reuseFailAlloc_2350_, 1, v_snd_2341_);
v___x_2346_ = v_reuseFailAlloc_2350_;
goto v_reusejp_2345_;
}
v_reusejp_2345_:
{
lean_object* v___x_2348_; 
if (v_isShared_2339_ == 0)
{
lean_ctor_set(v___x_2338_, 0, v___x_2346_);
v___x_2348_ = v___x_2338_;
goto v_reusejp_2347_;
}
else
{
lean_object* v_reuseFailAlloc_2349_; 
v_reuseFailAlloc_2349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2349_, 0, v___x_2346_);
v___x_2348_ = v_reuseFailAlloc_2349_;
goto v_reusejp_2347_;
}
v_reusejp_2347_:
{
return v___x_2348_;
}
}
}
}
}
else
{
return v___x_2335_;
}
}
else
{
lean_object* v___x_2353_; lean_object* v___x_2354_; 
v___x_2353_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems___closed__1));
v___x_2354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2354_, 0, v___x_2353_);
return v___x_2354_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems___boxed(lean_object* v_ids_x3f_2355_, lean_object* v_a_2356_, lean_object* v_a_2357_, lean_object* v_a_2358_, lean_object* v_a_2359_, lean_object* v_a_2360_, lean_object* v_a_2361_, lean_object* v_a_2362_, lean_object* v_a_2363_, lean_object* v_a_2364_){
_start:
{
lean_object* v_res_2365_; 
v_res_2365_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems(v_ids_x3f_2355_, v_a_2356_, v_a_2357_, v_a_2358_, v_a_2359_, v_a_2360_, v_a_2361_, v_a_2362_, v_a_2363_);
lean_dec(v_a_2363_);
lean_dec_ref(v_a_2362_);
lean_dec(v_a_2361_);
lean_dec_ref(v_a_2360_);
lean_dec(v_a_2359_);
lean_dec_ref(v_a_2358_);
lean_dec(v_a_2357_);
lean_dec_ref(v_a_2356_);
lean_dec(v_ids_x3f_2355_);
return v_res_2365_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__0(lean_object* v___x_2366_, lean_object* v_as_2367_, size_t v_sz_2368_, size_t v_i_2369_, lean_object* v_b_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_){
_start:
{
lean_object* v___x_2380_; 
v___x_2380_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__0___redArg(v___x_2366_, v_as_2367_, v_sz_2368_, v_i_2369_, v_b_2370_, v___y_2375_, v___y_2376_, v___y_2377_, v___y_2378_);
return v___x_2380_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__0___boxed(lean_object* v___x_2381_, lean_object* v_as_2382_, lean_object* v_sz_2383_, lean_object* v_i_2384_, lean_object* v_b_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_){
_start:
{
size_t v_sz_boxed_2395_; size_t v_i_boxed_2396_; lean_object* v_res_2397_; 
v_sz_boxed_2395_ = lean_unbox_usize(v_sz_2383_);
lean_dec(v_sz_2383_);
v_i_boxed_2396_ = lean_unbox_usize(v_i_2384_);
lean_dec(v_i_2384_);
v_res_2397_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__0(v___x_2381_, v_as_2382_, v_sz_boxed_2395_, v_i_boxed_2396_, v_b_2385_, v___y_2386_, v___y_2387_, v___y_2388_, v___y_2389_, v___y_2390_, v___y_2391_, v___y_2392_, v___y_2393_);
lean_dec(v___y_2393_);
lean_dec_ref(v___y_2392_);
lean_dec(v___y_2391_);
lean_dec_ref(v___y_2390_);
lean_dec(v___y_2389_);
lean_dec_ref(v___y_2388_);
lean_dec(v___y_2387_);
lean_dec_ref(v___y_2386_);
lean_dec_ref(v_as_2382_);
lean_dec_ref(v___x_2381_);
return v_res_2397_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___lam__0(lean_object* v_a_2399_, lean_object* v_x_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_){
_start:
{
lean_object* v___x_2412_; lean_object* v___x_2413_; 
v___x_2412_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___lam__0___closed__0));
v___x_2413_ = l_Lean_Meta_Sym_Simp_Theorems_rewrite(v_a_2399_, v___x_2412_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_);
return v___x_2413_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___lam__0___boxed(lean_object* v_a_2414_, lean_object* v_x_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_){
_start:
{
lean_object* v_res_2427_; 
v_res_2427_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___lam__0(v_a_2414_, v_x_2415_, v___y_2416_, v___y_2417_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_);
lean_dec(v___y_2425_);
lean_dec_ref(v___y_2424_);
lean_dec(v___y_2423_);
lean_dec_ref(v___y_2422_);
lean_dec(v___y_2421_);
lean_dec_ref(v___y_2420_);
lean_dec(v___y_2419_);
lean_dec_ref(v___y_2418_);
lean_dec(v___y_2417_);
lean_dec_ref(v_a_2414_);
return v_res_2427_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___lam__1(lean_object* v_post_2428_, lean_object* v___f_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_){
_start:
{
lean_object* v___x_2441_; 
lean_inc(v___y_2439_);
lean_inc_ref(v___y_2438_);
lean_inc(v___y_2437_);
lean_inc_ref(v___y_2436_);
lean_inc(v___y_2435_);
lean_inc_ref(v___y_2434_);
lean_inc(v___y_2433_);
lean_inc_ref(v___y_2432_);
lean_inc(v___y_2431_);
lean_inc_ref(v___y_2430_);
v___x_2441_ = lean_apply_11(v_post_2428_, v___y_2430_, v___y_2431_, v___y_2432_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_, lean_box(0));
if (lean_obj_tag(v___x_2441_) == 0)
{
lean_object* v_a_2442_; lean_object* v___x_2443_; 
v_a_2442_ = lean_ctor_get(v___x_2441_, 0);
lean_inc(v_a_2442_);
v___x_2443_ = lean_box(0);
if (lean_obj_tag(v_a_2442_) == 0)
{
uint8_t v_done_2444_; 
v_done_2444_ = lean_ctor_get_uint8(v_a_2442_, 0);
if (v_done_2444_ == 0)
{
uint8_t v_contextDependent_2445_; lean_object* v___x_2446_; 
lean_dec_ref(v___x_2441_);
v_contextDependent_2445_ = lean_ctor_get_uint8(v_a_2442_, 1);
lean_dec_ref(v_a_2442_);
v___x_2446_ = lean_apply_12(v___f_2429_, v___x_2443_, v___y_2430_, v___y_2431_, v___y_2432_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_, lean_box(0));
if (lean_obj_tag(v___x_2446_) == 0)
{
lean_object* v_a_2447_; uint8_t v___y_2449_; 
v_a_2447_ = lean_ctor_get(v___x_2446_, 0);
lean_inc(v_a_2447_);
if (v_contextDependent_2445_ == 0)
{
lean_dec(v_a_2447_);
return v___x_2446_;
}
else
{
if (lean_obj_tag(v_a_2447_) == 0)
{
uint8_t v_contextDependent_2459_; 
v_contextDependent_2459_ = lean_ctor_get_uint8(v_a_2447_, 1);
v___y_2449_ = v_contextDependent_2459_;
goto v___jp_2448_;
}
else
{
uint8_t v_contextDependent_2460_; 
v_contextDependent_2460_ = lean_ctor_get_uint8(v_a_2447_, sizeof(void*)*2 + 1);
v___y_2449_ = v_contextDependent_2460_;
goto v___jp_2448_;
}
}
v___jp_2448_:
{
if (v___y_2449_ == 0)
{
lean_object* v___x_2451_; uint8_t v_isShared_2452_; uint8_t v_isSharedCheck_2457_; 
v_isSharedCheck_2457_ = !lean_is_exclusive(v___x_2446_);
if (v_isSharedCheck_2457_ == 0)
{
lean_object* v_unused_2458_; 
v_unused_2458_ = lean_ctor_get(v___x_2446_, 0);
lean_dec(v_unused_2458_);
v___x_2451_ = v___x_2446_;
v_isShared_2452_ = v_isSharedCheck_2457_;
goto v_resetjp_2450_;
}
else
{
lean_dec(v___x_2446_);
v___x_2451_ = lean_box(0);
v_isShared_2452_ = v_isSharedCheck_2457_;
goto v_resetjp_2450_;
}
v_resetjp_2450_:
{
lean_object* v___x_2453_; lean_object* v___x_2455_; 
v___x_2453_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_2447_);
if (v_isShared_2452_ == 0)
{
lean_ctor_set(v___x_2451_, 0, v___x_2453_);
v___x_2455_ = v___x_2451_;
goto v_reusejp_2454_;
}
else
{
lean_object* v_reuseFailAlloc_2456_; 
v_reuseFailAlloc_2456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2456_, 0, v___x_2453_);
v___x_2455_ = v_reuseFailAlloc_2456_;
goto v_reusejp_2454_;
}
v_reusejp_2454_:
{
return v___x_2455_;
}
}
}
else
{
lean_dec(v_a_2447_);
return v___x_2446_;
}
}
}
else
{
return v___x_2446_;
}
}
else
{
lean_dec_ref(v_a_2442_);
lean_dec(v___y_2439_);
lean_dec_ref(v___y_2438_);
lean_dec(v___y_2437_);
lean_dec_ref(v___y_2436_);
lean_dec(v___y_2435_);
lean_dec_ref(v___y_2434_);
lean_dec(v___y_2433_);
lean_dec_ref(v___y_2432_);
lean_dec(v___y_2431_);
lean_dec_ref(v___y_2430_);
lean_dec_ref(v___f_2429_);
return v___x_2441_;
}
}
else
{
uint8_t v_done_2461_; 
v_done_2461_ = lean_ctor_get_uint8(v_a_2442_, sizeof(void*)*2);
if (v_done_2461_ == 0)
{
lean_object* v_e_x27_2462_; lean_object* v_proof_2463_; uint8_t v_contextDependent_2464_; lean_object* v___x_2466_; uint8_t v_isShared_2467_; uint8_t v_isSharedCheck_2514_; 
lean_dec_ref(v___x_2441_);
v_e_x27_2462_ = lean_ctor_get(v_a_2442_, 0);
v_proof_2463_ = lean_ctor_get(v_a_2442_, 1);
v_contextDependent_2464_ = lean_ctor_get_uint8(v_a_2442_, sizeof(void*)*2 + 1);
v_isSharedCheck_2514_ = !lean_is_exclusive(v_a_2442_);
if (v_isSharedCheck_2514_ == 0)
{
v___x_2466_ = v_a_2442_;
v_isShared_2467_ = v_isSharedCheck_2514_;
goto v_resetjp_2465_;
}
else
{
lean_inc(v_proof_2463_);
lean_inc(v_e_x27_2462_);
lean_dec(v_a_2442_);
v___x_2466_ = lean_box(0);
v_isShared_2467_ = v_isSharedCheck_2514_;
goto v_resetjp_2465_;
}
v_resetjp_2465_:
{
lean_object* v___x_2468_; 
lean_inc(v___y_2439_);
lean_inc_ref(v___y_2438_);
lean_inc(v___y_2437_);
lean_inc_ref(v___y_2436_);
lean_inc(v___y_2435_);
lean_inc_ref(v_e_x27_2462_);
v___x_2468_ = lean_apply_12(v___f_2429_, v___x_2443_, v_e_x27_2462_, v___y_2431_, v___y_2432_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_, lean_box(0));
if (lean_obj_tag(v___x_2468_) == 0)
{
lean_object* v_a_2469_; lean_object* v___x_2471_; uint8_t v_isShared_2472_; uint8_t v_isSharedCheck_2513_; 
v_a_2469_ = lean_ctor_get(v___x_2468_, 0);
v_isSharedCheck_2513_ = !lean_is_exclusive(v___x_2468_);
if (v_isSharedCheck_2513_ == 0)
{
v___x_2471_ = v___x_2468_;
v_isShared_2472_ = v_isSharedCheck_2513_;
goto v_resetjp_2470_;
}
else
{
lean_inc(v_a_2469_);
lean_dec(v___x_2468_);
v___x_2471_ = lean_box(0);
v_isShared_2472_ = v_isSharedCheck_2513_;
goto v_resetjp_2470_;
}
v_resetjp_2470_:
{
if (lean_obj_tag(v_a_2469_) == 0)
{
uint8_t v_done_2473_; uint8_t v_contextDependent_2474_; uint8_t v___y_2476_; 
lean_dec(v___y_2439_);
lean_dec_ref(v___y_2438_);
lean_dec(v___y_2437_);
lean_dec_ref(v___y_2436_);
lean_dec(v___y_2435_);
lean_dec_ref(v___y_2430_);
v_done_2473_ = lean_ctor_get_uint8(v_a_2469_, 0);
v_contextDependent_2474_ = lean_ctor_get_uint8(v_a_2469_, 1);
lean_dec_ref(v_a_2469_);
if (v_contextDependent_2464_ == 0)
{
v___y_2476_ = v_contextDependent_2474_;
goto v___jp_2475_;
}
else
{
v___y_2476_ = v_contextDependent_2464_;
goto v___jp_2475_;
}
v___jp_2475_:
{
lean_object* v___x_2478_; 
if (v_isShared_2467_ == 0)
{
v___x_2478_ = v___x_2466_;
goto v_reusejp_2477_;
}
else
{
lean_object* v_reuseFailAlloc_2482_; 
v_reuseFailAlloc_2482_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2482_, 0, v_e_x27_2462_);
lean_ctor_set(v_reuseFailAlloc_2482_, 1, v_proof_2463_);
v___x_2478_ = v_reuseFailAlloc_2482_;
goto v_reusejp_2477_;
}
v_reusejp_2477_:
{
lean_object* v___x_2480_; 
lean_ctor_set_uint8(v___x_2478_, sizeof(void*)*2, v_done_2473_);
lean_ctor_set_uint8(v___x_2478_, sizeof(void*)*2 + 1, v___y_2476_);
if (v_isShared_2472_ == 0)
{
lean_ctor_set(v___x_2471_, 0, v___x_2478_);
v___x_2480_ = v___x_2471_;
goto v_reusejp_2479_;
}
else
{
lean_object* v_reuseFailAlloc_2481_; 
v_reuseFailAlloc_2481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2481_, 0, v___x_2478_);
v___x_2480_ = v_reuseFailAlloc_2481_;
goto v_reusejp_2479_;
}
v_reusejp_2479_:
{
return v___x_2480_;
}
}
}
}
else
{
lean_object* v_e_x27_2483_; lean_object* v_proof_2484_; uint8_t v_done_2485_; uint8_t v_contextDependent_2486_; lean_object* v___x_2488_; uint8_t v_isShared_2489_; uint8_t v_isSharedCheck_2512_; 
lean_del_object(v___x_2471_);
lean_del_object(v___x_2466_);
v_e_x27_2483_ = lean_ctor_get(v_a_2469_, 0);
v_proof_2484_ = lean_ctor_get(v_a_2469_, 1);
v_done_2485_ = lean_ctor_get_uint8(v_a_2469_, sizeof(void*)*2);
v_contextDependent_2486_ = lean_ctor_get_uint8(v_a_2469_, sizeof(void*)*2 + 1);
v_isSharedCheck_2512_ = !lean_is_exclusive(v_a_2469_);
if (v_isSharedCheck_2512_ == 0)
{
v___x_2488_ = v_a_2469_;
v_isShared_2489_ = v_isSharedCheck_2512_;
goto v_resetjp_2487_;
}
else
{
lean_inc(v_proof_2484_);
lean_inc(v_e_x27_2483_);
lean_dec(v_a_2469_);
v___x_2488_ = lean_box(0);
v_isShared_2489_ = v_isSharedCheck_2512_;
goto v_resetjp_2487_;
}
v_resetjp_2487_:
{
lean_object* v___x_2490_; 
lean_inc_ref(v_e_x27_2483_);
v___x_2490_ = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(v___y_2430_, v_e_x27_2462_, v_proof_2463_, v_e_x27_2483_, v_proof_2484_, v___y_2435_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_);
lean_dec(v___y_2439_);
lean_dec_ref(v___y_2438_);
lean_dec(v___y_2437_);
lean_dec_ref(v___y_2436_);
lean_dec(v___y_2435_);
if (lean_obj_tag(v___x_2490_) == 0)
{
lean_object* v_a_2491_; lean_object* v___x_2493_; uint8_t v_isShared_2494_; uint8_t v_isSharedCheck_2503_; 
v_a_2491_ = lean_ctor_get(v___x_2490_, 0);
v_isSharedCheck_2503_ = !lean_is_exclusive(v___x_2490_);
if (v_isSharedCheck_2503_ == 0)
{
v___x_2493_ = v___x_2490_;
v_isShared_2494_ = v_isSharedCheck_2503_;
goto v_resetjp_2492_;
}
else
{
lean_inc(v_a_2491_);
lean_dec(v___x_2490_);
v___x_2493_ = lean_box(0);
v_isShared_2494_ = v_isSharedCheck_2503_;
goto v_resetjp_2492_;
}
v_resetjp_2492_:
{
uint8_t v___y_2496_; 
if (v_contextDependent_2464_ == 0)
{
v___y_2496_ = v_contextDependent_2486_;
goto v___jp_2495_;
}
else
{
v___y_2496_ = v_contextDependent_2464_;
goto v___jp_2495_;
}
v___jp_2495_:
{
lean_object* v___x_2498_; 
if (v_isShared_2489_ == 0)
{
lean_ctor_set(v___x_2488_, 1, v_a_2491_);
v___x_2498_ = v___x_2488_;
goto v_reusejp_2497_;
}
else
{
lean_object* v_reuseFailAlloc_2502_; 
v_reuseFailAlloc_2502_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2502_, 0, v_e_x27_2483_);
lean_ctor_set(v_reuseFailAlloc_2502_, 1, v_a_2491_);
lean_ctor_set_uint8(v_reuseFailAlloc_2502_, sizeof(void*)*2, v_done_2485_);
v___x_2498_ = v_reuseFailAlloc_2502_;
goto v_reusejp_2497_;
}
v_reusejp_2497_:
{
lean_object* v___x_2500_; 
lean_ctor_set_uint8(v___x_2498_, sizeof(void*)*2 + 1, v___y_2496_);
if (v_isShared_2494_ == 0)
{
lean_ctor_set(v___x_2493_, 0, v___x_2498_);
v___x_2500_ = v___x_2493_;
goto v_reusejp_2499_;
}
else
{
lean_object* v_reuseFailAlloc_2501_; 
v_reuseFailAlloc_2501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2501_, 0, v___x_2498_);
v___x_2500_ = v_reuseFailAlloc_2501_;
goto v_reusejp_2499_;
}
v_reusejp_2499_:
{
return v___x_2500_;
}
}
}
}
}
else
{
lean_object* v_a_2504_; lean_object* v___x_2506_; uint8_t v_isShared_2507_; uint8_t v_isSharedCheck_2511_; 
lean_del_object(v___x_2488_);
lean_dec_ref(v_e_x27_2483_);
v_a_2504_ = lean_ctor_get(v___x_2490_, 0);
v_isSharedCheck_2511_ = !lean_is_exclusive(v___x_2490_);
if (v_isSharedCheck_2511_ == 0)
{
v___x_2506_ = v___x_2490_;
v_isShared_2507_ = v_isSharedCheck_2511_;
goto v_resetjp_2505_;
}
else
{
lean_inc(v_a_2504_);
lean_dec(v___x_2490_);
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
}
}
else
{
lean_del_object(v___x_2466_);
lean_dec_ref(v_proof_2463_);
lean_dec_ref(v_e_x27_2462_);
lean_dec(v___y_2439_);
lean_dec_ref(v___y_2438_);
lean_dec(v___y_2437_);
lean_dec_ref(v___y_2436_);
lean_dec(v___y_2435_);
lean_dec_ref(v___y_2430_);
return v___x_2468_;
}
}
}
else
{
lean_dec_ref(v_a_2442_);
lean_dec(v___y_2439_);
lean_dec_ref(v___y_2438_);
lean_dec(v___y_2437_);
lean_dec_ref(v___y_2436_);
lean_dec(v___y_2435_);
lean_dec_ref(v___y_2434_);
lean_dec(v___y_2433_);
lean_dec_ref(v___y_2432_);
lean_dec(v___y_2431_);
lean_dec_ref(v___y_2430_);
lean_dec_ref(v___f_2429_);
return v___x_2441_;
}
}
}
else
{
lean_dec(v___y_2439_);
lean_dec_ref(v___y_2438_);
lean_dec(v___y_2437_);
lean_dec_ref(v___y_2436_);
lean_dec(v___y_2435_);
lean_dec_ref(v___y_2434_);
lean_dec(v___y_2433_);
lean_dec_ref(v___y_2432_);
lean_dec(v___y_2431_);
lean_dec_ref(v___y_2430_);
lean_dec_ref(v___f_2429_);
return v___x_2441_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___lam__1___boxed(lean_object* v_post_2515_, lean_object* v___f_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_){
_start:
{
lean_object* v_res_2528_; 
v_res_2528_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___lam__1(v_post_2515_, v___f_2516_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_, v___y_2525_, v___y_2526_);
return v_res_2528_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems_spec__0___redArg(lean_object* v_as_2529_, size_t v_sz_2530_, size_t v_i_2531_, lean_object* v_b_2532_){
_start:
{
uint8_t v___x_2534_; 
v___x_2534_ = lean_usize_dec_lt(v_i_2531_, v_sz_2530_);
if (v___x_2534_ == 0)
{
lean_object* v___x_2535_; 
v___x_2535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2535_, 0, v_b_2532_);
return v___x_2535_;
}
else
{
lean_object* v_a_2536_; lean_object* v___x_2537_; size_t v___x_2538_; size_t v___x_2539_; 
v_a_2536_ = lean_array_uget_borrowed(v_as_2529_, v_i_2531_);
lean_inc(v_a_2536_);
v___x_2537_ = l_Lean_Meta_Sym_Simp_Theorems_insert(v_b_2532_, v_a_2536_);
v___x_2538_ = ((size_t)1ULL);
v___x_2539_ = lean_usize_add(v_i_2531_, v___x_2538_);
v_i_2531_ = v___x_2539_;
v_b_2532_ = v___x_2537_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems_spec__0___redArg___boxed(lean_object* v_as_2541_, lean_object* v_sz_2542_, lean_object* v_i_2543_, lean_object* v_b_2544_, lean_object* v___y_2545_){
_start:
{
size_t v_sz_boxed_2546_; size_t v_i_boxed_2547_; lean_object* v_res_2548_; 
v_sz_boxed_2546_ = lean_unbox_usize(v_sz_2542_);
lean_dec(v_sz_2542_);
v_i_boxed_2547_ = lean_unbox_usize(v_i_2543_);
lean_dec(v_i_2543_);
v_res_2548_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems_spec__0___redArg(v_as_2541_, v_sz_boxed_2546_, v_i_boxed_2547_, v_b_2544_);
lean_dec_ref(v_as_2541_);
return v_res_2548_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___closed__0(void){
_start:
{
lean_object* v___x_2549_; 
v___x_2549_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2549_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___closed__1(void){
_start:
{
lean_object* v___x_2550_; lean_object* v_thms_2551_; 
v___x_2550_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___closed__0, &l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___closed__0_once, _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___closed__0);
v_thms_2551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_thms_2551_, 0, v___x_2550_);
return v_thms_2551_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems(lean_object* v_post_2552_, lean_object* v_extraThms_2553_, lean_object* v_a_2554_, lean_object* v_a_2555_, lean_object* v_a_2556_, lean_object* v_a_2557_, lean_object* v_a_2558_, lean_object* v_a_2559_, lean_object* v_a_2560_, lean_object* v_a_2561_){
_start:
{
lean_object* v___x_2563_; lean_object* v___x_2564_; uint8_t v___x_2565_; 
v___x_2563_ = lean_array_get_size(v_extraThms_2553_);
v___x_2564_ = lean_unsigned_to_nat(0u);
v___x_2565_ = lean_nat_dec_eq(v___x_2563_, v___x_2564_);
if (v___x_2565_ == 0)
{
lean_object* v_thms_2566_; size_t v_sz_2567_; size_t v___x_2568_; lean_object* v___x_2569_; 
v_thms_2566_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___closed__1, &l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___closed__1);
v_sz_2567_ = lean_array_size(v_extraThms_2553_);
v___x_2568_ = ((size_t)0ULL);
v___x_2569_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems_spec__0___redArg(v_extraThms_2553_, v_sz_2567_, v___x_2568_, v_thms_2566_);
if (lean_obj_tag(v___x_2569_) == 0)
{
lean_object* v_a_2570_; lean_object* v___x_2572_; uint8_t v_isShared_2573_; uint8_t v_isSharedCheck_2579_; 
v_a_2570_ = lean_ctor_get(v___x_2569_, 0);
v_isSharedCheck_2579_ = !lean_is_exclusive(v___x_2569_);
if (v_isSharedCheck_2579_ == 0)
{
v___x_2572_ = v___x_2569_;
v_isShared_2573_ = v_isSharedCheck_2579_;
goto v_resetjp_2571_;
}
else
{
lean_inc(v_a_2570_);
lean_dec(v___x_2569_);
v___x_2572_ = lean_box(0);
v_isShared_2573_ = v_isSharedCheck_2579_;
goto v_resetjp_2571_;
}
v_resetjp_2571_:
{
lean_object* v___f_2574_; lean_object* v___f_2575_; lean_object* v___x_2577_; 
v___f_2574_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___lam__0___boxed), 13, 1);
lean_closure_set(v___f_2574_, 0, v_a_2570_);
v___f_2575_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___lam__1___boxed), 13, 2);
lean_closure_set(v___f_2575_, 0, v_post_2552_);
lean_closure_set(v___f_2575_, 1, v___f_2574_);
if (v_isShared_2573_ == 0)
{
lean_ctor_set(v___x_2572_, 0, v___f_2575_);
v___x_2577_ = v___x_2572_;
goto v_reusejp_2576_;
}
else
{
lean_object* v_reuseFailAlloc_2578_; 
v_reuseFailAlloc_2578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2578_, 0, v___f_2575_);
v___x_2577_ = v_reuseFailAlloc_2578_;
goto v_reusejp_2576_;
}
v_reusejp_2576_:
{
return v___x_2577_;
}
}
}
else
{
lean_object* v_a_2580_; lean_object* v___x_2582_; uint8_t v_isShared_2583_; uint8_t v_isSharedCheck_2587_; 
lean_dec_ref(v_post_2552_);
v_a_2580_ = lean_ctor_get(v___x_2569_, 0);
v_isSharedCheck_2587_ = !lean_is_exclusive(v___x_2569_);
if (v_isSharedCheck_2587_ == 0)
{
v___x_2582_ = v___x_2569_;
v_isShared_2583_ = v_isSharedCheck_2587_;
goto v_resetjp_2581_;
}
else
{
lean_inc(v_a_2580_);
lean_dec(v___x_2569_);
v___x_2582_ = lean_box(0);
v_isShared_2583_ = v_isSharedCheck_2587_;
goto v_resetjp_2581_;
}
v_resetjp_2581_:
{
lean_object* v___x_2585_; 
if (v_isShared_2583_ == 0)
{
v___x_2585_ = v___x_2582_;
goto v_reusejp_2584_;
}
else
{
lean_object* v_reuseFailAlloc_2586_; 
v_reuseFailAlloc_2586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2586_, 0, v_a_2580_);
v___x_2585_ = v_reuseFailAlloc_2586_;
goto v_reusejp_2584_;
}
v_reusejp_2584_:
{
return v___x_2585_;
}
}
}
}
else
{
lean_object* v___x_2588_; 
v___x_2588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2588_, 0, v_post_2552_);
return v___x_2588_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___boxed(lean_object* v_post_2589_, lean_object* v_extraThms_2590_, lean_object* v_a_2591_, lean_object* v_a_2592_, lean_object* v_a_2593_, lean_object* v_a_2594_, lean_object* v_a_2595_, lean_object* v_a_2596_, lean_object* v_a_2597_, lean_object* v_a_2598_, lean_object* v_a_2599_){
_start:
{
lean_object* v_res_2600_; 
v_res_2600_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems(v_post_2589_, v_extraThms_2590_, v_a_2591_, v_a_2592_, v_a_2593_, v_a_2594_, v_a_2595_, v_a_2596_, v_a_2597_, v_a_2598_);
lean_dec(v_a_2598_);
lean_dec_ref(v_a_2597_);
lean_dec(v_a_2596_);
lean_dec_ref(v_a_2595_);
lean_dec(v_a_2594_);
lean_dec_ref(v_a_2593_);
lean_dec(v_a_2592_);
lean_dec_ref(v_a_2591_);
lean_dec_ref(v_extraThms_2590_);
return v_res_2600_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems_spec__0(lean_object* v_as_2601_, size_t v_sz_2602_, size_t v_i_2603_, lean_object* v_b_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_){
_start:
{
lean_object* v___x_2614_; 
v___x_2614_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems_spec__0___redArg(v_as_2601_, v_sz_2602_, v_i_2603_, v_b_2604_);
return v___x_2614_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems_spec__0___boxed(lean_object* v_as_2615_, lean_object* v_sz_2616_, lean_object* v_i_2617_, lean_object* v_b_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_){
_start:
{
size_t v_sz_boxed_2628_; size_t v_i_boxed_2629_; lean_object* v_res_2630_; 
v_sz_boxed_2628_ = lean_unbox_usize(v_sz_2616_);
lean_dec(v_sz_2616_);
v_i_boxed_2629_ = lean_unbox_usize(v_i_2617_);
lean_dec(v_i_2617_);
v_res_2630_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems_spec__0(v_as_2615_, v_sz_boxed_2628_, v_i_boxed_2629_, v_b_2618_, v___y_2619_, v___y_2620_, v___y_2621_, v___y_2622_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_);
lean_dec(v___y_2626_);
lean_dec_ref(v___y_2625_);
lean_dec(v___y_2624_);
lean_dec_ref(v___y_2623_);
lean_dec(v___y_2622_);
lean_dec_ref(v___y_2621_);
lean_dec(v___y_2620_);
lean_dec_ref(v___y_2619_);
lean_dec_ref(v_as_2615_);
return v_res_2630_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkDefaultMethods___lam__1(lean_object* v___x_2631_, lean_object* v___f_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_){
_start:
{
lean_object* v___x_2644_; 
lean_inc_ref(v___y_2633_);
v___x_2644_ = l_Lean_Meta_Sym_Simp_evalGround___redArg(v___x_2631_, v___y_2633_, v___y_2637_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_);
if (lean_obj_tag(v___x_2644_) == 0)
{
lean_object* v_a_2645_; lean_object* v___x_2646_; 
v_a_2645_ = lean_ctor_get(v___x_2644_, 0);
lean_inc(v_a_2645_);
v___x_2646_ = lean_box(0);
if (lean_obj_tag(v_a_2645_) == 0)
{
uint8_t v_done_2647_; 
v_done_2647_ = lean_ctor_get_uint8(v_a_2645_, 0);
if (v_done_2647_ == 0)
{
uint8_t v_contextDependent_2648_; lean_object* v___x_2649_; 
lean_dec_ref(v___x_2644_);
v_contextDependent_2648_ = lean_ctor_get_uint8(v_a_2645_, 1);
lean_dec_ref(v_a_2645_);
v___x_2649_ = lean_apply_12(v___f_2632_, v___x_2646_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_, lean_box(0));
if (lean_obj_tag(v___x_2649_) == 0)
{
lean_object* v_a_2650_; uint8_t v___y_2652_; 
v_a_2650_ = lean_ctor_get(v___x_2649_, 0);
lean_inc(v_a_2650_);
if (v_contextDependent_2648_ == 0)
{
lean_dec(v_a_2650_);
return v___x_2649_;
}
else
{
if (lean_obj_tag(v_a_2650_) == 0)
{
uint8_t v_contextDependent_2662_; 
v_contextDependent_2662_ = lean_ctor_get_uint8(v_a_2650_, 1);
v___y_2652_ = v_contextDependent_2662_;
goto v___jp_2651_;
}
else
{
uint8_t v_contextDependent_2663_; 
v_contextDependent_2663_ = lean_ctor_get_uint8(v_a_2650_, sizeof(void*)*2 + 1);
v___y_2652_ = v_contextDependent_2663_;
goto v___jp_2651_;
}
}
v___jp_2651_:
{
if (v___y_2652_ == 0)
{
lean_object* v___x_2654_; uint8_t v_isShared_2655_; uint8_t v_isSharedCheck_2660_; 
v_isSharedCheck_2660_ = !lean_is_exclusive(v___x_2649_);
if (v_isSharedCheck_2660_ == 0)
{
lean_object* v_unused_2661_; 
v_unused_2661_ = lean_ctor_get(v___x_2649_, 0);
lean_dec(v_unused_2661_);
v___x_2654_ = v___x_2649_;
v_isShared_2655_ = v_isSharedCheck_2660_;
goto v_resetjp_2653_;
}
else
{
lean_dec(v___x_2649_);
v___x_2654_ = lean_box(0);
v_isShared_2655_ = v_isSharedCheck_2660_;
goto v_resetjp_2653_;
}
v_resetjp_2653_:
{
lean_object* v___x_2656_; lean_object* v___x_2658_; 
v___x_2656_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_2650_);
if (v_isShared_2655_ == 0)
{
lean_ctor_set(v___x_2654_, 0, v___x_2656_);
v___x_2658_ = v___x_2654_;
goto v_reusejp_2657_;
}
else
{
lean_object* v_reuseFailAlloc_2659_; 
v_reuseFailAlloc_2659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2659_, 0, v___x_2656_);
v___x_2658_ = v_reuseFailAlloc_2659_;
goto v_reusejp_2657_;
}
v_reusejp_2657_:
{
return v___x_2658_;
}
}
}
else
{
lean_dec(v_a_2650_);
return v___x_2649_;
}
}
}
else
{
return v___x_2649_;
}
}
else
{
lean_dec_ref(v_a_2645_);
lean_dec(v___y_2642_);
lean_dec_ref(v___y_2641_);
lean_dec(v___y_2640_);
lean_dec_ref(v___y_2639_);
lean_dec(v___y_2638_);
lean_dec_ref(v___y_2637_);
lean_dec(v___y_2636_);
lean_dec_ref(v___y_2635_);
lean_dec(v___y_2634_);
lean_dec_ref(v___y_2633_);
lean_dec_ref(v___f_2632_);
return v___x_2644_;
}
}
else
{
uint8_t v_done_2664_; 
v_done_2664_ = lean_ctor_get_uint8(v_a_2645_, sizeof(void*)*2);
if (v_done_2664_ == 0)
{
lean_object* v_e_x27_2665_; lean_object* v_proof_2666_; uint8_t v_contextDependent_2667_; lean_object* v___x_2669_; uint8_t v_isShared_2670_; uint8_t v_isSharedCheck_2717_; 
lean_dec_ref(v___x_2644_);
v_e_x27_2665_ = lean_ctor_get(v_a_2645_, 0);
v_proof_2666_ = lean_ctor_get(v_a_2645_, 1);
v_contextDependent_2667_ = lean_ctor_get_uint8(v_a_2645_, sizeof(void*)*2 + 1);
v_isSharedCheck_2717_ = !lean_is_exclusive(v_a_2645_);
if (v_isSharedCheck_2717_ == 0)
{
v___x_2669_ = v_a_2645_;
v_isShared_2670_ = v_isSharedCheck_2717_;
goto v_resetjp_2668_;
}
else
{
lean_inc(v_proof_2666_);
lean_inc(v_e_x27_2665_);
lean_dec(v_a_2645_);
v___x_2669_ = lean_box(0);
v_isShared_2670_ = v_isSharedCheck_2717_;
goto v_resetjp_2668_;
}
v_resetjp_2668_:
{
lean_object* v___x_2671_; 
lean_inc(v___y_2642_);
lean_inc_ref(v___y_2641_);
lean_inc(v___y_2640_);
lean_inc_ref(v___y_2639_);
lean_inc(v___y_2638_);
lean_inc_ref(v_e_x27_2665_);
v___x_2671_ = lean_apply_12(v___f_2632_, v___x_2646_, v_e_x27_2665_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_, lean_box(0));
if (lean_obj_tag(v___x_2671_) == 0)
{
lean_object* v_a_2672_; lean_object* v___x_2674_; uint8_t v_isShared_2675_; uint8_t v_isSharedCheck_2716_; 
v_a_2672_ = lean_ctor_get(v___x_2671_, 0);
v_isSharedCheck_2716_ = !lean_is_exclusive(v___x_2671_);
if (v_isSharedCheck_2716_ == 0)
{
v___x_2674_ = v___x_2671_;
v_isShared_2675_ = v_isSharedCheck_2716_;
goto v_resetjp_2673_;
}
else
{
lean_inc(v_a_2672_);
lean_dec(v___x_2671_);
v___x_2674_ = lean_box(0);
v_isShared_2675_ = v_isSharedCheck_2716_;
goto v_resetjp_2673_;
}
v_resetjp_2673_:
{
if (lean_obj_tag(v_a_2672_) == 0)
{
uint8_t v_done_2676_; uint8_t v_contextDependent_2677_; uint8_t v___y_2679_; 
lean_dec(v___y_2642_);
lean_dec_ref(v___y_2641_);
lean_dec(v___y_2640_);
lean_dec_ref(v___y_2639_);
lean_dec(v___y_2638_);
lean_dec_ref(v___y_2633_);
v_done_2676_ = lean_ctor_get_uint8(v_a_2672_, 0);
v_contextDependent_2677_ = lean_ctor_get_uint8(v_a_2672_, 1);
lean_dec_ref(v_a_2672_);
if (v_contextDependent_2667_ == 0)
{
v___y_2679_ = v_contextDependent_2677_;
goto v___jp_2678_;
}
else
{
v___y_2679_ = v_contextDependent_2667_;
goto v___jp_2678_;
}
v___jp_2678_:
{
lean_object* v___x_2681_; 
if (v_isShared_2670_ == 0)
{
v___x_2681_ = v___x_2669_;
goto v_reusejp_2680_;
}
else
{
lean_object* v_reuseFailAlloc_2685_; 
v_reuseFailAlloc_2685_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2685_, 0, v_e_x27_2665_);
lean_ctor_set(v_reuseFailAlloc_2685_, 1, v_proof_2666_);
v___x_2681_ = v_reuseFailAlloc_2685_;
goto v_reusejp_2680_;
}
v_reusejp_2680_:
{
lean_object* v___x_2683_; 
lean_ctor_set_uint8(v___x_2681_, sizeof(void*)*2, v_done_2676_);
lean_ctor_set_uint8(v___x_2681_, sizeof(void*)*2 + 1, v___y_2679_);
if (v_isShared_2675_ == 0)
{
lean_ctor_set(v___x_2674_, 0, v___x_2681_);
v___x_2683_ = v___x_2674_;
goto v_reusejp_2682_;
}
else
{
lean_object* v_reuseFailAlloc_2684_; 
v_reuseFailAlloc_2684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2684_, 0, v___x_2681_);
v___x_2683_ = v_reuseFailAlloc_2684_;
goto v_reusejp_2682_;
}
v_reusejp_2682_:
{
return v___x_2683_;
}
}
}
}
else
{
lean_object* v_e_x27_2686_; lean_object* v_proof_2687_; uint8_t v_done_2688_; uint8_t v_contextDependent_2689_; lean_object* v___x_2691_; uint8_t v_isShared_2692_; uint8_t v_isSharedCheck_2715_; 
lean_del_object(v___x_2674_);
lean_del_object(v___x_2669_);
v_e_x27_2686_ = lean_ctor_get(v_a_2672_, 0);
v_proof_2687_ = lean_ctor_get(v_a_2672_, 1);
v_done_2688_ = lean_ctor_get_uint8(v_a_2672_, sizeof(void*)*2);
v_contextDependent_2689_ = lean_ctor_get_uint8(v_a_2672_, sizeof(void*)*2 + 1);
v_isSharedCheck_2715_ = !lean_is_exclusive(v_a_2672_);
if (v_isSharedCheck_2715_ == 0)
{
v___x_2691_ = v_a_2672_;
v_isShared_2692_ = v_isSharedCheck_2715_;
goto v_resetjp_2690_;
}
else
{
lean_inc(v_proof_2687_);
lean_inc(v_e_x27_2686_);
lean_dec(v_a_2672_);
v___x_2691_ = lean_box(0);
v_isShared_2692_ = v_isSharedCheck_2715_;
goto v_resetjp_2690_;
}
v_resetjp_2690_:
{
lean_object* v___x_2693_; 
lean_inc_ref(v_e_x27_2686_);
v___x_2693_ = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(v___y_2633_, v_e_x27_2665_, v_proof_2666_, v_e_x27_2686_, v_proof_2687_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_);
lean_dec(v___y_2642_);
lean_dec_ref(v___y_2641_);
lean_dec(v___y_2640_);
lean_dec_ref(v___y_2639_);
lean_dec(v___y_2638_);
if (lean_obj_tag(v___x_2693_) == 0)
{
lean_object* v_a_2694_; lean_object* v___x_2696_; uint8_t v_isShared_2697_; uint8_t v_isSharedCheck_2706_; 
v_a_2694_ = lean_ctor_get(v___x_2693_, 0);
v_isSharedCheck_2706_ = !lean_is_exclusive(v___x_2693_);
if (v_isSharedCheck_2706_ == 0)
{
v___x_2696_ = v___x_2693_;
v_isShared_2697_ = v_isSharedCheck_2706_;
goto v_resetjp_2695_;
}
else
{
lean_inc(v_a_2694_);
lean_dec(v___x_2693_);
v___x_2696_ = lean_box(0);
v_isShared_2697_ = v_isSharedCheck_2706_;
goto v_resetjp_2695_;
}
v_resetjp_2695_:
{
uint8_t v___y_2699_; 
if (v_contextDependent_2667_ == 0)
{
v___y_2699_ = v_contextDependent_2689_;
goto v___jp_2698_;
}
else
{
v___y_2699_ = v_contextDependent_2667_;
goto v___jp_2698_;
}
v___jp_2698_:
{
lean_object* v___x_2701_; 
if (v_isShared_2692_ == 0)
{
lean_ctor_set(v___x_2691_, 1, v_a_2694_);
v___x_2701_ = v___x_2691_;
goto v_reusejp_2700_;
}
else
{
lean_object* v_reuseFailAlloc_2705_; 
v_reuseFailAlloc_2705_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2705_, 0, v_e_x27_2686_);
lean_ctor_set(v_reuseFailAlloc_2705_, 1, v_a_2694_);
lean_ctor_set_uint8(v_reuseFailAlloc_2705_, sizeof(void*)*2, v_done_2688_);
v___x_2701_ = v_reuseFailAlloc_2705_;
goto v_reusejp_2700_;
}
v_reusejp_2700_:
{
lean_object* v___x_2703_; 
lean_ctor_set_uint8(v___x_2701_, sizeof(void*)*2 + 1, v___y_2699_);
if (v_isShared_2697_ == 0)
{
lean_ctor_set(v___x_2696_, 0, v___x_2701_);
v___x_2703_ = v___x_2696_;
goto v_reusejp_2702_;
}
else
{
lean_object* v_reuseFailAlloc_2704_; 
v_reuseFailAlloc_2704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2704_, 0, v___x_2701_);
v___x_2703_ = v_reuseFailAlloc_2704_;
goto v_reusejp_2702_;
}
v_reusejp_2702_:
{
return v___x_2703_;
}
}
}
}
}
else
{
lean_object* v_a_2707_; lean_object* v___x_2709_; uint8_t v_isShared_2710_; uint8_t v_isSharedCheck_2714_; 
lean_del_object(v___x_2691_);
lean_dec_ref(v_e_x27_2686_);
v_a_2707_ = lean_ctor_get(v___x_2693_, 0);
v_isSharedCheck_2714_ = !lean_is_exclusive(v___x_2693_);
if (v_isSharedCheck_2714_ == 0)
{
v___x_2709_ = v___x_2693_;
v_isShared_2710_ = v_isSharedCheck_2714_;
goto v_resetjp_2708_;
}
else
{
lean_inc(v_a_2707_);
lean_dec(v___x_2693_);
v___x_2709_ = lean_box(0);
v_isShared_2710_ = v_isSharedCheck_2714_;
goto v_resetjp_2708_;
}
v_resetjp_2708_:
{
lean_object* v___x_2712_; 
if (v_isShared_2710_ == 0)
{
v___x_2712_ = v___x_2709_;
goto v_reusejp_2711_;
}
else
{
lean_object* v_reuseFailAlloc_2713_; 
v_reuseFailAlloc_2713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2713_, 0, v_a_2707_);
v___x_2712_ = v_reuseFailAlloc_2713_;
goto v_reusejp_2711_;
}
v_reusejp_2711_:
{
return v___x_2712_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_2669_);
lean_dec_ref(v_proof_2666_);
lean_dec_ref(v_e_x27_2665_);
lean_dec(v___y_2642_);
lean_dec_ref(v___y_2641_);
lean_dec(v___y_2640_);
lean_dec_ref(v___y_2639_);
lean_dec(v___y_2638_);
lean_dec_ref(v___y_2633_);
return v___x_2671_;
}
}
}
else
{
lean_dec_ref(v_a_2645_);
lean_dec(v___y_2642_);
lean_dec_ref(v___y_2641_);
lean_dec(v___y_2640_);
lean_dec_ref(v___y_2639_);
lean_dec(v___y_2638_);
lean_dec_ref(v___y_2637_);
lean_dec(v___y_2636_);
lean_dec_ref(v___y_2635_);
lean_dec(v___y_2634_);
lean_dec_ref(v___y_2633_);
lean_dec_ref(v___f_2632_);
return v___x_2644_;
}
}
}
else
{
lean_dec(v___y_2642_);
lean_dec_ref(v___y_2641_);
lean_dec(v___y_2640_);
lean_dec_ref(v___y_2639_);
lean_dec(v___y_2638_);
lean_dec_ref(v___y_2637_);
lean_dec(v___y_2636_);
lean_dec_ref(v___y_2635_);
lean_dec(v___y_2634_);
lean_dec_ref(v___y_2633_);
lean_dec_ref(v___f_2632_);
return v___x_2644_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkDefaultMethods___lam__1___boxed(lean_object* v___x_2718_, lean_object* v___f_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_){
_start:
{
lean_object* v_res_2731_; 
v_res_2731_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkDefaultMethods___lam__1(v___x_2718_, v___f_2719_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_);
lean_dec(v___x_2718_);
return v_res_2731_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkDefaultMethods___lam__0(lean_object* v_x_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_){
_start:
{
lean_object* v___x_2745_; lean_object* v___x_2746_; 
v___x_2745_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkDefaultMethods___lam__0___closed__0));
v___x_2746_ = l_Lean_Meta_Sym_Simp_simpArrowTelescope(v___x_2745_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_, v___y_2740_, v___y_2741_, v___y_2742_, v___y_2743_);
return v___x_2746_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkDefaultMethods___lam__0___boxed(lean_object* v_x_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_){
_start:
{
lean_object* v_res_2759_; 
v_res_2759_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkDefaultMethods___lam__0(v_x_2747_, v___y_2748_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_, v___y_2753_, v___y_2754_, v___y_2755_, v___y_2756_, v___y_2757_);
lean_dec(v___y_2757_);
lean_dec_ref(v___y_2756_);
lean_dec(v___y_2755_);
lean_dec_ref(v___y_2754_);
lean_dec(v___y_2753_);
lean_dec_ref(v___y_2752_);
lean_dec(v___y_2751_);
lean_dec_ref(v___y_2750_);
lean_dec(v___y_2749_);
return v_res_2759_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkDefaultMethods___lam__2(lean_object* v___f_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_){
_start:
{
lean_object* v___x_2772_; 
lean_inc_ref(v___y_2761_);
v___x_2772_ = l_Lean_Meta_Sym_Simp_simpControl(v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_, v___y_2765_, v___y_2766_, v___y_2767_, v___y_2768_, v___y_2769_, v___y_2770_);
if (lean_obj_tag(v___x_2772_) == 0)
{
lean_object* v_a_2773_; lean_object* v___x_2774_; 
v_a_2773_ = lean_ctor_get(v___x_2772_, 0);
lean_inc(v_a_2773_);
v___x_2774_ = lean_box(0);
if (lean_obj_tag(v_a_2773_) == 0)
{
uint8_t v_done_2775_; 
v_done_2775_ = lean_ctor_get_uint8(v_a_2773_, 0);
if (v_done_2775_ == 0)
{
uint8_t v_contextDependent_2776_; lean_object* v___x_2777_; 
lean_dec_ref(v___x_2772_);
v_contextDependent_2776_ = lean_ctor_get_uint8(v_a_2773_, 1);
lean_dec_ref(v_a_2773_);
v___x_2777_ = lean_apply_12(v___f_2760_, v___x_2774_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_, v___y_2765_, v___y_2766_, v___y_2767_, v___y_2768_, v___y_2769_, v___y_2770_, lean_box(0));
if (lean_obj_tag(v___x_2777_) == 0)
{
lean_object* v_a_2778_; uint8_t v___y_2780_; 
v_a_2778_ = lean_ctor_get(v___x_2777_, 0);
lean_inc(v_a_2778_);
if (v_contextDependent_2776_ == 0)
{
lean_dec(v_a_2778_);
return v___x_2777_;
}
else
{
if (lean_obj_tag(v_a_2778_) == 0)
{
uint8_t v_contextDependent_2790_; 
v_contextDependent_2790_ = lean_ctor_get_uint8(v_a_2778_, 1);
v___y_2780_ = v_contextDependent_2790_;
goto v___jp_2779_;
}
else
{
uint8_t v_contextDependent_2791_; 
v_contextDependent_2791_ = lean_ctor_get_uint8(v_a_2778_, sizeof(void*)*2 + 1);
v___y_2780_ = v_contextDependent_2791_;
goto v___jp_2779_;
}
}
v___jp_2779_:
{
if (v___y_2780_ == 0)
{
lean_object* v___x_2782_; uint8_t v_isShared_2783_; uint8_t v_isSharedCheck_2788_; 
v_isSharedCheck_2788_ = !lean_is_exclusive(v___x_2777_);
if (v_isSharedCheck_2788_ == 0)
{
lean_object* v_unused_2789_; 
v_unused_2789_ = lean_ctor_get(v___x_2777_, 0);
lean_dec(v_unused_2789_);
v___x_2782_ = v___x_2777_;
v_isShared_2783_ = v_isSharedCheck_2788_;
goto v_resetjp_2781_;
}
else
{
lean_dec(v___x_2777_);
v___x_2782_ = lean_box(0);
v_isShared_2783_ = v_isSharedCheck_2788_;
goto v_resetjp_2781_;
}
v_resetjp_2781_:
{
lean_object* v___x_2784_; lean_object* v___x_2786_; 
v___x_2784_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_2778_);
if (v_isShared_2783_ == 0)
{
lean_ctor_set(v___x_2782_, 0, v___x_2784_);
v___x_2786_ = v___x_2782_;
goto v_reusejp_2785_;
}
else
{
lean_object* v_reuseFailAlloc_2787_; 
v_reuseFailAlloc_2787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2787_, 0, v___x_2784_);
v___x_2786_ = v_reuseFailAlloc_2787_;
goto v_reusejp_2785_;
}
v_reusejp_2785_:
{
return v___x_2786_;
}
}
}
else
{
lean_dec(v_a_2778_);
return v___x_2777_;
}
}
}
else
{
return v___x_2777_;
}
}
else
{
lean_dec_ref(v_a_2773_);
lean_dec(v___y_2770_);
lean_dec_ref(v___y_2769_);
lean_dec(v___y_2768_);
lean_dec_ref(v___y_2767_);
lean_dec(v___y_2766_);
lean_dec_ref(v___y_2765_);
lean_dec(v___y_2764_);
lean_dec_ref(v___y_2763_);
lean_dec(v___y_2762_);
lean_dec_ref(v___y_2761_);
lean_dec_ref(v___f_2760_);
return v___x_2772_;
}
}
else
{
uint8_t v_done_2792_; 
v_done_2792_ = lean_ctor_get_uint8(v_a_2773_, sizeof(void*)*2);
if (v_done_2792_ == 0)
{
lean_object* v_e_x27_2793_; lean_object* v_proof_2794_; uint8_t v_contextDependent_2795_; lean_object* v___x_2797_; uint8_t v_isShared_2798_; uint8_t v_isSharedCheck_2845_; 
lean_dec_ref(v___x_2772_);
v_e_x27_2793_ = lean_ctor_get(v_a_2773_, 0);
v_proof_2794_ = lean_ctor_get(v_a_2773_, 1);
v_contextDependent_2795_ = lean_ctor_get_uint8(v_a_2773_, sizeof(void*)*2 + 1);
v_isSharedCheck_2845_ = !lean_is_exclusive(v_a_2773_);
if (v_isSharedCheck_2845_ == 0)
{
v___x_2797_ = v_a_2773_;
v_isShared_2798_ = v_isSharedCheck_2845_;
goto v_resetjp_2796_;
}
else
{
lean_inc(v_proof_2794_);
lean_inc(v_e_x27_2793_);
lean_dec(v_a_2773_);
v___x_2797_ = lean_box(0);
v_isShared_2798_ = v_isSharedCheck_2845_;
goto v_resetjp_2796_;
}
v_resetjp_2796_:
{
lean_object* v___x_2799_; 
lean_inc(v___y_2770_);
lean_inc_ref(v___y_2769_);
lean_inc(v___y_2768_);
lean_inc_ref(v___y_2767_);
lean_inc(v___y_2766_);
lean_inc_ref(v_e_x27_2793_);
v___x_2799_ = lean_apply_12(v___f_2760_, v___x_2774_, v_e_x27_2793_, v___y_2762_, v___y_2763_, v___y_2764_, v___y_2765_, v___y_2766_, v___y_2767_, v___y_2768_, v___y_2769_, v___y_2770_, lean_box(0));
if (lean_obj_tag(v___x_2799_) == 0)
{
lean_object* v_a_2800_; lean_object* v___x_2802_; uint8_t v_isShared_2803_; uint8_t v_isSharedCheck_2844_; 
v_a_2800_ = lean_ctor_get(v___x_2799_, 0);
v_isSharedCheck_2844_ = !lean_is_exclusive(v___x_2799_);
if (v_isSharedCheck_2844_ == 0)
{
v___x_2802_ = v___x_2799_;
v_isShared_2803_ = v_isSharedCheck_2844_;
goto v_resetjp_2801_;
}
else
{
lean_inc(v_a_2800_);
lean_dec(v___x_2799_);
v___x_2802_ = lean_box(0);
v_isShared_2803_ = v_isSharedCheck_2844_;
goto v_resetjp_2801_;
}
v_resetjp_2801_:
{
if (lean_obj_tag(v_a_2800_) == 0)
{
uint8_t v_done_2804_; uint8_t v_contextDependent_2805_; uint8_t v___y_2807_; 
lean_dec(v___y_2770_);
lean_dec_ref(v___y_2769_);
lean_dec(v___y_2768_);
lean_dec_ref(v___y_2767_);
lean_dec(v___y_2766_);
lean_dec_ref(v___y_2761_);
v_done_2804_ = lean_ctor_get_uint8(v_a_2800_, 0);
v_contextDependent_2805_ = lean_ctor_get_uint8(v_a_2800_, 1);
lean_dec_ref(v_a_2800_);
if (v_contextDependent_2795_ == 0)
{
v___y_2807_ = v_contextDependent_2805_;
goto v___jp_2806_;
}
else
{
v___y_2807_ = v_contextDependent_2795_;
goto v___jp_2806_;
}
v___jp_2806_:
{
lean_object* v___x_2809_; 
if (v_isShared_2798_ == 0)
{
v___x_2809_ = v___x_2797_;
goto v_reusejp_2808_;
}
else
{
lean_object* v_reuseFailAlloc_2813_; 
v_reuseFailAlloc_2813_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2813_, 0, v_e_x27_2793_);
lean_ctor_set(v_reuseFailAlloc_2813_, 1, v_proof_2794_);
v___x_2809_ = v_reuseFailAlloc_2813_;
goto v_reusejp_2808_;
}
v_reusejp_2808_:
{
lean_object* v___x_2811_; 
lean_ctor_set_uint8(v___x_2809_, sizeof(void*)*2, v_done_2804_);
lean_ctor_set_uint8(v___x_2809_, sizeof(void*)*2 + 1, v___y_2807_);
if (v_isShared_2803_ == 0)
{
lean_ctor_set(v___x_2802_, 0, v___x_2809_);
v___x_2811_ = v___x_2802_;
goto v_reusejp_2810_;
}
else
{
lean_object* v_reuseFailAlloc_2812_; 
v_reuseFailAlloc_2812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2812_, 0, v___x_2809_);
v___x_2811_ = v_reuseFailAlloc_2812_;
goto v_reusejp_2810_;
}
v_reusejp_2810_:
{
return v___x_2811_;
}
}
}
}
else
{
lean_object* v_e_x27_2814_; lean_object* v_proof_2815_; uint8_t v_done_2816_; uint8_t v_contextDependent_2817_; lean_object* v___x_2819_; uint8_t v_isShared_2820_; uint8_t v_isSharedCheck_2843_; 
lean_del_object(v___x_2802_);
lean_del_object(v___x_2797_);
v_e_x27_2814_ = lean_ctor_get(v_a_2800_, 0);
v_proof_2815_ = lean_ctor_get(v_a_2800_, 1);
v_done_2816_ = lean_ctor_get_uint8(v_a_2800_, sizeof(void*)*2);
v_contextDependent_2817_ = lean_ctor_get_uint8(v_a_2800_, sizeof(void*)*2 + 1);
v_isSharedCheck_2843_ = !lean_is_exclusive(v_a_2800_);
if (v_isSharedCheck_2843_ == 0)
{
v___x_2819_ = v_a_2800_;
v_isShared_2820_ = v_isSharedCheck_2843_;
goto v_resetjp_2818_;
}
else
{
lean_inc(v_proof_2815_);
lean_inc(v_e_x27_2814_);
lean_dec(v_a_2800_);
v___x_2819_ = lean_box(0);
v_isShared_2820_ = v_isSharedCheck_2843_;
goto v_resetjp_2818_;
}
v_resetjp_2818_:
{
lean_object* v___x_2821_; 
lean_inc_ref(v_e_x27_2814_);
v___x_2821_ = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(v___y_2761_, v_e_x27_2793_, v_proof_2794_, v_e_x27_2814_, v_proof_2815_, v___y_2766_, v___y_2767_, v___y_2768_, v___y_2769_, v___y_2770_);
lean_dec(v___y_2770_);
lean_dec_ref(v___y_2769_);
lean_dec(v___y_2768_);
lean_dec_ref(v___y_2767_);
lean_dec(v___y_2766_);
if (lean_obj_tag(v___x_2821_) == 0)
{
lean_object* v_a_2822_; lean_object* v___x_2824_; uint8_t v_isShared_2825_; uint8_t v_isSharedCheck_2834_; 
v_a_2822_ = lean_ctor_get(v___x_2821_, 0);
v_isSharedCheck_2834_ = !lean_is_exclusive(v___x_2821_);
if (v_isSharedCheck_2834_ == 0)
{
v___x_2824_ = v___x_2821_;
v_isShared_2825_ = v_isSharedCheck_2834_;
goto v_resetjp_2823_;
}
else
{
lean_inc(v_a_2822_);
lean_dec(v___x_2821_);
v___x_2824_ = lean_box(0);
v_isShared_2825_ = v_isSharedCheck_2834_;
goto v_resetjp_2823_;
}
v_resetjp_2823_:
{
uint8_t v___y_2827_; 
if (v_contextDependent_2795_ == 0)
{
v___y_2827_ = v_contextDependent_2817_;
goto v___jp_2826_;
}
else
{
v___y_2827_ = v_contextDependent_2795_;
goto v___jp_2826_;
}
v___jp_2826_:
{
lean_object* v___x_2829_; 
if (v_isShared_2820_ == 0)
{
lean_ctor_set(v___x_2819_, 1, v_a_2822_);
v___x_2829_ = v___x_2819_;
goto v_reusejp_2828_;
}
else
{
lean_object* v_reuseFailAlloc_2833_; 
v_reuseFailAlloc_2833_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2833_, 0, v_e_x27_2814_);
lean_ctor_set(v_reuseFailAlloc_2833_, 1, v_a_2822_);
lean_ctor_set_uint8(v_reuseFailAlloc_2833_, sizeof(void*)*2, v_done_2816_);
v___x_2829_ = v_reuseFailAlloc_2833_;
goto v_reusejp_2828_;
}
v_reusejp_2828_:
{
lean_object* v___x_2831_; 
lean_ctor_set_uint8(v___x_2829_, sizeof(void*)*2 + 1, v___y_2827_);
if (v_isShared_2825_ == 0)
{
lean_ctor_set(v___x_2824_, 0, v___x_2829_);
v___x_2831_ = v___x_2824_;
goto v_reusejp_2830_;
}
else
{
lean_object* v_reuseFailAlloc_2832_; 
v_reuseFailAlloc_2832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2832_, 0, v___x_2829_);
v___x_2831_ = v_reuseFailAlloc_2832_;
goto v_reusejp_2830_;
}
v_reusejp_2830_:
{
return v___x_2831_;
}
}
}
}
}
else
{
lean_object* v_a_2835_; lean_object* v___x_2837_; uint8_t v_isShared_2838_; uint8_t v_isSharedCheck_2842_; 
lean_del_object(v___x_2819_);
lean_dec_ref(v_e_x27_2814_);
v_a_2835_ = lean_ctor_get(v___x_2821_, 0);
v_isSharedCheck_2842_ = !lean_is_exclusive(v___x_2821_);
if (v_isSharedCheck_2842_ == 0)
{
v___x_2837_ = v___x_2821_;
v_isShared_2838_ = v_isSharedCheck_2842_;
goto v_resetjp_2836_;
}
else
{
lean_inc(v_a_2835_);
lean_dec(v___x_2821_);
v___x_2837_ = lean_box(0);
v_isShared_2838_ = v_isSharedCheck_2842_;
goto v_resetjp_2836_;
}
v_resetjp_2836_:
{
lean_object* v___x_2840_; 
if (v_isShared_2838_ == 0)
{
v___x_2840_ = v___x_2837_;
goto v_reusejp_2839_;
}
else
{
lean_object* v_reuseFailAlloc_2841_; 
v_reuseFailAlloc_2841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2841_, 0, v_a_2835_);
v___x_2840_ = v_reuseFailAlloc_2841_;
goto v_reusejp_2839_;
}
v_reusejp_2839_:
{
return v___x_2840_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_2797_);
lean_dec_ref(v_proof_2794_);
lean_dec_ref(v_e_x27_2793_);
lean_dec(v___y_2770_);
lean_dec_ref(v___y_2769_);
lean_dec(v___y_2768_);
lean_dec_ref(v___y_2767_);
lean_dec(v___y_2766_);
lean_dec_ref(v___y_2761_);
return v___x_2799_;
}
}
}
else
{
lean_dec_ref(v_a_2773_);
lean_dec(v___y_2770_);
lean_dec_ref(v___y_2769_);
lean_dec(v___y_2768_);
lean_dec_ref(v___y_2767_);
lean_dec(v___y_2766_);
lean_dec_ref(v___y_2765_);
lean_dec(v___y_2764_);
lean_dec_ref(v___y_2763_);
lean_dec(v___y_2762_);
lean_dec_ref(v___y_2761_);
lean_dec_ref(v___f_2760_);
return v___x_2772_;
}
}
}
else
{
lean_dec(v___y_2770_);
lean_dec_ref(v___y_2769_);
lean_dec(v___y_2768_);
lean_dec_ref(v___y_2767_);
lean_dec(v___y_2766_);
lean_dec_ref(v___y_2765_);
lean_dec(v___y_2764_);
lean_dec_ref(v___y_2763_);
lean_dec(v___y_2762_);
lean_dec_ref(v___y_2761_);
lean_dec_ref(v___f_2760_);
return v___x_2772_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkDefaultMethods___lam__2___boxed(lean_object* v___f_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_){
_start:
{
lean_object* v_res_2858_; 
v_res_2858_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkDefaultMethods___lam__2(v___f_2846_, v___y_2847_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_, v___y_2855_, v___y_2856_);
return v_res_2858_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkDefaultMethods(lean_object* v_extraThms_2862_, lean_object* v_a_2863_, lean_object* v_a_2864_, lean_object* v_a_2865_, lean_object* v_a_2866_, lean_object* v_a_2867_, lean_object* v_a_2868_, lean_object* v_a_2869_, lean_object* v_a_2870_){
_start:
{
lean_object* v___x_2872_; 
v___x_2872_ = l_Lean_Meta_Sym_Simp_getSymSimpTheorems___redArg(v_a_2870_);
if (lean_obj_tag(v___x_2872_) == 0)
{
lean_object* v_a_2873_; lean_object* v___f_2874_; lean_object* v___x_2875_; lean_object* v___f_2876_; lean_object* v___x_2877_; 
v_a_2873_ = lean_ctor_get(v___x_2872_, 0);
lean_inc(v_a_2873_);
lean_dec_ref(v___x_2872_);
v___f_2874_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___lam__0___boxed), 13, 1);
lean_closure_set(v___f_2874_, 0, v_a_2873_);
v___x_2875_ = lean_unsigned_to_nat(255u);
v___f_2876_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkDefaultMethods___lam__1___boxed), 13, 2);
lean_closure_set(v___f_2876_, 0, v___x_2875_);
lean_closure_set(v___f_2876_, 1, v___f_2874_);
v___x_2877_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems(v___f_2876_, v_extraThms_2862_, v_a_2863_, v_a_2864_, v_a_2865_, v_a_2866_, v_a_2867_, v_a_2868_, v_a_2869_, v_a_2870_);
if (lean_obj_tag(v___x_2877_) == 0)
{
lean_object* v_a_2878_; lean_object* v___x_2880_; uint8_t v_isShared_2881_; uint8_t v_isSharedCheck_2887_; 
v_a_2878_ = lean_ctor_get(v___x_2877_, 0);
v_isSharedCheck_2887_ = !lean_is_exclusive(v___x_2877_);
if (v_isSharedCheck_2887_ == 0)
{
v___x_2880_ = v___x_2877_;
v_isShared_2881_ = v_isSharedCheck_2887_;
goto v_resetjp_2879_;
}
else
{
lean_inc(v_a_2878_);
lean_dec(v___x_2877_);
v___x_2880_ = lean_box(0);
v_isShared_2881_ = v_isSharedCheck_2887_;
goto v_resetjp_2879_;
}
v_resetjp_2879_:
{
lean_object* v___f_2882_; lean_object* v___x_2883_; lean_object* v___x_2885_; 
v___f_2882_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkDefaultMethods___closed__1));
v___x_2883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2883_, 0, v___f_2882_);
lean_ctor_set(v___x_2883_, 1, v_a_2878_);
if (v_isShared_2881_ == 0)
{
lean_ctor_set(v___x_2880_, 0, v___x_2883_);
v___x_2885_ = v___x_2880_;
goto v_reusejp_2884_;
}
else
{
lean_object* v_reuseFailAlloc_2886_; 
v_reuseFailAlloc_2886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2886_, 0, v___x_2883_);
v___x_2885_ = v_reuseFailAlloc_2886_;
goto v_reusejp_2884_;
}
v_reusejp_2884_:
{
return v___x_2885_;
}
}
}
else
{
lean_object* v_a_2888_; lean_object* v___x_2890_; uint8_t v_isShared_2891_; uint8_t v_isSharedCheck_2895_; 
v_a_2888_ = lean_ctor_get(v___x_2877_, 0);
v_isSharedCheck_2895_ = !lean_is_exclusive(v___x_2877_);
if (v_isSharedCheck_2895_ == 0)
{
v___x_2890_ = v___x_2877_;
v_isShared_2891_ = v_isSharedCheck_2895_;
goto v_resetjp_2889_;
}
else
{
lean_inc(v_a_2888_);
lean_dec(v___x_2877_);
v___x_2890_ = lean_box(0);
v_isShared_2891_ = v_isSharedCheck_2895_;
goto v_resetjp_2889_;
}
v_resetjp_2889_:
{
lean_object* v___x_2893_; 
if (v_isShared_2891_ == 0)
{
v___x_2893_ = v___x_2890_;
goto v_reusejp_2892_;
}
else
{
lean_object* v_reuseFailAlloc_2894_; 
v_reuseFailAlloc_2894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2894_, 0, v_a_2888_);
v___x_2893_ = v_reuseFailAlloc_2894_;
goto v_reusejp_2892_;
}
v_reusejp_2892_:
{
return v___x_2893_;
}
}
}
}
else
{
lean_object* v_a_2896_; lean_object* v___x_2898_; uint8_t v_isShared_2899_; uint8_t v_isSharedCheck_2903_; 
v_a_2896_ = lean_ctor_get(v___x_2872_, 0);
v_isSharedCheck_2903_ = !lean_is_exclusive(v___x_2872_);
if (v_isSharedCheck_2903_ == 0)
{
v___x_2898_ = v___x_2872_;
v_isShared_2899_ = v_isSharedCheck_2903_;
goto v_resetjp_2897_;
}
else
{
lean_inc(v_a_2896_);
lean_dec(v___x_2872_);
v___x_2898_ = lean_box(0);
v_isShared_2899_ = v_isSharedCheck_2903_;
goto v_resetjp_2897_;
}
v_resetjp_2897_:
{
lean_object* v___x_2901_; 
if (v_isShared_2899_ == 0)
{
v___x_2901_ = v___x_2898_;
goto v_reusejp_2900_;
}
else
{
lean_object* v_reuseFailAlloc_2902_; 
v_reuseFailAlloc_2902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2902_, 0, v_a_2896_);
v___x_2901_ = v_reuseFailAlloc_2902_;
goto v_reusejp_2900_;
}
v_reusejp_2900_:
{
return v___x_2901_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkDefaultMethods___boxed(lean_object* v_extraThms_2904_, lean_object* v_a_2905_, lean_object* v_a_2906_, lean_object* v_a_2907_, lean_object* v_a_2908_, lean_object* v_a_2909_, lean_object* v_a_2910_, lean_object* v_a_2911_, lean_object* v_a_2912_, lean_object* v_a_2913_){
_start:
{
lean_object* v_res_2914_; 
v_res_2914_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkDefaultMethods(v_extraThms_2904_, v_a_2905_, v_a_2906_, v_a_2907_, v_a_2908_, v_a_2909_, v_a_2910_, v_a_2911_, v_a_2912_);
lean_dec(v_a_2912_);
lean_dec_ref(v_a_2911_);
lean_dec(v_a_2910_);
lean_dec_ref(v_a_2909_);
lean_dec(v_a_2908_);
lean_dec_ref(v_a_2907_);
lean_dec(v_a_2906_);
lean_dec_ref(v_a_2905_);
lean_dec_ref(v_extraThms_2904_);
return v_res_2914_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabVariant___closed__1(void){
_start:
{
lean_object* v___x_2916_; lean_object* v___x_2917_; 
v___x_2916_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabVariant___closed__0));
v___x_2917_ = l_Lean_stringToMessageData(v___x_2916_);
return v___x_2917_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabVariant___closed__3(void){
_start:
{
lean_object* v___x_2919_; lean_object* v___x_2920_; 
v___x_2919_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabVariant___closed__2));
v___x_2920_ = l_Lean_stringToMessageData(v___x_2919_);
return v___x_2920_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabVariant(lean_object* v_variantName_2924_, lean_object* v_extraThms_2925_, lean_object* v_a_2926_, lean_object* v_a_2927_, lean_object* v_a_2928_, lean_object* v_a_2929_, lean_object* v_a_2930_, lean_object* v_a_2931_, lean_object* v_a_2932_, lean_object* v_a_2933_){
_start:
{
uint8_t v___x_2935_; 
v___x_2935_ = l_Lean_Name_isAnonymous(v_variantName_2924_);
if (v___x_2935_ == 0)
{
lean_object* v___x_2936_; lean_object* v_env_2937_; lean_object* v___x_2938_; 
v___x_2936_ = lean_st_ref_get(v_a_2933_);
v_env_2937_ = lean_ctor_get(v___x_2936_, 0);
lean_inc_ref(v_env_2937_);
lean_dec(v___x_2936_);
v___x_2938_ = l_Lean_Meta_Sym_Simp_getSymSimpVariant_x3f(v_env_2937_, v_variantName_2924_);
if (lean_obj_tag(v___x_2938_) == 1)
{
lean_object* v_val_2939_; lean_object* v_pre_x3f_2940_; lean_object* v_post_x3f_2941_; lean_object* v_config_2942_; lean_object* v___x_2943_; 
lean_dec(v_variantName_2924_);
v_val_2939_ = lean_ctor_get(v___x_2938_, 0);
lean_inc(v_val_2939_);
lean_dec_ref(v___x_2938_);
v_pre_x3f_2940_ = lean_ctor_get(v_val_2939_, 0);
lean_inc(v_pre_x3f_2940_);
v_post_x3f_2941_ = lean_ctor_get(v_val_2939_, 1);
lean_inc(v_post_x3f_2941_);
v_config_2942_ = lean_ctor_get(v_val_2939_, 2);
lean_inc_ref(v_config_2942_);
lean_dec(v_val_2939_);
v___x_2943_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabOptSimproc(v_pre_x3f_2940_, v_a_2926_, v_a_2927_, v_a_2928_, v_a_2929_, v_a_2930_, v_a_2931_, v_a_2932_, v_a_2933_);
if (lean_obj_tag(v___x_2943_) == 0)
{
lean_object* v_a_2944_; lean_object* v___x_2945_; 
v_a_2944_ = lean_ctor_get(v___x_2943_, 0);
lean_inc(v_a_2944_);
lean_dec_ref(v___x_2943_);
v___x_2945_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabOptSimproc(v_post_x3f_2941_, v_a_2926_, v_a_2927_, v_a_2928_, v_a_2929_, v_a_2930_, v_a_2931_, v_a_2932_, v_a_2933_);
if (lean_obj_tag(v___x_2945_) == 0)
{
lean_object* v_a_2946_; lean_object* v___x_2947_; 
v_a_2946_ = lean_ctor_get(v___x_2945_, 0);
lean_inc(v_a_2946_);
lean_dec_ref(v___x_2945_);
v___x_2947_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems(v_a_2946_, v_extraThms_2925_, v_a_2926_, v_a_2927_, v_a_2928_, v_a_2929_, v_a_2930_, v_a_2931_, v_a_2932_, v_a_2933_);
if (lean_obj_tag(v___x_2947_) == 0)
{
lean_object* v_a_2948_; lean_object* v___x_2950_; uint8_t v_isShared_2951_; uint8_t v_isSharedCheck_2957_; 
v_a_2948_ = lean_ctor_get(v___x_2947_, 0);
v_isSharedCheck_2957_ = !lean_is_exclusive(v___x_2947_);
if (v_isSharedCheck_2957_ == 0)
{
v___x_2950_ = v___x_2947_;
v_isShared_2951_ = v_isSharedCheck_2957_;
goto v_resetjp_2949_;
}
else
{
lean_inc(v_a_2948_);
lean_dec(v___x_2947_);
v___x_2950_ = lean_box(0);
v_isShared_2951_ = v_isSharedCheck_2957_;
goto v_resetjp_2949_;
}
v_resetjp_2949_:
{
lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2955_; 
v___x_2952_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2952_, 0, v_a_2944_);
lean_ctor_set(v___x_2952_, 1, v_a_2948_);
v___x_2953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2953_, 0, v___x_2952_);
lean_ctor_set(v___x_2953_, 1, v_config_2942_);
if (v_isShared_2951_ == 0)
{
lean_ctor_set(v___x_2950_, 0, v___x_2953_);
v___x_2955_ = v___x_2950_;
goto v_reusejp_2954_;
}
else
{
lean_object* v_reuseFailAlloc_2956_; 
v_reuseFailAlloc_2956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2956_, 0, v___x_2953_);
v___x_2955_ = v_reuseFailAlloc_2956_;
goto v_reusejp_2954_;
}
v_reusejp_2954_:
{
return v___x_2955_;
}
}
}
else
{
lean_object* v_a_2958_; lean_object* v___x_2960_; uint8_t v_isShared_2961_; uint8_t v_isSharedCheck_2965_; 
lean_dec(v_a_2944_);
lean_dec_ref(v_config_2942_);
v_a_2958_ = lean_ctor_get(v___x_2947_, 0);
v_isSharedCheck_2965_ = !lean_is_exclusive(v___x_2947_);
if (v_isSharedCheck_2965_ == 0)
{
v___x_2960_ = v___x_2947_;
v_isShared_2961_ = v_isSharedCheck_2965_;
goto v_resetjp_2959_;
}
else
{
lean_inc(v_a_2958_);
lean_dec(v___x_2947_);
v___x_2960_ = lean_box(0);
v_isShared_2961_ = v_isSharedCheck_2965_;
goto v_resetjp_2959_;
}
v_resetjp_2959_:
{
lean_object* v___x_2963_; 
if (v_isShared_2961_ == 0)
{
v___x_2963_ = v___x_2960_;
goto v_reusejp_2962_;
}
else
{
lean_object* v_reuseFailAlloc_2964_; 
v_reuseFailAlloc_2964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2964_, 0, v_a_2958_);
v___x_2963_ = v_reuseFailAlloc_2964_;
goto v_reusejp_2962_;
}
v_reusejp_2962_:
{
return v___x_2963_;
}
}
}
}
else
{
lean_object* v_a_2966_; lean_object* v___x_2968_; uint8_t v_isShared_2969_; uint8_t v_isSharedCheck_2973_; 
lean_dec(v_a_2944_);
lean_dec_ref(v_config_2942_);
v_a_2966_ = lean_ctor_get(v___x_2945_, 0);
v_isSharedCheck_2973_ = !lean_is_exclusive(v___x_2945_);
if (v_isSharedCheck_2973_ == 0)
{
v___x_2968_ = v___x_2945_;
v_isShared_2969_ = v_isSharedCheck_2973_;
goto v_resetjp_2967_;
}
else
{
lean_inc(v_a_2966_);
lean_dec(v___x_2945_);
v___x_2968_ = lean_box(0);
v_isShared_2969_ = v_isSharedCheck_2973_;
goto v_resetjp_2967_;
}
v_resetjp_2967_:
{
lean_object* v___x_2971_; 
if (v_isShared_2969_ == 0)
{
v___x_2971_ = v___x_2968_;
goto v_reusejp_2970_;
}
else
{
lean_object* v_reuseFailAlloc_2972_; 
v_reuseFailAlloc_2972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2972_, 0, v_a_2966_);
v___x_2971_ = v_reuseFailAlloc_2972_;
goto v_reusejp_2970_;
}
v_reusejp_2970_:
{
return v___x_2971_;
}
}
}
}
else
{
lean_object* v_a_2974_; lean_object* v___x_2976_; uint8_t v_isShared_2977_; uint8_t v_isSharedCheck_2981_; 
lean_dec_ref(v_config_2942_);
lean_dec(v_post_x3f_2941_);
v_a_2974_ = lean_ctor_get(v___x_2943_, 0);
v_isSharedCheck_2981_ = !lean_is_exclusive(v___x_2943_);
if (v_isSharedCheck_2981_ == 0)
{
v___x_2976_ = v___x_2943_;
v_isShared_2977_ = v_isSharedCheck_2981_;
goto v_resetjp_2975_;
}
else
{
lean_inc(v_a_2974_);
lean_dec(v___x_2943_);
v___x_2976_ = lean_box(0);
v_isShared_2977_ = v_isSharedCheck_2981_;
goto v_resetjp_2975_;
}
v_resetjp_2975_:
{
lean_object* v___x_2979_; 
if (v_isShared_2977_ == 0)
{
v___x_2979_ = v___x_2976_;
goto v_reusejp_2978_;
}
else
{
lean_object* v_reuseFailAlloc_2980_; 
v_reuseFailAlloc_2980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2980_, 0, v_a_2974_);
v___x_2979_ = v_reuseFailAlloc_2980_;
goto v_reusejp_2978_;
}
v_reusejp_2978_:
{
return v___x_2979_;
}
}
}
}
else
{
lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; 
lean_dec(v___x_2938_);
v___x_2982_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabVariant___closed__1, &l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabVariant___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabVariant___closed__1);
v___x_2983_ = l_Lean_MessageData_ofName(v_variantName_2924_);
v___x_2984_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2984_, 0, v___x_2982_);
lean_ctor_set(v___x_2984_, 1, v___x_2983_);
v___x_2985_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabVariant___closed__3, &l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabVariant___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabVariant___closed__3);
v___x_2986_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2986_, 0, v___x_2984_);
lean_ctor_set(v___x_2986_, 1, v___x_2985_);
v___x_2987_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_ensureSym_spec__0___redArg(v___x_2986_, v_a_2930_, v_a_2931_, v_a_2932_, v_a_2933_);
return v___x_2987_;
}
}
else
{
lean_object* v___x_2988_; 
lean_dec(v_variantName_2924_);
v___x_2988_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkDefaultMethods(v_extraThms_2925_, v_a_2926_, v_a_2927_, v_a_2928_, v_a_2929_, v_a_2930_, v_a_2931_, v_a_2932_, v_a_2933_);
if (lean_obj_tag(v___x_2988_) == 0)
{
lean_object* v_a_2989_; lean_object* v___x_2991_; uint8_t v_isShared_2992_; uint8_t v_isSharedCheck_2998_; 
v_a_2989_ = lean_ctor_get(v___x_2988_, 0);
v_isSharedCheck_2998_ = !lean_is_exclusive(v___x_2988_);
if (v_isSharedCheck_2998_ == 0)
{
v___x_2991_ = v___x_2988_;
v_isShared_2992_ = v_isSharedCheck_2998_;
goto v_resetjp_2990_;
}
else
{
lean_inc(v_a_2989_);
lean_dec(v___x_2988_);
v___x_2991_ = lean_box(0);
v_isShared_2992_ = v_isSharedCheck_2998_;
goto v_resetjp_2990_;
}
v_resetjp_2990_:
{
lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2996_; 
v___x_2993_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabVariant___closed__4));
v___x_2994_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2994_, 0, v_a_2989_);
lean_ctor_set(v___x_2994_, 1, v___x_2993_);
if (v_isShared_2992_ == 0)
{
lean_ctor_set(v___x_2991_, 0, v___x_2994_);
v___x_2996_ = v___x_2991_;
goto v_reusejp_2995_;
}
else
{
lean_object* v_reuseFailAlloc_2997_; 
v_reuseFailAlloc_2997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2997_, 0, v___x_2994_);
v___x_2996_ = v_reuseFailAlloc_2997_;
goto v_reusejp_2995_;
}
v_reusejp_2995_:
{
return v___x_2996_;
}
}
}
else
{
lean_object* v_a_2999_; lean_object* v___x_3001_; uint8_t v_isShared_3002_; uint8_t v_isSharedCheck_3006_; 
v_a_2999_ = lean_ctor_get(v___x_2988_, 0);
v_isSharedCheck_3006_ = !lean_is_exclusive(v___x_2988_);
if (v_isSharedCheck_3006_ == 0)
{
v___x_3001_ = v___x_2988_;
v_isShared_3002_ = v_isSharedCheck_3006_;
goto v_resetjp_3000_;
}
else
{
lean_inc(v_a_2999_);
lean_dec(v___x_2988_);
v___x_3001_ = lean_box(0);
v_isShared_3002_ = v_isSharedCheck_3006_;
goto v_resetjp_3000_;
}
v_resetjp_3000_:
{
lean_object* v___x_3004_; 
if (v_isShared_3002_ == 0)
{
v___x_3004_ = v___x_3001_;
goto v_reusejp_3003_;
}
else
{
lean_object* v_reuseFailAlloc_3005_; 
v_reuseFailAlloc_3005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3005_, 0, v_a_2999_);
v___x_3004_ = v_reuseFailAlloc_3005_;
goto v_reusejp_3003_;
}
v_reusejp_3003_:
{
return v___x_3004_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabVariant___boxed(lean_object* v_variantName_3007_, lean_object* v_extraThms_3008_, lean_object* v_a_3009_, lean_object* v_a_3010_, lean_object* v_a_3011_, lean_object* v_a_3012_, lean_object* v_a_3013_, lean_object* v_a_3014_, lean_object* v_a_3015_, lean_object* v_a_3016_, lean_object* v_a_3017_){
_start:
{
lean_object* v_res_3018_; 
v_res_3018_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabVariant(v_variantName_3007_, v_extraThms_3008_, v_a_3009_, v_a_3010_, v_a_3011_, v_a_3012_, v_a_3013_, v_a_3014_, v_a_3015_, v_a_3016_);
lean_dec(v_a_3016_);
lean_dec_ref(v_a_3015_);
lean_dec(v_a_3014_);
lean_dec_ref(v_a_3013_);
lean_dec(v_a_3012_);
lean_dec_ref(v_a_3011_);
lean_dec(v_a_3010_);
lean_dec_ref(v_a_3009_);
lean_dec_ref(v_extraThms_3008_);
return v_res_3018_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__0___redArg___lam__0(lean_object* v_x_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_){
_start:
{
lean_object* v___x_3030_; 
lean_inc(v___y_3024_);
lean_inc_ref(v___y_3023_);
lean_inc(v___y_3022_);
lean_inc_ref(v___y_3021_);
lean_inc(v___y_3020_);
v___x_3030_ = lean_apply_10(v_x_3019_, v___y_3020_, v___y_3021_, v___y_3022_, v___y_3023_, v___y_3024_, v___y_3025_, v___y_3026_, v___y_3027_, v___y_3028_, lean_box(0));
return v___x_3030_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__0___redArg___lam__0___boxed(lean_object* v_x_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_){
_start:
{
lean_object* v_res_3042_; 
v_res_3042_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__0___redArg___lam__0(v_x_3031_, v___y_3032_, v___y_3033_, v___y_3034_, v___y_3035_, v___y_3036_, v___y_3037_, v___y_3038_, v___y_3039_, v___y_3040_);
lean_dec(v___y_3036_);
lean_dec_ref(v___y_3035_);
lean_dec(v___y_3034_);
lean_dec_ref(v___y_3033_);
lean_dec(v___y_3032_);
return v_res_3042_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__0___redArg(lean_object* v_mvarId_3043_, lean_object* v_x_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_){
_start:
{
lean_object* v___f_3055_; lean_object* v___x_3056_; 
lean_inc(v___y_3049_);
lean_inc_ref(v___y_3048_);
lean_inc(v___y_3047_);
lean_inc_ref(v___y_3046_);
lean_inc(v___y_3045_);
v___f_3055_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__0___redArg___lam__0___boxed), 11, 6);
lean_closure_set(v___f_3055_, 0, v_x_3044_);
lean_closure_set(v___f_3055_, 1, v___y_3045_);
lean_closure_set(v___f_3055_, 2, v___y_3046_);
lean_closure_set(v___f_3055_, 3, v___y_3047_);
lean_closure_set(v___f_3055_, 4, v___y_3048_);
lean_closure_set(v___f_3055_, 5, v___y_3049_);
v___x_3056_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_3043_, v___f_3055_, v___y_3050_, v___y_3051_, v___y_3052_, v___y_3053_);
if (lean_obj_tag(v___x_3056_) == 0)
{
return v___x_3056_;
}
else
{
lean_object* v_a_3057_; lean_object* v___x_3059_; uint8_t v_isShared_3060_; uint8_t v_isSharedCheck_3064_; 
v_a_3057_ = lean_ctor_get(v___x_3056_, 0);
v_isSharedCheck_3064_ = !lean_is_exclusive(v___x_3056_);
if (v_isSharedCheck_3064_ == 0)
{
v___x_3059_ = v___x_3056_;
v_isShared_3060_ = v_isSharedCheck_3064_;
goto v_resetjp_3058_;
}
else
{
lean_inc(v_a_3057_);
lean_dec(v___x_3056_);
v___x_3059_ = lean_box(0);
v_isShared_3060_ = v_isSharedCheck_3064_;
goto v_resetjp_3058_;
}
v_resetjp_3058_:
{
lean_object* v___x_3062_; 
if (v_isShared_3060_ == 0)
{
v___x_3062_ = v___x_3059_;
goto v_reusejp_3061_;
}
else
{
lean_object* v_reuseFailAlloc_3063_; 
v_reuseFailAlloc_3063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3063_, 0, v_a_3057_);
v___x_3062_ = v_reuseFailAlloc_3063_;
goto v_reusejp_3061_;
}
v_reusejp_3061_:
{
return v___x_3062_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__0___redArg___boxed(lean_object* v_mvarId_3065_, lean_object* v_x_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_){
_start:
{
lean_object* v_res_3077_; 
v_res_3077_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__0___redArg(v_mvarId_3065_, v_x_3066_, v___y_3067_, v___y_3068_, v___y_3069_, v___y_3070_, v___y_3071_, v___y_3072_, v___y_3073_, v___y_3074_, v___y_3075_);
lean_dec(v___y_3075_);
lean_dec_ref(v___y_3074_);
lean_dec(v___y_3073_);
lean_dec_ref(v___y_3072_);
lean_dec(v___y_3071_);
lean_dec_ref(v___y_3070_);
lean_dec(v___y_3069_);
lean_dec_ref(v___y_3068_);
lean_dec(v___y_3067_);
return v_res_3077_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__0(lean_object* v_00_u03b1_3078_, lean_object* v_mvarId_3079_, lean_object* v_x_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_){
_start:
{
lean_object* v___x_3091_; 
v___x_3091_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__0___redArg(v_mvarId_3079_, v_x_3080_, v___y_3081_, v___y_3082_, v___y_3083_, v___y_3084_, v___y_3085_, v___y_3086_, v___y_3087_, v___y_3088_, v___y_3089_);
return v___x_3091_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__0___boxed(lean_object* v_00_u03b1_3092_, lean_object* v_mvarId_3093_, lean_object* v_x_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_){
_start:
{
lean_object* v_res_3105_; 
v_res_3105_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__0(v_00_u03b1_3092_, v_mvarId_3093_, v_x_3094_, v___y_3095_, v___y_3096_, v___y_3097_, v___y_3098_, v___y_3099_, v___y_3100_, v___y_3101_, v___y_3102_, v___y_3103_);
lean_dec(v___y_3103_);
lean_dec_ref(v___y_3102_);
lean_dec(v___y_3101_);
lean_dec_ref(v___y_3100_);
lean_dec(v___y_3099_);
lean_dec_ref(v___y_3098_);
lean_dec(v___y_3097_);
lean_dec_ref(v___y_3096_);
lean_dec(v___y_3095_);
return v_res_3105_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__0(lean_object* v_mvarId_3106_, lean_object* v_fst_3107_, lean_object* v_snd_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_){
_start:
{
lean_object* v___x_3120_; 
v___x_3120_ = l_Lean_MVarId_getType(v_mvarId_3106_, v___y_3115_, v___y_3116_, v___y_3117_, v___y_3118_);
if (lean_obj_tag(v___x_3120_) == 0)
{
lean_object* v_a_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; 
v_a_3121_ = lean_ctor_get(v___x_3120_, 0);
lean_inc(v_a_3121_);
lean_dec_ref(v___x_3120_);
v___x_3122_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simp___boxed), 11, 1);
lean_closure_set(v___x_3122_, 0, v_a_3121_);
v___x_3123_ = l_Lean_Meta_Sym_Simp_SimpM_run___redArg(v___x_3122_, v_fst_3107_, v_snd_3108_, v___y_3109_, v___y_3113_, v___y_3114_, v___y_3115_, v___y_3116_, v___y_3117_, v___y_3118_);
return v___x_3123_;
}
else
{
lean_object* v_a_3124_; lean_object* v___x_3126_; uint8_t v_isShared_3127_; uint8_t v_isSharedCheck_3131_; 
lean_dec_ref(v___y_3109_);
lean_dec_ref(v_snd_3108_);
lean_dec_ref(v_fst_3107_);
v_a_3124_ = lean_ctor_get(v___x_3120_, 0);
v_isSharedCheck_3131_ = !lean_is_exclusive(v___x_3120_);
if (v_isSharedCheck_3131_ == 0)
{
v___x_3126_ = v___x_3120_;
v_isShared_3127_ = v_isSharedCheck_3131_;
goto v_resetjp_3125_;
}
else
{
lean_inc(v_a_3124_);
lean_dec(v___x_3120_);
v___x_3126_ = lean_box(0);
v_isShared_3127_ = v_isSharedCheck_3131_;
goto v_resetjp_3125_;
}
v_resetjp_3125_:
{
lean_object* v___x_3129_; 
if (v_isShared_3127_ == 0)
{
v___x_3129_ = v___x_3126_;
goto v_reusejp_3128_;
}
else
{
lean_object* v_reuseFailAlloc_3130_; 
v_reuseFailAlloc_3130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3130_, 0, v_a_3124_);
v___x_3129_ = v_reuseFailAlloc_3130_;
goto v_reusejp_3128_;
}
v_reusejp_3128_:
{
return v___x_3129_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__0___boxed(lean_object* v_mvarId_3132_, lean_object* v_fst_3133_, lean_object* v_snd_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_){
_start:
{
lean_object* v_res_3146_; 
v_res_3146_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__0(v_mvarId_3132_, v_fst_3133_, v_snd_3134_, v___y_3135_, v___y_3136_, v___y_3137_, v___y_3138_, v___y_3139_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_, v___y_3144_);
lean_dec(v___y_3144_);
lean_dec_ref(v___y_3143_);
lean_dec(v___y_3142_);
lean_dec_ref(v___y_3141_);
lean_dec(v___y_3140_);
lean_dec_ref(v___y_3139_);
lean_dec(v___y_3138_);
lean_dec_ref(v___y_3137_);
lean_dec(v___y_3136_);
return v_res_3146_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__1(lean_object* v_fst_3147_, lean_object* v_mvarId_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_){
_start:
{
lean_object* v___x_3159_; 
v___x_3159_ = l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult(v_fst_3147_, v_mvarId_3148_, v___y_3152_, v___y_3153_, v___y_3154_, v___y_3155_, v___y_3156_, v___y_3157_);
return v___x_3159_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__1___boxed(lean_object* v_fst_3160_, lean_object* v_mvarId_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_){
_start:
{
lean_object* v_res_3172_; 
v_res_3172_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__1(v_fst_3160_, v_mvarId_3161_, v___y_3162_, v___y_3163_, v___y_3164_, v___y_3165_, v___y_3166_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_);
lean_dec(v___y_3170_);
lean_dec_ref(v___y_3169_);
lean_dec(v___y_3168_);
lean_dec_ref(v___y_3167_);
lean_dec(v___y_3166_);
lean_dec_ref(v___y_3165_);
lean_dec(v___y_3164_);
lean_dec_ref(v___y_3163_);
lean_dec(v___y_3162_);
return v_res_3172_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__2_spec__5___redArg(lean_object* v_a_3173_, lean_object* v_x_3174_){
_start:
{
if (lean_obj_tag(v_x_3174_) == 0)
{
lean_object* v___x_3175_; 
v___x_3175_ = lean_box(0);
return v___x_3175_;
}
else
{
lean_object* v_key_3176_; lean_object* v_value_3177_; lean_object* v_tail_3178_; uint8_t v___x_3179_; 
v_key_3176_ = lean_ctor_get(v_x_3174_, 0);
v_value_3177_ = lean_ctor_get(v_x_3174_, 1);
v_tail_3178_ = lean_ctor_get(v_x_3174_, 2);
v___x_3179_ = l_Lean_Elab_Tactic_Grind_instBEqSimpCacheKey_beq(v_key_3176_, v_a_3173_);
if (v___x_3179_ == 0)
{
v_x_3174_ = v_tail_3178_;
goto _start;
}
else
{
lean_object* v___x_3181_; 
lean_inc(v_value_3177_);
v___x_3181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3181_, 0, v_value_3177_);
return v___x_3181_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__2_spec__5___redArg___boxed(lean_object* v_a_3182_, lean_object* v_x_3183_){
_start:
{
lean_object* v_res_3184_; 
v_res_3184_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__2_spec__5___redArg(v_a_3182_, v_x_3183_);
lean_dec(v_x_3183_);
lean_dec_ref(v_a_3182_);
return v_res_3184_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__2___redArg(lean_object* v_m_3185_, lean_object* v_a_3186_){
_start:
{
lean_object* v_buckets_3187_; lean_object* v___x_3188_; uint64_t v___x_3189_; uint64_t v___x_3190_; uint64_t v___x_3191_; uint64_t v_fold_3192_; uint64_t v___x_3193_; uint64_t v___x_3194_; uint64_t v___x_3195_; size_t v___x_3196_; size_t v___x_3197_; size_t v___x_3198_; size_t v___x_3199_; size_t v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; 
v_buckets_3187_ = lean_ctor_get(v_m_3185_, 1);
v___x_3188_ = lean_array_get_size(v_buckets_3187_);
v___x_3189_ = l_Lean_Elab_Tactic_Grind_instHashableSimpCacheKey_hash(v_a_3186_);
v___x_3190_ = 32ULL;
v___x_3191_ = lean_uint64_shift_right(v___x_3189_, v___x_3190_);
v_fold_3192_ = lean_uint64_xor(v___x_3189_, v___x_3191_);
v___x_3193_ = 16ULL;
v___x_3194_ = lean_uint64_shift_right(v_fold_3192_, v___x_3193_);
v___x_3195_ = lean_uint64_xor(v_fold_3192_, v___x_3194_);
v___x_3196_ = lean_uint64_to_usize(v___x_3195_);
v___x_3197_ = lean_usize_of_nat(v___x_3188_);
v___x_3198_ = ((size_t)1ULL);
v___x_3199_ = lean_usize_sub(v___x_3197_, v___x_3198_);
v___x_3200_ = lean_usize_land(v___x_3196_, v___x_3199_);
v___x_3201_ = lean_array_uget_borrowed(v_buckets_3187_, v___x_3200_);
v___x_3202_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__2_spec__5___redArg(v_a_3186_, v___x_3201_);
return v___x_3202_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__2___redArg___boxed(lean_object* v_m_3203_, lean_object* v_a_3204_){
_start:
{
lean_object* v_res_3205_; 
v_res_3205_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__2___redArg(v_m_3203_, v_a_3204_);
lean_dec_ref(v_a_3204_);
lean_dec_ref(v_m_3203_);
return v_res_3205_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__4(uint8_t v___x_3206_, uint8_t v___x_3207_, lean_object* v_as_3208_, size_t v_i_3209_, size_t v_stop_3210_, lean_object* v_b_3211_){
_start:
{
lean_object* v___y_3213_; uint8_t v___x_3217_; 
v___x_3217_ = lean_usize_dec_eq(v_i_3209_, v_stop_3210_);
if (v___x_3217_ == 0)
{
lean_object* v_fst_3218_; uint8_t v___x_3219_; 
v_fst_3218_ = lean_ctor_get(v_b_3211_, 0);
v___x_3219_ = lean_unbox(v_fst_3218_);
if (v___x_3219_ == 0)
{
lean_object* v_snd_3220_; lean_object* v___x_3222_; uint8_t v_isShared_3223_; uint8_t v_isSharedCheck_3228_; 
v_snd_3220_ = lean_ctor_get(v_b_3211_, 1);
v_isSharedCheck_3228_ = !lean_is_exclusive(v_b_3211_);
if (v_isSharedCheck_3228_ == 0)
{
lean_object* v_unused_3229_; 
v_unused_3229_ = lean_ctor_get(v_b_3211_, 0);
lean_dec(v_unused_3229_);
v___x_3222_ = v_b_3211_;
v_isShared_3223_ = v_isSharedCheck_3228_;
goto v_resetjp_3221_;
}
else
{
lean_inc(v_snd_3220_);
lean_dec(v_b_3211_);
v___x_3222_ = lean_box(0);
v_isShared_3223_ = v_isSharedCheck_3228_;
goto v_resetjp_3221_;
}
v_resetjp_3221_:
{
lean_object* v___x_3224_; lean_object* v___x_3226_; 
v___x_3224_ = lean_box(v___x_3206_);
if (v_isShared_3223_ == 0)
{
lean_ctor_set(v___x_3222_, 0, v___x_3224_);
v___x_3226_ = v___x_3222_;
goto v_reusejp_3225_;
}
else
{
lean_object* v_reuseFailAlloc_3227_; 
v_reuseFailAlloc_3227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3227_, 0, v___x_3224_);
lean_ctor_set(v_reuseFailAlloc_3227_, 1, v_snd_3220_);
v___x_3226_ = v_reuseFailAlloc_3227_;
goto v_reusejp_3225_;
}
v_reusejp_3225_:
{
v___y_3213_ = v___x_3226_;
goto v___jp_3212_;
}
}
}
else
{
lean_object* v_snd_3230_; lean_object* v___x_3232_; uint8_t v_isShared_3233_; uint8_t v_isSharedCheck_3240_; 
v_snd_3230_ = lean_ctor_get(v_b_3211_, 1);
v_isSharedCheck_3240_ = !lean_is_exclusive(v_b_3211_);
if (v_isSharedCheck_3240_ == 0)
{
lean_object* v_unused_3241_; 
v_unused_3241_ = lean_ctor_get(v_b_3211_, 0);
lean_dec(v_unused_3241_);
v___x_3232_ = v_b_3211_;
v_isShared_3233_ = v_isSharedCheck_3240_;
goto v_resetjp_3231_;
}
else
{
lean_inc(v_snd_3230_);
lean_dec(v_b_3211_);
v___x_3232_ = lean_box(0);
v_isShared_3233_ = v_isSharedCheck_3240_;
goto v_resetjp_3231_;
}
v_resetjp_3231_:
{
lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3238_; 
v___x_3234_ = lean_array_uget_borrowed(v_as_3208_, v_i_3209_);
lean_inc(v___x_3234_);
v___x_3235_ = lean_array_push(v_snd_3230_, v___x_3234_);
v___x_3236_ = lean_box(v___x_3207_);
if (v_isShared_3233_ == 0)
{
lean_ctor_set(v___x_3232_, 1, v___x_3235_);
lean_ctor_set(v___x_3232_, 0, v___x_3236_);
v___x_3238_ = v___x_3232_;
goto v_reusejp_3237_;
}
else
{
lean_object* v_reuseFailAlloc_3239_; 
v_reuseFailAlloc_3239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3239_, 0, v___x_3236_);
lean_ctor_set(v_reuseFailAlloc_3239_, 1, v___x_3235_);
v___x_3238_ = v_reuseFailAlloc_3239_;
goto v_reusejp_3237_;
}
v_reusejp_3237_:
{
v___y_3213_ = v___x_3238_;
goto v___jp_3212_;
}
}
}
}
else
{
return v_b_3211_;
}
v___jp_3212_:
{
size_t v___x_3214_; size_t v___x_3215_; 
v___x_3214_ = ((size_t)1ULL);
v___x_3215_ = lean_usize_add(v_i_3209_, v___x_3214_);
v_i_3209_ = v___x_3215_;
v_b_3211_ = v___y_3213_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__4___boxed(lean_object* v___x_3242_, lean_object* v___x_3243_, lean_object* v_as_3244_, lean_object* v_i_3245_, lean_object* v_stop_3246_, lean_object* v_b_3247_){
_start:
{
uint8_t v___x_9487__boxed_3248_; uint8_t v___x_9488__boxed_3249_; size_t v_i_boxed_3250_; size_t v_stop_boxed_3251_; lean_object* v_res_3252_; 
v___x_9487__boxed_3248_ = lean_unbox(v___x_3242_);
v___x_9488__boxed_3249_ = lean_unbox(v___x_3243_);
v_i_boxed_3250_ = lean_unbox_usize(v_i_3245_);
lean_dec(v_i_3245_);
v_stop_boxed_3251_ = lean_unbox_usize(v_stop_3246_);
lean_dec(v_stop_3246_);
v_res_3252_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__4(v___x_9487__boxed_3248_, v___x_9488__boxed_3249_, v_as_3244_, v_i_boxed_3250_, v_stop_boxed_3251_, v_b_3247_);
lean_dec_ref(v_as_3244_);
return v_res_3252_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__3___redArg(lean_object* v_a_3253_, lean_object* v_b_3254_, lean_object* v_x_3255_){
_start:
{
if (lean_obj_tag(v_x_3255_) == 0)
{
lean_dec(v_b_3254_);
lean_dec_ref(v_a_3253_);
return v_x_3255_;
}
else
{
lean_object* v_key_3256_; lean_object* v_value_3257_; lean_object* v_tail_3258_; lean_object* v___x_3260_; uint8_t v_isShared_3261_; uint8_t v_isSharedCheck_3270_; 
v_key_3256_ = lean_ctor_get(v_x_3255_, 0);
v_value_3257_ = lean_ctor_get(v_x_3255_, 1);
v_tail_3258_ = lean_ctor_get(v_x_3255_, 2);
v_isSharedCheck_3270_ = !lean_is_exclusive(v_x_3255_);
if (v_isSharedCheck_3270_ == 0)
{
v___x_3260_ = v_x_3255_;
v_isShared_3261_ = v_isSharedCheck_3270_;
goto v_resetjp_3259_;
}
else
{
lean_inc(v_tail_3258_);
lean_inc(v_value_3257_);
lean_inc(v_key_3256_);
lean_dec(v_x_3255_);
v___x_3260_ = lean_box(0);
v_isShared_3261_ = v_isSharedCheck_3270_;
goto v_resetjp_3259_;
}
v_resetjp_3259_:
{
uint8_t v___x_3262_; 
v___x_3262_ = l_Lean_Elab_Tactic_Grind_instBEqSimpCacheKey_beq(v_key_3256_, v_a_3253_);
if (v___x_3262_ == 0)
{
lean_object* v___x_3263_; lean_object* v___x_3265_; 
v___x_3263_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__3___redArg(v_a_3253_, v_b_3254_, v_tail_3258_);
if (v_isShared_3261_ == 0)
{
lean_ctor_set(v___x_3260_, 2, v___x_3263_);
v___x_3265_ = v___x_3260_;
goto v_reusejp_3264_;
}
else
{
lean_object* v_reuseFailAlloc_3266_; 
v_reuseFailAlloc_3266_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3266_, 0, v_key_3256_);
lean_ctor_set(v_reuseFailAlloc_3266_, 1, v_value_3257_);
lean_ctor_set(v_reuseFailAlloc_3266_, 2, v___x_3263_);
v___x_3265_ = v_reuseFailAlloc_3266_;
goto v_reusejp_3264_;
}
v_reusejp_3264_:
{
return v___x_3265_;
}
}
else
{
lean_object* v___x_3268_; 
lean_dec(v_value_3257_);
lean_dec(v_key_3256_);
if (v_isShared_3261_ == 0)
{
lean_ctor_set(v___x_3260_, 1, v_b_3254_);
lean_ctor_set(v___x_3260_, 0, v_a_3253_);
v___x_3268_ = v___x_3260_;
goto v_reusejp_3267_;
}
else
{
lean_object* v_reuseFailAlloc_3269_; 
v_reuseFailAlloc_3269_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3269_, 0, v_a_3253_);
lean_ctor_set(v_reuseFailAlloc_3269_, 1, v_b_3254_);
lean_ctor_set(v_reuseFailAlloc_3269_, 2, v_tail_3258_);
v___x_3268_ = v_reuseFailAlloc_3269_;
goto v_reusejp_3267_;
}
v_reusejp_3267_:
{
return v___x_3268_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__2_spec__3_spec__7___redArg(lean_object* v_x_3271_, lean_object* v_x_3272_){
_start:
{
if (lean_obj_tag(v_x_3272_) == 0)
{
return v_x_3271_;
}
else
{
lean_object* v_key_3273_; lean_object* v_value_3274_; lean_object* v_tail_3275_; lean_object* v___x_3277_; uint8_t v_isShared_3278_; uint8_t v_isSharedCheck_3298_; 
v_key_3273_ = lean_ctor_get(v_x_3272_, 0);
v_value_3274_ = lean_ctor_get(v_x_3272_, 1);
v_tail_3275_ = lean_ctor_get(v_x_3272_, 2);
v_isSharedCheck_3298_ = !lean_is_exclusive(v_x_3272_);
if (v_isSharedCheck_3298_ == 0)
{
v___x_3277_ = v_x_3272_;
v_isShared_3278_ = v_isSharedCheck_3298_;
goto v_resetjp_3276_;
}
else
{
lean_inc(v_tail_3275_);
lean_inc(v_value_3274_);
lean_inc(v_key_3273_);
lean_dec(v_x_3272_);
v___x_3277_ = lean_box(0);
v_isShared_3278_ = v_isSharedCheck_3298_;
goto v_resetjp_3276_;
}
v_resetjp_3276_:
{
lean_object* v___x_3279_; uint64_t v___x_3280_; uint64_t v___x_3281_; uint64_t v___x_3282_; uint64_t v_fold_3283_; uint64_t v___x_3284_; uint64_t v___x_3285_; uint64_t v___x_3286_; size_t v___x_3287_; size_t v___x_3288_; size_t v___x_3289_; size_t v___x_3290_; size_t v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3294_; 
v___x_3279_ = lean_array_get_size(v_x_3271_);
v___x_3280_ = l_Lean_Elab_Tactic_Grind_instHashableSimpCacheKey_hash(v_key_3273_);
v___x_3281_ = 32ULL;
v___x_3282_ = lean_uint64_shift_right(v___x_3280_, v___x_3281_);
v_fold_3283_ = lean_uint64_xor(v___x_3280_, v___x_3282_);
v___x_3284_ = 16ULL;
v___x_3285_ = lean_uint64_shift_right(v_fold_3283_, v___x_3284_);
v___x_3286_ = lean_uint64_xor(v_fold_3283_, v___x_3285_);
v___x_3287_ = lean_uint64_to_usize(v___x_3286_);
v___x_3288_ = lean_usize_of_nat(v___x_3279_);
v___x_3289_ = ((size_t)1ULL);
v___x_3290_ = lean_usize_sub(v___x_3288_, v___x_3289_);
v___x_3291_ = lean_usize_land(v___x_3287_, v___x_3290_);
v___x_3292_ = lean_array_uget_borrowed(v_x_3271_, v___x_3291_);
lean_inc(v___x_3292_);
if (v_isShared_3278_ == 0)
{
lean_ctor_set(v___x_3277_, 2, v___x_3292_);
v___x_3294_ = v___x_3277_;
goto v_reusejp_3293_;
}
else
{
lean_object* v_reuseFailAlloc_3297_; 
v_reuseFailAlloc_3297_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3297_, 0, v_key_3273_);
lean_ctor_set(v_reuseFailAlloc_3297_, 1, v_value_3274_);
lean_ctor_set(v_reuseFailAlloc_3297_, 2, v___x_3292_);
v___x_3294_ = v_reuseFailAlloc_3297_;
goto v_reusejp_3293_;
}
v_reusejp_3293_:
{
lean_object* v___x_3295_; 
v___x_3295_ = lean_array_uset(v_x_3271_, v___x_3291_, v___x_3294_);
v_x_3271_ = v___x_3295_;
v_x_3272_ = v_tail_3275_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__2_spec__3___redArg(lean_object* v_i_3299_, lean_object* v_source_3300_, lean_object* v_target_3301_){
_start:
{
lean_object* v___x_3302_; uint8_t v___x_3303_; 
v___x_3302_ = lean_array_get_size(v_source_3300_);
v___x_3303_ = lean_nat_dec_lt(v_i_3299_, v___x_3302_);
if (v___x_3303_ == 0)
{
lean_dec_ref(v_source_3300_);
lean_dec(v_i_3299_);
return v_target_3301_;
}
else
{
lean_object* v_es_3304_; lean_object* v___x_3305_; lean_object* v_source_3306_; lean_object* v_target_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; 
v_es_3304_ = lean_array_fget(v_source_3300_, v_i_3299_);
v___x_3305_ = lean_box(0);
v_source_3306_ = lean_array_fset(v_source_3300_, v_i_3299_, v___x_3305_);
v_target_3307_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__2_spec__3_spec__7___redArg(v_target_3301_, v_es_3304_);
v___x_3308_ = lean_unsigned_to_nat(1u);
v___x_3309_ = lean_nat_add(v_i_3299_, v___x_3308_);
lean_dec(v_i_3299_);
v_i_3299_ = v___x_3309_;
v_source_3300_ = v_source_3306_;
v_target_3301_ = v_target_3307_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__2___redArg(lean_object* v_data_3311_){
_start:
{
lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v_nbuckets_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; 
v___x_3312_ = lean_array_get_size(v_data_3311_);
v___x_3313_ = lean_unsigned_to_nat(2u);
v_nbuckets_3314_ = lean_nat_mul(v___x_3312_, v___x_3313_);
v___x_3315_ = lean_unsigned_to_nat(0u);
v___x_3316_ = lean_box(0);
v___x_3317_ = lean_mk_array(v_nbuckets_3314_, v___x_3316_);
v___x_3318_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__2_spec__3___redArg(v___x_3315_, v_data_3311_, v___x_3317_);
return v___x_3318_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__1___redArg(lean_object* v_a_3319_, lean_object* v_x_3320_){
_start:
{
if (lean_obj_tag(v_x_3320_) == 0)
{
uint8_t v___x_3321_; 
v___x_3321_ = 0;
return v___x_3321_;
}
else
{
lean_object* v_key_3322_; lean_object* v_tail_3323_; uint8_t v___x_3324_; 
v_key_3322_ = lean_ctor_get(v_x_3320_, 0);
v_tail_3323_ = lean_ctor_get(v_x_3320_, 2);
v___x_3324_ = l_Lean_Elab_Tactic_Grind_instBEqSimpCacheKey_beq(v_key_3322_, v_a_3319_);
if (v___x_3324_ == 0)
{
v_x_3320_ = v_tail_3323_;
goto _start;
}
else
{
return v___x_3324_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__1___redArg___boxed(lean_object* v_a_3326_, lean_object* v_x_3327_){
_start:
{
uint8_t v_res_3328_; lean_object* v_r_3329_; 
v_res_3328_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__1___redArg(v_a_3326_, v_x_3327_);
lean_dec(v_x_3327_);
lean_dec_ref(v_a_3326_);
v_r_3329_ = lean_box(v_res_3328_);
return v_r_3329_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1___redArg(lean_object* v_m_3330_, lean_object* v_a_3331_, lean_object* v_b_3332_){
_start:
{
lean_object* v_size_3333_; lean_object* v_buckets_3334_; lean_object* v___x_3336_; uint8_t v_isShared_3337_; uint8_t v_isSharedCheck_3377_; 
v_size_3333_ = lean_ctor_get(v_m_3330_, 0);
v_buckets_3334_ = lean_ctor_get(v_m_3330_, 1);
v_isSharedCheck_3377_ = !lean_is_exclusive(v_m_3330_);
if (v_isSharedCheck_3377_ == 0)
{
v___x_3336_ = v_m_3330_;
v_isShared_3337_ = v_isSharedCheck_3377_;
goto v_resetjp_3335_;
}
else
{
lean_inc(v_buckets_3334_);
lean_inc(v_size_3333_);
lean_dec(v_m_3330_);
v___x_3336_ = lean_box(0);
v_isShared_3337_ = v_isSharedCheck_3377_;
goto v_resetjp_3335_;
}
v_resetjp_3335_:
{
lean_object* v___x_3338_; uint64_t v___x_3339_; uint64_t v___x_3340_; uint64_t v___x_3341_; uint64_t v_fold_3342_; uint64_t v___x_3343_; uint64_t v___x_3344_; uint64_t v___x_3345_; size_t v___x_3346_; size_t v___x_3347_; size_t v___x_3348_; size_t v___x_3349_; size_t v___x_3350_; lean_object* v_bkt_3351_; uint8_t v___x_3352_; 
v___x_3338_ = lean_array_get_size(v_buckets_3334_);
v___x_3339_ = l_Lean_Elab_Tactic_Grind_instHashableSimpCacheKey_hash(v_a_3331_);
v___x_3340_ = 32ULL;
v___x_3341_ = lean_uint64_shift_right(v___x_3339_, v___x_3340_);
v_fold_3342_ = lean_uint64_xor(v___x_3339_, v___x_3341_);
v___x_3343_ = 16ULL;
v___x_3344_ = lean_uint64_shift_right(v_fold_3342_, v___x_3343_);
v___x_3345_ = lean_uint64_xor(v_fold_3342_, v___x_3344_);
v___x_3346_ = lean_uint64_to_usize(v___x_3345_);
v___x_3347_ = lean_usize_of_nat(v___x_3338_);
v___x_3348_ = ((size_t)1ULL);
v___x_3349_ = lean_usize_sub(v___x_3347_, v___x_3348_);
v___x_3350_ = lean_usize_land(v___x_3346_, v___x_3349_);
v_bkt_3351_ = lean_array_uget_borrowed(v_buckets_3334_, v___x_3350_);
v___x_3352_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__1___redArg(v_a_3331_, v_bkt_3351_);
if (v___x_3352_ == 0)
{
lean_object* v___x_3353_; lean_object* v_size_x27_3354_; lean_object* v___x_3355_; lean_object* v_buckets_x27_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; uint8_t v___x_3362_; 
v___x_3353_ = lean_unsigned_to_nat(1u);
v_size_x27_3354_ = lean_nat_add(v_size_3333_, v___x_3353_);
lean_dec(v_size_3333_);
lean_inc(v_bkt_3351_);
v___x_3355_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3355_, 0, v_a_3331_);
lean_ctor_set(v___x_3355_, 1, v_b_3332_);
lean_ctor_set(v___x_3355_, 2, v_bkt_3351_);
v_buckets_x27_3356_ = lean_array_uset(v_buckets_3334_, v___x_3350_, v___x_3355_);
v___x_3357_ = lean_unsigned_to_nat(4u);
v___x_3358_ = lean_nat_mul(v_size_x27_3354_, v___x_3357_);
v___x_3359_ = lean_unsigned_to_nat(3u);
v___x_3360_ = lean_nat_div(v___x_3358_, v___x_3359_);
lean_dec(v___x_3358_);
v___x_3361_ = lean_array_get_size(v_buckets_x27_3356_);
v___x_3362_ = lean_nat_dec_le(v___x_3360_, v___x_3361_);
lean_dec(v___x_3360_);
if (v___x_3362_ == 0)
{
lean_object* v_val_3363_; lean_object* v___x_3365_; 
v_val_3363_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__2___redArg(v_buckets_x27_3356_);
if (v_isShared_3337_ == 0)
{
lean_ctor_set(v___x_3336_, 1, v_val_3363_);
lean_ctor_set(v___x_3336_, 0, v_size_x27_3354_);
v___x_3365_ = v___x_3336_;
goto v_reusejp_3364_;
}
else
{
lean_object* v_reuseFailAlloc_3366_; 
v_reuseFailAlloc_3366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3366_, 0, v_size_x27_3354_);
lean_ctor_set(v_reuseFailAlloc_3366_, 1, v_val_3363_);
v___x_3365_ = v_reuseFailAlloc_3366_;
goto v_reusejp_3364_;
}
v_reusejp_3364_:
{
return v___x_3365_;
}
}
else
{
lean_object* v___x_3368_; 
if (v_isShared_3337_ == 0)
{
lean_ctor_set(v___x_3336_, 1, v_buckets_x27_3356_);
lean_ctor_set(v___x_3336_, 0, v_size_x27_3354_);
v___x_3368_ = v___x_3336_;
goto v_reusejp_3367_;
}
else
{
lean_object* v_reuseFailAlloc_3369_; 
v_reuseFailAlloc_3369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3369_, 0, v_size_x27_3354_);
lean_ctor_set(v_reuseFailAlloc_3369_, 1, v_buckets_x27_3356_);
v___x_3368_ = v_reuseFailAlloc_3369_;
goto v_reusejp_3367_;
}
v_reusejp_3367_:
{
return v___x_3368_;
}
}
}
else
{
lean_object* v___x_3370_; lean_object* v_buckets_x27_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3375_; 
lean_inc(v_bkt_3351_);
v___x_3370_ = lean_box(0);
v_buckets_x27_3371_ = lean_array_uset(v_buckets_3334_, v___x_3350_, v___x_3370_);
v___x_3372_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__3___redArg(v_a_3331_, v_b_3332_, v_bkt_3351_);
v___x_3373_ = lean_array_uset(v_buckets_x27_3371_, v___x_3350_, v___x_3372_);
if (v_isShared_3337_ == 0)
{
lean_ctor_set(v___x_3336_, 1, v___x_3373_);
v___x_3375_ = v___x_3336_;
goto v_reusejp_3374_;
}
else
{
lean_object* v_reuseFailAlloc_3376_; 
v_reuseFailAlloc_3376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3376_, 0, v_size_3333_);
lean_ctor_set(v_reuseFailAlloc_3376_, 1, v___x_3373_);
v___x_3375_ = v_reuseFailAlloc_3376_;
goto v_reusejp_3374_;
}
v_reusejp_3374_:
{
return v___x_3375_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__3(size_t v_sz_3378_, size_t v_i_3379_, lean_object* v_bs_3380_){
_start:
{
uint8_t v___x_3381_; 
v___x_3381_ = lean_usize_dec_lt(v_i_3379_, v_sz_3378_);
if (v___x_3381_ == 0)
{
lean_object* v___x_3382_; 
v___x_3382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3382_, 0, v_bs_3380_);
return v___x_3382_;
}
else
{
lean_object* v_v_3383_; lean_object* v___x_3384_; lean_object* v_bs_x27_3385_; size_t v___x_3386_; size_t v___x_3387_; lean_object* v___x_3388_; 
v_v_3383_ = lean_array_uget(v_bs_3380_, v_i_3379_);
v___x_3384_ = lean_unsigned_to_nat(0u);
v_bs_x27_3385_ = lean_array_uset(v_bs_3380_, v_i_3379_, v___x_3384_);
v___x_3386_ = ((size_t)1ULL);
v___x_3387_ = lean_usize_add(v_i_3379_, v___x_3386_);
v___x_3388_ = lean_array_uset(v_bs_x27_3385_, v_i_3379_, v_v_3383_);
v_i_3379_ = v___x_3387_;
v_bs_3380_ = v___x_3388_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__3___boxed(lean_object* v_sz_3390_, lean_object* v_i_3391_, lean_object* v_bs_3392_){
_start:
{
size_t v_sz_boxed_3393_; size_t v_i_boxed_3394_; lean_object* v_res_3395_; 
v_sz_boxed_3393_ = lean_unbox_usize(v_sz_3390_);
lean_dec(v_sz_3390_);
v_i_boxed_3394_ = lean_unbox_usize(v_i_3391_);
lean_dec(v_i_3391_);
v_res_3395_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__3(v_sz_boxed_3393_, v_i_boxed_3394_, v_bs_3392_);
return v_res_3395_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__1(void){
_start:
{
lean_object* v___x_3397_; lean_object* v___x_3398_; 
v___x_3397_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__0));
v___x_3398_ = l_Lean_stringToMessageData(v___x_3397_);
return v___x_3398_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__4(void){
_start:
{
lean_object* v___x_3406_; 
v___x_3406_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3406_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__5(void){
_start:
{
lean_object* v___x_3407_; lean_object* v___x_3408_; 
v___x_3407_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__4, &l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__4_once, _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__4);
v___x_3408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3408_, 0, v___x_3407_);
return v___x_3408_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__6(void){
_start:
{
lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; 
v___x_3409_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__5, &l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__5);
v___x_3410_ = lean_unsigned_to_nat(0u);
v___x_3411_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3411_, 0, v___x_3410_);
lean_ctor_set(v___x_3411_, 1, v___x_3409_);
lean_ctor_set(v___x_3411_, 2, v___x_3409_);
lean_ctor_set(v___x_3411_, 3, v___x_3409_);
return v___x_3411_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2(lean_object* v_stx_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_){
_start:
{
lean_object* v___y_3425_; lean_object* v___y_3426_; lean_object* v___y_3427_; lean_object* v___y_3428_; lean_object* v___y_3429_; lean_object* v___y_3430_; lean_object* v___y_3431_; lean_object* v___y_3432_; lean_object* v___y_3433_; lean_object* v___y_3434_; lean_object* v___y_3435_; lean_object* v___y_3436_; lean_object* v___x_3531_; 
v___x_3531_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_ensureSym(v___y_3415_, v___y_3416_, v___y_3417_, v___y_3418_, v___y_3419_, v___y_3420_, v___y_3421_, v___y_3422_);
if (lean_obj_tag(v___x_3531_) == 0)
{
lean_object* v___x_3533_; uint8_t v_isShared_3534_; uint8_t v_isSharedCheck_3647_; 
v_isSharedCheck_3647_ = !lean_is_exclusive(v___x_3531_);
if (v_isSharedCheck_3647_ == 0)
{
lean_object* v_unused_3648_; 
v_unused_3648_ = lean_ctor_get(v___x_3531_, 0);
lean_dec(v_unused_3648_);
v___x_3533_ = v___x_3531_;
v_isShared_3534_ = v_isSharedCheck_3647_;
goto v_resetjp_3532_;
}
else
{
lean_dec(v___x_3531_);
v___x_3533_ = lean_box(0);
v_isShared_3534_ = v_isSharedCheck_3647_;
goto v_resetjp_3532_;
}
v_resetjp_3532_:
{
lean_object* v___x_3535_; uint8_t v___x_3536_; 
v___x_3535_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__3));
lean_inc(v_stx_3414_);
v___x_3536_ = l_Lean_Syntax_isOfKind(v_stx_3414_, v___x_3535_);
if (v___x_3536_ == 0)
{
lean_object* v___x_3537_; 
lean_del_object(v___x_3533_);
lean_dec(v_stx_3414_);
v___x_3537_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro_spec__0___redArg();
return v___x_3537_;
}
else
{
lean_object* v___x_3538_; lean_object* v___y_3540_; lean_object* v___y_3541_; lean_object* v___y_3542_; lean_object* v___y_3543_; lean_object* v___y_3544_; lean_object* v___y_3545_; lean_object* v___y_3546_; lean_object* v___y_3547_; lean_object* v___y_3548_; lean_object* v___y_3549_; lean_object* v___y_3576_; lean_object* v_extraIds_3577_; lean_object* v___y_3578_; lean_object* v___y_3579_; lean_object* v___y_3580_; lean_object* v___y_3581_; lean_object* v___y_3582_; lean_object* v___y_3583_; lean_object* v___y_3584_; lean_object* v___y_3585_; lean_object* v___y_3590_; lean_object* v___y_3591_; lean_object* v___y_3592_; lean_object* v___y_3593_; lean_object* v___y_3594_; lean_object* v___y_3595_; lean_object* v___y_3596_; lean_object* v___y_3597_; lean_object* v___y_3598_; lean_object* v___y_3599_; lean_object* v___x_3604_; lean_object* v_variantId_x3f_3606_; lean_object* v___y_3607_; lean_object* v___y_3608_; lean_object* v___y_3609_; lean_object* v___y_3610_; lean_object* v___y_3611_; lean_object* v___y_3612_; lean_object* v___y_3613_; lean_object* v___y_3614_; lean_object* v___x_3638_; uint8_t v___x_3639_; 
v___x_3538_ = lean_unsigned_to_nat(0u);
v___x_3604_ = lean_unsigned_to_nat(1u);
v___x_3638_ = l_Lean_Syntax_getArg(v_stx_3414_, v___x_3604_);
v___x_3639_ = l_Lean_Syntax_isNone(v___x_3638_);
if (v___x_3639_ == 0)
{
uint8_t v___x_3640_; 
lean_inc(v___x_3638_);
v___x_3640_ = l_Lean_Syntax_matchesNull(v___x_3638_, v___x_3604_);
if (v___x_3640_ == 0)
{
lean_object* v___x_3641_; 
lean_dec(v___x_3638_);
lean_del_object(v___x_3533_);
lean_dec(v_stx_3414_);
v___x_3641_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro_spec__0___redArg();
return v___x_3641_;
}
else
{
lean_object* v___x_3642_; lean_object* v___x_3644_; 
v___x_3642_ = l_Lean_Syntax_getArg(v___x_3638_, v___x_3538_);
lean_dec(v___x_3638_);
if (v_isShared_3534_ == 0)
{
lean_ctor_set_tag(v___x_3533_, 1);
lean_ctor_set(v___x_3533_, 0, v___x_3642_);
v___x_3644_ = v___x_3533_;
goto v_reusejp_3643_;
}
else
{
lean_object* v_reuseFailAlloc_3645_; 
v_reuseFailAlloc_3645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3645_, 0, v___x_3642_);
v___x_3644_ = v_reuseFailAlloc_3645_;
goto v_reusejp_3643_;
}
v_reusejp_3643_:
{
v_variantId_x3f_3606_ = v___x_3644_;
v___y_3607_ = v___y_3415_;
v___y_3608_ = v___y_3416_;
v___y_3609_ = v___y_3417_;
v___y_3610_ = v___y_3418_;
v___y_3611_ = v___y_3419_;
v___y_3612_ = v___y_3420_;
v___y_3613_ = v___y_3421_;
v___y_3614_ = v___y_3422_;
goto v___jp_3605_;
}
}
}
else
{
lean_object* v___x_3646_; 
lean_dec(v___x_3638_);
lean_del_object(v___x_3533_);
v___x_3646_ = lean_box(0);
v_variantId_x3f_3606_ = v___x_3646_;
v___y_3607_ = v___y_3415_;
v___y_3608_ = v___y_3416_;
v___y_3609_ = v___y_3417_;
v___y_3610_ = v___y_3418_;
v___y_3611_ = v___y_3419_;
v___y_3612_ = v___y_3420_;
v___y_3613_ = v___y_3421_;
v___y_3614_ = v___y_3422_;
goto v___jp_3605_;
}
v___jp_3539_:
{
lean_object* v___x_3550_; 
v___x_3550_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems(v___y_3540_, v___y_3542_, v___y_3548_, v___y_3547_, v___y_3546_, v___y_3544_, v___y_3543_, v___y_3545_, v___y_3541_);
lean_dec(v___y_3540_);
if (lean_obj_tag(v___x_3550_) == 0)
{
lean_object* v_a_3551_; lean_object* v_fst_3552_; lean_object* v_snd_3553_; lean_object* v___x_3555_; uint8_t v_isShared_3556_; uint8_t v_isSharedCheck_3566_; 
v_a_3551_ = lean_ctor_get(v___x_3550_, 0);
lean_inc(v_a_3551_);
lean_dec_ref(v___x_3550_);
v_fst_3552_ = lean_ctor_get(v_a_3551_, 0);
v_snd_3553_ = lean_ctor_get(v_a_3551_, 1);
v_isSharedCheck_3566_ = !lean_is_exclusive(v_a_3551_);
if (v_isSharedCheck_3566_ == 0)
{
v___x_3555_ = v_a_3551_;
v_isShared_3556_ = v_isSharedCheck_3566_;
goto v_resetjp_3554_;
}
else
{
lean_inc(v_snd_3553_);
lean_inc(v_fst_3552_);
lean_dec(v_a_3551_);
v___x_3555_ = lean_box(0);
v_isShared_3556_ = v_isSharedCheck_3566_;
goto v_resetjp_3554_;
}
v_resetjp_3554_:
{
lean_object* v___x_3557_; lean_object* v_cache_3558_; lean_object* v_simpState_3559_; lean_object* v___x_3561_; 
v___x_3557_ = lean_st_ref_get(v___y_3548_);
v_cache_3558_ = lean_ctor_get(v___x_3557_, 3);
lean_inc_ref(v_cache_3558_);
lean_dec(v___x_3557_);
v_simpState_3559_ = lean_ctor_get(v_cache_3558_, 2);
lean_inc_ref(v_simpState_3559_);
lean_dec_ref(v_cache_3558_);
lean_inc(v___y_3549_);
if (v_isShared_3556_ == 0)
{
lean_ctor_set(v___x_3555_, 1, v_fst_3552_);
lean_ctor_set(v___x_3555_, 0, v___y_3549_);
v___x_3561_ = v___x_3555_;
goto v_reusejp_3560_;
}
else
{
lean_object* v_reuseFailAlloc_3565_; 
v_reuseFailAlloc_3565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3565_, 0, v___y_3549_);
lean_ctor_set(v_reuseFailAlloc_3565_, 1, v_fst_3552_);
v___x_3561_ = v_reuseFailAlloc_3565_;
goto v_reusejp_3560_;
}
v_reusejp_3560_:
{
lean_object* v___x_3562_; 
v___x_3562_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__2___redArg(v_simpState_3559_, v___x_3561_);
lean_dec_ref(v_simpState_3559_);
if (lean_obj_tag(v___x_3562_) == 0)
{
lean_object* v___x_3563_; 
v___x_3563_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__6, &l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__6_once, _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__6);
v___y_3425_ = v___x_3561_;
v___y_3426_ = v___y_3541_;
v___y_3427_ = v___y_3542_;
v___y_3428_ = v___y_3543_;
v___y_3429_ = v___y_3544_;
v___y_3430_ = v___y_3545_;
v___y_3431_ = v___y_3546_;
v___y_3432_ = v___y_3547_;
v___y_3433_ = v___y_3548_;
v___y_3434_ = v_snd_3553_;
v___y_3435_ = v___y_3549_;
v___y_3436_ = v___x_3563_;
goto v___jp_3424_;
}
else
{
lean_object* v_val_3564_; 
v_val_3564_ = lean_ctor_get(v___x_3562_, 0);
lean_inc(v_val_3564_);
lean_dec_ref(v___x_3562_);
v___y_3425_ = v___x_3561_;
v___y_3426_ = v___y_3541_;
v___y_3427_ = v___y_3542_;
v___y_3428_ = v___y_3543_;
v___y_3429_ = v___y_3544_;
v___y_3430_ = v___y_3545_;
v___y_3431_ = v___y_3546_;
v___y_3432_ = v___y_3547_;
v___y_3433_ = v___y_3548_;
v___y_3434_ = v_snd_3553_;
v___y_3435_ = v___y_3549_;
v___y_3436_ = v_val_3564_;
goto v___jp_3424_;
}
}
}
}
else
{
lean_object* v_a_3567_; lean_object* v___x_3569_; uint8_t v_isShared_3570_; uint8_t v_isSharedCheck_3574_; 
lean_dec(v___y_3549_);
v_a_3567_ = lean_ctor_get(v___x_3550_, 0);
v_isSharedCheck_3574_ = !lean_is_exclusive(v___x_3550_);
if (v_isSharedCheck_3574_ == 0)
{
v___x_3569_ = v___x_3550_;
v_isShared_3570_ = v_isSharedCheck_3574_;
goto v_resetjp_3568_;
}
else
{
lean_inc(v_a_3567_);
lean_dec(v___x_3550_);
v___x_3569_ = lean_box(0);
v_isShared_3570_ = v_isSharedCheck_3574_;
goto v_resetjp_3568_;
}
v_resetjp_3568_:
{
lean_object* v___x_3572_; 
if (v_isShared_3570_ == 0)
{
v___x_3572_ = v___x_3569_;
goto v_reusejp_3571_;
}
else
{
lean_object* v_reuseFailAlloc_3573_; 
v_reuseFailAlloc_3573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3573_, 0, v_a_3567_);
v___x_3572_ = v_reuseFailAlloc_3573_;
goto v_reusejp_3571_;
}
v_reusejp_3571_:
{
return v___x_3572_;
}
}
}
}
v___jp_3575_:
{
if (lean_obj_tag(v___y_3576_) == 0)
{
lean_object* v___x_3586_; 
v___x_3586_ = lean_box(0);
v___y_3540_ = v_extraIds_3577_;
v___y_3541_ = v___y_3585_;
v___y_3542_ = v___y_3578_;
v___y_3543_ = v___y_3583_;
v___y_3544_ = v___y_3582_;
v___y_3545_ = v___y_3584_;
v___y_3546_ = v___y_3581_;
v___y_3547_ = v___y_3580_;
v___y_3548_ = v___y_3579_;
v___y_3549_ = v___x_3586_;
goto v___jp_3539_;
}
else
{
lean_object* v_val_3587_; lean_object* v___x_3588_; 
v_val_3587_ = lean_ctor_get(v___y_3576_, 0);
lean_inc(v_val_3587_);
lean_dec_ref(v___y_3576_);
v___x_3588_ = l_Lean_TSyntax_getId(v_val_3587_);
lean_dec(v_val_3587_);
v___y_3540_ = v_extraIds_3577_;
v___y_3541_ = v___y_3585_;
v___y_3542_ = v___y_3578_;
v___y_3543_ = v___y_3583_;
v___y_3544_ = v___y_3582_;
v___y_3545_ = v___y_3584_;
v___y_3546_ = v___y_3581_;
v___y_3547_ = v___y_3580_;
v___y_3548_ = v___y_3579_;
v___y_3549_ = v___x_3588_;
goto v___jp_3539_;
}
}
v___jp_3589_:
{
size_t v_sz_3600_; size_t v___x_3601_; lean_object* v___x_3602_; 
v_sz_3600_ = lean_array_size(v___y_3599_);
v___x_3601_ = ((size_t)0ULL);
v___x_3602_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__3(v_sz_3600_, v___x_3601_, v___y_3599_);
if (lean_obj_tag(v___x_3602_) == 0)
{
lean_object* v___x_3603_; 
lean_dec(v___y_3598_);
v___x_3603_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro_spec__0___redArg();
return v___x_3603_;
}
else
{
v___y_3576_ = v___y_3598_;
v_extraIds_3577_ = v___x_3602_;
v___y_3578_ = v___y_3590_;
v___y_3579_ = v___y_3593_;
v___y_3580_ = v___y_3594_;
v___y_3581_ = v___y_3592_;
v___y_3582_ = v___y_3595_;
v___y_3583_ = v___y_3596_;
v___y_3584_ = v___y_3591_;
v___y_3585_ = v___y_3597_;
goto v___jp_3575_;
}
}
v___jp_3605_:
{
lean_object* v___x_3615_; lean_object* v___x_3616_; uint8_t v___x_3617_; 
v___x_3615_ = lean_unsigned_to_nat(2u);
v___x_3616_ = l_Lean_Syntax_getArg(v_stx_3414_, v___x_3615_);
lean_dec(v_stx_3414_);
v___x_3617_ = l_Lean_Syntax_isNone(v___x_3616_);
if (v___x_3617_ == 0)
{
lean_object* v___x_3618_; uint8_t v___x_3619_; 
v___x_3618_ = lean_unsigned_to_nat(3u);
lean_inc(v___x_3616_);
v___x_3619_ = l_Lean_Syntax_matchesNull(v___x_3616_, v___x_3618_);
if (v___x_3619_ == 0)
{
lean_object* v___x_3620_; 
lean_dec(v___x_3616_);
lean_dec(v_variantId_x3f_3606_);
v___x_3620_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro_spec__0___redArg();
return v___x_3620_;
}
else
{
lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; uint8_t v___x_3625_; 
v___x_3621_ = l_Lean_Syntax_getArg(v___x_3616_, v___x_3604_);
lean_dec(v___x_3616_);
v___x_3622_ = l_Lean_Syntax_getArgs(v___x_3621_);
lean_dec(v___x_3621_);
v___x_3623_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__7));
v___x_3624_ = lean_array_get_size(v___x_3622_);
v___x_3625_ = lean_nat_dec_lt(v___x_3538_, v___x_3624_);
if (v___x_3625_ == 0)
{
lean_dec_ref(v___x_3622_);
v___y_3590_ = v___y_3607_;
v___y_3591_ = v___y_3613_;
v___y_3592_ = v___y_3610_;
v___y_3593_ = v___y_3608_;
v___y_3594_ = v___y_3609_;
v___y_3595_ = v___y_3611_;
v___y_3596_ = v___y_3612_;
v___y_3597_ = v___y_3614_;
v___y_3598_ = v_variantId_x3f_3606_;
v___y_3599_ = v___x_3623_;
goto v___jp_3589_;
}
else
{
lean_object* v___x_3626_; lean_object* v___x_3627_; uint8_t v___x_3628_; 
v___x_3626_ = lean_box(v___x_3619_);
v___x_3627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3627_, 0, v___x_3626_);
lean_ctor_set(v___x_3627_, 1, v___x_3623_);
v___x_3628_ = lean_nat_dec_le(v___x_3624_, v___x_3624_);
if (v___x_3628_ == 0)
{
if (v___x_3625_ == 0)
{
lean_dec_ref(v___x_3627_);
lean_dec_ref(v___x_3622_);
v___y_3590_ = v___y_3607_;
v___y_3591_ = v___y_3613_;
v___y_3592_ = v___y_3610_;
v___y_3593_ = v___y_3608_;
v___y_3594_ = v___y_3609_;
v___y_3595_ = v___y_3611_;
v___y_3596_ = v___y_3612_;
v___y_3597_ = v___y_3614_;
v___y_3598_ = v_variantId_x3f_3606_;
v___y_3599_ = v___x_3623_;
goto v___jp_3589_;
}
else
{
size_t v___x_3629_; size_t v___x_3630_; lean_object* v___x_3631_; lean_object* v_snd_3632_; 
v___x_3629_ = ((size_t)0ULL);
v___x_3630_ = lean_usize_of_nat(v___x_3624_);
v___x_3631_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__4(v___x_3619_, v___x_3617_, v___x_3622_, v___x_3629_, v___x_3630_, v___x_3627_);
lean_dec_ref(v___x_3622_);
v_snd_3632_ = lean_ctor_get(v___x_3631_, 1);
lean_inc(v_snd_3632_);
lean_dec_ref(v___x_3631_);
v___y_3590_ = v___y_3607_;
v___y_3591_ = v___y_3613_;
v___y_3592_ = v___y_3610_;
v___y_3593_ = v___y_3608_;
v___y_3594_ = v___y_3609_;
v___y_3595_ = v___y_3611_;
v___y_3596_ = v___y_3612_;
v___y_3597_ = v___y_3614_;
v___y_3598_ = v_variantId_x3f_3606_;
v___y_3599_ = v_snd_3632_;
goto v___jp_3589_;
}
}
else
{
size_t v___x_3633_; size_t v___x_3634_; lean_object* v___x_3635_; lean_object* v_snd_3636_; 
v___x_3633_ = ((size_t)0ULL);
v___x_3634_ = lean_usize_of_nat(v___x_3624_);
v___x_3635_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__4(v___x_3619_, v___x_3617_, v___x_3622_, v___x_3633_, v___x_3634_, v___x_3627_);
lean_dec_ref(v___x_3622_);
v_snd_3636_ = lean_ctor_get(v___x_3635_, 1);
lean_inc(v_snd_3636_);
lean_dec_ref(v___x_3635_);
v___y_3590_ = v___y_3607_;
v___y_3591_ = v___y_3613_;
v___y_3592_ = v___y_3610_;
v___y_3593_ = v___y_3608_;
v___y_3594_ = v___y_3609_;
v___y_3595_ = v___y_3611_;
v___y_3596_ = v___y_3612_;
v___y_3597_ = v___y_3614_;
v___y_3598_ = v_variantId_x3f_3606_;
v___y_3599_ = v_snd_3636_;
goto v___jp_3589_;
}
}
}
}
else
{
lean_object* v___x_3637_; 
lean_dec(v___x_3616_);
v___x_3637_ = lean_box(0);
v___y_3576_ = v_variantId_x3f_3606_;
v_extraIds_3577_ = v___x_3637_;
v___y_3578_ = v___y_3607_;
v___y_3579_ = v___y_3608_;
v___y_3580_ = v___y_3609_;
v___y_3581_ = v___y_3610_;
v___y_3582_ = v___y_3611_;
v___y_3583_ = v___y_3612_;
v___y_3584_ = v___y_3613_;
v___y_3585_ = v___y_3614_;
goto v___jp_3575_;
}
}
}
}
}
else
{
lean_dec(v_stx_3414_);
return v___x_3531_;
}
v___jp_3424_:
{
lean_object* v___x_3437_; 
v___x_3437_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabVariant(v___y_3435_, v___y_3434_, v___y_3427_, v___y_3433_, v___y_3432_, v___y_3431_, v___y_3429_, v___y_3428_, v___y_3430_, v___y_3426_);
lean_dec_ref(v___y_3434_);
if (lean_obj_tag(v___x_3437_) == 0)
{
lean_object* v_a_3438_; lean_object* v_fst_3439_; lean_object* v_snd_3440_; lean_object* v___x_3441_; 
v_a_3438_ = lean_ctor_get(v___x_3437_, 0);
lean_inc(v_a_3438_);
lean_dec_ref(v___x_3437_);
v_fst_3439_ = lean_ctor_get(v_a_3438_, 0);
lean_inc(v_fst_3439_);
v_snd_3440_ = lean_ctor_get(v_a_3438_, 1);
lean_inc(v_snd_3440_);
lean_dec(v_a_3438_);
v___x_3441_ = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(v___y_3433_, v___y_3429_, v___y_3428_, v___y_3430_, v___y_3426_);
if (lean_obj_tag(v___x_3441_) == 0)
{
lean_object* v_a_3442_; lean_object* v_toGoalState_3443_; lean_object* v_mvarId_3444_; lean_object* v___x_3446_; uint8_t v_isShared_3447_; uint8_t v_isSharedCheck_3514_; 
v_a_3442_ = lean_ctor_get(v___x_3441_, 0);
lean_inc(v_a_3442_);
lean_dec_ref(v___x_3441_);
v_toGoalState_3443_ = lean_ctor_get(v_a_3442_, 0);
v_mvarId_3444_ = lean_ctor_get(v_a_3442_, 1);
v_isSharedCheck_3514_ = !lean_is_exclusive(v_a_3442_);
if (v_isSharedCheck_3514_ == 0)
{
v___x_3446_ = v_a_3442_;
v_isShared_3447_ = v_isSharedCheck_3514_;
goto v_resetjp_3445_;
}
else
{
lean_inc(v_mvarId_3444_);
lean_inc(v_toGoalState_3443_);
lean_dec(v_a_3442_);
v___x_3446_ = lean_box(0);
v_isShared_3447_ = v_isSharedCheck_3514_;
goto v_resetjp_3445_;
}
v_resetjp_3445_:
{
lean_object* v___f_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; 
lean_inc_n(v_mvarId_3444_, 2);
v___f_3448_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__0___boxed), 14, 4);
lean_closure_set(v___f_3448_, 0, v_mvarId_3444_);
lean_closure_set(v___f_3448_, 1, v_fst_3439_);
lean_closure_set(v___f_3448_, 2, v_snd_3440_);
lean_closure_set(v___f_3448_, 3, v___y_3436_);
v___x_3449_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__0___boxed), 13, 3);
lean_closure_set(v___x_3449_, 0, lean_box(0));
lean_closure_set(v___x_3449_, 1, v_mvarId_3444_);
lean_closure_set(v___x_3449_, 2, v___f_3448_);
v___x_3450_ = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(v___x_3449_, v___y_3427_, v___y_3433_, v___y_3429_, v___y_3428_, v___y_3430_, v___y_3426_);
if (lean_obj_tag(v___x_3450_) == 0)
{
lean_object* v_a_3451_; lean_object* v_fst_3452_; lean_object* v_snd_3453_; lean_object* v___x_3455_; uint8_t v_isShared_3456_; uint8_t v_isSharedCheck_3505_; 
v_a_3451_ = lean_ctor_get(v___x_3450_, 0);
lean_inc(v_a_3451_);
lean_dec_ref(v___x_3450_);
v_fst_3452_ = lean_ctor_get(v_a_3451_, 0);
v_snd_3453_ = lean_ctor_get(v_a_3451_, 1);
v_isSharedCheck_3505_ = !lean_is_exclusive(v_a_3451_);
if (v_isSharedCheck_3505_ == 0)
{
v___x_3455_ = v_a_3451_;
v_isShared_3456_ = v_isSharedCheck_3505_;
goto v_resetjp_3454_;
}
else
{
lean_inc(v_snd_3453_);
lean_inc(v_fst_3452_);
lean_dec(v_a_3451_);
v___x_3455_ = lean_box(0);
v_isShared_3456_ = v_isSharedCheck_3505_;
goto v_resetjp_3454_;
}
v_resetjp_3454_:
{
lean_object* v___x_3457_; lean_object* v_cache_3458_; lean_object* v_symState_3459_; lean_object* v_grindState_3460_; lean_object* v_goals_3461_; lean_object* v___x_3463_; uint8_t v_isShared_3464_; uint8_t v_isSharedCheck_3504_; 
v___x_3457_ = lean_st_ref_take(v___y_3433_);
v_cache_3458_ = lean_ctor_get(v___x_3457_, 3);
v_symState_3459_ = lean_ctor_get(v___x_3457_, 0);
v_grindState_3460_ = lean_ctor_get(v___x_3457_, 1);
v_goals_3461_ = lean_ctor_get(v___x_3457_, 2);
v_isSharedCheck_3504_ = !lean_is_exclusive(v___x_3457_);
if (v_isSharedCheck_3504_ == 0)
{
v___x_3463_ = v___x_3457_;
v_isShared_3464_ = v_isSharedCheck_3504_;
goto v_resetjp_3462_;
}
else
{
lean_inc(v_cache_3458_);
lean_inc(v_goals_3461_);
lean_inc(v_grindState_3460_);
lean_inc(v_symState_3459_);
lean_dec(v___x_3457_);
v___x_3463_ = lean_box(0);
v_isShared_3464_ = v_isSharedCheck_3504_;
goto v_resetjp_3462_;
}
v_resetjp_3462_:
{
lean_object* v_backwardRuleName_3465_; lean_object* v_backwardRuleSyntax_3466_; lean_object* v_simpState_3467_; lean_object* v___x_3469_; uint8_t v_isShared_3470_; uint8_t v_isSharedCheck_3503_; 
v_backwardRuleName_3465_ = lean_ctor_get(v_cache_3458_, 0);
v_backwardRuleSyntax_3466_ = lean_ctor_get(v_cache_3458_, 1);
v_simpState_3467_ = lean_ctor_get(v_cache_3458_, 2);
v_isSharedCheck_3503_ = !lean_is_exclusive(v_cache_3458_);
if (v_isSharedCheck_3503_ == 0)
{
v___x_3469_ = v_cache_3458_;
v_isShared_3470_ = v_isSharedCheck_3503_;
goto v_resetjp_3468_;
}
else
{
lean_inc(v_simpState_3467_);
lean_inc(v_backwardRuleSyntax_3466_);
lean_inc(v_backwardRuleName_3465_);
lean_dec(v_cache_3458_);
v___x_3469_ = lean_box(0);
v_isShared_3470_ = v_isSharedCheck_3503_;
goto v_resetjp_3468_;
}
v_resetjp_3468_:
{
lean_object* v___x_3471_; lean_object* v___x_3473_; 
v___x_3471_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1___redArg(v_simpState_3467_, v___y_3425_, v_snd_3453_);
if (v_isShared_3470_ == 0)
{
lean_ctor_set(v___x_3469_, 2, v___x_3471_);
v___x_3473_ = v___x_3469_;
goto v_reusejp_3472_;
}
else
{
lean_object* v_reuseFailAlloc_3502_; 
v_reuseFailAlloc_3502_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3502_, 0, v_backwardRuleName_3465_);
lean_ctor_set(v_reuseFailAlloc_3502_, 1, v_backwardRuleSyntax_3466_);
lean_ctor_set(v_reuseFailAlloc_3502_, 2, v___x_3471_);
v___x_3473_ = v_reuseFailAlloc_3502_;
goto v_reusejp_3472_;
}
v_reusejp_3472_:
{
lean_object* v___x_3475_; 
if (v_isShared_3464_ == 0)
{
lean_ctor_set(v___x_3463_, 3, v___x_3473_);
v___x_3475_ = v___x_3463_;
goto v_reusejp_3474_;
}
else
{
lean_object* v_reuseFailAlloc_3501_; 
v_reuseFailAlloc_3501_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3501_, 0, v_symState_3459_);
lean_ctor_set(v_reuseFailAlloc_3501_, 1, v_grindState_3460_);
lean_ctor_set(v_reuseFailAlloc_3501_, 2, v_goals_3461_);
lean_ctor_set(v_reuseFailAlloc_3501_, 3, v___x_3473_);
v___x_3475_ = v_reuseFailAlloc_3501_;
goto v_reusejp_3474_;
}
v_reusejp_3474_:
{
lean_object* v___x_3476_; lean_object* v___f_3477_; lean_object* v___x_3478_; 
v___x_3476_ = lean_st_ref_set(v___y_3433_, v___x_3475_);
v___f_3477_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__1___boxed), 12, 2);
lean_closure_set(v___f_3477_, 0, v_fst_3452_);
lean_closure_set(v___f_3477_, 1, v_mvarId_3444_);
v___x_3478_ = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(v___f_3477_, v___y_3427_, v___y_3433_, v___y_3429_, v___y_3428_, v___y_3430_, v___y_3426_);
if (lean_obj_tag(v___x_3478_) == 0)
{
lean_object* v_a_3479_; 
v_a_3479_ = lean_ctor_get(v___x_3478_, 0);
lean_inc(v_a_3479_);
lean_dec_ref(v___x_3478_);
switch(lean_obj_tag(v_a_3479_))
{
case 0:
{
lean_object* v___x_3480_; lean_object* v___x_3481_; 
lean_del_object(v___x_3455_);
lean_del_object(v___x_3446_);
lean_dec_ref(v_toGoalState_3443_);
v___x_3480_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__1, &l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__1);
v___x_3481_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_ensureSym_spec__0___redArg(v___x_3480_, v___y_3429_, v___y_3428_, v___y_3430_, v___y_3426_);
return v___x_3481_;
}
case 1:
{
lean_object* v___x_3482_; lean_object* v___x_3483_; 
lean_del_object(v___x_3455_);
lean_del_object(v___x_3446_);
lean_dec_ref(v_toGoalState_3443_);
v___x_3482_ = lean_box(0);
v___x_3483_ = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(v___x_3482_, v___y_3433_, v___y_3429_, v___y_3428_, v___y_3430_, v___y_3426_);
return v___x_3483_;
}
default: 
{
lean_object* v_mvarId_3484_; lean_object* v___x_3486_; 
v_mvarId_3484_ = lean_ctor_get(v_a_3479_, 0);
lean_inc(v_mvarId_3484_);
lean_dec_ref(v_a_3479_);
if (v_isShared_3447_ == 0)
{
lean_ctor_set(v___x_3446_, 1, v_mvarId_3484_);
v___x_3486_ = v___x_3446_;
goto v_reusejp_3485_;
}
else
{
lean_object* v_reuseFailAlloc_3492_; 
v_reuseFailAlloc_3492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3492_, 0, v_toGoalState_3443_);
lean_ctor_set(v_reuseFailAlloc_3492_, 1, v_mvarId_3484_);
v___x_3486_ = v_reuseFailAlloc_3492_;
goto v_reusejp_3485_;
}
v_reusejp_3485_:
{
lean_object* v___x_3487_; lean_object* v___x_3489_; 
v___x_3487_ = lean_box(0);
if (v_isShared_3456_ == 0)
{
lean_ctor_set_tag(v___x_3455_, 1);
lean_ctor_set(v___x_3455_, 1, v___x_3487_);
lean_ctor_set(v___x_3455_, 0, v___x_3486_);
v___x_3489_ = v___x_3455_;
goto v_reusejp_3488_;
}
else
{
lean_object* v_reuseFailAlloc_3491_; 
v_reuseFailAlloc_3491_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3491_, 0, v___x_3486_);
lean_ctor_set(v_reuseFailAlloc_3491_, 1, v___x_3487_);
v___x_3489_ = v_reuseFailAlloc_3491_;
goto v_reusejp_3488_;
}
v_reusejp_3488_:
{
lean_object* v___x_3490_; 
v___x_3490_ = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(v___x_3489_, v___y_3433_, v___y_3429_, v___y_3428_, v___y_3430_, v___y_3426_);
return v___x_3490_;
}
}
}
}
}
else
{
lean_object* v_a_3493_; lean_object* v___x_3495_; uint8_t v_isShared_3496_; uint8_t v_isSharedCheck_3500_; 
lean_del_object(v___x_3455_);
lean_del_object(v___x_3446_);
lean_dec_ref(v_toGoalState_3443_);
v_a_3493_ = lean_ctor_get(v___x_3478_, 0);
v_isSharedCheck_3500_ = !lean_is_exclusive(v___x_3478_);
if (v_isSharedCheck_3500_ == 0)
{
v___x_3495_ = v___x_3478_;
v_isShared_3496_ = v_isSharedCheck_3500_;
goto v_resetjp_3494_;
}
else
{
lean_inc(v_a_3493_);
lean_dec(v___x_3478_);
v___x_3495_ = lean_box(0);
v_isShared_3496_ = v_isSharedCheck_3500_;
goto v_resetjp_3494_;
}
v_resetjp_3494_:
{
lean_object* v___x_3498_; 
if (v_isShared_3496_ == 0)
{
v___x_3498_ = v___x_3495_;
goto v_reusejp_3497_;
}
else
{
lean_object* v_reuseFailAlloc_3499_; 
v_reuseFailAlloc_3499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3499_, 0, v_a_3493_);
v___x_3498_ = v_reuseFailAlloc_3499_;
goto v_reusejp_3497_;
}
v_reusejp_3497_:
{
return v___x_3498_;
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
lean_object* v_a_3506_; lean_object* v___x_3508_; uint8_t v_isShared_3509_; uint8_t v_isSharedCheck_3513_; 
lean_del_object(v___x_3446_);
lean_dec(v_mvarId_3444_);
lean_dec_ref(v_toGoalState_3443_);
lean_dec_ref(v___y_3425_);
v_a_3506_ = lean_ctor_get(v___x_3450_, 0);
v_isSharedCheck_3513_ = !lean_is_exclusive(v___x_3450_);
if (v_isSharedCheck_3513_ == 0)
{
v___x_3508_ = v___x_3450_;
v_isShared_3509_ = v_isSharedCheck_3513_;
goto v_resetjp_3507_;
}
else
{
lean_inc(v_a_3506_);
lean_dec(v___x_3450_);
v___x_3508_ = lean_box(0);
v_isShared_3509_ = v_isSharedCheck_3513_;
goto v_resetjp_3507_;
}
v_resetjp_3507_:
{
lean_object* v___x_3511_; 
if (v_isShared_3509_ == 0)
{
v___x_3511_ = v___x_3508_;
goto v_reusejp_3510_;
}
else
{
lean_object* v_reuseFailAlloc_3512_; 
v_reuseFailAlloc_3512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3512_, 0, v_a_3506_);
v___x_3511_ = v_reuseFailAlloc_3512_;
goto v_reusejp_3510_;
}
v_reusejp_3510_:
{
return v___x_3511_;
}
}
}
}
}
else
{
lean_object* v_a_3515_; lean_object* v___x_3517_; uint8_t v_isShared_3518_; uint8_t v_isSharedCheck_3522_; 
lean_dec(v_snd_3440_);
lean_dec(v_fst_3439_);
lean_dec_ref(v___y_3436_);
lean_dec_ref(v___y_3425_);
v_a_3515_ = lean_ctor_get(v___x_3441_, 0);
v_isSharedCheck_3522_ = !lean_is_exclusive(v___x_3441_);
if (v_isSharedCheck_3522_ == 0)
{
v___x_3517_ = v___x_3441_;
v_isShared_3518_ = v_isSharedCheck_3522_;
goto v_resetjp_3516_;
}
else
{
lean_inc(v_a_3515_);
lean_dec(v___x_3441_);
v___x_3517_ = lean_box(0);
v_isShared_3518_ = v_isSharedCheck_3522_;
goto v_resetjp_3516_;
}
v_resetjp_3516_:
{
lean_object* v___x_3520_; 
if (v_isShared_3518_ == 0)
{
v___x_3520_ = v___x_3517_;
goto v_reusejp_3519_;
}
else
{
lean_object* v_reuseFailAlloc_3521_; 
v_reuseFailAlloc_3521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3521_, 0, v_a_3515_);
v___x_3520_ = v_reuseFailAlloc_3521_;
goto v_reusejp_3519_;
}
v_reusejp_3519_:
{
return v___x_3520_;
}
}
}
}
else
{
lean_object* v_a_3523_; lean_object* v___x_3525_; uint8_t v_isShared_3526_; uint8_t v_isSharedCheck_3530_; 
lean_dec_ref(v___y_3436_);
lean_dec_ref(v___y_3425_);
v_a_3523_ = lean_ctor_get(v___x_3437_, 0);
v_isSharedCheck_3530_ = !lean_is_exclusive(v___x_3437_);
if (v_isSharedCheck_3530_ == 0)
{
v___x_3525_ = v___x_3437_;
v_isShared_3526_ = v_isSharedCheck_3530_;
goto v_resetjp_3524_;
}
else
{
lean_inc(v_a_3523_);
lean_dec(v___x_3437_);
v___x_3525_ = lean_box(0);
v_isShared_3526_ = v_isSharedCheck_3530_;
goto v_resetjp_3524_;
}
v_resetjp_3524_:
{
lean_object* v___x_3528_; 
if (v_isShared_3526_ == 0)
{
v___x_3528_ = v___x_3525_;
goto v_reusejp_3527_;
}
else
{
lean_object* v_reuseFailAlloc_3529_; 
v_reuseFailAlloc_3529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3529_, 0, v_a_3523_);
v___x_3528_ = v_reuseFailAlloc_3529_;
goto v_reusejp_3527_;
}
v_reusejp_3527_:
{
return v___x_3528_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___boxed(lean_object* v_stx_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_, lean_object* v___y_3654_, lean_object* v___y_3655_, lean_object* v___y_3656_, lean_object* v___y_3657_, lean_object* v___y_3658_){
_start:
{
lean_object* v_res_3659_; 
v_res_3659_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2(v_stx_3649_, v___y_3650_, v___y_3651_, v___y_3652_, v___y_3653_, v___y_3654_, v___y_3655_, v___y_3656_, v___y_3657_);
lean_dec(v___y_3657_);
lean_dec_ref(v___y_3656_);
lean_dec(v___y_3655_);
lean_dec_ref(v___y_3654_);
lean_dec(v___y_3653_);
lean_dec_ref(v___y_3652_);
lean_dec(v___y_3651_);
lean_dec_ref(v___y_3650_);
return v_res_3659_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp(lean_object* v_stx_3660_, lean_object* v_a_3661_, lean_object* v_a_3662_, lean_object* v_a_3663_, lean_object* v_a_3664_, lean_object* v_a_3665_, lean_object* v_a_3666_, lean_object* v_a_3667_, lean_object* v_a_3668_){
_start:
{
lean_object* v___f_3670_; lean_object* v___x_3671_; 
v___f_3670_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___boxed), 10, 1);
lean_closure_set(v___f_3670_, 0, v_stx_3660_);
v___x_3671_ = l_Lean_Elab_Tactic_Grind_withMainContext___redArg(v___f_3670_, v_a_3661_, v_a_3662_, v_a_3663_, v_a_3664_, v_a_3665_, v_a_3666_, v_a_3667_, v_a_3668_);
return v___x_3671_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___boxed(lean_object* v_stx_3672_, lean_object* v_a_3673_, lean_object* v_a_3674_, lean_object* v_a_3675_, lean_object* v_a_3676_, lean_object* v_a_3677_, lean_object* v_a_3678_, lean_object* v_a_3679_, lean_object* v_a_3680_, lean_object* v_a_3681_){
_start:
{
lean_object* v_res_3682_; 
v_res_3682_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp(v_stx_3672_, v_a_3673_, v_a_3674_, v_a_3675_, v_a_3676_, v_a_3677_, v_a_3678_, v_a_3679_, v_a_3680_);
lean_dec(v_a_3680_);
lean_dec_ref(v_a_3679_);
lean_dec(v_a_3678_);
lean_dec_ref(v_a_3677_);
lean_dec(v_a_3676_);
lean_dec_ref(v_a_3675_);
lean_dec(v_a_3674_);
lean_dec_ref(v_a_3673_);
return v_res_3682_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1(lean_object* v_00_u03b2_3683_, lean_object* v_m_3684_, lean_object* v_a_3685_, lean_object* v_b_3686_){
_start:
{
lean_object* v___x_3687_; 
v___x_3687_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1___redArg(v_m_3684_, v_a_3685_, v_b_3686_);
return v___x_3687_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__2(lean_object* v_00_u03b2_3688_, lean_object* v_m_3689_, lean_object* v_a_3690_){
_start:
{
lean_object* v___x_3691_; 
v___x_3691_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__2___redArg(v_m_3689_, v_a_3690_);
return v___x_3691_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__2___boxed(lean_object* v_00_u03b2_3692_, lean_object* v_m_3693_, lean_object* v_a_3694_){
_start:
{
lean_object* v_res_3695_; 
v_res_3695_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__2(v_00_u03b2_3692_, v_m_3693_, v_a_3694_);
lean_dec_ref(v_a_3694_);
lean_dec_ref(v_m_3693_);
return v_res_3695_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__1(lean_object* v_00_u03b2_3696_, lean_object* v_a_3697_, lean_object* v_x_3698_){
_start:
{
uint8_t v___x_3699_; 
v___x_3699_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__1___redArg(v_a_3697_, v_x_3698_);
return v___x_3699_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__1___boxed(lean_object* v_00_u03b2_3700_, lean_object* v_a_3701_, lean_object* v_x_3702_){
_start:
{
uint8_t v_res_3703_; lean_object* v_r_3704_; 
v_res_3703_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__1(v_00_u03b2_3700_, v_a_3701_, v_x_3702_);
lean_dec(v_x_3702_);
lean_dec_ref(v_a_3701_);
v_r_3704_ = lean_box(v_res_3703_);
return v_r_3704_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__2(lean_object* v_00_u03b2_3705_, lean_object* v_data_3706_){
_start:
{
lean_object* v___x_3707_; 
v___x_3707_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__2___redArg(v_data_3706_);
return v___x_3707_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__3(lean_object* v_00_u03b2_3708_, lean_object* v_a_3709_, lean_object* v_b_3710_, lean_object* v_x_3711_){
_start:
{
lean_object* v___x_3712_; 
v___x_3712_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__3___redArg(v_a_3709_, v_b_3710_, v_x_3711_);
return v___x_3712_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__2_spec__5(lean_object* v_00_u03b2_3713_, lean_object* v_a_3714_, lean_object* v_x_3715_){
_start:
{
lean_object* v___x_3716_; 
v___x_3716_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__2_spec__5___redArg(v_a_3714_, v_x_3715_);
return v___x_3716_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__2_spec__5___boxed(lean_object* v_00_u03b2_3717_, lean_object* v_a_3718_, lean_object* v_x_3719_){
_start:
{
lean_object* v_res_3720_; 
v_res_3720_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__2_spec__5(v_00_u03b2_3717_, v_a_3718_, v_x_3719_);
lean_dec(v_x_3719_);
lean_dec_ref(v_a_3718_);
return v_res_3720_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_3721_, lean_object* v_i_3722_, lean_object* v_source_3723_, lean_object* v_target_3724_){
_start:
{
lean_object* v___x_3725_; 
v___x_3725_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__2_spec__3___redArg(v_i_3722_, v_source_3723_, v_target_3724_);
return v___x_3725_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__2_spec__3_spec__7(lean_object* v_00_u03b2_3726_, lean_object* v_x_3727_, lean_object* v_x_3728_){
_start:
{
lean_object* v___x_3729_; 
v___x_3729_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__2_spec__3_spec__7___redArg(v_x_3727_, v_x_3728_);
return v___x_3729_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp__1(){
_start:
{
lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; 
v___x_3735_ = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
v___x_3736_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__3));
v___x_3737_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp__1___closed__1));
v___x_3738_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___boxed), 10, 0);
v___x_3739_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3735_, v___x_3736_, v___x_3737_, v___x_3738_);
return v___x_3739_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp__1___boxed(lean_object* v_a_3740_){
_start:
{
lean_object* v_res_3741_; 
v_res_3741_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp__1();
return v_res_3741_;
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
lean_object* runtime_initialize_Lean_Elab_SyntheticMVars(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Grind_Sym(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
