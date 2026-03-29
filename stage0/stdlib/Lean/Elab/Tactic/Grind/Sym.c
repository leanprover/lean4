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
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
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
lean_object* v_es_692_; lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_713_; 
v_es_692_ = lean_ctor_get(v_x_689_, 0);
v_isSharedCheck_713_ = !lean_is_exclusive(v_x_689_);
if (v_isSharedCheck_713_ == 0)
{
v___x_694_ = v_x_689_;
v_isShared_695_ = v_isSharedCheck_713_;
goto v_resetjp_693_;
}
else
{
lean_inc(v_es_692_);
lean_dec(v_x_689_);
v___x_694_ = lean_box(0);
v_isShared_695_ = v_isSharedCheck_713_;
goto v_resetjp_693_;
}
v_resetjp_693_:
{
lean_object* v___x_696_; size_t v___x_697_; size_t v___x_698_; size_t v___x_699_; lean_object* v_j_700_; lean_object* v___x_701_; 
v___x_696_ = lean_box(2);
v___x_697_ = ((size_t)5ULL);
v___x_698_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0_spec__0___redArg___closed__1);
v___x_699_ = lean_usize_land(v_x_690_, v___x_698_);
v_j_700_ = lean_usize_to_nat(v___x_699_);
v___x_701_ = lean_array_get(v___x_696_, v_es_692_, v_j_700_);
lean_dec(v_j_700_);
lean_dec_ref(v_es_692_);
switch(lean_obj_tag(v___x_701_))
{
case 0:
{
lean_object* v_key_702_; lean_object* v_val_703_; uint8_t v___x_704_; 
v_key_702_ = lean_ctor_get(v___x_701_, 0);
lean_inc(v_key_702_);
v_val_703_ = lean_ctor_get(v___x_701_, 1);
lean_inc(v_val_703_);
lean_dec_ref(v___x_701_);
v___x_704_ = lean_name_eq(v_x_691_, v_key_702_);
lean_dec(v_key_702_);
if (v___x_704_ == 0)
{
lean_object* v___x_705_; 
lean_dec(v_val_703_);
lean_del_object(v___x_694_);
v___x_705_ = lean_box(0);
return v___x_705_;
}
else
{
lean_object* v___x_707_; 
if (v_isShared_695_ == 0)
{
lean_ctor_set_tag(v___x_694_, 1);
lean_ctor_set(v___x_694_, 0, v_val_703_);
v___x_707_ = v___x_694_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_708_; 
v_reuseFailAlloc_708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_708_, 0, v_val_703_);
v___x_707_ = v_reuseFailAlloc_708_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
return v___x_707_;
}
}
}
case 1:
{
lean_object* v_node_709_; size_t v___x_710_; 
lean_del_object(v___x_694_);
v_node_709_ = lean_ctor_get(v___x_701_, 0);
lean_inc(v_node_709_);
lean_dec_ref(v___x_701_);
v___x_710_ = lean_usize_shift_right(v_x_690_, v___x_697_);
v_x_689_ = v_node_709_;
v_x_690_ = v___x_710_;
goto _start;
}
default: 
{
lean_object* v___x_712_; 
lean_del_object(v___x_694_);
v___x_712_ = lean_box(0);
return v___x_712_;
}
}
}
}
else
{
lean_object* v_ks_714_; lean_object* v_vs_715_; lean_object* v___x_716_; lean_object* v___x_717_; 
v_ks_714_ = lean_ctor_get(v_x_689_, 0);
lean_inc_ref(v_ks_714_);
v_vs_715_ = lean_ctor_get(v_x_689_, 1);
lean_inc_ref(v_vs_715_);
lean_dec_ref(v_x_689_);
v___x_716_ = lean_unsigned_to_nat(0u);
v___x_717_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0_spec__0_spec__1___redArg(v_ks_714_, v_vs_715_, v___x_716_, v_x_691_);
lean_dec_ref(v_vs_715_);
lean_dec_ref(v_ks_714_);
return v___x_717_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0_spec__0___redArg___boxed(lean_object* v_x_718_, lean_object* v_x_719_, lean_object* v_x_720_){
_start:
{
size_t v_x_2008__boxed_721_; lean_object* v_res_722_; 
v_x_2008__boxed_721_ = lean_unbox_usize(v_x_719_);
lean_dec(v_x_719_);
v_res_722_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0_spec__0___redArg(v_x_718_, v_x_2008__boxed_721_, v_x_720_);
lean_dec(v_x_720_);
return v_res_722_;
}
}
static uint64_t _init_l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_723_; uint64_t v___x_724_; 
v___x_723_ = lean_unsigned_to_nat(1723u);
v___x_724_ = lean_uint64_of_nat(v___x_723_);
return v___x_724_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0___redArg(lean_object* v_x_725_, lean_object* v_x_726_){
_start:
{
uint64_t v___y_728_; 
if (lean_obj_tag(v_x_726_) == 0)
{
uint64_t v___x_731_; 
v___x_731_ = lean_uint64_once(&l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0___redArg___closed__0);
v___y_728_ = v___x_731_;
goto v___jp_727_;
}
else
{
uint64_t v_hash_732_; 
v_hash_732_ = lean_ctor_get_uint64(v_x_726_, sizeof(void*)*2);
v___y_728_ = v_hash_732_;
goto v___jp_727_;
}
v___jp_727_:
{
size_t v___x_729_; lean_object* v___x_730_; 
v___x_729_ = lean_uint64_to_usize(v___y_728_);
v___x_730_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0_spec__0___redArg(v_x_725_, v___x_729_, v_x_726_);
return v___x_730_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0___redArg___boxed(lean_object* v_x_733_, lean_object* v_x_734_){
_start:
{
lean_object* v_res_735_; 
v_res_735_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0___redArg(v_x_733_, v_x_734_);
lean_dec(v_x_734_);
return v_res_735_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2_spec__4_spec__5___redArg(lean_object* v_x_736_, lean_object* v_x_737_, lean_object* v_x_738_, lean_object* v_x_739_){
_start:
{
lean_object* v_ks_740_; lean_object* v_vs_741_; lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_765_; 
v_ks_740_ = lean_ctor_get(v_x_736_, 0);
v_vs_741_ = lean_ctor_get(v_x_736_, 1);
v_isSharedCheck_765_ = !lean_is_exclusive(v_x_736_);
if (v_isSharedCheck_765_ == 0)
{
v___x_743_ = v_x_736_;
v_isShared_744_ = v_isSharedCheck_765_;
goto v_resetjp_742_;
}
else
{
lean_inc(v_vs_741_);
lean_inc(v_ks_740_);
lean_dec(v_x_736_);
v___x_743_ = lean_box(0);
v_isShared_744_ = v_isSharedCheck_765_;
goto v_resetjp_742_;
}
v_resetjp_742_:
{
lean_object* v___x_745_; uint8_t v___x_746_; 
v___x_745_ = lean_array_get_size(v_ks_740_);
v___x_746_ = lean_nat_dec_lt(v_x_737_, v___x_745_);
if (v___x_746_ == 0)
{
lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_750_; 
lean_dec(v_x_737_);
v___x_747_ = lean_array_push(v_ks_740_, v_x_738_);
v___x_748_ = lean_array_push(v_vs_741_, v_x_739_);
if (v_isShared_744_ == 0)
{
lean_ctor_set(v___x_743_, 1, v___x_748_);
lean_ctor_set(v___x_743_, 0, v___x_747_);
v___x_750_ = v___x_743_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v___x_747_);
lean_ctor_set(v_reuseFailAlloc_751_, 1, v___x_748_);
v___x_750_ = v_reuseFailAlloc_751_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
return v___x_750_;
}
}
else
{
lean_object* v_k_x27_752_; uint8_t v___x_753_; 
v_k_x27_752_ = lean_array_fget_borrowed(v_ks_740_, v_x_737_);
v___x_753_ = lean_name_eq(v_x_738_, v_k_x27_752_);
if (v___x_753_ == 0)
{
lean_object* v___x_755_; 
if (v_isShared_744_ == 0)
{
v___x_755_ = v___x_743_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v_ks_740_);
lean_ctor_set(v_reuseFailAlloc_759_, 1, v_vs_741_);
v___x_755_ = v_reuseFailAlloc_759_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
lean_object* v___x_756_; lean_object* v___x_757_; 
v___x_756_ = lean_unsigned_to_nat(1u);
v___x_757_ = lean_nat_add(v_x_737_, v___x_756_);
lean_dec(v_x_737_);
v_x_736_ = v___x_755_;
v_x_737_ = v___x_757_;
goto _start;
}
}
else
{
lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_763_; 
v___x_760_ = lean_array_fset(v_ks_740_, v_x_737_, v_x_738_);
v___x_761_ = lean_array_fset(v_vs_741_, v_x_737_, v_x_739_);
lean_dec(v_x_737_);
if (v_isShared_744_ == 0)
{
lean_ctor_set(v___x_743_, 1, v___x_761_);
lean_ctor_set(v___x_743_, 0, v___x_760_);
v___x_763_ = v___x_743_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v___x_760_);
lean_ctor_set(v_reuseFailAlloc_764_, 1, v___x_761_);
v___x_763_ = v_reuseFailAlloc_764_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
return v___x_763_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2_spec__4___redArg(lean_object* v_n_766_, lean_object* v_k_767_, lean_object* v_v_768_){
_start:
{
lean_object* v___x_769_; lean_object* v___x_770_; 
v___x_769_ = lean_unsigned_to_nat(0u);
v___x_770_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2_spec__4_spec__5___redArg(v_n_766_, v___x_769_, v_k_767_, v_v_768_);
return v___x_770_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_771_; 
v___x_771_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_771_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2___redArg(lean_object* v_x_772_, size_t v_x_773_, size_t v_x_774_, lean_object* v_x_775_, lean_object* v_x_776_){
_start:
{
if (lean_obj_tag(v_x_772_) == 0)
{
lean_object* v_es_777_; size_t v___x_778_; size_t v___x_779_; size_t v___x_780_; size_t v___x_781_; lean_object* v_j_782_; lean_object* v___x_783_; uint8_t v___x_784_; 
v_es_777_ = lean_ctor_get(v_x_772_, 0);
v___x_778_ = ((size_t)5ULL);
v___x_779_ = ((size_t)1ULL);
v___x_780_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0_spec__0___redArg___closed__1);
v___x_781_ = lean_usize_land(v_x_773_, v___x_780_);
v_j_782_ = lean_usize_to_nat(v___x_781_);
v___x_783_ = lean_array_get_size(v_es_777_);
v___x_784_ = lean_nat_dec_lt(v_j_782_, v___x_783_);
if (v___x_784_ == 0)
{
lean_dec(v_j_782_);
lean_dec(v_x_776_);
lean_dec(v_x_775_);
return v_x_772_;
}
else
{
lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_821_; 
lean_inc_ref(v_es_777_);
v_isSharedCheck_821_ = !lean_is_exclusive(v_x_772_);
if (v_isSharedCheck_821_ == 0)
{
lean_object* v_unused_822_; 
v_unused_822_ = lean_ctor_get(v_x_772_, 0);
lean_dec(v_unused_822_);
v___x_786_ = v_x_772_;
v_isShared_787_ = v_isSharedCheck_821_;
goto v_resetjp_785_;
}
else
{
lean_dec(v_x_772_);
v___x_786_ = lean_box(0);
v_isShared_787_ = v_isSharedCheck_821_;
goto v_resetjp_785_;
}
v_resetjp_785_:
{
lean_object* v_v_788_; lean_object* v___x_789_; lean_object* v_xs_x27_790_; lean_object* v___y_792_; 
v_v_788_ = lean_array_fget(v_es_777_, v_j_782_);
v___x_789_ = lean_box(0);
v_xs_x27_790_ = lean_array_fset(v_es_777_, v_j_782_, v___x_789_);
switch(lean_obj_tag(v_v_788_))
{
case 0:
{
lean_object* v_key_797_; lean_object* v_val_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_808_; 
v_key_797_ = lean_ctor_get(v_v_788_, 0);
v_val_798_ = lean_ctor_get(v_v_788_, 1);
v_isSharedCheck_808_ = !lean_is_exclusive(v_v_788_);
if (v_isSharedCheck_808_ == 0)
{
v___x_800_ = v_v_788_;
v_isShared_801_ = v_isSharedCheck_808_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_val_798_);
lean_inc(v_key_797_);
lean_dec(v_v_788_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_808_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
uint8_t v___x_802_; 
v___x_802_ = lean_name_eq(v_x_775_, v_key_797_);
if (v___x_802_ == 0)
{
lean_object* v___x_803_; lean_object* v___x_804_; 
lean_del_object(v___x_800_);
v___x_803_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_797_, v_val_798_, v_x_775_, v_x_776_);
v___x_804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_804_, 0, v___x_803_);
v___y_792_ = v___x_804_;
goto v___jp_791_;
}
else
{
lean_object* v___x_806_; 
lean_dec(v_val_798_);
lean_dec(v_key_797_);
if (v_isShared_801_ == 0)
{
lean_ctor_set(v___x_800_, 1, v_x_776_);
lean_ctor_set(v___x_800_, 0, v_x_775_);
v___x_806_ = v___x_800_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v_x_775_);
lean_ctor_set(v_reuseFailAlloc_807_, 1, v_x_776_);
v___x_806_ = v_reuseFailAlloc_807_;
goto v_reusejp_805_;
}
v_reusejp_805_:
{
v___y_792_ = v___x_806_;
goto v___jp_791_;
}
}
}
}
case 1:
{
lean_object* v_node_809_; lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_819_; 
v_node_809_ = lean_ctor_get(v_v_788_, 0);
v_isSharedCheck_819_ = !lean_is_exclusive(v_v_788_);
if (v_isSharedCheck_819_ == 0)
{
v___x_811_ = v_v_788_;
v_isShared_812_ = v_isSharedCheck_819_;
goto v_resetjp_810_;
}
else
{
lean_inc(v_node_809_);
lean_dec(v_v_788_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_819_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
size_t v___x_813_; size_t v___x_814_; lean_object* v___x_815_; lean_object* v___x_817_; 
v___x_813_ = lean_usize_shift_right(v_x_773_, v___x_778_);
v___x_814_ = lean_usize_add(v_x_774_, v___x_779_);
v___x_815_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2___redArg(v_node_809_, v___x_813_, v___x_814_, v_x_775_, v_x_776_);
if (v_isShared_812_ == 0)
{
lean_ctor_set(v___x_811_, 0, v___x_815_);
v___x_817_ = v___x_811_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v___x_815_);
v___x_817_ = v_reuseFailAlloc_818_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
v___y_792_ = v___x_817_;
goto v___jp_791_;
}
}
}
default: 
{
lean_object* v___x_820_; 
v___x_820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_820_, 0, v_x_775_);
lean_ctor_set(v___x_820_, 1, v_x_776_);
v___y_792_ = v___x_820_;
goto v___jp_791_;
}
}
v___jp_791_:
{
lean_object* v___x_793_; lean_object* v___x_795_; 
v___x_793_ = lean_array_fset(v_xs_x27_790_, v_j_782_, v___y_792_);
lean_dec(v_j_782_);
if (v_isShared_787_ == 0)
{
lean_ctor_set(v___x_786_, 0, v___x_793_);
v___x_795_ = v___x_786_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v___x_793_);
v___x_795_ = v_reuseFailAlloc_796_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
return v___x_795_;
}
}
}
}
}
else
{
lean_object* v_ks_823_; lean_object* v_vs_824_; lean_object* v___x_826_; uint8_t v_isShared_827_; uint8_t v_isSharedCheck_844_; 
v_ks_823_ = lean_ctor_get(v_x_772_, 0);
v_vs_824_ = lean_ctor_get(v_x_772_, 1);
v_isSharedCheck_844_ = !lean_is_exclusive(v_x_772_);
if (v_isSharedCheck_844_ == 0)
{
v___x_826_ = v_x_772_;
v_isShared_827_ = v_isSharedCheck_844_;
goto v_resetjp_825_;
}
else
{
lean_inc(v_vs_824_);
lean_inc(v_ks_823_);
lean_dec(v_x_772_);
v___x_826_ = lean_box(0);
v_isShared_827_ = v_isSharedCheck_844_;
goto v_resetjp_825_;
}
v_resetjp_825_:
{
lean_object* v___x_829_; 
if (v_isShared_827_ == 0)
{
v___x_829_ = v___x_826_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_843_; 
v_reuseFailAlloc_843_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_843_, 0, v_ks_823_);
lean_ctor_set(v_reuseFailAlloc_843_, 1, v_vs_824_);
v___x_829_ = v_reuseFailAlloc_843_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
lean_object* v_newNode_830_; uint8_t v___y_832_; size_t v___x_838_; uint8_t v___x_839_; 
v_newNode_830_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2_spec__4___redArg(v___x_829_, v_x_775_, v_x_776_);
v___x_838_ = ((size_t)7ULL);
v___x_839_ = lean_usize_dec_le(v___x_838_, v_x_774_);
if (v___x_839_ == 0)
{
lean_object* v___x_840_; lean_object* v___x_841_; uint8_t v___x_842_; 
v___x_840_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_830_);
v___x_841_ = lean_unsigned_to_nat(4u);
v___x_842_ = lean_nat_dec_lt(v___x_840_, v___x_841_);
lean_dec(v___x_840_);
v___y_832_ = v___x_842_;
goto v___jp_831_;
}
else
{
v___y_832_ = v___x_839_;
goto v___jp_831_;
}
v___jp_831_:
{
if (v___y_832_ == 0)
{
lean_object* v_ks_833_; lean_object* v_vs_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; 
v_ks_833_ = lean_ctor_get(v_newNode_830_, 0);
lean_inc_ref(v_ks_833_);
v_vs_834_ = lean_ctor_get(v_newNode_830_, 1);
lean_inc_ref(v_vs_834_);
lean_dec_ref(v_newNode_830_);
v___x_835_ = lean_unsigned_to_nat(0u);
v___x_836_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2___redArg___closed__0);
v___x_837_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2_spec__5___redArg(v_x_774_, v_ks_833_, v_vs_834_, v___x_835_, v___x_836_);
lean_dec_ref(v_vs_834_);
lean_dec_ref(v_ks_833_);
return v___x_837_;
}
else
{
return v_newNode_830_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2_spec__5___redArg(size_t v_depth_845_, lean_object* v_keys_846_, lean_object* v_vals_847_, lean_object* v_i_848_, lean_object* v_entries_849_){
_start:
{
lean_object* v___x_850_; uint8_t v___x_851_; 
v___x_850_ = lean_array_get_size(v_keys_846_);
v___x_851_ = lean_nat_dec_lt(v_i_848_, v___x_850_);
if (v___x_851_ == 0)
{
lean_dec(v_i_848_);
return v_entries_849_;
}
else
{
lean_object* v_k_852_; lean_object* v_v_853_; uint64_t v___y_855_; 
v_k_852_ = lean_array_fget_borrowed(v_keys_846_, v_i_848_);
v_v_853_ = lean_array_fget_borrowed(v_vals_847_, v_i_848_);
if (lean_obj_tag(v_k_852_) == 0)
{
uint64_t v___x_866_; 
v___x_866_ = lean_uint64_once(&l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0___redArg___closed__0);
v___y_855_ = v___x_866_;
goto v___jp_854_;
}
else
{
uint64_t v_hash_867_; 
v_hash_867_ = lean_ctor_get_uint64(v_k_852_, sizeof(void*)*2);
v___y_855_ = v_hash_867_;
goto v___jp_854_;
}
v___jp_854_:
{
size_t v_h_856_; size_t v___x_857_; lean_object* v___x_858_; size_t v___x_859_; size_t v___x_860_; size_t v___x_861_; size_t v_h_862_; lean_object* v___x_863_; lean_object* v___x_864_; 
v_h_856_ = lean_uint64_to_usize(v___y_855_);
v___x_857_ = ((size_t)5ULL);
v___x_858_ = lean_unsigned_to_nat(1u);
v___x_859_ = ((size_t)1ULL);
v___x_860_ = lean_usize_sub(v_depth_845_, v___x_859_);
v___x_861_ = lean_usize_mul(v___x_857_, v___x_860_);
v_h_862_ = lean_usize_shift_right(v_h_856_, v___x_861_);
v___x_863_ = lean_nat_add(v_i_848_, v___x_858_);
lean_dec(v_i_848_);
lean_inc(v_v_853_);
lean_inc(v_k_852_);
v___x_864_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2___redArg(v_entries_849_, v_h_862_, v_depth_845_, v_k_852_, v_v_853_);
v_i_848_ = v___x_863_;
v_entries_849_ = v___x_864_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_depth_868_, lean_object* v_keys_869_, lean_object* v_vals_870_, lean_object* v_i_871_, lean_object* v_entries_872_){
_start:
{
size_t v_depth_boxed_873_; lean_object* v_res_874_; 
v_depth_boxed_873_ = lean_unbox_usize(v_depth_868_);
lean_dec(v_depth_868_);
v_res_874_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2_spec__5___redArg(v_depth_boxed_873_, v_keys_869_, v_vals_870_, v_i_871_, v_entries_872_);
lean_dec_ref(v_vals_870_);
lean_dec_ref(v_keys_869_);
return v_res_874_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2___redArg___boxed(lean_object* v_x_875_, lean_object* v_x_876_, lean_object* v_x_877_, lean_object* v_x_878_, lean_object* v_x_879_){
_start:
{
size_t v_x_2182__boxed_880_; size_t v_x_2183__boxed_881_; lean_object* v_res_882_; 
v_x_2182__boxed_880_ = lean_unbox_usize(v_x_876_);
lean_dec(v_x_876_);
v_x_2183__boxed_881_ = lean_unbox_usize(v_x_877_);
lean_dec(v_x_877_);
v_res_882_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2___redArg(v_x_875_, v_x_2182__boxed_880_, v_x_2183__boxed_881_, v_x_878_, v_x_879_);
return v_res_882_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1___redArg(lean_object* v_x_883_, lean_object* v_x_884_, lean_object* v_x_885_){
_start:
{
uint64_t v___y_887_; 
if (lean_obj_tag(v_x_884_) == 0)
{
uint64_t v___x_891_; 
v___x_891_ = lean_uint64_once(&l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0___redArg___closed__0);
v___y_887_ = v___x_891_;
goto v___jp_886_;
}
else
{
uint64_t v_hash_892_; 
v_hash_892_ = lean_ctor_get_uint64(v_x_884_, sizeof(void*)*2);
v___y_887_ = v_hash_892_;
goto v___jp_886_;
}
v___jp_886_:
{
size_t v___x_888_; size_t v___x_889_; lean_object* v___x_890_; 
v___x_888_ = lean_uint64_to_usize(v___y_887_);
v___x_889_ = ((size_t)1ULL);
v___x_890_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2___redArg(v_x_883_, v___x_888_, v___x_889_, v_x_884_, v_x_885_);
return v___x_890_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule___redArg(lean_object* v_declName_893_, lean_object* v_a_894_, lean_object* v_a_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_){
_start:
{
lean_object* v___x_900_; lean_object* v_cache_901_; lean_object* v_backwardRuleName_902_; lean_object* v___x_903_; 
v___x_900_ = lean_st_ref_get(v_a_894_);
v_cache_901_ = lean_ctor_get(v___x_900_, 3);
lean_inc_ref(v_cache_901_);
lean_dec(v___x_900_);
v_backwardRuleName_902_ = lean_ctor_get(v_cache_901_, 0);
lean_inc_ref(v_backwardRuleName_902_);
lean_dec_ref(v_cache_901_);
v___x_903_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0___redArg(v_backwardRuleName_902_, v_declName_893_);
if (lean_obj_tag(v___x_903_) == 1)
{
lean_object* v_val_904_; lean_object* v___x_906_; uint8_t v_isShared_907_; uint8_t v_isSharedCheck_911_; 
lean_dec(v_declName_893_);
v_val_904_ = lean_ctor_get(v___x_903_, 0);
v_isSharedCheck_911_ = !lean_is_exclusive(v___x_903_);
if (v_isSharedCheck_911_ == 0)
{
v___x_906_ = v___x_903_;
v_isShared_907_ = v_isSharedCheck_911_;
goto v_resetjp_905_;
}
else
{
lean_inc(v_val_904_);
lean_dec(v___x_903_);
v___x_906_ = lean_box(0);
v_isShared_907_ = v_isSharedCheck_911_;
goto v_resetjp_905_;
}
v_resetjp_905_:
{
lean_object* v___x_909_; 
if (v_isShared_907_ == 0)
{
lean_ctor_set_tag(v___x_906_, 0);
v___x_909_ = v___x_906_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v_val_904_);
v___x_909_ = v_reuseFailAlloc_910_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
return v___x_909_;
}
}
}
else
{
lean_object* v___x_912_; lean_object* v___x_913_; 
lean_dec(v___x_903_);
v___x_912_ = lean_box(0);
lean_inc(v_declName_893_);
v___x_913_ = l_Lean_Meta_Sym_mkBackwardRuleFromDecl(v_declName_893_, v___x_912_, v_a_895_, v_a_896_, v_a_897_, v_a_898_);
if (lean_obj_tag(v___x_913_) == 0)
{
lean_object* v_a_914_; lean_object* v___x_916_; uint8_t v_isShared_917_; uint8_t v_isSharedCheck_945_; 
v_a_914_ = lean_ctor_get(v___x_913_, 0);
v_isSharedCheck_945_ = !lean_is_exclusive(v___x_913_);
if (v_isSharedCheck_945_ == 0)
{
v___x_916_ = v___x_913_;
v_isShared_917_ = v_isSharedCheck_945_;
goto v_resetjp_915_;
}
else
{
lean_inc(v_a_914_);
lean_dec(v___x_913_);
v___x_916_ = lean_box(0);
v_isShared_917_ = v_isSharedCheck_945_;
goto v_resetjp_915_;
}
v_resetjp_915_:
{
lean_object* v___x_918_; lean_object* v_cache_919_; lean_object* v_symState_920_; lean_object* v_grindState_921_; lean_object* v_goals_922_; lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_944_; 
v___x_918_ = lean_st_ref_take(v_a_894_);
v_cache_919_ = lean_ctor_get(v___x_918_, 3);
v_symState_920_ = lean_ctor_get(v___x_918_, 0);
v_grindState_921_ = lean_ctor_get(v___x_918_, 1);
v_goals_922_ = lean_ctor_get(v___x_918_, 2);
v_isSharedCheck_944_ = !lean_is_exclusive(v___x_918_);
if (v_isSharedCheck_944_ == 0)
{
v___x_924_ = v___x_918_;
v_isShared_925_ = v_isSharedCheck_944_;
goto v_resetjp_923_;
}
else
{
lean_inc(v_cache_919_);
lean_inc(v_goals_922_);
lean_inc(v_grindState_921_);
lean_inc(v_symState_920_);
lean_dec(v___x_918_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_944_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
lean_object* v_backwardRuleName_926_; lean_object* v_backwardRuleSyntax_927_; lean_object* v_simpState_928_; lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_943_; 
v_backwardRuleName_926_ = lean_ctor_get(v_cache_919_, 0);
v_backwardRuleSyntax_927_ = lean_ctor_get(v_cache_919_, 1);
v_simpState_928_ = lean_ctor_get(v_cache_919_, 2);
v_isSharedCheck_943_ = !lean_is_exclusive(v_cache_919_);
if (v_isSharedCheck_943_ == 0)
{
v___x_930_ = v_cache_919_;
v_isShared_931_ = v_isSharedCheck_943_;
goto v_resetjp_929_;
}
else
{
lean_inc(v_simpState_928_);
lean_inc(v_backwardRuleSyntax_927_);
lean_inc(v_backwardRuleName_926_);
lean_dec(v_cache_919_);
v___x_930_ = lean_box(0);
v_isShared_931_ = v_isSharedCheck_943_;
goto v_resetjp_929_;
}
v_resetjp_929_:
{
lean_object* v___x_932_; lean_object* v___x_934_; 
lean_inc(v_a_914_);
v___x_932_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1___redArg(v_backwardRuleName_926_, v_declName_893_, v_a_914_);
if (v_isShared_931_ == 0)
{
lean_ctor_set(v___x_930_, 0, v___x_932_);
v___x_934_ = v___x_930_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_942_; 
v_reuseFailAlloc_942_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_942_, 0, v___x_932_);
lean_ctor_set(v_reuseFailAlloc_942_, 1, v_backwardRuleSyntax_927_);
lean_ctor_set(v_reuseFailAlloc_942_, 2, v_simpState_928_);
v___x_934_ = v_reuseFailAlloc_942_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
lean_object* v___x_936_; 
if (v_isShared_925_ == 0)
{
lean_ctor_set(v___x_924_, 3, v___x_934_);
v___x_936_ = v___x_924_;
goto v_reusejp_935_;
}
else
{
lean_object* v_reuseFailAlloc_941_; 
v_reuseFailAlloc_941_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_941_, 0, v_symState_920_);
lean_ctor_set(v_reuseFailAlloc_941_, 1, v_grindState_921_);
lean_ctor_set(v_reuseFailAlloc_941_, 2, v_goals_922_);
lean_ctor_set(v_reuseFailAlloc_941_, 3, v___x_934_);
v___x_936_ = v_reuseFailAlloc_941_;
goto v_reusejp_935_;
}
v_reusejp_935_:
{
lean_object* v___x_937_; lean_object* v___x_939_; 
v___x_937_ = lean_st_ref_set(v_a_894_, v___x_936_);
if (v_isShared_917_ == 0)
{
v___x_939_ = v___x_916_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_940_; 
v_reuseFailAlloc_940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_940_, 0, v_a_914_);
v___x_939_ = v_reuseFailAlloc_940_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
return v___x_939_;
}
}
}
}
}
}
}
else
{
lean_dec(v_declName_893_);
return v___x_913_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule___redArg___boxed(lean_object* v_declName_946_, lean_object* v_a_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_){
_start:
{
lean_object* v_res_953_; 
v_res_953_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule___redArg(v_declName_946_, v_a_947_, v_a_948_, v_a_949_, v_a_950_, v_a_951_);
lean_dec(v_a_951_);
lean_dec_ref(v_a_950_);
lean_dec(v_a_949_);
lean_dec_ref(v_a_948_);
lean_dec(v_a_947_);
return v_res_953_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule(lean_object* v_declName_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_){
_start:
{
lean_object* v___x_964_; 
v___x_964_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule___redArg(v_declName_954_, v_a_956_, v_a_959_, v_a_960_, v_a_961_, v_a_962_);
return v___x_964_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule___boxed(lean_object* v_declName_965_, lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_, lean_object* v_a_969_, lean_object* v_a_970_, lean_object* v_a_971_, lean_object* v_a_972_, lean_object* v_a_973_, lean_object* v_a_974_){
_start:
{
lean_object* v_res_975_; 
v_res_975_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule(v_declName_965_, v_a_966_, v_a_967_, v_a_968_, v_a_969_, v_a_970_, v_a_971_, v_a_972_, v_a_973_);
lean_dec(v_a_973_);
lean_dec_ref(v_a_972_);
lean_dec(v_a_971_);
lean_dec_ref(v_a_970_);
lean_dec(v_a_969_);
lean_dec_ref(v_a_968_);
lean_dec(v_a_967_);
lean_dec_ref(v_a_966_);
return v_res_975_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0(lean_object* v_00_u03b2_976_, lean_object* v_x_977_, lean_object* v_x_978_){
_start:
{
lean_object* v___x_979_; 
v___x_979_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0___redArg(v_x_977_, v_x_978_);
return v___x_979_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0___boxed(lean_object* v_00_u03b2_980_, lean_object* v_x_981_, lean_object* v_x_982_){
_start:
{
lean_object* v_res_983_; 
v_res_983_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0(v_00_u03b2_980_, v_x_981_, v_x_982_);
lean_dec(v_x_982_);
return v_res_983_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1(lean_object* v_00_u03b2_984_, lean_object* v_x_985_, lean_object* v_x_986_, lean_object* v_x_987_){
_start:
{
lean_object* v___x_988_; 
v___x_988_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1___redArg(v_x_985_, v_x_986_, v_x_987_);
return v___x_988_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0_spec__0(lean_object* v_00_u03b2_989_, lean_object* v_x_990_, size_t v_x_991_, lean_object* v_x_992_){
_start:
{
lean_object* v___x_993_; 
v___x_993_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0_spec__0___redArg(v_x_990_, v_x_991_, v_x_992_);
return v___x_993_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0_spec__0___boxed(lean_object* v_00_u03b2_994_, lean_object* v_x_995_, lean_object* v_x_996_, lean_object* v_x_997_){
_start:
{
size_t v_x_2460__boxed_998_; lean_object* v_res_999_; 
v_x_2460__boxed_998_ = lean_unbox_usize(v_x_996_);
lean_dec(v_x_996_);
v_res_999_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0_spec__0(v_00_u03b2_994_, v_x_995_, v_x_2460__boxed_998_, v_x_997_);
lean_dec(v_x_997_);
return v_res_999_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2(lean_object* v_00_u03b2_1000_, lean_object* v_x_1001_, size_t v_x_1002_, size_t v_x_1003_, lean_object* v_x_1004_, lean_object* v_x_1005_){
_start:
{
lean_object* v___x_1006_; 
v___x_1006_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2___redArg(v_x_1001_, v_x_1002_, v_x_1003_, v_x_1004_, v_x_1005_);
return v___x_1006_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1007_, lean_object* v_x_1008_, lean_object* v_x_1009_, lean_object* v_x_1010_, lean_object* v_x_1011_, lean_object* v_x_1012_){
_start:
{
size_t v_x_2471__boxed_1013_; size_t v_x_2472__boxed_1014_; lean_object* v_res_1015_; 
v_x_2471__boxed_1013_ = lean_unbox_usize(v_x_1009_);
lean_dec(v_x_1009_);
v_x_2472__boxed_1014_ = lean_unbox_usize(v_x_1010_);
lean_dec(v_x_1010_);
v_res_1015_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2(v_00_u03b2_1007_, v_x_1008_, v_x_2471__boxed_1013_, v_x_2472__boxed_1014_, v_x_1011_, v_x_1012_);
return v_res_1015_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1016_, lean_object* v_keys_1017_, lean_object* v_vals_1018_, lean_object* v_heq_1019_, lean_object* v_i_1020_, lean_object* v_k_1021_){
_start:
{
lean_object* v___x_1022_; 
v___x_1022_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0_spec__0_spec__1___redArg(v_keys_1017_, v_vals_1018_, v_i_1020_, v_k_1021_);
return v___x_1022_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1023_, lean_object* v_keys_1024_, lean_object* v_vals_1025_, lean_object* v_heq_1026_, lean_object* v_i_1027_, lean_object* v_k_1028_){
_start:
{
lean_object* v_res_1029_; 
v_res_1029_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0_spec__0_spec__1(v_00_u03b2_1023_, v_keys_1024_, v_vals_1025_, v_heq_1026_, v_i_1027_, v_k_1028_);
lean_dec(v_k_1028_);
lean_dec_ref(v_vals_1025_);
lean_dec_ref(v_keys_1024_);
return v_res_1029_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_1030_, lean_object* v_n_1031_, lean_object* v_k_1032_, lean_object* v_v_1033_){
_start:
{
lean_object* v___x_1034_; 
v___x_1034_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2_spec__4___redArg(v_n_1031_, v_k_1032_, v_v_1033_);
return v___x_1034_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_1035_, size_t v_depth_1036_, lean_object* v_keys_1037_, lean_object* v_vals_1038_, lean_object* v_heq_1039_, lean_object* v_i_1040_, lean_object* v_entries_1041_){
_start:
{
lean_object* v___x_1042_; 
v___x_1042_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2_spec__5___redArg(v_depth_1036_, v_keys_1037_, v_vals_1038_, v_i_1040_, v_entries_1041_);
return v___x_1042_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1043_, lean_object* v_depth_1044_, lean_object* v_keys_1045_, lean_object* v_vals_1046_, lean_object* v_heq_1047_, lean_object* v_i_1048_, lean_object* v_entries_1049_){
_start:
{
size_t v_depth_boxed_1050_; lean_object* v_res_1051_; 
v_depth_boxed_1050_ = lean_unbox_usize(v_depth_1044_);
lean_dec(v_depth_1044_);
v_res_1051_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2_spec__5(v_00_u03b2_1043_, v_depth_boxed_1050_, v_keys_1045_, v_vals_1046_, v_heq_1047_, v_i_1048_, v_entries_1049_);
lean_dec_ref(v_vals_1046_);
lean_dec_ref(v_keys_1045_);
return v_res_1051_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_1052_, lean_object* v_x_1053_, lean_object* v_x_1054_, lean_object* v_x_1055_, lean_object* v_x_1056_){
_start:
{
lean_object* v___x_1057_; 
v___x_1057_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2_spec__4_spec__5___redArg(v_x_1053_, v_x_1054_, v_x_1055_, v_x_1056_);
return v___x_1057_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__1___redArg(lean_object* v_e_1058_, lean_object* v___y_1059_){
_start:
{
uint8_t v___x_1061_; 
v___x_1061_ = l_Lean_Expr_hasMVar(v_e_1058_);
if (v___x_1061_ == 0)
{
lean_object* v___x_1062_; 
v___x_1062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1062_, 0, v_e_1058_);
return v___x_1062_;
}
else
{
lean_object* v___x_1063_; lean_object* v_mctx_1064_; lean_object* v___x_1065_; lean_object* v_fst_1066_; lean_object* v_snd_1067_; lean_object* v___x_1068_; lean_object* v_cache_1069_; lean_object* v_zetaDeltaFVarIds_1070_; lean_object* v_postponed_1071_; lean_object* v_diag_1072_; lean_object* v___x_1074_; uint8_t v_isShared_1075_; uint8_t v_isSharedCheck_1081_; 
v___x_1063_ = lean_st_ref_get(v___y_1059_);
v_mctx_1064_ = lean_ctor_get(v___x_1063_, 0);
lean_inc_ref(v_mctx_1064_);
lean_dec(v___x_1063_);
v___x_1065_ = l_Lean_instantiateMVarsCore(v_mctx_1064_, v_e_1058_);
v_fst_1066_ = lean_ctor_get(v___x_1065_, 0);
lean_inc(v_fst_1066_);
v_snd_1067_ = lean_ctor_get(v___x_1065_, 1);
lean_inc(v_snd_1067_);
lean_dec_ref(v___x_1065_);
v___x_1068_ = lean_st_ref_take(v___y_1059_);
v_cache_1069_ = lean_ctor_get(v___x_1068_, 1);
v_zetaDeltaFVarIds_1070_ = lean_ctor_get(v___x_1068_, 2);
v_postponed_1071_ = lean_ctor_get(v___x_1068_, 3);
v_diag_1072_ = lean_ctor_get(v___x_1068_, 4);
v_isSharedCheck_1081_ = !lean_is_exclusive(v___x_1068_);
if (v_isSharedCheck_1081_ == 0)
{
lean_object* v_unused_1082_; 
v_unused_1082_ = lean_ctor_get(v___x_1068_, 0);
lean_dec(v_unused_1082_);
v___x_1074_ = v___x_1068_;
v_isShared_1075_ = v_isSharedCheck_1081_;
goto v_resetjp_1073_;
}
else
{
lean_inc(v_diag_1072_);
lean_inc(v_postponed_1071_);
lean_inc(v_zetaDeltaFVarIds_1070_);
lean_inc(v_cache_1069_);
lean_dec(v___x_1068_);
v___x_1074_ = lean_box(0);
v_isShared_1075_ = v_isSharedCheck_1081_;
goto v_resetjp_1073_;
}
v_resetjp_1073_:
{
lean_object* v___x_1077_; 
if (v_isShared_1075_ == 0)
{
lean_ctor_set(v___x_1074_, 0, v_snd_1067_);
v___x_1077_ = v___x_1074_;
goto v_reusejp_1076_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v_snd_1067_);
lean_ctor_set(v_reuseFailAlloc_1080_, 1, v_cache_1069_);
lean_ctor_set(v_reuseFailAlloc_1080_, 2, v_zetaDeltaFVarIds_1070_);
lean_ctor_set(v_reuseFailAlloc_1080_, 3, v_postponed_1071_);
lean_ctor_set(v_reuseFailAlloc_1080_, 4, v_diag_1072_);
v___x_1077_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1076_;
}
v_reusejp_1076_:
{
lean_object* v___x_1078_; lean_object* v___x_1079_; 
v___x_1078_ = lean_st_ref_set(v___y_1059_, v___x_1077_);
v___x_1079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1079_, 0, v_fst_1066_);
return v___x_1079_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__1___redArg___boxed(lean_object* v_e_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_){
_start:
{
lean_object* v_res_1086_; 
v_res_1086_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__1___redArg(v_e_1083_, v___y_1084_);
lean_dec(v___y_1084_);
return v_res_1086_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__1(lean_object* v_e_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_){
_start:
{
lean_object* v___x_1097_; 
v___x_1097_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__1___redArg(v_e_1087_, v___y_1093_);
return v___x_1097_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__1___boxed(lean_object* v_e_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_){
_start:
{
lean_object* v_res_1108_; 
v_res_1108_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__1(v_e_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_);
lean_dec(v___y_1106_);
lean_dec_ref(v___y_1105_);
lean_dec(v___y_1104_);
lean_dec_ref(v___y_1103_);
lean_dec(v___y_1102_);
lean_dec_ref(v___y_1101_);
lean_dec(v___y_1100_);
lean_dec_ref(v___y_1099_);
return v_res_1108_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm___lam__0(lean_object* v_term_1109_, lean_object* v___x_1110_, uint8_t v___x_1111_, uint8_t v___x_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_){
_start:
{
lean_object* v___x_1122_; 
v___x_1122_ = l_Lean_Elab_Term_elabTerm(v_term_1109_, v___x_1110_, v___x_1111_, v___x_1111_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_, v___y_1120_);
if (lean_obj_tag(v___x_1122_) == 0)
{
lean_object* v_a_1123_; uint8_t v___x_1124_; lean_object* v___x_1125_; 
v_a_1123_ = lean_ctor_get(v___x_1122_, 0);
lean_inc(v_a_1123_);
lean_dec_ref(v___x_1122_);
v___x_1124_ = 1;
v___x_1125_ = l_Lean_Elab_Term_synthesizeSyntheticMVars(v___x_1124_, v___x_1112_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_, v___y_1120_);
if (lean_obj_tag(v___x_1125_) == 0)
{
lean_object* v___x_1126_; 
lean_dec_ref(v___x_1125_);
v___x_1126_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__1___redArg(v_a_1123_, v___y_1118_);
return v___x_1126_;
}
else
{
lean_object* v_a_1127_; lean_object* v___x_1129_; uint8_t v_isShared_1130_; uint8_t v_isSharedCheck_1134_; 
lean_dec(v_a_1123_);
v_a_1127_ = lean_ctor_get(v___x_1125_, 0);
v_isSharedCheck_1134_ = !lean_is_exclusive(v___x_1125_);
if (v_isSharedCheck_1134_ == 0)
{
v___x_1129_ = v___x_1125_;
v_isShared_1130_ = v_isSharedCheck_1134_;
goto v_resetjp_1128_;
}
else
{
lean_inc(v_a_1127_);
lean_dec(v___x_1125_);
v___x_1129_ = lean_box(0);
v_isShared_1130_ = v_isSharedCheck_1134_;
goto v_resetjp_1128_;
}
v_resetjp_1128_:
{
lean_object* v___x_1132_; 
if (v_isShared_1130_ == 0)
{
v___x_1132_ = v___x_1129_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v_a_1127_);
v___x_1132_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
return v___x_1132_;
}
}
}
}
else
{
return v___x_1122_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm___lam__0___boxed(lean_object* v_term_1135_, lean_object* v___x_1136_, lean_object* v___x_1137_, lean_object* v___x_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_){
_start:
{
uint8_t v___x_3591__boxed_1148_; uint8_t v___x_3592__boxed_1149_; lean_object* v_res_1150_; 
v___x_3591__boxed_1148_ = lean_unbox(v___x_1137_);
v___x_3592__boxed_1149_ = lean_unbox(v___x_1138_);
v_res_1150_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm___lam__0(v_term_1135_, v___x_1136_, v___x_3591__boxed_1148_, v___x_3592__boxed_1149_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_);
lean_dec(v___y_1146_);
lean_dec_ref(v___y_1145_);
lean_dec(v___y_1144_);
lean_dec_ref(v___y_1143_);
lean_dec(v___y_1142_);
lean_dec_ref(v___y_1141_);
lean_dec(v___y_1140_);
lean_dec_ref(v___y_1139_);
return v_res_1150_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3_spec__5_spec__6___redArg(lean_object* v_x_1151_, lean_object* v_x_1152_, lean_object* v_x_1153_, lean_object* v_x_1154_){
_start:
{
lean_object* v_ks_1155_; lean_object* v_vs_1156_; lean_object* v___x_1158_; uint8_t v_isShared_1159_; uint8_t v_isSharedCheck_1185_; 
v_ks_1155_ = lean_ctor_get(v_x_1151_, 0);
v_vs_1156_ = lean_ctor_get(v_x_1151_, 1);
v_isSharedCheck_1185_ = !lean_is_exclusive(v_x_1151_);
if (v_isSharedCheck_1185_ == 0)
{
v___x_1158_ = v_x_1151_;
v_isShared_1159_ = v_isSharedCheck_1185_;
goto v_resetjp_1157_;
}
else
{
lean_inc(v_vs_1156_);
lean_inc(v_ks_1155_);
lean_dec(v_x_1151_);
v___x_1158_ = lean_box(0);
v_isShared_1159_ = v_isSharedCheck_1185_;
goto v_resetjp_1157_;
}
v_resetjp_1157_:
{
uint8_t v___y_1161_; lean_object* v___x_1173_; uint8_t v___x_1174_; 
v___x_1173_ = lean_array_get_size(v_ks_1155_);
v___x_1174_ = lean_nat_dec_lt(v_x_1152_, v___x_1173_);
if (v___x_1174_ == 0)
{
lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; 
lean_del_object(v___x_1158_);
lean_dec(v_x_1152_);
v___x_1175_ = lean_array_push(v_ks_1155_, v_x_1153_);
v___x_1176_ = lean_array_push(v_vs_1156_, v_x_1154_);
v___x_1177_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1177_, 0, v___x_1175_);
lean_ctor_set(v___x_1177_, 1, v___x_1176_);
return v___x_1177_;
}
else
{
lean_object* v_fst_1178_; lean_object* v_snd_1179_; lean_object* v_k_x27_1180_; lean_object* v_fst_1181_; lean_object* v_snd_1182_; uint8_t v___x_1183_; 
v_fst_1178_ = lean_ctor_get(v_x_1153_, 0);
v_snd_1179_ = lean_ctor_get(v_x_1153_, 1);
v_k_x27_1180_ = lean_array_fget_borrowed(v_ks_1155_, v_x_1152_);
v_fst_1181_ = lean_ctor_get(v_k_x27_1180_, 0);
v_snd_1182_ = lean_ctor_get(v_k_x27_1180_, 1);
v___x_1183_ = lean_nat_dec_eq(v_fst_1178_, v_fst_1181_);
if (v___x_1183_ == 0)
{
v___y_1161_ = v___x_1183_;
goto v___jp_1160_;
}
else
{
uint8_t v___x_1184_; 
v___x_1184_ = lean_nat_dec_eq(v_snd_1179_, v_snd_1182_);
v___y_1161_ = v___x_1184_;
goto v___jp_1160_;
}
}
v___jp_1160_:
{
if (v___y_1161_ == 0)
{
lean_object* v___x_1163_; 
if (v_isShared_1159_ == 0)
{
v___x_1163_ = v___x_1158_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1167_; 
v_reuseFailAlloc_1167_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1167_, 0, v_ks_1155_);
lean_ctor_set(v_reuseFailAlloc_1167_, 1, v_vs_1156_);
v___x_1163_ = v_reuseFailAlloc_1167_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
lean_object* v___x_1164_; lean_object* v___x_1165_; 
v___x_1164_ = lean_unsigned_to_nat(1u);
v___x_1165_ = lean_nat_add(v_x_1152_, v___x_1164_);
lean_dec(v_x_1152_);
v_x_1151_ = v___x_1163_;
v_x_1152_ = v___x_1165_;
goto _start;
}
}
else
{
lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1171_; 
v___x_1168_ = lean_array_fset(v_ks_1155_, v_x_1152_, v_x_1153_);
v___x_1169_ = lean_array_fset(v_vs_1156_, v_x_1152_, v_x_1154_);
lean_dec(v_x_1152_);
if (v_isShared_1159_ == 0)
{
lean_ctor_set(v___x_1158_, 1, v___x_1169_);
lean_ctor_set(v___x_1158_, 0, v___x_1168_);
v___x_1171_ = v___x_1158_;
goto v_reusejp_1170_;
}
else
{
lean_object* v_reuseFailAlloc_1172_; 
v_reuseFailAlloc_1172_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1172_, 0, v___x_1168_);
lean_ctor_set(v_reuseFailAlloc_1172_, 1, v___x_1169_);
v___x_1171_ = v_reuseFailAlloc_1172_;
goto v_reusejp_1170_;
}
v_reusejp_1170_:
{
return v___x_1171_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3_spec__5___redArg(lean_object* v_n_1186_, lean_object* v_k_1187_, lean_object* v_v_1188_){
_start:
{
lean_object* v___x_1189_; lean_object* v___x_1190_; 
v___x_1189_ = lean_unsigned_to_nat(0u);
v___x_1190_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3_spec__5_spec__6___redArg(v_n_1186_, v___x_1189_, v_k_1187_, v_v_1188_);
return v___x_1190_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_1191_; 
v___x_1191_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1191_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3___redArg(lean_object* v_x_1192_, size_t v_x_1193_, size_t v_x_1194_, lean_object* v_x_1195_, lean_object* v_x_1196_){
_start:
{
if (lean_obj_tag(v_x_1192_) == 0)
{
lean_object* v_es_1197_; size_t v___x_1198_; size_t v___x_1199_; size_t v___x_1200_; size_t v___x_1201_; lean_object* v_j_1202_; lean_object* v___x_1203_; uint8_t v___x_1204_; 
v_es_1197_ = lean_ctor_get(v_x_1192_, 0);
v___x_1198_ = ((size_t)5ULL);
v___x_1199_ = ((size_t)1ULL);
v___x_1200_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0_spec__0___redArg___closed__1);
v___x_1201_ = lean_usize_land(v_x_1193_, v___x_1200_);
v_j_1202_ = lean_usize_to_nat(v___x_1201_);
v___x_1203_ = lean_array_get_size(v_es_1197_);
v___x_1204_ = lean_nat_dec_lt(v_j_1202_, v___x_1203_);
if (v___x_1204_ == 0)
{
lean_dec(v_j_1202_);
lean_dec(v_x_1196_);
lean_dec_ref(v_x_1195_);
return v_x_1192_;
}
else
{
lean_object* v___x_1206_; uint8_t v_isShared_1207_; uint8_t v_isSharedCheck_1248_; 
lean_inc_ref(v_es_1197_);
v_isSharedCheck_1248_ = !lean_is_exclusive(v_x_1192_);
if (v_isSharedCheck_1248_ == 0)
{
lean_object* v_unused_1249_; 
v_unused_1249_ = lean_ctor_get(v_x_1192_, 0);
lean_dec(v_unused_1249_);
v___x_1206_ = v_x_1192_;
v_isShared_1207_ = v_isSharedCheck_1248_;
goto v_resetjp_1205_;
}
else
{
lean_dec(v_x_1192_);
v___x_1206_ = lean_box(0);
v_isShared_1207_ = v_isSharedCheck_1248_;
goto v_resetjp_1205_;
}
v_resetjp_1205_:
{
lean_object* v_v_1208_; lean_object* v___x_1209_; lean_object* v_xs_x27_1210_; lean_object* v___y_1212_; 
v_v_1208_ = lean_array_fget(v_es_1197_, v_j_1202_);
v___x_1209_ = lean_box(0);
v_xs_x27_1210_ = lean_array_fset(v_es_1197_, v_j_1202_, v___x_1209_);
switch(lean_obj_tag(v_v_1208_))
{
case 0:
{
lean_object* v_key_1217_; lean_object* v_val_1218_; lean_object* v___x_1220_; uint8_t v_isShared_1221_; uint8_t v_isSharedCheck_1235_; 
v_key_1217_ = lean_ctor_get(v_v_1208_, 0);
v_val_1218_ = lean_ctor_get(v_v_1208_, 1);
v_isSharedCheck_1235_ = !lean_is_exclusive(v_v_1208_);
if (v_isSharedCheck_1235_ == 0)
{
v___x_1220_ = v_v_1208_;
v_isShared_1221_ = v_isSharedCheck_1235_;
goto v_resetjp_1219_;
}
else
{
lean_inc(v_val_1218_);
lean_inc(v_key_1217_);
lean_dec(v_v_1208_);
v___x_1220_ = lean_box(0);
v_isShared_1221_ = v_isSharedCheck_1235_;
goto v_resetjp_1219_;
}
v_resetjp_1219_:
{
uint8_t v___y_1223_; lean_object* v_fst_1229_; lean_object* v_snd_1230_; lean_object* v_fst_1231_; lean_object* v_snd_1232_; uint8_t v___x_1233_; 
v_fst_1229_ = lean_ctor_get(v_x_1195_, 0);
v_snd_1230_ = lean_ctor_get(v_x_1195_, 1);
v_fst_1231_ = lean_ctor_get(v_key_1217_, 0);
v_snd_1232_ = lean_ctor_get(v_key_1217_, 1);
v___x_1233_ = lean_nat_dec_eq(v_fst_1229_, v_fst_1231_);
if (v___x_1233_ == 0)
{
v___y_1223_ = v___x_1233_;
goto v___jp_1222_;
}
else
{
uint8_t v___x_1234_; 
v___x_1234_ = lean_nat_dec_eq(v_snd_1230_, v_snd_1232_);
v___y_1223_ = v___x_1234_;
goto v___jp_1222_;
}
v___jp_1222_:
{
if (v___y_1223_ == 0)
{
lean_object* v___x_1224_; lean_object* v___x_1225_; 
lean_del_object(v___x_1220_);
v___x_1224_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1217_, v_val_1218_, v_x_1195_, v_x_1196_);
v___x_1225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1225_, 0, v___x_1224_);
v___y_1212_ = v___x_1225_;
goto v___jp_1211_;
}
else
{
lean_object* v___x_1227_; 
lean_dec(v_val_1218_);
lean_dec(v_key_1217_);
if (v_isShared_1221_ == 0)
{
lean_ctor_set(v___x_1220_, 1, v_x_1196_);
lean_ctor_set(v___x_1220_, 0, v_x_1195_);
v___x_1227_ = v___x_1220_;
goto v_reusejp_1226_;
}
else
{
lean_object* v_reuseFailAlloc_1228_; 
v_reuseFailAlloc_1228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1228_, 0, v_x_1195_);
lean_ctor_set(v_reuseFailAlloc_1228_, 1, v_x_1196_);
v___x_1227_ = v_reuseFailAlloc_1228_;
goto v_reusejp_1226_;
}
v_reusejp_1226_:
{
v___y_1212_ = v___x_1227_;
goto v___jp_1211_;
}
}
}
}
}
case 1:
{
lean_object* v_node_1236_; lean_object* v___x_1238_; uint8_t v_isShared_1239_; uint8_t v_isSharedCheck_1246_; 
v_node_1236_ = lean_ctor_get(v_v_1208_, 0);
v_isSharedCheck_1246_ = !lean_is_exclusive(v_v_1208_);
if (v_isSharedCheck_1246_ == 0)
{
v___x_1238_ = v_v_1208_;
v_isShared_1239_ = v_isSharedCheck_1246_;
goto v_resetjp_1237_;
}
else
{
lean_inc(v_node_1236_);
lean_dec(v_v_1208_);
v___x_1238_ = lean_box(0);
v_isShared_1239_ = v_isSharedCheck_1246_;
goto v_resetjp_1237_;
}
v_resetjp_1237_:
{
size_t v___x_1240_; size_t v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1244_; 
v___x_1240_ = lean_usize_shift_right(v_x_1193_, v___x_1198_);
v___x_1241_ = lean_usize_add(v_x_1194_, v___x_1199_);
v___x_1242_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3___redArg(v_node_1236_, v___x_1240_, v___x_1241_, v_x_1195_, v_x_1196_);
if (v_isShared_1239_ == 0)
{
lean_ctor_set(v___x_1238_, 0, v___x_1242_);
v___x_1244_ = v___x_1238_;
goto v_reusejp_1243_;
}
else
{
lean_object* v_reuseFailAlloc_1245_; 
v_reuseFailAlloc_1245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1245_, 0, v___x_1242_);
v___x_1244_ = v_reuseFailAlloc_1245_;
goto v_reusejp_1243_;
}
v_reusejp_1243_:
{
v___y_1212_ = v___x_1244_;
goto v___jp_1211_;
}
}
}
default: 
{
lean_object* v___x_1247_; 
v___x_1247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1247_, 0, v_x_1195_);
lean_ctor_set(v___x_1247_, 1, v_x_1196_);
v___y_1212_ = v___x_1247_;
goto v___jp_1211_;
}
}
v___jp_1211_:
{
lean_object* v___x_1213_; lean_object* v___x_1215_; 
v___x_1213_ = lean_array_fset(v_xs_x27_1210_, v_j_1202_, v___y_1212_);
lean_dec(v_j_1202_);
if (v_isShared_1207_ == 0)
{
lean_ctor_set(v___x_1206_, 0, v___x_1213_);
v___x_1215_ = v___x_1206_;
goto v_reusejp_1214_;
}
else
{
lean_object* v_reuseFailAlloc_1216_; 
v_reuseFailAlloc_1216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1216_, 0, v___x_1213_);
v___x_1215_ = v_reuseFailAlloc_1216_;
goto v_reusejp_1214_;
}
v_reusejp_1214_:
{
return v___x_1215_;
}
}
}
}
}
else
{
lean_object* v_ks_1250_; lean_object* v_vs_1251_; lean_object* v___x_1253_; uint8_t v_isShared_1254_; uint8_t v_isSharedCheck_1271_; 
v_ks_1250_ = lean_ctor_get(v_x_1192_, 0);
v_vs_1251_ = lean_ctor_get(v_x_1192_, 1);
v_isSharedCheck_1271_ = !lean_is_exclusive(v_x_1192_);
if (v_isSharedCheck_1271_ == 0)
{
v___x_1253_ = v_x_1192_;
v_isShared_1254_ = v_isSharedCheck_1271_;
goto v_resetjp_1252_;
}
else
{
lean_inc(v_vs_1251_);
lean_inc(v_ks_1250_);
lean_dec(v_x_1192_);
v___x_1253_ = lean_box(0);
v_isShared_1254_ = v_isSharedCheck_1271_;
goto v_resetjp_1252_;
}
v_resetjp_1252_:
{
lean_object* v___x_1256_; 
if (v_isShared_1254_ == 0)
{
v___x_1256_ = v___x_1253_;
goto v_reusejp_1255_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v_ks_1250_);
lean_ctor_set(v_reuseFailAlloc_1270_, 1, v_vs_1251_);
v___x_1256_ = v_reuseFailAlloc_1270_;
goto v_reusejp_1255_;
}
v_reusejp_1255_:
{
lean_object* v_newNode_1257_; uint8_t v___y_1259_; size_t v___x_1265_; uint8_t v___x_1266_; 
v_newNode_1257_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3_spec__5___redArg(v___x_1256_, v_x_1195_, v_x_1196_);
v___x_1265_ = ((size_t)7ULL);
v___x_1266_ = lean_usize_dec_le(v___x_1265_, v_x_1194_);
if (v___x_1266_ == 0)
{
lean_object* v___x_1267_; lean_object* v___x_1268_; uint8_t v___x_1269_; 
v___x_1267_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1257_);
v___x_1268_ = lean_unsigned_to_nat(4u);
v___x_1269_ = lean_nat_dec_lt(v___x_1267_, v___x_1268_);
lean_dec(v___x_1267_);
v___y_1259_ = v___x_1269_;
goto v___jp_1258_;
}
else
{
v___y_1259_ = v___x_1266_;
goto v___jp_1258_;
}
v___jp_1258_:
{
if (v___y_1259_ == 0)
{
lean_object* v_ks_1260_; lean_object* v_vs_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; 
v_ks_1260_ = lean_ctor_get(v_newNode_1257_, 0);
lean_inc_ref(v_ks_1260_);
v_vs_1261_ = lean_ctor_get(v_newNode_1257_, 1);
lean_inc_ref(v_vs_1261_);
lean_dec_ref(v_newNode_1257_);
v___x_1262_ = lean_unsigned_to_nat(0u);
v___x_1263_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3___redArg___closed__0);
v___x_1264_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3_spec__6___redArg(v_x_1194_, v_ks_1260_, v_vs_1261_, v___x_1262_, v___x_1263_);
lean_dec_ref(v_vs_1261_);
lean_dec_ref(v_ks_1260_);
return v___x_1264_;
}
else
{
return v_newNode_1257_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3_spec__6___redArg(size_t v_depth_1272_, lean_object* v_keys_1273_, lean_object* v_vals_1274_, lean_object* v_i_1275_, lean_object* v_entries_1276_){
_start:
{
lean_object* v___x_1277_; uint8_t v___x_1278_; 
v___x_1277_ = lean_array_get_size(v_keys_1273_);
v___x_1278_ = lean_nat_dec_lt(v_i_1275_, v___x_1277_);
if (v___x_1278_ == 0)
{
lean_dec(v_i_1275_);
return v_entries_1276_;
}
else
{
lean_object* v_k_1279_; lean_object* v_fst_1280_; lean_object* v_snd_1281_; lean_object* v_v_1282_; uint64_t v___x_1283_; uint64_t v___x_1284_; uint64_t v___x_1285_; size_t v_h_1286_; size_t v___x_1287_; lean_object* v___x_1288_; size_t v___x_1289_; size_t v___x_1290_; size_t v___x_1291_; size_t v_h_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; 
v_k_1279_ = lean_array_fget_borrowed(v_keys_1273_, v_i_1275_);
v_fst_1280_ = lean_ctor_get(v_k_1279_, 0);
v_snd_1281_ = lean_ctor_get(v_k_1279_, 1);
v_v_1282_ = lean_array_fget_borrowed(v_vals_1274_, v_i_1275_);
v___x_1283_ = lean_uint64_of_nat(v_fst_1280_);
v___x_1284_ = lean_uint64_of_nat(v_snd_1281_);
v___x_1285_ = lean_uint64_mix_hash(v___x_1283_, v___x_1284_);
v_h_1286_ = lean_uint64_to_usize(v___x_1285_);
v___x_1287_ = ((size_t)5ULL);
v___x_1288_ = lean_unsigned_to_nat(1u);
v___x_1289_ = ((size_t)1ULL);
v___x_1290_ = lean_usize_sub(v_depth_1272_, v___x_1289_);
v___x_1291_ = lean_usize_mul(v___x_1287_, v___x_1290_);
v_h_1292_ = lean_usize_shift_right(v_h_1286_, v___x_1291_);
v___x_1293_ = lean_nat_add(v_i_1275_, v___x_1288_);
lean_dec(v_i_1275_);
lean_inc(v_v_1282_);
lean_inc(v_k_1279_);
v___x_1294_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3___redArg(v_entries_1276_, v_h_1292_, v_depth_1272_, v_k_1279_, v_v_1282_);
v_i_1275_ = v___x_1293_;
v_entries_1276_ = v___x_1294_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_depth_1296_, lean_object* v_keys_1297_, lean_object* v_vals_1298_, lean_object* v_i_1299_, lean_object* v_entries_1300_){
_start:
{
size_t v_depth_boxed_1301_; lean_object* v_res_1302_; 
v_depth_boxed_1301_ = lean_unbox_usize(v_depth_1296_);
lean_dec(v_depth_1296_);
v_res_1302_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3_spec__6___redArg(v_depth_boxed_1301_, v_keys_1297_, v_vals_1298_, v_i_1299_, v_entries_1300_);
lean_dec_ref(v_vals_1298_);
lean_dec_ref(v_keys_1297_);
return v_res_1302_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3___redArg___boxed(lean_object* v_x_1303_, lean_object* v_x_1304_, lean_object* v_x_1305_, lean_object* v_x_1306_, lean_object* v_x_1307_){
_start:
{
size_t v_x_3751__boxed_1308_; size_t v_x_3752__boxed_1309_; lean_object* v_res_1310_; 
v_x_3751__boxed_1308_ = lean_unbox_usize(v_x_1304_);
lean_dec(v_x_1304_);
v_x_3752__boxed_1309_ = lean_unbox_usize(v_x_1305_);
lean_dec(v_x_1305_);
v_res_1310_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3___redArg(v_x_1303_, v_x_3751__boxed_1308_, v_x_3752__boxed_1309_, v_x_1306_, v_x_1307_);
return v_res_1310_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2___redArg(lean_object* v_x_1311_, lean_object* v_x_1312_, lean_object* v_x_1313_){
_start:
{
lean_object* v_fst_1314_; lean_object* v_snd_1315_; uint64_t v___x_1316_; uint64_t v___x_1317_; uint64_t v___x_1318_; size_t v___x_1319_; size_t v___x_1320_; lean_object* v___x_1321_; 
v_fst_1314_ = lean_ctor_get(v_x_1312_, 0);
v_snd_1315_ = lean_ctor_get(v_x_1312_, 1);
v___x_1316_ = lean_uint64_of_nat(v_fst_1314_);
v___x_1317_ = lean_uint64_of_nat(v_snd_1315_);
v___x_1318_ = lean_uint64_mix_hash(v___x_1316_, v___x_1317_);
v___x_1319_ = lean_uint64_to_usize(v___x_1318_);
v___x_1320_ = ((size_t)1ULL);
v___x_1321_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3___redArg(v_x_1311_, v___x_1319_, v___x_1320_, v_x_1312_, v_x_1313_);
return v___x_1321_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0_spec__0_spec__2___redArg(lean_object* v_keys_1322_, lean_object* v_vals_1323_, lean_object* v_i_1324_, lean_object* v_k_1325_){
_start:
{
uint8_t v___y_1327_; lean_object* v___x_1333_; uint8_t v___x_1334_; 
v___x_1333_ = lean_array_get_size(v_keys_1322_);
v___x_1334_ = lean_nat_dec_lt(v_i_1324_, v___x_1333_);
if (v___x_1334_ == 0)
{
lean_object* v___x_1335_; 
lean_dec(v_i_1324_);
v___x_1335_ = lean_box(0);
return v___x_1335_;
}
else
{
lean_object* v_fst_1336_; lean_object* v_snd_1337_; lean_object* v_k_x27_1338_; lean_object* v_fst_1339_; lean_object* v_snd_1340_; uint8_t v___x_1341_; 
v_fst_1336_ = lean_ctor_get(v_k_1325_, 0);
v_snd_1337_ = lean_ctor_get(v_k_1325_, 1);
v_k_x27_1338_ = lean_array_fget_borrowed(v_keys_1322_, v_i_1324_);
v_fst_1339_ = lean_ctor_get(v_k_x27_1338_, 0);
v_snd_1340_ = lean_ctor_get(v_k_x27_1338_, 1);
v___x_1341_ = lean_nat_dec_eq(v_fst_1336_, v_fst_1339_);
if (v___x_1341_ == 0)
{
v___y_1327_ = v___x_1341_;
goto v___jp_1326_;
}
else
{
uint8_t v___x_1342_; 
v___x_1342_ = lean_nat_dec_eq(v_snd_1337_, v_snd_1340_);
v___y_1327_ = v___x_1342_;
goto v___jp_1326_;
}
}
v___jp_1326_:
{
if (v___y_1327_ == 0)
{
lean_object* v___x_1328_; lean_object* v___x_1329_; 
v___x_1328_ = lean_unsigned_to_nat(1u);
v___x_1329_ = lean_nat_add(v_i_1324_, v___x_1328_);
lean_dec(v_i_1324_);
v_i_1324_ = v___x_1329_;
goto _start;
}
else
{
lean_object* v___x_1331_; lean_object* v___x_1332_; 
v___x_1331_ = lean_array_fget_borrowed(v_vals_1323_, v_i_1324_);
lean_dec(v_i_1324_);
lean_inc(v___x_1331_);
v___x_1332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1332_, 0, v___x_1331_);
return v___x_1332_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_keys_1343_, lean_object* v_vals_1344_, lean_object* v_i_1345_, lean_object* v_k_1346_){
_start:
{
lean_object* v_res_1347_; 
v_res_1347_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0_spec__0_spec__2___redArg(v_keys_1343_, v_vals_1344_, v_i_1345_, v_k_1346_);
lean_dec_ref(v_k_1346_);
lean_dec_ref(v_vals_1344_);
lean_dec_ref(v_keys_1343_);
return v_res_1347_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0_spec__0___redArg(lean_object* v_x_1348_, size_t v_x_1349_, lean_object* v_x_1350_){
_start:
{
if (lean_obj_tag(v_x_1348_) == 0)
{
lean_object* v_es_1351_; lean_object* v___x_1353_; uint8_t v_isShared_1354_; uint8_t v_isSharedCheck_1379_; 
v_es_1351_ = lean_ctor_get(v_x_1348_, 0);
v_isSharedCheck_1379_ = !lean_is_exclusive(v_x_1348_);
if (v_isSharedCheck_1379_ == 0)
{
v___x_1353_ = v_x_1348_;
v_isShared_1354_ = v_isSharedCheck_1379_;
goto v_resetjp_1352_;
}
else
{
lean_inc(v_es_1351_);
lean_dec(v_x_1348_);
v___x_1353_ = lean_box(0);
v_isShared_1354_ = v_isSharedCheck_1379_;
goto v_resetjp_1352_;
}
v_resetjp_1352_:
{
lean_object* v___x_1355_; size_t v___x_1356_; size_t v___x_1357_; size_t v___x_1358_; lean_object* v_j_1359_; lean_object* v___x_1360_; 
v___x_1355_ = lean_box(2);
v___x_1356_ = ((size_t)5ULL);
v___x_1357_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0_spec__0___redArg___closed__1);
v___x_1358_ = lean_usize_land(v_x_1349_, v___x_1357_);
v_j_1359_ = lean_usize_to_nat(v___x_1358_);
v___x_1360_ = lean_array_get(v___x_1355_, v_es_1351_, v_j_1359_);
lean_dec(v_j_1359_);
lean_dec_ref(v_es_1351_);
switch(lean_obj_tag(v___x_1360_))
{
case 0:
{
lean_object* v_key_1361_; lean_object* v_val_1362_; uint8_t v___y_1364_; lean_object* v_fst_1369_; lean_object* v_snd_1370_; lean_object* v_fst_1371_; lean_object* v_snd_1372_; uint8_t v___x_1373_; 
v_key_1361_ = lean_ctor_get(v___x_1360_, 0);
lean_inc(v_key_1361_);
v_val_1362_ = lean_ctor_get(v___x_1360_, 1);
lean_inc(v_val_1362_);
lean_dec_ref(v___x_1360_);
v_fst_1369_ = lean_ctor_get(v_x_1350_, 0);
v_snd_1370_ = lean_ctor_get(v_x_1350_, 1);
v_fst_1371_ = lean_ctor_get(v_key_1361_, 0);
lean_inc(v_fst_1371_);
v_snd_1372_ = lean_ctor_get(v_key_1361_, 1);
lean_inc(v_snd_1372_);
lean_dec(v_key_1361_);
v___x_1373_ = lean_nat_dec_eq(v_fst_1369_, v_fst_1371_);
lean_dec(v_fst_1371_);
if (v___x_1373_ == 0)
{
lean_dec(v_snd_1372_);
v___y_1364_ = v___x_1373_;
goto v___jp_1363_;
}
else
{
uint8_t v___x_1374_; 
v___x_1374_ = lean_nat_dec_eq(v_snd_1370_, v_snd_1372_);
lean_dec(v_snd_1372_);
v___y_1364_ = v___x_1374_;
goto v___jp_1363_;
}
v___jp_1363_:
{
if (v___y_1364_ == 0)
{
lean_object* v___x_1365_; 
lean_dec(v_val_1362_);
lean_del_object(v___x_1353_);
v___x_1365_ = lean_box(0);
return v___x_1365_;
}
else
{
lean_object* v___x_1367_; 
if (v_isShared_1354_ == 0)
{
lean_ctor_set_tag(v___x_1353_, 1);
lean_ctor_set(v___x_1353_, 0, v_val_1362_);
v___x_1367_ = v___x_1353_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v_val_1362_);
v___x_1367_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
return v___x_1367_;
}
}
}
}
case 1:
{
lean_object* v_node_1375_; size_t v___x_1376_; 
lean_del_object(v___x_1353_);
v_node_1375_ = lean_ctor_get(v___x_1360_, 0);
lean_inc(v_node_1375_);
lean_dec_ref(v___x_1360_);
v___x_1376_ = lean_usize_shift_right(v_x_1349_, v___x_1356_);
v_x_1348_ = v_node_1375_;
v_x_1349_ = v___x_1376_;
goto _start;
}
default: 
{
lean_object* v___x_1378_; 
lean_del_object(v___x_1353_);
v___x_1378_ = lean_box(0);
return v___x_1378_;
}
}
}
}
else
{
lean_object* v_ks_1380_; lean_object* v_vs_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; 
v_ks_1380_ = lean_ctor_get(v_x_1348_, 0);
lean_inc_ref(v_ks_1380_);
v_vs_1381_ = lean_ctor_get(v_x_1348_, 1);
lean_inc_ref(v_vs_1381_);
lean_dec_ref(v_x_1348_);
v___x_1382_ = lean_unsigned_to_nat(0u);
v___x_1383_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0_spec__0_spec__2___redArg(v_ks_1380_, v_vs_1381_, v___x_1382_, v_x_1350_);
lean_dec_ref(v_vs_1381_);
lean_dec_ref(v_ks_1380_);
return v___x_1383_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0_spec__0___redArg___boxed(lean_object* v_x_1384_, lean_object* v_x_1385_, lean_object* v_x_1386_){
_start:
{
size_t v_x_3985__boxed_1387_; lean_object* v_res_1388_; 
v_x_3985__boxed_1387_ = lean_unbox_usize(v_x_1385_);
lean_dec(v_x_1385_);
v_res_1388_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0_spec__0___redArg(v_x_1384_, v_x_3985__boxed_1387_, v_x_1386_);
lean_dec_ref(v_x_1386_);
return v_res_1388_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0___redArg(lean_object* v_x_1389_, lean_object* v_x_1390_){
_start:
{
lean_object* v_fst_1391_; lean_object* v_snd_1392_; uint64_t v___x_1393_; uint64_t v___x_1394_; uint64_t v___x_1395_; size_t v___x_1396_; lean_object* v___x_1397_; 
v_fst_1391_ = lean_ctor_get(v_x_1390_, 0);
v_snd_1392_ = lean_ctor_get(v_x_1390_, 1);
v___x_1393_ = lean_uint64_of_nat(v_fst_1391_);
v___x_1394_ = lean_uint64_of_nat(v_snd_1392_);
v___x_1395_ = lean_uint64_mix_hash(v___x_1393_, v___x_1394_);
v___x_1396_ = lean_uint64_to_usize(v___x_1395_);
v___x_1397_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0_spec__0___redArg(v_x_1389_, v___x_1396_, v_x_1390_);
return v___x_1397_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0___redArg___boxed(lean_object* v_x_1398_, lean_object* v_x_1399_){
_start:
{
lean_object* v_res_1400_; 
v_res_1400_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0___redArg(v_x_1398_, v_x_1399_);
lean_dec_ref(v_x_1399_);
return v_res_1400_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm(lean_object* v_term_1401_, lean_object* v_a_1402_, lean_object* v_a_1403_, lean_object* v_a_1404_, lean_object* v_a_1405_, lean_object* v_a_1406_, lean_object* v_a_1407_, lean_object* v_a_1408_, lean_object* v_a_1409_){
_start:
{
uint8_t v___x_1411_; lean_object* v___y_1413_; lean_object* v___y_1414_; lean_object* v___y_1478_; lean_object* v___x_1482_; 
v___x_1411_ = 0;
v___x_1482_ = l_Lean_Syntax_getPos_x3f(v_term_1401_, v___x_1411_);
if (lean_obj_tag(v___x_1482_) == 0)
{
lean_object* v___x_1483_; 
v___x_1483_ = lean_unsigned_to_nat(0u);
v___y_1478_ = v___x_1483_;
goto v___jp_1477_;
}
else
{
lean_object* v_val_1484_; 
v_val_1484_ = lean_ctor_get(v___x_1482_, 0);
lean_inc(v_val_1484_);
lean_dec_ref(v___x_1482_);
v___y_1478_ = v_val_1484_;
goto v___jp_1477_;
}
v___jp_1412_:
{
lean_object* v___x_1415_; lean_object* v_cache_1416_; lean_object* v_backwardRuleSyntax_1417_; lean_object* v_pos_1418_; lean_object* v___x_1419_; 
v___x_1415_ = lean_st_ref_get(v_a_1403_);
v_cache_1416_ = lean_ctor_get(v___x_1415_, 3);
lean_inc_ref(v_cache_1416_);
lean_dec(v___x_1415_);
v_backwardRuleSyntax_1417_ = lean_ctor_get(v_cache_1416_, 1);
lean_inc_ref(v_backwardRuleSyntax_1417_);
lean_dec_ref(v_cache_1416_);
v_pos_1418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_pos_1418_, 0, v___y_1413_);
lean_ctor_set(v_pos_1418_, 1, v___y_1414_);
v___x_1419_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0___redArg(v_backwardRuleSyntax_1417_, v_pos_1418_);
if (lean_obj_tag(v___x_1419_) == 1)
{
lean_object* v_val_1420_; lean_object* v___x_1422_; uint8_t v_isShared_1423_; uint8_t v_isSharedCheck_1427_; 
lean_dec_ref(v_pos_1418_);
lean_dec(v_term_1401_);
v_val_1420_ = lean_ctor_get(v___x_1419_, 0);
v_isSharedCheck_1427_ = !lean_is_exclusive(v___x_1419_);
if (v_isSharedCheck_1427_ == 0)
{
v___x_1422_ = v___x_1419_;
v_isShared_1423_ = v_isSharedCheck_1427_;
goto v_resetjp_1421_;
}
else
{
lean_inc(v_val_1420_);
lean_dec(v___x_1419_);
v___x_1422_ = lean_box(0);
v_isShared_1423_ = v_isSharedCheck_1427_;
goto v_resetjp_1421_;
}
v_resetjp_1421_:
{
lean_object* v___x_1425_; 
if (v_isShared_1423_ == 0)
{
lean_ctor_set_tag(v___x_1422_, 0);
v___x_1425_ = v___x_1422_;
goto v_reusejp_1424_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v_val_1420_);
v___x_1425_ = v_reuseFailAlloc_1426_;
goto v_reusejp_1424_;
}
v_reusejp_1424_:
{
return v___x_1425_;
}
}
}
else
{
lean_object* v___x_1428_; uint8_t v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___f_1432_; lean_object* v___x_1433_; 
lean_dec(v___x_1419_);
v___x_1428_ = lean_box(0);
v___x_1429_ = 1;
v___x_1430_ = lean_box(v___x_1429_);
v___x_1431_ = lean_box(v___x_1411_);
v___f_1432_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm___lam__0___boxed), 13, 4);
lean_closure_set(v___f_1432_, 0, v_term_1401_);
lean_closure_set(v___f_1432_, 1, v___x_1428_);
lean_closure_set(v___f_1432_, 2, v___x_1430_);
lean_closure_set(v___f_1432_, 3, v___x_1431_);
v___x_1433_ = l_Lean_Elab_Tactic_Grind_withMainContext___redArg(v___f_1432_, v_a_1402_, v_a_1403_, v_a_1404_, v_a_1405_, v_a_1406_, v_a_1407_, v_a_1408_, v_a_1409_);
if (lean_obj_tag(v___x_1433_) == 0)
{
lean_object* v_a_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; 
v_a_1434_ = lean_ctor_get(v___x_1433_, 0);
lean_inc(v_a_1434_);
lean_dec_ref(v___x_1433_);
v___x_1435_ = lean_box(0);
v___x_1436_ = l_Lean_Meta_Sym_mkBackwardRuleFromExpr(v_a_1434_, v___x_1435_, v___x_1428_, v_a_1406_, v_a_1407_, v_a_1408_, v_a_1409_);
if (lean_obj_tag(v___x_1436_) == 0)
{
lean_object* v_a_1437_; lean_object* v___x_1439_; uint8_t v_isShared_1440_; uint8_t v_isSharedCheck_1468_; 
v_a_1437_ = lean_ctor_get(v___x_1436_, 0);
v_isSharedCheck_1468_ = !lean_is_exclusive(v___x_1436_);
if (v_isSharedCheck_1468_ == 0)
{
v___x_1439_ = v___x_1436_;
v_isShared_1440_ = v_isSharedCheck_1468_;
goto v_resetjp_1438_;
}
else
{
lean_inc(v_a_1437_);
lean_dec(v___x_1436_);
v___x_1439_ = lean_box(0);
v_isShared_1440_ = v_isSharedCheck_1468_;
goto v_resetjp_1438_;
}
v_resetjp_1438_:
{
lean_object* v___x_1441_; lean_object* v_cache_1442_; lean_object* v_symState_1443_; lean_object* v_grindState_1444_; lean_object* v_goals_1445_; lean_object* v___x_1447_; uint8_t v_isShared_1448_; uint8_t v_isSharedCheck_1467_; 
v___x_1441_ = lean_st_ref_take(v_a_1403_);
v_cache_1442_ = lean_ctor_get(v___x_1441_, 3);
v_symState_1443_ = lean_ctor_get(v___x_1441_, 0);
v_grindState_1444_ = lean_ctor_get(v___x_1441_, 1);
v_goals_1445_ = lean_ctor_get(v___x_1441_, 2);
v_isSharedCheck_1467_ = !lean_is_exclusive(v___x_1441_);
if (v_isSharedCheck_1467_ == 0)
{
v___x_1447_ = v___x_1441_;
v_isShared_1448_ = v_isSharedCheck_1467_;
goto v_resetjp_1446_;
}
else
{
lean_inc(v_cache_1442_);
lean_inc(v_goals_1445_);
lean_inc(v_grindState_1444_);
lean_inc(v_symState_1443_);
lean_dec(v___x_1441_);
v___x_1447_ = lean_box(0);
v_isShared_1448_ = v_isSharedCheck_1467_;
goto v_resetjp_1446_;
}
v_resetjp_1446_:
{
lean_object* v_backwardRuleName_1449_; lean_object* v_backwardRuleSyntax_1450_; lean_object* v_simpState_1451_; lean_object* v___x_1453_; uint8_t v_isShared_1454_; uint8_t v_isSharedCheck_1466_; 
v_backwardRuleName_1449_ = lean_ctor_get(v_cache_1442_, 0);
v_backwardRuleSyntax_1450_ = lean_ctor_get(v_cache_1442_, 1);
v_simpState_1451_ = lean_ctor_get(v_cache_1442_, 2);
v_isSharedCheck_1466_ = !lean_is_exclusive(v_cache_1442_);
if (v_isSharedCheck_1466_ == 0)
{
v___x_1453_ = v_cache_1442_;
v_isShared_1454_ = v_isSharedCheck_1466_;
goto v_resetjp_1452_;
}
else
{
lean_inc(v_simpState_1451_);
lean_inc(v_backwardRuleSyntax_1450_);
lean_inc(v_backwardRuleName_1449_);
lean_dec(v_cache_1442_);
v___x_1453_ = lean_box(0);
v_isShared_1454_ = v_isSharedCheck_1466_;
goto v_resetjp_1452_;
}
v_resetjp_1452_:
{
lean_object* v___x_1455_; lean_object* v___x_1457_; 
lean_inc(v_a_1437_);
v___x_1455_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2___redArg(v_backwardRuleSyntax_1450_, v_pos_1418_, v_a_1437_);
if (v_isShared_1454_ == 0)
{
lean_ctor_set(v___x_1453_, 1, v___x_1455_);
v___x_1457_ = v___x_1453_;
goto v_reusejp_1456_;
}
else
{
lean_object* v_reuseFailAlloc_1465_; 
v_reuseFailAlloc_1465_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1465_, 0, v_backwardRuleName_1449_);
lean_ctor_set(v_reuseFailAlloc_1465_, 1, v___x_1455_);
lean_ctor_set(v_reuseFailAlloc_1465_, 2, v_simpState_1451_);
v___x_1457_ = v_reuseFailAlloc_1465_;
goto v_reusejp_1456_;
}
v_reusejp_1456_:
{
lean_object* v___x_1459_; 
if (v_isShared_1448_ == 0)
{
lean_ctor_set(v___x_1447_, 3, v___x_1457_);
v___x_1459_ = v___x_1447_;
goto v_reusejp_1458_;
}
else
{
lean_object* v_reuseFailAlloc_1464_; 
v_reuseFailAlloc_1464_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1464_, 0, v_symState_1443_);
lean_ctor_set(v_reuseFailAlloc_1464_, 1, v_grindState_1444_);
lean_ctor_set(v_reuseFailAlloc_1464_, 2, v_goals_1445_);
lean_ctor_set(v_reuseFailAlloc_1464_, 3, v___x_1457_);
v___x_1459_ = v_reuseFailAlloc_1464_;
goto v_reusejp_1458_;
}
v_reusejp_1458_:
{
lean_object* v___x_1460_; lean_object* v___x_1462_; 
v___x_1460_ = lean_st_ref_set(v_a_1403_, v___x_1459_);
if (v_isShared_1440_ == 0)
{
v___x_1462_ = v___x_1439_;
goto v_reusejp_1461_;
}
else
{
lean_object* v_reuseFailAlloc_1463_; 
v_reuseFailAlloc_1463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1463_, 0, v_a_1437_);
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
}
}
else
{
lean_dec_ref(v_pos_1418_);
return v___x_1436_;
}
}
else
{
lean_object* v_a_1469_; lean_object* v___x_1471_; uint8_t v_isShared_1472_; uint8_t v_isSharedCheck_1476_; 
lean_dec_ref(v_pos_1418_);
v_a_1469_ = lean_ctor_get(v___x_1433_, 0);
v_isSharedCheck_1476_ = !lean_is_exclusive(v___x_1433_);
if (v_isSharedCheck_1476_ == 0)
{
v___x_1471_ = v___x_1433_;
v_isShared_1472_ = v_isSharedCheck_1476_;
goto v_resetjp_1470_;
}
else
{
lean_inc(v_a_1469_);
lean_dec(v___x_1433_);
v___x_1471_ = lean_box(0);
v_isShared_1472_ = v_isSharedCheck_1476_;
goto v_resetjp_1470_;
}
v_resetjp_1470_:
{
lean_object* v___x_1474_; 
if (v_isShared_1472_ == 0)
{
v___x_1474_ = v___x_1471_;
goto v_reusejp_1473_;
}
else
{
lean_object* v_reuseFailAlloc_1475_; 
v_reuseFailAlloc_1475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v_a_1469_);
v___x_1474_ = v_reuseFailAlloc_1475_;
goto v_reusejp_1473_;
}
v_reusejp_1473_:
{
return v___x_1474_;
}
}
}
}
}
v___jp_1477_:
{
lean_object* v___x_1479_; 
v___x_1479_ = l_Lean_Syntax_getTailPos_x3f(v_term_1401_, v___x_1411_);
if (lean_obj_tag(v___x_1479_) == 0)
{
lean_object* v___x_1480_; 
v___x_1480_ = lean_unsigned_to_nat(0u);
v___y_1413_ = v___y_1478_;
v___y_1414_ = v___x_1480_;
goto v___jp_1412_;
}
else
{
lean_object* v_val_1481_; 
v_val_1481_ = lean_ctor_get(v___x_1479_, 0);
lean_inc(v_val_1481_);
lean_dec_ref(v___x_1479_);
v___y_1413_ = v___y_1478_;
v___y_1414_ = v_val_1481_;
goto v___jp_1412_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm___boxed(lean_object* v_term_1485_, lean_object* v_a_1486_, lean_object* v_a_1487_, lean_object* v_a_1488_, lean_object* v_a_1489_, lean_object* v_a_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_){
_start:
{
lean_object* v_res_1495_; 
v_res_1495_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm(v_term_1485_, v_a_1486_, v_a_1487_, v_a_1488_, v_a_1489_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_);
lean_dec(v_a_1493_);
lean_dec_ref(v_a_1492_);
lean_dec(v_a_1491_);
lean_dec_ref(v_a_1490_);
lean_dec(v_a_1489_);
lean_dec_ref(v_a_1488_);
lean_dec(v_a_1487_);
lean_dec_ref(v_a_1486_);
return v_res_1495_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0(lean_object* v_00_u03b2_1496_, lean_object* v_x_1497_, lean_object* v_x_1498_){
_start:
{
lean_object* v___x_1499_; 
v___x_1499_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0___redArg(v_x_1497_, v_x_1498_);
return v___x_1499_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0___boxed(lean_object* v_00_u03b2_1500_, lean_object* v_x_1501_, lean_object* v_x_1502_){
_start:
{
lean_object* v_res_1503_; 
v_res_1503_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0(v_00_u03b2_1500_, v_x_1501_, v_x_1502_);
lean_dec_ref(v_x_1502_);
return v_res_1503_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2(lean_object* v_00_u03b2_1504_, lean_object* v_x_1505_, lean_object* v_x_1506_, lean_object* v_x_1507_){
_start:
{
lean_object* v___x_1508_; 
v___x_1508_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2___redArg(v_x_1505_, v_x_1506_, v_x_1507_);
return v___x_1508_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0_spec__0(lean_object* v_00_u03b2_1509_, lean_object* v_x_1510_, size_t v_x_1511_, lean_object* v_x_1512_){
_start:
{
lean_object* v___x_1513_; 
v___x_1513_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0_spec__0___redArg(v_x_1510_, v_x_1511_, v_x_1512_);
return v___x_1513_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1514_, lean_object* v_x_1515_, lean_object* v_x_1516_, lean_object* v_x_1517_){
_start:
{
size_t v_x_4228__boxed_1518_; lean_object* v_res_1519_; 
v_x_4228__boxed_1518_ = lean_unbox_usize(v_x_1516_);
lean_dec(v_x_1516_);
v_res_1519_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0_spec__0(v_00_u03b2_1514_, v_x_1515_, v_x_4228__boxed_1518_, v_x_1517_);
lean_dec_ref(v_x_1517_);
return v_res_1519_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3(lean_object* v_00_u03b2_1520_, lean_object* v_x_1521_, size_t v_x_1522_, size_t v_x_1523_, lean_object* v_x_1524_, lean_object* v_x_1525_){
_start:
{
lean_object* v___x_1526_; 
v___x_1526_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3___redArg(v_x_1521_, v_x_1522_, v_x_1523_, v_x_1524_, v_x_1525_);
return v___x_1526_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3___boxed(lean_object* v_00_u03b2_1527_, lean_object* v_x_1528_, lean_object* v_x_1529_, lean_object* v_x_1530_, lean_object* v_x_1531_, lean_object* v_x_1532_){
_start:
{
size_t v_x_4239__boxed_1533_; size_t v_x_4240__boxed_1534_; lean_object* v_res_1535_; 
v_x_4239__boxed_1533_ = lean_unbox_usize(v_x_1529_);
lean_dec(v_x_1529_);
v_x_4240__boxed_1534_ = lean_unbox_usize(v_x_1530_);
lean_dec(v_x_1530_);
v_res_1535_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3(v_00_u03b2_1527_, v_x_1528_, v_x_4239__boxed_1533_, v_x_4240__boxed_1534_, v_x_1531_, v_x_1532_);
return v_res_1535_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1536_, lean_object* v_keys_1537_, lean_object* v_vals_1538_, lean_object* v_heq_1539_, lean_object* v_i_1540_, lean_object* v_k_1541_){
_start:
{
lean_object* v___x_1542_; 
v___x_1542_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0_spec__0_spec__2___redArg(v_keys_1537_, v_vals_1538_, v_i_1540_, v_k_1541_);
return v___x_1542_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1543_, lean_object* v_keys_1544_, lean_object* v_vals_1545_, lean_object* v_heq_1546_, lean_object* v_i_1547_, lean_object* v_k_1548_){
_start:
{
lean_object* v_res_1549_; 
v_res_1549_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0_spec__0_spec__2(v_00_u03b2_1543_, v_keys_1544_, v_vals_1545_, v_heq_1546_, v_i_1547_, v_k_1548_);
lean_dec_ref(v_k_1548_);
lean_dec_ref(v_vals_1545_);
lean_dec_ref(v_keys_1544_);
return v_res_1549_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_1550_, lean_object* v_n_1551_, lean_object* v_k_1552_, lean_object* v_v_1553_){
_start:
{
lean_object* v___x_1554_; 
v___x_1554_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3_spec__5___redArg(v_n_1551_, v_k_1552_, v_v_1553_);
return v___x_1554_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3_spec__6(lean_object* v_00_u03b2_1555_, size_t v_depth_1556_, lean_object* v_keys_1557_, lean_object* v_vals_1558_, lean_object* v_heq_1559_, lean_object* v_i_1560_, lean_object* v_entries_1561_){
_start:
{
lean_object* v___x_1562_; 
v___x_1562_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3_spec__6___redArg(v_depth_1556_, v_keys_1557_, v_vals_1558_, v_i_1560_, v_entries_1561_);
return v___x_1562_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3_spec__6___boxed(lean_object* v_00_u03b2_1563_, lean_object* v_depth_1564_, lean_object* v_keys_1565_, lean_object* v_vals_1566_, lean_object* v_heq_1567_, lean_object* v_i_1568_, lean_object* v_entries_1569_){
_start:
{
size_t v_depth_boxed_1570_; lean_object* v_res_1571_; 
v_depth_boxed_1570_ = lean_unbox_usize(v_depth_1564_);
lean_dec(v_depth_1564_);
v_res_1571_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3_spec__6(v_00_u03b2_1563_, v_depth_boxed_1570_, v_keys_1565_, v_vals_1566_, v_heq_1567_, v_i_1568_, v_entries_1569_);
lean_dec_ref(v_vals_1566_);
lean_dec_ref(v_keys_1565_);
return v_res_1571_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3_spec__5_spec__6(lean_object* v_00_u03b2_1572_, lean_object* v_x_1573_, lean_object* v_x_1574_, lean_object* v_x_1575_, lean_object* v_x_1576_){
_start:
{
lean_object* v___x_1577_; 
v___x_1577_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3_spec__5_spec__6___redArg(v_x_1573_, v_x_1574_, v_x_1575_, v_x_1576_);
return v___x_1577_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply_spec__0___redArg___lam__0(lean_object* v_x_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_){
_start:
{
lean_object* v___x_1588_; 
lean_inc(v___y_1582_);
lean_inc_ref(v___y_1581_);
lean_inc(v___y_1580_);
lean_inc_ref(v___y_1579_);
v___x_1588_ = lean_apply_9(v_x_1578_, v___y_1579_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_, v___y_1585_, v___y_1586_, lean_box(0));
return v___x_1588_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply_spec__0___redArg___lam__0___boxed(lean_object* v_x_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_){
_start:
{
lean_object* v_res_1599_; 
v_res_1599_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply_spec__0___redArg___lam__0(v_x_1589_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_, v___y_1596_, v___y_1597_);
lean_dec(v___y_1593_);
lean_dec_ref(v___y_1592_);
lean_dec(v___y_1591_);
lean_dec_ref(v___y_1590_);
return v_res_1599_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply_spec__0___redArg(lean_object* v_mvarId_1600_, lean_object* v_x_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_){
_start:
{
lean_object* v___f_1611_; lean_object* v___x_1612_; 
lean_inc(v___y_1605_);
lean_inc_ref(v___y_1604_);
lean_inc(v___y_1603_);
lean_inc_ref(v___y_1602_);
v___f_1611_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply_spec__0___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_1611_, 0, v_x_1601_);
lean_closure_set(v___f_1611_, 1, v___y_1602_);
lean_closure_set(v___f_1611_, 2, v___y_1603_);
lean_closure_set(v___f_1611_, 3, v___y_1604_);
lean_closure_set(v___f_1611_, 4, v___y_1605_);
v___x_1612_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1600_, v___f_1611_, v___y_1606_, v___y_1607_, v___y_1608_, v___y_1609_);
if (lean_obj_tag(v___x_1612_) == 0)
{
return v___x_1612_;
}
else
{
lean_object* v_a_1613_; lean_object* v___x_1615_; uint8_t v_isShared_1616_; uint8_t v_isSharedCheck_1620_; 
v_a_1613_ = lean_ctor_get(v___x_1612_, 0);
v_isSharedCheck_1620_ = !lean_is_exclusive(v___x_1612_);
if (v_isSharedCheck_1620_ == 0)
{
v___x_1615_ = v___x_1612_;
v_isShared_1616_ = v_isSharedCheck_1620_;
goto v_resetjp_1614_;
}
else
{
lean_inc(v_a_1613_);
lean_dec(v___x_1612_);
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
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply_spec__0___redArg___boxed(lean_object* v_mvarId_1621_, lean_object* v_x_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_){
_start:
{
lean_object* v_res_1632_; 
v_res_1632_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply_spec__0___redArg(v_mvarId_1621_, v_x_1622_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_);
lean_dec(v___y_1630_);
lean_dec_ref(v___y_1629_);
lean_dec(v___y_1628_);
lean_dec_ref(v___y_1627_);
lean_dec(v___y_1626_);
lean_dec_ref(v___y_1625_);
lean_dec(v___y_1624_);
lean_dec_ref(v___y_1623_);
return v_res_1632_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply_spec__0(lean_object* v_00_u03b1_1633_, lean_object* v_mvarId_1634_, lean_object* v_x_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_){
_start:
{
lean_object* v___x_1645_; 
v___x_1645_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply_spec__0___redArg(v_mvarId_1634_, v_x_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_);
return v___x_1645_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply_spec__0___boxed(lean_object* v_00_u03b1_1646_, lean_object* v_mvarId_1647_, lean_object* v_x_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_){
_start:
{
lean_object* v_res_1658_; 
v_res_1658_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply_spec__0(v_00_u03b1_1646_, v_mvarId_1647_, v_x_1648_, v___y_1649_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_);
lean_dec(v___y_1656_);
lean_dec_ref(v___y_1655_);
lean_dec(v___y_1654_);
lean_dec_ref(v___y_1653_);
lean_dec(v___y_1652_);
lean_dec_ref(v___y_1651_);
lean_dec(v___y_1650_);
lean_dec_ref(v___y_1649_);
return v_res_1658_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1660_; lean_object* v___x_1661_; 
v___x_1660_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___lam__0___closed__0));
v___x_1661_ = l_Lean_stringToMessageData(v___x_1660_);
return v___x_1661_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___lam__0(lean_object* v_a_1662_, lean_object* v_rule_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_){
_start:
{
lean_object* v___x_1673_; lean_object* v___x_1674_; 
v___x_1673_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Goal_apply___boxed), 9, 2);
lean_closure_set(v___x_1673_, 0, v_a_1662_);
lean_closure_set(v___x_1673_, 1, v_rule_1663_);
v___x_1674_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_liftSymM___redArg(v___x_1673_, v___y_1664_, v___y_1665_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_);
if (lean_obj_tag(v___x_1674_) == 0)
{
lean_object* v_a_1675_; 
v_a_1675_ = lean_ctor_get(v___x_1674_, 0);
lean_inc(v_a_1675_);
lean_dec_ref(v___x_1674_);
if (lean_obj_tag(v_a_1675_) == 0)
{
lean_object* v___x_1676_; lean_object* v___x_1677_; 
v___x_1676_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___lam__0___closed__1, &l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___lam__0___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___lam__0___closed__1);
v___x_1677_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_ensureSym_spec__0___redArg(v___x_1676_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_);
return v___x_1677_;
}
else
{
lean_object* v_subgoals_1678_; lean_object* v___x_1679_; 
v_subgoals_1678_ = lean_ctor_get(v_a_1675_, 0);
lean_inc(v_subgoals_1678_);
lean_dec_ref(v_a_1675_);
v___x_1679_ = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(v_subgoals_1678_, v___y_1665_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_);
return v___x_1679_;
}
}
else
{
lean_object* v_a_1680_; lean_object* v___x_1682_; uint8_t v_isShared_1683_; uint8_t v_isSharedCheck_1687_; 
v_a_1680_ = lean_ctor_get(v___x_1674_, 0);
v_isSharedCheck_1687_ = !lean_is_exclusive(v___x_1674_);
if (v_isSharedCheck_1687_ == 0)
{
v___x_1682_ = v___x_1674_;
v_isShared_1683_ = v_isSharedCheck_1687_;
goto v_resetjp_1681_;
}
else
{
lean_inc(v_a_1680_);
lean_dec(v___x_1674_);
v___x_1682_ = lean_box(0);
v_isShared_1683_ = v_isSharedCheck_1687_;
goto v_resetjp_1681_;
}
v_resetjp_1681_:
{
lean_object* v___x_1685_; 
if (v_isShared_1683_ == 0)
{
v___x_1685_ = v___x_1682_;
goto v_reusejp_1684_;
}
else
{
lean_object* v_reuseFailAlloc_1686_; 
v_reuseFailAlloc_1686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1686_, 0, v_a_1680_);
v___x_1685_ = v_reuseFailAlloc_1686_;
goto v_reusejp_1684_;
}
v_reusejp_1684_:
{
return v___x_1685_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___lam__0___boxed(lean_object* v_a_1688_, lean_object* v_rule_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_){
_start:
{
lean_object* v_res_1699_; 
v_res_1699_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___lam__0(v_a_1688_, v_rule_1689_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_);
lean_dec(v___y_1697_);
lean_dec_ref(v___y_1696_);
lean_dec(v___y_1695_);
lean_dec_ref(v___y_1694_);
lean_dec(v___y_1693_);
lean_dec_ref(v___y_1692_);
lean_dec(v___y_1691_);
lean_dec_ref(v___y_1690_);
return v_res_1699_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___lam__1(uint8_t v___x_1700_, lean_object* v___x_1701_, lean_object* v___f_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_){
_start:
{
if (v___x_1700_ == 0)
{
lean_object* v___x_1712_; 
v___x_1712_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm(v___x_1701_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_);
if (lean_obj_tag(v___x_1712_) == 0)
{
lean_object* v_a_1713_; lean_object* v___x_1714_; 
v_a_1713_ = lean_ctor_get(v___x_1712_, 0);
lean_inc(v_a_1713_);
lean_dec_ref(v___x_1712_);
lean_inc(v___y_1710_);
lean_inc_ref(v___y_1709_);
lean_inc(v___y_1708_);
lean_inc_ref(v___y_1707_);
lean_inc(v___y_1706_);
lean_inc_ref(v___y_1705_);
lean_inc(v___y_1704_);
lean_inc_ref(v___y_1703_);
v___x_1714_ = lean_apply_10(v___f_1702_, v_a_1713_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_, lean_box(0));
return v___x_1714_;
}
else
{
lean_object* v_a_1715_; lean_object* v___x_1717_; uint8_t v_isShared_1718_; uint8_t v_isSharedCheck_1722_; 
lean_dec_ref(v___f_1702_);
v_a_1715_ = lean_ctor_get(v___x_1712_, 0);
v_isSharedCheck_1722_ = !lean_is_exclusive(v___x_1712_);
if (v_isSharedCheck_1722_ == 0)
{
v___x_1717_ = v___x_1712_;
v_isShared_1718_ = v_isSharedCheck_1722_;
goto v_resetjp_1716_;
}
else
{
lean_inc(v_a_1715_);
lean_dec(v___x_1712_);
v___x_1717_ = lean_box(0);
v_isShared_1718_ = v_isSharedCheck_1722_;
goto v_resetjp_1716_;
}
v_resetjp_1716_:
{
lean_object* v___x_1720_; 
if (v_isShared_1718_ == 0)
{
v___x_1720_ = v___x_1717_;
goto v_reusejp_1719_;
}
else
{
lean_object* v_reuseFailAlloc_1721_; 
v_reuseFailAlloc_1721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1721_, 0, v_a_1715_);
v___x_1720_ = v_reuseFailAlloc_1721_;
goto v_reusejp_1719_;
}
v_reusejp_1719_:
{
return v___x_1720_;
}
}
}
}
else
{
lean_object* v___x_1723_; 
v___x_1723_ = l_Lean_Elab_Tactic_Grind_saveState___redArg(v___y_1704_, v___y_1706_, v___y_1708_, v___y_1710_);
if (lean_obj_tag(v___x_1723_) == 0)
{
lean_object* v_a_1724_; lean_object* v___x_1726_; uint8_t v_isShared_1727_; uint8_t v_isSharedCheck_1757_; 
v_a_1724_ = lean_ctor_get(v___x_1723_, 0);
v_isSharedCheck_1757_ = !lean_is_exclusive(v___x_1723_);
if (v_isSharedCheck_1757_ == 0)
{
v___x_1726_ = v___x_1723_;
v_isShared_1727_ = v_isSharedCheck_1757_;
goto v_resetjp_1725_;
}
else
{
lean_inc(v_a_1724_);
lean_dec(v___x_1723_);
v___x_1726_ = lean_box(0);
v_isShared_1727_ = v_isSharedCheck_1757_;
goto v_resetjp_1725_;
}
v_resetjp_1725_:
{
lean_object* v___y_1729_; uint8_t v___y_1730_; lean_object* v_a_1747_; lean_object* v___x_1750_; 
lean_inc(v___x_1701_);
v___x_1750_ = l_Lean_realizeGlobalConstNoOverload(v___x_1701_, v___y_1709_, v___y_1710_);
if (lean_obj_tag(v___x_1750_) == 0)
{
lean_object* v_a_1751_; lean_object* v___x_1752_; 
v_a_1751_ = lean_ctor_get(v___x_1750_, 0);
lean_inc(v_a_1751_);
lean_dec_ref(v___x_1750_);
v___x_1752_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule___redArg(v_a_1751_, v___y_1704_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_);
if (lean_obj_tag(v___x_1752_) == 0)
{
lean_object* v_a_1753_; lean_object* v___x_1754_; 
lean_del_object(v___x_1726_);
lean_dec(v_a_1724_);
lean_dec(v___x_1701_);
v_a_1753_ = lean_ctor_get(v___x_1752_, 0);
lean_inc(v_a_1753_);
lean_dec_ref(v___x_1752_);
lean_inc(v___y_1710_);
lean_inc_ref(v___y_1709_);
lean_inc(v___y_1708_);
lean_inc_ref(v___y_1707_);
lean_inc(v___y_1706_);
lean_inc_ref(v___y_1705_);
lean_inc(v___y_1704_);
lean_inc_ref(v___y_1703_);
v___x_1754_ = lean_apply_10(v___f_1702_, v_a_1753_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_, lean_box(0));
return v___x_1754_;
}
else
{
lean_object* v_a_1755_; 
v_a_1755_ = lean_ctor_get(v___x_1752_, 0);
lean_inc(v_a_1755_);
lean_dec_ref(v___x_1752_);
v_a_1747_ = v_a_1755_;
goto v___jp_1746_;
}
}
else
{
lean_object* v_a_1756_; 
v_a_1756_ = lean_ctor_get(v___x_1750_, 0);
lean_inc(v_a_1756_);
lean_dec_ref(v___x_1750_);
v_a_1747_ = v_a_1756_;
goto v___jp_1746_;
}
v___jp_1728_:
{
if (v___y_1730_ == 0)
{
lean_object* v___x_1731_; 
lean_dec_ref(v___y_1729_);
lean_del_object(v___x_1726_);
v___x_1731_ = l_Lean_Elab_Tactic_Grind_SavedState_restore___redArg(v_a_1724_, v___y_1730_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_);
if (lean_obj_tag(v___x_1731_) == 0)
{
lean_object* v___x_1732_; 
lean_dec_ref(v___x_1731_);
v___x_1732_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm(v___x_1701_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_);
if (lean_obj_tag(v___x_1732_) == 0)
{
lean_object* v_a_1733_; lean_object* v___x_1734_; 
v_a_1733_ = lean_ctor_get(v___x_1732_, 0);
lean_inc(v_a_1733_);
lean_dec_ref(v___x_1732_);
lean_inc(v___y_1710_);
lean_inc_ref(v___y_1709_);
lean_inc(v___y_1708_);
lean_inc_ref(v___y_1707_);
lean_inc(v___y_1706_);
lean_inc_ref(v___y_1705_);
lean_inc(v___y_1704_);
lean_inc_ref(v___y_1703_);
v___x_1734_ = lean_apply_10(v___f_1702_, v_a_1733_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_, lean_box(0));
return v___x_1734_;
}
else
{
lean_object* v_a_1735_; lean_object* v___x_1737_; uint8_t v_isShared_1738_; uint8_t v_isSharedCheck_1742_; 
lean_dec_ref(v___f_1702_);
v_a_1735_ = lean_ctor_get(v___x_1732_, 0);
v_isSharedCheck_1742_ = !lean_is_exclusive(v___x_1732_);
if (v_isSharedCheck_1742_ == 0)
{
v___x_1737_ = v___x_1732_;
v_isShared_1738_ = v_isSharedCheck_1742_;
goto v_resetjp_1736_;
}
else
{
lean_inc(v_a_1735_);
lean_dec(v___x_1732_);
v___x_1737_ = lean_box(0);
v_isShared_1738_ = v_isSharedCheck_1742_;
goto v_resetjp_1736_;
}
v_resetjp_1736_:
{
lean_object* v___x_1740_; 
if (v_isShared_1738_ == 0)
{
v___x_1740_ = v___x_1737_;
goto v_reusejp_1739_;
}
else
{
lean_object* v_reuseFailAlloc_1741_; 
v_reuseFailAlloc_1741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1741_, 0, v_a_1735_);
v___x_1740_ = v_reuseFailAlloc_1741_;
goto v_reusejp_1739_;
}
v_reusejp_1739_:
{
return v___x_1740_;
}
}
}
}
else
{
lean_dec_ref(v___f_1702_);
lean_dec(v___x_1701_);
return v___x_1731_;
}
}
else
{
lean_object* v___x_1744_; 
lean_dec(v_a_1724_);
lean_dec_ref(v___f_1702_);
lean_dec(v___x_1701_);
if (v_isShared_1727_ == 0)
{
lean_ctor_set_tag(v___x_1726_, 1);
lean_ctor_set(v___x_1726_, 0, v___y_1729_);
v___x_1744_ = v___x_1726_;
goto v_reusejp_1743_;
}
else
{
lean_object* v_reuseFailAlloc_1745_; 
v_reuseFailAlloc_1745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1745_, 0, v___y_1729_);
v___x_1744_ = v_reuseFailAlloc_1745_;
goto v_reusejp_1743_;
}
v_reusejp_1743_:
{
return v___x_1744_;
}
}
}
v___jp_1746_:
{
uint8_t v___x_1748_; 
v___x_1748_ = l_Lean_Exception_isInterrupt(v_a_1747_);
if (v___x_1748_ == 0)
{
uint8_t v___x_1749_; 
lean_inc_ref(v_a_1747_);
v___x_1749_ = l_Lean_Exception_isRuntime(v_a_1747_);
v___y_1729_ = v_a_1747_;
v___y_1730_ = v___x_1749_;
goto v___jp_1728_;
}
else
{
v___y_1729_ = v_a_1747_;
v___y_1730_ = v___x_1748_;
goto v___jp_1728_;
}
}
}
}
else
{
lean_object* v_a_1758_; lean_object* v___x_1760_; uint8_t v_isShared_1761_; uint8_t v_isSharedCheck_1765_; 
lean_dec_ref(v___f_1702_);
lean_dec(v___x_1701_);
v_a_1758_ = lean_ctor_get(v___x_1723_, 0);
v_isSharedCheck_1765_ = !lean_is_exclusive(v___x_1723_);
if (v_isSharedCheck_1765_ == 0)
{
v___x_1760_ = v___x_1723_;
v_isShared_1761_ = v_isSharedCheck_1765_;
goto v_resetjp_1759_;
}
else
{
lean_inc(v_a_1758_);
lean_dec(v___x_1723_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___lam__1___boxed(lean_object* v___x_1766_, lean_object* v___x_1767_, lean_object* v___f_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_){
_start:
{
uint8_t v___x_3542__boxed_1778_; lean_object* v_res_1779_; 
v___x_3542__boxed_1778_ = lean_unbox(v___x_1766_);
v_res_1779_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___lam__1(v___x_3542__boxed_1778_, v___x_1767_, v___f_1768_, v___y_1769_, v___y_1770_, v___y_1771_, v___y_1772_, v___y_1773_, v___y_1774_, v___y_1775_, v___y_1776_);
lean_dec(v___y_1776_);
lean_dec_ref(v___y_1775_);
lean_dec(v___y_1774_);
lean_dec_ref(v___y_1773_);
lean_dec(v___y_1772_);
lean_dec_ref(v___y_1771_);
lean_dec(v___y_1770_);
lean_dec_ref(v___y_1769_);
return v_res_1779_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply(lean_object* v_stx_1787_, lean_object* v_a_1788_, lean_object* v_a_1789_, lean_object* v_a_1790_, lean_object* v_a_1791_, lean_object* v_a_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_, lean_object* v_a_1795_){
_start:
{
lean_object* v___x_1797_; 
v___x_1797_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_ensureSym(v_a_1788_, v_a_1789_, v_a_1790_, v_a_1791_, v_a_1792_, v_a_1793_, v_a_1794_, v_a_1795_);
if (lean_obj_tag(v___x_1797_) == 0)
{
lean_object* v___x_1798_; uint8_t v___x_1799_; 
lean_dec_ref(v___x_1797_);
v___x_1798_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___closed__1));
lean_inc(v_stx_1787_);
v___x_1799_ = l_Lean_Syntax_isOfKind(v_stx_1787_, v___x_1798_);
if (v___x_1799_ == 0)
{
lean_object* v___x_1800_; 
lean_dec(v_stx_1787_);
v___x_1800_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro_spec__0___redArg();
return v___x_1800_;
}
else
{
lean_object* v___x_1801_; 
v___x_1801_ = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(v_a_1789_, v_a_1792_, v_a_1793_, v_a_1794_, v_a_1795_);
if (lean_obj_tag(v___x_1801_) == 0)
{
lean_object* v_a_1802_; lean_object* v_mvarId_1803_; lean_object* v___f_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; uint8_t v___x_1808_; lean_object* v___x_1809_; lean_object* v___y_1810_; lean_object* v___x_1811_; 
v_a_1802_ = lean_ctor_get(v___x_1801_, 0);
lean_inc(v_a_1802_);
lean_dec_ref(v___x_1801_);
v_mvarId_1803_ = lean_ctor_get(v_a_1802_, 1);
lean_inc(v_mvarId_1803_);
v___f_1804_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___lam__0___boxed), 11, 1);
lean_closure_set(v___f_1804_, 0, v_a_1802_);
v___x_1805_ = lean_unsigned_to_nat(1u);
v___x_1806_ = l_Lean_Syntax_getArg(v_stx_1787_, v___x_1805_);
lean_dec(v_stx_1787_);
v___x_1807_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__0___redArg___closed__6));
lean_inc(v___x_1806_);
v___x_1808_ = l_Lean_Syntax_isOfKind(v___x_1806_, v___x_1807_);
v___x_1809_ = lean_box(v___x_1808_);
v___y_1810_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___lam__1___boxed), 12, 3);
lean_closure_set(v___y_1810_, 0, v___x_1809_);
lean_closure_set(v___y_1810_, 1, v___x_1806_);
lean_closure_set(v___y_1810_, 2, v___f_1804_);
v___x_1811_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply_spec__0___redArg(v_mvarId_1803_, v___y_1810_, v_a_1788_, v_a_1789_, v_a_1790_, v_a_1791_, v_a_1792_, v_a_1793_, v_a_1794_, v_a_1795_);
return v___x_1811_;
}
else
{
lean_object* v_a_1812_; lean_object* v___x_1814_; uint8_t v_isShared_1815_; uint8_t v_isSharedCheck_1819_; 
lean_dec(v_stx_1787_);
v_a_1812_ = lean_ctor_get(v___x_1801_, 0);
v_isSharedCheck_1819_ = !lean_is_exclusive(v___x_1801_);
if (v_isSharedCheck_1819_ == 0)
{
v___x_1814_ = v___x_1801_;
v_isShared_1815_ = v_isSharedCheck_1819_;
goto v_resetjp_1813_;
}
else
{
lean_inc(v_a_1812_);
lean_dec(v___x_1801_);
v___x_1814_ = lean_box(0);
v_isShared_1815_ = v_isSharedCheck_1819_;
goto v_resetjp_1813_;
}
v_resetjp_1813_:
{
lean_object* v___x_1817_; 
if (v_isShared_1815_ == 0)
{
v___x_1817_ = v___x_1814_;
goto v_reusejp_1816_;
}
else
{
lean_object* v_reuseFailAlloc_1818_; 
v_reuseFailAlloc_1818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1818_, 0, v_a_1812_);
v___x_1817_ = v_reuseFailAlloc_1818_;
goto v_reusejp_1816_;
}
v_reusejp_1816_:
{
return v___x_1817_;
}
}
}
}
}
else
{
lean_dec(v_stx_1787_);
return v___x_1797_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___boxed(lean_object* v_stx_1820_, lean_object* v_a_1821_, lean_object* v_a_1822_, lean_object* v_a_1823_, lean_object* v_a_1824_, lean_object* v_a_1825_, lean_object* v_a_1826_, lean_object* v_a_1827_, lean_object* v_a_1828_, lean_object* v_a_1829_){
_start:
{
lean_object* v_res_1830_; 
v_res_1830_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply(v_stx_1820_, v_a_1821_, v_a_1822_, v_a_1823_, v_a_1824_, v_a_1825_, v_a_1826_, v_a_1827_, v_a_1828_);
lean_dec(v_a_1828_);
lean_dec_ref(v_a_1827_);
lean_dec(v_a_1826_);
lean_dec_ref(v_a_1825_);
lean_dec(v_a_1824_);
lean_dec_ref(v_a_1823_);
lean_dec(v_a_1822_);
lean_dec_ref(v_a_1821_);
return v_res_1830_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply__1(){
_start:
{
lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; 
v___x_1836_ = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
v___x_1837_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___closed__1));
v___x_1838_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply__1___closed__1));
v___x_1839_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___boxed), 10, 0);
v___x_1840_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1836_, v___x_1837_, v___x_1838_, v___x_1839_);
return v___x_1840_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply__1___boxed(lean_object* v_a_1841_){
_start:
{
lean_object* v_res_1842_; 
v_res_1842_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply__1();
return v_res_1842_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize(lean_object* v_stx_1843_, lean_object* v_a_1844_, lean_object* v_a_1845_, lean_object* v_a_1846_, lean_object* v_a_1847_, lean_object* v_a_1848_, lean_object* v_a_1849_, lean_object* v_a_1850_, lean_object* v_a_1851_){
_start:
{
lean_object* v___x_1853_; 
v___x_1853_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_ensureSym(v_a_1844_, v_a_1845_, v_a_1846_, v_a_1847_, v_a_1848_, v_a_1849_, v_a_1850_, v_a_1851_);
if (lean_obj_tag(v___x_1853_) == 0)
{
lean_object* v___x_1854_; 
lean_dec_ref(v___x_1853_);
v___x_1854_ = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(v_a_1845_, v_a_1848_, v_a_1849_, v_a_1850_, v_a_1851_);
if (lean_obj_tag(v___x_1854_) == 0)
{
lean_object* v_a_1855_; lean_object* v___y_1857_; lean_object* v___x_1872_; lean_object* v___x_1873_; uint8_t v___x_1874_; 
v_a_1855_ = lean_ctor_get(v___x_1854_, 0);
lean_inc(v_a_1855_);
lean_dec_ref(v___x_1854_);
v___x_1872_ = lean_unsigned_to_nat(1u);
v___x_1873_ = l_Lean_Syntax_getArg(v_stx_1843_, v___x_1872_);
v___x_1874_ = l_Lean_Syntax_isNone(v___x_1873_);
if (v___x_1874_ == 0)
{
lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; 
v___x_1875_ = lean_unsigned_to_nat(0u);
v___x_1876_ = l_Lean_Syntax_getArg(v___x_1873_, v___x_1875_);
lean_dec(v___x_1873_);
v___x_1877_ = l_Lean_Syntax_toNat(v___x_1876_);
lean_dec(v___x_1876_);
v___y_1857_ = v___x_1877_;
goto v___jp_1856_;
}
else
{
lean_dec(v___x_1873_);
v___y_1857_ = v___x_1872_;
goto v___jp_1856_;
}
v___jp_1856_:
{
lean_object* v___x_1858_; lean_object* v___x_1859_; 
v___x_1858_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Goal_internalize___boxed), 12, 2);
lean_closure_set(v___x_1858_, 0, v_a_1855_);
lean_closure_set(v___x_1858_, 1, v___y_1857_);
v___x_1859_ = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(v___x_1858_, v_a_1844_, v_a_1845_, v_a_1848_, v_a_1849_, v_a_1850_, v_a_1851_);
if (lean_obj_tag(v___x_1859_) == 0)
{
lean_object* v_a_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; 
v_a_1860_ = lean_ctor_get(v___x_1859_, 0);
lean_inc(v_a_1860_);
lean_dec_ref(v___x_1859_);
v___x_1861_ = lean_box(0);
v___x_1862_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1862_, 0, v_a_1860_);
lean_ctor_set(v___x_1862_, 1, v___x_1861_);
v___x_1863_ = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(v___x_1862_, v_a_1845_, v_a_1848_, v_a_1849_, v_a_1850_, v_a_1851_);
return v___x_1863_;
}
else
{
lean_object* v_a_1864_; lean_object* v___x_1866_; uint8_t v_isShared_1867_; uint8_t v_isSharedCheck_1871_; 
v_a_1864_ = lean_ctor_get(v___x_1859_, 0);
v_isSharedCheck_1871_ = !lean_is_exclusive(v___x_1859_);
if (v_isSharedCheck_1871_ == 0)
{
v___x_1866_ = v___x_1859_;
v_isShared_1867_ = v_isSharedCheck_1871_;
goto v_resetjp_1865_;
}
else
{
lean_inc(v_a_1864_);
lean_dec(v___x_1859_);
v___x_1866_ = lean_box(0);
v_isShared_1867_ = v_isSharedCheck_1871_;
goto v_resetjp_1865_;
}
v_resetjp_1865_:
{
lean_object* v___x_1869_; 
if (v_isShared_1867_ == 0)
{
v___x_1869_ = v___x_1866_;
goto v_reusejp_1868_;
}
else
{
lean_object* v_reuseFailAlloc_1870_; 
v_reuseFailAlloc_1870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1870_, 0, v_a_1864_);
v___x_1869_ = v_reuseFailAlloc_1870_;
goto v_reusejp_1868_;
}
v_reusejp_1868_:
{
return v___x_1869_;
}
}
}
}
}
else
{
lean_object* v_a_1878_; lean_object* v___x_1880_; uint8_t v_isShared_1881_; uint8_t v_isSharedCheck_1885_; 
v_a_1878_ = lean_ctor_get(v___x_1854_, 0);
v_isSharedCheck_1885_ = !lean_is_exclusive(v___x_1854_);
if (v_isSharedCheck_1885_ == 0)
{
v___x_1880_ = v___x_1854_;
v_isShared_1881_ = v_isSharedCheck_1885_;
goto v_resetjp_1879_;
}
else
{
lean_inc(v_a_1878_);
lean_dec(v___x_1854_);
v___x_1880_ = lean_box(0);
v_isShared_1881_ = v_isSharedCheck_1885_;
goto v_resetjp_1879_;
}
v_resetjp_1879_:
{
lean_object* v___x_1883_; 
if (v_isShared_1881_ == 0)
{
v___x_1883_ = v___x_1880_;
goto v_reusejp_1882_;
}
else
{
lean_object* v_reuseFailAlloc_1884_; 
v_reuseFailAlloc_1884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1884_, 0, v_a_1878_);
v___x_1883_ = v_reuseFailAlloc_1884_;
goto v_reusejp_1882_;
}
v_reusejp_1882_:
{
return v___x_1883_;
}
}
}
}
else
{
return v___x_1853_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize___boxed(lean_object* v_stx_1886_, lean_object* v_a_1887_, lean_object* v_a_1888_, lean_object* v_a_1889_, lean_object* v_a_1890_, lean_object* v_a_1891_, lean_object* v_a_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_){
_start:
{
lean_object* v_res_1896_; 
v_res_1896_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize(v_stx_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_);
lean_dec(v_a_1894_);
lean_dec_ref(v_a_1893_);
lean_dec(v_a_1892_);
lean_dec_ref(v_a_1891_);
lean_dec(v_a_1890_);
lean_dec_ref(v_a_1889_);
lean_dec(v_a_1888_);
lean_dec_ref(v_a_1887_);
lean_dec(v_stx_1886_);
return v_res_1896_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize__1(){
_start:
{
lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; 
v___x_1909_ = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
v___x_1910_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize__1___closed__1));
v___x_1911_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize__1___closed__3));
v___x_1912_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize___boxed), 10, 0);
v___x_1913_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1909_, v___x_1910_, v___x_1911_, v___x_1912_);
return v___x_1913_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize__1___boxed(lean_object* v_a_1914_){
_start:
{
lean_object* v_res_1915_; 
v_res_1915_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize__1();
return v_res_1915_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll___redArg(lean_object* v_a_1916_, lean_object* v_a_1917_, lean_object* v_a_1918_, lean_object* v_a_1919_, lean_object* v_a_1920_, lean_object* v_a_1921_, lean_object* v_a_1922_, lean_object* v_a_1923_){
_start:
{
lean_object* v___x_1925_; 
v___x_1925_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_ensureSym(v_a_1916_, v_a_1917_, v_a_1918_, v_a_1919_, v_a_1920_, v_a_1921_, v_a_1922_, v_a_1923_);
if (lean_obj_tag(v___x_1925_) == 0)
{
lean_object* v___x_1926_; 
lean_dec_ref(v___x_1925_);
v___x_1926_ = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(v_a_1917_, v_a_1920_, v_a_1921_, v_a_1922_, v_a_1923_);
if (lean_obj_tag(v___x_1926_) == 0)
{
lean_object* v_a_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; 
v_a_1927_ = lean_ctor_get(v___x_1926_, 0);
lean_inc(v_a_1927_);
lean_dec_ref(v___x_1926_);
v___x_1928_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Goal_internalizeAll___boxed), 11, 1);
lean_closure_set(v___x_1928_, 0, v_a_1927_);
v___x_1929_ = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(v___x_1928_, v_a_1916_, v_a_1917_, v_a_1920_, v_a_1921_, v_a_1922_, v_a_1923_);
if (lean_obj_tag(v___x_1929_) == 0)
{
lean_object* v_a_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; 
v_a_1930_ = lean_ctor_get(v___x_1929_, 0);
lean_inc(v_a_1930_);
lean_dec_ref(v___x_1929_);
v___x_1931_ = lean_box(0);
v___x_1932_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1932_, 0, v_a_1930_);
lean_ctor_set(v___x_1932_, 1, v___x_1931_);
v___x_1933_ = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(v___x_1932_, v_a_1917_, v_a_1920_, v_a_1921_, v_a_1922_, v_a_1923_);
return v___x_1933_;
}
else
{
lean_object* v_a_1934_; lean_object* v___x_1936_; uint8_t v_isShared_1937_; uint8_t v_isSharedCheck_1941_; 
v_a_1934_ = lean_ctor_get(v___x_1929_, 0);
v_isSharedCheck_1941_ = !lean_is_exclusive(v___x_1929_);
if (v_isSharedCheck_1941_ == 0)
{
v___x_1936_ = v___x_1929_;
v_isShared_1937_ = v_isSharedCheck_1941_;
goto v_resetjp_1935_;
}
else
{
lean_inc(v_a_1934_);
lean_dec(v___x_1929_);
v___x_1936_ = lean_box(0);
v_isShared_1937_ = v_isSharedCheck_1941_;
goto v_resetjp_1935_;
}
v_resetjp_1935_:
{
lean_object* v___x_1939_; 
if (v_isShared_1937_ == 0)
{
v___x_1939_ = v___x_1936_;
goto v_reusejp_1938_;
}
else
{
lean_object* v_reuseFailAlloc_1940_; 
v_reuseFailAlloc_1940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1940_, 0, v_a_1934_);
v___x_1939_ = v_reuseFailAlloc_1940_;
goto v_reusejp_1938_;
}
v_reusejp_1938_:
{
return v___x_1939_;
}
}
}
}
else
{
lean_object* v_a_1942_; lean_object* v___x_1944_; uint8_t v_isShared_1945_; uint8_t v_isSharedCheck_1949_; 
v_a_1942_ = lean_ctor_get(v___x_1926_, 0);
v_isSharedCheck_1949_ = !lean_is_exclusive(v___x_1926_);
if (v_isSharedCheck_1949_ == 0)
{
v___x_1944_ = v___x_1926_;
v_isShared_1945_ = v_isSharedCheck_1949_;
goto v_resetjp_1943_;
}
else
{
lean_inc(v_a_1942_);
lean_dec(v___x_1926_);
v___x_1944_ = lean_box(0);
v_isShared_1945_ = v_isSharedCheck_1949_;
goto v_resetjp_1943_;
}
v_resetjp_1943_:
{
lean_object* v___x_1947_; 
if (v_isShared_1945_ == 0)
{
v___x_1947_ = v___x_1944_;
goto v_reusejp_1946_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v_a_1942_);
v___x_1947_ = v_reuseFailAlloc_1948_;
goto v_reusejp_1946_;
}
v_reusejp_1946_:
{
return v___x_1947_;
}
}
}
}
else
{
return v___x_1925_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll___redArg___boxed(lean_object* v_a_1950_, lean_object* v_a_1951_, lean_object* v_a_1952_, lean_object* v_a_1953_, lean_object* v_a_1954_, lean_object* v_a_1955_, lean_object* v_a_1956_, lean_object* v_a_1957_, lean_object* v_a_1958_){
_start:
{
lean_object* v_res_1959_; 
v_res_1959_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll___redArg(v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_, v_a_1954_, v_a_1955_, v_a_1956_, v_a_1957_);
lean_dec(v_a_1957_);
lean_dec_ref(v_a_1956_);
lean_dec(v_a_1955_);
lean_dec_ref(v_a_1954_);
lean_dec(v_a_1953_);
lean_dec_ref(v_a_1952_);
lean_dec(v_a_1951_);
lean_dec_ref(v_a_1950_);
return v_res_1959_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll(lean_object* v_x_1960_, lean_object* v_a_1961_, lean_object* v_a_1962_, lean_object* v_a_1963_, lean_object* v_a_1964_, lean_object* v_a_1965_, lean_object* v_a_1966_, lean_object* v_a_1967_, lean_object* v_a_1968_){
_start:
{
lean_object* v___x_1970_; 
v___x_1970_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll___redArg(v_a_1961_, v_a_1962_, v_a_1963_, v_a_1964_, v_a_1965_, v_a_1966_, v_a_1967_, v_a_1968_);
return v___x_1970_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll___boxed(lean_object* v_x_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_, lean_object* v_a_1977_, lean_object* v_a_1978_, lean_object* v_a_1979_, lean_object* v_a_1980_){
_start:
{
lean_object* v_res_1981_; 
v_res_1981_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll(v_x_1971_, v_a_1972_, v_a_1973_, v_a_1974_, v_a_1975_, v_a_1976_, v_a_1977_, v_a_1978_, v_a_1979_);
lean_dec(v_a_1979_);
lean_dec_ref(v_a_1978_);
lean_dec(v_a_1977_);
lean_dec_ref(v_a_1976_);
lean_dec(v_a_1975_);
lean_dec_ref(v_a_1974_);
lean_dec(v_a_1973_);
lean_dec_ref(v_a_1972_);
lean_dec(v_x_1971_);
return v_res_1981_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll__1(){
_start:
{
lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; 
v___x_1994_ = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
v___x_1995_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll__1___closed__1));
v___x_1996_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll__1___closed__3));
v___x_1997_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll___boxed), 10, 0);
v___x_1998_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1994_, v___x_1995_, v___x_1996_, v___x_1997_);
return v___x_1998_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll__1___boxed(lean_object* v_a_1999_){
_start:
{
lean_object* v_res_2000_; 
v_res_2000_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll__1();
return v_res_2000_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___redArg___closed__1(void){
_start:
{
lean_object* v___x_2002_; lean_object* v___x_2003_; 
v___x_2002_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___redArg___closed__0));
v___x_2003_ = l_Lean_stringToMessageData(v___x_2002_);
return v___x_2003_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___redArg___closed__3(void){
_start:
{
lean_object* v___x_2005_; lean_object* v___x_2006_; 
v___x_2005_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___redArg___closed__2));
v___x_2006_ = l_Lean_stringToMessageData(v___x_2005_);
return v___x_2006_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___redArg(lean_object* v_a_2007_, lean_object* v_a_2008_, lean_object* v_a_2009_, lean_object* v_a_2010_, lean_object* v_a_2011_, lean_object* v_a_2012_, lean_object* v_a_2013_, lean_object* v_a_2014_){
_start:
{
lean_object* v___x_2016_; 
v___x_2016_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_ensureSym(v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_);
if (lean_obj_tag(v___x_2016_) == 0)
{
lean_object* v___x_2017_; 
lean_dec_ref(v___x_2016_);
v___x_2017_ = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(v_a_2008_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_);
if (lean_obj_tag(v___x_2017_) == 0)
{
lean_object* v_a_2018_; lean_object* v_toGoalState_2019_; lean_object* v_mvarId_2020_; lean_object* v___x_2022_; uint8_t v_isShared_2023_; uint8_t v_isSharedCheck_2122_; 
v_a_2018_ = lean_ctor_get(v___x_2017_, 0);
lean_inc(v_a_2018_);
lean_dec_ref(v___x_2017_);
v_toGoalState_2019_ = lean_ctor_get(v_a_2018_, 0);
v_mvarId_2020_ = lean_ctor_get(v_a_2018_, 1);
v_isSharedCheck_2122_ = !lean_is_exclusive(v_a_2018_);
if (v_isSharedCheck_2122_ == 0)
{
v___x_2022_ = v_a_2018_;
v_isShared_2023_ = v_isSharedCheck_2122_;
goto v_resetjp_2021_;
}
else
{
lean_inc(v_mvarId_2020_);
lean_inc(v_toGoalState_2019_);
lean_dec(v_a_2018_);
v___x_2022_ = lean_box(0);
v_isShared_2023_ = v_isSharedCheck_2122_;
goto v_resetjp_2021_;
}
v_resetjp_2021_:
{
lean_object* v_mvarId_2025_; lean_object* v___y_2026_; lean_object* v___y_2027_; lean_object* v___y_2028_; lean_object* v___y_2029_; lean_object* v___y_2030_; lean_object* v___y_2031_; lean_object* v___x_2081_; 
lean_inc(v_mvarId_2020_);
v___x_2081_ = l_Lean_MVarId_getType(v_mvarId_2020_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_);
if (lean_obj_tag(v___x_2081_) == 0)
{
lean_object* v_a_2082_; lean_object* v___y_2084_; lean_object* v___y_2085_; lean_object* v___y_2086_; lean_object* v___y_2087_; lean_object* v___y_2088_; lean_object* v___y_2089_; uint8_t v___x_2111_; 
v_a_2082_ = lean_ctor_get(v___x_2081_, 0);
lean_inc_n(v_a_2082_, 2);
lean_dec_ref(v___x_2081_);
v___x_2111_ = l_Lean_Expr_isFalse(v_a_2082_);
if (v___x_2111_ == 0)
{
v___y_2084_ = v_a_2007_;
v___y_2085_ = v_a_2008_;
v___y_2086_ = v_a_2011_;
v___y_2087_ = v_a_2012_;
v___y_2088_ = v_a_2013_;
v___y_2089_ = v_a_2014_;
goto v___jp_2083_;
}
else
{
lean_object* v___x_2112_; lean_object* v___x_2113_; 
lean_dec(v_a_2082_);
lean_del_object(v___x_2022_);
lean_dec(v_mvarId_2020_);
lean_dec_ref(v_toGoalState_2019_);
v___x_2112_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___redArg___closed__3, &l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___redArg___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___redArg___closed__3);
v___x_2113_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_ensureSym_spec__0___redArg(v___x_2112_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_);
return v___x_2113_;
}
v___jp_2083_:
{
lean_object* v___x_2090_; 
v___x_2090_ = l_Lean_Meta_isProp(v_a_2082_, v___y_2086_, v___y_2087_, v___y_2088_, v___y_2089_);
if (lean_obj_tag(v___x_2090_) == 0)
{
lean_object* v_a_2091_; uint8_t v___x_2092_; 
v_a_2091_ = lean_ctor_get(v___x_2090_, 0);
lean_inc(v_a_2091_);
lean_dec_ref(v___x_2090_);
v___x_2092_ = lean_unbox(v_a_2091_);
lean_dec(v_a_2091_);
if (v___x_2092_ == 0)
{
lean_object* v___x_2093_; 
v___x_2093_ = l_Lean_MVarId_exfalso(v_mvarId_2020_, v___y_2086_, v___y_2087_, v___y_2088_, v___y_2089_);
if (lean_obj_tag(v___x_2093_) == 0)
{
lean_object* v_a_2094_; 
v_a_2094_ = lean_ctor_get(v___x_2093_, 0);
lean_inc(v_a_2094_);
lean_dec_ref(v___x_2093_);
v_mvarId_2025_ = v_a_2094_;
v___y_2026_ = v___y_2084_;
v___y_2027_ = v___y_2085_;
v___y_2028_ = v___y_2086_;
v___y_2029_ = v___y_2087_;
v___y_2030_ = v___y_2088_;
v___y_2031_ = v___y_2089_;
goto v___jp_2024_;
}
else
{
lean_object* v_a_2095_; lean_object* v___x_2097_; uint8_t v_isShared_2098_; uint8_t v_isSharedCheck_2102_; 
lean_del_object(v___x_2022_);
lean_dec_ref(v_toGoalState_2019_);
v_a_2095_ = lean_ctor_get(v___x_2093_, 0);
v_isSharedCheck_2102_ = !lean_is_exclusive(v___x_2093_);
if (v_isSharedCheck_2102_ == 0)
{
v___x_2097_ = v___x_2093_;
v_isShared_2098_ = v_isSharedCheck_2102_;
goto v_resetjp_2096_;
}
else
{
lean_inc(v_a_2095_);
lean_dec(v___x_2093_);
v___x_2097_ = lean_box(0);
v_isShared_2098_ = v_isSharedCheck_2102_;
goto v_resetjp_2096_;
}
v_resetjp_2096_:
{
lean_object* v___x_2100_; 
if (v_isShared_2098_ == 0)
{
v___x_2100_ = v___x_2097_;
goto v_reusejp_2099_;
}
else
{
lean_object* v_reuseFailAlloc_2101_; 
v_reuseFailAlloc_2101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2101_, 0, v_a_2095_);
v___x_2100_ = v_reuseFailAlloc_2101_;
goto v_reusejp_2099_;
}
v_reusejp_2099_:
{
return v___x_2100_;
}
}
}
}
else
{
v_mvarId_2025_ = v_mvarId_2020_;
v___y_2026_ = v___y_2084_;
v___y_2027_ = v___y_2085_;
v___y_2028_ = v___y_2086_;
v___y_2029_ = v___y_2087_;
v___y_2030_ = v___y_2088_;
v___y_2031_ = v___y_2089_;
goto v___jp_2024_;
}
}
else
{
lean_object* v_a_2103_; lean_object* v___x_2105_; uint8_t v_isShared_2106_; uint8_t v_isSharedCheck_2110_; 
lean_del_object(v___x_2022_);
lean_dec(v_mvarId_2020_);
lean_dec_ref(v_toGoalState_2019_);
v_a_2103_ = lean_ctor_get(v___x_2090_, 0);
v_isSharedCheck_2110_ = !lean_is_exclusive(v___x_2090_);
if (v_isSharedCheck_2110_ == 0)
{
v___x_2105_ = v___x_2090_;
v_isShared_2106_ = v_isSharedCheck_2110_;
goto v_resetjp_2104_;
}
else
{
lean_inc(v_a_2103_);
lean_dec(v___x_2090_);
v___x_2105_ = lean_box(0);
v_isShared_2106_ = v_isSharedCheck_2110_;
goto v_resetjp_2104_;
}
v_resetjp_2104_:
{
lean_object* v___x_2108_; 
if (v_isShared_2106_ == 0)
{
v___x_2108_ = v___x_2105_;
goto v_reusejp_2107_;
}
else
{
lean_object* v_reuseFailAlloc_2109_; 
v_reuseFailAlloc_2109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2109_, 0, v_a_2103_);
v___x_2108_ = v_reuseFailAlloc_2109_;
goto v_reusejp_2107_;
}
v_reusejp_2107_:
{
return v___x_2108_;
}
}
}
}
}
else
{
lean_object* v_a_2114_; lean_object* v___x_2116_; uint8_t v_isShared_2117_; uint8_t v_isSharedCheck_2121_; 
lean_del_object(v___x_2022_);
lean_dec(v_mvarId_2020_);
lean_dec_ref(v_toGoalState_2019_);
v_a_2114_ = lean_ctor_get(v___x_2081_, 0);
v_isSharedCheck_2121_ = !lean_is_exclusive(v___x_2081_);
if (v_isSharedCheck_2121_ == 0)
{
v___x_2116_ = v___x_2081_;
v_isShared_2117_ = v_isSharedCheck_2121_;
goto v_resetjp_2115_;
}
else
{
lean_inc(v_a_2114_);
lean_dec(v___x_2081_);
v___x_2116_ = lean_box(0);
v_isShared_2117_ = v_isSharedCheck_2121_;
goto v_resetjp_2115_;
}
v_resetjp_2115_:
{
lean_object* v___x_2119_; 
if (v_isShared_2117_ == 0)
{
v___x_2119_ = v___x_2116_;
goto v_reusejp_2118_;
}
else
{
lean_object* v_reuseFailAlloc_2120_; 
v_reuseFailAlloc_2120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2120_, 0, v_a_2114_);
v___x_2119_ = v_reuseFailAlloc_2120_;
goto v_reusejp_2118_;
}
v_reusejp_2118_:
{
return v___x_2119_;
}
}
}
v___jp_2024_:
{
lean_object* v___x_2032_; 
v___x_2032_ = l_Lean_MVarId_byContra_x3f(v_mvarId_2025_, v___y_2028_, v___y_2029_, v___y_2030_, v___y_2031_);
if (lean_obj_tag(v___x_2032_) == 0)
{
lean_object* v_a_2033_; 
v_a_2033_ = lean_ctor_get(v___x_2032_, 0);
lean_inc(v_a_2033_);
lean_dec_ref(v___x_2032_);
if (lean_obj_tag(v_a_2033_) == 1)
{
lean_object* v_val_2034_; uint8_t v___x_2035_; lean_object* v___x_2036_; 
v_val_2034_ = lean_ctor_get(v_a_2033_, 0);
lean_inc(v_val_2034_);
lean_dec_ref(v_a_2033_);
v___x_2035_ = 0;
v___x_2036_ = l_Lean_Meta_intro1Core(v_val_2034_, v___x_2035_, v___y_2028_, v___y_2029_, v___y_2030_, v___y_2031_);
if (lean_obj_tag(v___x_2036_) == 0)
{
lean_object* v_a_2037_; lean_object* v_snd_2038_; lean_object* v___x_2040_; uint8_t v_isShared_2041_; uint8_t v_isSharedCheck_2061_; 
v_a_2037_ = lean_ctor_get(v___x_2036_, 0);
lean_inc(v_a_2037_);
lean_dec_ref(v___x_2036_);
v_snd_2038_ = lean_ctor_get(v_a_2037_, 1);
v_isSharedCheck_2061_ = !lean_is_exclusive(v_a_2037_);
if (v_isSharedCheck_2061_ == 0)
{
lean_object* v_unused_2062_; 
v_unused_2062_ = lean_ctor_get(v_a_2037_, 0);
lean_dec(v_unused_2062_);
v___x_2040_ = v_a_2037_;
v_isShared_2041_ = v_isSharedCheck_2061_;
goto v_resetjp_2039_;
}
else
{
lean_inc(v_snd_2038_);
lean_dec(v_a_2037_);
v___x_2040_ = lean_box(0);
v_isShared_2041_ = v_isSharedCheck_2061_;
goto v_resetjp_2039_;
}
v_resetjp_2039_:
{
lean_object* v___x_2043_; 
if (v_isShared_2023_ == 0)
{
lean_ctor_set(v___x_2022_, 1, v_snd_2038_);
v___x_2043_ = v___x_2022_;
goto v_reusejp_2042_;
}
else
{
lean_object* v_reuseFailAlloc_2060_; 
v_reuseFailAlloc_2060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2060_, 0, v_toGoalState_2019_);
lean_ctor_set(v_reuseFailAlloc_2060_, 1, v_snd_2038_);
v___x_2043_ = v_reuseFailAlloc_2060_;
goto v_reusejp_2042_;
}
v_reusejp_2042_:
{
lean_object* v___x_2044_; lean_object* v___x_2045_; 
v___x_2044_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Goal_internalizeAll___boxed), 11, 1);
lean_closure_set(v___x_2044_, 0, v___x_2043_);
v___x_2045_ = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(v___x_2044_, v___y_2026_, v___y_2027_, v___y_2028_, v___y_2029_, v___y_2030_, v___y_2031_);
if (lean_obj_tag(v___x_2045_) == 0)
{
lean_object* v_a_2046_; lean_object* v___x_2047_; lean_object* v___x_2049_; 
v_a_2046_ = lean_ctor_get(v___x_2045_, 0);
lean_inc(v_a_2046_);
lean_dec_ref(v___x_2045_);
v___x_2047_ = lean_box(0);
if (v_isShared_2041_ == 0)
{
lean_ctor_set_tag(v___x_2040_, 1);
lean_ctor_set(v___x_2040_, 1, v___x_2047_);
lean_ctor_set(v___x_2040_, 0, v_a_2046_);
v___x_2049_ = v___x_2040_;
goto v_reusejp_2048_;
}
else
{
lean_object* v_reuseFailAlloc_2051_; 
v_reuseFailAlloc_2051_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2051_, 0, v_a_2046_);
lean_ctor_set(v_reuseFailAlloc_2051_, 1, v___x_2047_);
v___x_2049_ = v_reuseFailAlloc_2051_;
goto v_reusejp_2048_;
}
v_reusejp_2048_:
{
lean_object* v___x_2050_; 
v___x_2050_ = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(v___x_2049_, v___y_2027_, v___y_2028_, v___y_2029_, v___y_2030_, v___y_2031_);
return v___x_2050_;
}
}
else
{
lean_object* v_a_2052_; lean_object* v___x_2054_; uint8_t v_isShared_2055_; uint8_t v_isSharedCheck_2059_; 
lean_del_object(v___x_2040_);
v_a_2052_ = lean_ctor_get(v___x_2045_, 0);
v_isSharedCheck_2059_ = !lean_is_exclusive(v___x_2045_);
if (v_isSharedCheck_2059_ == 0)
{
v___x_2054_ = v___x_2045_;
v_isShared_2055_ = v_isSharedCheck_2059_;
goto v_resetjp_2053_;
}
else
{
lean_inc(v_a_2052_);
lean_dec(v___x_2045_);
v___x_2054_ = lean_box(0);
v_isShared_2055_ = v_isSharedCheck_2059_;
goto v_resetjp_2053_;
}
v_resetjp_2053_:
{
lean_object* v___x_2057_; 
if (v_isShared_2055_ == 0)
{
v___x_2057_ = v___x_2054_;
goto v_reusejp_2056_;
}
else
{
lean_object* v_reuseFailAlloc_2058_; 
v_reuseFailAlloc_2058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2058_, 0, v_a_2052_);
v___x_2057_ = v_reuseFailAlloc_2058_;
goto v_reusejp_2056_;
}
v_reusejp_2056_:
{
return v___x_2057_;
}
}
}
}
}
}
else
{
lean_object* v_a_2063_; lean_object* v___x_2065_; uint8_t v_isShared_2066_; uint8_t v_isSharedCheck_2070_; 
lean_del_object(v___x_2022_);
lean_dec_ref(v_toGoalState_2019_);
v_a_2063_ = lean_ctor_get(v___x_2036_, 0);
v_isSharedCheck_2070_ = !lean_is_exclusive(v___x_2036_);
if (v_isSharedCheck_2070_ == 0)
{
v___x_2065_ = v___x_2036_;
v_isShared_2066_ = v_isSharedCheck_2070_;
goto v_resetjp_2064_;
}
else
{
lean_inc(v_a_2063_);
lean_dec(v___x_2036_);
v___x_2065_ = lean_box(0);
v_isShared_2066_ = v_isSharedCheck_2070_;
goto v_resetjp_2064_;
}
v_resetjp_2064_:
{
lean_object* v___x_2068_; 
if (v_isShared_2066_ == 0)
{
v___x_2068_ = v___x_2065_;
goto v_reusejp_2067_;
}
else
{
lean_object* v_reuseFailAlloc_2069_; 
v_reuseFailAlloc_2069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2069_, 0, v_a_2063_);
v___x_2068_ = v_reuseFailAlloc_2069_;
goto v_reusejp_2067_;
}
v_reusejp_2067_:
{
return v___x_2068_;
}
}
}
}
else
{
lean_object* v___x_2071_; lean_object* v___x_2072_; 
lean_dec(v_a_2033_);
lean_del_object(v___x_2022_);
lean_dec_ref(v_toGoalState_2019_);
v___x_2071_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___redArg___closed__1, &l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___redArg___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___redArg___closed__1);
v___x_2072_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_ensureSym_spec__0___redArg(v___x_2071_, v___y_2028_, v___y_2029_, v___y_2030_, v___y_2031_);
return v___x_2072_;
}
}
else
{
lean_object* v_a_2073_; lean_object* v___x_2075_; uint8_t v_isShared_2076_; uint8_t v_isSharedCheck_2080_; 
lean_del_object(v___x_2022_);
lean_dec_ref(v_toGoalState_2019_);
v_a_2073_ = lean_ctor_get(v___x_2032_, 0);
v_isSharedCheck_2080_ = !lean_is_exclusive(v___x_2032_);
if (v_isSharedCheck_2080_ == 0)
{
v___x_2075_ = v___x_2032_;
v_isShared_2076_ = v_isSharedCheck_2080_;
goto v_resetjp_2074_;
}
else
{
lean_inc(v_a_2073_);
lean_dec(v___x_2032_);
v___x_2075_ = lean_box(0);
v_isShared_2076_ = v_isSharedCheck_2080_;
goto v_resetjp_2074_;
}
v_resetjp_2074_:
{
lean_object* v___x_2078_; 
if (v_isShared_2076_ == 0)
{
v___x_2078_ = v___x_2075_;
goto v_reusejp_2077_;
}
else
{
lean_object* v_reuseFailAlloc_2079_; 
v_reuseFailAlloc_2079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2079_, 0, v_a_2073_);
v___x_2078_ = v_reuseFailAlloc_2079_;
goto v_reusejp_2077_;
}
v_reusejp_2077_:
{
return v___x_2078_;
}
}
}
}
}
}
else
{
lean_object* v_a_2123_; lean_object* v___x_2125_; uint8_t v_isShared_2126_; uint8_t v_isSharedCheck_2130_; 
v_a_2123_ = lean_ctor_get(v___x_2017_, 0);
v_isSharedCheck_2130_ = !lean_is_exclusive(v___x_2017_);
if (v_isSharedCheck_2130_ == 0)
{
v___x_2125_ = v___x_2017_;
v_isShared_2126_ = v_isSharedCheck_2130_;
goto v_resetjp_2124_;
}
else
{
lean_inc(v_a_2123_);
lean_dec(v___x_2017_);
v___x_2125_ = lean_box(0);
v_isShared_2126_ = v_isSharedCheck_2130_;
goto v_resetjp_2124_;
}
v_resetjp_2124_:
{
lean_object* v___x_2128_; 
if (v_isShared_2126_ == 0)
{
v___x_2128_ = v___x_2125_;
goto v_reusejp_2127_;
}
else
{
lean_object* v_reuseFailAlloc_2129_; 
v_reuseFailAlloc_2129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2129_, 0, v_a_2123_);
v___x_2128_ = v_reuseFailAlloc_2129_;
goto v_reusejp_2127_;
}
v_reusejp_2127_:
{
return v___x_2128_;
}
}
}
}
else
{
return v___x_2016_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___redArg___boxed(lean_object* v_a_2131_, lean_object* v_a_2132_, lean_object* v_a_2133_, lean_object* v_a_2134_, lean_object* v_a_2135_, lean_object* v_a_2136_, lean_object* v_a_2137_, lean_object* v_a_2138_, lean_object* v_a_2139_){
_start:
{
lean_object* v_res_2140_; 
v_res_2140_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___redArg(v_a_2131_, v_a_2132_, v_a_2133_, v_a_2134_, v_a_2135_, v_a_2136_, v_a_2137_, v_a_2138_);
lean_dec(v_a_2138_);
lean_dec_ref(v_a_2137_);
lean_dec(v_a_2136_);
lean_dec_ref(v_a_2135_);
lean_dec(v_a_2134_);
lean_dec_ref(v_a_2133_);
lean_dec(v_a_2132_);
lean_dec_ref(v_a_2131_);
return v_res_2140_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra(lean_object* v_x_2141_, lean_object* v_a_2142_, lean_object* v_a_2143_, lean_object* v_a_2144_, lean_object* v_a_2145_, lean_object* v_a_2146_, lean_object* v_a_2147_, lean_object* v_a_2148_, lean_object* v_a_2149_){
_start:
{
lean_object* v___x_2151_; 
v___x_2151_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___redArg(v_a_2142_, v_a_2143_, v_a_2144_, v_a_2145_, v_a_2146_, v_a_2147_, v_a_2148_, v_a_2149_);
return v___x_2151_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___boxed(lean_object* v_x_2152_, lean_object* v_a_2153_, lean_object* v_a_2154_, lean_object* v_a_2155_, lean_object* v_a_2156_, lean_object* v_a_2157_, lean_object* v_a_2158_, lean_object* v_a_2159_, lean_object* v_a_2160_, lean_object* v_a_2161_){
_start:
{
lean_object* v_res_2162_; 
v_res_2162_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra(v_x_2152_, v_a_2153_, v_a_2154_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_, v_a_2160_);
lean_dec(v_a_2160_);
lean_dec_ref(v_a_2159_);
lean_dec(v_a_2158_);
lean_dec_ref(v_a_2157_);
lean_dec(v_a_2156_);
lean_dec_ref(v_a_2155_);
lean_dec(v_a_2154_);
lean_dec_ref(v_a_2153_);
lean_dec(v_x_2152_);
return v_res_2162_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra__1(){
_start:
{
lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; 
v___x_2175_ = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
v___x_2176_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra__1___closed__1));
v___x_2177_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra__1___closed__3));
v___x_2178_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___boxed), 10, 0);
v___x_2179_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2175_, v___x_2176_, v___x_2177_, v___x_2178_);
return v___x_2179_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra__1___boxed(lean_object* v_a_2180_){
_start:
{
lean_object* v_res_2181_; 
v_res_2181_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra__1();
return v_res_2181_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_trivialSimproc___redArg(){
_start:
{
lean_object* v___x_2185_; lean_object* v___x_2186_; 
v___x_2185_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_trivialSimproc___redArg___closed__0));
v___x_2186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2186_, 0, v___x_2185_);
return v___x_2186_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_trivialSimproc___redArg___boxed(lean_object* v_a_2187_){
_start:
{
lean_object* v_res_2188_; 
v_res_2188_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_trivialSimproc___redArg();
return v_res_2188_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_trivialSimproc(lean_object* v_x_2189_, lean_object* v_a_2190_, lean_object* v_a_2191_, lean_object* v_a_2192_, lean_object* v_a_2193_, lean_object* v_a_2194_, lean_object* v_a_2195_, lean_object* v_a_2196_, lean_object* v_a_2197_, lean_object* v_a_2198_){
_start:
{
lean_object* v___x_2200_; 
v___x_2200_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_trivialSimproc___redArg();
return v___x_2200_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_trivialSimproc___boxed(lean_object* v_x_2201_, lean_object* v_a_2202_, lean_object* v_a_2203_, lean_object* v_a_2204_, lean_object* v_a_2205_, lean_object* v_a_2206_, lean_object* v_a_2207_, lean_object* v_a_2208_, lean_object* v_a_2209_, lean_object* v_a_2210_, lean_object* v_a_2211_){
_start:
{
lean_object* v_res_2212_; 
v_res_2212_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_trivialSimproc(v_x_2201_, v_a_2202_, v_a_2203_, v_a_2204_, v_a_2205_, v_a_2206_, v_a_2207_, v_a_2208_, v_a_2209_, v_a_2210_);
lean_dec(v_a_2210_);
lean_dec_ref(v_a_2209_);
lean_dec(v_a_2208_);
lean_dec_ref(v_a_2207_);
lean_dec(v_a_2206_);
lean_dec_ref(v_a_2205_);
lean_dec(v_a_2204_);
lean_dec_ref(v_a_2203_);
lean_dec(v_a_2202_);
lean_dec_ref(v_x_2201_);
return v_res_2212_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabOptSimproc(lean_object* v_stx_x3f_2213_, lean_object* v_a_2214_, lean_object* v_a_2215_, lean_object* v_a_2216_, lean_object* v_a_2217_, lean_object* v_a_2218_, lean_object* v_a_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_){
_start:
{
if (lean_obj_tag(v_stx_x3f_2213_) == 1)
{
lean_object* v_val_2223_; lean_object* v___x_2224_; 
v_val_2223_ = lean_ctor_get(v_stx_x3f_2213_, 0);
lean_inc(v_val_2223_);
lean_dec_ref(v_stx_x3f_2213_);
v___x_2224_ = l_Lean_Elab_Tactic_Grind_elabSymSimproc(v_val_2223_, v_a_2214_, v_a_2215_, v_a_2216_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_);
return v___x_2224_;
}
else
{
lean_object* v___x_2225_; lean_object* v___x_2226_; 
lean_dec(v_stx_x3f_2213_);
v___x_2225_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_trivialSimproc___boxed), 11, 0);
v___x_2226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2226_, 0, v___x_2225_);
return v___x_2226_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabOptSimproc___boxed(lean_object* v_stx_x3f_2227_, lean_object* v_a_2228_, lean_object* v_a_2229_, lean_object* v_a_2230_, lean_object* v_a_2231_, lean_object* v_a_2232_, lean_object* v_a_2233_, lean_object* v_a_2234_, lean_object* v_a_2235_, lean_object* v_a_2236_){
_start:
{
lean_object* v_res_2237_; 
v_res_2237_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabOptSimproc(v_stx_x3f_2227_, v_a_2228_, v_a_2229_, v_a_2230_, v_a_2231_, v_a_2232_, v_a_2233_, v_a_2234_, v_a_2235_);
lean_dec(v_a_2235_);
lean_dec_ref(v_a_2234_);
lean_dec(v_a_2233_);
lean_dec_ref(v_a_2232_);
lean_dec(v_a_2231_);
lean_dec_ref(v_a_2230_);
lean_dec(v_a_2229_);
lean_dec_ref(v_a_2228_);
return v_res_2237_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__0___redArg(lean_object* v___x_2238_, lean_object* v_as_2239_, size_t v_sz_2240_, size_t v_i_2241_, lean_object* v_b_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_){
_start:
{
lean_object* v_a_2249_; uint8_t v___x_2253_; 
v___x_2253_ = lean_usize_dec_lt(v_i_2241_, v_sz_2240_);
if (v___x_2253_ == 0)
{
lean_object* v___x_2254_; 
v___x_2254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2254_, 0, v_b_2242_);
return v___x_2254_;
}
else
{
lean_object* v_fst_2255_; lean_object* v_snd_2256_; lean_object* v___x_2258_; uint8_t v_isShared_2259_; uint8_t v_isSharedCheck_2314_; 
v_fst_2255_ = lean_ctor_get(v_b_2242_, 0);
v_snd_2256_ = lean_ctor_get(v_b_2242_, 1);
v_isSharedCheck_2314_ = !lean_is_exclusive(v_b_2242_);
if (v_isSharedCheck_2314_ == 0)
{
v___x_2258_ = v_b_2242_;
v_isShared_2259_ = v_isSharedCheck_2314_;
goto v_resetjp_2257_;
}
else
{
lean_inc(v_snd_2256_);
lean_inc(v_fst_2255_);
lean_dec(v_b_2242_);
v___x_2258_ = lean_box(0);
v_isShared_2259_ = v_isSharedCheck_2314_;
goto v_resetjp_2257_;
}
v_resetjp_2257_:
{
lean_object* v_a_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; 
v_a_2260_ = lean_array_uget_borrowed(v_as_2239_, v_i_2241_);
v___x_2261_ = l_Lean_TSyntax_getId(v_a_2260_);
v___x_2262_ = l_Lean_LocalContext_findFromUserName_x3f(v___x_2238_, v___x_2261_);
lean_dec(v___x_2261_);
if (lean_obj_tag(v___x_2262_) == 1)
{
lean_object* v_val_2263_; lean_object* v___x_2265_; uint8_t v_isShared_2266_; uint8_t v_isSharedCheck_2287_; 
v_val_2263_ = lean_ctor_get(v___x_2262_, 0);
v_isSharedCheck_2287_ = !lean_is_exclusive(v___x_2262_);
if (v_isSharedCheck_2287_ == 0)
{
v___x_2265_ = v___x_2262_;
v_isShared_2266_ = v_isSharedCheck_2287_;
goto v_resetjp_2264_;
}
else
{
lean_inc(v_val_2263_);
lean_dec(v___x_2262_);
v___x_2265_ = lean_box(0);
v_isShared_2266_ = v_isSharedCheck_2287_;
goto v_resetjp_2264_;
}
v_resetjp_2264_:
{
lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; 
v___x_2267_ = l_Lean_LocalDecl_fvarId(v_val_2263_);
v___x_2268_ = l_Lean_LocalDecl_toExpr(v_val_2263_);
v___x_2269_ = l_Lean_Meta_Sym_Simp_mkTheoremFromExpr(v___x_2268_, v___y_2243_, v___y_2244_, v___y_2245_, v___y_2246_);
if (lean_obj_tag(v___x_2269_) == 0)
{
lean_object* v_a_2270_; lean_object* v___x_2272_; 
v_a_2270_ = lean_ctor_get(v___x_2269_, 0);
lean_inc(v_a_2270_);
lean_dec_ref(v___x_2269_);
if (v_isShared_2266_ == 0)
{
lean_ctor_set(v___x_2265_, 0, v___x_2267_);
v___x_2272_ = v___x_2265_;
goto v_reusejp_2271_;
}
else
{
lean_object* v_reuseFailAlloc_2278_; 
v_reuseFailAlloc_2278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2278_, 0, v___x_2267_);
v___x_2272_ = v_reuseFailAlloc_2278_;
goto v_reusejp_2271_;
}
v_reusejp_2271_:
{
lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2276_; 
v___x_2273_ = lean_array_push(v_fst_2255_, v___x_2272_);
v___x_2274_ = lean_array_push(v_snd_2256_, v_a_2270_);
if (v_isShared_2259_ == 0)
{
lean_ctor_set(v___x_2258_, 1, v___x_2274_);
lean_ctor_set(v___x_2258_, 0, v___x_2273_);
v___x_2276_ = v___x_2258_;
goto v_reusejp_2275_;
}
else
{
lean_object* v_reuseFailAlloc_2277_; 
v_reuseFailAlloc_2277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2277_, 0, v___x_2273_);
lean_ctor_set(v_reuseFailAlloc_2277_, 1, v___x_2274_);
v___x_2276_ = v_reuseFailAlloc_2277_;
goto v_reusejp_2275_;
}
v_reusejp_2275_:
{
v_a_2249_ = v___x_2276_;
goto v___jp_2248_;
}
}
}
else
{
lean_object* v_a_2279_; lean_object* v___x_2281_; uint8_t v_isShared_2282_; uint8_t v_isSharedCheck_2286_; 
lean_dec(v___x_2267_);
lean_del_object(v___x_2265_);
lean_del_object(v___x_2258_);
lean_dec(v_snd_2256_);
lean_dec(v_fst_2255_);
v_a_2279_ = lean_ctor_get(v___x_2269_, 0);
v_isSharedCheck_2286_ = !lean_is_exclusive(v___x_2269_);
if (v_isSharedCheck_2286_ == 0)
{
v___x_2281_ = v___x_2269_;
v_isShared_2282_ = v_isSharedCheck_2286_;
goto v_resetjp_2280_;
}
else
{
lean_inc(v_a_2279_);
lean_dec(v___x_2269_);
v___x_2281_ = lean_box(0);
v_isShared_2282_ = v_isSharedCheck_2286_;
goto v_resetjp_2280_;
}
v_resetjp_2280_:
{
lean_object* v___x_2284_; 
if (v_isShared_2282_ == 0)
{
v___x_2284_ = v___x_2281_;
goto v_reusejp_2283_;
}
else
{
lean_object* v_reuseFailAlloc_2285_; 
v_reuseFailAlloc_2285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2285_, 0, v_a_2279_);
v___x_2284_ = v_reuseFailAlloc_2285_;
goto v_reusejp_2283_;
}
v_reusejp_2283_:
{
return v___x_2284_;
}
}
}
}
}
else
{
lean_object* v___x_2288_; 
lean_dec(v___x_2262_);
lean_inc(v_a_2260_);
v___x_2288_ = l_Lean_realizeGlobalConstNoOverload(v_a_2260_, v___y_2245_, v___y_2246_);
if (lean_obj_tag(v___x_2288_) == 0)
{
lean_object* v_a_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; 
v_a_2289_ = lean_ctor_get(v___x_2288_, 0);
lean_inc_n(v_a_2289_, 2);
lean_dec_ref(v___x_2288_);
v___x_2290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2290_, 0, v_a_2289_);
v___x_2291_ = l_Lean_Meta_Sym_Simp_mkTheoremFromDecl(v_a_2289_, v___y_2243_, v___y_2244_, v___y_2245_, v___y_2246_);
if (lean_obj_tag(v___x_2291_) == 0)
{
lean_object* v_a_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2296_; 
v_a_2292_ = lean_ctor_get(v___x_2291_, 0);
lean_inc(v_a_2292_);
lean_dec_ref(v___x_2291_);
v___x_2293_ = lean_array_push(v_fst_2255_, v___x_2290_);
v___x_2294_ = lean_array_push(v_snd_2256_, v_a_2292_);
if (v_isShared_2259_ == 0)
{
lean_ctor_set(v___x_2258_, 1, v___x_2294_);
lean_ctor_set(v___x_2258_, 0, v___x_2293_);
v___x_2296_ = v___x_2258_;
goto v_reusejp_2295_;
}
else
{
lean_object* v_reuseFailAlloc_2297_; 
v_reuseFailAlloc_2297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2297_, 0, v___x_2293_);
lean_ctor_set(v_reuseFailAlloc_2297_, 1, v___x_2294_);
v___x_2296_ = v_reuseFailAlloc_2297_;
goto v_reusejp_2295_;
}
v_reusejp_2295_:
{
v_a_2249_ = v___x_2296_;
goto v___jp_2248_;
}
}
else
{
lean_object* v_a_2298_; lean_object* v___x_2300_; uint8_t v_isShared_2301_; uint8_t v_isSharedCheck_2305_; 
lean_dec_ref(v___x_2290_);
lean_del_object(v___x_2258_);
lean_dec(v_snd_2256_);
lean_dec(v_fst_2255_);
v_a_2298_ = lean_ctor_get(v___x_2291_, 0);
v_isSharedCheck_2305_ = !lean_is_exclusive(v___x_2291_);
if (v_isSharedCheck_2305_ == 0)
{
v___x_2300_ = v___x_2291_;
v_isShared_2301_ = v_isSharedCheck_2305_;
goto v_resetjp_2299_;
}
else
{
lean_inc(v_a_2298_);
lean_dec(v___x_2291_);
v___x_2300_ = lean_box(0);
v_isShared_2301_ = v_isSharedCheck_2305_;
goto v_resetjp_2299_;
}
v_resetjp_2299_:
{
lean_object* v___x_2303_; 
if (v_isShared_2301_ == 0)
{
v___x_2303_ = v___x_2300_;
goto v_reusejp_2302_;
}
else
{
lean_object* v_reuseFailAlloc_2304_; 
v_reuseFailAlloc_2304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2304_, 0, v_a_2298_);
v___x_2303_ = v_reuseFailAlloc_2304_;
goto v_reusejp_2302_;
}
v_reusejp_2302_:
{
return v___x_2303_;
}
}
}
}
else
{
lean_object* v_a_2306_; lean_object* v___x_2308_; uint8_t v_isShared_2309_; uint8_t v_isSharedCheck_2313_; 
lean_del_object(v___x_2258_);
lean_dec(v_snd_2256_);
lean_dec(v_fst_2255_);
v_a_2306_ = lean_ctor_get(v___x_2288_, 0);
v_isSharedCheck_2313_ = !lean_is_exclusive(v___x_2288_);
if (v_isSharedCheck_2313_ == 0)
{
v___x_2308_ = v___x_2288_;
v_isShared_2309_ = v_isSharedCheck_2313_;
goto v_resetjp_2307_;
}
else
{
lean_inc(v_a_2306_);
lean_dec(v___x_2288_);
v___x_2308_ = lean_box(0);
v_isShared_2309_ = v_isSharedCheck_2313_;
goto v_resetjp_2307_;
}
v_resetjp_2307_:
{
lean_object* v___x_2311_; 
if (v_isShared_2309_ == 0)
{
v___x_2311_ = v___x_2308_;
goto v_reusejp_2310_;
}
else
{
lean_object* v_reuseFailAlloc_2312_; 
v_reuseFailAlloc_2312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2312_, 0, v_a_2306_);
v___x_2311_ = v_reuseFailAlloc_2312_;
goto v_reusejp_2310_;
}
v_reusejp_2310_:
{
return v___x_2311_;
}
}
}
}
}
}
v___jp_2248_:
{
size_t v___x_2250_; size_t v___x_2251_; 
v___x_2250_ = ((size_t)1ULL);
v___x_2251_ = lean_usize_add(v_i_2241_, v___x_2250_);
v_i_2241_ = v___x_2251_;
v_b_2242_ = v_a_2249_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__0___redArg___boxed(lean_object* v___x_2315_, lean_object* v_as_2316_, lean_object* v_sz_2317_, lean_object* v_i_2318_, lean_object* v_b_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_){
_start:
{
size_t v_sz_boxed_2325_; size_t v_i_boxed_2326_; lean_object* v_res_2327_; 
v_sz_boxed_2325_ = lean_unbox_usize(v_sz_2317_);
lean_dec(v_sz_2317_);
v_i_boxed_2326_ = lean_unbox_usize(v_i_2318_);
lean_dec(v_i_2318_);
v_res_2327_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__0___redArg(v___x_2315_, v_as_2316_, v_sz_boxed_2325_, v_i_boxed_2326_, v_b_2319_, v___y_2320_, v___y_2321_, v___y_2322_, v___y_2323_);
lean_dec(v___y_2323_);
lean_dec_ref(v___y_2322_);
lean_dec(v___y_2321_);
lean_dec_ref(v___y_2320_);
lean_dec_ref(v_as_2316_);
lean_dec_ref(v___x_2315_);
return v_res_2327_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems(lean_object* v_ids_x3f_2332_, lean_object* v_a_2333_, lean_object* v_a_2334_, lean_object* v_a_2335_, lean_object* v_a_2336_, lean_object* v_a_2337_, lean_object* v_a_2338_, lean_object* v_a_2339_, lean_object* v_a_2340_){
_start:
{
if (lean_obj_tag(v_ids_x3f_2332_) == 1)
{
lean_object* v_val_2342_; lean_object* v_lctx_2343_; lean_object* v___x_2344_; size_t v_sz_2345_; size_t v___x_2346_; lean_object* v___x_2347_; 
v_val_2342_ = lean_ctor_get(v_ids_x3f_2332_, 0);
v_lctx_2343_ = lean_ctor_get(v_a_2337_, 2);
v___x_2344_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems___closed__1));
v_sz_2345_ = lean_array_size(v_val_2342_);
v___x_2346_ = ((size_t)0ULL);
v___x_2347_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__0___redArg(v_lctx_2343_, v_val_2342_, v_sz_2345_, v___x_2346_, v___x_2344_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_);
if (lean_obj_tag(v___x_2347_) == 0)
{
lean_object* v_a_2348_; lean_object* v___x_2350_; uint8_t v_isShared_2351_; uint8_t v_isSharedCheck_2364_; 
v_a_2348_ = lean_ctor_get(v___x_2347_, 0);
v_isSharedCheck_2364_ = !lean_is_exclusive(v___x_2347_);
if (v_isSharedCheck_2364_ == 0)
{
v___x_2350_ = v___x_2347_;
v_isShared_2351_ = v_isSharedCheck_2364_;
goto v_resetjp_2349_;
}
else
{
lean_inc(v_a_2348_);
lean_dec(v___x_2347_);
v___x_2350_ = lean_box(0);
v_isShared_2351_ = v_isSharedCheck_2364_;
goto v_resetjp_2349_;
}
v_resetjp_2349_:
{
lean_object* v_fst_2352_; lean_object* v_snd_2353_; lean_object* v___x_2355_; uint8_t v_isShared_2356_; uint8_t v_isSharedCheck_2363_; 
v_fst_2352_ = lean_ctor_get(v_a_2348_, 0);
v_snd_2353_ = lean_ctor_get(v_a_2348_, 1);
v_isSharedCheck_2363_ = !lean_is_exclusive(v_a_2348_);
if (v_isSharedCheck_2363_ == 0)
{
v___x_2355_ = v_a_2348_;
v_isShared_2356_ = v_isSharedCheck_2363_;
goto v_resetjp_2354_;
}
else
{
lean_inc(v_snd_2353_);
lean_inc(v_fst_2352_);
lean_dec(v_a_2348_);
v___x_2355_ = lean_box(0);
v_isShared_2356_ = v_isSharedCheck_2363_;
goto v_resetjp_2354_;
}
v_resetjp_2354_:
{
lean_object* v___x_2358_; 
if (v_isShared_2356_ == 0)
{
v___x_2358_ = v___x_2355_;
goto v_reusejp_2357_;
}
else
{
lean_object* v_reuseFailAlloc_2362_; 
v_reuseFailAlloc_2362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2362_, 0, v_fst_2352_);
lean_ctor_set(v_reuseFailAlloc_2362_, 1, v_snd_2353_);
v___x_2358_ = v_reuseFailAlloc_2362_;
goto v_reusejp_2357_;
}
v_reusejp_2357_:
{
lean_object* v___x_2360_; 
if (v_isShared_2351_ == 0)
{
lean_ctor_set(v___x_2350_, 0, v___x_2358_);
v___x_2360_ = v___x_2350_;
goto v_reusejp_2359_;
}
else
{
lean_object* v_reuseFailAlloc_2361_; 
v_reuseFailAlloc_2361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2361_, 0, v___x_2358_);
v___x_2360_ = v_reuseFailAlloc_2361_;
goto v_reusejp_2359_;
}
v_reusejp_2359_:
{
return v___x_2360_;
}
}
}
}
}
else
{
return v___x_2347_;
}
}
else
{
lean_object* v___x_2365_; lean_object* v___x_2366_; 
v___x_2365_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems___closed__1));
v___x_2366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2366_, 0, v___x_2365_);
return v___x_2366_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems___boxed(lean_object* v_ids_x3f_2367_, lean_object* v_a_2368_, lean_object* v_a_2369_, lean_object* v_a_2370_, lean_object* v_a_2371_, lean_object* v_a_2372_, lean_object* v_a_2373_, lean_object* v_a_2374_, lean_object* v_a_2375_, lean_object* v_a_2376_){
_start:
{
lean_object* v_res_2377_; 
v_res_2377_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems(v_ids_x3f_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_);
lean_dec(v_a_2375_);
lean_dec_ref(v_a_2374_);
lean_dec(v_a_2373_);
lean_dec_ref(v_a_2372_);
lean_dec(v_a_2371_);
lean_dec_ref(v_a_2370_);
lean_dec(v_a_2369_);
lean_dec_ref(v_a_2368_);
lean_dec(v_ids_x3f_2367_);
return v_res_2377_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__0(lean_object* v___x_2378_, lean_object* v_as_2379_, size_t v_sz_2380_, size_t v_i_2381_, lean_object* v_b_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_){
_start:
{
lean_object* v___x_2392_; 
v___x_2392_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__0___redArg(v___x_2378_, v_as_2379_, v_sz_2380_, v_i_2381_, v_b_2382_, v___y_2387_, v___y_2388_, v___y_2389_, v___y_2390_);
return v___x_2392_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__0___boxed(lean_object* v___x_2393_, lean_object* v_as_2394_, lean_object* v_sz_2395_, lean_object* v_i_2396_, lean_object* v_b_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_){
_start:
{
size_t v_sz_boxed_2407_; size_t v_i_boxed_2408_; lean_object* v_res_2409_; 
v_sz_boxed_2407_ = lean_unbox_usize(v_sz_2395_);
lean_dec(v_sz_2395_);
v_i_boxed_2408_ = lean_unbox_usize(v_i_2396_);
lean_dec(v_i_2396_);
v_res_2409_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__0(v___x_2393_, v_as_2394_, v_sz_boxed_2407_, v_i_boxed_2408_, v_b_2397_, v___y_2398_, v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_);
lean_dec(v___y_2405_);
lean_dec_ref(v___y_2404_);
lean_dec(v___y_2403_);
lean_dec_ref(v___y_2402_);
lean_dec(v___y_2401_);
lean_dec_ref(v___y_2400_);
lean_dec(v___y_2399_);
lean_dec_ref(v___y_2398_);
lean_dec_ref(v_as_2394_);
lean_dec_ref(v___x_2393_);
return v_res_2409_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___lam__0(lean_object* v_a_2411_, lean_object* v_x_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_){
_start:
{
lean_object* v___x_2424_; lean_object* v___x_2425_; 
v___x_2424_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___lam__0___closed__0));
v___x_2425_ = l_Lean_Meta_Sym_Simp_Theorems_rewrite(v_a_2411_, v___x_2424_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_);
return v___x_2425_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___lam__0___boxed(lean_object* v_a_2426_, lean_object* v_x_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_){
_start:
{
lean_object* v_res_2439_; 
v_res_2439_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___lam__0(v_a_2426_, v_x_2427_, v___y_2428_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_, v___y_2437_);
lean_dec(v___y_2437_);
lean_dec_ref(v___y_2436_);
lean_dec(v___y_2435_);
lean_dec_ref(v___y_2434_);
lean_dec(v___y_2433_);
lean_dec_ref(v___y_2432_);
lean_dec(v___y_2431_);
lean_dec_ref(v___y_2430_);
lean_dec(v___y_2429_);
return v_res_2439_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___lam__1(lean_object* v_post_2440_, lean_object* v___f_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_){
_start:
{
lean_object* v___x_2453_; 
lean_inc(v___y_2451_);
lean_inc_ref(v___y_2450_);
lean_inc(v___y_2449_);
lean_inc_ref(v___y_2448_);
lean_inc(v___y_2447_);
lean_inc_ref(v___y_2446_);
lean_inc(v___y_2445_);
lean_inc_ref(v___y_2444_);
lean_inc(v___y_2443_);
lean_inc_ref(v___y_2442_);
v___x_2453_ = lean_apply_11(v_post_2440_, v___y_2442_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_, lean_box(0));
if (lean_obj_tag(v___x_2453_) == 0)
{
lean_object* v_a_2454_; lean_object* v___x_2455_; 
v_a_2454_ = lean_ctor_get(v___x_2453_, 0);
lean_inc(v_a_2454_);
v___x_2455_ = lean_box(0);
if (lean_obj_tag(v_a_2454_) == 0)
{
uint8_t v_done_2456_; 
v_done_2456_ = lean_ctor_get_uint8(v_a_2454_, 0);
if (v_done_2456_ == 0)
{
uint8_t v_contextDependent_2457_; lean_object* v___x_2458_; 
lean_dec_ref(v___x_2453_);
v_contextDependent_2457_ = lean_ctor_get_uint8(v_a_2454_, 1);
lean_dec_ref(v_a_2454_);
v___x_2458_ = lean_apply_12(v___f_2441_, v___x_2455_, v___y_2442_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_, lean_box(0));
if (lean_obj_tag(v___x_2458_) == 0)
{
lean_object* v_a_2459_; uint8_t v___y_2461_; 
v_a_2459_ = lean_ctor_get(v___x_2458_, 0);
lean_inc(v_a_2459_);
if (v_contextDependent_2457_ == 0)
{
lean_dec(v_a_2459_);
return v___x_2458_;
}
else
{
if (lean_obj_tag(v_a_2459_) == 0)
{
uint8_t v_contextDependent_2471_; 
v_contextDependent_2471_ = lean_ctor_get_uint8(v_a_2459_, 1);
v___y_2461_ = v_contextDependent_2471_;
goto v___jp_2460_;
}
else
{
uint8_t v_contextDependent_2472_; 
v_contextDependent_2472_ = lean_ctor_get_uint8(v_a_2459_, sizeof(void*)*2 + 1);
v___y_2461_ = v_contextDependent_2472_;
goto v___jp_2460_;
}
}
v___jp_2460_:
{
if (v___y_2461_ == 0)
{
lean_object* v___x_2463_; uint8_t v_isShared_2464_; uint8_t v_isSharedCheck_2469_; 
v_isSharedCheck_2469_ = !lean_is_exclusive(v___x_2458_);
if (v_isSharedCheck_2469_ == 0)
{
lean_object* v_unused_2470_; 
v_unused_2470_ = lean_ctor_get(v___x_2458_, 0);
lean_dec(v_unused_2470_);
v___x_2463_ = v___x_2458_;
v_isShared_2464_ = v_isSharedCheck_2469_;
goto v_resetjp_2462_;
}
else
{
lean_dec(v___x_2458_);
v___x_2463_ = lean_box(0);
v_isShared_2464_ = v_isSharedCheck_2469_;
goto v_resetjp_2462_;
}
v_resetjp_2462_:
{
lean_object* v___x_2465_; lean_object* v___x_2467_; 
v___x_2465_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_2459_);
if (v_isShared_2464_ == 0)
{
lean_ctor_set(v___x_2463_, 0, v___x_2465_);
v___x_2467_ = v___x_2463_;
goto v_reusejp_2466_;
}
else
{
lean_object* v_reuseFailAlloc_2468_; 
v_reuseFailAlloc_2468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2468_, 0, v___x_2465_);
v___x_2467_ = v_reuseFailAlloc_2468_;
goto v_reusejp_2466_;
}
v_reusejp_2466_:
{
return v___x_2467_;
}
}
}
else
{
lean_dec(v_a_2459_);
return v___x_2458_;
}
}
}
else
{
return v___x_2458_;
}
}
else
{
lean_dec_ref(v_a_2454_);
lean_dec(v___y_2451_);
lean_dec_ref(v___y_2450_);
lean_dec(v___y_2449_);
lean_dec_ref(v___y_2448_);
lean_dec(v___y_2447_);
lean_dec_ref(v___y_2446_);
lean_dec(v___y_2445_);
lean_dec_ref(v___y_2444_);
lean_dec(v___y_2443_);
lean_dec_ref(v___y_2442_);
lean_dec_ref(v___f_2441_);
return v___x_2453_;
}
}
else
{
uint8_t v_done_2473_; 
v_done_2473_ = lean_ctor_get_uint8(v_a_2454_, sizeof(void*)*2);
if (v_done_2473_ == 0)
{
lean_object* v_e_x27_2474_; lean_object* v_proof_2475_; uint8_t v_contextDependent_2476_; lean_object* v___x_2478_; uint8_t v_isShared_2479_; uint8_t v_isSharedCheck_2526_; 
lean_dec_ref(v___x_2453_);
v_e_x27_2474_ = lean_ctor_get(v_a_2454_, 0);
v_proof_2475_ = lean_ctor_get(v_a_2454_, 1);
v_contextDependent_2476_ = lean_ctor_get_uint8(v_a_2454_, sizeof(void*)*2 + 1);
v_isSharedCheck_2526_ = !lean_is_exclusive(v_a_2454_);
if (v_isSharedCheck_2526_ == 0)
{
v___x_2478_ = v_a_2454_;
v_isShared_2479_ = v_isSharedCheck_2526_;
goto v_resetjp_2477_;
}
else
{
lean_inc(v_proof_2475_);
lean_inc(v_e_x27_2474_);
lean_dec(v_a_2454_);
v___x_2478_ = lean_box(0);
v_isShared_2479_ = v_isSharedCheck_2526_;
goto v_resetjp_2477_;
}
v_resetjp_2477_:
{
lean_object* v___x_2480_; 
lean_inc(v___y_2451_);
lean_inc_ref(v___y_2450_);
lean_inc(v___y_2449_);
lean_inc_ref(v___y_2448_);
lean_inc(v___y_2447_);
lean_inc_ref(v_e_x27_2474_);
v___x_2480_ = lean_apply_12(v___f_2441_, v___x_2455_, v_e_x27_2474_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_, lean_box(0));
if (lean_obj_tag(v___x_2480_) == 0)
{
lean_object* v_a_2481_; lean_object* v___x_2483_; uint8_t v_isShared_2484_; uint8_t v_isSharedCheck_2525_; 
v_a_2481_ = lean_ctor_get(v___x_2480_, 0);
v_isSharedCheck_2525_ = !lean_is_exclusive(v___x_2480_);
if (v_isSharedCheck_2525_ == 0)
{
v___x_2483_ = v___x_2480_;
v_isShared_2484_ = v_isSharedCheck_2525_;
goto v_resetjp_2482_;
}
else
{
lean_inc(v_a_2481_);
lean_dec(v___x_2480_);
v___x_2483_ = lean_box(0);
v_isShared_2484_ = v_isSharedCheck_2525_;
goto v_resetjp_2482_;
}
v_resetjp_2482_:
{
if (lean_obj_tag(v_a_2481_) == 0)
{
uint8_t v_done_2485_; uint8_t v_contextDependent_2486_; uint8_t v___y_2488_; 
lean_dec(v___y_2451_);
lean_dec_ref(v___y_2450_);
lean_dec(v___y_2449_);
lean_dec_ref(v___y_2448_);
lean_dec(v___y_2447_);
lean_dec_ref(v___y_2442_);
v_done_2485_ = lean_ctor_get_uint8(v_a_2481_, 0);
v_contextDependent_2486_ = lean_ctor_get_uint8(v_a_2481_, 1);
lean_dec_ref(v_a_2481_);
if (v_contextDependent_2476_ == 0)
{
v___y_2488_ = v_contextDependent_2486_;
goto v___jp_2487_;
}
else
{
v___y_2488_ = v_contextDependent_2476_;
goto v___jp_2487_;
}
v___jp_2487_:
{
lean_object* v___x_2490_; 
if (v_isShared_2479_ == 0)
{
v___x_2490_ = v___x_2478_;
goto v_reusejp_2489_;
}
else
{
lean_object* v_reuseFailAlloc_2494_; 
v_reuseFailAlloc_2494_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2494_, 0, v_e_x27_2474_);
lean_ctor_set(v_reuseFailAlloc_2494_, 1, v_proof_2475_);
v___x_2490_ = v_reuseFailAlloc_2494_;
goto v_reusejp_2489_;
}
v_reusejp_2489_:
{
lean_object* v___x_2492_; 
lean_ctor_set_uint8(v___x_2490_, sizeof(void*)*2, v_done_2485_);
lean_ctor_set_uint8(v___x_2490_, sizeof(void*)*2 + 1, v___y_2488_);
if (v_isShared_2484_ == 0)
{
lean_ctor_set(v___x_2483_, 0, v___x_2490_);
v___x_2492_ = v___x_2483_;
goto v_reusejp_2491_;
}
else
{
lean_object* v_reuseFailAlloc_2493_; 
v_reuseFailAlloc_2493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2493_, 0, v___x_2490_);
v___x_2492_ = v_reuseFailAlloc_2493_;
goto v_reusejp_2491_;
}
v_reusejp_2491_:
{
return v___x_2492_;
}
}
}
}
else
{
lean_object* v_e_x27_2495_; lean_object* v_proof_2496_; uint8_t v_done_2497_; uint8_t v_contextDependent_2498_; lean_object* v___x_2500_; uint8_t v_isShared_2501_; uint8_t v_isSharedCheck_2524_; 
lean_del_object(v___x_2483_);
lean_del_object(v___x_2478_);
v_e_x27_2495_ = lean_ctor_get(v_a_2481_, 0);
v_proof_2496_ = lean_ctor_get(v_a_2481_, 1);
v_done_2497_ = lean_ctor_get_uint8(v_a_2481_, sizeof(void*)*2);
v_contextDependent_2498_ = lean_ctor_get_uint8(v_a_2481_, sizeof(void*)*2 + 1);
v_isSharedCheck_2524_ = !lean_is_exclusive(v_a_2481_);
if (v_isSharedCheck_2524_ == 0)
{
v___x_2500_ = v_a_2481_;
v_isShared_2501_ = v_isSharedCheck_2524_;
goto v_resetjp_2499_;
}
else
{
lean_inc(v_proof_2496_);
lean_inc(v_e_x27_2495_);
lean_dec(v_a_2481_);
v___x_2500_ = lean_box(0);
v_isShared_2501_ = v_isSharedCheck_2524_;
goto v_resetjp_2499_;
}
v_resetjp_2499_:
{
lean_object* v___x_2502_; 
lean_inc_ref(v_e_x27_2495_);
v___x_2502_ = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(v___y_2442_, v_e_x27_2474_, v_proof_2475_, v_e_x27_2495_, v_proof_2496_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_);
lean_dec(v___y_2451_);
lean_dec_ref(v___y_2450_);
lean_dec(v___y_2449_);
lean_dec_ref(v___y_2448_);
lean_dec(v___y_2447_);
if (lean_obj_tag(v___x_2502_) == 0)
{
lean_object* v_a_2503_; lean_object* v___x_2505_; uint8_t v_isShared_2506_; uint8_t v_isSharedCheck_2515_; 
v_a_2503_ = lean_ctor_get(v___x_2502_, 0);
v_isSharedCheck_2515_ = !lean_is_exclusive(v___x_2502_);
if (v_isSharedCheck_2515_ == 0)
{
v___x_2505_ = v___x_2502_;
v_isShared_2506_ = v_isSharedCheck_2515_;
goto v_resetjp_2504_;
}
else
{
lean_inc(v_a_2503_);
lean_dec(v___x_2502_);
v___x_2505_ = lean_box(0);
v_isShared_2506_ = v_isSharedCheck_2515_;
goto v_resetjp_2504_;
}
v_resetjp_2504_:
{
uint8_t v___y_2508_; 
if (v_contextDependent_2476_ == 0)
{
v___y_2508_ = v_contextDependent_2498_;
goto v___jp_2507_;
}
else
{
v___y_2508_ = v_contextDependent_2476_;
goto v___jp_2507_;
}
v___jp_2507_:
{
lean_object* v___x_2510_; 
if (v_isShared_2501_ == 0)
{
lean_ctor_set(v___x_2500_, 1, v_a_2503_);
v___x_2510_ = v___x_2500_;
goto v_reusejp_2509_;
}
else
{
lean_object* v_reuseFailAlloc_2514_; 
v_reuseFailAlloc_2514_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2514_, 0, v_e_x27_2495_);
lean_ctor_set(v_reuseFailAlloc_2514_, 1, v_a_2503_);
lean_ctor_set_uint8(v_reuseFailAlloc_2514_, sizeof(void*)*2, v_done_2497_);
v___x_2510_ = v_reuseFailAlloc_2514_;
goto v_reusejp_2509_;
}
v_reusejp_2509_:
{
lean_object* v___x_2512_; 
lean_ctor_set_uint8(v___x_2510_, sizeof(void*)*2 + 1, v___y_2508_);
if (v_isShared_2506_ == 0)
{
lean_ctor_set(v___x_2505_, 0, v___x_2510_);
v___x_2512_ = v___x_2505_;
goto v_reusejp_2511_;
}
else
{
lean_object* v_reuseFailAlloc_2513_; 
v_reuseFailAlloc_2513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2513_, 0, v___x_2510_);
v___x_2512_ = v_reuseFailAlloc_2513_;
goto v_reusejp_2511_;
}
v_reusejp_2511_:
{
return v___x_2512_;
}
}
}
}
}
else
{
lean_object* v_a_2516_; lean_object* v___x_2518_; uint8_t v_isShared_2519_; uint8_t v_isSharedCheck_2523_; 
lean_del_object(v___x_2500_);
lean_dec_ref(v_e_x27_2495_);
v_a_2516_ = lean_ctor_get(v___x_2502_, 0);
v_isSharedCheck_2523_ = !lean_is_exclusive(v___x_2502_);
if (v_isSharedCheck_2523_ == 0)
{
v___x_2518_ = v___x_2502_;
v_isShared_2519_ = v_isSharedCheck_2523_;
goto v_resetjp_2517_;
}
else
{
lean_inc(v_a_2516_);
lean_dec(v___x_2502_);
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
}
}
}
else
{
lean_del_object(v___x_2478_);
lean_dec_ref(v_proof_2475_);
lean_dec_ref(v_e_x27_2474_);
lean_dec(v___y_2451_);
lean_dec_ref(v___y_2450_);
lean_dec(v___y_2449_);
lean_dec_ref(v___y_2448_);
lean_dec(v___y_2447_);
lean_dec_ref(v___y_2442_);
return v___x_2480_;
}
}
}
else
{
lean_dec_ref(v_a_2454_);
lean_dec(v___y_2451_);
lean_dec_ref(v___y_2450_);
lean_dec(v___y_2449_);
lean_dec_ref(v___y_2448_);
lean_dec(v___y_2447_);
lean_dec_ref(v___y_2446_);
lean_dec(v___y_2445_);
lean_dec_ref(v___y_2444_);
lean_dec(v___y_2443_);
lean_dec_ref(v___y_2442_);
lean_dec_ref(v___f_2441_);
return v___x_2453_;
}
}
}
else
{
lean_dec(v___y_2451_);
lean_dec_ref(v___y_2450_);
lean_dec(v___y_2449_);
lean_dec_ref(v___y_2448_);
lean_dec(v___y_2447_);
lean_dec_ref(v___y_2446_);
lean_dec(v___y_2445_);
lean_dec_ref(v___y_2444_);
lean_dec(v___y_2443_);
lean_dec_ref(v___y_2442_);
lean_dec_ref(v___f_2441_);
return v___x_2453_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___lam__1___boxed(lean_object* v_post_2527_, lean_object* v___f_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_){
_start:
{
lean_object* v_res_2540_; 
v_res_2540_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___lam__1(v_post_2527_, v___f_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_);
return v_res_2540_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems_spec__0___redArg(lean_object* v_as_2541_, size_t v_sz_2542_, size_t v_i_2543_, lean_object* v_b_2544_){
_start:
{
uint8_t v___x_2546_; 
v___x_2546_ = lean_usize_dec_lt(v_i_2543_, v_sz_2542_);
if (v___x_2546_ == 0)
{
lean_object* v___x_2547_; 
v___x_2547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2547_, 0, v_b_2544_);
return v___x_2547_;
}
else
{
lean_object* v_a_2548_; lean_object* v___x_2549_; size_t v___x_2550_; size_t v___x_2551_; 
v_a_2548_ = lean_array_uget_borrowed(v_as_2541_, v_i_2543_);
lean_inc(v_a_2548_);
v___x_2549_ = l_Lean_Meta_Sym_Simp_Theorems_insert(v_b_2544_, v_a_2548_);
v___x_2550_ = ((size_t)1ULL);
v___x_2551_ = lean_usize_add(v_i_2543_, v___x_2550_);
v_i_2543_ = v___x_2551_;
v_b_2544_ = v___x_2549_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems_spec__0___redArg___boxed(lean_object* v_as_2553_, lean_object* v_sz_2554_, lean_object* v_i_2555_, lean_object* v_b_2556_, lean_object* v___y_2557_){
_start:
{
size_t v_sz_boxed_2558_; size_t v_i_boxed_2559_; lean_object* v_res_2560_; 
v_sz_boxed_2558_ = lean_unbox_usize(v_sz_2554_);
lean_dec(v_sz_2554_);
v_i_boxed_2559_ = lean_unbox_usize(v_i_2555_);
lean_dec(v_i_2555_);
v_res_2560_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems_spec__0___redArg(v_as_2553_, v_sz_boxed_2558_, v_i_boxed_2559_, v_b_2556_);
lean_dec_ref(v_as_2553_);
return v_res_2560_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___closed__0(void){
_start:
{
lean_object* v___x_2561_; 
v___x_2561_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2561_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___closed__1(void){
_start:
{
lean_object* v___x_2562_; lean_object* v_thms_2563_; 
v___x_2562_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___closed__0, &l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___closed__0_once, _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___closed__0);
v_thms_2563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_thms_2563_, 0, v___x_2562_);
return v_thms_2563_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems(lean_object* v_post_2564_, lean_object* v_extraThms_2565_, lean_object* v_a_2566_, lean_object* v_a_2567_, lean_object* v_a_2568_, lean_object* v_a_2569_, lean_object* v_a_2570_, lean_object* v_a_2571_, lean_object* v_a_2572_, lean_object* v_a_2573_){
_start:
{
lean_object* v___x_2575_; lean_object* v___x_2576_; uint8_t v___x_2577_; 
v___x_2575_ = lean_array_get_size(v_extraThms_2565_);
v___x_2576_ = lean_unsigned_to_nat(0u);
v___x_2577_ = lean_nat_dec_eq(v___x_2575_, v___x_2576_);
if (v___x_2577_ == 0)
{
lean_object* v_thms_2578_; size_t v_sz_2579_; size_t v___x_2580_; lean_object* v___x_2581_; 
v_thms_2578_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___closed__1, &l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___closed__1);
v_sz_2579_ = lean_array_size(v_extraThms_2565_);
v___x_2580_ = ((size_t)0ULL);
v___x_2581_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems_spec__0___redArg(v_extraThms_2565_, v_sz_2579_, v___x_2580_, v_thms_2578_);
if (lean_obj_tag(v___x_2581_) == 0)
{
lean_object* v_a_2582_; lean_object* v___x_2584_; uint8_t v_isShared_2585_; uint8_t v_isSharedCheck_2591_; 
v_a_2582_ = lean_ctor_get(v___x_2581_, 0);
v_isSharedCheck_2591_ = !lean_is_exclusive(v___x_2581_);
if (v_isSharedCheck_2591_ == 0)
{
v___x_2584_ = v___x_2581_;
v_isShared_2585_ = v_isSharedCheck_2591_;
goto v_resetjp_2583_;
}
else
{
lean_inc(v_a_2582_);
lean_dec(v___x_2581_);
v___x_2584_ = lean_box(0);
v_isShared_2585_ = v_isSharedCheck_2591_;
goto v_resetjp_2583_;
}
v_resetjp_2583_:
{
lean_object* v___f_2586_; lean_object* v___f_2587_; lean_object* v___x_2589_; 
v___f_2586_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___lam__0___boxed), 13, 1);
lean_closure_set(v___f_2586_, 0, v_a_2582_);
v___f_2587_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___lam__1___boxed), 13, 2);
lean_closure_set(v___f_2587_, 0, v_post_2564_);
lean_closure_set(v___f_2587_, 1, v___f_2586_);
if (v_isShared_2585_ == 0)
{
lean_ctor_set(v___x_2584_, 0, v___f_2587_);
v___x_2589_ = v___x_2584_;
goto v_reusejp_2588_;
}
else
{
lean_object* v_reuseFailAlloc_2590_; 
v_reuseFailAlloc_2590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2590_, 0, v___f_2587_);
v___x_2589_ = v_reuseFailAlloc_2590_;
goto v_reusejp_2588_;
}
v_reusejp_2588_:
{
return v___x_2589_;
}
}
}
else
{
lean_object* v_a_2592_; lean_object* v___x_2594_; uint8_t v_isShared_2595_; uint8_t v_isSharedCheck_2599_; 
lean_dec_ref(v_post_2564_);
v_a_2592_ = lean_ctor_get(v___x_2581_, 0);
v_isSharedCheck_2599_ = !lean_is_exclusive(v___x_2581_);
if (v_isSharedCheck_2599_ == 0)
{
v___x_2594_ = v___x_2581_;
v_isShared_2595_ = v_isSharedCheck_2599_;
goto v_resetjp_2593_;
}
else
{
lean_inc(v_a_2592_);
lean_dec(v___x_2581_);
v___x_2594_ = lean_box(0);
v_isShared_2595_ = v_isSharedCheck_2599_;
goto v_resetjp_2593_;
}
v_resetjp_2593_:
{
lean_object* v___x_2597_; 
if (v_isShared_2595_ == 0)
{
v___x_2597_ = v___x_2594_;
goto v_reusejp_2596_;
}
else
{
lean_object* v_reuseFailAlloc_2598_; 
v_reuseFailAlloc_2598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2598_, 0, v_a_2592_);
v___x_2597_ = v_reuseFailAlloc_2598_;
goto v_reusejp_2596_;
}
v_reusejp_2596_:
{
return v___x_2597_;
}
}
}
}
else
{
lean_object* v___x_2600_; 
v___x_2600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2600_, 0, v_post_2564_);
return v___x_2600_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___boxed(lean_object* v_post_2601_, lean_object* v_extraThms_2602_, lean_object* v_a_2603_, lean_object* v_a_2604_, lean_object* v_a_2605_, lean_object* v_a_2606_, lean_object* v_a_2607_, lean_object* v_a_2608_, lean_object* v_a_2609_, lean_object* v_a_2610_, lean_object* v_a_2611_){
_start:
{
lean_object* v_res_2612_; 
v_res_2612_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems(v_post_2601_, v_extraThms_2602_, v_a_2603_, v_a_2604_, v_a_2605_, v_a_2606_, v_a_2607_, v_a_2608_, v_a_2609_, v_a_2610_);
lean_dec(v_a_2610_);
lean_dec_ref(v_a_2609_);
lean_dec(v_a_2608_);
lean_dec_ref(v_a_2607_);
lean_dec(v_a_2606_);
lean_dec_ref(v_a_2605_);
lean_dec(v_a_2604_);
lean_dec_ref(v_a_2603_);
lean_dec_ref(v_extraThms_2602_);
return v_res_2612_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems_spec__0(lean_object* v_as_2613_, size_t v_sz_2614_, size_t v_i_2615_, lean_object* v_b_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_){
_start:
{
lean_object* v___x_2626_; 
v___x_2626_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems_spec__0___redArg(v_as_2613_, v_sz_2614_, v_i_2615_, v_b_2616_);
return v___x_2626_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems_spec__0___boxed(lean_object* v_as_2627_, lean_object* v_sz_2628_, lean_object* v_i_2629_, lean_object* v_b_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_){
_start:
{
size_t v_sz_boxed_2640_; size_t v_i_boxed_2641_; lean_object* v_res_2642_; 
v_sz_boxed_2640_ = lean_unbox_usize(v_sz_2628_);
lean_dec(v_sz_2628_);
v_i_boxed_2641_ = lean_unbox_usize(v_i_2629_);
lean_dec(v_i_2629_);
v_res_2642_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems_spec__0(v_as_2627_, v_sz_boxed_2640_, v_i_boxed_2641_, v_b_2630_, v___y_2631_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_);
lean_dec(v___y_2638_);
lean_dec_ref(v___y_2637_);
lean_dec(v___y_2636_);
lean_dec_ref(v___y_2635_);
lean_dec(v___y_2634_);
lean_dec_ref(v___y_2633_);
lean_dec(v___y_2632_);
lean_dec_ref(v___y_2631_);
lean_dec_ref(v_as_2627_);
return v_res_2642_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkDefaultMethods___lam__1(lean_object* v___x_2643_, lean_object* v___f_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_){
_start:
{
lean_object* v___x_2656_; 
lean_inc_ref(v___y_2645_);
v___x_2656_ = l_Lean_Meta_Sym_Simp_evalGround___redArg(v___x_2643_, v___y_2645_, v___y_2649_, v___y_2650_, v___y_2651_, v___y_2652_, v___y_2653_, v___y_2654_);
if (lean_obj_tag(v___x_2656_) == 0)
{
lean_object* v_a_2657_; lean_object* v___x_2658_; 
v_a_2657_ = lean_ctor_get(v___x_2656_, 0);
lean_inc(v_a_2657_);
v___x_2658_ = lean_box(0);
if (lean_obj_tag(v_a_2657_) == 0)
{
uint8_t v_done_2659_; 
v_done_2659_ = lean_ctor_get_uint8(v_a_2657_, 0);
if (v_done_2659_ == 0)
{
uint8_t v_contextDependent_2660_; lean_object* v___x_2661_; 
lean_dec_ref(v___x_2656_);
v_contextDependent_2660_ = lean_ctor_get_uint8(v_a_2657_, 1);
lean_dec_ref(v_a_2657_);
v___x_2661_ = lean_apply_12(v___f_2644_, v___x_2658_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_, v___y_2651_, v___y_2652_, v___y_2653_, v___y_2654_, lean_box(0));
if (lean_obj_tag(v___x_2661_) == 0)
{
lean_object* v_a_2662_; uint8_t v___y_2664_; 
v_a_2662_ = lean_ctor_get(v___x_2661_, 0);
lean_inc(v_a_2662_);
if (v_contextDependent_2660_ == 0)
{
lean_dec(v_a_2662_);
return v___x_2661_;
}
else
{
if (lean_obj_tag(v_a_2662_) == 0)
{
uint8_t v_contextDependent_2674_; 
v_contextDependent_2674_ = lean_ctor_get_uint8(v_a_2662_, 1);
v___y_2664_ = v_contextDependent_2674_;
goto v___jp_2663_;
}
else
{
uint8_t v_contextDependent_2675_; 
v_contextDependent_2675_ = lean_ctor_get_uint8(v_a_2662_, sizeof(void*)*2 + 1);
v___y_2664_ = v_contextDependent_2675_;
goto v___jp_2663_;
}
}
v___jp_2663_:
{
if (v___y_2664_ == 0)
{
lean_object* v___x_2666_; uint8_t v_isShared_2667_; uint8_t v_isSharedCheck_2672_; 
v_isSharedCheck_2672_ = !lean_is_exclusive(v___x_2661_);
if (v_isSharedCheck_2672_ == 0)
{
lean_object* v_unused_2673_; 
v_unused_2673_ = lean_ctor_get(v___x_2661_, 0);
lean_dec(v_unused_2673_);
v___x_2666_ = v___x_2661_;
v_isShared_2667_ = v_isSharedCheck_2672_;
goto v_resetjp_2665_;
}
else
{
lean_dec(v___x_2661_);
v___x_2666_ = lean_box(0);
v_isShared_2667_ = v_isSharedCheck_2672_;
goto v_resetjp_2665_;
}
v_resetjp_2665_:
{
lean_object* v___x_2668_; lean_object* v___x_2670_; 
v___x_2668_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_2662_);
if (v_isShared_2667_ == 0)
{
lean_ctor_set(v___x_2666_, 0, v___x_2668_);
v___x_2670_ = v___x_2666_;
goto v_reusejp_2669_;
}
else
{
lean_object* v_reuseFailAlloc_2671_; 
v_reuseFailAlloc_2671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2671_, 0, v___x_2668_);
v___x_2670_ = v_reuseFailAlloc_2671_;
goto v_reusejp_2669_;
}
v_reusejp_2669_:
{
return v___x_2670_;
}
}
}
else
{
lean_dec(v_a_2662_);
return v___x_2661_;
}
}
}
else
{
return v___x_2661_;
}
}
else
{
lean_dec_ref(v_a_2657_);
lean_dec(v___y_2654_);
lean_dec_ref(v___y_2653_);
lean_dec(v___y_2652_);
lean_dec_ref(v___y_2651_);
lean_dec(v___y_2650_);
lean_dec_ref(v___y_2649_);
lean_dec(v___y_2648_);
lean_dec_ref(v___y_2647_);
lean_dec(v___y_2646_);
lean_dec_ref(v___y_2645_);
lean_dec_ref(v___f_2644_);
return v___x_2656_;
}
}
else
{
uint8_t v_done_2676_; 
v_done_2676_ = lean_ctor_get_uint8(v_a_2657_, sizeof(void*)*2);
if (v_done_2676_ == 0)
{
lean_object* v_e_x27_2677_; lean_object* v_proof_2678_; uint8_t v_contextDependent_2679_; lean_object* v___x_2681_; uint8_t v_isShared_2682_; uint8_t v_isSharedCheck_2729_; 
lean_dec_ref(v___x_2656_);
v_e_x27_2677_ = lean_ctor_get(v_a_2657_, 0);
v_proof_2678_ = lean_ctor_get(v_a_2657_, 1);
v_contextDependent_2679_ = lean_ctor_get_uint8(v_a_2657_, sizeof(void*)*2 + 1);
v_isSharedCheck_2729_ = !lean_is_exclusive(v_a_2657_);
if (v_isSharedCheck_2729_ == 0)
{
v___x_2681_ = v_a_2657_;
v_isShared_2682_ = v_isSharedCheck_2729_;
goto v_resetjp_2680_;
}
else
{
lean_inc(v_proof_2678_);
lean_inc(v_e_x27_2677_);
lean_dec(v_a_2657_);
v___x_2681_ = lean_box(0);
v_isShared_2682_ = v_isSharedCheck_2729_;
goto v_resetjp_2680_;
}
v_resetjp_2680_:
{
lean_object* v___x_2683_; 
lean_inc(v___y_2654_);
lean_inc_ref(v___y_2653_);
lean_inc(v___y_2652_);
lean_inc_ref(v___y_2651_);
lean_inc(v___y_2650_);
lean_inc_ref(v_e_x27_2677_);
v___x_2683_ = lean_apply_12(v___f_2644_, v___x_2658_, v_e_x27_2677_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_, v___y_2651_, v___y_2652_, v___y_2653_, v___y_2654_, lean_box(0));
if (lean_obj_tag(v___x_2683_) == 0)
{
lean_object* v_a_2684_; lean_object* v___x_2686_; uint8_t v_isShared_2687_; uint8_t v_isSharedCheck_2728_; 
v_a_2684_ = lean_ctor_get(v___x_2683_, 0);
v_isSharedCheck_2728_ = !lean_is_exclusive(v___x_2683_);
if (v_isSharedCheck_2728_ == 0)
{
v___x_2686_ = v___x_2683_;
v_isShared_2687_ = v_isSharedCheck_2728_;
goto v_resetjp_2685_;
}
else
{
lean_inc(v_a_2684_);
lean_dec(v___x_2683_);
v___x_2686_ = lean_box(0);
v_isShared_2687_ = v_isSharedCheck_2728_;
goto v_resetjp_2685_;
}
v_resetjp_2685_:
{
if (lean_obj_tag(v_a_2684_) == 0)
{
uint8_t v_done_2688_; uint8_t v_contextDependent_2689_; uint8_t v___y_2691_; 
lean_dec(v___y_2654_);
lean_dec_ref(v___y_2653_);
lean_dec(v___y_2652_);
lean_dec_ref(v___y_2651_);
lean_dec(v___y_2650_);
lean_dec_ref(v___y_2645_);
v_done_2688_ = lean_ctor_get_uint8(v_a_2684_, 0);
v_contextDependent_2689_ = lean_ctor_get_uint8(v_a_2684_, 1);
lean_dec_ref(v_a_2684_);
if (v_contextDependent_2679_ == 0)
{
v___y_2691_ = v_contextDependent_2689_;
goto v___jp_2690_;
}
else
{
v___y_2691_ = v_contextDependent_2679_;
goto v___jp_2690_;
}
v___jp_2690_:
{
lean_object* v___x_2693_; 
if (v_isShared_2682_ == 0)
{
v___x_2693_ = v___x_2681_;
goto v_reusejp_2692_;
}
else
{
lean_object* v_reuseFailAlloc_2697_; 
v_reuseFailAlloc_2697_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2697_, 0, v_e_x27_2677_);
lean_ctor_set(v_reuseFailAlloc_2697_, 1, v_proof_2678_);
v___x_2693_ = v_reuseFailAlloc_2697_;
goto v_reusejp_2692_;
}
v_reusejp_2692_:
{
lean_object* v___x_2695_; 
lean_ctor_set_uint8(v___x_2693_, sizeof(void*)*2, v_done_2688_);
lean_ctor_set_uint8(v___x_2693_, sizeof(void*)*2 + 1, v___y_2691_);
if (v_isShared_2687_ == 0)
{
lean_ctor_set(v___x_2686_, 0, v___x_2693_);
v___x_2695_ = v___x_2686_;
goto v_reusejp_2694_;
}
else
{
lean_object* v_reuseFailAlloc_2696_; 
v_reuseFailAlloc_2696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2696_, 0, v___x_2693_);
v___x_2695_ = v_reuseFailAlloc_2696_;
goto v_reusejp_2694_;
}
v_reusejp_2694_:
{
return v___x_2695_;
}
}
}
}
else
{
lean_object* v_e_x27_2698_; lean_object* v_proof_2699_; uint8_t v_done_2700_; uint8_t v_contextDependent_2701_; lean_object* v___x_2703_; uint8_t v_isShared_2704_; uint8_t v_isSharedCheck_2727_; 
lean_del_object(v___x_2686_);
lean_del_object(v___x_2681_);
v_e_x27_2698_ = lean_ctor_get(v_a_2684_, 0);
v_proof_2699_ = lean_ctor_get(v_a_2684_, 1);
v_done_2700_ = lean_ctor_get_uint8(v_a_2684_, sizeof(void*)*2);
v_contextDependent_2701_ = lean_ctor_get_uint8(v_a_2684_, sizeof(void*)*2 + 1);
v_isSharedCheck_2727_ = !lean_is_exclusive(v_a_2684_);
if (v_isSharedCheck_2727_ == 0)
{
v___x_2703_ = v_a_2684_;
v_isShared_2704_ = v_isSharedCheck_2727_;
goto v_resetjp_2702_;
}
else
{
lean_inc(v_proof_2699_);
lean_inc(v_e_x27_2698_);
lean_dec(v_a_2684_);
v___x_2703_ = lean_box(0);
v_isShared_2704_ = v_isSharedCheck_2727_;
goto v_resetjp_2702_;
}
v_resetjp_2702_:
{
lean_object* v___x_2705_; 
lean_inc_ref(v_e_x27_2698_);
v___x_2705_ = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(v___y_2645_, v_e_x27_2677_, v_proof_2678_, v_e_x27_2698_, v_proof_2699_, v___y_2650_, v___y_2651_, v___y_2652_, v___y_2653_, v___y_2654_);
lean_dec(v___y_2654_);
lean_dec_ref(v___y_2653_);
lean_dec(v___y_2652_);
lean_dec_ref(v___y_2651_);
lean_dec(v___y_2650_);
if (lean_obj_tag(v___x_2705_) == 0)
{
lean_object* v_a_2706_; lean_object* v___x_2708_; uint8_t v_isShared_2709_; uint8_t v_isSharedCheck_2718_; 
v_a_2706_ = lean_ctor_get(v___x_2705_, 0);
v_isSharedCheck_2718_ = !lean_is_exclusive(v___x_2705_);
if (v_isSharedCheck_2718_ == 0)
{
v___x_2708_ = v___x_2705_;
v_isShared_2709_ = v_isSharedCheck_2718_;
goto v_resetjp_2707_;
}
else
{
lean_inc(v_a_2706_);
lean_dec(v___x_2705_);
v___x_2708_ = lean_box(0);
v_isShared_2709_ = v_isSharedCheck_2718_;
goto v_resetjp_2707_;
}
v_resetjp_2707_:
{
uint8_t v___y_2711_; 
if (v_contextDependent_2679_ == 0)
{
v___y_2711_ = v_contextDependent_2701_;
goto v___jp_2710_;
}
else
{
v___y_2711_ = v_contextDependent_2679_;
goto v___jp_2710_;
}
v___jp_2710_:
{
lean_object* v___x_2713_; 
if (v_isShared_2704_ == 0)
{
lean_ctor_set(v___x_2703_, 1, v_a_2706_);
v___x_2713_ = v___x_2703_;
goto v_reusejp_2712_;
}
else
{
lean_object* v_reuseFailAlloc_2717_; 
v_reuseFailAlloc_2717_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2717_, 0, v_e_x27_2698_);
lean_ctor_set(v_reuseFailAlloc_2717_, 1, v_a_2706_);
lean_ctor_set_uint8(v_reuseFailAlloc_2717_, sizeof(void*)*2, v_done_2700_);
v___x_2713_ = v_reuseFailAlloc_2717_;
goto v_reusejp_2712_;
}
v_reusejp_2712_:
{
lean_object* v___x_2715_; 
lean_ctor_set_uint8(v___x_2713_, sizeof(void*)*2 + 1, v___y_2711_);
if (v_isShared_2709_ == 0)
{
lean_ctor_set(v___x_2708_, 0, v___x_2713_);
v___x_2715_ = v___x_2708_;
goto v_reusejp_2714_;
}
else
{
lean_object* v_reuseFailAlloc_2716_; 
v_reuseFailAlloc_2716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2716_, 0, v___x_2713_);
v___x_2715_ = v_reuseFailAlloc_2716_;
goto v_reusejp_2714_;
}
v_reusejp_2714_:
{
return v___x_2715_;
}
}
}
}
}
else
{
lean_object* v_a_2719_; lean_object* v___x_2721_; uint8_t v_isShared_2722_; uint8_t v_isSharedCheck_2726_; 
lean_del_object(v___x_2703_);
lean_dec_ref(v_e_x27_2698_);
v_a_2719_ = lean_ctor_get(v___x_2705_, 0);
v_isSharedCheck_2726_ = !lean_is_exclusive(v___x_2705_);
if (v_isSharedCheck_2726_ == 0)
{
v___x_2721_ = v___x_2705_;
v_isShared_2722_ = v_isSharedCheck_2726_;
goto v_resetjp_2720_;
}
else
{
lean_inc(v_a_2719_);
lean_dec(v___x_2705_);
v___x_2721_ = lean_box(0);
v_isShared_2722_ = v_isSharedCheck_2726_;
goto v_resetjp_2720_;
}
v_resetjp_2720_:
{
lean_object* v___x_2724_; 
if (v_isShared_2722_ == 0)
{
v___x_2724_ = v___x_2721_;
goto v_reusejp_2723_;
}
else
{
lean_object* v_reuseFailAlloc_2725_; 
v_reuseFailAlloc_2725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2725_, 0, v_a_2719_);
v___x_2724_ = v_reuseFailAlloc_2725_;
goto v_reusejp_2723_;
}
v_reusejp_2723_:
{
return v___x_2724_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_2681_);
lean_dec_ref(v_proof_2678_);
lean_dec_ref(v_e_x27_2677_);
lean_dec(v___y_2654_);
lean_dec_ref(v___y_2653_);
lean_dec(v___y_2652_);
lean_dec_ref(v___y_2651_);
lean_dec(v___y_2650_);
lean_dec_ref(v___y_2645_);
return v___x_2683_;
}
}
}
else
{
lean_dec_ref(v_a_2657_);
lean_dec(v___y_2654_);
lean_dec_ref(v___y_2653_);
lean_dec(v___y_2652_);
lean_dec_ref(v___y_2651_);
lean_dec(v___y_2650_);
lean_dec_ref(v___y_2649_);
lean_dec(v___y_2648_);
lean_dec_ref(v___y_2647_);
lean_dec(v___y_2646_);
lean_dec_ref(v___y_2645_);
lean_dec_ref(v___f_2644_);
return v___x_2656_;
}
}
}
else
{
lean_dec(v___y_2654_);
lean_dec_ref(v___y_2653_);
lean_dec(v___y_2652_);
lean_dec_ref(v___y_2651_);
lean_dec(v___y_2650_);
lean_dec_ref(v___y_2649_);
lean_dec(v___y_2648_);
lean_dec_ref(v___y_2647_);
lean_dec(v___y_2646_);
lean_dec_ref(v___y_2645_);
lean_dec_ref(v___f_2644_);
return v___x_2656_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkDefaultMethods___lam__1___boxed(lean_object* v___x_2730_, lean_object* v___f_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_){
_start:
{
lean_object* v_res_2743_; 
v_res_2743_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkDefaultMethods___lam__1(v___x_2730_, v___f_2731_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_, v___y_2740_, v___y_2741_);
lean_dec(v___x_2730_);
return v_res_2743_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkDefaultMethods___lam__0(lean_object* v_x_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_){
_start:
{
lean_object* v___x_2757_; lean_object* v___x_2758_; 
v___x_2757_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkDefaultMethods___lam__0___closed__0));
v___x_2758_ = l_Lean_Meta_Sym_Simp_simpArrowTelescope(v___x_2757_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_, v___y_2753_, v___y_2754_, v___y_2755_);
return v___x_2758_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkDefaultMethods___lam__0___boxed(lean_object* v_x_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_){
_start:
{
lean_object* v_res_2771_; 
v_res_2771_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkDefaultMethods___lam__0(v_x_2759_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_, v___y_2765_, v___y_2766_, v___y_2767_, v___y_2768_, v___y_2769_);
lean_dec(v___y_2769_);
lean_dec_ref(v___y_2768_);
lean_dec(v___y_2767_);
lean_dec_ref(v___y_2766_);
lean_dec(v___y_2765_);
lean_dec_ref(v___y_2764_);
lean_dec(v___y_2763_);
lean_dec_ref(v___y_2762_);
lean_dec(v___y_2761_);
return v_res_2771_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkDefaultMethods___lam__2(lean_object* v___f_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_){
_start:
{
lean_object* v___x_2784_; 
lean_inc_ref(v___y_2773_);
v___x_2784_ = l_Lean_Meta_Sym_Simp_simpControl(v___y_2773_, v___y_2774_, v___y_2775_, v___y_2776_, v___y_2777_, v___y_2778_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_);
if (lean_obj_tag(v___x_2784_) == 0)
{
lean_object* v_a_2785_; lean_object* v___x_2786_; 
v_a_2785_ = lean_ctor_get(v___x_2784_, 0);
lean_inc(v_a_2785_);
v___x_2786_ = lean_box(0);
if (lean_obj_tag(v_a_2785_) == 0)
{
uint8_t v_done_2787_; 
v_done_2787_ = lean_ctor_get_uint8(v_a_2785_, 0);
if (v_done_2787_ == 0)
{
uint8_t v_contextDependent_2788_; lean_object* v___x_2789_; 
lean_dec_ref(v___x_2784_);
v_contextDependent_2788_ = lean_ctor_get_uint8(v_a_2785_, 1);
lean_dec_ref(v_a_2785_);
v___x_2789_ = lean_apply_12(v___f_2772_, v___x_2786_, v___y_2773_, v___y_2774_, v___y_2775_, v___y_2776_, v___y_2777_, v___y_2778_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_, lean_box(0));
if (lean_obj_tag(v___x_2789_) == 0)
{
lean_object* v_a_2790_; uint8_t v___y_2792_; 
v_a_2790_ = lean_ctor_get(v___x_2789_, 0);
lean_inc(v_a_2790_);
if (v_contextDependent_2788_ == 0)
{
lean_dec(v_a_2790_);
return v___x_2789_;
}
else
{
if (lean_obj_tag(v_a_2790_) == 0)
{
uint8_t v_contextDependent_2802_; 
v_contextDependent_2802_ = lean_ctor_get_uint8(v_a_2790_, 1);
v___y_2792_ = v_contextDependent_2802_;
goto v___jp_2791_;
}
else
{
uint8_t v_contextDependent_2803_; 
v_contextDependent_2803_ = lean_ctor_get_uint8(v_a_2790_, sizeof(void*)*2 + 1);
v___y_2792_ = v_contextDependent_2803_;
goto v___jp_2791_;
}
}
v___jp_2791_:
{
if (v___y_2792_ == 0)
{
lean_object* v___x_2794_; uint8_t v_isShared_2795_; uint8_t v_isSharedCheck_2800_; 
v_isSharedCheck_2800_ = !lean_is_exclusive(v___x_2789_);
if (v_isSharedCheck_2800_ == 0)
{
lean_object* v_unused_2801_; 
v_unused_2801_ = lean_ctor_get(v___x_2789_, 0);
lean_dec(v_unused_2801_);
v___x_2794_ = v___x_2789_;
v_isShared_2795_ = v_isSharedCheck_2800_;
goto v_resetjp_2793_;
}
else
{
lean_dec(v___x_2789_);
v___x_2794_ = lean_box(0);
v_isShared_2795_ = v_isSharedCheck_2800_;
goto v_resetjp_2793_;
}
v_resetjp_2793_:
{
lean_object* v___x_2796_; lean_object* v___x_2798_; 
v___x_2796_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_2790_);
if (v_isShared_2795_ == 0)
{
lean_ctor_set(v___x_2794_, 0, v___x_2796_);
v___x_2798_ = v___x_2794_;
goto v_reusejp_2797_;
}
else
{
lean_object* v_reuseFailAlloc_2799_; 
v_reuseFailAlloc_2799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2799_, 0, v___x_2796_);
v___x_2798_ = v_reuseFailAlloc_2799_;
goto v_reusejp_2797_;
}
v_reusejp_2797_:
{
return v___x_2798_;
}
}
}
else
{
lean_dec(v_a_2790_);
return v___x_2789_;
}
}
}
else
{
return v___x_2789_;
}
}
else
{
lean_dec_ref(v_a_2785_);
lean_dec(v___y_2782_);
lean_dec_ref(v___y_2781_);
lean_dec(v___y_2780_);
lean_dec_ref(v___y_2779_);
lean_dec(v___y_2778_);
lean_dec_ref(v___y_2777_);
lean_dec(v___y_2776_);
lean_dec_ref(v___y_2775_);
lean_dec(v___y_2774_);
lean_dec_ref(v___y_2773_);
lean_dec_ref(v___f_2772_);
return v___x_2784_;
}
}
else
{
uint8_t v_done_2804_; 
v_done_2804_ = lean_ctor_get_uint8(v_a_2785_, sizeof(void*)*2);
if (v_done_2804_ == 0)
{
lean_object* v_e_x27_2805_; lean_object* v_proof_2806_; uint8_t v_contextDependent_2807_; lean_object* v___x_2809_; uint8_t v_isShared_2810_; uint8_t v_isSharedCheck_2857_; 
lean_dec_ref(v___x_2784_);
v_e_x27_2805_ = lean_ctor_get(v_a_2785_, 0);
v_proof_2806_ = lean_ctor_get(v_a_2785_, 1);
v_contextDependent_2807_ = lean_ctor_get_uint8(v_a_2785_, sizeof(void*)*2 + 1);
v_isSharedCheck_2857_ = !lean_is_exclusive(v_a_2785_);
if (v_isSharedCheck_2857_ == 0)
{
v___x_2809_ = v_a_2785_;
v_isShared_2810_ = v_isSharedCheck_2857_;
goto v_resetjp_2808_;
}
else
{
lean_inc(v_proof_2806_);
lean_inc(v_e_x27_2805_);
lean_dec(v_a_2785_);
v___x_2809_ = lean_box(0);
v_isShared_2810_ = v_isSharedCheck_2857_;
goto v_resetjp_2808_;
}
v_resetjp_2808_:
{
lean_object* v___x_2811_; 
lean_inc(v___y_2782_);
lean_inc_ref(v___y_2781_);
lean_inc(v___y_2780_);
lean_inc_ref(v___y_2779_);
lean_inc(v___y_2778_);
lean_inc_ref(v_e_x27_2805_);
v___x_2811_ = lean_apply_12(v___f_2772_, v___x_2786_, v_e_x27_2805_, v___y_2774_, v___y_2775_, v___y_2776_, v___y_2777_, v___y_2778_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_, lean_box(0));
if (lean_obj_tag(v___x_2811_) == 0)
{
lean_object* v_a_2812_; lean_object* v___x_2814_; uint8_t v_isShared_2815_; uint8_t v_isSharedCheck_2856_; 
v_a_2812_ = lean_ctor_get(v___x_2811_, 0);
v_isSharedCheck_2856_ = !lean_is_exclusive(v___x_2811_);
if (v_isSharedCheck_2856_ == 0)
{
v___x_2814_ = v___x_2811_;
v_isShared_2815_ = v_isSharedCheck_2856_;
goto v_resetjp_2813_;
}
else
{
lean_inc(v_a_2812_);
lean_dec(v___x_2811_);
v___x_2814_ = lean_box(0);
v_isShared_2815_ = v_isSharedCheck_2856_;
goto v_resetjp_2813_;
}
v_resetjp_2813_:
{
if (lean_obj_tag(v_a_2812_) == 0)
{
uint8_t v_done_2816_; uint8_t v_contextDependent_2817_; uint8_t v___y_2819_; 
lean_dec(v___y_2782_);
lean_dec_ref(v___y_2781_);
lean_dec(v___y_2780_);
lean_dec_ref(v___y_2779_);
lean_dec(v___y_2778_);
lean_dec_ref(v___y_2773_);
v_done_2816_ = lean_ctor_get_uint8(v_a_2812_, 0);
v_contextDependent_2817_ = lean_ctor_get_uint8(v_a_2812_, 1);
lean_dec_ref(v_a_2812_);
if (v_contextDependent_2807_ == 0)
{
v___y_2819_ = v_contextDependent_2817_;
goto v___jp_2818_;
}
else
{
v___y_2819_ = v_contextDependent_2807_;
goto v___jp_2818_;
}
v___jp_2818_:
{
lean_object* v___x_2821_; 
if (v_isShared_2810_ == 0)
{
v___x_2821_ = v___x_2809_;
goto v_reusejp_2820_;
}
else
{
lean_object* v_reuseFailAlloc_2825_; 
v_reuseFailAlloc_2825_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2825_, 0, v_e_x27_2805_);
lean_ctor_set(v_reuseFailAlloc_2825_, 1, v_proof_2806_);
v___x_2821_ = v_reuseFailAlloc_2825_;
goto v_reusejp_2820_;
}
v_reusejp_2820_:
{
lean_object* v___x_2823_; 
lean_ctor_set_uint8(v___x_2821_, sizeof(void*)*2, v_done_2816_);
lean_ctor_set_uint8(v___x_2821_, sizeof(void*)*2 + 1, v___y_2819_);
if (v_isShared_2815_ == 0)
{
lean_ctor_set(v___x_2814_, 0, v___x_2821_);
v___x_2823_ = v___x_2814_;
goto v_reusejp_2822_;
}
else
{
lean_object* v_reuseFailAlloc_2824_; 
v_reuseFailAlloc_2824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2824_, 0, v___x_2821_);
v___x_2823_ = v_reuseFailAlloc_2824_;
goto v_reusejp_2822_;
}
v_reusejp_2822_:
{
return v___x_2823_;
}
}
}
}
else
{
lean_object* v_e_x27_2826_; lean_object* v_proof_2827_; uint8_t v_done_2828_; uint8_t v_contextDependent_2829_; lean_object* v___x_2831_; uint8_t v_isShared_2832_; uint8_t v_isSharedCheck_2855_; 
lean_del_object(v___x_2814_);
lean_del_object(v___x_2809_);
v_e_x27_2826_ = lean_ctor_get(v_a_2812_, 0);
v_proof_2827_ = lean_ctor_get(v_a_2812_, 1);
v_done_2828_ = lean_ctor_get_uint8(v_a_2812_, sizeof(void*)*2);
v_contextDependent_2829_ = lean_ctor_get_uint8(v_a_2812_, sizeof(void*)*2 + 1);
v_isSharedCheck_2855_ = !lean_is_exclusive(v_a_2812_);
if (v_isSharedCheck_2855_ == 0)
{
v___x_2831_ = v_a_2812_;
v_isShared_2832_ = v_isSharedCheck_2855_;
goto v_resetjp_2830_;
}
else
{
lean_inc(v_proof_2827_);
lean_inc(v_e_x27_2826_);
lean_dec(v_a_2812_);
v___x_2831_ = lean_box(0);
v_isShared_2832_ = v_isSharedCheck_2855_;
goto v_resetjp_2830_;
}
v_resetjp_2830_:
{
lean_object* v___x_2833_; 
lean_inc_ref(v_e_x27_2826_);
v___x_2833_ = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(v___y_2773_, v_e_x27_2805_, v_proof_2806_, v_e_x27_2826_, v_proof_2827_, v___y_2778_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_);
lean_dec(v___y_2782_);
lean_dec_ref(v___y_2781_);
lean_dec(v___y_2780_);
lean_dec_ref(v___y_2779_);
lean_dec(v___y_2778_);
if (lean_obj_tag(v___x_2833_) == 0)
{
lean_object* v_a_2834_; lean_object* v___x_2836_; uint8_t v_isShared_2837_; uint8_t v_isSharedCheck_2846_; 
v_a_2834_ = lean_ctor_get(v___x_2833_, 0);
v_isSharedCheck_2846_ = !lean_is_exclusive(v___x_2833_);
if (v_isSharedCheck_2846_ == 0)
{
v___x_2836_ = v___x_2833_;
v_isShared_2837_ = v_isSharedCheck_2846_;
goto v_resetjp_2835_;
}
else
{
lean_inc(v_a_2834_);
lean_dec(v___x_2833_);
v___x_2836_ = lean_box(0);
v_isShared_2837_ = v_isSharedCheck_2846_;
goto v_resetjp_2835_;
}
v_resetjp_2835_:
{
uint8_t v___y_2839_; 
if (v_contextDependent_2807_ == 0)
{
v___y_2839_ = v_contextDependent_2829_;
goto v___jp_2838_;
}
else
{
v___y_2839_ = v_contextDependent_2807_;
goto v___jp_2838_;
}
v___jp_2838_:
{
lean_object* v___x_2841_; 
if (v_isShared_2832_ == 0)
{
lean_ctor_set(v___x_2831_, 1, v_a_2834_);
v___x_2841_ = v___x_2831_;
goto v_reusejp_2840_;
}
else
{
lean_object* v_reuseFailAlloc_2845_; 
v_reuseFailAlloc_2845_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2845_, 0, v_e_x27_2826_);
lean_ctor_set(v_reuseFailAlloc_2845_, 1, v_a_2834_);
lean_ctor_set_uint8(v_reuseFailAlloc_2845_, sizeof(void*)*2, v_done_2828_);
v___x_2841_ = v_reuseFailAlloc_2845_;
goto v_reusejp_2840_;
}
v_reusejp_2840_:
{
lean_object* v___x_2843_; 
lean_ctor_set_uint8(v___x_2841_, sizeof(void*)*2 + 1, v___y_2839_);
if (v_isShared_2837_ == 0)
{
lean_ctor_set(v___x_2836_, 0, v___x_2841_);
v___x_2843_ = v___x_2836_;
goto v_reusejp_2842_;
}
else
{
lean_object* v_reuseFailAlloc_2844_; 
v_reuseFailAlloc_2844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2844_, 0, v___x_2841_);
v___x_2843_ = v_reuseFailAlloc_2844_;
goto v_reusejp_2842_;
}
v_reusejp_2842_:
{
return v___x_2843_;
}
}
}
}
}
else
{
lean_object* v_a_2847_; lean_object* v___x_2849_; uint8_t v_isShared_2850_; uint8_t v_isSharedCheck_2854_; 
lean_del_object(v___x_2831_);
lean_dec_ref(v_e_x27_2826_);
v_a_2847_ = lean_ctor_get(v___x_2833_, 0);
v_isSharedCheck_2854_ = !lean_is_exclusive(v___x_2833_);
if (v_isSharedCheck_2854_ == 0)
{
v___x_2849_ = v___x_2833_;
v_isShared_2850_ = v_isSharedCheck_2854_;
goto v_resetjp_2848_;
}
else
{
lean_inc(v_a_2847_);
lean_dec(v___x_2833_);
v___x_2849_ = lean_box(0);
v_isShared_2850_ = v_isSharedCheck_2854_;
goto v_resetjp_2848_;
}
v_resetjp_2848_:
{
lean_object* v___x_2852_; 
if (v_isShared_2850_ == 0)
{
v___x_2852_ = v___x_2849_;
goto v_reusejp_2851_;
}
else
{
lean_object* v_reuseFailAlloc_2853_; 
v_reuseFailAlloc_2853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2853_, 0, v_a_2847_);
v___x_2852_ = v_reuseFailAlloc_2853_;
goto v_reusejp_2851_;
}
v_reusejp_2851_:
{
return v___x_2852_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_2809_);
lean_dec_ref(v_proof_2806_);
lean_dec_ref(v_e_x27_2805_);
lean_dec(v___y_2782_);
lean_dec_ref(v___y_2781_);
lean_dec(v___y_2780_);
lean_dec_ref(v___y_2779_);
lean_dec(v___y_2778_);
lean_dec_ref(v___y_2773_);
return v___x_2811_;
}
}
}
else
{
lean_dec_ref(v_a_2785_);
lean_dec(v___y_2782_);
lean_dec_ref(v___y_2781_);
lean_dec(v___y_2780_);
lean_dec_ref(v___y_2779_);
lean_dec(v___y_2778_);
lean_dec_ref(v___y_2777_);
lean_dec(v___y_2776_);
lean_dec_ref(v___y_2775_);
lean_dec(v___y_2774_);
lean_dec_ref(v___y_2773_);
lean_dec_ref(v___f_2772_);
return v___x_2784_;
}
}
}
else
{
lean_dec(v___y_2782_);
lean_dec_ref(v___y_2781_);
lean_dec(v___y_2780_);
lean_dec_ref(v___y_2779_);
lean_dec(v___y_2778_);
lean_dec_ref(v___y_2777_);
lean_dec(v___y_2776_);
lean_dec_ref(v___y_2775_);
lean_dec(v___y_2774_);
lean_dec_ref(v___y_2773_);
lean_dec_ref(v___f_2772_);
return v___x_2784_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkDefaultMethods___lam__2___boxed(lean_object* v___f_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_){
_start:
{
lean_object* v_res_2870_; 
v_res_2870_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkDefaultMethods___lam__2(v___f_2858_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_, v___y_2866_, v___y_2867_, v___y_2868_);
return v_res_2870_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkDefaultMethods(lean_object* v_extraThms_2874_, lean_object* v_a_2875_, lean_object* v_a_2876_, lean_object* v_a_2877_, lean_object* v_a_2878_, lean_object* v_a_2879_, lean_object* v_a_2880_, lean_object* v_a_2881_, lean_object* v_a_2882_){
_start:
{
lean_object* v___x_2884_; 
v___x_2884_ = l_Lean_Meta_Sym_Simp_getSymSimpTheorems___redArg(v_a_2882_);
if (lean_obj_tag(v___x_2884_) == 0)
{
lean_object* v_a_2885_; lean_object* v___f_2886_; lean_object* v___x_2887_; lean_object* v___f_2888_; lean_object* v___x_2889_; 
v_a_2885_ = lean_ctor_get(v___x_2884_, 0);
lean_inc(v_a_2885_);
lean_dec_ref(v___x_2884_);
v___f_2886_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___lam__0___boxed), 13, 1);
lean_closure_set(v___f_2886_, 0, v_a_2885_);
v___x_2887_ = lean_unsigned_to_nat(255u);
v___f_2888_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkDefaultMethods___lam__1___boxed), 13, 2);
lean_closure_set(v___f_2888_, 0, v___x_2887_);
lean_closure_set(v___f_2888_, 1, v___f_2886_);
v___x_2889_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems(v___f_2888_, v_extraThms_2874_, v_a_2875_, v_a_2876_, v_a_2877_, v_a_2878_, v_a_2879_, v_a_2880_, v_a_2881_, v_a_2882_);
if (lean_obj_tag(v___x_2889_) == 0)
{
lean_object* v_a_2890_; lean_object* v___x_2892_; uint8_t v_isShared_2893_; uint8_t v_isSharedCheck_2899_; 
v_a_2890_ = lean_ctor_get(v___x_2889_, 0);
v_isSharedCheck_2899_ = !lean_is_exclusive(v___x_2889_);
if (v_isSharedCheck_2899_ == 0)
{
v___x_2892_ = v___x_2889_;
v_isShared_2893_ = v_isSharedCheck_2899_;
goto v_resetjp_2891_;
}
else
{
lean_inc(v_a_2890_);
lean_dec(v___x_2889_);
v___x_2892_ = lean_box(0);
v_isShared_2893_ = v_isSharedCheck_2899_;
goto v_resetjp_2891_;
}
v_resetjp_2891_:
{
lean_object* v___f_2894_; lean_object* v___x_2895_; lean_object* v___x_2897_; 
v___f_2894_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkDefaultMethods___closed__1));
v___x_2895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2895_, 0, v___f_2894_);
lean_ctor_set(v___x_2895_, 1, v_a_2890_);
if (v_isShared_2893_ == 0)
{
lean_ctor_set(v___x_2892_, 0, v___x_2895_);
v___x_2897_ = v___x_2892_;
goto v_reusejp_2896_;
}
else
{
lean_object* v_reuseFailAlloc_2898_; 
v_reuseFailAlloc_2898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2898_, 0, v___x_2895_);
v___x_2897_ = v_reuseFailAlloc_2898_;
goto v_reusejp_2896_;
}
v_reusejp_2896_:
{
return v___x_2897_;
}
}
}
else
{
lean_object* v_a_2900_; lean_object* v___x_2902_; uint8_t v_isShared_2903_; uint8_t v_isSharedCheck_2907_; 
v_a_2900_ = lean_ctor_get(v___x_2889_, 0);
v_isSharedCheck_2907_ = !lean_is_exclusive(v___x_2889_);
if (v_isSharedCheck_2907_ == 0)
{
v___x_2902_ = v___x_2889_;
v_isShared_2903_ = v_isSharedCheck_2907_;
goto v_resetjp_2901_;
}
else
{
lean_inc(v_a_2900_);
lean_dec(v___x_2889_);
v___x_2902_ = lean_box(0);
v_isShared_2903_ = v_isSharedCheck_2907_;
goto v_resetjp_2901_;
}
v_resetjp_2901_:
{
lean_object* v___x_2905_; 
if (v_isShared_2903_ == 0)
{
v___x_2905_ = v___x_2902_;
goto v_reusejp_2904_;
}
else
{
lean_object* v_reuseFailAlloc_2906_; 
v_reuseFailAlloc_2906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2906_, 0, v_a_2900_);
v___x_2905_ = v_reuseFailAlloc_2906_;
goto v_reusejp_2904_;
}
v_reusejp_2904_:
{
return v___x_2905_;
}
}
}
}
else
{
lean_object* v_a_2908_; lean_object* v___x_2910_; uint8_t v_isShared_2911_; uint8_t v_isSharedCheck_2915_; 
v_a_2908_ = lean_ctor_get(v___x_2884_, 0);
v_isSharedCheck_2915_ = !lean_is_exclusive(v___x_2884_);
if (v_isSharedCheck_2915_ == 0)
{
v___x_2910_ = v___x_2884_;
v_isShared_2911_ = v_isSharedCheck_2915_;
goto v_resetjp_2909_;
}
else
{
lean_inc(v_a_2908_);
lean_dec(v___x_2884_);
v___x_2910_ = lean_box(0);
v_isShared_2911_ = v_isSharedCheck_2915_;
goto v_resetjp_2909_;
}
v_resetjp_2909_:
{
lean_object* v___x_2913_; 
if (v_isShared_2911_ == 0)
{
v___x_2913_ = v___x_2910_;
goto v_reusejp_2912_;
}
else
{
lean_object* v_reuseFailAlloc_2914_; 
v_reuseFailAlloc_2914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2914_, 0, v_a_2908_);
v___x_2913_ = v_reuseFailAlloc_2914_;
goto v_reusejp_2912_;
}
v_reusejp_2912_:
{
return v___x_2913_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkDefaultMethods___boxed(lean_object* v_extraThms_2916_, lean_object* v_a_2917_, lean_object* v_a_2918_, lean_object* v_a_2919_, lean_object* v_a_2920_, lean_object* v_a_2921_, lean_object* v_a_2922_, lean_object* v_a_2923_, lean_object* v_a_2924_, lean_object* v_a_2925_){
_start:
{
lean_object* v_res_2926_; 
v_res_2926_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkDefaultMethods(v_extraThms_2916_, v_a_2917_, v_a_2918_, v_a_2919_, v_a_2920_, v_a_2921_, v_a_2922_, v_a_2923_, v_a_2924_);
lean_dec(v_a_2924_);
lean_dec_ref(v_a_2923_);
lean_dec(v_a_2922_);
lean_dec_ref(v_a_2921_);
lean_dec(v_a_2920_);
lean_dec_ref(v_a_2919_);
lean_dec(v_a_2918_);
lean_dec_ref(v_a_2917_);
lean_dec_ref(v_extraThms_2916_);
return v_res_2926_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabVariant___closed__1(void){
_start:
{
lean_object* v___x_2928_; lean_object* v___x_2929_; 
v___x_2928_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabVariant___closed__0));
v___x_2929_ = l_Lean_stringToMessageData(v___x_2928_);
return v___x_2929_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabVariant___closed__3(void){
_start:
{
lean_object* v___x_2931_; lean_object* v___x_2932_; 
v___x_2931_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabVariant___closed__2));
v___x_2932_ = l_Lean_stringToMessageData(v___x_2931_);
return v___x_2932_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabVariant(lean_object* v_variantName_2936_, lean_object* v_extraThms_2937_, lean_object* v_a_2938_, lean_object* v_a_2939_, lean_object* v_a_2940_, lean_object* v_a_2941_, lean_object* v_a_2942_, lean_object* v_a_2943_, lean_object* v_a_2944_, lean_object* v_a_2945_){
_start:
{
uint8_t v___x_2947_; 
v___x_2947_ = l_Lean_Name_isAnonymous(v_variantName_2936_);
if (v___x_2947_ == 0)
{
lean_object* v___x_2948_; lean_object* v_env_2949_; lean_object* v___x_2950_; 
v___x_2948_ = lean_st_ref_get(v_a_2945_);
v_env_2949_ = lean_ctor_get(v___x_2948_, 0);
lean_inc_ref(v_env_2949_);
lean_dec(v___x_2948_);
v___x_2950_ = l_Lean_Meta_Sym_Simp_getSymSimpVariant_x3f(v_env_2949_, v_variantName_2936_);
if (lean_obj_tag(v___x_2950_) == 1)
{
lean_object* v_val_2951_; lean_object* v_pre_x3f_2952_; lean_object* v_post_x3f_2953_; lean_object* v_config_2954_; lean_object* v___x_2955_; 
lean_dec(v_variantName_2936_);
v_val_2951_ = lean_ctor_get(v___x_2950_, 0);
lean_inc(v_val_2951_);
lean_dec_ref(v___x_2950_);
v_pre_x3f_2952_ = lean_ctor_get(v_val_2951_, 0);
lean_inc(v_pre_x3f_2952_);
v_post_x3f_2953_ = lean_ctor_get(v_val_2951_, 1);
lean_inc(v_post_x3f_2953_);
v_config_2954_ = lean_ctor_get(v_val_2951_, 2);
lean_inc_ref(v_config_2954_);
lean_dec(v_val_2951_);
v___x_2955_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabOptSimproc(v_pre_x3f_2952_, v_a_2938_, v_a_2939_, v_a_2940_, v_a_2941_, v_a_2942_, v_a_2943_, v_a_2944_, v_a_2945_);
if (lean_obj_tag(v___x_2955_) == 0)
{
lean_object* v_a_2956_; lean_object* v___x_2957_; 
v_a_2956_ = lean_ctor_get(v___x_2955_, 0);
lean_inc(v_a_2956_);
lean_dec_ref(v___x_2955_);
v___x_2957_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabOptSimproc(v_post_x3f_2953_, v_a_2938_, v_a_2939_, v_a_2940_, v_a_2941_, v_a_2942_, v_a_2943_, v_a_2944_, v_a_2945_);
if (lean_obj_tag(v___x_2957_) == 0)
{
lean_object* v_a_2958_; lean_object* v___x_2959_; 
v_a_2958_ = lean_ctor_get(v___x_2957_, 0);
lean_inc(v_a_2958_);
lean_dec_ref(v___x_2957_);
v___x_2959_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems(v_a_2958_, v_extraThms_2937_, v_a_2938_, v_a_2939_, v_a_2940_, v_a_2941_, v_a_2942_, v_a_2943_, v_a_2944_, v_a_2945_);
if (lean_obj_tag(v___x_2959_) == 0)
{
lean_object* v_a_2960_; lean_object* v___x_2962_; uint8_t v_isShared_2963_; uint8_t v_isSharedCheck_2969_; 
v_a_2960_ = lean_ctor_get(v___x_2959_, 0);
v_isSharedCheck_2969_ = !lean_is_exclusive(v___x_2959_);
if (v_isSharedCheck_2969_ == 0)
{
v___x_2962_ = v___x_2959_;
v_isShared_2963_ = v_isSharedCheck_2969_;
goto v_resetjp_2961_;
}
else
{
lean_inc(v_a_2960_);
lean_dec(v___x_2959_);
v___x_2962_ = lean_box(0);
v_isShared_2963_ = v_isSharedCheck_2969_;
goto v_resetjp_2961_;
}
v_resetjp_2961_:
{
lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2967_; 
v___x_2964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2964_, 0, v_a_2956_);
lean_ctor_set(v___x_2964_, 1, v_a_2960_);
v___x_2965_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2965_, 0, v___x_2964_);
lean_ctor_set(v___x_2965_, 1, v_config_2954_);
if (v_isShared_2963_ == 0)
{
lean_ctor_set(v___x_2962_, 0, v___x_2965_);
v___x_2967_ = v___x_2962_;
goto v_reusejp_2966_;
}
else
{
lean_object* v_reuseFailAlloc_2968_; 
v_reuseFailAlloc_2968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2968_, 0, v___x_2965_);
v___x_2967_ = v_reuseFailAlloc_2968_;
goto v_reusejp_2966_;
}
v_reusejp_2966_:
{
return v___x_2967_;
}
}
}
else
{
lean_object* v_a_2970_; lean_object* v___x_2972_; uint8_t v_isShared_2973_; uint8_t v_isSharedCheck_2977_; 
lean_dec(v_a_2956_);
lean_dec_ref(v_config_2954_);
v_a_2970_ = lean_ctor_get(v___x_2959_, 0);
v_isSharedCheck_2977_ = !lean_is_exclusive(v___x_2959_);
if (v_isSharedCheck_2977_ == 0)
{
v___x_2972_ = v___x_2959_;
v_isShared_2973_ = v_isSharedCheck_2977_;
goto v_resetjp_2971_;
}
else
{
lean_inc(v_a_2970_);
lean_dec(v___x_2959_);
v___x_2972_ = lean_box(0);
v_isShared_2973_ = v_isSharedCheck_2977_;
goto v_resetjp_2971_;
}
v_resetjp_2971_:
{
lean_object* v___x_2975_; 
if (v_isShared_2973_ == 0)
{
v___x_2975_ = v___x_2972_;
goto v_reusejp_2974_;
}
else
{
lean_object* v_reuseFailAlloc_2976_; 
v_reuseFailAlloc_2976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2976_, 0, v_a_2970_);
v___x_2975_ = v_reuseFailAlloc_2976_;
goto v_reusejp_2974_;
}
v_reusejp_2974_:
{
return v___x_2975_;
}
}
}
}
else
{
lean_object* v_a_2978_; lean_object* v___x_2980_; uint8_t v_isShared_2981_; uint8_t v_isSharedCheck_2985_; 
lean_dec(v_a_2956_);
lean_dec_ref(v_config_2954_);
v_a_2978_ = lean_ctor_get(v___x_2957_, 0);
v_isSharedCheck_2985_ = !lean_is_exclusive(v___x_2957_);
if (v_isSharedCheck_2985_ == 0)
{
v___x_2980_ = v___x_2957_;
v_isShared_2981_ = v_isSharedCheck_2985_;
goto v_resetjp_2979_;
}
else
{
lean_inc(v_a_2978_);
lean_dec(v___x_2957_);
v___x_2980_ = lean_box(0);
v_isShared_2981_ = v_isSharedCheck_2985_;
goto v_resetjp_2979_;
}
v_resetjp_2979_:
{
lean_object* v___x_2983_; 
if (v_isShared_2981_ == 0)
{
v___x_2983_ = v___x_2980_;
goto v_reusejp_2982_;
}
else
{
lean_object* v_reuseFailAlloc_2984_; 
v_reuseFailAlloc_2984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2984_, 0, v_a_2978_);
v___x_2983_ = v_reuseFailAlloc_2984_;
goto v_reusejp_2982_;
}
v_reusejp_2982_:
{
return v___x_2983_;
}
}
}
}
else
{
lean_object* v_a_2986_; lean_object* v___x_2988_; uint8_t v_isShared_2989_; uint8_t v_isSharedCheck_2993_; 
lean_dec_ref(v_config_2954_);
lean_dec(v_post_x3f_2953_);
v_a_2986_ = lean_ctor_get(v___x_2955_, 0);
v_isSharedCheck_2993_ = !lean_is_exclusive(v___x_2955_);
if (v_isSharedCheck_2993_ == 0)
{
v___x_2988_ = v___x_2955_;
v_isShared_2989_ = v_isSharedCheck_2993_;
goto v_resetjp_2987_;
}
else
{
lean_inc(v_a_2986_);
lean_dec(v___x_2955_);
v___x_2988_ = lean_box(0);
v_isShared_2989_ = v_isSharedCheck_2993_;
goto v_resetjp_2987_;
}
v_resetjp_2987_:
{
lean_object* v___x_2991_; 
if (v_isShared_2989_ == 0)
{
v___x_2991_ = v___x_2988_;
goto v_reusejp_2990_;
}
else
{
lean_object* v_reuseFailAlloc_2992_; 
v_reuseFailAlloc_2992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2992_, 0, v_a_2986_);
v___x_2991_ = v_reuseFailAlloc_2992_;
goto v_reusejp_2990_;
}
v_reusejp_2990_:
{
return v___x_2991_;
}
}
}
}
else
{
lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; 
lean_dec(v___x_2950_);
v___x_2994_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabVariant___closed__1, &l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabVariant___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabVariant___closed__1);
v___x_2995_ = l_Lean_MessageData_ofName(v_variantName_2936_);
v___x_2996_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2996_, 0, v___x_2994_);
lean_ctor_set(v___x_2996_, 1, v___x_2995_);
v___x_2997_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabVariant___closed__3, &l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabVariant___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabVariant___closed__3);
v___x_2998_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2998_, 0, v___x_2996_);
lean_ctor_set(v___x_2998_, 1, v___x_2997_);
v___x_2999_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_ensureSym_spec__0___redArg(v___x_2998_, v_a_2942_, v_a_2943_, v_a_2944_, v_a_2945_);
return v___x_2999_;
}
}
else
{
lean_object* v___x_3000_; 
lean_dec(v_variantName_2936_);
v___x_3000_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkDefaultMethods(v_extraThms_2937_, v_a_2938_, v_a_2939_, v_a_2940_, v_a_2941_, v_a_2942_, v_a_2943_, v_a_2944_, v_a_2945_);
if (lean_obj_tag(v___x_3000_) == 0)
{
lean_object* v_a_3001_; lean_object* v___x_3003_; uint8_t v_isShared_3004_; uint8_t v_isSharedCheck_3010_; 
v_a_3001_ = lean_ctor_get(v___x_3000_, 0);
v_isSharedCheck_3010_ = !lean_is_exclusive(v___x_3000_);
if (v_isSharedCheck_3010_ == 0)
{
v___x_3003_ = v___x_3000_;
v_isShared_3004_ = v_isSharedCheck_3010_;
goto v_resetjp_3002_;
}
else
{
lean_inc(v_a_3001_);
lean_dec(v___x_3000_);
v___x_3003_ = lean_box(0);
v_isShared_3004_ = v_isSharedCheck_3010_;
goto v_resetjp_3002_;
}
v_resetjp_3002_:
{
lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3008_; 
v___x_3005_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabVariant___closed__4));
v___x_3006_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3006_, 0, v_a_3001_);
lean_ctor_set(v___x_3006_, 1, v___x_3005_);
if (v_isShared_3004_ == 0)
{
lean_ctor_set(v___x_3003_, 0, v___x_3006_);
v___x_3008_ = v___x_3003_;
goto v_reusejp_3007_;
}
else
{
lean_object* v_reuseFailAlloc_3009_; 
v_reuseFailAlloc_3009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3009_, 0, v___x_3006_);
v___x_3008_ = v_reuseFailAlloc_3009_;
goto v_reusejp_3007_;
}
v_reusejp_3007_:
{
return v___x_3008_;
}
}
}
else
{
lean_object* v_a_3011_; lean_object* v___x_3013_; uint8_t v_isShared_3014_; uint8_t v_isSharedCheck_3018_; 
v_a_3011_ = lean_ctor_get(v___x_3000_, 0);
v_isSharedCheck_3018_ = !lean_is_exclusive(v___x_3000_);
if (v_isSharedCheck_3018_ == 0)
{
v___x_3013_ = v___x_3000_;
v_isShared_3014_ = v_isSharedCheck_3018_;
goto v_resetjp_3012_;
}
else
{
lean_inc(v_a_3011_);
lean_dec(v___x_3000_);
v___x_3013_ = lean_box(0);
v_isShared_3014_ = v_isSharedCheck_3018_;
goto v_resetjp_3012_;
}
v_resetjp_3012_:
{
lean_object* v___x_3016_; 
if (v_isShared_3014_ == 0)
{
v___x_3016_ = v___x_3013_;
goto v_reusejp_3015_;
}
else
{
lean_object* v_reuseFailAlloc_3017_; 
v_reuseFailAlloc_3017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3017_, 0, v_a_3011_);
v___x_3016_ = v_reuseFailAlloc_3017_;
goto v_reusejp_3015_;
}
v_reusejp_3015_:
{
return v___x_3016_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabVariant___boxed(lean_object* v_variantName_3019_, lean_object* v_extraThms_3020_, lean_object* v_a_3021_, lean_object* v_a_3022_, lean_object* v_a_3023_, lean_object* v_a_3024_, lean_object* v_a_3025_, lean_object* v_a_3026_, lean_object* v_a_3027_, lean_object* v_a_3028_, lean_object* v_a_3029_){
_start:
{
lean_object* v_res_3030_; 
v_res_3030_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabVariant(v_variantName_3019_, v_extraThms_3020_, v_a_3021_, v_a_3022_, v_a_3023_, v_a_3024_, v_a_3025_, v_a_3026_, v_a_3027_, v_a_3028_);
lean_dec(v_a_3028_);
lean_dec_ref(v_a_3027_);
lean_dec(v_a_3026_);
lean_dec_ref(v_a_3025_);
lean_dec(v_a_3024_);
lean_dec_ref(v_a_3023_);
lean_dec(v_a_3022_);
lean_dec_ref(v_a_3021_);
lean_dec_ref(v_extraThms_3020_);
return v_res_3030_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__0___redArg___lam__0(lean_object* v_x_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_){
_start:
{
lean_object* v___x_3042_; 
lean_inc(v___y_3036_);
lean_inc_ref(v___y_3035_);
lean_inc(v___y_3034_);
lean_inc_ref(v___y_3033_);
lean_inc(v___y_3032_);
v___x_3042_ = lean_apply_10(v_x_3031_, v___y_3032_, v___y_3033_, v___y_3034_, v___y_3035_, v___y_3036_, v___y_3037_, v___y_3038_, v___y_3039_, v___y_3040_, lean_box(0));
return v___x_3042_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__0___redArg___lam__0___boxed(lean_object* v_x_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_){
_start:
{
lean_object* v_res_3054_; 
v_res_3054_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__0___redArg___lam__0(v_x_3043_, v___y_3044_, v___y_3045_, v___y_3046_, v___y_3047_, v___y_3048_, v___y_3049_, v___y_3050_, v___y_3051_, v___y_3052_);
lean_dec(v___y_3048_);
lean_dec_ref(v___y_3047_);
lean_dec(v___y_3046_);
lean_dec_ref(v___y_3045_);
lean_dec(v___y_3044_);
return v_res_3054_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__0___redArg(lean_object* v_mvarId_3055_, lean_object* v_x_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_){
_start:
{
lean_object* v___f_3067_; lean_object* v___x_3068_; 
lean_inc(v___y_3061_);
lean_inc_ref(v___y_3060_);
lean_inc(v___y_3059_);
lean_inc_ref(v___y_3058_);
lean_inc(v___y_3057_);
v___f_3067_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__0___redArg___lam__0___boxed), 11, 6);
lean_closure_set(v___f_3067_, 0, v_x_3056_);
lean_closure_set(v___f_3067_, 1, v___y_3057_);
lean_closure_set(v___f_3067_, 2, v___y_3058_);
lean_closure_set(v___f_3067_, 3, v___y_3059_);
lean_closure_set(v___f_3067_, 4, v___y_3060_);
lean_closure_set(v___f_3067_, 5, v___y_3061_);
v___x_3068_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_3055_, v___f_3067_, v___y_3062_, v___y_3063_, v___y_3064_, v___y_3065_);
if (lean_obj_tag(v___x_3068_) == 0)
{
return v___x_3068_;
}
else
{
lean_object* v_a_3069_; lean_object* v___x_3071_; uint8_t v_isShared_3072_; uint8_t v_isSharedCheck_3076_; 
v_a_3069_ = lean_ctor_get(v___x_3068_, 0);
v_isSharedCheck_3076_ = !lean_is_exclusive(v___x_3068_);
if (v_isSharedCheck_3076_ == 0)
{
v___x_3071_ = v___x_3068_;
v_isShared_3072_ = v_isSharedCheck_3076_;
goto v_resetjp_3070_;
}
else
{
lean_inc(v_a_3069_);
lean_dec(v___x_3068_);
v___x_3071_ = lean_box(0);
v_isShared_3072_ = v_isSharedCheck_3076_;
goto v_resetjp_3070_;
}
v_resetjp_3070_:
{
lean_object* v___x_3074_; 
if (v_isShared_3072_ == 0)
{
v___x_3074_ = v___x_3071_;
goto v_reusejp_3073_;
}
else
{
lean_object* v_reuseFailAlloc_3075_; 
v_reuseFailAlloc_3075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3075_, 0, v_a_3069_);
v___x_3074_ = v_reuseFailAlloc_3075_;
goto v_reusejp_3073_;
}
v_reusejp_3073_:
{
return v___x_3074_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__0___redArg___boxed(lean_object* v_mvarId_3077_, lean_object* v_x_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_){
_start:
{
lean_object* v_res_3089_; 
v_res_3089_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__0___redArg(v_mvarId_3077_, v_x_3078_, v___y_3079_, v___y_3080_, v___y_3081_, v___y_3082_, v___y_3083_, v___y_3084_, v___y_3085_, v___y_3086_, v___y_3087_);
lean_dec(v___y_3087_);
lean_dec_ref(v___y_3086_);
lean_dec(v___y_3085_);
lean_dec_ref(v___y_3084_);
lean_dec(v___y_3083_);
lean_dec_ref(v___y_3082_);
lean_dec(v___y_3081_);
lean_dec_ref(v___y_3080_);
lean_dec(v___y_3079_);
return v_res_3089_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__0(lean_object* v_00_u03b1_3090_, lean_object* v_mvarId_3091_, lean_object* v_x_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_){
_start:
{
lean_object* v___x_3103_; 
v___x_3103_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__0___redArg(v_mvarId_3091_, v_x_3092_, v___y_3093_, v___y_3094_, v___y_3095_, v___y_3096_, v___y_3097_, v___y_3098_, v___y_3099_, v___y_3100_, v___y_3101_);
return v___x_3103_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__0___boxed(lean_object* v_00_u03b1_3104_, lean_object* v_mvarId_3105_, lean_object* v_x_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_){
_start:
{
lean_object* v_res_3117_; 
v_res_3117_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__0(v_00_u03b1_3104_, v_mvarId_3105_, v_x_3106_, v___y_3107_, v___y_3108_, v___y_3109_, v___y_3110_, v___y_3111_, v___y_3112_, v___y_3113_, v___y_3114_, v___y_3115_);
lean_dec(v___y_3115_);
lean_dec_ref(v___y_3114_);
lean_dec(v___y_3113_);
lean_dec_ref(v___y_3112_);
lean_dec(v___y_3111_);
lean_dec_ref(v___y_3110_);
lean_dec(v___y_3109_);
lean_dec_ref(v___y_3108_);
lean_dec(v___y_3107_);
return v_res_3117_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__0(lean_object* v_mvarId_3118_, lean_object* v_fst_3119_, lean_object* v_snd_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_, lean_object* v___y_3130_){
_start:
{
lean_object* v___x_3132_; 
v___x_3132_ = l_Lean_MVarId_getType(v_mvarId_3118_, v___y_3127_, v___y_3128_, v___y_3129_, v___y_3130_);
if (lean_obj_tag(v___x_3132_) == 0)
{
lean_object* v_a_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; 
v_a_3133_ = lean_ctor_get(v___x_3132_, 0);
lean_inc(v_a_3133_);
lean_dec_ref(v___x_3132_);
v___x_3134_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simp___boxed), 11, 1);
lean_closure_set(v___x_3134_, 0, v_a_3133_);
v___x_3135_ = l_Lean_Meta_Sym_Simp_SimpM_run___redArg(v___x_3134_, v_fst_3119_, v_snd_3120_, v___y_3121_, v___y_3125_, v___y_3126_, v___y_3127_, v___y_3128_, v___y_3129_, v___y_3130_);
return v___x_3135_;
}
else
{
lean_object* v_a_3136_; lean_object* v___x_3138_; uint8_t v_isShared_3139_; uint8_t v_isSharedCheck_3143_; 
lean_dec_ref(v___y_3121_);
lean_dec_ref(v_snd_3120_);
lean_dec_ref(v_fst_3119_);
v_a_3136_ = lean_ctor_get(v___x_3132_, 0);
v_isSharedCheck_3143_ = !lean_is_exclusive(v___x_3132_);
if (v_isSharedCheck_3143_ == 0)
{
v___x_3138_ = v___x_3132_;
v_isShared_3139_ = v_isSharedCheck_3143_;
goto v_resetjp_3137_;
}
else
{
lean_inc(v_a_3136_);
lean_dec(v___x_3132_);
v___x_3138_ = lean_box(0);
v_isShared_3139_ = v_isSharedCheck_3143_;
goto v_resetjp_3137_;
}
v_resetjp_3137_:
{
lean_object* v___x_3141_; 
if (v_isShared_3139_ == 0)
{
v___x_3141_ = v___x_3138_;
goto v_reusejp_3140_;
}
else
{
lean_object* v_reuseFailAlloc_3142_; 
v_reuseFailAlloc_3142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3142_, 0, v_a_3136_);
v___x_3141_ = v_reuseFailAlloc_3142_;
goto v_reusejp_3140_;
}
v_reusejp_3140_:
{
return v___x_3141_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__0___boxed(lean_object* v_mvarId_3144_, lean_object* v_fst_3145_, lean_object* v_snd_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_){
_start:
{
lean_object* v_res_3158_; 
v_res_3158_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__0(v_mvarId_3144_, v_fst_3145_, v_snd_3146_, v___y_3147_, v___y_3148_, v___y_3149_, v___y_3150_, v___y_3151_, v___y_3152_, v___y_3153_, v___y_3154_, v___y_3155_, v___y_3156_);
lean_dec(v___y_3156_);
lean_dec_ref(v___y_3155_);
lean_dec(v___y_3154_);
lean_dec_ref(v___y_3153_);
lean_dec(v___y_3152_);
lean_dec_ref(v___y_3151_);
lean_dec(v___y_3150_);
lean_dec_ref(v___y_3149_);
lean_dec(v___y_3148_);
return v_res_3158_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__1(lean_object* v_fst_3159_, lean_object* v_mvarId_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_){
_start:
{
lean_object* v___x_3171_; 
v___x_3171_ = l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult(v_fst_3159_, v_mvarId_3160_, v___y_3164_, v___y_3165_, v___y_3166_, v___y_3167_, v___y_3168_, v___y_3169_);
return v___x_3171_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__1___boxed(lean_object* v_fst_3172_, lean_object* v_mvarId_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_){
_start:
{
lean_object* v_res_3184_; 
v_res_3184_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__1(v_fst_3172_, v_mvarId_3173_, v___y_3174_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_, v___y_3181_, v___y_3182_);
lean_dec(v___y_3182_);
lean_dec_ref(v___y_3181_);
lean_dec(v___y_3180_);
lean_dec_ref(v___y_3179_);
lean_dec(v___y_3178_);
lean_dec_ref(v___y_3177_);
lean_dec(v___y_3176_);
lean_dec_ref(v___y_3175_);
lean_dec(v___y_3174_);
return v_res_3184_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__2_spec__5___redArg(lean_object* v_a_3185_, lean_object* v_x_3186_){
_start:
{
if (lean_obj_tag(v_x_3186_) == 0)
{
lean_object* v___x_3187_; 
v___x_3187_ = lean_box(0);
return v___x_3187_;
}
else
{
lean_object* v_key_3188_; lean_object* v_value_3189_; lean_object* v_tail_3190_; uint8_t v___x_3191_; 
v_key_3188_ = lean_ctor_get(v_x_3186_, 0);
v_value_3189_ = lean_ctor_get(v_x_3186_, 1);
v_tail_3190_ = lean_ctor_get(v_x_3186_, 2);
v___x_3191_ = l_Lean_Elab_Tactic_Grind_instBEqSimpCacheKey_beq(v_key_3188_, v_a_3185_);
if (v___x_3191_ == 0)
{
v_x_3186_ = v_tail_3190_;
goto _start;
}
else
{
lean_object* v___x_3193_; 
lean_inc(v_value_3189_);
v___x_3193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3193_, 0, v_value_3189_);
return v___x_3193_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__2_spec__5___redArg___boxed(lean_object* v_a_3194_, lean_object* v_x_3195_){
_start:
{
lean_object* v_res_3196_; 
v_res_3196_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__2_spec__5___redArg(v_a_3194_, v_x_3195_);
lean_dec(v_x_3195_);
lean_dec_ref(v_a_3194_);
return v_res_3196_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__2___redArg(lean_object* v_m_3197_, lean_object* v_a_3198_){
_start:
{
lean_object* v_buckets_3199_; lean_object* v___x_3200_; uint64_t v___x_3201_; uint64_t v___x_3202_; uint64_t v___x_3203_; uint64_t v_fold_3204_; uint64_t v___x_3205_; uint64_t v___x_3206_; uint64_t v___x_3207_; size_t v___x_3208_; size_t v___x_3209_; size_t v___x_3210_; size_t v___x_3211_; size_t v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; 
v_buckets_3199_ = lean_ctor_get(v_m_3197_, 1);
v___x_3200_ = lean_array_get_size(v_buckets_3199_);
v___x_3201_ = l_Lean_Elab_Tactic_Grind_instHashableSimpCacheKey_hash(v_a_3198_);
v___x_3202_ = 32ULL;
v___x_3203_ = lean_uint64_shift_right(v___x_3201_, v___x_3202_);
v_fold_3204_ = lean_uint64_xor(v___x_3201_, v___x_3203_);
v___x_3205_ = 16ULL;
v___x_3206_ = lean_uint64_shift_right(v_fold_3204_, v___x_3205_);
v___x_3207_ = lean_uint64_xor(v_fold_3204_, v___x_3206_);
v___x_3208_ = lean_uint64_to_usize(v___x_3207_);
v___x_3209_ = lean_usize_of_nat(v___x_3200_);
v___x_3210_ = ((size_t)1ULL);
v___x_3211_ = lean_usize_sub(v___x_3209_, v___x_3210_);
v___x_3212_ = lean_usize_land(v___x_3208_, v___x_3211_);
v___x_3213_ = lean_array_uget_borrowed(v_buckets_3199_, v___x_3212_);
v___x_3214_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__2_spec__5___redArg(v_a_3198_, v___x_3213_);
return v___x_3214_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__2___redArg___boxed(lean_object* v_m_3215_, lean_object* v_a_3216_){
_start:
{
lean_object* v_res_3217_; 
v_res_3217_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__2___redArg(v_m_3215_, v_a_3216_);
lean_dec_ref(v_a_3216_);
lean_dec_ref(v_m_3215_);
return v_res_3217_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__4(uint8_t v___x_3218_, uint8_t v___x_3219_, lean_object* v_as_3220_, size_t v_i_3221_, size_t v_stop_3222_, lean_object* v_b_3223_){
_start:
{
lean_object* v___y_3225_; uint8_t v___x_3229_; 
v___x_3229_ = lean_usize_dec_eq(v_i_3221_, v_stop_3222_);
if (v___x_3229_ == 0)
{
lean_object* v_fst_3230_; uint8_t v___x_3231_; 
v_fst_3230_ = lean_ctor_get(v_b_3223_, 0);
v___x_3231_ = lean_unbox(v_fst_3230_);
if (v___x_3231_ == 0)
{
lean_object* v_snd_3232_; lean_object* v___x_3234_; uint8_t v_isShared_3235_; uint8_t v_isSharedCheck_3240_; 
v_snd_3232_ = lean_ctor_get(v_b_3223_, 1);
v_isSharedCheck_3240_ = !lean_is_exclusive(v_b_3223_);
if (v_isSharedCheck_3240_ == 0)
{
lean_object* v_unused_3241_; 
v_unused_3241_ = lean_ctor_get(v_b_3223_, 0);
lean_dec(v_unused_3241_);
v___x_3234_ = v_b_3223_;
v_isShared_3235_ = v_isSharedCheck_3240_;
goto v_resetjp_3233_;
}
else
{
lean_inc(v_snd_3232_);
lean_dec(v_b_3223_);
v___x_3234_ = lean_box(0);
v_isShared_3235_ = v_isSharedCheck_3240_;
goto v_resetjp_3233_;
}
v_resetjp_3233_:
{
lean_object* v___x_3236_; lean_object* v___x_3238_; 
v___x_3236_ = lean_box(v___x_3218_);
if (v_isShared_3235_ == 0)
{
lean_ctor_set(v___x_3234_, 0, v___x_3236_);
v___x_3238_ = v___x_3234_;
goto v_reusejp_3237_;
}
else
{
lean_object* v_reuseFailAlloc_3239_; 
v_reuseFailAlloc_3239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3239_, 0, v___x_3236_);
lean_ctor_set(v_reuseFailAlloc_3239_, 1, v_snd_3232_);
v___x_3238_ = v_reuseFailAlloc_3239_;
goto v_reusejp_3237_;
}
v_reusejp_3237_:
{
v___y_3225_ = v___x_3238_;
goto v___jp_3224_;
}
}
}
else
{
lean_object* v_snd_3242_; lean_object* v___x_3244_; uint8_t v_isShared_3245_; uint8_t v_isSharedCheck_3252_; 
v_snd_3242_ = lean_ctor_get(v_b_3223_, 1);
v_isSharedCheck_3252_ = !lean_is_exclusive(v_b_3223_);
if (v_isSharedCheck_3252_ == 0)
{
lean_object* v_unused_3253_; 
v_unused_3253_ = lean_ctor_get(v_b_3223_, 0);
lean_dec(v_unused_3253_);
v___x_3244_ = v_b_3223_;
v_isShared_3245_ = v_isSharedCheck_3252_;
goto v_resetjp_3243_;
}
else
{
lean_inc(v_snd_3242_);
lean_dec(v_b_3223_);
v___x_3244_ = lean_box(0);
v_isShared_3245_ = v_isSharedCheck_3252_;
goto v_resetjp_3243_;
}
v_resetjp_3243_:
{
lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3250_; 
v___x_3246_ = lean_array_uget_borrowed(v_as_3220_, v_i_3221_);
lean_inc(v___x_3246_);
v___x_3247_ = lean_array_push(v_snd_3242_, v___x_3246_);
v___x_3248_ = lean_box(v___x_3219_);
if (v_isShared_3245_ == 0)
{
lean_ctor_set(v___x_3244_, 1, v___x_3247_);
lean_ctor_set(v___x_3244_, 0, v___x_3248_);
v___x_3250_ = v___x_3244_;
goto v_reusejp_3249_;
}
else
{
lean_object* v_reuseFailAlloc_3251_; 
v_reuseFailAlloc_3251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3251_, 0, v___x_3248_);
lean_ctor_set(v_reuseFailAlloc_3251_, 1, v___x_3247_);
v___x_3250_ = v_reuseFailAlloc_3251_;
goto v_reusejp_3249_;
}
v_reusejp_3249_:
{
v___y_3225_ = v___x_3250_;
goto v___jp_3224_;
}
}
}
}
else
{
return v_b_3223_;
}
v___jp_3224_:
{
size_t v___x_3226_; size_t v___x_3227_; 
v___x_3226_ = ((size_t)1ULL);
v___x_3227_ = lean_usize_add(v_i_3221_, v___x_3226_);
v_i_3221_ = v___x_3227_;
v_b_3223_ = v___y_3225_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__4___boxed(lean_object* v___x_3254_, lean_object* v___x_3255_, lean_object* v_as_3256_, lean_object* v_i_3257_, lean_object* v_stop_3258_, lean_object* v_b_3259_){
_start:
{
uint8_t v___x_9487__boxed_3260_; uint8_t v___x_9488__boxed_3261_; size_t v_i_boxed_3262_; size_t v_stop_boxed_3263_; lean_object* v_res_3264_; 
v___x_9487__boxed_3260_ = lean_unbox(v___x_3254_);
v___x_9488__boxed_3261_ = lean_unbox(v___x_3255_);
v_i_boxed_3262_ = lean_unbox_usize(v_i_3257_);
lean_dec(v_i_3257_);
v_stop_boxed_3263_ = lean_unbox_usize(v_stop_3258_);
lean_dec(v_stop_3258_);
v_res_3264_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__4(v___x_9487__boxed_3260_, v___x_9488__boxed_3261_, v_as_3256_, v_i_boxed_3262_, v_stop_boxed_3263_, v_b_3259_);
lean_dec_ref(v_as_3256_);
return v_res_3264_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__3___redArg(lean_object* v_a_3265_, lean_object* v_b_3266_, lean_object* v_x_3267_){
_start:
{
if (lean_obj_tag(v_x_3267_) == 0)
{
lean_dec(v_b_3266_);
lean_dec_ref(v_a_3265_);
return v_x_3267_;
}
else
{
lean_object* v_key_3268_; lean_object* v_value_3269_; lean_object* v_tail_3270_; lean_object* v___x_3272_; uint8_t v_isShared_3273_; uint8_t v_isSharedCheck_3282_; 
v_key_3268_ = lean_ctor_get(v_x_3267_, 0);
v_value_3269_ = lean_ctor_get(v_x_3267_, 1);
v_tail_3270_ = lean_ctor_get(v_x_3267_, 2);
v_isSharedCheck_3282_ = !lean_is_exclusive(v_x_3267_);
if (v_isSharedCheck_3282_ == 0)
{
v___x_3272_ = v_x_3267_;
v_isShared_3273_ = v_isSharedCheck_3282_;
goto v_resetjp_3271_;
}
else
{
lean_inc(v_tail_3270_);
lean_inc(v_value_3269_);
lean_inc(v_key_3268_);
lean_dec(v_x_3267_);
v___x_3272_ = lean_box(0);
v_isShared_3273_ = v_isSharedCheck_3282_;
goto v_resetjp_3271_;
}
v_resetjp_3271_:
{
uint8_t v___x_3274_; 
v___x_3274_ = l_Lean_Elab_Tactic_Grind_instBEqSimpCacheKey_beq(v_key_3268_, v_a_3265_);
if (v___x_3274_ == 0)
{
lean_object* v___x_3275_; lean_object* v___x_3277_; 
v___x_3275_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__3___redArg(v_a_3265_, v_b_3266_, v_tail_3270_);
if (v_isShared_3273_ == 0)
{
lean_ctor_set(v___x_3272_, 2, v___x_3275_);
v___x_3277_ = v___x_3272_;
goto v_reusejp_3276_;
}
else
{
lean_object* v_reuseFailAlloc_3278_; 
v_reuseFailAlloc_3278_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3278_, 0, v_key_3268_);
lean_ctor_set(v_reuseFailAlloc_3278_, 1, v_value_3269_);
lean_ctor_set(v_reuseFailAlloc_3278_, 2, v___x_3275_);
v___x_3277_ = v_reuseFailAlloc_3278_;
goto v_reusejp_3276_;
}
v_reusejp_3276_:
{
return v___x_3277_;
}
}
else
{
lean_object* v___x_3280_; 
lean_dec(v_value_3269_);
lean_dec(v_key_3268_);
if (v_isShared_3273_ == 0)
{
lean_ctor_set(v___x_3272_, 1, v_b_3266_);
lean_ctor_set(v___x_3272_, 0, v_a_3265_);
v___x_3280_ = v___x_3272_;
goto v_reusejp_3279_;
}
else
{
lean_object* v_reuseFailAlloc_3281_; 
v_reuseFailAlloc_3281_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3281_, 0, v_a_3265_);
lean_ctor_set(v_reuseFailAlloc_3281_, 1, v_b_3266_);
lean_ctor_set(v_reuseFailAlloc_3281_, 2, v_tail_3270_);
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
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__2_spec__3_spec__7___redArg(lean_object* v_x_3283_, lean_object* v_x_3284_){
_start:
{
if (lean_obj_tag(v_x_3284_) == 0)
{
return v_x_3283_;
}
else
{
lean_object* v_key_3285_; lean_object* v_value_3286_; lean_object* v_tail_3287_; lean_object* v___x_3289_; uint8_t v_isShared_3290_; uint8_t v_isSharedCheck_3310_; 
v_key_3285_ = lean_ctor_get(v_x_3284_, 0);
v_value_3286_ = lean_ctor_get(v_x_3284_, 1);
v_tail_3287_ = lean_ctor_get(v_x_3284_, 2);
v_isSharedCheck_3310_ = !lean_is_exclusive(v_x_3284_);
if (v_isSharedCheck_3310_ == 0)
{
v___x_3289_ = v_x_3284_;
v_isShared_3290_ = v_isSharedCheck_3310_;
goto v_resetjp_3288_;
}
else
{
lean_inc(v_tail_3287_);
lean_inc(v_value_3286_);
lean_inc(v_key_3285_);
lean_dec(v_x_3284_);
v___x_3289_ = lean_box(0);
v_isShared_3290_ = v_isSharedCheck_3310_;
goto v_resetjp_3288_;
}
v_resetjp_3288_:
{
lean_object* v___x_3291_; uint64_t v___x_3292_; uint64_t v___x_3293_; uint64_t v___x_3294_; uint64_t v_fold_3295_; uint64_t v___x_3296_; uint64_t v___x_3297_; uint64_t v___x_3298_; size_t v___x_3299_; size_t v___x_3300_; size_t v___x_3301_; size_t v___x_3302_; size_t v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3306_; 
v___x_3291_ = lean_array_get_size(v_x_3283_);
v___x_3292_ = l_Lean_Elab_Tactic_Grind_instHashableSimpCacheKey_hash(v_key_3285_);
v___x_3293_ = 32ULL;
v___x_3294_ = lean_uint64_shift_right(v___x_3292_, v___x_3293_);
v_fold_3295_ = lean_uint64_xor(v___x_3292_, v___x_3294_);
v___x_3296_ = 16ULL;
v___x_3297_ = lean_uint64_shift_right(v_fold_3295_, v___x_3296_);
v___x_3298_ = lean_uint64_xor(v_fold_3295_, v___x_3297_);
v___x_3299_ = lean_uint64_to_usize(v___x_3298_);
v___x_3300_ = lean_usize_of_nat(v___x_3291_);
v___x_3301_ = ((size_t)1ULL);
v___x_3302_ = lean_usize_sub(v___x_3300_, v___x_3301_);
v___x_3303_ = lean_usize_land(v___x_3299_, v___x_3302_);
v___x_3304_ = lean_array_uget_borrowed(v_x_3283_, v___x_3303_);
lean_inc(v___x_3304_);
if (v_isShared_3290_ == 0)
{
lean_ctor_set(v___x_3289_, 2, v___x_3304_);
v___x_3306_ = v___x_3289_;
goto v_reusejp_3305_;
}
else
{
lean_object* v_reuseFailAlloc_3309_; 
v_reuseFailAlloc_3309_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3309_, 0, v_key_3285_);
lean_ctor_set(v_reuseFailAlloc_3309_, 1, v_value_3286_);
lean_ctor_set(v_reuseFailAlloc_3309_, 2, v___x_3304_);
v___x_3306_ = v_reuseFailAlloc_3309_;
goto v_reusejp_3305_;
}
v_reusejp_3305_:
{
lean_object* v___x_3307_; 
v___x_3307_ = lean_array_uset(v_x_3283_, v___x_3303_, v___x_3306_);
v_x_3283_ = v___x_3307_;
v_x_3284_ = v_tail_3287_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__2_spec__3___redArg(lean_object* v_i_3311_, lean_object* v_source_3312_, lean_object* v_target_3313_){
_start:
{
lean_object* v___x_3314_; uint8_t v___x_3315_; 
v___x_3314_ = lean_array_get_size(v_source_3312_);
v___x_3315_ = lean_nat_dec_lt(v_i_3311_, v___x_3314_);
if (v___x_3315_ == 0)
{
lean_dec_ref(v_source_3312_);
lean_dec(v_i_3311_);
return v_target_3313_;
}
else
{
lean_object* v_es_3316_; lean_object* v___x_3317_; lean_object* v_source_3318_; lean_object* v_target_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; 
v_es_3316_ = lean_array_fget(v_source_3312_, v_i_3311_);
v___x_3317_ = lean_box(0);
v_source_3318_ = lean_array_fset(v_source_3312_, v_i_3311_, v___x_3317_);
v_target_3319_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__2_spec__3_spec__7___redArg(v_target_3313_, v_es_3316_);
v___x_3320_ = lean_unsigned_to_nat(1u);
v___x_3321_ = lean_nat_add(v_i_3311_, v___x_3320_);
lean_dec(v_i_3311_);
v_i_3311_ = v___x_3321_;
v_source_3312_ = v_source_3318_;
v_target_3313_ = v_target_3319_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__2___redArg(lean_object* v_data_3323_){
_start:
{
lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v_nbuckets_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; 
v___x_3324_ = lean_array_get_size(v_data_3323_);
v___x_3325_ = lean_unsigned_to_nat(2u);
v_nbuckets_3326_ = lean_nat_mul(v___x_3324_, v___x_3325_);
v___x_3327_ = lean_unsigned_to_nat(0u);
v___x_3328_ = lean_box(0);
v___x_3329_ = lean_mk_array(v_nbuckets_3326_, v___x_3328_);
v___x_3330_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__2_spec__3___redArg(v___x_3327_, v_data_3323_, v___x_3329_);
return v___x_3330_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__1___redArg(lean_object* v_a_3331_, lean_object* v_x_3332_){
_start:
{
if (lean_obj_tag(v_x_3332_) == 0)
{
uint8_t v___x_3333_; 
v___x_3333_ = 0;
return v___x_3333_;
}
else
{
lean_object* v_key_3334_; lean_object* v_tail_3335_; uint8_t v___x_3336_; 
v_key_3334_ = lean_ctor_get(v_x_3332_, 0);
v_tail_3335_ = lean_ctor_get(v_x_3332_, 2);
v___x_3336_ = l_Lean_Elab_Tactic_Grind_instBEqSimpCacheKey_beq(v_key_3334_, v_a_3331_);
if (v___x_3336_ == 0)
{
v_x_3332_ = v_tail_3335_;
goto _start;
}
else
{
return v___x_3336_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__1___redArg___boxed(lean_object* v_a_3338_, lean_object* v_x_3339_){
_start:
{
uint8_t v_res_3340_; lean_object* v_r_3341_; 
v_res_3340_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__1___redArg(v_a_3338_, v_x_3339_);
lean_dec(v_x_3339_);
lean_dec_ref(v_a_3338_);
v_r_3341_ = lean_box(v_res_3340_);
return v_r_3341_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1___redArg(lean_object* v_m_3342_, lean_object* v_a_3343_, lean_object* v_b_3344_){
_start:
{
lean_object* v_size_3345_; lean_object* v_buckets_3346_; lean_object* v___x_3348_; uint8_t v_isShared_3349_; uint8_t v_isSharedCheck_3389_; 
v_size_3345_ = lean_ctor_get(v_m_3342_, 0);
v_buckets_3346_ = lean_ctor_get(v_m_3342_, 1);
v_isSharedCheck_3389_ = !lean_is_exclusive(v_m_3342_);
if (v_isSharedCheck_3389_ == 0)
{
v___x_3348_ = v_m_3342_;
v_isShared_3349_ = v_isSharedCheck_3389_;
goto v_resetjp_3347_;
}
else
{
lean_inc(v_buckets_3346_);
lean_inc(v_size_3345_);
lean_dec(v_m_3342_);
v___x_3348_ = lean_box(0);
v_isShared_3349_ = v_isSharedCheck_3389_;
goto v_resetjp_3347_;
}
v_resetjp_3347_:
{
lean_object* v___x_3350_; uint64_t v___x_3351_; uint64_t v___x_3352_; uint64_t v___x_3353_; uint64_t v_fold_3354_; uint64_t v___x_3355_; uint64_t v___x_3356_; uint64_t v___x_3357_; size_t v___x_3358_; size_t v___x_3359_; size_t v___x_3360_; size_t v___x_3361_; size_t v___x_3362_; lean_object* v_bkt_3363_; uint8_t v___x_3364_; 
v___x_3350_ = lean_array_get_size(v_buckets_3346_);
v___x_3351_ = l_Lean_Elab_Tactic_Grind_instHashableSimpCacheKey_hash(v_a_3343_);
v___x_3352_ = 32ULL;
v___x_3353_ = lean_uint64_shift_right(v___x_3351_, v___x_3352_);
v_fold_3354_ = lean_uint64_xor(v___x_3351_, v___x_3353_);
v___x_3355_ = 16ULL;
v___x_3356_ = lean_uint64_shift_right(v_fold_3354_, v___x_3355_);
v___x_3357_ = lean_uint64_xor(v_fold_3354_, v___x_3356_);
v___x_3358_ = lean_uint64_to_usize(v___x_3357_);
v___x_3359_ = lean_usize_of_nat(v___x_3350_);
v___x_3360_ = ((size_t)1ULL);
v___x_3361_ = lean_usize_sub(v___x_3359_, v___x_3360_);
v___x_3362_ = lean_usize_land(v___x_3358_, v___x_3361_);
v_bkt_3363_ = lean_array_uget_borrowed(v_buckets_3346_, v___x_3362_);
v___x_3364_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__1___redArg(v_a_3343_, v_bkt_3363_);
if (v___x_3364_ == 0)
{
lean_object* v___x_3365_; lean_object* v_size_x27_3366_; lean_object* v___x_3367_; lean_object* v_buckets_x27_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; uint8_t v___x_3374_; 
v___x_3365_ = lean_unsigned_to_nat(1u);
v_size_x27_3366_ = lean_nat_add(v_size_3345_, v___x_3365_);
lean_dec(v_size_3345_);
lean_inc(v_bkt_3363_);
v___x_3367_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3367_, 0, v_a_3343_);
lean_ctor_set(v___x_3367_, 1, v_b_3344_);
lean_ctor_set(v___x_3367_, 2, v_bkt_3363_);
v_buckets_x27_3368_ = lean_array_uset(v_buckets_3346_, v___x_3362_, v___x_3367_);
v___x_3369_ = lean_unsigned_to_nat(4u);
v___x_3370_ = lean_nat_mul(v_size_x27_3366_, v___x_3369_);
v___x_3371_ = lean_unsigned_to_nat(3u);
v___x_3372_ = lean_nat_div(v___x_3370_, v___x_3371_);
lean_dec(v___x_3370_);
v___x_3373_ = lean_array_get_size(v_buckets_x27_3368_);
v___x_3374_ = lean_nat_dec_le(v___x_3372_, v___x_3373_);
lean_dec(v___x_3372_);
if (v___x_3374_ == 0)
{
lean_object* v_val_3375_; lean_object* v___x_3377_; 
v_val_3375_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__2___redArg(v_buckets_x27_3368_);
if (v_isShared_3349_ == 0)
{
lean_ctor_set(v___x_3348_, 1, v_val_3375_);
lean_ctor_set(v___x_3348_, 0, v_size_x27_3366_);
v___x_3377_ = v___x_3348_;
goto v_reusejp_3376_;
}
else
{
lean_object* v_reuseFailAlloc_3378_; 
v_reuseFailAlloc_3378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3378_, 0, v_size_x27_3366_);
lean_ctor_set(v_reuseFailAlloc_3378_, 1, v_val_3375_);
v___x_3377_ = v_reuseFailAlloc_3378_;
goto v_reusejp_3376_;
}
v_reusejp_3376_:
{
return v___x_3377_;
}
}
else
{
lean_object* v___x_3380_; 
if (v_isShared_3349_ == 0)
{
lean_ctor_set(v___x_3348_, 1, v_buckets_x27_3368_);
lean_ctor_set(v___x_3348_, 0, v_size_x27_3366_);
v___x_3380_ = v___x_3348_;
goto v_reusejp_3379_;
}
else
{
lean_object* v_reuseFailAlloc_3381_; 
v_reuseFailAlloc_3381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3381_, 0, v_size_x27_3366_);
lean_ctor_set(v_reuseFailAlloc_3381_, 1, v_buckets_x27_3368_);
v___x_3380_ = v_reuseFailAlloc_3381_;
goto v_reusejp_3379_;
}
v_reusejp_3379_:
{
return v___x_3380_;
}
}
}
else
{
lean_object* v___x_3382_; lean_object* v_buckets_x27_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3387_; 
lean_inc(v_bkt_3363_);
v___x_3382_ = lean_box(0);
v_buckets_x27_3383_ = lean_array_uset(v_buckets_3346_, v___x_3362_, v___x_3382_);
v___x_3384_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__3___redArg(v_a_3343_, v_b_3344_, v_bkt_3363_);
v___x_3385_ = lean_array_uset(v_buckets_x27_3383_, v___x_3362_, v___x_3384_);
if (v_isShared_3349_ == 0)
{
lean_ctor_set(v___x_3348_, 1, v___x_3385_);
v___x_3387_ = v___x_3348_;
goto v_reusejp_3386_;
}
else
{
lean_object* v_reuseFailAlloc_3388_; 
v_reuseFailAlloc_3388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3388_, 0, v_size_3345_);
lean_ctor_set(v_reuseFailAlloc_3388_, 1, v___x_3385_);
v___x_3387_ = v_reuseFailAlloc_3388_;
goto v_reusejp_3386_;
}
v_reusejp_3386_:
{
return v___x_3387_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__3(size_t v_sz_3390_, size_t v_i_3391_, lean_object* v_bs_3392_){
_start:
{
uint8_t v___x_3393_; 
v___x_3393_ = lean_usize_dec_lt(v_i_3391_, v_sz_3390_);
if (v___x_3393_ == 0)
{
lean_object* v___x_3394_; 
v___x_3394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3394_, 0, v_bs_3392_);
return v___x_3394_;
}
else
{
lean_object* v_v_3395_; lean_object* v___x_3396_; lean_object* v_bs_x27_3397_; size_t v___x_3398_; size_t v___x_3399_; lean_object* v___x_3400_; 
v_v_3395_ = lean_array_uget(v_bs_3392_, v_i_3391_);
v___x_3396_ = lean_unsigned_to_nat(0u);
v_bs_x27_3397_ = lean_array_uset(v_bs_3392_, v_i_3391_, v___x_3396_);
v___x_3398_ = ((size_t)1ULL);
v___x_3399_ = lean_usize_add(v_i_3391_, v___x_3398_);
v___x_3400_ = lean_array_uset(v_bs_x27_3397_, v_i_3391_, v_v_3395_);
v_i_3391_ = v___x_3399_;
v_bs_3392_ = v___x_3400_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__3___boxed(lean_object* v_sz_3402_, lean_object* v_i_3403_, lean_object* v_bs_3404_){
_start:
{
size_t v_sz_boxed_3405_; size_t v_i_boxed_3406_; lean_object* v_res_3407_; 
v_sz_boxed_3405_ = lean_unbox_usize(v_sz_3402_);
lean_dec(v_sz_3402_);
v_i_boxed_3406_ = lean_unbox_usize(v_i_3403_);
lean_dec(v_i_3403_);
v_res_3407_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__3(v_sz_boxed_3405_, v_i_boxed_3406_, v_bs_3404_);
return v_res_3407_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__1(void){
_start:
{
lean_object* v___x_3409_; lean_object* v___x_3410_; 
v___x_3409_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__0));
v___x_3410_ = l_Lean_stringToMessageData(v___x_3409_);
return v___x_3410_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__4(void){
_start:
{
lean_object* v___x_3418_; 
v___x_3418_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3418_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__5(void){
_start:
{
lean_object* v___x_3419_; lean_object* v___x_3420_; 
v___x_3419_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__4, &l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__4_once, _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__4);
v___x_3420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3420_, 0, v___x_3419_);
return v___x_3420_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__6(void){
_start:
{
lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; 
v___x_3421_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__5, &l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__5);
v___x_3422_ = lean_unsigned_to_nat(0u);
v___x_3423_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3423_, 0, v___x_3422_);
lean_ctor_set(v___x_3423_, 1, v___x_3421_);
lean_ctor_set(v___x_3423_, 2, v___x_3421_);
lean_ctor_set(v___x_3423_, 3, v___x_3421_);
return v___x_3423_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2(lean_object* v_stx_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_){
_start:
{
lean_object* v___y_3437_; lean_object* v___y_3438_; lean_object* v___y_3439_; lean_object* v___y_3440_; lean_object* v___y_3441_; lean_object* v___y_3442_; lean_object* v___y_3443_; lean_object* v___y_3444_; lean_object* v___y_3445_; lean_object* v___y_3446_; lean_object* v___y_3447_; lean_object* v___y_3448_; lean_object* v___x_3543_; 
v___x_3543_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_ensureSym(v___y_3427_, v___y_3428_, v___y_3429_, v___y_3430_, v___y_3431_, v___y_3432_, v___y_3433_, v___y_3434_);
if (lean_obj_tag(v___x_3543_) == 0)
{
lean_object* v___x_3545_; uint8_t v_isShared_3546_; uint8_t v_isSharedCheck_3659_; 
v_isSharedCheck_3659_ = !lean_is_exclusive(v___x_3543_);
if (v_isSharedCheck_3659_ == 0)
{
lean_object* v_unused_3660_; 
v_unused_3660_ = lean_ctor_get(v___x_3543_, 0);
lean_dec(v_unused_3660_);
v___x_3545_ = v___x_3543_;
v_isShared_3546_ = v_isSharedCheck_3659_;
goto v_resetjp_3544_;
}
else
{
lean_dec(v___x_3543_);
v___x_3545_ = lean_box(0);
v_isShared_3546_ = v_isSharedCheck_3659_;
goto v_resetjp_3544_;
}
v_resetjp_3544_:
{
lean_object* v___x_3547_; uint8_t v___x_3548_; 
v___x_3547_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__3));
lean_inc(v_stx_3426_);
v___x_3548_ = l_Lean_Syntax_isOfKind(v_stx_3426_, v___x_3547_);
if (v___x_3548_ == 0)
{
lean_object* v___x_3549_; 
lean_del_object(v___x_3545_);
lean_dec(v_stx_3426_);
v___x_3549_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro_spec__0___redArg();
return v___x_3549_;
}
else
{
lean_object* v___x_3550_; lean_object* v___y_3552_; lean_object* v___y_3553_; lean_object* v___y_3554_; lean_object* v___y_3555_; lean_object* v___y_3556_; lean_object* v___y_3557_; lean_object* v___y_3558_; lean_object* v___y_3559_; lean_object* v___y_3560_; lean_object* v___y_3561_; lean_object* v___y_3588_; lean_object* v_extraIds_3589_; lean_object* v___y_3590_; lean_object* v___y_3591_; lean_object* v___y_3592_; lean_object* v___y_3593_; lean_object* v___y_3594_; lean_object* v___y_3595_; lean_object* v___y_3596_; lean_object* v___y_3597_; lean_object* v___y_3602_; lean_object* v___y_3603_; lean_object* v___y_3604_; lean_object* v___y_3605_; lean_object* v___y_3606_; lean_object* v___y_3607_; lean_object* v___y_3608_; lean_object* v___y_3609_; lean_object* v___y_3610_; lean_object* v___y_3611_; lean_object* v___x_3616_; lean_object* v_variantId_x3f_3618_; lean_object* v___y_3619_; lean_object* v___y_3620_; lean_object* v___y_3621_; lean_object* v___y_3622_; lean_object* v___y_3623_; lean_object* v___y_3624_; lean_object* v___y_3625_; lean_object* v___y_3626_; lean_object* v___x_3650_; uint8_t v___x_3651_; 
v___x_3550_ = lean_unsigned_to_nat(0u);
v___x_3616_ = lean_unsigned_to_nat(1u);
v___x_3650_ = l_Lean_Syntax_getArg(v_stx_3426_, v___x_3616_);
v___x_3651_ = l_Lean_Syntax_isNone(v___x_3650_);
if (v___x_3651_ == 0)
{
uint8_t v___x_3652_; 
lean_inc(v___x_3650_);
v___x_3652_ = l_Lean_Syntax_matchesNull(v___x_3650_, v___x_3616_);
if (v___x_3652_ == 0)
{
lean_object* v___x_3653_; 
lean_dec(v___x_3650_);
lean_del_object(v___x_3545_);
lean_dec(v_stx_3426_);
v___x_3653_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro_spec__0___redArg();
return v___x_3653_;
}
else
{
lean_object* v___x_3654_; lean_object* v___x_3656_; 
v___x_3654_ = l_Lean_Syntax_getArg(v___x_3650_, v___x_3550_);
lean_dec(v___x_3650_);
if (v_isShared_3546_ == 0)
{
lean_ctor_set_tag(v___x_3545_, 1);
lean_ctor_set(v___x_3545_, 0, v___x_3654_);
v___x_3656_ = v___x_3545_;
goto v_reusejp_3655_;
}
else
{
lean_object* v_reuseFailAlloc_3657_; 
v_reuseFailAlloc_3657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3657_, 0, v___x_3654_);
v___x_3656_ = v_reuseFailAlloc_3657_;
goto v_reusejp_3655_;
}
v_reusejp_3655_:
{
v_variantId_x3f_3618_ = v___x_3656_;
v___y_3619_ = v___y_3427_;
v___y_3620_ = v___y_3428_;
v___y_3621_ = v___y_3429_;
v___y_3622_ = v___y_3430_;
v___y_3623_ = v___y_3431_;
v___y_3624_ = v___y_3432_;
v___y_3625_ = v___y_3433_;
v___y_3626_ = v___y_3434_;
goto v___jp_3617_;
}
}
}
else
{
lean_object* v___x_3658_; 
lean_dec(v___x_3650_);
lean_del_object(v___x_3545_);
v___x_3658_ = lean_box(0);
v_variantId_x3f_3618_ = v___x_3658_;
v___y_3619_ = v___y_3427_;
v___y_3620_ = v___y_3428_;
v___y_3621_ = v___y_3429_;
v___y_3622_ = v___y_3430_;
v___y_3623_ = v___y_3431_;
v___y_3624_ = v___y_3432_;
v___y_3625_ = v___y_3433_;
v___y_3626_ = v___y_3434_;
goto v___jp_3617_;
}
v___jp_3551_:
{
lean_object* v___x_3562_; 
v___x_3562_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems(v___y_3558_, v___y_3557_, v___y_3553_, v___y_3556_, v___y_3560_, v___y_3559_, v___y_3555_, v___y_3552_, v___y_3554_);
lean_dec(v___y_3558_);
if (lean_obj_tag(v___x_3562_) == 0)
{
lean_object* v_a_3563_; lean_object* v_fst_3564_; lean_object* v_snd_3565_; lean_object* v___x_3567_; uint8_t v_isShared_3568_; uint8_t v_isSharedCheck_3578_; 
v_a_3563_ = lean_ctor_get(v___x_3562_, 0);
lean_inc(v_a_3563_);
lean_dec_ref(v___x_3562_);
v_fst_3564_ = lean_ctor_get(v_a_3563_, 0);
v_snd_3565_ = lean_ctor_get(v_a_3563_, 1);
v_isSharedCheck_3578_ = !lean_is_exclusive(v_a_3563_);
if (v_isSharedCheck_3578_ == 0)
{
v___x_3567_ = v_a_3563_;
v_isShared_3568_ = v_isSharedCheck_3578_;
goto v_resetjp_3566_;
}
else
{
lean_inc(v_snd_3565_);
lean_inc(v_fst_3564_);
lean_dec(v_a_3563_);
v___x_3567_ = lean_box(0);
v_isShared_3568_ = v_isSharedCheck_3578_;
goto v_resetjp_3566_;
}
v_resetjp_3566_:
{
lean_object* v___x_3569_; lean_object* v_cache_3570_; lean_object* v_simpState_3571_; lean_object* v___x_3573_; 
v___x_3569_ = lean_st_ref_get(v___y_3553_);
v_cache_3570_ = lean_ctor_get(v___x_3569_, 3);
lean_inc_ref(v_cache_3570_);
lean_dec(v___x_3569_);
v_simpState_3571_ = lean_ctor_get(v_cache_3570_, 2);
lean_inc_ref(v_simpState_3571_);
lean_dec_ref(v_cache_3570_);
lean_inc(v___y_3561_);
if (v_isShared_3568_ == 0)
{
lean_ctor_set(v___x_3567_, 1, v_fst_3564_);
lean_ctor_set(v___x_3567_, 0, v___y_3561_);
v___x_3573_ = v___x_3567_;
goto v_reusejp_3572_;
}
else
{
lean_object* v_reuseFailAlloc_3577_; 
v_reuseFailAlloc_3577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3577_, 0, v___y_3561_);
lean_ctor_set(v_reuseFailAlloc_3577_, 1, v_fst_3564_);
v___x_3573_ = v_reuseFailAlloc_3577_;
goto v_reusejp_3572_;
}
v_reusejp_3572_:
{
lean_object* v___x_3574_; 
v___x_3574_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__2___redArg(v_simpState_3571_, v___x_3573_);
lean_dec_ref(v_simpState_3571_);
if (lean_obj_tag(v___x_3574_) == 0)
{
lean_object* v___x_3575_; 
v___x_3575_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__6, &l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__6_once, _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__6);
v___y_3437_ = v___x_3573_;
v___y_3438_ = v___y_3552_;
v___y_3439_ = v___y_3553_;
v___y_3440_ = v___y_3554_;
v___y_3441_ = v___y_3555_;
v___y_3442_ = v___y_3556_;
v___y_3443_ = v___y_3557_;
v___y_3444_ = v___y_3559_;
v___y_3445_ = v___y_3561_;
v___y_3446_ = v___y_3560_;
v___y_3447_ = v_snd_3565_;
v___y_3448_ = v___x_3575_;
goto v___jp_3436_;
}
else
{
lean_object* v_val_3576_; 
v_val_3576_ = lean_ctor_get(v___x_3574_, 0);
lean_inc(v_val_3576_);
lean_dec_ref(v___x_3574_);
v___y_3437_ = v___x_3573_;
v___y_3438_ = v___y_3552_;
v___y_3439_ = v___y_3553_;
v___y_3440_ = v___y_3554_;
v___y_3441_ = v___y_3555_;
v___y_3442_ = v___y_3556_;
v___y_3443_ = v___y_3557_;
v___y_3444_ = v___y_3559_;
v___y_3445_ = v___y_3561_;
v___y_3446_ = v___y_3560_;
v___y_3447_ = v_snd_3565_;
v___y_3448_ = v_val_3576_;
goto v___jp_3436_;
}
}
}
}
else
{
lean_object* v_a_3579_; lean_object* v___x_3581_; uint8_t v_isShared_3582_; uint8_t v_isSharedCheck_3586_; 
lean_dec(v___y_3561_);
v_a_3579_ = lean_ctor_get(v___x_3562_, 0);
v_isSharedCheck_3586_ = !lean_is_exclusive(v___x_3562_);
if (v_isSharedCheck_3586_ == 0)
{
v___x_3581_ = v___x_3562_;
v_isShared_3582_ = v_isSharedCheck_3586_;
goto v_resetjp_3580_;
}
else
{
lean_inc(v_a_3579_);
lean_dec(v___x_3562_);
v___x_3581_ = lean_box(0);
v_isShared_3582_ = v_isSharedCheck_3586_;
goto v_resetjp_3580_;
}
v_resetjp_3580_:
{
lean_object* v___x_3584_; 
if (v_isShared_3582_ == 0)
{
v___x_3584_ = v___x_3581_;
goto v_reusejp_3583_;
}
else
{
lean_object* v_reuseFailAlloc_3585_; 
v_reuseFailAlloc_3585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3585_, 0, v_a_3579_);
v___x_3584_ = v_reuseFailAlloc_3585_;
goto v_reusejp_3583_;
}
v_reusejp_3583_:
{
return v___x_3584_;
}
}
}
}
v___jp_3587_:
{
if (lean_obj_tag(v___y_3588_) == 0)
{
lean_object* v___x_3598_; 
v___x_3598_ = lean_box(0);
v___y_3552_ = v___y_3596_;
v___y_3553_ = v___y_3591_;
v___y_3554_ = v___y_3597_;
v___y_3555_ = v___y_3595_;
v___y_3556_ = v___y_3592_;
v___y_3557_ = v___y_3590_;
v___y_3558_ = v_extraIds_3589_;
v___y_3559_ = v___y_3594_;
v___y_3560_ = v___y_3593_;
v___y_3561_ = v___x_3598_;
goto v___jp_3551_;
}
else
{
lean_object* v_val_3599_; lean_object* v___x_3600_; 
v_val_3599_ = lean_ctor_get(v___y_3588_, 0);
lean_inc(v_val_3599_);
lean_dec_ref(v___y_3588_);
v___x_3600_ = l_Lean_TSyntax_getId(v_val_3599_);
lean_dec(v_val_3599_);
v___y_3552_ = v___y_3596_;
v___y_3553_ = v___y_3591_;
v___y_3554_ = v___y_3597_;
v___y_3555_ = v___y_3595_;
v___y_3556_ = v___y_3592_;
v___y_3557_ = v___y_3590_;
v___y_3558_ = v_extraIds_3589_;
v___y_3559_ = v___y_3594_;
v___y_3560_ = v___y_3593_;
v___y_3561_ = v___x_3600_;
goto v___jp_3551_;
}
}
v___jp_3601_:
{
size_t v_sz_3612_; size_t v___x_3613_; lean_object* v___x_3614_; 
v_sz_3612_ = lean_array_size(v___y_3611_);
v___x_3613_ = ((size_t)0ULL);
v___x_3614_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__3(v_sz_3612_, v___x_3613_, v___y_3611_);
if (lean_obj_tag(v___x_3614_) == 0)
{
lean_object* v___x_3615_; 
lean_dec(v___y_3604_);
v___x_3615_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro_spec__0___redArg();
return v___x_3615_;
}
else
{
v___y_3588_ = v___y_3604_;
v_extraIds_3589_ = v___x_3614_;
v___y_3590_ = v___y_3603_;
v___y_3591_ = v___y_3602_;
v___y_3592_ = v___y_3609_;
v___y_3593_ = v___y_3605_;
v___y_3594_ = v___y_3610_;
v___y_3595_ = v___y_3607_;
v___y_3596_ = v___y_3606_;
v___y_3597_ = v___y_3608_;
goto v___jp_3587_;
}
}
v___jp_3617_:
{
lean_object* v___x_3627_; lean_object* v___x_3628_; uint8_t v___x_3629_; 
v___x_3627_ = lean_unsigned_to_nat(2u);
v___x_3628_ = l_Lean_Syntax_getArg(v_stx_3426_, v___x_3627_);
lean_dec(v_stx_3426_);
v___x_3629_ = l_Lean_Syntax_isNone(v___x_3628_);
if (v___x_3629_ == 0)
{
lean_object* v___x_3630_; uint8_t v___x_3631_; 
v___x_3630_ = lean_unsigned_to_nat(3u);
lean_inc(v___x_3628_);
v___x_3631_ = l_Lean_Syntax_matchesNull(v___x_3628_, v___x_3630_);
if (v___x_3631_ == 0)
{
lean_object* v___x_3632_; 
lean_dec(v___x_3628_);
lean_dec(v_variantId_x3f_3618_);
v___x_3632_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro_spec__0___redArg();
return v___x_3632_;
}
else
{
lean_object* v___x_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; uint8_t v___x_3637_; 
v___x_3633_ = l_Lean_Syntax_getArg(v___x_3628_, v___x_3616_);
lean_dec(v___x_3628_);
v___x_3634_ = l_Lean_Syntax_getArgs(v___x_3633_);
lean_dec(v___x_3633_);
v___x_3635_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__7));
v___x_3636_ = lean_array_get_size(v___x_3634_);
v___x_3637_ = lean_nat_dec_lt(v___x_3550_, v___x_3636_);
if (v___x_3637_ == 0)
{
lean_dec_ref(v___x_3634_);
v___y_3602_ = v___y_3620_;
v___y_3603_ = v___y_3619_;
v___y_3604_ = v_variantId_x3f_3618_;
v___y_3605_ = v___y_3622_;
v___y_3606_ = v___y_3625_;
v___y_3607_ = v___y_3624_;
v___y_3608_ = v___y_3626_;
v___y_3609_ = v___y_3621_;
v___y_3610_ = v___y_3623_;
v___y_3611_ = v___x_3635_;
goto v___jp_3601_;
}
else
{
lean_object* v___x_3638_; lean_object* v___x_3639_; uint8_t v___x_3640_; 
v___x_3638_ = lean_box(v___x_3631_);
v___x_3639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3639_, 0, v___x_3638_);
lean_ctor_set(v___x_3639_, 1, v___x_3635_);
v___x_3640_ = lean_nat_dec_le(v___x_3636_, v___x_3636_);
if (v___x_3640_ == 0)
{
if (v___x_3637_ == 0)
{
lean_dec_ref(v___x_3639_);
lean_dec_ref(v___x_3634_);
v___y_3602_ = v___y_3620_;
v___y_3603_ = v___y_3619_;
v___y_3604_ = v_variantId_x3f_3618_;
v___y_3605_ = v___y_3622_;
v___y_3606_ = v___y_3625_;
v___y_3607_ = v___y_3624_;
v___y_3608_ = v___y_3626_;
v___y_3609_ = v___y_3621_;
v___y_3610_ = v___y_3623_;
v___y_3611_ = v___x_3635_;
goto v___jp_3601_;
}
else
{
size_t v___x_3641_; size_t v___x_3642_; lean_object* v___x_3643_; lean_object* v_snd_3644_; 
v___x_3641_ = ((size_t)0ULL);
v___x_3642_ = lean_usize_of_nat(v___x_3636_);
v___x_3643_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__4(v___x_3631_, v___x_3629_, v___x_3634_, v___x_3641_, v___x_3642_, v___x_3639_);
lean_dec_ref(v___x_3634_);
v_snd_3644_ = lean_ctor_get(v___x_3643_, 1);
lean_inc(v_snd_3644_);
lean_dec_ref(v___x_3643_);
v___y_3602_ = v___y_3620_;
v___y_3603_ = v___y_3619_;
v___y_3604_ = v_variantId_x3f_3618_;
v___y_3605_ = v___y_3622_;
v___y_3606_ = v___y_3625_;
v___y_3607_ = v___y_3624_;
v___y_3608_ = v___y_3626_;
v___y_3609_ = v___y_3621_;
v___y_3610_ = v___y_3623_;
v___y_3611_ = v_snd_3644_;
goto v___jp_3601_;
}
}
else
{
size_t v___x_3645_; size_t v___x_3646_; lean_object* v___x_3647_; lean_object* v_snd_3648_; 
v___x_3645_ = ((size_t)0ULL);
v___x_3646_ = lean_usize_of_nat(v___x_3636_);
v___x_3647_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__4(v___x_3631_, v___x_3629_, v___x_3634_, v___x_3645_, v___x_3646_, v___x_3639_);
lean_dec_ref(v___x_3634_);
v_snd_3648_ = lean_ctor_get(v___x_3647_, 1);
lean_inc(v_snd_3648_);
lean_dec_ref(v___x_3647_);
v___y_3602_ = v___y_3620_;
v___y_3603_ = v___y_3619_;
v___y_3604_ = v_variantId_x3f_3618_;
v___y_3605_ = v___y_3622_;
v___y_3606_ = v___y_3625_;
v___y_3607_ = v___y_3624_;
v___y_3608_ = v___y_3626_;
v___y_3609_ = v___y_3621_;
v___y_3610_ = v___y_3623_;
v___y_3611_ = v_snd_3648_;
goto v___jp_3601_;
}
}
}
}
else
{
lean_object* v___x_3649_; 
lean_dec(v___x_3628_);
v___x_3649_ = lean_box(0);
v___y_3588_ = v_variantId_x3f_3618_;
v_extraIds_3589_ = v___x_3649_;
v___y_3590_ = v___y_3619_;
v___y_3591_ = v___y_3620_;
v___y_3592_ = v___y_3621_;
v___y_3593_ = v___y_3622_;
v___y_3594_ = v___y_3623_;
v___y_3595_ = v___y_3624_;
v___y_3596_ = v___y_3625_;
v___y_3597_ = v___y_3626_;
goto v___jp_3587_;
}
}
}
}
}
else
{
lean_dec(v_stx_3426_);
return v___x_3543_;
}
v___jp_3436_:
{
lean_object* v___x_3449_; 
v___x_3449_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabVariant(v___y_3445_, v___y_3447_, v___y_3443_, v___y_3439_, v___y_3442_, v___y_3446_, v___y_3444_, v___y_3441_, v___y_3438_, v___y_3440_);
lean_dec_ref(v___y_3447_);
if (lean_obj_tag(v___x_3449_) == 0)
{
lean_object* v_a_3450_; lean_object* v_fst_3451_; lean_object* v_snd_3452_; lean_object* v___x_3453_; 
v_a_3450_ = lean_ctor_get(v___x_3449_, 0);
lean_inc(v_a_3450_);
lean_dec_ref(v___x_3449_);
v_fst_3451_ = lean_ctor_get(v_a_3450_, 0);
lean_inc(v_fst_3451_);
v_snd_3452_ = lean_ctor_get(v_a_3450_, 1);
lean_inc(v_snd_3452_);
lean_dec(v_a_3450_);
v___x_3453_ = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(v___y_3439_, v___y_3444_, v___y_3441_, v___y_3438_, v___y_3440_);
if (lean_obj_tag(v___x_3453_) == 0)
{
lean_object* v_a_3454_; lean_object* v_toGoalState_3455_; lean_object* v_mvarId_3456_; lean_object* v___x_3458_; uint8_t v_isShared_3459_; uint8_t v_isSharedCheck_3526_; 
v_a_3454_ = lean_ctor_get(v___x_3453_, 0);
lean_inc(v_a_3454_);
lean_dec_ref(v___x_3453_);
v_toGoalState_3455_ = lean_ctor_get(v_a_3454_, 0);
v_mvarId_3456_ = lean_ctor_get(v_a_3454_, 1);
v_isSharedCheck_3526_ = !lean_is_exclusive(v_a_3454_);
if (v_isSharedCheck_3526_ == 0)
{
v___x_3458_ = v_a_3454_;
v_isShared_3459_ = v_isSharedCheck_3526_;
goto v_resetjp_3457_;
}
else
{
lean_inc(v_mvarId_3456_);
lean_inc(v_toGoalState_3455_);
lean_dec(v_a_3454_);
v___x_3458_ = lean_box(0);
v_isShared_3459_ = v_isSharedCheck_3526_;
goto v_resetjp_3457_;
}
v_resetjp_3457_:
{
lean_object* v___f_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; 
lean_inc_n(v_mvarId_3456_, 2);
v___f_3460_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__0___boxed), 14, 4);
lean_closure_set(v___f_3460_, 0, v_mvarId_3456_);
lean_closure_set(v___f_3460_, 1, v_fst_3451_);
lean_closure_set(v___f_3460_, 2, v_snd_3452_);
lean_closure_set(v___f_3460_, 3, v___y_3448_);
v___x_3461_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__0___boxed), 13, 3);
lean_closure_set(v___x_3461_, 0, lean_box(0));
lean_closure_set(v___x_3461_, 1, v_mvarId_3456_);
lean_closure_set(v___x_3461_, 2, v___f_3460_);
v___x_3462_ = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(v___x_3461_, v___y_3443_, v___y_3439_, v___y_3444_, v___y_3441_, v___y_3438_, v___y_3440_);
if (lean_obj_tag(v___x_3462_) == 0)
{
lean_object* v_a_3463_; lean_object* v_fst_3464_; lean_object* v_snd_3465_; lean_object* v___x_3467_; uint8_t v_isShared_3468_; uint8_t v_isSharedCheck_3517_; 
v_a_3463_ = lean_ctor_get(v___x_3462_, 0);
lean_inc(v_a_3463_);
lean_dec_ref(v___x_3462_);
v_fst_3464_ = lean_ctor_get(v_a_3463_, 0);
v_snd_3465_ = lean_ctor_get(v_a_3463_, 1);
v_isSharedCheck_3517_ = !lean_is_exclusive(v_a_3463_);
if (v_isSharedCheck_3517_ == 0)
{
v___x_3467_ = v_a_3463_;
v_isShared_3468_ = v_isSharedCheck_3517_;
goto v_resetjp_3466_;
}
else
{
lean_inc(v_snd_3465_);
lean_inc(v_fst_3464_);
lean_dec(v_a_3463_);
v___x_3467_ = lean_box(0);
v_isShared_3468_ = v_isSharedCheck_3517_;
goto v_resetjp_3466_;
}
v_resetjp_3466_:
{
lean_object* v___x_3469_; lean_object* v_cache_3470_; lean_object* v_symState_3471_; lean_object* v_grindState_3472_; lean_object* v_goals_3473_; lean_object* v___x_3475_; uint8_t v_isShared_3476_; uint8_t v_isSharedCheck_3516_; 
v___x_3469_ = lean_st_ref_take(v___y_3439_);
v_cache_3470_ = lean_ctor_get(v___x_3469_, 3);
v_symState_3471_ = lean_ctor_get(v___x_3469_, 0);
v_grindState_3472_ = lean_ctor_get(v___x_3469_, 1);
v_goals_3473_ = lean_ctor_get(v___x_3469_, 2);
v_isSharedCheck_3516_ = !lean_is_exclusive(v___x_3469_);
if (v_isSharedCheck_3516_ == 0)
{
v___x_3475_ = v___x_3469_;
v_isShared_3476_ = v_isSharedCheck_3516_;
goto v_resetjp_3474_;
}
else
{
lean_inc(v_cache_3470_);
lean_inc(v_goals_3473_);
lean_inc(v_grindState_3472_);
lean_inc(v_symState_3471_);
lean_dec(v___x_3469_);
v___x_3475_ = lean_box(0);
v_isShared_3476_ = v_isSharedCheck_3516_;
goto v_resetjp_3474_;
}
v_resetjp_3474_:
{
lean_object* v_backwardRuleName_3477_; lean_object* v_backwardRuleSyntax_3478_; lean_object* v_simpState_3479_; lean_object* v___x_3481_; uint8_t v_isShared_3482_; uint8_t v_isSharedCheck_3515_; 
v_backwardRuleName_3477_ = lean_ctor_get(v_cache_3470_, 0);
v_backwardRuleSyntax_3478_ = lean_ctor_get(v_cache_3470_, 1);
v_simpState_3479_ = lean_ctor_get(v_cache_3470_, 2);
v_isSharedCheck_3515_ = !lean_is_exclusive(v_cache_3470_);
if (v_isSharedCheck_3515_ == 0)
{
v___x_3481_ = v_cache_3470_;
v_isShared_3482_ = v_isSharedCheck_3515_;
goto v_resetjp_3480_;
}
else
{
lean_inc(v_simpState_3479_);
lean_inc(v_backwardRuleSyntax_3478_);
lean_inc(v_backwardRuleName_3477_);
lean_dec(v_cache_3470_);
v___x_3481_ = lean_box(0);
v_isShared_3482_ = v_isSharedCheck_3515_;
goto v_resetjp_3480_;
}
v_resetjp_3480_:
{
lean_object* v___x_3483_; lean_object* v___x_3485_; 
v___x_3483_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1___redArg(v_simpState_3479_, v___y_3437_, v_snd_3465_);
if (v_isShared_3482_ == 0)
{
lean_ctor_set(v___x_3481_, 2, v___x_3483_);
v___x_3485_ = v___x_3481_;
goto v_reusejp_3484_;
}
else
{
lean_object* v_reuseFailAlloc_3514_; 
v_reuseFailAlloc_3514_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3514_, 0, v_backwardRuleName_3477_);
lean_ctor_set(v_reuseFailAlloc_3514_, 1, v_backwardRuleSyntax_3478_);
lean_ctor_set(v_reuseFailAlloc_3514_, 2, v___x_3483_);
v___x_3485_ = v_reuseFailAlloc_3514_;
goto v_reusejp_3484_;
}
v_reusejp_3484_:
{
lean_object* v___x_3487_; 
if (v_isShared_3476_ == 0)
{
lean_ctor_set(v___x_3475_, 3, v___x_3485_);
v___x_3487_ = v___x_3475_;
goto v_reusejp_3486_;
}
else
{
lean_object* v_reuseFailAlloc_3513_; 
v_reuseFailAlloc_3513_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3513_, 0, v_symState_3471_);
lean_ctor_set(v_reuseFailAlloc_3513_, 1, v_grindState_3472_);
lean_ctor_set(v_reuseFailAlloc_3513_, 2, v_goals_3473_);
lean_ctor_set(v_reuseFailAlloc_3513_, 3, v___x_3485_);
v___x_3487_ = v_reuseFailAlloc_3513_;
goto v_reusejp_3486_;
}
v_reusejp_3486_:
{
lean_object* v___x_3488_; lean_object* v___f_3489_; lean_object* v___x_3490_; 
v___x_3488_ = lean_st_ref_set(v___y_3439_, v___x_3487_);
v___f_3489_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__1___boxed), 12, 2);
lean_closure_set(v___f_3489_, 0, v_fst_3464_);
lean_closure_set(v___f_3489_, 1, v_mvarId_3456_);
v___x_3490_ = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(v___f_3489_, v___y_3443_, v___y_3439_, v___y_3444_, v___y_3441_, v___y_3438_, v___y_3440_);
if (lean_obj_tag(v___x_3490_) == 0)
{
lean_object* v_a_3491_; 
v_a_3491_ = lean_ctor_get(v___x_3490_, 0);
lean_inc(v_a_3491_);
lean_dec_ref(v___x_3490_);
switch(lean_obj_tag(v_a_3491_))
{
case 0:
{
lean_object* v___x_3492_; lean_object* v___x_3493_; 
lean_del_object(v___x_3467_);
lean_del_object(v___x_3458_);
lean_dec_ref(v_toGoalState_3455_);
v___x_3492_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__1, &l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__1);
v___x_3493_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_ensureSym_spec__0___redArg(v___x_3492_, v___y_3444_, v___y_3441_, v___y_3438_, v___y_3440_);
return v___x_3493_;
}
case 1:
{
lean_object* v___x_3494_; lean_object* v___x_3495_; 
lean_del_object(v___x_3467_);
lean_del_object(v___x_3458_);
lean_dec_ref(v_toGoalState_3455_);
v___x_3494_ = lean_box(0);
v___x_3495_ = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(v___x_3494_, v___y_3439_, v___y_3444_, v___y_3441_, v___y_3438_, v___y_3440_);
return v___x_3495_;
}
default: 
{
lean_object* v_mvarId_3496_; lean_object* v___x_3498_; 
v_mvarId_3496_ = lean_ctor_get(v_a_3491_, 0);
lean_inc(v_mvarId_3496_);
lean_dec_ref(v_a_3491_);
if (v_isShared_3459_ == 0)
{
lean_ctor_set(v___x_3458_, 1, v_mvarId_3496_);
v___x_3498_ = v___x_3458_;
goto v_reusejp_3497_;
}
else
{
lean_object* v_reuseFailAlloc_3504_; 
v_reuseFailAlloc_3504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3504_, 0, v_toGoalState_3455_);
lean_ctor_set(v_reuseFailAlloc_3504_, 1, v_mvarId_3496_);
v___x_3498_ = v_reuseFailAlloc_3504_;
goto v_reusejp_3497_;
}
v_reusejp_3497_:
{
lean_object* v___x_3499_; lean_object* v___x_3501_; 
v___x_3499_ = lean_box(0);
if (v_isShared_3468_ == 0)
{
lean_ctor_set_tag(v___x_3467_, 1);
lean_ctor_set(v___x_3467_, 1, v___x_3499_);
lean_ctor_set(v___x_3467_, 0, v___x_3498_);
v___x_3501_ = v___x_3467_;
goto v_reusejp_3500_;
}
else
{
lean_object* v_reuseFailAlloc_3503_; 
v_reuseFailAlloc_3503_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3503_, 0, v___x_3498_);
lean_ctor_set(v_reuseFailAlloc_3503_, 1, v___x_3499_);
v___x_3501_ = v_reuseFailAlloc_3503_;
goto v_reusejp_3500_;
}
v_reusejp_3500_:
{
lean_object* v___x_3502_; 
v___x_3502_ = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(v___x_3501_, v___y_3439_, v___y_3444_, v___y_3441_, v___y_3438_, v___y_3440_);
return v___x_3502_;
}
}
}
}
}
else
{
lean_object* v_a_3505_; lean_object* v___x_3507_; uint8_t v_isShared_3508_; uint8_t v_isSharedCheck_3512_; 
lean_del_object(v___x_3467_);
lean_del_object(v___x_3458_);
lean_dec_ref(v_toGoalState_3455_);
v_a_3505_ = lean_ctor_get(v___x_3490_, 0);
v_isSharedCheck_3512_ = !lean_is_exclusive(v___x_3490_);
if (v_isSharedCheck_3512_ == 0)
{
v___x_3507_ = v___x_3490_;
v_isShared_3508_ = v_isSharedCheck_3512_;
goto v_resetjp_3506_;
}
else
{
lean_inc(v_a_3505_);
lean_dec(v___x_3490_);
v___x_3507_ = lean_box(0);
v_isShared_3508_ = v_isSharedCheck_3512_;
goto v_resetjp_3506_;
}
v_resetjp_3506_:
{
lean_object* v___x_3510_; 
if (v_isShared_3508_ == 0)
{
v___x_3510_ = v___x_3507_;
goto v_reusejp_3509_;
}
else
{
lean_object* v_reuseFailAlloc_3511_; 
v_reuseFailAlloc_3511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3511_, 0, v_a_3505_);
v___x_3510_ = v_reuseFailAlloc_3511_;
goto v_reusejp_3509_;
}
v_reusejp_3509_:
{
return v___x_3510_;
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
lean_object* v_a_3518_; lean_object* v___x_3520_; uint8_t v_isShared_3521_; uint8_t v_isSharedCheck_3525_; 
lean_del_object(v___x_3458_);
lean_dec(v_mvarId_3456_);
lean_dec_ref(v_toGoalState_3455_);
lean_dec_ref(v___y_3437_);
v_a_3518_ = lean_ctor_get(v___x_3462_, 0);
v_isSharedCheck_3525_ = !lean_is_exclusive(v___x_3462_);
if (v_isSharedCheck_3525_ == 0)
{
v___x_3520_ = v___x_3462_;
v_isShared_3521_ = v_isSharedCheck_3525_;
goto v_resetjp_3519_;
}
else
{
lean_inc(v_a_3518_);
lean_dec(v___x_3462_);
v___x_3520_ = lean_box(0);
v_isShared_3521_ = v_isSharedCheck_3525_;
goto v_resetjp_3519_;
}
v_resetjp_3519_:
{
lean_object* v___x_3523_; 
if (v_isShared_3521_ == 0)
{
v___x_3523_ = v___x_3520_;
goto v_reusejp_3522_;
}
else
{
lean_object* v_reuseFailAlloc_3524_; 
v_reuseFailAlloc_3524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3524_, 0, v_a_3518_);
v___x_3523_ = v_reuseFailAlloc_3524_;
goto v_reusejp_3522_;
}
v_reusejp_3522_:
{
return v___x_3523_;
}
}
}
}
}
else
{
lean_object* v_a_3527_; lean_object* v___x_3529_; uint8_t v_isShared_3530_; uint8_t v_isSharedCheck_3534_; 
lean_dec(v_snd_3452_);
lean_dec(v_fst_3451_);
lean_dec_ref(v___y_3448_);
lean_dec_ref(v___y_3437_);
v_a_3527_ = lean_ctor_get(v___x_3453_, 0);
v_isSharedCheck_3534_ = !lean_is_exclusive(v___x_3453_);
if (v_isSharedCheck_3534_ == 0)
{
v___x_3529_ = v___x_3453_;
v_isShared_3530_ = v_isSharedCheck_3534_;
goto v_resetjp_3528_;
}
else
{
lean_inc(v_a_3527_);
lean_dec(v___x_3453_);
v___x_3529_ = lean_box(0);
v_isShared_3530_ = v_isSharedCheck_3534_;
goto v_resetjp_3528_;
}
v_resetjp_3528_:
{
lean_object* v___x_3532_; 
if (v_isShared_3530_ == 0)
{
v___x_3532_ = v___x_3529_;
goto v_reusejp_3531_;
}
else
{
lean_object* v_reuseFailAlloc_3533_; 
v_reuseFailAlloc_3533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3533_, 0, v_a_3527_);
v___x_3532_ = v_reuseFailAlloc_3533_;
goto v_reusejp_3531_;
}
v_reusejp_3531_:
{
return v___x_3532_;
}
}
}
}
else
{
lean_object* v_a_3535_; lean_object* v___x_3537_; uint8_t v_isShared_3538_; uint8_t v_isSharedCheck_3542_; 
lean_dec_ref(v___y_3448_);
lean_dec_ref(v___y_3437_);
v_a_3535_ = lean_ctor_get(v___x_3449_, 0);
v_isSharedCheck_3542_ = !lean_is_exclusive(v___x_3449_);
if (v_isSharedCheck_3542_ == 0)
{
v___x_3537_ = v___x_3449_;
v_isShared_3538_ = v_isSharedCheck_3542_;
goto v_resetjp_3536_;
}
else
{
lean_inc(v_a_3535_);
lean_dec(v___x_3449_);
v___x_3537_ = lean_box(0);
v_isShared_3538_ = v_isSharedCheck_3542_;
goto v_resetjp_3536_;
}
v_resetjp_3536_:
{
lean_object* v___x_3540_; 
if (v_isShared_3538_ == 0)
{
v___x_3540_ = v___x_3537_;
goto v_reusejp_3539_;
}
else
{
lean_object* v_reuseFailAlloc_3541_; 
v_reuseFailAlloc_3541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3541_, 0, v_a_3535_);
v___x_3540_ = v_reuseFailAlloc_3541_;
goto v_reusejp_3539_;
}
v_reusejp_3539_:
{
return v___x_3540_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___boxed(lean_object* v_stx_3661_, lean_object* v___y_3662_, lean_object* v___y_3663_, lean_object* v___y_3664_, lean_object* v___y_3665_, lean_object* v___y_3666_, lean_object* v___y_3667_, lean_object* v___y_3668_, lean_object* v___y_3669_, lean_object* v___y_3670_){
_start:
{
lean_object* v_res_3671_; 
v_res_3671_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2(v_stx_3661_, v___y_3662_, v___y_3663_, v___y_3664_, v___y_3665_, v___y_3666_, v___y_3667_, v___y_3668_, v___y_3669_);
lean_dec(v___y_3669_);
lean_dec_ref(v___y_3668_);
lean_dec(v___y_3667_);
lean_dec_ref(v___y_3666_);
lean_dec(v___y_3665_);
lean_dec_ref(v___y_3664_);
lean_dec(v___y_3663_);
lean_dec_ref(v___y_3662_);
return v_res_3671_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp(lean_object* v_stx_3672_, lean_object* v_a_3673_, lean_object* v_a_3674_, lean_object* v_a_3675_, lean_object* v_a_3676_, lean_object* v_a_3677_, lean_object* v_a_3678_, lean_object* v_a_3679_, lean_object* v_a_3680_){
_start:
{
lean_object* v___f_3682_; lean_object* v___x_3683_; 
v___f_3682_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___boxed), 10, 1);
lean_closure_set(v___f_3682_, 0, v_stx_3672_);
v___x_3683_ = l_Lean_Elab_Tactic_Grind_withMainContext___redArg(v___f_3682_, v_a_3673_, v_a_3674_, v_a_3675_, v_a_3676_, v_a_3677_, v_a_3678_, v_a_3679_, v_a_3680_);
return v___x_3683_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___boxed(lean_object* v_stx_3684_, lean_object* v_a_3685_, lean_object* v_a_3686_, lean_object* v_a_3687_, lean_object* v_a_3688_, lean_object* v_a_3689_, lean_object* v_a_3690_, lean_object* v_a_3691_, lean_object* v_a_3692_, lean_object* v_a_3693_){
_start:
{
lean_object* v_res_3694_; 
v_res_3694_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp(v_stx_3684_, v_a_3685_, v_a_3686_, v_a_3687_, v_a_3688_, v_a_3689_, v_a_3690_, v_a_3691_, v_a_3692_);
lean_dec(v_a_3692_);
lean_dec_ref(v_a_3691_);
lean_dec(v_a_3690_);
lean_dec_ref(v_a_3689_);
lean_dec(v_a_3688_);
lean_dec_ref(v_a_3687_);
lean_dec(v_a_3686_);
lean_dec_ref(v_a_3685_);
return v_res_3694_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1(lean_object* v_00_u03b2_3695_, lean_object* v_m_3696_, lean_object* v_a_3697_, lean_object* v_b_3698_){
_start:
{
lean_object* v___x_3699_; 
v___x_3699_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1___redArg(v_m_3696_, v_a_3697_, v_b_3698_);
return v___x_3699_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__2(lean_object* v_00_u03b2_3700_, lean_object* v_m_3701_, lean_object* v_a_3702_){
_start:
{
lean_object* v___x_3703_; 
v___x_3703_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__2___redArg(v_m_3701_, v_a_3702_);
return v___x_3703_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__2___boxed(lean_object* v_00_u03b2_3704_, lean_object* v_m_3705_, lean_object* v_a_3706_){
_start:
{
lean_object* v_res_3707_; 
v_res_3707_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__2(v_00_u03b2_3704_, v_m_3705_, v_a_3706_);
lean_dec_ref(v_a_3706_);
lean_dec_ref(v_m_3705_);
return v_res_3707_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__1(lean_object* v_00_u03b2_3708_, lean_object* v_a_3709_, lean_object* v_x_3710_){
_start:
{
uint8_t v___x_3711_; 
v___x_3711_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__1___redArg(v_a_3709_, v_x_3710_);
return v___x_3711_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__1___boxed(lean_object* v_00_u03b2_3712_, lean_object* v_a_3713_, lean_object* v_x_3714_){
_start:
{
uint8_t v_res_3715_; lean_object* v_r_3716_; 
v_res_3715_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__1(v_00_u03b2_3712_, v_a_3713_, v_x_3714_);
lean_dec(v_x_3714_);
lean_dec_ref(v_a_3713_);
v_r_3716_ = lean_box(v_res_3715_);
return v_r_3716_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__2(lean_object* v_00_u03b2_3717_, lean_object* v_data_3718_){
_start:
{
lean_object* v___x_3719_; 
v___x_3719_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__2___redArg(v_data_3718_);
return v___x_3719_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__3(lean_object* v_00_u03b2_3720_, lean_object* v_a_3721_, lean_object* v_b_3722_, lean_object* v_x_3723_){
_start:
{
lean_object* v___x_3724_; 
v___x_3724_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__3___redArg(v_a_3721_, v_b_3722_, v_x_3723_);
return v___x_3724_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__2_spec__5(lean_object* v_00_u03b2_3725_, lean_object* v_a_3726_, lean_object* v_x_3727_){
_start:
{
lean_object* v___x_3728_; 
v___x_3728_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__2_spec__5___redArg(v_a_3726_, v_x_3727_);
return v___x_3728_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__2_spec__5___boxed(lean_object* v_00_u03b2_3729_, lean_object* v_a_3730_, lean_object* v_x_3731_){
_start:
{
lean_object* v_res_3732_; 
v_res_3732_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__2_spec__5(v_00_u03b2_3729_, v_a_3730_, v_x_3731_);
lean_dec(v_x_3731_);
lean_dec_ref(v_a_3730_);
return v_res_3732_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_3733_, lean_object* v_i_3734_, lean_object* v_source_3735_, lean_object* v_target_3736_){
_start:
{
lean_object* v___x_3737_; 
v___x_3737_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__2_spec__3___redArg(v_i_3734_, v_source_3735_, v_target_3736_);
return v___x_3737_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__2_spec__3_spec__7(lean_object* v_00_u03b2_3738_, lean_object* v_x_3739_, lean_object* v_x_3740_){
_start:
{
lean_object* v___x_3741_; 
v___x_3741_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__2_spec__3_spec__7___redArg(v_x_3739_, v_x_3740_);
return v___x_3741_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp__1(){
_start:
{
lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; 
v___x_3747_ = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
v___x_3748_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__3));
v___x_3749_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp__1___closed__1));
v___x_3750_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___boxed), 10, 0);
v___x_3751_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3747_, v___x_3748_, v___x_3749_, v___x_3750_);
return v___x_3751_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp__1___boxed(lean_object* v_a_3752_){
_start:
{
lean_object* v_res_3753_; 
v_res_3753_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp__1();
return v_res_3753_;
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
