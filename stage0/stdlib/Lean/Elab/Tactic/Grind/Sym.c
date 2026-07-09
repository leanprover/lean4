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
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
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
lean_object* l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_tactic_hygienic;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_intros___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_liftSymM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_internalizeAll___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_MVarId_byContra_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_intro1Core(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_exfalso(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFalse(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_saveState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_SavedState_restore___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkSimpDefaultMethods___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkSimpDefaultMethods___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkSimpDefaultMethods___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_Simp_simp___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkSimpDefaultMethods___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkSimpDefaultMethods___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkSimpDefaultMethods___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkSimpDefaultMethods___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkSimpDefaultMethods___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkSimpDefaultMethods___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkSimpDefaultMethods___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkSimpDefaultMethods___lam__0___boxed, .m_arity = 12, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkSimpDefaultMethods___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkSimpDefaultMethods___closed__0_value;
static const lean_closure_object l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkSimpDefaultMethods___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkSimpDefaultMethods___lam__2___boxed, .m_arity = 12, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkSimpDefaultMethods___closed__0_value)} };
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkSimpDefaultMethods___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkSimpDefaultMethods___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkSimpDefaultMethods(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkSimpDefaultMethods___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_21_; lean_object* v_env_22_; lean_object* v___x_23_; lean_object* v_mctx_24_; lean_object* v_lctx_25_; lean_object* v_options_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; 
v___x_21_ = lean_st_ref_get(v___y_19_);
v_env_22_ = lean_ctor_get(v___x_21_, 0);
lean_inc_ref(v_env_22_);
lean_dec(v___x_21_);
v___x_23_ = lean_st_ref_get(v___y_17_);
v_mctx_24_ = lean_ctor_get(v___x_23_, 0);
lean_inc_ref(v_mctx_24_);
lean_dec(v___x_23_);
v_lctx_25_ = lean_ctor_get(v___y_16_, 2);
v_options_26_ = lean_ctor_get(v___y_18_, 2);
lean_inc_ref(v_options_26_);
lean_inc_ref(v_lctx_25_);
v___x_27_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_27_, 0, v_env_22_);
lean_ctor_set(v___x_27_, 1, v_mctx_24_);
lean_ctor_set(v___x_27_, 2, v_lctx_25_);
lean_ctor_set(v___x_27_, 3, v_options_26_);
v___x_28_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_28_, 0, v___x_27_);
lean_ctor_set(v___x_28_, 1, v_msgData_15_);
v___x_29_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_29_, 0, v___x_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__2_spec__2___boxed(lean_object* v_msgData_30_, lean_object* v___y_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__2_spec__2(v_msgData_30_, v___y_31_, v___y_32_, v___y_33_, v___y_34_);
lean_dec(v___y_34_);
lean_dec_ref(v___y_33_);
lean_dec(v___y_32_);
lean_dec_ref(v___y_31_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__2___redArg(lean_object* v_msg_37_, lean_object* v___y_38_, lean_object* v___y_39_, lean_object* v___y_40_, lean_object* v___y_41_){
_start:
{
lean_object* v_ref_43_; lean_object* v___x_44_; lean_object* v_a_45_; lean_object* v___x_47_; uint8_t v_isShared_48_; uint8_t v_isSharedCheck_53_; 
v_ref_43_ = lean_ctor_get(v___y_40_, 5);
v___x_44_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__2_spec__2(v_msg_37_, v___y_38_, v___y_39_, v___y_40_, v___y_41_);
v_a_45_ = lean_ctor_get(v___x_44_, 0);
v_isSharedCheck_53_ = !lean_is_exclusive(v___x_44_);
if (v_isSharedCheck_53_ == 0)
{
v___x_47_ = v___x_44_;
v_isShared_48_ = v_isSharedCheck_53_;
goto v_resetjp_46_;
}
else
{
lean_inc(v_a_45_);
lean_dec(v___x_44_);
v___x_47_ = lean_box(0);
v_isShared_48_ = v_isSharedCheck_53_;
goto v_resetjp_46_;
}
v_resetjp_46_:
{
lean_object* v___x_49_; lean_object* v___x_51_; 
lean_inc(v_ref_43_);
v___x_49_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_49_, 0, v_ref_43_);
lean_ctor_set(v___x_49_, 1, v_a_45_);
if (v_isShared_48_ == 0)
{
lean_ctor_set_tag(v___x_47_, 1);
lean_ctor_set(v___x_47_, 0, v___x_49_);
v___x_51_ = v___x_47_;
goto v_reusejp_50_;
}
else
{
lean_object* v_reuseFailAlloc_52_; 
v_reuseFailAlloc_52_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_52_, 0, v___x_49_);
v___x_51_ = v_reuseFailAlloc_52_;
goto v_reusejp_50_;
}
v_reusejp_50_:
{
return v___x_51_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__2___redArg___boxed(lean_object* v_msg_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__2___redArg(v_msg_54_, v___y_55_, v___y_56_, v___y_57_, v___y_58_);
lean_dec(v___y_58_);
lean_dec_ref(v___y_57_);
lean_dec(v___y_56_);
lean_dec_ref(v___y_55_);
return v_res_60_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__1___redArg(size_t v_sz_72_, size_t v_i_73_, lean_object* v_bs_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_){
_start:
{
uint8_t v___x_79_; 
v___x_79_ = lean_usize_dec_lt(v_i_73_, v_sz_72_);
if (v___x_79_ == 0)
{
lean_object* v___x_80_; 
v___x_80_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_80_, 0, v_bs_74_);
return v___x_80_;
}
else
{
lean_object* v_v_81_; lean_object* v___x_82_; lean_object* v_bs_x27_83_; lean_object* v_a_85_; lean_object* v___y_91_; lean_object* v___x_101_; uint8_t v___x_102_; 
v_v_81_ = lean_array_uget(v_bs_74_, v_i_73_);
v___x_82_ = lean_unsigned_to_nat(0u);
v_bs_x27_83_ = lean_array_uset(v_bs_74_, v_i_73_, v___x_82_);
v___x_101_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__1___redArg___closed__2));
lean_inc(v_v_81_);
v___x_102_ = l_Lean_Syntax_isOfKind(v_v_81_, v___x_101_);
if (v___x_102_ == 0)
{
lean_object* v___x_103_; lean_object* v___x_104_; 
lean_dec(v_v_81_);
v___x_103_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__1___redArg___closed__4));
v___x_104_ = l_Lean_Meta_mkFreshBinderNameForTactic___redArg(v___x_103_, v___y_75_, v___y_76_, v___y_77_);
v___y_91_ = v___x_104_;
goto v___jp_90_;
}
else
{
lean_object* v___x_105_; lean_object* v___x_106_; uint8_t v___x_107_; 
v___x_105_ = l_Lean_Syntax_getArg(v_v_81_, v___x_82_);
lean_dec(v_v_81_);
v___x_106_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__1___redArg___closed__6));
lean_inc(v___x_105_);
v___x_107_ = l_Lean_Syntax_isOfKind(v___x_105_, v___x_106_);
if (v___x_107_ == 0)
{
lean_object* v___x_108_; lean_object* v___x_109_; 
lean_dec(v___x_105_);
v___x_108_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__1___redArg___closed__4));
v___x_109_ = l_Lean_Meta_mkFreshBinderNameForTactic___redArg(v___x_108_, v___y_75_, v___y_76_, v___y_77_);
v___y_91_ = v___x_109_;
goto v___jp_90_;
}
else
{
lean_object* v___x_110_; 
v___x_110_ = l_Lean_TSyntax_getId(v___x_105_);
lean_dec(v___x_105_);
v_a_85_ = v___x_110_;
goto v___jp_84_;
}
}
v___jp_84_:
{
size_t v___x_86_; size_t v___x_87_; lean_object* v___x_88_; 
v___x_86_ = ((size_t)1ULL);
v___x_87_ = lean_usize_add(v_i_73_, v___x_86_);
v___x_88_ = lean_array_uset(v_bs_x27_83_, v_i_73_, v_a_85_);
v_i_73_ = v___x_87_;
v_bs_74_ = v___x_88_;
goto _start;
}
v___jp_90_:
{
if (lean_obj_tag(v___y_91_) == 0)
{
lean_object* v_a_92_; 
v_a_92_ = lean_ctor_get(v___y_91_, 0);
lean_inc(v_a_92_);
lean_dec_ref_known(v___y_91_, 1);
v_a_85_ = v_a_92_;
goto v___jp_84_;
}
else
{
lean_object* v_a_93_; lean_object* v___x_95_; uint8_t v_isShared_96_; uint8_t v_isSharedCheck_100_; 
lean_dec_ref(v_bs_x27_83_);
v_a_93_ = lean_ctor_get(v___y_91_, 0);
v_isSharedCheck_100_ = !lean_is_exclusive(v___y_91_);
if (v_isSharedCheck_100_ == 0)
{
v___x_95_ = v___y_91_;
v_isShared_96_ = v_isSharedCheck_100_;
goto v_resetjp_94_;
}
else
{
lean_inc(v_a_93_);
lean_dec(v___y_91_);
v___x_95_ = lean_box(0);
v_isShared_96_ = v_isSharedCheck_100_;
goto v_resetjp_94_;
}
v_resetjp_94_:
{
lean_object* v___x_98_; 
if (v_isShared_96_ == 0)
{
v___x_98_ = v___x_95_;
goto v_reusejp_97_;
}
else
{
lean_object* v_reuseFailAlloc_99_; 
v_reuseFailAlloc_99_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_99_, 0, v_a_93_);
v___x_98_ = v_reuseFailAlloc_99_;
goto v_reusejp_97_;
}
v_reusejp_97_:
{
return v___x_98_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__1___redArg___boxed(lean_object* v_sz_111_, lean_object* v_i_112_, lean_object* v_bs_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_){
_start:
{
size_t v_sz_boxed_118_; size_t v_i_boxed_119_; lean_object* v_res_120_; 
v_sz_boxed_118_ = lean_unbox_usize(v_sz_111_);
lean_dec(v_sz_111_);
v_i_boxed_119_ = lean_unbox_usize(v_i_112_);
lean_dec(v_i_112_);
v_res_120_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__1___redArg(v_sz_boxed_118_, v_i_boxed_119_, v_bs_113_, v___y_114_, v___y_115_, v___y_116_);
lean_dec(v___y_116_);
lean_dec_ref(v___y_115_);
lean_dec_ref(v___y_114_);
return v_res_120_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore___closed__1(void){
_start:
{
lean_object* v___x_122_; lean_object* v___x_123_; 
v___x_122_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore___closed__0));
v___x_123_ = l_Lean_stringToMessageData(v___x_122_);
return v___x_123_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore___closed__3(void){
_start:
{
lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_125_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore___closed__2));
v___x_126_ = l_Lean_stringToMessageData(v___x_125_);
return v___x_126_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore(uint8_t v_internalize_127_, lean_object* v_ids_128_, lean_object* v_a_129_, lean_object* v_a_130_, lean_object* v_a_131_, lean_object* v_a_132_, lean_object* v_a_133_, lean_object* v_a_134_, lean_object* v_a_135_, lean_object* v_a_136_){
_start:
{
lean_object* v_goal_139_; lean_object* v___y_140_; lean_object* v___y_141_; lean_object* v___y_142_; lean_object* v___y_143_; lean_object* v___y_144_; lean_object* v_goal_149_; lean_object* v___y_150_; lean_object* v___y_151_; lean_object* v___y_152_; lean_object* v___y_153_; lean_object* v___y_154_; lean_object* v___y_155_; lean_object* v___x_167_; 
v___x_167_ = l_Lean_Elab_Tactic_Grind_ensureSym___redArg(v_a_129_, v_a_133_, v_a_134_, v_a_135_, v_a_136_);
if (lean_obj_tag(v___x_167_) == 0)
{
lean_object* v___x_168_; 
lean_dec_ref_known(v___x_167_, 1);
v___x_168_ = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(v_a_130_, v_a_133_, v_a_134_, v_a_135_, v_a_136_);
if (lean_obj_tag(v___x_168_) == 0)
{
lean_object* v_a_169_; lean_object* v_options_170_; lean_object* v___x_171_; uint8_t v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; uint8_t v___x_175_; 
v_a_169_ = lean_ctor_get(v___x_168_, 0);
lean_inc(v_a_169_);
lean_dec_ref_known(v___x_168_, 1);
v_options_170_ = lean_ctor_get(v_a_135_, 2);
v___x_171_ = l_Lean_Meta_tactic_hygienic;
v___x_172_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__0(v_options_170_, v___x_171_);
v___x_173_ = lean_array_get_size(v_ids_128_);
v___x_174_ = lean_unsigned_to_nat(0u);
v___x_175_ = lean_nat_dec_eq(v___x_173_, v___x_174_);
if (v___x_175_ == 0)
{
size_t v_sz_176_; size_t v___x_177_; lean_object* v___x_178_; 
v_sz_176_ = lean_array_size(v_ids_128_);
v___x_177_ = ((size_t)0ULL);
v___x_178_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__1___redArg(v_sz_176_, v___x_177_, v_ids_128_, v_a_133_, v_a_135_, v_a_136_);
if (lean_obj_tag(v___x_178_) == 0)
{
lean_object* v_a_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
v_a_179_ = lean_ctor_get(v___x_178_, 0);
lean_inc(v_a_179_);
lean_dec_ref_known(v___x_178_, 1);
v___x_180_ = lean_box(v___x_172_);
v___x_181_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Goal_intros___boxed), 10, 3);
lean_closure_set(v___x_181_, 0, v_a_169_);
lean_closure_set(v___x_181_, 1, v_a_179_);
lean_closure_set(v___x_181_, 2, v___x_180_);
v___x_182_ = l_Lean_Elab_Tactic_Grind_liftSymM___redArg(v___x_181_, v_a_129_, v_a_130_, v_a_133_, v_a_134_, v_a_135_, v_a_136_);
if (lean_obj_tag(v___x_182_) == 0)
{
lean_object* v_a_183_; 
v_a_183_ = lean_ctor_get(v___x_182_, 0);
lean_inc(v_a_183_);
lean_dec_ref_known(v___x_182_, 1);
if (lean_obj_tag(v_a_183_) == 0)
{
lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v_a_186_; lean_object* v___x_188_; uint8_t v_isShared_189_; uint8_t v_isSharedCheck_193_; 
v___x_184_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore___closed__1, &l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore___closed__1);
v___x_185_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__2___redArg(v___x_184_, v_a_133_, v_a_134_, v_a_135_, v_a_136_);
v_a_186_ = lean_ctor_get(v___x_185_, 0);
v_isSharedCheck_193_ = !lean_is_exclusive(v___x_185_);
if (v_isSharedCheck_193_ == 0)
{
v___x_188_ = v___x_185_;
v_isShared_189_ = v_isSharedCheck_193_;
goto v_resetjp_187_;
}
else
{
lean_inc(v_a_186_);
lean_dec(v___x_185_);
v___x_188_ = lean_box(0);
v_isShared_189_ = v_isSharedCheck_193_;
goto v_resetjp_187_;
}
v_resetjp_187_:
{
lean_object* v___x_191_; 
if (v_isShared_189_ == 0)
{
v___x_191_ = v___x_188_;
goto v_reusejp_190_;
}
else
{
lean_object* v_reuseFailAlloc_192_; 
v_reuseFailAlloc_192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_192_, 0, v_a_186_);
v___x_191_ = v_reuseFailAlloc_192_;
goto v_reusejp_190_;
}
v_reusejp_190_:
{
return v___x_191_;
}
}
}
else
{
lean_object* v_goal_194_; 
v_goal_194_ = lean_ctor_get(v_a_183_, 1);
lean_inc_ref(v_goal_194_);
lean_dec_ref_known(v_a_183_, 2);
v_goal_149_ = v_goal_194_;
v___y_150_ = v_a_129_;
v___y_151_ = v_a_130_;
v___y_152_ = v_a_133_;
v___y_153_ = v_a_134_;
v___y_154_ = v_a_135_;
v___y_155_ = v_a_136_;
goto v___jp_148_;
}
}
else
{
lean_object* v_a_195_; lean_object* v___x_197_; uint8_t v_isShared_198_; uint8_t v_isSharedCheck_202_; 
v_a_195_ = lean_ctor_get(v___x_182_, 0);
v_isSharedCheck_202_ = !lean_is_exclusive(v___x_182_);
if (v_isSharedCheck_202_ == 0)
{
v___x_197_ = v___x_182_;
v_isShared_198_ = v_isSharedCheck_202_;
goto v_resetjp_196_;
}
else
{
lean_inc(v_a_195_);
lean_dec(v___x_182_);
v___x_197_ = lean_box(0);
v_isShared_198_ = v_isSharedCheck_202_;
goto v_resetjp_196_;
}
v_resetjp_196_:
{
lean_object* v___x_200_; 
if (v_isShared_198_ == 0)
{
v___x_200_ = v___x_197_;
goto v_reusejp_199_;
}
else
{
lean_object* v_reuseFailAlloc_201_; 
v_reuseFailAlloc_201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_201_, 0, v_a_195_);
v___x_200_ = v_reuseFailAlloc_201_;
goto v_reusejp_199_;
}
v_reusejp_199_:
{
return v___x_200_;
}
}
}
}
else
{
lean_object* v_a_203_; lean_object* v___x_205_; uint8_t v_isShared_206_; uint8_t v_isSharedCheck_210_; 
lean_dec(v_a_169_);
v_a_203_ = lean_ctor_get(v___x_178_, 0);
v_isSharedCheck_210_ = !lean_is_exclusive(v___x_178_);
if (v_isSharedCheck_210_ == 0)
{
v___x_205_ = v___x_178_;
v_isShared_206_ = v_isSharedCheck_210_;
goto v_resetjp_204_;
}
else
{
lean_inc(v_a_203_);
lean_dec(v___x_178_);
v___x_205_ = lean_box(0);
v_isShared_206_ = v_isSharedCheck_210_;
goto v_resetjp_204_;
}
v_resetjp_204_:
{
lean_object* v___x_208_; 
if (v_isShared_206_ == 0)
{
v___x_208_ = v___x_205_;
goto v_reusejp_207_;
}
else
{
lean_object* v_reuseFailAlloc_209_; 
v_reuseFailAlloc_209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_209_, 0, v_a_203_);
v___x_208_ = v_reuseFailAlloc_209_;
goto v_reusejp_207_;
}
v_reusejp_207_:
{
return v___x_208_;
}
}
}
}
else
{
lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; 
lean_dec_ref(v_ids_128_);
v___x_211_ = lean_unsigned_to_nat(1u);
v___x_212_ = lean_box(v___x_172_);
v___x_213_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Goal_introN___boxed), 10, 3);
lean_closure_set(v___x_213_, 0, v_a_169_);
lean_closure_set(v___x_213_, 1, v___x_211_);
lean_closure_set(v___x_213_, 2, v___x_212_);
v___x_214_ = l_Lean_Elab_Tactic_Grind_liftSymM___redArg(v___x_213_, v_a_129_, v_a_130_, v_a_133_, v_a_134_, v_a_135_, v_a_136_);
if (lean_obj_tag(v___x_214_) == 0)
{
lean_object* v_a_215_; 
v_a_215_ = lean_ctor_get(v___x_214_, 0);
lean_inc(v_a_215_);
lean_dec_ref_known(v___x_214_, 1);
if (lean_obj_tag(v_a_215_) == 0)
{
lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v_a_218_; lean_object* v___x_220_; uint8_t v_isShared_221_; uint8_t v_isSharedCheck_225_; 
v___x_216_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore___closed__3, &l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore___closed__3);
v___x_217_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__2___redArg(v___x_216_, v_a_133_, v_a_134_, v_a_135_, v_a_136_);
v_a_218_ = lean_ctor_get(v___x_217_, 0);
v_isSharedCheck_225_ = !lean_is_exclusive(v___x_217_);
if (v_isSharedCheck_225_ == 0)
{
v___x_220_ = v___x_217_;
v_isShared_221_ = v_isSharedCheck_225_;
goto v_resetjp_219_;
}
else
{
lean_inc(v_a_218_);
lean_dec(v___x_217_);
v___x_220_ = lean_box(0);
v_isShared_221_ = v_isSharedCheck_225_;
goto v_resetjp_219_;
}
v_resetjp_219_:
{
lean_object* v___x_223_; 
if (v_isShared_221_ == 0)
{
v___x_223_ = v___x_220_;
goto v_reusejp_222_;
}
else
{
lean_object* v_reuseFailAlloc_224_; 
v_reuseFailAlloc_224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_224_, 0, v_a_218_);
v___x_223_ = v_reuseFailAlloc_224_;
goto v_reusejp_222_;
}
v_reusejp_222_:
{
return v___x_223_;
}
}
}
else
{
lean_object* v_goal_226_; 
v_goal_226_ = lean_ctor_get(v_a_215_, 1);
lean_inc_ref(v_goal_226_);
lean_dec_ref_known(v_a_215_, 2);
v_goal_149_ = v_goal_226_;
v___y_150_ = v_a_129_;
v___y_151_ = v_a_130_;
v___y_152_ = v_a_133_;
v___y_153_ = v_a_134_;
v___y_154_ = v_a_135_;
v___y_155_ = v_a_136_;
goto v___jp_148_;
}
}
else
{
lean_object* v_a_227_; lean_object* v___x_229_; uint8_t v_isShared_230_; uint8_t v_isSharedCheck_234_; 
v_a_227_ = lean_ctor_get(v___x_214_, 0);
v_isSharedCheck_234_ = !lean_is_exclusive(v___x_214_);
if (v_isSharedCheck_234_ == 0)
{
v___x_229_ = v___x_214_;
v_isShared_230_ = v_isSharedCheck_234_;
goto v_resetjp_228_;
}
else
{
lean_inc(v_a_227_);
lean_dec(v___x_214_);
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
}
}
else
{
lean_object* v_a_235_; lean_object* v___x_237_; uint8_t v_isShared_238_; uint8_t v_isSharedCheck_242_; 
lean_dec_ref(v_ids_128_);
v_a_235_ = lean_ctor_get(v___x_168_, 0);
v_isSharedCheck_242_ = !lean_is_exclusive(v___x_168_);
if (v_isSharedCheck_242_ == 0)
{
v___x_237_ = v___x_168_;
v_isShared_238_ = v_isSharedCheck_242_;
goto v_resetjp_236_;
}
else
{
lean_inc(v_a_235_);
lean_dec(v___x_168_);
v___x_237_ = lean_box(0);
v_isShared_238_ = v_isSharedCheck_242_;
goto v_resetjp_236_;
}
v_resetjp_236_:
{
lean_object* v___x_240_; 
if (v_isShared_238_ == 0)
{
v___x_240_ = v___x_237_;
goto v_reusejp_239_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v_a_235_);
v___x_240_ = v_reuseFailAlloc_241_;
goto v_reusejp_239_;
}
v_reusejp_239_:
{
return v___x_240_;
}
}
}
}
else
{
lean_dec_ref(v_ids_128_);
return v___x_167_;
}
v___jp_138_:
{
lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_145_ = lean_box(0);
v___x_146_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_146_, 0, v_goal_139_);
lean_ctor_set(v___x_146_, 1, v___x_145_);
v___x_147_ = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(v___x_146_, v___y_140_, v___y_141_, v___y_142_, v___y_143_, v___y_144_);
return v___x_147_;
}
v___jp_148_:
{
if (v_internalize_127_ == 0)
{
v_goal_139_ = v_goal_149_;
v___y_140_ = v___y_151_;
v___y_141_ = v___y_152_;
v___y_142_ = v___y_153_;
v___y_143_ = v___y_154_;
v___y_144_ = v___y_155_;
goto v___jp_138_;
}
else
{
lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_156_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Goal_internalizeAll___boxed), 11, 1);
lean_closure_set(v___x_156_, 0, v_goal_149_);
v___x_157_ = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(v___x_156_, v___y_150_, v___y_151_, v___y_152_, v___y_153_, v___y_154_, v___y_155_);
if (lean_obj_tag(v___x_157_) == 0)
{
lean_object* v_a_158_; 
v_a_158_ = lean_ctor_get(v___x_157_, 0);
lean_inc(v_a_158_);
lean_dec_ref_known(v___x_157_, 1);
v_goal_139_ = v_a_158_;
v___y_140_ = v___y_151_;
v___y_141_ = v___y_152_;
v___y_142_ = v___y_153_;
v___y_143_ = v___y_154_;
v___y_144_ = v___y_155_;
goto v___jp_138_;
}
else
{
lean_object* v_a_159_; lean_object* v___x_161_; uint8_t v_isShared_162_; uint8_t v_isSharedCheck_166_; 
v_a_159_ = lean_ctor_get(v___x_157_, 0);
v_isSharedCheck_166_ = !lean_is_exclusive(v___x_157_);
if (v_isSharedCheck_166_ == 0)
{
v___x_161_ = v___x_157_;
v_isShared_162_ = v_isSharedCheck_166_;
goto v_resetjp_160_;
}
else
{
lean_inc(v_a_159_);
lean_dec(v___x_157_);
v___x_161_ = lean_box(0);
v_isShared_162_ = v_isSharedCheck_166_;
goto v_resetjp_160_;
}
v_resetjp_160_:
{
lean_object* v___x_164_; 
if (v_isShared_162_ == 0)
{
v___x_164_ = v___x_161_;
goto v_reusejp_163_;
}
else
{
lean_object* v_reuseFailAlloc_165_; 
v_reuseFailAlloc_165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_165_, 0, v_a_159_);
v___x_164_ = v_reuseFailAlloc_165_;
goto v_reusejp_163_;
}
v_reusejp_163_:
{
return v___x_164_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore___boxed(lean_object* v_internalize_243_, lean_object* v_ids_244_, lean_object* v_a_245_, lean_object* v_a_246_, lean_object* v_a_247_, lean_object* v_a_248_, lean_object* v_a_249_, lean_object* v_a_250_, lean_object* v_a_251_, lean_object* v_a_252_, lean_object* v_a_253_){
_start:
{
uint8_t v_internalize_boxed_254_; lean_object* v_res_255_; 
v_internalize_boxed_254_ = lean_unbox(v_internalize_243_);
v_res_255_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore(v_internalize_boxed_254_, v_ids_244_, v_a_245_, v_a_246_, v_a_247_, v_a_248_, v_a_249_, v_a_250_, v_a_251_, v_a_252_);
lean_dec(v_a_252_);
lean_dec_ref(v_a_251_);
lean_dec(v_a_250_);
lean_dec_ref(v_a_249_);
lean_dec(v_a_248_);
lean_dec_ref(v_a_247_);
lean_dec(v_a_246_);
lean_dec_ref(v_a_245_);
return v_res_255_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__1(size_t v_sz_256_, size_t v_i_257_, lean_object* v_bs_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_){
_start:
{
lean_object* v___x_268_; 
v___x_268_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__1___redArg(v_sz_256_, v_i_257_, v_bs_258_, v___y_263_, v___y_265_, v___y_266_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__1___boxed(lean_object* v_sz_269_, lean_object* v_i_270_, lean_object* v_bs_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_){
_start:
{
size_t v_sz_boxed_281_; size_t v_i_boxed_282_; lean_object* v_res_283_; 
v_sz_boxed_281_ = lean_unbox_usize(v_sz_269_);
lean_dec(v_sz_269_);
v_i_boxed_282_ = lean_unbox_usize(v_i_270_);
lean_dec(v_i_270_);
v_res_283_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__1(v_sz_boxed_281_, v_i_boxed_282_, v_bs_271_, v___y_272_, v___y_273_, v___y_274_, v___y_275_, v___y_276_, v___y_277_, v___y_278_, v___y_279_);
lean_dec(v___y_279_);
lean_dec_ref(v___y_278_);
lean_dec(v___y_277_);
lean_dec_ref(v___y_276_);
lean_dec(v___y_275_);
lean_dec_ref(v___y_274_);
lean_dec(v___y_273_);
lean_dec_ref(v___y_272_);
return v_res_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__2(lean_object* v_00_u03b1_284_, lean_object* v_msg_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_){
_start:
{
lean_object* v___x_295_; 
v___x_295_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__2___redArg(v_msg_285_, v___y_290_, v___y_291_, v___y_292_, v___y_293_);
return v___x_295_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__2___boxed(lean_object* v_00_u03b1_296_, lean_object* v_msg_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_){
_start:
{
lean_object* v_res_307_; 
v_res_307_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__2(v_00_u03b1_296_, v_msg_297_, v___y_298_, v___y_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_, v___y_305_);
lean_dec(v___y_305_);
lean_dec_ref(v___y_304_);
lean_dec(v___y_303_);
lean_dec_ref(v___y_302_);
lean_dec(v___y_301_);
lean_dec_ref(v___y_300_);
lean_dec(v___y_299_);
lean_dec_ref(v___y_298_);
return v_res_307_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_308_ = lean_box(0);
v___x_309_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_310_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_310_, 0, v___x_309_);
lean_ctor_set(v___x_310_, 1, v___x_308_);
return v___x_310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro_spec__0___redArg(){
_start:
{
lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_312_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro_spec__0___redArg___closed__0);
v___x_313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_313_, 0, v___x_312_);
return v___x_313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro_spec__0___redArg___boxed(lean_object* v___y_314_){
_start:
{
lean_object* v_res_315_; 
v_res_315_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro_spec__0___redArg();
return v_res_315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro_spec__0(lean_object* v_00_u03b1_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_){
_start:
{
lean_object* v___x_326_; 
v___x_326_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro_spec__0___redArg();
return v___x_326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro_spec__0___boxed(lean_object* v_00_u03b1_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_){
_start:
{
lean_object* v_res_337_; 
v_res_337_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro_spec__0(v_00_u03b1_327_, v___y_328_, v___y_329_, v___y_330_, v___y_331_, v___y_332_, v___y_333_, v___y_334_, v___y_335_);
lean_dec(v___y_335_);
lean_dec_ref(v___y_334_);
lean_dec(v___y_333_);
lean_dec_ref(v___y_332_);
lean_dec(v___y_331_);
lean_dec_ref(v___y_330_);
lean_dec(v___y_329_);
lean_dec_ref(v___y_328_);
return v_res_337_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro(lean_object* v_stx_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_){
_start:
{
lean_object* v___x_367_; uint8_t v___x_368_; 
v___x_367_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___closed__4));
lean_inc(v_stx_357_);
v___x_368_ = l_Lean_Syntax_isOfKind(v_stx_357_, v___x_367_);
if (v___x_368_ == 0)
{
lean_object* v___x_369_; 
lean_dec(v_stx_357_);
v___x_369_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro_spec__0___redArg();
return v___x_369_;
}
else
{
lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; uint8_t v___x_373_; 
v___x_370_ = lean_unsigned_to_nat(0u);
v___x_371_ = lean_unsigned_to_nat(1u);
v___x_372_ = l_Lean_Syntax_getArg(v_stx_357_, v___x_371_);
lean_inc(v___x_372_);
v___x_373_ = l_Lean_Syntax_matchesNull(v___x_372_, v___x_370_);
if (v___x_373_ == 0)
{
lean_object* v___x_374_; uint8_t v___x_375_; 
v___x_374_ = lean_unsigned_to_nat(5u);
lean_inc(v___x_372_);
v___x_375_ = l_Lean_Syntax_matchesNull(v___x_372_, v___x_374_);
if (v___x_375_ == 0)
{
lean_object* v___x_376_; 
lean_dec(v___x_372_);
lean_dec(v_stx_357_);
v___x_376_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro_spec__0___redArg();
return v___x_376_;
}
else
{
lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; uint8_t v___x_381_; 
v___x_377_ = lean_unsigned_to_nat(2u);
v___x_378_ = lean_unsigned_to_nat(3u);
v___x_379_ = l_Lean_Syntax_getArg(v___x_372_, v___x_378_);
lean_dec(v___x_372_);
v___x_380_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___closed__7));
lean_inc(v___x_379_);
v___x_381_ = l_Lean_Syntax_isOfKind(v___x_379_, v___x_380_);
if (v___x_381_ == 0)
{
lean_object* v___x_382_; uint8_t v___x_383_; 
v___x_382_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___closed__9));
v___x_383_ = l_Lean_Syntax_isOfKind(v___x_379_, v___x_382_);
if (v___x_383_ == 0)
{
lean_object* v___x_384_; 
lean_dec(v_stx_357_);
v___x_384_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro_spec__0___redArg();
return v___x_384_;
}
else
{
lean_object* v___x_385_; lean_object* v_ids_386_; lean_object* v___x_387_; 
v___x_385_ = l_Lean_Syntax_getArg(v_stx_357_, v___x_377_);
lean_dec(v_stx_357_);
v_ids_386_ = l_Lean_Syntax_getArgs(v___x_385_);
lean_dec(v___x_385_);
v___x_387_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore(v___x_368_, v_ids_386_, v_a_358_, v_a_359_, v_a_360_, v_a_361_, v_a_362_, v_a_363_, v_a_364_, v_a_365_);
return v___x_387_;
}
}
else
{
lean_object* v___x_388_; lean_object* v_ids_389_; lean_object* v___x_390_; 
lean_dec(v___x_379_);
v___x_388_ = l_Lean_Syntax_getArg(v_stx_357_, v___x_377_);
lean_dec(v_stx_357_);
v_ids_389_ = l_Lean_Syntax_getArgs(v___x_388_);
lean_dec(v___x_388_);
v___x_390_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore(v___x_373_, v_ids_389_, v_a_358_, v_a_359_, v_a_360_, v_a_361_, v_a_362_, v_a_363_, v_a_364_, v_a_365_);
return v___x_390_;
}
}
}
else
{
lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v_ids_393_; lean_object* v___x_394_; 
lean_dec(v___x_372_);
v___x_391_ = lean_unsigned_to_nat(2u);
v___x_392_ = l_Lean_Syntax_getArg(v_stx_357_, v___x_391_);
lean_dec(v_stx_357_);
v_ids_393_ = l_Lean_Syntax_getArgs(v___x_392_);
lean_dec(v___x_392_);
v___x_394_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore(v___x_368_, v_ids_393_, v_a_358_, v_a_359_, v_a_360_, v_a_361_, v_a_362_, v_a_363_, v_a_364_, v_a_365_);
return v___x_394_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___boxed(lean_object* v_stx_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_){
_start:
{
lean_object* v_res_405_; 
v_res_405_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro(v_stx_395_, v_a_396_, v_a_397_, v_a_398_, v_a_399_, v_a_400_, v_a_401_, v_a_402_, v_a_403_);
lean_dec(v_a_403_);
lean_dec_ref(v_a_402_);
lean_dec(v_a_401_);
lean_dec_ref(v_a_400_);
lean_dec(v_a_399_);
lean_dec_ref(v_a_398_);
lean_dec(v_a_397_);
lean_dec_ref(v_a_396_);
return v_res_405_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro__1(){
_start:
{
lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; 
v___x_447_ = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
v___x_448_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___closed__4));
v___x_449_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro__1___closed__15));
v___x_450_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___boxed), 10, 0);
v___x_451_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_447_, v___x_448_, v___x_449_, v___x_450_);
return v___x_451_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro__1___boxed(lean_object* v_a_452_){
_start:
{
lean_object* v_res_453_; 
v_res_453_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro__1();
return v_res_453_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntrosCore___redArg___closed__2(void){
_start:
{
lean_object* v___x_457_; lean_object* v___x_458_; 
v___x_457_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntrosCore___redArg___closed__1));
v___x_458_ = l_Lean_stringToMessageData(v___x_457_);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntrosCore___redArg(uint8_t v_internalize_459_, lean_object* v_a_460_, lean_object* v_a_461_, lean_object* v_a_462_, lean_object* v_a_463_, lean_object* v_a_464_, lean_object* v_a_465_){
_start:
{
lean_object* v_goal_468_; lean_object* v___y_469_; lean_object* v___y_470_; lean_object* v___y_471_; lean_object* v___y_472_; lean_object* v___y_473_; lean_object* v___x_477_; 
v___x_477_ = l_Lean_Elab_Tactic_Grind_ensureSym___redArg(v_a_460_, v_a_462_, v_a_463_, v_a_464_, v_a_465_);
if (lean_obj_tag(v___x_477_) == 0)
{
lean_object* v___x_478_; 
lean_dec_ref_known(v___x_477_, 1);
v___x_478_ = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(v_a_461_, v_a_462_, v_a_463_, v_a_464_, v_a_465_);
if (lean_obj_tag(v___x_478_) == 0)
{
lean_object* v_a_479_; lean_object* v_options_480_; lean_object* v___x_481_; uint8_t v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; 
v_a_479_ = lean_ctor_get(v___x_478_, 0);
lean_inc(v_a_479_);
lean_dec_ref_known(v___x_478_, 1);
v_options_480_ = lean_ctor_get(v_a_464_, 2);
v___x_481_ = l_Lean_Meta_tactic_hygienic;
v___x_482_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__0(v_options_480_, v___x_481_);
v___x_483_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntrosCore___redArg___closed__0));
v___x_484_ = lean_box(v___x_482_);
v___x_485_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Goal_intros___boxed), 10, 3);
lean_closure_set(v___x_485_, 0, v_a_479_);
lean_closure_set(v___x_485_, 1, v___x_483_);
lean_closure_set(v___x_485_, 2, v___x_484_);
v___x_486_ = l_Lean_Elab_Tactic_Grind_liftSymM___redArg(v___x_485_, v_a_460_, v_a_461_, v_a_462_, v_a_463_, v_a_464_, v_a_465_);
if (lean_obj_tag(v___x_486_) == 0)
{
lean_object* v_a_487_; 
v_a_487_ = lean_ctor_get(v___x_486_, 0);
lean_inc(v_a_487_);
lean_dec_ref_known(v___x_486_, 1);
if (lean_obj_tag(v_a_487_) == 0)
{
lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_488_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntrosCore___redArg___closed__2, &l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntrosCore___redArg___closed__2_once, _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntrosCore___redArg___closed__2);
v___x_489_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__2___redArg(v___x_488_, v_a_462_, v_a_463_, v_a_464_, v_a_465_);
return v___x_489_;
}
else
{
if (v_internalize_459_ == 0)
{
lean_object* v_goal_490_; 
v_goal_490_ = lean_ctor_get(v_a_487_, 1);
lean_inc_ref(v_goal_490_);
lean_dec_ref_known(v_a_487_, 2);
v_goal_468_ = v_goal_490_;
v___y_469_ = v_a_461_;
v___y_470_ = v_a_462_;
v___y_471_ = v_a_463_;
v___y_472_ = v_a_464_;
v___y_473_ = v_a_465_;
goto v___jp_467_;
}
else
{
lean_object* v_goal_491_; lean_object* v___x_492_; lean_object* v___x_493_; 
v_goal_491_ = lean_ctor_get(v_a_487_, 1);
lean_inc_ref(v_goal_491_);
lean_dec_ref_known(v_a_487_, 2);
v___x_492_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Goal_internalizeAll___boxed), 11, 1);
lean_closure_set(v___x_492_, 0, v_goal_491_);
v___x_493_ = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(v___x_492_, v_a_460_, v_a_461_, v_a_462_, v_a_463_, v_a_464_, v_a_465_);
if (lean_obj_tag(v___x_493_) == 0)
{
lean_object* v_a_494_; 
v_a_494_ = lean_ctor_get(v___x_493_, 0);
lean_inc(v_a_494_);
lean_dec_ref_known(v___x_493_, 1);
v_goal_468_ = v_a_494_;
v___y_469_ = v_a_461_;
v___y_470_ = v_a_462_;
v___y_471_ = v_a_463_;
v___y_472_ = v_a_464_;
v___y_473_ = v_a_465_;
goto v___jp_467_;
}
else
{
lean_object* v_a_495_; lean_object* v___x_497_; uint8_t v_isShared_498_; uint8_t v_isSharedCheck_502_; 
v_a_495_ = lean_ctor_get(v___x_493_, 0);
v_isSharedCheck_502_ = !lean_is_exclusive(v___x_493_);
if (v_isSharedCheck_502_ == 0)
{
v___x_497_ = v___x_493_;
v_isShared_498_ = v_isSharedCheck_502_;
goto v_resetjp_496_;
}
else
{
lean_inc(v_a_495_);
lean_dec(v___x_493_);
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
}
}
else
{
lean_object* v_a_503_; lean_object* v___x_505_; uint8_t v_isShared_506_; uint8_t v_isSharedCheck_510_; 
v_a_503_ = lean_ctor_get(v___x_486_, 0);
v_isSharedCheck_510_ = !lean_is_exclusive(v___x_486_);
if (v_isSharedCheck_510_ == 0)
{
v___x_505_ = v___x_486_;
v_isShared_506_ = v_isSharedCheck_510_;
goto v_resetjp_504_;
}
else
{
lean_inc(v_a_503_);
lean_dec(v___x_486_);
v___x_505_ = lean_box(0);
v_isShared_506_ = v_isSharedCheck_510_;
goto v_resetjp_504_;
}
v_resetjp_504_:
{
lean_object* v___x_508_; 
if (v_isShared_506_ == 0)
{
v___x_508_ = v___x_505_;
goto v_reusejp_507_;
}
else
{
lean_object* v_reuseFailAlloc_509_; 
v_reuseFailAlloc_509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_509_, 0, v_a_503_);
v___x_508_ = v_reuseFailAlloc_509_;
goto v_reusejp_507_;
}
v_reusejp_507_:
{
return v___x_508_;
}
}
}
}
else
{
lean_object* v_a_511_; lean_object* v___x_513_; uint8_t v_isShared_514_; uint8_t v_isSharedCheck_518_; 
v_a_511_ = lean_ctor_get(v___x_478_, 0);
v_isSharedCheck_518_ = !lean_is_exclusive(v___x_478_);
if (v_isSharedCheck_518_ == 0)
{
v___x_513_ = v___x_478_;
v_isShared_514_ = v_isSharedCheck_518_;
goto v_resetjp_512_;
}
else
{
lean_inc(v_a_511_);
lean_dec(v___x_478_);
v___x_513_ = lean_box(0);
v_isShared_514_ = v_isSharedCheck_518_;
goto v_resetjp_512_;
}
v_resetjp_512_:
{
lean_object* v___x_516_; 
if (v_isShared_514_ == 0)
{
v___x_516_ = v___x_513_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v_a_511_);
v___x_516_ = v_reuseFailAlloc_517_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
return v___x_516_;
}
}
}
}
else
{
return v___x_477_;
}
v___jp_467_:
{
lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_474_ = lean_box(0);
v___x_475_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_475_, 0, v_goal_468_);
lean_ctor_set(v___x_475_, 1, v___x_474_);
v___x_476_ = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(v___x_475_, v___y_469_, v___y_470_, v___y_471_, v___y_472_, v___y_473_);
return v___x_476_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntrosCore___redArg___boxed(lean_object* v_internalize_519_, lean_object* v_a_520_, lean_object* v_a_521_, lean_object* v_a_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_, lean_object* v_a_526_){
_start:
{
uint8_t v_internalize_boxed_527_; lean_object* v_res_528_; 
v_internalize_boxed_527_ = lean_unbox(v_internalize_519_);
v_res_528_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntrosCore___redArg(v_internalize_boxed_527_, v_a_520_, v_a_521_, v_a_522_, v_a_523_, v_a_524_, v_a_525_);
lean_dec(v_a_525_);
lean_dec_ref(v_a_524_);
lean_dec(v_a_523_);
lean_dec_ref(v_a_522_);
lean_dec(v_a_521_);
lean_dec_ref(v_a_520_);
return v_res_528_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntrosCore(uint8_t v_internalize_529_, lean_object* v_a_530_, lean_object* v_a_531_, lean_object* v_a_532_, lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_a_535_, lean_object* v_a_536_, lean_object* v_a_537_){
_start:
{
lean_object* v___x_539_; 
v___x_539_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntrosCore___redArg(v_internalize_529_, v_a_530_, v_a_531_, v_a_534_, v_a_535_, v_a_536_, v_a_537_);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntrosCore___boxed(lean_object* v_internalize_540_, lean_object* v_a_541_, lean_object* v_a_542_, lean_object* v_a_543_, lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_, lean_object* v_a_547_, lean_object* v_a_548_, lean_object* v_a_549_){
_start:
{
uint8_t v_internalize_boxed_550_; lean_object* v_res_551_; 
v_internalize_boxed_550_ = lean_unbox(v_internalize_540_);
v_res_551_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntrosCore(v_internalize_boxed_550_, v_a_541_, v_a_542_, v_a_543_, v_a_544_, v_a_545_, v_a_546_, v_a_547_, v_a_548_);
lean_dec(v_a_548_);
lean_dec_ref(v_a_547_);
lean_dec(v_a_546_);
lean_dec_ref(v_a_545_);
lean_dec(v_a_544_);
lean_dec_ref(v_a_543_);
lean_dec(v_a_542_);
lean_dec_ref(v_a_541_);
return v_res_551_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntros___redArg(lean_object* v_stx_559_, lean_object* v_a_560_, lean_object* v_a_561_, lean_object* v_a_562_, lean_object* v_a_563_, lean_object* v_a_564_, lean_object* v_a_565_){
_start:
{
lean_object* v___x_567_; uint8_t v___x_568_; 
v___x_567_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntros___redArg___closed__1));
lean_inc(v_stx_559_);
v___x_568_ = l_Lean_Syntax_isOfKind(v_stx_559_, v___x_567_);
if (v___x_568_ == 0)
{
lean_object* v___x_569_; 
lean_dec(v_stx_559_);
v___x_569_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro_spec__0___redArg();
return v___x_569_;
}
else
{
lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; uint8_t v___x_573_; 
v___x_570_ = lean_unsigned_to_nat(0u);
v___x_571_ = lean_unsigned_to_nat(1u);
v___x_572_ = l_Lean_Syntax_getArg(v_stx_559_, v___x_571_);
lean_dec(v_stx_559_);
lean_inc(v___x_572_);
v___x_573_ = l_Lean_Syntax_matchesNull(v___x_572_, v___x_570_);
if (v___x_573_ == 0)
{
lean_object* v___x_574_; uint8_t v___x_575_; 
v___x_574_ = lean_unsigned_to_nat(5u);
lean_inc(v___x_572_);
v___x_575_ = l_Lean_Syntax_matchesNull(v___x_572_, v___x_574_);
if (v___x_575_ == 0)
{
lean_object* v___x_576_; 
lean_dec(v___x_572_);
v___x_576_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro_spec__0___redArg();
return v___x_576_;
}
else
{
lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; uint8_t v___x_580_; 
v___x_577_ = lean_unsigned_to_nat(3u);
v___x_578_ = l_Lean_Syntax_getArg(v___x_572_, v___x_577_);
lean_dec(v___x_572_);
v___x_579_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___closed__7));
lean_inc(v___x_578_);
v___x_580_ = l_Lean_Syntax_isOfKind(v___x_578_, v___x_579_);
if (v___x_580_ == 0)
{
lean_object* v___x_581_; uint8_t v___x_582_; 
v___x_581_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro___closed__9));
v___x_582_ = l_Lean_Syntax_isOfKind(v___x_578_, v___x_581_);
if (v___x_582_ == 0)
{
lean_object* v___x_583_; 
v___x_583_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro_spec__0___redArg();
return v___x_583_;
}
else
{
lean_object* v___x_584_; 
v___x_584_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntrosCore___redArg(v___x_568_, v_a_560_, v_a_561_, v_a_562_, v_a_563_, v_a_564_, v_a_565_);
return v___x_584_;
}
}
else
{
lean_object* v___x_585_; 
lean_dec(v___x_578_);
v___x_585_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntrosCore___redArg(v___x_573_, v_a_560_, v_a_561_, v_a_562_, v_a_563_, v_a_564_, v_a_565_);
return v___x_585_;
}
}
}
else
{
lean_object* v___x_586_; 
lean_dec(v___x_572_);
v___x_586_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntrosCore___redArg(v___x_568_, v_a_560_, v_a_561_, v_a_562_, v_a_563_, v_a_564_, v_a_565_);
return v___x_586_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntros___redArg___boxed(lean_object* v_stx_587_, lean_object* v_a_588_, lean_object* v_a_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_, lean_object* v_a_593_, lean_object* v_a_594_){
_start:
{
lean_object* v_res_595_; 
v_res_595_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntros___redArg(v_stx_587_, v_a_588_, v_a_589_, v_a_590_, v_a_591_, v_a_592_, v_a_593_);
lean_dec(v_a_593_);
lean_dec_ref(v_a_592_);
lean_dec(v_a_591_);
lean_dec_ref(v_a_590_);
lean_dec(v_a_589_);
lean_dec_ref(v_a_588_);
return v_res_595_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntros(lean_object* v_stx_596_, lean_object* v_a_597_, lean_object* v_a_598_, lean_object* v_a_599_, lean_object* v_a_600_, lean_object* v_a_601_, lean_object* v_a_602_, lean_object* v_a_603_, lean_object* v_a_604_){
_start:
{
lean_object* v___x_606_; 
v___x_606_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntros___redArg(v_stx_596_, v_a_597_, v_a_598_, v_a_601_, v_a_602_, v_a_603_, v_a_604_);
return v___x_606_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntros___boxed(lean_object* v_stx_607_, lean_object* v_a_608_, lean_object* v_a_609_, lean_object* v_a_610_, lean_object* v_a_611_, lean_object* v_a_612_, lean_object* v_a_613_, lean_object* v_a_614_, lean_object* v_a_615_, lean_object* v_a_616_){
_start:
{
lean_object* v_res_617_; 
v_res_617_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntros(v_stx_607_, v_a_608_, v_a_609_, v_a_610_, v_a_611_, v_a_612_, v_a_613_, v_a_614_, v_a_615_);
lean_dec(v_a_615_);
lean_dec_ref(v_a_614_);
lean_dec(v_a_613_);
lean_dec_ref(v_a_612_);
lean_dec(v_a_611_);
lean_dec_ref(v_a_610_);
lean_dec(v_a_609_);
lean_dec_ref(v_a_608_);
return v_res_617_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntros___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntros__1(){
_start:
{
lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_623_ = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
v___x_624_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntros___redArg___closed__1));
v___x_625_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntros___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntros__1___closed__1));
v___x_626_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntros___boxed), 10, 0);
v___x_627_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_623_, v___x_624_, v___x_625_, v___x_626_);
return v___x_627_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntros___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntros__1___boxed(lean_object* v_a_628_){
_start:
{
lean_object* v_res_629_; 
v_res_629_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntros___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntros__1();
return v_res_629_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_630_, lean_object* v_vals_631_, lean_object* v_i_632_, lean_object* v_k_633_){
_start:
{
lean_object* v___x_634_; uint8_t v___x_635_; 
v___x_634_ = lean_array_get_size(v_keys_630_);
v___x_635_ = lean_nat_dec_lt(v_i_632_, v___x_634_);
if (v___x_635_ == 0)
{
lean_object* v___x_636_; 
lean_dec(v_i_632_);
v___x_636_ = lean_box(0);
return v___x_636_;
}
else
{
lean_object* v_k_x27_637_; uint8_t v___x_638_; 
v_k_x27_637_ = lean_array_fget_borrowed(v_keys_630_, v_i_632_);
v___x_638_ = lean_name_eq(v_k_633_, v_k_x27_637_);
if (v___x_638_ == 0)
{
lean_object* v___x_639_; lean_object* v___x_640_; 
v___x_639_ = lean_unsigned_to_nat(1u);
v___x_640_ = lean_nat_add(v_i_632_, v___x_639_);
lean_dec(v_i_632_);
v_i_632_ = v___x_640_;
goto _start;
}
else
{
lean_object* v___x_642_; lean_object* v___x_643_; 
v___x_642_ = lean_array_fget_borrowed(v_vals_631_, v_i_632_);
lean_dec(v_i_632_);
lean_inc(v___x_642_);
v___x_643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_643_, 0, v___x_642_);
return v___x_643_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_644_, lean_object* v_vals_645_, lean_object* v_i_646_, lean_object* v_k_647_){
_start:
{
lean_object* v_res_648_; 
v_res_648_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0_spec__0_spec__1___redArg(v_keys_644_, v_vals_645_, v_i_646_, v_k_647_);
lean_dec(v_k_647_);
lean_dec_ref(v_vals_645_);
lean_dec_ref(v_keys_644_);
return v_res_648_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0_spec__0___redArg(lean_object* v_x_649_, size_t v_x_650_, lean_object* v_x_651_){
_start:
{
if (lean_obj_tag(v_x_649_) == 0)
{
lean_object* v_es_652_; lean_object* v___x_653_; size_t v___x_654_; size_t v___x_655_; lean_object* v_j_656_; lean_object* v___x_657_; 
v_es_652_ = lean_ctor_get(v_x_649_, 0);
v___x_653_ = lean_box(2);
v___x_654_ = ((size_t)31ULL);
v___x_655_ = lean_usize_land(v_x_650_, v___x_654_);
v_j_656_ = lean_usize_to_nat(v___x_655_);
v___x_657_ = lean_array_get_borrowed(v___x_653_, v_es_652_, v_j_656_);
lean_dec(v_j_656_);
switch(lean_obj_tag(v___x_657_))
{
case 0:
{
lean_object* v_key_658_; lean_object* v_val_659_; uint8_t v___x_660_; 
v_key_658_ = lean_ctor_get(v___x_657_, 0);
v_val_659_ = lean_ctor_get(v___x_657_, 1);
v___x_660_ = lean_name_eq(v_x_651_, v_key_658_);
if (v___x_660_ == 0)
{
lean_object* v___x_661_; 
v___x_661_ = lean_box(0);
return v___x_661_;
}
else
{
lean_object* v___x_662_; 
lean_inc(v_val_659_);
v___x_662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_662_, 0, v_val_659_);
return v___x_662_;
}
}
case 1:
{
lean_object* v_node_663_; size_t v___x_664_; size_t v___x_665_; 
v_node_663_ = lean_ctor_get(v___x_657_, 0);
v___x_664_ = ((size_t)5ULL);
v___x_665_ = lean_usize_shift_right(v_x_650_, v___x_664_);
v_x_649_ = v_node_663_;
v_x_650_ = v___x_665_;
goto _start;
}
default: 
{
lean_object* v___x_667_; 
v___x_667_ = lean_box(0);
return v___x_667_;
}
}
}
else
{
lean_object* v_ks_668_; lean_object* v_vs_669_; lean_object* v___x_670_; lean_object* v___x_671_; 
v_ks_668_ = lean_ctor_get(v_x_649_, 0);
v_vs_669_ = lean_ctor_get(v_x_649_, 1);
v___x_670_ = lean_unsigned_to_nat(0u);
v___x_671_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0_spec__0_spec__1___redArg(v_ks_668_, v_vs_669_, v___x_670_, v_x_651_);
return v___x_671_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0_spec__0___redArg___boxed(lean_object* v_x_672_, lean_object* v_x_673_, lean_object* v_x_674_){
_start:
{
size_t v_x_1906__boxed_675_; lean_object* v_res_676_; 
v_x_1906__boxed_675_ = lean_unbox_usize(v_x_673_);
lean_dec(v_x_673_);
v_res_676_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0_spec__0___redArg(v_x_672_, v_x_1906__boxed_675_, v_x_674_);
lean_dec(v_x_674_);
lean_dec_ref(v_x_672_);
return v_res_676_;
}
}
static uint64_t _init_l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_677_; uint64_t v___x_678_; 
v___x_677_ = lean_unsigned_to_nat(1723u);
v___x_678_ = lean_uint64_of_nat(v___x_677_);
return v___x_678_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0___redArg(lean_object* v_x_679_, lean_object* v_x_680_){
_start:
{
uint64_t v___y_682_; 
if (lean_obj_tag(v_x_680_) == 0)
{
uint64_t v___x_685_; 
v___x_685_ = lean_uint64_once(&l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0___redArg___closed__0);
v___y_682_ = v___x_685_;
goto v___jp_681_;
}
else
{
uint64_t v_hash_686_; 
v_hash_686_ = lean_ctor_get_uint64(v_x_680_, sizeof(void*)*2);
v___y_682_ = v_hash_686_;
goto v___jp_681_;
}
v___jp_681_:
{
size_t v___x_683_; lean_object* v___x_684_; 
v___x_683_ = lean_uint64_to_usize(v___y_682_);
v___x_684_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0_spec__0___redArg(v_x_679_, v___x_683_, v_x_680_);
return v___x_684_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0___redArg___boxed(lean_object* v_x_687_, lean_object* v_x_688_){
_start:
{
lean_object* v_res_689_; 
v_res_689_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0___redArg(v_x_687_, v_x_688_);
lean_dec(v_x_688_);
lean_dec_ref(v_x_687_);
return v_res_689_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2_spec__4_spec__5___redArg(lean_object* v_x_690_, lean_object* v_x_691_, lean_object* v_x_692_, lean_object* v_x_693_){
_start:
{
lean_object* v_ks_694_; lean_object* v_vs_695_; lean_object* v___x_697_; uint8_t v_isShared_698_; uint8_t v_isSharedCheck_719_; 
v_ks_694_ = lean_ctor_get(v_x_690_, 0);
v_vs_695_ = lean_ctor_get(v_x_690_, 1);
v_isSharedCheck_719_ = !lean_is_exclusive(v_x_690_);
if (v_isSharedCheck_719_ == 0)
{
v___x_697_ = v_x_690_;
v_isShared_698_ = v_isSharedCheck_719_;
goto v_resetjp_696_;
}
else
{
lean_inc(v_vs_695_);
lean_inc(v_ks_694_);
lean_dec(v_x_690_);
v___x_697_ = lean_box(0);
v_isShared_698_ = v_isSharedCheck_719_;
goto v_resetjp_696_;
}
v_resetjp_696_:
{
lean_object* v___x_699_; uint8_t v___x_700_; 
v___x_699_ = lean_array_get_size(v_ks_694_);
v___x_700_ = lean_nat_dec_lt(v_x_691_, v___x_699_);
if (v___x_700_ == 0)
{
lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_704_; 
lean_dec(v_x_691_);
v___x_701_ = lean_array_push(v_ks_694_, v_x_692_);
v___x_702_ = lean_array_push(v_vs_695_, v_x_693_);
if (v_isShared_698_ == 0)
{
lean_ctor_set(v___x_697_, 1, v___x_702_);
lean_ctor_set(v___x_697_, 0, v___x_701_);
v___x_704_ = v___x_697_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v___x_701_);
lean_ctor_set(v_reuseFailAlloc_705_, 1, v___x_702_);
v___x_704_ = v_reuseFailAlloc_705_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
return v___x_704_;
}
}
else
{
lean_object* v_k_x27_706_; uint8_t v___x_707_; 
v_k_x27_706_ = lean_array_fget_borrowed(v_ks_694_, v_x_691_);
v___x_707_ = lean_name_eq(v_x_692_, v_k_x27_706_);
if (v___x_707_ == 0)
{
lean_object* v___x_709_; 
if (v_isShared_698_ == 0)
{
v___x_709_ = v___x_697_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v_ks_694_);
lean_ctor_set(v_reuseFailAlloc_713_, 1, v_vs_695_);
v___x_709_ = v_reuseFailAlloc_713_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
lean_object* v___x_710_; lean_object* v___x_711_; 
v___x_710_ = lean_unsigned_to_nat(1u);
v___x_711_ = lean_nat_add(v_x_691_, v___x_710_);
lean_dec(v_x_691_);
v_x_690_ = v___x_709_;
v_x_691_ = v___x_711_;
goto _start;
}
}
else
{
lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_717_; 
v___x_714_ = lean_array_fset(v_ks_694_, v_x_691_, v_x_692_);
v___x_715_ = lean_array_fset(v_vs_695_, v_x_691_, v_x_693_);
lean_dec(v_x_691_);
if (v_isShared_698_ == 0)
{
lean_ctor_set(v___x_697_, 1, v___x_715_);
lean_ctor_set(v___x_697_, 0, v___x_714_);
v___x_717_ = v___x_697_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v___x_714_);
lean_ctor_set(v_reuseFailAlloc_718_, 1, v___x_715_);
v___x_717_ = v_reuseFailAlloc_718_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
return v___x_717_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2_spec__4___redArg(lean_object* v_n_720_, lean_object* v_k_721_, lean_object* v_v_722_){
_start:
{
lean_object* v___x_723_; lean_object* v___x_724_; 
v___x_723_ = lean_unsigned_to_nat(0u);
v___x_724_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2_spec__4_spec__5___redArg(v_n_720_, v___x_723_, v_k_721_, v_v_722_);
return v___x_724_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_725_; 
v___x_725_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_725_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2___redArg(lean_object* v_x_726_, size_t v_x_727_, size_t v_x_728_, lean_object* v_x_729_, lean_object* v_x_730_){
_start:
{
if (lean_obj_tag(v_x_726_) == 0)
{
lean_object* v_es_731_; size_t v___x_732_; size_t v___x_733_; lean_object* v_j_734_; lean_object* v___x_735_; uint8_t v___x_736_; 
v_es_731_ = lean_ctor_get(v_x_726_, 0);
v___x_732_ = ((size_t)31ULL);
v___x_733_ = lean_usize_land(v_x_727_, v___x_732_);
v_j_734_ = lean_usize_to_nat(v___x_733_);
v___x_735_ = lean_array_get_size(v_es_731_);
v___x_736_ = lean_nat_dec_lt(v_j_734_, v___x_735_);
if (v___x_736_ == 0)
{
lean_dec(v_j_734_);
lean_dec(v_x_730_);
lean_dec(v_x_729_);
return v_x_726_;
}
else
{
lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_775_; 
lean_inc_ref(v_es_731_);
v_isSharedCheck_775_ = !lean_is_exclusive(v_x_726_);
if (v_isSharedCheck_775_ == 0)
{
lean_object* v_unused_776_; 
v_unused_776_ = lean_ctor_get(v_x_726_, 0);
lean_dec(v_unused_776_);
v___x_738_ = v_x_726_;
v_isShared_739_ = v_isSharedCheck_775_;
goto v_resetjp_737_;
}
else
{
lean_dec(v_x_726_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_775_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v_v_740_; lean_object* v___x_741_; lean_object* v_xs_x27_742_; lean_object* v___y_744_; 
v_v_740_ = lean_array_fget(v_es_731_, v_j_734_);
v___x_741_ = lean_box(0);
v_xs_x27_742_ = lean_array_fset(v_es_731_, v_j_734_, v___x_741_);
switch(lean_obj_tag(v_v_740_))
{
case 0:
{
lean_object* v_key_749_; lean_object* v_val_750_; lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_760_; 
v_key_749_ = lean_ctor_get(v_v_740_, 0);
v_val_750_ = lean_ctor_get(v_v_740_, 1);
v_isSharedCheck_760_ = !lean_is_exclusive(v_v_740_);
if (v_isSharedCheck_760_ == 0)
{
v___x_752_ = v_v_740_;
v_isShared_753_ = v_isSharedCheck_760_;
goto v_resetjp_751_;
}
else
{
lean_inc(v_val_750_);
lean_inc(v_key_749_);
lean_dec(v_v_740_);
v___x_752_ = lean_box(0);
v_isShared_753_ = v_isSharedCheck_760_;
goto v_resetjp_751_;
}
v_resetjp_751_:
{
uint8_t v___x_754_; 
v___x_754_ = lean_name_eq(v_x_729_, v_key_749_);
if (v___x_754_ == 0)
{
lean_object* v___x_755_; lean_object* v___x_756_; 
lean_del_object(v___x_752_);
v___x_755_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_749_, v_val_750_, v_x_729_, v_x_730_);
v___x_756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_756_, 0, v___x_755_);
v___y_744_ = v___x_756_;
goto v___jp_743_;
}
else
{
lean_object* v___x_758_; 
lean_dec(v_val_750_);
lean_dec(v_key_749_);
if (v_isShared_753_ == 0)
{
lean_ctor_set(v___x_752_, 1, v_x_730_);
lean_ctor_set(v___x_752_, 0, v_x_729_);
v___x_758_ = v___x_752_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v_x_729_);
lean_ctor_set(v_reuseFailAlloc_759_, 1, v_x_730_);
v___x_758_ = v_reuseFailAlloc_759_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
v___y_744_ = v___x_758_;
goto v___jp_743_;
}
}
}
}
case 1:
{
lean_object* v_node_761_; lean_object* v___x_763_; uint8_t v_isShared_764_; uint8_t v_isSharedCheck_773_; 
v_node_761_ = lean_ctor_get(v_v_740_, 0);
v_isSharedCheck_773_ = !lean_is_exclusive(v_v_740_);
if (v_isSharedCheck_773_ == 0)
{
v___x_763_ = v_v_740_;
v_isShared_764_ = v_isSharedCheck_773_;
goto v_resetjp_762_;
}
else
{
lean_inc(v_node_761_);
lean_dec(v_v_740_);
v___x_763_ = lean_box(0);
v_isShared_764_ = v_isSharedCheck_773_;
goto v_resetjp_762_;
}
v_resetjp_762_:
{
size_t v___x_765_; size_t v___x_766_; size_t v___x_767_; size_t v___x_768_; lean_object* v___x_769_; lean_object* v___x_771_; 
v___x_765_ = ((size_t)5ULL);
v___x_766_ = lean_usize_shift_right(v_x_727_, v___x_765_);
v___x_767_ = ((size_t)1ULL);
v___x_768_ = lean_usize_add(v_x_728_, v___x_767_);
v___x_769_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2___redArg(v_node_761_, v___x_766_, v___x_768_, v_x_729_, v_x_730_);
if (v_isShared_764_ == 0)
{
lean_ctor_set(v___x_763_, 0, v___x_769_);
v___x_771_ = v___x_763_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v___x_769_);
v___x_771_ = v_reuseFailAlloc_772_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
v___y_744_ = v___x_771_;
goto v___jp_743_;
}
}
}
default: 
{
lean_object* v___x_774_; 
v___x_774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_774_, 0, v_x_729_);
lean_ctor_set(v___x_774_, 1, v_x_730_);
v___y_744_ = v___x_774_;
goto v___jp_743_;
}
}
v___jp_743_:
{
lean_object* v___x_745_; lean_object* v___x_747_; 
v___x_745_ = lean_array_fset(v_xs_x27_742_, v_j_734_, v___y_744_);
lean_dec(v_j_734_);
if (v_isShared_739_ == 0)
{
lean_ctor_set(v___x_738_, 0, v___x_745_);
v___x_747_ = v___x_738_;
goto v_reusejp_746_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v___x_745_);
v___x_747_ = v_reuseFailAlloc_748_;
goto v_reusejp_746_;
}
v_reusejp_746_:
{
return v___x_747_;
}
}
}
}
}
else
{
lean_object* v_ks_777_; lean_object* v_vs_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_798_; 
v_ks_777_ = lean_ctor_get(v_x_726_, 0);
v_vs_778_ = lean_ctor_get(v_x_726_, 1);
v_isSharedCheck_798_ = !lean_is_exclusive(v_x_726_);
if (v_isSharedCheck_798_ == 0)
{
v___x_780_ = v_x_726_;
v_isShared_781_ = v_isSharedCheck_798_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_vs_778_);
lean_inc(v_ks_777_);
lean_dec(v_x_726_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_798_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v___x_783_; 
if (v_isShared_781_ == 0)
{
v___x_783_ = v___x_780_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v_ks_777_);
lean_ctor_set(v_reuseFailAlloc_797_, 1, v_vs_778_);
v___x_783_ = v_reuseFailAlloc_797_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
lean_object* v_newNode_784_; uint8_t v___y_786_; size_t v___x_792_; uint8_t v___x_793_; 
v_newNode_784_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2_spec__4___redArg(v___x_783_, v_x_729_, v_x_730_);
v___x_792_ = ((size_t)7ULL);
v___x_793_ = lean_usize_dec_le(v___x_792_, v_x_728_);
if (v___x_793_ == 0)
{
lean_object* v___x_794_; lean_object* v___x_795_; uint8_t v___x_796_; 
v___x_794_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_784_);
v___x_795_ = lean_unsigned_to_nat(4u);
v___x_796_ = lean_nat_dec_lt(v___x_794_, v___x_795_);
lean_dec(v___x_794_);
v___y_786_ = v___x_796_;
goto v___jp_785_;
}
else
{
v___y_786_ = v___x_793_;
goto v___jp_785_;
}
v___jp_785_:
{
if (v___y_786_ == 0)
{
lean_object* v_ks_787_; lean_object* v_vs_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; 
v_ks_787_ = lean_ctor_get(v_newNode_784_, 0);
lean_inc_ref(v_ks_787_);
v_vs_788_ = lean_ctor_get(v_newNode_784_, 1);
lean_inc_ref(v_vs_788_);
lean_dec_ref(v_newNode_784_);
v___x_789_ = lean_unsigned_to_nat(0u);
v___x_790_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2___redArg___closed__0);
v___x_791_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2_spec__5___redArg(v_x_728_, v_ks_787_, v_vs_788_, v___x_789_, v___x_790_);
lean_dec_ref(v_vs_788_);
lean_dec_ref(v_ks_787_);
return v___x_791_;
}
else
{
return v_newNode_784_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2_spec__5___redArg(size_t v_depth_799_, lean_object* v_keys_800_, lean_object* v_vals_801_, lean_object* v_i_802_, lean_object* v_entries_803_){
_start:
{
lean_object* v___x_804_; uint8_t v___x_805_; 
v___x_804_ = lean_array_get_size(v_keys_800_);
v___x_805_ = lean_nat_dec_lt(v_i_802_, v___x_804_);
if (v___x_805_ == 0)
{
lean_dec(v_i_802_);
return v_entries_803_;
}
else
{
lean_object* v_k_806_; lean_object* v_v_807_; uint64_t v___y_809_; 
v_k_806_ = lean_array_fget_borrowed(v_keys_800_, v_i_802_);
v_v_807_ = lean_array_fget_borrowed(v_vals_801_, v_i_802_);
if (lean_obj_tag(v_k_806_) == 0)
{
uint64_t v___x_820_; 
v___x_820_ = lean_uint64_once(&l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0___redArg___closed__0);
v___y_809_ = v___x_820_;
goto v___jp_808_;
}
else
{
uint64_t v_hash_821_; 
v_hash_821_ = lean_ctor_get_uint64(v_k_806_, sizeof(void*)*2);
v___y_809_ = v_hash_821_;
goto v___jp_808_;
}
v___jp_808_:
{
size_t v_h_810_; size_t v___x_811_; lean_object* v___x_812_; size_t v___x_813_; size_t v___x_814_; size_t v___x_815_; size_t v_h_816_; lean_object* v___x_817_; lean_object* v___x_818_; 
v_h_810_ = lean_uint64_to_usize(v___y_809_);
v___x_811_ = ((size_t)5ULL);
v___x_812_ = lean_unsigned_to_nat(1u);
v___x_813_ = ((size_t)1ULL);
v___x_814_ = lean_usize_sub(v_depth_799_, v___x_813_);
v___x_815_ = lean_usize_mul(v___x_811_, v___x_814_);
v_h_816_ = lean_usize_shift_right(v_h_810_, v___x_815_);
v___x_817_ = lean_nat_add(v_i_802_, v___x_812_);
lean_dec(v_i_802_);
lean_inc(v_v_807_);
lean_inc(v_k_806_);
v___x_818_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2___redArg(v_entries_803_, v_h_816_, v_depth_799_, v_k_806_, v_v_807_);
v_i_802_ = v___x_817_;
v_entries_803_ = v___x_818_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_depth_822_, lean_object* v_keys_823_, lean_object* v_vals_824_, lean_object* v_i_825_, lean_object* v_entries_826_){
_start:
{
size_t v_depth_boxed_827_; lean_object* v_res_828_; 
v_depth_boxed_827_ = lean_unbox_usize(v_depth_822_);
lean_dec(v_depth_822_);
v_res_828_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2_spec__5___redArg(v_depth_boxed_827_, v_keys_823_, v_vals_824_, v_i_825_, v_entries_826_);
lean_dec_ref(v_vals_824_);
lean_dec_ref(v_keys_823_);
return v_res_828_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2___redArg___boxed(lean_object* v_x_829_, lean_object* v_x_830_, lean_object* v_x_831_, lean_object* v_x_832_, lean_object* v_x_833_){
_start:
{
size_t v_x_2056__boxed_834_; size_t v_x_2057__boxed_835_; lean_object* v_res_836_; 
v_x_2056__boxed_834_ = lean_unbox_usize(v_x_830_);
lean_dec(v_x_830_);
v_x_2057__boxed_835_ = lean_unbox_usize(v_x_831_);
lean_dec(v_x_831_);
v_res_836_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2___redArg(v_x_829_, v_x_2056__boxed_834_, v_x_2057__boxed_835_, v_x_832_, v_x_833_);
return v_res_836_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1___redArg(lean_object* v_x_837_, lean_object* v_x_838_, lean_object* v_x_839_){
_start:
{
uint64_t v___y_841_; 
if (lean_obj_tag(v_x_838_) == 0)
{
uint64_t v___x_845_; 
v___x_845_ = lean_uint64_once(&l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0___redArg___closed__0);
v___y_841_ = v___x_845_;
goto v___jp_840_;
}
else
{
uint64_t v_hash_846_; 
v_hash_846_ = lean_ctor_get_uint64(v_x_838_, sizeof(void*)*2);
v___y_841_ = v_hash_846_;
goto v___jp_840_;
}
v___jp_840_:
{
size_t v___x_842_; size_t v___x_843_; lean_object* v___x_844_; 
v___x_842_ = lean_uint64_to_usize(v___y_841_);
v___x_843_ = ((size_t)1ULL);
v___x_844_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2___redArg(v_x_837_, v___x_842_, v___x_843_, v_x_838_, v_x_839_);
return v___x_844_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule___redArg(lean_object* v_declName_847_, lean_object* v_a_848_, lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_){
_start:
{
lean_object* v___x_854_; lean_object* v_cache_855_; lean_object* v_backwardRuleName_856_; lean_object* v___x_857_; 
v___x_854_ = lean_st_ref_get(v_a_848_);
v_cache_855_ = lean_ctor_get(v___x_854_, 3);
lean_inc_ref(v_cache_855_);
lean_dec(v___x_854_);
v_backwardRuleName_856_ = lean_ctor_get(v_cache_855_, 0);
lean_inc_ref(v_backwardRuleName_856_);
lean_dec_ref(v_cache_855_);
v___x_857_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0___redArg(v_backwardRuleName_856_, v_declName_847_);
lean_dec_ref(v_backwardRuleName_856_);
if (lean_obj_tag(v___x_857_) == 1)
{
lean_object* v_val_858_; lean_object* v___x_860_; uint8_t v_isShared_861_; uint8_t v_isSharedCheck_865_; 
lean_dec(v_declName_847_);
v_val_858_ = lean_ctor_get(v___x_857_, 0);
v_isSharedCheck_865_ = !lean_is_exclusive(v___x_857_);
if (v_isSharedCheck_865_ == 0)
{
v___x_860_ = v___x_857_;
v_isShared_861_ = v_isSharedCheck_865_;
goto v_resetjp_859_;
}
else
{
lean_inc(v_val_858_);
lean_dec(v___x_857_);
v___x_860_ = lean_box(0);
v_isShared_861_ = v_isSharedCheck_865_;
goto v_resetjp_859_;
}
v_resetjp_859_:
{
lean_object* v___x_863_; 
if (v_isShared_861_ == 0)
{
lean_ctor_set_tag(v___x_860_, 0);
v___x_863_ = v___x_860_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v_val_858_);
v___x_863_ = v_reuseFailAlloc_864_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
return v___x_863_;
}
}
}
else
{
lean_object* v___x_866_; lean_object* v___x_867_; 
lean_dec(v___x_857_);
v___x_866_ = lean_box(0);
lean_inc(v_declName_847_);
v___x_867_ = l_Lean_Meta_Sym_mkBackwardRuleFromDecl(v_declName_847_, v___x_866_, v_a_849_, v_a_850_, v_a_851_, v_a_852_);
if (lean_obj_tag(v___x_867_) == 0)
{
lean_object* v_a_868_; lean_object* v___x_870_; uint8_t v_isShared_871_; uint8_t v_isSharedCheck_900_; 
v_a_868_ = lean_ctor_get(v___x_867_, 0);
v_isSharedCheck_900_ = !lean_is_exclusive(v___x_867_);
if (v_isSharedCheck_900_ == 0)
{
v___x_870_ = v___x_867_;
v_isShared_871_ = v_isSharedCheck_900_;
goto v_resetjp_869_;
}
else
{
lean_inc(v_a_868_);
lean_dec(v___x_867_);
v___x_870_ = lean_box(0);
v_isShared_871_ = v_isSharedCheck_900_;
goto v_resetjp_869_;
}
v_resetjp_869_:
{
lean_object* v___x_872_; lean_object* v_cache_873_; lean_object* v_symState_874_; lean_object* v_grindState_875_; lean_object* v_goals_876_; lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_899_; 
v___x_872_ = lean_st_ref_take(v_a_848_);
v_cache_873_ = lean_ctor_get(v___x_872_, 3);
v_symState_874_ = lean_ctor_get(v___x_872_, 0);
v_grindState_875_ = lean_ctor_get(v___x_872_, 1);
v_goals_876_ = lean_ctor_get(v___x_872_, 2);
v_isSharedCheck_899_ = !lean_is_exclusive(v___x_872_);
if (v_isSharedCheck_899_ == 0)
{
v___x_878_ = v___x_872_;
v_isShared_879_ = v_isSharedCheck_899_;
goto v_resetjp_877_;
}
else
{
lean_inc(v_cache_873_);
lean_inc(v_goals_876_);
lean_inc(v_grindState_875_);
lean_inc(v_symState_874_);
lean_dec(v___x_872_);
v___x_878_ = lean_box(0);
v_isShared_879_ = v_isSharedCheck_899_;
goto v_resetjp_877_;
}
v_resetjp_877_:
{
lean_object* v_backwardRuleName_880_; lean_object* v_backwardRuleSyntax_881_; lean_object* v_simpState_882_; lean_object* v_dsimpState_883_; lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_898_; 
v_backwardRuleName_880_ = lean_ctor_get(v_cache_873_, 0);
v_backwardRuleSyntax_881_ = lean_ctor_get(v_cache_873_, 1);
v_simpState_882_ = lean_ctor_get(v_cache_873_, 2);
v_dsimpState_883_ = lean_ctor_get(v_cache_873_, 3);
v_isSharedCheck_898_ = !lean_is_exclusive(v_cache_873_);
if (v_isSharedCheck_898_ == 0)
{
v___x_885_ = v_cache_873_;
v_isShared_886_ = v_isSharedCheck_898_;
goto v_resetjp_884_;
}
else
{
lean_inc(v_dsimpState_883_);
lean_inc(v_simpState_882_);
lean_inc(v_backwardRuleSyntax_881_);
lean_inc(v_backwardRuleName_880_);
lean_dec(v_cache_873_);
v___x_885_ = lean_box(0);
v_isShared_886_ = v_isSharedCheck_898_;
goto v_resetjp_884_;
}
v_resetjp_884_:
{
lean_object* v___x_887_; lean_object* v___x_889_; 
lean_inc(v_a_868_);
v___x_887_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1___redArg(v_backwardRuleName_880_, v_declName_847_, v_a_868_);
if (v_isShared_886_ == 0)
{
lean_ctor_set(v___x_885_, 0, v___x_887_);
v___x_889_ = v___x_885_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v___x_887_);
lean_ctor_set(v_reuseFailAlloc_897_, 1, v_backwardRuleSyntax_881_);
lean_ctor_set(v_reuseFailAlloc_897_, 2, v_simpState_882_);
lean_ctor_set(v_reuseFailAlloc_897_, 3, v_dsimpState_883_);
v___x_889_ = v_reuseFailAlloc_897_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
lean_object* v___x_891_; 
if (v_isShared_879_ == 0)
{
lean_ctor_set(v___x_878_, 3, v___x_889_);
v___x_891_ = v___x_878_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v_symState_874_);
lean_ctor_set(v_reuseFailAlloc_896_, 1, v_grindState_875_);
lean_ctor_set(v_reuseFailAlloc_896_, 2, v_goals_876_);
lean_ctor_set(v_reuseFailAlloc_896_, 3, v___x_889_);
v___x_891_ = v_reuseFailAlloc_896_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
lean_object* v___x_892_; lean_object* v___x_894_; 
v___x_892_ = lean_st_ref_set(v_a_848_, v___x_891_);
if (v_isShared_871_ == 0)
{
v___x_894_ = v___x_870_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v_a_868_);
v___x_894_ = v_reuseFailAlloc_895_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
return v___x_894_;
}
}
}
}
}
}
}
else
{
lean_dec(v_declName_847_);
return v___x_867_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule___redArg___boxed(lean_object* v_declName_901_, lean_object* v_a_902_, lean_object* v_a_903_, lean_object* v_a_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_){
_start:
{
lean_object* v_res_908_; 
v_res_908_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule___redArg(v_declName_901_, v_a_902_, v_a_903_, v_a_904_, v_a_905_, v_a_906_);
lean_dec(v_a_906_);
lean_dec_ref(v_a_905_);
lean_dec(v_a_904_);
lean_dec_ref(v_a_903_);
lean_dec(v_a_902_);
return v_res_908_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule(lean_object* v_declName_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_, lean_object* v_a_914_, lean_object* v_a_915_, lean_object* v_a_916_, lean_object* v_a_917_){
_start:
{
lean_object* v___x_919_; 
v___x_919_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule___redArg(v_declName_909_, v_a_911_, v_a_914_, v_a_915_, v_a_916_, v_a_917_);
return v___x_919_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule___boxed(lean_object* v_declName_920_, lean_object* v_a_921_, lean_object* v_a_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_, lean_object* v_a_928_, lean_object* v_a_929_){
_start:
{
lean_object* v_res_930_; 
v_res_930_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule(v_declName_920_, v_a_921_, v_a_922_, v_a_923_, v_a_924_, v_a_925_, v_a_926_, v_a_927_, v_a_928_);
lean_dec(v_a_928_);
lean_dec_ref(v_a_927_);
lean_dec(v_a_926_);
lean_dec_ref(v_a_925_);
lean_dec(v_a_924_);
lean_dec_ref(v_a_923_);
lean_dec(v_a_922_);
lean_dec_ref(v_a_921_);
return v_res_930_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0(lean_object* v_00_u03b2_931_, lean_object* v_x_932_, lean_object* v_x_933_){
_start:
{
lean_object* v___x_934_; 
v___x_934_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0___redArg(v_x_932_, v_x_933_);
return v___x_934_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0___boxed(lean_object* v_00_u03b2_935_, lean_object* v_x_936_, lean_object* v_x_937_){
_start:
{
lean_object* v_res_938_; 
v_res_938_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0(v_00_u03b2_935_, v_x_936_, v_x_937_);
lean_dec(v_x_937_);
lean_dec_ref(v_x_936_);
return v_res_938_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1(lean_object* v_00_u03b2_939_, lean_object* v_x_940_, lean_object* v_x_941_, lean_object* v_x_942_){
_start:
{
lean_object* v___x_943_; 
v___x_943_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1___redArg(v_x_940_, v_x_941_, v_x_942_);
return v___x_943_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0_spec__0(lean_object* v_00_u03b2_944_, lean_object* v_x_945_, size_t v_x_946_, lean_object* v_x_947_){
_start:
{
lean_object* v___x_948_; 
v___x_948_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0_spec__0___redArg(v_x_945_, v_x_946_, v_x_947_);
return v___x_948_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0_spec__0___boxed(lean_object* v_00_u03b2_949_, lean_object* v_x_950_, lean_object* v_x_951_, lean_object* v_x_952_){
_start:
{
size_t v_x_2334__boxed_953_; lean_object* v_res_954_; 
v_x_2334__boxed_953_ = lean_unbox_usize(v_x_951_);
lean_dec(v_x_951_);
v_res_954_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0_spec__0(v_00_u03b2_949_, v_x_950_, v_x_2334__boxed_953_, v_x_952_);
lean_dec(v_x_952_);
lean_dec_ref(v_x_950_);
return v_res_954_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2(lean_object* v_00_u03b2_955_, lean_object* v_x_956_, size_t v_x_957_, size_t v_x_958_, lean_object* v_x_959_, lean_object* v_x_960_){
_start:
{
lean_object* v___x_961_; 
v___x_961_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2___redArg(v_x_956_, v_x_957_, v_x_958_, v_x_959_, v_x_960_);
return v___x_961_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2___boxed(lean_object* v_00_u03b2_962_, lean_object* v_x_963_, lean_object* v_x_964_, lean_object* v_x_965_, lean_object* v_x_966_, lean_object* v_x_967_){
_start:
{
size_t v_x_2345__boxed_968_; size_t v_x_2346__boxed_969_; lean_object* v_res_970_; 
v_x_2345__boxed_968_ = lean_unbox_usize(v_x_964_);
lean_dec(v_x_964_);
v_x_2346__boxed_969_ = lean_unbox_usize(v_x_965_);
lean_dec(v_x_965_);
v_res_970_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2(v_00_u03b2_962_, v_x_963_, v_x_2345__boxed_968_, v_x_2346__boxed_969_, v_x_966_, v_x_967_);
return v_res_970_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_971_, lean_object* v_keys_972_, lean_object* v_vals_973_, lean_object* v_heq_974_, lean_object* v_i_975_, lean_object* v_k_976_){
_start:
{
lean_object* v___x_977_; 
v___x_977_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0_spec__0_spec__1___redArg(v_keys_972_, v_vals_973_, v_i_975_, v_k_976_);
return v___x_977_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_978_, lean_object* v_keys_979_, lean_object* v_vals_980_, lean_object* v_heq_981_, lean_object* v_i_982_, lean_object* v_k_983_){
_start:
{
lean_object* v_res_984_; 
v_res_984_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__0_spec__0_spec__1(v_00_u03b2_978_, v_keys_979_, v_vals_980_, v_heq_981_, v_i_982_, v_k_983_);
lean_dec(v_k_983_);
lean_dec_ref(v_vals_980_);
lean_dec_ref(v_keys_979_);
return v_res_984_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_985_, lean_object* v_n_986_, lean_object* v_k_987_, lean_object* v_v_988_){
_start:
{
lean_object* v___x_989_; 
v___x_989_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2_spec__4___redArg(v_n_986_, v_k_987_, v_v_988_);
return v___x_989_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_990_, size_t v_depth_991_, lean_object* v_keys_992_, lean_object* v_vals_993_, lean_object* v_heq_994_, lean_object* v_i_995_, lean_object* v_entries_996_){
_start:
{
lean_object* v___x_997_; 
v___x_997_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2_spec__5___redArg(v_depth_991_, v_keys_992_, v_vals_993_, v_i_995_, v_entries_996_);
return v___x_997_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_998_, lean_object* v_depth_999_, lean_object* v_keys_1000_, lean_object* v_vals_1001_, lean_object* v_heq_1002_, lean_object* v_i_1003_, lean_object* v_entries_1004_){
_start:
{
size_t v_depth_boxed_1005_; lean_object* v_res_1006_; 
v_depth_boxed_1005_ = lean_unbox_usize(v_depth_999_);
lean_dec(v_depth_999_);
v_res_1006_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2_spec__5(v_00_u03b2_998_, v_depth_boxed_1005_, v_keys_1000_, v_vals_1001_, v_heq_1002_, v_i_1003_, v_entries_1004_);
lean_dec_ref(v_vals_1001_);
lean_dec_ref(v_keys_1000_);
return v_res_1006_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_1007_, lean_object* v_x_1008_, lean_object* v_x_1009_, lean_object* v_x_1010_, lean_object* v_x_1011_){
_start:
{
lean_object* v___x_1012_; 
v___x_1012_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule_spec__1_spec__2_spec__4_spec__5___redArg(v_x_1008_, v_x_1009_, v_x_1010_, v_x_1011_);
return v___x_1012_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__1___redArg(lean_object* v_e_1013_, lean_object* v___y_1014_){
_start:
{
uint8_t v___x_1016_; 
v___x_1016_ = l_Lean_Expr_hasMVar(v_e_1013_);
if (v___x_1016_ == 0)
{
lean_object* v___x_1017_; 
v___x_1017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1017_, 0, v_e_1013_);
return v___x_1017_;
}
else
{
lean_object* v___x_1018_; lean_object* v_mctx_1019_; lean_object* v___x_1020_; lean_object* v_fst_1021_; lean_object* v_snd_1022_; lean_object* v___x_1023_; lean_object* v_cache_1024_; lean_object* v_zetaDeltaFVarIds_1025_; lean_object* v_postponed_1026_; lean_object* v_diag_1027_; lean_object* v___x_1029_; uint8_t v_isShared_1030_; uint8_t v_isSharedCheck_1036_; 
v___x_1018_ = lean_st_ref_get(v___y_1014_);
v_mctx_1019_ = lean_ctor_get(v___x_1018_, 0);
lean_inc_ref(v_mctx_1019_);
lean_dec(v___x_1018_);
v___x_1020_ = l_Lean_instantiateMVarsCore(v_mctx_1019_, v_e_1013_);
v_fst_1021_ = lean_ctor_get(v___x_1020_, 0);
lean_inc(v_fst_1021_);
v_snd_1022_ = lean_ctor_get(v___x_1020_, 1);
lean_inc(v_snd_1022_);
lean_dec_ref(v___x_1020_);
v___x_1023_ = lean_st_ref_take(v___y_1014_);
v_cache_1024_ = lean_ctor_get(v___x_1023_, 1);
v_zetaDeltaFVarIds_1025_ = lean_ctor_get(v___x_1023_, 2);
v_postponed_1026_ = lean_ctor_get(v___x_1023_, 3);
v_diag_1027_ = lean_ctor_get(v___x_1023_, 4);
v_isSharedCheck_1036_ = !lean_is_exclusive(v___x_1023_);
if (v_isSharedCheck_1036_ == 0)
{
lean_object* v_unused_1037_; 
v_unused_1037_ = lean_ctor_get(v___x_1023_, 0);
lean_dec(v_unused_1037_);
v___x_1029_ = v___x_1023_;
v_isShared_1030_ = v_isSharedCheck_1036_;
goto v_resetjp_1028_;
}
else
{
lean_inc(v_diag_1027_);
lean_inc(v_postponed_1026_);
lean_inc(v_zetaDeltaFVarIds_1025_);
lean_inc(v_cache_1024_);
lean_dec(v___x_1023_);
v___x_1029_ = lean_box(0);
v_isShared_1030_ = v_isSharedCheck_1036_;
goto v_resetjp_1028_;
}
v_resetjp_1028_:
{
lean_object* v___x_1032_; 
if (v_isShared_1030_ == 0)
{
lean_ctor_set(v___x_1029_, 0, v_snd_1022_);
v___x_1032_ = v___x_1029_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1035_; 
v_reuseFailAlloc_1035_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1035_, 0, v_snd_1022_);
lean_ctor_set(v_reuseFailAlloc_1035_, 1, v_cache_1024_);
lean_ctor_set(v_reuseFailAlloc_1035_, 2, v_zetaDeltaFVarIds_1025_);
lean_ctor_set(v_reuseFailAlloc_1035_, 3, v_postponed_1026_);
lean_ctor_set(v_reuseFailAlloc_1035_, 4, v_diag_1027_);
v___x_1032_ = v_reuseFailAlloc_1035_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
lean_object* v___x_1033_; lean_object* v___x_1034_; 
v___x_1033_ = lean_st_ref_set(v___y_1014_, v___x_1032_);
v___x_1034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1034_, 0, v_fst_1021_);
return v___x_1034_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__1___redArg___boxed(lean_object* v_e_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_){
_start:
{
lean_object* v_res_1041_; 
v_res_1041_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__1___redArg(v_e_1038_, v___y_1039_);
lean_dec(v___y_1039_);
return v_res_1041_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__1(lean_object* v_e_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_){
_start:
{
lean_object* v___x_1052_; 
v___x_1052_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__1___redArg(v_e_1042_, v___y_1048_);
return v___x_1052_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__1___boxed(lean_object* v_e_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_){
_start:
{
lean_object* v_res_1063_; 
v_res_1063_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__1(v_e_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_);
lean_dec(v___y_1061_);
lean_dec_ref(v___y_1060_);
lean_dec(v___y_1059_);
lean_dec_ref(v___y_1058_);
lean_dec(v___y_1057_);
lean_dec_ref(v___y_1056_);
lean_dec(v___y_1055_);
lean_dec_ref(v___y_1054_);
return v_res_1063_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm___lam__0(lean_object* v_term_1064_, lean_object* v___x_1065_, uint8_t v___x_1066_, uint8_t v___x_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_){
_start:
{
lean_object* v___x_1077_; 
v___x_1077_ = l_Lean_Elab_Term_elabTerm(v_term_1064_, v___x_1065_, v___x_1066_, v___x_1066_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_);
if (lean_obj_tag(v___x_1077_) == 0)
{
lean_object* v_a_1078_; uint8_t v___x_1079_; lean_object* v___x_1080_; 
v_a_1078_ = lean_ctor_get(v___x_1077_, 0);
lean_inc(v_a_1078_);
lean_dec_ref_known(v___x_1077_, 1);
v___x_1079_ = 1;
v___x_1080_ = l_Lean_Elab_Term_synthesizeSyntheticMVars(v___x_1079_, v___x_1067_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_);
if (lean_obj_tag(v___x_1080_) == 0)
{
lean_object* v___x_1081_; 
lean_dec_ref_known(v___x_1080_, 1);
v___x_1081_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__1___redArg(v_a_1078_, v___y_1073_);
return v___x_1081_;
}
else
{
lean_object* v_a_1082_; lean_object* v___x_1084_; uint8_t v_isShared_1085_; uint8_t v_isSharedCheck_1089_; 
lean_dec(v_a_1078_);
v_a_1082_ = lean_ctor_get(v___x_1080_, 0);
v_isSharedCheck_1089_ = !lean_is_exclusive(v___x_1080_);
if (v_isSharedCheck_1089_ == 0)
{
v___x_1084_ = v___x_1080_;
v_isShared_1085_ = v_isSharedCheck_1089_;
goto v_resetjp_1083_;
}
else
{
lean_inc(v_a_1082_);
lean_dec(v___x_1080_);
v___x_1084_ = lean_box(0);
v_isShared_1085_ = v_isSharedCheck_1089_;
goto v_resetjp_1083_;
}
v_resetjp_1083_:
{
lean_object* v___x_1087_; 
if (v_isShared_1085_ == 0)
{
v___x_1087_ = v___x_1084_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v_a_1082_);
v___x_1087_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
return v___x_1087_;
}
}
}
}
else
{
return v___x_1077_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm___lam__0___boxed(lean_object* v_term_1090_, lean_object* v___x_1091_, lean_object* v___x_1092_, lean_object* v___x_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_){
_start:
{
uint8_t v___x_3483__boxed_1103_; uint8_t v___x_3484__boxed_1104_; lean_object* v_res_1105_; 
v___x_3483__boxed_1103_ = lean_unbox(v___x_1092_);
v___x_3484__boxed_1104_ = lean_unbox(v___x_1093_);
v_res_1105_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm___lam__0(v_term_1090_, v___x_1091_, v___x_3483__boxed_1103_, v___x_3484__boxed_1104_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_);
lean_dec(v___y_1101_);
lean_dec_ref(v___y_1100_);
lean_dec(v___y_1099_);
lean_dec_ref(v___y_1098_);
lean_dec(v___y_1097_);
lean_dec_ref(v___y_1096_);
lean_dec(v___y_1095_);
lean_dec_ref(v___y_1094_);
return v_res_1105_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3_spec__5_spec__6___redArg(lean_object* v_x_1106_, lean_object* v_x_1107_, lean_object* v_x_1108_, lean_object* v_x_1109_){
_start:
{
lean_object* v_ks_1110_; lean_object* v_vs_1111_; lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1140_; 
v_ks_1110_ = lean_ctor_get(v_x_1106_, 0);
v_vs_1111_ = lean_ctor_get(v_x_1106_, 1);
v_isSharedCheck_1140_ = !lean_is_exclusive(v_x_1106_);
if (v_isSharedCheck_1140_ == 0)
{
v___x_1113_ = v_x_1106_;
v_isShared_1114_ = v_isSharedCheck_1140_;
goto v_resetjp_1112_;
}
else
{
lean_inc(v_vs_1111_);
lean_inc(v_ks_1110_);
lean_dec(v_x_1106_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1140_;
goto v_resetjp_1112_;
}
v_resetjp_1112_:
{
uint8_t v___y_1116_; lean_object* v___x_1128_; uint8_t v___x_1129_; 
v___x_1128_ = lean_array_get_size(v_ks_1110_);
v___x_1129_ = lean_nat_dec_lt(v_x_1107_, v___x_1128_);
if (v___x_1129_ == 0)
{
lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; 
lean_del_object(v___x_1113_);
lean_dec(v_x_1107_);
v___x_1130_ = lean_array_push(v_ks_1110_, v_x_1108_);
v___x_1131_ = lean_array_push(v_vs_1111_, v_x_1109_);
v___x_1132_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1132_, 0, v___x_1130_);
lean_ctor_set(v___x_1132_, 1, v___x_1131_);
return v___x_1132_;
}
else
{
lean_object* v_fst_1133_; lean_object* v_snd_1134_; lean_object* v_k_x27_1135_; lean_object* v_fst_1136_; lean_object* v_snd_1137_; uint8_t v___x_1138_; 
v_fst_1133_ = lean_ctor_get(v_x_1108_, 0);
v_snd_1134_ = lean_ctor_get(v_x_1108_, 1);
v_k_x27_1135_ = lean_array_fget_borrowed(v_ks_1110_, v_x_1107_);
v_fst_1136_ = lean_ctor_get(v_k_x27_1135_, 0);
v_snd_1137_ = lean_ctor_get(v_k_x27_1135_, 1);
v___x_1138_ = lean_nat_dec_eq(v_fst_1133_, v_fst_1136_);
if (v___x_1138_ == 0)
{
v___y_1116_ = v___x_1138_;
goto v___jp_1115_;
}
else
{
uint8_t v___x_1139_; 
v___x_1139_ = lean_nat_dec_eq(v_snd_1134_, v_snd_1137_);
v___y_1116_ = v___x_1139_;
goto v___jp_1115_;
}
}
v___jp_1115_:
{
if (v___y_1116_ == 0)
{
lean_object* v___x_1118_; 
if (v_isShared_1114_ == 0)
{
v___x_1118_ = v___x_1113_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1122_; 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v_ks_1110_);
lean_ctor_set(v_reuseFailAlloc_1122_, 1, v_vs_1111_);
v___x_1118_ = v_reuseFailAlloc_1122_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
lean_object* v___x_1119_; lean_object* v___x_1120_; 
v___x_1119_ = lean_unsigned_to_nat(1u);
v___x_1120_ = lean_nat_add(v_x_1107_, v___x_1119_);
lean_dec(v_x_1107_);
v_x_1106_ = v___x_1118_;
v_x_1107_ = v___x_1120_;
goto _start;
}
}
else
{
lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1126_; 
v___x_1123_ = lean_array_fset(v_ks_1110_, v_x_1107_, v_x_1108_);
v___x_1124_ = lean_array_fset(v_vs_1111_, v_x_1107_, v_x_1109_);
lean_dec(v_x_1107_);
if (v_isShared_1114_ == 0)
{
lean_ctor_set(v___x_1113_, 1, v___x_1124_);
lean_ctor_set(v___x_1113_, 0, v___x_1123_);
v___x_1126_ = v___x_1113_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v___x_1123_);
lean_ctor_set(v_reuseFailAlloc_1127_, 1, v___x_1124_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3_spec__5___redArg(lean_object* v_n_1141_, lean_object* v_k_1142_, lean_object* v_v_1143_){
_start:
{
lean_object* v___x_1144_; lean_object* v___x_1145_; 
v___x_1144_ = lean_unsigned_to_nat(0u);
v___x_1145_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3_spec__5_spec__6___redArg(v_n_1141_, v___x_1144_, v_k_1142_, v_v_1143_);
return v___x_1145_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_1146_; 
v___x_1146_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1146_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3___redArg(lean_object* v_x_1147_, size_t v_x_1148_, size_t v_x_1149_, lean_object* v_x_1150_, lean_object* v_x_1151_){
_start:
{
if (lean_obj_tag(v_x_1147_) == 0)
{
lean_object* v_es_1152_; size_t v___x_1153_; size_t v___x_1154_; lean_object* v_j_1155_; lean_object* v___x_1156_; uint8_t v___x_1157_; 
v_es_1152_ = lean_ctor_get(v_x_1147_, 0);
v___x_1153_ = ((size_t)31ULL);
v___x_1154_ = lean_usize_land(v_x_1148_, v___x_1153_);
v_j_1155_ = lean_usize_to_nat(v___x_1154_);
v___x_1156_ = lean_array_get_size(v_es_1152_);
v___x_1157_ = lean_nat_dec_lt(v_j_1155_, v___x_1156_);
if (v___x_1157_ == 0)
{
lean_dec(v_j_1155_);
lean_dec(v_x_1151_);
lean_dec_ref(v_x_1150_);
return v_x_1147_;
}
else
{
lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1203_; 
lean_inc_ref(v_es_1152_);
v_isSharedCheck_1203_ = !lean_is_exclusive(v_x_1147_);
if (v_isSharedCheck_1203_ == 0)
{
lean_object* v_unused_1204_; 
v_unused_1204_ = lean_ctor_get(v_x_1147_, 0);
lean_dec(v_unused_1204_);
v___x_1159_ = v_x_1147_;
v_isShared_1160_ = v_isSharedCheck_1203_;
goto v_resetjp_1158_;
}
else
{
lean_dec(v_x_1147_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1203_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
lean_object* v_v_1161_; lean_object* v___x_1162_; lean_object* v_xs_x27_1163_; lean_object* v___y_1165_; 
v_v_1161_ = lean_array_fget(v_es_1152_, v_j_1155_);
v___x_1162_ = lean_box(0);
v_xs_x27_1163_ = lean_array_fset(v_es_1152_, v_j_1155_, v___x_1162_);
switch(lean_obj_tag(v_v_1161_))
{
case 0:
{
lean_object* v_key_1170_; lean_object* v_val_1171_; lean_object* v___x_1173_; uint8_t v_isShared_1174_; uint8_t v_isSharedCheck_1188_; 
v_key_1170_ = lean_ctor_get(v_v_1161_, 0);
v_val_1171_ = lean_ctor_get(v_v_1161_, 1);
v_isSharedCheck_1188_ = !lean_is_exclusive(v_v_1161_);
if (v_isSharedCheck_1188_ == 0)
{
v___x_1173_ = v_v_1161_;
v_isShared_1174_ = v_isSharedCheck_1188_;
goto v_resetjp_1172_;
}
else
{
lean_inc(v_val_1171_);
lean_inc(v_key_1170_);
lean_dec(v_v_1161_);
v___x_1173_ = lean_box(0);
v_isShared_1174_ = v_isSharedCheck_1188_;
goto v_resetjp_1172_;
}
v_resetjp_1172_:
{
uint8_t v___y_1176_; lean_object* v_fst_1182_; lean_object* v_snd_1183_; lean_object* v_fst_1184_; lean_object* v_snd_1185_; uint8_t v___x_1186_; 
v_fst_1182_ = lean_ctor_get(v_x_1150_, 0);
v_snd_1183_ = lean_ctor_get(v_x_1150_, 1);
v_fst_1184_ = lean_ctor_get(v_key_1170_, 0);
v_snd_1185_ = lean_ctor_get(v_key_1170_, 1);
v___x_1186_ = lean_nat_dec_eq(v_fst_1182_, v_fst_1184_);
if (v___x_1186_ == 0)
{
v___y_1176_ = v___x_1186_;
goto v___jp_1175_;
}
else
{
uint8_t v___x_1187_; 
v___x_1187_ = lean_nat_dec_eq(v_snd_1183_, v_snd_1185_);
v___y_1176_ = v___x_1187_;
goto v___jp_1175_;
}
v___jp_1175_:
{
if (v___y_1176_ == 0)
{
lean_object* v___x_1177_; lean_object* v___x_1178_; 
lean_del_object(v___x_1173_);
v___x_1177_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1170_, v_val_1171_, v_x_1150_, v_x_1151_);
v___x_1178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1178_, 0, v___x_1177_);
v___y_1165_ = v___x_1178_;
goto v___jp_1164_;
}
else
{
lean_object* v___x_1180_; 
lean_dec(v_val_1171_);
lean_dec(v_key_1170_);
if (v_isShared_1174_ == 0)
{
lean_ctor_set(v___x_1173_, 1, v_x_1151_);
lean_ctor_set(v___x_1173_, 0, v_x_1150_);
v___x_1180_ = v___x_1173_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v_x_1150_);
lean_ctor_set(v_reuseFailAlloc_1181_, 1, v_x_1151_);
v___x_1180_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
v___y_1165_ = v___x_1180_;
goto v___jp_1164_;
}
}
}
}
}
case 1:
{
lean_object* v_node_1189_; lean_object* v___x_1191_; uint8_t v_isShared_1192_; uint8_t v_isSharedCheck_1201_; 
v_node_1189_ = lean_ctor_get(v_v_1161_, 0);
v_isSharedCheck_1201_ = !lean_is_exclusive(v_v_1161_);
if (v_isSharedCheck_1201_ == 0)
{
v___x_1191_ = v_v_1161_;
v_isShared_1192_ = v_isSharedCheck_1201_;
goto v_resetjp_1190_;
}
else
{
lean_inc(v_node_1189_);
lean_dec(v_v_1161_);
v___x_1191_ = lean_box(0);
v_isShared_1192_ = v_isSharedCheck_1201_;
goto v_resetjp_1190_;
}
v_resetjp_1190_:
{
size_t v___x_1193_; size_t v___x_1194_; size_t v___x_1195_; size_t v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1199_; 
v___x_1193_ = ((size_t)5ULL);
v___x_1194_ = lean_usize_shift_right(v_x_1148_, v___x_1193_);
v___x_1195_ = ((size_t)1ULL);
v___x_1196_ = lean_usize_add(v_x_1149_, v___x_1195_);
v___x_1197_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3___redArg(v_node_1189_, v___x_1194_, v___x_1196_, v_x_1150_, v_x_1151_);
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
v___y_1165_ = v___x_1199_;
goto v___jp_1164_;
}
}
}
default: 
{
lean_object* v___x_1202_; 
v___x_1202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1202_, 0, v_x_1150_);
lean_ctor_set(v___x_1202_, 1, v_x_1151_);
v___y_1165_ = v___x_1202_;
goto v___jp_1164_;
}
}
v___jp_1164_:
{
lean_object* v___x_1166_; lean_object* v___x_1168_; 
v___x_1166_ = lean_array_fset(v_xs_x27_1163_, v_j_1155_, v___y_1165_);
lean_dec(v_j_1155_);
if (v_isShared_1160_ == 0)
{
lean_ctor_set(v___x_1159_, 0, v___x_1166_);
v___x_1168_ = v___x_1159_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v___x_1166_);
v___x_1168_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1167_;
}
v_reusejp_1167_:
{
return v___x_1168_;
}
}
}
}
}
else
{
lean_object* v_ks_1205_; lean_object* v_vs_1206_; lean_object* v___x_1208_; uint8_t v_isShared_1209_; uint8_t v_isSharedCheck_1226_; 
v_ks_1205_ = lean_ctor_get(v_x_1147_, 0);
v_vs_1206_ = lean_ctor_get(v_x_1147_, 1);
v_isSharedCheck_1226_ = !lean_is_exclusive(v_x_1147_);
if (v_isSharedCheck_1226_ == 0)
{
v___x_1208_ = v_x_1147_;
v_isShared_1209_ = v_isSharedCheck_1226_;
goto v_resetjp_1207_;
}
else
{
lean_inc(v_vs_1206_);
lean_inc(v_ks_1205_);
lean_dec(v_x_1147_);
v___x_1208_ = lean_box(0);
v_isShared_1209_ = v_isSharedCheck_1226_;
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
lean_object* v_reuseFailAlloc_1225_; 
v_reuseFailAlloc_1225_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1225_, 0, v_ks_1205_);
lean_ctor_set(v_reuseFailAlloc_1225_, 1, v_vs_1206_);
v___x_1211_ = v_reuseFailAlloc_1225_;
goto v_reusejp_1210_;
}
v_reusejp_1210_:
{
lean_object* v_newNode_1212_; uint8_t v___y_1214_; size_t v___x_1220_; uint8_t v___x_1221_; 
v_newNode_1212_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3_spec__5___redArg(v___x_1211_, v_x_1150_, v_x_1151_);
v___x_1220_ = ((size_t)7ULL);
v___x_1221_ = lean_usize_dec_le(v___x_1220_, v_x_1149_);
if (v___x_1221_ == 0)
{
lean_object* v___x_1222_; lean_object* v___x_1223_; uint8_t v___x_1224_; 
v___x_1222_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1212_);
v___x_1223_ = lean_unsigned_to_nat(4u);
v___x_1224_ = lean_nat_dec_lt(v___x_1222_, v___x_1223_);
lean_dec(v___x_1222_);
v___y_1214_ = v___x_1224_;
goto v___jp_1213_;
}
else
{
v___y_1214_ = v___x_1221_;
goto v___jp_1213_;
}
v___jp_1213_:
{
if (v___y_1214_ == 0)
{
lean_object* v_ks_1215_; lean_object* v_vs_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; 
v_ks_1215_ = lean_ctor_get(v_newNode_1212_, 0);
lean_inc_ref(v_ks_1215_);
v_vs_1216_ = lean_ctor_get(v_newNode_1212_, 1);
lean_inc_ref(v_vs_1216_);
lean_dec_ref(v_newNode_1212_);
v___x_1217_ = lean_unsigned_to_nat(0u);
v___x_1218_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3___redArg___closed__0);
v___x_1219_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3_spec__6___redArg(v_x_1149_, v_ks_1215_, v_vs_1216_, v___x_1217_, v___x_1218_);
lean_dec_ref(v_vs_1216_);
lean_dec_ref(v_ks_1215_);
return v___x_1219_;
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
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3_spec__6___redArg(size_t v_depth_1227_, lean_object* v_keys_1228_, lean_object* v_vals_1229_, lean_object* v_i_1230_, lean_object* v_entries_1231_){
_start:
{
lean_object* v___x_1232_; uint8_t v___x_1233_; 
v___x_1232_ = lean_array_get_size(v_keys_1228_);
v___x_1233_ = lean_nat_dec_lt(v_i_1230_, v___x_1232_);
if (v___x_1233_ == 0)
{
lean_dec(v_i_1230_);
return v_entries_1231_;
}
else
{
lean_object* v_k_1234_; lean_object* v_fst_1235_; lean_object* v_snd_1236_; lean_object* v_v_1237_; uint64_t v___x_1238_; uint64_t v___x_1239_; uint64_t v___x_1240_; size_t v_h_1241_; size_t v___x_1242_; lean_object* v___x_1243_; size_t v___x_1244_; size_t v___x_1245_; size_t v___x_1246_; size_t v_h_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; 
v_k_1234_ = lean_array_fget_borrowed(v_keys_1228_, v_i_1230_);
v_fst_1235_ = lean_ctor_get(v_k_1234_, 0);
v_snd_1236_ = lean_ctor_get(v_k_1234_, 1);
v_v_1237_ = lean_array_fget_borrowed(v_vals_1229_, v_i_1230_);
v___x_1238_ = lean_uint64_of_nat(v_fst_1235_);
v___x_1239_ = lean_uint64_of_nat(v_snd_1236_);
v___x_1240_ = lean_uint64_mix_hash(v___x_1238_, v___x_1239_);
v_h_1241_ = lean_uint64_to_usize(v___x_1240_);
v___x_1242_ = ((size_t)5ULL);
v___x_1243_ = lean_unsigned_to_nat(1u);
v___x_1244_ = ((size_t)1ULL);
v___x_1245_ = lean_usize_sub(v_depth_1227_, v___x_1244_);
v___x_1246_ = lean_usize_mul(v___x_1242_, v___x_1245_);
v_h_1247_ = lean_usize_shift_right(v_h_1241_, v___x_1246_);
v___x_1248_ = lean_nat_add(v_i_1230_, v___x_1243_);
lean_dec(v_i_1230_);
lean_inc(v_v_1237_);
lean_inc(v_k_1234_);
v___x_1249_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3___redArg(v_entries_1231_, v_h_1247_, v_depth_1227_, v_k_1234_, v_v_1237_);
v_i_1230_ = v___x_1248_;
v_entries_1231_ = v___x_1249_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_depth_1251_, lean_object* v_keys_1252_, lean_object* v_vals_1253_, lean_object* v_i_1254_, lean_object* v_entries_1255_){
_start:
{
size_t v_depth_boxed_1256_; lean_object* v_res_1257_; 
v_depth_boxed_1256_ = lean_unbox_usize(v_depth_1251_);
lean_dec(v_depth_1251_);
v_res_1257_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3_spec__6___redArg(v_depth_boxed_1256_, v_keys_1252_, v_vals_1253_, v_i_1254_, v_entries_1255_);
lean_dec_ref(v_vals_1253_);
lean_dec_ref(v_keys_1252_);
return v_res_1257_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3___redArg___boxed(lean_object* v_x_1258_, lean_object* v_x_1259_, lean_object* v_x_1260_, lean_object* v_x_1261_, lean_object* v_x_1262_){
_start:
{
size_t v_x_3637__boxed_1263_; size_t v_x_3638__boxed_1264_; lean_object* v_res_1265_; 
v_x_3637__boxed_1263_ = lean_unbox_usize(v_x_1259_);
lean_dec(v_x_1259_);
v_x_3638__boxed_1264_ = lean_unbox_usize(v_x_1260_);
lean_dec(v_x_1260_);
v_res_1265_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3___redArg(v_x_1258_, v_x_3637__boxed_1263_, v_x_3638__boxed_1264_, v_x_1261_, v_x_1262_);
return v_res_1265_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2___redArg(lean_object* v_x_1266_, lean_object* v_x_1267_, lean_object* v_x_1268_){
_start:
{
lean_object* v_fst_1269_; lean_object* v_snd_1270_; uint64_t v___x_1271_; uint64_t v___x_1272_; uint64_t v___x_1273_; size_t v___x_1274_; size_t v___x_1275_; lean_object* v___x_1276_; 
v_fst_1269_ = lean_ctor_get(v_x_1267_, 0);
v_snd_1270_ = lean_ctor_get(v_x_1267_, 1);
v___x_1271_ = lean_uint64_of_nat(v_fst_1269_);
v___x_1272_ = lean_uint64_of_nat(v_snd_1270_);
v___x_1273_ = lean_uint64_mix_hash(v___x_1271_, v___x_1272_);
v___x_1274_ = lean_uint64_to_usize(v___x_1273_);
v___x_1275_ = ((size_t)1ULL);
v___x_1276_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3___redArg(v_x_1266_, v___x_1274_, v___x_1275_, v_x_1267_, v_x_1268_);
return v___x_1276_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0_spec__0_spec__2___redArg(lean_object* v_keys_1277_, lean_object* v_vals_1278_, lean_object* v_i_1279_, lean_object* v_k_1280_){
_start:
{
uint8_t v___y_1282_; lean_object* v___x_1288_; uint8_t v___x_1289_; 
v___x_1288_ = lean_array_get_size(v_keys_1277_);
v___x_1289_ = lean_nat_dec_lt(v_i_1279_, v___x_1288_);
if (v___x_1289_ == 0)
{
lean_object* v___x_1290_; 
lean_dec(v_i_1279_);
v___x_1290_ = lean_box(0);
return v___x_1290_;
}
else
{
lean_object* v_fst_1291_; lean_object* v_snd_1292_; lean_object* v_k_x27_1293_; lean_object* v_fst_1294_; lean_object* v_snd_1295_; uint8_t v___x_1296_; 
v_fst_1291_ = lean_ctor_get(v_k_1280_, 0);
v_snd_1292_ = lean_ctor_get(v_k_1280_, 1);
v_k_x27_1293_ = lean_array_fget_borrowed(v_keys_1277_, v_i_1279_);
v_fst_1294_ = lean_ctor_get(v_k_x27_1293_, 0);
v_snd_1295_ = lean_ctor_get(v_k_x27_1293_, 1);
v___x_1296_ = lean_nat_dec_eq(v_fst_1291_, v_fst_1294_);
if (v___x_1296_ == 0)
{
v___y_1282_ = v___x_1296_;
goto v___jp_1281_;
}
else
{
uint8_t v___x_1297_; 
v___x_1297_ = lean_nat_dec_eq(v_snd_1292_, v_snd_1295_);
v___y_1282_ = v___x_1297_;
goto v___jp_1281_;
}
}
v___jp_1281_:
{
if (v___y_1282_ == 0)
{
lean_object* v___x_1283_; lean_object* v___x_1284_; 
v___x_1283_ = lean_unsigned_to_nat(1u);
v___x_1284_ = lean_nat_add(v_i_1279_, v___x_1283_);
lean_dec(v_i_1279_);
v_i_1279_ = v___x_1284_;
goto _start;
}
else
{
lean_object* v___x_1286_; lean_object* v___x_1287_; 
v___x_1286_ = lean_array_fget_borrowed(v_vals_1278_, v_i_1279_);
lean_dec(v_i_1279_);
lean_inc(v___x_1286_);
v___x_1287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1287_, 0, v___x_1286_);
return v___x_1287_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_keys_1298_, lean_object* v_vals_1299_, lean_object* v_i_1300_, lean_object* v_k_1301_){
_start:
{
lean_object* v_res_1302_; 
v_res_1302_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0_spec__0_spec__2___redArg(v_keys_1298_, v_vals_1299_, v_i_1300_, v_k_1301_);
lean_dec_ref(v_k_1301_);
lean_dec_ref(v_vals_1299_);
lean_dec_ref(v_keys_1298_);
return v_res_1302_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0_spec__0___redArg(lean_object* v_x_1303_, size_t v_x_1304_, lean_object* v_x_1305_){
_start:
{
if (lean_obj_tag(v_x_1303_) == 0)
{
lean_object* v_es_1306_; lean_object* v___x_1307_; size_t v___x_1308_; size_t v___x_1309_; lean_object* v_j_1310_; lean_object* v___x_1311_; 
v_es_1306_ = lean_ctor_get(v_x_1303_, 0);
v___x_1307_ = lean_box(2);
v___x_1308_ = ((size_t)31ULL);
v___x_1309_ = lean_usize_land(v_x_1304_, v___x_1308_);
v_j_1310_ = lean_usize_to_nat(v___x_1309_);
v___x_1311_ = lean_array_get_borrowed(v___x_1307_, v_es_1306_, v_j_1310_);
lean_dec(v_j_1310_);
switch(lean_obj_tag(v___x_1311_))
{
case 0:
{
lean_object* v_key_1312_; lean_object* v_val_1313_; uint8_t v___y_1315_; lean_object* v_fst_1318_; lean_object* v_snd_1319_; lean_object* v_fst_1320_; lean_object* v_snd_1321_; uint8_t v___x_1322_; 
v_key_1312_ = lean_ctor_get(v___x_1311_, 0);
v_val_1313_ = lean_ctor_get(v___x_1311_, 1);
v_fst_1318_ = lean_ctor_get(v_x_1305_, 0);
v_snd_1319_ = lean_ctor_get(v_x_1305_, 1);
v_fst_1320_ = lean_ctor_get(v_key_1312_, 0);
v_snd_1321_ = lean_ctor_get(v_key_1312_, 1);
v___x_1322_ = lean_nat_dec_eq(v_fst_1318_, v_fst_1320_);
if (v___x_1322_ == 0)
{
v___y_1315_ = v___x_1322_;
goto v___jp_1314_;
}
else
{
uint8_t v___x_1323_; 
v___x_1323_ = lean_nat_dec_eq(v_snd_1319_, v_snd_1321_);
v___y_1315_ = v___x_1323_;
goto v___jp_1314_;
}
v___jp_1314_:
{
if (v___y_1315_ == 0)
{
lean_object* v___x_1316_; 
v___x_1316_ = lean_box(0);
return v___x_1316_;
}
else
{
lean_object* v___x_1317_; 
lean_inc(v_val_1313_);
v___x_1317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1317_, 0, v_val_1313_);
return v___x_1317_;
}
}
}
case 1:
{
lean_object* v_node_1324_; size_t v___x_1325_; size_t v___x_1326_; 
v_node_1324_ = lean_ctor_get(v___x_1311_, 0);
v___x_1325_ = ((size_t)5ULL);
v___x_1326_ = lean_usize_shift_right(v_x_1304_, v___x_1325_);
v_x_1303_ = v_node_1324_;
v_x_1304_ = v___x_1326_;
goto _start;
}
default: 
{
lean_object* v___x_1328_; 
v___x_1328_ = lean_box(0);
return v___x_1328_;
}
}
}
else
{
lean_object* v_ks_1329_; lean_object* v_vs_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; 
v_ks_1329_ = lean_ctor_get(v_x_1303_, 0);
v_vs_1330_ = lean_ctor_get(v_x_1303_, 1);
v___x_1331_ = lean_unsigned_to_nat(0u);
v___x_1332_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0_spec__0_spec__2___redArg(v_ks_1329_, v_vs_1330_, v___x_1331_, v_x_1305_);
return v___x_1332_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0_spec__0___redArg___boxed(lean_object* v_x_1333_, lean_object* v_x_1334_, lean_object* v_x_1335_){
_start:
{
size_t v_x_3865__boxed_1336_; lean_object* v_res_1337_; 
v_x_3865__boxed_1336_ = lean_unbox_usize(v_x_1334_);
lean_dec(v_x_1334_);
v_res_1337_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0_spec__0___redArg(v_x_1333_, v_x_3865__boxed_1336_, v_x_1335_);
lean_dec_ref(v_x_1335_);
lean_dec_ref(v_x_1333_);
return v_res_1337_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0___redArg(lean_object* v_x_1338_, lean_object* v_x_1339_){
_start:
{
lean_object* v_fst_1340_; lean_object* v_snd_1341_; uint64_t v___x_1342_; uint64_t v___x_1343_; uint64_t v___x_1344_; size_t v___x_1345_; lean_object* v___x_1346_; 
v_fst_1340_ = lean_ctor_get(v_x_1339_, 0);
v_snd_1341_ = lean_ctor_get(v_x_1339_, 1);
v___x_1342_ = lean_uint64_of_nat(v_fst_1340_);
v___x_1343_ = lean_uint64_of_nat(v_snd_1341_);
v___x_1344_ = lean_uint64_mix_hash(v___x_1342_, v___x_1343_);
v___x_1345_ = lean_uint64_to_usize(v___x_1344_);
v___x_1346_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0_spec__0___redArg(v_x_1338_, v___x_1345_, v_x_1339_);
return v___x_1346_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0___redArg___boxed(lean_object* v_x_1347_, lean_object* v_x_1348_){
_start:
{
lean_object* v_res_1349_; 
v_res_1349_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0___redArg(v_x_1347_, v_x_1348_);
lean_dec_ref(v_x_1348_);
lean_dec_ref(v_x_1347_);
return v_res_1349_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm(lean_object* v_term_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_, lean_object* v_a_1357_, lean_object* v_a_1358_){
_start:
{
uint8_t v___x_1360_; lean_object* v___y_1362_; lean_object* v___y_1363_; lean_object* v___y_1428_; lean_object* v___x_1432_; 
v___x_1360_ = 0;
v___x_1432_ = l_Lean_Syntax_getPos_x3f(v_term_1350_, v___x_1360_);
if (lean_obj_tag(v___x_1432_) == 0)
{
lean_object* v___x_1433_; 
v___x_1433_ = lean_unsigned_to_nat(0u);
v___y_1428_ = v___x_1433_;
goto v___jp_1427_;
}
else
{
lean_object* v_val_1434_; 
v_val_1434_ = lean_ctor_get(v___x_1432_, 0);
lean_inc(v_val_1434_);
lean_dec_ref_known(v___x_1432_, 1);
v___y_1428_ = v_val_1434_;
goto v___jp_1427_;
}
v___jp_1361_:
{
lean_object* v___x_1364_; lean_object* v_cache_1365_; lean_object* v_backwardRuleSyntax_1366_; lean_object* v_pos_1367_; lean_object* v___x_1368_; 
v___x_1364_ = lean_st_ref_get(v_a_1352_);
v_cache_1365_ = lean_ctor_get(v___x_1364_, 3);
lean_inc_ref(v_cache_1365_);
lean_dec(v___x_1364_);
v_backwardRuleSyntax_1366_ = lean_ctor_get(v_cache_1365_, 1);
lean_inc_ref(v_backwardRuleSyntax_1366_);
lean_dec_ref(v_cache_1365_);
v_pos_1367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_pos_1367_, 0, v___y_1362_);
lean_ctor_set(v_pos_1367_, 1, v___y_1363_);
v___x_1368_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0___redArg(v_backwardRuleSyntax_1366_, v_pos_1367_);
lean_dec_ref(v_backwardRuleSyntax_1366_);
if (lean_obj_tag(v___x_1368_) == 1)
{
lean_object* v_val_1369_; lean_object* v___x_1371_; uint8_t v_isShared_1372_; uint8_t v_isSharedCheck_1376_; 
lean_dec_ref_known(v_pos_1367_, 2);
lean_dec(v_term_1350_);
v_val_1369_ = lean_ctor_get(v___x_1368_, 0);
v_isSharedCheck_1376_ = !lean_is_exclusive(v___x_1368_);
if (v_isSharedCheck_1376_ == 0)
{
v___x_1371_ = v___x_1368_;
v_isShared_1372_ = v_isSharedCheck_1376_;
goto v_resetjp_1370_;
}
else
{
lean_inc(v_val_1369_);
lean_dec(v___x_1368_);
v___x_1371_ = lean_box(0);
v_isShared_1372_ = v_isSharedCheck_1376_;
goto v_resetjp_1370_;
}
v_resetjp_1370_:
{
lean_object* v___x_1374_; 
if (v_isShared_1372_ == 0)
{
lean_ctor_set_tag(v___x_1371_, 0);
v___x_1374_ = v___x_1371_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1375_; 
v_reuseFailAlloc_1375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1375_, 0, v_val_1369_);
v___x_1374_ = v_reuseFailAlloc_1375_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
return v___x_1374_;
}
}
}
else
{
lean_object* v___x_1377_; uint8_t v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___f_1381_; lean_object* v___x_1382_; 
lean_dec(v___x_1368_);
v___x_1377_ = lean_box(0);
v___x_1378_ = 1;
v___x_1379_ = lean_box(v___x_1378_);
v___x_1380_ = lean_box(v___x_1360_);
v___f_1381_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm___lam__0___boxed), 13, 4);
lean_closure_set(v___f_1381_, 0, v_term_1350_);
lean_closure_set(v___f_1381_, 1, v___x_1377_);
lean_closure_set(v___f_1381_, 2, v___x_1379_);
lean_closure_set(v___f_1381_, 3, v___x_1380_);
v___x_1382_ = l_Lean_Elab_Tactic_Grind_withMainContext___redArg(v___f_1381_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_);
if (lean_obj_tag(v___x_1382_) == 0)
{
lean_object* v_a_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; 
v_a_1383_ = lean_ctor_get(v___x_1382_, 0);
lean_inc(v_a_1383_);
lean_dec_ref_known(v___x_1382_, 1);
v___x_1384_ = lean_box(0);
v___x_1385_ = l_Lean_Meta_Sym_mkBackwardRuleFromExpr(v_a_1383_, v___x_1384_, v___x_1377_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_);
if (lean_obj_tag(v___x_1385_) == 0)
{
lean_object* v_a_1386_; lean_object* v___x_1388_; uint8_t v_isShared_1389_; uint8_t v_isSharedCheck_1418_; 
v_a_1386_ = lean_ctor_get(v___x_1385_, 0);
v_isSharedCheck_1418_ = !lean_is_exclusive(v___x_1385_);
if (v_isSharedCheck_1418_ == 0)
{
v___x_1388_ = v___x_1385_;
v_isShared_1389_ = v_isSharedCheck_1418_;
goto v_resetjp_1387_;
}
else
{
lean_inc(v_a_1386_);
lean_dec(v___x_1385_);
v___x_1388_ = lean_box(0);
v_isShared_1389_ = v_isSharedCheck_1418_;
goto v_resetjp_1387_;
}
v_resetjp_1387_:
{
lean_object* v___x_1390_; lean_object* v_cache_1391_; lean_object* v_symState_1392_; lean_object* v_grindState_1393_; lean_object* v_goals_1394_; lean_object* v___x_1396_; uint8_t v_isShared_1397_; uint8_t v_isSharedCheck_1417_; 
v___x_1390_ = lean_st_ref_take(v_a_1352_);
v_cache_1391_ = lean_ctor_get(v___x_1390_, 3);
v_symState_1392_ = lean_ctor_get(v___x_1390_, 0);
v_grindState_1393_ = lean_ctor_get(v___x_1390_, 1);
v_goals_1394_ = lean_ctor_get(v___x_1390_, 2);
v_isSharedCheck_1417_ = !lean_is_exclusive(v___x_1390_);
if (v_isSharedCheck_1417_ == 0)
{
v___x_1396_ = v___x_1390_;
v_isShared_1397_ = v_isSharedCheck_1417_;
goto v_resetjp_1395_;
}
else
{
lean_inc(v_cache_1391_);
lean_inc(v_goals_1394_);
lean_inc(v_grindState_1393_);
lean_inc(v_symState_1392_);
lean_dec(v___x_1390_);
v___x_1396_ = lean_box(0);
v_isShared_1397_ = v_isSharedCheck_1417_;
goto v_resetjp_1395_;
}
v_resetjp_1395_:
{
lean_object* v_backwardRuleName_1398_; lean_object* v_backwardRuleSyntax_1399_; lean_object* v_simpState_1400_; lean_object* v_dsimpState_1401_; lean_object* v___x_1403_; uint8_t v_isShared_1404_; uint8_t v_isSharedCheck_1416_; 
v_backwardRuleName_1398_ = lean_ctor_get(v_cache_1391_, 0);
v_backwardRuleSyntax_1399_ = lean_ctor_get(v_cache_1391_, 1);
v_simpState_1400_ = lean_ctor_get(v_cache_1391_, 2);
v_dsimpState_1401_ = lean_ctor_get(v_cache_1391_, 3);
v_isSharedCheck_1416_ = !lean_is_exclusive(v_cache_1391_);
if (v_isSharedCheck_1416_ == 0)
{
v___x_1403_ = v_cache_1391_;
v_isShared_1404_ = v_isSharedCheck_1416_;
goto v_resetjp_1402_;
}
else
{
lean_inc(v_dsimpState_1401_);
lean_inc(v_simpState_1400_);
lean_inc(v_backwardRuleSyntax_1399_);
lean_inc(v_backwardRuleName_1398_);
lean_dec(v_cache_1391_);
v___x_1403_ = lean_box(0);
v_isShared_1404_ = v_isSharedCheck_1416_;
goto v_resetjp_1402_;
}
v_resetjp_1402_:
{
lean_object* v___x_1405_; lean_object* v___x_1407_; 
lean_inc(v_a_1386_);
v___x_1405_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2___redArg(v_backwardRuleSyntax_1399_, v_pos_1367_, v_a_1386_);
if (v_isShared_1404_ == 0)
{
lean_ctor_set(v___x_1403_, 1, v___x_1405_);
v___x_1407_ = v___x_1403_;
goto v_reusejp_1406_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v_backwardRuleName_1398_);
lean_ctor_set(v_reuseFailAlloc_1415_, 1, v___x_1405_);
lean_ctor_set(v_reuseFailAlloc_1415_, 2, v_simpState_1400_);
lean_ctor_set(v_reuseFailAlloc_1415_, 3, v_dsimpState_1401_);
v___x_1407_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1406_;
}
v_reusejp_1406_:
{
lean_object* v___x_1409_; 
if (v_isShared_1397_ == 0)
{
lean_ctor_set(v___x_1396_, 3, v___x_1407_);
v___x_1409_ = v___x_1396_;
goto v_reusejp_1408_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v_symState_1392_);
lean_ctor_set(v_reuseFailAlloc_1414_, 1, v_grindState_1393_);
lean_ctor_set(v_reuseFailAlloc_1414_, 2, v_goals_1394_);
lean_ctor_set(v_reuseFailAlloc_1414_, 3, v___x_1407_);
v___x_1409_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1408_;
}
v_reusejp_1408_:
{
lean_object* v___x_1410_; lean_object* v___x_1412_; 
v___x_1410_ = lean_st_ref_set(v_a_1352_, v___x_1409_);
if (v_isShared_1389_ == 0)
{
v___x_1412_ = v___x_1388_;
goto v_reusejp_1411_;
}
else
{
lean_object* v_reuseFailAlloc_1413_; 
v_reuseFailAlloc_1413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1413_, 0, v_a_1386_);
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
}
}
}
else
{
lean_dec_ref_known(v_pos_1367_, 2);
return v___x_1385_;
}
}
else
{
lean_object* v_a_1419_; lean_object* v___x_1421_; uint8_t v_isShared_1422_; uint8_t v_isSharedCheck_1426_; 
lean_dec_ref_known(v_pos_1367_, 2);
v_a_1419_ = lean_ctor_get(v___x_1382_, 0);
v_isSharedCheck_1426_ = !lean_is_exclusive(v___x_1382_);
if (v_isSharedCheck_1426_ == 0)
{
v___x_1421_ = v___x_1382_;
v_isShared_1422_ = v_isSharedCheck_1426_;
goto v_resetjp_1420_;
}
else
{
lean_inc(v_a_1419_);
lean_dec(v___x_1382_);
v___x_1421_ = lean_box(0);
v_isShared_1422_ = v_isSharedCheck_1426_;
goto v_resetjp_1420_;
}
v_resetjp_1420_:
{
lean_object* v___x_1424_; 
if (v_isShared_1422_ == 0)
{
v___x_1424_ = v___x_1421_;
goto v_reusejp_1423_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v_a_1419_);
v___x_1424_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1423_;
}
v_reusejp_1423_:
{
return v___x_1424_;
}
}
}
}
}
v___jp_1427_:
{
lean_object* v___x_1429_; 
v___x_1429_ = l_Lean_Syntax_getTailPos_x3f(v_term_1350_, v___x_1360_);
if (lean_obj_tag(v___x_1429_) == 0)
{
lean_object* v___x_1430_; 
v___x_1430_ = lean_unsigned_to_nat(0u);
v___y_1362_ = v___y_1428_;
v___y_1363_ = v___x_1430_;
goto v___jp_1361_;
}
else
{
lean_object* v_val_1431_; 
v_val_1431_ = lean_ctor_get(v___x_1429_, 0);
lean_inc(v_val_1431_);
lean_dec_ref_known(v___x_1429_, 1);
v___y_1362_ = v___y_1428_;
v___y_1363_ = v_val_1431_;
goto v___jp_1361_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm___boxed(lean_object* v_term_1435_, lean_object* v_a_1436_, lean_object* v_a_1437_, lean_object* v_a_1438_, lean_object* v_a_1439_, lean_object* v_a_1440_, lean_object* v_a_1441_, lean_object* v_a_1442_, lean_object* v_a_1443_, lean_object* v_a_1444_){
_start:
{
lean_object* v_res_1445_; 
v_res_1445_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm(v_term_1435_, v_a_1436_, v_a_1437_, v_a_1438_, v_a_1439_, v_a_1440_, v_a_1441_, v_a_1442_, v_a_1443_);
lean_dec(v_a_1443_);
lean_dec_ref(v_a_1442_);
lean_dec(v_a_1441_);
lean_dec_ref(v_a_1440_);
lean_dec(v_a_1439_);
lean_dec_ref(v_a_1438_);
lean_dec(v_a_1437_);
lean_dec_ref(v_a_1436_);
return v_res_1445_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0(lean_object* v_00_u03b2_1446_, lean_object* v_x_1447_, lean_object* v_x_1448_){
_start:
{
lean_object* v___x_1449_; 
v___x_1449_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0___redArg(v_x_1447_, v_x_1448_);
return v___x_1449_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0___boxed(lean_object* v_00_u03b2_1450_, lean_object* v_x_1451_, lean_object* v_x_1452_){
_start:
{
lean_object* v_res_1453_; 
v_res_1453_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0(v_00_u03b2_1450_, v_x_1451_, v_x_1452_);
lean_dec_ref(v_x_1452_);
lean_dec_ref(v_x_1451_);
return v_res_1453_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2(lean_object* v_00_u03b2_1454_, lean_object* v_x_1455_, lean_object* v_x_1456_, lean_object* v_x_1457_){
_start:
{
lean_object* v___x_1458_; 
v___x_1458_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2___redArg(v_x_1455_, v_x_1456_, v_x_1457_);
return v___x_1458_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0_spec__0(lean_object* v_00_u03b2_1459_, lean_object* v_x_1460_, size_t v_x_1461_, lean_object* v_x_1462_){
_start:
{
lean_object* v___x_1463_; 
v___x_1463_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0_spec__0___redArg(v_x_1460_, v_x_1461_, v_x_1462_);
return v___x_1463_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1464_, lean_object* v_x_1465_, lean_object* v_x_1466_, lean_object* v_x_1467_){
_start:
{
size_t v_x_4094__boxed_1468_; lean_object* v_res_1469_; 
v_x_4094__boxed_1468_ = lean_unbox_usize(v_x_1466_);
lean_dec(v_x_1466_);
v_res_1469_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0_spec__0(v_00_u03b2_1464_, v_x_1465_, v_x_4094__boxed_1468_, v_x_1467_);
lean_dec_ref(v_x_1467_);
lean_dec_ref(v_x_1465_);
return v_res_1469_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3(lean_object* v_00_u03b2_1470_, lean_object* v_x_1471_, size_t v_x_1472_, size_t v_x_1473_, lean_object* v_x_1474_, lean_object* v_x_1475_){
_start:
{
lean_object* v___x_1476_; 
v___x_1476_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3___redArg(v_x_1471_, v_x_1472_, v_x_1473_, v_x_1474_, v_x_1475_);
return v___x_1476_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3___boxed(lean_object* v_00_u03b2_1477_, lean_object* v_x_1478_, lean_object* v_x_1479_, lean_object* v_x_1480_, lean_object* v_x_1481_, lean_object* v_x_1482_){
_start:
{
size_t v_x_4105__boxed_1483_; size_t v_x_4106__boxed_1484_; lean_object* v_res_1485_; 
v_x_4105__boxed_1483_ = lean_unbox_usize(v_x_1479_);
lean_dec(v_x_1479_);
v_x_4106__boxed_1484_ = lean_unbox_usize(v_x_1480_);
lean_dec(v_x_1480_);
v_res_1485_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3(v_00_u03b2_1477_, v_x_1478_, v_x_4105__boxed_1483_, v_x_4106__boxed_1484_, v_x_1481_, v_x_1482_);
return v_res_1485_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1486_, lean_object* v_keys_1487_, lean_object* v_vals_1488_, lean_object* v_heq_1489_, lean_object* v_i_1490_, lean_object* v_k_1491_){
_start:
{
lean_object* v___x_1492_; 
v___x_1492_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0_spec__0_spec__2___redArg(v_keys_1487_, v_vals_1488_, v_i_1490_, v_k_1491_);
return v___x_1492_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1493_, lean_object* v_keys_1494_, lean_object* v_vals_1495_, lean_object* v_heq_1496_, lean_object* v_i_1497_, lean_object* v_k_1498_){
_start:
{
lean_object* v_res_1499_; 
v_res_1499_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0_spec__0_spec__2(v_00_u03b2_1493_, v_keys_1494_, v_vals_1495_, v_heq_1496_, v_i_1497_, v_k_1498_);
lean_dec_ref(v_k_1498_);
lean_dec_ref(v_vals_1495_);
lean_dec_ref(v_keys_1494_);
return v_res_1499_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_1500_, lean_object* v_n_1501_, lean_object* v_k_1502_, lean_object* v_v_1503_){
_start:
{
lean_object* v___x_1504_; 
v___x_1504_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3_spec__5___redArg(v_n_1501_, v_k_1502_, v_v_1503_);
return v___x_1504_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3_spec__6(lean_object* v_00_u03b2_1505_, size_t v_depth_1506_, lean_object* v_keys_1507_, lean_object* v_vals_1508_, lean_object* v_heq_1509_, lean_object* v_i_1510_, lean_object* v_entries_1511_){
_start:
{
lean_object* v___x_1512_; 
v___x_1512_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3_spec__6___redArg(v_depth_1506_, v_keys_1507_, v_vals_1508_, v_i_1510_, v_entries_1511_);
return v___x_1512_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3_spec__6___boxed(lean_object* v_00_u03b2_1513_, lean_object* v_depth_1514_, lean_object* v_keys_1515_, lean_object* v_vals_1516_, lean_object* v_heq_1517_, lean_object* v_i_1518_, lean_object* v_entries_1519_){
_start:
{
size_t v_depth_boxed_1520_; lean_object* v_res_1521_; 
v_depth_boxed_1520_ = lean_unbox_usize(v_depth_1514_);
lean_dec(v_depth_1514_);
v_res_1521_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3_spec__6(v_00_u03b2_1513_, v_depth_boxed_1520_, v_keys_1515_, v_vals_1516_, v_heq_1517_, v_i_1518_, v_entries_1519_);
lean_dec_ref(v_vals_1516_);
lean_dec_ref(v_keys_1515_);
return v_res_1521_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3_spec__5_spec__6(lean_object* v_00_u03b2_1522_, lean_object* v_x_1523_, lean_object* v_x_1524_, lean_object* v_x_1525_, lean_object* v_x_1526_){
_start:
{
lean_object* v___x_1527_; 
v___x_1527_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3_spec__5_spec__6___redArg(v_x_1523_, v_x_1524_, v_x_1525_, v_x_1526_);
return v___x_1527_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply_spec__0___redArg___lam__0(lean_object* v_x_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_){
_start:
{
lean_object* v___x_1538_; 
lean_inc(v___y_1532_);
lean_inc_ref(v___y_1531_);
lean_inc(v___y_1530_);
lean_inc_ref(v___y_1529_);
v___x_1538_ = lean_apply_9(v_x_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_, lean_box(0));
return v___x_1538_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply_spec__0___redArg___lam__0___boxed(lean_object* v_x_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_){
_start:
{
lean_object* v_res_1549_; 
v_res_1549_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply_spec__0___redArg___lam__0(v_x_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_, v___y_1546_, v___y_1547_);
lean_dec(v___y_1543_);
lean_dec_ref(v___y_1542_);
lean_dec(v___y_1541_);
lean_dec_ref(v___y_1540_);
return v_res_1549_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply_spec__0___redArg(lean_object* v_mvarId_1550_, lean_object* v_x_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_){
_start:
{
lean_object* v___f_1561_; lean_object* v___x_1562_; 
lean_inc(v___y_1555_);
lean_inc_ref(v___y_1554_);
lean_inc(v___y_1553_);
lean_inc_ref(v___y_1552_);
v___f_1561_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply_spec__0___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_1561_, 0, v_x_1551_);
lean_closure_set(v___f_1561_, 1, v___y_1552_);
lean_closure_set(v___f_1561_, 2, v___y_1553_);
lean_closure_set(v___f_1561_, 3, v___y_1554_);
lean_closure_set(v___f_1561_, 4, v___y_1555_);
v___x_1562_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1550_, v___f_1561_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_);
if (lean_obj_tag(v___x_1562_) == 0)
{
return v___x_1562_;
}
else
{
lean_object* v_a_1563_; lean_object* v___x_1565_; uint8_t v_isShared_1566_; uint8_t v_isSharedCheck_1570_; 
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
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply_spec__0___redArg___boxed(lean_object* v_mvarId_1571_, lean_object* v_x_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_){
_start:
{
lean_object* v_res_1582_; 
v_res_1582_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply_spec__0___redArg(v_mvarId_1571_, v_x_1572_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_);
lean_dec(v___y_1580_);
lean_dec_ref(v___y_1579_);
lean_dec(v___y_1578_);
lean_dec_ref(v___y_1577_);
lean_dec(v___y_1576_);
lean_dec_ref(v___y_1575_);
lean_dec(v___y_1574_);
lean_dec_ref(v___y_1573_);
return v_res_1582_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply_spec__0(lean_object* v_00_u03b1_1583_, lean_object* v_mvarId_1584_, lean_object* v_x_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_){
_start:
{
lean_object* v___x_1595_; 
v___x_1595_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply_spec__0___redArg(v_mvarId_1584_, v_x_1585_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_);
return v___x_1595_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply_spec__0___boxed(lean_object* v_00_u03b1_1596_, lean_object* v_mvarId_1597_, lean_object* v_x_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_){
_start:
{
lean_object* v_res_1608_; 
v_res_1608_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply_spec__0(v_00_u03b1_1596_, v_mvarId_1597_, v_x_1598_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_);
lean_dec(v___y_1606_);
lean_dec_ref(v___y_1605_);
lean_dec(v___y_1604_);
lean_dec_ref(v___y_1603_);
lean_dec(v___y_1602_);
lean_dec_ref(v___y_1601_);
lean_dec(v___y_1600_);
lean_dec_ref(v___y_1599_);
return v_res_1608_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1610_; lean_object* v___x_1611_; 
v___x_1610_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___lam__0___closed__0));
v___x_1611_ = l_Lean_stringToMessageData(v___x_1610_);
return v___x_1611_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___lam__0(lean_object* v_a_1612_, lean_object* v_rule_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_){
_start:
{
lean_object* v___x_1623_; lean_object* v___x_1624_; 
v___x_1623_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Goal_apply___boxed), 9, 2);
lean_closure_set(v___x_1623_, 0, v_a_1612_);
lean_closure_set(v___x_1623_, 1, v_rule_1613_);
v___x_1624_ = l_Lean_Elab_Tactic_Grind_liftSymM___redArg(v___x_1623_, v___y_1614_, v___y_1615_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_);
if (lean_obj_tag(v___x_1624_) == 0)
{
lean_object* v_a_1625_; 
v_a_1625_ = lean_ctor_get(v___x_1624_, 0);
lean_inc(v_a_1625_);
lean_dec_ref_known(v___x_1624_, 1);
if (lean_obj_tag(v_a_1625_) == 0)
{
lean_object* v___x_1626_; lean_object* v___x_1627_; 
v___x_1626_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___lam__0___closed__1, &l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___lam__0___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___lam__0___closed__1);
v___x_1627_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__2___redArg(v___x_1626_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_);
return v___x_1627_;
}
else
{
lean_object* v_subgoals_1628_; lean_object* v___x_1629_; 
v_subgoals_1628_ = lean_ctor_get(v_a_1625_, 0);
lean_inc(v_subgoals_1628_);
lean_dec_ref_known(v_a_1625_, 1);
v___x_1629_ = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(v_subgoals_1628_, v___y_1615_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_);
return v___x_1629_;
}
}
else
{
lean_object* v_a_1630_; lean_object* v___x_1632_; uint8_t v_isShared_1633_; uint8_t v_isSharedCheck_1637_; 
v_a_1630_ = lean_ctor_get(v___x_1624_, 0);
v_isSharedCheck_1637_ = !lean_is_exclusive(v___x_1624_);
if (v_isSharedCheck_1637_ == 0)
{
v___x_1632_ = v___x_1624_;
v_isShared_1633_ = v_isSharedCheck_1637_;
goto v_resetjp_1631_;
}
else
{
lean_inc(v_a_1630_);
lean_dec(v___x_1624_);
v___x_1632_ = lean_box(0);
v_isShared_1633_ = v_isSharedCheck_1637_;
goto v_resetjp_1631_;
}
v_resetjp_1631_:
{
lean_object* v___x_1635_; 
if (v_isShared_1633_ == 0)
{
v___x_1635_ = v___x_1632_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v_a_1630_);
v___x_1635_ = v_reuseFailAlloc_1636_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
return v___x_1635_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___lam__0___boxed(lean_object* v_a_1638_, lean_object* v_rule_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_){
_start:
{
lean_object* v_res_1649_; 
v_res_1649_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___lam__0(v_a_1638_, v_rule_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_);
lean_dec(v___y_1647_);
lean_dec_ref(v___y_1646_);
lean_dec(v___y_1645_);
lean_dec_ref(v___y_1644_);
lean_dec(v___y_1643_);
lean_dec_ref(v___y_1642_);
lean_dec(v___y_1641_);
lean_dec_ref(v___y_1640_);
return v_res_1649_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___lam__1(uint8_t v___x_1650_, lean_object* v___x_1651_, lean_object* v___f_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_){
_start:
{
if (v___x_1650_ == 0)
{
lean_object* v___x_1662_; 
v___x_1662_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm(v___x_1651_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_);
if (lean_obj_tag(v___x_1662_) == 0)
{
lean_object* v_a_1663_; lean_object* v___x_1664_; 
v_a_1663_ = lean_ctor_get(v___x_1662_, 0);
lean_inc(v_a_1663_);
lean_dec_ref_known(v___x_1662_, 1);
lean_inc(v___y_1660_);
lean_inc_ref(v___y_1659_);
lean_inc(v___y_1658_);
lean_inc_ref(v___y_1657_);
lean_inc(v___y_1656_);
lean_inc_ref(v___y_1655_);
lean_inc(v___y_1654_);
lean_inc_ref(v___y_1653_);
v___x_1664_ = lean_apply_10(v___f_1652_, v_a_1663_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_, lean_box(0));
return v___x_1664_;
}
else
{
lean_object* v_a_1665_; lean_object* v___x_1667_; uint8_t v_isShared_1668_; uint8_t v_isSharedCheck_1672_; 
lean_dec_ref(v___f_1652_);
v_a_1665_ = lean_ctor_get(v___x_1662_, 0);
v_isSharedCheck_1672_ = !lean_is_exclusive(v___x_1662_);
if (v_isSharedCheck_1672_ == 0)
{
v___x_1667_ = v___x_1662_;
v_isShared_1668_ = v_isSharedCheck_1672_;
goto v_resetjp_1666_;
}
else
{
lean_inc(v_a_1665_);
lean_dec(v___x_1662_);
v___x_1667_ = lean_box(0);
v_isShared_1668_ = v_isSharedCheck_1672_;
goto v_resetjp_1666_;
}
v_resetjp_1666_:
{
lean_object* v___x_1670_; 
if (v_isShared_1668_ == 0)
{
v___x_1670_ = v___x_1667_;
goto v_reusejp_1669_;
}
else
{
lean_object* v_reuseFailAlloc_1671_; 
v_reuseFailAlloc_1671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1671_, 0, v_a_1665_);
v___x_1670_ = v_reuseFailAlloc_1671_;
goto v_reusejp_1669_;
}
v_reusejp_1669_:
{
return v___x_1670_;
}
}
}
}
else
{
lean_object* v___x_1673_; 
v___x_1673_ = l_Lean_Elab_Tactic_Grind_saveState___redArg(v___y_1654_, v___y_1656_, v___y_1658_, v___y_1660_);
if (lean_obj_tag(v___x_1673_) == 0)
{
lean_object* v_a_1674_; lean_object* v___x_1676_; uint8_t v_isShared_1677_; uint8_t v_isSharedCheck_1707_; 
v_a_1674_ = lean_ctor_get(v___x_1673_, 0);
v_isSharedCheck_1707_ = !lean_is_exclusive(v___x_1673_);
if (v_isSharedCheck_1707_ == 0)
{
v___x_1676_ = v___x_1673_;
v_isShared_1677_ = v_isSharedCheck_1707_;
goto v_resetjp_1675_;
}
else
{
lean_inc(v_a_1674_);
lean_dec(v___x_1673_);
v___x_1676_ = lean_box(0);
v_isShared_1677_ = v_isSharedCheck_1707_;
goto v_resetjp_1675_;
}
v_resetjp_1675_:
{
lean_object* v___y_1679_; uint8_t v___y_1680_; lean_object* v_a_1697_; lean_object* v___x_1700_; 
lean_inc(v___x_1651_);
v___x_1700_ = l_Lean_realizeGlobalConstNoOverload(v___x_1651_, v___y_1659_, v___y_1660_);
if (lean_obj_tag(v___x_1700_) == 0)
{
lean_object* v_a_1701_; lean_object* v___x_1702_; 
v_a_1701_ = lean_ctor_get(v___x_1700_, 0);
lean_inc(v_a_1701_);
lean_dec_ref_known(v___x_1700_, 1);
v___x_1702_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule___redArg(v_a_1701_, v___y_1654_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_);
if (lean_obj_tag(v___x_1702_) == 0)
{
lean_object* v_a_1703_; lean_object* v___x_1704_; 
lean_del_object(v___x_1676_);
lean_dec(v_a_1674_);
lean_dec(v___x_1651_);
v_a_1703_ = lean_ctor_get(v___x_1702_, 0);
lean_inc(v_a_1703_);
lean_dec_ref_known(v___x_1702_, 1);
lean_inc(v___y_1660_);
lean_inc_ref(v___y_1659_);
lean_inc(v___y_1658_);
lean_inc_ref(v___y_1657_);
lean_inc(v___y_1656_);
lean_inc_ref(v___y_1655_);
lean_inc(v___y_1654_);
lean_inc_ref(v___y_1653_);
v___x_1704_ = lean_apply_10(v___f_1652_, v_a_1703_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_, lean_box(0));
return v___x_1704_;
}
else
{
lean_object* v_a_1705_; 
v_a_1705_ = lean_ctor_get(v___x_1702_, 0);
lean_inc(v_a_1705_);
lean_dec_ref_known(v___x_1702_, 1);
v_a_1697_ = v_a_1705_;
goto v___jp_1696_;
}
}
else
{
lean_object* v_a_1706_; 
v_a_1706_ = lean_ctor_get(v___x_1700_, 0);
lean_inc(v_a_1706_);
lean_dec_ref_known(v___x_1700_, 1);
v_a_1697_ = v_a_1706_;
goto v___jp_1696_;
}
v___jp_1678_:
{
if (v___y_1680_ == 0)
{
lean_object* v___x_1681_; 
lean_dec_ref(v___y_1679_);
lean_del_object(v___x_1676_);
v___x_1681_ = l_Lean_Elab_Tactic_Grind_SavedState_restore___redArg(v_a_1674_, v___y_1680_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_);
if (lean_obj_tag(v___x_1681_) == 0)
{
lean_object* v___x_1682_; 
lean_dec_ref_known(v___x_1681_, 1);
v___x_1682_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm(v___x_1651_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_);
if (lean_obj_tag(v___x_1682_) == 0)
{
lean_object* v_a_1683_; lean_object* v___x_1684_; 
v_a_1683_ = lean_ctor_get(v___x_1682_, 0);
lean_inc(v_a_1683_);
lean_dec_ref_known(v___x_1682_, 1);
lean_inc(v___y_1660_);
lean_inc_ref(v___y_1659_);
lean_inc(v___y_1658_);
lean_inc_ref(v___y_1657_);
lean_inc(v___y_1656_);
lean_inc_ref(v___y_1655_);
lean_inc(v___y_1654_);
lean_inc_ref(v___y_1653_);
v___x_1684_ = lean_apply_10(v___f_1652_, v_a_1683_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_, lean_box(0));
return v___x_1684_;
}
else
{
lean_object* v_a_1685_; lean_object* v___x_1687_; uint8_t v_isShared_1688_; uint8_t v_isSharedCheck_1692_; 
lean_dec_ref(v___f_1652_);
v_a_1685_ = lean_ctor_get(v___x_1682_, 0);
v_isSharedCheck_1692_ = !lean_is_exclusive(v___x_1682_);
if (v_isSharedCheck_1692_ == 0)
{
v___x_1687_ = v___x_1682_;
v_isShared_1688_ = v_isSharedCheck_1692_;
goto v_resetjp_1686_;
}
else
{
lean_inc(v_a_1685_);
lean_dec(v___x_1682_);
v___x_1687_ = lean_box(0);
v_isShared_1688_ = v_isSharedCheck_1692_;
goto v_resetjp_1686_;
}
v_resetjp_1686_:
{
lean_object* v___x_1690_; 
if (v_isShared_1688_ == 0)
{
v___x_1690_ = v___x_1687_;
goto v_reusejp_1689_;
}
else
{
lean_object* v_reuseFailAlloc_1691_; 
v_reuseFailAlloc_1691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1691_, 0, v_a_1685_);
v___x_1690_ = v_reuseFailAlloc_1691_;
goto v_reusejp_1689_;
}
v_reusejp_1689_:
{
return v___x_1690_;
}
}
}
}
else
{
lean_dec_ref(v___f_1652_);
lean_dec(v___x_1651_);
return v___x_1681_;
}
}
else
{
lean_object* v___x_1694_; 
lean_dec(v_a_1674_);
lean_dec_ref(v___f_1652_);
lean_dec(v___x_1651_);
if (v_isShared_1677_ == 0)
{
lean_ctor_set_tag(v___x_1676_, 1);
lean_ctor_set(v___x_1676_, 0, v___y_1679_);
v___x_1694_ = v___x_1676_;
goto v_reusejp_1693_;
}
else
{
lean_object* v_reuseFailAlloc_1695_; 
v_reuseFailAlloc_1695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1695_, 0, v___y_1679_);
v___x_1694_ = v_reuseFailAlloc_1695_;
goto v_reusejp_1693_;
}
v_reusejp_1693_:
{
return v___x_1694_;
}
}
}
v___jp_1696_:
{
uint8_t v___x_1698_; 
v___x_1698_ = l_Lean_Exception_isInterrupt(v_a_1697_);
if (v___x_1698_ == 0)
{
uint8_t v___x_1699_; 
lean_inc_ref(v_a_1697_);
v___x_1699_ = l_Lean_Exception_isRuntime(v_a_1697_);
v___y_1679_ = v_a_1697_;
v___y_1680_ = v___x_1699_;
goto v___jp_1678_;
}
else
{
v___y_1679_ = v_a_1697_;
v___y_1680_ = v___x_1698_;
goto v___jp_1678_;
}
}
}
}
else
{
lean_object* v_a_1708_; lean_object* v___x_1710_; uint8_t v_isShared_1711_; uint8_t v_isSharedCheck_1715_; 
lean_dec_ref(v___f_1652_);
lean_dec(v___x_1651_);
v_a_1708_ = lean_ctor_get(v___x_1673_, 0);
v_isSharedCheck_1715_ = !lean_is_exclusive(v___x_1673_);
if (v_isSharedCheck_1715_ == 0)
{
v___x_1710_ = v___x_1673_;
v_isShared_1711_ = v_isSharedCheck_1715_;
goto v_resetjp_1709_;
}
else
{
lean_inc(v_a_1708_);
lean_dec(v___x_1673_);
v___x_1710_ = lean_box(0);
v_isShared_1711_ = v_isSharedCheck_1715_;
goto v_resetjp_1709_;
}
v_resetjp_1709_:
{
lean_object* v___x_1713_; 
if (v_isShared_1711_ == 0)
{
v___x_1713_ = v___x_1710_;
goto v_reusejp_1712_;
}
else
{
lean_object* v_reuseFailAlloc_1714_; 
v_reuseFailAlloc_1714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1714_, 0, v_a_1708_);
v___x_1713_ = v_reuseFailAlloc_1714_;
goto v_reusejp_1712_;
}
v_reusejp_1712_:
{
return v___x_1713_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___lam__1___boxed(lean_object* v___x_1716_, lean_object* v___x_1717_, lean_object* v___f_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_){
_start:
{
uint8_t v___x_3542__boxed_1728_; lean_object* v_res_1729_; 
v___x_3542__boxed_1728_ = lean_unbox(v___x_1716_);
v_res_1729_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___lam__1(v___x_3542__boxed_1728_, v___x_1717_, v___f_1718_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_);
lean_dec(v___y_1726_);
lean_dec_ref(v___y_1725_);
lean_dec(v___y_1724_);
lean_dec_ref(v___y_1723_);
lean_dec(v___y_1722_);
lean_dec_ref(v___y_1721_);
lean_dec(v___y_1720_);
lean_dec_ref(v___y_1719_);
return v_res_1729_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply(lean_object* v_stx_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_, lean_object* v_a_1741_, lean_object* v_a_1742_, lean_object* v_a_1743_, lean_object* v_a_1744_, lean_object* v_a_1745_){
_start:
{
lean_object* v___x_1747_; 
v___x_1747_ = l_Lean_Elab_Tactic_Grind_ensureSym___redArg(v_a_1738_, v_a_1742_, v_a_1743_, v_a_1744_, v_a_1745_);
if (lean_obj_tag(v___x_1747_) == 0)
{
lean_object* v___x_1748_; uint8_t v___x_1749_; 
lean_dec_ref_known(v___x_1747_, 1);
v___x_1748_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___closed__1));
lean_inc(v_stx_1737_);
v___x_1749_ = l_Lean_Syntax_isOfKind(v_stx_1737_, v___x_1748_);
if (v___x_1749_ == 0)
{
lean_object* v___x_1750_; 
lean_dec(v_stx_1737_);
v___x_1750_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro_spec__0___redArg();
return v___x_1750_;
}
else
{
lean_object* v___x_1751_; 
v___x_1751_ = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(v_a_1739_, v_a_1742_, v_a_1743_, v_a_1744_, v_a_1745_);
if (lean_obj_tag(v___x_1751_) == 0)
{
lean_object* v_a_1752_; lean_object* v_mvarId_1753_; lean_object* v___f_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; uint8_t v___x_1758_; lean_object* v___x_1759_; lean_object* v___y_1760_; lean_object* v___x_1761_; 
v_a_1752_ = lean_ctor_get(v___x_1751_, 0);
lean_inc(v_a_1752_);
lean_dec_ref_known(v___x_1751_, 1);
v_mvarId_1753_ = lean_ctor_get(v_a_1752_, 1);
lean_inc(v_mvarId_1753_);
v___f_1754_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___lam__0___boxed), 11, 1);
lean_closure_set(v___f_1754_, 0, v_a_1752_);
v___x_1755_ = lean_unsigned_to_nat(1u);
v___x_1756_ = l_Lean_Syntax_getArg(v_stx_1737_, v___x_1755_);
lean_dec(v_stx_1737_);
v___x_1757_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__1___redArg___closed__6));
lean_inc(v___x_1756_);
v___x_1758_ = l_Lean_Syntax_isOfKind(v___x_1756_, v___x_1757_);
v___x_1759_ = lean_box(v___x_1758_);
v___y_1760_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___lam__1___boxed), 12, 3);
lean_closure_set(v___y_1760_, 0, v___x_1759_);
lean_closure_set(v___y_1760_, 1, v___x_1756_);
lean_closure_set(v___y_1760_, 2, v___f_1754_);
v___x_1761_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply_spec__0___redArg(v_mvarId_1753_, v___y_1760_, v_a_1738_, v_a_1739_, v_a_1740_, v_a_1741_, v_a_1742_, v_a_1743_, v_a_1744_, v_a_1745_);
return v___x_1761_;
}
else
{
lean_object* v_a_1762_; lean_object* v___x_1764_; uint8_t v_isShared_1765_; uint8_t v_isSharedCheck_1769_; 
lean_dec(v_stx_1737_);
v_a_1762_ = lean_ctor_get(v___x_1751_, 0);
v_isSharedCheck_1769_ = !lean_is_exclusive(v___x_1751_);
if (v_isSharedCheck_1769_ == 0)
{
v___x_1764_ = v___x_1751_;
v_isShared_1765_ = v_isSharedCheck_1769_;
goto v_resetjp_1763_;
}
else
{
lean_inc(v_a_1762_);
lean_dec(v___x_1751_);
v___x_1764_ = lean_box(0);
v_isShared_1765_ = v_isSharedCheck_1769_;
goto v_resetjp_1763_;
}
v_resetjp_1763_:
{
lean_object* v___x_1767_; 
if (v_isShared_1765_ == 0)
{
v___x_1767_ = v___x_1764_;
goto v_reusejp_1766_;
}
else
{
lean_object* v_reuseFailAlloc_1768_; 
v_reuseFailAlloc_1768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1768_, 0, v_a_1762_);
v___x_1767_ = v_reuseFailAlloc_1768_;
goto v_reusejp_1766_;
}
v_reusejp_1766_:
{
return v___x_1767_;
}
}
}
}
}
else
{
lean_dec(v_stx_1737_);
return v___x_1747_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___boxed(lean_object* v_stx_1770_, lean_object* v_a_1771_, lean_object* v_a_1772_, lean_object* v_a_1773_, lean_object* v_a_1774_, lean_object* v_a_1775_, lean_object* v_a_1776_, lean_object* v_a_1777_, lean_object* v_a_1778_, lean_object* v_a_1779_){
_start:
{
lean_object* v_res_1780_; 
v_res_1780_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply(v_stx_1770_, v_a_1771_, v_a_1772_, v_a_1773_, v_a_1774_, v_a_1775_, v_a_1776_, v_a_1777_, v_a_1778_);
lean_dec(v_a_1778_);
lean_dec_ref(v_a_1777_);
lean_dec(v_a_1776_);
lean_dec_ref(v_a_1775_);
lean_dec(v_a_1774_);
lean_dec_ref(v_a_1773_);
lean_dec(v_a_1772_);
lean_dec_ref(v_a_1771_);
return v_res_1780_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply__1(){
_start:
{
lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; 
v___x_1786_ = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
v___x_1787_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___closed__1));
v___x_1788_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply__1___closed__1));
v___x_1789_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___boxed), 10, 0);
v___x_1790_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1786_, v___x_1787_, v___x_1788_, v___x_1789_);
return v___x_1790_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply__1___boxed(lean_object* v_a_1791_){
_start:
{
lean_object* v_res_1792_; 
v_res_1792_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply__1();
return v_res_1792_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize___redArg(lean_object* v_stx_1793_, lean_object* v_a_1794_, lean_object* v_a_1795_, lean_object* v_a_1796_, lean_object* v_a_1797_, lean_object* v_a_1798_, lean_object* v_a_1799_){
_start:
{
lean_object* v___x_1801_; 
v___x_1801_ = l_Lean_Elab_Tactic_Grind_ensureSym___redArg(v_a_1794_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_);
if (lean_obj_tag(v___x_1801_) == 0)
{
lean_object* v___x_1802_; 
lean_dec_ref_known(v___x_1801_, 1);
v___x_1802_ = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_);
if (lean_obj_tag(v___x_1802_) == 0)
{
lean_object* v_a_1803_; lean_object* v___y_1805_; lean_object* v___x_1820_; lean_object* v___x_1821_; uint8_t v___x_1822_; 
v_a_1803_ = lean_ctor_get(v___x_1802_, 0);
lean_inc(v_a_1803_);
lean_dec_ref_known(v___x_1802_, 1);
v___x_1820_ = lean_unsigned_to_nat(1u);
v___x_1821_ = l_Lean_Syntax_getArg(v_stx_1793_, v___x_1820_);
v___x_1822_ = l_Lean_Syntax_isNone(v___x_1821_);
if (v___x_1822_ == 0)
{
lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; 
v___x_1823_ = lean_unsigned_to_nat(0u);
v___x_1824_ = l_Lean_Syntax_getArg(v___x_1821_, v___x_1823_);
lean_dec(v___x_1821_);
v___x_1825_ = l_Lean_Syntax_toNat(v___x_1824_);
lean_dec(v___x_1824_);
v___y_1805_ = v___x_1825_;
goto v___jp_1804_;
}
else
{
lean_dec(v___x_1821_);
v___y_1805_ = v___x_1820_;
goto v___jp_1804_;
}
v___jp_1804_:
{
lean_object* v___x_1806_; lean_object* v___x_1807_; 
v___x_1806_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Goal_internalize___boxed), 12, 2);
lean_closure_set(v___x_1806_, 0, v_a_1803_);
lean_closure_set(v___x_1806_, 1, v___y_1805_);
v___x_1807_ = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(v___x_1806_, v_a_1794_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_);
if (lean_obj_tag(v___x_1807_) == 0)
{
lean_object* v_a_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; 
v_a_1808_ = lean_ctor_get(v___x_1807_, 0);
lean_inc(v_a_1808_);
lean_dec_ref_known(v___x_1807_, 1);
v___x_1809_ = lean_box(0);
v___x_1810_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1810_, 0, v_a_1808_);
lean_ctor_set(v___x_1810_, 1, v___x_1809_);
v___x_1811_ = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(v___x_1810_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_);
return v___x_1811_;
}
else
{
lean_object* v_a_1812_; lean_object* v___x_1814_; uint8_t v_isShared_1815_; uint8_t v_isSharedCheck_1819_; 
v_a_1812_ = lean_ctor_get(v___x_1807_, 0);
v_isSharedCheck_1819_ = !lean_is_exclusive(v___x_1807_);
if (v_isSharedCheck_1819_ == 0)
{
v___x_1814_ = v___x_1807_;
v_isShared_1815_ = v_isSharedCheck_1819_;
goto v_resetjp_1813_;
}
else
{
lean_inc(v_a_1812_);
lean_dec(v___x_1807_);
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
lean_object* v_a_1826_; lean_object* v___x_1828_; uint8_t v_isShared_1829_; uint8_t v_isSharedCheck_1833_; 
v_a_1826_ = lean_ctor_get(v___x_1802_, 0);
v_isSharedCheck_1833_ = !lean_is_exclusive(v___x_1802_);
if (v_isSharedCheck_1833_ == 0)
{
v___x_1828_ = v___x_1802_;
v_isShared_1829_ = v_isSharedCheck_1833_;
goto v_resetjp_1827_;
}
else
{
lean_inc(v_a_1826_);
lean_dec(v___x_1802_);
v___x_1828_ = lean_box(0);
v_isShared_1829_ = v_isSharedCheck_1833_;
goto v_resetjp_1827_;
}
v_resetjp_1827_:
{
lean_object* v___x_1831_; 
if (v_isShared_1829_ == 0)
{
v___x_1831_ = v___x_1828_;
goto v_reusejp_1830_;
}
else
{
lean_object* v_reuseFailAlloc_1832_; 
v_reuseFailAlloc_1832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1832_, 0, v_a_1826_);
v___x_1831_ = v_reuseFailAlloc_1832_;
goto v_reusejp_1830_;
}
v_reusejp_1830_:
{
return v___x_1831_;
}
}
}
}
else
{
return v___x_1801_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize___redArg___boxed(lean_object* v_stx_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_, lean_object* v_a_1838_, lean_object* v_a_1839_, lean_object* v_a_1840_, lean_object* v_a_1841_){
_start:
{
lean_object* v_res_1842_; 
v_res_1842_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize___redArg(v_stx_1834_, v_a_1835_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_, v_a_1840_);
lean_dec(v_a_1840_);
lean_dec_ref(v_a_1839_);
lean_dec(v_a_1838_);
lean_dec_ref(v_a_1837_);
lean_dec(v_a_1836_);
lean_dec_ref(v_a_1835_);
lean_dec(v_stx_1834_);
return v_res_1842_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize(lean_object* v_stx_1843_, lean_object* v_a_1844_, lean_object* v_a_1845_, lean_object* v_a_1846_, lean_object* v_a_1847_, lean_object* v_a_1848_, lean_object* v_a_1849_, lean_object* v_a_1850_, lean_object* v_a_1851_){
_start:
{
lean_object* v___x_1853_; 
v___x_1853_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize___redArg(v_stx_1843_, v_a_1844_, v_a_1845_, v_a_1848_, v_a_1849_, v_a_1850_, v_a_1851_);
return v___x_1853_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize___boxed(lean_object* v_stx_1854_, lean_object* v_a_1855_, lean_object* v_a_1856_, lean_object* v_a_1857_, lean_object* v_a_1858_, lean_object* v_a_1859_, lean_object* v_a_1860_, lean_object* v_a_1861_, lean_object* v_a_1862_, lean_object* v_a_1863_){
_start:
{
lean_object* v_res_1864_; 
v_res_1864_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize(v_stx_1854_, v_a_1855_, v_a_1856_, v_a_1857_, v_a_1858_, v_a_1859_, v_a_1860_, v_a_1861_, v_a_1862_);
lean_dec(v_a_1862_);
lean_dec_ref(v_a_1861_);
lean_dec(v_a_1860_);
lean_dec_ref(v_a_1859_);
lean_dec(v_a_1858_);
lean_dec_ref(v_a_1857_);
lean_dec(v_a_1856_);
lean_dec_ref(v_a_1855_);
lean_dec(v_stx_1854_);
return v_res_1864_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize__1(){
_start:
{
lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; 
v___x_1877_ = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
v___x_1878_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize__1___closed__1));
v___x_1879_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize__1___closed__3));
v___x_1880_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize___boxed), 10, 0);
v___x_1881_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1877_, v___x_1878_, v___x_1879_, v___x_1880_);
return v___x_1881_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize__1___boxed(lean_object* v_a_1882_){
_start:
{
lean_object* v_res_1883_; 
v_res_1883_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize__1();
return v_res_1883_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll___redArg(lean_object* v_a_1884_, lean_object* v_a_1885_, lean_object* v_a_1886_, lean_object* v_a_1887_, lean_object* v_a_1888_, lean_object* v_a_1889_){
_start:
{
lean_object* v___x_1891_; 
v___x_1891_ = l_Lean_Elab_Tactic_Grind_ensureSym___redArg(v_a_1884_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_);
if (lean_obj_tag(v___x_1891_) == 0)
{
lean_object* v___x_1892_; 
lean_dec_ref_known(v___x_1891_, 1);
v___x_1892_ = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_);
if (lean_obj_tag(v___x_1892_) == 0)
{
lean_object* v_a_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; 
v_a_1893_ = lean_ctor_get(v___x_1892_, 0);
lean_inc(v_a_1893_);
lean_dec_ref_known(v___x_1892_, 1);
v___x_1894_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Goal_internalizeAll___boxed), 11, 1);
lean_closure_set(v___x_1894_, 0, v_a_1893_);
v___x_1895_ = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(v___x_1894_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_);
if (lean_obj_tag(v___x_1895_) == 0)
{
lean_object* v_a_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; 
v_a_1896_ = lean_ctor_get(v___x_1895_, 0);
lean_inc(v_a_1896_);
lean_dec_ref_known(v___x_1895_, 1);
v___x_1897_ = lean_box(0);
v___x_1898_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1898_, 0, v_a_1896_);
lean_ctor_set(v___x_1898_, 1, v___x_1897_);
v___x_1899_ = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(v___x_1898_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_);
return v___x_1899_;
}
else
{
lean_object* v_a_1900_; lean_object* v___x_1902_; uint8_t v_isShared_1903_; uint8_t v_isSharedCheck_1907_; 
v_a_1900_ = lean_ctor_get(v___x_1895_, 0);
v_isSharedCheck_1907_ = !lean_is_exclusive(v___x_1895_);
if (v_isSharedCheck_1907_ == 0)
{
v___x_1902_ = v___x_1895_;
v_isShared_1903_ = v_isSharedCheck_1907_;
goto v_resetjp_1901_;
}
else
{
lean_inc(v_a_1900_);
lean_dec(v___x_1895_);
v___x_1902_ = lean_box(0);
v_isShared_1903_ = v_isSharedCheck_1907_;
goto v_resetjp_1901_;
}
v_resetjp_1901_:
{
lean_object* v___x_1905_; 
if (v_isShared_1903_ == 0)
{
v___x_1905_ = v___x_1902_;
goto v_reusejp_1904_;
}
else
{
lean_object* v_reuseFailAlloc_1906_; 
v_reuseFailAlloc_1906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1906_, 0, v_a_1900_);
v___x_1905_ = v_reuseFailAlloc_1906_;
goto v_reusejp_1904_;
}
v_reusejp_1904_:
{
return v___x_1905_;
}
}
}
}
else
{
lean_object* v_a_1908_; lean_object* v___x_1910_; uint8_t v_isShared_1911_; uint8_t v_isSharedCheck_1915_; 
v_a_1908_ = lean_ctor_get(v___x_1892_, 0);
v_isSharedCheck_1915_ = !lean_is_exclusive(v___x_1892_);
if (v_isSharedCheck_1915_ == 0)
{
v___x_1910_ = v___x_1892_;
v_isShared_1911_ = v_isSharedCheck_1915_;
goto v_resetjp_1909_;
}
else
{
lean_inc(v_a_1908_);
lean_dec(v___x_1892_);
v___x_1910_ = lean_box(0);
v_isShared_1911_ = v_isSharedCheck_1915_;
goto v_resetjp_1909_;
}
v_resetjp_1909_:
{
lean_object* v___x_1913_; 
if (v_isShared_1911_ == 0)
{
v___x_1913_ = v___x_1910_;
goto v_reusejp_1912_;
}
else
{
lean_object* v_reuseFailAlloc_1914_; 
v_reuseFailAlloc_1914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1914_, 0, v_a_1908_);
v___x_1913_ = v_reuseFailAlloc_1914_;
goto v_reusejp_1912_;
}
v_reusejp_1912_:
{
return v___x_1913_;
}
}
}
}
else
{
return v___x_1891_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll___redArg___boxed(lean_object* v_a_1916_, lean_object* v_a_1917_, lean_object* v_a_1918_, lean_object* v_a_1919_, lean_object* v_a_1920_, lean_object* v_a_1921_, lean_object* v_a_1922_){
_start:
{
lean_object* v_res_1923_; 
v_res_1923_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll___redArg(v_a_1916_, v_a_1917_, v_a_1918_, v_a_1919_, v_a_1920_, v_a_1921_);
lean_dec(v_a_1921_);
lean_dec_ref(v_a_1920_);
lean_dec(v_a_1919_);
lean_dec_ref(v_a_1918_);
lean_dec(v_a_1917_);
lean_dec_ref(v_a_1916_);
return v_res_1923_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll(lean_object* v_x_1924_, lean_object* v_a_1925_, lean_object* v_a_1926_, lean_object* v_a_1927_, lean_object* v_a_1928_, lean_object* v_a_1929_, lean_object* v_a_1930_, lean_object* v_a_1931_, lean_object* v_a_1932_){
_start:
{
lean_object* v___x_1934_; 
v___x_1934_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll___redArg(v_a_1925_, v_a_1926_, v_a_1929_, v_a_1930_, v_a_1931_, v_a_1932_);
return v___x_1934_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll___boxed(lean_object* v_x_1935_, lean_object* v_a_1936_, lean_object* v_a_1937_, lean_object* v_a_1938_, lean_object* v_a_1939_, lean_object* v_a_1940_, lean_object* v_a_1941_, lean_object* v_a_1942_, lean_object* v_a_1943_, lean_object* v_a_1944_){
_start:
{
lean_object* v_res_1945_; 
v_res_1945_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll(v_x_1935_, v_a_1936_, v_a_1937_, v_a_1938_, v_a_1939_, v_a_1940_, v_a_1941_, v_a_1942_, v_a_1943_);
lean_dec(v_a_1943_);
lean_dec_ref(v_a_1942_);
lean_dec(v_a_1941_);
lean_dec_ref(v_a_1940_);
lean_dec(v_a_1939_);
lean_dec_ref(v_a_1938_);
lean_dec(v_a_1937_);
lean_dec_ref(v_a_1936_);
lean_dec(v_x_1935_);
return v_res_1945_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll__1(){
_start:
{
lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; 
v___x_1958_ = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
v___x_1959_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll__1___closed__1));
v___x_1960_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll__1___closed__3));
v___x_1961_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll___boxed), 10, 0);
v___x_1962_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1958_, v___x_1959_, v___x_1960_, v___x_1961_);
return v___x_1962_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll__1___boxed(lean_object* v_a_1963_){
_start:
{
lean_object* v_res_1964_; 
v_res_1964_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll__1();
return v_res_1964_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___redArg___closed__1(void){
_start:
{
lean_object* v___x_1966_; lean_object* v___x_1967_; 
v___x_1966_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___redArg___closed__0));
v___x_1967_ = l_Lean_stringToMessageData(v___x_1966_);
return v___x_1967_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___redArg___closed__3(void){
_start:
{
lean_object* v___x_1969_; lean_object* v___x_1970_; 
v___x_1969_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___redArg___closed__2));
v___x_1970_ = l_Lean_stringToMessageData(v___x_1969_);
return v___x_1970_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___redArg(lean_object* v_a_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_){
_start:
{
lean_object* v___x_1978_; 
v___x_1978_ = l_Lean_Elab_Tactic_Grind_ensureSym___redArg(v_a_1971_, v_a_1973_, v_a_1974_, v_a_1975_, v_a_1976_);
if (lean_obj_tag(v___x_1978_) == 0)
{
lean_object* v___x_1979_; 
lean_dec_ref_known(v___x_1978_, 1);
v___x_1979_ = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(v_a_1972_, v_a_1973_, v_a_1974_, v_a_1975_, v_a_1976_);
if (lean_obj_tag(v___x_1979_) == 0)
{
lean_object* v_a_1980_; lean_object* v_toGoalState_1981_; lean_object* v_mvarId_1982_; lean_object* v___x_1984_; uint8_t v_isShared_1985_; uint8_t v_isSharedCheck_2084_; 
v_a_1980_ = lean_ctor_get(v___x_1979_, 0);
lean_inc(v_a_1980_);
lean_dec_ref_known(v___x_1979_, 1);
v_toGoalState_1981_ = lean_ctor_get(v_a_1980_, 0);
v_mvarId_1982_ = lean_ctor_get(v_a_1980_, 1);
v_isSharedCheck_2084_ = !lean_is_exclusive(v_a_1980_);
if (v_isSharedCheck_2084_ == 0)
{
v___x_1984_ = v_a_1980_;
v_isShared_1985_ = v_isSharedCheck_2084_;
goto v_resetjp_1983_;
}
else
{
lean_inc(v_mvarId_1982_);
lean_inc(v_toGoalState_1981_);
lean_dec(v_a_1980_);
v___x_1984_ = lean_box(0);
v_isShared_1985_ = v_isSharedCheck_2084_;
goto v_resetjp_1983_;
}
v_resetjp_1983_:
{
lean_object* v_mvarId_1987_; lean_object* v___y_1988_; lean_object* v___y_1989_; lean_object* v___y_1990_; lean_object* v___y_1991_; lean_object* v___y_1992_; lean_object* v___y_1993_; lean_object* v___x_2043_; 
lean_inc(v_mvarId_1982_);
v___x_2043_ = l_Lean_MVarId_getType(v_mvarId_1982_, v_a_1973_, v_a_1974_, v_a_1975_, v_a_1976_);
if (lean_obj_tag(v___x_2043_) == 0)
{
lean_object* v_a_2044_; lean_object* v___y_2046_; lean_object* v___y_2047_; lean_object* v___y_2048_; lean_object* v___y_2049_; lean_object* v___y_2050_; lean_object* v___y_2051_; uint8_t v___x_2073_; 
v_a_2044_ = lean_ctor_get(v___x_2043_, 0);
lean_inc_n(v_a_2044_, 2);
lean_dec_ref_known(v___x_2043_, 1);
v___x_2073_ = l_Lean_Expr_isFalse(v_a_2044_);
if (v___x_2073_ == 0)
{
v___y_2046_ = v_a_1971_;
v___y_2047_ = v_a_1972_;
v___y_2048_ = v_a_1973_;
v___y_2049_ = v_a_1974_;
v___y_2050_ = v_a_1975_;
v___y_2051_ = v_a_1976_;
goto v___jp_2045_;
}
else
{
lean_object* v___x_2074_; lean_object* v___x_2075_; 
lean_dec(v_a_2044_);
lean_del_object(v___x_1984_);
lean_dec(v_mvarId_1982_);
lean_dec_ref(v_toGoalState_1981_);
v___x_2074_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___redArg___closed__3, &l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___redArg___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___redArg___closed__3);
v___x_2075_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__2___redArg(v___x_2074_, v_a_1973_, v_a_1974_, v_a_1975_, v_a_1976_);
return v___x_2075_;
}
v___jp_2045_:
{
lean_object* v___x_2052_; 
v___x_2052_ = l_Lean_Meta_isProp(v_a_2044_, v___y_2048_, v___y_2049_, v___y_2050_, v___y_2051_);
if (lean_obj_tag(v___x_2052_) == 0)
{
lean_object* v_a_2053_; uint8_t v___x_2054_; 
v_a_2053_ = lean_ctor_get(v___x_2052_, 0);
lean_inc(v_a_2053_);
lean_dec_ref_known(v___x_2052_, 1);
v___x_2054_ = lean_unbox(v_a_2053_);
lean_dec(v_a_2053_);
if (v___x_2054_ == 0)
{
lean_object* v___x_2055_; 
v___x_2055_ = l_Lean_MVarId_exfalso(v_mvarId_1982_, v___y_2048_, v___y_2049_, v___y_2050_, v___y_2051_);
if (lean_obj_tag(v___x_2055_) == 0)
{
lean_object* v_a_2056_; 
v_a_2056_ = lean_ctor_get(v___x_2055_, 0);
lean_inc(v_a_2056_);
lean_dec_ref_known(v___x_2055_, 1);
v_mvarId_1987_ = v_a_2056_;
v___y_1988_ = v___y_2046_;
v___y_1989_ = v___y_2047_;
v___y_1990_ = v___y_2048_;
v___y_1991_ = v___y_2049_;
v___y_1992_ = v___y_2050_;
v___y_1993_ = v___y_2051_;
goto v___jp_1986_;
}
else
{
lean_object* v_a_2057_; lean_object* v___x_2059_; uint8_t v_isShared_2060_; uint8_t v_isSharedCheck_2064_; 
lean_del_object(v___x_1984_);
lean_dec_ref(v_toGoalState_1981_);
v_a_2057_ = lean_ctor_get(v___x_2055_, 0);
v_isSharedCheck_2064_ = !lean_is_exclusive(v___x_2055_);
if (v_isSharedCheck_2064_ == 0)
{
v___x_2059_ = v___x_2055_;
v_isShared_2060_ = v_isSharedCheck_2064_;
goto v_resetjp_2058_;
}
else
{
lean_inc(v_a_2057_);
lean_dec(v___x_2055_);
v___x_2059_ = lean_box(0);
v_isShared_2060_ = v_isSharedCheck_2064_;
goto v_resetjp_2058_;
}
v_resetjp_2058_:
{
lean_object* v___x_2062_; 
if (v_isShared_2060_ == 0)
{
v___x_2062_ = v___x_2059_;
goto v_reusejp_2061_;
}
else
{
lean_object* v_reuseFailAlloc_2063_; 
v_reuseFailAlloc_2063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2063_, 0, v_a_2057_);
v___x_2062_ = v_reuseFailAlloc_2063_;
goto v_reusejp_2061_;
}
v_reusejp_2061_:
{
return v___x_2062_;
}
}
}
}
else
{
v_mvarId_1987_ = v_mvarId_1982_;
v___y_1988_ = v___y_2046_;
v___y_1989_ = v___y_2047_;
v___y_1990_ = v___y_2048_;
v___y_1991_ = v___y_2049_;
v___y_1992_ = v___y_2050_;
v___y_1993_ = v___y_2051_;
goto v___jp_1986_;
}
}
else
{
lean_object* v_a_2065_; lean_object* v___x_2067_; uint8_t v_isShared_2068_; uint8_t v_isSharedCheck_2072_; 
lean_del_object(v___x_1984_);
lean_dec(v_mvarId_1982_);
lean_dec_ref(v_toGoalState_1981_);
v_a_2065_ = lean_ctor_get(v___x_2052_, 0);
v_isSharedCheck_2072_ = !lean_is_exclusive(v___x_2052_);
if (v_isSharedCheck_2072_ == 0)
{
v___x_2067_ = v___x_2052_;
v_isShared_2068_ = v_isSharedCheck_2072_;
goto v_resetjp_2066_;
}
else
{
lean_inc(v_a_2065_);
lean_dec(v___x_2052_);
v___x_2067_ = lean_box(0);
v_isShared_2068_ = v_isSharedCheck_2072_;
goto v_resetjp_2066_;
}
v_resetjp_2066_:
{
lean_object* v___x_2070_; 
if (v_isShared_2068_ == 0)
{
v___x_2070_ = v___x_2067_;
goto v_reusejp_2069_;
}
else
{
lean_object* v_reuseFailAlloc_2071_; 
v_reuseFailAlloc_2071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2071_, 0, v_a_2065_);
v___x_2070_ = v_reuseFailAlloc_2071_;
goto v_reusejp_2069_;
}
v_reusejp_2069_:
{
return v___x_2070_;
}
}
}
}
}
else
{
lean_object* v_a_2076_; lean_object* v___x_2078_; uint8_t v_isShared_2079_; uint8_t v_isSharedCheck_2083_; 
lean_del_object(v___x_1984_);
lean_dec(v_mvarId_1982_);
lean_dec_ref(v_toGoalState_1981_);
v_a_2076_ = lean_ctor_get(v___x_2043_, 0);
v_isSharedCheck_2083_ = !lean_is_exclusive(v___x_2043_);
if (v_isSharedCheck_2083_ == 0)
{
v___x_2078_ = v___x_2043_;
v_isShared_2079_ = v_isSharedCheck_2083_;
goto v_resetjp_2077_;
}
else
{
lean_inc(v_a_2076_);
lean_dec(v___x_2043_);
v___x_2078_ = lean_box(0);
v_isShared_2079_ = v_isSharedCheck_2083_;
goto v_resetjp_2077_;
}
v_resetjp_2077_:
{
lean_object* v___x_2081_; 
if (v_isShared_2079_ == 0)
{
v___x_2081_ = v___x_2078_;
goto v_reusejp_2080_;
}
else
{
lean_object* v_reuseFailAlloc_2082_; 
v_reuseFailAlloc_2082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2082_, 0, v_a_2076_);
v___x_2081_ = v_reuseFailAlloc_2082_;
goto v_reusejp_2080_;
}
v_reusejp_2080_:
{
return v___x_2081_;
}
}
}
v___jp_1986_:
{
lean_object* v___x_1994_; 
v___x_1994_ = l_Lean_MVarId_byContra_x3f(v_mvarId_1987_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_);
if (lean_obj_tag(v___x_1994_) == 0)
{
lean_object* v_a_1995_; 
v_a_1995_ = lean_ctor_get(v___x_1994_, 0);
lean_inc(v_a_1995_);
lean_dec_ref_known(v___x_1994_, 1);
if (lean_obj_tag(v_a_1995_) == 1)
{
lean_object* v_val_1996_; uint8_t v___x_1997_; lean_object* v___x_1998_; 
v_val_1996_ = lean_ctor_get(v_a_1995_, 0);
lean_inc(v_val_1996_);
lean_dec_ref_known(v_a_1995_, 1);
v___x_1997_ = 0;
v___x_1998_ = l_Lean_Meta_intro1Core(v_val_1996_, v___x_1997_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_);
if (lean_obj_tag(v___x_1998_) == 0)
{
lean_object* v_a_1999_; lean_object* v_snd_2000_; lean_object* v___x_2002_; uint8_t v_isShared_2003_; uint8_t v_isSharedCheck_2023_; 
v_a_1999_ = lean_ctor_get(v___x_1998_, 0);
lean_inc(v_a_1999_);
lean_dec_ref_known(v___x_1998_, 1);
v_snd_2000_ = lean_ctor_get(v_a_1999_, 1);
v_isSharedCheck_2023_ = !lean_is_exclusive(v_a_1999_);
if (v_isSharedCheck_2023_ == 0)
{
lean_object* v_unused_2024_; 
v_unused_2024_ = lean_ctor_get(v_a_1999_, 0);
lean_dec(v_unused_2024_);
v___x_2002_ = v_a_1999_;
v_isShared_2003_ = v_isSharedCheck_2023_;
goto v_resetjp_2001_;
}
else
{
lean_inc(v_snd_2000_);
lean_dec(v_a_1999_);
v___x_2002_ = lean_box(0);
v_isShared_2003_ = v_isSharedCheck_2023_;
goto v_resetjp_2001_;
}
v_resetjp_2001_:
{
lean_object* v___x_2005_; 
if (v_isShared_1985_ == 0)
{
lean_ctor_set(v___x_1984_, 1, v_snd_2000_);
v___x_2005_ = v___x_1984_;
goto v_reusejp_2004_;
}
else
{
lean_object* v_reuseFailAlloc_2022_; 
v_reuseFailAlloc_2022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2022_, 0, v_toGoalState_1981_);
lean_ctor_set(v_reuseFailAlloc_2022_, 1, v_snd_2000_);
v___x_2005_ = v_reuseFailAlloc_2022_;
goto v_reusejp_2004_;
}
v_reusejp_2004_:
{
lean_object* v___x_2006_; lean_object* v___x_2007_; 
v___x_2006_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Goal_internalizeAll___boxed), 11, 1);
lean_closure_set(v___x_2006_, 0, v___x_2005_);
v___x_2007_ = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(v___x_2006_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_);
if (lean_obj_tag(v___x_2007_) == 0)
{
lean_object* v_a_2008_; lean_object* v___x_2009_; lean_object* v___x_2011_; 
v_a_2008_ = lean_ctor_get(v___x_2007_, 0);
lean_inc(v_a_2008_);
lean_dec_ref_known(v___x_2007_, 1);
v___x_2009_ = lean_box(0);
if (v_isShared_2003_ == 0)
{
lean_ctor_set_tag(v___x_2002_, 1);
lean_ctor_set(v___x_2002_, 1, v___x_2009_);
lean_ctor_set(v___x_2002_, 0, v_a_2008_);
v___x_2011_ = v___x_2002_;
goto v_reusejp_2010_;
}
else
{
lean_object* v_reuseFailAlloc_2013_; 
v_reuseFailAlloc_2013_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2013_, 0, v_a_2008_);
lean_ctor_set(v_reuseFailAlloc_2013_, 1, v___x_2009_);
v___x_2011_ = v_reuseFailAlloc_2013_;
goto v_reusejp_2010_;
}
v_reusejp_2010_:
{
lean_object* v___x_2012_; 
v___x_2012_ = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(v___x_2011_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_);
return v___x_2012_;
}
}
else
{
lean_object* v_a_2014_; lean_object* v___x_2016_; uint8_t v_isShared_2017_; uint8_t v_isSharedCheck_2021_; 
lean_del_object(v___x_2002_);
v_a_2014_ = lean_ctor_get(v___x_2007_, 0);
v_isSharedCheck_2021_ = !lean_is_exclusive(v___x_2007_);
if (v_isSharedCheck_2021_ == 0)
{
v___x_2016_ = v___x_2007_;
v_isShared_2017_ = v_isSharedCheck_2021_;
goto v_resetjp_2015_;
}
else
{
lean_inc(v_a_2014_);
lean_dec(v___x_2007_);
v___x_2016_ = lean_box(0);
v_isShared_2017_ = v_isSharedCheck_2021_;
goto v_resetjp_2015_;
}
v_resetjp_2015_:
{
lean_object* v___x_2019_; 
if (v_isShared_2017_ == 0)
{
v___x_2019_ = v___x_2016_;
goto v_reusejp_2018_;
}
else
{
lean_object* v_reuseFailAlloc_2020_; 
v_reuseFailAlloc_2020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2020_, 0, v_a_2014_);
v___x_2019_ = v_reuseFailAlloc_2020_;
goto v_reusejp_2018_;
}
v_reusejp_2018_:
{
return v___x_2019_;
}
}
}
}
}
}
else
{
lean_object* v_a_2025_; lean_object* v___x_2027_; uint8_t v_isShared_2028_; uint8_t v_isSharedCheck_2032_; 
lean_del_object(v___x_1984_);
lean_dec_ref(v_toGoalState_1981_);
v_a_2025_ = lean_ctor_get(v___x_1998_, 0);
v_isSharedCheck_2032_ = !lean_is_exclusive(v___x_1998_);
if (v_isSharedCheck_2032_ == 0)
{
v___x_2027_ = v___x_1998_;
v_isShared_2028_ = v_isSharedCheck_2032_;
goto v_resetjp_2026_;
}
else
{
lean_inc(v_a_2025_);
lean_dec(v___x_1998_);
v___x_2027_ = lean_box(0);
v_isShared_2028_ = v_isSharedCheck_2032_;
goto v_resetjp_2026_;
}
v_resetjp_2026_:
{
lean_object* v___x_2030_; 
if (v_isShared_2028_ == 0)
{
v___x_2030_ = v___x_2027_;
goto v_reusejp_2029_;
}
else
{
lean_object* v_reuseFailAlloc_2031_; 
v_reuseFailAlloc_2031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2031_, 0, v_a_2025_);
v___x_2030_ = v_reuseFailAlloc_2031_;
goto v_reusejp_2029_;
}
v_reusejp_2029_:
{
return v___x_2030_;
}
}
}
}
else
{
lean_object* v___x_2033_; lean_object* v___x_2034_; 
lean_dec(v_a_1995_);
lean_del_object(v___x_1984_);
lean_dec_ref(v_toGoalState_1981_);
v___x_2033_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___redArg___closed__1, &l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___redArg___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___redArg___closed__1);
v___x_2034_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__2___redArg(v___x_2033_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_);
return v___x_2034_;
}
}
else
{
lean_object* v_a_2035_; lean_object* v___x_2037_; uint8_t v_isShared_2038_; uint8_t v_isSharedCheck_2042_; 
lean_del_object(v___x_1984_);
lean_dec_ref(v_toGoalState_1981_);
v_a_2035_ = lean_ctor_get(v___x_1994_, 0);
v_isSharedCheck_2042_ = !lean_is_exclusive(v___x_1994_);
if (v_isSharedCheck_2042_ == 0)
{
v___x_2037_ = v___x_1994_;
v_isShared_2038_ = v_isSharedCheck_2042_;
goto v_resetjp_2036_;
}
else
{
lean_inc(v_a_2035_);
lean_dec(v___x_1994_);
v___x_2037_ = lean_box(0);
v_isShared_2038_ = v_isSharedCheck_2042_;
goto v_resetjp_2036_;
}
v_resetjp_2036_:
{
lean_object* v___x_2040_; 
if (v_isShared_2038_ == 0)
{
v___x_2040_ = v___x_2037_;
goto v_reusejp_2039_;
}
else
{
lean_object* v_reuseFailAlloc_2041_; 
v_reuseFailAlloc_2041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2041_, 0, v_a_2035_);
v___x_2040_ = v_reuseFailAlloc_2041_;
goto v_reusejp_2039_;
}
v_reusejp_2039_:
{
return v___x_2040_;
}
}
}
}
}
}
else
{
lean_object* v_a_2085_; lean_object* v___x_2087_; uint8_t v_isShared_2088_; uint8_t v_isSharedCheck_2092_; 
v_a_2085_ = lean_ctor_get(v___x_1979_, 0);
v_isSharedCheck_2092_ = !lean_is_exclusive(v___x_1979_);
if (v_isSharedCheck_2092_ == 0)
{
v___x_2087_ = v___x_1979_;
v_isShared_2088_ = v_isSharedCheck_2092_;
goto v_resetjp_2086_;
}
else
{
lean_inc(v_a_2085_);
lean_dec(v___x_1979_);
v___x_2087_ = lean_box(0);
v_isShared_2088_ = v_isSharedCheck_2092_;
goto v_resetjp_2086_;
}
v_resetjp_2086_:
{
lean_object* v___x_2090_; 
if (v_isShared_2088_ == 0)
{
v___x_2090_ = v___x_2087_;
goto v_reusejp_2089_;
}
else
{
lean_object* v_reuseFailAlloc_2091_; 
v_reuseFailAlloc_2091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2091_, 0, v_a_2085_);
v___x_2090_ = v_reuseFailAlloc_2091_;
goto v_reusejp_2089_;
}
v_reusejp_2089_:
{
return v___x_2090_;
}
}
}
}
else
{
return v___x_1978_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___redArg___boxed(lean_object* v_a_2093_, lean_object* v_a_2094_, lean_object* v_a_2095_, lean_object* v_a_2096_, lean_object* v_a_2097_, lean_object* v_a_2098_, lean_object* v_a_2099_){
_start:
{
lean_object* v_res_2100_; 
v_res_2100_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___redArg(v_a_2093_, v_a_2094_, v_a_2095_, v_a_2096_, v_a_2097_, v_a_2098_);
lean_dec(v_a_2098_);
lean_dec_ref(v_a_2097_);
lean_dec(v_a_2096_);
lean_dec_ref(v_a_2095_);
lean_dec(v_a_2094_);
lean_dec_ref(v_a_2093_);
return v_res_2100_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra(lean_object* v_x_2101_, lean_object* v_a_2102_, lean_object* v_a_2103_, lean_object* v_a_2104_, lean_object* v_a_2105_, lean_object* v_a_2106_, lean_object* v_a_2107_, lean_object* v_a_2108_, lean_object* v_a_2109_){
_start:
{
lean_object* v___x_2111_; 
v___x_2111_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___redArg(v_a_2102_, v_a_2103_, v_a_2106_, v_a_2107_, v_a_2108_, v_a_2109_);
return v___x_2111_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___boxed(lean_object* v_x_2112_, lean_object* v_a_2113_, lean_object* v_a_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_, lean_object* v_a_2119_, lean_object* v_a_2120_, lean_object* v_a_2121_){
_start:
{
lean_object* v_res_2122_; 
v_res_2122_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra(v_x_2112_, v_a_2113_, v_a_2114_, v_a_2115_, v_a_2116_, v_a_2117_, v_a_2118_, v_a_2119_, v_a_2120_);
lean_dec(v_a_2120_);
lean_dec_ref(v_a_2119_);
lean_dec(v_a_2118_);
lean_dec_ref(v_a_2117_);
lean_dec(v_a_2116_);
lean_dec_ref(v_a_2115_);
lean_dec(v_a_2114_);
lean_dec_ref(v_a_2113_);
lean_dec(v_x_2112_);
return v_res_2122_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra__1(){
_start:
{
lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; 
v___x_2135_ = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
v___x_2136_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra__1___closed__1));
v___x_2137_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra__1___closed__3));
v___x_2138_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___boxed), 10, 0);
v___x_2139_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2135_, v___x_2136_, v___x_2137_, v___x_2138_);
return v___x_2139_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra__1___boxed(lean_object* v_a_2140_){
_start:
{
lean_object* v_res_2141_; 
v_res_2141_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra__1();
return v_res_2141_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_trivialSimproc___redArg(){
_start:
{
lean_object* v___x_2145_; lean_object* v___x_2146_; 
v___x_2145_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_trivialSimproc___redArg___closed__0));
v___x_2146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2146_, 0, v___x_2145_);
return v___x_2146_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_trivialSimproc___redArg___boxed(lean_object* v_a_2147_){
_start:
{
lean_object* v_res_2148_; 
v_res_2148_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_trivialSimproc___redArg();
return v_res_2148_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_trivialSimproc(lean_object* v_x_2149_, lean_object* v_a_2150_, lean_object* v_a_2151_, lean_object* v_a_2152_, lean_object* v_a_2153_, lean_object* v_a_2154_, lean_object* v_a_2155_, lean_object* v_a_2156_, lean_object* v_a_2157_, lean_object* v_a_2158_){
_start:
{
lean_object* v___x_2160_; 
v___x_2160_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_trivialSimproc___redArg();
return v___x_2160_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_trivialSimproc___boxed(lean_object* v_x_2161_, lean_object* v_a_2162_, lean_object* v_a_2163_, lean_object* v_a_2164_, lean_object* v_a_2165_, lean_object* v_a_2166_, lean_object* v_a_2167_, lean_object* v_a_2168_, lean_object* v_a_2169_, lean_object* v_a_2170_, lean_object* v_a_2171_){
_start:
{
lean_object* v_res_2172_; 
v_res_2172_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_trivialSimproc(v_x_2161_, v_a_2162_, v_a_2163_, v_a_2164_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_);
lean_dec(v_a_2170_);
lean_dec_ref(v_a_2169_);
lean_dec(v_a_2168_);
lean_dec_ref(v_a_2167_);
lean_dec(v_a_2166_);
lean_dec_ref(v_a_2165_);
lean_dec(v_a_2164_);
lean_dec_ref(v_a_2163_);
lean_dec(v_a_2162_);
lean_dec_ref(v_x_2161_);
return v_res_2172_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabOptSimproc(lean_object* v_stx_x3f_2173_, lean_object* v_a_2174_, lean_object* v_a_2175_, lean_object* v_a_2176_, lean_object* v_a_2177_, lean_object* v_a_2178_, lean_object* v_a_2179_, lean_object* v_a_2180_, lean_object* v_a_2181_){
_start:
{
if (lean_obj_tag(v_stx_x3f_2173_) == 1)
{
lean_object* v_val_2183_; lean_object* v___x_2184_; 
v_val_2183_ = lean_ctor_get(v_stx_x3f_2173_, 0);
lean_inc(v_val_2183_);
lean_dec_ref_known(v_stx_x3f_2173_, 1);
v___x_2184_ = l_Lean_Elab_Tactic_Grind_elabSymSimproc(v_val_2183_, v_a_2174_, v_a_2175_, v_a_2176_, v_a_2177_, v_a_2178_, v_a_2179_, v_a_2180_, v_a_2181_);
return v___x_2184_;
}
else
{
lean_object* v___x_2185_; lean_object* v___x_2186_; 
lean_dec(v_stx_x3f_2173_);
v___x_2185_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_trivialSimproc___boxed), 11, 0);
v___x_2186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2186_, 0, v___x_2185_);
return v___x_2186_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabOptSimproc___boxed(lean_object* v_stx_x3f_2187_, lean_object* v_a_2188_, lean_object* v_a_2189_, lean_object* v_a_2190_, lean_object* v_a_2191_, lean_object* v_a_2192_, lean_object* v_a_2193_, lean_object* v_a_2194_, lean_object* v_a_2195_, lean_object* v_a_2196_){
_start:
{
lean_object* v_res_2197_; 
v_res_2197_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabOptSimproc(v_stx_x3f_2187_, v_a_2188_, v_a_2189_, v_a_2190_, v_a_2191_, v_a_2192_, v_a_2193_, v_a_2194_, v_a_2195_);
lean_dec(v_a_2195_);
lean_dec_ref(v_a_2194_);
lean_dec(v_a_2193_);
lean_dec_ref(v_a_2192_);
lean_dec(v_a_2191_);
lean_dec_ref(v_a_2190_);
lean_dec(v_a_2189_);
lean_dec_ref(v_a_2188_);
return v_res_2197_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__0___redArg(lean_object* v___x_2198_, lean_object* v_as_2199_, size_t v_sz_2200_, size_t v_i_2201_, lean_object* v_b_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_){
_start:
{
lean_object* v_a_2209_; uint8_t v___x_2213_; 
v___x_2213_ = lean_usize_dec_lt(v_i_2201_, v_sz_2200_);
if (v___x_2213_ == 0)
{
lean_object* v___x_2214_; 
v___x_2214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2214_, 0, v_b_2202_);
return v___x_2214_;
}
else
{
lean_object* v_fst_2215_; lean_object* v_snd_2216_; lean_object* v___x_2218_; uint8_t v_isShared_2219_; uint8_t v_isSharedCheck_2274_; 
v_fst_2215_ = lean_ctor_get(v_b_2202_, 0);
v_snd_2216_ = lean_ctor_get(v_b_2202_, 1);
v_isSharedCheck_2274_ = !lean_is_exclusive(v_b_2202_);
if (v_isSharedCheck_2274_ == 0)
{
v___x_2218_ = v_b_2202_;
v_isShared_2219_ = v_isSharedCheck_2274_;
goto v_resetjp_2217_;
}
else
{
lean_inc(v_snd_2216_);
lean_inc(v_fst_2215_);
lean_dec(v_b_2202_);
v___x_2218_ = lean_box(0);
v_isShared_2219_ = v_isSharedCheck_2274_;
goto v_resetjp_2217_;
}
v_resetjp_2217_:
{
lean_object* v_a_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; 
v_a_2220_ = lean_array_uget_borrowed(v_as_2199_, v_i_2201_);
v___x_2221_ = l_Lean_TSyntax_getId(v_a_2220_);
v___x_2222_ = l_Lean_LocalContext_findFromUserName_x3f(v___x_2198_, v___x_2221_);
lean_dec(v___x_2221_);
if (lean_obj_tag(v___x_2222_) == 1)
{
lean_object* v_val_2223_; lean_object* v___x_2225_; uint8_t v_isShared_2226_; uint8_t v_isSharedCheck_2247_; 
v_val_2223_ = lean_ctor_get(v___x_2222_, 0);
v_isSharedCheck_2247_ = !lean_is_exclusive(v___x_2222_);
if (v_isSharedCheck_2247_ == 0)
{
v___x_2225_ = v___x_2222_;
v_isShared_2226_ = v_isSharedCheck_2247_;
goto v_resetjp_2224_;
}
else
{
lean_inc(v_val_2223_);
lean_dec(v___x_2222_);
v___x_2225_ = lean_box(0);
v_isShared_2226_ = v_isSharedCheck_2247_;
goto v_resetjp_2224_;
}
v_resetjp_2224_:
{
lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; 
v___x_2227_ = l_Lean_LocalDecl_fvarId(v_val_2223_);
v___x_2228_ = l_Lean_LocalDecl_toExpr(v_val_2223_);
v___x_2229_ = l_Lean_Meta_Sym_Simp_mkTheoremFromExpr(v___x_2228_, v___y_2203_, v___y_2204_, v___y_2205_, v___y_2206_);
if (lean_obj_tag(v___x_2229_) == 0)
{
lean_object* v_a_2230_; lean_object* v___x_2232_; 
v_a_2230_ = lean_ctor_get(v___x_2229_, 0);
lean_inc(v_a_2230_);
lean_dec_ref_known(v___x_2229_, 1);
if (v_isShared_2226_ == 0)
{
lean_ctor_set(v___x_2225_, 0, v___x_2227_);
v___x_2232_ = v___x_2225_;
goto v_reusejp_2231_;
}
else
{
lean_object* v_reuseFailAlloc_2238_; 
v_reuseFailAlloc_2238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2238_, 0, v___x_2227_);
v___x_2232_ = v_reuseFailAlloc_2238_;
goto v_reusejp_2231_;
}
v_reusejp_2231_:
{
lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2236_; 
v___x_2233_ = lean_array_push(v_fst_2215_, v___x_2232_);
v___x_2234_ = lean_array_push(v_snd_2216_, v_a_2230_);
if (v_isShared_2219_ == 0)
{
lean_ctor_set(v___x_2218_, 1, v___x_2234_);
lean_ctor_set(v___x_2218_, 0, v___x_2233_);
v___x_2236_ = v___x_2218_;
goto v_reusejp_2235_;
}
else
{
lean_object* v_reuseFailAlloc_2237_; 
v_reuseFailAlloc_2237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2237_, 0, v___x_2233_);
lean_ctor_set(v_reuseFailAlloc_2237_, 1, v___x_2234_);
v___x_2236_ = v_reuseFailAlloc_2237_;
goto v_reusejp_2235_;
}
v_reusejp_2235_:
{
v_a_2209_ = v___x_2236_;
goto v___jp_2208_;
}
}
}
else
{
lean_object* v_a_2239_; lean_object* v___x_2241_; uint8_t v_isShared_2242_; uint8_t v_isSharedCheck_2246_; 
lean_dec(v___x_2227_);
lean_del_object(v___x_2225_);
lean_del_object(v___x_2218_);
lean_dec(v_snd_2216_);
lean_dec(v_fst_2215_);
v_a_2239_ = lean_ctor_get(v___x_2229_, 0);
v_isSharedCheck_2246_ = !lean_is_exclusive(v___x_2229_);
if (v_isSharedCheck_2246_ == 0)
{
v___x_2241_ = v___x_2229_;
v_isShared_2242_ = v_isSharedCheck_2246_;
goto v_resetjp_2240_;
}
else
{
lean_inc(v_a_2239_);
lean_dec(v___x_2229_);
v___x_2241_ = lean_box(0);
v_isShared_2242_ = v_isSharedCheck_2246_;
goto v_resetjp_2240_;
}
v_resetjp_2240_:
{
lean_object* v___x_2244_; 
if (v_isShared_2242_ == 0)
{
v___x_2244_ = v___x_2241_;
goto v_reusejp_2243_;
}
else
{
lean_object* v_reuseFailAlloc_2245_; 
v_reuseFailAlloc_2245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2245_, 0, v_a_2239_);
v___x_2244_ = v_reuseFailAlloc_2245_;
goto v_reusejp_2243_;
}
v_reusejp_2243_:
{
return v___x_2244_;
}
}
}
}
}
else
{
lean_object* v___x_2248_; 
lean_dec(v___x_2222_);
lean_inc(v_a_2220_);
v___x_2248_ = l_Lean_realizeGlobalConstNoOverload(v_a_2220_, v___y_2205_, v___y_2206_);
if (lean_obj_tag(v___x_2248_) == 0)
{
lean_object* v_a_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; 
v_a_2249_ = lean_ctor_get(v___x_2248_, 0);
lean_inc_n(v_a_2249_, 2);
lean_dec_ref_known(v___x_2248_, 1);
v___x_2250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2250_, 0, v_a_2249_);
v___x_2251_ = l_Lean_Meta_Sym_Simp_mkTheoremFromDecl(v_a_2249_, v___y_2203_, v___y_2204_, v___y_2205_, v___y_2206_);
if (lean_obj_tag(v___x_2251_) == 0)
{
lean_object* v_a_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2256_; 
v_a_2252_ = lean_ctor_get(v___x_2251_, 0);
lean_inc(v_a_2252_);
lean_dec_ref_known(v___x_2251_, 1);
v___x_2253_ = lean_array_push(v_fst_2215_, v___x_2250_);
v___x_2254_ = lean_array_push(v_snd_2216_, v_a_2252_);
if (v_isShared_2219_ == 0)
{
lean_ctor_set(v___x_2218_, 1, v___x_2254_);
lean_ctor_set(v___x_2218_, 0, v___x_2253_);
v___x_2256_ = v___x_2218_;
goto v_reusejp_2255_;
}
else
{
lean_object* v_reuseFailAlloc_2257_; 
v_reuseFailAlloc_2257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2257_, 0, v___x_2253_);
lean_ctor_set(v_reuseFailAlloc_2257_, 1, v___x_2254_);
v___x_2256_ = v_reuseFailAlloc_2257_;
goto v_reusejp_2255_;
}
v_reusejp_2255_:
{
v_a_2209_ = v___x_2256_;
goto v___jp_2208_;
}
}
else
{
lean_object* v_a_2258_; lean_object* v___x_2260_; uint8_t v_isShared_2261_; uint8_t v_isSharedCheck_2265_; 
lean_dec_ref_known(v___x_2250_, 1);
lean_del_object(v___x_2218_);
lean_dec(v_snd_2216_);
lean_dec(v_fst_2215_);
v_a_2258_ = lean_ctor_get(v___x_2251_, 0);
v_isSharedCheck_2265_ = !lean_is_exclusive(v___x_2251_);
if (v_isSharedCheck_2265_ == 0)
{
v___x_2260_ = v___x_2251_;
v_isShared_2261_ = v_isSharedCheck_2265_;
goto v_resetjp_2259_;
}
else
{
lean_inc(v_a_2258_);
lean_dec(v___x_2251_);
v___x_2260_ = lean_box(0);
v_isShared_2261_ = v_isSharedCheck_2265_;
goto v_resetjp_2259_;
}
v_resetjp_2259_:
{
lean_object* v___x_2263_; 
if (v_isShared_2261_ == 0)
{
v___x_2263_ = v___x_2260_;
goto v_reusejp_2262_;
}
else
{
lean_object* v_reuseFailAlloc_2264_; 
v_reuseFailAlloc_2264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2264_, 0, v_a_2258_);
v___x_2263_ = v_reuseFailAlloc_2264_;
goto v_reusejp_2262_;
}
v_reusejp_2262_:
{
return v___x_2263_;
}
}
}
}
else
{
lean_object* v_a_2266_; lean_object* v___x_2268_; uint8_t v_isShared_2269_; uint8_t v_isSharedCheck_2273_; 
lean_del_object(v___x_2218_);
lean_dec(v_snd_2216_);
lean_dec(v_fst_2215_);
v_a_2266_ = lean_ctor_get(v___x_2248_, 0);
v_isSharedCheck_2273_ = !lean_is_exclusive(v___x_2248_);
if (v_isSharedCheck_2273_ == 0)
{
v___x_2268_ = v___x_2248_;
v_isShared_2269_ = v_isSharedCheck_2273_;
goto v_resetjp_2267_;
}
else
{
lean_inc(v_a_2266_);
lean_dec(v___x_2248_);
v___x_2268_ = lean_box(0);
v_isShared_2269_ = v_isSharedCheck_2273_;
goto v_resetjp_2267_;
}
v_resetjp_2267_:
{
lean_object* v___x_2271_; 
if (v_isShared_2269_ == 0)
{
v___x_2271_ = v___x_2268_;
goto v_reusejp_2270_;
}
else
{
lean_object* v_reuseFailAlloc_2272_; 
v_reuseFailAlloc_2272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2272_, 0, v_a_2266_);
v___x_2271_ = v_reuseFailAlloc_2272_;
goto v_reusejp_2270_;
}
v_reusejp_2270_:
{
return v___x_2271_;
}
}
}
}
}
}
v___jp_2208_:
{
size_t v___x_2210_; size_t v___x_2211_; 
v___x_2210_ = ((size_t)1ULL);
v___x_2211_ = lean_usize_add(v_i_2201_, v___x_2210_);
v_i_2201_ = v___x_2211_;
v_b_2202_ = v_a_2209_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__0___redArg___boxed(lean_object* v___x_2275_, lean_object* v_as_2276_, lean_object* v_sz_2277_, lean_object* v_i_2278_, lean_object* v_b_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_){
_start:
{
size_t v_sz_boxed_2285_; size_t v_i_boxed_2286_; lean_object* v_res_2287_; 
v_sz_boxed_2285_ = lean_unbox_usize(v_sz_2277_);
lean_dec(v_sz_2277_);
v_i_boxed_2286_ = lean_unbox_usize(v_i_2278_);
lean_dec(v_i_2278_);
v_res_2287_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__0___redArg(v___x_2275_, v_as_2276_, v_sz_boxed_2285_, v_i_boxed_2286_, v_b_2279_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_);
lean_dec(v___y_2283_);
lean_dec_ref(v___y_2282_);
lean_dec(v___y_2281_);
lean_dec_ref(v___y_2280_);
lean_dec_ref(v_as_2276_);
lean_dec_ref(v___x_2275_);
return v_res_2287_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems(lean_object* v_ids_x3f_2292_, lean_object* v_a_2293_, lean_object* v_a_2294_, lean_object* v_a_2295_, lean_object* v_a_2296_, lean_object* v_a_2297_, lean_object* v_a_2298_, lean_object* v_a_2299_, lean_object* v_a_2300_){
_start:
{
if (lean_obj_tag(v_ids_x3f_2292_) == 1)
{
lean_object* v_val_2302_; lean_object* v_lctx_2303_; lean_object* v___x_2304_; size_t v_sz_2305_; size_t v___x_2306_; lean_object* v___x_2307_; 
v_val_2302_ = lean_ctor_get(v_ids_x3f_2292_, 0);
v_lctx_2303_ = lean_ctor_get(v_a_2297_, 2);
v___x_2304_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems___closed__1));
v_sz_2305_ = lean_array_size(v_val_2302_);
v___x_2306_ = ((size_t)0ULL);
v___x_2307_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__0___redArg(v_lctx_2303_, v_val_2302_, v_sz_2305_, v___x_2306_, v___x_2304_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_);
if (lean_obj_tag(v___x_2307_) == 0)
{
lean_object* v_a_2308_; lean_object* v___x_2310_; uint8_t v_isShared_2311_; uint8_t v_isSharedCheck_2324_; 
v_a_2308_ = lean_ctor_get(v___x_2307_, 0);
v_isSharedCheck_2324_ = !lean_is_exclusive(v___x_2307_);
if (v_isSharedCheck_2324_ == 0)
{
v___x_2310_ = v___x_2307_;
v_isShared_2311_ = v_isSharedCheck_2324_;
goto v_resetjp_2309_;
}
else
{
lean_inc(v_a_2308_);
lean_dec(v___x_2307_);
v___x_2310_ = lean_box(0);
v_isShared_2311_ = v_isSharedCheck_2324_;
goto v_resetjp_2309_;
}
v_resetjp_2309_:
{
lean_object* v_fst_2312_; lean_object* v_snd_2313_; lean_object* v___x_2315_; uint8_t v_isShared_2316_; uint8_t v_isSharedCheck_2323_; 
v_fst_2312_ = lean_ctor_get(v_a_2308_, 0);
v_snd_2313_ = lean_ctor_get(v_a_2308_, 1);
v_isSharedCheck_2323_ = !lean_is_exclusive(v_a_2308_);
if (v_isSharedCheck_2323_ == 0)
{
v___x_2315_ = v_a_2308_;
v_isShared_2316_ = v_isSharedCheck_2323_;
goto v_resetjp_2314_;
}
else
{
lean_inc(v_snd_2313_);
lean_inc(v_fst_2312_);
lean_dec(v_a_2308_);
v___x_2315_ = lean_box(0);
v_isShared_2316_ = v_isSharedCheck_2323_;
goto v_resetjp_2314_;
}
v_resetjp_2314_:
{
lean_object* v___x_2318_; 
if (v_isShared_2316_ == 0)
{
v___x_2318_ = v___x_2315_;
goto v_reusejp_2317_;
}
else
{
lean_object* v_reuseFailAlloc_2322_; 
v_reuseFailAlloc_2322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2322_, 0, v_fst_2312_);
lean_ctor_set(v_reuseFailAlloc_2322_, 1, v_snd_2313_);
v___x_2318_ = v_reuseFailAlloc_2322_;
goto v_reusejp_2317_;
}
v_reusejp_2317_:
{
lean_object* v___x_2320_; 
if (v_isShared_2311_ == 0)
{
lean_ctor_set(v___x_2310_, 0, v___x_2318_);
v___x_2320_ = v___x_2310_;
goto v_reusejp_2319_;
}
else
{
lean_object* v_reuseFailAlloc_2321_; 
v_reuseFailAlloc_2321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2321_, 0, v___x_2318_);
v___x_2320_ = v_reuseFailAlloc_2321_;
goto v_reusejp_2319_;
}
v_reusejp_2319_:
{
return v___x_2320_;
}
}
}
}
}
else
{
return v___x_2307_;
}
}
else
{
lean_object* v___x_2325_; lean_object* v___x_2326_; 
v___x_2325_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems___closed__1));
v___x_2326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2326_, 0, v___x_2325_);
return v___x_2326_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems___boxed(lean_object* v_ids_x3f_2327_, lean_object* v_a_2328_, lean_object* v_a_2329_, lean_object* v_a_2330_, lean_object* v_a_2331_, lean_object* v_a_2332_, lean_object* v_a_2333_, lean_object* v_a_2334_, lean_object* v_a_2335_, lean_object* v_a_2336_){
_start:
{
lean_object* v_res_2337_; 
v_res_2337_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems(v_ids_x3f_2327_, v_a_2328_, v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_);
lean_dec(v_a_2335_);
lean_dec_ref(v_a_2334_);
lean_dec(v_a_2333_);
lean_dec_ref(v_a_2332_);
lean_dec(v_a_2331_);
lean_dec_ref(v_a_2330_);
lean_dec(v_a_2329_);
lean_dec_ref(v_a_2328_);
lean_dec(v_ids_x3f_2327_);
return v_res_2337_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__0(lean_object* v___x_2338_, lean_object* v_as_2339_, size_t v_sz_2340_, size_t v_i_2341_, lean_object* v_b_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_){
_start:
{
lean_object* v___x_2352_; 
v___x_2352_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__0___redArg(v___x_2338_, v_as_2339_, v_sz_2340_, v_i_2341_, v_b_2342_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_);
return v___x_2352_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__0___boxed(lean_object* v___x_2353_, lean_object* v_as_2354_, lean_object* v_sz_2355_, lean_object* v_i_2356_, lean_object* v_b_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_){
_start:
{
size_t v_sz_boxed_2367_; size_t v_i_boxed_2368_; lean_object* v_res_2369_; 
v_sz_boxed_2367_ = lean_unbox_usize(v_sz_2355_);
lean_dec(v_sz_2355_);
v_i_boxed_2368_ = lean_unbox_usize(v_i_2356_);
lean_dec(v_i_2356_);
v_res_2369_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__0(v___x_2353_, v_as_2354_, v_sz_boxed_2367_, v_i_boxed_2368_, v_b_2357_, v___y_2358_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_);
lean_dec(v___y_2365_);
lean_dec_ref(v___y_2364_);
lean_dec(v___y_2363_);
lean_dec_ref(v___y_2362_);
lean_dec(v___y_2361_);
lean_dec_ref(v___y_2360_);
lean_dec(v___y_2359_);
lean_dec_ref(v___y_2358_);
lean_dec_ref(v_as_2354_);
lean_dec_ref(v___x_2353_);
return v_res_2369_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___lam__0(lean_object* v_a_2371_, lean_object* v_x_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_){
_start:
{
lean_object* v___x_2384_; lean_object* v___x_2385_; 
v___x_2384_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___lam__0___closed__0));
v___x_2385_ = l_Lean_Meta_Sym_Simp_Theorems_rewrite(v_a_2371_, v___x_2384_, v___y_2373_, v___y_2374_, v___y_2375_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_);
return v___x_2385_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___lam__0___boxed(lean_object* v_a_2386_, lean_object* v_x_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_){
_start:
{
lean_object* v_res_2399_; 
v_res_2399_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___lam__0(v_a_2386_, v_x_2387_, v___y_2388_, v___y_2389_, v___y_2390_, v___y_2391_, v___y_2392_, v___y_2393_, v___y_2394_, v___y_2395_, v___y_2396_, v___y_2397_);
lean_dec(v___y_2397_);
lean_dec_ref(v___y_2396_);
lean_dec(v___y_2395_);
lean_dec_ref(v___y_2394_);
lean_dec(v___y_2393_);
lean_dec_ref(v___y_2392_);
lean_dec(v___y_2391_);
lean_dec_ref(v___y_2390_);
lean_dec(v___y_2389_);
lean_dec_ref(v_a_2386_);
return v_res_2399_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___lam__1(lean_object* v_post_2400_, lean_object* v___f_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_){
_start:
{
lean_object* v___x_2413_; 
lean_inc(v___y_2411_);
lean_inc_ref(v___y_2410_);
lean_inc(v___y_2409_);
lean_inc_ref(v___y_2408_);
lean_inc(v___y_2407_);
lean_inc_ref(v___y_2406_);
lean_inc(v___y_2405_);
lean_inc_ref(v___y_2404_);
lean_inc(v___y_2403_);
lean_inc_ref(v___y_2402_);
v___x_2413_ = lean_apply_11(v_post_2400_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_, lean_box(0));
if (lean_obj_tag(v___x_2413_) == 0)
{
lean_object* v_a_2414_; lean_object* v___x_2415_; 
v_a_2414_ = lean_ctor_get(v___x_2413_, 0);
lean_inc(v_a_2414_);
v___x_2415_ = lean_box(0);
if (lean_obj_tag(v_a_2414_) == 0)
{
uint8_t v_done_2416_; 
v_done_2416_ = lean_ctor_get_uint8(v_a_2414_, 0);
if (v_done_2416_ == 0)
{
uint8_t v_contextDependent_2417_; lean_object* v___x_2418_; 
lean_dec_ref_known(v___x_2413_, 1);
v_contextDependent_2417_ = lean_ctor_get_uint8(v_a_2414_, 1);
lean_dec_ref_known(v_a_2414_, 0);
v___x_2418_ = lean_apply_12(v___f_2401_, v___x_2415_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_, lean_box(0));
if (lean_obj_tag(v___x_2418_) == 0)
{
lean_object* v_a_2419_; uint8_t v___y_2421_; 
v_a_2419_ = lean_ctor_get(v___x_2418_, 0);
lean_inc(v_a_2419_);
if (v_contextDependent_2417_ == 0)
{
lean_dec(v_a_2419_);
return v___x_2418_;
}
else
{
if (lean_obj_tag(v_a_2419_) == 0)
{
uint8_t v_contextDependent_2431_; 
v_contextDependent_2431_ = lean_ctor_get_uint8(v_a_2419_, 1);
v___y_2421_ = v_contextDependent_2431_;
goto v___jp_2420_;
}
else
{
uint8_t v_contextDependent_2432_; 
v_contextDependent_2432_ = lean_ctor_get_uint8(v_a_2419_, sizeof(void*)*2 + 1);
v___y_2421_ = v_contextDependent_2432_;
goto v___jp_2420_;
}
}
v___jp_2420_:
{
if (v___y_2421_ == 0)
{
lean_object* v___x_2423_; uint8_t v_isShared_2424_; uint8_t v_isSharedCheck_2429_; 
v_isSharedCheck_2429_ = !lean_is_exclusive(v___x_2418_);
if (v_isSharedCheck_2429_ == 0)
{
lean_object* v_unused_2430_; 
v_unused_2430_ = lean_ctor_get(v___x_2418_, 0);
lean_dec(v_unused_2430_);
v___x_2423_ = v___x_2418_;
v_isShared_2424_ = v_isSharedCheck_2429_;
goto v_resetjp_2422_;
}
else
{
lean_dec(v___x_2418_);
v___x_2423_ = lean_box(0);
v_isShared_2424_ = v_isSharedCheck_2429_;
goto v_resetjp_2422_;
}
v_resetjp_2422_:
{
lean_object* v___x_2425_; lean_object* v___x_2427_; 
v___x_2425_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_2419_);
if (v_isShared_2424_ == 0)
{
lean_ctor_set(v___x_2423_, 0, v___x_2425_);
v___x_2427_ = v___x_2423_;
goto v_reusejp_2426_;
}
else
{
lean_object* v_reuseFailAlloc_2428_; 
v_reuseFailAlloc_2428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2428_, 0, v___x_2425_);
v___x_2427_ = v_reuseFailAlloc_2428_;
goto v_reusejp_2426_;
}
v_reusejp_2426_:
{
return v___x_2427_;
}
}
}
else
{
lean_dec(v_a_2419_);
return v___x_2418_;
}
}
}
else
{
return v___x_2418_;
}
}
else
{
lean_dec_ref_known(v_a_2414_, 0);
lean_dec(v___y_2411_);
lean_dec_ref(v___y_2410_);
lean_dec(v___y_2409_);
lean_dec_ref(v___y_2408_);
lean_dec(v___y_2407_);
lean_dec_ref(v___y_2406_);
lean_dec(v___y_2405_);
lean_dec_ref(v___y_2404_);
lean_dec(v___y_2403_);
lean_dec_ref(v___y_2402_);
lean_dec_ref(v___f_2401_);
return v___x_2413_;
}
}
else
{
uint8_t v_done_2433_; 
v_done_2433_ = lean_ctor_get_uint8(v_a_2414_, sizeof(void*)*2);
if (v_done_2433_ == 0)
{
lean_object* v_e_x27_2434_; lean_object* v_proof_2435_; uint8_t v_contextDependent_2436_; lean_object* v___x_2438_; uint8_t v_isShared_2439_; uint8_t v_isSharedCheck_2486_; 
lean_dec_ref_known(v___x_2413_, 1);
v_e_x27_2434_ = lean_ctor_get(v_a_2414_, 0);
v_proof_2435_ = lean_ctor_get(v_a_2414_, 1);
v_contextDependent_2436_ = lean_ctor_get_uint8(v_a_2414_, sizeof(void*)*2 + 1);
v_isSharedCheck_2486_ = !lean_is_exclusive(v_a_2414_);
if (v_isSharedCheck_2486_ == 0)
{
v___x_2438_ = v_a_2414_;
v_isShared_2439_ = v_isSharedCheck_2486_;
goto v_resetjp_2437_;
}
else
{
lean_inc(v_proof_2435_);
lean_inc(v_e_x27_2434_);
lean_dec(v_a_2414_);
v___x_2438_ = lean_box(0);
v_isShared_2439_ = v_isSharedCheck_2486_;
goto v_resetjp_2437_;
}
v_resetjp_2437_:
{
lean_object* v___x_2440_; 
lean_inc(v___y_2411_);
lean_inc_ref(v___y_2410_);
lean_inc(v___y_2409_);
lean_inc_ref(v___y_2408_);
lean_inc(v___y_2407_);
lean_inc_ref(v_e_x27_2434_);
v___x_2440_ = lean_apply_12(v___f_2401_, v___x_2415_, v_e_x27_2434_, v___y_2403_, v___y_2404_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_, lean_box(0));
if (lean_obj_tag(v___x_2440_) == 0)
{
lean_object* v_a_2441_; lean_object* v___x_2443_; uint8_t v_isShared_2444_; uint8_t v_isSharedCheck_2485_; 
v_a_2441_ = lean_ctor_get(v___x_2440_, 0);
v_isSharedCheck_2485_ = !lean_is_exclusive(v___x_2440_);
if (v_isSharedCheck_2485_ == 0)
{
v___x_2443_ = v___x_2440_;
v_isShared_2444_ = v_isSharedCheck_2485_;
goto v_resetjp_2442_;
}
else
{
lean_inc(v_a_2441_);
lean_dec(v___x_2440_);
v___x_2443_ = lean_box(0);
v_isShared_2444_ = v_isSharedCheck_2485_;
goto v_resetjp_2442_;
}
v_resetjp_2442_:
{
if (lean_obj_tag(v_a_2441_) == 0)
{
uint8_t v_done_2445_; uint8_t v_contextDependent_2446_; uint8_t v___y_2448_; 
lean_dec(v___y_2411_);
lean_dec_ref(v___y_2410_);
lean_dec(v___y_2409_);
lean_dec_ref(v___y_2408_);
lean_dec(v___y_2407_);
lean_dec_ref(v___y_2402_);
v_done_2445_ = lean_ctor_get_uint8(v_a_2441_, 0);
v_contextDependent_2446_ = lean_ctor_get_uint8(v_a_2441_, 1);
lean_dec_ref_known(v_a_2441_, 0);
if (v_contextDependent_2436_ == 0)
{
v___y_2448_ = v_contextDependent_2446_;
goto v___jp_2447_;
}
else
{
v___y_2448_ = v_contextDependent_2436_;
goto v___jp_2447_;
}
v___jp_2447_:
{
lean_object* v___x_2450_; 
if (v_isShared_2439_ == 0)
{
v___x_2450_ = v___x_2438_;
goto v_reusejp_2449_;
}
else
{
lean_object* v_reuseFailAlloc_2454_; 
v_reuseFailAlloc_2454_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2454_, 0, v_e_x27_2434_);
lean_ctor_set(v_reuseFailAlloc_2454_, 1, v_proof_2435_);
v___x_2450_ = v_reuseFailAlloc_2454_;
goto v_reusejp_2449_;
}
v_reusejp_2449_:
{
lean_object* v___x_2452_; 
lean_ctor_set_uint8(v___x_2450_, sizeof(void*)*2, v_done_2445_);
lean_ctor_set_uint8(v___x_2450_, sizeof(void*)*2 + 1, v___y_2448_);
if (v_isShared_2444_ == 0)
{
lean_ctor_set(v___x_2443_, 0, v___x_2450_);
v___x_2452_ = v___x_2443_;
goto v_reusejp_2451_;
}
else
{
lean_object* v_reuseFailAlloc_2453_; 
v_reuseFailAlloc_2453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2453_, 0, v___x_2450_);
v___x_2452_ = v_reuseFailAlloc_2453_;
goto v_reusejp_2451_;
}
v_reusejp_2451_:
{
return v___x_2452_;
}
}
}
}
else
{
lean_object* v_e_x27_2455_; lean_object* v_proof_2456_; uint8_t v_done_2457_; uint8_t v_contextDependent_2458_; lean_object* v___x_2460_; uint8_t v_isShared_2461_; uint8_t v_isSharedCheck_2484_; 
lean_del_object(v___x_2443_);
lean_del_object(v___x_2438_);
v_e_x27_2455_ = lean_ctor_get(v_a_2441_, 0);
v_proof_2456_ = lean_ctor_get(v_a_2441_, 1);
v_done_2457_ = lean_ctor_get_uint8(v_a_2441_, sizeof(void*)*2);
v_contextDependent_2458_ = lean_ctor_get_uint8(v_a_2441_, sizeof(void*)*2 + 1);
v_isSharedCheck_2484_ = !lean_is_exclusive(v_a_2441_);
if (v_isSharedCheck_2484_ == 0)
{
v___x_2460_ = v_a_2441_;
v_isShared_2461_ = v_isSharedCheck_2484_;
goto v_resetjp_2459_;
}
else
{
lean_inc(v_proof_2456_);
lean_inc(v_e_x27_2455_);
lean_dec(v_a_2441_);
v___x_2460_ = lean_box(0);
v_isShared_2461_ = v_isSharedCheck_2484_;
goto v_resetjp_2459_;
}
v_resetjp_2459_:
{
lean_object* v___x_2462_; 
lean_inc_ref(v_e_x27_2455_);
v___x_2462_ = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(v___y_2402_, v_e_x27_2434_, v_proof_2435_, v_e_x27_2455_, v_proof_2456_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_);
lean_dec(v___y_2411_);
lean_dec_ref(v___y_2410_);
lean_dec(v___y_2409_);
lean_dec_ref(v___y_2408_);
lean_dec(v___y_2407_);
if (lean_obj_tag(v___x_2462_) == 0)
{
lean_object* v_a_2463_; lean_object* v___x_2465_; uint8_t v_isShared_2466_; uint8_t v_isSharedCheck_2475_; 
v_a_2463_ = lean_ctor_get(v___x_2462_, 0);
v_isSharedCheck_2475_ = !lean_is_exclusive(v___x_2462_);
if (v_isSharedCheck_2475_ == 0)
{
v___x_2465_ = v___x_2462_;
v_isShared_2466_ = v_isSharedCheck_2475_;
goto v_resetjp_2464_;
}
else
{
lean_inc(v_a_2463_);
lean_dec(v___x_2462_);
v___x_2465_ = lean_box(0);
v_isShared_2466_ = v_isSharedCheck_2475_;
goto v_resetjp_2464_;
}
v_resetjp_2464_:
{
uint8_t v___y_2468_; 
if (v_contextDependent_2436_ == 0)
{
v___y_2468_ = v_contextDependent_2458_;
goto v___jp_2467_;
}
else
{
v___y_2468_ = v_contextDependent_2436_;
goto v___jp_2467_;
}
v___jp_2467_:
{
lean_object* v___x_2470_; 
if (v_isShared_2461_ == 0)
{
lean_ctor_set(v___x_2460_, 1, v_a_2463_);
v___x_2470_ = v___x_2460_;
goto v_reusejp_2469_;
}
else
{
lean_object* v_reuseFailAlloc_2474_; 
v_reuseFailAlloc_2474_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2474_, 0, v_e_x27_2455_);
lean_ctor_set(v_reuseFailAlloc_2474_, 1, v_a_2463_);
lean_ctor_set_uint8(v_reuseFailAlloc_2474_, sizeof(void*)*2, v_done_2457_);
v___x_2470_ = v_reuseFailAlloc_2474_;
goto v_reusejp_2469_;
}
v_reusejp_2469_:
{
lean_object* v___x_2472_; 
lean_ctor_set_uint8(v___x_2470_, sizeof(void*)*2 + 1, v___y_2468_);
if (v_isShared_2466_ == 0)
{
lean_ctor_set(v___x_2465_, 0, v___x_2470_);
v___x_2472_ = v___x_2465_;
goto v_reusejp_2471_;
}
else
{
lean_object* v_reuseFailAlloc_2473_; 
v_reuseFailAlloc_2473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2473_, 0, v___x_2470_);
v___x_2472_ = v_reuseFailAlloc_2473_;
goto v_reusejp_2471_;
}
v_reusejp_2471_:
{
return v___x_2472_;
}
}
}
}
}
else
{
lean_object* v_a_2476_; lean_object* v___x_2478_; uint8_t v_isShared_2479_; uint8_t v_isSharedCheck_2483_; 
lean_del_object(v___x_2460_);
lean_dec_ref(v_e_x27_2455_);
v_a_2476_ = lean_ctor_get(v___x_2462_, 0);
v_isSharedCheck_2483_ = !lean_is_exclusive(v___x_2462_);
if (v_isSharedCheck_2483_ == 0)
{
v___x_2478_ = v___x_2462_;
v_isShared_2479_ = v_isSharedCheck_2483_;
goto v_resetjp_2477_;
}
else
{
lean_inc(v_a_2476_);
lean_dec(v___x_2462_);
v___x_2478_ = lean_box(0);
v_isShared_2479_ = v_isSharedCheck_2483_;
goto v_resetjp_2477_;
}
v_resetjp_2477_:
{
lean_object* v___x_2481_; 
if (v_isShared_2479_ == 0)
{
v___x_2481_ = v___x_2478_;
goto v_reusejp_2480_;
}
else
{
lean_object* v_reuseFailAlloc_2482_; 
v_reuseFailAlloc_2482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2482_, 0, v_a_2476_);
v___x_2481_ = v_reuseFailAlloc_2482_;
goto v_reusejp_2480_;
}
v_reusejp_2480_:
{
return v___x_2481_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_2438_);
lean_dec_ref(v_proof_2435_);
lean_dec_ref(v_e_x27_2434_);
lean_dec(v___y_2411_);
lean_dec_ref(v___y_2410_);
lean_dec(v___y_2409_);
lean_dec_ref(v___y_2408_);
lean_dec(v___y_2407_);
lean_dec_ref(v___y_2402_);
return v___x_2440_;
}
}
}
else
{
lean_dec_ref_known(v_a_2414_, 2);
lean_dec(v___y_2411_);
lean_dec_ref(v___y_2410_);
lean_dec(v___y_2409_);
lean_dec_ref(v___y_2408_);
lean_dec(v___y_2407_);
lean_dec_ref(v___y_2406_);
lean_dec(v___y_2405_);
lean_dec_ref(v___y_2404_);
lean_dec(v___y_2403_);
lean_dec_ref(v___y_2402_);
lean_dec_ref(v___f_2401_);
return v___x_2413_;
}
}
}
else
{
lean_dec(v___y_2411_);
lean_dec_ref(v___y_2410_);
lean_dec(v___y_2409_);
lean_dec_ref(v___y_2408_);
lean_dec(v___y_2407_);
lean_dec_ref(v___y_2406_);
lean_dec(v___y_2405_);
lean_dec_ref(v___y_2404_);
lean_dec(v___y_2403_);
lean_dec_ref(v___y_2402_);
lean_dec_ref(v___f_2401_);
return v___x_2413_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___lam__1___boxed(lean_object* v_post_2487_, lean_object* v___f_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_){
_start:
{
lean_object* v_res_2500_; 
v_res_2500_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___lam__1(v_post_2487_, v___f_2488_, v___y_2489_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_);
return v_res_2500_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems_spec__0___redArg(lean_object* v_as_2501_, size_t v_sz_2502_, size_t v_i_2503_, lean_object* v_b_2504_){
_start:
{
uint8_t v___x_2506_; 
v___x_2506_ = lean_usize_dec_lt(v_i_2503_, v_sz_2502_);
if (v___x_2506_ == 0)
{
lean_object* v___x_2507_; 
v___x_2507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2507_, 0, v_b_2504_);
return v___x_2507_;
}
else
{
lean_object* v_a_2508_; lean_object* v___x_2509_; size_t v___x_2510_; size_t v___x_2511_; 
v_a_2508_ = lean_array_uget_borrowed(v_as_2501_, v_i_2503_);
lean_inc(v_a_2508_);
v___x_2509_ = l_Lean_Meta_Sym_Simp_Theorems_insert(v_b_2504_, v_a_2508_);
v___x_2510_ = ((size_t)1ULL);
v___x_2511_ = lean_usize_add(v_i_2503_, v___x_2510_);
v_i_2503_ = v___x_2511_;
v_b_2504_ = v___x_2509_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems_spec__0___redArg___boxed(lean_object* v_as_2513_, lean_object* v_sz_2514_, lean_object* v_i_2515_, lean_object* v_b_2516_, lean_object* v___y_2517_){
_start:
{
size_t v_sz_boxed_2518_; size_t v_i_boxed_2519_; lean_object* v_res_2520_; 
v_sz_boxed_2518_ = lean_unbox_usize(v_sz_2514_);
lean_dec(v_sz_2514_);
v_i_boxed_2519_ = lean_unbox_usize(v_i_2515_);
lean_dec(v_i_2515_);
v_res_2520_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems_spec__0___redArg(v_as_2513_, v_sz_boxed_2518_, v_i_boxed_2519_, v_b_2516_);
lean_dec_ref(v_as_2513_);
return v_res_2520_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___closed__0(void){
_start:
{
lean_object* v___x_2521_; 
v___x_2521_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2521_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___closed__1(void){
_start:
{
lean_object* v___x_2522_; lean_object* v_thms_2523_; 
v___x_2522_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___closed__0, &l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___closed__0_once, _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___closed__0);
v_thms_2523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_thms_2523_, 0, v___x_2522_);
return v_thms_2523_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems(lean_object* v_post_2524_, lean_object* v_extraThms_2525_, lean_object* v_a_2526_, lean_object* v_a_2527_, lean_object* v_a_2528_, lean_object* v_a_2529_, lean_object* v_a_2530_, lean_object* v_a_2531_, lean_object* v_a_2532_, lean_object* v_a_2533_){
_start:
{
lean_object* v___x_2535_; lean_object* v___x_2536_; uint8_t v___x_2537_; 
v___x_2535_ = lean_array_get_size(v_extraThms_2525_);
v___x_2536_ = lean_unsigned_to_nat(0u);
v___x_2537_ = lean_nat_dec_eq(v___x_2535_, v___x_2536_);
if (v___x_2537_ == 0)
{
lean_object* v_thms_2538_; size_t v_sz_2539_; size_t v___x_2540_; lean_object* v___x_2541_; 
v_thms_2538_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___closed__1, &l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___closed__1);
v_sz_2539_ = lean_array_size(v_extraThms_2525_);
v___x_2540_ = ((size_t)0ULL);
v___x_2541_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems_spec__0___redArg(v_extraThms_2525_, v_sz_2539_, v___x_2540_, v_thms_2538_);
if (lean_obj_tag(v___x_2541_) == 0)
{
lean_object* v_a_2542_; lean_object* v___x_2544_; uint8_t v_isShared_2545_; uint8_t v_isSharedCheck_2551_; 
v_a_2542_ = lean_ctor_get(v___x_2541_, 0);
v_isSharedCheck_2551_ = !lean_is_exclusive(v___x_2541_);
if (v_isSharedCheck_2551_ == 0)
{
v___x_2544_ = v___x_2541_;
v_isShared_2545_ = v_isSharedCheck_2551_;
goto v_resetjp_2543_;
}
else
{
lean_inc(v_a_2542_);
lean_dec(v___x_2541_);
v___x_2544_ = lean_box(0);
v_isShared_2545_ = v_isSharedCheck_2551_;
goto v_resetjp_2543_;
}
v_resetjp_2543_:
{
lean_object* v___f_2546_; lean_object* v___f_2547_; lean_object* v___x_2549_; 
v___f_2546_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___lam__0___boxed), 13, 1);
lean_closure_set(v___f_2546_, 0, v_a_2542_);
v___f_2547_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___lam__1___boxed), 13, 2);
lean_closure_set(v___f_2547_, 0, v_post_2524_);
lean_closure_set(v___f_2547_, 1, v___f_2546_);
if (v_isShared_2545_ == 0)
{
lean_ctor_set(v___x_2544_, 0, v___f_2547_);
v___x_2549_ = v___x_2544_;
goto v_reusejp_2548_;
}
else
{
lean_object* v_reuseFailAlloc_2550_; 
v_reuseFailAlloc_2550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2550_, 0, v___f_2547_);
v___x_2549_ = v_reuseFailAlloc_2550_;
goto v_reusejp_2548_;
}
v_reusejp_2548_:
{
return v___x_2549_;
}
}
}
else
{
lean_object* v_a_2552_; lean_object* v___x_2554_; uint8_t v_isShared_2555_; uint8_t v_isSharedCheck_2559_; 
lean_dec_ref(v_post_2524_);
v_a_2552_ = lean_ctor_get(v___x_2541_, 0);
v_isSharedCheck_2559_ = !lean_is_exclusive(v___x_2541_);
if (v_isSharedCheck_2559_ == 0)
{
v___x_2554_ = v___x_2541_;
v_isShared_2555_ = v_isSharedCheck_2559_;
goto v_resetjp_2553_;
}
else
{
lean_inc(v_a_2552_);
lean_dec(v___x_2541_);
v___x_2554_ = lean_box(0);
v_isShared_2555_ = v_isSharedCheck_2559_;
goto v_resetjp_2553_;
}
v_resetjp_2553_:
{
lean_object* v___x_2557_; 
if (v_isShared_2555_ == 0)
{
v___x_2557_ = v___x_2554_;
goto v_reusejp_2556_;
}
else
{
lean_object* v_reuseFailAlloc_2558_; 
v_reuseFailAlloc_2558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2558_, 0, v_a_2552_);
v___x_2557_ = v_reuseFailAlloc_2558_;
goto v_reusejp_2556_;
}
v_reusejp_2556_:
{
return v___x_2557_;
}
}
}
}
else
{
lean_object* v___x_2560_; 
v___x_2560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2560_, 0, v_post_2524_);
return v___x_2560_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___boxed(lean_object* v_post_2561_, lean_object* v_extraThms_2562_, lean_object* v_a_2563_, lean_object* v_a_2564_, lean_object* v_a_2565_, lean_object* v_a_2566_, lean_object* v_a_2567_, lean_object* v_a_2568_, lean_object* v_a_2569_, lean_object* v_a_2570_, lean_object* v_a_2571_){
_start:
{
lean_object* v_res_2572_; 
v_res_2572_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems(v_post_2561_, v_extraThms_2562_, v_a_2563_, v_a_2564_, v_a_2565_, v_a_2566_, v_a_2567_, v_a_2568_, v_a_2569_, v_a_2570_);
lean_dec(v_a_2570_);
lean_dec_ref(v_a_2569_);
lean_dec(v_a_2568_);
lean_dec_ref(v_a_2567_);
lean_dec(v_a_2566_);
lean_dec_ref(v_a_2565_);
lean_dec(v_a_2564_);
lean_dec_ref(v_a_2563_);
lean_dec_ref(v_extraThms_2562_);
return v_res_2572_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems_spec__0(lean_object* v_as_2573_, size_t v_sz_2574_, size_t v_i_2575_, lean_object* v_b_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_){
_start:
{
lean_object* v___x_2586_; 
v___x_2586_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems_spec__0___redArg(v_as_2573_, v_sz_2574_, v_i_2575_, v_b_2576_);
return v___x_2586_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems_spec__0___boxed(lean_object* v_as_2587_, lean_object* v_sz_2588_, lean_object* v_i_2589_, lean_object* v_b_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_){
_start:
{
size_t v_sz_boxed_2600_; size_t v_i_boxed_2601_; lean_object* v_res_2602_; 
v_sz_boxed_2600_ = lean_unbox_usize(v_sz_2588_);
lean_dec(v_sz_2588_);
v_i_boxed_2601_ = lean_unbox_usize(v_i_2589_);
lean_dec(v_i_2589_);
v_res_2602_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems_spec__0(v_as_2587_, v_sz_boxed_2600_, v_i_boxed_2601_, v_b_2590_, v___y_2591_, v___y_2592_, v___y_2593_, v___y_2594_, v___y_2595_, v___y_2596_, v___y_2597_, v___y_2598_);
lean_dec(v___y_2598_);
lean_dec_ref(v___y_2597_);
lean_dec(v___y_2596_);
lean_dec_ref(v___y_2595_);
lean_dec(v___y_2594_);
lean_dec_ref(v___y_2593_);
lean_dec(v___y_2592_);
lean_dec_ref(v___y_2591_);
lean_dec_ref(v_as_2587_);
return v_res_2602_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkSimpDefaultMethods___lam__1(lean_object* v___x_2603_, lean_object* v___f_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_){
_start:
{
lean_object* v___x_2616_; 
lean_inc_ref(v___y_2605_);
v___x_2616_ = l_Lean_Meta_Sym_Simp_evalGround___redArg(v___x_2603_, v___y_2605_, v___y_2609_, v___y_2610_, v___y_2611_, v___y_2612_, v___y_2613_, v___y_2614_);
if (lean_obj_tag(v___x_2616_) == 0)
{
lean_object* v_a_2617_; lean_object* v___x_2618_; 
v_a_2617_ = lean_ctor_get(v___x_2616_, 0);
lean_inc(v_a_2617_);
v___x_2618_ = lean_box(0);
if (lean_obj_tag(v_a_2617_) == 0)
{
uint8_t v_done_2619_; 
v_done_2619_ = lean_ctor_get_uint8(v_a_2617_, 0);
if (v_done_2619_ == 0)
{
uint8_t v_contextDependent_2620_; lean_object* v___x_2621_; 
lean_dec_ref_known(v___x_2616_, 1);
v_contextDependent_2620_ = lean_ctor_get_uint8(v_a_2617_, 1);
lean_dec_ref_known(v_a_2617_, 0);
v___x_2621_ = lean_apply_12(v___f_2604_, v___x_2618_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_, v___y_2612_, v___y_2613_, v___y_2614_, lean_box(0));
if (lean_obj_tag(v___x_2621_) == 0)
{
lean_object* v_a_2622_; uint8_t v___y_2624_; 
v_a_2622_ = lean_ctor_get(v___x_2621_, 0);
lean_inc(v_a_2622_);
if (v_contextDependent_2620_ == 0)
{
lean_dec(v_a_2622_);
return v___x_2621_;
}
else
{
if (lean_obj_tag(v_a_2622_) == 0)
{
uint8_t v_contextDependent_2634_; 
v_contextDependent_2634_ = lean_ctor_get_uint8(v_a_2622_, 1);
v___y_2624_ = v_contextDependent_2634_;
goto v___jp_2623_;
}
else
{
uint8_t v_contextDependent_2635_; 
v_contextDependent_2635_ = lean_ctor_get_uint8(v_a_2622_, sizeof(void*)*2 + 1);
v___y_2624_ = v_contextDependent_2635_;
goto v___jp_2623_;
}
}
v___jp_2623_:
{
if (v___y_2624_ == 0)
{
lean_object* v___x_2626_; uint8_t v_isShared_2627_; uint8_t v_isSharedCheck_2632_; 
v_isSharedCheck_2632_ = !lean_is_exclusive(v___x_2621_);
if (v_isSharedCheck_2632_ == 0)
{
lean_object* v_unused_2633_; 
v_unused_2633_ = lean_ctor_get(v___x_2621_, 0);
lean_dec(v_unused_2633_);
v___x_2626_ = v___x_2621_;
v_isShared_2627_ = v_isSharedCheck_2632_;
goto v_resetjp_2625_;
}
else
{
lean_dec(v___x_2621_);
v___x_2626_ = lean_box(0);
v_isShared_2627_ = v_isSharedCheck_2632_;
goto v_resetjp_2625_;
}
v_resetjp_2625_:
{
lean_object* v___x_2628_; lean_object* v___x_2630_; 
v___x_2628_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_2622_);
if (v_isShared_2627_ == 0)
{
lean_ctor_set(v___x_2626_, 0, v___x_2628_);
v___x_2630_ = v___x_2626_;
goto v_reusejp_2629_;
}
else
{
lean_object* v_reuseFailAlloc_2631_; 
v_reuseFailAlloc_2631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2631_, 0, v___x_2628_);
v___x_2630_ = v_reuseFailAlloc_2631_;
goto v_reusejp_2629_;
}
v_reusejp_2629_:
{
return v___x_2630_;
}
}
}
else
{
lean_dec(v_a_2622_);
return v___x_2621_;
}
}
}
else
{
return v___x_2621_;
}
}
else
{
lean_dec_ref_known(v_a_2617_, 0);
lean_dec(v___y_2614_);
lean_dec_ref(v___y_2613_);
lean_dec(v___y_2612_);
lean_dec_ref(v___y_2611_);
lean_dec(v___y_2610_);
lean_dec_ref(v___y_2609_);
lean_dec(v___y_2608_);
lean_dec_ref(v___y_2607_);
lean_dec(v___y_2606_);
lean_dec_ref(v___y_2605_);
lean_dec_ref(v___f_2604_);
return v___x_2616_;
}
}
else
{
uint8_t v_done_2636_; 
v_done_2636_ = lean_ctor_get_uint8(v_a_2617_, sizeof(void*)*2);
if (v_done_2636_ == 0)
{
lean_object* v_e_x27_2637_; lean_object* v_proof_2638_; uint8_t v_contextDependent_2639_; lean_object* v___x_2641_; uint8_t v_isShared_2642_; uint8_t v_isSharedCheck_2689_; 
lean_dec_ref_known(v___x_2616_, 1);
v_e_x27_2637_ = lean_ctor_get(v_a_2617_, 0);
v_proof_2638_ = lean_ctor_get(v_a_2617_, 1);
v_contextDependent_2639_ = lean_ctor_get_uint8(v_a_2617_, sizeof(void*)*2 + 1);
v_isSharedCheck_2689_ = !lean_is_exclusive(v_a_2617_);
if (v_isSharedCheck_2689_ == 0)
{
v___x_2641_ = v_a_2617_;
v_isShared_2642_ = v_isSharedCheck_2689_;
goto v_resetjp_2640_;
}
else
{
lean_inc(v_proof_2638_);
lean_inc(v_e_x27_2637_);
lean_dec(v_a_2617_);
v___x_2641_ = lean_box(0);
v_isShared_2642_ = v_isSharedCheck_2689_;
goto v_resetjp_2640_;
}
v_resetjp_2640_:
{
lean_object* v___x_2643_; 
lean_inc(v___y_2614_);
lean_inc_ref(v___y_2613_);
lean_inc(v___y_2612_);
lean_inc_ref(v___y_2611_);
lean_inc(v___y_2610_);
lean_inc_ref(v_e_x27_2637_);
v___x_2643_ = lean_apply_12(v___f_2604_, v___x_2618_, v_e_x27_2637_, v___y_2606_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_, v___y_2612_, v___y_2613_, v___y_2614_, lean_box(0));
if (lean_obj_tag(v___x_2643_) == 0)
{
lean_object* v_a_2644_; lean_object* v___x_2646_; uint8_t v_isShared_2647_; uint8_t v_isSharedCheck_2688_; 
v_a_2644_ = lean_ctor_get(v___x_2643_, 0);
v_isSharedCheck_2688_ = !lean_is_exclusive(v___x_2643_);
if (v_isSharedCheck_2688_ == 0)
{
v___x_2646_ = v___x_2643_;
v_isShared_2647_ = v_isSharedCheck_2688_;
goto v_resetjp_2645_;
}
else
{
lean_inc(v_a_2644_);
lean_dec(v___x_2643_);
v___x_2646_ = lean_box(0);
v_isShared_2647_ = v_isSharedCheck_2688_;
goto v_resetjp_2645_;
}
v_resetjp_2645_:
{
if (lean_obj_tag(v_a_2644_) == 0)
{
uint8_t v_done_2648_; uint8_t v_contextDependent_2649_; uint8_t v___y_2651_; 
lean_dec(v___y_2614_);
lean_dec_ref(v___y_2613_);
lean_dec(v___y_2612_);
lean_dec_ref(v___y_2611_);
lean_dec(v___y_2610_);
lean_dec_ref(v___y_2605_);
v_done_2648_ = lean_ctor_get_uint8(v_a_2644_, 0);
v_contextDependent_2649_ = lean_ctor_get_uint8(v_a_2644_, 1);
lean_dec_ref_known(v_a_2644_, 0);
if (v_contextDependent_2639_ == 0)
{
v___y_2651_ = v_contextDependent_2649_;
goto v___jp_2650_;
}
else
{
v___y_2651_ = v_contextDependent_2639_;
goto v___jp_2650_;
}
v___jp_2650_:
{
lean_object* v___x_2653_; 
if (v_isShared_2642_ == 0)
{
v___x_2653_ = v___x_2641_;
goto v_reusejp_2652_;
}
else
{
lean_object* v_reuseFailAlloc_2657_; 
v_reuseFailAlloc_2657_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2657_, 0, v_e_x27_2637_);
lean_ctor_set(v_reuseFailAlloc_2657_, 1, v_proof_2638_);
v___x_2653_ = v_reuseFailAlloc_2657_;
goto v_reusejp_2652_;
}
v_reusejp_2652_:
{
lean_object* v___x_2655_; 
lean_ctor_set_uint8(v___x_2653_, sizeof(void*)*2, v_done_2648_);
lean_ctor_set_uint8(v___x_2653_, sizeof(void*)*2 + 1, v___y_2651_);
if (v_isShared_2647_ == 0)
{
lean_ctor_set(v___x_2646_, 0, v___x_2653_);
v___x_2655_ = v___x_2646_;
goto v_reusejp_2654_;
}
else
{
lean_object* v_reuseFailAlloc_2656_; 
v_reuseFailAlloc_2656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2656_, 0, v___x_2653_);
v___x_2655_ = v_reuseFailAlloc_2656_;
goto v_reusejp_2654_;
}
v_reusejp_2654_:
{
return v___x_2655_;
}
}
}
}
else
{
lean_object* v_e_x27_2658_; lean_object* v_proof_2659_; uint8_t v_done_2660_; uint8_t v_contextDependent_2661_; lean_object* v___x_2663_; uint8_t v_isShared_2664_; uint8_t v_isSharedCheck_2687_; 
lean_del_object(v___x_2646_);
lean_del_object(v___x_2641_);
v_e_x27_2658_ = lean_ctor_get(v_a_2644_, 0);
v_proof_2659_ = lean_ctor_get(v_a_2644_, 1);
v_done_2660_ = lean_ctor_get_uint8(v_a_2644_, sizeof(void*)*2);
v_contextDependent_2661_ = lean_ctor_get_uint8(v_a_2644_, sizeof(void*)*2 + 1);
v_isSharedCheck_2687_ = !lean_is_exclusive(v_a_2644_);
if (v_isSharedCheck_2687_ == 0)
{
v___x_2663_ = v_a_2644_;
v_isShared_2664_ = v_isSharedCheck_2687_;
goto v_resetjp_2662_;
}
else
{
lean_inc(v_proof_2659_);
lean_inc(v_e_x27_2658_);
lean_dec(v_a_2644_);
v___x_2663_ = lean_box(0);
v_isShared_2664_ = v_isSharedCheck_2687_;
goto v_resetjp_2662_;
}
v_resetjp_2662_:
{
lean_object* v___x_2665_; 
lean_inc_ref(v_e_x27_2658_);
v___x_2665_ = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(v___y_2605_, v_e_x27_2637_, v_proof_2638_, v_e_x27_2658_, v_proof_2659_, v___y_2610_, v___y_2611_, v___y_2612_, v___y_2613_, v___y_2614_);
lean_dec(v___y_2614_);
lean_dec_ref(v___y_2613_);
lean_dec(v___y_2612_);
lean_dec_ref(v___y_2611_);
lean_dec(v___y_2610_);
if (lean_obj_tag(v___x_2665_) == 0)
{
lean_object* v_a_2666_; lean_object* v___x_2668_; uint8_t v_isShared_2669_; uint8_t v_isSharedCheck_2678_; 
v_a_2666_ = lean_ctor_get(v___x_2665_, 0);
v_isSharedCheck_2678_ = !lean_is_exclusive(v___x_2665_);
if (v_isSharedCheck_2678_ == 0)
{
v___x_2668_ = v___x_2665_;
v_isShared_2669_ = v_isSharedCheck_2678_;
goto v_resetjp_2667_;
}
else
{
lean_inc(v_a_2666_);
lean_dec(v___x_2665_);
v___x_2668_ = lean_box(0);
v_isShared_2669_ = v_isSharedCheck_2678_;
goto v_resetjp_2667_;
}
v_resetjp_2667_:
{
uint8_t v___y_2671_; 
if (v_contextDependent_2639_ == 0)
{
v___y_2671_ = v_contextDependent_2661_;
goto v___jp_2670_;
}
else
{
v___y_2671_ = v_contextDependent_2639_;
goto v___jp_2670_;
}
v___jp_2670_:
{
lean_object* v___x_2673_; 
if (v_isShared_2664_ == 0)
{
lean_ctor_set(v___x_2663_, 1, v_a_2666_);
v___x_2673_ = v___x_2663_;
goto v_reusejp_2672_;
}
else
{
lean_object* v_reuseFailAlloc_2677_; 
v_reuseFailAlloc_2677_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2677_, 0, v_e_x27_2658_);
lean_ctor_set(v_reuseFailAlloc_2677_, 1, v_a_2666_);
lean_ctor_set_uint8(v_reuseFailAlloc_2677_, sizeof(void*)*2, v_done_2660_);
v___x_2673_ = v_reuseFailAlloc_2677_;
goto v_reusejp_2672_;
}
v_reusejp_2672_:
{
lean_object* v___x_2675_; 
lean_ctor_set_uint8(v___x_2673_, sizeof(void*)*2 + 1, v___y_2671_);
if (v_isShared_2669_ == 0)
{
lean_ctor_set(v___x_2668_, 0, v___x_2673_);
v___x_2675_ = v___x_2668_;
goto v_reusejp_2674_;
}
else
{
lean_object* v_reuseFailAlloc_2676_; 
v_reuseFailAlloc_2676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2676_, 0, v___x_2673_);
v___x_2675_ = v_reuseFailAlloc_2676_;
goto v_reusejp_2674_;
}
v_reusejp_2674_:
{
return v___x_2675_;
}
}
}
}
}
else
{
lean_object* v_a_2679_; lean_object* v___x_2681_; uint8_t v_isShared_2682_; uint8_t v_isSharedCheck_2686_; 
lean_del_object(v___x_2663_);
lean_dec_ref(v_e_x27_2658_);
v_a_2679_ = lean_ctor_get(v___x_2665_, 0);
v_isSharedCheck_2686_ = !lean_is_exclusive(v___x_2665_);
if (v_isSharedCheck_2686_ == 0)
{
v___x_2681_ = v___x_2665_;
v_isShared_2682_ = v_isSharedCheck_2686_;
goto v_resetjp_2680_;
}
else
{
lean_inc(v_a_2679_);
lean_dec(v___x_2665_);
v___x_2681_ = lean_box(0);
v_isShared_2682_ = v_isSharedCheck_2686_;
goto v_resetjp_2680_;
}
v_resetjp_2680_:
{
lean_object* v___x_2684_; 
if (v_isShared_2682_ == 0)
{
v___x_2684_ = v___x_2681_;
goto v_reusejp_2683_;
}
else
{
lean_object* v_reuseFailAlloc_2685_; 
v_reuseFailAlloc_2685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2685_, 0, v_a_2679_);
v___x_2684_ = v_reuseFailAlloc_2685_;
goto v_reusejp_2683_;
}
v_reusejp_2683_:
{
return v___x_2684_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_2641_);
lean_dec_ref(v_proof_2638_);
lean_dec_ref(v_e_x27_2637_);
lean_dec(v___y_2614_);
lean_dec_ref(v___y_2613_);
lean_dec(v___y_2612_);
lean_dec_ref(v___y_2611_);
lean_dec(v___y_2610_);
lean_dec_ref(v___y_2605_);
return v___x_2643_;
}
}
}
else
{
lean_dec_ref_known(v_a_2617_, 2);
lean_dec(v___y_2614_);
lean_dec_ref(v___y_2613_);
lean_dec(v___y_2612_);
lean_dec_ref(v___y_2611_);
lean_dec(v___y_2610_);
lean_dec_ref(v___y_2609_);
lean_dec(v___y_2608_);
lean_dec_ref(v___y_2607_);
lean_dec(v___y_2606_);
lean_dec_ref(v___y_2605_);
lean_dec_ref(v___f_2604_);
return v___x_2616_;
}
}
}
else
{
lean_dec(v___y_2614_);
lean_dec_ref(v___y_2613_);
lean_dec(v___y_2612_);
lean_dec_ref(v___y_2611_);
lean_dec(v___y_2610_);
lean_dec_ref(v___y_2609_);
lean_dec(v___y_2608_);
lean_dec_ref(v___y_2607_);
lean_dec(v___y_2606_);
lean_dec_ref(v___y_2605_);
lean_dec_ref(v___f_2604_);
return v___x_2616_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkSimpDefaultMethods___lam__1___boxed(lean_object* v___x_2690_, lean_object* v___f_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_){
_start:
{
lean_object* v_res_2703_; 
v_res_2703_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkSimpDefaultMethods___lam__1(v___x_2690_, v___f_2691_, v___y_2692_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_, v___y_2698_, v___y_2699_, v___y_2700_, v___y_2701_);
lean_dec(v___x_2690_);
return v_res_2703_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkSimpDefaultMethods___lam__0(lean_object* v_x_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_){
_start:
{
lean_object* v___x_2717_; lean_object* v___x_2718_; 
v___x_2717_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkSimpDefaultMethods___lam__0___closed__0));
v___x_2718_ = l_Lean_Meta_Sym_Simp_simpArrowTelescope(v___x_2717_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_, v___y_2713_, v___y_2714_, v___y_2715_);
return v___x_2718_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkSimpDefaultMethods___lam__0___boxed(lean_object* v_x_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_){
_start:
{
lean_object* v_res_2731_; 
v_res_2731_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkSimpDefaultMethods___lam__0(v_x_2719_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_);
lean_dec(v___y_2729_);
lean_dec_ref(v___y_2728_);
lean_dec(v___y_2727_);
lean_dec_ref(v___y_2726_);
lean_dec(v___y_2725_);
lean_dec_ref(v___y_2724_);
lean_dec(v___y_2723_);
lean_dec_ref(v___y_2722_);
lean_dec(v___y_2721_);
return v_res_2731_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkSimpDefaultMethods___lam__2(lean_object* v___f_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_){
_start:
{
lean_object* v___x_2744_; 
lean_inc_ref(v___y_2733_);
v___x_2744_ = l_Lean_Meta_Sym_Simp_simpControl(v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_, v___y_2740_, v___y_2741_, v___y_2742_);
if (lean_obj_tag(v___x_2744_) == 0)
{
lean_object* v_a_2745_; lean_object* v___x_2746_; 
v_a_2745_ = lean_ctor_get(v___x_2744_, 0);
lean_inc(v_a_2745_);
v___x_2746_ = lean_box(0);
if (lean_obj_tag(v_a_2745_) == 0)
{
uint8_t v_done_2747_; 
v_done_2747_ = lean_ctor_get_uint8(v_a_2745_, 0);
if (v_done_2747_ == 0)
{
uint8_t v_contextDependent_2748_; lean_object* v___x_2749_; 
lean_dec_ref_known(v___x_2744_, 1);
v_contextDependent_2748_ = lean_ctor_get_uint8(v_a_2745_, 1);
lean_dec_ref_known(v_a_2745_, 0);
v___x_2749_ = lean_apply_12(v___f_2732_, v___x_2746_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_, v___y_2740_, v___y_2741_, v___y_2742_, lean_box(0));
if (lean_obj_tag(v___x_2749_) == 0)
{
lean_object* v_a_2750_; uint8_t v___y_2752_; 
v_a_2750_ = lean_ctor_get(v___x_2749_, 0);
lean_inc(v_a_2750_);
if (v_contextDependent_2748_ == 0)
{
lean_dec(v_a_2750_);
return v___x_2749_;
}
else
{
if (lean_obj_tag(v_a_2750_) == 0)
{
uint8_t v_contextDependent_2762_; 
v_contextDependent_2762_ = lean_ctor_get_uint8(v_a_2750_, 1);
v___y_2752_ = v_contextDependent_2762_;
goto v___jp_2751_;
}
else
{
uint8_t v_contextDependent_2763_; 
v_contextDependent_2763_ = lean_ctor_get_uint8(v_a_2750_, sizeof(void*)*2 + 1);
v___y_2752_ = v_contextDependent_2763_;
goto v___jp_2751_;
}
}
v___jp_2751_:
{
if (v___y_2752_ == 0)
{
lean_object* v___x_2754_; uint8_t v_isShared_2755_; uint8_t v_isSharedCheck_2760_; 
v_isSharedCheck_2760_ = !lean_is_exclusive(v___x_2749_);
if (v_isSharedCheck_2760_ == 0)
{
lean_object* v_unused_2761_; 
v_unused_2761_ = lean_ctor_get(v___x_2749_, 0);
lean_dec(v_unused_2761_);
v___x_2754_ = v___x_2749_;
v_isShared_2755_ = v_isSharedCheck_2760_;
goto v_resetjp_2753_;
}
else
{
lean_dec(v___x_2749_);
v___x_2754_ = lean_box(0);
v_isShared_2755_ = v_isSharedCheck_2760_;
goto v_resetjp_2753_;
}
v_resetjp_2753_:
{
lean_object* v___x_2756_; lean_object* v___x_2758_; 
v___x_2756_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_2750_);
if (v_isShared_2755_ == 0)
{
lean_ctor_set(v___x_2754_, 0, v___x_2756_);
v___x_2758_ = v___x_2754_;
goto v_reusejp_2757_;
}
else
{
lean_object* v_reuseFailAlloc_2759_; 
v_reuseFailAlloc_2759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2759_, 0, v___x_2756_);
v___x_2758_ = v_reuseFailAlloc_2759_;
goto v_reusejp_2757_;
}
v_reusejp_2757_:
{
return v___x_2758_;
}
}
}
else
{
lean_dec(v_a_2750_);
return v___x_2749_;
}
}
}
else
{
return v___x_2749_;
}
}
else
{
lean_dec_ref_known(v_a_2745_, 0);
lean_dec(v___y_2742_);
lean_dec_ref(v___y_2741_);
lean_dec(v___y_2740_);
lean_dec_ref(v___y_2739_);
lean_dec(v___y_2738_);
lean_dec_ref(v___y_2737_);
lean_dec(v___y_2736_);
lean_dec_ref(v___y_2735_);
lean_dec(v___y_2734_);
lean_dec_ref(v___y_2733_);
lean_dec_ref(v___f_2732_);
return v___x_2744_;
}
}
else
{
uint8_t v_done_2764_; 
v_done_2764_ = lean_ctor_get_uint8(v_a_2745_, sizeof(void*)*2);
if (v_done_2764_ == 0)
{
lean_object* v_e_x27_2765_; lean_object* v_proof_2766_; uint8_t v_contextDependent_2767_; lean_object* v___x_2769_; uint8_t v_isShared_2770_; uint8_t v_isSharedCheck_2817_; 
lean_dec_ref_known(v___x_2744_, 1);
v_e_x27_2765_ = lean_ctor_get(v_a_2745_, 0);
v_proof_2766_ = lean_ctor_get(v_a_2745_, 1);
v_contextDependent_2767_ = lean_ctor_get_uint8(v_a_2745_, sizeof(void*)*2 + 1);
v_isSharedCheck_2817_ = !lean_is_exclusive(v_a_2745_);
if (v_isSharedCheck_2817_ == 0)
{
v___x_2769_ = v_a_2745_;
v_isShared_2770_ = v_isSharedCheck_2817_;
goto v_resetjp_2768_;
}
else
{
lean_inc(v_proof_2766_);
lean_inc(v_e_x27_2765_);
lean_dec(v_a_2745_);
v___x_2769_ = lean_box(0);
v_isShared_2770_ = v_isSharedCheck_2817_;
goto v_resetjp_2768_;
}
v_resetjp_2768_:
{
lean_object* v___x_2771_; 
lean_inc(v___y_2742_);
lean_inc_ref(v___y_2741_);
lean_inc(v___y_2740_);
lean_inc_ref(v___y_2739_);
lean_inc(v___y_2738_);
lean_inc_ref(v_e_x27_2765_);
v___x_2771_ = lean_apply_12(v___f_2732_, v___x_2746_, v_e_x27_2765_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_, v___y_2740_, v___y_2741_, v___y_2742_, lean_box(0));
if (lean_obj_tag(v___x_2771_) == 0)
{
lean_object* v_a_2772_; lean_object* v___x_2774_; uint8_t v_isShared_2775_; uint8_t v_isSharedCheck_2816_; 
v_a_2772_ = lean_ctor_get(v___x_2771_, 0);
v_isSharedCheck_2816_ = !lean_is_exclusive(v___x_2771_);
if (v_isSharedCheck_2816_ == 0)
{
v___x_2774_ = v___x_2771_;
v_isShared_2775_ = v_isSharedCheck_2816_;
goto v_resetjp_2773_;
}
else
{
lean_inc(v_a_2772_);
lean_dec(v___x_2771_);
v___x_2774_ = lean_box(0);
v_isShared_2775_ = v_isSharedCheck_2816_;
goto v_resetjp_2773_;
}
v_resetjp_2773_:
{
if (lean_obj_tag(v_a_2772_) == 0)
{
uint8_t v_done_2776_; uint8_t v_contextDependent_2777_; uint8_t v___y_2779_; 
lean_dec(v___y_2742_);
lean_dec_ref(v___y_2741_);
lean_dec(v___y_2740_);
lean_dec_ref(v___y_2739_);
lean_dec(v___y_2738_);
lean_dec_ref(v___y_2733_);
v_done_2776_ = lean_ctor_get_uint8(v_a_2772_, 0);
v_contextDependent_2777_ = lean_ctor_get_uint8(v_a_2772_, 1);
lean_dec_ref_known(v_a_2772_, 0);
if (v_contextDependent_2767_ == 0)
{
v___y_2779_ = v_contextDependent_2777_;
goto v___jp_2778_;
}
else
{
v___y_2779_ = v_contextDependent_2767_;
goto v___jp_2778_;
}
v___jp_2778_:
{
lean_object* v___x_2781_; 
if (v_isShared_2770_ == 0)
{
v___x_2781_ = v___x_2769_;
goto v_reusejp_2780_;
}
else
{
lean_object* v_reuseFailAlloc_2785_; 
v_reuseFailAlloc_2785_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2785_, 0, v_e_x27_2765_);
lean_ctor_set(v_reuseFailAlloc_2785_, 1, v_proof_2766_);
v___x_2781_ = v_reuseFailAlloc_2785_;
goto v_reusejp_2780_;
}
v_reusejp_2780_:
{
lean_object* v___x_2783_; 
lean_ctor_set_uint8(v___x_2781_, sizeof(void*)*2, v_done_2776_);
lean_ctor_set_uint8(v___x_2781_, sizeof(void*)*2 + 1, v___y_2779_);
if (v_isShared_2775_ == 0)
{
lean_ctor_set(v___x_2774_, 0, v___x_2781_);
v___x_2783_ = v___x_2774_;
goto v_reusejp_2782_;
}
else
{
lean_object* v_reuseFailAlloc_2784_; 
v_reuseFailAlloc_2784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2784_, 0, v___x_2781_);
v___x_2783_ = v_reuseFailAlloc_2784_;
goto v_reusejp_2782_;
}
v_reusejp_2782_:
{
return v___x_2783_;
}
}
}
}
else
{
lean_object* v_e_x27_2786_; lean_object* v_proof_2787_; uint8_t v_done_2788_; uint8_t v_contextDependent_2789_; lean_object* v___x_2791_; uint8_t v_isShared_2792_; uint8_t v_isSharedCheck_2815_; 
lean_del_object(v___x_2774_);
lean_del_object(v___x_2769_);
v_e_x27_2786_ = lean_ctor_get(v_a_2772_, 0);
v_proof_2787_ = lean_ctor_get(v_a_2772_, 1);
v_done_2788_ = lean_ctor_get_uint8(v_a_2772_, sizeof(void*)*2);
v_contextDependent_2789_ = lean_ctor_get_uint8(v_a_2772_, sizeof(void*)*2 + 1);
v_isSharedCheck_2815_ = !lean_is_exclusive(v_a_2772_);
if (v_isSharedCheck_2815_ == 0)
{
v___x_2791_ = v_a_2772_;
v_isShared_2792_ = v_isSharedCheck_2815_;
goto v_resetjp_2790_;
}
else
{
lean_inc(v_proof_2787_);
lean_inc(v_e_x27_2786_);
lean_dec(v_a_2772_);
v___x_2791_ = lean_box(0);
v_isShared_2792_ = v_isSharedCheck_2815_;
goto v_resetjp_2790_;
}
v_resetjp_2790_:
{
lean_object* v___x_2793_; 
lean_inc_ref(v_e_x27_2786_);
v___x_2793_ = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(v___y_2733_, v_e_x27_2765_, v_proof_2766_, v_e_x27_2786_, v_proof_2787_, v___y_2738_, v___y_2739_, v___y_2740_, v___y_2741_, v___y_2742_);
lean_dec(v___y_2742_);
lean_dec_ref(v___y_2741_);
lean_dec(v___y_2740_);
lean_dec_ref(v___y_2739_);
lean_dec(v___y_2738_);
if (lean_obj_tag(v___x_2793_) == 0)
{
lean_object* v_a_2794_; lean_object* v___x_2796_; uint8_t v_isShared_2797_; uint8_t v_isSharedCheck_2806_; 
v_a_2794_ = lean_ctor_get(v___x_2793_, 0);
v_isSharedCheck_2806_ = !lean_is_exclusive(v___x_2793_);
if (v_isSharedCheck_2806_ == 0)
{
v___x_2796_ = v___x_2793_;
v_isShared_2797_ = v_isSharedCheck_2806_;
goto v_resetjp_2795_;
}
else
{
lean_inc(v_a_2794_);
lean_dec(v___x_2793_);
v___x_2796_ = lean_box(0);
v_isShared_2797_ = v_isSharedCheck_2806_;
goto v_resetjp_2795_;
}
v_resetjp_2795_:
{
uint8_t v___y_2799_; 
if (v_contextDependent_2767_ == 0)
{
v___y_2799_ = v_contextDependent_2789_;
goto v___jp_2798_;
}
else
{
v___y_2799_ = v_contextDependent_2767_;
goto v___jp_2798_;
}
v___jp_2798_:
{
lean_object* v___x_2801_; 
if (v_isShared_2792_ == 0)
{
lean_ctor_set(v___x_2791_, 1, v_a_2794_);
v___x_2801_ = v___x_2791_;
goto v_reusejp_2800_;
}
else
{
lean_object* v_reuseFailAlloc_2805_; 
v_reuseFailAlloc_2805_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2805_, 0, v_e_x27_2786_);
lean_ctor_set(v_reuseFailAlloc_2805_, 1, v_a_2794_);
lean_ctor_set_uint8(v_reuseFailAlloc_2805_, sizeof(void*)*2, v_done_2788_);
v___x_2801_ = v_reuseFailAlloc_2805_;
goto v_reusejp_2800_;
}
v_reusejp_2800_:
{
lean_object* v___x_2803_; 
lean_ctor_set_uint8(v___x_2801_, sizeof(void*)*2 + 1, v___y_2799_);
if (v_isShared_2797_ == 0)
{
lean_ctor_set(v___x_2796_, 0, v___x_2801_);
v___x_2803_ = v___x_2796_;
goto v_reusejp_2802_;
}
else
{
lean_object* v_reuseFailAlloc_2804_; 
v_reuseFailAlloc_2804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2804_, 0, v___x_2801_);
v___x_2803_ = v_reuseFailAlloc_2804_;
goto v_reusejp_2802_;
}
v_reusejp_2802_:
{
return v___x_2803_;
}
}
}
}
}
else
{
lean_object* v_a_2807_; lean_object* v___x_2809_; uint8_t v_isShared_2810_; uint8_t v_isSharedCheck_2814_; 
lean_del_object(v___x_2791_);
lean_dec_ref(v_e_x27_2786_);
v_a_2807_ = lean_ctor_get(v___x_2793_, 0);
v_isSharedCheck_2814_ = !lean_is_exclusive(v___x_2793_);
if (v_isSharedCheck_2814_ == 0)
{
v___x_2809_ = v___x_2793_;
v_isShared_2810_ = v_isSharedCheck_2814_;
goto v_resetjp_2808_;
}
else
{
lean_inc(v_a_2807_);
lean_dec(v___x_2793_);
v___x_2809_ = lean_box(0);
v_isShared_2810_ = v_isSharedCheck_2814_;
goto v_resetjp_2808_;
}
v_resetjp_2808_:
{
lean_object* v___x_2812_; 
if (v_isShared_2810_ == 0)
{
v___x_2812_ = v___x_2809_;
goto v_reusejp_2811_;
}
else
{
lean_object* v_reuseFailAlloc_2813_; 
v_reuseFailAlloc_2813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2813_, 0, v_a_2807_);
v___x_2812_ = v_reuseFailAlloc_2813_;
goto v_reusejp_2811_;
}
v_reusejp_2811_:
{
return v___x_2812_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_2769_);
lean_dec_ref(v_proof_2766_);
lean_dec_ref(v_e_x27_2765_);
lean_dec(v___y_2742_);
lean_dec_ref(v___y_2741_);
lean_dec(v___y_2740_);
lean_dec_ref(v___y_2739_);
lean_dec(v___y_2738_);
lean_dec_ref(v___y_2733_);
return v___x_2771_;
}
}
}
else
{
lean_dec_ref_known(v_a_2745_, 2);
lean_dec(v___y_2742_);
lean_dec_ref(v___y_2741_);
lean_dec(v___y_2740_);
lean_dec_ref(v___y_2739_);
lean_dec(v___y_2738_);
lean_dec_ref(v___y_2737_);
lean_dec(v___y_2736_);
lean_dec_ref(v___y_2735_);
lean_dec(v___y_2734_);
lean_dec_ref(v___y_2733_);
lean_dec_ref(v___f_2732_);
return v___x_2744_;
}
}
}
else
{
lean_dec(v___y_2742_);
lean_dec_ref(v___y_2741_);
lean_dec(v___y_2740_);
lean_dec_ref(v___y_2739_);
lean_dec(v___y_2738_);
lean_dec_ref(v___y_2737_);
lean_dec(v___y_2736_);
lean_dec_ref(v___y_2735_);
lean_dec(v___y_2734_);
lean_dec_ref(v___y_2733_);
lean_dec_ref(v___f_2732_);
return v___x_2744_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkSimpDefaultMethods___lam__2___boxed(lean_object* v___f_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_){
_start:
{
lean_object* v_res_2830_; 
v_res_2830_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkSimpDefaultMethods___lam__2(v___f_2818_, v___y_2819_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_);
return v_res_2830_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkSimpDefaultMethods(lean_object* v_extraThms_2834_, lean_object* v_a_2835_, lean_object* v_a_2836_, lean_object* v_a_2837_, lean_object* v_a_2838_, lean_object* v_a_2839_, lean_object* v_a_2840_, lean_object* v_a_2841_, lean_object* v_a_2842_){
_start:
{
lean_object* v___x_2844_; 
v___x_2844_ = l_Lean_Meta_Sym_Simp_getSymSimpTheorems___redArg(v_a_2842_);
if (lean_obj_tag(v___x_2844_) == 0)
{
lean_object* v_a_2845_; lean_object* v___f_2846_; lean_object* v___x_2847_; lean_object* v___f_2848_; lean_object* v___x_2849_; 
v_a_2845_ = lean_ctor_get(v___x_2844_, 0);
lean_inc(v_a_2845_);
lean_dec_ref_known(v___x_2844_, 1);
v___f_2846_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___lam__0___boxed), 13, 1);
lean_closure_set(v___f_2846_, 0, v_a_2845_);
v___x_2847_ = lean_unsigned_to_nat(255u);
v___f_2848_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkSimpDefaultMethods___lam__1___boxed), 13, 2);
lean_closure_set(v___f_2848_, 0, v___x_2847_);
lean_closure_set(v___f_2848_, 1, v___f_2846_);
v___x_2849_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems(v___f_2848_, v_extraThms_2834_, v_a_2835_, v_a_2836_, v_a_2837_, v_a_2838_, v_a_2839_, v_a_2840_, v_a_2841_, v_a_2842_);
if (lean_obj_tag(v___x_2849_) == 0)
{
lean_object* v_a_2850_; lean_object* v___x_2852_; uint8_t v_isShared_2853_; uint8_t v_isSharedCheck_2859_; 
v_a_2850_ = lean_ctor_get(v___x_2849_, 0);
v_isSharedCheck_2859_ = !lean_is_exclusive(v___x_2849_);
if (v_isSharedCheck_2859_ == 0)
{
v___x_2852_ = v___x_2849_;
v_isShared_2853_ = v_isSharedCheck_2859_;
goto v_resetjp_2851_;
}
else
{
lean_inc(v_a_2850_);
lean_dec(v___x_2849_);
v___x_2852_ = lean_box(0);
v_isShared_2853_ = v_isSharedCheck_2859_;
goto v_resetjp_2851_;
}
v_resetjp_2851_:
{
lean_object* v___f_2854_; lean_object* v___x_2855_; lean_object* v___x_2857_; 
v___f_2854_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkSimpDefaultMethods___closed__1));
v___x_2855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2855_, 0, v___f_2854_);
lean_ctor_set(v___x_2855_, 1, v_a_2850_);
if (v_isShared_2853_ == 0)
{
lean_ctor_set(v___x_2852_, 0, v___x_2855_);
v___x_2857_ = v___x_2852_;
goto v_reusejp_2856_;
}
else
{
lean_object* v_reuseFailAlloc_2858_; 
v_reuseFailAlloc_2858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2858_, 0, v___x_2855_);
v___x_2857_ = v_reuseFailAlloc_2858_;
goto v_reusejp_2856_;
}
v_reusejp_2856_:
{
return v___x_2857_;
}
}
}
else
{
lean_object* v_a_2860_; lean_object* v___x_2862_; uint8_t v_isShared_2863_; uint8_t v_isSharedCheck_2867_; 
v_a_2860_ = lean_ctor_get(v___x_2849_, 0);
v_isSharedCheck_2867_ = !lean_is_exclusive(v___x_2849_);
if (v_isSharedCheck_2867_ == 0)
{
v___x_2862_ = v___x_2849_;
v_isShared_2863_ = v_isSharedCheck_2867_;
goto v_resetjp_2861_;
}
else
{
lean_inc(v_a_2860_);
lean_dec(v___x_2849_);
v___x_2862_ = lean_box(0);
v_isShared_2863_ = v_isSharedCheck_2867_;
goto v_resetjp_2861_;
}
v_resetjp_2861_:
{
lean_object* v___x_2865_; 
if (v_isShared_2863_ == 0)
{
v___x_2865_ = v___x_2862_;
goto v_reusejp_2864_;
}
else
{
lean_object* v_reuseFailAlloc_2866_; 
v_reuseFailAlloc_2866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2866_, 0, v_a_2860_);
v___x_2865_ = v_reuseFailAlloc_2866_;
goto v_reusejp_2864_;
}
v_reusejp_2864_:
{
return v___x_2865_;
}
}
}
}
else
{
lean_object* v_a_2868_; lean_object* v___x_2870_; uint8_t v_isShared_2871_; uint8_t v_isSharedCheck_2875_; 
v_a_2868_ = lean_ctor_get(v___x_2844_, 0);
v_isSharedCheck_2875_ = !lean_is_exclusive(v___x_2844_);
if (v_isSharedCheck_2875_ == 0)
{
v___x_2870_ = v___x_2844_;
v_isShared_2871_ = v_isSharedCheck_2875_;
goto v_resetjp_2869_;
}
else
{
lean_inc(v_a_2868_);
lean_dec(v___x_2844_);
v___x_2870_ = lean_box(0);
v_isShared_2871_ = v_isSharedCheck_2875_;
goto v_resetjp_2869_;
}
v_resetjp_2869_:
{
lean_object* v___x_2873_; 
if (v_isShared_2871_ == 0)
{
v___x_2873_ = v___x_2870_;
goto v_reusejp_2872_;
}
else
{
lean_object* v_reuseFailAlloc_2874_; 
v_reuseFailAlloc_2874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2874_, 0, v_a_2868_);
v___x_2873_ = v_reuseFailAlloc_2874_;
goto v_reusejp_2872_;
}
v_reusejp_2872_:
{
return v___x_2873_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkSimpDefaultMethods___boxed(lean_object* v_extraThms_2876_, lean_object* v_a_2877_, lean_object* v_a_2878_, lean_object* v_a_2879_, lean_object* v_a_2880_, lean_object* v_a_2881_, lean_object* v_a_2882_, lean_object* v_a_2883_, lean_object* v_a_2884_, lean_object* v_a_2885_){
_start:
{
lean_object* v_res_2886_; 
v_res_2886_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkSimpDefaultMethods(v_extraThms_2876_, v_a_2877_, v_a_2878_, v_a_2879_, v_a_2880_, v_a_2881_, v_a_2882_, v_a_2883_, v_a_2884_);
lean_dec(v_a_2884_);
lean_dec_ref(v_a_2883_);
lean_dec(v_a_2882_);
lean_dec_ref(v_a_2881_);
lean_dec(v_a_2880_);
lean_dec_ref(v_a_2879_);
lean_dec(v_a_2878_);
lean_dec_ref(v_a_2877_);
lean_dec_ref(v_extraThms_2876_);
return v_res_2886_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabSimpVariant___closed__1(void){
_start:
{
lean_object* v___x_2888_; lean_object* v___x_2889_; 
v___x_2888_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabSimpVariant___closed__0));
v___x_2889_ = l_Lean_stringToMessageData(v___x_2888_);
return v___x_2889_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabSimpVariant___closed__3(void){
_start:
{
lean_object* v___x_2891_; lean_object* v___x_2892_; 
v___x_2891_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabSimpVariant___closed__2));
v___x_2892_ = l_Lean_stringToMessageData(v___x_2891_);
return v___x_2892_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabSimpVariant(lean_object* v_variantName_2896_, lean_object* v_extraThms_2897_, lean_object* v_a_2898_, lean_object* v_a_2899_, lean_object* v_a_2900_, lean_object* v_a_2901_, lean_object* v_a_2902_, lean_object* v_a_2903_, lean_object* v_a_2904_, lean_object* v_a_2905_){
_start:
{
uint8_t v___x_2907_; 
v___x_2907_ = l_Lean_Name_isAnonymous(v_variantName_2896_);
if (v___x_2907_ == 0)
{
lean_object* v___x_2908_; lean_object* v_env_2909_; lean_object* v___x_2910_; 
v___x_2908_ = lean_st_ref_get(v_a_2905_);
v_env_2909_ = lean_ctor_get(v___x_2908_, 0);
lean_inc_ref(v_env_2909_);
lean_dec(v___x_2908_);
v___x_2910_ = l_Lean_Meta_Sym_Simp_getSymSimpVariant_x3f(v_env_2909_, v_variantName_2896_);
if (lean_obj_tag(v___x_2910_) == 1)
{
lean_object* v_val_2911_; lean_object* v_pre_x3f_2912_; lean_object* v_post_x3f_2913_; lean_object* v_config_2914_; lean_object* v___x_2915_; 
lean_dec(v_variantName_2896_);
v_val_2911_ = lean_ctor_get(v___x_2910_, 0);
lean_inc(v_val_2911_);
lean_dec_ref_known(v___x_2910_, 1);
v_pre_x3f_2912_ = lean_ctor_get(v_val_2911_, 0);
lean_inc(v_pre_x3f_2912_);
v_post_x3f_2913_ = lean_ctor_get(v_val_2911_, 1);
lean_inc(v_post_x3f_2913_);
v_config_2914_ = lean_ctor_get(v_val_2911_, 2);
lean_inc_ref(v_config_2914_);
lean_dec(v_val_2911_);
v___x_2915_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabOptSimproc(v_pre_x3f_2912_, v_a_2898_, v_a_2899_, v_a_2900_, v_a_2901_, v_a_2902_, v_a_2903_, v_a_2904_, v_a_2905_);
if (lean_obj_tag(v___x_2915_) == 0)
{
lean_object* v_a_2916_; lean_object* v___x_2917_; 
v_a_2916_ = lean_ctor_get(v___x_2915_, 0);
lean_inc(v_a_2916_);
lean_dec_ref_known(v___x_2915_, 1);
v___x_2917_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabOptSimproc(v_post_x3f_2913_, v_a_2898_, v_a_2899_, v_a_2900_, v_a_2901_, v_a_2902_, v_a_2903_, v_a_2904_, v_a_2905_);
if (lean_obj_tag(v___x_2917_) == 0)
{
lean_object* v_a_2918_; lean_object* v___x_2919_; 
v_a_2918_ = lean_ctor_get(v___x_2917_, 0);
lean_inc(v_a_2918_);
lean_dec_ref_known(v___x_2917_, 1);
v___x_2919_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems(v_a_2918_, v_extraThms_2897_, v_a_2898_, v_a_2899_, v_a_2900_, v_a_2901_, v_a_2902_, v_a_2903_, v_a_2904_, v_a_2905_);
if (lean_obj_tag(v___x_2919_) == 0)
{
lean_object* v_a_2920_; lean_object* v___x_2922_; uint8_t v_isShared_2923_; uint8_t v_isSharedCheck_2929_; 
v_a_2920_ = lean_ctor_get(v___x_2919_, 0);
v_isSharedCheck_2929_ = !lean_is_exclusive(v___x_2919_);
if (v_isSharedCheck_2929_ == 0)
{
v___x_2922_ = v___x_2919_;
v_isShared_2923_ = v_isSharedCheck_2929_;
goto v_resetjp_2921_;
}
else
{
lean_inc(v_a_2920_);
lean_dec(v___x_2919_);
v___x_2922_ = lean_box(0);
v_isShared_2923_ = v_isSharedCheck_2929_;
goto v_resetjp_2921_;
}
v_resetjp_2921_:
{
lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2927_; 
v___x_2924_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2924_, 0, v_a_2916_);
lean_ctor_set(v___x_2924_, 1, v_a_2920_);
v___x_2925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2925_, 0, v___x_2924_);
lean_ctor_set(v___x_2925_, 1, v_config_2914_);
if (v_isShared_2923_ == 0)
{
lean_ctor_set(v___x_2922_, 0, v___x_2925_);
v___x_2927_ = v___x_2922_;
goto v_reusejp_2926_;
}
else
{
lean_object* v_reuseFailAlloc_2928_; 
v_reuseFailAlloc_2928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2928_, 0, v___x_2925_);
v___x_2927_ = v_reuseFailAlloc_2928_;
goto v_reusejp_2926_;
}
v_reusejp_2926_:
{
return v___x_2927_;
}
}
}
else
{
lean_object* v_a_2930_; lean_object* v___x_2932_; uint8_t v_isShared_2933_; uint8_t v_isSharedCheck_2937_; 
lean_dec(v_a_2916_);
lean_dec_ref(v_config_2914_);
v_a_2930_ = lean_ctor_get(v___x_2919_, 0);
v_isSharedCheck_2937_ = !lean_is_exclusive(v___x_2919_);
if (v_isSharedCheck_2937_ == 0)
{
v___x_2932_ = v___x_2919_;
v_isShared_2933_ = v_isSharedCheck_2937_;
goto v_resetjp_2931_;
}
else
{
lean_inc(v_a_2930_);
lean_dec(v___x_2919_);
v___x_2932_ = lean_box(0);
v_isShared_2933_ = v_isSharedCheck_2937_;
goto v_resetjp_2931_;
}
v_resetjp_2931_:
{
lean_object* v___x_2935_; 
if (v_isShared_2933_ == 0)
{
v___x_2935_ = v___x_2932_;
goto v_reusejp_2934_;
}
else
{
lean_object* v_reuseFailAlloc_2936_; 
v_reuseFailAlloc_2936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2936_, 0, v_a_2930_);
v___x_2935_ = v_reuseFailAlloc_2936_;
goto v_reusejp_2934_;
}
v_reusejp_2934_:
{
return v___x_2935_;
}
}
}
}
else
{
lean_object* v_a_2938_; lean_object* v___x_2940_; uint8_t v_isShared_2941_; uint8_t v_isSharedCheck_2945_; 
lean_dec(v_a_2916_);
lean_dec_ref(v_config_2914_);
v_a_2938_ = lean_ctor_get(v___x_2917_, 0);
v_isSharedCheck_2945_ = !lean_is_exclusive(v___x_2917_);
if (v_isSharedCheck_2945_ == 0)
{
v___x_2940_ = v___x_2917_;
v_isShared_2941_ = v_isSharedCheck_2945_;
goto v_resetjp_2939_;
}
else
{
lean_inc(v_a_2938_);
lean_dec(v___x_2917_);
v___x_2940_ = lean_box(0);
v_isShared_2941_ = v_isSharedCheck_2945_;
goto v_resetjp_2939_;
}
v_resetjp_2939_:
{
lean_object* v___x_2943_; 
if (v_isShared_2941_ == 0)
{
v___x_2943_ = v___x_2940_;
goto v_reusejp_2942_;
}
else
{
lean_object* v_reuseFailAlloc_2944_; 
v_reuseFailAlloc_2944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2944_, 0, v_a_2938_);
v___x_2943_ = v_reuseFailAlloc_2944_;
goto v_reusejp_2942_;
}
v_reusejp_2942_:
{
return v___x_2943_;
}
}
}
}
else
{
lean_object* v_a_2946_; lean_object* v___x_2948_; uint8_t v_isShared_2949_; uint8_t v_isSharedCheck_2953_; 
lean_dec_ref(v_config_2914_);
lean_dec(v_post_x3f_2913_);
v_a_2946_ = lean_ctor_get(v___x_2915_, 0);
v_isSharedCheck_2953_ = !lean_is_exclusive(v___x_2915_);
if (v_isSharedCheck_2953_ == 0)
{
v___x_2948_ = v___x_2915_;
v_isShared_2949_ = v_isSharedCheck_2953_;
goto v_resetjp_2947_;
}
else
{
lean_inc(v_a_2946_);
lean_dec(v___x_2915_);
v___x_2948_ = lean_box(0);
v_isShared_2949_ = v_isSharedCheck_2953_;
goto v_resetjp_2947_;
}
v_resetjp_2947_:
{
lean_object* v___x_2951_; 
if (v_isShared_2949_ == 0)
{
v___x_2951_ = v___x_2948_;
goto v_reusejp_2950_;
}
else
{
lean_object* v_reuseFailAlloc_2952_; 
v_reuseFailAlloc_2952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2952_, 0, v_a_2946_);
v___x_2951_ = v_reuseFailAlloc_2952_;
goto v_reusejp_2950_;
}
v_reusejp_2950_:
{
return v___x_2951_;
}
}
}
}
else
{
lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; 
lean_dec(v___x_2910_);
v___x_2954_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabSimpVariant___closed__1, &l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabSimpVariant___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabSimpVariant___closed__1);
v___x_2955_ = l_Lean_MessageData_ofName(v_variantName_2896_);
v___x_2956_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2956_, 0, v___x_2954_);
lean_ctor_set(v___x_2956_, 1, v___x_2955_);
v___x_2957_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabSimpVariant___closed__3, &l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabSimpVariant___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabSimpVariant___closed__3);
v___x_2958_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2958_, 0, v___x_2956_);
lean_ctor_set(v___x_2958_, 1, v___x_2957_);
v___x_2959_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__2___redArg(v___x_2958_, v_a_2902_, v_a_2903_, v_a_2904_, v_a_2905_);
return v___x_2959_;
}
}
else
{
lean_object* v___x_2960_; 
lean_dec(v_variantName_2896_);
v___x_2960_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkSimpDefaultMethods(v_extraThms_2897_, v_a_2898_, v_a_2899_, v_a_2900_, v_a_2901_, v_a_2902_, v_a_2903_, v_a_2904_, v_a_2905_);
if (lean_obj_tag(v___x_2960_) == 0)
{
lean_object* v_a_2961_; lean_object* v___x_2963_; uint8_t v_isShared_2964_; uint8_t v_isSharedCheck_2970_; 
v_a_2961_ = lean_ctor_get(v___x_2960_, 0);
v_isSharedCheck_2970_ = !lean_is_exclusive(v___x_2960_);
if (v_isSharedCheck_2970_ == 0)
{
v___x_2963_ = v___x_2960_;
v_isShared_2964_ = v_isSharedCheck_2970_;
goto v_resetjp_2962_;
}
else
{
lean_inc(v_a_2961_);
lean_dec(v___x_2960_);
v___x_2963_ = lean_box(0);
v_isShared_2964_ = v_isSharedCheck_2970_;
goto v_resetjp_2962_;
}
v_resetjp_2962_:
{
lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2968_; 
v___x_2965_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabSimpVariant___closed__4));
v___x_2966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2966_, 0, v_a_2961_);
lean_ctor_set(v___x_2966_, 1, v___x_2965_);
if (v_isShared_2964_ == 0)
{
lean_ctor_set(v___x_2963_, 0, v___x_2966_);
v___x_2968_ = v___x_2963_;
goto v_reusejp_2967_;
}
else
{
lean_object* v_reuseFailAlloc_2969_; 
v_reuseFailAlloc_2969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2969_, 0, v___x_2966_);
v___x_2968_ = v_reuseFailAlloc_2969_;
goto v_reusejp_2967_;
}
v_reusejp_2967_:
{
return v___x_2968_;
}
}
}
else
{
lean_object* v_a_2971_; lean_object* v___x_2973_; uint8_t v_isShared_2974_; uint8_t v_isSharedCheck_2978_; 
v_a_2971_ = lean_ctor_get(v___x_2960_, 0);
v_isSharedCheck_2978_ = !lean_is_exclusive(v___x_2960_);
if (v_isSharedCheck_2978_ == 0)
{
v___x_2973_ = v___x_2960_;
v_isShared_2974_ = v_isSharedCheck_2978_;
goto v_resetjp_2972_;
}
else
{
lean_inc(v_a_2971_);
lean_dec(v___x_2960_);
v___x_2973_ = lean_box(0);
v_isShared_2974_ = v_isSharedCheck_2978_;
goto v_resetjp_2972_;
}
v_resetjp_2972_:
{
lean_object* v___x_2976_; 
if (v_isShared_2974_ == 0)
{
v___x_2976_ = v___x_2973_;
goto v_reusejp_2975_;
}
else
{
lean_object* v_reuseFailAlloc_2977_; 
v_reuseFailAlloc_2977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2977_, 0, v_a_2971_);
v___x_2976_ = v_reuseFailAlloc_2977_;
goto v_reusejp_2975_;
}
v_reusejp_2975_:
{
return v___x_2976_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabSimpVariant___boxed(lean_object* v_variantName_2979_, lean_object* v_extraThms_2980_, lean_object* v_a_2981_, lean_object* v_a_2982_, lean_object* v_a_2983_, lean_object* v_a_2984_, lean_object* v_a_2985_, lean_object* v_a_2986_, lean_object* v_a_2987_, lean_object* v_a_2988_, lean_object* v_a_2989_){
_start:
{
lean_object* v_res_2990_; 
v_res_2990_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabSimpVariant(v_variantName_2979_, v_extraThms_2980_, v_a_2981_, v_a_2982_, v_a_2983_, v_a_2984_, v_a_2985_, v_a_2986_, v_a_2987_, v_a_2988_);
lean_dec(v_a_2988_);
lean_dec_ref(v_a_2987_);
lean_dec(v_a_2986_);
lean_dec_ref(v_a_2985_);
lean_dec(v_a_2984_);
lean_dec_ref(v_a_2983_);
lean_dec(v_a_2982_);
lean_dec_ref(v_a_2981_);
lean_dec_ref(v_extraThms_2980_);
return v_res_2990_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__0___redArg___lam__0(lean_object* v_x_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_){
_start:
{
lean_object* v___x_3002_; 
lean_inc(v___y_2996_);
lean_inc_ref(v___y_2995_);
lean_inc(v___y_2994_);
lean_inc_ref(v___y_2993_);
lean_inc(v___y_2992_);
v___x_3002_ = lean_apply_10(v_x_2991_, v___y_2992_, v___y_2993_, v___y_2994_, v___y_2995_, v___y_2996_, v___y_2997_, v___y_2998_, v___y_2999_, v___y_3000_, lean_box(0));
return v___x_3002_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__0___redArg___lam__0___boxed(lean_object* v_x_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_){
_start:
{
lean_object* v_res_3014_; 
v_res_3014_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__0___redArg___lam__0(v_x_3003_, v___y_3004_, v___y_3005_, v___y_3006_, v___y_3007_, v___y_3008_, v___y_3009_, v___y_3010_, v___y_3011_, v___y_3012_);
lean_dec(v___y_3008_);
lean_dec_ref(v___y_3007_);
lean_dec(v___y_3006_);
lean_dec_ref(v___y_3005_);
lean_dec(v___y_3004_);
return v_res_3014_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__0___redArg(lean_object* v_mvarId_3015_, lean_object* v_x_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_){
_start:
{
lean_object* v___f_3027_; lean_object* v___x_3028_; 
lean_inc(v___y_3021_);
lean_inc_ref(v___y_3020_);
lean_inc(v___y_3019_);
lean_inc_ref(v___y_3018_);
lean_inc(v___y_3017_);
v___f_3027_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__0___redArg___lam__0___boxed), 11, 6);
lean_closure_set(v___f_3027_, 0, v_x_3016_);
lean_closure_set(v___f_3027_, 1, v___y_3017_);
lean_closure_set(v___f_3027_, 2, v___y_3018_);
lean_closure_set(v___f_3027_, 3, v___y_3019_);
lean_closure_set(v___f_3027_, 4, v___y_3020_);
lean_closure_set(v___f_3027_, 5, v___y_3021_);
v___x_3028_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_3015_, v___f_3027_, v___y_3022_, v___y_3023_, v___y_3024_, v___y_3025_);
if (lean_obj_tag(v___x_3028_) == 0)
{
return v___x_3028_;
}
else
{
lean_object* v_a_3029_; lean_object* v___x_3031_; uint8_t v_isShared_3032_; uint8_t v_isSharedCheck_3036_; 
v_a_3029_ = lean_ctor_get(v___x_3028_, 0);
v_isSharedCheck_3036_ = !lean_is_exclusive(v___x_3028_);
if (v_isSharedCheck_3036_ == 0)
{
v___x_3031_ = v___x_3028_;
v_isShared_3032_ = v_isSharedCheck_3036_;
goto v_resetjp_3030_;
}
else
{
lean_inc(v_a_3029_);
lean_dec(v___x_3028_);
v___x_3031_ = lean_box(0);
v_isShared_3032_ = v_isSharedCheck_3036_;
goto v_resetjp_3030_;
}
v_resetjp_3030_:
{
lean_object* v___x_3034_; 
if (v_isShared_3032_ == 0)
{
v___x_3034_ = v___x_3031_;
goto v_reusejp_3033_;
}
else
{
lean_object* v_reuseFailAlloc_3035_; 
v_reuseFailAlloc_3035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3035_, 0, v_a_3029_);
v___x_3034_ = v_reuseFailAlloc_3035_;
goto v_reusejp_3033_;
}
v_reusejp_3033_:
{
return v___x_3034_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__0___redArg___boxed(lean_object* v_mvarId_3037_, lean_object* v_x_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_){
_start:
{
lean_object* v_res_3049_; 
v_res_3049_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__0___redArg(v_mvarId_3037_, v_x_3038_, v___y_3039_, v___y_3040_, v___y_3041_, v___y_3042_, v___y_3043_, v___y_3044_, v___y_3045_, v___y_3046_, v___y_3047_);
lean_dec(v___y_3047_);
lean_dec_ref(v___y_3046_);
lean_dec(v___y_3045_);
lean_dec_ref(v___y_3044_);
lean_dec(v___y_3043_);
lean_dec_ref(v___y_3042_);
lean_dec(v___y_3041_);
lean_dec_ref(v___y_3040_);
lean_dec(v___y_3039_);
return v_res_3049_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__0(lean_object* v_00_u03b1_3050_, lean_object* v_mvarId_3051_, lean_object* v_x_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_){
_start:
{
lean_object* v___x_3063_; 
v___x_3063_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__0___redArg(v_mvarId_3051_, v_x_3052_, v___y_3053_, v___y_3054_, v___y_3055_, v___y_3056_, v___y_3057_, v___y_3058_, v___y_3059_, v___y_3060_, v___y_3061_);
return v___x_3063_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__0___boxed(lean_object* v_00_u03b1_3064_, lean_object* v_mvarId_3065_, lean_object* v_x_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_){
_start:
{
lean_object* v_res_3077_; 
v_res_3077_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__0(v_00_u03b1_3064_, v_mvarId_3065_, v_x_3066_, v___y_3067_, v___y_3068_, v___y_3069_, v___y_3070_, v___y_3071_, v___y_3072_, v___y_3073_, v___y_3074_, v___y_3075_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__0(lean_object* v_mvarId_3078_, lean_object* v_fst_3079_, lean_object* v_snd_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_){
_start:
{
lean_object* v___x_3092_; 
v___x_3092_ = l_Lean_MVarId_getType(v_mvarId_3078_, v___y_3087_, v___y_3088_, v___y_3089_, v___y_3090_);
if (lean_obj_tag(v___x_3092_) == 0)
{
lean_object* v_a_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; 
v_a_3093_ = lean_ctor_get(v___x_3092_, 0);
lean_inc(v_a_3093_);
lean_dec_ref_known(v___x_3092_, 1);
v___x_3094_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simp___boxed), 11, 1);
lean_closure_set(v___x_3094_, 0, v_a_3093_);
v___x_3095_ = l_Lean_Meta_Sym_Simp_SimpM_run___redArg(v___x_3094_, v_fst_3079_, v_snd_3080_, v___y_3081_, v___y_3085_, v___y_3086_, v___y_3087_, v___y_3088_, v___y_3089_, v___y_3090_);
return v___x_3095_;
}
else
{
lean_object* v_a_3096_; lean_object* v___x_3098_; uint8_t v_isShared_3099_; uint8_t v_isSharedCheck_3103_; 
lean_dec_ref(v___y_3081_);
lean_dec_ref(v_snd_3080_);
lean_dec_ref(v_fst_3079_);
v_a_3096_ = lean_ctor_get(v___x_3092_, 0);
v_isSharedCheck_3103_ = !lean_is_exclusive(v___x_3092_);
if (v_isSharedCheck_3103_ == 0)
{
v___x_3098_ = v___x_3092_;
v_isShared_3099_ = v_isSharedCheck_3103_;
goto v_resetjp_3097_;
}
else
{
lean_inc(v_a_3096_);
lean_dec(v___x_3092_);
v___x_3098_ = lean_box(0);
v_isShared_3099_ = v_isSharedCheck_3103_;
goto v_resetjp_3097_;
}
v_resetjp_3097_:
{
lean_object* v___x_3101_; 
if (v_isShared_3099_ == 0)
{
v___x_3101_ = v___x_3098_;
goto v_reusejp_3100_;
}
else
{
lean_object* v_reuseFailAlloc_3102_; 
v_reuseFailAlloc_3102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3102_, 0, v_a_3096_);
v___x_3101_ = v_reuseFailAlloc_3102_;
goto v_reusejp_3100_;
}
v_reusejp_3100_:
{
return v___x_3101_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__0___boxed(lean_object* v_mvarId_3104_, lean_object* v_fst_3105_, lean_object* v_snd_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_){
_start:
{
lean_object* v_res_3118_; 
v_res_3118_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__0(v_mvarId_3104_, v_fst_3105_, v_snd_3106_, v___y_3107_, v___y_3108_, v___y_3109_, v___y_3110_, v___y_3111_, v___y_3112_, v___y_3113_, v___y_3114_, v___y_3115_, v___y_3116_);
lean_dec(v___y_3116_);
lean_dec_ref(v___y_3115_);
lean_dec(v___y_3114_);
lean_dec_ref(v___y_3113_);
lean_dec(v___y_3112_);
lean_dec_ref(v___y_3111_);
lean_dec(v___y_3110_);
lean_dec_ref(v___y_3109_);
lean_dec(v___y_3108_);
return v_res_3118_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__1(lean_object* v_fst_3119_, lean_object* v_mvarId_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_){
_start:
{
lean_object* v___x_3131_; 
v___x_3131_ = l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult(v_fst_3119_, v_mvarId_3120_, v___y_3124_, v___y_3125_, v___y_3126_, v___y_3127_, v___y_3128_, v___y_3129_);
return v___x_3131_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__1___boxed(lean_object* v_fst_3132_, lean_object* v_mvarId_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_){
_start:
{
lean_object* v_res_3144_; 
v_res_3144_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__1(v_fst_3132_, v_mvarId_3133_, v___y_3134_, v___y_3135_, v___y_3136_, v___y_3137_, v___y_3138_, v___y_3139_, v___y_3140_, v___y_3141_, v___y_3142_);
lean_dec(v___y_3142_);
lean_dec_ref(v___y_3141_);
lean_dec(v___y_3140_);
lean_dec_ref(v___y_3139_);
lean_dec(v___y_3138_);
lean_dec_ref(v___y_3137_);
lean_dec(v___y_3136_);
lean_dec_ref(v___y_3135_);
lean_dec(v___y_3134_);
return v_res_3144_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__2_spec__5___redArg(lean_object* v_a_3145_, lean_object* v_x_3146_){
_start:
{
if (lean_obj_tag(v_x_3146_) == 0)
{
lean_object* v___x_3147_; 
v___x_3147_ = lean_box(0);
return v___x_3147_;
}
else
{
lean_object* v_key_3148_; lean_object* v_value_3149_; lean_object* v_tail_3150_; uint8_t v___x_3151_; 
v_key_3148_ = lean_ctor_get(v_x_3146_, 0);
v_value_3149_ = lean_ctor_get(v_x_3146_, 1);
v_tail_3150_ = lean_ctor_get(v_x_3146_, 2);
v___x_3151_ = l_Lean_Elab_Tactic_Grind_instBEqSimpCacheKey_beq(v_key_3148_, v_a_3145_);
if (v___x_3151_ == 0)
{
v_x_3146_ = v_tail_3150_;
goto _start;
}
else
{
lean_object* v___x_3153_; 
lean_inc(v_value_3149_);
v___x_3153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3153_, 0, v_value_3149_);
return v___x_3153_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__2_spec__5___redArg___boxed(lean_object* v_a_3154_, lean_object* v_x_3155_){
_start:
{
lean_object* v_res_3156_; 
v_res_3156_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__2_spec__5___redArg(v_a_3154_, v_x_3155_);
lean_dec(v_x_3155_);
lean_dec_ref(v_a_3154_);
return v_res_3156_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__2___redArg(lean_object* v_m_3157_, lean_object* v_a_3158_){
_start:
{
lean_object* v_buckets_3159_; lean_object* v___x_3160_; uint64_t v___x_3161_; uint64_t v___x_3162_; uint64_t v___x_3163_; uint64_t v_fold_3164_; uint64_t v___x_3165_; uint64_t v___x_3166_; uint64_t v___x_3167_; size_t v___x_3168_; size_t v___x_3169_; size_t v___x_3170_; size_t v___x_3171_; size_t v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; 
v_buckets_3159_ = lean_ctor_get(v_m_3157_, 1);
v___x_3160_ = lean_array_get_size(v_buckets_3159_);
v___x_3161_ = l_Lean_Elab_Tactic_Grind_instHashableSimpCacheKey_hash(v_a_3158_);
v___x_3162_ = 32ULL;
v___x_3163_ = lean_uint64_shift_right(v___x_3161_, v___x_3162_);
v_fold_3164_ = lean_uint64_xor(v___x_3161_, v___x_3163_);
v___x_3165_ = 16ULL;
v___x_3166_ = lean_uint64_shift_right(v_fold_3164_, v___x_3165_);
v___x_3167_ = lean_uint64_xor(v_fold_3164_, v___x_3166_);
v___x_3168_ = lean_uint64_to_usize(v___x_3167_);
v___x_3169_ = lean_usize_of_nat(v___x_3160_);
v___x_3170_ = ((size_t)1ULL);
v___x_3171_ = lean_usize_sub(v___x_3169_, v___x_3170_);
v___x_3172_ = lean_usize_land(v___x_3168_, v___x_3171_);
v___x_3173_ = lean_array_uget_borrowed(v_buckets_3159_, v___x_3172_);
v___x_3174_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__2_spec__5___redArg(v_a_3158_, v___x_3173_);
return v___x_3174_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__2___redArg___boxed(lean_object* v_m_3175_, lean_object* v_a_3176_){
_start:
{
lean_object* v_res_3177_; 
v_res_3177_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__2___redArg(v_m_3175_, v_a_3176_);
lean_dec_ref(v_a_3176_);
lean_dec_ref(v_m_3175_);
return v_res_3177_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__4(uint8_t v___x_3178_, uint8_t v___x_3179_, lean_object* v_as_3180_, size_t v_i_3181_, size_t v_stop_3182_, lean_object* v_b_3183_){
_start:
{
lean_object* v___y_3185_; uint8_t v___x_3189_; 
v___x_3189_ = lean_usize_dec_eq(v_i_3181_, v_stop_3182_);
if (v___x_3189_ == 0)
{
lean_object* v_fst_3190_; uint8_t v___x_3191_; 
v_fst_3190_ = lean_ctor_get(v_b_3183_, 0);
v___x_3191_ = lean_unbox(v_fst_3190_);
if (v___x_3191_ == 0)
{
lean_object* v_snd_3192_; lean_object* v___x_3194_; uint8_t v_isShared_3195_; uint8_t v_isSharedCheck_3200_; 
v_snd_3192_ = lean_ctor_get(v_b_3183_, 1);
v_isSharedCheck_3200_ = !lean_is_exclusive(v_b_3183_);
if (v_isSharedCheck_3200_ == 0)
{
lean_object* v_unused_3201_; 
v_unused_3201_ = lean_ctor_get(v_b_3183_, 0);
lean_dec(v_unused_3201_);
v___x_3194_ = v_b_3183_;
v_isShared_3195_ = v_isSharedCheck_3200_;
goto v_resetjp_3193_;
}
else
{
lean_inc(v_snd_3192_);
lean_dec(v_b_3183_);
v___x_3194_ = lean_box(0);
v_isShared_3195_ = v_isSharedCheck_3200_;
goto v_resetjp_3193_;
}
v_resetjp_3193_:
{
lean_object* v___x_3196_; lean_object* v___x_3198_; 
v___x_3196_ = lean_box(v___x_3178_);
if (v_isShared_3195_ == 0)
{
lean_ctor_set(v___x_3194_, 0, v___x_3196_);
v___x_3198_ = v___x_3194_;
goto v_reusejp_3197_;
}
else
{
lean_object* v_reuseFailAlloc_3199_; 
v_reuseFailAlloc_3199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3199_, 0, v___x_3196_);
lean_ctor_set(v_reuseFailAlloc_3199_, 1, v_snd_3192_);
v___x_3198_ = v_reuseFailAlloc_3199_;
goto v_reusejp_3197_;
}
v_reusejp_3197_:
{
v___y_3185_ = v___x_3198_;
goto v___jp_3184_;
}
}
}
else
{
lean_object* v_snd_3202_; lean_object* v___x_3204_; uint8_t v_isShared_3205_; uint8_t v_isSharedCheck_3212_; 
v_snd_3202_ = lean_ctor_get(v_b_3183_, 1);
v_isSharedCheck_3212_ = !lean_is_exclusive(v_b_3183_);
if (v_isSharedCheck_3212_ == 0)
{
lean_object* v_unused_3213_; 
v_unused_3213_ = lean_ctor_get(v_b_3183_, 0);
lean_dec(v_unused_3213_);
v___x_3204_ = v_b_3183_;
v_isShared_3205_ = v_isSharedCheck_3212_;
goto v_resetjp_3203_;
}
else
{
lean_inc(v_snd_3202_);
lean_dec(v_b_3183_);
v___x_3204_ = lean_box(0);
v_isShared_3205_ = v_isSharedCheck_3212_;
goto v_resetjp_3203_;
}
v_resetjp_3203_:
{
lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3210_; 
v___x_3206_ = lean_array_uget_borrowed(v_as_3180_, v_i_3181_);
lean_inc(v___x_3206_);
v___x_3207_ = lean_array_push(v_snd_3202_, v___x_3206_);
v___x_3208_ = lean_box(v___x_3179_);
if (v_isShared_3205_ == 0)
{
lean_ctor_set(v___x_3204_, 1, v___x_3207_);
lean_ctor_set(v___x_3204_, 0, v___x_3208_);
v___x_3210_ = v___x_3204_;
goto v_reusejp_3209_;
}
else
{
lean_object* v_reuseFailAlloc_3211_; 
v_reuseFailAlloc_3211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3211_, 0, v___x_3208_);
lean_ctor_set(v_reuseFailAlloc_3211_, 1, v___x_3207_);
v___x_3210_ = v_reuseFailAlloc_3211_;
goto v_reusejp_3209_;
}
v_reusejp_3209_:
{
v___y_3185_ = v___x_3210_;
goto v___jp_3184_;
}
}
}
}
else
{
return v_b_3183_;
}
v___jp_3184_:
{
size_t v___x_3186_; size_t v___x_3187_; 
v___x_3186_ = ((size_t)1ULL);
v___x_3187_ = lean_usize_add(v_i_3181_, v___x_3186_);
v_i_3181_ = v___x_3187_;
v_b_3183_ = v___y_3185_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__4___boxed(lean_object* v___x_3214_, lean_object* v___x_3215_, lean_object* v_as_3216_, lean_object* v_i_3217_, lean_object* v_stop_3218_, lean_object* v_b_3219_){
_start:
{
uint8_t v___x_9506__boxed_3220_; uint8_t v___x_9507__boxed_3221_; size_t v_i_boxed_3222_; size_t v_stop_boxed_3223_; lean_object* v_res_3224_; 
v___x_9506__boxed_3220_ = lean_unbox(v___x_3214_);
v___x_9507__boxed_3221_ = lean_unbox(v___x_3215_);
v_i_boxed_3222_ = lean_unbox_usize(v_i_3217_);
lean_dec(v_i_3217_);
v_stop_boxed_3223_ = lean_unbox_usize(v_stop_3218_);
lean_dec(v_stop_3218_);
v_res_3224_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__4(v___x_9506__boxed_3220_, v___x_9507__boxed_3221_, v_as_3216_, v_i_boxed_3222_, v_stop_boxed_3223_, v_b_3219_);
lean_dec_ref(v_as_3216_);
return v_res_3224_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__3___redArg(lean_object* v_a_3225_, lean_object* v_b_3226_, lean_object* v_x_3227_){
_start:
{
if (lean_obj_tag(v_x_3227_) == 0)
{
lean_dec(v_b_3226_);
lean_dec_ref(v_a_3225_);
return v_x_3227_;
}
else
{
lean_object* v_key_3228_; lean_object* v_value_3229_; lean_object* v_tail_3230_; lean_object* v___x_3232_; uint8_t v_isShared_3233_; uint8_t v_isSharedCheck_3242_; 
v_key_3228_ = lean_ctor_get(v_x_3227_, 0);
v_value_3229_ = lean_ctor_get(v_x_3227_, 1);
v_tail_3230_ = lean_ctor_get(v_x_3227_, 2);
v_isSharedCheck_3242_ = !lean_is_exclusive(v_x_3227_);
if (v_isSharedCheck_3242_ == 0)
{
v___x_3232_ = v_x_3227_;
v_isShared_3233_ = v_isSharedCheck_3242_;
goto v_resetjp_3231_;
}
else
{
lean_inc(v_tail_3230_);
lean_inc(v_value_3229_);
lean_inc(v_key_3228_);
lean_dec(v_x_3227_);
v___x_3232_ = lean_box(0);
v_isShared_3233_ = v_isSharedCheck_3242_;
goto v_resetjp_3231_;
}
v_resetjp_3231_:
{
uint8_t v___x_3234_; 
v___x_3234_ = l_Lean_Elab_Tactic_Grind_instBEqSimpCacheKey_beq(v_key_3228_, v_a_3225_);
if (v___x_3234_ == 0)
{
lean_object* v___x_3235_; lean_object* v___x_3237_; 
v___x_3235_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__3___redArg(v_a_3225_, v_b_3226_, v_tail_3230_);
if (v_isShared_3233_ == 0)
{
lean_ctor_set(v___x_3232_, 2, v___x_3235_);
v___x_3237_ = v___x_3232_;
goto v_reusejp_3236_;
}
else
{
lean_object* v_reuseFailAlloc_3238_; 
v_reuseFailAlloc_3238_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3238_, 0, v_key_3228_);
lean_ctor_set(v_reuseFailAlloc_3238_, 1, v_value_3229_);
lean_ctor_set(v_reuseFailAlloc_3238_, 2, v___x_3235_);
v___x_3237_ = v_reuseFailAlloc_3238_;
goto v_reusejp_3236_;
}
v_reusejp_3236_:
{
return v___x_3237_;
}
}
else
{
lean_object* v___x_3240_; 
lean_dec(v_value_3229_);
lean_dec(v_key_3228_);
if (v_isShared_3233_ == 0)
{
lean_ctor_set(v___x_3232_, 1, v_b_3226_);
lean_ctor_set(v___x_3232_, 0, v_a_3225_);
v___x_3240_ = v___x_3232_;
goto v_reusejp_3239_;
}
else
{
lean_object* v_reuseFailAlloc_3241_; 
v_reuseFailAlloc_3241_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3241_, 0, v_a_3225_);
lean_ctor_set(v_reuseFailAlloc_3241_, 1, v_b_3226_);
lean_ctor_set(v_reuseFailAlloc_3241_, 2, v_tail_3230_);
v___x_3240_ = v_reuseFailAlloc_3241_;
goto v_reusejp_3239_;
}
v_reusejp_3239_:
{
return v___x_3240_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__2_spec__3_spec__7___redArg(lean_object* v_x_3243_, lean_object* v_x_3244_){
_start:
{
if (lean_obj_tag(v_x_3244_) == 0)
{
return v_x_3243_;
}
else
{
lean_object* v_key_3245_; lean_object* v_value_3246_; lean_object* v_tail_3247_; lean_object* v___x_3249_; uint8_t v_isShared_3250_; uint8_t v_isSharedCheck_3270_; 
v_key_3245_ = lean_ctor_get(v_x_3244_, 0);
v_value_3246_ = lean_ctor_get(v_x_3244_, 1);
v_tail_3247_ = lean_ctor_get(v_x_3244_, 2);
v_isSharedCheck_3270_ = !lean_is_exclusive(v_x_3244_);
if (v_isSharedCheck_3270_ == 0)
{
v___x_3249_ = v_x_3244_;
v_isShared_3250_ = v_isSharedCheck_3270_;
goto v_resetjp_3248_;
}
else
{
lean_inc(v_tail_3247_);
lean_inc(v_value_3246_);
lean_inc(v_key_3245_);
lean_dec(v_x_3244_);
v___x_3249_ = lean_box(0);
v_isShared_3250_ = v_isSharedCheck_3270_;
goto v_resetjp_3248_;
}
v_resetjp_3248_:
{
lean_object* v___x_3251_; uint64_t v___x_3252_; uint64_t v___x_3253_; uint64_t v___x_3254_; uint64_t v_fold_3255_; uint64_t v___x_3256_; uint64_t v___x_3257_; uint64_t v___x_3258_; size_t v___x_3259_; size_t v___x_3260_; size_t v___x_3261_; size_t v___x_3262_; size_t v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3266_; 
v___x_3251_ = lean_array_get_size(v_x_3243_);
v___x_3252_ = l_Lean_Elab_Tactic_Grind_instHashableSimpCacheKey_hash(v_key_3245_);
v___x_3253_ = 32ULL;
v___x_3254_ = lean_uint64_shift_right(v___x_3252_, v___x_3253_);
v_fold_3255_ = lean_uint64_xor(v___x_3252_, v___x_3254_);
v___x_3256_ = 16ULL;
v___x_3257_ = lean_uint64_shift_right(v_fold_3255_, v___x_3256_);
v___x_3258_ = lean_uint64_xor(v_fold_3255_, v___x_3257_);
v___x_3259_ = lean_uint64_to_usize(v___x_3258_);
v___x_3260_ = lean_usize_of_nat(v___x_3251_);
v___x_3261_ = ((size_t)1ULL);
v___x_3262_ = lean_usize_sub(v___x_3260_, v___x_3261_);
v___x_3263_ = lean_usize_land(v___x_3259_, v___x_3262_);
v___x_3264_ = lean_array_uget_borrowed(v_x_3243_, v___x_3263_);
lean_inc(v___x_3264_);
if (v_isShared_3250_ == 0)
{
lean_ctor_set(v___x_3249_, 2, v___x_3264_);
v___x_3266_ = v___x_3249_;
goto v_reusejp_3265_;
}
else
{
lean_object* v_reuseFailAlloc_3269_; 
v_reuseFailAlloc_3269_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3269_, 0, v_key_3245_);
lean_ctor_set(v_reuseFailAlloc_3269_, 1, v_value_3246_);
lean_ctor_set(v_reuseFailAlloc_3269_, 2, v___x_3264_);
v___x_3266_ = v_reuseFailAlloc_3269_;
goto v_reusejp_3265_;
}
v_reusejp_3265_:
{
lean_object* v___x_3267_; 
v___x_3267_ = lean_array_uset(v_x_3243_, v___x_3263_, v___x_3266_);
v_x_3243_ = v___x_3267_;
v_x_3244_ = v_tail_3247_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__2_spec__3___redArg(lean_object* v_i_3271_, lean_object* v_source_3272_, lean_object* v_target_3273_){
_start:
{
lean_object* v___x_3274_; uint8_t v___x_3275_; 
v___x_3274_ = lean_array_get_size(v_source_3272_);
v___x_3275_ = lean_nat_dec_lt(v_i_3271_, v___x_3274_);
if (v___x_3275_ == 0)
{
lean_dec_ref(v_source_3272_);
lean_dec(v_i_3271_);
return v_target_3273_;
}
else
{
lean_object* v_es_3276_; lean_object* v___x_3277_; lean_object* v_source_3278_; lean_object* v_target_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; 
v_es_3276_ = lean_array_fget(v_source_3272_, v_i_3271_);
v___x_3277_ = lean_box(0);
v_source_3278_ = lean_array_fset(v_source_3272_, v_i_3271_, v___x_3277_);
v_target_3279_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__2_spec__3_spec__7___redArg(v_target_3273_, v_es_3276_);
v___x_3280_ = lean_unsigned_to_nat(1u);
v___x_3281_ = lean_nat_add(v_i_3271_, v___x_3280_);
lean_dec(v_i_3271_);
v_i_3271_ = v___x_3281_;
v_source_3272_ = v_source_3278_;
v_target_3273_ = v_target_3279_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__2___redArg(lean_object* v_data_3283_){
_start:
{
lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v_nbuckets_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; 
v___x_3284_ = lean_array_get_size(v_data_3283_);
v___x_3285_ = lean_unsigned_to_nat(2u);
v_nbuckets_3286_ = lean_nat_mul(v___x_3284_, v___x_3285_);
v___x_3287_ = lean_unsigned_to_nat(0u);
v___x_3288_ = lean_box(0);
v___x_3289_ = lean_mk_array(v_nbuckets_3286_, v___x_3288_);
v___x_3290_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__2_spec__3___redArg(v___x_3287_, v_data_3283_, v___x_3289_);
return v___x_3290_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__1___redArg(lean_object* v_a_3291_, lean_object* v_x_3292_){
_start:
{
if (lean_obj_tag(v_x_3292_) == 0)
{
uint8_t v___x_3293_; 
v___x_3293_ = 0;
return v___x_3293_;
}
else
{
lean_object* v_key_3294_; lean_object* v_tail_3295_; uint8_t v___x_3296_; 
v_key_3294_ = lean_ctor_get(v_x_3292_, 0);
v_tail_3295_ = lean_ctor_get(v_x_3292_, 2);
v___x_3296_ = l_Lean_Elab_Tactic_Grind_instBEqSimpCacheKey_beq(v_key_3294_, v_a_3291_);
if (v___x_3296_ == 0)
{
v_x_3292_ = v_tail_3295_;
goto _start;
}
else
{
return v___x_3296_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__1___redArg___boxed(lean_object* v_a_3298_, lean_object* v_x_3299_){
_start:
{
uint8_t v_res_3300_; lean_object* v_r_3301_; 
v_res_3300_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__1___redArg(v_a_3298_, v_x_3299_);
lean_dec(v_x_3299_);
lean_dec_ref(v_a_3298_);
v_r_3301_ = lean_box(v_res_3300_);
return v_r_3301_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1___redArg(lean_object* v_m_3302_, lean_object* v_a_3303_, lean_object* v_b_3304_){
_start:
{
lean_object* v_size_3305_; lean_object* v_buckets_3306_; lean_object* v___x_3308_; uint8_t v_isShared_3309_; uint8_t v_isSharedCheck_3349_; 
v_size_3305_ = lean_ctor_get(v_m_3302_, 0);
v_buckets_3306_ = lean_ctor_get(v_m_3302_, 1);
v_isSharedCheck_3349_ = !lean_is_exclusive(v_m_3302_);
if (v_isSharedCheck_3349_ == 0)
{
v___x_3308_ = v_m_3302_;
v_isShared_3309_ = v_isSharedCheck_3349_;
goto v_resetjp_3307_;
}
else
{
lean_inc(v_buckets_3306_);
lean_inc(v_size_3305_);
lean_dec(v_m_3302_);
v___x_3308_ = lean_box(0);
v_isShared_3309_ = v_isSharedCheck_3349_;
goto v_resetjp_3307_;
}
v_resetjp_3307_:
{
lean_object* v___x_3310_; uint64_t v___x_3311_; uint64_t v___x_3312_; uint64_t v___x_3313_; uint64_t v_fold_3314_; uint64_t v___x_3315_; uint64_t v___x_3316_; uint64_t v___x_3317_; size_t v___x_3318_; size_t v___x_3319_; size_t v___x_3320_; size_t v___x_3321_; size_t v___x_3322_; lean_object* v_bkt_3323_; uint8_t v___x_3324_; 
v___x_3310_ = lean_array_get_size(v_buckets_3306_);
v___x_3311_ = l_Lean_Elab_Tactic_Grind_instHashableSimpCacheKey_hash(v_a_3303_);
v___x_3312_ = 32ULL;
v___x_3313_ = lean_uint64_shift_right(v___x_3311_, v___x_3312_);
v_fold_3314_ = lean_uint64_xor(v___x_3311_, v___x_3313_);
v___x_3315_ = 16ULL;
v___x_3316_ = lean_uint64_shift_right(v_fold_3314_, v___x_3315_);
v___x_3317_ = lean_uint64_xor(v_fold_3314_, v___x_3316_);
v___x_3318_ = lean_uint64_to_usize(v___x_3317_);
v___x_3319_ = lean_usize_of_nat(v___x_3310_);
v___x_3320_ = ((size_t)1ULL);
v___x_3321_ = lean_usize_sub(v___x_3319_, v___x_3320_);
v___x_3322_ = lean_usize_land(v___x_3318_, v___x_3321_);
v_bkt_3323_ = lean_array_uget_borrowed(v_buckets_3306_, v___x_3322_);
v___x_3324_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__1___redArg(v_a_3303_, v_bkt_3323_);
if (v___x_3324_ == 0)
{
lean_object* v___x_3325_; lean_object* v_size_x27_3326_; lean_object* v___x_3327_; lean_object* v_buckets_x27_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; uint8_t v___x_3334_; 
v___x_3325_ = lean_unsigned_to_nat(1u);
v_size_x27_3326_ = lean_nat_add(v_size_3305_, v___x_3325_);
lean_dec(v_size_3305_);
lean_inc(v_bkt_3323_);
v___x_3327_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3327_, 0, v_a_3303_);
lean_ctor_set(v___x_3327_, 1, v_b_3304_);
lean_ctor_set(v___x_3327_, 2, v_bkt_3323_);
v_buckets_x27_3328_ = lean_array_uset(v_buckets_3306_, v___x_3322_, v___x_3327_);
v___x_3329_ = lean_unsigned_to_nat(4u);
v___x_3330_ = lean_nat_mul(v_size_x27_3326_, v___x_3329_);
v___x_3331_ = lean_unsigned_to_nat(3u);
v___x_3332_ = lean_nat_div(v___x_3330_, v___x_3331_);
lean_dec(v___x_3330_);
v___x_3333_ = lean_array_get_size(v_buckets_x27_3328_);
v___x_3334_ = lean_nat_dec_le(v___x_3332_, v___x_3333_);
lean_dec(v___x_3332_);
if (v___x_3334_ == 0)
{
lean_object* v_val_3335_; lean_object* v___x_3337_; 
v_val_3335_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__2___redArg(v_buckets_x27_3328_);
if (v_isShared_3309_ == 0)
{
lean_ctor_set(v___x_3308_, 1, v_val_3335_);
lean_ctor_set(v___x_3308_, 0, v_size_x27_3326_);
v___x_3337_ = v___x_3308_;
goto v_reusejp_3336_;
}
else
{
lean_object* v_reuseFailAlloc_3338_; 
v_reuseFailAlloc_3338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3338_, 0, v_size_x27_3326_);
lean_ctor_set(v_reuseFailAlloc_3338_, 1, v_val_3335_);
v___x_3337_ = v_reuseFailAlloc_3338_;
goto v_reusejp_3336_;
}
v_reusejp_3336_:
{
return v___x_3337_;
}
}
else
{
lean_object* v___x_3340_; 
if (v_isShared_3309_ == 0)
{
lean_ctor_set(v___x_3308_, 1, v_buckets_x27_3328_);
lean_ctor_set(v___x_3308_, 0, v_size_x27_3326_);
v___x_3340_ = v___x_3308_;
goto v_reusejp_3339_;
}
else
{
lean_object* v_reuseFailAlloc_3341_; 
v_reuseFailAlloc_3341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3341_, 0, v_size_x27_3326_);
lean_ctor_set(v_reuseFailAlloc_3341_, 1, v_buckets_x27_3328_);
v___x_3340_ = v_reuseFailAlloc_3341_;
goto v_reusejp_3339_;
}
v_reusejp_3339_:
{
return v___x_3340_;
}
}
}
else
{
lean_object* v___x_3342_; lean_object* v_buckets_x27_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3347_; 
lean_inc(v_bkt_3323_);
v___x_3342_ = lean_box(0);
v_buckets_x27_3343_ = lean_array_uset(v_buckets_3306_, v___x_3322_, v___x_3342_);
v___x_3344_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__3___redArg(v_a_3303_, v_b_3304_, v_bkt_3323_);
v___x_3345_ = lean_array_uset(v_buckets_x27_3343_, v___x_3322_, v___x_3344_);
if (v_isShared_3309_ == 0)
{
lean_ctor_set(v___x_3308_, 1, v___x_3345_);
v___x_3347_ = v___x_3308_;
goto v_reusejp_3346_;
}
else
{
lean_object* v_reuseFailAlloc_3348_; 
v_reuseFailAlloc_3348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3348_, 0, v_size_3305_);
lean_ctor_set(v_reuseFailAlloc_3348_, 1, v___x_3345_);
v___x_3347_ = v_reuseFailAlloc_3348_;
goto v_reusejp_3346_;
}
v_reusejp_3346_:
{
return v___x_3347_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__3(size_t v_sz_3350_, size_t v_i_3351_, lean_object* v_bs_3352_){
_start:
{
uint8_t v___x_3353_; 
v___x_3353_ = lean_usize_dec_lt(v_i_3351_, v_sz_3350_);
if (v___x_3353_ == 0)
{
lean_object* v___x_3354_; 
v___x_3354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3354_, 0, v_bs_3352_);
return v___x_3354_;
}
else
{
lean_object* v_v_3355_; lean_object* v___x_3356_; lean_object* v_bs_x27_3357_; size_t v___x_3358_; size_t v___x_3359_; lean_object* v___x_3360_; 
v_v_3355_ = lean_array_uget(v_bs_3352_, v_i_3351_);
v___x_3356_ = lean_unsigned_to_nat(0u);
v_bs_x27_3357_ = lean_array_uset(v_bs_3352_, v_i_3351_, v___x_3356_);
v___x_3358_ = ((size_t)1ULL);
v___x_3359_ = lean_usize_add(v_i_3351_, v___x_3358_);
v___x_3360_ = lean_array_uset(v_bs_x27_3357_, v_i_3351_, v_v_3355_);
v_i_3351_ = v___x_3359_;
v_bs_3352_ = v___x_3360_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__3___boxed(lean_object* v_sz_3362_, lean_object* v_i_3363_, lean_object* v_bs_3364_){
_start:
{
size_t v_sz_boxed_3365_; size_t v_i_boxed_3366_; lean_object* v_res_3367_; 
v_sz_boxed_3365_ = lean_unbox_usize(v_sz_3362_);
lean_dec(v_sz_3362_);
v_i_boxed_3366_ = lean_unbox_usize(v_i_3363_);
lean_dec(v_i_3363_);
v_res_3367_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__3(v_sz_boxed_3365_, v_i_boxed_3366_, v_bs_3364_);
return v_res_3367_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__1(void){
_start:
{
lean_object* v___x_3369_; lean_object* v___x_3370_; 
v___x_3369_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__0));
v___x_3370_ = l_Lean_stringToMessageData(v___x_3369_);
return v___x_3370_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__4(void){
_start:
{
lean_object* v___x_3378_; 
v___x_3378_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3378_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__5(void){
_start:
{
lean_object* v___x_3379_; lean_object* v___x_3380_; 
v___x_3379_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__4, &l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__4_once, _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__4);
v___x_3380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3380_, 0, v___x_3379_);
return v___x_3380_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__6(void){
_start:
{
lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; 
v___x_3381_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__5, &l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__5);
v___x_3382_ = lean_unsigned_to_nat(0u);
v___x_3383_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3383_, 0, v___x_3382_);
lean_ctor_set(v___x_3383_, 1, v___x_3381_);
lean_ctor_set(v___x_3383_, 2, v___x_3381_);
lean_ctor_set(v___x_3383_, 3, v___x_3381_);
return v___x_3383_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2(lean_object* v_stx_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_, lean_object* v___y_3394_){
_start:
{
lean_object* v___y_3397_; lean_object* v___y_3398_; lean_object* v___y_3399_; lean_object* v___y_3400_; lean_object* v___y_3401_; lean_object* v___y_3402_; lean_object* v___y_3403_; lean_object* v___y_3404_; lean_object* v___y_3405_; lean_object* v___y_3406_; lean_object* v___y_3407_; lean_object* v___y_3408_; lean_object* v___x_3504_; 
v___x_3504_ = l_Lean_Elab_Tactic_Grind_ensureSym___redArg(v___y_3387_, v___y_3391_, v___y_3392_, v___y_3393_, v___y_3394_);
if (lean_obj_tag(v___x_3504_) == 0)
{
lean_object* v___x_3506_; uint8_t v_isShared_3507_; uint8_t v_isSharedCheck_3620_; 
v_isSharedCheck_3620_ = !lean_is_exclusive(v___x_3504_);
if (v_isSharedCheck_3620_ == 0)
{
lean_object* v_unused_3621_; 
v_unused_3621_ = lean_ctor_get(v___x_3504_, 0);
lean_dec(v_unused_3621_);
v___x_3506_ = v___x_3504_;
v_isShared_3507_ = v_isSharedCheck_3620_;
goto v_resetjp_3505_;
}
else
{
lean_dec(v___x_3504_);
v___x_3506_ = lean_box(0);
v_isShared_3507_ = v_isSharedCheck_3620_;
goto v_resetjp_3505_;
}
v_resetjp_3505_:
{
lean_object* v___x_3508_; uint8_t v___x_3509_; 
v___x_3508_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__3));
lean_inc(v_stx_3386_);
v___x_3509_ = l_Lean_Syntax_isOfKind(v_stx_3386_, v___x_3508_);
if (v___x_3509_ == 0)
{
lean_object* v___x_3510_; 
lean_del_object(v___x_3506_);
lean_dec(v_stx_3386_);
v___x_3510_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro_spec__0___redArg();
return v___x_3510_;
}
else
{
lean_object* v___x_3511_; lean_object* v___y_3513_; lean_object* v___y_3514_; lean_object* v___y_3515_; lean_object* v___y_3516_; lean_object* v___y_3517_; lean_object* v___y_3518_; lean_object* v___y_3519_; lean_object* v___y_3520_; lean_object* v___y_3521_; lean_object* v___y_3522_; lean_object* v___y_3549_; lean_object* v_extraIds_3550_; lean_object* v___y_3551_; lean_object* v___y_3552_; lean_object* v___y_3553_; lean_object* v___y_3554_; lean_object* v___y_3555_; lean_object* v___y_3556_; lean_object* v___y_3557_; lean_object* v___y_3558_; lean_object* v___y_3563_; lean_object* v___y_3564_; lean_object* v___y_3565_; lean_object* v___y_3566_; lean_object* v___y_3567_; lean_object* v___y_3568_; lean_object* v___y_3569_; lean_object* v___y_3570_; lean_object* v___y_3571_; lean_object* v___y_3572_; lean_object* v___x_3577_; lean_object* v_variantId_x3f_3579_; lean_object* v___y_3580_; lean_object* v___y_3581_; lean_object* v___y_3582_; lean_object* v___y_3583_; lean_object* v___y_3584_; lean_object* v___y_3585_; lean_object* v___y_3586_; lean_object* v___y_3587_; lean_object* v___x_3611_; uint8_t v___x_3612_; 
v___x_3511_ = lean_unsigned_to_nat(0u);
v___x_3577_ = lean_unsigned_to_nat(1u);
v___x_3611_ = l_Lean_Syntax_getArg(v_stx_3386_, v___x_3577_);
v___x_3612_ = l_Lean_Syntax_isNone(v___x_3611_);
if (v___x_3612_ == 0)
{
uint8_t v___x_3613_; 
lean_inc(v___x_3611_);
v___x_3613_ = l_Lean_Syntax_matchesNull(v___x_3611_, v___x_3577_);
if (v___x_3613_ == 0)
{
lean_object* v___x_3614_; 
lean_dec(v___x_3611_);
lean_del_object(v___x_3506_);
lean_dec(v_stx_3386_);
v___x_3614_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro_spec__0___redArg();
return v___x_3614_;
}
else
{
lean_object* v___x_3615_; lean_object* v___x_3617_; 
v___x_3615_ = l_Lean_Syntax_getArg(v___x_3611_, v___x_3511_);
lean_dec(v___x_3611_);
if (v_isShared_3507_ == 0)
{
lean_ctor_set_tag(v___x_3506_, 1);
lean_ctor_set(v___x_3506_, 0, v___x_3615_);
v___x_3617_ = v___x_3506_;
goto v_reusejp_3616_;
}
else
{
lean_object* v_reuseFailAlloc_3618_; 
v_reuseFailAlloc_3618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3618_, 0, v___x_3615_);
v___x_3617_ = v_reuseFailAlloc_3618_;
goto v_reusejp_3616_;
}
v_reusejp_3616_:
{
v_variantId_x3f_3579_ = v___x_3617_;
v___y_3580_ = v___y_3387_;
v___y_3581_ = v___y_3388_;
v___y_3582_ = v___y_3389_;
v___y_3583_ = v___y_3390_;
v___y_3584_ = v___y_3391_;
v___y_3585_ = v___y_3392_;
v___y_3586_ = v___y_3393_;
v___y_3587_ = v___y_3394_;
goto v___jp_3578_;
}
}
}
else
{
lean_object* v___x_3619_; 
lean_dec(v___x_3611_);
lean_del_object(v___x_3506_);
v___x_3619_ = lean_box(0);
v_variantId_x3f_3579_ = v___x_3619_;
v___y_3580_ = v___y_3387_;
v___y_3581_ = v___y_3388_;
v___y_3582_ = v___y_3389_;
v___y_3583_ = v___y_3390_;
v___y_3584_ = v___y_3391_;
v___y_3585_ = v___y_3392_;
v___y_3586_ = v___y_3393_;
v___y_3587_ = v___y_3394_;
goto v___jp_3578_;
}
v___jp_3512_:
{
lean_object* v___x_3523_; 
v___x_3523_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems(v___y_3520_, v___y_3518_, v___y_3516_, v___y_3519_, v___y_3517_, v___y_3521_, v___y_3515_, v___y_3514_, v___y_3513_);
lean_dec(v___y_3520_);
if (lean_obj_tag(v___x_3523_) == 0)
{
lean_object* v_a_3524_; lean_object* v_fst_3525_; lean_object* v_snd_3526_; lean_object* v___x_3528_; uint8_t v_isShared_3529_; uint8_t v_isSharedCheck_3539_; 
v_a_3524_ = lean_ctor_get(v___x_3523_, 0);
lean_inc(v_a_3524_);
lean_dec_ref_known(v___x_3523_, 1);
v_fst_3525_ = lean_ctor_get(v_a_3524_, 0);
v_snd_3526_ = lean_ctor_get(v_a_3524_, 1);
v_isSharedCheck_3539_ = !lean_is_exclusive(v_a_3524_);
if (v_isSharedCheck_3539_ == 0)
{
v___x_3528_ = v_a_3524_;
v_isShared_3529_ = v_isSharedCheck_3539_;
goto v_resetjp_3527_;
}
else
{
lean_inc(v_snd_3526_);
lean_inc(v_fst_3525_);
lean_dec(v_a_3524_);
v___x_3528_ = lean_box(0);
v_isShared_3529_ = v_isSharedCheck_3539_;
goto v_resetjp_3527_;
}
v_resetjp_3527_:
{
lean_object* v___x_3530_; lean_object* v_cache_3531_; lean_object* v_simpState_3532_; lean_object* v___x_3534_; 
v___x_3530_ = lean_st_ref_get(v___y_3516_);
v_cache_3531_ = lean_ctor_get(v___x_3530_, 3);
lean_inc_ref(v_cache_3531_);
lean_dec(v___x_3530_);
v_simpState_3532_ = lean_ctor_get(v_cache_3531_, 2);
lean_inc_ref(v_simpState_3532_);
lean_dec_ref(v_cache_3531_);
lean_inc(v___y_3522_);
if (v_isShared_3529_ == 0)
{
lean_ctor_set(v___x_3528_, 1, v_fst_3525_);
lean_ctor_set(v___x_3528_, 0, v___y_3522_);
v___x_3534_ = v___x_3528_;
goto v_reusejp_3533_;
}
else
{
lean_object* v_reuseFailAlloc_3538_; 
v_reuseFailAlloc_3538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3538_, 0, v___y_3522_);
lean_ctor_set(v_reuseFailAlloc_3538_, 1, v_fst_3525_);
v___x_3534_ = v_reuseFailAlloc_3538_;
goto v_reusejp_3533_;
}
v_reusejp_3533_:
{
lean_object* v___x_3535_; 
v___x_3535_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__2___redArg(v_simpState_3532_, v___x_3534_);
lean_dec_ref(v_simpState_3532_);
if (lean_obj_tag(v___x_3535_) == 0)
{
lean_object* v___x_3536_; 
v___x_3536_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__6, &l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__6_once, _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__6);
v___y_3397_ = v___y_3513_;
v___y_3398_ = v___y_3514_;
v___y_3399_ = v_snd_3526_;
v___y_3400_ = v___y_3515_;
v___y_3401_ = v___y_3516_;
v___y_3402_ = v___y_3517_;
v___y_3403_ = v___y_3518_;
v___y_3404_ = v___y_3519_;
v___y_3405_ = v___x_3534_;
v___y_3406_ = v___y_3521_;
v___y_3407_ = v___y_3522_;
v___y_3408_ = v___x_3536_;
goto v___jp_3396_;
}
else
{
lean_object* v_val_3537_; 
v_val_3537_ = lean_ctor_get(v___x_3535_, 0);
lean_inc(v_val_3537_);
lean_dec_ref_known(v___x_3535_, 1);
v___y_3397_ = v___y_3513_;
v___y_3398_ = v___y_3514_;
v___y_3399_ = v_snd_3526_;
v___y_3400_ = v___y_3515_;
v___y_3401_ = v___y_3516_;
v___y_3402_ = v___y_3517_;
v___y_3403_ = v___y_3518_;
v___y_3404_ = v___y_3519_;
v___y_3405_ = v___x_3534_;
v___y_3406_ = v___y_3521_;
v___y_3407_ = v___y_3522_;
v___y_3408_ = v_val_3537_;
goto v___jp_3396_;
}
}
}
}
else
{
lean_object* v_a_3540_; lean_object* v___x_3542_; uint8_t v_isShared_3543_; uint8_t v_isSharedCheck_3547_; 
lean_dec(v___y_3522_);
v_a_3540_ = lean_ctor_get(v___x_3523_, 0);
v_isSharedCheck_3547_ = !lean_is_exclusive(v___x_3523_);
if (v_isSharedCheck_3547_ == 0)
{
v___x_3542_ = v___x_3523_;
v_isShared_3543_ = v_isSharedCheck_3547_;
goto v_resetjp_3541_;
}
else
{
lean_inc(v_a_3540_);
lean_dec(v___x_3523_);
v___x_3542_ = lean_box(0);
v_isShared_3543_ = v_isSharedCheck_3547_;
goto v_resetjp_3541_;
}
v_resetjp_3541_:
{
lean_object* v___x_3545_; 
if (v_isShared_3543_ == 0)
{
v___x_3545_ = v___x_3542_;
goto v_reusejp_3544_;
}
else
{
lean_object* v_reuseFailAlloc_3546_; 
v_reuseFailAlloc_3546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3546_, 0, v_a_3540_);
v___x_3545_ = v_reuseFailAlloc_3546_;
goto v_reusejp_3544_;
}
v_reusejp_3544_:
{
return v___x_3545_;
}
}
}
}
v___jp_3548_:
{
if (lean_obj_tag(v___y_3549_) == 0)
{
lean_object* v___x_3559_; 
v___x_3559_ = lean_box(0);
v___y_3513_ = v___y_3558_;
v___y_3514_ = v___y_3557_;
v___y_3515_ = v___y_3556_;
v___y_3516_ = v___y_3552_;
v___y_3517_ = v___y_3554_;
v___y_3518_ = v___y_3551_;
v___y_3519_ = v___y_3553_;
v___y_3520_ = v_extraIds_3550_;
v___y_3521_ = v___y_3555_;
v___y_3522_ = v___x_3559_;
goto v___jp_3512_;
}
else
{
lean_object* v_val_3560_; lean_object* v___x_3561_; 
v_val_3560_ = lean_ctor_get(v___y_3549_, 0);
lean_inc(v_val_3560_);
lean_dec_ref_known(v___y_3549_, 1);
v___x_3561_ = l_Lean_TSyntax_getId(v_val_3560_);
lean_dec(v_val_3560_);
v___y_3513_ = v___y_3558_;
v___y_3514_ = v___y_3557_;
v___y_3515_ = v___y_3556_;
v___y_3516_ = v___y_3552_;
v___y_3517_ = v___y_3554_;
v___y_3518_ = v___y_3551_;
v___y_3519_ = v___y_3553_;
v___y_3520_ = v_extraIds_3550_;
v___y_3521_ = v___y_3555_;
v___y_3522_ = v___x_3561_;
goto v___jp_3512_;
}
}
v___jp_3562_:
{
size_t v_sz_3573_; size_t v___x_3574_; lean_object* v___x_3575_; 
v_sz_3573_ = lean_array_size(v___y_3572_);
v___x_3574_ = ((size_t)0ULL);
v___x_3575_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__3(v_sz_3573_, v___x_3574_, v___y_3572_);
if (lean_obj_tag(v___x_3575_) == 0)
{
lean_object* v___x_3576_; 
lean_dec(v___y_3571_);
v___x_3576_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro_spec__0___redArg();
return v___x_3576_;
}
else
{
v___y_3549_ = v___y_3571_;
v_extraIds_3550_ = v___x_3575_;
v___y_3551_ = v___y_3567_;
v___y_3552_ = v___y_3566_;
v___y_3553_ = v___y_3565_;
v___y_3554_ = v___y_3568_;
v___y_3555_ = v___y_3564_;
v___y_3556_ = v___y_3570_;
v___y_3557_ = v___y_3569_;
v___y_3558_ = v___y_3563_;
goto v___jp_3548_;
}
}
v___jp_3578_:
{
lean_object* v___x_3588_; lean_object* v___x_3589_; uint8_t v___x_3590_; 
v___x_3588_ = lean_unsigned_to_nat(2u);
v___x_3589_ = l_Lean_Syntax_getArg(v_stx_3386_, v___x_3588_);
lean_dec(v_stx_3386_);
v___x_3590_ = l_Lean_Syntax_isNone(v___x_3589_);
if (v___x_3590_ == 0)
{
lean_object* v___x_3591_; uint8_t v___x_3592_; 
v___x_3591_ = lean_unsigned_to_nat(3u);
lean_inc(v___x_3589_);
v___x_3592_ = l_Lean_Syntax_matchesNull(v___x_3589_, v___x_3591_);
if (v___x_3592_ == 0)
{
lean_object* v___x_3593_; 
lean_dec(v___x_3589_);
lean_dec(v_variantId_x3f_3579_);
v___x_3593_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro_spec__0___redArg();
return v___x_3593_;
}
else
{
lean_object* v___x_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; uint8_t v___x_3598_; 
v___x_3594_ = l_Lean_Syntax_getArg(v___x_3589_, v___x_3577_);
lean_dec(v___x_3589_);
v___x_3595_ = l_Lean_Syntax_getArgs(v___x_3594_);
lean_dec(v___x_3594_);
v___x_3596_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__7));
v___x_3597_ = lean_array_get_size(v___x_3595_);
v___x_3598_ = lean_nat_dec_lt(v___x_3511_, v___x_3597_);
if (v___x_3598_ == 0)
{
lean_dec_ref(v___x_3595_);
v___y_3563_ = v___y_3587_;
v___y_3564_ = v___y_3584_;
v___y_3565_ = v___y_3582_;
v___y_3566_ = v___y_3581_;
v___y_3567_ = v___y_3580_;
v___y_3568_ = v___y_3583_;
v___y_3569_ = v___y_3586_;
v___y_3570_ = v___y_3585_;
v___y_3571_ = v_variantId_x3f_3579_;
v___y_3572_ = v___x_3596_;
goto v___jp_3562_;
}
else
{
lean_object* v___x_3599_; lean_object* v___x_3600_; uint8_t v___x_3601_; 
v___x_3599_ = lean_box(v___x_3592_);
v___x_3600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3600_, 0, v___x_3599_);
lean_ctor_set(v___x_3600_, 1, v___x_3596_);
v___x_3601_ = lean_nat_dec_le(v___x_3597_, v___x_3597_);
if (v___x_3601_ == 0)
{
if (v___x_3598_ == 0)
{
lean_dec_ref_known(v___x_3600_, 2);
lean_dec_ref(v___x_3595_);
v___y_3563_ = v___y_3587_;
v___y_3564_ = v___y_3584_;
v___y_3565_ = v___y_3582_;
v___y_3566_ = v___y_3581_;
v___y_3567_ = v___y_3580_;
v___y_3568_ = v___y_3583_;
v___y_3569_ = v___y_3586_;
v___y_3570_ = v___y_3585_;
v___y_3571_ = v_variantId_x3f_3579_;
v___y_3572_ = v___x_3596_;
goto v___jp_3562_;
}
else
{
size_t v___x_3602_; size_t v___x_3603_; lean_object* v___x_3604_; lean_object* v_snd_3605_; 
v___x_3602_ = ((size_t)0ULL);
v___x_3603_ = lean_usize_of_nat(v___x_3597_);
v___x_3604_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__4(v___x_3592_, v___x_3590_, v___x_3595_, v___x_3602_, v___x_3603_, v___x_3600_);
lean_dec_ref(v___x_3595_);
v_snd_3605_ = lean_ctor_get(v___x_3604_, 1);
lean_inc(v_snd_3605_);
lean_dec_ref(v___x_3604_);
v___y_3563_ = v___y_3587_;
v___y_3564_ = v___y_3584_;
v___y_3565_ = v___y_3582_;
v___y_3566_ = v___y_3581_;
v___y_3567_ = v___y_3580_;
v___y_3568_ = v___y_3583_;
v___y_3569_ = v___y_3586_;
v___y_3570_ = v___y_3585_;
v___y_3571_ = v_variantId_x3f_3579_;
v___y_3572_ = v_snd_3605_;
goto v___jp_3562_;
}
}
else
{
size_t v___x_3606_; size_t v___x_3607_; lean_object* v___x_3608_; lean_object* v_snd_3609_; 
v___x_3606_ = ((size_t)0ULL);
v___x_3607_ = lean_usize_of_nat(v___x_3597_);
v___x_3608_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__4(v___x_3592_, v___x_3590_, v___x_3595_, v___x_3606_, v___x_3607_, v___x_3600_);
lean_dec_ref(v___x_3595_);
v_snd_3609_ = lean_ctor_get(v___x_3608_, 1);
lean_inc(v_snd_3609_);
lean_dec_ref(v___x_3608_);
v___y_3563_ = v___y_3587_;
v___y_3564_ = v___y_3584_;
v___y_3565_ = v___y_3582_;
v___y_3566_ = v___y_3581_;
v___y_3567_ = v___y_3580_;
v___y_3568_ = v___y_3583_;
v___y_3569_ = v___y_3586_;
v___y_3570_ = v___y_3585_;
v___y_3571_ = v_variantId_x3f_3579_;
v___y_3572_ = v_snd_3609_;
goto v___jp_3562_;
}
}
}
}
else
{
lean_object* v___x_3610_; 
lean_dec(v___x_3589_);
v___x_3610_ = lean_box(0);
v___y_3549_ = v_variantId_x3f_3579_;
v_extraIds_3550_ = v___x_3610_;
v___y_3551_ = v___y_3580_;
v___y_3552_ = v___y_3581_;
v___y_3553_ = v___y_3582_;
v___y_3554_ = v___y_3583_;
v___y_3555_ = v___y_3584_;
v___y_3556_ = v___y_3585_;
v___y_3557_ = v___y_3586_;
v___y_3558_ = v___y_3587_;
goto v___jp_3548_;
}
}
}
}
}
else
{
lean_dec(v_stx_3386_);
return v___x_3504_;
}
v___jp_3396_:
{
lean_object* v___x_3409_; 
v___x_3409_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabSimpVariant(v___y_3407_, v___y_3399_, v___y_3403_, v___y_3401_, v___y_3404_, v___y_3402_, v___y_3406_, v___y_3400_, v___y_3398_, v___y_3397_);
lean_dec_ref(v___y_3399_);
if (lean_obj_tag(v___x_3409_) == 0)
{
lean_object* v_a_3410_; lean_object* v_fst_3411_; lean_object* v_snd_3412_; lean_object* v___x_3413_; 
v_a_3410_ = lean_ctor_get(v___x_3409_, 0);
lean_inc(v_a_3410_);
lean_dec_ref_known(v___x_3409_, 1);
v_fst_3411_ = lean_ctor_get(v_a_3410_, 0);
lean_inc(v_fst_3411_);
v_snd_3412_ = lean_ctor_get(v_a_3410_, 1);
lean_inc(v_snd_3412_);
lean_dec(v_a_3410_);
v___x_3413_ = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(v___y_3401_, v___y_3406_, v___y_3400_, v___y_3398_, v___y_3397_);
if (lean_obj_tag(v___x_3413_) == 0)
{
lean_object* v_a_3414_; lean_object* v_toGoalState_3415_; lean_object* v_mvarId_3416_; lean_object* v___x_3418_; uint8_t v_isShared_3419_; uint8_t v_isSharedCheck_3487_; 
v_a_3414_ = lean_ctor_get(v___x_3413_, 0);
lean_inc(v_a_3414_);
lean_dec_ref_known(v___x_3413_, 1);
v_toGoalState_3415_ = lean_ctor_get(v_a_3414_, 0);
v_mvarId_3416_ = lean_ctor_get(v_a_3414_, 1);
v_isSharedCheck_3487_ = !lean_is_exclusive(v_a_3414_);
if (v_isSharedCheck_3487_ == 0)
{
v___x_3418_ = v_a_3414_;
v_isShared_3419_ = v_isSharedCheck_3487_;
goto v_resetjp_3417_;
}
else
{
lean_inc(v_mvarId_3416_);
lean_inc(v_toGoalState_3415_);
lean_dec(v_a_3414_);
v___x_3418_ = lean_box(0);
v_isShared_3419_ = v_isSharedCheck_3487_;
goto v_resetjp_3417_;
}
v_resetjp_3417_:
{
lean_object* v___f_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; 
lean_inc_n(v_mvarId_3416_, 2);
v___f_3420_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__0___boxed), 14, 4);
lean_closure_set(v___f_3420_, 0, v_mvarId_3416_);
lean_closure_set(v___f_3420_, 1, v_fst_3411_);
lean_closure_set(v___f_3420_, 2, v_snd_3412_);
lean_closure_set(v___f_3420_, 3, v___y_3408_);
v___x_3421_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__0___boxed), 13, 3);
lean_closure_set(v___x_3421_, 0, lean_box(0));
lean_closure_set(v___x_3421_, 1, v_mvarId_3416_);
lean_closure_set(v___x_3421_, 2, v___f_3420_);
v___x_3422_ = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(v___x_3421_, v___y_3403_, v___y_3401_, v___y_3406_, v___y_3400_, v___y_3398_, v___y_3397_);
if (lean_obj_tag(v___x_3422_) == 0)
{
lean_object* v_a_3423_; lean_object* v_fst_3424_; lean_object* v_snd_3425_; lean_object* v___x_3427_; uint8_t v_isShared_3428_; uint8_t v_isSharedCheck_3478_; 
v_a_3423_ = lean_ctor_get(v___x_3422_, 0);
lean_inc(v_a_3423_);
lean_dec_ref_known(v___x_3422_, 1);
v_fst_3424_ = lean_ctor_get(v_a_3423_, 0);
v_snd_3425_ = lean_ctor_get(v_a_3423_, 1);
v_isSharedCheck_3478_ = !lean_is_exclusive(v_a_3423_);
if (v_isSharedCheck_3478_ == 0)
{
v___x_3427_ = v_a_3423_;
v_isShared_3428_ = v_isSharedCheck_3478_;
goto v_resetjp_3426_;
}
else
{
lean_inc(v_snd_3425_);
lean_inc(v_fst_3424_);
lean_dec(v_a_3423_);
v___x_3427_ = lean_box(0);
v_isShared_3428_ = v_isSharedCheck_3478_;
goto v_resetjp_3426_;
}
v_resetjp_3426_:
{
lean_object* v___x_3429_; lean_object* v_cache_3430_; lean_object* v_symState_3431_; lean_object* v_grindState_3432_; lean_object* v_goals_3433_; lean_object* v___x_3435_; uint8_t v_isShared_3436_; uint8_t v_isSharedCheck_3477_; 
v___x_3429_ = lean_st_ref_take(v___y_3401_);
v_cache_3430_ = lean_ctor_get(v___x_3429_, 3);
v_symState_3431_ = lean_ctor_get(v___x_3429_, 0);
v_grindState_3432_ = lean_ctor_get(v___x_3429_, 1);
v_goals_3433_ = lean_ctor_get(v___x_3429_, 2);
v_isSharedCheck_3477_ = !lean_is_exclusive(v___x_3429_);
if (v_isSharedCheck_3477_ == 0)
{
v___x_3435_ = v___x_3429_;
v_isShared_3436_ = v_isSharedCheck_3477_;
goto v_resetjp_3434_;
}
else
{
lean_inc(v_cache_3430_);
lean_inc(v_goals_3433_);
lean_inc(v_grindState_3432_);
lean_inc(v_symState_3431_);
lean_dec(v___x_3429_);
v___x_3435_ = lean_box(0);
v_isShared_3436_ = v_isSharedCheck_3477_;
goto v_resetjp_3434_;
}
v_resetjp_3434_:
{
lean_object* v_backwardRuleName_3437_; lean_object* v_backwardRuleSyntax_3438_; lean_object* v_simpState_3439_; lean_object* v_dsimpState_3440_; lean_object* v___x_3442_; uint8_t v_isShared_3443_; uint8_t v_isSharedCheck_3476_; 
v_backwardRuleName_3437_ = lean_ctor_get(v_cache_3430_, 0);
v_backwardRuleSyntax_3438_ = lean_ctor_get(v_cache_3430_, 1);
v_simpState_3439_ = lean_ctor_get(v_cache_3430_, 2);
v_dsimpState_3440_ = lean_ctor_get(v_cache_3430_, 3);
v_isSharedCheck_3476_ = !lean_is_exclusive(v_cache_3430_);
if (v_isSharedCheck_3476_ == 0)
{
v___x_3442_ = v_cache_3430_;
v_isShared_3443_ = v_isSharedCheck_3476_;
goto v_resetjp_3441_;
}
else
{
lean_inc(v_dsimpState_3440_);
lean_inc(v_simpState_3439_);
lean_inc(v_backwardRuleSyntax_3438_);
lean_inc(v_backwardRuleName_3437_);
lean_dec(v_cache_3430_);
v___x_3442_ = lean_box(0);
v_isShared_3443_ = v_isSharedCheck_3476_;
goto v_resetjp_3441_;
}
v_resetjp_3441_:
{
lean_object* v___x_3444_; lean_object* v___x_3446_; 
v___x_3444_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1___redArg(v_simpState_3439_, v___y_3405_, v_snd_3425_);
if (v_isShared_3443_ == 0)
{
lean_ctor_set(v___x_3442_, 2, v___x_3444_);
v___x_3446_ = v___x_3442_;
goto v_reusejp_3445_;
}
else
{
lean_object* v_reuseFailAlloc_3475_; 
v_reuseFailAlloc_3475_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3475_, 0, v_backwardRuleName_3437_);
lean_ctor_set(v_reuseFailAlloc_3475_, 1, v_backwardRuleSyntax_3438_);
lean_ctor_set(v_reuseFailAlloc_3475_, 2, v___x_3444_);
lean_ctor_set(v_reuseFailAlloc_3475_, 3, v_dsimpState_3440_);
v___x_3446_ = v_reuseFailAlloc_3475_;
goto v_reusejp_3445_;
}
v_reusejp_3445_:
{
lean_object* v___x_3448_; 
if (v_isShared_3436_ == 0)
{
lean_ctor_set(v___x_3435_, 3, v___x_3446_);
v___x_3448_ = v___x_3435_;
goto v_reusejp_3447_;
}
else
{
lean_object* v_reuseFailAlloc_3474_; 
v_reuseFailAlloc_3474_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3474_, 0, v_symState_3431_);
lean_ctor_set(v_reuseFailAlloc_3474_, 1, v_grindState_3432_);
lean_ctor_set(v_reuseFailAlloc_3474_, 2, v_goals_3433_);
lean_ctor_set(v_reuseFailAlloc_3474_, 3, v___x_3446_);
v___x_3448_ = v_reuseFailAlloc_3474_;
goto v_reusejp_3447_;
}
v_reusejp_3447_:
{
lean_object* v___x_3449_; lean_object* v___f_3450_; lean_object* v___x_3451_; 
v___x_3449_ = lean_st_ref_set(v___y_3401_, v___x_3448_);
v___f_3450_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__1___boxed), 12, 2);
lean_closure_set(v___f_3450_, 0, v_fst_3424_);
lean_closure_set(v___f_3450_, 1, v_mvarId_3416_);
v___x_3451_ = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(v___f_3450_, v___y_3403_, v___y_3401_, v___y_3406_, v___y_3400_, v___y_3398_, v___y_3397_);
if (lean_obj_tag(v___x_3451_) == 0)
{
lean_object* v_a_3452_; 
v_a_3452_ = lean_ctor_get(v___x_3451_, 0);
lean_inc(v_a_3452_);
lean_dec_ref_known(v___x_3451_, 1);
switch(lean_obj_tag(v_a_3452_))
{
case 0:
{
lean_object* v___x_3453_; lean_object* v___x_3454_; 
lean_del_object(v___x_3427_);
lean_del_object(v___x_3418_);
lean_dec_ref(v_toGoalState_3415_);
v___x_3453_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__1, &l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__1);
v___x_3454_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__2___redArg(v___x_3453_, v___y_3406_, v___y_3400_, v___y_3398_, v___y_3397_);
return v___x_3454_;
}
case 1:
{
lean_object* v___x_3455_; lean_object* v___x_3456_; 
lean_del_object(v___x_3427_);
lean_del_object(v___x_3418_);
lean_dec_ref(v_toGoalState_3415_);
v___x_3455_ = lean_box(0);
v___x_3456_ = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(v___x_3455_, v___y_3401_, v___y_3406_, v___y_3400_, v___y_3398_, v___y_3397_);
return v___x_3456_;
}
default: 
{
lean_object* v_mvarId_3457_; lean_object* v___x_3459_; 
v_mvarId_3457_ = lean_ctor_get(v_a_3452_, 0);
lean_inc(v_mvarId_3457_);
lean_dec_ref_known(v_a_3452_, 1);
if (v_isShared_3419_ == 0)
{
lean_ctor_set(v___x_3418_, 1, v_mvarId_3457_);
v___x_3459_ = v___x_3418_;
goto v_reusejp_3458_;
}
else
{
lean_object* v_reuseFailAlloc_3465_; 
v_reuseFailAlloc_3465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3465_, 0, v_toGoalState_3415_);
lean_ctor_set(v_reuseFailAlloc_3465_, 1, v_mvarId_3457_);
v___x_3459_ = v_reuseFailAlloc_3465_;
goto v_reusejp_3458_;
}
v_reusejp_3458_:
{
lean_object* v___x_3460_; lean_object* v___x_3462_; 
v___x_3460_ = lean_box(0);
if (v_isShared_3428_ == 0)
{
lean_ctor_set_tag(v___x_3427_, 1);
lean_ctor_set(v___x_3427_, 1, v___x_3460_);
lean_ctor_set(v___x_3427_, 0, v___x_3459_);
v___x_3462_ = v___x_3427_;
goto v_reusejp_3461_;
}
else
{
lean_object* v_reuseFailAlloc_3464_; 
v_reuseFailAlloc_3464_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3464_, 0, v___x_3459_);
lean_ctor_set(v_reuseFailAlloc_3464_, 1, v___x_3460_);
v___x_3462_ = v_reuseFailAlloc_3464_;
goto v_reusejp_3461_;
}
v_reusejp_3461_:
{
lean_object* v___x_3463_; 
v___x_3463_ = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(v___x_3462_, v___y_3401_, v___y_3406_, v___y_3400_, v___y_3398_, v___y_3397_);
return v___x_3463_;
}
}
}
}
}
else
{
lean_object* v_a_3466_; lean_object* v___x_3468_; uint8_t v_isShared_3469_; uint8_t v_isSharedCheck_3473_; 
lean_del_object(v___x_3427_);
lean_del_object(v___x_3418_);
lean_dec_ref(v_toGoalState_3415_);
v_a_3466_ = lean_ctor_get(v___x_3451_, 0);
v_isSharedCheck_3473_ = !lean_is_exclusive(v___x_3451_);
if (v_isSharedCheck_3473_ == 0)
{
v___x_3468_ = v___x_3451_;
v_isShared_3469_ = v_isSharedCheck_3473_;
goto v_resetjp_3467_;
}
else
{
lean_inc(v_a_3466_);
lean_dec(v___x_3451_);
v___x_3468_ = lean_box(0);
v_isShared_3469_ = v_isSharedCheck_3473_;
goto v_resetjp_3467_;
}
v_resetjp_3467_:
{
lean_object* v___x_3471_; 
if (v_isShared_3469_ == 0)
{
v___x_3471_ = v___x_3468_;
goto v_reusejp_3470_;
}
else
{
lean_object* v_reuseFailAlloc_3472_; 
v_reuseFailAlloc_3472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3472_, 0, v_a_3466_);
v___x_3471_ = v_reuseFailAlloc_3472_;
goto v_reusejp_3470_;
}
v_reusejp_3470_:
{
return v___x_3471_;
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
lean_object* v_a_3479_; lean_object* v___x_3481_; uint8_t v_isShared_3482_; uint8_t v_isSharedCheck_3486_; 
lean_del_object(v___x_3418_);
lean_dec(v_mvarId_3416_);
lean_dec_ref(v_toGoalState_3415_);
lean_dec_ref(v___y_3405_);
v_a_3479_ = lean_ctor_get(v___x_3422_, 0);
v_isSharedCheck_3486_ = !lean_is_exclusive(v___x_3422_);
if (v_isSharedCheck_3486_ == 0)
{
v___x_3481_ = v___x_3422_;
v_isShared_3482_ = v_isSharedCheck_3486_;
goto v_resetjp_3480_;
}
else
{
lean_inc(v_a_3479_);
lean_dec(v___x_3422_);
v___x_3481_ = lean_box(0);
v_isShared_3482_ = v_isSharedCheck_3486_;
goto v_resetjp_3480_;
}
v_resetjp_3480_:
{
lean_object* v___x_3484_; 
if (v_isShared_3482_ == 0)
{
v___x_3484_ = v___x_3481_;
goto v_reusejp_3483_;
}
else
{
lean_object* v_reuseFailAlloc_3485_; 
v_reuseFailAlloc_3485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3485_, 0, v_a_3479_);
v___x_3484_ = v_reuseFailAlloc_3485_;
goto v_reusejp_3483_;
}
v_reusejp_3483_:
{
return v___x_3484_;
}
}
}
}
}
else
{
lean_object* v_a_3488_; lean_object* v___x_3490_; uint8_t v_isShared_3491_; uint8_t v_isSharedCheck_3495_; 
lean_dec(v_snd_3412_);
lean_dec(v_fst_3411_);
lean_dec_ref(v___y_3408_);
lean_dec_ref(v___y_3405_);
v_a_3488_ = lean_ctor_get(v___x_3413_, 0);
v_isSharedCheck_3495_ = !lean_is_exclusive(v___x_3413_);
if (v_isSharedCheck_3495_ == 0)
{
v___x_3490_ = v___x_3413_;
v_isShared_3491_ = v_isSharedCheck_3495_;
goto v_resetjp_3489_;
}
else
{
lean_inc(v_a_3488_);
lean_dec(v___x_3413_);
v___x_3490_ = lean_box(0);
v_isShared_3491_ = v_isSharedCheck_3495_;
goto v_resetjp_3489_;
}
v_resetjp_3489_:
{
lean_object* v___x_3493_; 
if (v_isShared_3491_ == 0)
{
v___x_3493_ = v___x_3490_;
goto v_reusejp_3492_;
}
else
{
lean_object* v_reuseFailAlloc_3494_; 
v_reuseFailAlloc_3494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3494_, 0, v_a_3488_);
v___x_3493_ = v_reuseFailAlloc_3494_;
goto v_reusejp_3492_;
}
v_reusejp_3492_:
{
return v___x_3493_;
}
}
}
}
else
{
lean_object* v_a_3496_; lean_object* v___x_3498_; uint8_t v_isShared_3499_; uint8_t v_isSharedCheck_3503_; 
lean_dec_ref(v___y_3408_);
lean_dec_ref(v___y_3405_);
v_a_3496_ = lean_ctor_get(v___x_3409_, 0);
v_isSharedCheck_3503_ = !lean_is_exclusive(v___x_3409_);
if (v_isSharedCheck_3503_ == 0)
{
v___x_3498_ = v___x_3409_;
v_isShared_3499_ = v_isSharedCheck_3503_;
goto v_resetjp_3497_;
}
else
{
lean_inc(v_a_3496_);
lean_dec(v___x_3409_);
v___x_3498_ = lean_box(0);
v_isShared_3499_ = v_isSharedCheck_3503_;
goto v_resetjp_3497_;
}
v_resetjp_3497_:
{
lean_object* v___x_3501_; 
if (v_isShared_3499_ == 0)
{
v___x_3501_ = v___x_3498_;
goto v_reusejp_3500_;
}
else
{
lean_object* v_reuseFailAlloc_3502_; 
v_reuseFailAlloc_3502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3502_, 0, v_a_3496_);
v___x_3501_ = v_reuseFailAlloc_3502_;
goto v_reusejp_3500_;
}
v_reusejp_3500_:
{
return v___x_3501_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___boxed(lean_object* v_stx_3622_, lean_object* v___y_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_){
_start:
{
lean_object* v_res_3632_; 
v_res_3632_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2(v_stx_3622_, v___y_3623_, v___y_3624_, v___y_3625_, v___y_3626_, v___y_3627_, v___y_3628_, v___y_3629_, v___y_3630_);
lean_dec(v___y_3630_);
lean_dec_ref(v___y_3629_);
lean_dec(v___y_3628_);
lean_dec_ref(v___y_3627_);
lean_dec(v___y_3626_);
lean_dec_ref(v___y_3625_);
lean_dec(v___y_3624_);
lean_dec_ref(v___y_3623_);
return v_res_3632_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp(lean_object* v_stx_3633_, lean_object* v_a_3634_, lean_object* v_a_3635_, lean_object* v_a_3636_, lean_object* v_a_3637_, lean_object* v_a_3638_, lean_object* v_a_3639_, lean_object* v_a_3640_, lean_object* v_a_3641_){
_start:
{
lean_object* v___f_3643_; lean_object* v___x_3644_; 
v___f_3643_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___boxed), 10, 1);
lean_closure_set(v___f_3643_, 0, v_stx_3633_);
v___x_3644_ = l_Lean_Elab_Tactic_Grind_withMainContext___redArg(v___f_3643_, v_a_3634_, v_a_3635_, v_a_3636_, v_a_3637_, v_a_3638_, v_a_3639_, v_a_3640_, v_a_3641_);
return v___x_3644_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___boxed(lean_object* v_stx_3645_, lean_object* v_a_3646_, lean_object* v_a_3647_, lean_object* v_a_3648_, lean_object* v_a_3649_, lean_object* v_a_3650_, lean_object* v_a_3651_, lean_object* v_a_3652_, lean_object* v_a_3653_, lean_object* v_a_3654_){
_start:
{
lean_object* v_res_3655_; 
v_res_3655_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp(v_stx_3645_, v_a_3646_, v_a_3647_, v_a_3648_, v_a_3649_, v_a_3650_, v_a_3651_, v_a_3652_, v_a_3653_);
lean_dec(v_a_3653_);
lean_dec_ref(v_a_3652_);
lean_dec(v_a_3651_);
lean_dec_ref(v_a_3650_);
lean_dec(v_a_3649_);
lean_dec_ref(v_a_3648_);
lean_dec(v_a_3647_);
lean_dec_ref(v_a_3646_);
return v_res_3655_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1(lean_object* v_00_u03b2_3656_, lean_object* v_m_3657_, lean_object* v_a_3658_, lean_object* v_b_3659_){
_start:
{
lean_object* v___x_3660_; 
v___x_3660_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1___redArg(v_m_3657_, v_a_3658_, v_b_3659_);
return v___x_3660_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__2(lean_object* v_00_u03b2_3661_, lean_object* v_m_3662_, lean_object* v_a_3663_){
_start:
{
lean_object* v___x_3664_; 
v___x_3664_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__2___redArg(v_m_3662_, v_a_3663_);
return v___x_3664_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__2___boxed(lean_object* v_00_u03b2_3665_, lean_object* v_m_3666_, lean_object* v_a_3667_){
_start:
{
lean_object* v_res_3668_; 
v_res_3668_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__2(v_00_u03b2_3665_, v_m_3666_, v_a_3667_);
lean_dec_ref(v_a_3667_);
lean_dec_ref(v_m_3666_);
return v_res_3668_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__1(lean_object* v_00_u03b2_3669_, lean_object* v_a_3670_, lean_object* v_x_3671_){
_start:
{
uint8_t v___x_3672_; 
v___x_3672_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__1___redArg(v_a_3670_, v_x_3671_);
return v___x_3672_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__1___boxed(lean_object* v_00_u03b2_3673_, lean_object* v_a_3674_, lean_object* v_x_3675_){
_start:
{
uint8_t v_res_3676_; lean_object* v_r_3677_; 
v_res_3676_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__1(v_00_u03b2_3673_, v_a_3674_, v_x_3675_);
lean_dec(v_x_3675_);
lean_dec_ref(v_a_3674_);
v_r_3677_ = lean_box(v_res_3676_);
return v_r_3677_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__2(lean_object* v_00_u03b2_3678_, lean_object* v_data_3679_){
_start:
{
lean_object* v___x_3680_; 
v___x_3680_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__2___redArg(v_data_3679_);
return v___x_3680_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__3(lean_object* v_00_u03b2_3681_, lean_object* v_a_3682_, lean_object* v_b_3683_, lean_object* v_x_3684_){
_start:
{
lean_object* v___x_3685_; 
v___x_3685_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__3___redArg(v_a_3682_, v_b_3683_, v_x_3684_);
return v___x_3685_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__2_spec__5(lean_object* v_00_u03b2_3686_, lean_object* v_a_3687_, lean_object* v_x_3688_){
_start:
{
lean_object* v___x_3689_; 
v___x_3689_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__2_spec__5___redArg(v_a_3687_, v_x_3688_);
return v___x_3689_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__2_spec__5___boxed(lean_object* v_00_u03b2_3690_, lean_object* v_a_3691_, lean_object* v_x_3692_){
_start:
{
lean_object* v_res_3693_; 
v_res_3693_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__2_spec__5(v_00_u03b2_3690_, v_a_3691_, v_x_3692_);
lean_dec(v_x_3692_);
lean_dec_ref(v_a_3691_);
return v_res_3693_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_3694_, lean_object* v_i_3695_, lean_object* v_source_3696_, lean_object* v_target_3697_){
_start:
{
lean_object* v___x_3698_; 
v___x_3698_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__2_spec__3___redArg(v_i_3695_, v_source_3696_, v_target_3697_);
return v___x_3698_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__2_spec__3_spec__7(lean_object* v_00_u03b2_3699_, lean_object* v_x_3700_, lean_object* v_x_3701_){
_start:
{
lean_object* v___x_3702_; 
v___x_3702_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__2_spec__3_spec__7___redArg(v_x_3700_, v_x_3701_);
return v___x_3702_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp__1(){
_start:
{
lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; 
v___x_3708_ = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
v___x_3709_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__3));
v___x_3710_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp__1___closed__1));
v___x_3711_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___boxed), 10, 0);
v___x_3712_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3708_, v___x_3709_, v___x_3710_, v___x_3711_);
return v___x_3712_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp__1___boxed(lean_object* v_a_3713_){
_start:
{
lean_object* v_res_3714_; 
v_res_3714_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp__1();
return v_res_3714_;
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
