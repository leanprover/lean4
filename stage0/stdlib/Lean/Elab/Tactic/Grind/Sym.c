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
uint8_t lean_bool_not(uint8_t);
lean_object* l_Lean_Meta_Sym_Simp_mkEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t v___x_1016_; uint8_t v___x_1017_; 
v___x_1016_ = l_Lean_Expr_hasMVar(v_e_1013_);
v___x_1017_ = lean_bool_not(v___x_1016_);
if (v___x_1017_ == 0)
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
else
{
lean_object* v___x_1038_; 
v___x_1038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1038_, 0, v_e_1013_);
return v___x_1038_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__1___redArg___boxed(lean_object* v_e_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_){
_start:
{
lean_object* v_res_1042_; 
v_res_1042_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__1___redArg(v_e_1039_, v___y_1040_);
lean_dec(v___y_1040_);
return v_res_1042_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__1(lean_object* v_e_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_){
_start:
{
lean_object* v___x_1053_; 
v___x_1053_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__1___redArg(v_e_1043_, v___y_1049_);
return v___x_1053_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__1___boxed(lean_object* v_e_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_){
_start:
{
lean_object* v_res_1064_; 
v_res_1064_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__1(v_e_1054_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_);
lean_dec(v___y_1062_);
lean_dec_ref(v___y_1061_);
lean_dec(v___y_1060_);
lean_dec_ref(v___y_1059_);
lean_dec(v___y_1058_);
lean_dec_ref(v___y_1057_);
lean_dec(v___y_1056_);
lean_dec_ref(v___y_1055_);
return v_res_1064_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm___lam__0(lean_object* v_term_1065_, lean_object* v___x_1066_, uint8_t v___x_1067_, uint8_t v___x_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_){
_start:
{
lean_object* v___x_1078_; 
v___x_1078_ = l_Lean_Elab_Term_elabTerm(v_term_1065_, v___x_1066_, v___x_1067_, v___x_1067_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_);
if (lean_obj_tag(v___x_1078_) == 0)
{
lean_object* v_a_1079_; uint8_t v___x_1080_; lean_object* v___x_1081_; 
v_a_1079_ = lean_ctor_get(v___x_1078_, 0);
lean_inc(v_a_1079_);
lean_dec_ref_known(v___x_1078_, 1);
v___x_1080_ = 1;
v___x_1081_ = l_Lean_Elab_Term_synthesizeSyntheticMVars(v___x_1080_, v___x_1068_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_);
if (lean_obj_tag(v___x_1081_) == 0)
{
lean_object* v___x_1082_; 
lean_dec_ref_known(v___x_1081_, 1);
v___x_1082_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__1___redArg(v_a_1079_, v___y_1074_);
return v___x_1082_;
}
else
{
lean_object* v_a_1083_; lean_object* v___x_1085_; uint8_t v_isShared_1086_; uint8_t v_isSharedCheck_1090_; 
lean_dec(v_a_1079_);
v_a_1083_ = lean_ctor_get(v___x_1081_, 0);
v_isSharedCheck_1090_ = !lean_is_exclusive(v___x_1081_);
if (v_isSharedCheck_1090_ == 0)
{
v___x_1085_ = v___x_1081_;
v_isShared_1086_ = v_isSharedCheck_1090_;
goto v_resetjp_1084_;
}
else
{
lean_inc(v_a_1083_);
lean_dec(v___x_1081_);
v___x_1085_ = lean_box(0);
v_isShared_1086_ = v_isSharedCheck_1090_;
goto v_resetjp_1084_;
}
v_resetjp_1084_:
{
lean_object* v___x_1088_; 
if (v_isShared_1086_ == 0)
{
v___x_1088_ = v___x_1085_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v_a_1083_);
v___x_1088_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
return v___x_1088_;
}
}
}
}
else
{
return v___x_1078_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm___lam__0___boxed(lean_object* v_term_1091_, lean_object* v___x_1092_, lean_object* v___x_1093_, lean_object* v___x_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_){
_start:
{
uint8_t v___x_3487__boxed_1104_; uint8_t v___x_3488__boxed_1105_; lean_object* v_res_1106_; 
v___x_3487__boxed_1104_ = lean_unbox(v___x_1093_);
v___x_3488__boxed_1105_ = lean_unbox(v___x_1094_);
v_res_1106_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm___lam__0(v_term_1091_, v___x_1092_, v___x_3487__boxed_1104_, v___x_3488__boxed_1105_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_);
lean_dec(v___y_1102_);
lean_dec_ref(v___y_1101_);
lean_dec(v___y_1100_);
lean_dec_ref(v___y_1099_);
lean_dec(v___y_1098_);
lean_dec_ref(v___y_1097_);
lean_dec(v___y_1096_);
lean_dec_ref(v___y_1095_);
return v_res_1106_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3_spec__5_spec__6___redArg(lean_object* v_x_1107_, lean_object* v_x_1108_, lean_object* v_x_1109_, lean_object* v_x_1110_){
_start:
{
lean_object* v_ks_1111_; lean_object* v_vs_1112_; lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1141_; 
v_ks_1111_ = lean_ctor_get(v_x_1107_, 0);
v_vs_1112_ = lean_ctor_get(v_x_1107_, 1);
v_isSharedCheck_1141_ = !lean_is_exclusive(v_x_1107_);
if (v_isSharedCheck_1141_ == 0)
{
v___x_1114_ = v_x_1107_;
v_isShared_1115_ = v_isSharedCheck_1141_;
goto v_resetjp_1113_;
}
else
{
lean_inc(v_vs_1112_);
lean_inc(v_ks_1111_);
lean_dec(v_x_1107_);
v___x_1114_ = lean_box(0);
v_isShared_1115_ = v_isSharedCheck_1141_;
goto v_resetjp_1113_;
}
v_resetjp_1113_:
{
uint8_t v___y_1117_; lean_object* v___x_1129_; uint8_t v___x_1130_; 
v___x_1129_ = lean_array_get_size(v_ks_1111_);
v___x_1130_ = lean_nat_dec_lt(v_x_1108_, v___x_1129_);
if (v___x_1130_ == 0)
{
lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; 
lean_del_object(v___x_1114_);
lean_dec(v_x_1108_);
v___x_1131_ = lean_array_push(v_ks_1111_, v_x_1109_);
v___x_1132_ = lean_array_push(v_vs_1112_, v_x_1110_);
v___x_1133_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1133_, 0, v___x_1131_);
lean_ctor_set(v___x_1133_, 1, v___x_1132_);
return v___x_1133_;
}
else
{
lean_object* v_fst_1134_; lean_object* v_snd_1135_; lean_object* v_k_x27_1136_; lean_object* v_fst_1137_; lean_object* v_snd_1138_; uint8_t v___x_1139_; 
v_fst_1134_ = lean_ctor_get(v_x_1109_, 0);
v_snd_1135_ = lean_ctor_get(v_x_1109_, 1);
v_k_x27_1136_ = lean_array_fget_borrowed(v_ks_1111_, v_x_1108_);
v_fst_1137_ = lean_ctor_get(v_k_x27_1136_, 0);
v_snd_1138_ = lean_ctor_get(v_k_x27_1136_, 1);
v___x_1139_ = lean_nat_dec_eq(v_fst_1134_, v_fst_1137_);
if (v___x_1139_ == 0)
{
v___y_1117_ = v___x_1139_;
goto v___jp_1116_;
}
else
{
uint8_t v___x_1140_; 
v___x_1140_ = lean_nat_dec_eq(v_snd_1135_, v_snd_1138_);
v___y_1117_ = v___x_1140_;
goto v___jp_1116_;
}
}
v___jp_1116_:
{
if (v___y_1117_ == 0)
{
lean_object* v___x_1119_; 
if (v_isShared_1115_ == 0)
{
v___x_1119_ = v___x_1114_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v_ks_1111_);
lean_ctor_set(v_reuseFailAlloc_1123_, 1, v_vs_1112_);
v___x_1119_ = v_reuseFailAlloc_1123_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
lean_object* v___x_1120_; lean_object* v___x_1121_; 
v___x_1120_ = lean_unsigned_to_nat(1u);
v___x_1121_ = lean_nat_add(v_x_1108_, v___x_1120_);
lean_dec(v_x_1108_);
v_x_1107_ = v___x_1119_;
v_x_1108_ = v___x_1121_;
goto _start;
}
}
else
{
lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1127_; 
v___x_1124_ = lean_array_fset(v_ks_1111_, v_x_1108_, v_x_1109_);
v___x_1125_ = lean_array_fset(v_vs_1112_, v_x_1108_, v_x_1110_);
lean_dec(v_x_1108_);
if (v_isShared_1115_ == 0)
{
lean_ctor_set(v___x_1114_, 1, v___x_1125_);
lean_ctor_set(v___x_1114_, 0, v___x_1124_);
v___x_1127_ = v___x_1114_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v___x_1124_);
lean_ctor_set(v_reuseFailAlloc_1128_, 1, v___x_1125_);
v___x_1127_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
return v___x_1127_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3_spec__5___redArg(lean_object* v_n_1142_, lean_object* v_k_1143_, lean_object* v_v_1144_){
_start:
{
lean_object* v___x_1145_; lean_object* v___x_1146_; 
v___x_1145_ = lean_unsigned_to_nat(0u);
v___x_1146_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3_spec__5_spec__6___redArg(v_n_1142_, v___x_1145_, v_k_1143_, v_v_1144_);
return v___x_1146_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_1147_; 
v___x_1147_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
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
lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1204_; 
lean_inc_ref(v_es_1153_);
v_isSharedCheck_1204_ = !lean_is_exclusive(v_x_1148_);
if (v_isSharedCheck_1204_ == 0)
{
lean_object* v_unused_1205_; 
v_unused_1205_ = lean_ctor_get(v_x_1148_, 0);
lean_dec(v_unused_1205_);
v___x_1160_ = v_x_1148_;
v_isShared_1161_ = v_isSharedCheck_1204_;
goto v_resetjp_1159_;
}
else
{
lean_dec(v_x_1148_);
v___x_1160_ = lean_box(0);
v_isShared_1161_ = v_isSharedCheck_1204_;
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
lean_object* v_key_1171_; lean_object* v_val_1172_; lean_object* v___x_1174_; uint8_t v_isShared_1175_; uint8_t v_isSharedCheck_1189_; 
v_key_1171_ = lean_ctor_get(v_v_1162_, 0);
v_val_1172_ = lean_ctor_get(v_v_1162_, 1);
v_isSharedCheck_1189_ = !lean_is_exclusive(v_v_1162_);
if (v_isSharedCheck_1189_ == 0)
{
v___x_1174_ = v_v_1162_;
v_isShared_1175_ = v_isSharedCheck_1189_;
goto v_resetjp_1173_;
}
else
{
lean_inc(v_val_1172_);
lean_inc(v_key_1171_);
lean_dec(v_v_1162_);
v___x_1174_ = lean_box(0);
v_isShared_1175_ = v_isSharedCheck_1189_;
goto v_resetjp_1173_;
}
v_resetjp_1173_:
{
uint8_t v___y_1177_; lean_object* v_fst_1183_; lean_object* v_snd_1184_; lean_object* v_fst_1185_; lean_object* v_snd_1186_; uint8_t v___x_1187_; 
v_fst_1183_ = lean_ctor_get(v_x_1151_, 0);
v_snd_1184_ = lean_ctor_get(v_x_1151_, 1);
v_fst_1185_ = lean_ctor_get(v_key_1171_, 0);
v_snd_1186_ = lean_ctor_get(v_key_1171_, 1);
v___x_1187_ = lean_nat_dec_eq(v_fst_1183_, v_fst_1185_);
if (v___x_1187_ == 0)
{
v___y_1177_ = v___x_1187_;
goto v___jp_1176_;
}
else
{
uint8_t v___x_1188_; 
v___x_1188_ = lean_nat_dec_eq(v_snd_1184_, v_snd_1186_);
v___y_1177_ = v___x_1188_;
goto v___jp_1176_;
}
v___jp_1176_:
{
if (v___y_1177_ == 0)
{
lean_object* v___x_1178_; lean_object* v___x_1179_; 
lean_del_object(v___x_1174_);
v___x_1178_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1171_, v_val_1172_, v_x_1151_, v_x_1152_);
v___x_1179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1179_, 0, v___x_1178_);
v___y_1166_ = v___x_1179_;
goto v___jp_1165_;
}
else
{
lean_object* v___x_1181_; 
lean_dec(v_val_1172_);
lean_dec(v_key_1171_);
if (v_isShared_1175_ == 0)
{
lean_ctor_set(v___x_1174_, 1, v_x_1152_);
lean_ctor_set(v___x_1174_, 0, v_x_1151_);
v___x_1181_ = v___x_1174_;
goto v_reusejp_1180_;
}
else
{
lean_object* v_reuseFailAlloc_1182_; 
v_reuseFailAlloc_1182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1182_, 0, v_x_1151_);
lean_ctor_set(v_reuseFailAlloc_1182_, 1, v_x_1152_);
v___x_1181_ = v_reuseFailAlloc_1182_;
goto v_reusejp_1180_;
}
v_reusejp_1180_:
{
v___y_1166_ = v___x_1181_;
goto v___jp_1165_;
}
}
}
}
}
case 1:
{
lean_object* v_node_1190_; lean_object* v___x_1192_; uint8_t v_isShared_1193_; uint8_t v_isSharedCheck_1202_; 
v_node_1190_ = lean_ctor_get(v_v_1162_, 0);
v_isSharedCheck_1202_ = !lean_is_exclusive(v_v_1162_);
if (v_isSharedCheck_1202_ == 0)
{
v___x_1192_ = v_v_1162_;
v_isShared_1193_ = v_isSharedCheck_1202_;
goto v_resetjp_1191_;
}
else
{
lean_inc(v_node_1190_);
lean_dec(v_v_1162_);
v___x_1192_ = lean_box(0);
v_isShared_1193_ = v_isSharedCheck_1202_;
goto v_resetjp_1191_;
}
v_resetjp_1191_:
{
size_t v___x_1194_; size_t v___x_1195_; size_t v___x_1196_; size_t v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1200_; 
v___x_1194_ = ((size_t)5ULL);
v___x_1195_ = lean_usize_shift_right(v_x_1149_, v___x_1194_);
v___x_1196_ = ((size_t)1ULL);
v___x_1197_ = lean_usize_add(v_x_1150_, v___x_1196_);
v___x_1198_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3___redArg(v_node_1190_, v___x_1195_, v___x_1197_, v_x_1151_, v_x_1152_);
if (v_isShared_1193_ == 0)
{
lean_ctor_set(v___x_1192_, 0, v___x_1198_);
v___x_1200_ = v___x_1192_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1201_; 
v_reuseFailAlloc_1201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1201_, 0, v___x_1198_);
v___x_1200_ = v_reuseFailAlloc_1201_;
goto v_reusejp_1199_;
}
v_reusejp_1199_:
{
v___y_1166_ = v___x_1200_;
goto v___jp_1165_;
}
}
}
default: 
{
lean_object* v___x_1203_; 
v___x_1203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1203_, 0, v_x_1151_);
lean_ctor_set(v___x_1203_, 1, v_x_1152_);
v___y_1166_ = v___x_1203_;
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
lean_object* v_ks_1206_; lean_object* v_vs_1207_; lean_object* v___x_1209_; uint8_t v_isShared_1210_; uint8_t v_isSharedCheck_1227_; 
v_ks_1206_ = lean_ctor_get(v_x_1148_, 0);
v_vs_1207_ = lean_ctor_get(v_x_1148_, 1);
v_isSharedCheck_1227_ = !lean_is_exclusive(v_x_1148_);
if (v_isSharedCheck_1227_ == 0)
{
v___x_1209_ = v_x_1148_;
v_isShared_1210_ = v_isSharedCheck_1227_;
goto v_resetjp_1208_;
}
else
{
lean_inc(v_vs_1207_);
lean_inc(v_ks_1206_);
lean_dec(v_x_1148_);
v___x_1209_ = lean_box(0);
v_isShared_1210_ = v_isSharedCheck_1227_;
goto v_resetjp_1208_;
}
v_resetjp_1208_:
{
lean_object* v___x_1212_; 
if (v_isShared_1210_ == 0)
{
v___x_1212_ = v___x_1209_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v_ks_1206_);
lean_ctor_set(v_reuseFailAlloc_1226_, 1, v_vs_1207_);
v___x_1212_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
lean_object* v_newNode_1213_; uint8_t v___y_1215_; size_t v___x_1221_; uint8_t v___x_1222_; 
v_newNode_1213_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3_spec__5___redArg(v___x_1212_, v_x_1151_, v_x_1152_);
v___x_1221_ = ((size_t)7ULL);
v___x_1222_ = lean_usize_dec_le(v___x_1221_, v_x_1150_);
if (v___x_1222_ == 0)
{
lean_object* v___x_1223_; lean_object* v___x_1224_; uint8_t v___x_1225_; 
v___x_1223_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1213_);
v___x_1224_ = lean_unsigned_to_nat(4u);
v___x_1225_ = lean_nat_dec_lt(v___x_1223_, v___x_1224_);
lean_dec(v___x_1223_);
v___y_1215_ = v___x_1225_;
goto v___jp_1214_;
}
else
{
v___y_1215_ = v___x_1222_;
goto v___jp_1214_;
}
v___jp_1214_:
{
if (v___y_1215_ == 0)
{
lean_object* v_ks_1216_; lean_object* v_vs_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; 
v_ks_1216_ = lean_ctor_get(v_newNode_1213_, 0);
lean_inc_ref(v_ks_1216_);
v_vs_1217_ = lean_ctor_get(v_newNode_1213_, 1);
lean_inc_ref(v_vs_1217_);
lean_dec_ref(v_newNode_1213_);
v___x_1218_ = lean_unsigned_to_nat(0u);
v___x_1219_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3___redArg___closed__0);
v___x_1220_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3_spec__6___redArg(v_x_1150_, v_ks_1216_, v_vs_1217_, v___x_1218_, v___x_1219_);
lean_dec_ref(v_vs_1217_);
lean_dec_ref(v_ks_1216_);
return v___x_1220_;
}
else
{
return v_newNode_1213_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3_spec__6___redArg(size_t v_depth_1228_, lean_object* v_keys_1229_, lean_object* v_vals_1230_, lean_object* v_i_1231_, lean_object* v_entries_1232_){
_start:
{
lean_object* v___x_1233_; uint8_t v___x_1234_; 
v___x_1233_ = lean_array_get_size(v_keys_1229_);
v___x_1234_ = lean_nat_dec_lt(v_i_1231_, v___x_1233_);
if (v___x_1234_ == 0)
{
lean_dec(v_i_1231_);
return v_entries_1232_;
}
else
{
lean_object* v_k_1235_; lean_object* v_fst_1236_; lean_object* v_snd_1237_; lean_object* v_v_1238_; uint64_t v___x_1239_; uint64_t v___x_1240_; uint64_t v___x_1241_; size_t v_h_1242_; size_t v___x_1243_; lean_object* v___x_1244_; size_t v___x_1245_; size_t v___x_1246_; size_t v___x_1247_; size_t v_h_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; 
v_k_1235_ = lean_array_fget_borrowed(v_keys_1229_, v_i_1231_);
v_fst_1236_ = lean_ctor_get(v_k_1235_, 0);
v_snd_1237_ = lean_ctor_get(v_k_1235_, 1);
v_v_1238_ = lean_array_fget_borrowed(v_vals_1230_, v_i_1231_);
v___x_1239_ = lean_uint64_of_nat(v_fst_1236_);
v___x_1240_ = lean_uint64_of_nat(v_snd_1237_);
v___x_1241_ = lean_uint64_mix_hash(v___x_1239_, v___x_1240_);
v_h_1242_ = lean_uint64_to_usize(v___x_1241_);
v___x_1243_ = ((size_t)5ULL);
v___x_1244_ = lean_unsigned_to_nat(1u);
v___x_1245_ = ((size_t)1ULL);
v___x_1246_ = lean_usize_sub(v_depth_1228_, v___x_1245_);
v___x_1247_ = lean_usize_mul(v___x_1243_, v___x_1246_);
v_h_1248_ = lean_usize_shift_right(v_h_1242_, v___x_1247_);
v___x_1249_ = lean_nat_add(v_i_1231_, v___x_1244_);
lean_dec(v_i_1231_);
lean_inc(v_v_1238_);
lean_inc(v_k_1235_);
v___x_1250_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3___redArg(v_entries_1232_, v_h_1248_, v_depth_1228_, v_k_1235_, v_v_1238_);
v_i_1231_ = v___x_1249_;
v_entries_1232_ = v___x_1250_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_depth_1252_, lean_object* v_keys_1253_, lean_object* v_vals_1254_, lean_object* v_i_1255_, lean_object* v_entries_1256_){
_start:
{
size_t v_depth_boxed_1257_; lean_object* v_res_1258_; 
v_depth_boxed_1257_ = lean_unbox_usize(v_depth_1252_);
lean_dec(v_depth_1252_);
v_res_1258_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3_spec__6___redArg(v_depth_boxed_1257_, v_keys_1253_, v_vals_1254_, v_i_1255_, v_entries_1256_);
lean_dec_ref(v_vals_1254_);
lean_dec_ref(v_keys_1253_);
return v_res_1258_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3___redArg___boxed(lean_object* v_x_1259_, lean_object* v_x_1260_, lean_object* v_x_1261_, lean_object* v_x_1262_, lean_object* v_x_1263_){
_start:
{
size_t v_x_3641__boxed_1264_; size_t v_x_3642__boxed_1265_; lean_object* v_res_1266_; 
v_x_3641__boxed_1264_ = lean_unbox_usize(v_x_1260_);
lean_dec(v_x_1260_);
v_x_3642__boxed_1265_ = lean_unbox_usize(v_x_1261_);
lean_dec(v_x_1261_);
v_res_1266_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3___redArg(v_x_1259_, v_x_3641__boxed_1264_, v_x_3642__boxed_1265_, v_x_1262_, v_x_1263_);
return v_res_1266_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2___redArg(lean_object* v_x_1267_, lean_object* v_x_1268_, lean_object* v_x_1269_){
_start:
{
lean_object* v_fst_1270_; lean_object* v_snd_1271_; uint64_t v___x_1272_; uint64_t v___x_1273_; uint64_t v___x_1274_; size_t v___x_1275_; size_t v___x_1276_; lean_object* v___x_1277_; 
v_fst_1270_ = lean_ctor_get(v_x_1268_, 0);
v_snd_1271_ = lean_ctor_get(v_x_1268_, 1);
v___x_1272_ = lean_uint64_of_nat(v_fst_1270_);
v___x_1273_ = lean_uint64_of_nat(v_snd_1271_);
v___x_1274_ = lean_uint64_mix_hash(v___x_1272_, v___x_1273_);
v___x_1275_ = lean_uint64_to_usize(v___x_1274_);
v___x_1276_ = ((size_t)1ULL);
v___x_1277_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3___redArg(v_x_1267_, v___x_1275_, v___x_1276_, v_x_1268_, v_x_1269_);
return v___x_1277_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0_spec__0_spec__2___redArg(lean_object* v_keys_1278_, lean_object* v_vals_1279_, lean_object* v_i_1280_, lean_object* v_k_1281_){
_start:
{
uint8_t v___y_1283_; lean_object* v___x_1289_; uint8_t v___x_1290_; 
v___x_1289_ = lean_array_get_size(v_keys_1278_);
v___x_1290_ = lean_nat_dec_lt(v_i_1280_, v___x_1289_);
if (v___x_1290_ == 0)
{
lean_object* v___x_1291_; 
lean_dec(v_i_1280_);
v___x_1291_ = lean_box(0);
return v___x_1291_;
}
else
{
lean_object* v_fst_1292_; lean_object* v_snd_1293_; lean_object* v_k_x27_1294_; lean_object* v_fst_1295_; lean_object* v_snd_1296_; uint8_t v___x_1297_; 
v_fst_1292_ = lean_ctor_get(v_k_1281_, 0);
v_snd_1293_ = lean_ctor_get(v_k_1281_, 1);
v_k_x27_1294_ = lean_array_fget_borrowed(v_keys_1278_, v_i_1280_);
v_fst_1295_ = lean_ctor_get(v_k_x27_1294_, 0);
v_snd_1296_ = lean_ctor_get(v_k_x27_1294_, 1);
v___x_1297_ = lean_nat_dec_eq(v_fst_1292_, v_fst_1295_);
if (v___x_1297_ == 0)
{
v___y_1283_ = v___x_1297_;
goto v___jp_1282_;
}
else
{
uint8_t v___x_1298_; 
v___x_1298_ = lean_nat_dec_eq(v_snd_1293_, v_snd_1296_);
v___y_1283_ = v___x_1298_;
goto v___jp_1282_;
}
}
v___jp_1282_:
{
if (v___y_1283_ == 0)
{
lean_object* v___x_1284_; lean_object* v___x_1285_; 
v___x_1284_ = lean_unsigned_to_nat(1u);
v___x_1285_ = lean_nat_add(v_i_1280_, v___x_1284_);
lean_dec(v_i_1280_);
v_i_1280_ = v___x_1285_;
goto _start;
}
else
{
lean_object* v___x_1287_; lean_object* v___x_1288_; 
v___x_1287_ = lean_array_fget_borrowed(v_vals_1279_, v_i_1280_);
lean_dec(v_i_1280_);
lean_inc(v___x_1287_);
v___x_1288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1288_, 0, v___x_1287_);
return v___x_1288_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_keys_1299_, lean_object* v_vals_1300_, lean_object* v_i_1301_, lean_object* v_k_1302_){
_start:
{
lean_object* v_res_1303_; 
v_res_1303_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0_spec__0_spec__2___redArg(v_keys_1299_, v_vals_1300_, v_i_1301_, v_k_1302_);
lean_dec_ref(v_k_1302_);
lean_dec_ref(v_vals_1300_);
lean_dec_ref(v_keys_1299_);
return v_res_1303_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0_spec__0___redArg(lean_object* v_x_1304_, size_t v_x_1305_, lean_object* v_x_1306_){
_start:
{
if (lean_obj_tag(v_x_1304_) == 0)
{
lean_object* v_es_1307_; lean_object* v___x_1308_; size_t v___x_1309_; size_t v___x_1310_; lean_object* v_j_1311_; lean_object* v___x_1312_; 
v_es_1307_ = lean_ctor_get(v_x_1304_, 0);
v___x_1308_ = lean_box(2);
v___x_1309_ = ((size_t)31ULL);
v___x_1310_ = lean_usize_land(v_x_1305_, v___x_1309_);
v_j_1311_ = lean_usize_to_nat(v___x_1310_);
v___x_1312_ = lean_array_get_borrowed(v___x_1308_, v_es_1307_, v_j_1311_);
lean_dec(v_j_1311_);
switch(lean_obj_tag(v___x_1312_))
{
case 0:
{
lean_object* v_key_1313_; lean_object* v_val_1314_; uint8_t v___y_1316_; lean_object* v_fst_1319_; lean_object* v_snd_1320_; lean_object* v_fst_1321_; lean_object* v_snd_1322_; uint8_t v___x_1323_; 
v_key_1313_ = lean_ctor_get(v___x_1312_, 0);
v_val_1314_ = lean_ctor_get(v___x_1312_, 1);
v_fst_1319_ = lean_ctor_get(v_x_1306_, 0);
v_snd_1320_ = lean_ctor_get(v_x_1306_, 1);
v_fst_1321_ = lean_ctor_get(v_key_1313_, 0);
v_snd_1322_ = lean_ctor_get(v_key_1313_, 1);
v___x_1323_ = lean_nat_dec_eq(v_fst_1319_, v_fst_1321_);
if (v___x_1323_ == 0)
{
v___y_1316_ = v___x_1323_;
goto v___jp_1315_;
}
else
{
uint8_t v___x_1324_; 
v___x_1324_ = lean_nat_dec_eq(v_snd_1320_, v_snd_1322_);
v___y_1316_ = v___x_1324_;
goto v___jp_1315_;
}
v___jp_1315_:
{
if (v___y_1316_ == 0)
{
lean_object* v___x_1317_; 
v___x_1317_ = lean_box(0);
return v___x_1317_;
}
else
{
lean_object* v___x_1318_; 
lean_inc(v_val_1314_);
v___x_1318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1318_, 0, v_val_1314_);
return v___x_1318_;
}
}
}
case 1:
{
lean_object* v_node_1325_; size_t v___x_1326_; size_t v___x_1327_; 
v_node_1325_ = lean_ctor_get(v___x_1312_, 0);
v___x_1326_ = ((size_t)5ULL);
v___x_1327_ = lean_usize_shift_right(v_x_1305_, v___x_1326_);
v_x_1304_ = v_node_1325_;
v_x_1305_ = v___x_1327_;
goto _start;
}
default: 
{
lean_object* v___x_1329_; 
v___x_1329_ = lean_box(0);
return v___x_1329_;
}
}
}
else
{
lean_object* v_ks_1330_; lean_object* v_vs_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; 
v_ks_1330_ = lean_ctor_get(v_x_1304_, 0);
v_vs_1331_ = lean_ctor_get(v_x_1304_, 1);
v___x_1332_ = lean_unsigned_to_nat(0u);
v___x_1333_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0_spec__0_spec__2___redArg(v_ks_1330_, v_vs_1331_, v___x_1332_, v_x_1306_);
return v___x_1333_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0_spec__0___redArg___boxed(lean_object* v_x_1334_, lean_object* v_x_1335_, lean_object* v_x_1336_){
_start:
{
size_t v_x_3869__boxed_1337_; lean_object* v_res_1338_; 
v_x_3869__boxed_1337_ = lean_unbox_usize(v_x_1335_);
lean_dec(v_x_1335_);
v_res_1338_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0_spec__0___redArg(v_x_1334_, v_x_3869__boxed_1337_, v_x_1336_);
lean_dec_ref(v_x_1336_);
lean_dec_ref(v_x_1334_);
return v_res_1338_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0___redArg(lean_object* v_x_1339_, lean_object* v_x_1340_){
_start:
{
lean_object* v_fst_1341_; lean_object* v_snd_1342_; uint64_t v___x_1343_; uint64_t v___x_1344_; uint64_t v___x_1345_; size_t v___x_1346_; lean_object* v___x_1347_; 
v_fst_1341_ = lean_ctor_get(v_x_1340_, 0);
v_snd_1342_ = lean_ctor_get(v_x_1340_, 1);
v___x_1343_ = lean_uint64_of_nat(v_fst_1341_);
v___x_1344_ = lean_uint64_of_nat(v_snd_1342_);
v___x_1345_ = lean_uint64_mix_hash(v___x_1343_, v___x_1344_);
v___x_1346_ = lean_uint64_to_usize(v___x_1345_);
v___x_1347_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0_spec__0___redArg(v_x_1339_, v___x_1346_, v_x_1340_);
return v___x_1347_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0___redArg___boxed(lean_object* v_x_1348_, lean_object* v_x_1349_){
_start:
{
lean_object* v_res_1350_; 
v_res_1350_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0___redArg(v_x_1348_, v_x_1349_);
lean_dec_ref(v_x_1349_);
lean_dec_ref(v_x_1348_);
return v_res_1350_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm(lean_object* v_term_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_, lean_object* v_a_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_){
_start:
{
uint8_t v___x_1361_; lean_object* v___y_1363_; lean_object* v___y_1364_; lean_object* v___y_1429_; lean_object* v___x_1433_; 
v___x_1361_ = 0;
v___x_1433_ = l_Lean_Syntax_getPos_x3f(v_term_1351_, v___x_1361_);
if (lean_obj_tag(v___x_1433_) == 0)
{
lean_object* v___x_1434_; 
v___x_1434_ = lean_unsigned_to_nat(0u);
v___y_1429_ = v___x_1434_;
goto v___jp_1428_;
}
else
{
lean_object* v_val_1435_; 
v_val_1435_ = lean_ctor_get(v___x_1433_, 0);
lean_inc(v_val_1435_);
lean_dec_ref_known(v___x_1433_, 1);
v___y_1429_ = v_val_1435_;
goto v___jp_1428_;
}
v___jp_1362_:
{
lean_object* v___x_1365_; lean_object* v_cache_1366_; lean_object* v_backwardRuleSyntax_1367_; lean_object* v_pos_1368_; lean_object* v___x_1369_; 
v___x_1365_ = lean_st_ref_get(v_a_1353_);
v_cache_1366_ = lean_ctor_get(v___x_1365_, 3);
lean_inc_ref(v_cache_1366_);
lean_dec(v___x_1365_);
v_backwardRuleSyntax_1367_ = lean_ctor_get(v_cache_1366_, 1);
lean_inc_ref(v_backwardRuleSyntax_1367_);
lean_dec_ref(v_cache_1366_);
v_pos_1368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_pos_1368_, 0, v___y_1363_);
lean_ctor_set(v_pos_1368_, 1, v___y_1364_);
v___x_1369_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0___redArg(v_backwardRuleSyntax_1367_, v_pos_1368_);
lean_dec_ref(v_backwardRuleSyntax_1367_);
if (lean_obj_tag(v___x_1369_) == 1)
{
lean_object* v_val_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1377_; 
lean_dec_ref_known(v_pos_1368_, 2);
lean_dec(v_term_1351_);
v_val_1370_ = lean_ctor_get(v___x_1369_, 0);
v_isSharedCheck_1377_ = !lean_is_exclusive(v___x_1369_);
if (v_isSharedCheck_1377_ == 0)
{
v___x_1372_ = v___x_1369_;
v_isShared_1373_ = v_isSharedCheck_1377_;
goto v_resetjp_1371_;
}
else
{
lean_inc(v_val_1370_);
lean_dec(v___x_1369_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1377_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
lean_object* v___x_1375_; 
if (v_isShared_1373_ == 0)
{
lean_ctor_set_tag(v___x_1372_, 0);
v___x_1375_ = v___x_1372_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v_val_1370_);
v___x_1375_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
return v___x_1375_;
}
}
}
else
{
lean_object* v___x_1378_; uint8_t v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___f_1382_; lean_object* v___x_1383_; 
lean_dec(v___x_1369_);
v___x_1378_ = lean_box(0);
v___x_1379_ = 1;
v___x_1380_ = lean_box(v___x_1379_);
v___x_1381_ = lean_box(v___x_1361_);
v___f_1382_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm___lam__0___boxed), 13, 4);
lean_closure_set(v___f_1382_, 0, v_term_1351_);
lean_closure_set(v___f_1382_, 1, v___x_1378_);
lean_closure_set(v___f_1382_, 2, v___x_1380_);
lean_closure_set(v___f_1382_, 3, v___x_1381_);
v___x_1383_ = l_Lean_Elab_Tactic_Grind_withMainContext___redArg(v___f_1382_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_, v_a_1359_);
if (lean_obj_tag(v___x_1383_) == 0)
{
lean_object* v_a_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; 
v_a_1384_ = lean_ctor_get(v___x_1383_, 0);
lean_inc(v_a_1384_);
lean_dec_ref_known(v___x_1383_, 1);
v___x_1385_ = lean_box(0);
v___x_1386_ = l_Lean_Meta_Sym_mkBackwardRuleFromExpr(v_a_1384_, v___x_1385_, v___x_1378_, v_a_1356_, v_a_1357_, v_a_1358_, v_a_1359_);
if (lean_obj_tag(v___x_1386_) == 0)
{
lean_object* v_a_1387_; lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1419_; 
v_a_1387_ = lean_ctor_get(v___x_1386_, 0);
v_isSharedCheck_1419_ = !lean_is_exclusive(v___x_1386_);
if (v_isSharedCheck_1419_ == 0)
{
v___x_1389_ = v___x_1386_;
v_isShared_1390_ = v_isSharedCheck_1419_;
goto v_resetjp_1388_;
}
else
{
lean_inc(v_a_1387_);
lean_dec(v___x_1386_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1419_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
lean_object* v___x_1391_; lean_object* v_cache_1392_; lean_object* v_symState_1393_; lean_object* v_grindState_1394_; lean_object* v_goals_1395_; lean_object* v___x_1397_; uint8_t v_isShared_1398_; uint8_t v_isSharedCheck_1418_; 
v___x_1391_ = lean_st_ref_take(v_a_1353_);
v_cache_1392_ = lean_ctor_get(v___x_1391_, 3);
v_symState_1393_ = lean_ctor_get(v___x_1391_, 0);
v_grindState_1394_ = lean_ctor_get(v___x_1391_, 1);
v_goals_1395_ = lean_ctor_get(v___x_1391_, 2);
v_isSharedCheck_1418_ = !lean_is_exclusive(v___x_1391_);
if (v_isSharedCheck_1418_ == 0)
{
v___x_1397_ = v___x_1391_;
v_isShared_1398_ = v_isSharedCheck_1418_;
goto v_resetjp_1396_;
}
else
{
lean_inc(v_cache_1392_);
lean_inc(v_goals_1395_);
lean_inc(v_grindState_1394_);
lean_inc(v_symState_1393_);
lean_dec(v___x_1391_);
v___x_1397_ = lean_box(0);
v_isShared_1398_ = v_isSharedCheck_1418_;
goto v_resetjp_1396_;
}
v_resetjp_1396_:
{
lean_object* v_backwardRuleName_1399_; lean_object* v_backwardRuleSyntax_1400_; lean_object* v_simpState_1401_; lean_object* v_dsimpState_1402_; lean_object* v___x_1404_; uint8_t v_isShared_1405_; uint8_t v_isSharedCheck_1417_; 
v_backwardRuleName_1399_ = lean_ctor_get(v_cache_1392_, 0);
v_backwardRuleSyntax_1400_ = lean_ctor_get(v_cache_1392_, 1);
v_simpState_1401_ = lean_ctor_get(v_cache_1392_, 2);
v_dsimpState_1402_ = lean_ctor_get(v_cache_1392_, 3);
v_isSharedCheck_1417_ = !lean_is_exclusive(v_cache_1392_);
if (v_isSharedCheck_1417_ == 0)
{
v___x_1404_ = v_cache_1392_;
v_isShared_1405_ = v_isSharedCheck_1417_;
goto v_resetjp_1403_;
}
else
{
lean_inc(v_dsimpState_1402_);
lean_inc(v_simpState_1401_);
lean_inc(v_backwardRuleSyntax_1400_);
lean_inc(v_backwardRuleName_1399_);
lean_dec(v_cache_1392_);
v___x_1404_ = lean_box(0);
v_isShared_1405_ = v_isSharedCheck_1417_;
goto v_resetjp_1403_;
}
v_resetjp_1403_:
{
lean_object* v___x_1406_; lean_object* v___x_1408_; 
lean_inc(v_a_1387_);
v___x_1406_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2___redArg(v_backwardRuleSyntax_1400_, v_pos_1368_, v_a_1387_);
if (v_isShared_1405_ == 0)
{
lean_ctor_set(v___x_1404_, 1, v___x_1406_);
v___x_1408_ = v___x_1404_;
goto v_reusejp_1407_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v_backwardRuleName_1399_);
lean_ctor_set(v_reuseFailAlloc_1416_, 1, v___x_1406_);
lean_ctor_set(v_reuseFailAlloc_1416_, 2, v_simpState_1401_);
lean_ctor_set(v_reuseFailAlloc_1416_, 3, v_dsimpState_1402_);
v___x_1408_ = v_reuseFailAlloc_1416_;
goto v_reusejp_1407_;
}
v_reusejp_1407_:
{
lean_object* v___x_1410_; 
if (v_isShared_1398_ == 0)
{
lean_ctor_set(v___x_1397_, 3, v___x_1408_);
v___x_1410_ = v___x_1397_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v_symState_1393_);
lean_ctor_set(v_reuseFailAlloc_1415_, 1, v_grindState_1394_);
lean_ctor_set(v_reuseFailAlloc_1415_, 2, v_goals_1395_);
lean_ctor_set(v_reuseFailAlloc_1415_, 3, v___x_1408_);
v___x_1410_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
lean_object* v___x_1411_; lean_object* v___x_1413_; 
v___x_1411_ = lean_st_ref_set(v_a_1353_, v___x_1410_);
if (v_isShared_1390_ == 0)
{
v___x_1413_ = v___x_1389_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v_a_1387_);
v___x_1413_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
return v___x_1413_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_pos_1368_, 2);
return v___x_1386_;
}
}
else
{
lean_object* v_a_1420_; lean_object* v___x_1422_; uint8_t v_isShared_1423_; uint8_t v_isSharedCheck_1427_; 
lean_dec_ref_known(v_pos_1368_, 2);
v_a_1420_ = lean_ctor_get(v___x_1383_, 0);
v_isSharedCheck_1427_ = !lean_is_exclusive(v___x_1383_);
if (v_isSharedCheck_1427_ == 0)
{
v___x_1422_ = v___x_1383_;
v_isShared_1423_ = v_isSharedCheck_1427_;
goto v_resetjp_1421_;
}
else
{
lean_inc(v_a_1420_);
lean_dec(v___x_1383_);
v___x_1422_ = lean_box(0);
v_isShared_1423_ = v_isSharedCheck_1427_;
goto v_resetjp_1421_;
}
v_resetjp_1421_:
{
lean_object* v___x_1425_; 
if (v_isShared_1423_ == 0)
{
v___x_1425_ = v___x_1422_;
goto v_reusejp_1424_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v_a_1420_);
v___x_1425_ = v_reuseFailAlloc_1426_;
goto v_reusejp_1424_;
}
v_reusejp_1424_:
{
return v___x_1425_;
}
}
}
}
}
v___jp_1428_:
{
lean_object* v___x_1430_; 
v___x_1430_ = l_Lean_Syntax_getTailPos_x3f(v_term_1351_, v___x_1361_);
if (lean_obj_tag(v___x_1430_) == 0)
{
lean_object* v___x_1431_; 
v___x_1431_ = lean_unsigned_to_nat(0u);
v___y_1363_ = v___y_1429_;
v___y_1364_ = v___x_1431_;
goto v___jp_1362_;
}
else
{
lean_object* v_val_1432_; 
v_val_1432_ = lean_ctor_get(v___x_1430_, 0);
lean_inc(v_val_1432_);
lean_dec_ref_known(v___x_1430_, 1);
v___y_1363_ = v___y_1429_;
v___y_1364_ = v_val_1432_;
goto v___jp_1362_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm___boxed(lean_object* v_term_1436_, lean_object* v_a_1437_, lean_object* v_a_1438_, lean_object* v_a_1439_, lean_object* v_a_1440_, lean_object* v_a_1441_, lean_object* v_a_1442_, lean_object* v_a_1443_, lean_object* v_a_1444_, lean_object* v_a_1445_){
_start:
{
lean_object* v_res_1446_; 
v_res_1446_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm(v_term_1436_, v_a_1437_, v_a_1438_, v_a_1439_, v_a_1440_, v_a_1441_, v_a_1442_, v_a_1443_, v_a_1444_);
lean_dec(v_a_1444_);
lean_dec_ref(v_a_1443_);
lean_dec(v_a_1442_);
lean_dec_ref(v_a_1441_);
lean_dec(v_a_1440_);
lean_dec_ref(v_a_1439_);
lean_dec(v_a_1438_);
lean_dec_ref(v_a_1437_);
return v_res_1446_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0(lean_object* v_00_u03b2_1447_, lean_object* v_x_1448_, lean_object* v_x_1449_){
_start:
{
lean_object* v___x_1450_; 
v___x_1450_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0___redArg(v_x_1448_, v_x_1449_);
return v___x_1450_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0___boxed(lean_object* v_00_u03b2_1451_, lean_object* v_x_1452_, lean_object* v_x_1453_){
_start:
{
lean_object* v_res_1454_; 
v_res_1454_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0(v_00_u03b2_1451_, v_x_1452_, v_x_1453_);
lean_dec_ref(v_x_1453_);
lean_dec_ref(v_x_1452_);
return v_res_1454_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2(lean_object* v_00_u03b2_1455_, lean_object* v_x_1456_, lean_object* v_x_1457_, lean_object* v_x_1458_){
_start:
{
lean_object* v___x_1459_; 
v___x_1459_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2___redArg(v_x_1456_, v_x_1457_, v_x_1458_);
return v___x_1459_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0_spec__0(lean_object* v_00_u03b2_1460_, lean_object* v_x_1461_, size_t v_x_1462_, lean_object* v_x_1463_){
_start:
{
lean_object* v___x_1464_; 
v___x_1464_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0_spec__0___redArg(v_x_1461_, v_x_1462_, v_x_1463_);
return v___x_1464_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1465_, lean_object* v_x_1466_, lean_object* v_x_1467_, lean_object* v_x_1468_){
_start:
{
size_t v_x_4098__boxed_1469_; lean_object* v_res_1470_; 
v_x_4098__boxed_1469_ = lean_unbox_usize(v_x_1467_);
lean_dec(v_x_1467_);
v_res_1470_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0_spec__0(v_00_u03b2_1465_, v_x_1466_, v_x_4098__boxed_1469_, v_x_1468_);
lean_dec_ref(v_x_1468_);
lean_dec_ref(v_x_1466_);
return v_res_1470_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3(lean_object* v_00_u03b2_1471_, lean_object* v_x_1472_, size_t v_x_1473_, size_t v_x_1474_, lean_object* v_x_1475_, lean_object* v_x_1476_){
_start:
{
lean_object* v___x_1477_; 
v___x_1477_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3___redArg(v_x_1472_, v_x_1473_, v_x_1474_, v_x_1475_, v_x_1476_);
return v___x_1477_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3___boxed(lean_object* v_00_u03b2_1478_, lean_object* v_x_1479_, lean_object* v_x_1480_, lean_object* v_x_1481_, lean_object* v_x_1482_, lean_object* v_x_1483_){
_start:
{
size_t v_x_4109__boxed_1484_; size_t v_x_4110__boxed_1485_; lean_object* v_res_1486_; 
v_x_4109__boxed_1484_ = lean_unbox_usize(v_x_1480_);
lean_dec(v_x_1480_);
v_x_4110__boxed_1485_ = lean_unbox_usize(v_x_1481_);
lean_dec(v_x_1481_);
v_res_1486_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3(v_00_u03b2_1478_, v_x_1479_, v_x_4109__boxed_1484_, v_x_4110__boxed_1485_, v_x_1482_, v_x_1483_);
return v_res_1486_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1487_, lean_object* v_keys_1488_, lean_object* v_vals_1489_, lean_object* v_heq_1490_, lean_object* v_i_1491_, lean_object* v_k_1492_){
_start:
{
lean_object* v___x_1493_; 
v___x_1493_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0_spec__0_spec__2___redArg(v_keys_1488_, v_vals_1489_, v_i_1491_, v_k_1492_);
return v___x_1493_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1494_, lean_object* v_keys_1495_, lean_object* v_vals_1496_, lean_object* v_heq_1497_, lean_object* v_i_1498_, lean_object* v_k_1499_){
_start:
{
lean_object* v_res_1500_; 
v_res_1500_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__0_spec__0_spec__2(v_00_u03b2_1494_, v_keys_1495_, v_vals_1496_, v_heq_1497_, v_i_1498_, v_k_1499_);
lean_dec_ref(v_k_1499_);
lean_dec_ref(v_vals_1496_);
lean_dec_ref(v_keys_1495_);
return v_res_1500_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_1501_, lean_object* v_n_1502_, lean_object* v_k_1503_, lean_object* v_v_1504_){
_start:
{
lean_object* v___x_1505_; 
v___x_1505_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3_spec__5___redArg(v_n_1502_, v_k_1503_, v_v_1504_);
return v___x_1505_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3_spec__6(lean_object* v_00_u03b2_1506_, size_t v_depth_1507_, lean_object* v_keys_1508_, lean_object* v_vals_1509_, lean_object* v_heq_1510_, lean_object* v_i_1511_, lean_object* v_entries_1512_){
_start:
{
lean_object* v___x_1513_; 
v___x_1513_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3_spec__6___redArg(v_depth_1507_, v_keys_1508_, v_vals_1509_, v_i_1511_, v_entries_1512_);
return v___x_1513_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3_spec__6___boxed(lean_object* v_00_u03b2_1514_, lean_object* v_depth_1515_, lean_object* v_keys_1516_, lean_object* v_vals_1517_, lean_object* v_heq_1518_, lean_object* v_i_1519_, lean_object* v_entries_1520_){
_start:
{
size_t v_depth_boxed_1521_; lean_object* v_res_1522_; 
v_depth_boxed_1521_ = lean_unbox_usize(v_depth_1515_);
lean_dec(v_depth_1515_);
v_res_1522_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3_spec__6(v_00_u03b2_1514_, v_depth_boxed_1521_, v_keys_1516_, v_vals_1517_, v_heq_1518_, v_i_1519_, v_entries_1520_);
lean_dec_ref(v_vals_1517_);
lean_dec_ref(v_keys_1516_);
return v_res_1522_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3_spec__5_spec__6(lean_object* v_00_u03b2_1523_, lean_object* v_x_1524_, lean_object* v_x_1525_, lean_object* v_x_1526_, lean_object* v_x_1527_){
_start:
{
lean_object* v___x_1528_; 
v___x_1528_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm_spec__2_spec__3_spec__5_spec__6___redArg(v_x_1524_, v_x_1525_, v_x_1526_, v_x_1527_);
return v___x_1528_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply_spec__0___redArg___lam__0(lean_object* v_x_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_){
_start:
{
lean_object* v___x_1539_; 
lean_inc(v___y_1533_);
lean_inc_ref(v___y_1532_);
lean_inc(v___y_1531_);
lean_inc_ref(v___y_1530_);
v___x_1539_ = lean_apply_9(v_x_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_, lean_box(0));
return v___x_1539_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply_spec__0___redArg___lam__0___boxed(lean_object* v_x_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_){
_start:
{
lean_object* v_res_1550_; 
v_res_1550_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply_spec__0___redArg___lam__0(v_x_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_);
lean_dec(v___y_1544_);
lean_dec_ref(v___y_1543_);
lean_dec(v___y_1542_);
lean_dec_ref(v___y_1541_);
return v_res_1550_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply_spec__0___redArg(lean_object* v_mvarId_1551_, lean_object* v_x_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_){
_start:
{
lean_object* v___f_1562_; lean_object* v___x_1563_; 
lean_inc(v___y_1556_);
lean_inc_ref(v___y_1555_);
lean_inc(v___y_1554_);
lean_inc_ref(v___y_1553_);
v___f_1562_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply_spec__0___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_1562_, 0, v_x_1552_);
lean_closure_set(v___f_1562_, 1, v___y_1553_);
lean_closure_set(v___f_1562_, 2, v___y_1554_);
lean_closure_set(v___f_1562_, 3, v___y_1555_);
lean_closure_set(v___f_1562_, 4, v___y_1556_);
v___x_1563_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1551_, v___f_1562_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_);
if (lean_obj_tag(v___x_1563_) == 0)
{
return v___x_1563_;
}
else
{
lean_object* v_a_1564_; lean_object* v___x_1566_; uint8_t v_isShared_1567_; uint8_t v_isSharedCheck_1571_; 
v_a_1564_ = lean_ctor_get(v___x_1563_, 0);
v_isSharedCheck_1571_ = !lean_is_exclusive(v___x_1563_);
if (v_isSharedCheck_1571_ == 0)
{
v___x_1566_ = v___x_1563_;
v_isShared_1567_ = v_isSharedCheck_1571_;
goto v_resetjp_1565_;
}
else
{
lean_inc(v_a_1564_);
lean_dec(v___x_1563_);
v___x_1566_ = lean_box(0);
v_isShared_1567_ = v_isSharedCheck_1571_;
goto v_resetjp_1565_;
}
v_resetjp_1565_:
{
lean_object* v___x_1569_; 
if (v_isShared_1567_ == 0)
{
v___x_1569_ = v___x_1566_;
goto v_reusejp_1568_;
}
else
{
lean_object* v_reuseFailAlloc_1570_; 
v_reuseFailAlloc_1570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1570_, 0, v_a_1564_);
v___x_1569_ = v_reuseFailAlloc_1570_;
goto v_reusejp_1568_;
}
v_reusejp_1568_:
{
return v___x_1569_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply_spec__0___redArg___boxed(lean_object* v_mvarId_1572_, lean_object* v_x_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_){
_start:
{
lean_object* v_res_1583_; 
v_res_1583_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply_spec__0___redArg(v_mvarId_1572_, v_x_1573_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_, v___y_1581_);
lean_dec(v___y_1581_);
lean_dec_ref(v___y_1580_);
lean_dec(v___y_1579_);
lean_dec_ref(v___y_1578_);
lean_dec(v___y_1577_);
lean_dec_ref(v___y_1576_);
lean_dec(v___y_1575_);
lean_dec_ref(v___y_1574_);
return v_res_1583_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply_spec__0(lean_object* v_00_u03b1_1584_, lean_object* v_mvarId_1585_, lean_object* v_x_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_){
_start:
{
lean_object* v___x_1596_; 
v___x_1596_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply_spec__0___redArg(v_mvarId_1585_, v_x_1586_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_);
return v___x_1596_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply_spec__0___boxed(lean_object* v_00_u03b1_1597_, lean_object* v_mvarId_1598_, lean_object* v_x_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_){
_start:
{
lean_object* v_res_1609_; 
v_res_1609_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply_spec__0(v_00_u03b1_1597_, v_mvarId_1598_, v_x_1599_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_);
lean_dec(v___y_1607_);
lean_dec_ref(v___y_1606_);
lean_dec(v___y_1605_);
lean_dec_ref(v___y_1604_);
lean_dec(v___y_1603_);
lean_dec_ref(v___y_1602_);
lean_dec(v___y_1601_);
lean_dec_ref(v___y_1600_);
return v_res_1609_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1611_; lean_object* v___x_1612_; 
v___x_1611_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___lam__0___closed__0));
v___x_1612_ = l_Lean_stringToMessageData(v___x_1611_);
return v___x_1612_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___lam__0(lean_object* v_a_1613_, lean_object* v_rule_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_){
_start:
{
lean_object* v___x_1624_; lean_object* v___x_1625_; 
v___x_1624_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Goal_apply___boxed), 9, 2);
lean_closure_set(v___x_1624_, 0, v_a_1613_);
lean_closure_set(v___x_1624_, 1, v_rule_1614_);
v___x_1625_ = l_Lean_Elab_Tactic_Grind_liftSymM___redArg(v___x_1624_, v___y_1615_, v___y_1616_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_);
if (lean_obj_tag(v___x_1625_) == 0)
{
lean_object* v_a_1626_; 
v_a_1626_ = lean_ctor_get(v___x_1625_, 0);
lean_inc(v_a_1626_);
lean_dec_ref_known(v___x_1625_, 1);
if (lean_obj_tag(v_a_1626_) == 0)
{
lean_object* v___x_1627_; lean_object* v___x_1628_; 
v___x_1627_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___lam__0___closed__1, &l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___lam__0___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___lam__0___closed__1);
v___x_1628_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__2___redArg(v___x_1627_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_);
return v___x_1628_;
}
else
{
lean_object* v_subgoals_1629_; lean_object* v___x_1630_; 
v_subgoals_1629_ = lean_ctor_get(v_a_1626_, 0);
lean_inc(v_subgoals_1629_);
lean_dec_ref_known(v_a_1626_, 1);
v___x_1630_ = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(v_subgoals_1629_, v___y_1616_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_);
return v___x_1630_;
}
}
else
{
lean_object* v_a_1631_; lean_object* v___x_1633_; uint8_t v_isShared_1634_; uint8_t v_isSharedCheck_1638_; 
v_a_1631_ = lean_ctor_get(v___x_1625_, 0);
v_isSharedCheck_1638_ = !lean_is_exclusive(v___x_1625_);
if (v_isSharedCheck_1638_ == 0)
{
v___x_1633_ = v___x_1625_;
v_isShared_1634_ = v_isSharedCheck_1638_;
goto v_resetjp_1632_;
}
else
{
lean_inc(v_a_1631_);
lean_dec(v___x_1625_);
v___x_1633_ = lean_box(0);
v_isShared_1634_ = v_isSharedCheck_1638_;
goto v_resetjp_1632_;
}
v_resetjp_1632_:
{
lean_object* v___x_1636_; 
if (v_isShared_1634_ == 0)
{
v___x_1636_ = v___x_1633_;
goto v_reusejp_1635_;
}
else
{
lean_object* v_reuseFailAlloc_1637_; 
v_reuseFailAlloc_1637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1637_, 0, v_a_1631_);
v___x_1636_ = v_reuseFailAlloc_1637_;
goto v_reusejp_1635_;
}
v_reusejp_1635_:
{
return v___x_1636_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___lam__0___boxed(lean_object* v_a_1639_, lean_object* v_rule_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_){
_start:
{
lean_object* v_res_1650_; 
v_res_1650_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___lam__0(v_a_1639_, v_rule_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_, v___y_1648_);
lean_dec(v___y_1648_);
lean_dec_ref(v___y_1647_);
lean_dec(v___y_1646_);
lean_dec_ref(v___y_1645_);
lean_dec(v___y_1644_);
lean_dec_ref(v___y_1643_);
lean_dec(v___y_1642_);
lean_dec_ref(v___y_1641_);
return v_res_1650_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___lam__1(uint8_t v___x_1651_, lean_object* v___x_1652_, lean_object* v___f_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_){
_start:
{
if (v___x_1651_ == 0)
{
lean_object* v___x_1663_; 
v___x_1663_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm(v___x_1652_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_);
if (lean_obj_tag(v___x_1663_) == 0)
{
lean_object* v_a_1664_; lean_object* v___x_1665_; 
v_a_1664_ = lean_ctor_get(v___x_1663_, 0);
lean_inc(v_a_1664_);
lean_dec_ref_known(v___x_1663_, 1);
lean_inc(v___y_1661_);
lean_inc_ref(v___y_1660_);
lean_inc(v___y_1659_);
lean_inc_ref(v___y_1658_);
lean_inc(v___y_1657_);
lean_inc_ref(v___y_1656_);
lean_inc(v___y_1655_);
lean_inc_ref(v___y_1654_);
v___x_1665_ = lean_apply_10(v___f_1653_, v_a_1664_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_, lean_box(0));
return v___x_1665_;
}
else
{
lean_object* v_a_1666_; lean_object* v___x_1668_; uint8_t v_isShared_1669_; uint8_t v_isSharedCheck_1673_; 
lean_dec_ref(v___f_1653_);
v_a_1666_ = lean_ctor_get(v___x_1663_, 0);
v_isSharedCheck_1673_ = !lean_is_exclusive(v___x_1663_);
if (v_isSharedCheck_1673_ == 0)
{
v___x_1668_ = v___x_1663_;
v_isShared_1669_ = v_isSharedCheck_1673_;
goto v_resetjp_1667_;
}
else
{
lean_inc(v_a_1666_);
lean_dec(v___x_1663_);
v___x_1668_ = lean_box(0);
v_isShared_1669_ = v_isSharedCheck_1673_;
goto v_resetjp_1667_;
}
v_resetjp_1667_:
{
lean_object* v___x_1671_; 
if (v_isShared_1669_ == 0)
{
v___x_1671_ = v___x_1668_;
goto v_reusejp_1670_;
}
else
{
lean_object* v_reuseFailAlloc_1672_; 
v_reuseFailAlloc_1672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1672_, 0, v_a_1666_);
v___x_1671_ = v_reuseFailAlloc_1672_;
goto v_reusejp_1670_;
}
v_reusejp_1670_:
{
return v___x_1671_;
}
}
}
}
else
{
lean_object* v___x_1674_; 
v___x_1674_ = l_Lean_Elab_Tactic_Grind_saveState___redArg(v___y_1655_, v___y_1657_, v___y_1659_, v___y_1661_);
if (lean_obj_tag(v___x_1674_) == 0)
{
lean_object* v_a_1675_; lean_object* v___x_1677_; uint8_t v_isShared_1678_; uint8_t v_isSharedCheck_1708_; 
v_a_1675_ = lean_ctor_get(v___x_1674_, 0);
v_isSharedCheck_1708_ = !lean_is_exclusive(v___x_1674_);
if (v_isSharedCheck_1708_ == 0)
{
v___x_1677_ = v___x_1674_;
v_isShared_1678_ = v_isSharedCheck_1708_;
goto v_resetjp_1676_;
}
else
{
lean_inc(v_a_1675_);
lean_dec(v___x_1674_);
v___x_1677_ = lean_box(0);
v_isShared_1678_ = v_isSharedCheck_1708_;
goto v_resetjp_1676_;
}
v_resetjp_1676_:
{
lean_object* v___y_1680_; uint8_t v___y_1681_; lean_object* v_a_1698_; lean_object* v___x_1701_; 
lean_inc(v___x_1652_);
v___x_1701_ = l_Lean_realizeGlobalConstNoOverload(v___x_1652_, v___y_1660_, v___y_1661_);
if (lean_obj_tag(v___x_1701_) == 0)
{
lean_object* v_a_1702_; lean_object* v___x_1703_; 
v_a_1702_ = lean_ctor_get(v___x_1701_, 0);
lean_inc(v_a_1702_);
lean_dec_ref_known(v___x_1701_, 1);
v___x_1703_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRule___redArg(v_a_1702_, v___y_1655_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_);
if (lean_obj_tag(v___x_1703_) == 0)
{
lean_object* v_a_1704_; lean_object* v___x_1705_; 
lean_del_object(v___x_1677_);
lean_dec(v_a_1675_);
lean_dec(v___x_1652_);
v_a_1704_ = lean_ctor_get(v___x_1703_, 0);
lean_inc(v_a_1704_);
lean_dec_ref_known(v___x_1703_, 1);
lean_inc(v___y_1661_);
lean_inc_ref(v___y_1660_);
lean_inc(v___y_1659_);
lean_inc_ref(v___y_1658_);
lean_inc(v___y_1657_);
lean_inc_ref(v___y_1656_);
lean_inc(v___y_1655_);
lean_inc_ref(v___y_1654_);
v___x_1705_ = lean_apply_10(v___f_1653_, v_a_1704_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_, lean_box(0));
return v___x_1705_;
}
else
{
lean_object* v_a_1706_; 
v_a_1706_ = lean_ctor_get(v___x_1703_, 0);
lean_inc(v_a_1706_);
lean_dec_ref_known(v___x_1703_, 1);
v_a_1698_ = v_a_1706_;
goto v___jp_1697_;
}
}
else
{
lean_object* v_a_1707_; 
v_a_1707_ = lean_ctor_get(v___x_1701_, 0);
lean_inc(v_a_1707_);
lean_dec_ref_known(v___x_1701_, 1);
v_a_1698_ = v_a_1707_;
goto v___jp_1697_;
}
v___jp_1679_:
{
if (v___y_1681_ == 0)
{
lean_object* v___x_1682_; 
lean_dec_ref(v___y_1680_);
lean_del_object(v___x_1677_);
v___x_1682_ = l_Lean_Elab_Tactic_Grind_SavedState_restore___redArg(v_a_1675_, v___y_1681_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_);
if (lean_obj_tag(v___x_1682_) == 0)
{
lean_object* v___x_1683_; 
lean_dec_ref_known(v___x_1682_, 1);
v___x_1683_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_getOrCreateBackwardRuleFromTerm(v___x_1652_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_);
if (lean_obj_tag(v___x_1683_) == 0)
{
lean_object* v_a_1684_; lean_object* v___x_1685_; 
v_a_1684_ = lean_ctor_get(v___x_1683_, 0);
lean_inc(v_a_1684_);
lean_dec_ref_known(v___x_1683_, 1);
lean_inc(v___y_1661_);
lean_inc_ref(v___y_1660_);
lean_inc(v___y_1659_);
lean_inc_ref(v___y_1658_);
lean_inc(v___y_1657_);
lean_inc_ref(v___y_1656_);
lean_inc(v___y_1655_);
lean_inc_ref(v___y_1654_);
v___x_1685_ = lean_apply_10(v___f_1653_, v_a_1684_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_, lean_box(0));
return v___x_1685_;
}
else
{
lean_object* v_a_1686_; lean_object* v___x_1688_; uint8_t v_isShared_1689_; uint8_t v_isSharedCheck_1693_; 
lean_dec_ref(v___f_1653_);
v_a_1686_ = lean_ctor_get(v___x_1683_, 0);
v_isSharedCheck_1693_ = !lean_is_exclusive(v___x_1683_);
if (v_isSharedCheck_1693_ == 0)
{
v___x_1688_ = v___x_1683_;
v_isShared_1689_ = v_isSharedCheck_1693_;
goto v_resetjp_1687_;
}
else
{
lean_inc(v_a_1686_);
lean_dec(v___x_1683_);
v___x_1688_ = lean_box(0);
v_isShared_1689_ = v_isSharedCheck_1693_;
goto v_resetjp_1687_;
}
v_resetjp_1687_:
{
lean_object* v___x_1691_; 
if (v_isShared_1689_ == 0)
{
v___x_1691_ = v___x_1688_;
goto v_reusejp_1690_;
}
else
{
lean_object* v_reuseFailAlloc_1692_; 
v_reuseFailAlloc_1692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1692_, 0, v_a_1686_);
v___x_1691_ = v_reuseFailAlloc_1692_;
goto v_reusejp_1690_;
}
v_reusejp_1690_:
{
return v___x_1691_;
}
}
}
}
else
{
lean_dec_ref(v___f_1653_);
lean_dec(v___x_1652_);
return v___x_1682_;
}
}
else
{
lean_object* v___x_1695_; 
lean_dec(v_a_1675_);
lean_dec_ref(v___f_1653_);
lean_dec(v___x_1652_);
if (v_isShared_1678_ == 0)
{
lean_ctor_set_tag(v___x_1677_, 1);
lean_ctor_set(v___x_1677_, 0, v___y_1680_);
v___x_1695_ = v___x_1677_;
goto v_reusejp_1694_;
}
else
{
lean_object* v_reuseFailAlloc_1696_; 
v_reuseFailAlloc_1696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1696_, 0, v___y_1680_);
v___x_1695_ = v_reuseFailAlloc_1696_;
goto v_reusejp_1694_;
}
v_reusejp_1694_:
{
return v___x_1695_;
}
}
}
v___jp_1697_:
{
uint8_t v___x_1699_; 
v___x_1699_ = l_Lean_Exception_isInterrupt(v_a_1698_);
if (v___x_1699_ == 0)
{
uint8_t v___x_1700_; 
lean_inc_ref(v_a_1698_);
v___x_1700_ = l_Lean_Exception_isRuntime(v_a_1698_);
v___y_1680_ = v_a_1698_;
v___y_1681_ = v___x_1700_;
goto v___jp_1679_;
}
else
{
v___y_1680_ = v_a_1698_;
v___y_1681_ = v___x_1699_;
goto v___jp_1679_;
}
}
}
}
else
{
lean_object* v_a_1709_; lean_object* v___x_1711_; uint8_t v_isShared_1712_; uint8_t v_isSharedCheck_1716_; 
lean_dec_ref(v___f_1653_);
lean_dec(v___x_1652_);
v_a_1709_ = lean_ctor_get(v___x_1674_, 0);
v_isSharedCheck_1716_ = !lean_is_exclusive(v___x_1674_);
if (v_isSharedCheck_1716_ == 0)
{
v___x_1711_ = v___x_1674_;
v_isShared_1712_ = v_isSharedCheck_1716_;
goto v_resetjp_1710_;
}
else
{
lean_inc(v_a_1709_);
lean_dec(v___x_1674_);
v___x_1711_ = lean_box(0);
v_isShared_1712_ = v_isSharedCheck_1716_;
goto v_resetjp_1710_;
}
v_resetjp_1710_:
{
lean_object* v___x_1714_; 
if (v_isShared_1712_ == 0)
{
v___x_1714_ = v___x_1711_;
goto v_reusejp_1713_;
}
else
{
lean_object* v_reuseFailAlloc_1715_; 
v_reuseFailAlloc_1715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1715_, 0, v_a_1709_);
v___x_1714_ = v_reuseFailAlloc_1715_;
goto v_reusejp_1713_;
}
v_reusejp_1713_:
{
return v___x_1714_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___lam__1___boxed(lean_object* v___x_1717_, lean_object* v___x_1718_, lean_object* v___f_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_){
_start:
{
uint8_t v___x_3542__boxed_1729_; lean_object* v_res_1730_; 
v___x_3542__boxed_1729_ = lean_unbox(v___x_1717_);
v_res_1730_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___lam__1(v___x_3542__boxed_1729_, v___x_1718_, v___f_1719_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_);
lean_dec(v___y_1727_);
lean_dec_ref(v___y_1726_);
lean_dec(v___y_1725_);
lean_dec_ref(v___y_1724_);
lean_dec(v___y_1723_);
lean_dec_ref(v___y_1722_);
lean_dec(v___y_1721_);
lean_dec_ref(v___y_1720_);
return v_res_1730_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply(lean_object* v_stx_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_, lean_object* v_a_1741_, lean_object* v_a_1742_, lean_object* v_a_1743_, lean_object* v_a_1744_, lean_object* v_a_1745_, lean_object* v_a_1746_){
_start:
{
lean_object* v___x_1748_; 
v___x_1748_ = l_Lean_Elab_Tactic_Grind_ensureSym___redArg(v_a_1739_, v_a_1743_, v_a_1744_, v_a_1745_, v_a_1746_);
if (lean_obj_tag(v___x_1748_) == 0)
{
lean_object* v___x_1749_; uint8_t v___x_1750_; 
lean_dec_ref_known(v___x_1748_, 1);
v___x_1749_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___closed__1));
lean_inc(v_stx_1738_);
v___x_1750_ = l_Lean_Syntax_isOfKind(v_stx_1738_, v___x_1749_);
if (v___x_1750_ == 0)
{
lean_object* v___x_1751_; 
lean_dec(v_stx_1738_);
v___x_1751_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro_spec__0___redArg();
return v___x_1751_;
}
else
{
lean_object* v___x_1752_; 
v___x_1752_ = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(v_a_1740_, v_a_1743_, v_a_1744_, v_a_1745_, v_a_1746_);
if (lean_obj_tag(v___x_1752_) == 0)
{
lean_object* v_a_1753_; lean_object* v_mvarId_1754_; lean_object* v___f_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; uint8_t v___x_1759_; lean_object* v___x_1760_; lean_object* v___y_1761_; lean_object* v___x_1762_; 
v_a_1753_ = lean_ctor_get(v___x_1752_, 0);
lean_inc(v_a_1753_);
lean_dec_ref_known(v___x_1752_, 1);
v_mvarId_1754_ = lean_ctor_get(v_a_1753_, 1);
lean_inc(v_mvarId_1754_);
v___f_1755_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___lam__0___boxed), 11, 1);
lean_closure_set(v___f_1755_, 0, v_a_1753_);
v___x_1756_ = lean_unsigned_to_nat(1u);
v___x_1757_ = l_Lean_Syntax_getArg(v_stx_1738_, v___x_1756_);
lean_dec(v_stx_1738_);
v___x_1758_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__1___redArg___closed__6));
lean_inc(v___x_1757_);
v___x_1759_ = l_Lean_Syntax_isOfKind(v___x_1757_, v___x_1758_);
v___x_1760_ = lean_box(v___x_1759_);
v___y_1761_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___lam__1___boxed), 12, 3);
lean_closure_set(v___y_1761_, 0, v___x_1760_);
lean_closure_set(v___y_1761_, 1, v___x_1757_);
lean_closure_set(v___y_1761_, 2, v___f_1755_);
v___x_1762_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply_spec__0___redArg(v_mvarId_1754_, v___y_1761_, v_a_1739_, v_a_1740_, v_a_1741_, v_a_1742_, v_a_1743_, v_a_1744_, v_a_1745_, v_a_1746_);
return v___x_1762_;
}
else
{
lean_object* v_a_1763_; lean_object* v___x_1765_; uint8_t v_isShared_1766_; uint8_t v_isSharedCheck_1770_; 
lean_dec(v_stx_1738_);
v_a_1763_ = lean_ctor_get(v___x_1752_, 0);
v_isSharedCheck_1770_ = !lean_is_exclusive(v___x_1752_);
if (v_isSharedCheck_1770_ == 0)
{
v___x_1765_ = v___x_1752_;
v_isShared_1766_ = v_isSharedCheck_1770_;
goto v_resetjp_1764_;
}
else
{
lean_inc(v_a_1763_);
lean_dec(v___x_1752_);
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
}
else
{
lean_dec(v_stx_1738_);
return v___x_1748_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___boxed(lean_object* v_stx_1771_, lean_object* v_a_1772_, lean_object* v_a_1773_, lean_object* v_a_1774_, lean_object* v_a_1775_, lean_object* v_a_1776_, lean_object* v_a_1777_, lean_object* v_a_1778_, lean_object* v_a_1779_, lean_object* v_a_1780_){
_start:
{
lean_object* v_res_1781_; 
v_res_1781_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply(v_stx_1771_, v_a_1772_, v_a_1773_, v_a_1774_, v_a_1775_, v_a_1776_, v_a_1777_, v_a_1778_, v_a_1779_);
lean_dec(v_a_1779_);
lean_dec_ref(v_a_1778_);
lean_dec(v_a_1777_);
lean_dec_ref(v_a_1776_);
lean_dec(v_a_1775_);
lean_dec_ref(v_a_1774_);
lean_dec(v_a_1773_);
lean_dec_ref(v_a_1772_);
return v_res_1781_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply__1(){
_start:
{
lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; 
v___x_1787_ = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
v___x_1788_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___closed__1));
v___x_1789_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply__1___closed__1));
v___x_1790_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___boxed), 10, 0);
v___x_1791_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1787_, v___x_1788_, v___x_1789_, v___x_1790_);
return v___x_1791_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply__1___boxed(lean_object* v_a_1792_){
_start:
{
lean_object* v_res_1793_; 
v_res_1793_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymApply__1();
return v_res_1793_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize___redArg(lean_object* v_stx_1794_, lean_object* v_a_1795_, lean_object* v_a_1796_, lean_object* v_a_1797_, lean_object* v_a_1798_, lean_object* v_a_1799_, lean_object* v_a_1800_){
_start:
{
lean_object* v___x_1802_; 
v___x_1802_ = l_Lean_Elab_Tactic_Grind_ensureSym___redArg(v_a_1795_, v_a_1797_, v_a_1798_, v_a_1799_, v_a_1800_);
if (lean_obj_tag(v___x_1802_) == 0)
{
lean_object* v___x_1803_; 
lean_dec_ref_known(v___x_1802_, 1);
v___x_1803_ = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_, v_a_1800_);
if (lean_obj_tag(v___x_1803_) == 0)
{
lean_object* v_a_1804_; lean_object* v___y_1806_; lean_object* v___x_1821_; lean_object* v___x_1822_; uint8_t v___x_1823_; 
v_a_1804_ = lean_ctor_get(v___x_1803_, 0);
lean_inc(v_a_1804_);
lean_dec_ref_known(v___x_1803_, 1);
v___x_1821_ = lean_unsigned_to_nat(1u);
v___x_1822_ = l_Lean_Syntax_getArg(v_stx_1794_, v___x_1821_);
v___x_1823_ = l_Lean_Syntax_isNone(v___x_1822_);
if (v___x_1823_ == 0)
{
lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; 
v___x_1824_ = lean_unsigned_to_nat(0u);
v___x_1825_ = l_Lean_Syntax_getArg(v___x_1822_, v___x_1824_);
lean_dec(v___x_1822_);
v___x_1826_ = l_Lean_Syntax_toNat(v___x_1825_);
lean_dec(v___x_1825_);
v___y_1806_ = v___x_1826_;
goto v___jp_1805_;
}
else
{
lean_dec(v___x_1822_);
v___y_1806_ = v___x_1821_;
goto v___jp_1805_;
}
v___jp_1805_:
{
lean_object* v___x_1807_; lean_object* v___x_1808_; 
v___x_1807_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Goal_internalize___boxed), 12, 2);
lean_closure_set(v___x_1807_, 0, v_a_1804_);
lean_closure_set(v___x_1807_, 1, v___y_1806_);
v___x_1808_ = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(v___x_1807_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_, v_a_1800_);
if (lean_obj_tag(v___x_1808_) == 0)
{
lean_object* v_a_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; 
v_a_1809_ = lean_ctor_get(v___x_1808_, 0);
lean_inc(v_a_1809_);
lean_dec_ref_known(v___x_1808_, 1);
v___x_1810_ = lean_box(0);
v___x_1811_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1811_, 0, v_a_1809_);
lean_ctor_set(v___x_1811_, 1, v___x_1810_);
v___x_1812_ = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(v___x_1811_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_, v_a_1800_);
return v___x_1812_;
}
else
{
lean_object* v_a_1813_; lean_object* v___x_1815_; uint8_t v_isShared_1816_; uint8_t v_isSharedCheck_1820_; 
v_a_1813_ = lean_ctor_get(v___x_1808_, 0);
v_isSharedCheck_1820_ = !lean_is_exclusive(v___x_1808_);
if (v_isSharedCheck_1820_ == 0)
{
v___x_1815_ = v___x_1808_;
v_isShared_1816_ = v_isSharedCheck_1820_;
goto v_resetjp_1814_;
}
else
{
lean_inc(v_a_1813_);
lean_dec(v___x_1808_);
v___x_1815_ = lean_box(0);
v_isShared_1816_ = v_isSharedCheck_1820_;
goto v_resetjp_1814_;
}
v_resetjp_1814_:
{
lean_object* v___x_1818_; 
if (v_isShared_1816_ == 0)
{
v___x_1818_ = v___x_1815_;
goto v_reusejp_1817_;
}
else
{
lean_object* v_reuseFailAlloc_1819_; 
v_reuseFailAlloc_1819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1819_, 0, v_a_1813_);
v___x_1818_ = v_reuseFailAlloc_1819_;
goto v_reusejp_1817_;
}
v_reusejp_1817_:
{
return v___x_1818_;
}
}
}
}
}
else
{
lean_object* v_a_1827_; lean_object* v___x_1829_; uint8_t v_isShared_1830_; uint8_t v_isSharedCheck_1834_; 
v_a_1827_ = lean_ctor_get(v___x_1803_, 0);
v_isSharedCheck_1834_ = !lean_is_exclusive(v___x_1803_);
if (v_isSharedCheck_1834_ == 0)
{
v___x_1829_ = v___x_1803_;
v_isShared_1830_ = v_isSharedCheck_1834_;
goto v_resetjp_1828_;
}
else
{
lean_inc(v_a_1827_);
lean_dec(v___x_1803_);
v___x_1829_ = lean_box(0);
v_isShared_1830_ = v_isSharedCheck_1834_;
goto v_resetjp_1828_;
}
v_resetjp_1828_:
{
lean_object* v___x_1832_; 
if (v_isShared_1830_ == 0)
{
v___x_1832_ = v___x_1829_;
goto v_reusejp_1831_;
}
else
{
lean_object* v_reuseFailAlloc_1833_; 
v_reuseFailAlloc_1833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1833_, 0, v_a_1827_);
v___x_1832_ = v_reuseFailAlloc_1833_;
goto v_reusejp_1831_;
}
v_reusejp_1831_:
{
return v___x_1832_;
}
}
}
}
else
{
return v___x_1802_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize___redArg___boxed(lean_object* v_stx_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_, lean_object* v_a_1838_, lean_object* v_a_1839_, lean_object* v_a_1840_, lean_object* v_a_1841_, lean_object* v_a_1842_){
_start:
{
lean_object* v_res_1843_; 
v_res_1843_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize___redArg(v_stx_1835_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_, v_a_1840_, v_a_1841_);
lean_dec(v_a_1841_);
lean_dec_ref(v_a_1840_);
lean_dec(v_a_1839_);
lean_dec_ref(v_a_1838_);
lean_dec(v_a_1837_);
lean_dec_ref(v_a_1836_);
lean_dec(v_stx_1835_);
return v_res_1843_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize(lean_object* v_stx_1844_, lean_object* v_a_1845_, lean_object* v_a_1846_, lean_object* v_a_1847_, lean_object* v_a_1848_, lean_object* v_a_1849_, lean_object* v_a_1850_, lean_object* v_a_1851_, lean_object* v_a_1852_){
_start:
{
lean_object* v___x_1854_; 
v___x_1854_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize___redArg(v_stx_1844_, v_a_1845_, v_a_1846_, v_a_1849_, v_a_1850_, v_a_1851_, v_a_1852_);
return v___x_1854_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize___boxed(lean_object* v_stx_1855_, lean_object* v_a_1856_, lean_object* v_a_1857_, lean_object* v_a_1858_, lean_object* v_a_1859_, lean_object* v_a_1860_, lean_object* v_a_1861_, lean_object* v_a_1862_, lean_object* v_a_1863_, lean_object* v_a_1864_){
_start:
{
lean_object* v_res_1865_; 
v_res_1865_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize(v_stx_1855_, v_a_1856_, v_a_1857_, v_a_1858_, v_a_1859_, v_a_1860_, v_a_1861_, v_a_1862_, v_a_1863_);
lean_dec(v_a_1863_);
lean_dec_ref(v_a_1862_);
lean_dec(v_a_1861_);
lean_dec_ref(v_a_1860_);
lean_dec(v_a_1859_);
lean_dec_ref(v_a_1858_);
lean_dec(v_a_1857_);
lean_dec_ref(v_a_1856_);
lean_dec(v_stx_1855_);
return v_res_1865_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize__1(){
_start:
{
lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; 
v___x_1878_ = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
v___x_1879_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize__1___closed__1));
v___x_1880_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize__1___closed__3));
v___x_1881_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize___boxed), 10, 0);
v___x_1882_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1878_, v___x_1879_, v___x_1880_, v___x_1881_);
return v___x_1882_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize__1___boxed(lean_object* v_a_1883_){
_start:
{
lean_object* v_res_1884_; 
v_res_1884_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalize__1();
return v_res_1884_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll___redArg(lean_object* v_a_1885_, lean_object* v_a_1886_, lean_object* v_a_1887_, lean_object* v_a_1888_, lean_object* v_a_1889_, lean_object* v_a_1890_){
_start:
{
lean_object* v___x_1892_; 
v___x_1892_ = l_Lean_Elab_Tactic_Grind_ensureSym___redArg(v_a_1885_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_);
if (lean_obj_tag(v___x_1892_) == 0)
{
lean_object* v___x_1893_; 
lean_dec_ref_known(v___x_1892_, 1);
v___x_1893_ = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_);
if (lean_obj_tag(v___x_1893_) == 0)
{
lean_object* v_a_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; 
v_a_1894_ = lean_ctor_get(v___x_1893_, 0);
lean_inc(v_a_1894_);
lean_dec_ref_known(v___x_1893_, 1);
v___x_1895_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Goal_internalizeAll___boxed), 11, 1);
lean_closure_set(v___x_1895_, 0, v_a_1894_);
v___x_1896_ = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(v___x_1895_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_);
if (lean_obj_tag(v___x_1896_) == 0)
{
lean_object* v_a_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; 
v_a_1897_ = lean_ctor_get(v___x_1896_, 0);
lean_inc(v_a_1897_);
lean_dec_ref_known(v___x_1896_, 1);
v___x_1898_ = lean_box(0);
v___x_1899_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1899_, 0, v_a_1897_);
lean_ctor_set(v___x_1899_, 1, v___x_1898_);
v___x_1900_ = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(v___x_1899_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_);
return v___x_1900_;
}
else
{
lean_object* v_a_1901_; lean_object* v___x_1903_; uint8_t v_isShared_1904_; uint8_t v_isSharedCheck_1908_; 
v_a_1901_ = lean_ctor_get(v___x_1896_, 0);
v_isSharedCheck_1908_ = !lean_is_exclusive(v___x_1896_);
if (v_isSharedCheck_1908_ == 0)
{
v___x_1903_ = v___x_1896_;
v_isShared_1904_ = v_isSharedCheck_1908_;
goto v_resetjp_1902_;
}
else
{
lean_inc(v_a_1901_);
lean_dec(v___x_1896_);
v___x_1903_ = lean_box(0);
v_isShared_1904_ = v_isSharedCheck_1908_;
goto v_resetjp_1902_;
}
v_resetjp_1902_:
{
lean_object* v___x_1906_; 
if (v_isShared_1904_ == 0)
{
v___x_1906_ = v___x_1903_;
goto v_reusejp_1905_;
}
else
{
lean_object* v_reuseFailAlloc_1907_; 
v_reuseFailAlloc_1907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1907_, 0, v_a_1901_);
v___x_1906_ = v_reuseFailAlloc_1907_;
goto v_reusejp_1905_;
}
v_reusejp_1905_:
{
return v___x_1906_;
}
}
}
}
else
{
lean_object* v_a_1909_; lean_object* v___x_1911_; uint8_t v_isShared_1912_; uint8_t v_isSharedCheck_1916_; 
v_a_1909_ = lean_ctor_get(v___x_1893_, 0);
v_isSharedCheck_1916_ = !lean_is_exclusive(v___x_1893_);
if (v_isSharedCheck_1916_ == 0)
{
v___x_1911_ = v___x_1893_;
v_isShared_1912_ = v_isSharedCheck_1916_;
goto v_resetjp_1910_;
}
else
{
lean_inc(v_a_1909_);
lean_dec(v___x_1893_);
v___x_1911_ = lean_box(0);
v_isShared_1912_ = v_isSharedCheck_1916_;
goto v_resetjp_1910_;
}
v_resetjp_1910_:
{
lean_object* v___x_1914_; 
if (v_isShared_1912_ == 0)
{
v___x_1914_ = v___x_1911_;
goto v_reusejp_1913_;
}
else
{
lean_object* v_reuseFailAlloc_1915_; 
v_reuseFailAlloc_1915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1915_, 0, v_a_1909_);
v___x_1914_ = v_reuseFailAlloc_1915_;
goto v_reusejp_1913_;
}
v_reusejp_1913_:
{
return v___x_1914_;
}
}
}
}
else
{
return v___x_1892_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll___redArg___boxed(lean_object* v_a_1917_, lean_object* v_a_1918_, lean_object* v_a_1919_, lean_object* v_a_1920_, lean_object* v_a_1921_, lean_object* v_a_1922_, lean_object* v_a_1923_){
_start:
{
lean_object* v_res_1924_; 
v_res_1924_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll___redArg(v_a_1917_, v_a_1918_, v_a_1919_, v_a_1920_, v_a_1921_, v_a_1922_);
lean_dec(v_a_1922_);
lean_dec_ref(v_a_1921_);
lean_dec(v_a_1920_);
lean_dec_ref(v_a_1919_);
lean_dec(v_a_1918_);
lean_dec_ref(v_a_1917_);
return v_res_1924_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll(lean_object* v_x_1925_, lean_object* v_a_1926_, lean_object* v_a_1927_, lean_object* v_a_1928_, lean_object* v_a_1929_, lean_object* v_a_1930_, lean_object* v_a_1931_, lean_object* v_a_1932_, lean_object* v_a_1933_){
_start:
{
lean_object* v___x_1935_; 
v___x_1935_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll___redArg(v_a_1926_, v_a_1927_, v_a_1930_, v_a_1931_, v_a_1932_, v_a_1933_);
return v___x_1935_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll___boxed(lean_object* v_x_1936_, lean_object* v_a_1937_, lean_object* v_a_1938_, lean_object* v_a_1939_, lean_object* v_a_1940_, lean_object* v_a_1941_, lean_object* v_a_1942_, lean_object* v_a_1943_, lean_object* v_a_1944_, lean_object* v_a_1945_){
_start:
{
lean_object* v_res_1946_; 
v_res_1946_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll(v_x_1936_, v_a_1937_, v_a_1938_, v_a_1939_, v_a_1940_, v_a_1941_, v_a_1942_, v_a_1943_, v_a_1944_);
lean_dec(v_a_1944_);
lean_dec_ref(v_a_1943_);
lean_dec(v_a_1942_);
lean_dec_ref(v_a_1941_);
lean_dec(v_a_1940_);
lean_dec_ref(v_a_1939_);
lean_dec(v_a_1938_);
lean_dec_ref(v_a_1937_);
lean_dec(v_x_1936_);
return v_res_1946_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll__1(){
_start:
{
lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; 
v___x_1959_ = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
v___x_1960_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll__1___closed__1));
v___x_1961_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll__1___closed__3));
v___x_1962_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll___boxed), 10, 0);
v___x_1963_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1959_, v___x_1960_, v___x_1961_, v___x_1962_);
return v___x_1963_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll__1___boxed(lean_object* v_a_1964_){
_start:
{
lean_object* v_res_1965_; 
v_res_1965_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymInternalizeAll__1();
return v_res_1965_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___redArg___closed__1(void){
_start:
{
lean_object* v___x_1967_; lean_object* v___x_1968_; 
v___x_1967_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___redArg___closed__0));
v___x_1968_ = l_Lean_stringToMessageData(v___x_1967_);
return v___x_1968_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___redArg___closed__3(void){
_start:
{
lean_object* v___x_1970_; lean_object* v___x_1971_; 
v___x_1970_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___redArg___closed__2));
v___x_1971_ = l_Lean_stringToMessageData(v___x_1970_);
return v___x_1971_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___redArg(lean_object* v_a_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_, lean_object* v_a_1977_){
_start:
{
lean_object* v___x_1979_; 
v___x_1979_ = l_Lean_Elab_Tactic_Grind_ensureSym___redArg(v_a_1972_, v_a_1974_, v_a_1975_, v_a_1976_, v_a_1977_);
if (lean_obj_tag(v___x_1979_) == 0)
{
lean_object* v___x_1980_; 
lean_dec_ref_known(v___x_1979_, 1);
v___x_1980_ = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(v_a_1973_, v_a_1974_, v_a_1975_, v_a_1976_, v_a_1977_);
if (lean_obj_tag(v___x_1980_) == 0)
{
lean_object* v_a_1981_; lean_object* v_toGoalState_1982_; lean_object* v_mvarId_1983_; lean_object* v___x_1985_; uint8_t v_isShared_1986_; uint8_t v_isSharedCheck_2085_; 
v_a_1981_ = lean_ctor_get(v___x_1980_, 0);
lean_inc(v_a_1981_);
lean_dec_ref_known(v___x_1980_, 1);
v_toGoalState_1982_ = lean_ctor_get(v_a_1981_, 0);
v_mvarId_1983_ = lean_ctor_get(v_a_1981_, 1);
v_isSharedCheck_2085_ = !lean_is_exclusive(v_a_1981_);
if (v_isSharedCheck_2085_ == 0)
{
v___x_1985_ = v_a_1981_;
v_isShared_1986_ = v_isSharedCheck_2085_;
goto v_resetjp_1984_;
}
else
{
lean_inc(v_mvarId_1983_);
lean_inc(v_toGoalState_1982_);
lean_dec(v_a_1981_);
v___x_1985_ = lean_box(0);
v_isShared_1986_ = v_isSharedCheck_2085_;
goto v_resetjp_1984_;
}
v_resetjp_1984_:
{
lean_object* v_mvarId_1988_; lean_object* v___y_1989_; lean_object* v___y_1990_; lean_object* v___y_1991_; lean_object* v___y_1992_; lean_object* v___y_1993_; lean_object* v___y_1994_; lean_object* v___x_2044_; 
lean_inc(v_mvarId_1983_);
v___x_2044_ = l_Lean_MVarId_getType(v_mvarId_1983_, v_a_1974_, v_a_1975_, v_a_1976_, v_a_1977_);
if (lean_obj_tag(v___x_2044_) == 0)
{
lean_object* v_a_2045_; lean_object* v___y_2047_; lean_object* v___y_2048_; lean_object* v___y_2049_; lean_object* v___y_2050_; lean_object* v___y_2051_; lean_object* v___y_2052_; uint8_t v___x_2074_; 
v_a_2045_ = lean_ctor_get(v___x_2044_, 0);
lean_inc_n(v_a_2045_, 2);
lean_dec_ref_known(v___x_2044_, 1);
v___x_2074_ = l_Lean_Expr_isFalse(v_a_2045_);
if (v___x_2074_ == 0)
{
v___y_2047_ = v_a_1972_;
v___y_2048_ = v_a_1973_;
v___y_2049_ = v_a_1974_;
v___y_2050_ = v_a_1975_;
v___y_2051_ = v_a_1976_;
v___y_2052_ = v_a_1977_;
goto v___jp_2046_;
}
else
{
lean_object* v___x_2075_; lean_object* v___x_2076_; 
lean_dec(v_a_2045_);
lean_del_object(v___x_1985_);
lean_dec(v_mvarId_1983_);
lean_dec_ref(v_toGoalState_1982_);
v___x_2075_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___redArg___closed__3, &l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___redArg___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___redArg___closed__3);
v___x_2076_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__2___redArg(v___x_2075_, v_a_1974_, v_a_1975_, v_a_1976_, v_a_1977_);
return v___x_2076_;
}
v___jp_2046_:
{
lean_object* v___x_2053_; 
v___x_2053_ = l_Lean_Meta_isProp(v_a_2045_, v___y_2049_, v___y_2050_, v___y_2051_, v___y_2052_);
if (lean_obj_tag(v___x_2053_) == 0)
{
lean_object* v_a_2054_; uint8_t v___x_2055_; 
v_a_2054_ = lean_ctor_get(v___x_2053_, 0);
lean_inc(v_a_2054_);
lean_dec_ref_known(v___x_2053_, 1);
v___x_2055_ = lean_unbox(v_a_2054_);
lean_dec(v_a_2054_);
if (v___x_2055_ == 0)
{
lean_object* v___x_2056_; 
v___x_2056_ = l_Lean_MVarId_exfalso(v_mvarId_1983_, v___y_2049_, v___y_2050_, v___y_2051_, v___y_2052_);
if (lean_obj_tag(v___x_2056_) == 0)
{
lean_object* v_a_2057_; 
v_a_2057_ = lean_ctor_get(v___x_2056_, 0);
lean_inc(v_a_2057_);
lean_dec_ref_known(v___x_2056_, 1);
v_mvarId_1988_ = v_a_2057_;
v___y_1989_ = v___y_2047_;
v___y_1990_ = v___y_2048_;
v___y_1991_ = v___y_2049_;
v___y_1992_ = v___y_2050_;
v___y_1993_ = v___y_2051_;
v___y_1994_ = v___y_2052_;
goto v___jp_1987_;
}
else
{
lean_object* v_a_2058_; lean_object* v___x_2060_; uint8_t v_isShared_2061_; uint8_t v_isSharedCheck_2065_; 
lean_del_object(v___x_1985_);
lean_dec_ref(v_toGoalState_1982_);
v_a_2058_ = lean_ctor_get(v___x_2056_, 0);
v_isSharedCheck_2065_ = !lean_is_exclusive(v___x_2056_);
if (v_isSharedCheck_2065_ == 0)
{
v___x_2060_ = v___x_2056_;
v_isShared_2061_ = v_isSharedCheck_2065_;
goto v_resetjp_2059_;
}
else
{
lean_inc(v_a_2058_);
lean_dec(v___x_2056_);
v___x_2060_ = lean_box(0);
v_isShared_2061_ = v_isSharedCheck_2065_;
goto v_resetjp_2059_;
}
v_resetjp_2059_:
{
lean_object* v___x_2063_; 
if (v_isShared_2061_ == 0)
{
v___x_2063_ = v___x_2060_;
goto v_reusejp_2062_;
}
else
{
lean_object* v_reuseFailAlloc_2064_; 
v_reuseFailAlloc_2064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2064_, 0, v_a_2058_);
v___x_2063_ = v_reuseFailAlloc_2064_;
goto v_reusejp_2062_;
}
v_reusejp_2062_:
{
return v___x_2063_;
}
}
}
}
else
{
v_mvarId_1988_ = v_mvarId_1983_;
v___y_1989_ = v___y_2047_;
v___y_1990_ = v___y_2048_;
v___y_1991_ = v___y_2049_;
v___y_1992_ = v___y_2050_;
v___y_1993_ = v___y_2051_;
v___y_1994_ = v___y_2052_;
goto v___jp_1987_;
}
}
else
{
lean_object* v_a_2066_; lean_object* v___x_2068_; uint8_t v_isShared_2069_; uint8_t v_isSharedCheck_2073_; 
lean_del_object(v___x_1985_);
lean_dec(v_mvarId_1983_);
lean_dec_ref(v_toGoalState_1982_);
v_a_2066_ = lean_ctor_get(v___x_2053_, 0);
v_isSharedCheck_2073_ = !lean_is_exclusive(v___x_2053_);
if (v_isSharedCheck_2073_ == 0)
{
v___x_2068_ = v___x_2053_;
v_isShared_2069_ = v_isSharedCheck_2073_;
goto v_resetjp_2067_;
}
else
{
lean_inc(v_a_2066_);
lean_dec(v___x_2053_);
v___x_2068_ = lean_box(0);
v_isShared_2069_ = v_isSharedCheck_2073_;
goto v_resetjp_2067_;
}
v_resetjp_2067_:
{
lean_object* v___x_2071_; 
if (v_isShared_2069_ == 0)
{
v___x_2071_ = v___x_2068_;
goto v_reusejp_2070_;
}
else
{
lean_object* v_reuseFailAlloc_2072_; 
v_reuseFailAlloc_2072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2072_, 0, v_a_2066_);
v___x_2071_ = v_reuseFailAlloc_2072_;
goto v_reusejp_2070_;
}
v_reusejp_2070_:
{
return v___x_2071_;
}
}
}
}
}
else
{
lean_object* v_a_2077_; lean_object* v___x_2079_; uint8_t v_isShared_2080_; uint8_t v_isSharedCheck_2084_; 
lean_del_object(v___x_1985_);
lean_dec(v_mvarId_1983_);
lean_dec_ref(v_toGoalState_1982_);
v_a_2077_ = lean_ctor_get(v___x_2044_, 0);
v_isSharedCheck_2084_ = !lean_is_exclusive(v___x_2044_);
if (v_isSharedCheck_2084_ == 0)
{
v___x_2079_ = v___x_2044_;
v_isShared_2080_ = v_isSharedCheck_2084_;
goto v_resetjp_2078_;
}
else
{
lean_inc(v_a_2077_);
lean_dec(v___x_2044_);
v___x_2079_ = lean_box(0);
v_isShared_2080_ = v_isSharedCheck_2084_;
goto v_resetjp_2078_;
}
v_resetjp_2078_:
{
lean_object* v___x_2082_; 
if (v_isShared_2080_ == 0)
{
v___x_2082_ = v___x_2079_;
goto v_reusejp_2081_;
}
else
{
lean_object* v_reuseFailAlloc_2083_; 
v_reuseFailAlloc_2083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2083_, 0, v_a_2077_);
v___x_2082_ = v_reuseFailAlloc_2083_;
goto v_reusejp_2081_;
}
v_reusejp_2081_:
{
return v___x_2082_;
}
}
}
v___jp_1987_:
{
lean_object* v___x_1995_; 
v___x_1995_ = l_Lean_MVarId_byContra_x3f(v_mvarId_1988_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_);
if (lean_obj_tag(v___x_1995_) == 0)
{
lean_object* v_a_1996_; 
v_a_1996_ = lean_ctor_get(v___x_1995_, 0);
lean_inc(v_a_1996_);
lean_dec_ref_known(v___x_1995_, 1);
if (lean_obj_tag(v_a_1996_) == 1)
{
lean_object* v_val_1997_; uint8_t v___x_1998_; lean_object* v___x_1999_; 
v_val_1997_ = lean_ctor_get(v_a_1996_, 0);
lean_inc(v_val_1997_);
lean_dec_ref_known(v_a_1996_, 1);
v___x_1998_ = 0;
v___x_1999_ = l_Lean_Meta_intro1Core(v_val_1997_, v___x_1998_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_);
if (lean_obj_tag(v___x_1999_) == 0)
{
lean_object* v_a_2000_; lean_object* v_snd_2001_; lean_object* v___x_2003_; uint8_t v_isShared_2004_; uint8_t v_isSharedCheck_2024_; 
v_a_2000_ = lean_ctor_get(v___x_1999_, 0);
lean_inc(v_a_2000_);
lean_dec_ref_known(v___x_1999_, 1);
v_snd_2001_ = lean_ctor_get(v_a_2000_, 1);
v_isSharedCheck_2024_ = !lean_is_exclusive(v_a_2000_);
if (v_isSharedCheck_2024_ == 0)
{
lean_object* v_unused_2025_; 
v_unused_2025_ = lean_ctor_get(v_a_2000_, 0);
lean_dec(v_unused_2025_);
v___x_2003_ = v_a_2000_;
v_isShared_2004_ = v_isSharedCheck_2024_;
goto v_resetjp_2002_;
}
else
{
lean_inc(v_snd_2001_);
lean_dec(v_a_2000_);
v___x_2003_ = lean_box(0);
v_isShared_2004_ = v_isSharedCheck_2024_;
goto v_resetjp_2002_;
}
v_resetjp_2002_:
{
lean_object* v___x_2006_; 
if (v_isShared_1986_ == 0)
{
lean_ctor_set(v___x_1985_, 1, v_snd_2001_);
v___x_2006_ = v___x_1985_;
goto v_reusejp_2005_;
}
else
{
lean_object* v_reuseFailAlloc_2023_; 
v_reuseFailAlloc_2023_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2023_, 0, v_toGoalState_1982_);
lean_ctor_set(v_reuseFailAlloc_2023_, 1, v_snd_2001_);
v___x_2006_ = v_reuseFailAlloc_2023_;
goto v_reusejp_2005_;
}
v_reusejp_2005_:
{
lean_object* v___x_2007_; lean_object* v___x_2008_; 
v___x_2007_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Goal_internalizeAll___boxed), 11, 1);
lean_closure_set(v___x_2007_, 0, v___x_2006_);
v___x_2008_ = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(v___x_2007_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_);
if (lean_obj_tag(v___x_2008_) == 0)
{
lean_object* v_a_2009_; lean_object* v___x_2010_; lean_object* v___x_2012_; 
v_a_2009_ = lean_ctor_get(v___x_2008_, 0);
lean_inc(v_a_2009_);
lean_dec_ref_known(v___x_2008_, 1);
v___x_2010_ = lean_box(0);
if (v_isShared_2004_ == 0)
{
lean_ctor_set_tag(v___x_2003_, 1);
lean_ctor_set(v___x_2003_, 1, v___x_2010_);
lean_ctor_set(v___x_2003_, 0, v_a_2009_);
v___x_2012_ = v___x_2003_;
goto v_reusejp_2011_;
}
else
{
lean_object* v_reuseFailAlloc_2014_; 
v_reuseFailAlloc_2014_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2014_, 0, v_a_2009_);
lean_ctor_set(v_reuseFailAlloc_2014_, 1, v___x_2010_);
v___x_2012_ = v_reuseFailAlloc_2014_;
goto v_reusejp_2011_;
}
v_reusejp_2011_:
{
lean_object* v___x_2013_; 
v___x_2013_ = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(v___x_2012_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_);
return v___x_2013_;
}
}
else
{
lean_object* v_a_2015_; lean_object* v___x_2017_; uint8_t v_isShared_2018_; uint8_t v_isSharedCheck_2022_; 
lean_del_object(v___x_2003_);
v_a_2015_ = lean_ctor_get(v___x_2008_, 0);
v_isSharedCheck_2022_ = !lean_is_exclusive(v___x_2008_);
if (v_isSharedCheck_2022_ == 0)
{
v___x_2017_ = v___x_2008_;
v_isShared_2018_ = v_isSharedCheck_2022_;
goto v_resetjp_2016_;
}
else
{
lean_inc(v_a_2015_);
lean_dec(v___x_2008_);
v___x_2017_ = lean_box(0);
v_isShared_2018_ = v_isSharedCheck_2022_;
goto v_resetjp_2016_;
}
v_resetjp_2016_:
{
lean_object* v___x_2020_; 
if (v_isShared_2018_ == 0)
{
v___x_2020_ = v___x_2017_;
goto v_reusejp_2019_;
}
else
{
lean_object* v_reuseFailAlloc_2021_; 
v_reuseFailAlloc_2021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2021_, 0, v_a_2015_);
v___x_2020_ = v_reuseFailAlloc_2021_;
goto v_reusejp_2019_;
}
v_reusejp_2019_:
{
return v___x_2020_;
}
}
}
}
}
}
else
{
lean_object* v_a_2026_; lean_object* v___x_2028_; uint8_t v_isShared_2029_; uint8_t v_isSharedCheck_2033_; 
lean_del_object(v___x_1985_);
lean_dec_ref(v_toGoalState_1982_);
v_a_2026_ = lean_ctor_get(v___x_1999_, 0);
v_isSharedCheck_2033_ = !lean_is_exclusive(v___x_1999_);
if (v_isSharedCheck_2033_ == 0)
{
v___x_2028_ = v___x_1999_;
v_isShared_2029_ = v_isSharedCheck_2033_;
goto v_resetjp_2027_;
}
else
{
lean_inc(v_a_2026_);
lean_dec(v___x_1999_);
v___x_2028_ = lean_box(0);
v_isShared_2029_ = v_isSharedCheck_2033_;
goto v_resetjp_2027_;
}
v_resetjp_2027_:
{
lean_object* v___x_2031_; 
if (v_isShared_2029_ == 0)
{
v___x_2031_ = v___x_2028_;
goto v_reusejp_2030_;
}
else
{
lean_object* v_reuseFailAlloc_2032_; 
v_reuseFailAlloc_2032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2032_, 0, v_a_2026_);
v___x_2031_ = v_reuseFailAlloc_2032_;
goto v_reusejp_2030_;
}
v_reusejp_2030_:
{
return v___x_2031_;
}
}
}
}
else
{
lean_object* v___x_2034_; lean_object* v___x_2035_; 
lean_dec(v_a_1996_);
lean_del_object(v___x_1985_);
lean_dec_ref(v_toGoalState_1982_);
v___x_2034_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___redArg___closed__1, &l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___redArg___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___redArg___closed__1);
v___x_2035_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__2___redArg(v___x_2034_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_);
return v___x_2035_;
}
}
else
{
lean_object* v_a_2036_; lean_object* v___x_2038_; uint8_t v_isShared_2039_; uint8_t v_isSharedCheck_2043_; 
lean_del_object(v___x_1985_);
lean_dec_ref(v_toGoalState_1982_);
v_a_2036_ = lean_ctor_get(v___x_1995_, 0);
v_isSharedCheck_2043_ = !lean_is_exclusive(v___x_1995_);
if (v_isSharedCheck_2043_ == 0)
{
v___x_2038_ = v___x_1995_;
v_isShared_2039_ = v_isSharedCheck_2043_;
goto v_resetjp_2037_;
}
else
{
lean_inc(v_a_2036_);
lean_dec(v___x_1995_);
v___x_2038_ = lean_box(0);
v_isShared_2039_ = v_isSharedCheck_2043_;
goto v_resetjp_2037_;
}
v_resetjp_2037_:
{
lean_object* v___x_2041_; 
if (v_isShared_2039_ == 0)
{
v___x_2041_ = v___x_2038_;
goto v_reusejp_2040_;
}
else
{
lean_object* v_reuseFailAlloc_2042_; 
v_reuseFailAlloc_2042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2042_, 0, v_a_2036_);
v___x_2041_ = v_reuseFailAlloc_2042_;
goto v_reusejp_2040_;
}
v_reusejp_2040_:
{
return v___x_2041_;
}
}
}
}
}
}
else
{
lean_object* v_a_2086_; lean_object* v___x_2088_; uint8_t v_isShared_2089_; uint8_t v_isSharedCheck_2093_; 
v_a_2086_ = lean_ctor_get(v___x_1980_, 0);
v_isSharedCheck_2093_ = !lean_is_exclusive(v___x_1980_);
if (v_isSharedCheck_2093_ == 0)
{
v___x_2088_ = v___x_1980_;
v_isShared_2089_ = v_isSharedCheck_2093_;
goto v_resetjp_2087_;
}
else
{
lean_inc(v_a_2086_);
lean_dec(v___x_1980_);
v___x_2088_ = lean_box(0);
v_isShared_2089_ = v_isSharedCheck_2093_;
goto v_resetjp_2087_;
}
v_resetjp_2087_:
{
lean_object* v___x_2091_; 
if (v_isShared_2089_ == 0)
{
v___x_2091_ = v___x_2088_;
goto v_reusejp_2090_;
}
else
{
lean_object* v_reuseFailAlloc_2092_; 
v_reuseFailAlloc_2092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2092_, 0, v_a_2086_);
v___x_2091_ = v_reuseFailAlloc_2092_;
goto v_reusejp_2090_;
}
v_reusejp_2090_:
{
return v___x_2091_;
}
}
}
}
else
{
return v___x_1979_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___redArg___boxed(lean_object* v_a_2094_, lean_object* v_a_2095_, lean_object* v_a_2096_, lean_object* v_a_2097_, lean_object* v_a_2098_, lean_object* v_a_2099_, lean_object* v_a_2100_){
_start:
{
lean_object* v_res_2101_; 
v_res_2101_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___redArg(v_a_2094_, v_a_2095_, v_a_2096_, v_a_2097_, v_a_2098_, v_a_2099_);
lean_dec(v_a_2099_);
lean_dec_ref(v_a_2098_);
lean_dec(v_a_2097_);
lean_dec_ref(v_a_2096_);
lean_dec(v_a_2095_);
lean_dec_ref(v_a_2094_);
return v_res_2101_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra(lean_object* v_x_2102_, lean_object* v_a_2103_, lean_object* v_a_2104_, lean_object* v_a_2105_, lean_object* v_a_2106_, lean_object* v_a_2107_, lean_object* v_a_2108_, lean_object* v_a_2109_, lean_object* v_a_2110_){
_start:
{
lean_object* v___x_2112_; 
v___x_2112_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___redArg(v_a_2103_, v_a_2104_, v_a_2107_, v_a_2108_, v_a_2109_, v_a_2110_);
return v___x_2112_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___boxed(lean_object* v_x_2113_, lean_object* v_a_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_, lean_object* v_a_2119_, lean_object* v_a_2120_, lean_object* v_a_2121_, lean_object* v_a_2122_){
_start:
{
lean_object* v_res_2123_; 
v_res_2123_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra(v_x_2113_, v_a_2114_, v_a_2115_, v_a_2116_, v_a_2117_, v_a_2118_, v_a_2119_, v_a_2120_, v_a_2121_);
lean_dec(v_a_2121_);
lean_dec_ref(v_a_2120_);
lean_dec(v_a_2119_);
lean_dec_ref(v_a_2118_);
lean_dec(v_a_2117_);
lean_dec_ref(v_a_2116_);
lean_dec(v_a_2115_);
lean_dec_ref(v_a_2114_);
lean_dec(v_x_2113_);
return v_res_2123_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra__1(){
_start:
{
lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; 
v___x_2136_ = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
v___x_2137_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra__1___closed__1));
v___x_2138_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra__1___closed__3));
v___x_2139_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___boxed), 10, 0);
v___x_2140_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2136_, v___x_2137_, v___x_2138_, v___x_2139_);
return v___x_2140_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra__1___boxed(lean_object* v_a_2141_){
_start:
{
lean_object* v_res_2142_; 
v_res_2142_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymByContra__1();
return v_res_2142_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_trivialSimproc___redArg(){
_start:
{
lean_object* v___x_2146_; lean_object* v___x_2147_; 
v___x_2146_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_trivialSimproc___redArg___closed__0));
v___x_2147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2147_, 0, v___x_2146_);
return v___x_2147_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_trivialSimproc___redArg___boxed(lean_object* v_a_2148_){
_start:
{
lean_object* v_res_2149_; 
v_res_2149_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_trivialSimproc___redArg();
return v_res_2149_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_trivialSimproc(lean_object* v_x_2150_, lean_object* v_a_2151_, lean_object* v_a_2152_, lean_object* v_a_2153_, lean_object* v_a_2154_, lean_object* v_a_2155_, lean_object* v_a_2156_, lean_object* v_a_2157_, lean_object* v_a_2158_, lean_object* v_a_2159_){
_start:
{
lean_object* v___x_2161_; 
v___x_2161_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_trivialSimproc___redArg();
return v___x_2161_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_trivialSimproc___boxed(lean_object* v_x_2162_, lean_object* v_a_2163_, lean_object* v_a_2164_, lean_object* v_a_2165_, lean_object* v_a_2166_, lean_object* v_a_2167_, lean_object* v_a_2168_, lean_object* v_a_2169_, lean_object* v_a_2170_, lean_object* v_a_2171_, lean_object* v_a_2172_){
_start:
{
lean_object* v_res_2173_; 
v_res_2173_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_trivialSimproc(v_x_2162_, v_a_2163_, v_a_2164_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_);
lean_dec(v_a_2171_);
lean_dec_ref(v_a_2170_);
lean_dec(v_a_2169_);
lean_dec_ref(v_a_2168_);
lean_dec(v_a_2167_);
lean_dec_ref(v_a_2166_);
lean_dec(v_a_2165_);
lean_dec_ref(v_a_2164_);
lean_dec(v_a_2163_);
lean_dec_ref(v_x_2162_);
return v_res_2173_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabOptSimproc(lean_object* v_stx_x3f_2174_, lean_object* v_a_2175_, lean_object* v_a_2176_, lean_object* v_a_2177_, lean_object* v_a_2178_, lean_object* v_a_2179_, lean_object* v_a_2180_, lean_object* v_a_2181_, lean_object* v_a_2182_){
_start:
{
if (lean_obj_tag(v_stx_x3f_2174_) == 1)
{
lean_object* v_val_2184_; lean_object* v___x_2185_; 
v_val_2184_ = lean_ctor_get(v_stx_x3f_2174_, 0);
lean_inc(v_val_2184_);
lean_dec_ref_known(v_stx_x3f_2174_, 1);
v___x_2185_ = l_Lean_Elab_Tactic_Grind_elabSymSimproc(v_val_2184_, v_a_2175_, v_a_2176_, v_a_2177_, v_a_2178_, v_a_2179_, v_a_2180_, v_a_2181_, v_a_2182_);
return v___x_2185_;
}
else
{
lean_object* v___x_2186_; lean_object* v___x_2187_; 
lean_dec(v_stx_x3f_2174_);
v___x_2186_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_trivialSimproc___boxed), 11, 0);
v___x_2187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2187_, 0, v___x_2186_);
return v___x_2187_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabOptSimproc___boxed(lean_object* v_stx_x3f_2188_, lean_object* v_a_2189_, lean_object* v_a_2190_, lean_object* v_a_2191_, lean_object* v_a_2192_, lean_object* v_a_2193_, lean_object* v_a_2194_, lean_object* v_a_2195_, lean_object* v_a_2196_, lean_object* v_a_2197_){
_start:
{
lean_object* v_res_2198_; 
v_res_2198_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabOptSimproc(v_stx_x3f_2188_, v_a_2189_, v_a_2190_, v_a_2191_, v_a_2192_, v_a_2193_, v_a_2194_, v_a_2195_, v_a_2196_);
lean_dec(v_a_2196_);
lean_dec_ref(v_a_2195_);
lean_dec(v_a_2194_);
lean_dec_ref(v_a_2193_);
lean_dec(v_a_2192_);
lean_dec_ref(v_a_2191_);
lean_dec(v_a_2190_);
lean_dec_ref(v_a_2189_);
return v_res_2198_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__0___redArg(lean_object* v___x_2199_, lean_object* v_as_2200_, size_t v_sz_2201_, size_t v_i_2202_, lean_object* v_b_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_){
_start:
{
lean_object* v_a_2210_; uint8_t v___x_2214_; 
v___x_2214_ = lean_usize_dec_lt(v_i_2202_, v_sz_2201_);
if (v___x_2214_ == 0)
{
lean_object* v___x_2215_; 
v___x_2215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2215_, 0, v_b_2203_);
return v___x_2215_;
}
else
{
lean_object* v_fst_2216_; lean_object* v_snd_2217_; lean_object* v___x_2219_; uint8_t v_isShared_2220_; uint8_t v_isSharedCheck_2275_; 
v_fst_2216_ = lean_ctor_get(v_b_2203_, 0);
v_snd_2217_ = lean_ctor_get(v_b_2203_, 1);
v_isSharedCheck_2275_ = !lean_is_exclusive(v_b_2203_);
if (v_isSharedCheck_2275_ == 0)
{
v___x_2219_ = v_b_2203_;
v_isShared_2220_ = v_isSharedCheck_2275_;
goto v_resetjp_2218_;
}
else
{
lean_inc(v_snd_2217_);
lean_inc(v_fst_2216_);
lean_dec(v_b_2203_);
v___x_2219_ = lean_box(0);
v_isShared_2220_ = v_isSharedCheck_2275_;
goto v_resetjp_2218_;
}
v_resetjp_2218_:
{
lean_object* v_a_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; 
v_a_2221_ = lean_array_uget_borrowed(v_as_2200_, v_i_2202_);
v___x_2222_ = l_Lean_TSyntax_getId(v_a_2221_);
v___x_2223_ = l_Lean_LocalContext_findFromUserName_x3f(v___x_2199_, v___x_2222_);
lean_dec(v___x_2222_);
if (lean_obj_tag(v___x_2223_) == 1)
{
lean_object* v_val_2224_; lean_object* v___x_2226_; uint8_t v_isShared_2227_; uint8_t v_isSharedCheck_2248_; 
v_val_2224_ = lean_ctor_get(v___x_2223_, 0);
v_isSharedCheck_2248_ = !lean_is_exclusive(v___x_2223_);
if (v_isSharedCheck_2248_ == 0)
{
v___x_2226_ = v___x_2223_;
v_isShared_2227_ = v_isSharedCheck_2248_;
goto v_resetjp_2225_;
}
else
{
lean_inc(v_val_2224_);
lean_dec(v___x_2223_);
v___x_2226_ = lean_box(0);
v_isShared_2227_ = v_isSharedCheck_2248_;
goto v_resetjp_2225_;
}
v_resetjp_2225_:
{
lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; 
v___x_2228_ = l_Lean_LocalDecl_fvarId(v_val_2224_);
v___x_2229_ = l_Lean_LocalDecl_toExpr(v_val_2224_);
v___x_2230_ = l_Lean_Meta_Sym_Simp_mkTheoremFromExpr(v___x_2229_, v___y_2204_, v___y_2205_, v___y_2206_, v___y_2207_);
if (lean_obj_tag(v___x_2230_) == 0)
{
lean_object* v_a_2231_; lean_object* v___x_2233_; 
v_a_2231_ = lean_ctor_get(v___x_2230_, 0);
lean_inc(v_a_2231_);
lean_dec_ref_known(v___x_2230_, 1);
if (v_isShared_2227_ == 0)
{
lean_ctor_set(v___x_2226_, 0, v___x_2228_);
v___x_2233_ = v___x_2226_;
goto v_reusejp_2232_;
}
else
{
lean_object* v_reuseFailAlloc_2239_; 
v_reuseFailAlloc_2239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2239_, 0, v___x_2228_);
v___x_2233_ = v_reuseFailAlloc_2239_;
goto v_reusejp_2232_;
}
v_reusejp_2232_:
{
lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2237_; 
v___x_2234_ = lean_array_push(v_fst_2216_, v___x_2233_);
v___x_2235_ = lean_array_push(v_snd_2217_, v_a_2231_);
if (v_isShared_2220_ == 0)
{
lean_ctor_set(v___x_2219_, 1, v___x_2235_);
lean_ctor_set(v___x_2219_, 0, v___x_2234_);
v___x_2237_ = v___x_2219_;
goto v_reusejp_2236_;
}
else
{
lean_object* v_reuseFailAlloc_2238_; 
v_reuseFailAlloc_2238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2238_, 0, v___x_2234_);
lean_ctor_set(v_reuseFailAlloc_2238_, 1, v___x_2235_);
v___x_2237_ = v_reuseFailAlloc_2238_;
goto v_reusejp_2236_;
}
v_reusejp_2236_:
{
v_a_2210_ = v___x_2237_;
goto v___jp_2209_;
}
}
}
else
{
lean_object* v_a_2240_; lean_object* v___x_2242_; uint8_t v_isShared_2243_; uint8_t v_isSharedCheck_2247_; 
lean_dec(v___x_2228_);
lean_del_object(v___x_2226_);
lean_del_object(v___x_2219_);
lean_dec(v_snd_2217_);
lean_dec(v_fst_2216_);
v_a_2240_ = lean_ctor_get(v___x_2230_, 0);
v_isSharedCheck_2247_ = !lean_is_exclusive(v___x_2230_);
if (v_isSharedCheck_2247_ == 0)
{
v___x_2242_ = v___x_2230_;
v_isShared_2243_ = v_isSharedCheck_2247_;
goto v_resetjp_2241_;
}
else
{
lean_inc(v_a_2240_);
lean_dec(v___x_2230_);
v___x_2242_ = lean_box(0);
v_isShared_2243_ = v_isSharedCheck_2247_;
goto v_resetjp_2241_;
}
v_resetjp_2241_:
{
lean_object* v___x_2245_; 
if (v_isShared_2243_ == 0)
{
v___x_2245_ = v___x_2242_;
goto v_reusejp_2244_;
}
else
{
lean_object* v_reuseFailAlloc_2246_; 
v_reuseFailAlloc_2246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2246_, 0, v_a_2240_);
v___x_2245_ = v_reuseFailAlloc_2246_;
goto v_reusejp_2244_;
}
v_reusejp_2244_:
{
return v___x_2245_;
}
}
}
}
}
else
{
lean_object* v___x_2249_; 
lean_dec(v___x_2223_);
lean_inc(v_a_2221_);
v___x_2249_ = l_Lean_realizeGlobalConstNoOverload(v_a_2221_, v___y_2206_, v___y_2207_);
if (lean_obj_tag(v___x_2249_) == 0)
{
lean_object* v_a_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; 
v_a_2250_ = lean_ctor_get(v___x_2249_, 0);
lean_inc_n(v_a_2250_, 2);
lean_dec_ref_known(v___x_2249_, 1);
v___x_2251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2251_, 0, v_a_2250_);
v___x_2252_ = l_Lean_Meta_Sym_Simp_mkTheoremFromDecl(v_a_2250_, v___y_2204_, v___y_2205_, v___y_2206_, v___y_2207_);
if (lean_obj_tag(v___x_2252_) == 0)
{
lean_object* v_a_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2257_; 
v_a_2253_ = lean_ctor_get(v___x_2252_, 0);
lean_inc(v_a_2253_);
lean_dec_ref_known(v___x_2252_, 1);
v___x_2254_ = lean_array_push(v_fst_2216_, v___x_2251_);
v___x_2255_ = lean_array_push(v_snd_2217_, v_a_2253_);
if (v_isShared_2220_ == 0)
{
lean_ctor_set(v___x_2219_, 1, v___x_2255_);
lean_ctor_set(v___x_2219_, 0, v___x_2254_);
v___x_2257_ = v___x_2219_;
goto v_reusejp_2256_;
}
else
{
lean_object* v_reuseFailAlloc_2258_; 
v_reuseFailAlloc_2258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2258_, 0, v___x_2254_);
lean_ctor_set(v_reuseFailAlloc_2258_, 1, v___x_2255_);
v___x_2257_ = v_reuseFailAlloc_2258_;
goto v_reusejp_2256_;
}
v_reusejp_2256_:
{
v_a_2210_ = v___x_2257_;
goto v___jp_2209_;
}
}
else
{
lean_object* v_a_2259_; lean_object* v___x_2261_; uint8_t v_isShared_2262_; uint8_t v_isSharedCheck_2266_; 
lean_dec_ref_known(v___x_2251_, 1);
lean_del_object(v___x_2219_);
lean_dec(v_snd_2217_);
lean_dec(v_fst_2216_);
v_a_2259_ = lean_ctor_get(v___x_2252_, 0);
v_isSharedCheck_2266_ = !lean_is_exclusive(v___x_2252_);
if (v_isSharedCheck_2266_ == 0)
{
v___x_2261_ = v___x_2252_;
v_isShared_2262_ = v_isSharedCheck_2266_;
goto v_resetjp_2260_;
}
else
{
lean_inc(v_a_2259_);
lean_dec(v___x_2252_);
v___x_2261_ = lean_box(0);
v_isShared_2262_ = v_isSharedCheck_2266_;
goto v_resetjp_2260_;
}
v_resetjp_2260_:
{
lean_object* v___x_2264_; 
if (v_isShared_2262_ == 0)
{
v___x_2264_ = v___x_2261_;
goto v_reusejp_2263_;
}
else
{
lean_object* v_reuseFailAlloc_2265_; 
v_reuseFailAlloc_2265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2265_, 0, v_a_2259_);
v___x_2264_ = v_reuseFailAlloc_2265_;
goto v_reusejp_2263_;
}
v_reusejp_2263_:
{
return v___x_2264_;
}
}
}
}
else
{
lean_object* v_a_2267_; lean_object* v___x_2269_; uint8_t v_isShared_2270_; uint8_t v_isSharedCheck_2274_; 
lean_del_object(v___x_2219_);
lean_dec(v_snd_2217_);
lean_dec(v_fst_2216_);
v_a_2267_ = lean_ctor_get(v___x_2249_, 0);
v_isSharedCheck_2274_ = !lean_is_exclusive(v___x_2249_);
if (v_isSharedCheck_2274_ == 0)
{
v___x_2269_ = v___x_2249_;
v_isShared_2270_ = v_isSharedCheck_2274_;
goto v_resetjp_2268_;
}
else
{
lean_inc(v_a_2267_);
lean_dec(v___x_2249_);
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
}
v___jp_2209_:
{
size_t v___x_2211_; size_t v___x_2212_; 
v___x_2211_ = ((size_t)1ULL);
v___x_2212_ = lean_usize_add(v_i_2202_, v___x_2211_);
v_i_2202_ = v___x_2212_;
v_b_2203_ = v_a_2210_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__0___redArg___boxed(lean_object* v___x_2276_, lean_object* v_as_2277_, lean_object* v_sz_2278_, lean_object* v_i_2279_, lean_object* v_b_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_){
_start:
{
size_t v_sz_boxed_2286_; size_t v_i_boxed_2287_; lean_object* v_res_2288_; 
v_sz_boxed_2286_ = lean_unbox_usize(v_sz_2278_);
lean_dec(v_sz_2278_);
v_i_boxed_2287_ = lean_unbox_usize(v_i_2279_);
lean_dec(v_i_2279_);
v_res_2288_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__0___redArg(v___x_2276_, v_as_2277_, v_sz_boxed_2286_, v_i_boxed_2287_, v_b_2280_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_);
lean_dec(v___y_2284_);
lean_dec_ref(v___y_2283_);
lean_dec(v___y_2282_);
lean_dec_ref(v___y_2281_);
lean_dec_ref(v_as_2277_);
lean_dec_ref(v___x_2276_);
return v_res_2288_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems(lean_object* v_ids_x3f_2293_, lean_object* v_a_2294_, lean_object* v_a_2295_, lean_object* v_a_2296_, lean_object* v_a_2297_, lean_object* v_a_2298_, lean_object* v_a_2299_, lean_object* v_a_2300_, lean_object* v_a_2301_){
_start:
{
if (lean_obj_tag(v_ids_x3f_2293_) == 1)
{
lean_object* v_val_2303_; lean_object* v_lctx_2304_; lean_object* v___x_2305_; size_t v_sz_2306_; size_t v___x_2307_; lean_object* v___x_2308_; 
v_val_2303_ = lean_ctor_get(v_ids_x3f_2293_, 0);
v_lctx_2304_ = lean_ctor_get(v_a_2298_, 2);
v___x_2305_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems___closed__1));
v_sz_2306_ = lean_array_size(v_val_2303_);
v___x_2307_ = ((size_t)0ULL);
v___x_2308_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__0___redArg(v_lctx_2304_, v_val_2303_, v_sz_2306_, v___x_2307_, v___x_2305_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_);
if (lean_obj_tag(v___x_2308_) == 0)
{
lean_object* v_a_2309_; lean_object* v___x_2311_; uint8_t v_isShared_2312_; uint8_t v_isSharedCheck_2325_; 
v_a_2309_ = lean_ctor_get(v___x_2308_, 0);
v_isSharedCheck_2325_ = !lean_is_exclusive(v___x_2308_);
if (v_isSharedCheck_2325_ == 0)
{
v___x_2311_ = v___x_2308_;
v_isShared_2312_ = v_isSharedCheck_2325_;
goto v_resetjp_2310_;
}
else
{
lean_inc(v_a_2309_);
lean_dec(v___x_2308_);
v___x_2311_ = lean_box(0);
v_isShared_2312_ = v_isSharedCheck_2325_;
goto v_resetjp_2310_;
}
v_resetjp_2310_:
{
lean_object* v_fst_2313_; lean_object* v_snd_2314_; lean_object* v___x_2316_; uint8_t v_isShared_2317_; uint8_t v_isSharedCheck_2324_; 
v_fst_2313_ = lean_ctor_get(v_a_2309_, 0);
v_snd_2314_ = lean_ctor_get(v_a_2309_, 1);
v_isSharedCheck_2324_ = !lean_is_exclusive(v_a_2309_);
if (v_isSharedCheck_2324_ == 0)
{
v___x_2316_ = v_a_2309_;
v_isShared_2317_ = v_isSharedCheck_2324_;
goto v_resetjp_2315_;
}
else
{
lean_inc(v_snd_2314_);
lean_inc(v_fst_2313_);
lean_dec(v_a_2309_);
v___x_2316_ = lean_box(0);
v_isShared_2317_ = v_isSharedCheck_2324_;
goto v_resetjp_2315_;
}
v_resetjp_2315_:
{
lean_object* v___x_2319_; 
if (v_isShared_2317_ == 0)
{
v___x_2319_ = v___x_2316_;
goto v_reusejp_2318_;
}
else
{
lean_object* v_reuseFailAlloc_2323_; 
v_reuseFailAlloc_2323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2323_, 0, v_fst_2313_);
lean_ctor_set(v_reuseFailAlloc_2323_, 1, v_snd_2314_);
v___x_2319_ = v_reuseFailAlloc_2323_;
goto v_reusejp_2318_;
}
v_reusejp_2318_:
{
lean_object* v___x_2321_; 
if (v_isShared_2312_ == 0)
{
lean_ctor_set(v___x_2311_, 0, v___x_2319_);
v___x_2321_ = v___x_2311_;
goto v_reusejp_2320_;
}
else
{
lean_object* v_reuseFailAlloc_2322_; 
v_reuseFailAlloc_2322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2322_, 0, v___x_2319_);
v___x_2321_ = v_reuseFailAlloc_2322_;
goto v_reusejp_2320_;
}
v_reusejp_2320_:
{
return v___x_2321_;
}
}
}
}
}
else
{
return v___x_2308_;
}
}
else
{
lean_object* v___x_2326_; lean_object* v___x_2327_; 
v___x_2326_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems___closed__1));
v___x_2327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2327_, 0, v___x_2326_);
return v___x_2327_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems___boxed(lean_object* v_ids_x3f_2328_, lean_object* v_a_2329_, lean_object* v_a_2330_, lean_object* v_a_2331_, lean_object* v_a_2332_, lean_object* v_a_2333_, lean_object* v_a_2334_, lean_object* v_a_2335_, lean_object* v_a_2336_, lean_object* v_a_2337_){
_start:
{
lean_object* v_res_2338_; 
v_res_2338_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems(v_ids_x3f_2328_, v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_);
lean_dec(v_a_2336_);
lean_dec_ref(v_a_2335_);
lean_dec(v_a_2334_);
lean_dec_ref(v_a_2333_);
lean_dec(v_a_2332_);
lean_dec_ref(v_a_2331_);
lean_dec(v_a_2330_);
lean_dec_ref(v_a_2329_);
lean_dec(v_ids_x3f_2328_);
return v_res_2338_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__0(lean_object* v___x_2339_, lean_object* v_as_2340_, size_t v_sz_2341_, size_t v_i_2342_, lean_object* v_b_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_){
_start:
{
lean_object* v___x_2353_; 
v___x_2353_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__0___redArg(v___x_2339_, v_as_2340_, v_sz_2341_, v_i_2342_, v_b_2343_, v___y_2348_, v___y_2349_, v___y_2350_, v___y_2351_);
return v___x_2353_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__0___boxed(lean_object* v___x_2354_, lean_object* v_as_2355_, lean_object* v_sz_2356_, lean_object* v_i_2357_, lean_object* v_b_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_){
_start:
{
size_t v_sz_boxed_2368_; size_t v_i_boxed_2369_; lean_object* v_res_2370_; 
v_sz_boxed_2368_ = lean_unbox_usize(v_sz_2356_);
lean_dec(v_sz_2356_);
v_i_boxed_2369_ = lean_unbox_usize(v_i_2357_);
lean_dec(v_i_2357_);
v_res_2370_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems_spec__0(v___x_2354_, v_as_2355_, v_sz_boxed_2368_, v_i_boxed_2369_, v_b_2358_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_);
lean_dec(v___y_2366_);
lean_dec_ref(v___y_2365_);
lean_dec(v___y_2364_);
lean_dec_ref(v___y_2363_);
lean_dec(v___y_2362_);
lean_dec_ref(v___y_2361_);
lean_dec(v___y_2360_);
lean_dec_ref(v___y_2359_);
lean_dec_ref(v_as_2355_);
lean_dec_ref(v___x_2354_);
return v_res_2370_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___lam__0(lean_object* v_a_2372_, lean_object* v_x_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_){
_start:
{
lean_object* v___x_2385_; lean_object* v___x_2386_; 
v___x_2385_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___lam__0___closed__0));
v___x_2386_ = l_Lean_Meta_Sym_Simp_Theorems_rewrite(v_a_2372_, v___x_2385_, v___y_2374_, v___y_2375_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_);
return v___x_2386_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___lam__0___boxed(lean_object* v_a_2387_, lean_object* v_x_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_){
_start:
{
lean_object* v_res_2400_; 
v_res_2400_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___lam__0(v_a_2387_, v_x_2388_, v___y_2389_, v___y_2390_, v___y_2391_, v___y_2392_, v___y_2393_, v___y_2394_, v___y_2395_, v___y_2396_, v___y_2397_, v___y_2398_);
lean_dec(v___y_2398_);
lean_dec_ref(v___y_2397_);
lean_dec(v___y_2396_);
lean_dec_ref(v___y_2395_);
lean_dec(v___y_2394_);
lean_dec_ref(v___y_2393_);
lean_dec(v___y_2392_);
lean_dec_ref(v___y_2391_);
lean_dec(v___y_2390_);
lean_dec_ref(v_a_2387_);
return v_res_2400_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___lam__1(lean_object* v_post_2401_, lean_object* v___f_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_){
_start:
{
lean_object* v___x_2414_; 
lean_inc(v___y_2412_);
lean_inc_ref(v___y_2411_);
lean_inc(v___y_2410_);
lean_inc_ref(v___y_2409_);
lean_inc(v___y_2408_);
lean_inc_ref(v___y_2407_);
lean_inc(v___y_2406_);
lean_inc_ref(v___y_2405_);
lean_inc(v___y_2404_);
lean_inc_ref(v___y_2403_);
v___x_2414_ = lean_apply_11(v_post_2401_, v___y_2403_, v___y_2404_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_, lean_box(0));
if (lean_obj_tag(v___x_2414_) == 0)
{
lean_object* v_a_2415_; lean_object* v___x_2416_; 
v_a_2415_ = lean_ctor_get(v___x_2414_, 0);
lean_inc(v_a_2415_);
v___x_2416_ = lean_box(0);
if (lean_obj_tag(v_a_2415_) == 0)
{
uint8_t v_done_2417_; 
v_done_2417_ = lean_ctor_get_uint8(v_a_2415_, 0);
if (v_done_2417_ == 0)
{
uint8_t v_contextDependent_2418_; lean_object* v___x_2419_; 
lean_dec_ref_known(v___x_2414_, 1);
v_contextDependent_2418_ = lean_ctor_get_uint8(v_a_2415_, 1);
lean_dec_ref_known(v_a_2415_, 0);
v___x_2419_ = lean_apply_12(v___f_2402_, v___x_2416_, v___y_2403_, v___y_2404_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_, lean_box(0));
if (lean_obj_tag(v___x_2419_) == 0)
{
lean_object* v_a_2420_; uint8_t v___y_2422_; 
v_a_2420_ = lean_ctor_get(v___x_2419_, 0);
lean_inc(v_a_2420_);
if (v_contextDependent_2418_ == 0)
{
lean_dec(v_a_2420_);
return v___x_2419_;
}
else
{
if (lean_obj_tag(v_a_2420_) == 0)
{
uint8_t v_contextDependent_2432_; uint8_t v___x_2433_; 
v_contextDependent_2432_ = lean_ctor_get_uint8(v_a_2420_, 1);
v___x_2433_ = lean_bool_not(v_contextDependent_2432_);
v___y_2422_ = v___x_2433_;
goto v___jp_2421_;
}
else
{
uint8_t v_contextDependent_2434_; uint8_t v___x_2435_; 
v_contextDependent_2434_ = lean_ctor_get_uint8(v_a_2420_, sizeof(void*)*2 + 1);
v___x_2435_ = lean_bool_not(v_contextDependent_2434_);
v___y_2422_ = v___x_2435_;
goto v___jp_2421_;
}
}
v___jp_2421_:
{
if (v___y_2422_ == 0)
{
lean_dec(v_a_2420_);
return v___x_2419_;
}
else
{
lean_object* v___x_2424_; uint8_t v_isShared_2425_; uint8_t v_isSharedCheck_2430_; 
v_isSharedCheck_2430_ = !lean_is_exclusive(v___x_2419_);
if (v_isSharedCheck_2430_ == 0)
{
lean_object* v_unused_2431_; 
v_unused_2431_ = lean_ctor_get(v___x_2419_, 0);
lean_dec(v_unused_2431_);
v___x_2424_ = v___x_2419_;
v_isShared_2425_ = v_isSharedCheck_2430_;
goto v_resetjp_2423_;
}
else
{
lean_dec(v___x_2419_);
v___x_2424_ = lean_box(0);
v_isShared_2425_ = v_isSharedCheck_2430_;
goto v_resetjp_2423_;
}
v_resetjp_2423_:
{
lean_object* v___x_2426_; lean_object* v___x_2428_; 
v___x_2426_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_2420_);
if (v_isShared_2425_ == 0)
{
lean_ctor_set(v___x_2424_, 0, v___x_2426_);
v___x_2428_ = v___x_2424_;
goto v_reusejp_2427_;
}
else
{
lean_object* v_reuseFailAlloc_2429_; 
v_reuseFailAlloc_2429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2429_, 0, v___x_2426_);
v___x_2428_ = v_reuseFailAlloc_2429_;
goto v_reusejp_2427_;
}
v_reusejp_2427_:
{
return v___x_2428_;
}
}
}
}
}
else
{
return v___x_2419_;
}
}
else
{
lean_dec_ref_known(v_a_2415_, 0);
lean_dec(v___y_2412_);
lean_dec_ref(v___y_2411_);
lean_dec(v___y_2410_);
lean_dec_ref(v___y_2409_);
lean_dec(v___y_2408_);
lean_dec_ref(v___y_2407_);
lean_dec(v___y_2406_);
lean_dec_ref(v___y_2405_);
lean_dec(v___y_2404_);
lean_dec_ref(v___y_2403_);
lean_dec_ref(v___f_2402_);
return v___x_2414_;
}
}
else
{
uint8_t v_done_2436_; 
v_done_2436_ = lean_ctor_get_uint8(v_a_2415_, sizeof(void*)*2);
if (v_done_2436_ == 0)
{
lean_object* v_e_x27_2437_; lean_object* v_proof_2438_; uint8_t v_contextDependent_2439_; lean_object* v___x_2441_; uint8_t v_isShared_2442_; uint8_t v_isSharedCheck_2489_; 
lean_dec_ref_known(v___x_2414_, 1);
v_e_x27_2437_ = lean_ctor_get(v_a_2415_, 0);
v_proof_2438_ = lean_ctor_get(v_a_2415_, 1);
v_contextDependent_2439_ = lean_ctor_get_uint8(v_a_2415_, sizeof(void*)*2 + 1);
v_isSharedCheck_2489_ = !lean_is_exclusive(v_a_2415_);
if (v_isSharedCheck_2489_ == 0)
{
v___x_2441_ = v_a_2415_;
v_isShared_2442_ = v_isSharedCheck_2489_;
goto v_resetjp_2440_;
}
else
{
lean_inc(v_proof_2438_);
lean_inc(v_e_x27_2437_);
lean_dec(v_a_2415_);
v___x_2441_ = lean_box(0);
v_isShared_2442_ = v_isSharedCheck_2489_;
goto v_resetjp_2440_;
}
v_resetjp_2440_:
{
lean_object* v___x_2443_; 
lean_inc(v___y_2412_);
lean_inc_ref(v___y_2411_);
lean_inc(v___y_2410_);
lean_inc_ref(v___y_2409_);
lean_inc(v___y_2408_);
lean_inc_ref(v___y_2407_);
lean_inc_ref(v_e_x27_2437_);
v___x_2443_ = lean_apply_12(v___f_2402_, v___x_2416_, v_e_x27_2437_, v___y_2404_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_, lean_box(0));
if (lean_obj_tag(v___x_2443_) == 0)
{
lean_object* v_a_2444_; lean_object* v___x_2446_; uint8_t v_isShared_2447_; uint8_t v_isSharedCheck_2488_; 
v_a_2444_ = lean_ctor_get(v___x_2443_, 0);
v_isSharedCheck_2488_ = !lean_is_exclusive(v___x_2443_);
if (v_isSharedCheck_2488_ == 0)
{
v___x_2446_ = v___x_2443_;
v_isShared_2447_ = v_isSharedCheck_2488_;
goto v_resetjp_2445_;
}
else
{
lean_inc(v_a_2444_);
lean_dec(v___x_2443_);
v___x_2446_ = lean_box(0);
v_isShared_2447_ = v_isSharedCheck_2488_;
goto v_resetjp_2445_;
}
v_resetjp_2445_:
{
if (lean_obj_tag(v_a_2444_) == 0)
{
uint8_t v_done_2448_; uint8_t v_contextDependent_2449_; uint8_t v___y_2451_; 
lean_dec(v___y_2412_);
lean_dec_ref(v___y_2411_);
lean_dec(v___y_2410_);
lean_dec_ref(v___y_2409_);
lean_dec(v___y_2408_);
lean_dec_ref(v___y_2407_);
lean_dec_ref(v___y_2403_);
v_done_2448_ = lean_ctor_get_uint8(v_a_2444_, 0);
v_contextDependent_2449_ = lean_ctor_get_uint8(v_a_2444_, 1);
lean_dec_ref_known(v_a_2444_, 0);
if (v_contextDependent_2439_ == 0)
{
v___y_2451_ = v_contextDependent_2449_;
goto v___jp_2450_;
}
else
{
v___y_2451_ = v_contextDependent_2439_;
goto v___jp_2450_;
}
v___jp_2450_:
{
lean_object* v___x_2453_; 
if (v_isShared_2442_ == 0)
{
v___x_2453_ = v___x_2441_;
goto v_reusejp_2452_;
}
else
{
lean_object* v_reuseFailAlloc_2457_; 
v_reuseFailAlloc_2457_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2457_, 0, v_e_x27_2437_);
lean_ctor_set(v_reuseFailAlloc_2457_, 1, v_proof_2438_);
v___x_2453_ = v_reuseFailAlloc_2457_;
goto v_reusejp_2452_;
}
v_reusejp_2452_:
{
lean_object* v___x_2455_; 
lean_ctor_set_uint8(v___x_2453_, sizeof(void*)*2, v_done_2448_);
lean_ctor_set_uint8(v___x_2453_, sizeof(void*)*2 + 1, v___y_2451_);
if (v_isShared_2447_ == 0)
{
lean_ctor_set(v___x_2446_, 0, v___x_2453_);
v___x_2455_ = v___x_2446_;
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
}
else
{
lean_object* v_e_x27_2458_; lean_object* v_proof_2459_; uint8_t v_done_2460_; uint8_t v_contextDependent_2461_; lean_object* v___x_2463_; uint8_t v_isShared_2464_; uint8_t v_isSharedCheck_2487_; 
lean_del_object(v___x_2446_);
lean_del_object(v___x_2441_);
v_e_x27_2458_ = lean_ctor_get(v_a_2444_, 0);
v_proof_2459_ = lean_ctor_get(v_a_2444_, 1);
v_done_2460_ = lean_ctor_get_uint8(v_a_2444_, sizeof(void*)*2);
v_contextDependent_2461_ = lean_ctor_get_uint8(v_a_2444_, sizeof(void*)*2 + 1);
v_isSharedCheck_2487_ = !lean_is_exclusive(v_a_2444_);
if (v_isSharedCheck_2487_ == 0)
{
v___x_2463_ = v_a_2444_;
v_isShared_2464_ = v_isSharedCheck_2487_;
goto v_resetjp_2462_;
}
else
{
lean_inc(v_proof_2459_);
lean_inc(v_e_x27_2458_);
lean_dec(v_a_2444_);
v___x_2463_ = lean_box(0);
v_isShared_2464_ = v_isSharedCheck_2487_;
goto v_resetjp_2462_;
}
v_resetjp_2462_:
{
lean_object* v___x_2465_; 
lean_inc_ref(v_e_x27_2458_);
v___x_2465_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_2403_, v_e_x27_2437_, v_proof_2438_, v_e_x27_2458_, v_proof_2459_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_);
lean_dec(v___y_2412_);
lean_dec_ref(v___y_2411_);
lean_dec(v___y_2410_);
lean_dec_ref(v___y_2409_);
lean_dec(v___y_2408_);
lean_dec_ref(v___y_2407_);
if (lean_obj_tag(v___x_2465_) == 0)
{
lean_object* v_a_2466_; lean_object* v___x_2468_; uint8_t v_isShared_2469_; uint8_t v_isSharedCheck_2478_; 
v_a_2466_ = lean_ctor_get(v___x_2465_, 0);
v_isSharedCheck_2478_ = !lean_is_exclusive(v___x_2465_);
if (v_isSharedCheck_2478_ == 0)
{
v___x_2468_ = v___x_2465_;
v_isShared_2469_ = v_isSharedCheck_2478_;
goto v_resetjp_2467_;
}
else
{
lean_inc(v_a_2466_);
lean_dec(v___x_2465_);
v___x_2468_ = lean_box(0);
v_isShared_2469_ = v_isSharedCheck_2478_;
goto v_resetjp_2467_;
}
v_resetjp_2467_:
{
uint8_t v___y_2471_; 
if (v_contextDependent_2439_ == 0)
{
v___y_2471_ = v_contextDependent_2461_;
goto v___jp_2470_;
}
else
{
v___y_2471_ = v_contextDependent_2439_;
goto v___jp_2470_;
}
v___jp_2470_:
{
lean_object* v___x_2473_; 
if (v_isShared_2464_ == 0)
{
lean_ctor_set(v___x_2463_, 1, v_a_2466_);
v___x_2473_ = v___x_2463_;
goto v_reusejp_2472_;
}
else
{
lean_object* v_reuseFailAlloc_2477_; 
v_reuseFailAlloc_2477_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2477_, 0, v_e_x27_2458_);
lean_ctor_set(v_reuseFailAlloc_2477_, 1, v_a_2466_);
lean_ctor_set_uint8(v_reuseFailAlloc_2477_, sizeof(void*)*2, v_done_2460_);
v___x_2473_ = v_reuseFailAlloc_2477_;
goto v_reusejp_2472_;
}
v_reusejp_2472_:
{
lean_object* v___x_2475_; 
lean_ctor_set_uint8(v___x_2473_, sizeof(void*)*2 + 1, v___y_2471_);
if (v_isShared_2469_ == 0)
{
lean_ctor_set(v___x_2468_, 0, v___x_2473_);
v___x_2475_ = v___x_2468_;
goto v_reusejp_2474_;
}
else
{
lean_object* v_reuseFailAlloc_2476_; 
v_reuseFailAlloc_2476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2476_, 0, v___x_2473_);
v___x_2475_ = v_reuseFailAlloc_2476_;
goto v_reusejp_2474_;
}
v_reusejp_2474_:
{
return v___x_2475_;
}
}
}
}
}
else
{
lean_object* v_a_2479_; lean_object* v___x_2481_; uint8_t v_isShared_2482_; uint8_t v_isSharedCheck_2486_; 
lean_del_object(v___x_2463_);
lean_dec_ref(v_e_x27_2458_);
v_a_2479_ = lean_ctor_get(v___x_2465_, 0);
v_isSharedCheck_2486_ = !lean_is_exclusive(v___x_2465_);
if (v_isSharedCheck_2486_ == 0)
{
v___x_2481_ = v___x_2465_;
v_isShared_2482_ = v_isSharedCheck_2486_;
goto v_resetjp_2480_;
}
else
{
lean_inc(v_a_2479_);
lean_dec(v___x_2465_);
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
}
else
{
lean_del_object(v___x_2441_);
lean_dec_ref(v_proof_2438_);
lean_dec_ref(v_e_x27_2437_);
lean_dec(v___y_2412_);
lean_dec_ref(v___y_2411_);
lean_dec(v___y_2410_);
lean_dec_ref(v___y_2409_);
lean_dec(v___y_2408_);
lean_dec_ref(v___y_2407_);
lean_dec_ref(v___y_2403_);
return v___x_2443_;
}
}
}
else
{
lean_dec_ref_known(v_a_2415_, 2);
lean_dec(v___y_2412_);
lean_dec_ref(v___y_2411_);
lean_dec(v___y_2410_);
lean_dec_ref(v___y_2409_);
lean_dec(v___y_2408_);
lean_dec_ref(v___y_2407_);
lean_dec(v___y_2406_);
lean_dec_ref(v___y_2405_);
lean_dec(v___y_2404_);
lean_dec_ref(v___y_2403_);
lean_dec_ref(v___f_2402_);
return v___x_2414_;
}
}
}
else
{
lean_dec(v___y_2412_);
lean_dec_ref(v___y_2411_);
lean_dec(v___y_2410_);
lean_dec_ref(v___y_2409_);
lean_dec(v___y_2408_);
lean_dec_ref(v___y_2407_);
lean_dec(v___y_2406_);
lean_dec_ref(v___y_2405_);
lean_dec(v___y_2404_);
lean_dec_ref(v___y_2403_);
lean_dec_ref(v___f_2402_);
return v___x_2414_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___lam__1___boxed(lean_object* v_post_2490_, lean_object* v___f_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_){
_start:
{
lean_object* v_res_2503_; 
v_res_2503_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___lam__1(v_post_2490_, v___f_2491_, v___y_2492_, v___y_2493_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_, v___y_2501_);
return v_res_2503_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems_spec__0___redArg(lean_object* v_as_2504_, size_t v_sz_2505_, size_t v_i_2506_, lean_object* v_b_2507_){
_start:
{
uint8_t v___x_2509_; 
v___x_2509_ = lean_usize_dec_lt(v_i_2506_, v_sz_2505_);
if (v___x_2509_ == 0)
{
lean_object* v___x_2510_; 
v___x_2510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2510_, 0, v_b_2507_);
return v___x_2510_;
}
else
{
lean_object* v_a_2511_; lean_object* v___x_2512_; size_t v___x_2513_; size_t v___x_2514_; 
v_a_2511_ = lean_array_uget_borrowed(v_as_2504_, v_i_2506_);
lean_inc(v_a_2511_);
v___x_2512_ = l_Lean_Meta_Sym_Simp_Theorems_insert(v_b_2507_, v_a_2511_);
v___x_2513_ = ((size_t)1ULL);
v___x_2514_ = lean_usize_add(v_i_2506_, v___x_2513_);
v_i_2506_ = v___x_2514_;
v_b_2507_ = v___x_2512_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems_spec__0___redArg___boxed(lean_object* v_as_2516_, lean_object* v_sz_2517_, lean_object* v_i_2518_, lean_object* v_b_2519_, lean_object* v___y_2520_){
_start:
{
size_t v_sz_boxed_2521_; size_t v_i_boxed_2522_; lean_object* v_res_2523_; 
v_sz_boxed_2521_ = lean_unbox_usize(v_sz_2517_);
lean_dec(v_sz_2517_);
v_i_boxed_2522_ = lean_unbox_usize(v_i_2518_);
lean_dec(v_i_2518_);
v_res_2523_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems_spec__0___redArg(v_as_2516_, v_sz_boxed_2521_, v_i_boxed_2522_, v_b_2519_);
lean_dec_ref(v_as_2516_);
return v_res_2523_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___closed__0(void){
_start:
{
lean_object* v___x_2524_; 
v___x_2524_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2524_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___closed__1(void){
_start:
{
lean_object* v___x_2525_; lean_object* v_thms_2526_; 
v___x_2525_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___closed__0, &l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___closed__0_once, _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___closed__0);
v_thms_2526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_thms_2526_, 0, v___x_2525_);
return v_thms_2526_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems(lean_object* v_post_2527_, lean_object* v_extraThms_2528_, lean_object* v_a_2529_, lean_object* v_a_2530_, lean_object* v_a_2531_, lean_object* v_a_2532_, lean_object* v_a_2533_, lean_object* v_a_2534_, lean_object* v_a_2535_, lean_object* v_a_2536_){
_start:
{
lean_object* v___x_2538_; lean_object* v___x_2539_; uint8_t v___x_2540_; 
v___x_2538_ = lean_array_get_size(v_extraThms_2528_);
v___x_2539_ = lean_unsigned_to_nat(0u);
v___x_2540_ = lean_nat_dec_eq(v___x_2538_, v___x_2539_);
if (v___x_2540_ == 0)
{
lean_object* v_thms_2541_; size_t v_sz_2542_; size_t v___x_2543_; lean_object* v___x_2544_; 
v_thms_2541_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___closed__1, &l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___closed__1);
v_sz_2542_ = lean_array_size(v_extraThms_2528_);
v___x_2543_ = ((size_t)0ULL);
v___x_2544_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems_spec__0___redArg(v_extraThms_2528_, v_sz_2542_, v___x_2543_, v_thms_2541_);
if (lean_obj_tag(v___x_2544_) == 0)
{
lean_object* v_a_2545_; lean_object* v___x_2547_; uint8_t v_isShared_2548_; uint8_t v_isSharedCheck_2554_; 
v_a_2545_ = lean_ctor_get(v___x_2544_, 0);
v_isSharedCheck_2554_ = !lean_is_exclusive(v___x_2544_);
if (v_isSharedCheck_2554_ == 0)
{
v___x_2547_ = v___x_2544_;
v_isShared_2548_ = v_isSharedCheck_2554_;
goto v_resetjp_2546_;
}
else
{
lean_inc(v_a_2545_);
lean_dec(v___x_2544_);
v___x_2547_ = lean_box(0);
v_isShared_2548_ = v_isSharedCheck_2554_;
goto v_resetjp_2546_;
}
v_resetjp_2546_:
{
lean_object* v___f_2549_; lean_object* v___f_2550_; lean_object* v___x_2552_; 
v___f_2549_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___lam__0___boxed), 13, 1);
lean_closure_set(v___f_2549_, 0, v_a_2545_);
v___f_2550_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___lam__1___boxed), 13, 2);
lean_closure_set(v___f_2550_, 0, v_post_2527_);
lean_closure_set(v___f_2550_, 1, v___f_2549_);
if (v_isShared_2548_ == 0)
{
lean_ctor_set(v___x_2547_, 0, v___f_2550_);
v___x_2552_ = v___x_2547_;
goto v_reusejp_2551_;
}
else
{
lean_object* v_reuseFailAlloc_2553_; 
v_reuseFailAlloc_2553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2553_, 0, v___f_2550_);
v___x_2552_ = v_reuseFailAlloc_2553_;
goto v_reusejp_2551_;
}
v_reusejp_2551_:
{
return v___x_2552_;
}
}
}
else
{
lean_object* v_a_2555_; lean_object* v___x_2557_; uint8_t v_isShared_2558_; uint8_t v_isSharedCheck_2562_; 
lean_dec_ref(v_post_2527_);
v_a_2555_ = lean_ctor_get(v___x_2544_, 0);
v_isSharedCheck_2562_ = !lean_is_exclusive(v___x_2544_);
if (v_isSharedCheck_2562_ == 0)
{
v___x_2557_ = v___x_2544_;
v_isShared_2558_ = v_isSharedCheck_2562_;
goto v_resetjp_2556_;
}
else
{
lean_inc(v_a_2555_);
lean_dec(v___x_2544_);
v___x_2557_ = lean_box(0);
v_isShared_2558_ = v_isSharedCheck_2562_;
goto v_resetjp_2556_;
}
v_resetjp_2556_:
{
lean_object* v___x_2560_; 
if (v_isShared_2558_ == 0)
{
v___x_2560_ = v___x_2557_;
goto v_reusejp_2559_;
}
else
{
lean_object* v_reuseFailAlloc_2561_; 
v_reuseFailAlloc_2561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2561_, 0, v_a_2555_);
v___x_2560_ = v_reuseFailAlloc_2561_;
goto v_reusejp_2559_;
}
v_reusejp_2559_:
{
return v___x_2560_;
}
}
}
}
else
{
lean_object* v___x_2563_; 
v___x_2563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2563_, 0, v_post_2527_);
return v___x_2563_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___boxed(lean_object* v_post_2564_, lean_object* v_extraThms_2565_, lean_object* v_a_2566_, lean_object* v_a_2567_, lean_object* v_a_2568_, lean_object* v_a_2569_, lean_object* v_a_2570_, lean_object* v_a_2571_, lean_object* v_a_2572_, lean_object* v_a_2573_, lean_object* v_a_2574_){
_start:
{
lean_object* v_res_2575_; 
v_res_2575_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems(v_post_2564_, v_extraThms_2565_, v_a_2566_, v_a_2567_, v_a_2568_, v_a_2569_, v_a_2570_, v_a_2571_, v_a_2572_, v_a_2573_);
lean_dec(v_a_2573_);
lean_dec_ref(v_a_2572_);
lean_dec(v_a_2571_);
lean_dec_ref(v_a_2570_);
lean_dec(v_a_2569_);
lean_dec_ref(v_a_2568_);
lean_dec(v_a_2567_);
lean_dec_ref(v_a_2566_);
lean_dec_ref(v_extraThms_2565_);
return v_res_2575_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems_spec__0(lean_object* v_as_2576_, size_t v_sz_2577_, size_t v_i_2578_, lean_object* v_b_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_){
_start:
{
lean_object* v___x_2589_; 
v___x_2589_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems_spec__0___redArg(v_as_2576_, v_sz_2577_, v_i_2578_, v_b_2579_);
return v___x_2589_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems_spec__0___boxed(lean_object* v_as_2590_, lean_object* v_sz_2591_, lean_object* v_i_2592_, lean_object* v_b_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_){
_start:
{
size_t v_sz_boxed_2603_; size_t v_i_boxed_2604_; lean_object* v_res_2605_; 
v_sz_boxed_2603_ = lean_unbox_usize(v_sz_2591_);
lean_dec(v_sz_2591_);
v_i_boxed_2604_ = lean_unbox_usize(v_i_2592_);
lean_dec(v_i_2592_);
v_res_2605_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems_spec__0(v_as_2590_, v_sz_boxed_2603_, v_i_boxed_2604_, v_b_2593_, v___y_2594_, v___y_2595_, v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_);
lean_dec(v___y_2601_);
lean_dec_ref(v___y_2600_);
lean_dec(v___y_2599_);
lean_dec_ref(v___y_2598_);
lean_dec(v___y_2597_);
lean_dec_ref(v___y_2596_);
lean_dec(v___y_2595_);
lean_dec_ref(v___y_2594_);
lean_dec_ref(v_as_2590_);
return v_res_2605_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkSimpDefaultMethods___lam__1(lean_object* v___x_2606_, lean_object* v___f_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_){
_start:
{
lean_object* v___x_2619_; 
lean_inc_ref(v___y_2608_);
v___x_2619_ = l_Lean_Meta_Sym_Simp_evalGround___redArg(v___x_2606_, v___y_2608_, v___y_2612_, v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_, v___y_2617_);
if (lean_obj_tag(v___x_2619_) == 0)
{
lean_object* v_a_2620_; lean_object* v___x_2621_; 
v_a_2620_ = lean_ctor_get(v___x_2619_, 0);
lean_inc(v_a_2620_);
v___x_2621_ = lean_box(0);
if (lean_obj_tag(v_a_2620_) == 0)
{
uint8_t v_done_2622_; 
v_done_2622_ = lean_ctor_get_uint8(v_a_2620_, 0);
if (v_done_2622_ == 0)
{
uint8_t v_contextDependent_2623_; lean_object* v___x_2624_; 
lean_dec_ref_known(v___x_2619_, 1);
v_contextDependent_2623_ = lean_ctor_get_uint8(v_a_2620_, 1);
lean_dec_ref_known(v_a_2620_, 0);
v___x_2624_ = lean_apply_12(v___f_2607_, v___x_2621_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_, v___y_2612_, v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_, v___y_2617_, lean_box(0));
if (lean_obj_tag(v___x_2624_) == 0)
{
lean_object* v_a_2625_; uint8_t v___y_2627_; 
v_a_2625_ = lean_ctor_get(v___x_2624_, 0);
lean_inc(v_a_2625_);
if (v_contextDependent_2623_ == 0)
{
lean_dec(v_a_2625_);
return v___x_2624_;
}
else
{
if (lean_obj_tag(v_a_2625_) == 0)
{
uint8_t v_contextDependent_2637_; uint8_t v___x_2638_; 
v_contextDependent_2637_ = lean_ctor_get_uint8(v_a_2625_, 1);
v___x_2638_ = lean_bool_not(v_contextDependent_2637_);
v___y_2627_ = v___x_2638_;
goto v___jp_2626_;
}
else
{
uint8_t v_contextDependent_2639_; uint8_t v___x_2640_; 
v_contextDependent_2639_ = lean_ctor_get_uint8(v_a_2625_, sizeof(void*)*2 + 1);
v___x_2640_ = lean_bool_not(v_contextDependent_2639_);
v___y_2627_ = v___x_2640_;
goto v___jp_2626_;
}
}
v___jp_2626_:
{
if (v___y_2627_ == 0)
{
lean_dec(v_a_2625_);
return v___x_2624_;
}
else
{
lean_object* v___x_2629_; uint8_t v_isShared_2630_; uint8_t v_isSharedCheck_2635_; 
v_isSharedCheck_2635_ = !lean_is_exclusive(v___x_2624_);
if (v_isSharedCheck_2635_ == 0)
{
lean_object* v_unused_2636_; 
v_unused_2636_ = lean_ctor_get(v___x_2624_, 0);
lean_dec(v_unused_2636_);
v___x_2629_ = v___x_2624_;
v_isShared_2630_ = v_isSharedCheck_2635_;
goto v_resetjp_2628_;
}
else
{
lean_dec(v___x_2624_);
v___x_2629_ = lean_box(0);
v_isShared_2630_ = v_isSharedCheck_2635_;
goto v_resetjp_2628_;
}
v_resetjp_2628_:
{
lean_object* v___x_2631_; lean_object* v___x_2633_; 
v___x_2631_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_2625_);
if (v_isShared_2630_ == 0)
{
lean_ctor_set(v___x_2629_, 0, v___x_2631_);
v___x_2633_ = v___x_2629_;
goto v_reusejp_2632_;
}
else
{
lean_object* v_reuseFailAlloc_2634_; 
v_reuseFailAlloc_2634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2634_, 0, v___x_2631_);
v___x_2633_ = v_reuseFailAlloc_2634_;
goto v_reusejp_2632_;
}
v_reusejp_2632_:
{
return v___x_2633_;
}
}
}
}
}
else
{
return v___x_2624_;
}
}
else
{
lean_dec_ref_known(v_a_2620_, 0);
lean_dec(v___y_2617_);
lean_dec_ref(v___y_2616_);
lean_dec(v___y_2615_);
lean_dec_ref(v___y_2614_);
lean_dec(v___y_2613_);
lean_dec_ref(v___y_2612_);
lean_dec(v___y_2611_);
lean_dec_ref(v___y_2610_);
lean_dec(v___y_2609_);
lean_dec_ref(v___y_2608_);
lean_dec_ref(v___f_2607_);
return v___x_2619_;
}
}
else
{
uint8_t v_done_2641_; 
v_done_2641_ = lean_ctor_get_uint8(v_a_2620_, sizeof(void*)*2);
if (v_done_2641_ == 0)
{
lean_object* v_e_x27_2642_; lean_object* v_proof_2643_; uint8_t v_contextDependent_2644_; lean_object* v___x_2646_; uint8_t v_isShared_2647_; uint8_t v_isSharedCheck_2694_; 
lean_dec_ref_known(v___x_2619_, 1);
v_e_x27_2642_ = lean_ctor_get(v_a_2620_, 0);
v_proof_2643_ = lean_ctor_get(v_a_2620_, 1);
v_contextDependent_2644_ = lean_ctor_get_uint8(v_a_2620_, sizeof(void*)*2 + 1);
v_isSharedCheck_2694_ = !lean_is_exclusive(v_a_2620_);
if (v_isSharedCheck_2694_ == 0)
{
v___x_2646_ = v_a_2620_;
v_isShared_2647_ = v_isSharedCheck_2694_;
goto v_resetjp_2645_;
}
else
{
lean_inc(v_proof_2643_);
lean_inc(v_e_x27_2642_);
lean_dec(v_a_2620_);
v___x_2646_ = lean_box(0);
v_isShared_2647_ = v_isSharedCheck_2694_;
goto v_resetjp_2645_;
}
v_resetjp_2645_:
{
lean_object* v___x_2648_; 
lean_inc(v___y_2617_);
lean_inc_ref(v___y_2616_);
lean_inc(v___y_2615_);
lean_inc_ref(v___y_2614_);
lean_inc(v___y_2613_);
lean_inc_ref(v___y_2612_);
lean_inc_ref(v_e_x27_2642_);
v___x_2648_ = lean_apply_12(v___f_2607_, v___x_2621_, v_e_x27_2642_, v___y_2609_, v___y_2610_, v___y_2611_, v___y_2612_, v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_, v___y_2617_, lean_box(0));
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
lean_dec(v___y_2617_);
lean_dec_ref(v___y_2616_);
lean_dec(v___y_2615_);
lean_dec_ref(v___y_2614_);
lean_dec(v___y_2613_);
lean_dec_ref(v___y_2612_);
lean_dec_ref(v___y_2608_);
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
v___x_2670_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_2608_, v_e_x27_2642_, v_proof_2643_, v_e_x27_2663_, v_proof_2664_, v___y_2612_, v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_, v___y_2617_);
lean_dec(v___y_2617_);
lean_dec_ref(v___y_2616_);
lean_dec(v___y_2615_);
lean_dec_ref(v___y_2614_);
lean_dec(v___y_2613_);
lean_dec_ref(v___y_2612_);
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
lean_dec(v___y_2617_);
lean_dec_ref(v___y_2616_);
lean_dec(v___y_2615_);
lean_dec_ref(v___y_2614_);
lean_dec(v___y_2613_);
lean_dec_ref(v___y_2612_);
lean_dec_ref(v___y_2608_);
return v___x_2648_;
}
}
}
else
{
lean_dec_ref_known(v_a_2620_, 2);
lean_dec(v___y_2617_);
lean_dec_ref(v___y_2616_);
lean_dec(v___y_2615_);
lean_dec_ref(v___y_2614_);
lean_dec(v___y_2613_);
lean_dec_ref(v___y_2612_);
lean_dec(v___y_2611_);
lean_dec_ref(v___y_2610_);
lean_dec(v___y_2609_);
lean_dec_ref(v___y_2608_);
lean_dec_ref(v___f_2607_);
return v___x_2619_;
}
}
}
else
{
lean_dec(v___y_2617_);
lean_dec_ref(v___y_2616_);
lean_dec(v___y_2615_);
lean_dec_ref(v___y_2614_);
lean_dec(v___y_2613_);
lean_dec_ref(v___y_2612_);
lean_dec(v___y_2611_);
lean_dec_ref(v___y_2610_);
lean_dec(v___y_2609_);
lean_dec_ref(v___y_2608_);
lean_dec_ref(v___f_2607_);
return v___x_2619_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkSimpDefaultMethods___lam__1___boxed(lean_object* v___x_2695_, lean_object* v___f_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_){
_start:
{
lean_object* v_res_2708_; 
v_res_2708_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkSimpDefaultMethods___lam__1(v___x_2695_, v___f_2696_, v___y_2697_, v___y_2698_, v___y_2699_, v___y_2700_, v___y_2701_, v___y_2702_, v___y_2703_, v___y_2704_, v___y_2705_, v___y_2706_);
lean_dec(v___x_2695_);
return v_res_2708_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkSimpDefaultMethods___lam__0(lean_object* v_x_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_){
_start:
{
lean_object* v___x_2722_; lean_object* v___x_2723_; 
v___x_2722_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkSimpDefaultMethods___lam__0___closed__0));
v___x_2723_ = l_Lean_Meta_Sym_Simp_simpArrowTelescope(v___x_2722_, v___y_2711_, v___y_2712_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_, v___y_2719_, v___y_2720_);
return v___x_2723_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkSimpDefaultMethods___lam__0___boxed(lean_object* v_x_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_){
_start:
{
lean_object* v_res_2736_; 
v_res_2736_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkSimpDefaultMethods___lam__0(v_x_2724_, v___y_2725_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_);
lean_dec(v___y_2734_);
lean_dec_ref(v___y_2733_);
lean_dec(v___y_2732_);
lean_dec_ref(v___y_2731_);
lean_dec(v___y_2730_);
lean_dec_ref(v___y_2729_);
lean_dec(v___y_2728_);
lean_dec_ref(v___y_2727_);
lean_dec(v___y_2726_);
return v_res_2736_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkSimpDefaultMethods___lam__2(lean_object* v___f_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_){
_start:
{
lean_object* v___x_2749_; 
lean_inc_ref(v___y_2738_);
v___x_2749_ = l_Lean_Meta_Sym_Simp_simpControl(v___y_2738_, v___y_2739_, v___y_2740_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_);
if (lean_obj_tag(v___x_2749_) == 0)
{
lean_object* v_a_2750_; lean_object* v___x_2751_; 
v_a_2750_ = lean_ctor_get(v___x_2749_, 0);
lean_inc(v_a_2750_);
v___x_2751_ = lean_box(0);
if (lean_obj_tag(v_a_2750_) == 0)
{
uint8_t v_done_2752_; 
v_done_2752_ = lean_ctor_get_uint8(v_a_2750_, 0);
if (v_done_2752_ == 0)
{
uint8_t v_contextDependent_2753_; lean_object* v___x_2754_; 
lean_dec_ref_known(v___x_2749_, 1);
v_contextDependent_2753_ = lean_ctor_get_uint8(v_a_2750_, 1);
lean_dec_ref_known(v_a_2750_, 0);
v___x_2754_ = lean_apply_12(v___f_2737_, v___x_2751_, v___y_2738_, v___y_2739_, v___y_2740_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_, lean_box(0));
if (lean_obj_tag(v___x_2754_) == 0)
{
lean_object* v_a_2755_; uint8_t v___y_2757_; 
v_a_2755_ = lean_ctor_get(v___x_2754_, 0);
lean_inc(v_a_2755_);
if (v_contextDependent_2753_ == 0)
{
lean_dec(v_a_2755_);
return v___x_2754_;
}
else
{
if (lean_obj_tag(v_a_2755_) == 0)
{
uint8_t v_contextDependent_2767_; uint8_t v___x_2768_; 
v_contextDependent_2767_ = lean_ctor_get_uint8(v_a_2755_, 1);
v___x_2768_ = lean_bool_not(v_contextDependent_2767_);
v___y_2757_ = v___x_2768_;
goto v___jp_2756_;
}
else
{
uint8_t v_contextDependent_2769_; uint8_t v___x_2770_; 
v_contextDependent_2769_ = lean_ctor_get_uint8(v_a_2755_, sizeof(void*)*2 + 1);
v___x_2770_ = lean_bool_not(v_contextDependent_2769_);
v___y_2757_ = v___x_2770_;
goto v___jp_2756_;
}
}
v___jp_2756_:
{
if (v___y_2757_ == 0)
{
lean_dec(v_a_2755_);
return v___x_2754_;
}
else
{
lean_object* v___x_2759_; uint8_t v_isShared_2760_; uint8_t v_isSharedCheck_2765_; 
v_isSharedCheck_2765_ = !lean_is_exclusive(v___x_2754_);
if (v_isSharedCheck_2765_ == 0)
{
lean_object* v_unused_2766_; 
v_unused_2766_ = lean_ctor_get(v___x_2754_, 0);
lean_dec(v_unused_2766_);
v___x_2759_ = v___x_2754_;
v_isShared_2760_ = v_isSharedCheck_2765_;
goto v_resetjp_2758_;
}
else
{
lean_dec(v___x_2754_);
v___x_2759_ = lean_box(0);
v_isShared_2760_ = v_isSharedCheck_2765_;
goto v_resetjp_2758_;
}
v_resetjp_2758_:
{
lean_object* v___x_2761_; lean_object* v___x_2763_; 
v___x_2761_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_2755_);
if (v_isShared_2760_ == 0)
{
lean_ctor_set(v___x_2759_, 0, v___x_2761_);
v___x_2763_ = v___x_2759_;
goto v_reusejp_2762_;
}
else
{
lean_object* v_reuseFailAlloc_2764_; 
v_reuseFailAlloc_2764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2764_, 0, v___x_2761_);
v___x_2763_ = v_reuseFailAlloc_2764_;
goto v_reusejp_2762_;
}
v_reusejp_2762_:
{
return v___x_2763_;
}
}
}
}
}
else
{
return v___x_2754_;
}
}
else
{
lean_dec_ref_known(v_a_2750_, 0);
lean_dec(v___y_2747_);
lean_dec_ref(v___y_2746_);
lean_dec(v___y_2745_);
lean_dec_ref(v___y_2744_);
lean_dec(v___y_2743_);
lean_dec_ref(v___y_2742_);
lean_dec(v___y_2741_);
lean_dec_ref(v___y_2740_);
lean_dec(v___y_2739_);
lean_dec_ref(v___y_2738_);
lean_dec_ref(v___f_2737_);
return v___x_2749_;
}
}
else
{
uint8_t v_done_2771_; 
v_done_2771_ = lean_ctor_get_uint8(v_a_2750_, sizeof(void*)*2);
if (v_done_2771_ == 0)
{
lean_object* v_e_x27_2772_; lean_object* v_proof_2773_; uint8_t v_contextDependent_2774_; lean_object* v___x_2776_; uint8_t v_isShared_2777_; uint8_t v_isSharedCheck_2824_; 
lean_dec_ref_known(v___x_2749_, 1);
v_e_x27_2772_ = lean_ctor_get(v_a_2750_, 0);
v_proof_2773_ = lean_ctor_get(v_a_2750_, 1);
v_contextDependent_2774_ = lean_ctor_get_uint8(v_a_2750_, sizeof(void*)*2 + 1);
v_isSharedCheck_2824_ = !lean_is_exclusive(v_a_2750_);
if (v_isSharedCheck_2824_ == 0)
{
v___x_2776_ = v_a_2750_;
v_isShared_2777_ = v_isSharedCheck_2824_;
goto v_resetjp_2775_;
}
else
{
lean_inc(v_proof_2773_);
lean_inc(v_e_x27_2772_);
lean_dec(v_a_2750_);
v___x_2776_ = lean_box(0);
v_isShared_2777_ = v_isSharedCheck_2824_;
goto v_resetjp_2775_;
}
v_resetjp_2775_:
{
lean_object* v___x_2778_; 
lean_inc(v___y_2747_);
lean_inc_ref(v___y_2746_);
lean_inc(v___y_2745_);
lean_inc_ref(v___y_2744_);
lean_inc(v___y_2743_);
lean_inc_ref(v___y_2742_);
lean_inc_ref(v_e_x27_2772_);
v___x_2778_ = lean_apply_12(v___f_2737_, v___x_2751_, v_e_x27_2772_, v___y_2739_, v___y_2740_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_, lean_box(0));
if (lean_obj_tag(v___x_2778_) == 0)
{
lean_object* v_a_2779_; lean_object* v___x_2781_; uint8_t v_isShared_2782_; uint8_t v_isSharedCheck_2823_; 
v_a_2779_ = lean_ctor_get(v___x_2778_, 0);
v_isSharedCheck_2823_ = !lean_is_exclusive(v___x_2778_);
if (v_isSharedCheck_2823_ == 0)
{
v___x_2781_ = v___x_2778_;
v_isShared_2782_ = v_isSharedCheck_2823_;
goto v_resetjp_2780_;
}
else
{
lean_inc(v_a_2779_);
lean_dec(v___x_2778_);
v___x_2781_ = lean_box(0);
v_isShared_2782_ = v_isSharedCheck_2823_;
goto v_resetjp_2780_;
}
v_resetjp_2780_:
{
if (lean_obj_tag(v_a_2779_) == 0)
{
uint8_t v_done_2783_; uint8_t v_contextDependent_2784_; uint8_t v___y_2786_; 
lean_dec(v___y_2747_);
lean_dec_ref(v___y_2746_);
lean_dec(v___y_2745_);
lean_dec_ref(v___y_2744_);
lean_dec(v___y_2743_);
lean_dec_ref(v___y_2742_);
lean_dec_ref(v___y_2738_);
v_done_2783_ = lean_ctor_get_uint8(v_a_2779_, 0);
v_contextDependent_2784_ = lean_ctor_get_uint8(v_a_2779_, 1);
lean_dec_ref_known(v_a_2779_, 0);
if (v_contextDependent_2774_ == 0)
{
v___y_2786_ = v_contextDependent_2784_;
goto v___jp_2785_;
}
else
{
v___y_2786_ = v_contextDependent_2774_;
goto v___jp_2785_;
}
v___jp_2785_:
{
lean_object* v___x_2788_; 
if (v_isShared_2777_ == 0)
{
v___x_2788_ = v___x_2776_;
goto v_reusejp_2787_;
}
else
{
lean_object* v_reuseFailAlloc_2792_; 
v_reuseFailAlloc_2792_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2792_, 0, v_e_x27_2772_);
lean_ctor_set(v_reuseFailAlloc_2792_, 1, v_proof_2773_);
v___x_2788_ = v_reuseFailAlloc_2792_;
goto v_reusejp_2787_;
}
v_reusejp_2787_:
{
lean_object* v___x_2790_; 
lean_ctor_set_uint8(v___x_2788_, sizeof(void*)*2, v_done_2783_);
lean_ctor_set_uint8(v___x_2788_, sizeof(void*)*2 + 1, v___y_2786_);
if (v_isShared_2782_ == 0)
{
lean_ctor_set(v___x_2781_, 0, v___x_2788_);
v___x_2790_ = v___x_2781_;
goto v_reusejp_2789_;
}
else
{
lean_object* v_reuseFailAlloc_2791_; 
v_reuseFailAlloc_2791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2791_, 0, v___x_2788_);
v___x_2790_ = v_reuseFailAlloc_2791_;
goto v_reusejp_2789_;
}
v_reusejp_2789_:
{
return v___x_2790_;
}
}
}
}
else
{
lean_object* v_e_x27_2793_; lean_object* v_proof_2794_; uint8_t v_done_2795_; uint8_t v_contextDependent_2796_; lean_object* v___x_2798_; uint8_t v_isShared_2799_; uint8_t v_isSharedCheck_2822_; 
lean_del_object(v___x_2781_);
lean_del_object(v___x_2776_);
v_e_x27_2793_ = lean_ctor_get(v_a_2779_, 0);
v_proof_2794_ = lean_ctor_get(v_a_2779_, 1);
v_done_2795_ = lean_ctor_get_uint8(v_a_2779_, sizeof(void*)*2);
v_contextDependent_2796_ = lean_ctor_get_uint8(v_a_2779_, sizeof(void*)*2 + 1);
v_isSharedCheck_2822_ = !lean_is_exclusive(v_a_2779_);
if (v_isSharedCheck_2822_ == 0)
{
v___x_2798_ = v_a_2779_;
v_isShared_2799_ = v_isSharedCheck_2822_;
goto v_resetjp_2797_;
}
else
{
lean_inc(v_proof_2794_);
lean_inc(v_e_x27_2793_);
lean_dec(v_a_2779_);
v___x_2798_ = lean_box(0);
v_isShared_2799_ = v_isSharedCheck_2822_;
goto v_resetjp_2797_;
}
v_resetjp_2797_:
{
lean_object* v___x_2800_; 
lean_inc_ref(v_e_x27_2793_);
v___x_2800_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_2738_, v_e_x27_2772_, v_proof_2773_, v_e_x27_2793_, v_proof_2794_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_);
lean_dec(v___y_2747_);
lean_dec_ref(v___y_2746_);
lean_dec(v___y_2745_);
lean_dec_ref(v___y_2744_);
lean_dec(v___y_2743_);
lean_dec_ref(v___y_2742_);
if (lean_obj_tag(v___x_2800_) == 0)
{
lean_object* v_a_2801_; lean_object* v___x_2803_; uint8_t v_isShared_2804_; uint8_t v_isSharedCheck_2813_; 
v_a_2801_ = lean_ctor_get(v___x_2800_, 0);
v_isSharedCheck_2813_ = !lean_is_exclusive(v___x_2800_);
if (v_isSharedCheck_2813_ == 0)
{
v___x_2803_ = v___x_2800_;
v_isShared_2804_ = v_isSharedCheck_2813_;
goto v_resetjp_2802_;
}
else
{
lean_inc(v_a_2801_);
lean_dec(v___x_2800_);
v___x_2803_ = lean_box(0);
v_isShared_2804_ = v_isSharedCheck_2813_;
goto v_resetjp_2802_;
}
v_resetjp_2802_:
{
uint8_t v___y_2806_; 
if (v_contextDependent_2774_ == 0)
{
v___y_2806_ = v_contextDependent_2796_;
goto v___jp_2805_;
}
else
{
v___y_2806_ = v_contextDependent_2774_;
goto v___jp_2805_;
}
v___jp_2805_:
{
lean_object* v___x_2808_; 
if (v_isShared_2799_ == 0)
{
lean_ctor_set(v___x_2798_, 1, v_a_2801_);
v___x_2808_ = v___x_2798_;
goto v_reusejp_2807_;
}
else
{
lean_object* v_reuseFailAlloc_2812_; 
v_reuseFailAlloc_2812_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2812_, 0, v_e_x27_2793_);
lean_ctor_set(v_reuseFailAlloc_2812_, 1, v_a_2801_);
lean_ctor_set_uint8(v_reuseFailAlloc_2812_, sizeof(void*)*2, v_done_2795_);
v___x_2808_ = v_reuseFailAlloc_2812_;
goto v_reusejp_2807_;
}
v_reusejp_2807_:
{
lean_object* v___x_2810_; 
lean_ctor_set_uint8(v___x_2808_, sizeof(void*)*2 + 1, v___y_2806_);
if (v_isShared_2804_ == 0)
{
lean_ctor_set(v___x_2803_, 0, v___x_2808_);
v___x_2810_ = v___x_2803_;
goto v_reusejp_2809_;
}
else
{
lean_object* v_reuseFailAlloc_2811_; 
v_reuseFailAlloc_2811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2811_, 0, v___x_2808_);
v___x_2810_ = v_reuseFailAlloc_2811_;
goto v_reusejp_2809_;
}
v_reusejp_2809_:
{
return v___x_2810_;
}
}
}
}
}
else
{
lean_object* v_a_2814_; lean_object* v___x_2816_; uint8_t v_isShared_2817_; uint8_t v_isSharedCheck_2821_; 
lean_del_object(v___x_2798_);
lean_dec_ref(v_e_x27_2793_);
v_a_2814_ = lean_ctor_get(v___x_2800_, 0);
v_isSharedCheck_2821_ = !lean_is_exclusive(v___x_2800_);
if (v_isSharedCheck_2821_ == 0)
{
v___x_2816_ = v___x_2800_;
v_isShared_2817_ = v_isSharedCheck_2821_;
goto v_resetjp_2815_;
}
else
{
lean_inc(v_a_2814_);
lean_dec(v___x_2800_);
v___x_2816_ = lean_box(0);
v_isShared_2817_ = v_isSharedCheck_2821_;
goto v_resetjp_2815_;
}
v_resetjp_2815_:
{
lean_object* v___x_2819_; 
if (v_isShared_2817_ == 0)
{
v___x_2819_ = v___x_2816_;
goto v_reusejp_2818_;
}
else
{
lean_object* v_reuseFailAlloc_2820_; 
v_reuseFailAlloc_2820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2820_, 0, v_a_2814_);
v___x_2819_ = v_reuseFailAlloc_2820_;
goto v_reusejp_2818_;
}
v_reusejp_2818_:
{
return v___x_2819_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_2776_);
lean_dec_ref(v_proof_2773_);
lean_dec_ref(v_e_x27_2772_);
lean_dec(v___y_2747_);
lean_dec_ref(v___y_2746_);
lean_dec(v___y_2745_);
lean_dec_ref(v___y_2744_);
lean_dec(v___y_2743_);
lean_dec_ref(v___y_2742_);
lean_dec_ref(v___y_2738_);
return v___x_2778_;
}
}
}
else
{
lean_dec_ref_known(v_a_2750_, 2);
lean_dec(v___y_2747_);
lean_dec_ref(v___y_2746_);
lean_dec(v___y_2745_);
lean_dec_ref(v___y_2744_);
lean_dec(v___y_2743_);
lean_dec_ref(v___y_2742_);
lean_dec(v___y_2741_);
lean_dec_ref(v___y_2740_);
lean_dec(v___y_2739_);
lean_dec_ref(v___y_2738_);
lean_dec_ref(v___f_2737_);
return v___x_2749_;
}
}
}
else
{
lean_dec(v___y_2747_);
lean_dec_ref(v___y_2746_);
lean_dec(v___y_2745_);
lean_dec_ref(v___y_2744_);
lean_dec(v___y_2743_);
lean_dec_ref(v___y_2742_);
lean_dec(v___y_2741_);
lean_dec_ref(v___y_2740_);
lean_dec(v___y_2739_);
lean_dec_ref(v___y_2738_);
lean_dec_ref(v___f_2737_);
return v___x_2749_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkSimpDefaultMethods___lam__2___boxed(lean_object* v___f_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_){
_start:
{
lean_object* v_res_2837_; 
v_res_2837_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkSimpDefaultMethods___lam__2(v___f_2825_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_);
return v_res_2837_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkSimpDefaultMethods(lean_object* v_extraThms_2841_, lean_object* v_a_2842_, lean_object* v_a_2843_, lean_object* v_a_2844_, lean_object* v_a_2845_, lean_object* v_a_2846_, lean_object* v_a_2847_, lean_object* v_a_2848_, lean_object* v_a_2849_){
_start:
{
lean_object* v___x_2851_; 
v___x_2851_ = l_Lean_Meta_Sym_Simp_getSymSimpTheorems___redArg(v_a_2849_);
if (lean_obj_tag(v___x_2851_) == 0)
{
lean_object* v_a_2852_; lean_object* v___f_2853_; lean_object* v___x_2854_; lean_object* v___f_2855_; lean_object* v___x_2856_; 
v_a_2852_ = lean_ctor_get(v___x_2851_, 0);
lean_inc(v_a_2852_);
lean_dec_ref_known(v___x_2851_, 1);
v___f_2853_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems___lam__0___boxed), 13, 1);
lean_closure_set(v___f_2853_, 0, v_a_2852_);
v___x_2854_ = lean_unsigned_to_nat(255u);
v___f_2855_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkSimpDefaultMethods___lam__1___boxed), 13, 2);
lean_closure_set(v___f_2855_, 0, v___x_2854_);
lean_closure_set(v___f_2855_, 1, v___f_2853_);
v___x_2856_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems(v___f_2855_, v_extraThms_2841_, v_a_2842_, v_a_2843_, v_a_2844_, v_a_2845_, v_a_2846_, v_a_2847_, v_a_2848_, v_a_2849_);
if (lean_obj_tag(v___x_2856_) == 0)
{
lean_object* v_a_2857_; lean_object* v___x_2859_; uint8_t v_isShared_2860_; uint8_t v_isSharedCheck_2866_; 
v_a_2857_ = lean_ctor_get(v___x_2856_, 0);
v_isSharedCheck_2866_ = !lean_is_exclusive(v___x_2856_);
if (v_isSharedCheck_2866_ == 0)
{
v___x_2859_ = v___x_2856_;
v_isShared_2860_ = v_isSharedCheck_2866_;
goto v_resetjp_2858_;
}
else
{
lean_inc(v_a_2857_);
lean_dec(v___x_2856_);
v___x_2859_ = lean_box(0);
v_isShared_2860_ = v_isSharedCheck_2866_;
goto v_resetjp_2858_;
}
v_resetjp_2858_:
{
lean_object* v___f_2861_; lean_object* v___x_2862_; lean_object* v___x_2864_; 
v___f_2861_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkSimpDefaultMethods___closed__1));
v___x_2862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2862_, 0, v___f_2861_);
lean_ctor_set(v___x_2862_, 1, v_a_2857_);
if (v_isShared_2860_ == 0)
{
lean_ctor_set(v___x_2859_, 0, v___x_2862_);
v___x_2864_ = v___x_2859_;
goto v_reusejp_2863_;
}
else
{
lean_object* v_reuseFailAlloc_2865_; 
v_reuseFailAlloc_2865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2865_, 0, v___x_2862_);
v___x_2864_ = v_reuseFailAlloc_2865_;
goto v_reusejp_2863_;
}
v_reusejp_2863_:
{
return v___x_2864_;
}
}
}
else
{
lean_object* v_a_2867_; lean_object* v___x_2869_; uint8_t v_isShared_2870_; uint8_t v_isSharedCheck_2874_; 
v_a_2867_ = lean_ctor_get(v___x_2856_, 0);
v_isSharedCheck_2874_ = !lean_is_exclusive(v___x_2856_);
if (v_isSharedCheck_2874_ == 0)
{
v___x_2869_ = v___x_2856_;
v_isShared_2870_ = v_isSharedCheck_2874_;
goto v_resetjp_2868_;
}
else
{
lean_inc(v_a_2867_);
lean_dec(v___x_2856_);
v___x_2869_ = lean_box(0);
v_isShared_2870_ = v_isSharedCheck_2874_;
goto v_resetjp_2868_;
}
v_resetjp_2868_:
{
lean_object* v___x_2872_; 
if (v_isShared_2870_ == 0)
{
v___x_2872_ = v___x_2869_;
goto v_reusejp_2871_;
}
else
{
lean_object* v_reuseFailAlloc_2873_; 
v_reuseFailAlloc_2873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2873_, 0, v_a_2867_);
v___x_2872_ = v_reuseFailAlloc_2873_;
goto v_reusejp_2871_;
}
v_reusejp_2871_:
{
return v___x_2872_;
}
}
}
}
else
{
lean_object* v_a_2875_; lean_object* v___x_2877_; uint8_t v_isShared_2878_; uint8_t v_isSharedCheck_2882_; 
v_a_2875_ = lean_ctor_get(v___x_2851_, 0);
v_isSharedCheck_2882_ = !lean_is_exclusive(v___x_2851_);
if (v_isSharedCheck_2882_ == 0)
{
v___x_2877_ = v___x_2851_;
v_isShared_2878_ = v_isSharedCheck_2882_;
goto v_resetjp_2876_;
}
else
{
lean_inc(v_a_2875_);
lean_dec(v___x_2851_);
v___x_2877_ = lean_box(0);
v_isShared_2878_ = v_isSharedCheck_2882_;
goto v_resetjp_2876_;
}
v_resetjp_2876_:
{
lean_object* v___x_2880_; 
if (v_isShared_2878_ == 0)
{
v___x_2880_ = v___x_2877_;
goto v_reusejp_2879_;
}
else
{
lean_object* v_reuseFailAlloc_2881_; 
v_reuseFailAlloc_2881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2881_, 0, v_a_2875_);
v___x_2880_ = v_reuseFailAlloc_2881_;
goto v_reusejp_2879_;
}
v_reusejp_2879_:
{
return v___x_2880_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkSimpDefaultMethods___boxed(lean_object* v_extraThms_2883_, lean_object* v_a_2884_, lean_object* v_a_2885_, lean_object* v_a_2886_, lean_object* v_a_2887_, lean_object* v_a_2888_, lean_object* v_a_2889_, lean_object* v_a_2890_, lean_object* v_a_2891_, lean_object* v_a_2892_){
_start:
{
lean_object* v_res_2893_; 
v_res_2893_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkSimpDefaultMethods(v_extraThms_2883_, v_a_2884_, v_a_2885_, v_a_2886_, v_a_2887_, v_a_2888_, v_a_2889_, v_a_2890_, v_a_2891_);
lean_dec(v_a_2891_);
lean_dec_ref(v_a_2890_);
lean_dec(v_a_2889_);
lean_dec_ref(v_a_2888_);
lean_dec(v_a_2887_);
lean_dec_ref(v_a_2886_);
lean_dec(v_a_2885_);
lean_dec_ref(v_a_2884_);
lean_dec_ref(v_extraThms_2883_);
return v_res_2893_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabSimpVariant___closed__1(void){
_start:
{
lean_object* v___x_2895_; lean_object* v___x_2896_; 
v___x_2895_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabSimpVariant___closed__0));
v___x_2896_ = l_Lean_stringToMessageData(v___x_2895_);
return v___x_2896_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabSimpVariant___closed__3(void){
_start:
{
lean_object* v___x_2898_; lean_object* v___x_2899_; 
v___x_2898_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabSimpVariant___closed__2));
v___x_2899_ = l_Lean_stringToMessageData(v___x_2898_);
return v___x_2899_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabSimpVariant(lean_object* v_variantName_2903_, lean_object* v_extraThms_2904_, lean_object* v_a_2905_, lean_object* v_a_2906_, lean_object* v_a_2907_, lean_object* v_a_2908_, lean_object* v_a_2909_, lean_object* v_a_2910_, lean_object* v_a_2911_, lean_object* v_a_2912_){
_start:
{
uint8_t v___x_2914_; 
v___x_2914_ = l_Lean_Name_isAnonymous(v_variantName_2903_);
if (v___x_2914_ == 0)
{
lean_object* v___x_2915_; lean_object* v_env_2916_; lean_object* v___x_2917_; 
v___x_2915_ = lean_st_ref_get(v_a_2912_);
v_env_2916_ = lean_ctor_get(v___x_2915_, 0);
lean_inc_ref(v_env_2916_);
lean_dec(v___x_2915_);
v___x_2917_ = l_Lean_Meta_Sym_Simp_getSymSimpVariant_x3f(v_env_2916_, v_variantName_2903_);
if (lean_obj_tag(v___x_2917_) == 1)
{
lean_object* v_val_2918_; lean_object* v_pre_x3f_2919_; lean_object* v_post_x3f_2920_; lean_object* v_config_2921_; lean_object* v___x_2922_; 
lean_dec(v_variantName_2903_);
v_val_2918_ = lean_ctor_get(v___x_2917_, 0);
lean_inc(v_val_2918_);
lean_dec_ref_known(v___x_2917_, 1);
v_pre_x3f_2919_ = lean_ctor_get(v_val_2918_, 0);
lean_inc(v_pre_x3f_2919_);
v_post_x3f_2920_ = lean_ctor_get(v_val_2918_, 1);
lean_inc(v_post_x3f_2920_);
v_config_2921_ = lean_ctor_get(v_val_2918_, 2);
lean_inc_ref(v_config_2921_);
lean_dec(v_val_2918_);
v___x_2922_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabOptSimproc(v_pre_x3f_2919_, v_a_2905_, v_a_2906_, v_a_2907_, v_a_2908_, v_a_2909_, v_a_2910_, v_a_2911_, v_a_2912_);
if (lean_obj_tag(v___x_2922_) == 0)
{
lean_object* v_a_2923_; lean_object* v___x_2924_; 
v_a_2923_ = lean_ctor_get(v___x_2922_, 0);
lean_inc(v_a_2923_);
lean_dec_ref_known(v___x_2922_, 1);
v___x_2924_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabOptSimproc(v_post_x3f_2920_, v_a_2905_, v_a_2906_, v_a_2907_, v_a_2908_, v_a_2909_, v_a_2910_, v_a_2911_, v_a_2912_);
if (lean_obj_tag(v___x_2924_) == 0)
{
lean_object* v_a_2925_; lean_object* v___x_2926_; 
v_a_2925_ = lean_ctor_get(v___x_2924_, 0);
lean_inc(v_a_2925_);
lean_dec_ref_known(v___x_2924_, 1);
v___x_2926_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_addExtraTheorems(v_a_2925_, v_extraThms_2904_, v_a_2905_, v_a_2906_, v_a_2907_, v_a_2908_, v_a_2909_, v_a_2910_, v_a_2911_, v_a_2912_);
if (lean_obj_tag(v___x_2926_) == 0)
{
lean_object* v_a_2927_; lean_object* v___x_2929_; uint8_t v_isShared_2930_; uint8_t v_isSharedCheck_2936_; 
v_a_2927_ = lean_ctor_get(v___x_2926_, 0);
v_isSharedCheck_2936_ = !lean_is_exclusive(v___x_2926_);
if (v_isSharedCheck_2936_ == 0)
{
v___x_2929_ = v___x_2926_;
v_isShared_2930_ = v_isSharedCheck_2936_;
goto v_resetjp_2928_;
}
else
{
lean_inc(v_a_2927_);
lean_dec(v___x_2926_);
v___x_2929_ = lean_box(0);
v_isShared_2930_ = v_isSharedCheck_2936_;
goto v_resetjp_2928_;
}
v_resetjp_2928_:
{
lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2934_; 
v___x_2931_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2931_, 0, v_a_2923_);
lean_ctor_set(v___x_2931_, 1, v_a_2927_);
v___x_2932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2932_, 0, v___x_2931_);
lean_ctor_set(v___x_2932_, 1, v_config_2921_);
if (v_isShared_2930_ == 0)
{
lean_ctor_set(v___x_2929_, 0, v___x_2932_);
v___x_2934_ = v___x_2929_;
goto v_reusejp_2933_;
}
else
{
lean_object* v_reuseFailAlloc_2935_; 
v_reuseFailAlloc_2935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2935_, 0, v___x_2932_);
v___x_2934_ = v_reuseFailAlloc_2935_;
goto v_reusejp_2933_;
}
v_reusejp_2933_:
{
return v___x_2934_;
}
}
}
else
{
lean_object* v_a_2937_; lean_object* v___x_2939_; uint8_t v_isShared_2940_; uint8_t v_isSharedCheck_2944_; 
lean_dec(v_a_2923_);
lean_dec_ref(v_config_2921_);
v_a_2937_ = lean_ctor_get(v___x_2926_, 0);
v_isSharedCheck_2944_ = !lean_is_exclusive(v___x_2926_);
if (v_isSharedCheck_2944_ == 0)
{
v___x_2939_ = v___x_2926_;
v_isShared_2940_ = v_isSharedCheck_2944_;
goto v_resetjp_2938_;
}
else
{
lean_inc(v_a_2937_);
lean_dec(v___x_2926_);
v___x_2939_ = lean_box(0);
v_isShared_2940_ = v_isSharedCheck_2944_;
goto v_resetjp_2938_;
}
v_resetjp_2938_:
{
lean_object* v___x_2942_; 
if (v_isShared_2940_ == 0)
{
v___x_2942_ = v___x_2939_;
goto v_reusejp_2941_;
}
else
{
lean_object* v_reuseFailAlloc_2943_; 
v_reuseFailAlloc_2943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2943_, 0, v_a_2937_);
v___x_2942_ = v_reuseFailAlloc_2943_;
goto v_reusejp_2941_;
}
v_reusejp_2941_:
{
return v___x_2942_;
}
}
}
}
else
{
lean_object* v_a_2945_; lean_object* v___x_2947_; uint8_t v_isShared_2948_; uint8_t v_isSharedCheck_2952_; 
lean_dec(v_a_2923_);
lean_dec_ref(v_config_2921_);
v_a_2945_ = lean_ctor_get(v___x_2924_, 0);
v_isSharedCheck_2952_ = !lean_is_exclusive(v___x_2924_);
if (v_isSharedCheck_2952_ == 0)
{
v___x_2947_ = v___x_2924_;
v_isShared_2948_ = v_isSharedCheck_2952_;
goto v_resetjp_2946_;
}
else
{
lean_inc(v_a_2945_);
lean_dec(v___x_2924_);
v___x_2947_ = lean_box(0);
v_isShared_2948_ = v_isSharedCheck_2952_;
goto v_resetjp_2946_;
}
v_resetjp_2946_:
{
lean_object* v___x_2950_; 
if (v_isShared_2948_ == 0)
{
v___x_2950_ = v___x_2947_;
goto v_reusejp_2949_;
}
else
{
lean_object* v_reuseFailAlloc_2951_; 
v_reuseFailAlloc_2951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2951_, 0, v_a_2945_);
v___x_2950_ = v_reuseFailAlloc_2951_;
goto v_reusejp_2949_;
}
v_reusejp_2949_:
{
return v___x_2950_;
}
}
}
}
else
{
lean_object* v_a_2953_; lean_object* v___x_2955_; uint8_t v_isShared_2956_; uint8_t v_isSharedCheck_2960_; 
lean_dec_ref(v_config_2921_);
lean_dec(v_post_x3f_2920_);
v_a_2953_ = lean_ctor_get(v___x_2922_, 0);
v_isSharedCheck_2960_ = !lean_is_exclusive(v___x_2922_);
if (v_isSharedCheck_2960_ == 0)
{
v___x_2955_ = v___x_2922_;
v_isShared_2956_ = v_isSharedCheck_2960_;
goto v_resetjp_2954_;
}
else
{
lean_inc(v_a_2953_);
lean_dec(v___x_2922_);
v___x_2955_ = lean_box(0);
v_isShared_2956_ = v_isSharedCheck_2960_;
goto v_resetjp_2954_;
}
v_resetjp_2954_:
{
lean_object* v___x_2958_; 
if (v_isShared_2956_ == 0)
{
v___x_2958_ = v___x_2955_;
goto v_reusejp_2957_;
}
else
{
lean_object* v_reuseFailAlloc_2959_; 
v_reuseFailAlloc_2959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2959_, 0, v_a_2953_);
v___x_2958_ = v_reuseFailAlloc_2959_;
goto v_reusejp_2957_;
}
v_reusejp_2957_:
{
return v___x_2958_;
}
}
}
}
else
{
lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; 
lean_dec(v___x_2917_);
v___x_2961_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabSimpVariant___closed__1, &l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabSimpVariant___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabSimpVariant___closed__1);
v___x_2962_ = l_Lean_MessageData_ofName(v_variantName_2903_);
v___x_2963_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2963_, 0, v___x_2961_);
lean_ctor_set(v___x_2963_, 1, v___x_2962_);
v___x_2964_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabSimpVariant___closed__3, &l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabSimpVariant___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabSimpVariant___closed__3);
v___x_2965_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2965_, 0, v___x_2963_);
lean_ctor_set(v___x_2965_, 1, v___x_2964_);
v___x_2966_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__2___redArg(v___x_2965_, v_a_2909_, v_a_2910_, v_a_2911_, v_a_2912_);
return v___x_2966_;
}
}
else
{
lean_object* v___x_2967_; 
lean_dec(v_variantName_2903_);
v___x_2967_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_mkSimpDefaultMethods(v_extraThms_2904_, v_a_2905_, v_a_2906_, v_a_2907_, v_a_2908_, v_a_2909_, v_a_2910_, v_a_2911_, v_a_2912_);
if (lean_obj_tag(v___x_2967_) == 0)
{
lean_object* v_a_2968_; lean_object* v___x_2970_; uint8_t v_isShared_2971_; uint8_t v_isSharedCheck_2977_; 
v_a_2968_ = lean_ctor_get(v___x_2967_, 0);
v_isSharedCheck_2977_ = !lean_is_exclusive(v___x_2967_);
if (v_isSharedCheck_2977_ == 0)
{
v___x_2970_ = v___x_2967_;
v_isShared_2971_ = v_isSharedCheck_2977_;
goto v_resetjp_2969_;
}
else
{
lean_inc(v_a_2968_);
lean_dec(v___x_2967_);
v___x_2970_ = lean_box(0);
v_isShared_2971_ = v_isSharedCheck_2977_;
goto v_resetjp_2969_;
}
v_resetjp_2969_:
{
lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2975_; 
v___x_2972_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabSimpVariant___closed__4));
v___x_2973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2973_, 0, v_a_2968_);
lean_ctor_set(v___x_2973_, 1, v___x_2972_);
if (v_isShared_2971_ == 0)
{
lean_ctor_set(v___x_2970_, 0, v___x_2973_);
v___x_2975_ = v___x_2970_;
goto v_reusejp_2974_;
}
else
{
lean_object* v_reuseFailAlloc_2976_; 
v_reuseFailAlloc_2976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2976_, 0, v___x_2973_);
v___x_2975_ = v_reuseFailAlloc_2976_;
goto v_reusejp_2974_;
}
v_reusejp_2974_:
{
return v___x_2975_;
}
}
}
else
{
lean_object* v_a_2978_; lean_object* v___x_2980_; uint8_t v_isShared_2981_; uint8_t v_isSharedCheck_2985_; 
v_a_2978_ = lean_ctor_get(v___x_2967_, 0);
v_isSharedCheck_2985_ = !lean_is_exclusive(v___x_2967_);
if (v_isSharedCheck_2985_ == 0)
{
v___x_2980_ = v___x_2967_;
v_isShared_2981_ = v_isSharedCheck_2985_;
goto v_resetjp_2979_;
}
else
{
lean_inc(v_a_2978_);
lean_dec(v___x_2967_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabSimpVariant___boxed(lean_object* v_variantName_2986_, lean_object* v_extraThms_2987_, lean_object* v_a_2988_, lean_object* v_a_2989_, lean_object* v_a_2990_, lean_object* v_a_2991_, lean_object* v_a_2992_, lean_object* v_a_2993_, lean_object* v_a_2994_, lean_object* v_a_2995_, lean_object* v_a_2996_){
_start:
{
lean_object* v_res_2997_; 
v_res_2997_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabSimpVariant(v_variantName_2986_, v_extraThms_2987_, v_a_2988_, v_a_2989_, v_a_2990_, v_a_2991_, v_a_2992_, v_a_2993_, v_a_2994_, v_a_2995_);
lean_dec(v_a_2995_);
lean_dec_ref(v_a_2994_);
lean_dec(v_a_2993_);
lean_dec_ref(v_a_2992_);
lean_dec(v_a_2991_);
lean_dec_ref(v_a_2990_);
lean_dec(v_a_2989_);
lean_dec_ref(v_a_2988_);
lean_dec_ref(v_extraThms_2987_);
return v_res_2997_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__0___redArg___lam__0(lean_object* v_x_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_){
_start:
{
lean_object* v___x_3009_; 
lean_inc(v___y_3003_);
lean_inc_ref(v___y_3002_);
lean_inc(v___y_3001_);
lean_inc_ref(v___y_3000_);
lean_inc(v___y_2999_);
v___x_3009_ = lean_apply_10(v_x_2998_, v___y_2999_, v___y_3000_, v___y_3001_, v___y_3002_, v___y_3003_, v___y_3004_, v___y_3005_, v___y_3006_, v___y_3007_, lean_box(0));
return v___x_3009_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__0___redArg___lam__0___boxed(lean_object* v_x_3010_, lean_object* v___y_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_){
_start:
{
lean_object* v_res_3021_; 
v_res_3021_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__0___redArg___lam__0(v_x_3010_, v___y_3011_, v___y_3012_, v___y_3013_, v___y_3014_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_, v___y_3019_);
lean_dec(v___y_3015_);
lean_dec_ref(v___y_3014_);
lean_dec(v___y_3013_);
lean_dec_ref(v___y_3012_);
lean_dec(v___y_3011_);
return v_res_3021_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__0___redArg(lean_object* v_mvarId_3022_, lean_object* v_x_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_, lean_object* v___y_3032_){
_start:
{
lean_object* v___f_3034_; lean_object* v___x_3035_; 
lean_inc(v___y_3028_);
lean_inc_ref(v___y_3027_);
lean_inc(v___y_3026_);
lean_inc_ref(v___y_3025_);
lean_inc(v___y_3024_);
v___f_3034_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__0___redArg___lam__0___boxed), 11, 6);
lean_closure_set(v___f_3034_, 0, v_x_3023_);
lean_closure_set(v___f_3034_, 1, v___y_3024_);
lean_closure_set(v___f_3034_, 2, v___y_3025_);
lean_closure_set(v___f_3034_, 3, v___y_3026_);
lean_closure_set(v___f_3034_, 4, v___y_3027_);
lean_closure_set(v___f_3034_, 5, v___y_3028_);
v___x_3035_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_3022_, v___f_3034_, v___y_3029_, v___y_3030_, v___y_3031_, v___y_3032_);
if (lean_obj_tag(v___x_3035_) == 0)
{
return v___x_3035_;
}
else
{
lean_object* v_a_3036_; lean_object* v___x_3038_; uint8_t v_isShared_3039_; uint8_t v_isSharedCheck_3043_; 
v_a_3036_ = lean_ctor_get(v___x_3035_, 0);
v_isSharedCheck_3043_ = !lean_is_exclusive(v___x_3035_);
if (v_isSharedCheck_3043_ == 0)
{
v___x_3038_ = v___x_3035_;
v_isShared_3039_ = v_isSharedCheck_3043_;
goto v_resetjp_3037_;
}
else
{
lean_inc(v_a_3036_);
lean_dec(v___x_3035_);
v___x_3038_ = lean_box(0);
v_isShared_3039_ = v_isSharedCheck_3043_;
goto v_resetjp_3037_;
}
v_resetjp_3037_:
{
lean_object* v___x_3041_; 
if (v_isShared_3039_ == 0)
{
v___x_3041_ = v___x_3038_;
goto v_reusejp_3040_;
}
else
{
lean_object* v_reuseFailAlloc_3042_; 
v_reuseFailAlloc_3042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3042_, 0, v_a_3036_);
v___x_3041_ = v_reuseFailAlloc_3042_;
goto v_reusejp_3040_;
}
v_reusejp_3040_:
{
return v___x_3041_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__0___redArg___boxed(lean_object* v_mvarId_3044_, lean_object* v_x_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_){
_start:
{
lean_object* v_res_3056_; 
v_res_3056_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__0___redArg(v_mvarId_3044_, v_x_3045_, v___y_3046_, v___y_3047_, v___y_3048_, v___y_3049_, v___y_3050_, v___y_3051_, v___y_3052_, v___y_3053_, v___y_3054_);
lean_dec(v___y_3054_);
lean_dec_ref(v___y_3053_);
lean_dec(v___y_3052_);
lean_dec_ref(v___y_3051_);
lean_dec(v___y_3050_);
lean_dec_ref(v___y_3049_);
lean_dec(v___y_3048_);
lean_dec_ref(v___y_3047_);
lean_dec(v___y_3046_);
return v_res_3056_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__0(lean_object* v_00_u03b1_3057_, lean_object* v_mvarId_3058_, lean_object* v_x_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_){
_start:
{
lean_object* v___x_3070_; 
v___x_3070_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__0___redArg(v_mvarId_3058_, v_x_3059_, v___y_3060_, v___y_3061_, v___y_3062_, v___y_3063_, v___y_3064_, v___y_3065_, v___y_3066_, v___y_3067_, v___y_3068_);
return v___x_3070_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__0___boxed(lean_object* v_00_u03b1_3071_, lean_object* v_mvarId_3072_, lean_object* v_x_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_){
_start:
{
lean_object* v_res_3084_; 
v_res_3084_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__0(v_00_u03b1_3071_, v_mvarId_3072_, v_x_3073_, v___y_3074_, v___y_3075_, v___y_3076_, v___y_3077_, v___y_3078_, v___y_3079_, v___y_3080_, v___y_3081_, v___y_3082_);
lean_dec(v___y_3082_);
lean_dec_ref(v___y_3081_);
lean_dec(v___y_3080_);
lean_dec_ref(v___y_3079_);
lean_dec(v___y_3078_);
lean_dec_ref(v___y_3077_);
lean_dec(v___y_3076_);
lean_dec_ref(v___y_3075_);
lean_dec(v___y_3074_);
return v_res_3084_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__0(lean_object* v_mvarId_3085_, lean_object* v_fst_3086_, lean_object* v_snd_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_){
_start:
{
lean_object* v___x_3099_; 
v___x_3099_ = l_Lean_MVarId_getType(v_mvarId_3085_, v___y_3094_, v___y_3095_, v___y_3096_, v___y_3097_);
if (lean_obj_tag(v___x_3099_) == 0)
{
lean_object* v_a_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; 
v_a_3100_ = lean_ctor_get(v___x_3099_, 0);
lean_inc(v_a_3100_);
lean_dec_ref_known(v___x_3099_, 1);
v___x_3101_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simp___boxed), 11, 1);
lean_closure_set(v___x_3101_, 0, v_a_3100_);
v___x_3102_ = l_Lean_Meta_Sym_Simp_SimpM_run___redArg(v___x_3101_, v_fst_3086_, v_snd_3087_, v___y_3088_, v___y_3092_, v___y_3093_, v___y_3094_, v___y_3095_, v___y_3096_, v___y_3097_);
return v___x_3102_;
}
else
{
lean_object* v_a_3103_; lean_object* v___x_3105_; uint8_t v_isShared_3106_; uint8_t v_isSharedCheck_3110_; 
lean_dec_ref(v___y_3088_);
lean_dec_ref(v_snd_3087_);
lean_dec_ref(v_fst_3086_);
v_a_3103_ = lean_ctor_get(v___x_3099_, 0);
v_isSharedCheck_3110_ = !lean_is_exclusive(v___x_3099_);
if (v_isSharedCheck_3110_ == 0)
{
v___x_3105_ = v___x_3099_;
v_isShared_3106_ = v_isSharedCheck_3110_;
goto v_resetjp_3104_;
}
else
{
lean_inc(v_a_3103_);
lean_dec(v___x_3099_);
v___x_3105_ = lean_box(0);
v_isShared_3106_ = v_isSharedCheck_3110_;
goto v_resetjp_3104_;
}
v_resetjp_3104_:
{
lean_object* v___x_3108_; 
if (v_isShared_3106_ == 0)
{
v___x_3108_ = v___x_3105_;
goto v_reusejp_3107_;
}
else
{
lean_object* v_reuseFailAlloc_3109_; 
v_reuseFailAlloc_3109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3109_, 0, v_a_3103_);
v___x_3108_ = v_reuseFailAlloc_3109_;
goto v_reusejp_3107_;
}
v_reusejp_3107_:
{
return v___x_3108_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__0___boxed(lean_object* v_mvarId_3111_, lean_object* v_fst_3112_, lean_object* v_snd_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_){
_start:
{
lean_object* v_res_3125_; 
v_res_3125_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__0(v_mvarId_3111_, v_fst_3112_, v_snd_3113_, v___y_3114_, v___y_3115_, v___y_3116_, v___y_3117_, v___y_3118_, v___y_3119_, v___y_3120_, v___y_3121_, v___y_3122_, v___y_3123_);
lean_dec(v___y_3123_);
lean_dec_ref(v___y_3122_);
lean_dec(v___y_3121_);
lean_dec_ref(v___y_3120_);
lean_dec(v___y_3119_);
lean_dec_ref(v___y_3118_);
lean_dec(v___y_3117_);
lean_dec_ref(v___y_3116_);
lean_dec(v___y_3115_);
return v_res_3125_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__1(lean_object* v_fst_3126_, lean_object* v_mvarId_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_){
_start:
{
lean_object* v___x_3138_; 
v___x_3138_ = l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult(v_fst_3126_, v_mvarId_3127_, v___y_3131_, v___y_3132_, v___y_3133_, v___y_3134_, v___y_3135_, v___y_3136_);
return v___x_3138_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__1___boxed(lean_object* v_fst_3139_, lean_object* v_mvarId_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_){
_start:
{
lean_object* v_res_3151_; 
v_res_3151_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__1(v_fst_3139_, v_mvarId_3140_, v___y_3141_, v___y_3142_, v___y_3143_, v___y_3144_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_, v___y_3149_);
lean_dec(v___y_3149_);
lean_dec_ref(v___y_3148_);
lean_dec(v___y_3147_);
lean_dec_ref(v___y_3146_);
lean_dec(v___y_3145_);
lean_dec_ref(v___y_3144_);
lean_dec(v___y_3143_);
lean_dec_ref(v___y_3142_);
lean_dec(v___y_3141_);
return v_res_3151_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__2_spec__5___redArg(lean_object* v_a_3152_, lean_object* v_x_3153_){
_start:
{
if (lean_obj_tag(v_x_3153_) == 0)
{
lean_object* v___x_3154_; 
v___x_3154_ = lean_box(0);
return v___x_3154_;
}
else
{
lean_object* v_key_3155_; lean_object* v_value_3156_; lean_object* v_tail_3157_; uint8_t v___x_3158_; 
v_key_3155_ = lean_ctor_get(v_x_3153_, 0);
v_value_3156_ = lean_ctor_get(v_x_3153_, 1);
v_tail_3157_ = lean_ctor_get(v_x_3153_, 2);
v___x_3158_ = l_Lean_Elab_Tactic_Grind_instBEqSimpCacheKey_beq(v_key_3155_, v_a_3152_);
if (v___x_3158_ == 0)
{
v_x_3153_ = v_tail_3157_;
goto _start;
}
else
{
lean_object* v___x_3160_; 
lean_inc(v_value_3156_);
v___x_3160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3160_, 0, v_value_3156_);
return v___x_3160_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__2_spec__5___redArg___boxed(lean_object* v_a_3161_, lean_object* v_x_3162_){
_start:
{
lean_object* v_res_3163_; 
v_res_3163_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__2_spec__5___redArg(v_a_3161_, v_x_3162_);
lean_dec(v_x_3162_);
lean_dec_ref(v_a_3161_);
return v_res_3163_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__2___redArg(lean_object* v_m_3164_, lean_object* v_a_3165_){
_start:
{
lean_object* v_buckets_3166_; lean_object* v___x_3167_; uint64_t v___x_3168_; uint64_t v___x_3169_; uint64_t v___x_3170_; uint64_t v_fold_3171_; uint64_t v___x_3172_; uint64_t v___x_3173_; uint64_t v___x_3174_; size_t v___x_3175_; size_t v___x_3176_; size_t v___x_3177_; size_t v___x_3178_; size_t v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; 
v_buckets_3166_ = lean_ctor_get(v_m_3164_, 1);
v___x_3167_ = lean_array_get_size(v_buckets_3166_);
v___x_3168_ = l_Lean_Elab_Tactic_Grind_instHashableSimpCacheKey_hash(v_a_3165_);
v___x_3169_ = 32ULL;
v___x_3170_ = lean_uint64_shift_right(v___x_3168_, v___x_3169_);
v_fold_3171_ = lean_uint64_xor(v___x_3168_, v___x_3170_);
v___x_3172_ = 16ULL;
v___x_3173_ = lean_uint64_shift_right(v_fold_3171_, v___x_3172_);
v___x_3174_ = lean_uint64_xor(v_fold_3171_, v___x_3173_);
v___x_3175_ = lean_uint64_to_usize(v___x_3174_);
v___x_3176_ = lean_usize_of_nat(v___x_3167_);
v___x_3177_ = ((size_t)1ULL);
v___x_3178_ = lean_usize_sub(v___x_3176_, v___x_3177_);
v___x_3179_ = lean_usize_land(v___x_3175_, v___x_3178_);
v___x_3180_ = lean_array_uget_borrowed(v_buckets_3166_, v___x_3179_);
v___x_3181_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__2_spec__5___redArg(v_a_3165_, v___x_3180_);
return v___x_3181_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__2___redArg___boxed(lean_object* v_m_3182_, lean_object* v_a_3183_){
_start:
{
lean_object* v_res_3184_; 
v_res_3184_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__2___redArg(v_m_3182_, v_a_3183_);
lean_dec_ref(v_a_3183_);
lean_dec_ref(v_m_3182_);
return v_res_3184_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__4(uint8_t v___x_3185_, uint8_t v___x_3186_, lean_object* v_as_3187_, size_t v_i_3188_, size_t v_stop_3189_, lean_object* v_b_3190_){
_start:
{
lean_object* v___y_3192_; uint8_t v___x_3196_; 
v___x_3196_ = lean_usize_dec_eq(v_i_3188_, v_stop_3189_);
if (v___x_3196_ == 0)
{
lean_object* v_fst_3197_; uint8_t v___x_3198_; 
v_fst_3197_ = lean_ctor_get(v_b_3190_, 0);
v___x_3198_ = lean_unbox(v_fst_3197_);
if (v___x_3198_ == 0)
{
lean_object* v_snd_3199_; lean_object* v___x_3201_; uint8_t v_isShared_3202_; uint8_t v_isSharedCheck_3207_; 
v_snd_3199_ = lean_ctor_get(v_b_3190_, 1);
v_isSharedCheck_3207_ = !lean_is_exclusive(v_b_3190_);
if (v_isSharedCheck_3207_ == 0)
{
lean_object* v_unused_3208_; 
v_unused_3208_ = lean_ctor_get(v_b_3190_, 0);
lean_dec(v_unused_3208_);
v___x_3201_ = v_b_3190_;
v_isShared_3202_ = v_isSharedCheck_3207_;
goto v_resetjp_3200_;
}
else
{
lean_inc(v_snd_3199_);
lean_dec(v_b_3190_);
v___x_3201_ = lean_box(0);
v_isShared_3202_ = v_isSharedCheck_3207_;
goto v_resetjp_3200_;
}
v_resetjp_3200_:
{
lean_object* v___x_3203_; lean_object* v___x_3205_; 
v___x_3203_ = lean_box(v___x_3185_);
if (v_isShared_3202_ == 0)
{
lean_ctor_set(v___x_3201_, 0, v___x_3203_);
v___x_3205_ = v___x_3201_;
goto v_reusejp_3204_;
}
else
{
lean_object* v_reuseFailAlloc_3206_; 
v_reuseFailAlloc_3206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3206_, 0, v___x_3203_);
lean_ctor_set(v_reuseFailAlloc_3206_, 1, v_snd_3199_);
v___x_3205_ = v_reuseFailAlloc_3206_;
goto v_reusejp_3204_;
}
v_reusejp_3204_:
{
v___y_3192_ = v___x_3205_;
goto v___jp_3191_;
}
}
}
else
{
lean_object* v_snd_3209_; lean_object* v___x_3211_; uint8_t v_isShared_3212_; uint8_t v_isSharedCheck_3219_; 
v_snd_3209_ = lean_ctor_get(v_b_3190_, 1);
v_isSharedCheck_3219_ = !lean_is_exclusive(v_b_3190_);
if (v_isSharedCheck_3219_ == 0)
{
lean_object* v_unused_3220_; 
v_unused_3220_ = lean_ctor_get(v_b_3190_, 0);
lean_dec(v_unused_3220_);
v___x_3211_ = v_b_3190_;
v_isShared_3212_ = v_isSharedCheck_3219_;
goto v_resetjp_3210_;
}
else
{
lean_inc(v_snd_3209_);
lean_dec(v_b_3190_);
v___x_3211_ = lean_box(0);
v_isShared_3212_ = v_isSharedCheck_3219_;
goto v_resetjp_3210_;
}
v_resetjp_3210_:
{
lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3217_; 
v___x_3213_ = lean_array_uget_borrowed(v_as_3187_, v_i_3188_);
lean_inc(v___x_3213_);
v___x_3214_ = lean_array_push(v_snd_3209_, v___x_3213_);
v___x_3215_ = lean_box(v___x_3186_);
if (v_isShared_3212_ == 0)
{
lean_ctor_set(v___x_3211_, 1, v___x_3214_);
lean_ctor_set(v___x_3211_, 0, v___x_3215_);
v___x_3217_ = v___x_3211_;
goto v_reusejp_3216_;
}
else
{
lean_object* v_reuseFailAlloc_3218_; 
v_reuseFailAlloc_3218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3218_, 0, v___x_3215_);
lean_ctor_set(v_reuseFailAlloc_3218_, 1, v___x_3214_);
v___x_3217_ = v_reuseFailAlloc_3218_;
goto v_reusejp_3216_;
}
v_reusejp_3216_:
{
v___y_3192_ = v___x_3217_;
goto v___jp_3191_;
}
}
}
}
else
{
return v_b_3190_;
}
v___jp_3191_:
{
size_t v___x_3193_; size_t v___x_3194_; 
v___x_3193_ = ((size_t)1ULL);
v___x_3194_ = lean_usize_add(v_i_3188_, v___x_3193_);
v_i_3188_ = v___x_3194_;
v_b_3190_ = v___y_3192_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__4___boxed(lean_object* v___x_3221_, lean_object* v___x_3222_, lean_object* v_as_3223_, lean_object* v_i_3224_, lean_object* v_stop_3225_, lean_object* v_b_3226_){
_start:
{
uint8_t v___x_9506__boxed_3227_; uint8_t v___x_9507__boxed_3228_; size_t v_i_boxed_3229_; size_t v_stop_boxed_3230_; lean_object* v_res_3231_; 
v___x_9506__boxed_3227_ = lean_unbox(v___x_3221_);
v___x_9507__boxed_3228_ = lean_unbox(v___x_3222_);
v_i_boxed_3229_ = lean_unbox_usize(v_i_3224_);
lean_dec(v_i_3224_);
v_stop_boxed_3230_ = lean_unbox_usize(v_stop_3225_);
lean_dec(v_stop_3225_);
v_res_3231_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__4(v___x_9506__boxed_3227_, v___x_9507__boxed_3228_, v_as_3223_, v_i_boxed_3229_, v_stop_boxed_3230_, v_b_3226_);
lean_dec_ref(v_as_3223_);
return v_res_3231_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__3___redArg(lean_object* v_a_3232_, lean_object* v_b_3233_, lean_object* v_x_3234_){
_start:
{
if (lean_obj_tag(v_x_3234_) == 0)
{
lean_dec(v_b_3233_);
lean_dec_ref(v_a_3232_);
return v_x_3234_;
}
else
{
lean_object* v_key_3235_; lean_object* v_value_3236_; lean_object* v_tail_3237_; lean_object* v___x_3239_; uint8_t v_isShared_3240_; uint8_t v_isSharedCheck_3249_; 
v_key_3235_ = lean_ctor_get(v_x_3234_, 0);
v_value_3236_ = lean_ctor_get(v_x_3234_, 1);
v_tail_3237_ = lean_ctor_get(v_x_3234_, 2);
v_isSharedCheck_3249_ = !lean_is_exclusive(v_x_3234_);
if (v_isSharedCheck_3249_ == 0)
{
v___x_3239_ = v_x_3234_;
v_isShared_3240_ = v_isSharedCheck_3249_;
goto v_resetjp_3238_;
}
else
{
lean_inc(v_tail_3237_);
lean_inc(v_value_3236_);
lean_inc(v_key_3235_);
lean_dec(v_x_3234_);
v___x_3239_ = lean_box(0);
v_isShared_3240_ = v_isSharedCheck_3249_;
goto v_resetjp_3238_;
}
v_resetjp_3238_:
{
uint8_t v___x_3241_; 
v___x_3241_ = l_Lean_Elab_Tactic_Grind_instBEqSimpCacheKey_beq(v_key_3235_, v_a_3232_);
if (v___x_3241_ == 0)
{
lean_object* v___x_3242_; lean_object* v___x_3244_; 
v___x_3242_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__3___redArg(v_a_3232_, v_b_3233_, v_tail_3237_);
if (v_isShared_3240_ == 0)
{
lean_ctor_set(v___x_3239_, 2, v___x_3242_);
v___x_3244_ = v___x_3239_;
goto v_reusejp_3243_;
}
else
{
lean_object* v_reuseFailAlloc_3245_; 
v_reuseFailAlloc_3245_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3245_, 0, v_key_3235_);
lean_ctor_set(v_reuseFailAlloc_3245_, 1, v_value_3236_);
lean_ctor_set(v_reuseFailAlloc_3245_, 2, v___x_3242_);
v___x_3244_ = v_reuseFailAlloc_3245_;
goto v_reusejp_3243_;
}
v_reusejp_3243_:
{
return v___x_3244_;
}
}
else
{
lean_object* v___x_3247_; 
lean_dec(v_value_3236_);
lean_dec(v_key_3235_);
if (v_isShared_3240_ == 0)
{
lean_ctor_set(v___x_3239_, 1, v_b_3233_);
lean_ctor_set(v___x_3239_, 0, v_a_3232_);
v___x_3247_ = v___x_3239_;
goto v_reusejp_3246_;
}
else
{
lean_object* v_reuseFailAlloc_3248_; 
v_reuseFailAlloc_3248_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3248_, 0, v_a_3232_);
lean_ctor_set(v_reuseFailAlloc_3248_, 1, v_b_3233_);
lean_ctor_set(v_reuseFailAlloc_3248_, 2, v_tail_3237_);
v___x_3247_ = v_reuseFailAlloc_3248_;
goto v_reusejp_3246_;
}
v_reusejp_3246_:
{
return v___x_3247_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__2_spec__3_spec__7___redArg(lean_object* v_x_3250_, lean_object* v_x_3251_){
_start:
{
if (lean_obj_tag(v_x_3251_) == 0)
{
return v_x_3250_;
}
else
{
lean_object* v_key_3252_; lean_object* v_value_3253_; lean_object* v_tail_3254_; lean_object* v___x_3256_; uint8_t v_isShared_3257_; uint8_t v_isSharedCheck_3277_; 
v_key_3252_ = lean_ctor_get(v_x_3251_, 0);
v_value_3253_ = lean_ctor_get(v_x_3251_, 1);
v_tail_3254_ = lean_ctor_get(v_x_3251_, 2);
v_isSharedCheck_3277_ = !lean_is_exclusive(v_x_3251_);
if (v_isSharedCheck_3277_ == 0)
{
v___x_3256_ = v_x_3251_;
v_isShared_3257_ = v_isSharedCheck_3277_;
goto v_resetjp_3255_;
}
else
{
lean_inc(v_tail_3254_);
lean_inc(v_value_3253_);
lean_inc(v_key_3252_);
lean_dec(v_x_3251_);
v___x_3256_ = lean_box(0);
v_isShared_3257_ = v_isSharedCheck_3277_;
goto v_resetjp_3255_;
}
v_resetjp_3255_:
{
lean_object* v___x_3258_; uint64_t v___x_3259_; uint64_t v___x_3260_; uint64_t v___x_3261_; uint64_t v_fold_3262_; uint64_t v___x_3263_; uint64_t v___x_3264_; uint64_t v___x_3265_; size_t v___x_3266_; size_t v___x_3267_; size_t v___x_3268_; size_t v___x_3269_; size_t v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3273_; 
v___x_3258_ = lean_array_get_size(v_x_3250_);
v___x_3259_ = l_Lean_Elab_Tactic_Grind_instHashableSimpCacheKey_hash(v_key_3252_);
v___x_3260_ = 32ULL;
v___x_3261_ = lean_uint64_shift_right(v___x_3259_, v___x_3260_);
v_fold_3262_ = lean_uint64_xor(v___x_3259_, v___x_3261_);
v___x_3263_ = 16ULL;
v___x_3264_ = lean_uint64_shift_right(v_fold_3262_, v___x_3263_);
v___x_3265_ = lean_uint64_xor(v_fold_3262_, v___x_3264_);
v___x_3266_ = lean_uint64_to_usize(v___x_3265_);
v___x_3267_ = lean_usize_of_nat(v___x_3258_);
v___x_3268_ = ((size_t)1ULL);
v___x_3269_ = lean_usize_sub(v___x_3267_, v___x_3268_);
v___x_3270_ = lean_usize_land(v___x_3266_, v___x_3269_);
v___x_3271_ = lean_array_uget_borrowed(v_x_3250_, v___x_3270_);
lean_inc(v___x_3271_);
if (v_isShared_3257_ == 0)
{
lean_ctor_set(v___x_3256_, 2, v___x_3271_);
v___x_3273_ = v___x_3256_;
goto v_reusejp_3272_;
}
else
{
lean_object* v_reuseFailAlloc_3276_; 
v_reuseFailAlloc_3276_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3276_, 0, v_key_3252_);
lean_ctor_set(v_reuseFailAlloc_3276_, 1, v_value_3253_);
lean_ctor_set(v_reuseFailAlloc_3276_, 2, v___x_3271_);
v___x_3273_ = v_reuseFailAlloc_3276_;
goto v_reusejp_3272_;
}
v_reusejp_3272_:
{
lean_object* v___x_3274_; 
v___x_3274_ = lean_array_uset(v_x_3250_, v___x_3270_, v___x_3273_);
v_x_3250_ = v___x_3274_;
v_x_3251_ = v_tail_3254_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__2_spec__3___redArg(lean_object* v_i_3278_, lean_object* v_source_3279_, lean_object* v_target_3280_){
_start:
{
lean_object* v___x_3281_; uint8_t v___x_3282_; 
v___x_3281_ = lean_array_get_size(v_source_3279_);
v___x_3282_ = lean_nat_dec_lt(v_i_3278_, v___x_3281_);
if (v___x_3282_ == 0)
{
lean_dec_ref(v_source_3279_);
lean_dec(v_i_3278_);
return v_target_3280_;
}
else
{
lean_object* v_es_3283_; lean_object* v___x_3284_; lean_object* v_source_3285_; lean_object* v_target_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; 
v_es_3283_ = lean_array_fget(v_source_3279_, v_i_3278_);
v___x_3284_ = lean_box(0);
v_source_3285_ = lean_array_fset(v_source_3279_, v_i_3278_, v___x_3284_);
v_target_3286_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__2_spec__3_spec__7___redArg(v_target_3280_, v_es_3283_);
v___x_3287_ = lean_unsigned_to_nat(1u);
v___x_3288_ = lean_nat_add(v_i_3278_, v___x_3287_);
lean_dec(v_i_3278_);
v_i_3278_ = v___x_3288_;
v_source_3279_ = v_source_3285_;
v_target_3280_ = v_target_3286_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__2___redArg(lean_object* v_data_3290_){
_start:
{
lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v_nbuckets_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; 
v___x_3291_ = lean_array_get_size(v_data_3290_);
v___x_3292_ = lean_unsigned_to_nat(2u);
v_nbuckets_3293_ = lean_nat_mul(v___x_3291_, v___x_3292_);
v___x_3294_ = lean_unsigned_to_nat(0u);
v___x_3295_ = lean_box(0);
v___x_3296_ = lean_mk_array(v_nbuckets_3293_, v___x_3295_);
v___x_3297_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__2_spec__3___redArg(v___x_3294_, v_data_3290_, v___x_3296_);
return v___x_3297_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__1___redArg(lean_object* v_a_3298_, lean_object* v_x_3299_){
_start:
{
if (lean_obj_tag(v_x_3299_) == 0)
{
uint8_t v___x_3300_; 
v___x_3300_ = 0;
return v___x_3300_;
}
else
{
lean_object* v_key_3301_; lean_object* v_tail_3302_; uint8_t v___x_3303_; 
v_key_3301_ = lean_ctor_get(v_x_3299_, 0);
v_tail_3302_ = lean_ctor_get(v_x_3299_, 2);
v___x_3303_ = l_Lean_Elab_Tactic_Grind_instBEqSimpCacheKey_beq(v_key_3301_, v_a_3298_);
if (v___x_3303_ == 0)
{
v_x_3299_ = v_tail_3302_;
goto _start;
}
else
{
return v___x_3303_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__1___redArg___boxed(lean_object* v_a_3305_, lean_object* v_x_3306_){
_start:
{
uint8_t v_res_3307_; lean_object* v_r_3308_; 
v_res_3307_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__1___redArg(v_a_3305_, v_x_3306_);
lean_dec(v_x_3306_);
lean_dec_ref(v_a_3305_);
v_r_3308_ = lean_box(v_res_3307_);
return v_r_3308_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1___redArg(lean_object* v_m_3309_, lean_object* v_a_3310_, lean_object* v_b_3311_){
_start:
{
lean_object* v_size_3312_; lean_object* v_buckets_3313_; lean_object* v___x_3315_; uint8_t v_isShared_3316_; uint8_t v_isSharedCheck_3356_; 
v_size_3312_ = lean_ctor_get(v_m_3309_, 0);
v_buckets_3313_ = lean_ctor_get(v_m_3309_, 1);
v_isSharedCheck_3356_ = !lean_is_exclusive(v_m_3309_);
if (v_isSharedCheck_3356_ == 0)
{
v___x_3315_ = v_m_3309_;
v_isShared_3316_ = v_isSharedCheck_3356_;
goto v_resetjp_3314_;
}
else
{
lean_inc(v_buckets_3313_);
lean_inc(v_size_3312_);
lean_dec(v_m_3309_);
v___x_3315_ = lean_box(0);
v_isShared_3316_ = v_isSharedCheck_3356_;
goto v_resetjp_3314_;
}
v_resetjp_3314_:
{
lean_object* v___x_3317_; uint64_t v___x_3318_; uint64_t v___x_3319_; uint64_t v___x_3320_; uint64_t v_fold_3321_; uint64_t v___x_3322_; uint64_t v___x_3323_; uint64_t v___x_3324_; size_t v___x_3325_; size_t v___x_3326_; size_t v___x_3327_; size_t v___x_3328_; size_t v___x_3329_; lean_object* v_bkt_3330_; uint8_t v___x_3331_; 
v___x_3317_ = lean_array_get_size(v_buckets_3313_);
v___x_3318_ = l_Lean_Elab_Tactic_Grind_instHashableSimpCacheKey_hash(v_a_3310_);
v___x_3319_ = 32ULL;
v___x_3320_ = lean_uint64_shift_right(v___x_3318_, v___x_3319_);
v_fold_3321_ = lean_uint64_xor(v___x_3318_, v___x_3320_);
v___x_3322_ = 16ULL;
v___x_3323_ = lean_uint64_shift_right(v_fold_3321_, v___x_3322_);
v___x_3324_ = lean_uint64_xor(v_fold_3321_, v___x_3323_);
v___x_3325_ = lean_uint64_to_usize(v___x_3324_);
v___x_3326_ = lean_usize_of_nat(v___x_3317_);
v___x_3327_ = ((size_t)1ULL);
v___x_3328_ = lean_usize_sub(v___x_3326_, v___x_3327_);
v___x_3329_ = lean_usize_land(v___x_3325_, v___x_3328_);
v_bkt_3330_ = lean_array_uget_borrowed(v_buckets_3313_, v___x_3329_);
v___x_3331_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__1___redArg(v_a_3310_, v_bkt_3330_);
if (v___x_3331_ == 0)
{
lean_object* v___x_3332_; lean_object* v_size_x27_3333_; lean_object* v___x_3334_; lean_object* v_buckets_x27_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; uint8_t v___x_3341_; 
v___x_3332_ = lean_unsigned_to_nat(1u);
v_size_x27_3333_ = lean_nat_add(v_size_3312_, v___x_3332_);
lean_dec(v_size_3312_);
lean_inc(v_bkt_3330_);
v___x_3334_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3334_, 0, v_a_3310_);
lean_ctor_set(v___x_3334_, 1, v_b_3311_);
lean_ctor_set(v___x_3334_, 2, v_bkt_3330_);
v_buckets_x27_3335_ = lean_array_uset(v_buckets_3313_, v___x_3329_, v___x_3334_);
v___x_3336_ = lean_unsigned_to_nat(4u);
v___x_3337_ = lean_nat_mul(v_size_x27_3333_, v___x_3336_);
v___x_3338_ = lean_unsigned_to_nat(3u);
v___x_3339_ = lean_nat_div(v___x_3337_, v___x_3338_);
lean_dec(v___x_3337_);
v___x_3340_ = lean_array_get_size(v_buckets_x27_3335_);
v___x_3341_ = lean_nat_dec_le(v___x_3339_, v___x_3340_);
lean_dec(v___x_3339_);
if (v___x_3341_ == 0)
{
lean_object* v_val_3342_; lean_object* v___x_3344_; 
v_val_3342_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__2___redArg(v_buckets_x27_3335_);
if (v_isShared_3316_ == 0)
{
lean_ctor_set(v___x_3315_, 1, v_val_3342_);
lean_ctor_set(v___x_3315_, 0, v_size_x27_3333_);
v___x_3344_ = v___x_3315_;
goto v_reusejp_3343_;
}
else
{
lean_object* v_reuseFailAlloc_3345_; 
v_reuseFailAlloc_3345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3345_, 0, v_size_x27_3333_);
lean_ctor_set(v_reuseFailAlloc_3345_, 1, v_val_3342_);
v___x_3344_ = v_reuseFailAlloc_3345_;
goto v_reusejp_3343_;
}
v_reusejp_3343_:
{
return v___x_3344_;
}
}
else
{
lean_object* v___x_3347_; 
if (v_isShared_3316_ == 0)
{
lean_ctor_set(v___x_3315_, 1, v_buckets_x27_3335_);
lean_ctor_set(v___x_3315_, 0, v_size_x27_3333_);
v___x_3347_ = v___x_3315_;
goto v_reusejp_3346_;
}
else
{
lean_object* v_reuseFailAlloc_3348_; 
v_reuseFailAlloc_3348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3348_, 0, v_size_x27_3333_);
lean_ctor_set(v_reuseFailAlloc_3348_, 1, v_buckets_x27_3335_);
v___x_3347_ = v_reuseFailAlloc_3348_;
goto v_reusejp_3346_;
}
v_reusejp_3346_:
{
return v___x_3347_;
}
}
}
else
{
lean_object* v___x_3349_; lean_object* v_buckets_x27_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3354_; 
lean_inc(v_bkt_3330_);
v___x_3349_ = lean_box(0);
v_buckets_x27_3350_ = lean_array_uset(v_buckets_3313_, v___x_3329_, v___x_3349_);
v___x_3351_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__3___redArg(v_a_3310_, v_b_3311_, v_bkt_3330_);
v___x_3352_ = lean_array_uset(v_buckets_x27_3350_, v___x_3329_, v___x_3351_);
if (v_isShared_3316_ == 0)
{
lean_ctor_set(v___x_3315_, 1, v___x_3352_);
v___x_3354_ = v___x_3315_;
goto v_reusejp_3353_;
}
else
{
lean_object* v_reuseFailAlloc_3355_; 
v_reuseFailAlloc_3355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3355_, 0, v_size_3312_);
lean_ctor_set(v_reuseFailAlloc_3355_, 1, v___x_3352_);
v___x_3354_ = v_reuseFailAlloc_3355_;
goto v_reusejp_3353_;
}
v_reusejp_3353_:
{
return v___x_3354_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__3(size_t v_sz_3357_, size_t v_i_3358_, lean_object* v_bs_3359_){
_start:
{
uint8_t v___x_3360_; 
v___x_3360_ = lean_usize_dec_lt(v_i_3358_, v_sz_3357_);
if (v___x_3360_ == 0)
{
lean_object* v___x_3361_; 
v___x_3361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3361_, 0, v_bs_3359_);
return v___x_3361_;
}
else
{
lean_object* v_v_3362_; lean_object* v___x_3363_; lean_object* v_bs_x27_3364_; size_t v___x_3365_; size_t v___x_3366_; lean_object* v___x_3367_; 
v_v_3362_ = lean_array_uget(v_bs_3359_, v_i_3358_);
v___x_3363_ = lean_unsigned_to_nat(0u);
v_bs_x27_3364_ = lean_array_uset(v_bs_3359_, v_i_3358_, v___x_3363_);
v___x_3365_ = ((size_t)1ULL);
v___x_3366_ = lean_usize_add(v_i_3358_, v___x_3365_);
v___x_3367_ = lean_array_uset(v_bs_x27_3364_, v_i_3358_, v_v_3362_);
v_i_3358_ = v___x_3366_;
v_bs_3359_ = v___x_3367_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__3___boxed(lean_object* v_sz_3369_, lean_object* v_i_3370_, lean_object* v_bs_3371_){
_start:
{
size_t v_sz_boxed_3372_; size_t v_i_boxed_3373_; lean_object* v_res_3374_; 
v_sz_boxed_3372_ = lean_unbox_usize(v_sz_3369_);
lean_dec(v_sz_3369_);
v_i_boxed_3373_ = lean_unbox_usize(v_i_3370_);
lean_dec(v_i_3370_);
v_res_3374_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__3(v_sz_boxed_3372_, v_i_boxed_3373_, v_bs_3371_);
return v_res_3374_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__1(void){
_start:
{
lean_object* v___x_3376_; lean_object* v___x_3377_; 
v___x_3376_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__0));
v___x_3377_ = l_Lean_stringToMessageData(v___x_3376_);
return v___x_3377_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__4(void){
_start:
{
lean_object* v___x_3385_; 
v___x_3385_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3385_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__5(void){
_start:
{
lean_object* v___x_3386_; lean_object* v___x_3387_; 
v___x_3386_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__4, &l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__4_once, _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__4);
v___x_3387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3387_, 0, v___x_3386_);
return v___x_3387_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__6(void){
_start:
{
lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; 
v___x_3388_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__5, &l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__5);
v___x_3389_ = lean_unsigned_to_nat(0u);
v___x_3390_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3390_, 0, v___x_3389_);
lean_ctor_set(v___x_3390_, 1, v___x_3388_);
lean_ctor_set(v___x_3390_, 2, v___x_3388_);
lean_ctor_set(v___x_3390_, 3, v___x_3388_);
return v___x_3390_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2(lean_object* v_stx_3393_, lean_object* v___y_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_){
_start:
{
lean_object* v___y_3404_; lean_object* v___y_3405_; lean_object* v___y_3406_; lean_object* v___y_3407_; lean_object* v___y_3408_; lean_object* v___y_3409_; lean_object* v___y_3410_; lean_object* v___y_3411_; lean_object* v___y_3412_; lean_object* v___y_3413_; lean_object* v___y_3414_; lean_object* v___y_3415_; lean_object* v___x_3511_; 
v___x_3511_ = l_Lean_Elab_Tactic_Grind_ensureSym___redArg(v___y_3394_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_);
if (lean_obj_tag(v___x_3511_) == 0)
{
lean_object* v___x_3513_; uint8_t v_isShared_3514_; uint8_t v_isSharedCheck_3627_; 
v_isSharedCheck_3627_ = !lean_is_exclusive(v___x_3511_);
if (v_isSharedCheck_3627_ == 0)
{
lean_object* v_unused_3628_; 
v_unused_3628_ = lean_ctor_get(v___x_3511_, 0);
lean_dec(v_unused_3628_);
v___x_3513_ = v___x_3511_;
v_isShared_3514_ = v_isSharedCheck_3627_;
goto v_resetjp_3512_;
}
else
{
lean_dec(v___x_3511_);
v___x_3513_ = lean_box(0);
v_isShared_3514_ = v_isSharedCheck_3627_;
goto v_resetjp_3512_;
}
v_resetjp_3512_:
{
lean_object* v___x_3515_; uint8_t v___x_3516_; 
v___x_3515_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__3));
lean_inc(v_stx_3393_);
v___x_3516_ = l_Lean_Syntax_isOfKind(v_stx_3393_, v___x_3515_);
if (v___x_3516_ == 0)
{
lean_object* v___x_3517_; 
lean_del_object(v___x_3513_);
lean_dec(v_stx_3393_);
v___x_3517_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro_spec__0___redArg();
return v___x_3517_;
}
else
{
lean_object* v___x_3518_; lean_object* v___y_3520_; lean_object* v___y_3521_; lean_object* v___y_3522_; lean_object* v___y_3523_; lean_object* v___y_3524_; lean_object* v___y_3525_; lean_object* v___y_3526_; lean_object* v___y_3527_; lean_object* v___y_3528_; lean_object* v___y_3529_; lean_object* v___y_3556_; lean_object* v_extraIds_3557_; lean_object* v___y_3558_; lean_object* v___y_3559_; lean_object* v___y_3560_; lean_object* v___y_3561_; lean_object* v___y_3562_; lean_object* v___y_3563_; lean_object* v___y_3564_; lean_object* v___y_3565_; lean_object* v___y_3570_; lean_object* v___y_3571_; lean_object* v___y_3572_; lean_object* v___y_3573_; lean_object* v___y_3574_; lean_object* v___y_3575_; lean_object* v___y_3576_; lean_object* v___y_3577_; lean_object* v___y_3578_; lean_object* v___y_3579_; lean_object* v___x_3584_; lean_object* v_variantId_x3f_3586_; lean_object* v___y_3587_; lean_object* v___y_3588_; lean_object* v___y_3589_; lean_object* v___y_3590_; lean_object* v___y_3591_; lean_object* v___y_3592_; lean_object* v___y_3593_; lean_object* v___y_3594_; lean_object* v___x_3618_; uint8_t v___x_3619_; 
v___x_3518_ = lean_unsigned_to_nat(0u);
v___x_3584_ = lean_unsigned_to_nat(1u);
v___x_3618_ = l_Lean_Syntax_getArg(v_stx_3393_, v___x_3584_);
v___x_3619_ = l_Lean_Syntax_isNone(v___x_3618_);
if (v___x_3619_ == 0)
{
uint8_t v___x_3620_; 
lean_inc(v___x_3618_);
v___x_3620_ = l_Lean_Syntax_matchesNull(v___x_3618_, v___x_3584_);
if (v___x_3620_ == 0)
{
lean_object* v___x_3621_; 
lean_dec(v___x_3618_);
lean_del_object(v___x_3513_);
lean_dec(v_stx_3393_);
v___x_3621_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro_spec__0___redArg();
return v___x_3621_;
}
else
{
lean_object* v___x_3622_; lean_object* v___x_3624_; 
v___x_3622_ = l_Lean_Syntax_getArg(v___x_3618_, v___x_3518_);
lean_dec(v___x_3618_);
if (v_isShared_3514_ == 0)
{
lean_ctor_set_tag(v___x_3513_, 1);
lean_ctor_set(v___x_3513_, 0, v___x_3622_);
v___x_3624_ = v___x_3513_;
goto v_reusejp_3623_;
}
else
{
lean_object* v_reuseFailAlloc_3625_; 
v_reuseFailAlloc_3625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3625_, 0, v___x_3622_);
v___x_3624_ = v_reuseFailAlloc_3625_;
goto v_reusejp_3623_;
}
v_reusejp_3623_:
{
v_variantId_x3f_3586_ = v___x_3624_;
v___y_3587_ = v___y_3394_;
v___y_3588_ = v___y_3395_;
v___y_3589_ = v___y_3396_;
v___y_3590_ = v___y_3397_;
v___y_3591_ = v___y_3398_;
v___y_3592_ = v___y_3399_;
v___y_3593_ = v___y_3400_;
v___y_3594_ = v___y_3401_;
goto v___jp_3585_;
}
}
}
else
{
lean_object* v___x_3626_; 
lean_dec(v___x_3618_);
lean_del_object(v___x_3513_);
v___x_3626_ = lean_box(0);
v_variantId_x3f_3586_ = v___x_3626_;
v___y_3587_ = v___y_3394_;
v___y_3588_ = v___y_3395_;
v___y_3589_ = v___y_3396_;
v___y_3590_ = v___y_3397_;
v___y_3591_ = v___y_3398_;
v___y_3592_ = v___y_3399_;
v___y_3593_ = v___y_3400_;
v___y_3594_ = v___y_3401_;
goto v___jp_3585_;
}
v___jp_3519_:
{
lean_object* v___x_3530_; 
v___x_3530_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_resolveExtraTheorems(v___y_3527_, v___y_3523_, v___y_3528_, v___y_3520_, v___y_3521_, v___y_3525_, v___y_3526_, v___y_3522_, v___y_3524_);
lean_dec(v___y_3527_);
if (lean_obj_tag(v___x_3530_) == 0)
{
lean_object* v_a_3531_; lean_object* v_fst_3532_; lean_object* v_snd_3533_; lean_object* v___x_3535_; uint8_t v_isShared_3536_; uint8_t v_isSharedCheck_3546_; 
v_a_3531_ = lean_ctor_get(v___x_3530_, 0);
lean_inc(v_a_3531_);
lean_dec_ref_known(v___x_3530_, 1);
v_fst_3532_ = lean_ctor_get(v_a_3531_, 0);
v_snd_3533_ = lean_ctor_get(v_a_3531_, 1);
v_isSharedCheck_3546_ = !lean_is_exclusive(v_a_3531_);
if (v_isSharedCheck_3546_ == 0)
{
v___x_3535_ = v_a_3531_;
v_isShared_3536_ = v_isSharedCheck_3546_;
goto v_resetjp_3534_;
}
else
{
lean_inc(v_snd_3533_);
lean_inc(v_fst_3532_);
lean_dec(v_a_3531_);
v___x_3535_ = lean_box(0);
v_isShared_3536_ = v_isSharedCheck_3546_;
goto v_resetjp_3534_;
}
v_resetjp_3534_:
{
lean_object* v___x_3537_; lean_object* v_cache_3538_; lean_object* v_simpState_3539_; lean_object* v___x_3541_; 
v___x_3537_ = lean_st_ref_get(v___y_3528_);
v_cache_3538_ = lean_ctor_get(v___x_3537_, 3);
lean_inc_ref(v_cache_3538_);
lean_dec(v___x_3537_);
v_simpState_3539_ = lean_ctor_get(v_cache_3538_, 2);
lean_inc_ref(v_simpState_3539_);
lean_dec_ref(v_cache_3538_);
lean_inc(v___y_3529_);
if (v_isShared_3536_ == 0)
{
lean_ctor_set(v___x_3535_, 1, v_fst_3532_);
lean_ctor_set(v___x_3535_, 0, v___y_3529_);
v___x_3541_ = v___x_3535_;
goto v_reusejp_3540_;
}
else
{
lean_object* v_reuseFailAlloc_3545_; 
v_reuseFailAlloc_3545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3545_, 0, v___y_3529_);
lean_ctor_set(v_reuseFailAlloc_3545_, 1, v_fst_3532_);
v___x_3541_ = v_reuseFailAlloc_3545_;
goto v_reusejp_3540_;
}
v_reusejp_3540_:
{
lean_object* v___x_3542_; 
v___x_3542_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__2___redArg(v_simpState_3539_, v___x_3541_);
lean_dec_ref(v_simpState_3539_);
if (lean_obj_tag(v___x_3542_) == 0)
{
lean_object* v___x_3543_; 
v___x_3543_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__6, &l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__6_once, _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__6);
v___y_3404_ = v___y_3520_;
v___y_3405_ = v___y_3521_;
v___y_3406_ = v___y_3522_;
v___y_3407_ = v_snd_3533_;
v___y_3408_ = v___y_3523_;
v___y_3409_ = v___y_3529_;
v___y_3410_ = v___x_3541_;
v___y_3411_ = v___y_3524_;
v___y_3412_ = v___y_3525_;
v___y_3413_ = v___y_3526_;
v___y_3414_ = v___y_3528_;
v___y_3415_ = v___x_3543_;
goto v___jp_3403_;
}
else
{
lean_object* v_val_3544_; 
v_val_3544_ = lean_ctor_get(v___x_3542_, 0);
lean_inc(v_val_3544_);
lean_dec_ref_known(v___x_3542_, 1);
v___y_3404_ = v___y_3520_;
v___y_3405_ = v___y_3521_;
v___y_3406_ = v___y_3522_;
v___y_3407_ = v_snd_3533_;
v___y_3408_ = v___y_3523_;
v___y_3409_ = v___y_3529_;
v___y_3410_ = v___x_3541_;
v___y_3411_ = v___y_3524_;
v___y_3412_ = v___y_3525_;
v___y_3413_ = v___y_3526_;
v___y_3414_ = v___y_3528_;
v___y_3415_ = v_val_3544_;
goto v___jp_3403_;
}
}
}
}
else
{
lean_object* v_a_3547_; lean_object* v___x_3549_; uint8_t v_isShared_3550_; uint8_t v_isSharedCheck_3554_; 
lean_dec(v___y_3529_);
v_a_3547_ = lean_ctor_get(v___x_3530_, 0);
v_isSharedCheck_3554_ = !lean_is_exclusive(v___x_3530_);
if (v_isSharedCheck_3554_ == 0)
{
v___x_3549_ = v___x_3530_;
v_isShared_3550_ = v_isSharedCheck_3554_;
goto v_resetjp_3548_;
}
else
{
lean_inc(v_a_3547_);
lean_dec(v___x_3530_);
v___x_3549_ = lean_box(0);
v_isShared_3550_ = v_isSharedCheck_3554_;
goto v_resetjp_3548_;
}
v_resetjp_3548_:
{
lean_object* v___x_3552_; 
if (v_isShared_3550_ == 0)
{
v___x_3552_ = v___x_3549_;
goto v_reusejp_3551_;
}
else
{
lean_object* v_reuseFailAlloc_3553_; 
v_reuseFailAlloc_3553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3553_, 0, v_a_3547_);
v___x_3552_ = v_reuseFailAlloc_3553_;
goto v_reusejp_3551_;
}
v_reusejp_3551_:
{
return v___x_3552_;
}
}
}
}
v___jp_3555_:
{
if (lean_obj_tag(v___y_3556_) == 0)
{
lean_object* v___x_3566_; 
v___x_3566_ = lean_box(0);
v___y_3520_ = v___y_3560_;
v___y_3521_ = v___y_3561_;
v___y_3522_ = v___y_3564_;
v___y_3523_ = v___y_3558_;
v___y_3524_ = v___y_3565_;
v___y_3525_ = v___y_3562_;
v___y_3526_ = v___y_3563_;
v___y_3527_ = v_extraIds_3557_;
v___y_3528_ = v___y_3559_;
v___y_3529_ = v___x_3566_;
goto v___jp_3519_;
}
else
{
lean_object* v_val_3567_; lean_object* v___x_3568_; 
v_val_3567_ = lean_ctor_get(v___y_3556_, 0);
lean_inc(v_val_3567_);
lean_dec_ref_known(v___y_3556_, 1);
v___x_3568_ = l_Lean_TSyntax_getId(v_val_3567_);
lean_dec(v_val_3567_);
v___y_3520_ = v___y_3560_;
v___y_3521_ = v___y_3561_;
v___y_3522_ = v___y_3564_;
v___y_3523_ = v___y_3558_;
v___y_3524_ = v___y_3565_;
v___y_3525_ = v___y_3562_;
v___y_3526_ = v___y_3563_;
v___y_3527_ = v_extraIds_3557_;
v___y_3528_ = v___y_3559_;
v___y_3529_ = v___x_3568_;
goto v___jp_3519_;
}
}
v___jp_3569_:
{
size_t v_sz_3580_; size_t v___x_3581_; lean_object* v___x_3582_; 
v_sz_3580_ = lean_array_size(v___y_3579_);
v___x_3581_ = ((size_t)0ULL);
v___x_3582_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__3(v_sz_3580_, v___x_3581_, v___y_3579_);
if (lean_obj_tag(v___x_3582_) == 0)
{
lean_object* v___x_3583_; 
lean_dec(v___y_3575_);
v___x_3583_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro_spec__0___redArg();
return v___x_3583_;
}
else
{
v___y_3556_ = v___y_3575_;
v_extraIds_3557_ = v___x_3582_;
v___y_3558_ = v___y_3570_;
v___y_3559_ = v___y_3576_;
v___y_3560_ = v___y_3577_;
v___y_3561_ = v___y_3574_;
v___y_3562_ = v___y_3578_;
v___y_3563_ = v___y_3573_;
v___y_3564_ = v___y_3572_;
v___y_3565_ = v___y_3571_;
goto v___jp_3555_;
}
}
v___jp_3585_:
{
lean_object* v___x_3595_; lean_object* v___x_3596_; uint8_t v___x_3597_; 
v___x_3595_ = lean_unsigned_to_nat(2u);
v___x_3596_ = l_Lean_Syntax_getArg(v_stx_3393_, v___x_3595_);
lean_dec(v_stx_3393_);
v___x_3597_ = l_Lean_Syntax_isNone(v___x_3596_);
if (v___x_3597_ == 0)
{
lean_object* v___x_3598_; uint8_t v___x_3599_; 
v___x_3598_ = lean_unsigned_to_nat(3u);
lean_inc(v___x_3596_);
v___x_3599_ = l_Lean_Syntax_matchesNull(v___x_3596_, v___x_3598_);
if (v___x_3599_ == 0)
{
lean_object* v___x_3600_; 
lean_dec(v___x_3596_);
lean_dec(v_variantId_x3f_3586_);
v___x_3600_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymIntro_spec__0___redArg();
return v___x_3600_;
}
else
{
lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; uint8_t v___x_3605_; 
v___x_3601_ = l_Lean_Syntax_getArg(v___x_3596_, v___x_3584_);
lean_dec(v___x_3596_);
v___x_3602_ = l_Lean_Syntax_getArgs(v___x_3601_);
lean_dec(v___x_3601_);
v___x_3603_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__7));
v___x_3604_ = lean_array_get_size(v___x_3602_);
v___x_3605_ = lean_nat_dec_lt(v___x_3518_, v___x_3604_);
if (v___x_3605_ == 0)
{
lean_dec_ref(v___x_3602_);
v___y_3570_ = v___y_3587_;
v___y_3571_ = v___y_3594_;
v___y_3572_ = v___y_3593_;
v___y_3573_ = v___y_3592_;
v___y_3574_ = v___y_3590_;
v___y_3575_ = v_variantId_x3f_3586_;
v___y_3576_ = v___y_3588_;
v___y_3577_ = v___y_3589_;
v___y_3578_ = v___y_3591_;
v___y_3579_ = v___x_3603_;
goto v___jp_3569_;
}
else
{
lean_object* v___x_3606_; lean_object* v___x_3607_; uint8_t v___x_3608_; 
v___x_3606_ = lean_box(v___x_3599_);
v___x_3607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3607_, 0, v___x_3606_);
lean_ctor_set(v___x_3607_, 1, v___x_3603_);
v___x_3608_ = lean_nat_dec_le(v___x_3604_, v___x_3604_);
if (v___x_3608_ == 0)
{
if (v___x_3605_ == 0)
{
lean_dec_ref_known(v___x_3607_, 2);
lean_dec_ref(v___x_3602_);
v___y_3570_ = v___y_3587_;
v___y_3571_ = v___y_3594_;
v___y_3572_ = v___y_3593_;
v___y_3573_ = v___y_3592_;
v___y_3574_ = v___y_3590_;
v___y_3575_ = v_variantId_x3f_3586_;
v___y_3576_ = v___y_3588_;
v___y_3577_ = v___y_3589_;
v___y_3578_ = v___y_3591_;
v___y_3579_ = v___x_3603_;
goto v___jp_3569_;
}
else
{
size_t v___x_3609_; size_t v___x_3610_; lean_object* v___x_3611_; lean_object* v_snd_3612_; 
v___x_3609_ = ((size_t)0ULL);
v___x_3610_ = lean_usize_of_nat(v___x_3604_);
v___x_3611_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__4(v___x_3599_, v___x_3597_, v___x_3602_, v___x_3609_, v___x_3610_, v___x_3607_);
lean_dec_ref(v___x_3602_);
v_snd_3612_ = lean_ctor_get(v___x_3611_, 1);
lean_inc(v_snd_3612_);
lean_dec_ref(v___x_3611_);
v___y_3570_ = v___y_3587_;
v___y_3571_ = v___y_3594_;
v___y_3572_ = v___y_3593_;
v___y_3573_ = v___y_3592_;
v___y_3574_ = v___y_3590_;
v___y_3575_ = v_variantId_x3f_3586_;
v___y_3576_ = v___y_3588_;
v___y_3577_ = v___y_3589_;
v___y_3578_ = v___y_3591_;
v___y_3579_ = v_snd_3612_;
goto v___jp_3569_;
}
}
else
{
size_t v___x_3613_; size_t v___x_3614_; lean_object* v___x_3615_; lean_object* v_snd_3616_; 
v___x_3613_ = ((size_t)0ULL);
v___x_3614_ = lean_usize_of_nat(v___x_3604_);
v___x_3615_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__4(v___x_3599_, v___x_3597_, v___x_3602_, v___x_3613_, v___x_3614_, v___x_3607_);
lean_dec_ref(v___x_3602_);
v_snd_3616_ = lean_ctor_get(v___x_3615_, 1);
lean_inc(v_snd_3616_);
lean_dec_ref(v___x_3615_);
v___y_3570_ = v___y_3587_;
v___y_3571_ = v___y_3594_;
v___y_3572_ = v___y_3593_;
v___y_3573_ = v___y_3592_;
v___y_3574_ = v___y_3590_;
v___y_3575_ = v_variantId_x3f_3586_;
v___y_3576_ = v___y_3588_;
v___y_3577_ = v___y_3589_;
v___y_3578_ = v___y_3591_;
v___y_3579_ = v_snd_3616_;
goto v___jp_3569_;
}
}
}
}
else
{
lean_object* v___x_3617_; 
lean_dec(v___x_3596_);
v___x_3617_ = lean_box(0);
v___y_3556_ = v_variantId_x3f_3586_;
v_extraIds_3557_ = v___x_3617_;
v___y_3558_ = v___y_3587_;
v___y_3559_ = v___y_3588_;
v___y_3560_ = v___y_3589_;
v___y_3561_ = v___y_3590_;
v___y_3562_ = v___y_3591_;
v___y_3563_ = v___y_3592_;
v___y_3564_ = v___y_3593_;
v___y_3565_ = v___y_3594_;
goto v___jp_3555_;
}
}
}
}
}
else
{
lean_dec(v_stx_3393_);
return v___x_3511_;
}
v___jp_3403_:
{
lean_object* v___x_3416_; 
v___x_3416_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_elabSimpVariant(v___y_3409_, v___y_3407_, v___y_3408_, v___y_3414_, v___y_3404_, v___y_3405_, v___y_3412_, v___y_3413_, v___y_3406_, v___y_3411_);
lean_dec_ref(v___y_3407_);
if (lean_obj_tag(v___x_3416_) == 0)
{
lean_object* v_a_3417_; lean_object* v_fst_3418_; lean_object* v_snd_3419_; lean_object* v___x_3420_; 
v_a_3417_ = lean_ctor_get(v___x_3416_, 0);
lean_inc(v_a_3417_);
lean_dec_ref_known(v___x_3416_, 1);
v_fst_3418_ = lean_ctor_get(v_a_3417_, 0);
lean_inc(v_fst_3418_);
v_snd_3419_ = lean_ctor_get(v_a_3417_, 1);
lean_inc(v_snd_3419_);
lean_dec(v_a_3417_);
v___x_3420_ = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(v___y_3414_, v___y_3412_, v___y_3413_, v___y_3406_, v___y_3411_);
if (lean_obj_tag(v___x_3420_) == 0)
{
lean_object* v_a_3421_; lean_object* v_toGoalState_3422_; lean_object* v_mvarId_3423_; lean_object* v___x_3425_; uint8_t v_isShared_3426_; uint8_t v_isSharedCheck_3494_; 
v_a_3421_ = lean_ctor_get(v___x_3420_, 0);
lean_inc(v_a_3421_);
lean_dec_ref_known(v___x_3420_, 1);
v_toGoalState_3422_ = lean_ctor_get(v_a_3421_, 0);
v_mvarId_3423_ = lean_ctor_get(v_a_3421_, 1);
v_isSharedCheck_3494_ = !lean_is_exclusive(v_a_3421_);
if (v_isSharedCheck_3494_ == 0)
{
v___x_3425_ = v_a_3421_;
v_isShared_3426_ = v_isSharedCheck_3494_;
goto v_resetjp_3424_;
}
else
{
lean_inc(v_mvarId_3423_);
lean_inc(v_toGoalState_3422_);
lean_dec(v_a_3421_);
v___x_3425_ = lean_box(0);
v_isShared_3426_ = v_isSharedCheck_3494_;
goto v_resetjp_3424_;
}
v_resetjp_3424_:
{
lean_object* v___f_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; 
lean_inc_n(v_mvarId_3423_, 2);
v___f_3427_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__0___boxed), 14, 4);
lean_closure_set(v___f_3427_, 0, v_mvarId_3423_);
lean_closure_set(v___f_3427_, 1, v_fst_3418_);
lean_closure_set(v___f_3427_, 2, v_snd_3419_);
lean_closure_set(v___f_3427_, 3, v___y_3415_);
v___x_3428_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__0___boxed), 13, 3);
lean_closure_set(v___x_3428_, 0, lean_box(0));
lean_closure_set(v___x_3428_, 1, v_mvarId_3423_);
lean_closure_set(v___x_3428_, 2, v___f_3427_);
v___x_3429_ = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(v___x_3428_, v___y_3408_, v___y_3414_, v___y_3412_, v___y_3413_, v___y_3406_, v___y_3411_);
if (lean_obj_tag(v___x_3429_) == 0)
{
lean_object* v_a_3430_; lean_object* v_fst_3431_; lean_object* v_snd_3432_; lean_object* v___x_3434_; uint8_t v_isShared_3435_; uint8_t v_isSharedCheck_3485_; 
v_a_3430_ = lean_ctor_get(v___x_3429_, 0);
lean_inc(v_a_3430_);
lean_dec_ref_known(v___x_3429_, 1);
v_fst_3431_ = lean_ctor_get(v_a_3430_, 0);
v_snd_3432_ = lean_ctor_get(v_a_3430_, 1);
v_isSharedCheck_3485_ = !lean_is_exclusive(v_a_3430_);
if (v_isSharedCheck_3485_ == 0)
{
v___x_3434_ = v_a_3430_;
v_isShared_3435_ = v_isSharedCheck_3485_;
goto v_resetjp_3433_;
}
else
{
lean_inc(v_snd_3432_);
lean_inc(v_fst_3431_);
lean_dec(v_a_3430_);
v___x_3434_ = lean_box(0);
v_isShared_3435_ = v_isSharedCheck_3485_;
goto v_resetjp_3433_;
}
v_resetjp_3433_:
{
lean_object* v___x_3436_; lean_object* v_cache_3437_; lean_object* v_symState_3438_; lean_object* v_grindState_3439_; lean_object* v_goals_3440_; lean_object* v___x_3442_; uint8_t v_isShared_3443_; uint8_t v_isSharedCheck_3484_; 
v___x_3436_ = lean_st_ref_take(v___y_3414_);
v_cache_3437_ = lean_ctor_get(v___x_3436_, 3);
v_symState_3438_ = lean_ctor_get(v___x_3436_, 0);
v_grindState_3439_ = lean_ctor_get(v___x_3436_, 1);
v_goals_3440_ = lean_ctor_get(v___x_3436_, 2);
v_isSharedCheck_3484_ = !lean_is_exclusive(v___x_3436_);
if (v_isSharedCheck_3484_ == 0)
{
v___x_3442_ = v___x_3436_;
v_isShared_3443_ = v_isSharedCheck_3484_;
goto v_resetjp_3441_;
}
else
{
lean_inc(v_cache_3437_);
lean_inc(v_goals_3440_);
lean_inc(v_grindState_3439_);
lean_inc(v_symState_3438_);
lean_dec(v___x_3436_);
v___x_3442_ = lean_box(0);
v_isShared_3443_ = v_isSharedCheck_3484_;
goto v_resetjp_3441_;
}
v_resetjp_3441_:
{
lean_object* v_backwardRuleName_3444_; lean_object* v_backwardRuleSyntax_3445_; lean_object* v_simpState_3446_; lean_object* v_dsimpState_3447_; lean_object* v___x_3449_; uint8_t v_isShared_3450_; uint8_t v_isSharedCheck_3483_; 
v_backwardRuleName_3444_ = lean_ctor_get(v_cache_3437_, 0);
v_backwardRuleSyntax_3445_ = lean_ctor_get(v_cache_3437_, 1);
v_simpState_3446_ = lean_ctor_get(v_cache_3437_, 2);
v_dsimpState_3447_ = lean_ctor_get(v_cache_3437_, 3);
v_isSharedCheck_3483_ = !lean_is_exclusive(v_cache_3437_);
if (v_isSharedCheck_3483_ == 0)
{
v___x_3449_ = v_cache_3437_;
v_isShared_3450_ = v_isSharedCheck_3483_;
goto v_resetjp_3448_;
}
else
{
lean_inc(v_dsimpState_3447_);
lean_inc(v_simpState_3446_);
lean_inc(v_backwardRuleSyntax_3445_);
lean_inc(v_backwardRuleName_3444_);
lean_dec(v_cache_3437_);
v___x_3449_ = lean_box(0);
v_isShared_3450_ = v_isSharedCheck_3483_;
goto v_resetjp_3448_;
}
v_resetjp_3448_:
{
lean_object* v___x_3451_; lean_object* v___x_3453_; 
v___x_3451_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1___redArg(v_simpState_3446_, v___y_3410_, v_snd_3432_);
if (v_isShared_3450_ == 0)
{
lean_ctor_set(v___x_3449_, 2, v___x_3451_);
v___x_3453_ = v___x_3449_;
goto v_reusejp_3452_;
}
else
{
lean_object* v_reuseFailAlloc_3482_; 
v_reuseFailAlloc_3482_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3482_, 0, v_backwardRuleName_3444_);
lean_ctor_set(v_reuseFailAlloc_3482_, 1, v_backwardRuleSyntax_3445_);
lean_ctor_set(v_reuseFailAlloc_3482_, 2, v___x_3451_);
lean_ctor_set(v_reuseFailAlloc_3482_, 3, v_dsimpState_3447_);
v___x_3453_ = v_reuseFailAlloc_3482_;
goto v_reusejp_3452_;
}
v_reusejp_3452_:
{
lean_object* v___x_3455_; 
if (v_isShared_3443_ == 0)
{
lean_ctor_set(v___x_3442_, 3, v___x_3453_);
v___x_3455_ = v___x_3442_;
goto v_reusejp_3454_;
}
else
{
lean_object* v_reuseFailAlloc_3481_; 
v_reuseFailAlloc_3481_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3481_, 0, v_symState_3438_);
lean_ctor_set(v_reuseFailAlloc_3481_, 1, v_grindState_3439_);
lean_ctor_set(v_reuseFailAlloc_3481_, 2, v_goals_3440_);
lean_ctor_set(v_reuseFailAlloc_3481_, 3, v___x_3453_);
v___x_3455_ = v_reuseFailAlloc_3481_;
goto v_reusejp_3454_;
}
v_reusejp_3454_:
{
lean_object* v___x_3456_; lean_object* v___f_3457_; lean_object* v___x_3458_; 
v___x_3456_ = lean_st_ref_set(v___y_3414_, v___x_3455_);
v___f_3457_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__1___boxed), 12, 2);
lean_closure_set(v___f_3457_, 0, v_fst_3431_);
lean_closure_set(v___f_3457_, 1, v_mvarId_3423_);
v___x_3458_ = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(v___f_3457_, v___y_3408_, v___y_3414_, v___y_3412_, v___y_3413_, v___y_3406_, v___y_3411_);
if (lean_obj_tag(v___x_3458_) == 0)
{
lean_object* v_a_3459_; 
v_a_3459_ = lean_ctor_get(v___x_3458_, 0);
lean_inc(v_a_3459_);
lean_dec_ref_known(v___x_3458_, 1);
switch(lean_obj_tag(v_a_3459_))
{
case 0:
{
lean_object* v___x_3460_; lean_object* v___x_3461_; 
lean_del_object(v___x_3434_);
lean_del_object(v___x_3425_);
lean_dec_ref(v_toGoalState_3422_);
v___x_3460_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__1, &l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__1);
v___x_3461_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalIntroCore_spec__2___redArg(v___x_3460_, v___y_3412_, v___y_3413_, v___y_3406_, v___y_3411_);
return v___x_3461_;
}
case 1:
{
lean_object* v___x_3462_; lean_object* v___x_3463_; 
lean_del_object(v___x_3434_);
lean_del_object(v___x_3425_);
lean_dec_ref(v_toGoalState_3422_);
v___x_3462_ = lean_box(0);
v___x_3463_ = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(v___x_3462_, v___y_3414_, v___y_3412_, v___y_3413_, v___y_3406_, v___y_3411_);
return v___x_3463_;
}
default: 
{
lean_object* v_mvarId_3464_; lean_object* v___x_3466_; 
v_mvarId_3464_ = lean_ctor_get(v_a_3459_, 0);
lean_inc(v_mvarId_3464_);
lean_dec_ref_known(v_a_3459_, 1);
if (v_isShared_3426_ == 0)
{
lean_ctor_set(v___x_3425_, 1, v_mvarId_3464_);
v___x_3466_ = v___x_3425_;
goto v_reusejp_3465_;
}
else
{
lean_object* v_reuseFailAlloc_3472_; 
v_reuseFailAlloc_3472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3472_, 0, v_toGoalState_3422_);
lean_ctor_set(v_reuseFailAlloc_3472_, 1, v_mvarId_3464_);
v___x_3466_ = v_reuseFailAlloc_3472_;
goto v_reusejp_3465_;
}
v_reusejp_3465_:
{
lean_object* v___x_3467_; lean_object* v___x_3469_; 
v___x_3467_ = lean_box(0);
if (v_isShared_3435_ == 0)
{
lean_ctor_set_tag(v___x_3434_, 1);
lean_ctor_set(v___x_3434_, 1, v___x_3467_);
lean_ctor_set(v___x_3434_, 0, v___x_3466_);
v___x_3469_ = v___x_3434_;
goto v_reusejp_3468_;
}
else
{
lean_object* v_reuseFailAlloc_3471_; 
v_reuseFailAlloc_3471_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3471_, 0, v___x_3466_);
lean_ctor_set(v_reuseFailAlloc_3471_, 1, v___x_3467_);
v___x_3469_ = v_reuseFailAlloc_3471_;
goto v_reusejp_3468_;
}
v_reusejp_3468_:
{
lean_object* v___x_3470_; 
v___x_3470_ = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(v___x_3469_, v___y_3414_, v___y_3412_, v___y_3413_, v___y_3406_, v___y_3411_);
return v___x_3470_;
}
}
}
}
}
else
{
lean_object* v_a_3473_; lean_object* v___x_3475_; uint8_t v_isShared_3476_; uint8_t v_isSharedCheck_3480_; 
lean_del_object(v___x_3434_);
lean_del_object(v___x_3425_);
lean_dec_ref(v_toGoalState_3422_);
v_a_3473_ = lean_ctor_get(v___x_3458_, 0);
v_isSharedCheck_3480_ = !lean_is_exclusive(v___x_3458_);
if (v_isSharedCheck_3480_ == 0)
{
v___x_3475_ = v___x_3458_;
v_isShared_3476_ = v_isSharedCheck_3480_;
goto v_resetjp_3474_;
}
else
{
lean_inc(v_a_3473_);
lean_dec(v___x_3458_);
v___x_3475_ = lean_box(0);
v_isShared_3476_ = v_isSharedCheck_3480_;
goto v_resetjp_3474_;
}
v_resetjp_3474_:
{
lean_object* v___x_3478_; 
if (v_isShared_3476_ == 0)
{
v___x_3478_ = v___x_3475_;
goto v_reusejp_3477_;
}
else
{
lean_object* v_reuseFailAlloc_3479_; 
v_reuseFailAlloc_3479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3479_, 0, v_a_3473_);
v___x_3478_ = v_reuseFailAlloc_3479_;
goto v_reusejp_3477_;
}
v_reusejp_3477_:
{
return v___x_3478_;
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
lean_object* v_a_3486_; lean_object* v___x_3488_; uint8_t v_isShared_3489_; uint8_t v_isSharedCheck_3493_; 
lean_del_object(v___x_3425_);
lean_dec(v_mvarId_3423_);
lean_dec_ref(v_toGoalState_3422_);
lean_dec_ref(v___y_3410_);
v_a_3486_ = lean_ctor_get(v___x_3429_, 0);
v_isSharedCheck_3493_ = !lean_is_exclusive(v___x_3429_);
if (v_isSharedCheck_3493_ == 0)
{
v___x_3488_ = v___x_3429_;
v_isShared_3489_ = v_isSharedCheck_3493_;
goto v_resetjp_3487_;
}
else
{
lean_inc(v_a_3486_);
lean_dec(v___x_3429_);
v___x_3488_ = lean_box(0);
v_isShared_3489_ = v_isSharedCheck_3493_;
goto v_resetjp_3487_;
}
v_resetjp_3487_:
{
lean_object* v___x_3491_; 
if (v_isShared_3489_ == 0)
{
v___x_3491_ = v___x_3488_;
goto v_reusejp_3490_;
}
else
{
lean_object* v_reuseFailAlloc_3492_; 
v_reuseFailAlloc_3492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3492_, 0, v_a_3486_);
v___x_3491_ = v_reuseFailAlloc_3492_;
goto v_reusejp_3490_;
}
v_reusejp_3490_:
{
return v___x_3491_;
}
}
}
}
}
else
{
lean_object* v_a_3495_; lean_object* v___x_3497_; uint8_t v_isShared_3498_; uint8_t v_isSharedCheck_3502_; 
lean_dec(v_snd_3419_);
lean_dec(v_fst_3418_);
lean_dec_ref(v___y_3415_);
lean_dec_ref(v___y_3410_);
v_a_3495_ = lean_ctor_get(v___x_3420_, 0);
v_isSharedCheck_3502_ = !lean_is_exclusive(v___x_3420_);
if (v_isSharedCheck_3502_ == 0)
{
v___x_3497_ = v___x_3420_;
v_isShared_3498_ = v_isSharedCheck_3502_;
goto v_resetjp_3496_;
}
else
{
lean_inc(v_a_3495_);
lean_dec(v___x_3420_);
v___x_3497_ = lean_box(0);
v_isShared_3498_ = v_isSharedCheck_3502_;
goto v_resetjp_3496_;
}
v_resetjp_3496_:
{
lean_object* v___x_3500_; 
if (v_isShared_3498_ == 0)
{
v___x_3500_ = v___x_3497_;
goto v_reusejp_3499_;
}
else
{
lean_object* v_reuseFailAlloc_3501_; 
v_reuseFailAlloc_3501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3501_, 0, v_a_3495_);
v___x_3500_ = v_reuseFailAlloc_3501_;
goto v_reusejp_3499_;
}
v_reusejp_3499_:
{
return v___x_3500_;
}
}
}
}
else
{
lean_object* v_a_3503_; lean_object* v___x_3505_; uint8_t v_isShared_3506_; uint8_t v_isSharedCheck_3510_; 
lean_dec_ref(v___y_3415_);
lean_dec_ref(v___y_3410_);
v_a_3503_ = lean_ctor_get(v___x_3416_, 0);
v_isSharedCheck_3510_ = !lean_is_exclusive(v___x_3416_);
if (v_isSharedCheck_3510_ == 0)
{
v___x_3505_ = v___x_3416_;
v_isShared_3506_ = v_isSharedCheck_3510_;
goto v_resetjp_3504_;
}
else
{
lean_inc(v_a_3503_);
lean_dec(v___x_3416_);
v___x_3505_ = lean_box(0);
v_isShared_3506_ = v_isSharedCheck_3510_;
goto v_resetjp_3504_;
}
v_resetjp_3504_:
{
lean_object* v___x_3508_; 
if (v_isShared_3506_ == 0)
{
v___x_3508_ = v___x_3505_;
goto v_reusejp_3507_;
}
else
{
lean_object* v_reuseFailAlloc_3509_; 
v_reuseFailAlloc_3509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3509_, 0, v_a_3503_);
v___x_3508_ = v_reuseFailAlloc_3509_;
goto v_reusejp_3507_;
}
v_reusejp_3507_:
{
return v___x_3508_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___boxed(lean_object* v_stx_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_, lean_object* v___y_3638_){
_start:
{
lean_object* v_res_3639_; 
v_res_3639_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2(v_stx_3629_, v___y_3630_, v___y_3631_, v___y_3632_, v___y_3633_, v___y_3634_, v___y_3635_, v___y_3636_, v___y_3637_);
lean_dec(v___y_3637_);
lean_dec_ref(v___y_3636_);
lean_dec(v___y_3635_);
lean_dec_ref(v___y_3634_);
lean_dec(v___y_3633_);
lean_dec_ref(v___y_3632_);
lean_dec(v___y_3631_);
lean_dec_ref(v___y_3630_);
return v_res_3639_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp(lean_object* v_stx_3640_, lean_object* v_a_3641_, lean_object* v_a_3642_, lean_object* v_a_3643_, lean_object* v_a_3644_, lean_object* v_a_3645_, lean_object* v_a_3646_, lean_object* v_a_3647_, lean_object* v_a_3648_){
_start:
{
lean_object* v___f_3650_; lean_object* v___x_3651_; 
v___f_3650_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___boxed), 10, 1);
lean_closure_set(v___f_3650_, 0, v_stx_3640_);
v___x_3651_ = l_Lean_Elab_Tactic_Grind_withMainContext___redArg(v___f_3650_, v_a_3641_, v_a_3642_, v_a_3643_, v_a_3644_, v_a_3645_, v_a_3646_, v_a_3647_, v_a_3648_);
return v___x_3651_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___boxed(lean_object* v_stx_3652_, lean_object* v_a_3653_, lean_object* v_a_3654_, lean_object* v_a_3655_, lean_object* v_a_3656_, lean_object* v_a_3657_, lean_object* v_a_3658_, lean_object* v_a_3659_, lean_object* v_a_3660_, lean_object* v_a_3661_){
_start:
{
lean_object* v_res_3662_; 
v_res_3662_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp(v_stx_3652_, v_a_3653_, v_a_3654_, v_a_3655_, v_a_3656_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_);
lean_dec(v_a_3660_);
lean_dec_ref(v_a_3659_);
lean_dec(v_a_3658_);
lean_dec_ref(v_a_3657_);
lean_dec(v_a_3656_);
lean_dec_ref(v_a_3655_);
lean_dec(v_a_3654_);
lean_dec_ref(v_a_3653_);
return v_res_3662_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1(lean_object* v_00_u03b2_3663_, lean_object* v_m_3664_, lean_object* v_a_3665_, lean_object* v_b_3666_){
_start:
{
lean_object* v___x_3667_; 
v___x_3667_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1___redArg(v_m_3664_, v_a_3665_, v_b_3666_);
return v___x_3667_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__2(lean_object* v_00_u03b2_3668_, lean_object* v_m_3669_, lean_object* v_a_3670_){
_start:
{
lean_object* v___x_3671_; 
v___x_3671_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__2___redArg(v_m_3669_, v_a_3670_);
return v___x_3671_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__2___boxed(lean_object* v_00_u03b2_3672_, lean_object* v_m_3673_, lean_object* v_a_3674_){
_start:
{
lean_object* v_res_3675_; 
v_res_3675_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__2(v_00_u03b2_3672_, v_m_3673_, v_a_3674_);
lean_dec_ref(v_a_3674_);
lean_dec_ref(v_m_3673_);
return v_res_3675_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__1(lean_object* v_00_u03b2_3676_, lean_object* v_a_3677_, lean_object* v_x_3678_){
_start:
{
uint8_t v___x_3679_; 
v___x_3679_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__1___redArg(v_a_3677_, v_x_3678_);
return v___x_3679_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__1___boxed(lean_object* v_00_u03b2_3680_, lean_object* v_a_3681_, lean_object* v_x_3682_){
_start:
{
uint8_t v_res_3683_; lean_object* v_r_3684_; 
v_res_3683_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__1(v_00_u03b2_3680_, v_a_3681_, v_x_3682_);
lean_dec(v_x_3682_);
lean_dec_ref(v_a_3681_);
v_r_3684_ = lean_box(v_res_3683_);
return v_r_3684_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__2(lean_object* v_00_u03b2_3685_, lean_object* v_data_3686_){
_start:
{
lean_object* v___x_3687_; 
v___x_3687_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__2___redArg(v_data_3686_);
return v___x_3687_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__3(lean_object* v_00_u03b2_3688_, lean_object* v_a_3689_, lean_object* v_b_3690_, lean_object* v_x_3691_){
_start:
{
lean_object* v___x_3692_; 
v___x_3692_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__3___redArg(v_a_3689_, v_b_3690_, v_x_3691_);
return v___x_3692_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__2_spec__5(lean_object* v_00_u03b2_3693_, lean_object* v_a_3694_, lean_object* v_x_3695_){
_start:
{
lean_object* v___x_3696_; 
v___x_3696_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__2_spec__5___redArg(v_a_3694_, v_x_3695_);
return v___x_3696_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__2_spec__5___boxed(lean_object* v_00_u03b2_3697_, lean_object* v_a_3698_, lean_object* v_x_3699_){
_start:
{
lean_object* v_res_3700_; 
v_res_3700_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__2_spec__5(v_00_u03b2_3697_, v_a_3698_, v_x_3699_);
lean_dec(v_x_3699_);
lean_dec_ref(v_a_3698_);
return v_res_3700_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_3701_, lean_object* v_i_3702_, lean_object* v_source_3703_, lean_object* v_target_3704_){
_start:
{
lean_object* v___x_3705_; 
v___x_3705_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__2_spec__3___redArg(v_i_3702_, v_source_3703_, v_target_3704_);
return v___x_3705_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__2_spec__3_spec__7(lean_object* v_00_u03b2_3706_, lean_object* v_x_3707_, lean_object* v_x_3708_){
_start:
{
lean_object* v___x_3709_; 
v___x_3709_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp_spec__1_spec__2_spec__3_spec__7___redArg(v_x_3707_, v_x_3708_);
return v___x_3709_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp__1(){
_start:
{
lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; 
v___x_3715_ = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
v___x_3716_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___lam__2___closed__3));
v___x_3717_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp__1___closed__1));
v___x_3718_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___boxed), 10, 0);
v___x_3719_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3715_, v___x_3716_, v___x_3717_, v___x_3718_);
return v___x_3719_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp__1___boxed(lean_object* v_a_3720_){
_start:
{
lean_object* v_res_3721_; 
v_res_3721_ = l___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp___regBuiltin___private_Lean_Elab_Tactic_Grind_Sym_0__Lean_Elab_Tactic_Grind_evalSymSimp__1();
return v_res_3721_;
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
