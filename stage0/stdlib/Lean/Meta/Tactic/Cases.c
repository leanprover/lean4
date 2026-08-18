// Lean compiler output
// Module: Lean.Meta.Tactic.Cases
// Imports: public import Lean.Meta.Tactic.Induction public import Lean.Meta.Tactic.Acyclic public import Lean.Meta.Tactic.UnifyEq import Lean.Meta.Constructions.SparseCasesOn import Lean.Meta.Constructions.CtorIdx import Init.Omega
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
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_MVarId_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVarAt(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_Meta_introNCore(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_intro1Core(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_of_nat(lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* l_Lean_Meta_saveState___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNot(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_induction(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Meta_FVarSubst_erase(lean_object*, lean_object*);
lean_object* l_Lean_Meta_FVarSubst_insert(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkCasesOnName(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkSparseCasesOn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkCtorIdxName(lean_object*);
lean_object* l_Lean_Meta_FVarSubst_get(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_clear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_acyclic___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_unifyEq_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_Meta_FVarSubst_apply(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwNestedTacticEx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_Meta_saturate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_exactlyOne(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
uint8_t l_Lean_Expr_isEq(lean_object*);
uint8_t l_Lean_Expr_isHEq(lean_object*);
lean_object* l_Lean_Meta_ensureAtMostOne(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 74, .m_capacity = 74, .m_length = 73, .m_data = "Failed to compile pattern matching: Expected an inductive type, but found"};
static const lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_getInductiveUniverseAndParams___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_getInductiveUniverseAndParams___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_getInductiveUniverseAndParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getInductiveUniverseAndParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "HEq"};
static const lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__0_value),LEAN_SCALAR_PTR_LITERAL(67, 180, 169, 191, 74, 196, 152, 188)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "refl"};
static const lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__0_value),LEAN_SCALAR_PTR_LITERAL(67, 180, 169, 191, 74, 196, 152, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__2_value),LEAN_SCALAR_PTR_LITERAL(180, 202, 227, 45, 204, 223, 127, 41)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__4_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__5_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__4_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__2_value),LEAN_SCALAR_PTR_LITERAL(72, 6, 107, 181, 0, 125, 21, 187)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "h"};
static const lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(176, 181, 207, 77, 197, 87, 68, 121)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_withNewEqs___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_withNewEqs___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_withNewEqs___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_withNewEqs___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewEqs___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewEqs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewEqs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_generalizeTargetsEq_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_generalizeTargetsEq_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_generalizeTargetsEq_spec__0___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_generalizeTargetsEq_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_generalizeTargetsEq_spec__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_generalizeTargetsEq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeTargetsEq___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeTargetsEq___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_generalizeTargetsEq___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Invalid number of targets: "};
static const lean_object* l_Lean_Meta_generalizeTargetsEq___lam__1___closed__0 = (const lean_object*)&l_Lean_Meta_generalizeTargetsEq___lam__1___closed__0_value;
static lean_once_cell_t l_Lean_Meta_generalizeTargetsEq___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_generalizeTargetsEq___lam__1___closed__1;
static const lean_string_object l_Lean_Meta_generalizeTargetsEq___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = " targets provided, but motive only takes "};
static const lean_object* l_Lean_Meta_generalizeTargetsEq___lam__1___closed__2 = (const lean_object*)&l_Lean_Meta_generalizeTargetsEq___lam__1___closed__2_value;
static lean_once_cell_t l_Lean_Meta_generalizeTargetsEq___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_generalizeTargetsEq___lam__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeTargetsEq___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeTargetsEq___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__5___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeTargetsEq___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeTargetsEq___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_generalizeTargetsEq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "generalizeTargets"};
static const lean_object* l_Lean_Meta_generalizeTargetsEq___closed__0 = (const lean_object*)&l_Lean_Meta_generalizeTargetsEq___closed__0_value;
static const lean_ctor_object l_Lean_Meta_generalizeTargetsEq___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_generalizeTargetsEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 33, 44, 197, 230, 161, 237, 93)}};
static const lean_object* l_Lean_Meta_generalizeTargetsEq___closed__1 = (const lean_object*)&l_Lean_Meta_generalizeTargetsEq___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeTargetsEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeTargetsEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__5(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "x"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__3___closed__0 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__3___closed__0_value;
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(243, 101, 181, 186, 114, 114, 131, 189)}};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__3___closed__1 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__3___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "generalizeIndices"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__0 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__0_value;
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(254, 199, 71, 14, 111, 8, 96, 84)}};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__1 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__1_value;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "inductive type expected"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__2 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__2_value;
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__2_value)}};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__3 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__3_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__4;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__5;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "ill-formed inductive datatype"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__6 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__6_value;
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__6_value)}};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__7 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__7_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__8;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__9;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "indexed inductive type expected"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__10 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__10_value;
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__10_value)}};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__11 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__11_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__12;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__13;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeIndices_x27___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeIndices_x27___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeIndices_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeIndices_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeIndices___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeIndices___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeIndices(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeIndices___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "casesOn"};
static const lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__2(lean_object*, uint8_t, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___lam__1(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__3(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___lam__0___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__0;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__2;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4_spec__5(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "runtime"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__0_value;
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "maxRecDepth"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__1_value;
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 128, 123, 132, 117, 90, 116, 101)}};
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(88, 230, 219, 180, 63, 89, 202, 3)}};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__2 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__3;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__4;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Cases_unifyEqs_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_MVarId_acyclic___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Cases_unifyEqs_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_Cases_unifyEqs_x3f___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_unifyEqs_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_unifyEqs_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1___closed__0 = (const lean_object*)&l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "casesAuxOn"};
static const lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(33, 160, 116, 144, 209, 153, 27, 121)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "hasNotBit"};
static const lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(117, 117, 142, 139, 222, 16, 37, 88)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__5_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Cases_cases___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "not applicable to the given hypothesis"};
static const lean_object* l_Lean_Meta_Cases_cases___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Cases_cases___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Cases_cases___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Cases_cases___lam__0___closed__0_value)}};
static const lean_object* l_Lean_Meta_Cases_cases___lam__0___closed__1 = (const lean_object*)&l_Lean_Meta_Cases_cases___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Cases_cases___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Cases_cases___lam__0___closed__2;
static lean_once_cell_t l_Lean_Meta_Cases_cases___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Cases_cases___lam__0___closed__3;
static const lean_string_object l_Lean_Meta_Cases_cases___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_Lean_Meta_Cases_cases___lam__0___closed__4 = (const lean_object*)&l_Lean_Meta_Cases_cases___lam__0___closed__4_value;
static const lean_string_object l_Lean_Meta_Cases_cases___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Meta_Cases_cases___lam__0___closed__5 = (const lean_object*)&l_Lean_Meta_Cases_cases___lam__0___closed__5_value;
static const lean_string_object l_Lean_Meta_Cases_cases___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Meta_Cases_cases___lam__0___closed__6 = (const lean_object*)&l_Lean_Meta_Cases_cases___lam__0___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Cases_cases___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Cases_cases___lam__0___closed__6_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Meta_Cases_cases___lam__0___closed__7 = (const lean_object*)&l_Lean_Meta_Cases_cases___lam__0___closed__7_value;
static const lean_string_object l_Lean_Meta_Cases_cases___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "after generalizeIndices\n"};
static const lean_object* l_Lean_Meta_Cases_cases___lam__0___closed__8 = (const lean_object*)&l_Lean_Meta_Cases_cases___lam__0___closed__8_value;
static lean_once_cell_t l_Lean_Meta_Cases_cases___lam__0___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Cases_cases___lam__0___closed__9;
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_cases___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_cases___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Cases_cases___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "cases"};
static const lean_object* l_Lean_Meta_Cases_cases___closed__0 = (const lean_object*)&l_Lean_Meta_Cases_cases___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Cases_cases___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Cases_cases___closed__0_value),LEAN_SCALAR_PTR_LITERAL(220, 93, 203, 178, 149, 199, 118, 190)}};
static const lean_object* l_Lean_Meta_Cases_cases___closed__1 = (const lean_object*)&l_Lean_Meta_Cases_cases___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_cases(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_cases___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_cases(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_cases___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_MVarId_casesRec_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5___closed__0_value;
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3_spec__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3_spec__6___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3_spec__6___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3_spec__6(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_MVarId_casesRec___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_MVarId_casesRec___lam__0___closed__0 = (const lean_object*)&l_Lean_MVarId_casesRec___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_MVarId_casesRec___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_casesRec___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_casesRec___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_casesRec___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_casesRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_casesRec___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MVarId_casesAnd___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "And"};
static const lean_object* l_Lean_MVarId_casesAnd___lam__0___closed__0 = (const lean_object*)&l_Lean_MVarId_casesAnd___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_MVarId_casesAnd___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_casesAnd___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(49, 220, 212, 156, 122, 214, 55, 135)}};
static const lean_object* l_Lean_MVarId_casesAnd___lam__0___closed__1 = (const lean_object*)&l_Lean_MVarId_casesAnd___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_MVarId_casesAnd___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_casesAnd___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_MVarId_casesAnd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_MVarId_casesAnd___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_MVarId_casesAnd___closed__0 = (const lean_object*)&l_Lean_MVarId_casesAnd___closed__0_value;
static const lean_string_object l_Lean_MVarId_casesAnd___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "unexpected number of goals"};
static const lean_object* l_Lean_MVarId_casesAnd___closed__1 = (const lean_object*)&l_Lean_MVarId_casesAnd___closed__1_value;
static const lean_ctor_object l_Lean_MVarId_casesAnd___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_MVarId_casesAnd___closed__1_value)}};
static const lean_object* l_Lean_MVarId_casesAnd___closed__2 = (const lean_object*)&l_Lean_MVarId_casesAnd___closed__2_value;
static lean_once_cell_t l_Lean_MVarId_casesAnd___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_casesAnd___closed__3;
LEAN_EXPORT lean_object* l_Lean_MVarId_casesAnd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_casesAnd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_substEqs___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_substEqs___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_MVarId_substEqs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_MVarId_substEqs___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_MVarId_substEqs___closed__0 = (const lean_object*)&l_Lean_MVarId_substEqs___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_MVarId_substEqs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_substEqs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkByCasesSubgoal___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkByCasesSubgoal___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkByCasesSubgoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkByCasesSubgoal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MVarId_byCases___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "isTrue"};
static const lean_object* l_Lean_MVarId_byCases___lam__0___closed__0 = (const lean_object*)&l_Lean_MVarId_byCases___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_MVarId_byCases___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_byCases___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(125, 82, 240, 34, 69, 121, 64, 234)}};
static const lean_object* l_Lean_MVarId_byCases___lam__0___closed__1 = (const lean_object*)&l_Lean_MVarId_byCases___lam__0___closed__1_value;
static const lean_string_object l_Lean_MVarId_byCases___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "isFalse"};
static const lean_object* l_Lean_MVarId_byCases___lam__0___closed__2 = (const lean_object*)&l_Lean_MVarId_byCases___lam__0___closed__2_value;
static const lean_ctor_object l_Lean_MVarId_byCases___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_byCases___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(113, 70, 3, 12, 31, 103, 230, 247)}};
static const lean_object* l_Lean_MVarId_byCases___lam__0___closed__3 = (const lean_object*)&l_Lean_MVarId_byCases___lam__0___closed__3_value;
static const lean_string_object l_Lean_MVarId_byCases___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Classical"};
static const lean_object* l_Lean_MVarId_byCases___lam__0___closed__4 = (const lean_object*)&l_Lean_MVarId_byCases___lam__0___closed__4_value;
static const lean_string_object l_Lean_MVarId_byCases___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "byCases"};
static const lean_object* l_Lean_MVarId_byCases___lam__0___closed__5 = (const lean_object*)&l_Lean_MVarId_byCases___lam__0___closed__5_value;
static const lean_ctor_object l_Lean_MVarId_byCases___lam__0___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_byCases___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(40, 236, 220, 79, 38, 141, 161, 150)}};
static const lean_ctor_object l_Lean_MVarId_byCases___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_MVarId_byCases___lam__0___closed__6_value_aux_0),((lean_object*)&l_Lean_MVarId_byCases___lam__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(240, 75, 32, 165, 126, 243, 120, 233)}};
static const lean_object* l_Lean_MVarId_byCases___lam__0___closed__6 = (const lean_object*)&l_Lean_MVarId_byCases___lam__0___closed__6_value;
static lean_once_cell_t l_Lean_MVarId_byCases___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_byCases___lam__0___closed__7;
static const lean_ctor_object l_Lean_MVarId_byCases___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_byCases___lam__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(223, 107, 197, 37, 106, 239, 120, 82)}};
static const lean_object* l_Lean_MVarId_byCases___lam__0___closed__8 = (const lean_object*)&l_Lean_MVarId_byCases___lam__0___closed__8_value;
static const lean_string_object l_Lean_MVarId_byCases___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Goal is not a proposition"};
static const lean_object* l_Lean_MVarId_byCases___lam__0___closed__9 = (const lean_object*)&l_Lean_MVarId_byCases___lam__0___closed__9_value;
static lean_once_cell_t l_Lean_MVarId_byCases___lam__0___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_byCases___lam__0___closed__10;
static lean_once_cell_t l_Lean_MVarId_byCases___lam__0___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_byCases___lam__0___closed__11;
LEAN_EXPORT lean_object* l_Lean_MVarId_byCases___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_byCases___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_byCases(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_byCases___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MVarId_byCasesDec___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "dite"};
static const lean_object* l_Lean_MVarId_byCasesDec___lam__0___closed__0 = (const lean_object*)&l_Lean_MVarId_byCasesDec___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_MVarId_byCasesDec___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_byCasesDec___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(137, 166, 197, 161, 68, 218, 116, 116)}};
static const lean_object* l_Lean_MVarId_byCasesDec___lam__0___closed__1 = (const lean_object*)&l_Lean_MVarId_byCasesDec___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_MVarId_byCasesDec___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_byCasesDec___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_byCasesDec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_byCasesDec___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Cases_cases___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Meta_Cases_cases___lam__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value_aux_1),((lean_object*)&l_Lean_Meta_Cases_cases___closed__0_value),LEAN_SCALAR_PTR_LITERAL(57, 31, 136, 203, 40, 113, 66, 100)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_Cases_cases___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_Cases_cases___lam__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(195, 68, 87, 56, 63, 220, 109, 253)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Cases"};
static const lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(116, 214, 45, 31, 61, 84, 55, 148)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(245, 246, 165, 222, 15, 227, 90, 185)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(96, 16, 241, 169, 223, 219, 97, 222)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_Cases_cases___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(76, 206, 219, 186, 41, 249, 249, 75)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(57, 5, 31, 238, 60, 141, 136, 2)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(244, 20, 148, 166, 205, 51, 90, 243)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(245, 111, 199, 196, 219, 75, 33, 173)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_Cases_cases___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(189, 169, 211, 84, 174, 39, 78, 59)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_Cases_cases___lam__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(228, 131, 106, 227, 136, 21, 5, 171)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(63, 103, 47, 118, 16, 248, 186, 58)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected_spec__0_spec__0(lean_object* v_msgData_1_, lean_object* v___y_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_){
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected_spec__0_spec__0___boxed(lean_object* v_msgData_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected_spec__0_spec__0(v_msgData_16_, v___y_17_, v___y_18_, v___y_19_, v___y_20_);
lean_dec(v___y_20_);
lean_dec_ref(v___y_19_);
lean_dec(v___y_18_);
lean_dec_ref(v___y_17_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected_spec__0___redArg(lean_object* v_msg_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_){
_start:
{
lean_object* v_ref_29_; lean_object* v___x_30_; lean_object* v_a_31_; lean_object* v___x_33_; uint8_t v_isShared_34_; uint8_t v_isSharedCheck_39_; 
v_ref_29_ = lean_ctor_get(v___y_26_, 5);
v___x_30_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected_spec__0_spec__0(v_msg_23_, v___y_24_, v___y_25_, v___y_26_, v___y_27_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected_spec__0___redArg___boxed(lean_object* v_msg_40_, lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected_spec__0___redArg(v_msg_40_, v___y_41_, v___y_42_, v___y_43_, v___y_44_);
lean_dec(v___y_44_);
lean_dec_ref(v___y_43_);
lean_dec(v___y_42_);
lean_dec_ref(v___y_41_);
return v_res_46_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg___closed__1(void){
_start:
{
lean_object* v___x_48_; lean_object* v___x_49_; 
v___x_48_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg___closed__0));
v___x_49_ = l_Lean_stringToMessageData(v___x_48_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg(lean_object* v_type_50_, lean_object* v_a_51_, lean_object* v_a_52_, lean_object* v_a_53_, lean_object* v_a_54_){
_start:
{
lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_56_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg___closed__1, &l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg___closed__1);
v___x_57_ = l_Lean_indentExpr(v_type_50_);
v___x_58_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_58_, 0, v___x_56_);
lean_ctor_set(v___x_58_, 1, v___x_57_);
v___x_59_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected_spec__0___redArg(v___x_58_, v_a_51_, v_a_52_, v_a_53_, v_a_54_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg___boxed(lean_object* v_type_60_, lean_object* v_a_61_, lean_object* v_a_62_, lean_object* v_a_63_, lean_object* v_a_64_, lean_object* v_a_65_){
_start:
{
lean_object* v_res_66_; 
v_res_66_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg(v_type_60_, v_a_61_, v_a_62_, v_a_63_, v_a_64_);
lean_dec(v_a_64_);
lean_dec_ref(v_a_63_);
lean_dec(v_a_62_);
lean_dec_ref(v_a_61_);
return v_res_66_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected(lean_object* v_00_u03b1_67_, lean_object* v_type_68_, lean_object* v_a_69_, lean_object* v_a_70_, lean_object* v_a_71_, lean_object* v_a_72_){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg(v_type_68_, v_a_69_, v_a_70_, v_a_71_, v_a_72_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___boxed(lean_object* v_00_u03b1_75_, lean_object* v_type_76_, lean_object* v_a_77_, lean_object* v_a_78_, lean_object* v_a_79_, lean_object* v_a_80_, lean_object* v_a_81_){
_start:
{
lean_object* v_res_82_; 
v_res_82_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected(v_00_u03b1_75_, v_type_76_, v_a_77_, v_a_78_, v_a_79_, v_a_80_);
lean_dec(v_a_80_);
lean_dec_ref(v_a_79_);
lean_dec(v_a_78_);
lean_dec_ref(v_a_77_);
return v_res_82_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected_spec__0(lean_object* v_00_u03b1_83_, lean_object* v_msg_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_){
_start:
{
lean_object* v___x_90_; 
v___x_90_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected_spec__0___redArg(v_msg_84_, v___y_85_, v___y_86_, v___y_87_, v___y_88_);
return v___x_90_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected_spec__0___boxed(lean_object* v_00_u03b1_91_, lean_object* v_msg_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_){
_start:
{
lean_object* v_res_98_; 
v_res_98_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected_spec__0(v_00_u03b1_91_, v_msg_92_, v___y_93_, v___y_94_, v___y_95_, v___y_96_);
lean_dec(v___y_96_);
lean_dec_ref(v___y_95_);
lean_dec(v___y_94_);
lean_dec_ref(v___y_93_);
return v_res_98_;
}
}
static lean_object* _init_l_Lean_Meta_getInductiveUniverseAndParams___closed__0(void){
_start:
{
lean_object* v___x_99_; lean_object* v_dummy_100_; 
v___x_99_ = lean_box(0);
v_dummy_100_ = l_Lean_Expr_sort___override(v___x_99_);
return v_dummy_100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInductiveUniverseAndParams(lean_object* v_type_101_, lean_object* v_a_102_, lean_object* v_a_103_, lean_object* v_a_104_, lean_object* v_a_105_){
_start:
{
lean_object* v___x_107_; 
v___x_107_ = l_Lean_Meta_whnfD(v_type_101_, v_a_102_, v_a_103_, v_a_104_, v_a_105_);
if (lean_obj_tag(v___x_107_) == 0)
{
lean_object* v_a_108_; lean_object* v___x_110_; uint8_t v_isShared_111_; uint8_t v_isSharedCheck_137_; 
v_a_108_ = lean_ctor_get(v___x_107_, 0);
v_isSharedCheck_137_ = !lean_is_exclusive(v___x_107_);
if (v_isSharedCheck_137_ == 0)
{
v___x_110_ = v___x_107_;
v_isShared_111_ = v_isSharedCheck_137_;
goto v_resetjp_109_;
}
else
{
lean_inc(v_a_108_);
lean_dec(v___x_107_);
v___x_110_ = lean_box(0);
v_isShared_111_ = v_isSharedCheck_137_;
goto v_resetjp_109_;
}
v_resetjp_109_:
{
lean_object* v___x_112_; 
v___x_112_ = l_Lean_Expr_getAppFn(v_a_108_);
if (lean_obj_tag(v___x_112_) == 4)
{
lean_object* v_declName_113_; lean_object* v_us_114_; lean_object* v___x_115_; lean_object* v_env_116_; uint8_t v___x_117_; lean_object* v___x_118_; 
v_declName_113_ = lean_ctor_get(v___x_112_, 0);
lean_inc(v_declName_113_);
v_us_114_ = lean_ctor_get(v___x_112_, 1);
lean_inc(v_us_114_);
lean_dec_ref_known(v___x_112_, 2);
v___x_115_ = lean_st_ref_get(v_a_105_);
v_env_116_ = lean_ctor_get(v___x_115_, 0);
lean_inc_ref(v_env_116_);
lean_dec(v___x_115_);
v___x_117_ = 0;
v___x_118_ = l_Lean_Environment_find_x3f(v_env_116_, v_declName_113_, v___x_117_);
if (lean_obj_tag(v___x_118_) == 0)
{
lean_object* v___x_119_; 
lean_dec(v_us_114_);
lean_del_object(v___x_110_);
v___x_119_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg(v_a_108_, v_a_102_, v_a_103_, v_a_104_, v_a_105_);
return v___x_119_;
}
else
{
lean_object* v_val_120_; 
v_val_120_ = lean_ctor_get(v___x_118_, 0);
lean_inc(v_val_120_);
lean_dec_ref_known(v___x_118_, 1);
if (lean_obj_tag(v_val_120_) == 5)
{
lean_object* v_val_121_; lean_object* v_numParams_122_; lean_object* v_nargs_123_; lean_object* v_dummy_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_133_; 
v_val_121_ = lean_ctor_get(v_val_120_, 0);
lean_inc_ref(v_val_121_);
lean_dec_ref_known(v_val_120_, 1);
v_numParams_122_ = lean_ctor_get(v_val_121_, 1);
lean_inc(v_numParams_122_);
lean_dec_ref(v_val_121_);
v_nargs_123_ = l_Lean_Expr_getAppNumArgs(v_a_108_);
v_dummy_124_ = lean_obj_once(&l_Lean_Meta_getInductiveUniverseAndParams___closed__0, &l_Lean_Meta_getInductiveUniverseAndParams___closed__0_once, _init_l_Lean_Meta_getInductiveUniverseAndParams___closed__0);
lean_inc(v_nargs_123_);
v___x_125_ = lean_mk_array(v_nargs_123_, v_dummy_124_);
v___x_126_ = lean_unsigned_to_nat(1u);
v___x_127_ = lean_nat_sub(v_nargs_123_, v___x_126_);
lean_dec(v_nargs_123_);
v___x_128_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_108_, v___x_125_, v___x_127_);
v___x_129_ = lean_unsigned_to_nat(0u);
v___x_130_ = l_Array_extract___redArg(v___x_128_, v___x_129_, v_numParams_122_);
lean_dec_ref(v___x_128_);
v___x_131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_131_, 0, v_us_114_);
lean_ctor_set(v___x_131_, 1, v___x_130_);
if (v_isShared_111_ == 0)
{
lean_ctor_set(v___x_110_, 0, v___x_131_);
v___x_133_ = v___x_110_;
goto v_reusejp_132_;
}
else
{
lean_object* v_reuseFailAlloc_134_; 
v_reuseFailAlloc_134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_134_, 0, v___x_131_);
v___x_133_ = v_reuseFailAlloc_134_;
goto v_reusejp_132_;
}
v_reusejp_132_:
{
return v___x_133_;
}
}
else
{
lean_object* v___x_135_; 
lean_dec(v_val_120_);
lean_dec(v_us_114_);
lean_del_object(v___x_110_);
v___x_135_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg(v_a_108_, v_a_102_, v_a_103_, v_a_104_, v_a_105_);
return v___x_135_;
}
}
}
else
{
lean_object* v___x_136_; 
lean_dec_ref(v___x_112_);
lean_del_object(v___x_110_);
v___x_136_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg(v_a_108_, v_a_102_, v_a_103_, v_a_104_, v_a_105_);
return v___x_136_;
}
}
}
else
{
lean_object* v_a_138_; lean_object* v___x_140_; uint8_t v_isShared_141_; uint8_t v_isSharedCheck_145_; 
v_a_138_ = lean_ctor_get(v___x_107_, 0);
v_isSharedCheck_145_ = !lean_is_exclusive(v___x_107_);
if (v_isSharedCheck_145_ == 0)
{
v___x_140_ = v___x_107_;
v_isShared_141_ = v_isSharedCheck_145_;
goto v_resetjp_139_;
}
else
{
lean_inc(v_a_138_);
lean_dec(v___x_107_);
v___x_140_ = lean_box(0);
v_isShared_141_ = v_isSharedCheck_145_;
goto v_resetjp_139_;
}
v_resetjp_139_:
{
lean_object* v___x_143_; 
if (v_isShared_141_ == 0)
{
v___x_143_ = v___x_140_;
goto v_reusejp_142_;
}
else
{
lean_object* v_reuseFailAlloc_144_; 
v_reuseFailAlloc_144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_144_, 0, v_a_138_);
v___x_143_ = v_reuseFailAlloc_144_;
goto v_reusejp_142_;
}
v_reusejp_142_:
{
return v___x_143_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInductiveUniverseAndParams___boxed(lean_object* v_type_146_, lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_){
_start:
{
lean_object* v_res_152_; 
v_res_152_ = l_Lean_Meta_getInductiveUniverseAndParams(v_type_146_, v_a_147_, v_a_148_, v_a_149_, v_a_150_);
lean_dec(v_a_150_);
lean_dec_ref(v_a_149_);
lean_dec(v_a_148_);
lean_dec_ref(v_a_147_);
return v_res_152_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof(lean_object* v_lhs_166_, lean_object* v_rhs_167_, lean_object* v_a_168_, lean_object* v_a_169_, lean_object* v_a_170_, lean_object* v_a_171_){
_start:
{
lean_object* v___x_173_; 
lean_inc(v_a_171_);
lean_inc_ref(v_a_170_);
lean_inc(v_a_169_);
lean_inc_ref(v_a_168_);
lean_inc_ref(v_lhs_166_);
v___x_173_ = lean_infer_type(v_lhs_166_, v_a_168_, v_a_169_, v_a_170_, v_a_171_);
if (lean_obj_tag(v___x_173_) == 0)
{
lean_object* v_a_174_; lean_object* v___x_175_; 
v_a_174_ = lean_ctor_get(v___x_173_, 0);
lean_inc(v_a_174_);
lean_dec_ref_known(v___x_173_, 1);
lean_inc(v_a_171_);
lean_inc_ref(v_a_170_);
lean_inc(v_a_169_);
lean_inc_ref(v_a_168_);
lean_inc_ref(v_rhs_167_);
v___x_175_ = lean_infer_type(v_rhs_167_, v_a_168_, v_a_169_, v_a_170_, v_a_171_);
if (lean_obj_tag(v___x_175_) == 0)
{
lean_object* v_a_176_; lean_object* v___x_177_; 
v_a_176_ = lean_ctor_get(v___x_175_, 0);
lean_inc(v_a_176_);
lean_dec_ref_known(v___x_175_, 1);
lean_inc(v_a_174_);
v___x_177_ = l_Lean_Meta_getLevel(v_a_174_, v_a_168_, v_a_169_, v_a_170_, v_a_171_);
if (lean_obj_tag(v___x_177_) == 0)
{
lean_object* v_a_178_; lean_object* v___x_179_; 
v_a_178_ = lean_ctor_get(v___x_177_, 0);
lean_inc(v_a_178_);
lean_dec_ref_known(v___x_177_, 1);
lean_inc(v_a_176_);
lean_inc(v_a_174_);
v___x_179_ = l_Lean_Meta_isExprDefEq(v_a_174_, v_a_176_, v_a_168_, v_a_169_, v_a_170_, v_a_171_);
if (lean_obj_tag(v___x_179_) == 0)
{
lean_object* v_a_180_; lean_object* v___x_182_; uint8_t v_isShared_183_; uint8_t v_isSharedCheck_209_; 
v_a_180_ = lean_ctor_get(v___x_179_, 0);
v_isSharedCheck_209_ = !lean_is_exclusive(v___x_179_);
if (v_isSharedCheck_209_ == 0)
{
v___x_182_ = v___x_179_;
v_isShared_183_ = v_isSharedCheck_209_;
goto v_resetjp_181_;
}
else
{
lean_inc(v_a_180_);
lean_dec(v___x_179_);
v___x_182_ = lean_box(0);
v_isShared_183_ = v_isSharedCheck_209_;
goto v_resetjp_181_;
}
v_resetjp_181_:
{
uint8_t v___x_184_; 
v___x_184_ = lean_unbox(v_a_180_);
lean_dec(v_a_180_);
if (v___x_184_ == 0)
{
lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_195_; 
v___x_185_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__1));
v___x_186_ = lean_box(0);
v___x_187_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_187_, 0, v_a_178_);
lean_ctor_set(v___x_187_, 1, v___x_186_);
lean_inc_ref(v___x_187_);
v___x_188_ = l_Lean_mkConst(v___x_185_, v___x_187_);
lean_inc_ref(v_lhs_166_);
lean_inc(v_a_174_);
v___x_189_ = l_Lean_mkApp4(v___x_188_, v_a_174_, v_lhs_166_, v_a_176_, v_rhs_167_);
v___x_190_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__3));
v___x_191_ = l_Lean_mkConst(v___x_190_, v___x_187_);
v___x_192_ = l_Lean_mkAppB(v___x_191_, v_a_174_, v_lhs_166_);
v___x_193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_193_, 0, v___x_189_);
lean_ctor_set(v___x_193_, 1, v___x_192_);
if (v_isShared_183_ == 0)
{
lean_ctor_set(v___x_182_, 0, v___x_193_);
v___x_195_ = v___x_182_;
goto v_reusejp_194_;
}
else
{
lean_object* v_reuseFailAlloc_196_; 
v_reuseFailAlloc_196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_196_, 0, v___x_193_);
v___x_195_ = v_reuseFailAlloc_196_;
goto v_reusejp_194_;
}
v_reusejp_194_:
{
return v___x_195_;
}
}
else
{
lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_207_; 
lean_dec(v_a_176_);
v___x_197_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__5));
v___x_198_ = lean_box(0);
v___x_199_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_199_, 0, v_a_178_);
lean_ctor_set(v___x_199_, 1, v___x_198_);
lean_inc_ref(v___x_199_);
v___x_200_ = l_Lean_mkConst(v___x_197_, v___x_199_);
lean_inc_ref(v_lhs_166_);
lean_inc(v_a_174_);
v___x_201_ = l_Lean_mkApp3(v___x_200_, v_a_174_, v_lhs_166_, v_rhs_167_);
v___x_202_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__6));
v___x_203_ = l_Lean_mkConst(v___x_202_, v___x_199_);
v___x_204_ = l_Lean_mkAppB(v___x_203_, v_a_174_, v_lhs_166_);
v___x_205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_205_, 0, v___x_201_);
lean_ctor_set(v___x_205_, 1, v___x_204_);
if (v_isShared_183_ == 0)
{
lean_ctor_set(v___x_182_, 0, v___x_205_);
v___x_207_ = v___x_182_;
goto v_reusejp_206_;
}
else
{
lean_object* v_reuseFailAlloc_208_; 
v_reuseFailAlloc_208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_208_, 0, v___x_205_);
v___x_207_ = v_reuseFailAlloc_208_;
goto v_reusejp_206_;
}
v_reusejp_206_:
{
return v___x_207_;
}
}
}
}
else
{
lean_object* v_a_210_; lean_object* v___x_212_; uint8_t v_isShared_213_; uint8_t v_isSharedCheck_217_; 
lean_dec(v_a_178_);
lean_dec(v_a_176_);
lean_dec(v_a_174_);
lean_dec_ref(v_rhs_167_);
lean_dec_ref(v_lhs_166_);
v_a_210_ = lean_ctor_get(v___x_179_, 0);
v_isSharedCheck_217_ = !lean_is_exclusive(v___x_179_);
if (v_isSharedCheck_217_ == 0)
{
v___x_212_ = v___x_179_;
v_isShared_213_ = v_isSharedCheck_217_;
goto v_resetjp_211_;
}
else
{
lean_inc(v_a_210_);
lean_dec(v___x_179_);
v___x_212_ = lean_box(0);
v_isShared_213_ = v_isSharedCheck_217_;
goto v_resetjp_211_;
}
v_resetjp_211_:
{
lean_object* v___x_215_; 
if (v_isShared_213_ == 0)
{
v___x_215_ = v___x_212_;
goto v_reusejp_214_;
}
else
{
lean_object* v_reuseFailAlloc_216_; 
v_reuseFailAlloc_216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_216_, 0, v_a_210_);
v___x_215_ = v_reuseFailAlloc_216_;
goto v_reusejp_214_;
}
v_reusejp_214_:
{
return v___x_215_;
}
}
}
}
else
{
lean_object* v_a_218_; lean_object* v___x_220_; uint8_t v_isShared_221_; uint8_t v_isSharedCheck_225_; 
lean_dec(v_a_176_);
lean_dec(v_a_174_);
lean_dec_ref(v_rhs_167_);
lean_dec_ref(v_lhs_166_);
v_a_218_ = lean_ctor_get(v___x_177_, 0);
v_isSharedCheck_225_ = !lean_is_exclusive(v___x_177_);
if (v_isSharedCheck_225_ == 0)
{
v___x_220_ = v___x_177_;
v_isShared_221_ = v_isSharedCheck_225_;
goto v_resetjp_219_;
}
else
{
lean_inc(v_a_218_);
lean_dec(v___x_177_);
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
}
else
{
lean_object* v_a_226_; lean_object* v___x_228_; uint8_t v_isShared_229_; uint8_t v_isSharedCheck_233_; 
lean_dec(v_a_174_);
lean_dec_ref(v_rhs_167_);
lean_dec_ref(v_lhs_166_);
v_a_226_ = lean_ctor_get(v___x_175_, 0);
v_isSharedCheck_233_ = !lean_is_exclusive(v___x_175_);
if (v_isSharedCheck_233_ == 0)
{
v___x_228_ = v___x_175_;
v_isShared_229_ = v_isSharedCheck_233_;
goto v_resetjp_227_;
}
else
{
lean_inc(v_a_226_);
lean_dec(v___x_175_);
v___x_228_ = lean_box(0);
v_isShared_229_ = v_isSharedCheck_233_;
goto v_resetjp_227_;
}
v_resetjp_227_:
{
lean_object* v___x_231_; 
if (v_isShared_229_ == 0)
{
v___x_231_ = v___x_228_;
goto v_reusejp_230_;
}
else
{
lean_object* v_reuseFailAlloc_232_; 
v_reuseFailAlloc_232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_232_, 0, v_a_226_);
v___x_231_ = v_reuseFailAlloc_232_;
goto v_reusejp_230_;
}
v_reusejp_230_:
{
return v___x_231_;
}
}
}
}
else
{
lean_object* v_a_234_; lean_object* v___x_236_; uint8_t v_isShared_237_; uint8_t v_isSharedCheck_241_; 
lean_dec_ref(v_rhs_167_);
lean_dec_ref(v_lhs_166_);
v_a_234_ = lean_ctor_get(v___x_173_, 0);
v_isSharedCheck_241_ = !lean_is_exclusive(v___x_173_);
if (v_isSharedCheck_241_ == 0)
{
v___x_236_ = v___x_173_;
v_isShared_237_ = v_isSharedCheck_241_;
goto v_resetjp_235_;
}
else
{
lean_inc(v_a_234_);
lean_dec(v___x_173_);
v___x_236_ = lean_box(0);
v_isShared_237_ = v_isSharedCheck_241_;
goto v_resetjp_235_;
}
v_resetjp_235_:
{
lean_object* v___x_239_; 
if (v_isShared_237_ == 0)
{
v___x_239_ = v___x_236_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v_a_234_);
v___x_239_ = v_reuseFailAlloc_240_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
return v___x_239_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___boxed(lean_object* v_lhs_242_, lean_object* v_rhs_243_, lean_object* v_a_244_, lean_object* v_a_245_, lean_object* v_a_246_, lean_object* v_a_247_, lean_object* v_a_248_){
_start:
{
lean_object* v_res_249_; 
v_res_249_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof(v_lhs_242_, v_rhs_243_, v_a_244_, v_a_245_, v_a_246_, v_a_247_);
lean_dec(v_a_247_);
lean_dec_ref(v_a_246_);
lean_dec(v_a_245_);
lean_dec_ref(v_a_244_);
return v_res_249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0_spec__0___redArg___lam__0(lean_object* v_k_250_, lean_object* v_b_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_){
_start:
{
lean_object* v___x_257_; 
lean_inc(v___y_255_);
lean_inc_ref(v___y_254_);
lean_inc(v___y_253_);
lean_inc_ref(v___y_252_);
v___x_257_ = lean_apply_6(v_k_250_, v_b_251_, v___y_252_, v___y_253_, v___y_254_, v___y_255_, lean_box(0));
return v___x_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_k_258_, lean_object* v_b_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_){
_start:
{
lean_object* v_res_265_; 
v_res_265_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0_spec__0___redArg___lam__0(v_k_258_, v_b_259_, v___y_260_, v___y_261_, v___y_262_, v___y_263_);
lean_dec(v___y_263_);
lean_dec_ref(v___y_262_);
lean_dec(v___y_261_);
lean_dec_ref(v___y_260_);
return v_res_265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0_spec__0___redArg(lean_object* v_name_266_, uint8_t v_bi_267_, lean_object* v_type_268_, lean_object* v_k_269_, uint8_t v_kind_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_){
_start:
{
lean_object* v___f_276_; lean_object* v___x_277_; 
v___f_276_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0_spec__0___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_276_, 0, v_k_269_);
v___x_277_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_266_, v_bi_267_, v_type_268_, v___f_276_, v_kind_270_, v___y_271_, v___y_272_, v___y_273_, v___y_274_);
if (lean_obj_tag(v___x_277_) == 0)
{
lean_object* v_a_278_; lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_285_; 
v_a_278_ = lean_ctor_get(v___x_277_, 0);
v_isSharedCheck_285_ = !lean_is_exclusive(v___x_277_);
if (v_isSharedCheck_285_ == 0)
{
v___x_280_ = v___x_277_;
v_isShared_281_ = v_isSharedCheck_285_;
goto v_resetjp_279_;
}
else
{
lean_inc(v_a_278_);
lean_dec(v___x_277_);
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_285_;
goto v_resetjp_279_;
}
v_resetjp_279_:
{
lean_object* v___x_283_; 
if (v_isShared_281_ == 0)
{
v___x_283_ = v___x_280_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_284_; 
v_reuseFailAlloc_284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_284_, 0, v_a_278_);
v___x_283_ = v_reuseFailAlloc_284_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
return v___x_283_;
}
}
}
else
{
lean_object* v_a_286_; lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_293_; 
v_a_286_ = lean_ctor_get(v___x_277_, 0);
v_isSharedCheck_293_ = !lean_is_exclusive(v___x_277_);
if (v_isSharedCheck_293_ == 0)
{
v___x_288_ = v___x_277_;
v_isShared_289_ = v_isSharedCheck_293_;
goto v_resetjp_287_;
}
else
{
lean_inc(v_a_286_);
lean_dec(v___x_277_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0_spec__0___redArg___boxed(lean_object* v_name_294_, lean_object* v_bi_295_, lean_object* v_type_296_, lean_object* v_k_297_, lean_object* v_kind_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_){
_start:
{
uint8_t v_bi_boxed_304_; uint8_t v_kind_boxed_305_; lean_object* v_res_306_; 
v_bi_boxed_304_ = lean_unbox(v_bi_295_);
v_kind_boxed_305_ = lean_unbox(v_kind_298_);
v_res_306_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0_spec__0___redArg(v_name_294_, v_bi_boxed_304_, v_type_296_, v_k_297_, v_kind_boxed_305_, v___y_299_, v___y_300_, v___y_301_, v___y_302_);
lean_dec(v___y_302_);
lean_dec_ref(v___y_301_);
lean_dec(v___y_300_);
lean_dec_ref(v___y_299_);
return v_res_306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0___redArg(lean_object* v_name_307_, lean_object* v_type_308_, lean_object* v_k_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_){
_start:
{
uint8_t v___x_315_; uint8_t v___x_316_; lean_object* v___x_317_; 
v___x_315_ = 0;
v___x_316_ = 0;
v___x_317_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0_spec__0___redArg(v_name_307_, v___x_315_, v_type_308_, v_k_309_, v___x_316_, v___y_310_, v___y_311_, v___y_312_, v___y_313_);
return v___x_317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0___redArg___boxed(lean_object* v_name_318_, lean_object* v_type_319_, lean_object* v_k_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_){
_start:
{
lean_object* v_res_326_; 
v_res_326_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0___redArg(v_name_318_, v_type_319_, v_k_320_, v___y_321_, v___y_322_, v___y_323_, v___y_324_);
lean_dec(v___y_324_);
lean_dec_ref(v___y_323_);
lean_dec(v___y_322_);
lean_dec_ref(v___y_321_);
return v_res_326_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___redArg___lam__0___boxed(lean_object* v_i_327_, lean_object* v_newEqs_328_, lean_object* v_newRefls_329_, lean_object* v_snd_330_, lean_object* v_targets_331_, lean_object* v_targetsNew_332_, lean_object* v_k_333_, lean_object* v_newEq_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_){
_start:
{
lean_object* v_res_340_; 
v_res_340_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___redArg___lam__0(v_i_327_, v_newEqs_328_, v_newRefls_329_, v_snd_330_, v_targets_331_, v_targetsNew_332_, v_k_333_, v_newEq_334_, v___y_335_, v___y_336_, v___y_337_, v___y_338_);
lean_dec(v___y_338_);
lean_dec_ref(v___y_337_);
lean_dec(v___y_336_);
lean_dec_ref(v___y_335_);
lean_dec(v_i_327_);
return v_res_340_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___redArg(lean_object* v_targets_344_, lean_object* v_targetsNew_345_, lean_object* v_k_346_, lean_object* v_i_347_, lean_object* v_newEqs_348_, lean_object* v_newRefls_349_, lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_a_353_){
_start:
{
lean_object* v___x_355_; uint8_t v___x_356_; 
v___x_355_ = lean_array_get_size(v_targets_344_);
v___x_356_ = lean_nat_dec_lt(v_i_347_, v___x_355_);
if (v___x_356_ == 0)
{
lean_object* v___x_357_; 
lean_dec(v_i_347_);
lean_dec_ref(v_targetsNew_345_);
lean_dec_ref(v_targets_344_);
lean_inc(v_a_353_);
lean_inc_ref(v_a_352_);
lean_inc(v_a_351_);
lean_inc_ref(v_a_350_);
v___x_357_ = lean_apply_7(v_k_346_, v_newEqs_348_, v_newRefls_349_, v_a_350_, v_a_351_, v_a_352_, v_a_353_, lean_box(0));
return v___x_357_;
}
else
{
lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_358_ = l_Lean_instInhabitedExpr;
v___x_359_ = lean_array_get_borrowed(v___x_358_, v_targets_344_, v_i_347_);
v___x_360_ = lean_array_get_borrowed(v___x_358_, v_targetsNew_345_, v_i_347_);
lean_inc(v___x_360_);
lean_inc(v___x_359_);
v___x_361_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof(v___x_359_, v___x_360_, v_a_350_, v_a_351_, v_a_352_, v_a_353_);
if (lean_obj_tag(v___x_361_) == 0)
{
lean_object* v_a_362_; lean_object* v_fst_363_; lean_object* v_snd_364_; lean_object* v___f_365_; lean_object* v___x_366_; lean_object* v___x_367_; 
v_a_362_ = lean_ctor_get(v___x_361_, 0);
lean_inc(v_a_362_);
lean_dec_ref_known(v___x_361_, 1);
v_fst_363_ = lean_ctor_get(v_a_362_, 0);
lean_inc(v_fst_363_);
v_snd_364_ = lean_ctor_get(v_a_362_, 1);
lean_inc(v_snd_364_);
lean_dec(v_a_362_);
v___f_365_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___redArg___lam__0___boxed), 13, 7);
lean_closure_set(v___f_365_, 0, v_i_347_);
lean_closure_set(v___f_365_, 1, v_newEqs_348_);
lean_closure_set(v___f_365_, 2, v_newRefls_349_);
lean_closure_set(v___f_365_, 3, v_snd_364_);
lean_closure_set(v___f_365_, 4, v_targets_344_);
lean_closure_set(v___f_365_, 5, v_targetsNew_345_);
lean_closure_set(v___f_365_, 6, v_k_346_);
v___x_366_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___redArg___closed__1));
v___x_367_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0___redArg(v___x_366_, v_fst_363_, v___f_365_, v_a_350_, v_a_351_, v_a_352_, v_a_353_);
return v___x_367_;
}
else
{
lean_object* v_a_368_; lean_object* v___x_370_; uint8_t v_isShared_371_; uint8_t v_isSharedCheck_375_; 
lean_dec_ref(v_newRefls_349_);
lean_dec_ref(v_newEqs_348_);
lean_dec(v_i_347_);
lean_dec_ref(v_k_346_);
lean_dec_ref(v_targetsNew_345_);
lean_dec_ref(v_targets_344_);
v_a_368_ = lean_ctor_get(v___x_361_, 0);
v_isSharedCheck_375_ = !lean_is_exclusive(v___x_361_);
if (v_isSharedCheck_375_ == 0)
{
v___x_370_ = v___x_361_;
v_isShared_371_ = v_isSharedCheck_375_;
goto v_resetjp_369_;
}
else
{
lean_inc(v_a_368_);
lean_dec(v___x_361_);
v___x_370_ = lean_box(0);
v_isShared_371_ = v_isSharedCheck_375_;
goto v_resetjp_369_;
}
v_resetjp_369_:
{
lean_object* v___x_373_; 
if (v_isShared_371_ == 0)
{
v___x_373_ = v___x_370_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v_a_368_);
v___x_373_ = v_reuseFailAlloc_374_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
return v___x_373_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___redArg___lam__0(lean_object* v_i_376_, lean_object* v_newEqs_377_, lean_object* v_newRefls_378_, lean_object* v_snd_379_, lean_object* v_targets_380_, lean_object* v_targetsNew_381_, lean_object* v_k_382_, lean_object* v_newEq_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_){
_start:
{
lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; 
v___x_389_ = lean_unsigned_to_nat(1u);
v___x_390_ = lean_nat_add(v_i_376_, v___x_389_);
v___x_391_ = lean_array_push(v_newEqs_377_, v_newEq_383_);
v___x_392_ = lean_array_push(v_newRefls_378_, v_snd_379_);
v___x_393_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___redArg(v_targets_380_, v_targetsNew_381_, v_k_382_, v___x_390_, v___x_391_, v___x_392_, v___y_384_, v___y_385_, v___y_386_, v___y_387_);
return v___x_393_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___redArg___boxed(lean_object* v_targets_394_, lean_object* v_targetsNew_395_, lean_object* v_k_396_, lean_object* v_i_397_, lean_object* v_newEqs_398_, lean_object* v_newRefls_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_){
_start:
{
lean_object* v_res_405_; 
v_res_405_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___redArg(v_targets_394_, v_targetsNew_395_, v_k_396_, v_i_397_, v_newEqs_398_, v_newRefls_399_, v_a_400_, v_a_401_, v_a_402_, v_a_403_);
lean_dec(v_a_403_);
lean_dec_ref(v_a_402_);
lean_dec(v_a_401_);
lean_dec_ref(v_a_400_);
return v_res_405_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop(lean_object* v_00_u03b1_406_, lean_object* v_targets_407_, lean_object* v_targetsNew_408_, lean_object* v_k_409_, lean_object* v_i_410_, lean_object* v_newEqs_411_, lean_object* v_newRefls_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_){
_start:
{
lean_object* v___x_418_; 
v___x_418_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___redArg(v_targets_407_, v_targetsNew_408_, v_k_409_, v_i_410_, v_newEqs_411_, v_newRefls_412_, v_a_413_, v_a_414_, v_a_415_, v_a_416_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___boxed(lean_object* v_00_u03b1_419_, lean_object* v_targets_420_, lean_object* v_targetsNew_421_, lean_object* v_k_422_, lean_object* v_i_423_, lean_object* v_newEqs_424_, lean_object* v_newRefls_425_, lean_object* v_a_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_){
_start:
{
lean_object* v_res_431_; 
v_res_431_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop(v_00_u03b1_419_, v_targets_420_, v_targetsNew_421_, v_k_422_, v_i_423_, v_newEqs_424_, v_newRefls_425_, v_a_426_, v_a_427_, v_a_428_, v_a_429_);
lean_dec(v_a_429_);
lean_dec_ref(v_a_428_);
lean_dec(v_a_427_);
lean_dec_ref(v_a_426_);
return v_res_431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0_spec__0(lean_object* v_00_u03b1_432_, lean_object* v_name_433_, uint8_t v_bi_434_, lean_object* v_type_435_, lean_object* v_k_436_, uint8_t v_kind_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_){
_start:
{
lean_object* v___x_443_; 
v___x_443_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0_spec__0___redArg(v_name_433_, v_bi_434_, v_type_435_, v_k_436_, v_kind_437_, v___y_438_, v___y_439_, v___y_440_, v___y_441_);
return v___x_443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0_spec__0___boxed(lean_object* v_00_u03b1_444_, lean_object* v_name_445_, lean_object* v_bi_446_, lean_object* v_type_447_, lean_object* v_k_448_, lean_object* v_kind_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_){
_start:
{
uint8_t v_bi_boxed_455_; uint8_t v_kind_boxed_456_; lean_object* v_res_457_; 
v_bi_boxed_455_ = lean_unbox(v_bi_446_);
v_kind_boxed_456_ = lean_unbox(v_kind_449_);
v_res_457_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0_spec__0(v_00_u03b1_444_, v_name_445_, v_bi_boxed_455_, v_type_447_, v_k_448_, v_kind_boxed_456_, v___y_450_, v___y_451_, v___y_452_, v___y_453_);
lean_dec(v___y_453_);
lean_dec_ref(v___y_452_);
lean_dec(v___y_451_);
lean_dec_ref(v___y_450_);
return v_res_457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0(lean_object* v_00_u03b1_458_, lean_object* v_name_459_, lean_object* v_type_460_, lean_object* v_k_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_){
_start:
{
lean_object* v___x_467_; 
v___x_467_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0___redArg(v_name_459_, v_type_460_, v_k_461_, v___y_462_, v___y_463_, v___y_464_, v___y_465_);
return v___x_467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0___boxed(lean_object* v_00_u03b1_468_, lean_object* v_name_469_, lean_object* v_type_470_, lean_object* v_k_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_){
_start:
{
lean_object* v_res_477_; 
v_res_477_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0(v_00_u03b1_468_, v_name_469_, v_type_470_, v_k_471_, v___y_472_, v___y_473_, v___y_474_, v___y_475_);
lean_dec(v___y_475_);
lean_dec_ref(v___y_474_);
lean_dec(v___y_473_);
lean_dec_ref(v___y_472_);
return v_res_477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewEqs___redArg(lean_object* v_targets_480_, lean_object* v_targetsNew_481_, lean_object* v_k_482_, lean_object* v_a_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_){
_start:
{
lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_488_ = lean_unsigned_to_nat(0u);
v___x_489_ = ((lean_object*)(l_Lean_Meta_withNewEqs___redArg___closed__0));
v___x_490_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___redArg(v_targets_480_, v_targetsNew_481_, v_k_482_, v___x_488_, v___x_489_, v___x_489_, v_a_483_, v_a_484_, v_a_485_, v_a_486_);
return v___x_490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewEqs___redArg___boxed(lean_object* v_targets_491_, lean_object* v_targetsNew_492_, lean_object* v_k_493_, lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_, lean_object* v_a_497_, lean_object* v_a_498_){
_start:
{
lean_object* v_res_499_; 
v_res_499_ = l_Lean_Meta_withNewEqs___redArg(v_targets_491_, v_targetsNew_492_, v_k_493_, v_a_494_, v_a_495_, v_a_496_, v_a_497_);
lean_dec(v_a_497_);
lean_dec_ref(v_a_496_);
lean_dec(v_a_495_);
lean_dec_ref(v_a_494_);
return v_res_499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewEqs(lean_object* v_00_u03b1_500_, lean_object* v_targets_501_, lean_object* v_targetsNew_502_, lean_object* v_k_503_, lean_object* v_a_504_, lean_object* v_a_505_, lean_object* v_a_506_, lean_object* v_a_507_){
_start:
{
lean_object* v___x_509_; 
v___x_509_ = l_Lean_Meta_withNewEqs___redArg(v_targets_501_, v_targetsNew_502_, v_k_503_, v_a_504_, v_a_505_, v_a_506_, v_a_507_);
return v___x_509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewEqs___boxed(lean_object* v_00_u03b1_510_, lean_object* v_targets_511_, lean_object* v_targetsNew_512_, lean_object* v_k_513_, lean_object* v_a_514_, lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v_a_517_, lean_object* v_a_518_){
_start:
{
lean_object* v_res_519_; 
v_res_519_ = l_Lean_Meta_withNewEqs(v_00_u03b1_510_, v_targets_511_, v_targetsNew_512_, v_k_513_, v_a_514_, v_a_515_, v_a_516_, v_a_517_);
lean_dec(v_a_517_);
lean_dec_ref(v_a_516_);
lean_dec(v_a_515_);
lean_dec_ref(v_a_514_);
return v_res_519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_generalizeTargetsEq_spec__0___redArg___lam__0(lean_object* v_k_520_, lean_object* v_b_521_, lean_object* v_c_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_){
_start:
{
lean_object* v___x_528_; 
lean_inc(v___y_526_);
lean_inc_ref(v___y_525_);
lean_inc(v___y_524_);
lean_inc_ref(v___y_523_);
v___x_528_ = lean_apply_7(v_k_520_, v_b_521_, v_c_522_, v___y_523_, v___y_524_, v___y_525_, v___y_526_, lean_box(0));
return v___x_528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_generalizeTargetsEq_spec__0___redArg___lam__0___boxed(lean_object* v_k_529_, lean_object* v_b_530_, lean_object* v_c_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_){
_start:
{
lean_object* v_res_537_; 
v_res_537_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_generalizeTargetsEq_spec__0___redArg___lam__0(v_k_529_, v_b_530_, v_c_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_);
lean_dec(v___y_535_);
lean_dec_ref(v___y_534_);
lean_dec(v___y_533_);
lean_dec_ref(v___y_532_);
return v_res_537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_generalizeTargetsEq_spec__0___redArg(lean_object* v_type_538_, lean_object* v_k_539_, uint8_t v_cleanupAnnotations_540_, uint8_t v_whnfType_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_){
_start:
{
lean_object* v___f_547_; lean_object* v___x_548_; 
v___f_547_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_generalizeTargetsEq_spec__0___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_547_, 0, v_k_539_);
v___x_548_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_538_, v___f_547_, v_cleanupAnnotations_540_, v_whnfType_541_, v___y_542_, v___y_543_, v___y_544_, v___y_545_);
if (lean_obj_tag(v___x_548_) == 0)
{
lean_object* v_a_549_; lean_object* v___x_551_; uint8_t v_isShared_552_; uint8_t v_isSharedCheck_556_; 
v_a_549_ = lean_ctor_get(v___x_548_, 0);
v_isSharedCheck_556_ = !lean_is_exclusive(v___x_548_);
if (v_isSharedCheck_556_ == 0)
{
v___x_551_ = v___x_548_;
v_isShared_552_ = v_isSharedCheck_556_;
goto v_resetjp_550_;
}
else
{
lean_inc(v_a_549_);
lean_dec(v___x_548_);
v___x_551_ = lean_box(0);
v_isShared_552_ = v_isSharedCheck_556_;
goto v_resetjp_550_;
}
v_resetjp_550_:
{
lean_object* v___x_554_; 
if (v_isShared_552_ == 0)
{
v___x_554_ = v___x_551_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v_a_549_);
v___x_554_ = v_reuseFailAlloc_555_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
return v___x_554_;
}
}
}
else
{
lean_object* v_a_557_; lean_object* v___x_559_; uint8_t v_isShared_560_; uint8_t v_isSharedCheck_564_; 
v_a_557_ = lean_ctor_get(v___x_548_, 0);
v_isSharedCheck_564_ = !lean_is_exclusive(v___x_548_);
if (v_isSharedCheck_564_ == 0)
{
v___x_559_ = v___x_548_;
v_isShared_560_ = v_isSharedCheck_564_;
goto v_resetjp_558_;
}
else
{
lean_inc(v_a_557_);
lean_dec(v___x_548_);
v___x_559_ = lean_box(0);
v_isShared_560_ = v_isSharedCheck_564_;
goto v_resetjp_558_;
}
v_resetjp_558_:
{
lean_object* v___x_562_; 
if (v_isShared_560_ == 0)
{
v___x_562_ = v___x_559_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v_a_557_);
v___x_562_ = v_reuseFailAlloc_563_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
return v___x_562_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_generalizeTargetsEq_spec__0___redArg___boxed(lean_object* v_type_565_, lean_object* v_k_566_, lean_object* v_cleanupAnnotations_567_, lean_object* v_whnfType_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_574_; uint8_t v_whnfType_boxed_575_; lean_object* v_res_576_; 
v_cleanupAnnotations_boxed_574_ = lean_unbox(v_cleanupAnnotations_567_);
v_whnfType_boxed_575_ = lean_unbox(v_whnfType_568_);
v_res_576_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_generalizeTargetsEq_spec__0___redArg(v_type_565_, v_k_566_, v_cleanupAnnotations_boxed_574_, v_whnfType_boxed_575_, v___y_569_, v___y_570_, v___y_571_, v___y_572_);
lean_dec(v___y_572_);
lean_dec_ref(v___y_571_);
lean_dec(v___y_570_);
lean_dec_ref(v___y_569_);
return v_res_576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_generalizeTargetsEq_spec__0(lean_object* v_00_u03b1_577_, lean_object* v_type_578_, lean_object* v_k_579_, uint8_t v_cleanupAnnotations_580_, uint8_t v_whnfType_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_){
_start:
{
lean_object* v___x_587_; 
v___x_587_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_generalizeTargetsEq_spec__0___redArg(v_type_578_, v_k_579_, v_cleanupAnnotations_580_, v_whnfType_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_);
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_generalizeTargetsEq_spec__0___boxed(lean_object* v_00_u03b1_588_, lean_object* v_type_589_, lean_object* v_k_590_, lean_object* v_cleanupAnnotations_591_, lean_object* v_whnfType_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_598_; uint8_t v_whnfType_boxed_599_; lean_object* v_res_600_; 
v_cleanupAnnotations_boxed_598_ = lean_unbox(v_cleanupAnnotations_591_);
v_whnfType_boxed_599_ = lean_unbox(v_whnfType_592_);
v_res_600_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_generalizeTargetsEq_spec__0(v_00_u03b1_588_, v_type_589_, v_k_590_, v_cleanupAnnotations_boxed_598_, v_whnfType_boxed_599_, v___y_593_, v___y_594_, v___y_595_, v___y_596_);
lean_dec(v___y_596_);
lean_dec_ref(v___y_595_);
lean_dec(v___y_594_);
lean_dec_ref(v___y_593_);
return v_res_600_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2___redArg(lean_object* v_mvarId_601_, lean_object* v_x_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_){
_start:
{
lean_object* v___x_608_; 
v___x_608_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_601_, v_x_602_, v___y_603_, v___y_604_, v___y_605_, v___y_606_);
if (lean_obj_tag(v___x_608_) == 0)
{
lean_object* v_a_609_; lean_object* v___x_611_; uint8_t v_isShared_612_; uint8_t v_isSharedCheck_616_; 
v_a_609_ = lean_ctor_get(v___x_608_, 0);
v_isSharedCheck_616_ = !lean_is_exclusive(v___x_608_);
if (v_isSharedCheck_616_ == 0)
{
v___x_611_ = v___x_608_;
v_isShared_612_ = v_isSharedCheck_616_;
goto v_resetjp_610_;
}
else
{
lean_inc(v_a_609_);
lean_dec(v___x_608_);
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
v_reuseFailAlloc_615_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_617_; lean_object* v___x_619_; uint8_t v_isShared_620_; uint8_t v_isSharedCheck_624_; 
v_a_617_ = lean_ctor_get(v___x_608_, 0);
v_isSharedCheck_624_ = !lean_is_exclusive(v___x_608_);
if (v_isSharedCheck_624_ == 0)
{
v___x_619_ = v___x_608_;
v_isShared_620_ = v_isSharedCheck_624_;
goto v_resetjp_618_;
}
else
{
lean_inc(v_a_617_);
lean_dec(v___x_608_);
v___x_619_ = lean_box(0);
v_isShared_620_ = v_isSharedCheck_624_;
goto v_resetjp_618_;
}
v_resetjp_618_:
{
lean_object* v___x_622_; 
if (v_isShared_620_ == 0)
{
v___x_622_ = v___x_619_;
goto v_reusejp_621_;
}
else
{
lean_object* v_reuseFailAlloc_623_; 
v_reuseFailAlloc_623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_623_, 0, v_a_617_);
v___x_622_ = v_reuseFailAlloc_623_;
goto v_reusejp_621_;
}
v_reusejp_621_:
{
return v___x_622_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2___redArg___boxed(lean_object* v_mvarId_625_, lean_object* v_x_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_){
_start:
{
lean_object* v_res_632_; 
v_res_632_ = l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2___redArg(v_mvarId_625_, v_x_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_);
lean_dec(v___y_630_);
lean_dec_ref(v___y_629_);
lean_dec(v___y_628_);
lean_dec_ref(v___y_627_);
return v_res_632_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2(lean_object* v_00_u03b1_633_, lean_object* v_mvarId_634_, lean_object* v_x_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_){
_start:
{
lean_object* v___x_641_; 
v___x_641_ = l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2___redArg(v_mvarId_634_, v_x_635_, v___y_636_, v___y_637_, v___y_638_, v___y_639_);
return v___x_641_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2___boxed(lean_object* v_00_u03b1_642_, lean_object* v_mvarId_643_, lean_object* v_x_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_){
_start:
{
lean_object* v_res_650_; 
v_res_650_ = l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2(v_00_u03b1_642_, v_mvarId_643_, v_x_644_, v___y_645_, v___y_646_, v___y_647_, v___y_648_);
lean_dec(v___y_648_);
lean_dec_ref(v___y_647_);
lean_dec(v___y_646_);
lean_dec_ref(v___y_645_);
return v_res_650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeTargetsEq___lam__0(lean_object* v_mvarId_651_, lean_object* v___x_652_, lean_object* v_eqs_653_, lean_object* v_eqRefls_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_){
_start:
{
lean_object* v___x_660_; 
v___x_660_ = l_Lean_MVarId_getType(v_mvarId_651_, v___y_655_, v___y_656_, v___y_657_, v___y_658_);
if (lean_obj_tag(v___x_660_) == 0)
{
lean_object* v_a_661_; uint8_t v___x_662_; uint8_t v___x_663_; uint8_t v___x_664_; lean_object* v___x_665_; 
v_a_661_ = lean_ctor_get(v___x_660_, 0);
lean_inc(v_a_661_);
lean_dec_ref_known(v___x_660_, 1);
v___x_662_ = 0;
v___x_663_ = 1;
v___x_664_ = 1;
v___x_665_ = l_Lean_Meta_mkForallFVars(v_eqs_653_, v_a_661_, v___x_662_, v___x_663_, v___x_663_, v___x_664_, v___y_655_, v___y_656_, v___y_657_, v___y_658_);
if (lean_obj_tag(v___x_665_) == 0)
{
lean_object* v_a_666_; lean_object* v___x_667_; 
v_a_666_ = lean_ctor_get(v___x_665_, 0);
lean_inc(v_a_666_);
lean_dec_ref_known(v___x_665_, 1);
v___x_667_ = l_Lean_Meta_mkForallFVars(v___x_652_, v_a_666_, v___x_662_, v___x_663_, v___x_663_, v___x_664_, v___y_655_, v___y_656_, v___y_657_, v___y_658_);
if (lean_obj_tag(v___x_667_) == 0)
{
lean_object* v_a_668_; lean_object* v___x_670_; uint8_t v_isShared_671_; uint8_t v_isSharedCheck_676_; 
v_a_668_ = lean_ctor_get(v___x_667_, 0);
v_isSharedCheck_676_ = !lean_is_exclusive(v___x_667_);
if (v_isSharedCheck_676_ == 0)
{
v___x_670_ = v___x_667_;
v_isShared_671_ = v_isSharedCheck_676_;
goto v_resetjp_669_;
}
else
{
lean_inc(v_a_668_);
lean_dec(v___x_667_);
v___x_670_ = lean_box(0);
v_isShared_671_ = v_isSharedCheck_676_;
goto v_resetjp_669_;
}
v_resetjp_669_:
{
lean_object* v___x_672_; lean_object* v___x_674_; 
v___x_672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_672_, 0, v_a_668_);
lean_ctor_set(v___x_672_, 1, v_eqRefls_654_);
if (v_isShared_671_ == 0)
{
lean_ctor_set(v___x_670_, 0, v___x_672_);
v___x_674_ = v___x_670_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_675_; 
v_reuseFailAlloc_675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_675_, 0, v___x_672_);
v___x_674_ = v_reuseFailAlloc_675_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
return v___x_674_;
}
}
}
else
{
lean_object* v_a_677_; lean_object* v___x_679_; uint8_t v_isShared_680_; uint8_t v_isSharedCheck_684_; 
lean_dec_ref(v_eqRefls_654_);
v_a_677_ = lean_ctor_get(v___x_667_, 0);
v_isSharedCheck_684_ = !lean_is_exclusive(v___x_667_);
if (v_isSharedCheck_684_ == 0)
{
v___x_679_ = v___x_667_;
v_isShared_680_ = v_isSharedCheck_684_;
goto v_resetjp_678_;
}
else
{
lean_inc(v_a_677_);
lean_dec(v___x_667_);
v___x_679_ = lean_box(0);
v_isShared_680_ = v_isSharedCheck_684_;
goto v_resetjp_678_;
}
v_resetjp_678_:
{
lean_object* v___x_682_; 
if (v_isShared_680_ == 0)
{
v___x_682_ = v___x_679_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v_a_677_);
v___x_682_ = v_reuseFailAlloc_683_;
goto v_reusejp_681_;
}
v_reusejp_681_:
{
return v___x_682_;
}
}
}
}
else
{
lean_object* v_a_685_; lean_object* v___x_687_; uint8_t v_isShared_688_; uint8_t v_isSharedCheck_692_; 
lean_dec_ref(v_eqRefls_654_);
v_a_685_ = lean_ctor_get(v___x_665_, 0);
v_isSharedCheck_692_ = !lean_is_exclusive(v___x_665_);
if (v_isSharedCheck_692_ == 0)
{
v___x_687_ = v___x_665_;
v_isShared_688_ = v_isSharedCheck_692_;
goto v_resetjp_686_;
}
else
{
lean_inc(v_a_685_);
lean_dec(v___x_665_);
v___x_687_ = lean_box(0);
v_isShared_688_ = v_isSharedCheck_692_;
goto v_resetjp_686_;
}
v_resetjp_686_:
{
lean_object* v___x_690_; 
if (v_isShared_688_ == 0)
{
v___x_690_ = v___x_687_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_691_; 
v_reuseFailAlloc_691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_691_, 0, v_a_685_);
v___x_690_ = v_reuseFailAlloc_691_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
return v___x_690_;
}
}
}
}
else
{
lean_object* v_a_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_700_; 
lean_dec_ref(v_eqRefls_654_);
v_a_693_ = lean_ctor_get(v___x_660_, 0);
v_isSharedCheck_700_ = !lean_is_exclusive(v___x_660_);
if (v_isSharedCheck_700_ == 0)
{
v___x_695_ = v___x_660_;
v_isShared_696_ = v_isSharedCheck_700_;
goto v_resetjp_694_;
}
else
{
lean_inc(v_a_693_);
lean_dec(v___x_660_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_700_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
lean_object* v___x_698_; 
if (v_isShared_696_ == 0)
{
v___x_698_ = v___x_695_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v_a_693_);
v___x_698_ = v_reuseFailAlloc_699_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
return v___x_698_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeTargetsEq___lam__0___boxed(lean_object* v_mvarId_701_, lean_object* v___x_702_, lean_object* v_eqs_703_, lean_object* v_eqRefls_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_){
_start:
{
lean_object* v_res_710_; 
v_res_710_ = l_Lean_Meta_generalizeTargetsEq___lam__0(v_mvarId_701_, v___x_702_, v_eqs_703_, v_eqRefls_704_, v___y_705_, v___y_706_, v___y_707_, v___y_708_);
lean_dec(v___y_708_);
lean_dec_ref(v___y_707_);
lean_dec(v___y_706_);
lean_dec_ref(v___y_705_);
lean_dec_ref(v_eqs_703_);
lean_dec_ref(v___x_702_);
return v_res_710_;
}
}
static lean_object* _init_l_Lean_Meta_generalizeTargetsEq___lam__1___closed__1(void){
_start:
{
lean_object* v___x_712_; lean_object* v___x_713_; 
v___x_712_ = ((lean_object*)(l_Lean_Meta_generalizeTargetsEq___lam__1___closed__0));
v___x_713_ = l_Lean_stringToMessageData(v___x_712_);
return v___x_713_;
}
}
static lean_object* _init_l_Lean_Meta_generalizeTargetsEq___lam__1___closed__3(void){
_start:
{
lean_object* v___x_715_; lean_object* v___x_716_; 
v___x_715_ = ((lean_object*)(l_Lean_Meta_generalizeTargetsEq___lam__1___closed__2));
v___x_716_ = l_Lean_stringToMessageData(v___x_715_);
return v___x_716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeTargetsEq___lam__1(lean_object* v_targets_717_, lean_object* v_mvarId_718_, lean_object* v_targetsNew_719_, lean_object* v_x_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_){
_start:
{
lean_object* v___x_733_; lean_object* v___x_734_; uint8_t v___x_735_; 
v___x_733_ = lean_array_get_size(v_targets_717_);
v___x_734_ = lean_array_get_size(v_targetsNew_719_);
v___x_735_ = lean_nat_dec_le(v___x_733_, v___x_734_);
if (v___x_735_ == 0)
{
lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v_a_748_; lean_object* v___x_750_; uint8_t v_isShared_751_; uint8_t v_isSharedCheck_755_; 
lean_dec_ref(v_targetsNew_719_);
lean_dec(v_mvarId_718_);
lean_dec_ref(v_targets_717_);
v___x_736_ = lean_obj_once(&l_Lean_Meta_generalizeTargetsEq___lam__1___closed__1, &l_Lean_Meta_generalizeTargetsEq___lam__1___closed__1_once, _init_l_Lean_Meta_generalizeTargetsEq___lam__1___closed__1);
v___x_737_ = l_Nat_reprFast(v___x_733_);
v___x_738_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_738_, 0, v___x_737_);
v___x_739_ = l_Lean_MessageData_ofFormat(v___x_738_);
v___x_740_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_740_, 0, v___x_736_);
lean_ctor_set(v___x_740_, 1, v___x_739_);
v___x_741_ = lean_obj_once(&l_Lean_Meta_generalizeTargetsEq___lam__1___closed__3, &l_Lean_Meta_generalizeTargetsEq___lam__1___closed__3_once, _init_l_Lean_Meta_generalizeTargetsEq___lam__1___closed__3);
v___x_742_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_742_, 0, v___x_740_);
lean_ctor_set(v___x_742_, 1, v___x_741_);
v___x_743_ = l_Nat_reprFast(v___x_734_);
v___x_744_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_744_, 0, v___x_743_);
v___x_745_ = l_Lean_MessageData_ofFormat(v___x_744_);
v___x_746_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_746_, 0, v___x_742_);
lean_ctor_set(v___x_746_, 1, v___x_745_);
v___x_747_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected_spec__0___redArg(v___x_746_, v___y_721_, v___y_722_, v___y_723_, v___y_724_);
v_a_748_ = lean_ctor_get(v___x_747_, 0);
v_isSharedCheck_755_ = !lean_is_exclusive(v___x_747_);
if (v_isSharedCheck_755_ == 0)
{
v___x_750_ = v___x_747_;
v_isShared_751_ = v_isSharedCheck_755_;
goto v_resetjp_749_;
}
else
{
lean_inc(v_a_748_);
lean_dec(v___x_747_);
v___x_750_ = lean_box(0);
v_isShared_751_ = v_isSharedCheck_755_;
goto v_resetjp_749_;
}
v_resetjp_749_:
{
lean_object* v___x_753_; 
if (v_isShared_751_ == 0)
{
v___x_753_ = v___x_750_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v_a_748_);
v___x_753_ = v_reuseFailAlloc_754_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
return v___x_753_;
}
}
}
else
{
goto v___jp_726_;
}
v___jp_726_:
{
lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___f_731_; lean_object* v___x_732_; 
v___x_727_ = lean_array_get_size(v_targets_717_);
v___x_728_ = lean_unsigned_to_nat(0u);
v___x_729_ = l_Array_toSubarray___redArg(v_targetsNew_719_, v___x_728_, v___x_727_);
v___x_730_ = l_Subarray_copy___redArg(v___x_729_);
lean_inc_ref(v___x_730_);
v___f_731_ = lean_alloc_closure((void*)(l_Lean_Meta_generalizeTargetsEq___lam__0___boxed), 9, 2);
lean_closure_set(v___f_731_, 0, v_mvarId_718_);
lean_closure_set(v___f_731_, 1, v___x_730_);
v___x_732_ = l_Lean_Meta_withNewEqs___redArg(v_targets_717_, v___x_730_, v___f_731_, v___y_721_, v___y_722_, v___y_723_, v___y_724_);
return v___x_732_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeTargetsEq___lam__1___boxed(lean_object* v_targets_756_, lean_object* v_mvarId_757_, lean_object* v_targetsNew_758_, lean_object* v_x_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_){
_start:
{
lean_object* v_res_765_; 
v_res_765_ = l_Lean_Meta_generalizeTargetsEq___lam__1(v_targets_756_, v_mvarId_757_, v_targetsNew_758_, v_x_759_, v___y_760_, v___y_761_, v___y_762_, v___y_763_);
lean_dec(v___y_763_);
lean_dec_ref(v___y_762_);
lean_dec(v___y_761_);
lean_dec_ref(v___y_760_);
lean_dec_ref(v_x_759_);
return v_res_765_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__4_spec__5___redArg(lean_object* v_x_766_, lean_object* v_x_767_, lean_object* v_x_768_, lean_object* v_x_769_){
_start:
{
lean_object* v_ks_770_; lean_object* v_vs_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_795_; 
v_ks_770_ = lean_ctor_get(v_x_766_, 0);
v_vs_771_ = lean_ctor_get(v_x_766_, 1);
v_isSharedCheck_795_ = !lean_is_exclusive(v_x_766_);
if (v_isSharedCheck_795_ == 0)
{
v___x_773_ = v_x_766_;
v_isShared_774_ = v_isSharedCheck_795_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_vs_771_);
lean_inc(v_ks_770_);
lean_dec(v_x_766_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_795_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
lean_object* v___x_775_; uint8_t v___x_776_; 
v___x_775_ = lean_array_get_size(v_ks_770_);
v___x_776_ = lean_nat_dec_lt(v_x_767_, v___x_775_);
if (v___x_776_ == 0)
{
lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_780_; 
lean_dec(v_x_767_);
v___x_777_ = lean_array_push(v_ks_770_, v_x_768_);
v___x_778_ = lean_array_push(v_vs_771_, v_x_769_);
if (v_isShared_774_ == 0)
{
lean_ctor_set(v___x_773_, 1, v___x_778_);
lean_ctor_set(v___x_773_, 0, v___x_777_);
v___x_780_ = v___x_773_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v___x_777_);
lean_ctor_set(v_reuseFailAlloc_781_, 1, v___x_778_);
v___x_780_ = v_reuseFailAlloc_781_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
return v___x_780_;
}
}
else
{
lean_object* v_k_x27_782_; uint8_t v___x_783_; 
v_k_x27_782_ = lean_array_fget_borrowed(v_ks_770_, v_x_767_);
v___x_783_ = l_Lean_instBEqMVarId_beq(v_x_768_, v_k_x27_782_);
if (v___x_783_ == 0)
{
lean_object* v___x_785_; 
if (v_isShared_774_ == 0)
{
v___x_785_ = v___x_773_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v_ks_770_);
lean_ctor_set(v_reuseFailAlloc_789_, 1, v_vs_771_);
v___x_785_ = v_reuseFailAlloc_789_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
lean_object* v___x_786_; lean_object* v___x_787_; 
v___x_786_ = lean_unsigned_to_nat(1u);
v___x_787_ = lean_nat_add(v_x_767_, v___x_786_);
lean_dec(v_x_767_);
v_x_766_ = v___x_785_;
v_x_767_ = v___x_787_;
goto _start;
}
}
else
{
lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_793_; 
v___x_790_ = lean_array_fset(v_ks_770_, v_x_767_, v_x_768_);
v___x_791_ = lean_array_fset(v_vs_771_, v_x_767_, v_x_769_);
lean_dec(v_x_767_);
if (v_isShared_774_ == 0)
{
lean_ctor_set(v___x_773_, 1, v___x_791_);
lean_ctor_set(v___x_773_, 0, v___x_790_);
v___x_793_ = v___x_773_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v___x_790_);
lean_ctor_set(v_reuseFailAlloc_794_, 1, v___x_791_);
v___x_793_ = v_reuseFailAlloc_794_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
return v___x_793_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__4___redArg(lean_object* v_n_796_, lean_object* v_k_797_, lean_object* v_v_798_){
_start:
{
lean_object* v___x_799_; lean_object* v___x_800_; 
v___x_799_ = lean_unsigned_to_nat(0u);
v___x_800_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__4_spec__5___redArg(v_n_796_, v___x_799_, v_k_797_, v_v_798_);
return v___x_800_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_801_; 
v___x_801_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_801_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg(lean_object* v_x_802_, size_t v_x_803_, size_t v_x_804_, lean_object* v_x_805_, lean_object* v_x_806_){
_start:
{
if (lean_obj_tag(v_x_802_) == 0)
{
lean_object* v_es_807_; size_t v___x_808_; size_t v___x_809_; lean_object* v_j_810_; lean_object* v___x_811_; uint8_t v___x_812_; 
v_es_807_ = lean_ctor_get(v_x_802_, 0);
v___x_808_ = ((size_t)31ULL);
v___x_809_ = lean_usize_land(v_x_803_, v___x_808_);
v_j_810_ = lean_usize_to_nat(v___x_809_);
v___x_811_ = lean_array_get_size(v_es_807_);
v___x_812_ = lean_nat_dec_lt(v_j_810_, v___x_811_);
if (v___x_812_ == 0)
{
lean_dec(v_j_810_);
lean_dec(v_x_806_);
lean_dec(v_x_805_);
return v_x_802_;
}
else
{
lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_851_; 
lean_inc_ref(v_es_807_);
v_isSharedCheck_851_ = !lean_is_exclusive(v_x_802_);
if (v_isSharedCheck_851_ == 0)
{
lean_object* v_unused_852_; 
v_unused_852_ = lean_ctor_get(v_x_802_, 0);
lean_dec(v_unused_852_);
v___x_814_ = v_x_802_;
v_isShared_815_ = v_isSharedCheck_851_;
goto v_resetjp_813_;
}
else
{
lean_dec(v_x_802_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_851_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
lean_object* v_v_816_; lean_object* v___x_817_; lean_object* v_xs_x27_818_; lean_object* v___y_820_; 
v_v_816_ = lean_array_fget(v_es_807_, v_j_810_);
v___x_817_ = lean_box(0);
v_xs_x27_818_ = lean_array_fset(v_es_807_, v_j_810_, v___x_817_);
switch(lean_obj_tag(v_v_816_))
{
case 0:
{
lean_object* v_key_825_; lean_object* v_val_826_; lean_object* v___x_828_; uint8_t v_isShared_829_; uint8_t v_isSharedCheck_836_; 
v_key_825_ = lean_ctor_get(v_v_816_, 0);
v_val_826_ = lean_ctor_get(v_v_816_, 1);
v_isSharedCheck_836_ = !lean_is_exclusive(v_v_816_);
if (v_isSharedCheck_836_ == 0)
{
v___x_828_ = v_v_816_;
v_isShared_829_ = v_isSharedCheck_836_;
goto v_resetjp_827_;
}
else
{
lean_inc(v_val_826_);
lean_inc(v_key_825_);
lean_dec(v_v_816_);
v___x_828_ = lean_box(0);
v_isShared_829_ = v_isSharedCheck_836_;
goto v_resetjp_827_;
}
v_resetjp_827_:
{
uint8_t v___x_830_; 
v___x_830_ = l_Lean_instBEqMVarId_beq(v_x_805_, v_key_825_);
if (v___x_830_ == 0)
{
lean_object* v___x_831_; lean_object* v___x_832_; 
lean_del_object(v___x_828_);
v___x_831_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_825_, v_val_826_, v_x_805_, v_x_806_);
v___x_832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_832_, 0, v___x_831_);
v___y_820_ = v___x_832_;
goto v___jp_819_;
}
else
{
lean_object* v___x_834_; 
lean_dec(v_val_826_);
lean_dec(v_key_825_);
if (v_isShared_829_ == 0)
{
lean_ctor_set(v___x_828_, 1, v_x_806_);
lean_ctor_set(v___x_828_, 0, v_x_805_);
v___x_834_ = v___x_828_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v_x_805_);
lean_ctor_set(v_reuseFailAlloc_835_, 1, v_x_806_);
v___x_834_ = v_reuseFailAlloc_835_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
v___y_820_ = v___x_834_;
goto v___jp_819_;
}
}
}
}
case 1:
{
lean_object* v_node_837_; lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_849_; 
v_node_837_ = lean_ctor_get(v_v_816_, 0);
v_isSharedCheck_849_ = !lean_is_exclusive(v_v_816_);
if (v_isSharedCheck_849_ == 0)
{
v___x_839_ = v_v_816_;
v_isShared_840_ = v_isSharedCheck_849_;
goto v_resetjp_838_;
}
else
{
lean_inc(v_node_837_);
lean_dec(v_v_816_);
v___x_839_ = lean_box(0);
v_isShared_840_ = v_isSharedCheck_849_;
goto v_resetjp_838_;
}
v_resetjp_838_:
{
size_t v___x_841_; size_t v___x_842_; size_t v___x_843_; size_t v___x_844_; lean_object* v___x_845_; lean_object* v___x_847_; 
v___x_841_ = ((size_t)5ULL);
v___x_842_ = lean_usize_shift_right(v_x_803_, v___x_841_);
v___x_843_ = ((size_t)1ULL);
v___x_844_ = lean_usize_add(v_x_804_, v___x_843_);
v___x_845_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg(v_node_837_, v___x_842_, v___x_844_, v_x_805_, v_x_806_);
if (v_isShared_840_ == 0)
{
lean_ctor_set(v___x_839_, 0, v___x_845_);
v___x_847_ = v___x_839_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v___x_845_);
v___x_847_ = v_reuseFailAlloc_848_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
v___y_820_ = v___x_847_;
goto v___jp_819_;
}
}
}
default: 
{
lean_object* v___x_850_; 
v___x_850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_850_, 0, v_x_805_);
lean_ctor_set(v___x_850_, 1, v_x_806_);
v___y_820_ = v___x_850_;
goto v___jp_819_;
}
}
v___jp_819_:
{
lean_object* v___x_821_; lean_object* v___x_823_; 
v___x_821_ = lean_array_fset(v_xs_x27_818_, v_j_810_, v___y_820_);
lean_dec(v_j_810_);
if (v_isShared_815_ == 0)
{
lean_ctor_set(v___x_814_, 0, v___x_821_);
v___x_823_ = v___x_814_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v___x_821_);
v___x_823_ = v_reuseFailAlloc_824_;
goto v_reusejp_822_;
}
v_reusejp_822_:
{
return v___x_823_;
}
}
}
}
}
else
{
lean_object* v_ks_853_; lean_object* v_vs_854_; lean_object* v___x_856_; uint8_t v_isShared_857_; uint8_t v_isSharedCheck_874_; 
v_ks_853_ = lean_ctor_get(v_x_802_, 0);
v_vs_854_ = lean_ctor_get(v_x_802_, 1);
v_isSharedCheck_874_ = !lean_is_exclusive(v_x_802_);
if (v_isSharedCheck_874_ == 0)
{
v___x_856_ = v_x_802_;
v_isShared_857_ = v_isSharedCheck_874_;
goto v_resetjp_855_;
}
else
{
lean_inc(v_vs_854_);
lean_inc(v_ks_853_);
lean_dec(v_x_802_);
v___x_856_ = lean_box(0);
v_isShared_857_ = v_isSharedCheck_874_;
goto v_resetjp_855_;
}
v_resetjp_855_:
{
lean_object* v___x_859_; 
if (v_isShared_857_ == 0)
{
v___x_859_ = v___x_856_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v_ks_853_);
lean_ctor_set(v_reuseFailAlloc_873_, 1, v_vs_854_);
v___x_859_ = v_reuseFailAlloc_873_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
lean_object* v_newNode_860_; uint8_t v___y_862_; size_t v___x_868_; uint8_t v___x_869_; 
v_newNode_860_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__4___redArg(v___x_859_, v_x_805_, v_x_806_);
v___x_868_ = ((size_t)7ULL);
v___x_869_ = lean_usize_dec_le(v___x_868_, v_x_804_);
if (v___x_869_ == 0)
{
lean_object* v___x_870_; lean_object* v___x_871_; uint8_t v___x_872_; 
v___x_870_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_860_);
v___x_871_ = lean_unsigned_to_nat(4u);
v___x_872_ = lean_nat_dec_lt(v___x_870_, v___x_871_);
lean_dec(v___x_870_);
v___y_862_ = v___x_872_;
goto v___jp_861_;
}
else
{
v___y_862_ = v___x_869_;
goto v___jp_861_;
}
v___jp_861_:
{
if (v___y_862_ == 0)
{
lean_object* v_ks_863_; lean_object* v_vs_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; 
v_ks_863_ = lean_ctor_get(v_newNode_860_, 0);
lean_inc_ref(v_ks_863_);
v_vs_864_ = lean_ctor_get(v_newNode_860_, 1);
lean_inc_ref(v_vs_864_);
lean_dec_ref(v_newNode_860_);
v___x_865_ = lean_unsigned_to_nat(0u);
v___x_866_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg___closed__0);
v___x_867_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__5___redArg(v_x_804_, v_ks_863_, v_vs_864_, v___x_865_, v___x_866_);
lean_dec_ref(v_vs_864_);
lean_dec_ref(v_ks_863_);
return v___x_867_;
}
else
{
return v_newNode_860_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__5___redArg(size_t v_depth_875_, lean_object* v_keys_876_, lean_object* v_vals_877_, lean_object* v_i_878_, lean_object* v_entries_879_){
_start:
{
lean_object* v___x_880_; uint8_t v___x_881_; 
v___x_880_ = lean_array_get_size(v_keys_876_);
v___x_881_ = lean_nat_dec_lt(v_i_878_, v___x_880_);
if (v___x_881_ == 0)
{
lean_dec(v_i_878_);
return v_entries_879_;
}
else
{
lean_object* v_k_882_; lean_object* v_v_883_; uint64_t v___x_884_; size_t v_h_885_; size_t v___x_886_; lean_object* v___x_887_; size_t v___x_888_; size_t v___x_889_; size_t v___x_890_; size_t v_h_891_; lean_object* v___x_892_; lean_object* v___x_893_; 
v_k_882_ = lean_array_fget_borrowed(v_keys_876_, v_i_878_);
v_v_883_ = lean_array_fget_borrowed(v_vals_877_, v_i_878_);
v___x_884_ = l_Lean_instHashableMVarId_hash(v_k_882_);
v_h_885_ = lean_uint64_to_usize(v___x_884_);
v___x_886_ = ((size_t)5ULL);
v___x_887_ = lean_unsigned_to_nat(1u);
v___x_888_ = ((size_t)1ULL);
v___x_889_ = lean_usize_sub(v_depth_875_, v___x_888_);
v___x_890_ = lean_usize_mul(v___x_886_, v___x_889_);
v_h_891_ = lean_usize_shift_right(v_h_885_, v___x_890_);
v___x_892_ = lean_nat_add(v_i_878_, v___x_887_);
lean_dec(v_i_878_);
lean_inc(v_v_883_);
lean_inc(v_k_882_);
v___x_893_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg(v_entries_879_, v_h_891_, v_depth_875_, v_k_882_, v_v_883_);
v_i_878_ = v___x_892_;
v_entries_879_ = v___x_893_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__5___redArg___boxed(lean_object* v_depth_895_, lean_object* v_keys_896_, lean_object* v_vals_897_, lean_object* v_i_898_, lean_object* v_entries_899_){
_start:
{
size_t v_depth_boxed_900_; lean_object* v_res_901_; 
v_depth_boxed_900_ = lean_unbox_usize(v_depth_895_);
lean_dec(v_depth_895_);
v_res_901_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__5___redArg(v_depth_boxed_900_, v_keys_896_, v_vals_897_, v_i_898_, v_entries_899_);
lean_dec_ref(v_vals_897_);
lean_dec_ref(v_keys_896_);
return v_res_901_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_x_902_, lean_object* v_x_903_, lean_object* v_x_904_, lean_object* v_x_905_, lean_object* v_x_906_){
_start:
{
size_t v_x_2561__boxed_907_; size_t v_x_2562__boxed_908_; lean_object* v_res_909_; 
v_x_2561__boxed_907_ = lean_unbox_usize(v_x_903_);
lean_dec(v_x_903_);
v_x_2562__boxed_908_ = lean_unbox_usize(v_x_904_);
lean_dec(v_x_904_);
v_res_909_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg(v_x_902_, v_x_2561__boxed_907_, v_x_2562__boxed_908_, v_x_905_, v_x_906_);
return v_res_909_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1___redArg(lean_object* v_x_910_, lean_object* v_x_911_, lean_object* v_x_912_){
_start:
{
uint64_t v___x_913_; size_t v___x_914_; size_t v___x_915_; lean_object* v___x_916_; 
v___x_913_ = l_Lean_instHashableMVarId_hash(v_x_911_);
v___x_914_ = lean_uint64_to_usize(v___x_913_);
v___x_915_ = ((size_t)1ULL);
v___x_916_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg(v_x_910_, v___x_914_, v___x_915_, v_x_911_, v_x_912_);
return v___x_916_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1___redArg(lean_object* v_mvarId_917_, lean_object* v_val_918_, lean_object* v___y_919_){
_start:
{
lean_object* v___x_921_; lean_object* v_mctx_922_; lean_object* v_cache_923_; lean_object* v_zetaDeltaFVarIds_924_; lean_object* v_postponed_925_; lean_object* v_diag_926_; lean_object* v___x_928_; uint8_t v_isShared_929_; uint8_t v_isSharedCheck_955_; 
v___x_921_ = lean_st_ref_take(v___y_919_);
v_mctx_922_ = lean_ctor_get(v___x_921_, 0);
v_cache_923_ = lean_ctor_get(v___x_921_, 1);
v_zetaDeltaFVarIds_924_ = lean_ctor_get(v___x_921_, 2);
v_postponed_925_ = lean_ctor_get(v___x_921_, 3);
v_diag_926_ = lean_ctor_get(v___x_921_, 4);
v_isSharedCheck_955_ = !lean_is_exclusive(v___x_921_);
if (v_isSharedCheck_955_ == 0)
{
v___x_928_ = v___x_921_;
v_isShared_929_ = v_isSharedCheck_955_;
goto v_resetjp_927_;
}
else
{
lean_inc(v_diag_926_);
lean_inc(v_postponed_925_);
lean_inc(v_zetaDeltaFVarIds_924_);
lean_inc(v_cache_923_);
lean_inc(v_mctx_922_);
lean_dec(v___x_921_);
v___x_928_ = lean_box(0);
v_isShared_929_ = v_isSharedCheck_955_;
goto v_resetjp_927_;
}
v_resetjp_927_:
{
lean_object* v_depth_930_; lean_object* v_levelAssignDepth_931_; lean_object* v_lmvarCounter_932_; lean_object* v_mvarCounter_933_; lean_object* v_lDecls_934_; lean_object* v_decls_935_; lean_object* v_userNames_936_; lean_object* v_lAssignment_937_; lean_object* v_eAssignment_938_; lean_object* v_dAssignment_939_; lean_object* v_instanceTypedMVars_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_954_; 
v_depth_930_ = lean_ctor_get(v_mctx_922_, 0);
v_levelAssignDepth_931_ = lean_ctor_get(v_mctx_922_, 1);
v_lmvarCounter_932_ = lean_ctor_get(v_mctx_922_, 2);
v_mvarCounter_933_ = lean_ctor_get(v_mctx_922_, 3);
v_lDecls_934_ = lean_ctor_get(v_mctx_922_, 4);
v_decls_935_ = lean_ctor_get(v_mctx_922_, 5);
v_userNames_936_ = lean_ctor_get(v_mctx_922_, 6);
v_lAssignment_937_ = lean_ctor_get(v_mctx_922_, 7);
v_eAssignment_938_ = lean_ctor_get(v_mctx_922_, 8);
v_dAssignment_939_ = lean_ctor_get(v_mctx_922_, 9);
v_instanceTypedMVars_940_ = lean_ctor_get(v_mctx_922_, 10);
v_isSharedCheck_954_ = !lean_is_exclusive(v_mctx_922_);
if (v_isSharedCheck_954_ == 0)
{
v___x_942_ = v_mctx_922_;
v_isShared_943_ = v_isSharedCheck_954_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_instanceTypedMVars_940_);
lean_inc(v_dAssignment_939_);
lean_inc(v_eAssignment_938_);
lean_inc(v_lAssignment_937_);
lean_inc(v_userNames_936_);
lean_inc(v_decls_935_);
lean_inc(v_lDecls_934_);
lean_inc(v_mvarCounter_933_);
lean_inc(v_lmvarCounter_932_);
lean_inc(v_levelAssignDepth_931_);
lean_inc(v_depth_930_);
lean_dec(v_mctx_922_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_954_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
lean_object* v___x_944_; lean_object* v___x_946_; 
v___x_944_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1___redArg(v_eAssignment_938_, v_mvarId_917_, v_val_918_);
if (v_isShared_943_ == 0)
{
lean_ctor_set(v___x_942_, 8, v___x_944_);
v___x_946_ = v___x_942_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_953_; 
v_reuseFailAlloc_953_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_953_, 0, v_depth_930_);
lean_ctor_set(v_reuseFailAlloc_953_, 1, v_levelAssignDepth_931_);
lean_ctor_set(v_reuseFailAlloc_953_, 2, v_lmvarCounter_932_);
lean_ctor_set(v_reuseFailAlloc_953_, 3, v_mvarCounter_933_);
lean_ctor_set(v_reuseFailAlloc_953_, 4, v_lDecls_934_);
lean_ctor_set(v_reuseFailAlloc_953_, 5, v_decls_935_);
lean_ctor_set(v_reuseFailAlloc_953_, 6, v_userNames_936_);
lean_ctor_set(v_reuseFailAlloc_953_, 7, v_lAssignment_937_);
lean_ctor_set(v_reuseFailAlloc_953_, 8, v___x_944_);
lean_ctor_set(v_reuseFailAlloc_953_, 9, v_dAssignment_939_);
lean_ctor_set(v_reuseFailAlloc_953_, 10, v_instanceTypedMVars_940_);
v___x_946_ = v_reuseFailAlloc_953_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
lean_object* v___x_948_; 
if (v_isShared_929_ == 0)
{
lean_ctor_set(v___x_928_, 0, v___x_946_);
v___x_948_ = v___x_928_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v___x_946_);
lean_ctor_set(v_reuseFailAlloc_952_, 1, v_cache_923_);
lean_ctor_set(v_reuseFailAlloc_952_, 2, v_zetaDeltaFVarIds_924_);
lean_ctor_set(v_reuseFailAlloc_952_, 3, v_postponed_925_);
lean_ctor_set(v_reuseFailAlloc_952_, 4, v_diag_926_);
v___x_948_ = v_reuseFailAlloc_952_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; 
v___x_949_ = lean_st_ref_put(v___y_919_, v___x_948_);
v___x_950_ = lean_box(0);
v___x_951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_951_, 0, v___x_950_);
return v___x_951_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1___redArg___boxed(lean_object* v_mvarId_956_, lean_object* v_val_957_, lean_object* v___y_958_, lean_object* v___y_959_){
_start:
{
lean_object* v_res_960_; 
v_res_960_ = l_Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1___redArg(v_mvarId_956_, v_val_957_, v___y_958_);
lean_dec(v___y_958_);
return v_res_960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeTargetsEq___lam__2(lean_object* v_mvarId_961_, lean_object* v___x_962_, lean_object* v_motiveType_963_, lean_object* v___f_964_, lean_object* v_targets_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_){
_start:
{
lean_object* v___x_971_; 
lean_inc(v_mvarId_961_);
v___x_971_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_961_, v___x_962_, v___y_966_, v___y_967_, v___y_968_, v___y_969_);
if (lean_obj_tag(v___x_971_) == 0)
{
uint8_t v___x_972_; lean_object* v___x_973_; 
lean_dec_ref_known(v___x_971_, 1);
v___x_972_ = 0;
v___x_973_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_generalizeTargetsEq_spec__0___redArg(v_motiveType_963_, v___f_964_, v___x_972_, v___x_972_, v___y_966_, v___y_967_, v___y_968_, v___y_969_);
if (lean_obj_tag(v___x_973_) == 0)
{
lean_object* v_a_974_; lean_object* v_fst_975_; lean_object* v_snd_976_; lean_object* v___x_977_; 
v_a_974_ = lean_ctor_get(v___x_973_, 0);
lean_inc(v_a_974_);
lean_dec_ref_known(v___x_973_, 1);
v_fst_975_ = lean_ctor_get(v_a_974_, 0);
lean_inc(v_fst_975_);
v_snd_976_ = lean_ctor_get(v_a_974_, 1);
lean_inc(v_snd_976_);
lean_dec(v_a_974_);
lean_inc(v_mvarId_961_);
v___x_977_ = l_Lean_MVarId_getTag(v_mvarId_961_, v___y_966_, v___y_967_, v___y_968_, v___y_969_);
if (lean_obj_tag(v___x_977_) == 0)
{
lean_object* v_a_978_; lean_object* v___x_979_; 
v_a_978_ = lean_ctor_get(v___x_977_, 0);
lean_inc(v_a_978_);
lean_dec_ref_known(v___x_977_, 1);
v___x_979_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_fst_975_, v_a_978_, v___y_966_, v___y_967_, v___y_968_, v___y_969_);
if (lean_obj_tag(v___x_979_) == 0)
{
lean_object* v_a_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_985_; uint8_t v_isShared_986_; uint8_t v_isSharedCheck_991_; 
v_a_980_ = lean_ctor_get(v___x_979_, 0);
lean_inc_n(v_a_980_, 2);
lean_dec_ref_known(v___x_979_, 1);
v___x_981_ = l_Lean_mkAppN(v_a_980_, v_targets_965_);
v___x_982_ = l_Lean_mkAppN(v___x_981_, v_snd_976_);
lean_dec(v_snd_976_);
v___x_983_ = l_Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1___redArg(v_mvarId_961_, v___x_982_, v___y_967_);
v_isSharedCheck_991_ = !lean_is_exclusive(v___x_983_);
if (v_isSharedCheck_991_ == 0)
{
lean_object* v_unused_992_; 
v_unused_992_ = lean_ctor_get(v___x_983_, 0);
lean_dec(v_unused_992_);
v___x_985_ = v___x_983_;
v_isShared_986_ = v_isSharedCheck_991_;
goto v_resetjp_984_;
}
else
{
lean_dec(v___x_983_);
v___x_985_ = lean_box(0);
v_isShared_986_ = v_isSharedCheck_991_;
goto v_resetjp_984_;
}
v_resetjp_984_:
{
lean_object* v___x_987_; lean_object* v___x_989_; 
v___x_987_ = l_Lean_Expr_mvarId_x21(v_a_980_);
lean_dec(v_a_980_);
if (v_isShared_986_ == 0)
{
lean_ctor_set(v___x_985_, 0, v___x_987_);
v___x_989_ = v___x_985_;
goto v_reusejp_988_;
}
else
{
lean_object* v_reuseFailAlloc_990_; 
v_reuseFailAlloc_990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_990_, 0, v___x_987_);
v___x_989_ = v_reuseFailAlloc_990_;
goto v_reusejp_988_;
}
v_reusejp_988_:
{
return v___x_989_;
}
}
}
else
{
lean_object* v_a_993_; lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1000_; 
lean_dec(v_snd_976_);
lean_dec(v_mvarId_961_);
v_a_993_ = lean_ctor_get(v___x_979_, 0);
v_isSharedCheck_1000_ = !lean_is_exclusive(v___x_979_);
if (v_isSharedCheck_1000_ == 0)
{
v___x_995_ = v___x_979_;
v_isShared_996_ = v_isSharedCheck_1000_;
goto v_resetjp_994_;
}
else
{
lean_inc(v_a_993_);
lean_dec(v___x_979_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1000_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
lean_object* v___x_998_; 
if (v_isShared_996_ == 0)
{
v___x_998_ = v___x_995_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v_a_993_);
v___x_998_ = v_reuseFailAlloc_999_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
return v___x_998_;
}
}
}
}
else
{
lean_object* v_a_1001_; lean_object* v___x_1003_; uint8_t v_isShared_1004_; uint8_t v_isSharedCheck_1008_; 
lean_dec(v_snd_976_);
lean_dec(v_fst_975_);
lean_dec(v_mvarId_961_);
v_a_1001_ = lean_ctor_get(v___x_977_, 0);
v_isSharedCheck_1008_ = !lean_is_exclusive(v___x_977_);
if (v_isSharedCheck_1008_ == 0)
{
v___x_1003_ = v___x_977_;
v_isShared_1004_ = v_isSharedCheck_1008_;
goto v_resetjp_1002_;
}
else
{
lean_inc(v_a_1001_);
lean_dec(v___x_977_);
v___x_1003_ = lean_box(0);
v_isShared_1004_ = v_isSharedCheck_1008_;
goto v_resetjp_1002_;
}
v_resetjp_1002_:
{
lean_object* v___x_1006_; 
if (v_isShared_1004_ == 0)
{
v___x_1006_ = v___x_1003_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v_a_1001_);
v___x_1006_ = v_reuseFailAlloc_1007_;
goto v_reusejp_1005_;
}
v_reusejp_1005_:
{
return v___x_1006_;
}
}
}
}
else
{
lean_object* v_a_1009_; lean_object* v___x_1011_; uint8_t v_isShared_1012_; uint8_t v_isSharedCheck_1016_; 
lean_dec(v_mvarId_961_);
v_a_1009_ = lean_ctor_get(v___x_973_, 0);
v_isSharedCheck_1016_ = !lean_is_exclusive(v___x_973_);
if (v_isSharedCheck_1016_ == 0)
{
v___x_1011_ = v___x_973_;
v_isShared_1012_ = v_isSharedCheck_1016_;
goto v_resetjp_1010_;
}
else
{
lean_inc(v_a_1009_);
lean_dec(v___x_973_);
v___x_1011_ = lean_box(0);
v_isShared_1012_ = v_isSharedCheck_1016_;
goto v_resetjp_1010_;
}
v_resetjp_1010_:
{
lean_object* v___x_1014_; 
if (v_isShared_1012_ == 0)
{
v___x_1014_ = v___x_1011_;
goto v_reusejp_1013_;
}
else
{
lean_object* v_reuseFailAlloc_1015_; 
v_reuseFailAlloc_1015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1015_, 0, v_a_1009_);
v___x_1014_ = v_reuseFailAlloc_1015_;
goto v_reusejp_1013_;
}
v_reusejp_1013_:
{
return v___x_1014_;
}
}
}
}
else
{
lean_object* v_a_1017_; lean_object* v___x_1019_; uint8_t v_isShared_1020_; uint8_t v_isSharedCheck_1024_; 
lean_dec_ref(v___f_964_);
lean_dec_ref(v_motiveType_963_);
lean_dec(v_mvarId_961_);
v_a_1017_ = lean_ctor_get(v___x_971_, 0);
v_isSharedCheck_1024_ = !lean_is_exclusive(v___x_971_);
if (v_isSharedCheck_1024_ == 0)
{
v___x_1019_ = v___x_971_;
v_isShared_1020_ = v_isSharedCheck_1024_;
goto v_resetjp_1018_;
}
else
{
lean_inc(v_a_1017_);
lean_dec(v___x_971_);
v___x_1019_ = lean_box(0);
v_isShared_1020_ = v_isSharedCheck_1024_;
goto v_resetjp_1018_;
}
v_resetjp_1018_:
{
lean_object* v___x_1022_; 
if (v_isShared_1020_ == 0)
{
v___x_1022_ = v___x_1019_;
goto v_reusejp_1021_;
}
else
{
lean_object* v_reuseFailAlloc_1023_; 
v_reuseFailAlloc_1023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1023_, 0, v_a_1017_);
v___x_1022_ = v_reuseFailAlloc_1023_;
goto v_reusejp_1021_;
}
v_reusejp_1021_:
{
return v___x_1022_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeTargetsEq___lam__2___boxed(lean_object* v_mvarId_1025_, lean_object* v___x_1026_, lean_object* v_motiveType_1027_, lean_object* v___f_1028_, lean_object* v_targets_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_){
_start:
{
lean_object* v_res_1035_; 
v_res_1035_ = l_Lean_Meta_generalizeTargetsEq___lam__2(v_mvarId_1025_, v___x_1026_, v_motiveType_1027_, v___f_1028_, v_targets_1029_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_);
lean_dec(v___y_1033_);
lean_dec_ref(v___y_1032_);
lean_dec(v___y_1031_);
lean_dec_ref(v___y_1030_);
lean_dec_ref(v_targets_1029_);
return v_res_1035_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeTargetsEq(lean_object* v_mvarId_1039_, lean_object* v_motiveType_1040_, lean_object* v_targets_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_){
_start:
{
lean_object* v___f_1047_; lean_object* v___x_1048_; lean_object* v___f_1049_; lean_object* v___x_1050_; 
lean_inc_n(v_mvarId_1039_, 2);
lean_inc_ref(v_targets_1041_);
v___f_1047_ = lean_alloc_closure((void*)(l_Lean_Meta_generalizeTargetsEq___lam__1___boxed), 9, 2);
lean_closure_set(v___f_1047_, 0, v_targets_1041_);
lean_closure_set(v___f_1047_, 1, v_mvarId_1039_);
v___x_1048_ = ((lean_object*)(l_Lean_Meta_generalizeTargetsEq___closed__1));
v___f_1049_ = lean_alloc_closure((void*)(l_Lean_Meta_generalizeTargetsEq___lam__2___boxed), 10, 5);
lean_closure_set(v___f_1049_, 0, v_mvarId_1039_);
lean_closure_set(v___f_1049_, 1, v___x_1048_);
lean_closure_set(v___f_1049_, 2, v_motiveType_1040_);
lean_closure_set(v___f_1049_, 3, v___f_1047_);
lean_closure_set(v___f_1049_, 4, v_targets_1041_);
v___x_1050_ = l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2___redArg(v_mvarId_1039_, v___f_1049_, v_a_1042_, v_a_1043_, v_a_1044_, v_a_1045_);
return v___x_1050_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeTargetsEq___boxed(lean_object* v_mvarId_1051_, lean_object* v_motiveType_1052_, lean_object* v_targets_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_){
_start:
{
lean_object* v_res_1059_; 
v_res_1059_ = l_Lean_Meta_generalizeTargetsEq(v_mvarId_1051_, v_motiveType_1052_, v_targets_1053_, v_a_1054_, v_a_1055_, v_a_1056_, v_a_1057_);
lean_dec(v_a_1057_);
lean_dec_ref(v_a_1056_);
lean_dec(v_a_1055_);
lean_dec_ref(v_a_1054_);
return v_res_1059_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1(lean_object* v_mvarId_1060_, lean_object* v_val_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_){
_start:
{
lean_object* v___x_1067_; 
v___x_1067_ = l_Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1___redArg(v_mvarId_1060_, v_val_1061_, v___y_1063_);
return v___x_1067_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1___boxed(lean_object* v_mvarId_1068_, lean_object* v_val_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_){
_start:
{
lean_object* v_res_1075_; 
v_res_1075_ = l_Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1(v_mvarId_1068_, v_val_1069_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_);
lean_dec(v___y_1073_);
lean_dec_ref(v___y_1072_);
lean_dec(v___y_1071_);
lean_dec_ref(v___y_1070_);
return v_res_1075_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1(lean_object* v_00_u03b2_1076_, lean_object* v_x_1077_, lean_object* v_x_1078_, lean_object* v_x_1079_){
_start:
{
lean_object* v___x_1080_; 
v___x_1080_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1___redArg(v_x_1077_, v_x_1078_, v_x_1079_);
return v___x_1080_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3(lean_object* v_00_u03b2_1081_, lean_object* v_x_1082_, size_t v_x_1083_, size_t v_x_1084_, lean_object* v_x_1085_, lean_object* v_x_1086_){
_start:
{
lean_object* v___x_1087_; 
v___x_1087_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg(v_x_1082_, v_x_1083_, v_x_1084_, v_x_1085_, v_x_1086_);
return v___x_1087_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1088_, lean_object* v_x_1089_, lean_object* v_x_1090_, lean_object* v_x_1091_, lean_object* v_x_1092_, lean_object* v_x_1093_){
_start:
{
size_t v_x_2952__boxed_1094_; size_t v_x_2953__boxed_1095_; lean_object* v_res_1096_; 
v_x_2952__boxed_1094_ = lean_unbox_usize(v_x_1090_);
lean_dec(v_x_1090_);
v_x_2953__boxed_1095_ = lean_unbox_usize(v_x_1091_);
lean_dec(v_x_1091_);
v_res_1096_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3(v_00_u03b2_1088_, v_x_1089_, v_x_2952__boxed_1094_, v_x_2953__boxed_1095_, v_x_1092_, v_x_1093_);
return v_res_1096_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_1097_, lean_object* v_n_1098_, lean_object* v_k_1099_, lean_object* v_v_1100_){
_start:
{
lean_object* v___x_1101_; 
v___x_1101_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__4___redArg(v_n_1098_, v_k_1099_, v_v_1100_);
return v___x_1101_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__5(lean_object* v_00_u03b2_1102_, size_t v_depth_1103_, lean_object* v_keys_1104_, lean_object* v_vals_1105_, lean_object* v_heq_1106_, lean_object* v_i_1107_, lean_object* v_entries_1108_){
_start:
{
lean_object* v___x_1109_; 
v___x_1109_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__5___redArg(v_depth_1103_, v_keys_1104_, v_vals_1105_, v_i_1107_, v_entries_1108_);
return v___x_1109_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__5___boxed(lean_object* v_00_u03b2_1110_, lean_object* v_depth_1111_, lean_object* v_keys_1112_, lean_object* v_vals_1113_, lean_object* v_heq_1114_, lean_object* v_i_1115_, lean_object* v_entries_1116_){
_start:
{
size_t v_depth_boxed_1117_; lean_object* v_res_1118_; 
v_depth_boxed_1117_ = lean_unbox_usize(v_depth_1111_);
lean_dec(v_depth_1111_);
v_res_1118_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__5(v_00_u03b2_1110_, v_depth_boxed_1117_, v_keys_1112_, v_vals_1113_, v_heq_1114_, v_i_1115_, v_entries_1116_);
lean_dec_ref(v_vals_1113_);
lean_dec_ref(v_keys_1112_);
return v_res_1118_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_1119_, lean_object* v_x_1120_, lean_object* v_x_1121_, lean_object* v_x_1122_, lean_object* v_x_1123_){
_start:
{
lean_object* v___x_1124_; 
v___x_1124_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__4_spec__5___redArg(v_x_1120_, v_x_1121_, v_x_1122_, v_x_1123_);
return v___x_1124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__0(lean_object* v_mvarId_1125_, lean_object* v_newEqs_1126_, uint8_t v___x_1127_, lean_object* v_h_x27_1128_, lean_object* v_newIndices_1129_, lean_object* v___x_1130_, lean_object* v___x_1131_, lean_object* v___x_1132_, lean_object* v___x_1133_, lean_object* v_e_1134_, lean_object* v___x_1135_, lean_object* v_newEq_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_){
_start:
{
lean_object* v___x_1142_; 
lean_inc(v_mvarId_1125_);
v___x_1142_ = l_Lean_MVarId_getType(v_mvarId_1125_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_);
if (lean_obj_tag(v___x_1142_) == 0)
{
lean_object* v_a_1143_; lean_object* v___x_1144_; 
v_a_1143_ = lean_ctor_get(v___x_1142_, 0);
lean_inc(v_a_1143_);
lean_dec_ref_known(v___x_1142_, 1);
lean_inc(v_mvarId_1125_);
v___x_1144_ = l_Lean_MVarId_getTag(v_mvarId_1125_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_);
if (lean_obj_tag(v___x_1144_) == 0)
{
lean_object* v_a_1145_; lean_object* v___x_1146_; uint8_t v___x_1147_; uint8_t v___x_1148_; lean_object* v___x_1149_; 
v_a_1145_ = lean_ctor_get(v___x_1144_, 0);
lean_inc(v_a_1145_);
lean_dec_ref_known(v___x_1144_, 1);
v___x_1146_ = lean_array_push(v_newEqs_1126_, v_newEq_1136_);
v___x_1147_ = 1;
v___x_1148_ = 1;
v___x_1149_ = l_Lean_Meta_mkForallFVars(v___x_1146_, v_a_1143_, v___x_1127_, v___x_1147_, v___x_1147_, v___x_1148_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_);
if (lean_obj_tag(v___x_1149_) == 0)
{
lean_object* v_a_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; 
v_a_1150_ = lean_ctor_get(v___x_1149_, 0);
lean_inc(v_a_1150_);
lean_dec_ref_known(v___x_1149_, 1);
v___x_1151_ = lean_unsigned_to_nat(1u);
v___x_1152_ = lean_mk_empty_array_with_capacity(v___x_1151_);
v___x_1153_ = lean_array_push(v___x_1152_, v_h_x27_1128_);
v___x_1154_ = l_Lean_Meta_mkForallFVars(v___x_1153_, v_a_1150_, v___x_1127_, v___x_1147_, v___x_1147_, v___x_1148_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_);
lean_dec_ref(v___x_1153_);
if (lean_obj_tag(v___x_1154_) == 0)
{
lean_object* v_a_1155_; lean_object* v___x_1156_; 
v_a_1155_ = lean_ctor_get(v___x_1154_, 0);
lean_inc(v_a_1155_);
lean_dec_ref_known(v___x_1154_, 1);
v___x_1156_ = l_Lean_Meta_mkForallFVars(v_newIndices_1129_, v_a_1155_, v___x_1127_, v___x_1147_, v___x_1147_, v___x_1148_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_);
if (lean_obj_tag(v___x_1156_) == 0)
{
lean_object* v_a_1157_; uint8_t v___x_1158_; lean_object* v___x_1159_; 
v_a_1157_ = lean_ctor_get(v___x_1156_, 0);
lean_inc(v_a_1157_);
lean_dec_ref_known(v___x_1156_, 1);
v___x_1158_ = 2;
v___x_1159_ = l_Lean_Meta_mkFreshExprMVarAt(v___x_1130_, v___x_1131_, v_a_1157_, v___x_1158_, v_a_1145_, v___x_1132_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_);
if (lean_obj_tag(v___x_1159_) == 0)
{
lean_object* v_a_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; 
v_a_1160_ = lean_ctor_get(v___x_1159_, 0);
lean_inc_n(v_a_1160_, 2);
lean_dec_ref_known(v___x_1159_, 1);
v___x_1161_ = l_Lean_mkAppN(v_a_1160_, v___x_1133_);
v___x_1162_ = l_Lean_Expr_app___override(v___x_1161_, v_e_1134_);
v___x_1163_ = l_Lean_mkAppN(v___x_1162_, v___x_1135_);
v___x_1164_ = l_Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1___redArg(v_mvarId_1125_, v___x_1163_, v___y_1138_);
lean_dec_ref(v___x_1164_);
v___x_1165_ = l_Lean_Expr_mvarId_x21(v_a_1160_);
lean_dec(v_a_1160_);
v___x_1166_ = lean_array_get_size(v_newIndices_1129_);
v___x_1167_ = lean_box(0);
v___x_1168_ = l_Lean_Meta_introNCore(v___x_1165_, v___x_1166_, v___x_1167_, v___x_1127_, v___x_1147_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_);
if (lean_obj_tag(v___x_1168_) == 0)
{
lean_object* v_a_1169_; lean_object* v_fst_1170_; lean_object* v_snd_1171_; lean_object* v___x_1172_; 
v_a_1169_ = lean_ctor_get(v___x_1168_, 0);
lean_inc(v_a_1169_);
lean_dec_ref_known(v___x_1168_, 1);
v_fst_1170_ = lean_ctor_get(v_a_1169_, 0);
lean_inc(v_fst_1170_);
v_snd_1171_ = lean_ctor_get(v_a_1169_, 1);
lean_inc(v_snd_1171_);
lean_dec(v_a_1169_);
v___x_1172_ = l_Lean_Meta_intro1Core(v_snd_1171_, v___x_1147_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_);
if (lean_obj_tag(v___x_1172_) == 0)
{
lean_object* v_a_1173_; lean_object* v___x_1175_; uint8_t v_isShared_1176_; uint8_t v_isSharedCheck_1184_; 
v_a_1173_ = lean_ctor_get(v___x_1172_, 0);
v_isSharedCheck_1184_ = !lean_is_exclusive(v___x_1172_);
if (v_isSharedCheck_1184_ == 0)
{
v___x_1175_ = v___x_1172_;
v_isShared_1176_ = v_isSharedCheck_1184_;
goto v_resetjp_1174_;
}
else
{
lean_inc(v_a_1173_);
lean_dec(v___x_1172_);
v___x_1175_ = lean_box(0);
v_isShared_1176_ = v_isSharedCheck_1184_;
goto v_resetjp_1174_;
}
v_resetjp_1174_:
{
lean_object* v_fst_1177_; lean_object* v_snd_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1182_; 
v_fst_1177_ = lean_ctor_get(v_a_1173_, 0);
lean_inc(v_fst_1177_);
v_snd_1178_ = lean_ctor_get(v_a_1173_, 1);
lean_inc(v_snd_1178_);
lean_dec(v_a_1173_);
v___x_1179_ = lean_array_get_size(v___x_1146_);
lean_dec_ref(v___x_1146_);
v___x_1180_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1180_, 0, v_snd_1178_);
lean_ctor_set(v___x_1180_, 1, v_fst_1170_);
lean_ctor_set(v___x_1180_, 2, v_fst_1177_);
lean_ctor_set(v___x_1180_, 3, v___x_1179_);
if (v_isShared_1176_ == 0)
{
lean_ctor_set(v___x_1175_, 0, v___x_1180_);
v___x_1182_ = v___x_1175_;
goto v_reusejp_1181_;
}
else
{
lean_object* v_reuseFailAlloc_1183_; 
v_reuseFailAlloc_1183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1183_, 0, v___x_1180_);
v___x_1182_ = v_reuseFailAlloc_1183_;
goto v_reusejp_1181_;
}
v_reusejp_1181_:
{
return v___x_1182_;
}
}
}
else
{
lean_object* v_a_1185_; lean_object* v___x_1187_; uint8_t v_isShared_1188_; uint8_t v_isSharedCheck_1192_; 
lean_dec(v_fst_1170_);
lean_dec_ref(v___x_1146_);
v_a_1185_ = lean_ctor_get(v___x_1172_, 0);
v_isSharedCheck_1192_ = !lean_is_exclusive(v___x_1172_);
if (v_isSharedCheck_1192_ == 0)
{
v___x_1187_ = v___x_1172_;
v_isShared_1188_ = v_isSharedCheck_1192_;
goto v_resetjp_1186_;
}
else
{
lean_inc(v_a_1185_);
lean_dec(v___x_1172_);
v___x_1187_ = lean_box(0);
v_isShared_1188_ = v_isSharedCheck_1192_;
goto v_resetjp_1186_;
}
v_resetjp_1186_:
{
lean_object* v___x_1190_; 
if (v_isShared_1188_ == 0)
{
v___x_1190_ = v___x_1187_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v_a_1185_);
v___x_1190_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
return v___x_1190_;
}
}
}
}
else
{
lean_object* v_a_1193_; lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1200_; 
lean_dec_ref(v___x_1146_);
v_a_1193_ = lean_ctor_get(v___x_1168_, 0);
v_isSharedCheck_1200_ = !lean_is_exclusive(v___x_1168_);
if (v_isSharedCheck_1200_ == 0)
{
v___x_1195_ = v___x_1168_;
v_isShared_1196_ = v_isSharedCheck_1200_;
goto v_resetjp_1194_;
}
else
{
lean_inc(v_a_1193_);
lean_dec(v___x_1168_);
v___x_1195_ = lean_box(0);
v_isShared_1196_ = v_isSharedCheck_1200_;
goto v_resetjp_1194_;
}
v_resetjp_1194_:
{
lean_object* v___x_1198_; 
if (v_isShared_1196_ == 0)
{
v___x_1198_ = v___x_1195_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v_a_1193_);
v___x_1198_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
return v___x_1198_;
}
}
}
}
else
{
lean_object* v_a_1201_; lean_object* v___x_1203_; uint8_t v_isShared_1204_; uint8_t v_isSharedCheck_1208_; 
lean_dec_ref(v___x_1146_);
lean_dec_ref(v_e_1134_);
lean_dec(v_mvarId_1125_);
v_a_1201_ = lean_ctor_get(v___x_1159_, 0);
v_isSharedCheck_1208_ = !lean_is_exclusive(v___x_1159_);
if (v_isSharedCheck_1208_ == 0)
{
v___x_1203_ = v___x_1159_;
v_isShared_1204_ = v_isSharedCheck_1208_;
goto v_resetjp_1202_;
}
else
{
lean_inc(v_a_1201_);
lean_dec(v___x_1159_);
v___x_1203_ = lean_box(0);
v_isShared_1204_ = v_isSharedCheck_1208_;
goto v_resetjp_1202_;
}
v_resetjp_1202_:
{
lean_object* v___x_1206_; 
if (v_isShared_1204_ == 0)
{
v___x_1206_ = v___x_1203_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v_a_1201_);
v___x_1206_ = v_reuseFailAlloc_1207_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
return v___x_1206_;
}
}
}
}
else
{
lean_object* v_a_1209_; lean_object* v___x_1211_; uint8_t v_isShared_1212_; uint8_t v_isSharedCheck_1216_; 
lean_dec_ref(v___x_1146_);
lean_dec(v_a_1145_);
lean_dec_ref(v_e_1134_);
lean_dec(v___x_1132_);
lean_dec_ref(v___x_1131_);
lean_dec_ref(v___x_1130_);
lean_dec(v_mvarId_1125_);
v_a_1209_ = lean_ctor_get(v___x_1156_, 0);
v_isSharedCheck_1216_ = !lean_is_exclusive(v___x_1156_);
if (v_isSharedCheck_1216_ == 0)
{
v___x_1211_ = v___x_1156_;
v_isShared_1212_ = v_isSharedCheck_1216_;
goto v_resetjp_1210_;
}
else
{
lean_inc(v_a_1209_);
lean_dec(v___x_1156_);
v___x_1211_ = lean_box(0);
v_isShared_1212_ = v_isSharedCheck_1216_;
goto v_resetjp_1210_;
}
v_resetjp_1210_:
{
lean_object* v___x_1214_; 
if (v_isShared_1212_ == 0)
{
v___x_1214_ = v___x_1211_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v_a_1209_);
v___x_1214_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
return v___x_1214_;
}
}
}
}
else
{
lean_object* v_a_1217_; lean_object* v___x_1219_; uint8_t v_isShared_1220_; uint8_t v_isSharedCheck_1224_; 
lean_dec_ref(v___x_1146_);
lean_dec(v_a_1145_);
lean_dec_ref(v_e_1134_);
lean_dec(v___x_1132_);
lean_dec_ref(v___x_1131_);
lean_dec_ref(v___x_1130_);
lean_dec(v_mvarId_1125_);
v_a_1217_ = lean_ctor_get(v___x_1154_, 0);
v_isSharedCheck_1224_ = !lean_is_exclusive(v___x_1154_);
if (v_isSharedCheck_1224_ == 0)
{
v___x_1219_ = v___x_1154_;
v_isShared_1220_ = v_isSharedCheck_1224_;
goto v_resetjp_1218_;
}
else
{
lean_inc(v_a_1217_);
lean_dec(v___x_1154_);
v___x_1219_ = lean_box(0);
v_isShared_1220_ = v_isSharedCheck_1224_;
goto v_resetjp_1218_;
}
v_resetjp_1218_:
{
lean_object* v___x_1222_; 
if (v_isShared_1220_ == 0)
{
v___x_1222_ = v___x_1219_;
goto v_reusejp_1221_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v_a_1217_);
v___x_1222_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1221_;
}
v_reusejp_1221_:
{
return v___x_1222_;
}
}
}
}
else
{
lean_object* v_a_1225_; lean_object* v___x_1227_; uint8_t v_isShared_1228_; uint8_t v_isSharedCheck_1232_; 
lean_dec_ref(v___x_1146_);
lean_dec(v_a_1145_);
lean_dec_ref(v_e_1134_);
lean_dec(v___x_1132_);
lean_dec_ref(v___x_1131_);
lean_dec_ref(v___x_1130_);
lean_dec_ref(v_h_x27_1128_);
lean_dec(v_mvarId_1125_);
v_a_1225_ = lean_ctor_get(v___x_1149_, 0);
v_isSharedCheck_1232_ = !lean_is_exclusive(v___x_1149_);
if (v_isSharedCheck_1232_ == 0)
{
v___x_1227_ = v___x_1149_;
v_isShared_1228_ = v_isSharedCheck_1232_;
goto v_resetjp_1226_;
}
else
{
lean_inc(v_a_1225_);
lean_dec(v___x_1149_);
v___x_1227_ = lean_box(0);
v_isShared_1228_ = v_isSharedCheck_1232_;
goto v_resetjp_1226_;
}
v_resetjp_1226_:
{
lean_object* v___x_1230_; 
if (v_isShared_1228_ == 0)
{
v___x_1230_ = v___x_1227_;
goto v_reusejp_1229_;
}
else
{
lean_object* v_reuseFailAlloc_1231_; 
v_reuseFailAlloc_1231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1231_, 0, v_a_1225_);
v___x_1230_ = v_reuseFailAlloc_1231_;
goto v_reusejp_1229_;
}
v_reusejp_1229_:
{
return v___x_1230_;
}
}
}
}
else
{
lean_object* v_a_1233_; lean_object* v___x_1235_; uint8_t v_isShared_1236_; uint8_t v_isSharedCheck_1240_; 
lean_dec(v_a_1143_);
lean_dec_ref(v_newEq_1136_);
lean_dec_ref(v_e_1134_);
lean_dec(v___x_1132_);
lean_dec_ref(v___x_1131_);
lean_dec_ref(v___x_1130_);
lean_dec_ref(v_h_x27_1128_);
lean_dec_ref(v_newEqs_1126_);
lean_dec(v_mvarId_1125_);
v_a_1233_ = lean_ctor_get(v___x_1144_, 0);
v_isSharedCheck_1240_ = !lean_is_exclusive(v___x_1144_);
if (v_isSharedCheck_1240_ == 0)
{
v___x_1235_ = v___x_1144_;
v_isShared_1236_ = v_isSharedCheck_1240_;
goto v_resetjp_1234_;
}
else
{
lean_inc(v_a_1233_);
lean_dec(v___x_1144_);
v___x_1235_ = lean_box(0);
v_isShared_1236_ = v_isSharedCheck_1240_;
goto v_resetjp_1234_;
}
v_resetjp_1234_:
{
lean_object* v___x_1238_; 
if (v_isShared_1236_ == 0)
{
v___x_1238_ = v___x_1235_;
goto v_reusejp_1237_;
}
else
{
lean_object* v_reuseFailAlloc_1239_; 
v_reuseFailAlloc_1239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1239_, 0, v_a_1233_);
v___x_1238_ = v_reuseFailAlloc_1239_;
goto v_reusejp_1237_;
}
v_reusejp_1237_:
{
return v___x_1238_;
}
}
}
}
else
{
lean_object* v_a_1241_; lean_object* v___x_1243_; uint8_t v_isShared_1244_; uint8_t v_isSharedCheck_1248_; 
lean_dec_ref(v_newEq_1136_);
lean_dec_ref(v_e_1134_);
lean_dec(v___x_1132_);
lean_dec_ref(v___x_1131_);
lean_dec_ref(v___x_1130_);
lean_dec_ref(v_h_x27_1128_);
lean_dec_ref(v_newEqs_1126_);
lean_dec(v_mvarId_1125_);
v_a_1241_ = lean_ctor_get(v___x_1142_, 0);
v_isSharedCheck_1248_ = !lean_is_exclusive(v___x_1142_);
if (v_isSharedCheck_1248_ == 0)
{
v___x_1243_ = v___x_1142_;
v_isShared_1244_ = v_isSharedCheck_1248_;
goto v_resetjp_1242_;
}
else
{
lean_inc(v_a_1241_);
lean_dec(v___x_1142_);
v___x_1243_ = lean_box(0);
v_isShared_1244_ = v_isSharedCheck_1248_;
goto v_resetjp_1242_;
}
v_resetjp_1242_:
{
lean_object* v___x_1246_; 
if (v_isShared_1244_ == 0)
{
v___x_1246_ = v___x_1243_;
goto v_reusejp_1245_;
}
else
{
lean_object* v_reuseFailAlloc_1247_; 
v_reuseFailAlloc_1247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1247_, 0, v_a_1241_);
v___x_1246_ = v_reuseFailAlloc_1247_;
goto v_reusejp_1245_;
}
v_reusejp_1245_:
{
return v___x_1246_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__0___boxed(lean_object** _args){
lean_object* v_mvarId_1249_ = _args[0];
lean_object* v_newEqs_1250_ = _args[1];
lean_object* v___x_1251_ = _args[2];
lean_object* v_h_x27_1252_ = _args[3];
lean_object* v_newIndices_1253_ = _args[4];
lean_object* v___x_1254_ = _args[5];
lean_object* v___x_1255_ = _args[6];
lean_object* v___x_1256_ = _args[7];
lean_object* v___x_1257_ = _args[8];
lean_object* v_e_1258_ = _args[9];
lean_object* v___x_1259_ = _args[10];
lean_object* v_newEq_1260_ = _args[11];
lean_object* v___y_1261_ = _args[12];
lean_object* v___y_1262_ = _args[13];
lean_object* v___y_1263_ = _args[14];
lean_object* v___y_1264_ = _args[15];
lean_object* v___y_1265_ = _args[16];
_start:
{
uint8_t v___x_6260__boxed_1266_; lean_object* v_res_1267_; 
v___x_6260__boxed_1266_ = lean_unbox(v___x_1251_);
v_res_1267_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__0(v_mvarId_1249_, v_newEqs_1250_, v___x_6260__boxed_1266_, v_h_x27_1252_, v_newIndices_1253_, v___x_1254_, v___x_1255_, v___x_1256_, v___x_1257_, v_e_1258_, v___x_1259_, v_newEq_1260_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_);
lean_dec(v___y_1264_);
lean_dec_ref(v___y_1263_);
lean_dec(v___y_1262_);
lean_dec_ref(v___y_1261_);
lean_dec_ref(v___x_1259_);
lean_dec_ref(v___x_1257_);
lean_dec_ref(v_newIndices_1253_);
return v_res_1267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__1(lean_object* v_e_1268_, lean_object* v_h_x27_1269_, lean_object* v_mvarId_1270_, uint8_t v___x_1271_, lean_object* v_newIndices_1272_, lean_object* v___x_1273_, lean_object* v___x_1274_, lean_object* v___x_1275_, lean_object* v___x_1276_, lean_object* v_newEqs_1277_, lean_object* v_newRefls_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_){
_start:
{
lean_object* v___x_1284_; 
lean_inc_ref(v_h_x27_1269_);
lean_inc_ref(v_e_1268_);
v___x_1284_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof(v_e_1268_, v_h_x27_1269_, v___y_1279_, v___y_1280_, v___y_1281_, v___y_1282_);
if (lean_obj_tag(v___x_1284_) == 0)
{
lean_object* v_a_1285_; lean_object* v_fst_1286_; lean_object* v_snd_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___f_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; 
v_a_1285_ = lean_ctor_get(v___x_1284_, 0);
lean_inc(v_a_1285_);
lean_dec_ref_known(v___x_1284_, 1);
v_fst_1286_ = lean_ctor_get(v_a_1285_, 0);
lean_inc(v_fst_1286_);
v_snd_1287_ = lean_ctor_get(v_a_1285_, 1);
lean_inc(v_snd_1287_);
lean_dec(v_a_1285_);
v___x_1288_ = lean_array_push(v_newRefls_1278_, v_snd_1287_);
v___x_1289_ = lean_box(v___x_1271_);
v___f_1290_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__0___boxed), 17, 11);
lean_closure_set(v___f_1290_, 0, v_mvarId_1270_);
lean_closure_set(v___f_1290_, 1, v_newEqs_1277_);
lean_closure_set(v___f_1290_, 2, v___x_1289_);
lean_closure_set(v___f_1290_, 3, v_h_x27_1269_);
lean_closure_set(v___f_1290_, 4, v_newIndices_1272_);
lean_closure_set(v___f_1290_, 5, v___x_1273_);
lean_closure_set(v___f_1290_, 6, v___x_1274_);
lean_closure_set(v___f_1290_, 7, v___x_1275_);
lean_closure_set(v___f_1290_, 8, v___x_1276_);
lean_closure_set(v___f_1290_, 9, v_e_1268_);
lean_closure_set(v___f_1290_, 10, v___x_1288_);
v___x_1291_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___redArg___closed__1));
v___x_1292_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0___redArg(v___x_1291_, v_fst_1286_, v___f_1290_, v___y_1279_, v___y_1280_, v___y_1281_, v___y_1282_);
return v___x_1292_;
}
else
{
lean_object* v_a_1293_; lean_object* v___x_1295_; uint8_t v_isShared_1296_; uint8_t v_isSharedCheck_1300_; 
lean_dec_ref(v_newRefls_1278_);
lean_dec_ref(v_newEqs_1277_);
lean_dec_ref(v___x_1276_);
lean_dec(v___x_1275_);
lean_dec_ref(v___x_1274_);
lean_dec_ref(v___x_1273_);
lean_dec_ref(v_newIndices_1272_);
lean_dec(v_mvarId_1270_);
lean_dec_ref(v_h_x27_1269_);
lean_dec_ref(v_e_1268_);
v_a_1293_ = lean_ctor_get(v___x_1284_, 0);
v_isSharedCheck_1300_ = !lean_is_exclusive(v___x_1284_);
if (v_isSharedCheck_1300_ == 0)
{
v___x_1295_ = v___x_1284_;
v_isShared_1296_ = v_isSharedCheck_1300_;
goto v_resetjp_1294_;
}
else
{
lean_inc(v_a_1293_);
lean_dec(v___x_1284_);
v___x_1295_ = lean_box(0);
v_isShared_1296_ = v_isSharedCheck_1300_;
goto v_resetjp_1294_;
}
v_resetjp_1294_:
{
lean_object* v___x_1298_; 
if (v_isShared_1296_ == 0)
{
v___x_1298_ = v___x_1295_;
goto v_reusejp_1297_;
}
else
{
lean_object* v_reuseFailAlloc_1299_; 
v_reuseFailAlloc_1299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1299_, 0, v_a_1293_);
v___x_1298_ = v_reuseFailAlloc_1299_;
goto v_reusejp_1297_;
}
v_reusejp_1297_:
{
return v___x_1298_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__1___boxed(lean_object* v_e_1301_, lean_object* v_h_x27_1302_, lean_object* v_mvarId_1303_, lean_object* v___x_1304_, lean_object* v_newIndices_1305_, lean_object* v___x_1306_, lean_object* v___x_1307_, lean_object* v___x_1308_, lean_object* v___x_1309_, lean_object* v_newEqs_1310_, lean_object* v_newRefls_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_){
_start:
{
uint8_t v___x_6512__boxed_1317_; lean_object* v_res_1318_; 
v___x_6512__boxed_1317_ = lean_unbox(v___x_1304_);
v_res_1318_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__1(v_e_1301_, v_h_x27_1302_, v_mvarId_1303_, v___x_6512__boxed_1317_, v_newIndices_1305_, v___x_1306_, v___x_1307_, v___x_1308_, v___x_1309_, v_newEqs_1310_, v_newRefls_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_);
lean_dec(v___y_1315_);
lean_dec_ref(v___y_1314_);
lean_dec(v___y_1313_);
lean_dec_ref(v___y_1312_);
return v_res_1318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__2(lean_object* v_e_1319_, lean_object* v_mvarId_1320_, uint8_t v___x_1321_, lean_object* v_newIndices_1322_, lean_object* v___x_1323_, lean_object* v___x_1324_, lean_object* v___x_1325_, lean_object* v___x_1326_, lean_object* v_h_x27_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_){
_start:
{
lean_object* v___x_1333_; lean_object* v___f_1334_; lean_object* v___x_1335_; 
v___x_1333_ = lean_box(v___x_1321_);
lean_inc_ref(v___x_1326_);
lean_inc_ref(v_newIndices_1322_);
v___f_1334_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__1___boxed), 16, 9);
lean_closure_set(v___f_1334_, 0, v_e_1319_);
lean_closure_set(v___f_1334_, 1, v_h_x27_1327_);
lean_closure_set(v___f_1334_, 2, v_mvarId_1320_);
lean_closure_set(v___f_1334_, 3, v___x_1333_);
lean_closure_set(v___f_1334_, 4, v_newIndices_1322_);
lean_closure_set(v___f_1334_, 5, v___x_1323_);
lean_closure_set(v___f_1334_, 6, v___x_1324_);
lean_closure_set(v___f_1334_, 7, v___x_1325_);
lean_closure_set(v___f_1334_, 8, v___x_1326_);
v___x_1335_ = l_Lean_Meta_withNewEqs___redArg(v___x_1326_, v_newIndices_1322_, v___f_1334_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_);
return v___x_1335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__2___boxed(lean_object* v_e_1336_, lean_object* v_mvarId_1337_, lean_object* v___x_1338_, lean_object* v_newIndices_1339_, lean_object* v___x_1340_, lean_object* v___x_1341_, lean_object* v___x_1342_, lean_object* v___x_1343_, lean_object* v_h_x27_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_){
_start:
{
uint8_t v___x_6577__boxed_1350_; lean_object* v_res_1351_; 
v___x_6577__boxed_1350_ = lean_unbox(v___x_1338_);
v_res_1351_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__2(v_e_1336_, v_mvarId_1337_, v___x_6577__boxed_1350_, v_newIndices_1339_, v___x_1340_, v___x_1341_, v___x_1342_, v___x_1343_, v_h_x27_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_);
lean_dec(v___y_1348_);
lean_dec_ref(v___y_1347_);
lean_dec(v___y_1346_);
lean_dec_ref(v___y_1345_);
return v_res_1351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__3(lean_object* v_e_1355_, lean_object* v_mvarId_1356_, uint8_t v___x_1357_, lean_object* v___x_1358_, lean_object* v___x_1359_, lean_object* v___x_1360_, lean_object* v___x_1361_, lean_object* v___x_1362_, lean_object* v_varName_x3f_1363_, lean_object* v_newIndices_1364_, lean_object* v_x_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_){
_start:
{
lean_object* v___x_1371_; lean_object* v___f_1372_; lean_object* v___x_1373_; 
v___x_1371_ = lean_box(v___x_1357_);
lean_inc_ref(v_newIndices_1364_);
v___f_1372_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__2___boxed), 14, 8);
lean_closure_set(v___f_1372_, 0, v_e_1355_);
lean_closure_set(v___f_1372_, 1, v_mvarId_1356_);
lean_closure_set(v___f_1372_, 2, v___x_1371_);
lean_closure_set(v___f_1372_, 3, v_newIndices_1364_);
lean_closure_set(v___f_1372_, 4, v___x_1358_);
lean_closure_set(v___f_1372_, 5, v___x_1359_);
lean_closure_set(v___f_1372_, 6, v___x_1360_);
lean_closure_set(v___f_1372_, 7, v___x_1361_);
v___x_1373_ = l_Lean_mkAppN(v___x_1362_, v_newIndices_1364_);
lean_dec_ref(v_newIndices_1364_);
if (lean_obj_tag(v_varName_x3f_1363_) == 1)
{
lean_object* v_val_1374_; lean_object* v___x_1375_; 
v_val_1374_ = lean_ctor_get(v_varName_x3f_1363_, 0);
lean_inc(v_val_1374_);
lean_dec_ref_known(v_varName_x3f_1363_, 1);
v___x_1375_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0___redArg(v_val_1374_, v___x_1373_, v___f_1372_, v___y_1366_, v___y_1367_, v___y_1368_, v___y_1369_);
return v___x_1375_;
}
else
{
lean_object* v___x_1376_; lean_object* v___x_1377_; 
lean_dec(v_varName_x3f_1363_);
v___x_1376_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__3___closed__1));
v___x_1377_ = l_Lean_Core_mkFreshUserName(v___x_1376_, v___y_1368_, v___y_1369_);
if (lean_obj_tag(v___x_1377_) == 0)
{
lean_object* v_a_1378_; lean_object* v___x_1379_; 
v_a_1378_ = lean_ctor_get(v___x_1377_, 0);
lean_inc(v_a_1378_);
lean_dec_ref_known(v___x_1377_, 1);
v___x_1379_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0___redArg(v_a_1378_, v___x_1373_, v___f_1372_, v___y_1366_, v___y_1367_, v___y_1368_, v___y_1369_);
return v___x_1379_;
}
else
{
lean_object* v_a_1380_; lean_object* v___x_1382_; uint8_t v_isShared_1383_; uint8_t v_isSharedCheck_1387_; 
lean_dec_ref(v___x_1373_);
lean_dec_ref(v___f_1372_);
v_a_1380_ = lean_ctor_get(v___x_1377_, 0);
v_isSharedCheck_1387_ = !lean_is_exclusive(v___x_1377_);
if (v_isSharedCheck_1387_ == 0)
{
v___x_1382_ = v___x_1377_;
v_isShared_1383_ = v_isSharedCheck_1387_;
goto v_resetjp_1381_;
}
else
{
lean_inc(v_a_1380_);
lean_dec(v___x_1377_);
v___x_1382_ = lean_box(0);
v_isShared_1383_ = v_isSharedCheck_1387_;
goto v_resetjp_1381_;
}
v_resetjp_1381_:
{
lean_object* v___x_1385_; 
if (v_isShared_1383_ == 0)
{
v___x_1385_ = v___x_1382_;
goto v_reusejp_1384_;
}
else
{
lean_object* v_reuseFailAlloc_1386_; 
v_reuseFailAlloc_1386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1386_, 0, v_a_1380_);
v___x_1385_ = v_reuseFailAlloc_1386_;
goto v_reusejp_1384_;
}
v_reusejp_1384_:
{
return v___x_1385_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__3___boxed(lean_object* v_e_1388_, lean_object* v_mvarId_1389_, lean_object* v___x_1390_, lean_object* v___x_1391_, lean_object* v___x_1392_, lean_object* v___x_1393_, lean_object* v___x_1394_, lean_object* v___x_1395_, lean_object* v_varName_x3f_1396_, lean_object* v_newIndices_1397_, lean_object* v_x_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_){
_start:
{
uint8_t v___x_6619__boxed_1404_; lean_object* v_res_1405_; 
v___x_6619__boxed_1404_ = lean_unbox(v___x_1390_);
v_res_1405_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__3(v_e_1388_, v_mvarId_1389_, v___x_6619__boxed_1404_, v___x_1391_, v___x_1392_, v___x_1393_, v___x_1394_, v___x_1395_, v_varName_x3f_1396_, v_newIndices_1397_, v_x_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_);
lean_dec(v___y_1402_);
lean_dec_ref(v___y_1401_);
lean_dec(v___y_1400_);
lean_dec_ref(v___y_1399_);
lean_dec_ref(v_x_1398_);
return v_res_1405_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__4(void){
_start:
{
lean_object* v___x_1412_; lean_object* v___x_1413_; 
v___x_1412_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__3));
v___x_1413_ = l_Lean_MessageData_ofFormat(v___x_1412_);
return v___x_1413_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__5(void){
_start:
{
lean_object* v___x_1414_; lean_object* v___x_1415_; 
v___x_1414_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__4, &l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__4_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__4);
v___x_1415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1415_, 0, v___x_1414_);
return v___x_1415_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__8(void){
_start:
{
lean_object* v___x_1419_; lean_object* v___x_1420_; 
v___x_1419_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__7));
v___x_1420_ = l_Lean_MessageData_ofFormat(v___x_1419_);
return v___x_1420_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__9(void){
_start:
{
lean_object* v___x_1421_; lean_object* v___x_1422_; 
v___x_1421_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__8, &l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__8_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__8);
v___x_1422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1422_, 0, v___x_1421_);
return v___x_1422_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__12(void){
_start:
{
lean_object* v___x_1426_; lean_object* v___x_1427_; 
v___x_1426_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__11));
v___x_1427_ = l_Lean_MessageData_ofFormat(v___x_1426_);
return v___x_1427_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__13(void){
_start:
{
lean_object* v___x_1428_; lean_object* v___x_1429_; 
v___x_1428_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__12, &l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__12_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__12);
v___x_1429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1429_, 0, v___x_1428_);
return v___x_1429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0(lean_object* v_mvarId_1430_, lean_object* v_e_1431_, lean_object* v___x_1432_, lean_object* v___x_1433_, lean_object* v_varName_x3f_1434_, lean_object* v_x_1435_, lean_object* v_x_1436_, lean_object* v_x_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_){
_start:
{
if (lean_obj_tag(v_x_1435_) == 5)
{
lean_object* v_fn_1443_; lean_object* v_arg_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; 
v_fn_1443_ = lean_ctor_get(v_x_1435_, 0);
lean_inc_ref(v_fn_1443_);
v_arg_1444_ = lean_ctor_get(v_x_1435_, 1);
lean_inc_ref(v_arg_1444_);
lean_dec_ref_known(v_x_1435_, 2);
v___x_1445_ = lean_array_set(v_x_1436_, v_x_1437_, v_arg_1444_);
v___x_1446_ = lean_unsigned_to_nat(1u);
v___x_1447_ = lean_nat_sub(v_x_1437_, v___x_1446_);
lean_dec(v_x_1437_);
v_x_1435_ = v_fn_1443_;
v_x_1436_ = v___x_1445_;
v_x_1437_ = v___x_1447_;
goto _start;
}
else
{
lean_object* v___x_1449_; lean_object* v___y_1451_; lean_object* v___y_1452_; lean_object* v___y_1453_; lean_object* v___y_1454_; 
lean_dec(v_x_1437_);
v___x_1449_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__1));
if (lean_obj_tag(v_x_1435_) == 4)
{
lean_object* v_declName_1457_; lean_object* v___x_1458_; lean_object* v_env_1459_; uint8_t v___x_1460_; lean_object* v___x_1461_; 
v_declName_1457_ = lean_ctor_get(v_x_1435_, 0);
v___x_1458_ = lean_st_ref_get(v___y_1441_);
v_env_1459_ = lean_ctor_get(v___x_1458_, 0);
lean_inc_ref(v_env_1459_);
lean_dec(v___x_1458_);
v___x_1460_ = 0;
lean_inc(v_declName_1457_);
v___x_1461_ = l_Lean_Environment_find_x3f(v_env_1459_, v_declName_1457_, v___x_1460_);
if (lean_obj_tag(v___x_1461_) == 0)
{
lean_dec_ref_known(v_x_1435_, 2);
lean_dec_ref(v_x_1436_);
lean_dec(v_varName_x3f_1434_);
lean_dec_ref(v___x_1433_);
lean_dec_ref(v___x_1432_);
lean_dec_ref(v_e_1431_);
v___y_1451_ = v___y_1438_;
v___y_1452_ = v___y_1439_;
v___y_1453_ = v___y_1440_;
v___y_1454_ = v___y_1441_;
goto v___jp_1450_;
}
else
{
lean_object* v_val_1462_; 
v_val_1462_ = lean_ctor_get(v___x_1461_, 0);
lean_inc(v_val_1462_);
lean_dec_ref_known(v___x_1461_, 1);
if (lean_obj_tag(v_val_1462_) == 5)
{
lean_object* v_val_1463_; lean_object* v_numParams_1464_; lean_object* v_numIndices_1465_; lean_object* v___y_1467_; lean_object* v___y_1468_; lean_object* v___y_1469_; lean_object* v___y_1470_; lean_object* v___y_1491_; lean_object* v___y_1492_; lean_object* v___y_1493_; lean_object* v___y_1494_; lean_object* v___x_1508_; uint8_t v___x_1509_; 
v_val_1463_ = lean_ctor_get(v_val_1462_, 0);
lean_inc_ref(v_val_1463_);
lean_dec_ref_known(v_val_1462_, 1);
v_numParams_1464_ = lean_ctor_get(v_val_1463_, 1);
lean_inc(v_numParams_1464_);
v_numIndices_1465_ = lean_ctor_get(v_val_1463_, 2);
lean_inc(v_numIndices_1465_);
lean_dec_ref(v_val_1463_);
v___x_1508_ = lean_unsigned_to_nat(0u);
v___x_1509_ = lean_nat_dec_lt(v___x_1508_, v_numIndices_1465_);
if (v___x_1509_ == 0)
{
lean_object* v___x_1510_; lean_object* v___x_1511_; 
v___x_1510_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__13, &l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__13_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__13);
lean_inc(v_mvarId_1430_);
v___x_1511_ = l_Lean_Meta_throwTacticEx___redArg(v___x_1449_, v_mvarId_1430_, v___x_1510_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_);
if (lean_obj_tag(v___x_1511_) == 0)
{
lean_dec_ref_known(v___x_1511_, 1);
v___y_1491_ = v___y_1438_;
v___y_1492_ = v___y_1439_;
v___y_1493_ = v___y_1440_;
v___y_1494_ = v___y_1441_;
goto v___jp_1490_;
}
else
{
lean_object* v_a_1512_; lean_object* v___x_1514_; uint8_t v_isShared_1515_; uint8_t v_isSharedCheck_1519_; 
lean_dec(v_numIndices_1465_);
lean_dec(v_numParams_1464_);
lean_dec_ref_known(v_x_1435_, 2);
lean_dec_ref(v_x_1436_);
lean_dec(v_varName_x3f_1434_);
lean_dec_ref(v___x_1433_);
lean_dec_ref(v___x_1432_);
lean_dec_ref(v_e_1431_);
lean_dec(v_mvarId_1430_);
v_a_1512_ = lean_ctor_get(v___x_1511_, 0);
v_isSharedCheck_1519_ = !lean_is_exclusive(v___x_1511_);
if (v_isSharedCheck_1519_ == 0)
{
v___x_1514_ = v___x_1511_;
v_isShared_1515_ = v_isSharedCheck_1519_;
goto v_resetjp_1513_;
}
else
{
lean_inc(v_a_1512_);
lean_dec(v___x_1511_);
v___x_1514_ = lean_box(0);
v_isShared_1515_ = v_isSharedCheck_1519_;
goto v_resetjp_1513_;
}
v_resetjp_1513_:
{
lean_object* v___x_1517_; 
if (v_isShared_1515_ == 0)
{
v___x_1517_ = v___x_1514_;
goto v_reusejp_1516_;
}
else
{
lean_object* v_reuseFailAlloc_1518_; 
v_reuseFailAlloc_1518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1518_, 0, v_a_1512_);
v___x_1517_ = v_reuseFailAlloc_1518_;
goto v_reusejp_1516_;
}
v_reusejp_1516_:
{
return v___x_1517_;
}
}
}
}
else
{
v___y_1491_ = v___y_1438_;
v___y_1492_ = v___y_1439_;
v___y_1493_ = v___y_1440_;
v___y_1494_ = v___y_1441_;
goto v___jp_1490_;
}
v___jp_1466_:
{
lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; 
v___x_1471_ = lean_unsigned_to_nat(0u);
v___x_1472_ = l_Array_extract___redArg(v_x_1436_, v___x_1471_, v_numParams_1464_);
v___x_1473_ = l_Lean_mkAppN(v_x_1435_, v___x_1472_);
lean_dec_ref(v___x_1472_);
lean_inc(v___y_1470_);
lean_inc_ref(v___y_1469_);
lean_inc(v___y_1468_);
lean_inc_ref(v___y_1467_);
lean_inc_ref(v___x_1473_);
v___x_1474_ = lean_infer_type(v___x_1473_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_);
if (lean_obj_tag(v___x_1474_) == 0)
{
lean_object* v_a_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___f_1480_; lean_object* v___x_1481_; 
v_a_1475_ = lean_ctor_get(v___x_1474_, 0);
lean_inc(v_a_1475_);
lean_dec_ref_known(v___x_1474_, 1);
v___x_1476_ = lean_array_get_size(v_x_1436_);
v___x_1477_ = lean_nat_sub(v___x_1476_, v_numIndices_1465_);
lean_dec(v_numIndices_1465_);
v___x_1478_ = l_Array_extract___redArg(v_x_1436_, v___x_1477_, v___x_1476_);
lean_dec_ref(v_x_1436_);
v___x_1479_ = lean_box(v___x_1460_);
v___f_1480_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__3___boxed), 16, 9);
lean_closure_set(v___f_1480_, 0, v_e_1431_);
lean_closure_set(v___f_1480_, 1, v_mvarId_1430_);
lean_closure_set(v___f_1480_, 2, v___x_1479_);
lean_closure_set(v___f_1480_, 3, v___x_1432_);
lean_closure_set(v___f_1480_, 4, v___x_1433_);
lean_closure_set(v___f_1480_, 5, v___x_1471_);
lean_closure_set(v___f_1480_, 6, v___x_1478_);
lean_closure_set(v___f_1480_, 7, v___x_1473_);
lean_closure_set(v___f_1480_, 8, v_varName_x3f_1434_);
v___x_1481_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_generalizeTargetsEq_spec__0___redArg(v_a_1475_, v___f_1480_, v___x_1460_, v___x_1460_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_);
return v___x_1481_;
}
else
{
lean_object* v_a_1482_; lean_object* v___x_1484_; uint8_t v_isShared_1485_; uint8_t v_isSharedCheck_1489_; 
lean_dec_ref(v___x_1473_);
lean_dec(v_numIndices_1465_);
lean_dec_ref(v_x_1436_);
lean_dec(v_varName_x3f_1434_);
lean_dec_ref(v___x_1433_);
lean_dec_ref(v___x_1432_);
lean_dec_ref(v_e_1431_);
lean_dec(v_mvarId_1430_);
v_a_1482_ = lean_ctor_get(v___x_1474_, 0);
v_isSharedCheck_1489_ = !lean_is_exclusive(v___x_1474_);
if (v_isSharedCheck_1489_ == 0)
{
v___x_1484_ = v___x_1474_;
v_isShared_1485_ = v_isSharedCheck_1489_;
goto v_resetjp_1483_;
}
else
{
lean_inc(v_a_1482_);
lean_dec(v___x_1474_);
v___x_1484_ = lean_box(0);
v_isShared_1485_ = v_isSharedCheck_1489_;
goto v_resetjp_1483_;
}
v_resetjp_1483_:
{
lean_object* v___x_1487_; 
if (v_isShared_1485_ == 0)
{
v___x_1487_ = v___x_1484_;
goto v_reusejp_1486_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1488_, 0, v_a_1482_);
v___x_1487_ = v_reuseFailAlloc_1488_;
goto v_reusejp_1486_;
}
v_reusejp_1486_:
{
return v___x_1487_;
}
}
}
}
v___jp_1490_:
{
lean_object* v___x_1495_; lean_object* v___x_1496_; uint8_t v___x_1497_; 
v___x_1495_ = lean_array_get_size(v_x_1436_);
v___x_1496_ = lean_nat_add(v_numIndices_1465_, v_numParams_1464_);
v___x_1497_ = lean_nat_dec_eq(v___x_1495_, v___x_1496_);
lean_dec(v___x_1496_);
if (v___x_1497_ == 0)
{
lean_object* v___x_1498_; lean_object* v___x_1499_; 
v___x_1498_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__9, &l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__9_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__9);
lean_inc(v_mvarId_1430_);
v___x_1499_ = l_Lean_Meta_throwTacticEx___redArg(v___x_1449_, v_mvarId_1430_, v___x_1498_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_);
if (lean_obj_tag(v___x_1499_) == 0)
{
lean_dec_ref_known(v___x_1499_, 1);
v___y_1467_ = v___y_1491_;
v___y_1468_ = v___y_1492_;
v___y_1469_ = v___y_1493_;
v___y_1470_ = v___y_1494_;
goto v___jp_1466_;
}
else
{
lean_object* v_a_1500_; lean_object* v___x_1502_; uint8_t v_isShared_1503_; uint8_t v_isSharedCheck_1507_; 
lean_dec(v_numIndices_1465_);
lean_dec(v_numParams_1464_);
lean_dec_ref_known(v_x_1435_, 2);
lean_dec_ref(v_x_1436_);
lean_dec(v_varName_x3f_1434_);
lean_dec_ref(v___x_1433_);
lean_dec_ref(v___x_1432_);
lean_dec_ref(v_e_1431_);
lean_dec(v_mvarId_1430_);
v_a_1500_ = lean_ctor_get(v___x_1499_, 0);
v_isSharedCheck_1507_ = !lean_is_exclusive(v___x_1499_);
if (v_isSharedCheck_1507_ == 0)
{
v___x_1502_ = v___x_1499_;
v_isShared_1503_ = v_isSharedCheck_1507_;
goto v_resetjp_1501_;
}
else
{
lean_inc(v_a_1500_);
lean_dec(v___x_1499_);
v___x_1502_ = lean_box(0);
v_isShared_1503_ = v_isSharedCheck_1507_;
goto v_resetjp_1501_;
}
v_resetjp_1501_:
{
lean_object* v___x_1505_; 
if (v_isShared_1503_ == 0)
{
v___x_1505_ = v___x_1502_;
goto v_reusejp_1504_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v_a_1500_);
v___x_1505_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1504_;
}
v_reusejp_1504_:
{
return v___x_1505_;
}
}
}
}
else
{
v___y_1467_ = v___y_1491_;
v___y_1468_ = v___y_1492_;
v___y_1469_ = v___y_1493_;
v___y_1470_ = v___y_1494_;
goto v___jp_1466_;
}
}
}
else
{
lean_dec(v_val_1462_);
lean_dec_ref_known(v_x_1435_, 2);
lean_dec_ref(v_x_1436_);
lean_dec(v_varName_x3f_1434_);
lean_dec_ref(v___x_1433_);
lean_dec_ref(v___x_1432_);
lean_dec_ref(v_e_1431_);
v___y_1451_ = v___y_1438_;
v___y_1452_ = v___y_1439_;
v___y_1453_ = v___y_1440_;
v___y_1454_ = v___y_1441_;
goto v___jp_1450_;
}
}
}
else
{
lean_dec_ref(v_x_1436_);
lean_dec_ref(v_x_1435_);
lean_dec(v_varName_x3f_1434_);
lean_dec_ref(v___x_1433_);
lean_dec_ref(v___x_1432_);
lean_dec_ref(v_e_1431_);
v___y_1451_ = v___y_1438_;
v___y_1452_ = v___y_1439_;
v___y_1453_ = v___y_1440_;
v___y_1454_ = v___y_1441_;
goto v___jp_1450_;
}
v___jp_1450_:
{
lean_object* v___x_1455_; lean_object* v___x_1456_; 
v___x_1455_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__5, &l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__5_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__5);
v___x_1456_ = l_Lean_Meta_throwTacticEx___redArg(v___x_1449_, v_mvarId_1430_, v___x_1455_, v___y_1451_, v___y_1452_, v___y_1453_, v___y_1454_);
return v___x_1456_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___boxed(lean_object* v_mvarId_1520_, lean_object* v_e_1521_, lean_object* v___x_1522_, lean_object* v___x_1523_, lean_object* v_varName_x3f_1524_, lean_object* v_x_1525_, lean_object* v_x_1526_, lean_object* v_x_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_){
_start:
{
lean_object* v_res_1533_; 
v_res_1533_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0(v_mvarId_1520_, v_e_1521_, v___x_1522_, v___x_1523_, v_varName_x3f_1524_, v_x_1525_, v_x_1526_, v_x_1527_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_);
lean_dec(v___y_1531_);
lean_dec_ref(v___y_1530_);
lean_dec(v___y_1529_);
lean_dec_ref(v___y_1528_);
return v_res_1533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeIndices_x27___lam__0(lean_object* v_mvarId_1534_, lean_object* v_e_1535_, lean_object* v_varName_x3f_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_){
_start:
{
lean_object* v___x_1542_; lean_object* v___x_1543_; 
v___x_1542_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__1));
lean_inc(v_mvarId_1534_);
v___x_1543_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_1534_, v___x_1542_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_);
if (lean_obj_tag(v___x_1543_) == 0)
{
lean_object* v_lctx_1544_; lean_object* v_localInstances_1545_; lean_object* v___x_1546_; 
lean_dec_ref_known(v___x_1543_, 1);
v_lctx_1544_ = lean_ctor_get(v___y_1537_, 2);
lean_inc_ref(v_lctx_1544_);
v_localInstances_1545_ = lean_ctor_get(v___y_1537_, 3);
lean_inc_ref(v_localInstances_1545_);
lean_inc(v___y_1540_);
lean_inc_ref(v___y_1539_);
lean_inc(v___y_1538_);
lean_inc_ref(v___y_1537_);
lean_inc_ref(v_e_1535_);
v___x_1546_ = lean_infer_type(v_e_1535_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_);
if (lean_obj_tag(v___x_1546_) == 0)
{
lean_object* v_a_1547_; lean_object* v___x_1548_; 
v_a_1547_ = lean_ctor_get(v___x_1546_, 0);
lean_inc(v_a_1547_);
lean_dec_ref_known(v___x_1546_, 1);
v___x_1548_ = l_Lean_Meta_whnfD(v_a_1547_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_);
if (lean_obj_tag(v___x_1548_) == 0)
{
lean_object* v_a_1549_; lean_object* v_dummy_1550_; lean_object* v_nargs_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; 
v_a_1549_ = lean_ctor_get(v___x_1548_, 0);
lean_inc(v_a_1549_);
lean_dec_ref_known(v___x_1548_, 1);
v_dummy_1550_ = lean_obj_once(&l_Lean_Meta_getInductiveUniverseAndParams___closed__0, &l_Lean_Meta_getInductiveUniverseAndParams___closed__0_once, _init_l_Lean_Meta_getInductiveUniverseAndParams___closed__0);
v_nargs_1551_ = l_Lean_Expr_getAppNumArgs(v_a_1549_);
lean_inc(v_nargs_1551_);
v___x_1552_ = lean_mk_array(v_nargs_1551_, v_dummy_1550_);
v___x_1553_ = lean_unsigned_to_nat(1u);
v___x_1554_ = lean_nat_sub(v_nargs_1551_, v___x_1553_);
lean_dec(v_nargs_1551_);
v___x_1555_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0(v_mvarId_1534_, v_e_1535_, v_lctx_1544_, v_localInstances_1545_, v_varName_x3f_1536_, v_a_1549_, v___x_1552_, v___x_1554_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_);
lean_dec(v___y_1540_);
lean_dec_ref(v___y_1539_);
lean_dec(v___y_1538_);
lean_dec_ref(v___y_1537_);
return v___x_1555_;
}
else
{
lean_object* v_a_1556_; lean_object* v___x_1558_; uint8_t v_isShared_1559_; uint8_t v_isSharedCheck_1563_; 
lean_dec_ref(v_localInstances_1545_);
lean_dec_ref(v_lctx_1544_);
lean_dec(v___y_1540_);
lean_dec_ref(v___y_1539_);
lean_dec(v___y_1538_);
lean_dec_ref(v___y_1537_);
lean_dec(v_varName_x3f_1536_);
lean_dec_ref(v_e_1535_);
lean_dec(v_mvarId_1534_);
v_a_1556_ = lean_ctor_get(v___x_1548_, 0);
v_isSharedCheck_1563_ = !lean_is_exclusive(v___x_1548_);
if (v_isSharedCheck_1563_ == 0)
{
v___x_1558_ = v___x_1548_;
v_isShared_1559_ = v_isSharedCheck_1563_;
goto v_resetjp_1557_;
}
else
{
lean_inc(v_a_1556_);
lean_dec(v___x_1548_);
v___x_1558_ = lean_box(0);
v_isShared_1559_ = v_isSharedCheck_1563_;
goto v_resetjp_1557_;
}
v_resetjp_1557_:
{
lean_object* v___x_1561_; 
if (v_isShared_1559_ == 0)
{
v___x_1561_ = v___x_1558_;
goto v_reusejp_1560_;
}
else
{
lean_object* v_reuseFailAlloc_1562_; 
v_reuseFailAlloc_1562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1562_, 0, v_a_1556_);
v___x_1561_ = v_reuseFailAlloc_1562_;
goto v_reusejp_1560_;
}
v_reusejp_1560_:
{
return v___x_1561_;
}
}
}
}
else
{
lean_object* v_a_1564_; lean_object* v___x_1566_; uint8_t v_isShared_1567_; uint8_t v_isSharedCheck_1571_; 
lean_dec_ref(v_localInstances_1545_);
lean_dec_ref(v_lctx_1544_);
lean_dec(v___y_1540_);
lean_dec_ref(v___y_1539_);
lean_dec(v___y_1538_);
lean_dec_ref(v___y_1537_);
lean_dec(v_varName_x3f_1536_);
lean_dec_ref(v_e_1535_);
lean_dec(v_mvarId_1534_);
v_a_1564_ = lean_ctor_get(v___x_1546_, 0);
v_isSharedCheck_1571_ = !lean_is_exclusive(v___x_1546_);
if (v_isSharedCheck_1571_ == 0)
{
v___x_1566_ = v___x_1546_;
v_isShared_1567_ = v_isSharedCheck_1571_;
goto v_resetjp_1565_;
}
else
{
lean_inc(v_a_1564_);
lean_dec(v___x_1546_);
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
else
{
lean_object* v_a_1572_; lean_object* v___x_1574_; uint8_t v_isShared_1575_; uint8_t v_isSharedCheck_1579_; 
lean_dec(v___y_1540_);
lean_dec_ref(v___y_1539_);
lean_dec(v___y_1538_);
lean_dec_ref(v___y_1537_);
lean_dec(v_varName_x3f_1536_);
lean_dec_ref(v_e_1535_);
lean_dec(v_mvarId_1534_);
v_a_1572_ = lean_ctor_get(v___x_1543_, 0);
v_isSharedCheck_1579_ = !lean_is_exclusive(v___x_1543_);
if (v_isSharedCheck_1579_ == 0)
{
v___x_1574_ = v___x_1543_;
v_isShared_1575_ = v_isSharedCheck_1579_;
goto v_resetjp_1573_;
}
else
{
lean_inc(v_a_1572_);
lean_dec(v___x_1543_);
v___x_1574_ = lean_box(0);
v_isShared_1575_ = v_isSharedCheck_1579_;
goto v_resetjp_1573_;
}
v_resetjp_1573_:
{
lean_object* v___x_1577_; 
if (v_isShared_1575_ == 0)
{
v___x_1577_ = v___x_1574_;
goto v_reusejp_1576_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v_a_1572_);
v___x_1577_ = v_reuseFailAlloc_1578_;
goto v_reusejp_1576_;
}
v_reusejp_1576_:
{
return v___x_1577_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeIndices_x27___lam__0___boxed(lean_object* v_mvarId_1580_, lean_object* v_e_1581_, lean_object* v_varName_x3f_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_){
_start:
{
lean_object* v_res_1588_; 
v_res_1588_ = l_Lean_Meta_generalizeIndices_x27___lam__0(v_mvarId_1580_, v_e_1581_, v_varName_x3f_1582_, v___y_1583_, v___y_1584_, v___y_1585_, v___y_1586_);
return v_res_1588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeIndices_x27(lean_object* v_mvarId_1589_, lean_object* v_e_1590_, lean_object* v_varName_x3f_1591_, lean_object* v_a_1592_, lean_object* v_a_1593_, lean_object* v_a_1594_, lean_object* v_a_1595_){
_start:
{
lean_object* v___f_1597_; lean_object* v___x_1598_; 
lean_inc(v_mvarId_1589_);
v___f_1597_ = lean_alloc_closure((void*)(l_Lean_Meta_generalizeIndices_x27___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1597_, 0, v_mvarId_1589_);
lean_closure_set(v___f_1597_, 1, v_e_1590_);
lean_closure_set(v___f_1597_, 2, v_varName_x3f_1591_);
v___x_1598_ = l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2___redArg(v_mvarId_1589_, v___f_1597_, v_a_1592_, v_a_1593_, v_a_1594_, v_a_1595_);
return v___x_1598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeIndices_x27___boxed(lean_object* v_mvarId_1599_, lean_object* v_e_1600_, lean_object* v_varName_x3f_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_){
_start:
{
lean_object* v_res_1607_; 
v_res_1607_ = l_Lean_Meta_generalizeIndices_x27(v_mvarId_1599_, v_e_1600_, v_varName_x3f_1601_, v_a_1602_, v_a_1603_, v_a_1604_, v_a_1605_);
lean_dec(v_a_1605_);
lean_dec_ref(v_a_1604_);
lean_dec(v_a_1603_);
lean_dec_ref(v_a_1602_);
return v_res_1607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeIndices___lam__0(lean_object* v_fvarId_1608_, lean_object* v_mvarId_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_){
_start:
{
lean_object* v___x_1615_; 
v___x_1615_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_1608_, v___y_1610_, v___y_1612_, v___y_1613_);
if (lean_obj_tag(v___x_1615_) == 0)
{
lean_object* v_a_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; 
v_a_1616_ = lean_ctor_get(v___x_1615_, 0);
lean_inc_n(v_a_1616_, 2);
lean_dec_ref_known(v___x_1615_, 1);
v___x_1617_ = l_Lean_LocalDecl_toExpr(v_a_1616_);
v___x_1618_ = l_Lean_LocalDecl_userName(v_a_1616_);
lean_dec(v_a_1616_);
v___x_1619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1619_, 0, v___x_1618_);
v___x_1620_ = l_Lean_Meta_generalizeIndices_x27(v_mvarId_1609_, v___x_1617_, v___x_1619_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_);
return v___x_1620_;
}
else
{
lean_object* v_a_1621_; lean_object* v___x_1623_; uint8_t v_isShared_1624_; uint8_t v_isSharedCheck_1628_; 
lean_dec(v_mvarId_1609_);
v_a_1621_ = lean_ctor_get(v___x_1615_, 0);
v_isSharedCheck_1628_ = !lean_is_exclusive(v___x_1615_);
if (v_isSharedCheck_1628_ == 0)
{
v___x_1623_ = v___x_1615_;
v_isShared_1624_ = v_isSharedCheck_1628_;
goto v_resetjp_1622_;
}
else
{
lean_inc(v_a_1621_);
lean_dec(v___x_1615_);
v___x_1623_ = lean_box(0);
v_isShared_1624_ = v_isSharedCheck_1628_;
goto v_resetjp_1622_;
}
v_resetjp_1622_:
{
lean_object* v___x_1626_; 
if (v_isShared_1624_ == 0)
{
v___x_1626_ = v___x_1623_;
goto v_reusejp_1625_;
}
else
{
lean_object* v_reuseFailAlloc_1627_; 
v_reuseFailAlloc_1627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1627_, 0, v_a_1621_);
v___x_1626_ = v_reuseFailAlloc_1627_;
goto v_reusejp_1625_;
}
v_reusejp_1625_:
{
return v___x_1626_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeIndices___lam__0___boxed(lean_object* v_fvarId_1629_, lean_object* v_mvarId_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_){
_start:
{
lean_object* v_res_1636_; 
v_res_1636_ = l_Lean_Meta_generalizeIndices___lam__0(v_fvarId_1629_, v_mvarId_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_);
lean_dec(v___y_1634_);
lean_dec_ref(v___y_1633_);
lean_dec(v___y_1632_);
lean_dec_ref(v___y_1631_);
return v_res_1636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeIndices(lean_object* v_mvarId_1637_, lean_object* v_fvarId_1638_, lean_object* v_a_1639_, lean_object* v_a_1640_, lean_object* v_a_1641_, lean_object* v_a_1642_){
_start:
{
lean_object* v___f_1644_; lean_object* v___x_1645_; 
lean_inc(v_mvarId_1637_);
v___f_1644_ = lean_alloc_closure((void*)(l_Lean_Meta_generalizeIndices___lam__0___boxed), 7, 2);
lean_closure_set(v___f_1644_, 0, v_fvarId_1638_);
lean_closure_set(v___f_1644_, 1, v_mvarId_1637_);
v___x_1645_ = l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2___redArg(v_mvarId_1637_, v___f_1644_, v_a_1639_, v_a_1640_, v_a_1641_, v_a_1642_);
return v___x_1645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeIndices___boxed(lean_object* v_mvarId_1646_, lean_object* v_fvarId_1647_, lean_object* v_a_1648_, lean_object* v_a_1649_, lean_object* v_a_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_){
_start:
{
lean_object* v_res_1653_; 
v_res_1653_ = l_Lean_Meta_generalizeIndices(v_mvarId_1646_, v_fvarId_1647_, v_a_1648_, v_a_1649_, v_a_1650_, v_a_1651_);
lean_dec(v_a_1651_);
lean_dec_ref(v_a_1650_);
lean_dec(v_a_1649_);
lean_dec_ref(v_a_1648_);
return v_res_1653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0___redArg(lean_object* v___x_1655_, lean_object* v_a_1656_, lean_object* v_x_1657_, lean_object* v_x_1658_, lean_object* v_x_1659_, lean_object* v___y_1660_){
_start:
{
if (lean_obj_tag(v_x_1657_) == 5)
{
lean_object* v_fn_1665_; lean_object* v_arg_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; 
v_fn_1665_ = lean_ctor_get(v_x_1657_, 0);
lean_inc_ref(v_fn_1665_);
v_arg_1666_ = lean_ctor_get(v_x_1657_, 1);
lean_inc_ref(v_arg_1666_);
lean_dec_ref_known(v_x_1657_, 2);
v___x_1667_ = lean_array_set(v_x_1658_, v_x_1659_, v_arg_1666_);
v___x_1668_ = lean_unsigned_to_nat(1u);
v___x_1669_ = lean_nat_sub(v_x_1659_, v___x_1668_);
lean_dec(v_x_1659_);
v_x_1657_ = v_fn_1665_;
v_x_1658_ = v___x_1667_;
v_x_1659_ = v___x_1669_;
goto _start;
}
else
{
lean_dec(v_x_1659_);
if (lean_obj_tag(v_x_1657_) == 4)
{
lean_object* v_declName_1671_; lean_object* v___x_1672_; lean_object* v_env_1673_; uint8_t v___x_1674_; lean_object* v___x_1675_; 
v_declName_1671_ = lean_ctor_get(v_x_1657_, 0);
v___x_1672_ = lean_st_ref_get(v___y_1660_);
v_env_1673_ = lean_ctor_get(v___x_1672_, 0);
lean_inc_ref(v_env_1673_);
lean_dec(v___x_1672_);
v___x_1674_ = 0;
lean_inc(v_declName_1671_);
v___x_1675_ = l_Lean_Environment_find_x3f(v_env_1673_, v_declName_1671_, v___x_1674_);
if (lean_obj_tag(v___x_1675_) == 0)
{
lean_dec_ref_known(v_x_1657_, 2);
lean_dec_ref(v_x_1658_);
lean_dec_ref(v_a_1656_);
lean_dec_ref(v___x_1655_);
goto v___jp_1662_;
}
else
{
lean_object* v_val_1676_; lean_object* v___x_1678_; uint8_t v_isShared_1679_; uint8_t v_isSharedCheck_1714_; 
v_val_1676_ = lean_ctor_get(v___x_1675_, 0);
v_isSharedCheck_1714_ = !lean_is_exclusive(v___x_1675_);
if (v_isSharedCheck_1714_ == 0)
{
v___x_1678_ = v___x_1675_;
v_isShared_1679_ = v_isSharedCheck_1714_;
goto v_resetjp_1677_;
}
else
{
lean_inc(v_val_1676_);
lean_dec(v___x_1675_);
v___x_1678_ = lean_box(0);
v_isShared_1679_ = v_isSharedCheck_1714_;
goto v_resetjp_1677_;
}
v_resetjp_1677_:
{
if (lean_obj_tag(v_val_1676_) == 5)
{
lean_object* v_val_1680_; lean_object* v___x_1682_; uint8_t v_isShared_1683_; uint8_t v_isSharedCheck_1713_; 
v_val_1680_ = lean_ctor_get(v_val_1676_, 0);
v_isSharedCheck_1713_ = !lean_is_exclusive(v_val_1676_);
if (v_isSharedCheck_1713_ == 0)
{
v___x_1682_ = v_val_1676_;
v_isShared_1683_ = v_isSharedCheck_1713_;
goto v_resetjp_1681_;
}
else
{
lean_inc(v_val_1680_);
lean_dec(v_val_1676_);
v___x_1682_ = lean_box(0);
v_isShared_1683_ = v_isSharedCheck_1713_;
goto v_resetjp_1681_;
}
v_resetjp_1681_:
{
lean_object* v_toConstantVal_1684_; lean_object* v_numParams_1685_; lean_object* v_numIndices_1686_; lean_object* v_ctors_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; uint8_t v___x_1690_; 
v_toConstantVal_1684_ = lean_ctor_get(v_val_1680_, 0);
v_numParams_1685_ = lean_ctor_get(v_val_1680_, 1);
v_numIndices_1686_ = lean_ctor_get(v_val_1680_, 2);
v_ctors_1687_ = lean_ctor_get(v_val_1680_, 4);
v___x_1688_ = lean_array_get_size(v_x_1658_);
v___x_1689_ = lean_nat_add(v_numIndices_1686_, v_numParams_1685_);
v___x_1690_ = lean_nat_dec_eq(v___x_1688_, v___x_1689_);
lean_dec(v___x_1689_);
if (v___x_1690_ == 0)
{
lean_object* v___x_1691_; lean_object* v___x_1693_; 
lean_dec_ref(v_val_1680_);
lean_del_object(v___x_1678_);
lean_dec_ref_known(v_x_1657_, 2);
lean_dec_ref(v_x_1658_);
lean_dec_ref(v_a_1656_);
lean_dec_ref(v___x_1655_);
v___x_1691_ = lean_box(0);
if (v_isShared_1683_ == 0)
{
lean_ctor_set_tag(v___x_1682_, 0);
lean_ctor_set(v___x_1682_, 0, v___x_1691_);
v___x_1693_ = v___x_1682_;
goto v_reusejp_1692_;
}
else
{
lean_object* v_reuseFailAlloc_1694_; 
v_reuseFailAlloc_1694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1694_, 0, v___x_1691_);
v___x_1693_ = v_reuseFailAlloc_1694_;
goto v_reusejp_1692_;
}
v_reusejp_1692_:
{
return v___x_1693_;
}
}
else
{
lean_object* v_name_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; uint8_t v___x_1698_; 
v_name_1695_ = lean_ctor_get(v_toConstantVal_1684_, 0);
v___x_1696_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0___redArg___closed__0));
lean_inc(v_name_1695_);
v___x_1697_ = l_Lean_Name_str___override(v_name_1695_, v___x_1696_);
v___x_1698_ = l_Lean_Environment_contains(v___x_1655_, v___x_1697_, v___x_1690_);
if (v___x_1698_ == 0)
{
lean_object* v___x_1699_; lean_object* v___x_1701_; 
lean_dec_ref(v_val_1680_);
lean_del_object(v___x_1678_);
lean_dec_ref_known(v_x_1657_, 2);
lean_dec_ref(v_x_1658_);
lean_dec_ref(v_a_1656_);
v___x_1699_ = lean_box(0);
if (v_isShared_1683_ == 0)
{
lean_ctor_set_tag(v___x_1682_, 0);
lean_ctor_set(v___x_1682_, 0, v___x_1699_);
v___x_1701_ = v___x_1682_;
goto v_reusejp_1700_;
}
else
{
lean_object* v_reuseFailAlloc_1702_; 
v_reuseFailAlloc_1702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1702_, 0, v___x_1699_);
v___x_1701_ = v_reuseFailAlloc_1702_;
goto v_reusejp_1700_;
}
v_reusejp_1700_:
{
return v___x_1701_;
}
}
else
{
lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1708_; 
v___x_1703_ = l_List_lengthTR___redArg(v_ctors_1687_);
v___x_1704_ = lean_nat_sub(v___x_1688_, v_numIndices_1686_);
v___x_1705_ = l_Array_extract___redArg(v_x_1658_, v___x_1704_, v___x_1688_);
v___x_1706_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1706_, 0, v_val_1680_);
lean_ctor_set(v___x_1706_, 1, v___x_1703_);
lean_ctor_set(v___x_1706_, 2, v_a_1656_);
lean_ctor_set(v___x_1706_, 3, v_x_1657_);
lean_ctor_set(v___x_1706_, 4, v_x_1658_);
lean_ctor_set(v___x_1706_, 5, v___x_1705_);
if (v_isShared_1679_ == 0)
{
lean_ctor_set(v___x_1678_, 0, v___x_1706_);
v___x_1708_ = v___x_1678_;
goto v_reusejp_1707_;
}
else
{
lean_object* v_reuseFailAlloc_1712_; 
v_reuseFailAlloc_1712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1712_, 0, v___x_1706_);
v___x_1708_ = v_reuseFailAlloc_1712_;
goto v_reusejp_1707_;
}
v_reusejp_1707_:
{
lean_object* v___x_1710_; 
if (v_isShared_1683_ == 0)
{
lean_ctor_set_tag(v___x_1682_, 0);
lean_ctor_set(v___x_1682_, 0, v___x_1708_);
v___x_1710_ = v___x_1682_;
goto v_reusejp_1709_;
}
else
{
lean_object* v_reuseFailAlloc_1711_; 
v_reuseFailAlloc_1711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1711_, 0, v___x_1708_);
v___x_1710_ = v_reuseFailAlloc_1711_;
goto v_reusejp_1709_;
}
v_reusejp_1709_:
{
return v___x_1710_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_1678_);
lean_dec(v_val_1676_);
lean_dec_ref_known(v_x_1657_, 2);
lean_dec_ref(v_x_1658_);
lean_dec_ref(v_a_1656_);
lean_dec_ref(v___x_1655_);
goto v___jp_1662_;
}
}
}
}
else
{
lean_dec_ref(v_x_1658_);
lean_dec_ref(v_x_1657_);
lean_dec_ref(v_a_1656_);
lean_dec_ref(v___x_1655_);
goto v___jp_1662_;
}
}
v___jp_1662_:
{
lean_object* v___x_1663_; lean_object* v___x_1664_; 
v___x_1663_ = lean_box(0);
v___x_1664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1664_, 0, v___x_1663_);
return v___x_1664_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0___redArg___boxed(lean_object* v___x_1715_, lean_object* v_a_1716_, lean_object* v_x_1717_, lean_object* v_x_1718_, lean_object* v_x_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_){
_start:
{
lean_object* v_res_1722_; 
v_res_1722_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0___redArg(v___x_1715_, v_a_1716_, v_x_1717_, v_x_1718_, v_x_1719_, v___y_1720_);
lean_dec(v___y_1720_);
return v_res_1722_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f(lean_object* v_majorFVarId_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_){
_start:
{
lean_object* v___x_1729_; lean_object* v_env_1733_; lean_object* v___x_1734_; uint8_t v___x_1735_; uint8_t v___x_1736_; 
v___x_1729_ = lean_st_ref_get(v_a_1727_);
v_env_1733_ = lean_ctor_get(v___x_1729_, 0);
lean_inc_ref_n(v_env_1733_, 2);
lean_dec(v___x_1729_);
v___x_1734_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__5));
v___x_1735_ = 1;
v___x_1736_ = l_Lean_Environment_contains(v_env_1733_, v___x_1734_, v___x_1735_);
if (v___x_1736_ == 0)
{
lean_dec_ref(v_env_1733_);
lean_dec(v_majorFVarId_1723_);
goto v___jp_1730_;
}
else
{
lean_object* v___x_1737_; uint8_t v___x_1738_; 
v___x_1737_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__1));
lean_inc_ref(v_env_1733_);
v___x_1738_ = l_Lean_Environment_contains(v_env_1733_, v___x_1737_, v___x_1736_);
if (v___x_1738_ == 0)
{
lean_dec_ref(v_env_1733_);
lean_dec(v_majorFVarId_1723_);
goto v___jp_1730_;
}
else
{
lean_object* v___x_1739_; 
v___x_1739_ = l_Lean_FVarId_getDecl___redArg(v_majorFVarId_1723_, v_a_1724_, v_a_1726_, v_a_1727_);
if (lean_obj_tag(v___x_1739_) == 0)
{
lean_object* v_a_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; 
v_a_1740_ = lean_ctor_get(v___x_1739_, 0);
lean_inc(v_a_1740_);
lean_dec_ref_known(v___x_1739_, 1);
v___x_1741_ = l_Lean_LocalDecl_type(v_a_1740_);
lean_inc(v_a_1727_);
lean_inc_ref(v_a_1726_);
lean_inc(v_a_1725_);
lean_inc_ref(v_a_1724_);
v___x_1742_ = lean_whnf(v___x_1741_, v_a_1724_, v_a_1725_, v_a_1726_, v_a_1727_);
if (lean_obj_tag(v___x_1742_) == 0)
{
lean_object* v_a_1743_; lean_object* v_dummy_1744_; lean_object* v_nargs_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; 
v_a_1743_ = lean_ctor_get(v___x_1742_, 0);
lean_inc(v_a_1743_);
lean_dec_ref_known(v___x_1742_, 1);
v_dummy_1744_ = lean_obj_once(&l_Lean_Meta_getInductiveUniverseAndParams___closed__0, &l_Lean_Meta_getInductiveUniverseAndParams___closed__0_once, _init_l_Lean_Meta_getInductiveUniverseAndParams___closed__0);
v_nargs_1745_ = l_Lean_Expr_getAppNumArgs(v_a_1743_);
lean_inc(v_nargs_1745_);
v___x_1746_ = lean_mk_array(v_nargs_1745_, v_dummy_1744_);
v___x_1747_ = lean_unsigned_to_nat(1u);
v___x_1748_ = lean_nat_sub(v_nargs_1745_, v___x_1747_);
lean_dec(v_nargs_1745_);
v___x_1749_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0___redArg(v_env_1733_, v_a_1740_, v_a_1743_, v___x_1746_, v___x_1748_, v_a_1727_);
return v___x_1749_;
}
else
{
lean_object* v_a_1750_; lean_object* v___x_1752_; uint8_t v_isShared_1753_; uint8_t v_isSharedCheck_1757_; 
lean_dec(v_a_1740_);
lean_dec_ref(v_env_1733_);
v_a_1750_ = lean_ctor_get(v___x_1742_, 0);
v_isSharedCheck_1757_ = !lean_is_exclusive(v___x_1742_);
if (v_isSharedCheck_1757_ == 0)
{
v___x_1752_ = v___x_1742_;
v_isShared_1753_ = v_isSharedCheck_1757_;
goto v_resetjp_1751_;
}
else
{
lean_inc(v_a_1750_);
lean_dec(v___x_1742_);
v___x_1752_ = lean_box(0);
v_isShared_1753_ = v_isSharedCheck_1757_;
goto v_resetjp_1751_;
}
v_resetjp_1751_:
{
lean_object* v___x_1755_; 
if (v_isShared_1753_ == 0)
{
v___x_1755_ = v___x_1752_;
goto v_reusejp_1754_;
}
else
{
lean_object* v_reuseFailAlloc_1756_; 
v_reuseFailAlloc_1756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1756_, 0, v_a_1750_);
v___x_1755_ = v_reuseFailAlloc_1756_;
goto v_reusejp_1754_;
}
v_reusejp_1754_:
{
return v___x_1755_;
}
}
}
}
else
{
lean_object* v_a_1758_; lean_object* v___x_1760_; uint8_t v_isShared_1761_; uint8_t v_isSharedCheck_1765_; 
lean_dec_ref(v_env_1733_);
v_a_1758_ = lean_ctor_get(v___x_1739_, 0);
v_isSharedCheck_1765_ = !lean_is_exclusive(v___x_1739_);
if (v_isSharedCheck_1765_ == 0)
{
v___x_1760_ = v___x_1739_;
v_isShared_1761_ = v_isSharedCheck_1765_;
goto v_resetjp_1759_;
}
else
{
lean_inc(v_a_1758_);
lean_dec(v___x_1739_);
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
v___jp_1730_:
{
lean_object* v___x_1731_; lean_object* v___x_1732_; 
v___x_1731_ = lean_box(0);
v___x_1732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1732_, 0, v___x_1731_);
return v___x_1732_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f___boxed(lean_object* v_majorFVarId_1766_, lean_object* v_a_1767_, lean_object* v_a_1768_, lean_object* v_a_1769_, lean_object* v_a_1770_, lean_object* v_a_1771_){
_start:
{
lean_object* v_res_1772_; 
v_res_1772_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f(v_majorFVarId_1766_, v_a_1767_, v_a_1768_, v_a_1769_, v_a_1770_);
lean_dec(v_a_1770_);
lean_dec_ref(v_a_1769_);
lean_dec(v_a_1768_);
lean_dec_ref(v_a_1767_);
return v_res_1772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0(lean_object* v___x_1773_, lean_object* v_a_1774_, lean_object* v_x_1775_, lean_object* v_x_1776_, lean_object* v_x_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_){
_start:
{
lean_object* v___x_1783_; 
v___x_1783_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0___redArg(v___x_1773_, v_a_1774_, v_x_1775_, v_x_1776_, v_x_1777_, v___y_1781_);
return v___x_1783_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0___boxed(lean_object* v___x_1784_, lean_object* v_a_1785_, lean_object* v_x_1786_, lean_object* v_x_1787_, lean_object* v_x_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_){
_start:
{
lean_object* v_res_1794_; 
v_res_1794_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0(v___x_1784_, v_a_1785_, v_x_1786_, v_x_1787_, v_x_1788_, v___y_1789_, v___y_1790_, v___y_1791_, v___y_1792_);
lean_dec(v___y_1792_);
lean_dec_ref(v___y_1791_);
lean_dec(v___y_1790_);
lean_dec_ref(v___y_1789_);
return v_res_1794_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0___redArg(lean_object* v___x_1795_, lean_object* v_i_1796_, lean_object* v_n_1797_, lean_object* v_i_1798_){
_start:
{
lean_object* v_zero_1799_; uint8_t v_isZero_1800_; 
v_zero_1799_ = lean_unsigned_to_nat(0u);
v_isZero_1800_ = lean_nat_dec_eq(v_i_1798_, v_zero_1799_);
if (v_isZero_1800_ == 1)
{
uint8_t v___x_1801_; 
lean_dec(v_i_1798_);
v___x_1801_ = 0;
return v___x_1801_;
}
else
{
lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; uint8_t v___x_1805_; 
v___x_1802_ = lean_nat_sub(v_n_1797_, v_i_1798_);
v___x_1803_ = lean_array_fget_borrowed(v___x_1795_, v_i_1796_);
v___x_1804_ = lean_array_fget_borrowed(v___x_1795_, v___x_1802_);
lean_dec(v___x_1802_);
v___x_1805_ = lean_expr_eqv(v___x_1803_, v___x_1804_);
if (v___x_1805_ == 0)
{
lean_object* v_one_1806_; lean_object* v_n_1807_; 
v_one_1806_ = lean_unsigned_to_nat(1u);
v_n_1807_ = lean_nat_sub(v_i_1798_, v_one_1806_);
lean_dec(v_i_1798_);
v_i_1798_ = v_n_1807_;
goto _start;
}
else
{
lean_dec(v_i_1798_);
return v___x_1805_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0___redArg___boxed(lean_object* v___x_1809_, lean_object* v_i_1810_, lean_object* v_n_1811_, lean_object* v_i_1812_){
_start:
{
uint8_t v_res_1813_; lean_object* v_r_1814_; 
v_res_1813_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0___redArg(v___x_1809_, v_i_1810_, v_n_1811_, v_i_1812_);
lean_dec(v_n_1811_);
lean_dec(v_i_1810_);
lean_dec_ref(v___x_1809_);
v_r_1814_ = lean_box(v_res_1813_);
return v_r_1814_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1___redArg(lean_object* v___x_1815_, lean_object* v_n_1816_, lean_object* v_i_1817_){
_start:
{
lean_object* v_zero_1818_; uint8_t v_isZero_1819_; 
v_zero_1818_ = lean_unsigned_to_nat(0u);
v_isZero_1819_ = lean_nat_dec_eq(v_i_1817_, v_zero_1818_);
if (v_isZero_1819_ == 1)
{
uint8_t v___x_1820_; 
lean_dec(v_i_1817_);
v___x_1820_ = 0;
return v___x_1820_;
}
else
{
lean_object* v___x_1821_; uint8_t v___x_1822_; 
v___x_1821_ = lean_nat_sub(v_n_1816_, v_i_1817_);
lean_inc(v___x_1821_);
v___x_1822_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0___redArg(v___x_1815_, v___x_1821_, v___x_1821_, v___x_1821_);
lean_dec(v___x_1821_);
if (v___x_1822_ == 0)
{
lean_object* v_one_1823_; lean_object* v_n_1824_; 
v_one_1823_ = lean_unsigned_to_nat(1u);
v_n_1824_ = lean_nat_sub(v_i_1817_, v_one_1823_);
lean_dec(v_i_1817_);
v_i_1817_ = v_n_1824_;
goto _start;
}
else
{
lean_dec(v_i_1817_);
return v___x_1822_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1___redArg___boxed(lean_object* v___x_1826_, lean_object* v_n_1827_, lean_object* v_i_1828_){
_start:
{
uint8_t v_res_1829_; lean_object* v_r_1830_; 
v_res_1829_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1___redArg(v___x_1826_, v_n_1827_, v_i_1828_);
lean_dec(v_n_1827_);
lean_dec_ref(v___x_1826_);
v_r_1830_ = lean_box(v_res_1829_);
return v_r_1830_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__2(lean_object* v_fvarId_1831_, uint8_t v___y_1832_, lean_object* v_as_1833_, size_t v_i_1834_, size_t v_stop_1835_){
_start:
{
uint8_t v___x_1836_; 
v___x_1836_ = lean_usize_dec_eq(v_i_1834_, v_stop_1835_);
if (v___x_1836_ == 0)
{
uint8_t v___x_1837_; uint8_t v___y_1839_; lean_object* v___x_1843_; lean_object* v___x_1844_; uint8_t v___x_1845_; 
v___x_1837_ = 1;
v___x_1843_ = lean_array_uget_borrowed(v_as_1833_, v_i_1834_);
v___x_1844_ = l_Lean_Expr_fvarId_x21(v___x_1843_);
v___x_1845_ = l_Lean_instBEqFVarId_beq(v___x_1844_, v_fvarId_1831_);
lean_dec(v___x_1844_);
if (v___x_1845_ == 0)
{
v___y_1839_ = v___y_1832_;
goto v___jp_1838_;
}
else
{
v___y_1839_ = v___x_1845_;
goto v___jp_1838_;
}
v___jp_1838_:
{
if (v___y_1839_ == 0)
{
size_t v___x_1840_; size_t v___x_1841_; 
v___x_1840_ = ((size_t)1ULL);
v___x_1841_ = lean_usize_add(v_i_1834_, v___x_1840_);
v_i_1834_ = v___x_1841_;
goto _start;
}
else
{
return v___x_1837_;
}
}
}
else
{
uint8_t v___x_1846_; 
v___x_1846_ = 0;
return v___x_1846_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__2___boxed(lean_object* v_fvarId_1847_, lean_object* v___y_1848_, lean_object* v_as_1849_, lean_object* v_i_1850_, lean_object* v_stop_1851_){
_start:
{
uint8_t v___y_9024__boxed_1852_; size_t v_i_boxed_1853_; size_t v_stop_boxed_1854_; uint8_t v_res_1855_; lean_object* v_r_1856_; 
v___y_9024__boxed_1852_ = lean_unbox(v___y_1848_);
v_i_boxed_1853_ = lean_unbox_usize(v_i_1850_);
lean_dec(v_i_1850_);
v_stop_boxed_1854_ = lean_unbox_usize(v_stop_1851_);
lean_dec(v_stop_1851_);
v_res_1855_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__2(v_fvarId_1847_, v___y_9024__boxed_1852_, v_as_1849_, v_i_boxed_1853_, v_stop_boxed_1854_);
lean_dec_ref(v_as_1849_);
lean_dec(v_fvarId_1847_);
v_r_1856_ = lean_box(v_res_1855_);
return v_r_1856_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___lam__1(lean_object* v___x_1857_, lean_object* v___x_1858_, uint8_t v___x_1859_, uint8_t v___y_1860_, lean_object* v___x_1861_, lean_object* v_fvarId_1862_){
_start:
{
lean_object* v___y_1864_; uint8_t v___x_1869_; 
v___x_1869_ = lean_nat_dec_lt(v___x_1857_, v___x_1858_);
if (v___x_1869_ == 0)
{
lean_dec(v___x_1858_);
return v___x_1859_;
}
else
{
lean_object* v___x_1870_; uint8_t v___x_1871_; 
v___x_1870_ = lean_array_get_size(v___x_1861_);
v___x_1871_ = lean_nat_dec_le(v___x_1858_, v___x_1870_);
if (v___x_1871_ == 0)
{
lean_dec(v___x_1858_);
v___y_1864_ = v___x_1870_;
goto v___jp_1863_;
}
else
{
v___y_1864_ = v___x_1858_;
goto v___jp_1863_;
}
}
v___jp_1863_:
{
uint8_t v___x_1865_; 
v___x_1865_ = lean_nat_dec_lt(v___x_1857_, v___y_1864_);
if (v___x_1865_ == 0)
{
lean_dec(v___y_1864_);
return v___x_1859_;
}
else
{
size_t v___x_1866_; size_t v___x_1867_; uint8_t v___x_1868_; 
v___x_1866_ = ((size_t)0ULL);
v___x_1867_ = lean_usize_of_nat(v___y_1864_);
lean_dec(v___y_1864_);
v___x_1868_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__2(v_fvarId_1862_, v___y_1860_, v___x_1861_, v___x_1866_, v___x_1867_);
if (v___x_1868_ == 0)
{
return v___x_1859_;
}
else
{
return v___y_1860_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___lam__1___boxed(lean_object* v___x_1872_, lean_object* v___x_1873_, lean_object* v___x_1874_, lean_object* v___y_1875_, lean_object* v___x_1876_, lean_object* v_fvarId_1877_){
_start:
{
uint8_t v___x_9051__boxed_1878_; uint8_t v___y_9052__boxed_1879_; uint8_t v_res_1880_; lean_object* v_r_1881_; 
v___x_9051__boxed_1878_ = lean_unbox(v___x_1874_);
v___y_9052__boxed_1879_ = lean_unbox(v___y_1875_);
v_res_1880_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___lam__1(v___x_1872_, v___x_1873_, v___x_9051__boxed_1878_, v___y_9052__boxed_1879_, v___x_1876_, v_fvarId_1877_);
lean_dec(v_fvarId_1877_);
lean_dec_ref(v___x_1876_);
lean_dec(v___x_1872_);
v_r_1881_ = lean_box(v_res_1880_);
return v_r_1881_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__3(lean_object* v___x_1882_, lean_object* v_as_1883_, size_t v_i_1884_, size_t v_stop_1885_){
_start:
{
uint8_t v___x_1886_; 
v___x_1886_ = lean_usize_dec_eq(v_i_1884_, v_stop_1885_);
if (v___x_1886_ == 0)
{
lean_object* v___x_1887_; lean_object* v___x_1888_; uint8_t v___x_1889_; 
v___x_1887_ = lean_array_uget_borrowed(v_as_1883_, v_i_1884_);
v___x_1888_ = l_Lean_Expr_fvarId_x21(v___x_1887_);
v___x_1889_ = l_Lean_instBEqFVarId_beq(v___x_1882_, v___x_1888_);
lean_dec(v___x_1888_);
if (v___x_1889_ == 0)
{
size_t v___x_1890_; size_t v___x_1891_; 
v___x_1890_ = ((size_t)1ULL);
v___x_1891_ = lean_usize_add(v_i_1884_, v___x_1890_);
v_i_1884_ = v___x_1891_;
goto _start;
}
else
{
return v___x_1889_;
}
}
else
{
uint8_t v___x_1893_; 
v___x_1893_ = 0;
return v___x_1893_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__3___boxed(lean_object* v___x_1894_, lean_object* v_as_1895_, lean_object* v_i_1896_, lean_object* v_stop_1897_){
_start:
{
size_t v_i_boxed_1898_; size_t v_stop_boxed_1899_; uint8_t v_res_1900_; lean_object* v_r_1901_; 
v_i_boxed_1898_ = lean_unbox_usize(v_i_1896_);
lean_dec(v_i_1896_);
v_stop_boxed_1899_ = lean_unbox_usize(v_stop_1897_);
lean_dec(v_stop_1897_);
v_res_1900_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__3(v___x_1894_, v_as_1895_, v_i_boxed_1898_, v_stop_boxed_1899_);
lean_dec_ref(v_as_1895_);
lean_dec(v___x_1894_);
v_r_1901_ = lean_box(v_res_1900_);
return v_r_1901_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___lam__0(uint8_t v___y_1902_, lean_object* v_x_1903_){
_start:
{
return v___y_1902_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___lam__0___boxed(lean_object* v___y_1904_, lean_object* v_x_1905_){
_start:
{
uint8_t v___y_9101__boxed_1906_; uint8_t v_res_1907_; lean_object* v_r_1908_; 
v___y_9101__boxed_1906_ = lean_unbox(v___y_1904_);
v_res_1907_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___lam__0(v___y_9101__boxed_1906_, v_x_1905_);
lean_dec(v_x_1905_);
v_r_1908_ = lean_box(v_res_1907_);
return v_r_1908_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v_cellCount_1909_; lean_object* v___x_1910_; 
v_cellCount_1909_ = lean_unsigned_to_nat(16u);
v___x_1910_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_1909_);
return v___x_1910_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v_cellCount_1911_; lean_object* v___x_1912_; 
v_cellCount_1911_ = lean_unsigned_to_nat(16u);
v___x_1912_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_1911_);
return v___x_1912_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; 
v___x_1913_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1);
v___x_1914_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__0);
v___x_1915_ = lean_unsigned_to_nat(0u);
v___x_1916_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1916_, 0, v___x_1915_);
lean_ctor_set(v___x_1916_, 1, v___x_1914_);
lean_ctor_set(v___x_1916_, 2, v___x_1913_);
return v___x_1916_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg(uint8_t v___x_1917_, lean_object* v___x_1918_, lean_object* v___x_1919_, lean_object* v_ctx_1920_, lean_object* v_as_1921_, size_t v_i_1922_, size_t v_stop_1923_, lean_object* v___y_1924_){
_start:
{
uint8_t v___x_1926_; 
v___x_1926_ = lean_usize_dec_eq(v_i_1922_, v_stop_1923_);
if (v___x_1926_ == 0)
{
uint8_t v___x_1927_; uint8_t v_a_1929_; uint8_t v_a_1936_; uint8_t v_fst_1940_; lean_object* v_mctx_1941_; lean_object* v___y_1957_; uint8_t v_fst_1963_; lean_object* v_snd_1964_; lean_object* v___y_1981_; lean_object* v___y_1986_; lean_object* v___y_1987_; lean_object* v___y_1988_; uint8_t v_fst_1989_; lean_object* v_snd_1990_; lean_object* v___y_1996_; lean_object* v___y_1997_; lean_object* v___y_1998_; lean_object* v___y_1999_; uint8_t v_fst_2004_; lean_object* v_mctx_2005_; lean_object* v___y_2021_; lean_object* v___x_2026_; 
v___x_1927_ = 1;
v___x_2026_ = lean_array_uget_borrowed(v_as_1921_, v_i_1922_);
if (lean_obj_tag(v___x_2026_) == 0)
{
v_a_1929_ = v___x_1917_;
goto v___jp_1928_;
}
else
{
lean_object* v_val_2027_; lean_object* v_majorDecl_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; uint8_t v___x_2031_; 
v_val_2027_ = lean_ctor_get(v___x_2026_, 0);
v_majorDecl_2028_ = lean_ctor_get(v_ctx_1920_, 2);
v___x_2029_ = l_Lean_LocalDecl_fvarId(v_val_2027_);
v___x_2030_ = l_Lean_LocalDecl_fvarId(v_majorDecl_2028_);
v___x_2031_ = l_Lean_instBEqFVarId_beq(v___x_2029_, v___x_2030_);
lean_dec(v___x_2030_);
if (v___x_2031_ == 0)
{
lean_object* v___x_2032_; uint8_t v___y_2034_; lean_object* v___y_2070_; uint8_t v___x_2075_; 
v___x_2032_ = lean_unsigned_to_nat(0u);
v___x_2075_ = lean_nat_dec_lt(v___x_2032_, v___x_1919_);
if (v___x_2075_ == 0)
{
lean_dec(v___x_2029_);
v___y_2034_ = v___x_2031_;
goto v___jp_2033_;
}
else
{
lean_object* v___x_2076_; uint8_t v___x_2077_; 
v___x_2076_ = lean_array_get_size(v___x_1918_);
v___x_2077_ = lean_nat_dec_le(v___x_1919_, v___x_2076_);
if (v___x_2077_ == 0)
{
v___y_2070_ = v___x_2076_;
goto v___jp_2069_;
}
else
{
lean_inc(v___x_1919_);
v___y_2070_ = v___x_1919_;
goto v___jp_2069_;
}
}
v___jp_2033_:
{
if (v___y_2034_ == 0)
{
lean_object* v___x_2035_; lean_object* v___f_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___f_2039_; 
v___x_2035_ = lean_box(v___y_2034_);
v___f_2036_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2036_, 0, v___x_2035_);
v___x_2037_ = lean_box(v___x_1927_);
v___x_2038_ = lean_box(v___y_2034_);
lean_inc_ref(v___x_1918_);
lean_inc(v___x_1919_);
v___f_2039_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_2039_, 0, v___x_2032_);
lean_closure_set(v___f_2039_, 1, v___x_1919_);
lean_closure_set(v___f_2039_, 2, v___x_2037_);
lean_closure_set(v___f_2039_, 3, v___x_2038_);
lean_closure_set(v___f_2039_, 4, v___x_1918_);
if (lean_obj_tag(v_val_2027_) == 0)
{
lean_object* v_type_2040_; lean_object* v___x_2041_; lean_object* v_mctx_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; uint8_t v___x_2045_; 
v_type_2040_ = lean_ctor_get(v_val_2027_, 3);
v___x_2041_ = lean_st_ref_get(v___y_1924_);
v_mctx_2042_ = lean_ctor_get(v___x_2041_, 0);
lean_inc_ref_n(v_mctx_2042_, 2);
lean_dec(v___x_2041_);
v___x_2043_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__2);
v___x_2044_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2044_, 0, v___x_2043_);
lean_ctor_set(v___x_2044_, 1, v_mctx_2042_);
v___x_2045_ = l_Lean_Expr_hasFVar(v_type_2040_);
if (v___x_2045_ == 0)
{
uint8_t v___x_2046_; 
v___x_2046_ = l_Lean_Expr_hasMVar(v_type_2040_);
if (v___x_2046_ == 0)
{
lean_dec_ref_known(v___x_2044_, 2);
lean_dec_ref(v___f_2039_);
lean_dec_ref(v___f_2036_);
v_fst_1940_ = v___x_2046_;
v_mctx_1941_ = v_mctx_2042_;
goto v___jp_1939_;
}
else
{
lean_object* v___x_2047_; 
lean_dec_ref(v_mctx_2042_);
lean_inc_ref(v_type_2040_);
v___x_2047_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_2039_, v___f_2036_, v_type_2040_, v___x_2044_);
v___y_1957_ = v___x_2047_;
goto v___jp_1956_;
}
}
else
{
lean_object* v___x_2048_; 
lean_dec_ref(v_mctx_2042_);
lean_inc_ref(v_type_2040_);
v___x_2048_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_2039_, v___f_2036_, v_type_2040_, v___x_2044_);
v___y_1957_ = v___x_2048_;
goto v___jp_1956_;
}
}
else
{
uint8_t v_nondep_2049_; 
v_nondep_2049_ = lean_ctor_get_uint8(v_val_2027_, sizeof(void*)*5);
if (v_nondep_2049_ == 0)
{
lean_object* v_type_2050_; lean_object* v_value_2051_; lean_object* v___x_2052_; lean_object* v_mctx_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; uint8_t v___x_2056_; 
v_type_2050_ = lean_ctor_get(v_val_2027_, 3);
v_value_2051_ = lean_ctor_get(v_val_2027_, 4);
v___x_2052_ = lean_st_ref_get(v___y_1924_);
v_mctx_2053_ = lean_ctor_get(v___x_2052_, 0);
lean_inc_ref(v_mctx_2053_);
lean_dec(v___x_2052_);
v___x_2054_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__2);
v___x_2055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2055_, 0, v___x_2054_);
lean_ctor_set(v___x_2055_, 1, v_mctx_2053_);
v___x_2056_ = l_Lean_Expr_hasFVar(v_type_2050_);
if (v___x_2056_ == 0)
{
uint8_t v___x_2057_; 
v___x_2057_ = l_Lean_Expr_hasMVar(v_type_2050_);
if (v___x_2057_ == 0)
{
lean_inc_ref(v_value_2051_);
v___y_1986_ = v___f_2039_;
v___y_1987_ = v_value_2051_;
v___y_1988_ = v___f_2036_;
v_fst_1989_ = v___x_2057_;
v_snd_1990_ = v___x_2055_;
goto v___jp_1985_;
}
else
{
lean_object* v___x_2058_; 
lean_inc_ref(v_type_2050_);
lean_inc_ref(v___f_2036_);
lean_inc_ref(v___f_2039_);
v___x_2058_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_2039_, v___f_2036_, v_type_2050_, v___x_2055_);
lean_inc_ref(v_value_2051_);
v___y_1996_ = v___f_2039_;
v___y_1997_ = v_value_2051_;
v___y_1998_ = v___f_2036_;
v___y_1999_ = v___x_2058_;
goto v___jp_1995_;
}
}
else
{
lean_object* v___x_2059_; 
lean_inc_ref(v_type_2050_);
lean_inc_ref(v___f_2036_);
lean_inc_ref(v___f_2039_);
v___x_2059_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_2039_, v___f_2036_, v_type_2050_, v___x_2055_);
lean_inc_ref(v_value_2051_);
v___y_1996_ = v___f_2039_;
v___y_1997_ = v_value_2051_;
v___y_1998_ = v___f_2036_;
v___y_1999_ = v___x_2059_;
goto v___jp_1995_;
}
}
else
{
lean_object* v_type_2060_; lean_object* v___x_2061_; lean_object* v_mctx_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; uint8_t v___x_2065_; 
v_type_2060_ = lean_ctor_get(v_val_2027_, 3);
v___x_2061_ = lean_st_ref_get(v___y_1924_);
v_mctx_2062_ = lean_ctor_get(v___x_2061_, 0);
lean_inc_ref_n(v_mctx_2062_, 2);
lean_dec(v___x_2061_);
v___x_2063_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__2);
v___x_2064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2064_, 0, v___x_2063_);
lean_ctor_set(v___x_2064_, 1, v_mctx_2062_);
v___x_2065_ = l_Lean_Expr_hasFVar(v_type_2060_);
if (v___x_2065_ == 0)
{
uint8_t v___x_2066_; 
v___x_2066_ = l_Lean_Expr_hasMVar(v_type_2060_);
if (v___x_2066_ == 0)
{
lean_dec_ref_known(v___x_2064_, 2);
lean_dec_ref(v___f_2039_);
lean_dec_ref(v___f_2036_);
v_fst_2004_ = v___x_2066_;
v_mctx_2005_ = v_mctx_2062_;
goto v___jp_2003_;
}
else
{
lean_object* v___x_2067_; 
lean_dec_ref(v_mctx_2062_);
lean_inc_ref(v_type_2060_);
v___x_2067_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_2039_, v___f_2036_, v_type_2060_, v___x_2064_);
v___y_2021_ = v___x_2067_;
goto v___jp_2020_;
}
}
else
{
lean_object* v___x_2068_; 
lean_dec_ref(v_mctx_2062_);
lean_inc_ref(v_type_2060_);
v___x_2068_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_2039_, v___f_2036_, v_type_2060_, v___x_2064_);
v___y_2021_ = v___x_2068_;
goto v___jp_2020_;
}
}
}
}
else
{
v_a_1929_ = v___x_1917_;
goto v___jp_1928_;
}
}
v___jp_2069_:
{
uint8_t v___x_2071_; 
v___x_2071_ = lean_nat_dec_lt(v___x_2032_, v___y_2070_);
if (v___x_2071_ == 0)
{
lean_dec(v___y_2070_);
lean_dec(v___x_2029_);
v___y_2034_ = v___x_2031_;
goto v___jp_2033_;
}
else
{
size_t v___x_2072_; size_t v___x_2073_; uint8_t v___x_2074_; 
v___x_2072_ = ((size_t)0ULL);
v___x_2073_ = lean_usize_of_nat(v___y_2070_);
lean_dec(v___y_2070_);
v___x_2074_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__3(v___x_2029_, v___x_1918_, v___x_2072_, v___x_2073_);
lean_dec(v___x_2029_);
v___y_2034_ = v___x_2074_;
goto v___jp_2033_;
}
}
}
else
{
lean_dec(v___x_2029_);
v_a_1936_ = v___x_2031_;
goto v___jp_1935_;
}
}
v___jp_1928_:
{
if (v_a_1929_ == 0)
{
size_t v___x_1930_; size_t v___x_1931_; 
v___x_1930_ = ((size_t)1ULL);
v___x_1931_ = lean_usize_add(v_i_1922_, v___x_1930_);
v_i_1922_ = v___x_1931_;
goto _start;
}
else
{
lean_object* v___x_1933_; lean_object* v___x_1934_; 
lean_dec(v___x_1919_);
lean_dec_ref(v___x_1918_);
v___x_1933_ = lean_box(v___x_1927_);
v___x_1934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1934_, 0, v___x_1933_);
return v___x_1934_;
}
}
v___jp_1935_:
{
if (v_a_1936_ == 0)
{
lean_object* v___x_1937_; lean_object* v___x_1938_; 
lean_dec(v___x_1919_);
lean_dec_ref(v___x_1918_);
v___x_1937_ = lean_box(v___x_1927_);
v___x_1938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1938_, 0, v___x_1937_);
return v___x_1938_;
}
else
{
v_a_1929_ = v___x_1917_;
goto v___jp_1928_;
}
}
v___jp_1939_:
{
lean_object* v___x_1942_; lean_object* v_cache_1943_; lean_object* v_zetaDeltaFVarIds_1944_; lean_object* v_postponed_1945_; lean_object* v_diag_1946_; lean_object* v___x_1948_; uint8_t v_isShared_1949_; uint8_t v_isSharedCheck_1954_; 
v___x_1942_ = lean_st_ref_take(v___y_1924_);
v_cache_1943_ = lean_ctor_get(v___x_1942_, 1);
v_zetaDeltaFVarIds_1944_ = lean_ctor_get(v___x_1942_, 2);
v_postponed_1945_ = lean_ctor_get(v___x_1942_, 3);
v_diag_1946_ = lean_ctor_get(v___x_1942_, 4);
v_isSharedCheck_1954_ = !lean_is_exclusive(v___x_1942_);
if (v_isSharedCheck_1954_ == 0)
{
lean_object* v_unused_1955_; 
v_unused_1955_ = lean_ctor_get(v___x_1942_, 0);
lean_dec(v_unused_1955_);
v___x_1948_ = v___x_1942_;
v_isShared_1949_ = v_isSharedCheck_1954_;
goto v_resetjp_1947_;
}
else
{
lean_inc(v_diag_1946_);
lean_inc(v_postponed_1945_);
lean_inc(v_zetaDeltaFVarIds_1944_);
lean_inc(v_cache_1943_);
lean_dec(v___x_1942_);
v___x_1948_ = lean_box(0);
v_isShared_1949_ = v_isSharedCheck_1954_;
goto v_resetjp_1947_;
}
v_resetjp_1947_:
{
lean_object* v___x_1951_; 
if (v_isShared_1949_ == 0)
{
lean_ctor_set(v___x_1948_, 0, v_mctx_1941_);
v___x_1951_ = v___x_1948_;
goto v_reusejp_1950_;
}
else
{
lean_object* v_reuseFailAlloc_1953_; 
v_reuseFailAlloc_1953_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1953_, 0, v_mctx_1941_);
lean_ctor_set(v_reuseFailAlloc_1953_, 1, v_cache_1943_);
lean_ctor_set(v_reuseFailAlloc_1953_, 2, v_zetaDeltaFVarIds_1944_);
lean_ctor_set(v_reuseFailAlloc_1953_, 3, v_postponed_1945_);
lean_ctor_set(v_reuseFailAlloc_1953_, 4, v_diag_1946_);
v___x_1951_ = v_reuseFailAlloc_1953_;
goto v_reusejp_1950_;
}
v_reusejp_1950_:
{
lean_object* v___x_1952_; 
v___x_1952_ = lean_st_ref_put(v___y_1924_, v___x_1951_);
v_a_1936_ = v_fst_1940_;
goto v___jp_1935_;
}
}
}
v___jp_1956_:
{
lean_object* v_snd_1958_; lean_object* v_fst_1959_; lean_object* v_mctx_1960_; uint8_t v___x_1961_; 
v_snd_1958_ = lean_ctor_get(v___y_1957_, 1);
lean_inc(v_snd_1958_);
v_fst_1959_ = lean_ctor_get(v___y_1957_, 0);
lean_inc(v_fst_1959_);
lean_dec_ref(v___y_1957_);
v_mctx_1960_ = lean_ctor_get(v_snd_1958_, 1);
lean_inc_ref(v_mctx_1960_);
lean_dec(v_snd_1958_);
v___x_1961_ = lean_unbox(v_fst_1959_);
lean_dec(v_fst_1959_);
v_fst_1940_ = v___x_1961_;
v_mctx_1941_ = v_mctx_1960_;
goto v___jp_1939_;
}
v___jp_1962_:
{
lean_object* v_mctx_1965_; lean_object* v___x_1966_; lean_object* v_cache_1967_; lean_object* v_zetaDeltaFVarIds_1968_; lean_object* v_postponed_1969_; lean_object* v_diag_1970_; lean_object* v___x_1972_; uint8_t v_isShared_1973_; uint8_t v_isSharedCheck_1978_; 
v_mctx_1965_ = lean_ctor_get(v_snd_1964_, 1);
lean_inc_ref(v_mctx_1965_);
lean_dec_ref(v_snd_1964_);
v___x_1966_ = lean_st_ref_take(v___y_1924_);
v_cache_1967_ = lean_ctor_get(v___x_1966_, 1);
v_zetaDeltaFVarIds_1968_ = lean_ctor_get(v___x_1966_, 2);
v_postponed_1969_ = lean_ctor_get(v___x_1966_, 3);
v_diag_1970_ = lean_ctor_get(v___x_1966_, 4);
v_isSharedCheck_1978_ = !lean_is_exclusive(v___x_1966_);
if (v_isSharedCheck_1978_ == 0)
{
lean_object* v_unused_1979_; 
v_unused_1979_ = lean_ctor_get(v___x_1966_, 0);
lean_dec(v_unused_1979_);
v___x_1972_ = v___x_1966_;
v_isShared_1973_ = v_isSharedCheck_1978_;
goto v_resetjp_1971_;
}
else
{
lean_inc(v_diag_1970_);
lean_inc(v_postponed_1969_);
lean_inc(v_zetaDeltaFVarIds_1968_);
lean_inc(v_cache_1967_);
lean_dec(v___x_1966_);
v___x_1972_ = lean_box(0);
v_isShared_1973_ = v_isSharedCheck_1978_;
goto v_resetjp_1971_;
}
v_resetjp_1971_:
{
lean_object* v___x_1975_; 
if (v_isShared_1973_ == 0)
{
lean_ctor_set(v___x_1972_, 0, v_mctx_1965_);
v___x_1975_ = v___x_1972_;
goto v_reusejp_1974_;
}
else
{
lean_object* v_reuseFailAlloc_1977_; 
v_reuseFailAlloc_1977_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1977_, 0, v_mctx_1965_);
lean_ctor_set(v_reuseFailAlloc_1977_, 1, v_cache_1967_);
lean_ctor_set(v_reuseFailAlloc_1977_, 2, v_zetaDeltaFVarIds_1968_);
lean_ctor_set(v_reuseFailAlloc_1977_, 3, v_postponed_1969_);
lean_ctor_set(v_reuseFailAlloc_1977_, 4, v_diag_1970_);
v___x_1975_ = v_reuseFailAlloc_1977_;
goto v_reusejp_1974_;
}
v_reusejp_1974_:
{
lean_object* v___x_1976_; 
v___x_1976_ = lean_st_ref_put(v___y_1924_, v___x_1975_);
v_a_1936_ = v_fst_1963_;
goto v___jp_1935_;
}
}
}
v___jp_1980_:
{
lean_object* v_fst_1982_; lean_object* v_snd_1983_; uint8_t v___x_1984_; 
v_fst_1982_ = lean_ctor_get(v___y_1981_, 0);
lean_inc(v_fst_1982_);
v_snd_1983_ = lean_ctor_get(v___y_1981_, 1);
lean_inc(v_snd_1983_);
lean_dec_ref(v___y_1981_);
v___x_1984_ = lean_unbox(v_fst_1982_);
lean_dec(v_fst_1982_);
v_fst_1963_ = v___x_1984_;
v_snd_1964_ = v_snd_1983_;
goto v___jp_1962_;
}
v___jp_1985_:
{
if (v_fst_1989_ == 0)
{
uint8_t v___x_1991_; 
v___x_1991_ = l_Lean_Expr_hasFVar(v___y_1987_);
if (v___x_1991_ == 0)
{
uint8_t v___x_1992_; 
v___x_1992_ = l_Lean_Expr_hasMVar(v___y_1987_);
if (v___x_1992_ == 0)
{
lean_dec_ref(v___y_1988_);
lean_dec_ref(v___y_1987_);
lean_dec_ref(v___y_1986_);
v_fst_1963_ = v___x_1992_;
v_snd_1964_ = v_snd_1990_;
goto v___jp_1962_;
}
else
{
lean_object* v___x_1993_; 
v___x_1993_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___y_1986_, v___y_1988_, v___y_1987_, v_snd_1990_);
v___y_1981_ = v___x_1993_;
goto v___jp_1980_;
}
}
else
{
lean_object* v___x_1994_; 
v___x_1994_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___y_1986_, v___y_1988_, v___y_1987_, v_snd_1990_);
v___y_1981_ = v___x_1994_;
goto v___jp_1980_;
}
}
else
{
lean_dec_ref(v___y_1988_);
lean_dec_ref(v___y_1987_);
lean_dec_ref(v___y_1986_);
v_fst_1963_ = v_fst_1989_;
v_snd_1964_ = v_snd_1990_;
goto v___jp_1962_;
}
}
v___jp_1995_:
{
lean_object* v_fst_2000_; lean_object* v_snd_2001_; uint8_t v___x_2002_; 
v_fst_2000_ = lean_ctor_get(v___y_1999_, 0);
lean_inc(v_fst_2000_);
v_snd_2001_ = lean_ctor_get(v___y_1999_, 1);
lean_inc(v_snd_2001_);
lean_dec_ref(v___y_1999_);
v___x_2002_ = lean_unbox(v_fst_2000_);
lean_dec(v_fst_2000_);
v___y_1986_ = v___y_1996_;
v___y_1987_ = v___y_1997_;
v___y_1988_ = v___y_1998_;
v_fst_1989_ = v___x_2002_;
v_snd_1990_ = v_snd_2001_;
goto v___jp_1985_;
}
v___jp_2003_:
{
lean_object* v___x_2006_; lean_object* v_cache_2007_; lean_object* v_zetaDeltaFVarIds_2008_; lean_object* v_postponed_2009_; lean_object* v_diag_2010_; lean_object* v___x_2012_; uint8_t v_isShared_2013_; uint8_t v_isSharedCheck_2018_; 
v___x_2006_ = lean_st_ref_take(v___y_1924_);
v_cache_2007_ = lean_ctor_get(v___x_2006_, 1);
v_zetaDeltaFVarIds_2008_ = lean_ctor_get(v___x_2006_, 2);
v_postponed_2009_ = lean_ctor_get(v___x_2006_, 3);
v_diag_2010_ = lean_ctor_get(v___x_2006_, 4);
v_isSharedCheck_2018_ = !lean_is_exclusive(v___x_2006_);
if (v_isSharedCheck_2018_ == 0)
{
lean_object* v_unused_2019_; 
v_unused_2019_ = lean_ctor_get(v___x_2006_, 0);
lean_dec(v_unused_2019_);
v___x_2012_ = v___x_2006_;
v_isShared_2013_ = v_isSharedCheck_2018_;
goto v_resetjp_2011_;
}
else
{
lean_inc(v_diag_2010_);
lean_inc(v_postponed_2009_);
lean_inc(v_zetaDeltaFVarIds_2008_);
lean_inc(v_cache_2007_);
lean_dec(v___x_2006_);
v___x_2012_ = lean_box(0);
v_isShared_2013_ = v_isSharedCheck_2018_;
goto v_resetjp_2011_;
}
v_resetjp_2011_:
{
lean_object* v___x_2015_; 
if (v_isShared_2013_ == 0)
{
lean_ctor_set(v___x_2012_, 0, v_mctx_2005_);
v___x_2015_ = v___x_2012_;
goto v_reusejp_2014_;
}
else
{
lean_object* v_reuseFailAlloc_2017_; 
v_reuseFailAlloc_2017_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2017_, 0, v_mctx_2005_);
lean_ctor_set(v_reuseFailAlloc_2017_, 1, v_cache_2007_);
lean_ctor_set(v_reuseFailAlloc_2017_, 2, v_zetaDeltaFVarIds_2008_);
lean_ctor_set(v_reuseFailAlloc_2017_, 3, v_postponed_2009_);
lean_ctor_set(v_reuseFailAlloc_2017_, 4, v_diag_2010_);
v___x_2015_ = v_reuseFailAlloc_2017_;
goto v_reusejp_2014_;
}
v_reusejp_2014_:
{
lean_object* v___x_2016_; 
v___x_2016_ = lean_st_ref_put(v___y_1924_, v___x_2015_);
v_a_1936_ = v_fst_2004_;
goto v___jp_1935_;
}
}
}
v___jp_2020_:
{
lean_object* v_snd_2022_; lean_object* v_fst_2023_; lean_object* v_mctx_2024_; uint8_t v___x_2025_; 
v_snd_2022_ = lean_ctor_get(v___y_2021_, 1);
lean_inc(v_snd_2022_);
v_fst_2023_ = lean_ctor_get(v___y_2021_, 0);
lean_inc(v_fst_2023_);
lean_dec_ref(v___y_2021_);
v_mctx_2024_ = lean_ctor_get(v_snd_2022_, 1);
lean_inc_ref(v_mctx_2024_);
lean_dec(v_snd_2022_);
v___x_2025_ = lean_unbox(v_fst_2023_);
lean_dec(v_fst_2023_);
v_fst_2004_ = v___x_2025_;
v_mctx_2005_ = v_mctx_2024_;
goto v___jp_2003_;
}
}
else
{
uint8_t v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; 
lean_dec(v___x_1919_);
lean_dec_ref(v___x_1918_);
v___x_2078_ = 0;
v___x_2079_ = lean_box(v___x_2078_);
v___x_2080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2080_, 0, v___x_2079_);
return v___x_2080_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___boxed(lean_object* v___x_2081_, lean_object* v___x_2082_, lean_object* v___x_2083_, lean_object* v_ctx_2084_, lean_object* v_as_2085_, lean_object* v_i_2086_, lean_object* v_stop_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_){
_start:
{
uint8_t v___x_9131__boxed_2090_; size_t v_i_boxed_2091_; size_t v_stop_boxed_2092_; lean_object* v_res_2093_; 
v___x_9131__boxed_2090_ = lean_unbox(v___x_2081_);
v_i_boxed_2091_ = lean_unbox_usize(v_i_2086_);
lean_dec(v_i_2086_);
v_stop_boxed_2092_ = lean_unbox_usize(v_stop_2087_);
lean_dec(v_stop_2087_);
v_res_2093_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg(v___x_9131__boxed_2090_, v___x_2082_, v___x_2083_, v_ctx_2084_, v_as_2085_, v_i_boxed_2091_, v_stop_boxed_2092_, v___y_2088_);
lean_dec(v___y_2088_);
lean_dec_ref(v_as_2085_);
lean_dec_ref(v_ctx_2084_);
return v_res_2093_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4(uint8_t v___x_2094_, lean_object* v___x_2095_, lean_object* v___x_2096_, lean_object* v_ctx_2097_, lean_object* v_x_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_){
_start:
{
if (lean_obj_tag(v_x_2098_) == 0)
{
lean_object* v_cs_2104_; lean_object* v___x_2106_; uint8_t v_isShared_2107_; uint8_t v_isSharedCheck_2122_; 
v_cs_2104_ = lean_ctor_get(v_x_2098_, 0);
v_isSharedCheck_2122_ = !lean_is_exclusive(v_x_2098_);
if (v_isSharedCheck_2122_ == 0)
{
v___x_2106_ = v_x_2098_;
v_isShared_2107_ = v_isSharedCheck_2122_;
goto v_resetjp_2105_;
}
else
{
lean_inc(v_cs_2104_);
lean_dec(v_x_2098_);
v___x_2106_ = lean_box(0);
v_isShared_2107_ = v_isSharedCheck_2122_;
goto v_resetjp_2105_;
}
v_resetjp_2105_:
{
lean_object* v___x_2108_; lean_object* v___x_2109_; uint8_t v___x_2110_; 
v___x_2108_ = lean_unsigned_to_nat(0u);
v___x_2109_ = lean_array_get_size(v_cs_2104_);
v___x_2110_ = lean_nat_dec_lt(v___x_2108_, v___x_2109_);
if (v___x_2110_ == 0)
{
lean_object* v___x_2111_; lean_object* v___x_2113_; 
lean_dec_ref(v_cs_2104_);
lean_dec(v___x_2096_);
lean_dec_ref(v___x_2095_);
v___x_2111_ = lean_box(v___x_2110_);
if (v_isShared_2107_ == 0)
{
lean_ctor_set(v___x_2106_, 0, v___x_2111_);
v___x_2113_ = v___x_2106_;
goto v_reusejp_2112_;
}
else
{
lean_object* v_reuseFailAlloc_2114_; 
v_reuseFailAlloc_2114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2114_, 0, v___x_2111_);
v___x_2113_ = v_reuseFailAlloc_2114_;
goto v_reusejp_2112_;
}
v_reusejp_2112_:
{
return v___x_2113_;
}
}
else
{
if (v___x_2110_ == 0)
{
lean_object* v___x_2115_; lean_object* v___x_2117_; 
lean_dec_ref(v_cs_2104_);
lean_dec(v___x_2096_);
lean_dec_ref(v___x_2095_);
v___x_2115_ = lean_box(v___x_2110_);
if (v_isShared_2107_ == 0)
{
lean_ctor_set(v___x_2106_, 0, v___x_2115_);
v___x_2117_ = v___x_2106_;
goto v_reusejp_2116_;
}
else
{
lean_object* v_reuseFailAlloc_2118_; 
v_reuseFailAlloc_2118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2118_, 0, v___x_2115_);
v___x_2117_ = v_reuseFailAlloc_2118_;
goto v_reusejp_2116_;
}
v_reusejp_2116_:
{
return v___x_2117_;
}
}
else
{
size_t v___x_2119_; size_t v___x_2120_; lean_object* v___x_2121_; 
lean_del_object(v___x_2106_);
v___x_2119_ = ((size_t)0ULL);
v___x_2120_ = lean_usize_of_nat(v___x_2109_);
v___x_2121_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4_spec__5(v___x_2094_, v___x_2095_, v___x_2096_, v_ctx_2097_, v_cs_2104_, v___x_2119_, v___x_2120_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_);
lean_dec_ref(v_cs_2104_);
return v___x_2121_;
}
}
}
}
else
{
lean_object* v_vs_2123_; lean_object* v___x_2125_; uint8_t v_isShared_2126_; uint8_t v_isSharedCheck_2141_; 
v_vs_2123_ = lean_ctor_get(v_x_2098_, 0);
v_isSharedCheck_2141_ = !lean_is_exclusive(v_x_2098_);
if (v_isSharedCheck_2141_ == 0)
{
v___x_2125_ = v_x_2098_;
v_isShared_2126_ = v_isSharedCheck_2141_;
goto v_resetjp_2124_;
}
else
{
lean_inc(v_vs_2123_);
lean_dec(v_x_2098_);
v___x_2125_ = lean_box(0);
v_isShared_2126_ = v_isSharedCheck_2141_;
goto v_resetjp_2124_;
}
v_resetjp_2124_:
{
lean_object* v___x_2127_; lean_object* v___x_2128_; uint8_t v___x_2129_; 
v___x_2127_ = lean_unsigned_to_nat(0u);
v___x_2128_ = lean_array_get_size(v_vs_2123_);
v___x_2129_ = lean_nat_dec_lt(v___x_2127_, v___x_2128_);
if (v___x_2129_ == 0)
{
lean_object* v___x_2130_; lean_object* v___x_2132_; 
lean_dec_ref(v_vs_2123_);
lean_dec(v___x_2096_);
lean_dec_ref(v___x_2095_);
v___x_2130_ = lean_box(v___x_2129_);
if (v_isShared_2126_ == 0)
{
lean_ctor_set_tag(v___x_2125_, 0);
lean_ctor_set(v___x_2125_, 0, v___x_2130_);
v___x_2132_ = v___x_2125_;
goto v_reusejp_2131_;
}
else
{
lean_object* v_reuseFailAlloc_2133_; 
v_reuseFailAlloc_2133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2133_, 0, v___x_2130_);
v___x_2132_ = v_reuseFailAlloc_2133_;
goto v_reusejp_2131_;
}
v_reusejp_2131_:
{
return v___x_2132_;
}
}
else
{
if (v___x_2129_ == 0)
{
lean_object* v___x_2134_; lean_object* v___x_2136_; 
lean_dec_ref(v_vs_2123_);
lean_dec(v___x_2096_);
lean_dec_ref(v___x_2095_);
v___x_2134_ = lean_box(v___x_2129_);
if (v_isShared_2126_ == 0)
{
lean_ctor_set_tag(v___x_2125_, 0);
lean_ctor_set(v___x_2125_, 0, v___x_2134_);
v___x_2136_ = v___x_2125_;
goto v_reusejp_2135_;
}
else
{
lean_object* v_reuseFailAlloc_2137_; 
v_reuseFailAlloc_2137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2137_, 0, v___x_2134_);
v___x_2136_ = v_reuseFailAlloc_2137_;
goto v_reusejp_2135_;
}
v_reusejp_2135_:
{
return v___x_2136_;
}
}
else
{
size_t v___x_2138_; size_t v___x_2139_; lean_object* v___x_2140_; 
lean_del_object(v___x_2125_);
v___x_2138_ = ((size_t)0ULL);
v___x_2139_ = lean_usize_of_nat(v___x_2128_);
v___x_2140_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg(v___x_2094_, v___x_2095_, v___x_2096_, v_ctx_2097_, v_vs_2123_, v___x_2138_, v___x_2139_, v___y_2100_);
lean_dec_ref(v_vs_2123_);
return v___x_2140_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4_spec__5(uint8_t v___x_2142_, lean_object* v___x_2143_, lean_object* v___x_2144_, lean_object* v_ctx_2145_, lean_object* v_as_2146_, size_t v_i_2147_, size_t v_stop_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_){
_start:
{
uint8_t v___x_2154_; 
v___x_2154_ = lean_usize_dec_eq(v_i_2147_, v_stop_2148_);
if (v___x_2154_ == 0)
{
lean_object* v___x_2155_; lean_object* v___x_2156_; 
v___x_2155_ = lean_array_uget_borrowed(v_as_2146_, v_i_2147_);
lean_inc(v___x_2155_);
lean_inc(v___x_2144_);
lean_inc_ref(v___x_2143_);
v___x_2156_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4(v___x_2142_, v___x_2143_, v___x_2144_, v_ctx_2145_, v___x_2155_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_);
if (lean_obj_tag(v___x_2156_) == 0)
{
lean_object* v_a_2157_; lean_object* v___x_2159_; uint8_t v_isShared_2160_; uint8_t v_isSharedCheck_2168_; 
v_a_2157_ = lean_ctor_get(v___x_2156_, 0);
v_isSharedCheck_2168_ = !lean_is_exclusive(v___x_2156_);
if (v_isSharedCheck_2168_ == 0)
{
v___x_2159_ = v___x_2156_;
v_isShared_2160_ = v_isSharedCheck_2168_;
goto v_resetjp_2158_;
}
else
{
lean_inc(v_a_2157_);
lean_dec(v___x_2156_);
v___x_2159_ = lean_box(0);
v_isShared_2160_ = v_isSharedCheck_2168_;
goto v_resetjp_2158_;
}
v_resetjp_2158_:
{
uint8_t v___x_2161_; 
v___x_2161_ = lean_unbox(v_a_2157_);
if (v___x_2161_ == 0)
{
size_t v___x_2162_; size_t v___x_2163_; 
lean_del_object(v___x_2159_);
lean_dec(v_a_2157_);
v___x_2162_ = ((size_t)1ULL);
v___x_2163_ = lean_usize_add(v_i_2147_, v___x_2162_);
v_i_2147_ = v___x_2163_;
goto _start;
}
else
{
lean_object* v___x_2166_; 
lean_dec(v___x_2144_);
lean_dec_ref(v___x_2143_);
if (v_isShared_2160_ == 0)
{
v___x_2166_ = v___x_2159_;
goto v_reusejp_2165_;
}
else
{
lean_object* v_reuseFailAlloc_2167_; 
v_reuseFailAlloc_2167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2167_, 0, v_a_2157_);
v___x_2166_ = v_reuseFailAlloc_2167_;
goto v_reusejp_2165_;
}
v_reusejp_2165_:
{
return v___x_2166_;
}
}
}
}
else
{
lean_dec(v___x_2144_);
lean_dec_ref(v___x_2143_);
return v___x_2156_;
}
}
else
{
uint8_t v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; 
lean_dec(v___x_2144_);
lean_dec_ref(v___x_2143_);
v___x_2169_ = 0;
v___x_2170_ = lean_box(v___x_2169_);
v___x_2171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2171_, 0, v___x_2170_);
return v___x_2171_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4_spec__5___boxed(lean_object* v___x_2172_, lean_object* v___x_2173_, lean_object* v___x_2174_, lean_object* v_ctx_2175_, lean_object* v_as_2176_, lean_object* v_i_2177_, lean_object* v_stop_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_){
_start:
{
uint8_t v___x_9438__boxed_2184_; size_t v_i_boxed_2185_; size_t v_stop_boxed_2186_; lean_object* v_res_2187_; 
v___x_9438__boxed_2184_ = lean_unbox(v___x_2172_);
v_i_boxed_2185_ = lean_unbox_usize(v_i_2177_);
lean_dec(v_i_2177_);
v_stop_boxed_2186_ = lean_unbox_usize(v_stop_2178_);
lean_dec(v_stop_2178_);
v_res_2187_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4_spec__5(v___x_9438__boxed_2184_, v___x_2173_, v___x_2174_, v_ctx_2175_, v_as_2176_, v_i_boxed_2185_, v_stop_boxed_2186_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_);
lean_dec(v___y_2182_);
lean_dec_ref(v___y_2181_);
lean_dec(v___y_2180_);
lean_dec_ref(v___y_2179_);
lean_dec_ref(v_as_2176_);
lean_dec_ref(v_ctx_2175_);
return v_res_2187_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4___boxed(lean_object* v___x_2188_, lean_object* v___x_2189_, lean_object* v___x_2190_, lean_object* v_ctx_2191_, lean_object* v_x_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_){
_start:
{
uint8_t v___x_9457__boxed_2198_; lean_object* v_res_2199_; 
v___x_9457__boxed_2198_ = lean_unbox(v___x_2188_);
v_res_2199_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4(v___x_9457__boxed_2198_, v___x_2189_, v___x_2190_, v_ctx_2191_, v_x_2192_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_);
lean_dec(v___y_2196_);
lean_dec_ref(v___y_2195_);
lean_dec(v___y_2194_);
lean_dec_ref(v___y_2193_);
lean_dec_ref(v_ctx_2191_);
return v_res_2199_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4(uint8_t v___x_2200_, lean_object* v___x_2201_, lean_object* v___x_2202_, lean_object* v_ctx_2203_, lean_object* v_t_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_){
_start:
{
lean_object* v_root_2210_; lean_object* v_tail_2211_; lean_object* v___x_2212_; 
v_root_2210_ = lean_ctor_get(v_t_2204_, 0);
lean_inc_ref(v_root_2210_);
v_tail_2211_ = lean_ctor_get(v_t_2204_, 1);
lean_inc_ref(v_tail_2211_);
lean_dec_ref(v_t_2204_);
lean_inc(v___x_2202_);
lean_inc_ref(v___x_2201_);
v___x_2212_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4(v___x_2200_, v___x_2201_, v___x_2202_, v_ctx_2203_, v_root_2210_, v___y_2205_, v___y_2206_, v___y_2207_, v___y_2208_);
if (lean_obj_tag(v___x_2212_) == 0)
{
lean_object* v_a_2213_; uint8_t v___x_2214_; 
v_a_2213_ = lean_ctor_get(v___x_2212_, 0);
lean_inc(v_a_2213_);
v___x_2214_ = lean_unbox(v_a_2213_);
lean_dec(v_a_2213_);
if (v___x_2214_ == 0)
{
lean_object* v___x_2215_; lean_object* v___x_2216_; uint8_t v___x_2217_; 
v___x_2215_ = lean_unsigned_to_nat(0u);
v___x_2216_ = lean_array_get_size(v_tail_2211_);
v___x_2217_ = lean_nat_dec_lt(v___x_2215_, v___x_2216_);
if (v___x_2217_ == 0)
{
lean_dec_ref(v_tail_2211_);
lean_dec(v___x_2202_);
lean_dec_ref(v___x_2201_);
return v___x_2212_;
}
else
{
if (v___x_2217_ == 0)
{
lean_dec_ref(v_tail_2211_);
lean_dec(v___x_2202_);
lean_dec_ref(v___x_2201_);
return v___x_2212_;
}
else
{
size_t v___x_2218_; size_t v___x_2219_; lean_object* v___x_2220_; 
lean_dec_ref_known(v___x_2212_, 1);
v___x_2218_ = ((size_t)0ULL);
v___x_2219_ = lean_usize_of_nat(v___x_2216_);
v___x_2220_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg(v___x_2200_, v___x_2201_, v___x_2202_, v_ctx_2203_, v_tail_2211_, v___x_2218_, v___x_2219_, v___y_2206_);
lean_dec_ref(v_tail_2211_);
return v___x_2220_;
}
}
}
else
{
lean_dec_ref(v_tail_2211_);
lean_dec(v___x_2202_);
lean_dec_ref(v___x_2201_);
return v___x_2212_;
}
}
else
{
lean_dec_ref(v_tail_2211_);
lean_dec(v___x_2202_);
lean_dec_ref(v___x_2201_);
return v___x_2212_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4___boxed(lean_object* v___x_2221_, lean_object* v___x_2222_, lean_object* v___x_2223_, lean_object* v_ctx_2224_, lean_object* v_t_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_){
_start:
{
uint8_t v___x_9602__boxed_2231_; lean_object* v_res_2232_; 
v___x_9602__boxed_2231_ = lean_unbox(v___x_2221_);
v_res_2232_ = l_Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4(v___x_9602__boxed_2231_, v___x_2222_, v___x_2223_, v_ctx_2224_, v_t_2225_, v___y_2226_, v___y_2227_, v___y_2228_, v___y_2229_);
lean_dec(v___y_2229_);
lean_dec_ref(v___y_2228_);
lean_dec(v___y_2227_);
lean_dec_ref(v___y_2226_);
lean_dec_ref(v_ctx_2224_);
return v_res_2232_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5(lean_object* v___x_2233_, lean_object* v_as_2234_, size_t v_i_2235_, size_t v_stop_2236_){
_start:
{
uint8_t v___x_2237_; 
v___x_2237_ = lean_usize_dec_eq(v_i_2235_, v_stop_2236_);
if (v___x_2237_ == 0)
{
uint8_t v___x_2238_; lean_object* v___x_2239_; uint8_t v___x_2240_; 
v___x_2238_ = 1;
v___x_2239_ = lean_array_uget_borrowed(v_as_2234_, v_i_2235_);
v___x_2240_ = l_Lean_Expr_isFVar(v___x_2239_);
if (v___x_2240_ == 0)
{
return v___x_2238_;
}
else
{
lean_object* v___x_2241_; uint8_t v___x_2242_; 
v___x_2241_ = lean_unsigned_to_nat(0u);
v___x_2242_ = lean_nat_dec_eq(v___x_2233_, v___x_2241_);
if (v___x_2242_ == 0)
{
size_t v___x_2243_; size_t v___x_2244_; 
v___x_2243_ = ((size_t)1ULL);
v___x_2244_ = lean_usize_add(v_i_2235_, v___x_2243_);
v_i_2235_ = v___x_2244_;
goto _start;
}
else
{
return v___x_2238_;
}
}
}
else
{
uint8_t v___x_2246_; 
v___x_2246_ = 0;
return v___x_2246_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5___boxed(lean_object* v___x_2247_, lean_object* v_as_2248_, lean_object* v_i_2249_, lean_object* v_stop_2250_){
_start:
{
size_t v_i_boxed_2251_; size_t v_stop_boxed_2252_; uint8_t v_res_2253_; lean_object* v_r_2254_; 
v_i_boxed_2251_ = lean_unbox_usize(v_i_2249_);
lean_dec(v_i_2249_);
v_stop_boxed_2252_ = lean_unbox_usize(v_stop_2250_);
lean_dec(v_stop_2250_);
v_res_2253_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5(v___x_2247_, v_as_2248_, v_i_boxed_2251_, v_stop_boxed_2252_);
lean_dec_ref(v_as_2248_);
lean_dec(v___x_2247_);
v_r_2254_ = lean_box(v_res_2253_);
return v_r_2254_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices(lean_object* v_ctx_2255_, lean_object* v_a_2256_, lean_object* v_a_2257_, lean_object* v_a_2258_, lean_object* v_a_2259_){
_start:
{
lean_object* v_majorTypeIndices_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; uint8_t v___x_2264_; uint8_t v___y_2266_; 
v_majorTypeIndices_2261_ = lean_ctor_get(v_ctx_2255_, 5);
lean_inc_ref(v_majorTypeIndices_2261_);
v___x_2262_ = lean_array_get_size(v_majorTypeIndices_2261_);
v___x_2263_ = lean_unsigned_to_nat(0u);
v___x_2264_ = lean_nat_dec_eq(v___x_2262_, v___x_2263_);
if (v___x_2264_ == 0)
{
uint8_t v___x_2290_; 
v___x_2290_ = lean_nat_dec_lt(v___x_2263_, v___x_2262_);
if (v___x_2290_ == 0)
{
v___y_2266_ = v___x_2264_;
goto v___jp_2265_;
}
else
{
if (v___x_2290_ == 0)
{
v___y_2266_ = v___x_2264_;
goto v___jp_2265_;
}
else
{
size_t v___x_2291_; size_t v___x_2292_; uint8_t v___x_2293_; 
v___x_2291_ = ((size_t)0ULL);
v___x_2292_ = lean_usize_of_nat(v___x_2262_);
v___x_2293_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5(v___x_2262_, v_majorTypeIndices_2261_, v___x_2291_, v___x_2292_);
v___y_2266_ = v___x_2293_;
goto v___jp_2265_;
}
}
}
else
{
lean_object* v___x_2294_; lean_object* v___x_2295_; 
lean_dec_ref(v_majorTypeIndices_2261_);
lean_dec_ref(v_ctx_2255_);
v___x_2294_ = lean_box(v___x_2264_);
v___x_2295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2295_, 0, v___x_2294_);
return v___x_2295_;
}
v___jp_2265_:
{
if (v___y_2266_ == 0)
{
uint8_t v___x_2267_; 
v___x_2267_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1___redArg(v_majorTypeIndices_2261_, v___x_2262_, v___x_2262_);
if (v___x_2267_ == 0)
{
lean_object* v_lctx_2268_; lean_object* v_decls_2269_; lean_object* v___x_2270_; 
v_lctx_2268_ = lean_ctor_get(v_a_2256_, 2);
v_decls_2269_ = lean_ctor_get(v_lctx_2268_, 1);
lean_inc_ref(v_decls_2269_);
v___x_2270_ = l_Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4(v___x_2267_, v_majorTypeIndices_2261_, v___x_2262_, v_ctx_2255_, v_decls_2269_, v_a_2256_, v_a_2257_, v_a_2258_, v_a_2259_);
lean_dec_ref(v_ctx_2255_);
if (lean_obj_tag(v___x_2270_) == 0)
{
lean_object* v_a_2271_; lean_object* v___x_2273_; uint8_t v_isShared_2274_; uint8_t v_isSharedCheck_2285_; 
v_a_2271_ = lean_ctor_get(v___x_2270_, 0);
v_isSharedCheck_2285_ = !lean_is_exclusive(v___x_2270_);
if (v_isSharedCheck_2285_ == 0)
{
v___x_2273_ = v___x_2270_;
v_isShared_2274_ = v_isSharedCheck_2285_;
goto v_resetjp_2272_;
}
else
{
lean_inc(v_a_2271_);
lean_dec(v___x_2270_);
v___x_2273_ = lean_box(0);
v_isShared_2274_ = v_isSharedCheck_2285_;
goto v_resetjp_2272_;
}
v_resetjp_2272_:
{
uint8_t v___x_2275_; 
v___x_2275_ = lean_unbox(v_a_2271_);
lean_dec(v_a_2271_);
if (v___x_2275_ == 0)
{
uint8_t v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2279_; 
v___x_2276_ = 1;
v___x_2277_ = lean_box(v___x_2276_);
if (v_isShared_2274_ == 0)
{
lean_ctor_set(v___x_2273_, 0, v___x_2277_);
v___x_2279_ = v___x_2273_;
goto v_reusejp_2278_;
}
else
{
lean_object* v_reuseFailAlloc_2280_; 
v_reuseFailAlloc_2280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2280_, 0, v___x_2277_);
v___x_2279_ = v_reuseFailAlloc_2280_;
goto v_reusejp_2278_;
}
v_reusejp_2278_:
{
return v___x_2279_;
}
}
else
{
lean_object* v___x_2281_; lean_object* v___x_2283_; 
v___x_2281_ = lean_box(v___x_2267_);
if (v_isShared_2274_ == 0)
{
lean_ctor_set(v___x_2273_, 0, v___x_2281_);
v___x_2283_ = v___x_2273_;
goto v_reusejp_2282_;
}
else
{
lean_object* v_reuseFailAlloc_2284_; 
v_reuseFailAlloc_2284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2284_, 0, v___x_2281_);
v___x_2283_ = v_reuseFailAlloc_2284_;
goto v_reusejp_2282_;
}
v_reusejp_2282_:
{
return v___x_2283_;
}
}
}
}
else
{
return v___x_2270_;
}
}
else
{
lean_object* v___x_2286_; lean_object* v___x_2287_; 
lean_dec_ref(v_majorTypeIndices_2261_);
lean_dec_ref(v_ctx_2255_);
v___x_2286_ = lean_box(v___y_2266_);
v___x_2287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2287_, 0, v___x_2286_);
return v___x_2287_;
}
}
else
{
lean_object* v___x_2288_; lean_object* v___x_2289_; 
lean_dec_ref(v_majorTypeIndices_2261_);
lean_dec_ref(v_ctx_2255_);
v___x_2288_ = lean_box(v___x_2264_);
v___x_2289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2289_, 0, v___x_2288_);
return v___x_2289_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___boxed(lean_object* v_ctx_2296_, lean_object* v_a_2297_, lean_object* v_a_2298_, lean_object* v_a_2299_, lean_object* v_a_2300_, lean_object* v_a_2301_){
_start:
{
lean_object* v_res_2302_; 
v_res_2302_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices(v_ctx_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_);
lean_dec(v_a_2300_);
lean_dec_ref(v_a_2299_);
lean_dec(v_a_2298_);
lean_dec_ref(v_a_2297_);
return v_res_2302_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0(lean_object* v___x_2303_, lean_object* v_i_2304_, lean_object* v_n_2305_, lean_object* v_i_2306_, lean_object* v_a_2307_){
_start:
{
uint8_t v___x_2308_; 
v___x_2308_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0___redArg(v___x_2303_, v_i_2304_, v_n_2305_, v_i_2306_);
return v___x_2308_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0___boxed(lean_object* v___x_2309_, lean_object* v_i_2310_, lean_object* v_n_2311_, lean_object* v_i_2312_, lean_object* v_a_2313_){
_start:
{
uint8_t v_res_2314_; lean_object* v_r_2315_; 
v_res_2314_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0(v___x_2309_, v_i_2310_, v_n_2311_, v_i_2312_, v_a_2313_);
lean_dec(v_n_2311_);
lean_dec(v_i_2310_);
lean_dec_ref(v___x_2309_);
v_r_2315_ = lean_box(v_res_2314_);
return v_r_2315_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1(lean_object* v___x_2316_, lean_object* v_n_2317_, lean_object* v_i_2318_, lean_object* v_a_2319_){
_start:
{
uint8_t v___x_2320_; 
v___x_2320_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1___redArg(v___x_2316_, v_n_2317_, v_i_2318_);
return v___x_2320_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1___boxed(lean_object* v___x_2321_, lean_object* v_n_2322_, lean_object* v_i_2323_, lean_object* v_a_2324_){
_start:
{
uint8_t v_res_2325_; lean_object* v_r_2326_; 
v_res_2325_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1(v___x_2321_, v_n_2322_, v_i_2323_, v_a_2324_);
lean_dec(v_n_2322_);
lean_dec_ref(v___x_2321_);
v_r_2326_ = lean_box(v_res_2325_);
return v_r_2326_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5(uint8_t v___x_2327_, lean_object* v___x_2328_, lean_object* v___x_2329_, lean_object* v_ctx_2330_, lean_object* v_as_2331_, size_t v_i_2332_, size_t v_stop_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_){
_start:
{
lean_object* v___x_2339_; 
v___x_2339_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg(v___x_2327_, v___x_2328_, v___x_2329_, v_ctx_2330_, v_as_2331_, v_i_2332_, v_stop_2333_, v___y_2335_);
return v___x_2339_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___boxed(lean_object* v___x_2340_, lean_object* v___x_2341_, lean_object* v___x_2342_, lean_object* v_ctx_2343_, lean_object* v_as_2344_, lean_object* v_i_2345_, lean_object* v_stop_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_){
_start:
{
uint8_t v___x_9752__boxed_2352_; size_t v_i_boxed_2353_; size_t v_stop_boxed_2354_; lean_object* v_res_2355_; 
v___x_9752__boxed_2352_ = lean_unbox(v___x_2340_);
v_i_boxed_2353_ = lean_unbox_usize(v_i_2345_);
lean_dec(v_i_2345_);
v_stop_boxed_2354_ = lean_unbox_usize(v_stop_2346_);
lean_dec(v_stop_2346_);
v_res_2355_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5(v___x_9752__boxed_2352_, v___x_2341_, v___x_2342_, v_ctx_2343_, v_as_2344_, v_i_boxed_2353_, v_stop_boxed_2354_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_);
lean_dec(v___y_2350_);
lean_dec_ref(v___y_2349_);
lean_dec(v___y_2348_);
lean_dec_ref(v___y_2347_);
lean_dec_ref(v_as_2344_);
lean_dec_ref(v_ctx_2343_);
return v_res_2355_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__0(lean_object* v_as_2356_, size_t v_i_2357_, size_t v_stop_2358_, lean_object* v_b_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_){
_start:
{
lean_object* v_a_2366_; uint8_t v___x_2370_; 
v___x_2370_ = lean_usize_dec_eq(v_i_2357_, v_stop_2358_);
if (v___x_2370_ == 0)
{
lean_object* v_toInductionSubgoal_2371_; lean_object* v_ctorName_2372_; lean_object* v_mvarId_2373_; lean_object* v_fields_2374_; lean_object* v_subst_2375_; lean_object* v___x_2377_; uint8_t v_isShared_2378_; uint8_t v_isSharedCheck_2428_; 
v_toInductionSubgoal_2371_ = lean_ctor_get(v_b_2359_, 0);
lean_inc_ref(v_toInductionSubgoal_2371_);
v_ctorName_2372_ = lean_ctor_get(v_b_2359_, 1);
v_mvarId_2373_ = lean_ctor_get(v_toInductionSubgoal_2371_, 0);
v_fields_2374_ = lean_ctor_get(v_toInductionSubgoal_2371_, 1);
v_subst_2375_ = lean_ctor_get(v_toInductionSubgoal_2371_, 2);
v_isSharedCheck_2428_ = !lean_is_exclusive(v_toInductionSubgoal_2371_);
if (v_isSharedCheck_2428_ == 0)
{
v___x_2377_ = v_toInductionSubgoal_2371_;
v_isShared_2378_ = v_isSharedCheck_2428_;
goto v_resetjp_2376_;
}
else
{
lean_inc(v_subst_2375_);
lean_inc(v_fields_2374_);
lean_inc(v_mvarId_2373_);
lean_dec(v_toInductionSubgoal_2371_);
v___x_2377_ = lean_box(0);
v_isShared_2378_ = v_isSharedCheck_2428_;
goto v_resetjp_2376_;
}
v_resetjp_2376_:
{
lean_object* v___x_2379_; lean_object* v___x_2380_; 
v___x_2379_ = lean_array_uget_borrowed(v_as_2356_, v_i_2357_);
lean_inc(v___x_2379_);
v___x_2380_ = l_Lean_Meta_FVarSubst_get(v_subst_2375_, v___x_2379_);
if (lean_obj_tag(v___x_2380_) == 1)
{
lean_object* v_fvarId_2381_; lean_object* v___x_2382_; 
v_fvarId_2381_ = lean_ctor_get(v___x_2380_, 0);
lean_inc(v_fvarId_2381_);
lean_dec_ref_known(v___x_2380_, 1);
v___x_2382_ = l_Lean_Meta_saveState___redArg(v___y_2361_, v___y_2363_);
if (lean_obj_tag(v___x_2382_) == 0)
{
lean_object* v_a_2383_; lean_object* v___x_2384_; 
v_a_2383_ = lean_ctor_get(v___x_2382_, 0);
lean_inc(v_a_2383_);
lean_dec_ref_known(v___x_2382_, 1);
v___x_2384_ = l_Lean_MVarId_clear(v_mvarId_2373_, v_fvarId_2381_, v___y_2360_, v___y_2361_, v___y_2362_, v___y_2363_);
if (lean_obj_tag(v___x_2384_) == 0)
{
lean_object* v___x_2386_; uint8_t v_isShared_2387_; uint8_t v_isSharedCheck_2396_; 
lean_inc(v_ctorName_2372_);
lean_dec(v_a_2383_);
v_isSharedCheck_2396_ = !lean_is_exclusive(v_b_2359_);
if (v_isSharedCheck_2396_ == 0)
{
lean_object* v_unused_2397_; lean_object* v_unused_2398_; 
v_unused_2397_ = lean_ctor_get(v_b_2359_, 1);
lean_dec(v_unused_2397_);
v_unused_2398_ = lean_ctor_get(v_b_2359_, 0);
lean_dec(v_unused_2398_);
v___x_2386_ = v_b_2359_;
v_isShared_2387_ = v_isSharedCheck_2396_;
goto v_resetjp_2385_;
}
else
{
lean_dec(v_b_2359_);
v___x_2386_ = lean_box(0);
v_isShared_2387_ = v_isSharedCheck_2396_;
goto v_resetjp_2385_;
}
v_resetjp_2385_:
{
lean_object* v_a_2388_; lean_object* v___x_2389_; lean_object* v___x_2391_; 
v_a_2388_ = lean_ctor_get(v___x_2384_, 0);
lean_inc(v_a_2388_);
lean_dec_ref_known(v___x_2384_, 1);
v___x_2389_ = l_Lean_Meta_FVarSubst_erase(v_subst_2375_, v___x_2379_);
if (v_isShared_2378_ == 0)
{
lean_ctor_set(v___x_2377_, 2, v___x_2389_);
lean_ctor_set(v___x_2377_, 0, v_a_2388_);
v___x_2391_ = v___x_2377_;
goto v_reusejp_2390_;
}
else
{
lean_object* v_reuseFailAlloc_2395_; 
v_reuseFailAlloc_2395_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2395_, 0, v_a_2388_);
lean_ctor_set(v_reuseFailAlloc_2395_, 1, v_fields_2374_);
lean_ctor_set(v_reuseFailAlloc_2395_, 2, v___x_2389_);
v___x_2391_ = v_reuseFailAlloc_2395_;
goto v_reusejp_2390_;
}
v_reusejp_2390_:
{
lean_object* v___x_2393_; 
if (v_isShared_2387_ == 0)
{
lean_ctor_set(v___x_2386_, 0, v___x_2391_);
v___x_2393_ = v___x_2386_;
goto v_reusejp_2392_;
}
else
{
lean_object* v_reuseFailAlloc_2394_; 
v_reuseFailAlloc_2394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2394_, 0, v___x_2391_);
lean_ctor_set(v_reuseFailAlloc_2394_, 1, v_ctorName_2372_);
v___x_2393_ = v_reuseFailAlloc_2394_;
goto v_reusejp_2392_;
}
v_reusejp_2392_:
{
v_a_2366_ = v___x_2393_;
goto v___jp_2365_;
}
}
}
}
else
{
lean_object* v_a_2399_; lean_object* v___x_2401_; uint8_t v_isShared_2402_; uint8_t v_isSharedCheck_2419_; 
lean_del_object(v___x_2377_);
lean_dec(v_subst_2375_);
lean_dec_ref(v_fields_2374_);
v_a_2399_ = lean_ctor_get(v___x_2384_, 0);
v_isSharedCheck_2419_ = !lean_is_exclusive(v___x_2384_);
if (v_isSharedCheck_2419_ == 0)
{
v___x_2401_ = v___x_2384_;
v_isShared_2402_ = v_isSharedCheck_2419_;
goto v_resetjp_2400_;
}
else
{
lean_inc(v_a_2399_);
lean_dec(v___x_2384_);
v___x_2401_ = lean_box(0);
v_isShared_2402_ = v_isSharedCheck_2419_;
goto v_resetjp_2400_;
}
v_resetjp_2400_:
{
lean_object* v___x_2404_; 
lean_inc(v_a_2399_);
if (v_isShared_2402_ == 0)
{
v___x_2404_ = v___x_2401_;
goto v_reusejp_2403_;
}
else
{
lean_object* v_reuseFailAlloc_2418_; 
v_reuseFailAlloc_2418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2418_, 0, v_a_2399_);
v___x_2404_ = v_reuseFailAlloc_2418_;
goto v_reusejp_2403_;
}
v_reusejp_2403_:
{
uint8_t v___y_2406_; uint8_t v___x_2416_; 
v___x_2416_ = l_Lean_Exception_isInterrupt(v_a_2399_);
if (v___x_2416_ == 0)
{
uint8_t v___x_2417_; 
v___x_2417_ = l_Lean_Exception_isRuntime(v_a_2399_);
v___y_2406_ = v___x_2417_;
goto v___jp_2405_;
}
else
{
lean_dec(v_a_2399_);
v___y_2406_ = v___x_2416_;
goto v___jp_2405_;
}
v___jp_2405_:
{
if (v___y_2406_ == 0)
{
lean_object* v___x_2407_; 
lean_dec_ref(v___x_2404_);
v___x_2407_ = l_Lean_Meta_SavedState_restore___redArg(v_a_2383_, v___y_2361_, v___y_2363_);
lean_dec(v_a_2383_);
if (lean_obj_tag(v___x_2407_) == 0)
{
lean_dec_ref_known(v___x_2407_, 1);
v_a_2366_ = v_b_2359_;
goto v___jp_2365_;
}
else
{
lean_object* v_a_2408_; lean_object* v___x_2410_; uint8_t v_isShared_2411_; uint8_t v_isSharedCheck_2415_; 
lean_dec_ref(v_b_2359_);
v_a_2408_ = lean_ctor_get(v___x_2407_, 0);
v_isSharedCheck_2415_ = !lean_is_exclusive(v___x_2407_);
if (v_isSharedCheck_2415_ == 0)
{
v___x_2410_ = v___x_2407_;
v_isShared_2411_ = v_isSharedCheck_2415_;
goto v_resetjp_2409_;
}
else
{
lean_inc(v_a_2408_);
lean_dec(v___x_2407_);
v___x_2410_ = lean_box(0);
v_isShared_2411_ = v_isSharedCheck_2415_;
goto v_resetjp_2409_;
}
v_resetjp_2409_:
{
lean_object* v___x_2413_; 
if (v_isShared_2411_ == 0)
{
v___x_2413_ = v___x_2410_;
goto v_reusejp_2412_;
}
else
{
lean_object* v_reuseFailAlloc_2414_; 
v_reuseFailAlloc_2414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2414_, 0, v_a_2408_);
v___x_2413_ = v_reuseFailAlloc_2414_;
goto v_reusejp_2412_;
}
v_reusejp_2412_:
{
return v___x_2413_;
}
}
}
}
else
{
lean_dec(v_a_2383_);
lean_dec_ref(v_b_2359_);
return v___x_2404_;
}
}
}
}
}
}
else
{
lean_object* v_a_2420_; lean_object* v___x_2422_; uint8_t v_isShared_2423_; uint8_t v_isSharedCheck_2427_; 
lean_dec(v_fvarId_2381_);
lean_del_object(v___x_2377_);
lean_dec(v_subst_2375_);
lean_dec_ref(v_fields_2374_);
lean_dec(v_mvarId_2373_);
lean_dec_ref(v_b_2359_);
v_a_2420_ = lean_ctor_get(v___x_2382_, 0);
v_isSharedCheck_2427_ = !lean_is_exclusive(v___x_2382_);
if (v_isSharedCheck_2427_ == 0)
{
v___x_2422_ = v___x_2382_;
v_isShared_2423_ = v_isSharedCheck_2427_;
goto v_resetjp_2421_;
}
else
{
lean_inc(v_a_2420_);
lean_dec(v___x_2382_);
v___x_2422_ = lean_box(0);
v_isShared_2423_ = v_isSharedCheck_2427_;
goto v_resetjp_2421_;
}
v_resetjp_2421_:
{
lean_object* v___x_2425_; 
if (v_isShared_2423_ == 0)
{
v___x_2425_ = v___x_2422_;
goto v_reusejp_2424_;
}
else
{
lean_object* v_reuseFailAlloc_2426_; 
v_reuseFailAlloc_2426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2426_, 0, v_a_2420_);
v___x_2425_ = v_reuseFailAlloc_2426_;
goto v_reusejp_2424_;
}
v_reusejp_2424_:
{
return v___x_2425_;
}
}
}
}
else
{
lean_dec_ref(v___x_2380_);
lean_del_object(v___x_2377_);
lean_dec(v_subst_2375_);
lean_dec_ref(v_fields_2374_);
lean_dec(v_mvarId_2373_);
v_a_2366_ = v_b_2359_;
goto v___jp_2365_;
}
}
}
else
{
lean_object* v___x_2429_; 
v___x_2429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2429_, 0, v_b_2359_);
return v___x_2429_;
}
v___jp_2365_:
{
size_t v___x_2367_; size_t v___x_2368_; 
v___x_2367_ = ((size_t)1ULL);
v___x_2368_ = lean_usize_add(v_i_2357_, v___x_2367_);
v_i_2357_ = v___x_2368_;
v_b_2359_ = v_a_2366_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__0___boxed(lean_object* v_as_2430_, lean_object* v_i_2431_, lean_object* v_stop_2432_, lean_object* v_b_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_){
_start:
{
size_t v_i_boxed_2439_; size_t v_stop_boxed_2440_; lean_object* v_res_2441_; 
v_i_boxed_2439_ = lean_unbox_usize(v_i_2431_);
lean_dec(v_i_2431_);
v_stop_boxed_2440_ = lean_unbox_usize(v_stop_2432_);
lean_dec(v_stop_2432_);
v_res_2441_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__0(v_as_2430_, v_i_boxed_2439_, v_stop_boxed_2440_, v_b_2433_, v___y_2434_, v___y_2435_, v___y_2436_, v___y_2437_);
lean_dec(v___y_2437_);
lean_dec_ref(v___y_2436_);
lean_dec(v___y_2435_);
lean_dec_ref(v___y_2434_);
lean_dec_ref(v_as_2430_);
return v_res_2441_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__1(lean_object* v_indicesFVarIds_2442_, size_t v_sz_2443_, size_t v_i_2444_, lean_object* v_bs_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_){
_start:
{
uint8_t v___x_2451_; 
v___x_2451_ = lean_usize_dec_lt(v_i_2444_, v_sz_2443_);
if (v___x_2451_ == 0)
{
lean_object* v___x_2452_; 
v___x_2452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2452_, 0, v_bs_2445_);
return v___x_2452_;
}
else
{
lean_object* v_v_2453_; lean_object* v___x_2454_; lean_object* v_bs_x27_2455_; lean_object* v_a_2457_; lean_object* v___y_2463_; lean_object* v___x_2473_; uint8_t v___x_2474_; 
v_v_2453_ = lean_array_uget(v_bs_2445_, v_i_2444_);
v___x_2454_ = lean_unsigned_to_nat(0u);
v_bs_x27_2455_ = lean_array_uset(v_bs_2445_, v_i_2444_, v___x_2454_);
v___x_2473_ = lean_array_get_size(v_indicesFVarIds_2442_);
v___x_2474_ = lean_nat_dec_lt(v___x_2454_, v___x_2473_);
if (v___x_2474_ == 0)
{
v_a_2457_ = v_v_2453_;
goto v___jp_2456_;
}
else
{
uint8_t v___x_2475_; 
v___x_2475_ = lean_nat_dec_le(v___x_2473_, v___x_2473_);
if (v___x_2475_ == 0)
{
if (v___x_2474_ == 0)
{
v_a_2457_ = v_v_2453_;
goto v___jp_2456_;
}
else
{
size_t v___x_2476_; size_t v___x_2477_; lean_object* v___x_2478_; 
v___x_2476_ = ((size_t)0ULL);
v___x_2477_ = lean_usize_of_nat(v___x_2473_);
v___x_2478_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__0(v_indicesFVarIds_2442_, v___x_2476_, v___x_2477_, v_v_2453_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_);
v___y_2463_ = v___x_2478_;
goto v___jp_2462_;
}
}
else
{
size_t v___x_2479_; size_t v___x_2480_; lean_object* v___x_2481_; 
v___x_2479_ = ((size_t)0ULL);
v___x_2480_ = lean_usize_of_nat(v___x_2473_);
v___x_2481_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__0(v_indicesFVarIds_2442_, v___x_2479_, v___x_2480_, v_v_2453_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_);
v___y_2463_ = v___x_2481_;
goto v___jp_2462_;
}
}
v___jp_2456_:
{
size_t v___x_2458_; size_t v___x_2459_; lean_object* v___x_2460_; 
v___x_2458_ = ((size_t)1ULL);
v___x_2459_ = lean_usize_add(v_i_2444_, v___x_2458_);
v___x_2460_ = lean_array_uset(v_bs_x27_2455_, v_i_2444_, v_a_2457_);
v_i_2444_ = v___x_2459_;
v_bs_2445_ = v___x_2460_;
goto _start;
}
v___jp_2462_:
{
if (lean_obj_tag(v___y_2463_) == 0)
{
lean_object* v_a_2464_; 
v_a_2464_ = lean_ctor_get(v___y_2463_, 0);
lean_inc(v_a_2464_);
lean_dec_ref_known(v___y_2463_, 1);
v_a_2457_ = v_a_2464_;
goto v___jp_2456_;
}
else
{
lean_object* v_a_2465_; lean_object* v___x_2467_; uint8_t v_isShared_2468_; uint8_t v_isSharedCheck_2472_; 
lean_dec_ref(v_bs_x27_2455_);
v_a_2465_ = lean_ctor_get(v___y_2463_, 0);
v_isSharedCheck_2472_ = !lean_is_exclusive(v___y_2463_);
if (v_isSharedCheck_2472_ == 0)
{
v___x_2467_ = v___y_2463_;
v_isShared_2468_ = v_isSharedCheck_2472_;
goto v_resetjp_2466_;
}
else
{
lean_inc(v_a_2465_);
lean_dec(v___y_2463_);
v___x_2467_ = lean_box(0);
v_isShared_2468_ = v_isSharedCheck_2472_;
goto v_resetjp_2466_;
}
v_resetjp_2466_:
{
lean_object* v___x_2470_; 
if (v_isShared_2468_ == 0)
{
v___x_2470_ = v___x_2467_;
goto v_reusejp_2469_;
}
else
{
lean_object* v_reuseFailAlloc_2471_; 
v_reuseFailAlloc_2471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2471_, 0, v_a_2465_);
v___x_2470_ = v_reuseFailAlloc_2471_;
goto v_reusejp_2469_;
}
v_reusejp_2469_:
{
return v___x_2470_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__1___boxed(lean_object* v_indicesFVarIds_2482_, lean_object* v_sz_2483_, lean_object* v_i_2484_, lean_object* v_bs_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_){
_start:
{
size_t v_sz_boxed_2491_; size_t v_i_boxed_2492_; lean_object* v_res_2493_; 
v_sz_boxed_2491_ = lean_unbox_usize(v_sz_2483_);
lean_dec(v_sz_2483_);
v_i_boxed_2492_ = lean_unbox_usize(v_i_2484_);
lean_dec(v_i_2484_);
v_res_2493_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__1(v_indicesFVarIds_2482_, v_sz_boxed_2491_, v_i_boxed_2492_, v_bs_2485_, v___y_2486_, v___y_2487_, v___y_2488_, v___y_2489_);
lean_dec(v___y_2489_);
lean_dec_ref(v___y_2488_);
lean_dec(v___y_2487_);
lean_dec_ref(v___y_2486_);
lean_dec_ref(v_indicesFVarIds_2482_);
return v_res_2493_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices(lean_object* v_s_u2081_2494_, lean_object* v_s_u2082_2495_, lean_object* v_a_2496_, lean_object* v_a_2497_, lean_object* v_a_2498_, lean_object* v_a_2499_){
_start:
{
lean_object* v_indicesFVarIds_2501_; size_t v_sz_2502_; size_t v___x_2503_; lean_object* v___x_2504_; 
v_indicesFVarIds_2501_ = lean_ctor_get(v_s_u2081_2494_, 1);
v_sz_2502_ = lean_array_size(v_s_u2082_2495_);
v___x_2503_ = ((size_t)0ULL);
v___x_2504_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__1(v_indicesFVarIds_2501_, v_sz_2502_, v___x_2503_, v_s_u2082_2495_, v_a_2496_, v_a_2497_, v_a_2498_, v_a_2499_);
return v___x_2504_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices___boxed(lean_object* v_s_u2081_2505_, lean_object* v_s_u2082_2506_, lean_object* v_a_2507_, lean_object* v_a_2508_, lean_object* v_a_2509_, lean_object* v_a_2510_, lean_object* v_a_2511_){
_start:
{
lean_object* v_res_2512_; 
v_res_2512_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices(v_s_u2081_2505_, v_s_u2082_2506_, v_a_2507_, v_a_2508_, v_a_2509_, v_a_2510_);
lean_dec(v_a_2510_);
lean_dec_ref(v_a_2509_);
lean_dec(v_a_2508_);
lean_dec_ref(v_a_2507_);
lean_dec_ref(v_s_u2081_2505_);
return v_res_2512_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0___redArg(lean_object* v_ctorNames_2513_, lean_object* v_us_2514_, lean_object* v_params_2515_, lean_object* v_majorFVarId_2516_, size_t v_sz_2517_, size_t v_i_2518_, lean_object* v_bs_2519_){
_start:
{
uint8_t v___x_2520_; 
v___x_2520_ = lean_usize_dec_lt(v_i_2518_, v_sz_2517_);
if (v___x_2520_ == 0)
{
lean_dec(v_majorFVarId_2516_);
lean_dec(v_us_2514_);
return v_bs_2519_;
}
else
{
lean_object* v_v_2521_; lean_object* v___x_2522_; lean_object* v_bs_x27_2523_; lean_object* v___y_2525_; lean_object* v___x_2530_; lean_object* v___x_2531_; uint8_t v___x_2532_; 
v_v_2521_ = lean_array_uget(v_bs_2519_, v_i_2518_);
v___x_2522_ = lean_unsigned_to_nat(0u);
v_bs_x27_2523_ = lean_array_uset(v_bs_2519_, v_i_2518_, v___x_2522_);
v___x_2530_ = lean_usize_to_nat(v_i_2518_);
v___x_2531_ = lean_array_get_size(v_ctorNames_2513_);
v___x_2532_ = lean_nat_dec_lt(v___x_2530_, v___x_2531_);
if (v___x_2532_ == 0)
{
lean_object* v___x_2533_; lean_object* v___x_2534_; 
lean_dec(v___x_2530_);
v___x_2533_ = lean_box(0);
v___x_2534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2534_, 0, v_v_2521_);
lean_ctor_set(v___x_2534_, 1, v___x_2533_);
v___y_2525_ = v___x_2534_;
goto v___jp_2524_;
}
else
{
lean_object* v_mvarId_2535_; lean_object* v_fields_2536_; lean_object* v_subst_2537_; lean_object* v___x_2539_; uint8_t v_isShared_2540_; uint8_t v_isSharedCheck_2552_; 
v_mvarId_2535_ = lean_ctor_get(v_v_2521_, 0);
v_fields_2536_ = lean_ctor_get(v_v_2521_, 1);
v_subst_2537_ = lean_ctor_get(v_v_2521_, 2);
v_isSharedCheck_2552_ = !lean_is_exclusive(v_v_2521_);
if (v_isSharedCheck_2552_ == 0)
{
v___x_2539_ = v_v_2521_;
v_isShared_2540_ = v_isSharedCheck_2552_;
goto v_resetjp_2538_;
}
else
{
lean_inc(v_subst_2537_);
lean_inc(v_fields_2536_);
lean_inc(v_mvarId_2535_);
lean_dec(v_v_2521_);
v___x_2539_ = lean_box(0);
v_isShared_2540_ = v_isSharedCheck_2552_;
goto v_resetjp_2538_;
}
v_resetjp_2538_:
{
lean_object* v_ctorName_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v_ctorApp_2544_; lean_object* v___x_2545_; lean_object* v_subst_2546_; lean_object* v___x_2548_; 
v_ctorName_2541_ = lean_array_fget_borrowed(v_ctorNames_2513_, v___x_2530_);
lean_dec(v___x_2530_);
lean_inc(v_us_2514_);
lean_inc(v_ctorName_2541_);
v___x_2542_ = l_Lean_mkConst(v_ctorName_2541_, v_us_2514_);
v___x_2543_ = l_Lean_mkAppN(v___x_2542_, v_params_2515_);
v_ctorApp_2544_ = l_Lean_mkAppN(v___x_2543_, v_fields_2536_);
v___x_2545_ = l_Lean_Meta_FVarSubst_erase(v_subst_2537_, v_majorFVarId_2516_);
lean_inc(v_majorFVarId_2516_);
v_subst_2546_ = l_Lean_Meta_FVarSubst_insert(v___x_2545_, v_majorFVarId_2516_, v_ctorApp_2544_);
if (v_isShared_2540_ == 0)
{
lean_ctor_set(v___x_2539_, 2, v_subst_2546_);
v___x_2548_ = v___x_2539_;
goto v_reusejp_2547_;
}
else
{
lean_object* v_reuseFailAlloc_2551_; 
v_reuseFailAlloc_2551_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2551_, 0, v_mvarId_2535_);
lean_ctor_set(v_reuseFailAlloc_2551_, 1, v_fields_2536_);
lean_ctor_set(v_reuseFailAlloc_2551_, 2, v_subst_2546_);
v___x_2548_ = v_reuseFailAlloc_2551_;
goto v_reusejp_2547_;
}
v_reusejp_2547_:
{
lean_object* v___x_2549_; lean_object* v___x_2550_; 
lean_inc(v_ctorName_2541_);
v___x_2549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2549_, 0, v_ctorName_2541_);
v___x_2550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2550_, 0, v___x_2548_);
lean_ctor_set(v___x_2550_, 1, v___x_2549_);
v___y_2525_ = v___x_2550_;
goto v___jp_2524_;
}
}
}
v___jp_2524_:
{
size_t v___x_2526_; size_t v___x_2527_; lean_object* v___x_2528_; 
v___x_2526_ = ((size_t)1ULL);
v___x_2527_ = lean_usize_add(v_i_2518_, v___x_2526_);
v___x_2528_ = lean_array_uset(v_bs_x27_2523_, v_i_2518_, v___y_2525_);
v_i_2518_ = v___x_2527_;
v_bs_2519_ = v___x_2528_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0___redArg___boxed(lean_object* v_ctorNames_2553_, lean_object* v_us_2554_, lean_object* v_params_2555_, lean_object* v_majorFVarId_2556_, lean_object* v_sz_2557_, lean_object* v_i_2558_, lean_object* v_bs_2559_){
_start:
{
size_t v_sz_boxed_2560_; size_t v_i_boxed_2561_; lean_object* v_res_2562_; 
v_sz_boxed_2560_ = lean_unbox_usize(v_sz_2557_);
lean_dec(v_sz_2557_);
v_i_boxed_2561_ = lean_unbox_usize(v_i_2558_);
lean_dec(v_i_2558_);
v_res_2562_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0___redArg(v_ctorNames_2553_, v_us_2554_, v_params_2555_, v_majorFVarId_2556_, v_sz_boxed_2560_, v_i_boxed_2561_, v_bs_2559_);
lean_dec_ref(v_params_2555_);
lean_dec_ref(v_ctorNames_2553_);
return v_res_2562_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals(lean_object* v_s_2563_, lean_object* v_ctorNames_2564_, lean_object* v_majorFVarId_2565_, lean_object* v_us_2566_, lean_object* v_params_2567_){
_start:
{
size_t v_sz_2568_; size_t v___x_2569_; lean_object* v___x_2570_; 
v_sz_2568_ = lean_array_size(v_s_2563_);
v___x_2569_ = ((size_t)0ULL);
v___x_2570_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0___redArg(v_ctorNames_2564_, v_us_2566_, v_params_2567_, v_majorFVarId_2565_, v_sz_2568_, v___x_2569_, v_s_2563_);
return v___x_2570_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals___boxed(lean_object* v_s_2571_, lean_object* v_ctorNames_2572_, lean_object* v_majorFVarId_2573_, lean_object* v_us_2574_, lean_object* v_params_2575_){
_start:
{
lean_object* v_res_2576_; 
v_res_2576_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals(v_s_2571_, v_ctorNames_2572_, v_majorFVarId_2573_, v_us_2574_, v_params_2575_);
lean_dec_ref(v_params_2575_);
lean_dec_ref(v_ctorNames_2572_);
return v_res_2576_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0(lean_object* v_ctorNames_2577_, lean_object* v_us_2578_, lean_object* v_params_2579_, lean_object* v_majorFVarId_2580_, lean_object* v_as_2581_, size_t v_sz_2582_, size_t v_i_2583_, lean_object* v_bs_2584_){
_start:
{
lean_object* v___x_2585_; 
v___x_2585_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0___redArg(v_ctorNames_2577_, v_us_2578_, v_params_2579_, v_majorFVarId_2580_, v_sz_2582_, v_i_2583_, v_bs_2584_);
return v___x_2585_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0___boxed(lean_object* v_ctorNames_2586_, lean_object* v_us_2587_, lean_object* v_params_2588_, lean_object* v_majorFVarId_2589_, lean_object* v_as_2590_, lean_object* v_sz_2591_, lean_object* v_i_2592_, lean_object* v_bs_2593_){
_start:
{
size_t v_sz_boxed_2594_; size_t v_i_boxed_2595_; lean_object* v_res_2596_; 
v_sz_boxed_2594_ = lean_unbox_usize(v_sz_2591_);
lean_dec(v_sz_2591_);
v_i_boxed_2595_ = lean_unbox_usize(v_i_2592_);
lean_dec(v_i_2592_);
v_res_2596_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0(v_ctorNames_2586_, v_us_2587_, v_params_2588_, v_majorFVarId_2589_, v_as_2590_, v_sz_boxed_2594_, v_i_boxed_2595_, v_bs_2593_);
lean_dec_ref(v_as_2590_);
lean_dec_ref(v_params_2588_);
lean_dec_ref(v_ctorNames_2586_);
return v_res_2596_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_2602_; lean_object* v___x_2603_; 
v___x_2602_ = l_Lean_maxRecDepthErrorMessage;
v___x_2603_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2603_, 0, v___x_2602_);
return v___x_2603_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_2604_; lean_object* v___x_2605_; 
v___x_2604_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__3);
v___x_2605_ = l_Lean_MessageData_ofFormat(v___x_2604_);
return v___x_2605_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; 
v___x_2606_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__4);
v___x_2607_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__2));
v___x_2608_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2608_, 0, v___x_2607_);
lean_ctor_set(v___x_2608_, 1, v___x_2606_);
return v___x_2608_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg(lean_object* v_ref_2609_){
_start:
{
lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; 
v___x_2611_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__5);
v___x_2612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2612_, 0, v_ref_2609_);
lean_ctor_set(v___x_2612_, 1, v___x_2611_);
v___x_2613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2613_, 0, v___x_2612_);
return v___x_2613_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___boxed(lean_object* v_ref_2614_, lean_object* v___y_2615_){
_start:
{
lean_object* v_res_2616_; 
v_res_2616_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg(v_ref_2614_);
return v_res_2616_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0(lean_object* v_00_u03b1_2617_, lean_object* v_ref_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_){
_start:
{
lean_object* v___x_2624_; 
v___x_2624_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg(v_ref_2618_);
return v___x_2624_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___boxed(lean_object* v_00_u03b1_2625_, lean_object* v_ref_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_){
_start:
{
lean_object* v_res_2632_; 
v_res_2632_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0(v_00_u03b1_2625_, v_ref_2626_, v___y_2627_, v___y_2628_, v___y_2629_, v___y_2630_);
lean_dec(v___y_2630_);
lean_dec_ref(v___y_2629_);
lean_dec(v___y_2628_);
lean_dec_ref(v___y_2627_);
return v_res_2632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_unifyEqs_x3f(lean_object* v_numEqs_2634_, lean_object* v_mvarId_2635_, lean_object* v_subst_2636_, lean_object* v_caseName_x3f_2637_, lean_object* v_a_2638_, lean_object* v_a_2639_, lean_object* v_a_2640_, lean_object* v_a_2641_){
_start:
{
lean_object* v_fileName_2643_; lean_object* v_fileMap_2644_; lean_object* v_options_2645_; lean_object* v_currRecDepth_2646_; lean_object* v_maxRecDepth_2647_; lean_object* v_ref_2648_; lean_object* v_currNamespace_2649_; lean_object* v_openDecls_2650_; lean_object* v_initHeartbeats_2651_; lean_object* v_maxHeartbeats_2652_; lean_object* v_quotContext_2653_; lean_object* v_currMacroScope_2654_; uint8_t v_diag_2655_; lean_object* v_cancelTk_x3f_2656_; uint8_t v_suppressElabErrors_2657_; lean_object* v_inheritedTraceOptions_2658_; lean_object* v___x_2659_; uint8_t v___x_2660_; uint8_t v___x_2706_; 
v_fileName_2643_ = lean_ctor_get(v_a_2640_, 0);
lean_inc_ref(v_fileName_2643_);
v_fileMap_2644_ = lean_ctor_get(v_a_2640_, 1);
lean_inc_ref(v_fileMap_2644_);
v_options_2645_ = lean_ctor_get(v_a_2640_, 2);
lean_inc_ref(v_options_2645_);
v_currRecDepth_2646_ = lean_ctor_get(v_a_2640_, 3);
lean_inc(v_currRecDepth_2646_);
v_maxRecDepth_2647_ = lean_ctor_get(v_a_2640_, 4);
lean_inc(v_maxRecDepth_2647_);
v_ref_2648_ = lean_ctor_get(v_a_2640_, 5);
lean_inc(v_ref_2648_);
v_currNamespace_2649_ = lean_ctor_get(v_a_2640_, 6);
lean_inc(v_currNamespace_2649_);
v_openDecls_2650_ = lean_ctor_get(v_a_2640_, 7);
lean_inc(v_openDecls_2650_);
v_initHeartbeats_2651_ = lean_ctor_get(v_a_2640_, 8);
lean_inc(v_initHeartbeats_2651_);
v_maxHeartbeats_2652_ = lean_ctor_get(v_a_2640_, 9);
lean_inc(v_maxHeartbeats_2652_);
v_quotContext_2653_ = lean_ctor_get(v_a_2640_, 10);
lean_inc(v_quotContext_2653_);
v_currMacroScope_2654_ = lean_ctor_get(v_a_2640_, 11);
lean_inc(v_currMacroScope_2654_);
v_diag_2655_ = lean_ctor_get_uint8(v_a_2640_, sizeof(void*)*14);
v_cancelTk_x3f_2656_ = lean_ctor_get(v_a_2640_, 12);
lean_inc(v_cancelTk_x3f_2656_);
v_suppressElabErrors_2657_ = lean_ctor_get_uint8(v_a_2640_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2658_ = lean_ctor_get(v_a_2640_, 13);
lean_inc_ref(v_inheritedTraceOptions_2658_);
lean_dec_ref(v_a_2640_);
v___x_2659_ = lean_unsigned_to_nat(0u);
v___x_2660_ = lean_nat_dec_eq(v_numEqs_2634_, v___x_2659_);
v___x_2706_ = lean_nat_dec_eq(v_maxRecDepth_2647_, v___x_2659_);
if (v___x_2706_ == 0)
{
uint8_t v___x_2707_; 
v___x_2707_ = lean_nat_dec_eq(v_currRecDepth_2646_, v_maxRecDepth_2647_);
if (v___x_2707_ == 0)
{
goto v___jp_2661_;
}
else
{
lean_object* v___x_2708_; 
lean_dec_ref(v_inheritedTraceOptions_2658_);
lean_dec(v_cancelTk_x3f_2656_);
lean_dec(v_currMacroScope_2654_);
lean_dec(v_quotContext_2653_);
lean_dec(v_maxHeartbeats_2652_);
lean_dec(v_initHeartbeats_2651_);
lean_dec(v_openDecls_2650_);
lean_dec(v_currNamespace_2649_);
lean_dec(v_maxRecDepth_2647_);
lean_dec(v_currRecDepth_2646_);
lean_dec_ref(v_options_2645_);
lean_dec_ref(v_fileMap_2644_);
lean_dec_ref(v_fileName_2643_);
lean_dec(v_caseName_x3f_2637_);
lean_dec(v_subst_2636_);
lean_dec(v_mvarId_2635_);
lean_dec(v_numEqs_2634_);
v___x_2708_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg(v_ref_2648_);
return v___x_2708_;
}
}
else
{
goto v___jp_2661_;
}
v___jp_2661_:
{
if (v___x_2660_ == 0)
{
lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; 
v___x_2662_ = lean_unsigned_to_nat(1u);
v___x_2663_ = lean_nat_add(v_currRecDepth_2646_, v___x_2662_);
lean_dec(v_currRecDepth_2646_);
v___x_2664_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2664_, 0, v_fileName_2643_);
lean_ctor_set(v___x_2664_, 1, v_fileMap_2644_);
lean_ctor_set(v___x_2664_, 2, v_options_2645_);
lean_ctor_set(v___x_2664_, 3, v___x_2663_);
lean_ctor_set(v___x_2664_, 4, v_maxRecDepth_2647_);
lean_ctor_set(v___x_2664_, 5, v_ref_2648_);
lean_ctor_set(v___x_2664_, 6, v_currNamespace_2649_);
lean_ctor_set(v___x_2664_, 7, v_openDecls_2650_);
lean_ctor_set(v___x_2664_, 8, v_initHeartbeats_2651_);
lean_ctor_set(v___x_2664_, 9, v_maxHeartbeats_2652_);
lean_ctor_set(v___x_2664_, 10, v_quotContext_2653_);
lean_ctor_set(v___x_2664_, 11, v_currMacroScope_2654_);
lean_ctor_set(v___x_2664_, 12, v_cancelTk_x3f_2656_);
lean_ctor_set(v___x_2664_, 13, v_inheritedTraceOptions_2658_);
lean_ctor_set_uint8(v___x_2664_, sizeof(void*)*14, v_diag_2655_);
lean_ctor_set_uint8(v___x_2664_, sizeof(void*)*14 + 1, v_suppressElabErrors_2657_);
v___x_2665_ = l_Lean_Meta_intro1Core(v_mvarId_2635_, v___x_2660_, v_a_2638_, v_a_2639_, v___x_2664_, v_a_2641_);
if (lean_obj_tag(v___x_2665_) == 0)
{
lean_object* v_a_2666_; lean_object* v_fst_2667_; lean_object* v_snd_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; 
v_a_2666_ = lean_ctor_get(v___x_2665_, 0);
lean_inc(v_a_2666_);
lean_dec_ref_known(v___x_2665_, 1);
v_fst_2667_ = lean_ctor_get(v_a_2666_, 0);
lean_inc(v_fst_2667_);
v_snd_2668_ = lean_ctor_get(v_a_2666_, 1);
lean_inc(v_snd_2668_);
lean_dec(v_a_2666_);
v___x_2669_ = ((lean_object*)(l_Lean_Meta_Cases_unifyEqs_x3f___closed__0));
lean_inc(v_caseName_x3f_2637_);
v___x_2670_ = l_Lean_Meta_unifyEq_x3f(v_snd_2668_, v_fst_2667_, v_subst_2636_, v___x_2669_, v_caseName_x3f_2637_, v_a_2638_, v_a_2639_, v___x_2664_, v_a_2641_);
if (lean_obj_tag(v___x_2670_) == 0)
{
lean_object* v_a_2671_; lean_object* v___x_2673_; uint8_t v_isShared_2674_; uint8_t v_isSharedCheck_2686_; 
v_a_2671_ = lean_ctor_get(v___x_2670_, 0);
v_isSharedCheck_2686_ = !lean_is_exclusive(v___x_2670_);
if (v_isSharedCheck_2686_ == 0)
{
v___x_2673_ = v___x_2670_;
v_isShared_2674_ = v_isSharedCheck_2686_;
goto v_resetjp_2672_;
}
else
{
lean_inc(v_a_2671_);
lean_dec(v___x_2670_);
v___x_2673_ = lean_box(0);
v_isShared_2674_ = v_isSharedCheck_2686_;
goto v_resetjp_2672_;
}
v_resetjp_2672_:
{
if (lean_obj_tag(v_a_2671_) == 1)
{
lean_object* v_val_2675_; lean_object* v_mvarId_2676_; lean_object* v_subst_2677_; lean_object* v_numNewEqs_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; 
lean_del_object(v___x_2673_);
v_val_2675_ = lean_ctor_get(v_a_2671_, 0);
lean_inc(v_val_2675_);
lean_dec_ref_known(v_a_2671_, 1);
v_mvarId_2676_ = lean_ctor_get(v_val_2675_, 0);
lean_inc(v_mvarId_2676_);
v_subst_2677_ = lean_ctor_get(v_val_2675_, 1);
lean_inc(v_subst_2677_);
v_numNewEqs_2678_ = lean_ctor_get(v_val_2675_, 2);
lean_inc(v_numNewEqs_2678_);
lean_dec(v_val_2675_);
v___x_2679_ = lean_nat_sub(v_numEqs_2634_, v___x_2662_);
lean_dec(v_numEqs_2634_);
v___x_2680_ = lean_nat_add(v___x_2679_, v_numNewEqs_2678_);
lean_dec(v_numNewEqs_2678_);
lean_dec(v___x_2679_);
v_numEqs_2634_ = v___x_2680_;
v_mvarId_2635_ = v_mvarId_2676_;
v_subst_2636_ = v_subst_2677_;
v_a_2640_ = v___x_2664_;
goto _start;
}
else
{
lean_object* v___x_2682_; lean_object* v___x_2684_; 
lean_dec(v_a_2671_);
lean_dec_ref_known(v___x_2664_, 14);
lean_dec(v_caseName_x3f_2637_);
lean_dec(v_numEqs_2634_);
v___x_2682_ = lean_box(0);
if (v_isShared_2674_ == 0)
{
lean_ctor_set(v___x_2673_, 0, v___x_2682_);
v___x_2684_ = v___x_2673_;
goto v_reusejp_2683_;
}
else
{
lean_object* v_reuseFailAlloc_2685_; 
v_reuseFailAlloc_2685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2685_, 0, v___x_2682_);
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
else
{
lean_object* v_a_2687_; lean_object* v___x_2689_; uint8_t v_isShared_2690_; uint8_t v_isSharedCheck_2694_; 
lean_dec_ref_known(v___x_2664_, 14);
lean_dec(v_caseName_x3f_2637_);
lean_dec(v_numEqs_2634_);
v_a_2687_ = lean_ctor_get(v___x_2670_, 0);
v_isSharedCheck_2694_ = !lean_is_exclusive(v___x_2670_);
if (v_isSharedCheck_2694_ == 0)
{
v___x_2689_ = v___x_2670_;
v_isShared_2690_ = v_isSharedCheck_2694_;
goto v_resetjp_2688_;
}
else
{
lean_inc(v_a_2687_);
lean_dec(v___x_2670_);
v___x_2689_ = lean_box(0);
v_isShared_2690_ = v_isSharedCheck_2694_;
goto v_resetjp_2688_;
}
v_resetjp_2688_:
{
lean_object* v___x_2692_; 
if (v_isShared_2690_ == 0)
{
v___x_2692_ = v___x_2689_;
goto v_reusejp_2691_;
}
else
{
lean_object* v_reuseFailAlloc_2693_; 
v_reuseFailAlloc_2693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2693_, 0, v_a_2687_);
v___x_2692_ = v_reuseFailAlloc_2693_;
goto v_reusejp_2691_;
}
v_reusejp_2691_:
{
return v___x_2692_;
}
}
}
}
else
{
lean_object* v_a_2695_; lean_object* v___x_2697_; uint8_t v_isShared_2698_; uint8_t v_isSharedCheck_2702_; 
lean_dec_ref_known(v___x_2664_, 14);
lean_dec(v_caseName_x3f_2637_);
lean_dec(v_subst_2636_);
lean_dec(v_numEqs_2634_);
v_a_2695_ = lean_ctor_get(v___x_2665_, 0);
v_isSharedCheck_2702_ = !lean_is_exclusive(v___x_2665_);
if (v_isSharedCheck_2702_ == 0)
{
v___x_2697_ = v___x_2665_;
v_isShared_2698_ = v_isSharedCheck_2702_;
goto v_resetjp_2696_;
}
else
{
lean_inc(v_a_2695_);
lean_dec(v___x_2665_);
v___x_2697_ = lean_box(0);
v_isShared_2698_ = v_isSharedCheck_2702_;
goto v_resetjp_2696_;
}
v_resetjp_2696_:
{
lean_object* v___x_2700_; 
if (v_isShared_2698_ == 0)
{
v___x_2700_ = v___x_2697_;
goto v_reusejp_2699_;
}
else
{
lean_object* v_reuseFailAlloc_2701_; 
v_reuseFailAlloc_2701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2701_, 0, v_a_2695_);
v___x_2700_ = v_reuseFailAlloc_2701_;
goto v_reusejp_2699_;
}
v_reusejp_2699_:
{
return v___x_2700_;
}
}
}
}
else
{
lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; 
lean_dec_ref(v_inheritedTraceOptions_2658_);
lean_dec(v_cancelTk_x3f_2656_);
lean_dec(v_currMacroScope_2654_);
lean_dec(v_quotContext_2653_);
lean_dec(v_maxHeartbeats_2652_);
lean_dec(v_initHeartbeats_2651_);
lean_dec(v_openDecls_2650_);
lean_dec(v_currNamespace_2649_);
lean_dec(v_ref_2648_);
lean_dec(v_maxRecDepth_2647_);
lean_dec(v_currRecDepth_2646_);
lean_dec_ref(v_options_2645_);
lean_dec_ref(v_fileMap_2644_);
lean_dec_ref(v_fileName_2643_);
lean_dec(v_caseName_x3f_2637_);
lean_dec(v_numEqs_2634_);
v___x_2703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2703_, 0, v_mvarId_2635_);
lean_ctor_set(v___x_2703_, 1, v_subst_2636_);
v___x_2704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2704_, 0, v___x_2703_);
v___x_2705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2705_, 0, v___x_2704_);
return v___x_2705_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_unifyEqs_x3f___boxed(lean_object* v_numEqs_2709_, lean_object* v_mvarId_2710_, lean_object* v_subst_2711_, lean_object* v_caseName_x3f_2712_, lean_object* v_a_2713_, lean_object* v_a_2714_, lean_object* v_a_2715_, lean_object* v_a_2716_, lean_object* v_a_2717_){
_start:
{
lean_object* v_res_2718_; 
v_res_2718_ = l_Lean_Meta_Cases_unifyEqs_x3f(v_numEqs_2709_, v_mvarId_2710_, v_subst_2711_, v_caseName_x3f_2712_, v_a_2713_, v_a_2714_, v_a_2715_, v_a_2716_);
lean_dec(v_a_2716_);
lean_dec(v_a_2714_);
lean_dec_ref(v_a_2713_);
return v_res_2718_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__0(lean_object* v_snd_2719_, size_t v_sz_2720_, size_t v_i_2721_, lean_object* v_bs_2722_){
_start:
{
uint8_t v___x_2723_; 
v___x_2723_ = lean_usize_dec_lt(v_i_2721_, v_sz_2720_);
if (v___x_2723_ == 0)
{
lean_dec(v_snd_2719_);
return v_bs_2722_;
}
else
{
lean_object* v_v_2724_; lean_object* v___x_2725_; lean_object* v_bs_x27_2726_; lean_object* v___x_2727_; size_t v___x_2728_; size_t v___x_2729_; lean_object* v___x_2730_; 
v_v_2724_ = lean_array_uget(v_bs_2722_, v_i_2721_);
v___x_2725_ = lean_unsigned_to_nat(0u);
v_bs_x27_2726_ = lean_array_uset(v_bs_2722_, v_i_2721_, v___x_2725_);
lean_inc(v_snd_2719_);
v___x_2727_ = l_Lean_Meta_FVarSubst_apply(v_snd_2719_, v_v_2724_);
lean_dec(v_v_2724_);
v___x_2728_ = ((size_t)1ULL);
v___x_2729_ = lean_usize_add(v_i_2721_, v___x_2728_);
v___x_2730_ = lean_array_uset(v_bs_x27_2726_, v_i_2721_, v___x_2727_);
v_i_2721_ = v___x_2729_;
v_bs_2722_ = v___x_2730_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__0___boxed(lean_object* v_snd_2732_, lean_object* v_sz_2733_, lean_object* v_i_2734_, lean_object* v_bs_2735_){
_start:
{
size_t v_sz_boxed_2736_; size_t v_i_boxed_2737_; lean_object* v_res_2738_; 
v_sz_boxed_2736_ = lean_unbox_usize(v_sz_2733_);
lean_dec(v_sz_2733_);
v_i_boxed_2737_ = lean_unbox_usize(v_i_2734_);
lean_dec(v_i_2734_);
v_res_2738_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__0(v_snd_2732_, v_sz_boxed_2736_, v_i_boxed_2737_, v_bs_2735_);
return v_res_2738_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1_spec__1(lean_object* v_numEqs_2739_, lean_object* v_as_2740_, size_t v_i_2741_, size_t v_stop_2742_, lean_object* v_b_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_){
_start:
{
uint8_t v___x_2749_; 
v___x_2749_ = lean_usize_dec_eq(v_i_2741_, v_stop_2742_);
if (v___x_2749_ == 0)
{
lean_object* v___x_2750_; lean_object* v_toInductionSubgoal_2751_; lean_object* v_ctorName_2752_; lean_object* v___x_2754_; uint8_t v_isShared_2755_; uint8_t v_isSharedCheck_2791_; 
v___x_2750_ = lean_array_uget(v_as_2740_, v_i_2741_);
v_toInductionSubgoal_2751_ = lean_ctor_get(v___x_2750_, 0);
v_ctorName_2752_ = lean_ctor_get(v___x_2750_, 1);
v_isSharedCheck_2791_ = !lean_is_exclusive(v___x_2750_);
if (v_isSharedCheck_2791_ == 0)
{
v___x_2754_ = v___x_2750_;
v_isShared_2755_ = v_isSharedCheck_2791_;
goto v_resetjp_2753_;
}
else
{
lean_inc(v_ctorName_2752_);
lean_inc(v_toInductionSubgoal_2751_);
lean_dec(v___x_2750_);
v___x_2754_ = lean_box(0);
v_isShared_2755_ = v_isSharedCheck_2791_;
goto v_resetjp_2753_;
}
v_resetjp_2753_:
{
lean_object* v_mvarId_2756_; lean_object* v_fields_2757_; lean_object* v_subst_2758_; lean_object* v___x_2760_; uint8_t v_isShared_2761_; uint8_t v_isSharedCheck_2790_; 
v_mvarId_2756_ = lean_ctor_get(v_toInductionSubgoal_2751_, 0);
v_fields_2757_ = lean_ctor_get(v_toInductionSubgoal_2751_, 1);
v_subst_2758_ = lean_ctor_get(v_toInductionSubgoal_2751_, 2);
v_isSharedCheck_2790_ = !lean_is_exclusive(v_toInductionSubgoal_2751_);
if (v_isSharedCheck_2790_ == 0)
{
v___x_2760_ = v_toInductionSubgoal_2751_;
v_isShared_2761_ = v_isSharedCheck_2790_;
goto v_resetjp_2759_;
}
else
{
lean_inc(v_subst_2758_);
lean_inc(v_fields_2757_);
lean_inc(v_mvarId_2756_);
lean_dec(v_toInductionSubgoal_2751_);
v___x_2760_ = lean_box(0);
v_isShared_2761_ = v_isSharedCheck_2790_;
goto v_resetjp_2759_;
}
v_resetjp_2759_:
{
lean_object* v___x_2762_; 
lean_inc_ref(v___y_2746_);
lean_inc(v_ctorName_2752_);
lean_inc(v_numEqs_2739_);
v___x_2762_ = l_Lean_Meta_Cases_unifyEqs_x3f(v_numEqs_2739_, v_mvarId_2756_, v_subst_2758_, v_ctorName_2752_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_);
if (lean_obj_tag(v___x_2762_) == 0)
{
lean_object* v_a_2763_; lean_object* v_a_2765_; 
v_a_2763_ = lean_ctor_get(v___x_2762_, 0);
lean_inc(v_a_2763_);
lean_dec_ref_known(v___x_2762_, 1);
if (lean_obj_tag(v_a_2763_) == 0)
{
lean_del_object(v___x_2760_);
lean_dec_ref(v_fields_2757_);
lean_del_object(v___x_2754_);
lean_dec(v_ctorName_2752_);
v_a_2765_ = v_b_2743_;
goto v___jp_2764_;
}
else
{
lean_object* v_val_2769_; lean_object* v_fst_2770_; lean_object* v_snd_2771_; size_t v_sz_2772_; size_t v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2776_; 
v_val_2769_ = lean_ctor_get(v_a_2763_, 0);
lean_inc(v_val_2769_);
lean_dec_ref_known(v_a_2763_, 1);
v_fst_2770_ = lean_ctor_get(v_val_2769_, 0);
lean_inc(v_fst_2770_);
v_snd_2771_ = lean_ctor_get(v_val_2769_, 1);
lean_inc_n(v_snd_2771_, 2);
lean_dec(v_val_2769_);
v_sz_2772_ = lean_array_size(v_fields_2757_);
v___x_2773_ = ((size_t)0ULL);
v___x_2774_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__0(v_snd_2771_, v_sz_2772_, v___x_2773_, v_fields_2757_);
if (v_isShared_2761_ == 0)
{
lean_ctor_set(v___x_2760_, 2, v_snd_2771_);
lean_ctor_set(v___x_2760_, 1, v___x_2774_);
lean_ctor_set(v___x_2760_, 0, v_fst_2770_);
v___x_2776_ = v___x_2760_;
goto v_reusejp_2775_;
}
else
{
lean_object* v_reuseFailAlloc_2781_; 
v_reuseFailAlloc_2781_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2781_, 0, v_fst_2770_);
lean_ctor_set(v_reuseFailAlloc_2781_, 1, v___x_2774_);
lean_ctor_set(v_reuseFailAlloc_2781_, 2, v_snd_2771_);
v___x_2776_ = v_reuseFailAlloc_2781_;
goto v_reusejp_2775_;
}
v_reusejp_2775_:
{
lean_object* v___x_2778_; 
if (v_isShared_2755_ == 0)
{
lean_ctor_set(v___x_2754_, 0, v___x_2776_);
v___x_2778_ = v___x_2754_;
goto v_reusejp_2777_;
}
else
{
lean_object* v_reuseFailAlloc_2780_; 
v_reuseFailAlloc_2780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2780_, 0, v___x_2776_);
lean_ctor_set(v_reuseFailAlloc_2780_, 1, v_ctorName_2752_);
v___x_2778_ = v_reuseFailAlloc_2780_;
goto v_reusejp_2777_;
}
v_reusejp_2777_:
{
lean_object* v___x_2779_; 
v___x_2779_ = lean_array_push(v_b_2743_, v___x_2778_);
v_a_2765_ = v___x_2779_;
goto v___jp_2764_;
}
}
}
v___jp_2764_:
{
size_t v___x_2766_; size_t v___x_2767_; 
v___x_2766_ = ((size_t)1ULL);
v___x_2767_ = lean_usize_add(v_i_2741_, v___x_2766_);
v_i_2741_ = v___x_2767_;
v_b_2743_ = v_a_2765_;
goto _start;
}
}
else
{
lean_object* v_a_2782_; lean_object* v___x_2784_; uint8_t v_isShared_2785_; uint8_t v_isSharedCheck_2789_; 
lean_del_object(v___x_2760_);
lean_dec_ref(v_fields_2757_);
lean_del_object(v___x_2754_);
lean_dec(v_ctorName_2752_);
lean_dec_ref(v_b_2743_);
lean_dec(v_numEqs_2739_);
v_a_2782_ = lean_ctor_get(v___x_2762_, 0);
v_isSharedCheck_2789_ = !lean_is_exclusive(v___x_2762_);
if (v_isSharedCheck_2789_ == 0)
{
v___x_2784_ = v___x_2762_;
v_isShared_2785_ = v_isSharedCheck_2789_;
goto v_resetjp_2783_;
}
else
{
lean_inc(v_a_2782_);
lean_dec(v___x_2762_);
v___x_2784_ = lean_box(0);
v_isShared_2785_ = v_isSharedCheck_2789_;
goto v_resetjp_2783_;
}
v_resetjp_2783_:
{
lean_object* v___x_2787_; 
if (v_isShared_2785_ == 0)
{
v___x_2787_ = v___x_2784_;
goto v_reusejp_2786_;
}
else
{
lean_object* v_reuseFailAlloc_2788_; 
v_reuseFailAlloc_2788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2788_, 0, v_a_2782_);
v___x_2787_ = v_reuseFailAlloc_2788_;
goto v_reusejp_2786_;
}
v_reusejp_2786_:
{
return v___x_2787_;
}
}
}
}
}
}
else
{
lean_object* v___x_2792_; 
lean_dec(v_numEqs_2739_);
v___x_2792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2792_, 0, v_b_2743_);
return v___x_2792_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1_spec__1___boxed(lean_object* v_numEqs_2793_, lean_object* v_as_2794_, lean_object* v_i_2795_, lean_object* v_stop_2796_, lean_object* v_b_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_){
_start:
{
size_t v_i_boxed_2803_; size_t v_stop_boxed_2804_; lean_object* v_res_2805_; 
v_i_boxed_2803_ = lean_unbox_usize(v_i_2795_);
lean_dec(v_i_2795_);
v_stop_boxed_2804_ = lean_unbox_usize(v_stop_2796_);
lean_dec(v_stop_2796_);
v_res_2805_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1_spec__1(v_numEqs_2793_, v_as_2794_, v_i_boxed_2803_, v_stop_boxed_2804_, v_b_2797_, v___y_2798_, v___y_2799_, v___y_2800_, v___y_2801_);
lean_dec(v___y_2801_);
lean_dec_ref(v___y_2800_);
lean_dec(v___y_2799_);
lean_dec_ref(v___y_2798_);
lean_dec_ref(v_as_2794_);
return v_res_2805_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1(lean_object* v_numEqs_2808_, lean_object* v_as_2809_, lean_object* v_start_2810_, lean_object* v_stop_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_){
_start:
{
lean_object* v___x_2817_; uint8_t v___x_2818_; 
v___x_2817_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1___closed__0));
v___x_2818_ = lean_nat_dec_lt(v_start_2810_, v_stop_2811_);
if (v___x_2818_ == 0)
{
lean_object* v___x_2819_; 
lean_dec(v_numEqs_2808_);
v___x_2819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2819_, 0, v___x_2817_);
return v___x_2819_;
}
else
{
lean_object* v___x_2820_; uint8_t v___x_2821_; 
v___x_2820_ = lean_array_get_size(v_as_2809_);
v___x_2821_ = lean_nat_dec_le(v_stop_2811_, v___x_2820_);
if (v___x_2821_ == 0)
{
uint8_t v___x_2822_; 
v___x_2822_ = lean_nat_dec_lt(v_start_2810_, v___x_2820_);
if (v___x_2822_ == 0)
{
lean_object* v___x_2823_; 
lean_dec(v_numEqs_2808_);
v___x_2823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2823_, 0, v___x_2817_);
return v___x_2823_;
}
else
{
size_t v___x_2824_; size_t v___x_2825_; lean_object* v___x_2826_; 
v___x_2824_ = lean_usize_of_nat(v_start_2810_);
v___x_2825_ = lean_usize_of_nat(v___x_2820_);
v___x_2826_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1_spec__1(v_numEqs_2808_, v_as_2809_, v___x_2824_, v___x_2825_, v___x_2817_, v___y_2812_, v___y_2813_, v___y_2814_, v___y_2815_);
return v___x_2826_;
}
}
else
{
size_t v___x_2827_; size_t v___x_2828_; lean_object* v___x_2829_; 
v___x_2827_ = lean_usize_of_nat(v_start_2810_);
v___x_2828_ = lean_usize_of_nat(v_stop_2811_);
v___x_2829_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1_spec__1(v_numEqs_2808_, v_as_2809_, v___x_2827_, v___x_2828_, v___x_2817_, v___y_2812_, v___y_2813_, v___y_2814_, v___y_2815_);
return v___x_2829_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1___boxed(lean_object* v_numEqs_2830_, lean_object* v_as_2831_, lean_object* v_start_2832_, lean_object* v_stop_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_){
_start:
{
lean_object* v_res_2839_; 
v_res_2839_ = l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1(v_numEqs_2830_, v_as_2831_, v_start_2832_, v_stop_2833_, v___y_2834_, v___y_2835_, v___y_2836_, v___y_2837_);
lean_dec(v___y_2837_);
lean_dec_ref(v___y_2836_);
lean_dec(v___y_2835_);
lean_dec_ref(v___y_2834_);
lean_dec(v_stop_2833_);
lean_dec(v_start_2832_);
lean_dec_ref(v_as_2831_);
return v_res_2839_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs(lean_object* v_numEqs_2840_, lean_object* v_subgoals_2841_, lean_object* v_a_2842_, lean_object* v_a_2843_, lean_object* v_a_2844_, lean_object* v_a_2845_){
_start:
{
lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; 
v___x_2847_ = lean_unsigned_to_nat(0u);
v___x_2848_ = lean_array_get_size(v_subgoals_2841_);
v___x_2849_ = l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1(v_numEqs_2840_, v_subgoals_2841_, v___x_2847_, v___x_2848_, v_a_2842_, v_a_2843_, v_a_2844_, v_a_2845_);
return v___x_2849_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs___boxed(lean_object* v_numEqs_2850_, lean_object* v_subgoals_2851_, lean_object* v_a_2852_, lean_object* v_a_2853_, lean_object* v_a_2854_, lean_object* v_a_2855_, lean_object* v_a_2856_){
_start:
{
lean_object* v_res_2857_; 
v_res_2857_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs(v_numEqs_2850_, v_subgoals_2851_, v_a_2852_, v_a_2853_, v_a_2854_, v_a_2855_);
lean_dec(v_a_2855_);
lean_dec_ref(v_a_2854_);
lean_dec(v_a_2853_);
lean_dec_ref(v_a_2852_);
lean_dec_ref(v_subgoals_2851_);
return v_res_2857_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0(lean_object* v___x_2869_, lean_object* v_mvarId_2870_, lean_object* v_majorFVarId_2871_, lean_object* v_givenNames_2872_, lean_object* v_ctx_2873_, uint8_t v_useNatCasesAuxOn_2874_, lean_object* v_interestingCtors_x3f_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_){
_start:
{
lean_object* v___x_2881_; 
lean_inc(v___y_2879_);
lean_inc_ref(v___y_2878_);
lean_inc(v___y_2877_);
lean_inc_ref(v___y_2876_);
v___x_2881_ = lean_infer_type(v___x_2869_, v___y_2876_, v___y_2877_, v___y_2878_, v___y_2879_);
if (lean_obj_tag(v___x_2881_) == 0)
{
lean_object* v_a_2882_; lean_object* v___x_2883_; 
v_a_2882_ = lean_ctor_get(v___x_2881_, 0);
lean_inc(v_a_2882_);
lean_dec_ref_known(v___x_2881_, 1);
v___x_2883_ = l_Lean_Meta_getInductiveUniverseAndParams(v_a_2882_, v___y_2876_, v___y_2877_, v___y_2878_, v___y_2879_);
if (lean_obj_tag(v___x_2883_) == 0)
{
lean_object* v_a_2884_; lean_object* v_fst_2885_; lean_object* v_snd_2886_; lean_object* v___y_2888_; lean_object* v___y_2889_; lean_object* v___y_2890_; lean_object* v___y_2891_; lean_object* v___y_2892_; lean_object* v___y_2915_; lean_object* v___y_2916_; lean_object* v___y_2917_; lean_object* v___y_2918_; lean_object* v___y_2924_; lean_object* v___y_2925_; lean_object* v___y_2926_; lean_object* v___y_2927_; 
v_a_2884_ = lean_ctor_get(v___x_2883_, 0);
lean_inc(v_a_2884_);
lean_dec_ref_known(v___x_2883_, 1);
v_fst_2885_ = lean_ctor_get(v_a_2884_, 0);
lean_inc(v_fst_2885_);
v_snd_2886_ = lean_ctor_get(v_a_2884_, 1);
lean_inc(v_snd_2886_);
lean_dec(v_a_2884_);
if (lean_obj_tag(v_interestingCtors_x3f_2875_) == 1)
{
lean_object* v_val_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v_inductiveVal_2940_; lean_object* v_toConstantVal_2941_; lean_object* v_env_2942_; lean_object* v_ctors_2943_; lean_object* v_name_2944_; uint8_t v___y_2946_; lean_object* v___x_2980_; uint8_t v___x_2981_; uint8_t v___x_2982_; 
v_val_2937_ = lean_ctor_get(v_interestingCtors_x3f_2875_, 0);
lean_inc(v_val_2937_);
lean_dec_ref_known(v_interestingCtors_x3f_2875_, 1);
v___x_2938_ = lean_st_ref_get(v___y_2879_);
v___x_2939_ = lean_st_ref_get(v___y_2879_);
v_inductiveVal_2940_ = lean_ctor_get(v_ctx_2873_, 0);
v_toConstantVal_2941_ = lean_ctor_get(v_inductiveVal_2940_, 0);
v_env_2942_ = lean_ctor_get(v___x_2938_, 0);
lean_inc_ref(v_env_2942_);
lean_dec(v___x_2938_);
v_ctors_2943_ = lean_ctor_get(v_inductiveVal_2940_, 4);
v_name_2944_ = lean_ctor_get(v_toConstantVal_2941_, 0);
v___x_2980_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__5));
v___x_2981_ = 1;
v___x_2982_ = l_Lean_Environment_contains(v_env_2942_, v___x_2980_, v___x_2981_);
if (v___x_2982_ == 0)
{
lean_dec(v___x_2939_);
v___y_2946_ = v___x_2982_;
goto v___jp_2945_;
}
else
{
lean_object* v_env_2983_; lean_object* v___x_2984_; uint8_t v___x_2985_; 
v_env_2983_ = lean_ctor_get(v___x_2939_, 0);
lean_inc_ref(v_env_2983_);
lean_dec(v___x_2939_);
lean_inc(v_name_2944_);
v___x_2984_ = l_Lean_mkCtorIdxName(v_name_2944_);
v___x_2985_ = l_Lean_Environment_contains(v_env_2983_, v___x_2984_, v___x_2981_);
v___y_2946_ = v___x_2985_;
goto v___jp_2945_;
}
v___jp_2945_:
{
if (v___y_2946_ == 0)
{
lean_dec(v_val_2937_);
v___y_2924_ = v___y_2876_;
v___y_2925_ = v___y_2877_;
v___y_2926_ = v___y_2878_;
v___y_2927_ = v___y_2879_;
goto v___jp_2923_;
}
else
{
lean_object* v___x_2947_; lean_object* v___x_2948_; uint8_t v___x_2949_; 
v___x_2947_ = lean_array_get_size(v_val_2937_);
v___x_2948_ = lean_unsigned_to_nat(0u);
v___x_2949_ = lean_nat_dec_eq(v___x_2947_, v___x_2948_);
if (v___x_2949_ == 0)
{
lean_object* v___x_2950_; uint8_t v___x_2951_; 
v___x_2950_ = l_List_lengthTR___redArg(v_ctors_2943_);
v___x_2951_ = lean_nat_dec_lt(v___x_2947_, v___x_2950_);
lean_dec(v___x_2950_);
if (v___x_2951_ == 0)
{
lean_dec(v_val_2937_);
v___y_2924_ = v___y_2876_;
v___y_2925_ = v___y_2877_;
v___y_2926_ = v___y_2878_;
v___y_2927_ = v___y_2879_;
goto v___jp_2923_;
}
else
{
lean_object* v___x_2952_; 
lean_inc(v_name_2944_);
lean_dec_ref(v_ctx_2873_);
lean_inc(v_val_2937_);
v___x_2952_ = l_Lean_Meta_mkSparseCasesOn(v_name_2944_, v_val_2937_, v___y_2876_, v___y_2877_, v___y_2878_, v___y_2879_);
if (lean_obj_tag(v___x_2952_) == 0)
{
lean_object* v_a_2953_; lean_object* v___x_2954_; 
v_a_2953_ = lean_ctor_get(v___x_2952_, 0);
lean_inc(v_a_2953_);
lean_dec_ref_known(v___x_2952_, 1);
lean_inc(v_majorFVarId_2871_);
v___x_2954_ = l_Lean_MVarId_induction(v_mvarId_2870_, v_majorFVarId_2871_, v_a_2953_, v_givenNames_2872_, v___y_2876_, v___y_2877_, v___y_2878_, v___y_2879_);
lean_dec(v___y_2879_);
lean_dec_ref(v___y_2878_);
lean_dec(v___y_2877_);
lean_dec_ref(v___y_2876_);
if (lean_obj_tag(v___x_2954_) == 0)
{
lean_object* v_a_2955_; lean_object* v___x_2957_; uint8_t v_isShared_2958_; uint8_t v_isSharedCheck_2963_; 
v_a_2955_ = lean_ctor_get(v___x_2954_, 0);
v_isSharedCheck_2963_ = !lean_is_exclusive(v___x_2954_);
if (v_isSharedCheck_2963_ == 0)
{
v___x_2957_ = v___x_2954_;
v_isShared_2958_ = v_isSharedCheck_2963_;
goto v_resetjp_2956_;
}
else
{
lean_inc(v_a_2955_);
lean_dec(v___x_2954_);
v___x_2957_ = lean_box(0);
v_isShared_2958_ = v_isSharedCheck_2963_;
goto v_resetjp_2956_;
}
v_resetjp_2956_:
{
lean_object* v___x_2959_; lean_object* v___x_2961_; 
v___x_2959_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals(v_a_2955_, v_val_2937_, v_majorFVarId_2871_, v_fst_2885_, v_snd_2886_);
lean_dec(v_snd_2886_);
lean_dec(v_val_2937_);
if (v_isShared_2958_ == 0)
{
lean_ctor_set(v___x_2957_, 0, v___x_2959_);
v___x_2961_ = v___x_2957_;
goto v_reusejp_2960_;
}
else
{
lean_object* v_reuseFailAlloc_2962_; 
v_reuseFailAlloc_2962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2962_, 0, v___x_2959_);
v___x_2961_ = v_reuseFailAlloc_2962_;
goto v_reusejp_2960_;
}
v_reusejp_2960_:
{
return v___x_2961_;
}
}
}
else
{
lean_object* v_a_2964_; lean_object* v___x_2966_; uint8_t v_isShared_2967_; uint8_t v_isSharedCheck_2971_; 
lean_dec(v_val_2937_);
lean_dec(v_snd_2886_);
lean_dec(v_fst_2885_);
lean_dec(v_majorFVarId_2871_);
v_a_2964_ = lean_ctor_get(v___x_2954_, 0);
v_isSharedCheck_2971_ = !lean_is_exclusive(v___x_2954_);
if (v_isSharedCheck_2971_ == 0)
{
v___x_2966_ = v___x_2954_;
v_isShared_2967_ = v_isSharedCheck_2971_;
goto v_resetjp_2965_;
}
else
{
lean_inc(v_a_2964_);
lean_dec(v___x_2954_);
v___x_2966_ = lean_box(0);
v_isShared_2967_ = v_isSharedCheck_2971_;
goto v_resetjp_2965_;
}
v_resetjp_2965_:
{
lean_object* v___x_2969_; 
if (v_isShared_2967_ == 0)
{
v___x_2969_ = v___x_2966_;
goto v_reusejp_2968_;
}
else
{
lean_object* v_reuseFailAlloc_2970_; 
v_reuseFailAlloc_2970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2970_, 0, v_a_2964_);
v___x_2969_ = v_reuseFailAlloc_2970_;
goto v_reusejp_2968_;
}
v_reusejp_2968_:
{
return v___x_2969_;
}
}
}
}
else
{
lean_object* v_a_2972_; lean_object* v___x_2974_; uint8_t v_isShared_2975_; uint8_t v_isSharedCheck_2979_; 
lean_dec(v_val_2937_);
lean_dec(v_snd_2886_);
lean_dec(v_fst_2885_);
lean_dec(v___y_2879_);
lean_dec_ref(v___y_2878_);
lean_dec(v___y_2877_);
lean_dec_ref(v___y_2876_);
lean_dec_ref(v_givenNames_2872_);
lean_dec(v_majorFVarId_2871_);
lean_dec(v_mvarId_2870_);
v_a_2972_ = lean_ctor_get(v___x_2952_, 0);
v_isSharedCheck_2979_ = !lean_is_exclusive(v___x_2952_);
if (v_isSharedCheck_2979_ == 0)
{
v___x_2974_ = v___x_2952_;
v_isShared_2975_ = v_isSharedCheck_2979_;
goto v_resetjp_2973_;
}
else
{
lean_inc(v_a_2972_);
lean_dec(v___x_2952_);
v___x_2974_ = lean_box(0);
v_isShared_2975_ = v_isSharedCheck_2979_;
goto v_resetjp_2973_;
}
v_resetjp_2973_:
{
lean_object* v___x_2977_; 
if (v_isShared_2975_ == 0)
{
v___x_2977_ = v___x_2974_;
goto v_reusejp_2976_;
}
else
{
lean_object* v_reuseFailAlloc_2978_; 
v_reuseFailAlloc_2978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2978_, 0, v_a_2972_);
v___x_2977_ = v_reuseFailAlloc_2978_;
goto v_reusejp_2976_;
}
v_reusejp_2976_:
{
return v___x_2977_;
}
}
}
}
}
else
{
lean_dec(v_val_2937_);
v___y_2924_ = v___y_2876_;
v___y_2925_ = v___y_2877_;
v___y_2926_ = v___y_2878_;
v___y_2927_ = v___y_2879_;
goto v___jp_2923_;
}
}
}
}
else
{
lean_dec(v_interestingCtors_x3f_2875_);
v___y_2924_ = v___y_2876_;
v___y_2925_ = v___y_2877_;
v___y_2926_ = v___y_2878_;
v___y_2927_ = v___y_2879_;
goto v___jp_2923_;
}
v___jp_2887_:
{
lean_object* v___x_2893_; 
lean_inc(v_majorFVarId_2871_);
v___x_2893_ = l_Lean_MVarId_induction(v_mvarId_2870_, v_majorFVarId_2871_, v___y_2892_, v_givenNames_2872_, v___y_2891_, v___y_2889_, v___y_2890_, v___y_2888_);
lean_dec(v___y_2888_);
lean_dec_ref(v___y_2890_);
lean_dec(v___y_2889_);
lean_dec_ref(v___y_2891_);
if (lean_obj_tag(v___x_2893_) == 0)
{
lean_object* v_inductiveVal_2894_; lean_object* v_a_2895_; lean_object* v___x_2897_; uint8_t v_isShared_2898_; uint8_t v_isSharedCheck_2905_; 
v_inductiveVal_2894_ = lean_ctor_get(v_ctx_2873_, 0);
lean_inc_ref(v_inductiveVal_2894_);
lean_dec_ref(v_ctx_2873_);
v_a_2895_ = lean_ctor_get(v___x_2893_, 0);
v_isSharedCheck_2905_ = !lean_is_exclusive(v___x_2893_);
if (v_isSharedCheck_2905_ == 0)
{
v___x_2897_ = v___x_2893_;
v_isShared_2898_ = v_isSharedCheck_2905_;
goto v_resetjp_2896_;
}
else
{
lean_inc(v_a_2895_);
lean_dec(v___x_2893_);
v___x_2897_ = lean_box(0);
v_isShared_2898_ = v_isSharedCheck_2905_;
goto v_resetjp_2896_;
}
v_resetjp_2896_:
{
lean_object* v_ctors_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2903_; 
v_ctors_2899_ = lean_ctor_get(v_inductiveVal_2894_, 4);
lean_inc(v_ctors_2899_);
lean_dec_ref(v_inductiveVal_2894_);
v___x_2900_ = lean_array_mk(v_ctors_2899_);
v___x_2901_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals(v_a_2895_, v___x_2900_, v_majorFVarId_2871_, v_fst_2885_, v_snd_2886_);
lean_dec(v_snd_2886_);
lean_dec_ref(v___x_2900_);
if (v_isShared_2898_ == 0)
{
lean_ctor_set(v___x_2897_, 0, v___x_2901_);
v___x_2903_ = v___x_2897_;
goto v_reusejp_2902_;
}
else
{
lean_object* v_reuseFailAlloc_2904_; 
v_reuseFailAlloc_2904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2904_, 0, v___x_2901_);
v___x_2903_ = v_reuseFailAlloc_2904_;
goto v_reusejp_2902_;
}
v_reusejp_2902_:
{
return v___x_2903_;
}
}
}
else
{
lean_object* v_a_2906_; lean_object* v___x_2908_; uint8_t v_isShared_2909_; uint8_t v_isSharedCheck_2913_; 
lean_dec(v_snd_2886_);
lean_dec(v_fst_2885_);
lean_dec_ref(v_ctx_2873_);
lean_dec(v_majorFVarId_2871_);
v_a_2906_ = lean_ctor_get(v___x_2893_, 0);
v_isSharedCheck_2913_ = !lean_is_exclusive(v___x_2893_);
if (v_isSharedCheck_2913_ == 0)
{
v___x_2908_ = v___x_2893_;
v_isShared_2909_ = v_isSharedCheck_2913_;
goto v_resetjp_2907_;
}
else
{
lean_inc(v_a_2906_);
lean_dec(v___x_2893_);
v___x_2908_ = lean_box(0);
v_isShared_2909_ = v_isSharedCheck_2913_;
goto v_resetjp_2907_;
}
v_resetjp_2907_:
{
lean_object* v___x_2911_; 
if (v_isShared_2909_ == 0)
{
v___x_2911_ = v___x_2908_;
goto v_reusejp_2910_;
}
else
{
lean_object* v_reuseFailAlloc_2912_; 
v_reuseFailAlloc_2912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2912_, 0, v_a_2906_);
v___x_2911_ = v_reuseFailAlloc_2912_;
goto v_reusejp_2910_;
}
v_reusejp_2910_:
{
return v___x_2911_;
}
}
}
}
v___jp_2914_:
{
lean_object* v_inductiveVal_2919_; lean_object* v_toConstantVal_2920_; lean_object* v_name_2921_; lean_object* v___x_2922_; 
v_inductiveVal_2919_ = lean_ctor_get(v_ctx_2873_, 0);
v_toConstantVal_2920_ = lean_ctor_get(v_inductiveVal_2919_, 0);
v_name_2921_ = lean_ctor_get(v_toConstantVal_2920_, 0);
lean_inc(v_name_2921_);
v___x_2922_ = l_Lean_mkCasesOnName(v_name_2921_);
v___y_2888_ = v___y_2915_;
v___y_2889_ = v___y_2916_;
v___y_2890_ = v___y_2917_;
v___y_2891_ = v___y_2918_;
v___y_2892_ = v___x_2922_;
goto v___jp_2887_;
}
v___jp_2923_:
{
lean_object* v___x_2928_; 
v___x_2928_ = lean_st_ref_get(v___y_2927_);
if (v_useNatCasesAuxOn_2874_ == 0)
{
lean_dec(v___x_2928_);
v___y_2915_ = v___y_2927_;
v___y_2916_ = v___y_2925_;
v___y_2917_ = v___y_2926_;
v___y_2918_ = v___y_2924_;
goto v___jp_2914_;
}
else
{
lean_object* v_inductiveVal_2929_; lean_object* v_toConstantVal_2930_; lean_object* v_env_2931_; lean_object* v_name_2932_; lean_object* v___x_2933_; uint8_t v___x_2934_; 
v_inductiveVal_2929_ = lean_ctor_get(v_ctx_2873_, 0);
v_toConstantVal_2930_ = lean_ctor_get(v_inductiveVal_2929_, 0);
v_env_2931_ = lean_ctor_get(v___x_2928_, 0);
lean_inc_ref(v_env_2931_);
lean_dec(v___x_2928_);
v_name_2932_ = lean_ctor_get(v_toConstantVal_2930_, 0);
v___x_2933_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__1));
v___x_2934_ = lean_name_eq(v_name_2932_, v___x_2933_);
if (v___x_2934_ == 0)
{
lean_dec_ref(v_env_2931_);
v___y_2915_ = v___y_2927_;
v___y_2916_ = v___y_2925_;
v___y_2917_ = v___y_2926_;
v___y_2918_ = v___y_2924_;
goto v___jp_2914_;
}
else
{
lean_object* v___x_2935_; uint8_t v___x_2936_; 
v___x_2935_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__3));
v___x_2936_ = l_Lean_Environment_contains(v_env_2931_, v___x_2935_, v___x_2934_);
if (v___x_2936_ == 0)
{
v___y_2915_ = v___y_2927_;
v___y_2916_ = v___y_2925_;
v___y_2917_ = v___y_2926_;
v___y_2918_ = v___y_2924_;
goto v___jp_2914_;
}
else
{
v___y_2888_ = v___y_2927_;
v___y_2889_ = v___y_2925_;
v___y_2890_ = v___y_2926_;
v___y_2891_ = v___y_2924_;
v___y_2892_ = v___x_2935_;
goto v___jp_2887_;
}
}
}
}
}
else
{
lean_object* v_a_2986_; lean_object* v___x_2988_; uint8_t v_isShared_2989_; uint8_t v_isSharedCheck_2993_; 
lean_dec(v___y_2879_);
lean_dec_ref(v___y_2878_);
lean_dec(v___y_2877_);
lean_dec_ref(v___y_2876_);
lean_dec(v_interestingCtors_x3f_2875_);
lean_dec_ref(v_ctx_2873_);
lean_dec_ref(v_givenNames_2872_);
lean_dec(v_majorFVarId_2871_);
lean_dec(v_mvarId_2870_);
v_a_2986_ = lean_ctor_get(v___x_2883_, 0);
v_isSharedCheck_2993_ = !lean_is_exclusive(v___x_2883_);
if (v_isSharedCheck_2993_ == 0)
{
v___x_2988_ = v___x_2883_;
v_isShared_2989_ = v_isSharedCheck_2993_;
goto v_resetjp_2987_;
}
else
{
lean_inc(v_a_2986_);
lean_dec(v___x_2883_);
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
lean_object* v_a_2994_; lean_object* v___x_2996_; uint8_t v_isShared_2997_; uint8_t v_isSharedCheck_3001_; 
lean_dec(v___y_2879_);
lean_dec_ref(v___y_2878_);
lean_dec(v___y_2877_);
lean_dec_ref(v___y_2876_);
lean_dec(v_interestingCtors_x3f_2875_);
lean_dec_ref(v_ctx_2873_);
lean_dec_ref(v_givenNames_2872_);
lean_dec(v_majorFVarId_2871_);
lean_dec(v_mvarId_2870_);
v_a_2994_ = lean_ctor_get(v___x_2881_, 0);
v_isSharedCheck_3001_ = !lean_is_exclusive(v___x_2881_);
if (v_isSharedCheck_3001_ == 0)
{
v___x_2996_ = v___x_2881_;
v_isShared_2997_ = v_isSharedCheck_3001_;
goto v_resetjp_2995_;
}
else
{
lean_inc(v_a_2994_);
lean_dec(v___x_2881_);
v___x_2996_ = lean_box(0);
v_isShared_2997_ = v_isSharedCheck_3001_;
goto v_resetjp_2995_;
}
v_resetjp_2995_:
{
lean_object* v___x_2999_; 
if (v_isShared_2997_ == 0)
{
v___x_2999_ = v___x_2996_;
goto v_reusejp_2998_;
}
else
{
lean_object* v_reuseFailAlloc_3000_; 
v_reuseFailAlloc_3000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3000_, 0, v_a_2994_);
v___x_2999_ = v_reuseFailAlloc_3000_;
goto v_reusejp_2998_;
}
v_reusejp_2998_:
{
return v___x_2999_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___boxed(lean_object* v___x_3002_, lean_object* v_mvarId_3003_, lean_object* v_majorFVarId_3004_, lean_object* v_givenNames_3005_, lean_object* v_ctx_3006_, lean_object* v_useNatCasesAuxOn_3007_, lean_object* v_interestingCtors_x3f_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_){
_start:
{
uint8_t v_useNatCasesAuxOn_boxed_3014_; lean_object* v_res_3015_; 
v_useNatCasesAuxOn_boxed_3014_ = lean_unbox(v_useNatCasesAuxOn_3007_);
v_res_3015_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0(v___x_3002_, v_mvarId_3003_, v_majorFVarId_3004_, v_givenNames_3005_, v_ctx_3006_, v_useNatCasesAuxOn_boxed_3014_, v_interestingCtors_x3f_3008_, v___y_3009_, v___y_3010_, v___y_3011_, v___y_3012_);
return v_res_3015_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn(lean_object* v_mvarId_3016_, lean_object* v_majorFVarId_3017_, lean_object* v_givenNames_3018_, lean_object* v_ctx_3019_, uint8_t v_useNatCasesAuxOn_3020_, lean_object* v_interestingCtors_x3f_3021_, lean_object* v_a_3022_, lean_object* v_a_3023_, lean_object* v_a_3024_, lean_object* v_a_3025_){
_start:
{
lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___f_3029_; lean_object* v___x_3030_; 
lean_inc(v_majorFVarId_3017_);
v___x_3027_ = l_Lean_mkFVar(v_majorFVarId_3017_);
v___x_3028_ = lean_box(v_useNatCasesAuxOn_3020_);
lean_inc(v_mvarId_3016_);
v___f_3029_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___boxed), 12, 7);
lean_closure_set(v___f_3029_, 0, v___x_3027_);
lean_closure_set(v___f_3029_, 1, v_mvarId_3016_);
lean_closure_set(v___f_3029_, 2, v_majorFVarId_3017_);
lean_closure_set(v___f_3029_, 3, v_givenNames_3018_);
lean_closure_set(v___f_3029_, 4, v_ctx_3019_);
lean_closure_set(v___f_3029_, 5, v___x_3028_);
lean_closure_set(v___f_3029_, 6, v_interestingCtors_x3f_3021_);
v___x_3030_ = l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2___redArg(v_mvarId_3016_, v___f_3029_, v_a_3022_, v_a_3023_, v_a_3024_, v_a_3025_);
return v___x_3030_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___boxed(lean_object* v_mvarId_3031_, lean_object* v_majorFVarId_3032_, lean_object* v_givenNames_3033_, lean_object* v_ctx_3034_, lean_object* v_useNatCasesAuxOn_3035_, lean_object* v_interestingCtors_x3f_3036_, lean_object* v_a_3037_, lean_object* v_a_3038_, lean_object* v_a_3039_, lean_object* v_a_3040_, lean_object* v_a_3041_){
_start:
{
uint8_t v_useNatCasesAuxOn_boxed_3042_; lean_object* v_res_3043_; 
v_useNatCasesAuxOn_boxed_3042_ = lean_unbox(v_useNatCasesAuxOn_3035_);
v_res_3043_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn(v_mvarId_3031_, v_majorFVarId_3032_, v_givenNames_3033_, v_ctx_3034_, v_useNatCasesAuxOn_boxed_3042_, v_interestingCtors_x3f_3036_, v_a_3037_, v_a_3038_, v_a_3039_, v_a_3040_);
lean_dec(v_a_3040_);
lean_dec_ref(v_a_3039_);
lean_dec(v_a_3038_);
lean_dec_ref(v_a_3037_);
return v_res_3043_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0___closed__0(void){
_start:
{
lean_object* v___x_3044_; double v___x_3045_; 
v___x_3044_ = lean_unsigned_to_nat(0u);
v___x_3045_ = lean_float_of_nat(v___x_3044_);
return v___x_3045_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0(lean_object* v_cls_3049_, lean_object* v_msg_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_){
_start:
{
lean_object* v_ref_3056_; lean_object* v___x_3057_; lean_object* v_a_3058_; lean_object* v___x_3060_; uint8_t v_isShared_3061_; uint8_t v_isSharedCheck_3102_; 
v_ref_3056_ = lean_ctor_get(v___y_3053_, 5);
v___x_3057_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected_spec__0_spec__0(v_msg_3050_, v___y_3051_, v___y_3052_, v___y_3053_, v___y_3054_);
v_a_3058_ = lean_ctor_get(v___x_3057_, 0);
v_isSharedCheck_3102_ = !lean_is_exclusive(v___x_3057_);
if (v_isSharedCheck_3102_ == 0)
{
v___x_3060_ = v___x_3057_;
v_isShared_3061_ = v_isSharedCheck_3102_;
goto v_resetjp_3059_;
}
else
{
lean_inc(v_a_3058_);
lean_dec(v___x_3057_);
v___x_3060_ = lean_box(0);
v_isShared_3061_ = v_isSharedCheck_3102_;
goto v_resetjp_3059_;
}
v_resetjp_3059_:
{
lean_object* v___x_3062_; lean_object* v_traceState_3063_; lean_object* v_env_3064_; lean_object* v_nextMacroScope_3065_; lean_object* v_ngen_3066_; lean_object* v_auxDeclNGen_3067_; lean_object* v_cache_3068_; lean_object* v_messages_3069_; lean_object* v_infoState_3070_; lean_object* v_snapshotTasks_3071_; lean_object* v___x_3073_; uint8_t v_isShared_3074_; uint8_t v_isSharedCheck_3101_; 
v___x_3062_ = lean_st_ref_take(v___y_3054_);
v_traceState_3063_ = lean_ctor_get(v___x_3062_, 4);
v_env_3064_ = lean_ctor_get(v___x_3062_, 0);
v_nextMacroScope_3065_ = lean_ctor_get(v___x_3062_, 1);
v_ngen_3066_ = lean_ctor_get(v___x_3062_, 2);
v_auxDeclNGen_3067_ = lean_ctor_get(v___x_3062_, 3);
v_cache_3068_ = lean_ctor_get(v___x_3062_, 5);
v_messages_3069_ = lean_ctor_get(v___x_3062_, 6);
v_infoState_3070_ = lean_ctor_get(v___x_3062_, 7);
v_snapshotTasks_3071_ = lean_ctor_get(v___x_3062_, 8);
v_isSharedCheck_3101_ = !lean_is_exclusive(v___x_3062_);
if (v_isSharedCheck_3101_ == 0)
{
v___x_3073_ = v___x_3062_;
v_isShared_3074_ = v_isSharedCheck_3101_;
goto v_resetjp_3072_;
}
else
{
lean_inc(v_snapshotTasks_3071_);
lean_inc(v_infoState_3070_);
lean_inc(v_messages_3069_);
lean_inc(v_cache_3068_);
lean_inc(v_traceState_3063_);
lean_inc(v_auxDeclNGen_3067_);
lean_inc(v_ngen_3066_);
lean_inc(v_nextMacroScope_3065_);
lean_inc(v_env_3064_);
lean_dec(v___x_3062_);
v___x_3073_ = lean_box(0);
v_isShared_3074_ = v_isSharedCheck_3101_;
goto v_resetjp_3072_;
}
v_resetjp_3072_:
{
uint64_t v_tid_3075_; lean_object* v_traces_3076_; lean_object* v___x_3078_; uint8_t v_isShared_3079_; uint8_t v_isSharedCheck_3100_; 
v_tid_3075_ = lean_ctor_get_uint64(v_traceState_3063_, sizeof(void*)*1);
v_traces_3076_ = lean_ctor_get(v_traceState_3063_, 0);
v_isSharedCheck_3100_ = !lean_is_exclusive(v_traceState_3063_);
if (v_isSharedCheck_3100_ == 0)
{
v___x_3078_ = v_traceState_3063_;
v_isShared_3079_ = v_isSharedCheck_3100_;
goto v_resetjp_3077_;
}
else
{
lean_inc(v_traces_3076_);
lean_dec(v_traceState_3063_);
v___x_3078_ = lean_box(0);
v_isShared_3079_ = v_isSharedCheck_3100_;
goto v_resetjp_3077_;
}
v_resetjp_3077_:
{
lean_object* v___x_3080_; double v___x_3081_; uint8_t v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3090_; 
v___x_3080_ = lean_box(0);
v___x_3081_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0___closed__0);
v___x_3082_ = 0;
v___x_3083_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0___closed__1));
v___x_3084_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3084_, 0, v_cls_3049_);
lean_ctor_set(v___x_3084_, 1, v___x_3080_);
lean_ctor_set(v___x_3084_, 2, v___x_3083_);
lean_ctor_set_float(v___x_3084_, sizeof(void*)*3, v___x_3081_);
lean_ctor_set_float(v___x_3084_, sizeof(void*)*3 + 8, v___x_3081_);
lean_ctor_set_uint8(v___x_3084_, sizeof(void*)*3 + 16, v___x_3082_);
v___x_3085_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0___closed__2));
v___x_3086_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3086_, 0, v___x_3084_);
lean_ctor_set(v___x_3086_, 1, v_a_3058_);
lean_ctor_set(v___x_3086_, 2, v___x_3085_);
lean_inc(v_ref_3056_);
v___x_3087_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3087_, 0, v_ref_3056_);
lean_ctor_set(v___x_3087_, 1, v___x_3086_);
v___x_3088_ = l_Lean_PersistentArray_push___redArg(v_traces_3076_, v___x_3087_);
if (v_isShared_3079_ == 0)
{
lean_ctor_set(v___x_3078_, 0, v___x_3088_);
v___x_3090_ = v___x_3078_;
goto v_reusejp_3089_;
}
else
{
lean_object* v_reuseFailAlloc_3099_; 
v_reuseFailAlloc_3099_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3099_, 0, v___x_3088_);
lean_ctor_set_uint64(v_reuseFailAlloc_3099_, sizeof(void*)*1, v_tid_3075_);
v___x_3090_ = v_reuseFailAlloc_3099_;
goto v_reusejp_3089_;
}
v_reusejp_3089_:
{
lean_object* v___x_3092_; 
if (v_isShared_3074_ == 0)
{
lean_ctor_set(v___x_3073_, 4, v___x_3090_);
v___x_3092_ = v___x_3073_;
goto v_reusejp_3091_;
}
else
{
lean_object* v_reuseFailAlloc_3098_; 
v_reuseFailAlloc_3098_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3098_, 0, v_env_3064_);
lean_ctor_set(v_reuseFailAlloc_3098_, 1, v_nextMacroScope_3065_);
lean_ctor_set(v_reuseFailAlloc_3098_, 2, v_ngen_3066_);
lean_ctor_set(v_reuseFailAlloc_3098_, 3, v_auxDeclNGen_3067_);
lean_ctor_set(v_reuseFailAlloc_3098_, 4, v___x_3090_);
lean_ctor_set(v_reuseFailAlloc_3098_, 5, v_cache_3068_);
lean_ctor_set(v_reuseFailAlloc_3098_, 6, v_messages_3069_);
lean_ctor_set(v_reuseFailAlloc_3098_, 7, v_infoState_3070_);
lean_ctor_set(v_reuseFailAlloc_3098_, 8, v_snapshotTasks_3071_);
v___x_3092_ = v_reuseFailAlloc_3098_;
goto v_reusejp_3091_;
}
v_reusejp_3091_:
{
lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3096_; 
v___x_3093_ = lean_st_ref_put(v___y_3054_, v___x_3092_);
v___x_3094_ = lean_box(0);
if (v_isShared_3061_ == 0)
{
lean_ctor_set(v___x_3060_, 0, v___x_3094_);
v___x_3096_ = v___x_3060_;
goto v_reusejp_3095_;
}
else
{
lean_object* v_reuseFailAlloc_3097_; 
v_reuseFailAlloc_3097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3097_, 0, v___x_3094_);
v___x_3096_ = v_reuseFailAlloc_3097_;
goto v_reusejp_3095_;
}
v_reusejp_3095_:
{
return v___x_3096_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0___boxed(lean_object* v_cls_3103_, lean_object* v_msg_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_){
_start:
{
lean_object* v_res_3110_; 
v_res_3110_ = l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0(v_cls_3103_, v_msg_3104_, v___y_3105_, v___y_3106_, v___y_3107_, v___y_3108_);
lean_dec(v___y_3108_);
lean_dec_ref(v___y_3107_);
lean_dec(v___y_3106_);
lean_dec_ref(v___y_3105_);
return v_res_3110_;
}
}
static lean_object* _init_l_Lean_Meta_Cases_cases___lam__0___closed__2(void){
_start:
{
lean_object* v___x_3114_; lean_object* v___x_3115_; 
v___x_3114_ = ((lean_object*)(l_Lean_Meta_Cases_cases___lam__0___closed__1));
v___x_3115_ = l_Lean_MessageData_ofFormat(v___x_3114_);
return v___x_3115_;
}
}
static lean_object* _init_l_Lean_Meta_Cases_cases___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3116_; lean_object* v___x_3117_; 
v___x_3116_ = lean_obj_once(&l_Lean_Meta_Cases_cases___lam__0___closed__2, &l_Lean_Meta_Cases_cases___lam__0___closed__2_once, _init_l_Lean_Meta_Cases_cases___lam__0___closed__2);
v___x_3117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3117_, 0, v___x_3116_);
return v___x_3117_;
}
}
static lean_object* _init_l_Lean_Meta_Cases_cases___lam__0___closed__9(void){
_start:
{
lean_object* v___x_3124_; lean_object* v___x_3125_; 
v___x_3124_ = ((lean_object*)(l_Lean_Meta_Cases_cases___lam__0___closed__8));
v___x_3125_ = l_Lean_stringToMessageData(v___x_3124_);
return v___x_3125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_cases___lam__0(lean_object* v_mvarId_3126_, lean_object* v___x_3127_, lean_object* v_majorFVarId_3128_, lean_object* v_givenNames_3129_, lean_object* v_interestingCtors_x3f_3130_, lean_object* v___x_3131_, uint8_t v_useNatCasesAuxOn_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_){
_start:
{
lean_object* v___x_3138_; 
lean_inc(v___x_3127_);
lean_inc(v_mvarId_3126_);
v___x_3138_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_3126_, v___x_3127_, v___y_3133_, v___y_3134_, v___y_3135_, v___y_3136_);
if (lean_obj_tag(v___x_3138_) == 0)
{
lean_object* v___x_3139_; 
lean_dec_ref_known(v___x_3138_, 1);
lean_inc(v_majorFVarId_3128_);
v___x_3139_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f(v_majorFVarId_3128_, v___y_3133_, v___y_3134_, v___y_3135_, v___y_3136_);
if (lean_obj_tag(v___x_3139_) == 0)
{
lean_object* v_a_3140_; 
v_a_3140_ = lean_ctor_get(v___x_3139_, 0);
lean_inc(v_a_3140_);
lean_dec_ref_known(v___x_3139_, 1);
if (lean_obj_tag(v_a_3140_) == 0)
{
lean_object* v___x_3141_; lean_object* v___x_3142_; 
lean_dec_ref(v___x_3131_);
lean_dec(v_interestingCtors_x3f_3130_);
lean_dec_ref(v_givenNames_3129_);
lean_dec(v_majorFVarId_3128_);
v___x_3141_ = lean_obj_once(&l_Lean_Meta_Cases_cases___lam__0___closed__3, &l_Lean_Meta_Cases_cases___lam__0___closed__3_once, _init_l_Lean_Meta_Cases_cases___lam__0___closed__3);
v___x_3142_ = l_Lean_Meta_throwTacticEx___redArg(v___x_3127_, v_mvarId_3126_, v___x_3141_, v___y_3133_, v___y_3134_, v___y_3135_, v___y_3136_);
return v___x_3142_;
}
else
{
lean_object* v_val_3143_; lean_object* v___x_3145_; uint8_t v_isShared_3146_; uint8_t v_isSharedCheck_3207_; 
lean_dec(v___x_3127_);
v_val_3143_ = lean_ctor_get(v_a_3140_, 0);
v_isSharedCheck_3207_ = !lean_is_exclusive(v_a_3140_);
if (v_isSharedCheck_3207_ == 0)
{
v___x_3145_ = v_a_3140_;
v_isShared_3146_ = v_isSharedCheck_3207_;
goto v_resetjp_3144_;
}
else
{
lean_inc(v_val_3143_);
lean_dec(v_a_3140_);
v___x_3145_ = lean_box(0);
v_isShared_3146_ = v_isSharedCheck_3207_;
goto v_resetjp_3144_;
}
v_resetjp_3144_:
{
lean_object* v___x_3147_; 
lean_inc(v_val_3143_);
v___x_3147_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices(v_val_3143_, v___y_3133_, v___y_3134_, v___y_3135_, v___y_3136_);
if (lean_obj_tag(v___x_3147_) == 0)
{
lean_object* v_a_3148_; uint8_t v___x_3149_; 
v_a_3148_ = lean_ctor_get(v___x_3147_, 0);
lean_inc(v_a_3148_);
lean_dec_ref_known(v___x_3147_, 1);
v___x_3149_ = lean_unbox(v_a_3148_);
if (v___x_3149_ == 0)
{
lean_object* v___x_3150_; 
v___x_3150_ = l_Lean_Meta_generalizeIndices(v_mvarId_3126_, v_majorFVarId_3128_, v___y_3133_, v___y_3134_, v___y_3135_, v___y_3136_);
if (lean_obj_tag(v___x_3150_) == 0)
{
lean_object* v_a_3151_; lean_object* v___y_3153_; lean_object* v___y_3154_; lean_object* v___y_3155_; lean_object* v___y_3156_; lean_object* v_options_3166_; uint8_t v_hasTrace_3167_; 
v_a_3151_ = lean_ctor_get(v___x_3150_, 0);
lean_inc(v_a_3151_);
lean_dec_ref_known(v___x_3150_, 1);
v_options_3166_ = lean_ctor_get(v___y_3135_, 2);
v_hasTrace_3167_ = lean_ctor_get_uint8(v_options_3166_, sizeof(void*)*1);
if (v_hasTrace_3167_ == 0)
{
lean_del_object(v___x_3145_);
lean_dec_ref(v___x_3131_);
v___y_3153_ = v___y_3133_;
v___y_3154_ = v___y_3134_;
v___y_3155_ = v___y_3135_;
v___y_3156_ = v___y_3136_;
goto v___jp_3152_;
}
else
{
lean_object* v_inheritedTraceOptions_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; uint8_t v___x_3174_; 
v_inheritedTraceOptions_3168_ = lean_ctor_get(v___y_3135_, 13);
v___x_3169_ = ((lean_object*)(l_Lean_Meta_Cases_cases___lam__0___closed__4));
v___x_3170_ = ((lean_object*)(l_Lean_Meta_Cases_cases___lam__0___closed__5));
v___x_3171_ = l_Lean_Name_mkStr3(v___x_3169_, v___x_3170_, v___x_3131_);
v___x_3172_ = ((lean_object*)(l_Lean_Meta_Cases_cases___lam__0___closed__7));
lean_inc(v___x_3171_);
v___x_3173_ = l_Lean_Name_append(v___x_3172_, v___x_3171_);
v___x_3174_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3168_, v_options_3166_, v___x_3173_);
lean_dec(v___x_3173_);
if (v___x_3174_ == 0)
{
lean_dec(v___x_3171_);
lean_del_object(v___x_3145_);
v___y_3153_ = v___y_3133_;
v___y_3154_ = v___y_3134_;
v___y_3155_ = v___y_3135_;
v___y_3156_ = v___y_3136_;
goto v___jp_3152_;
}
else
{
lean_object* v_mvarId_3175_; lean_object* v___x_3176_; lean_object* v___x_3178_; 
v_mvarId_3175_ = lean_ctor_get(v_a_3151_, 0);
v___x_3176_ = lean_obj_once(&l_Lean_Meta_Cases_cases___lam__0___closed__9, &l_Lean_Meta_Cases_cases___lam__0___closed__9_once, _init_l_Lean_Meta_Cases_cases___lam__0___closed__9);
lean_inc(v_mvarId_3175_);
if (v_isShared_3146_ == 0)
{
lean_ctor_set(v___x_3145_, 0, v_mvarId_3175_);
v___x_3178_ = v___x_3145_;
goto v_reusejp_3177_;
}
else
{
lean_object* v_reuseFailAlloc_3189_; 
v_reuseFailAlloc_3189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3189_, 0, v_mvarId_3175_);
v___x_3178_ = v_reuseFailAlloc_3189_;
goto v_reusejp_3177_;
}
v_reusejp_3177_:
{
lean_object* v___x_3179_; lean_object* v___x_3180_; 
v___x_3179_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3179_, 0, v___x_3176_);
lean_ctor_set(v___x_3179_, 1, v___x_3178_);
v___x_3180_ = l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0(v___x_3171_, v___x_3179_, v___y_3133_, v___y_3134_, v___y_3135_, v___y_3136_);
if (lean_obj_tag(v___x_3180_) == 0)
{
lean_dec_ref_known(v___x_3180_, 1);
v___y_3153_ = v___y_3133_;
v___y_3154_ = v___y_3134_;
v___y_3155_ = v___y_3135_;
v___y_3156_ = v___y_3136_;
goto v___jp_3152_;
}
else
{
lean_object* v_a_3181_; lean_object* v___x_3183_; uint8_t v_isShared_3184_; uint8_t v_isSharedCheck_3188_; 
lean_dec(v_a_3151_);
lean_dec(v_a_3148_);
lean_dec(v_val_3143_);
lean_dec(v_interestingCtors_x3f_3130_);
lean_dec_ref(v_givenNames_3129_);
v_a_3181_ = lean_ctor_get(v___x_3180_, 0);
v_isSharedCheck_3188_ = !lean_is_exclusive(v___x_3180_);
if (v_isSharedCheck_3188_ == 0)
{
v___x_3183_ = v___x_3180_;
v_isShared_3184_ = v_isSharedCheck_3188_;
goto v_resetjp_3182_;
}
else
{
lean_inc(v_a_3181_);
lean_dec(v___x_3180_);
v___x_3183_ = lean_box(0);
v_isShared_3184_ = v_isSharedCheck_3188_;
goto v_resetjp_3182_;
}
v_resetjp_3182_:
{
lean_object* v___x_3186_; 
if (v_isShared_3184_ == 0)
{
v___x_3186_ = v___x_3183_;
goto v_reusejp_3185_;
}
else
{
lean_object* v_reuseFailAlloc_3187_; 
v_reuseFailAlloc_3187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3187_, 0, v_a_3181_);
v___x_3186_ = v_reuseFailAlloc_3187_;
goto v_reusejp_3185_;
}
v_reusejp_3185_:
{
return v___x_3186_;
}
}
}
}
}
}
v___jp_3152_:
{
lean_object* v_mvarId_3157_; lean_object* v_fvarId_3158_; lean_object* v_numEqs_3159_; uint8_t v___x_3160_; lean_object* v___x_3161_; 
v_mvarId_3157_ = lean_ctor_get(v_a_3151_, 0);
v_fvarId_3158_ = lean_ctor_get(v_a_3151_, 2);
v_numEqs_3159_ = lean_ctor_get(v_a_3151_, 3);
lean_inc(v_numEqs_3159_);
v___x_3160_ = lean_unbox(v_a_3148_);
lean_dec(v_a_3148_);
lean_inc(v_fvarId_3158_);
lean_inc(v_mvarId_3157_);
v___x_3161_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn(v_mvarId_3157_, v_fvarId_3158_, v_givenNames_3129_, v_val_3143_, v___x_3160_, v_interestingCtors_x3f_3130_, v___y_3153_, v___y_3154_, v___y_3155_, v___y_3156_);
if (lean_obj_tag(v___x_3161_) == 0)
{
lean_object* v_a_3162_; lean_object* v___x_3163_; 
v_a_3162_ = lean_ctor_get(v___x_3161_, 0);
lean_inc(v_a_3162_);
lean_dec_ref_known(v___x_3161_, 1);
v___x_3163_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices(v_a_3151_, v_a_3162_, v___y_3153_, v___y_3154_, v___y_3155_, v___y_3156_);
lean_dec(v_a_3151_);
if (lean_obj_tag(v___x_3163_) == 0)
{
lean_object* v_a_3164_; lean_object* v___x_3165_; 
v_a_3164_ = lean_ctor_get(v___x_3163_, 0);
lean_inc(v_a_3164_);
lean_dec_ref_known(v___x_3163_, 1);
v___x_3165_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs(v_numEqs_3159_, v_a_3164_, v___y_3153_, v___y_3154_, v___y_3155_, v___y_3156_);
lean_dec(v_a_3164_);
return v___x_3165_;
}
else
{
lean_dec(v_numEqs_3159_);
return v___x_3163_;
}
}
else
{
lean_dec(v_numEqs_3159_);
lean_dec(v_a_3151_);
return v___x_3161_;
}
}
}
else
{
lean_object* v_a_3190_; lean_object* v___x_3192_; uint8_t v_isShared_3193_; uint8_t v_isSharedCheck_3197_; 
lean_dec(v_a_3148_);
lean_del_object(v___x_3145_);
lean_dec(v_val_3143_);
lean_dec_ref(v___x_3131_);
lean_dec(v_interestingCtors_x3f_3130_);
lean_dec_ref(v_givenNames_3129_);
v_a_3190_ = lean_ctor_get(v___x_3150_, 0);
v_isSharedCheck_3197_ = !lean_is_exclusive(v___x_3150_);
if (v_isSharedCheck_3197_ == 0)
{
v___x_3192_ = v___x_3150_;
v_isShared_3193_ = v_isSharedCheck_3197_;
goto v_resetjp_3191_;
}
else
{
lean_inc(v_a_3190_);
lean_dec(v___x_3150_);
v___x_3192_ = lean_box(0);
v_isShared_3193_ = v_isSharedCheck_3197_;
goto v_resetjp_3191_;
}
v_resetjp_3191_:
{
lean_object* v___x_3195_; 
if (v_isShared_3193_ == 0)
{
v___x_3195_ = v___x_3192_;
goto v_reusejp_3194_;
}
else
{
lean_object* v_reuseFailAlloc_3196_; 
v_reuseFailAlloc_3196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3196_, 0, v_a_3190_);
v___x_3195_ = v_reuseFailAlloc_3196_;
goto v_reusejp_3194_;
}
v_reusejp_3194_:
{
return v___x_3195_;
}
}
}
}
else
{
lean_object* v___x_3198_; 
lean_dec(v_a_3148_);
lean_del_object(v___x_3145_);
lean_dec_ref(v___x_3131_);
v___x_3198_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn(v_mvarId_3126_, v_majorFVarId_3128_, v_givenNames_3129_, v_val_3143_, v_useNatCasesAuxOn_3132_, v_interestingCtors_x3f_3130_, v___y_3133_, v___y_3134_, v___y_3135_, v___y_3136_);
return v___x_3198_;
}
}
else
{
lean_object* v_a_3199_; lean_object* v___x_3201_; uint8_t v_isShared_3202_; uint8_t v_isSharedCheck_3206_; 
lean_del_object(v___x_3145_);
lean_dec(v_val_3143_);
lean_dec_ref(v___x_3131_);
lean_dec(v_interestingCtors_x3f_3130_);
lean_dec_ref(v_givenNames_3129_);
lean_dec(v_majorFVarId_3128_);
lean_dec(v_mvarId_3126_);
v_a_3199_ = lean_ctor_get(v___x_3147_, 0);
v_isSharedCheck_3206_ = !lean_is_exclusive(v___x_3147_);
if (v_isSharedCheck_3206_ == 0)
{
v___x_3201_ = v___x_3147_;
v_isShared_3202_ = v_isSharedCheck_3206_;
goto v_resetjp_3200_;
}
else
{
lean_inc(v_a_3199_);
lean_dec(v___x_3147_);
v___x_3201_ = lean_box(0);
v_isShared_3202_ = v_isSharedCheck_3206_;
goto v_resetjp_3200_;
}
v_resetjp_3200_:
{
lean_object* v___x_3204_; 
if (v_isShared_3202_ == 0)
{
v___x_3204_ = v___x_3201_;
goto v_reusejp_3203_;
}
else
{
lean_object* v_reuseFailAlloc_3205_; 
v_reuseFailAlloc_3205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3205_, 0, v_a_3199_);
v___x_3204_ = v_reuseFailAlloc_3205_;
goto v_reusejp_3203_;
}
v_reusejp_3203_:
{
return v___x_3204_;
}
}
}
}
}
}
else
{
lean_object* v_a_3208_; lean_object* v___x_3210_; uint8_t v_isShared_3211_; uint8_t v_isSharedCheck_3215_; 
lean_dec_ref(v___x_3131_);
lean_dec(v_interestingCtors_x3f_3130_);
lean_dec_ref(v_givenNames_3129_);
lean_dec(v_majorFVarId_3128_);
lean_dec(v___x_3127_);
lean_dec(v_mvarId_3126_);
v_a_3208_ = lean_ctor_get(v___x_3139_, 0);
v_isSharedCheck_3215_ = !lean_is_exclusive(v___x_3139_);
if (v_isSharedCheck_3215_ == 0)
{
v___x_3210_ = v___x_3139_;
v_isShared_3211_ = v_isSharedCheck_3215_;
goto v_resetjp_3209_;
}
else
{
lean_inc(v_a_3208_);
lean_dec(v___x_3139_);
v___x_3210_ = lean_box(0);
v_isShared_3211_ = v_isSharedCheck_3215_;
goto v_resetjp_3209_;
}
v_resetjp_3209_:
{
lean_object* v___x_3213_; 
if (v_isShared_3211_ == 0)
{
v___x_3213_ = v___x_3210_;
goto v_reusejp_3212_;
}
else
{
lean_object* v_reuseFailAlloc_3214_; 
v_reuseFailAlloc_3214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3214_, 0, v_a_3208_);
v___x_3213_ = v_reuseFailAlloc_3214_;
goto v_reusejp_3212_;
}
v_reusejp_3212_:
{
return v___x_3213_;
}
}
}
}
else
{
lean_object* v_a_3216_; lean_object* v___x_3218_; uint8_t v_isShared_3219_; uint8_t v_isSharedCheck_3223_; 
lean_dec_ref(v___x_3131_);
lean_dec(v_interestingCtors_x3f_3130_);
lean_dec_ref(v_givenNames_3129_);
lean_dec(v_majorFVarId_3128_);
lean_dec(v___x_3127_);
lean_dec(v_mvarId_3126_);
v_a_3216_ = lean_ctor_get(v___x_3138_, 0);
v_isSharedCheck_3223_ = !lean_is_exclusive(v___x_3138_);
if (v_isSharedCheck_3223_ == 0)
{
v___x_3218_ = v___x_3138_;
v_isShared_3219_ = v_isSharedCheck_3223_;
goto v_resetjp_3217_;
}
else
{
lean_inc(v_a_3216_);
lean_dec(v___x_3138_);
v___x_3218_ = lean_box(0);
v_isShared_3219_ = v_isSharedCheck_3223_;
goto v_resetjp_3217_;
}
v_resetjp_3217_:
{
lean_object* v___x_3221_; 
if (v_isShared_3219_ == 0)
{
v___x_3221_ = v___x_3218_;
goto v_reusejp_3220_;
}
else
{
lean_object* v_reuseFailAlloc_3222_; 
v_reuseFailAlloc_3222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3222_, 0, v_a_3216_);
v___x_3221_ = v_reuseFailAlloc_3222_;
goto v_reusejp_3220_;
}
v_reusejp_3220_:
{
return v___x_3221_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_cases___lam__0___boxed(lean_object* v_mvarId_3224_, lean_object* v___x_3225_, lean_object* v_majorFVarId_3226_, lean_object* v_givenNames_3227_, lean_object* v_interestingCtors_x3f_3228_, lean_object* v___x_3229_, lean_object* v_useNatCasesAuxOn_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_){
_start:
{
uint8_t v_useNatCasesAuxOn_boxed_3236_; lean_object* v_res_3237_; 
v_useNatCasesAuxOn_boxed_3236_ = lean_unbox(v_useNatCasesAuxOn_3230_);
v_res_3237_ = l_Lean_Meta_Cases_cases___lam__0(v_mvarId_3224_, v___x_3225_, v_majorFVarId_3226_, v_givenNames_3227_, v_interestingCtors_x3f_3228_, v___x_3229_, v_useNatCasesAuxOn_boxed_3236_, v___y_3231_, v___y_3232_, v___y_3233_, v___y_3234_);
lean_dec(v___y_3234_);
lean_dec_ref(v___y_3233_);
lean_dec(v___y_3232_);
lean_dec_ref(v___y_3231_);
return v_res_3237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_cases(lean_object* v_mvarId_3241_, lean_object* v_majorFVarId_3242_, lean_object* v_givenNames_3243_, uint8_t v_useNatCasesAuxOn_3244_, lean_object* v_interestingCtors_x3f_3245_, lean_object* v_a_3246_, lean_object* v_a_3247_, lean_object* v_a_3248_, lean_object* v_a_3249_){
_start:
{
lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___f_3254_; lean_object* v___x_3255_; 
v___x_3251_ = ((lean_object*)(l_Lean_Meta_Cases_cases___closed__0));
v___x_3252_ = ((lean_object*)(l_Lean_Meta_Cases_cases___closed__1));
v___x_3253_ = lean_box(v_useNatCasesAuxOn_3244_);
lean_inc(v_mvarId_3241_);
v___f_3254_ = lean_alloc_closure((void*)(l_Lean_Meta_Cases_cases___lam__0___boxed), 12, 7);
lean_closure_set(v___f_3254_, 0, v_mvarId_3241_);
lean_closure_set(v___f_3254_, 1, v___x_3252_);
lean_closure_set(v___f_3254_, 2, v_majorFVarId_3242_);
lean_closure_set(v___f_3254_, 3, v_givenNames_3243_);
lean_closure_set(v___f_3254_, 4, v_interestingCtors_x3f_3245_);
lean_closure_set(v___f_3254_, 5, v___x_3251_);
lean_closure_set(v___f_3254_, 6, v___x_3253_);
v___x_3255_ = l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2___redArg(v_mvarId_3241_, v___f_3254_, v_a_3246_, v_a_3247_, v_a_3248_, v_a_3249_);
if (lean_obj_tag(v___x_3255_) == 0)
{
return v___x_3255_;
}
else
{
lean_object* v_a_3256_; uint8_t v___y_3258_; uint8_t v___x_3260_; 
v_a_3256_ = lean_ctor_get(v___x_3255_, 0);
lean_inc(v_a_3256_);
v___x_3260_ = l_Lean_Exception_isInterrupt(v_a_3256_);
if (v___x_3260_ == 0)
{
uint8_t v___x_3261_; 
lean_inc(v_a_3256_);
v___x_3261_ = l_Lean_Exception_isRuntime(v_a_3256_);
v___y_3258_ = v___x_3261_;
goto v___jp_3257_;
}
else
{
v___y_3258_ = v___x_3260_;
goto v___jp_3257_;
}
v___jp_3257_:
{
if (v___y_3258_ == 0)
{
lean_object* v___x_3259_; 
lean_dec_ref_known(v___x_3255_, 1);
v___x_3259_ = l_Lean_Meta_throwNestedTacticEx___redArg(v___x_3252_, v_a_3256_, v_a_3246_, v_a_3247_, v_a_3248_, v_a_3249_);
return v___x_3259_;
}
else
{
lean_dec(v_a_3256_);
return v___x_3255_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_cases___boxed(lean_object* v_mvarId_3262_, lean_object* v_majorFVarId_3263_, lean_object* v_givenNames_3264_, lean_object* v_useNatCasesAuxOn_3265_, lean_object* v_interestingCtors_x3f_3266_, lean_object* v_a_3267_, lean_object* v_a_3268_, lean_object* v_a_3269_, lean_object* v_a_3270_, lean_object* v_a_3271_){
_start:
{
uint8_t v_useNatCasesAuxOn_boxed_3272_; lean_object* v_res_3273_; 
v_useNatCasesAuxOn_boxed_3272_ = lean_unbox(v_useNatCasesAuxOn_3265_);
v_res_3273_ = l_Lean_Meta_Cases_cases(v_mvarId_3262_, v_majorFVarId_3263_, v_givenNames_3264_, v_useNatCasesAuxOn_boxed_3272_, v_interestingCtors_x3f_3266_, v_a_3267_, v_a_3268_, v_a_3269_, v_a_3270_);
lean_dec(v_a_3270_);
lean_dec_ref(v_a_3269_);
lean_dec(v_a_3268_);
lean_dec_ref(v_a_3267_);
return v_res_3273_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_cases(lean_object* v_mvarId_3274_, lean_object* v_majorFVarId_3275_, lean_object* v_givenNames_3276_, uint8_t v_useNatCasesAuxOn_3277_, lean_object* v_interestingCtors_x3f_3278_, lean_object* v_a_3279_, lean_object* v_a_3280_, lean_object* v_a_3281_, lean_object* v_a_3282_){
_start:
{
lean_object* v___x_3284_; 
v___x_3284_ = l_Lean_Meta_Cases_cases(v_mvarId_3274_, v_majorFVarId_3275_, v_givenNames_3276_, v_useNatCasesAuxOn_3277_, v_interestingCtors_x3f_3278_, v_a_3279_, v_a_3280_, v_a_3281_, v_a_3282_);
return v___x_3284_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_cases___boxed(lean_object* v_mvarId_3285_, lean_object* v_majorFVarId_3286_, lean_object* v_givenNames_3287_, lean_object* v_useNatCasesAuxOn_3288_, lean_object* v_interestingCtors_x3f_3289_, lean_object* v_a_3290_, lean_object* v_a_3291_, lean_object* v_a_3292_, lean_object* v_a_3293_, lean_object* v_a_3294_){
_start:
{
uint8_t v_useNatCasesAuxOn_boxed_3295_; lean_object* v_res_3296_; 
v_useNatCasesAuxOn_boxed_3295_ = lean_unbox(v_useNatCasesAuxOn_3288_);
v_res_3296_ = l_Lean_MVarId_cases(v_mvarId_3285_, v_majorFVarId_3286_, v_givenNames_3287_, v_useNatCasesAuxOn_boxed_3295_, v_interestingCtors_x3f_3289_, v_a_3290_, v_a_3291_, v_a_3292_, v_a_3293_);
lean_dec(v_a_3293_);
lean_dec_ref(v_a_3292_);
lean_dec(v_a_3291_);
lean_dec_ref(v_a_3290_);
return v_res_3296_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1___redArg(lean_object* v_x_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_){
_start:
{
lean_object* v___x_3303_; 
v___x_3303_ = l_Lean_Meta_saveState___redArg(v___y_3299_, v___y_3301_);
if (lean_obj_tag(v___x_3303_) == 0)
{
lean_object* v_a_3304_; lean_object* v___x_3305_; 
v_a_3304_ = lean_ctor_get(v___x_3303_, 0);
lean_inc(v_a_3304_);
lean_dec_ref_known(v___x_3303_, 1);
lean_inc(v___y_3301_);
lean_inc_ref(v___y_3300_);
lean_inc(v___y_3299_);
lean_inc_ref(v___y_3298_);
v___x_3305_ = lean_apply_5(v_x_3297_, v___y_3298_, v___y_3299_, v___y_3300_, v___y_3301_, lean_box(0));
if (lean_obj_tag(v___x_3305_) == 0)
{
lean_object* v_a_3306_; lean_object* v___x_3308_; uint8_t v_isShared_3309_; uint8_t v_isSharedCheck_3314_; 
lean_dec(v_a_3304_);
v_a_3306_ = lean_ctor_get(v___x_3305_, 0);
v_isSharedCheck_3314_ = !lean_is_exclusive(v___x_3305_);
if (v_isSharedCheck_3314_ == 0)
{
v___x_3308_ = v___x_3305_;
v_isShared_3309_ = v_isSharedCheck_3314_;
goto v_resetjp_3307_;
}
else
{
lean_inc(v_a_3306_);
lean_dec(v___x_3305_);
v___x_3308_ = lean_box(0);
v_isShared_3309_ = v_isSharedCheck_3314_;
goto v_resetjp_3307_;
}
v_resetjp_3307_:
{
lean_object* v___x_3310_; lean_object* v___x_3312_; 
v___x_3310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3310_, 0, v_a_3306_);
if (v_isShared_3309_ == 0)
{
lean_ctor_set(v___x_3308_, 0, v___x_3310_);
v___x_3312_ = v___x_3308_;
goto v_reusejp_3311_;
}
else
{
lean_object* v_reuseFailAlloc_3313_; 
v_reuseFailAlloc_3313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3313_, 0, v___x_3310_);
v___x_3312_ = v_reuseFailAlloc_3313_;
goto v_reusejp_3311_;
}
v_reusejp_3311_:
{
return v___x_3312_;
}
}
}
else
{
lean_object* v_a_3315_; lean_object* v___x_3317_; uint8_t v_isShared_3318_; uint8_t v_isSharedCheck_3344_; 
v_a_3315_ = lean_ctor_get(v___x_3305_, 0);
v_isSharedCheck_3344_ = !lean_is_exclusive(v___x_3305_);
if (v_isSharedCheck_3344_ == 0)
{
v___x_3317_ = v___x_3305_;
v_isShared_3318_ = v_isSharedCheck_3344_;
goto v_resetjp_3316_;
}
else
{
lean_inc(v_a_3315_);
lean_dec(v___x_3305_);
v___x_3317_ = lean_box(0);
v_isShared_3318_ = v_isSharedCheck_3344_;
goto v_resetjp_3316_;
}
v_resetjp_3316_:
{
uint8_t v___y_3320_; uint8_t v___x_3342_; 
v___x_3342_ = l_Lean_Exception_isInterrupt(v_a_3315_);
if (v___x_3342_ == 0)
{
uint8_t v___x_3343_; 
lean_inc(v_a_3315_);
v___x_3343_ = l_Lean_Exception_isRuntime(v_a_3315_);
v___y_3320_ = v___x_3343_;
goto v___jp_3319_;
}
else
{
v___y_3320_ = v___x_3342_;
goto v___jp_3319_;
}
v___jp_3319_:
{
if (v___y_3320_ == 0)
{
lean_object* v___x_3321_; 
lean_del_object(v___x_3317_);
lean_dec(v_a_3315_);
v___x_3321_ = l_Lean_Meta_SavedState_restore___redArg(v_a_3304_, v___y_3299_, v___y_3301_);
lean_dec(v_a_3304_);
if (lean_obj_tag(v___x_3321_) == 0)
{
lean_object* v___x_3323_; uint8_t v_isShared_3324_; uint8_t v_isSharedCheck_3329_; 
v_isSharedCheck_3329_ = !lean_is_exclusive(v___x_3321_);
if (v_isSharedCheck_3329_ == 0)
{
lean_object* v_unused_3330_; 
v_unused_3330_ = lean_ctor_get(v___x_3321_, 0);
lean_dec(v_unused_3330_);
v___x_3323_ = v___x_3321_;
v_isShared_3324_ = v_isSharedCheck_3329_;
goto v_resetjp_3322_;
}
else
{
lean_dec(v___x_3321_);
v___x_3323_ = lean_box(0);
v_isShared_3324_ = v_isSharedCheck_3329_;
goto v_resetjp_3322_;
}
v_resetjp_3322_:
{
lean_object* v___x_3325_; lean_object* v___x_3327_; 
v___x_3325_ = lean_box(0);
if (v_isShared_3324_ == 0)
{
lean_ctor_set(v___x_3323_, 0, v___x_3325_);
v___x_3327_ = v___x_3323_;
goto v_reusejp_3326_;
}
else
{
lean_object* v_reuseFailAlloc_3328_; 
v_reuseFailAlloc_3328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3328_, 0, v___x_3325_);
v___x_3327_ = v_reuseFailAlloc_3328_;
goto v_reusejp_3326_;
}
v_reusejp_3326_:
{
return v___x_3327_;
}
}
}
else
{
lean_object* v_a_3331_; lean_object* v___x_3333_; uint8_t v_isShared_3334_; uint8_t v_isSharedCheck_3338_; 
v_a_3331_ = lean_ctor_get(v___x_3321_, 0);
v_isSharedCheck_3338_ = !lean_is_exclusive(v___x_3321_);
if (v_isSharedCheck_3338_ == 0)
{
v___x_3333_ = v___x_3321_;
v_isShared_3334_ = v_isSharedCheck_3338_;
goto v_resetjp_3332_;
}
else
{
lean_inc(v_a_3331_);
lean_dec(v___x_3321_);
v___x_3333_ = lean_box(0);
v_isShared_3334_ = v_isSharedCheck_3338_;
goto v_resetjp_3332_;
}
v_resetjp_3332_:
{
lean_object* v___x_3336_; 
if (v_isShared_3334_ == 0)
{
v___x_3336_ = v___x_3333_;
goto v_reusejp_3335_;
}
else
{
lean_object* v_reuseFailAlloc_3337_; 
v_reuseFailAlloc_3337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3337_, 0, v_a_3331_);
v___x_3336_ = v_reuseFailAlloc_3337_;
goto v_reusejp_3335_;
}
v_reusejp_3335_:
{
return v___x_3336_;
}
}
}
}
else
{
lean_object* v___x_3340_; 
lean_dec(v_a_3304_);
if (v_isShared_3318_ == 0)
{
v___x_3340_ = v___x_3317_;
goto v_reusejp_3339_;
}
else
{
lean_object* v_reuseFailAlloc_3341_; 
v_reuseFailAlloc_3341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3341_, 0, v_a_3315_);
v___x_3340_ = v_reuseFailAlloc_3341_;
goto v_reusejp_3339_;
}
v_reusejp_3339_:
{
return v___x_3340_;
}
}
}
}
}
}
else
{
lean_object* v_a_3345_; lean_object* v___x_3347_; uint8_t v_isShared_3348_; uint8_t v_isSharedCheck_3352_; 
lean_dec_ref(v_x_3297_);
v_a_3345_ = lean_ctor_get(v___x_3303_, 0);
v_isSharedCheck_3352_ = !lean_is_exclusive(v___x_3303_);
if (v_isSharedCheck_3352_ == 0)
{
v___x_3347_ = v___x_3303_;
v_isShared_3348_ = v_isSharedCheck_3352_;
goto v_resetjp_3346_;
}
else
{
lean_inc(v_a_3345_);
lean_dec(v___x_3303_);
v___x_3347_ = lean_box(0);
v_isShared_3348_ = v_isSharedCheck_3352_;
goto v_resetjp_3346_;
}
v_resetjp_3346_:
{
lean_object* v___x_3350_; 
if (v_isShared_3348_ == 0)
{
v___x_3350_ = v___x_3347_;
goto v_reusejp_3349_;
}
else
{
lean_object* v_reuseFailAlloc_3351_; 
v_reuseFailAlloc_3351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3351_, 0, v_a_3345_);
v___x_3350_ = v_reuseFailAlloc_3351_;
goto v_reusejp_3349_;
}
v_reusejp_3349_:
{
return v___x_3350_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1___redArg___boxed(lean_object* v_x_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_){
_start:
{
lean_object* v_res_3359_; 
v_res_3359_ = l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1___redArg(v_x_3353_, v___y_3354_, v___y_3355_, v___y_3356_, v___y_3357_);
lean_dec(v___y_3357_);
lean_dec_ref(v___y_3356_);
lean_dec(v___y_3355_);
lean_dec_ref(v___y_3354_);
return v_res_3359_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1(lean_object* v_00_u03b1_3360_, lean_object* v_x_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_){
_start:
{
lean_object* v___x_3367_; 
v___x_3367_ = l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1___redArg(v_x_3361_, v___y_3362_, v___y_3363_, v___y_3364_, v___y_3365_);
return v___x_3367_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1___boxed(lean_object* v_00_u03b1_3368_, lean_object* v_x_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_){
_start:
{
lean_object* v_res_3375_; 
v_res_3375_ = l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1(v_00_u03b1_3368_, v_x_3369_, v___y_3370_, v___y_3371_, v___y_3372_, v___y_3373_);
lean_dec(v___y_3373_);
lean_dec_ref(v___y_3372_);
lean_dec(v___y_3371_);
lean_dec_ref(v___y_3370_);
return v_res_3375_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_MVarId_casesRec_spec__0(lean_object* v_a_3376_, lean_object* v_a_3377_){
_start:
{
if (lean_obj_tag(v_a_3376_) == 0)
{
lean_object* v___x_3378_; 
v___x_3378_ = l_List_reverse___redArg(v_a_3377_);
return v___x_3378_;
}
else
{
lean_object* v_head_3379_; lean_object* v_toInductionSubgoal_3380_; lean_object* v_tail_3381_; lean_object* v___x_3383_; uint8_t v_isShared_3384_; uint8_t v_isSharedCheck_3390_; 
v_head_3379_ = lean_ctor_get(v_a_3376_, 0);
v_toInductionSubgoal_3380_ = lean_ctor_get(v_head_3379_, 0);
lean_inc_ref(v_toInductionSubgoal_3380_);
v_tail_3381_ = lean_ctor_get(v_a_3376_, 1);
v_isSharedCheck_3390_ = !lean_is_exclusive(v_a_3376_);
if (v_isSharedCheck_3390_ == 0)
{
lean_object* v_unused_3391_; 
v_unused_3391_ = lean_ctor_get(v_a_3376_, 0);
lean_dec(v_unused_3391_);
v___x_3383_ = v_a_3376_;
v_isShared_3384_ = v_isSharedCheck_3390_;
goto v_resetjp_3382_;
}
else
{
lean_inc(v_tail_3381_);
lean_dec(v_a_3376_);
v___x_3383_ = lean_box(0);
v_isShared_3384_ = v_isSharedCheck_3390_;
goto v_resetjp_3382_;
}
v_resetjp_3382_:
{
lean_object* v_mvarId_3385_; lean_object* v___x_3387_; 
v_mvarId_3385_ = lean_ctor_get(v_toInductionSubgoal_3380_, 0);
lean_inc(v_mvarId_3385_);
lean_dec_ref(v_toInductionSubgoal_3380_);
if (v_isShared_3384_ == 0)
{
lean_ctor_set(v___x_3383_, 1, v_a_3377_);
lean_ctor_set(v___x_3383_, 0, v_mvarId_3385_);
v___x_3387_ = v___x_3383_;
goto v_reusejp_3386_;
}
else
{
lean_object* v_reuseFailAlloc_3389_; 
v_reuseFailAlloc_3389_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3389_, 0, v_mvarId_3385_);
lean_ctor_set(v_reuseFailAlloc_3389_, 1, v_a_3377_);
v___x_3387_ = v_reuseFailAlloc_3389_;
goto v_reusejp_3386_;
}
v_reusejp_3386_:
{
v_a_3376_ = v_tail_3381_;
v_a_3377_ = v___x_3387_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3___lam__0(lean_object* v_mvarId_3392_, lean_object* v___x_3393_, lean_object* v___x_3394_, uint8_t v___x_3395_, lean_object* v___x_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_){
_start:
{
lean_object* v___x_3402_; 
v___x_3402_ = l_Lean_Meta_Cases_cases(v_mvarId_3392_, v___x_3393_, v___x_3394_, v___x_3395_, v___x_3396_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_);
if (lean_obj_tag(v___x_3402_) == 0)
{
lean_object* v_a_3403_; lean_object* v___x_3405_; uint8_t v_isShared_3406_; uint8_t v_isSharedCheck_3413_; 
v_a_3403_ = lean_ctor_get(v___x_3402_, 0);
v_isSharedCheck_3413_ = !lean_is_exclusive(v___x_3402_);
if (v_isSharedCheck_3413_ == 0)
{
v___x_3405_ = v___x_3402_;
v_isShared_3406_ = v_isSharedCheck_3413_;
goto v_resetjp_3404_;
}
else
{
lean_inc(v_a_3403_);
lean_dec(v___x_3402_);
v___x_3405_ = lean_box(0);
v_isShared_3406_ = v_isSharedCheck_3413_;
goto v_resetjp_3404_;
}
v_resetjp_3404_:
{
lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3411_; 
v___x_3407_ = lean_array_to_list(v_a_3403_);
v___x_3408_ = lean_box(0);
v___x_3409_ = l_List_mapTR_loop___at___00Lean_MVarId_casesRec_spec__0(v___x_3407_, v___x_3408_);
if (v_isShared_3406_ == 0)
{
lean_ctor_set(v___x_3405_, 0, v___x_3409_);
v___x_3411_ = v___x_3405_;
goto v_reusejp_3410_;
}
else
{
lean_object* v_reuseFailAlloc_3412_; 
v_reuseFailAlloc_3412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3412_, 0, v___x_3409_);
v___x_3411_ = v_reuseFailAlloc_3412_;
goto v_reusejp_3410_;
}
v_reusejp_3410_:
{
return v___x_3411_;
}
}
}
else
{
lean_object* v_a_3414_; lean_object* v___x_3416_; uint8_t v_isShared_3417_; uint8_t v_isSharedCheck_3421_; 
v_a_3414_ = lean_ctor_get(v___x_3402_, 0);
v_isSharedCheck_3421_ = !lean_is_exclusive(v___x_3402_);
if (v_isSharedCheck_3421_ == 0)
{
v___x_3416_ = v___x_3402_;
v_isShared_3417_ = v_isSharedCheck_3421_;
goto v_resetjp_3415_;
}
else
{
lean_inc(v_a_3414_);
lean_dec(v___x_3402_);
v___x_3416_ = lean_box(0);
v_isShared_3417_ = v_isSharedCheck_3421_;
goto v_resetjp_3415_;
}
v_resetjp_3415_:
{
lean_object* v___x_3419_; 
if (v_isShared_3417_ == 0)
{
v___x_3419_ = v___x_3416_;
goto v_reusejp_3418_;
}
else
{
lean_object* v_reuseFailAlloc_3420_; 
v_reuseFailAlloc_3420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3420_, 0, v_a_3414_);
v___x_3419_ = v_reuseFailAlloc_3420_;
goto v_reusejp_3418_;
}
v_reusejp_3418_:
{
return v___x_3419_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3___lam__0___boxed(lean_object* v_mvarId_3422_, lean_object* v___x_3423_, lean_object* v___x_3424_, lean_object* v___x_3425_, lean_object* v___x_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_){
_start:
{
uint8_t v___x_6516__boxed_3432_; lean_object* v_res_3433_; 
v___x_6516__boxed_3432_ = lean_unbox(v___x_3425_);
v_res_3433_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3___lam__0(v_mvarId_3422_, v___x_3423_, v___x_3424_, v___x_6516__boxed_3432_, v___x_3426_, v___y_3427_, v___y_3428_, v___y_3429_, v___y_3430_);
lean_dec(v___y_3430_);
lean_dec_ref(v___y_3429_);
lean_dec(v___y_3428_);
lean_dec_ref(v___y_3427_);
return v_res_3433_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5(lean_object* v_p_3439_, lean_object* v_mvarId_3440_, lean_object* v_as_3441_, size_t v_sz_3442_, size_t v_i_3443_, lean_object* v_b_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_){
_start:
{
uint8_t v___x_3450_; 
v___x_3450_ = lean_usize_dec_lt(v_i_3443_, v_sz_3442_);
if (v___x_3450_ == 0)
{
lean_object* v___x_3451_; 
lean_dec(v_mvarId_3440_);
lean_dec_ref(v_p_3439_);
v___x_3451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3451_, 0, v_b_3444_);
return v___x_3451_;
}
else
{
lean_object* v_snd_3452_; lean_object* v___x_3454_; uint8_t v_isShared_3455_; uint8_t v_isSharedCheck_3520_; 
v_snd_3452_ = lean_ctor_get(v_b_3444_, 1);
v_isSharedCheck_3520_ = !lean_is_exclusive(v_b_3444_);
if (v_isSharedCheck_3520_ == 0)
{
lean_object* v_unused_3521_; 
v_unused_3521_ = lean_ctor_get(v_b_3444_, 0);
lean_dec(v_unused_3521_);
v___x_3454_ = v_b_3444_;
v_isShared_3455_ = v_isSharedCheck_3520_;
goto v_resetjp_3453_;
}
else
{
lean_inc(v_snd_3452_);
lean_dec(v_b_3444_);
v___x_3454_ = lean_box(0);
v_isShared_3455_ = v_isSharedCheck_3520_;
goto v_resetjp_3453_;
}
v_resetjp_3453_:
{
lean_object* v___x_3456_; lean_object* v_a_3458_; lean_object* v_a_3465_; 
v___x_3456_ = lean_box(0);
v_a_3465_ = lean_array_uget(v_as_3441_, v_i_3443_);
if (lean_obj_tag(v_a_3465_) == 0)
{
v_a_3458_ = v_snd_3452_;
goto v___jp_3457_;
}
else
{
lean_object* v_val_3466_; lean_object* v___x_3468_; uint8_t v_isShared_3469_; uint8_t v_isSharedCheck_3519_; 
v_val_3466_ = lean_ctor_get(v_a_3465_, 0);
v_isSharedCheck_3519_ = !lean_is_exclusive(v_a_3465_);
if (v_isSharedCheck_3519_ == 0)
{
v___x_3468_ = v_a_3465_;
v_isShared_3469_ = v_isSharedCheck_3519_;
goto v_resetjp_3467_;
}
else
{
lean_inc(v_val_3466_);
lean_dec(v_a_3465_);
v___x_3468_ = lean_box(0);
v_isShared_3469_ = v_isSharedCheck_3519_;
goto v_resetjp_3467_;
}
v_resetjp_3467_:
{
lean_object* v___x_3470_; 
lean_inc_ref(v_p_3439_);
lean_inc(v___y_3448_);
lean_inc_ref(v___y_3447_);
lean_inc(v___y_3446_);
lean_inc_ref(v___y_3445_);
lean_inc(v_val_3466_);
v___x_3470_ = lean_apply_6(v_p_3439_, v_val_3466_, v___y_3445_, v___y_3446_, v___y_3447_, v___y_3448_, lean_box(0));
if (lean_obj_tag(v___x_3470_) == 0)
{
lean_object* v_a_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; uint8_t v___x_3474_; 
v_a_3471_ = lean_ctor_get(v___x_3470_, 0);
lean_inc(v_a_3471_);
lean_dec_ref_known(v___x_3470_, 1);
v___x_3472_ = lean_box(0);
v___x_3473_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5___closed__0));
v___x_3474_ = lean_unbox(v_a_3471_);
lean_dec(v_a_3471_);
if (v___x_3474_ == 0)
{
lean_del_object(v___x_3468_);
lean_dec(v_val_3466_);
lean_dec(v_snd_3452_);
v_a_3458_ = v___x_3473_;
goto v___jp_3457_;
}
else
{
lean_object* v___x_3475_; lean_object* v___x_3476_; uint8_t v___x_3477_; lean_object* v___x_3478_; lean_object* v___f_3479_; lean_object* v___x_3480_; 
v___x_3475_ = l_Lean_LocalDecl_fvarId(v_val_3466_);
lean_dec(v_val_3466_);
v___x_3476_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5___closed__1));
v___x_3477_ = 0;
v___x_3478_ = lean_box(v___x_3477_);
lean_inc(v_mvarId_3440_);
v___f_3479_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3___lam__0___boxed), 10, 5);
lean_closure_set(v___f_3479_, 0, v_mvarId_3440_);
lean_closure_set(v___f_3479_, 1, v___x_3475_);
lean_closure_set(v___f_3479_, 2, v___x_3476_);
lean_closure_set(v___f_3479_, 3, v___x_3478_);
lean_closure_set(v___f_3479_, 4, v___x_3456_);
v___x_3480_ = l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1___redArg(v___f_3479_, v___y_3445_, v___y_3446_, v___y_3447_, v___y_3448_);
if (lean_obj_tag(v___x_3480_) == 0)
{
lean_object* v_a_3481_; lean_object* v___x_3483_; uint8_t v_isShared_3484_; uint8_t v_isSharedCheck_3502_; 
v_a_3481_ = lean_ctor_get(v___x_3480_, 0);
v_isSharedCheck_3502_ = !lean_is_exclusive(v___x_3480_);
if (v_isSharedCheck_3502_ == 0)
{
v___x_3483_ = v___x_3480_;
v_isShared_3484_ = v_isSharedCheck_3502_;
goto v_resetjp_3482_;
}
else
{
lean_inc(v_a_3481_);
lean_dec(v___x_3480_);
v___x_3483_ = lean_box(0);
v_isShared_3484_ = v_isSharedCheck_3502_;
goto v_resetjp_3482_;
}
v_resetjp_3482_:
{
if (lean_obj_tag(v_a_3481_) == 0)
{
lean_del_object(v___x_3483_);
lean_del_object(v___x_3468_);
lean_dec(v_snd_3452_);
v_a_3458_ = v___x_3473_;
goto v___jp_3457_;
}
else
{
lean_object* v___x_3486_; 
lean_del_object(v___x_3454_);
lean_dec(v_mvarId_3440_);
lean_dec_ref(v_p_3439_);
lean_inc_ref(v_a_3481_);
if (v_isShared_3469_ == 0)
{
lean_ctor_set(v___x_3468_, 0, v_a_3481_);
v___x_3486_ = v___x_3468_;
goto v_reusejp_3485_;
}
else
{
lean_object* v_reuseFailAlloc_3501_; 
v_reuseFailAlloc_3501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3501_, 0, v_a_3481_);
v___x_3486_ = v_reuseFailAlloc_3501_;
goto v_reusejp_3485_;
}
v_reusejp_3485_:
{
lean_object* v___x_3488_; uint8_t v_isShared_3489_; uint8_t v_isSharedCheck_3499_; 
v_isSharedCheck_3499_ = !lean_is_exclusive(v_a_3481_);
if (v_isSharedCheck_3499_ == 0)
{
lean_object* v_unused_3500_; 
v_unused_3500_ = lean_ctor_get(v_a_3481_, 0);
lean_dec(v_unused_3500_);
v___x_3488_ = v_a_3481_;
v_isShared_3489_ = v_isSharedCheck_3499_;
goto v_resetjp_3487_;
}
else
{
lean_dec(v_a_3481_);
v___x_3488_ = lean_box(0);
v_isShared_3489_ = v_isSharedCheck_3499_;
goto v_resetjp_3487_;
}
v_resetjp_3487_:
{
lean_object* v___x_3490_; lean_object* v___x_3492_; 
v___x_3490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3490_, 0, v___x_3486_);
lean_ctor_set(v___x_3490_, 1, v___x_3472_);
if (v_isShared_3489_ == 0)
{
lean_ctor_set_tag(v___x_3488_, 0);
lean_ctor_set(v___x_3488_, 0, v___x_3490_);
v___x_3492_ = v___x_3488_;
goto v_reusejp_3491_;
}
else
{
lean_object* v_reuseFailAlloc_3498_; 
v_reuseFailAlloc_3498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3498_, 0, v___x_3490_);
v___x_3492_ = v_reuseFailAlloc_3498_;
goto v_reusejp_3491_;
}
v_reusejp_3491_:
{
lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3496_; 
v___x_3493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3493_, 0, v___x_3492_);
v___x_3494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3494_, 0, v___x_3493_);
lean_ctor_set(v___x_3494_, 1, v_snd_3452_);
if (v_isShared_3484_ == 0)
{
lean_ctor_set(v___x_3483_, 0, v___x_3494_);
v___x_3496_ = v___x_3483_;
goto v_reusejp_3495_;
}
else
{
lean_object* v_reuseFailAlloc_3497_; 
v_reuseFailAlloc_3497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3497_, 0, v___x_3494_);
v___x_3496_ = v_reuseFailAlloc_3497_;
goto v_reusejp_3495_;
}
v_reusejp_3495_:
{
return v___x_3496_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3503_; lean_object* v___x_3505_; uint8_t v_isShared_3506_; uint8_t v_isSharedCheck_3510_; 
lean_del_object(v___x_3468_);
lean_del_object(v___x_3454_);
lean_dec(v_snd_3452_);
lean_dec(v_mvarId_3440_);
lean_dec_ref(v_p_3439_);
v_a_3503_ = lean_ctor_get(v___x_3480_, 0);
v_isSharedCheck_3510_ = !lean_is_exclusive(v___x_3480_);
if (v_isSharedCheck_3510_ == 0)
{
v___x_3505_ = v___x_3480_;
v_isShared_3506_ = v_isSharedCheck_3510_;
goto v_resetjp_3504_;
}
else
{
lean_inc(v_a_3503_);
lean_dec(v___x_3480_);
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
else
{
lean_object* v_a_3511_; lean_object* v___x_3513_; uint8_t v_isShared_3514_; uint8_t v_isSharedCheck_3518_; 
lean_del_object(v___x_3468_);
lean_dec(v_val_3466_);
lean_del_object(v___x_3454_);
lean_dec(v_snd_3452_);
lean_dec(v_mvarId_3440_);
lean_dec_ref(v_p_3439_);
v_a_3511_ = lean_ctor_get(v___x_3470_, 0);
v_isSharedCheck_3518_ = !lean_is_exclusive(v___x_3470_);
if (v_isSharedCheck_3518_ == 0)
{
v___x_3513_ = v___x_3470_;
v_isShared_3514_ = v_isSharedCheck_3518_;
goto v_resetjp_3512_;
}
else
{
lean_inc(v_a_3511_);
lean_dec(v___x_3470_);
v___x_3513_ = lean_box(0);
v_isShared_3514_ = v_isSharedCheck_3518_;
goto v_resetjp_3512_;
}
v_resetjp_3512_:
{
lean_object* v___x_3516_; 
if (v_isShared_3514_ == 0)
{
v___x_3516_ = v___x_3513_;
goto v_reusejp_3515_;
}
else
{
lean_object* v_reuseFailAlloc_3517_; 
v_reuseFailAlloc_3517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3517_, 0, v_a_3511_);
v___x_3516_ = v_reuseFailAlloc_3517_;
goto v_reusejp_3515_;
}
v_reusejp_3515_:
{
return v___x_3516_;
}
}
}
}
}
v___jp_3457_:
{
lean_object* v___x_3460_; 
if (v_isShared_3455_ == 0)
{
lean_ctor_set(v___x_3454_, 1, v_a_3458_);
lean_ctor_set(v___x_3454_, 0, v___x_3456_);
v___x_3460_ = v___x_3454_;
goto v_reusejp_3459_;
}
else
{
lean_object* v_reuseFailAlloc_3464_; 
v_reuseFailAlloc_3464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3464_, 0, v___x_3456_);
lean_ctor_set(v_reuseFailAlloc_3464_, 1, v_a_3458_);
v___x_3460_ = v_reuseFailAlloc_3464_;
goto v_reusejp_3459_;
}
v_reusejp_3459_:
{
size_t v___x_3461_; size_t v___x_3462_; 
v___x_3461_ = ((size_t)1ULL);
v___x_3462_ = lean_usize_add(v_i_3443_, v___x_3461_);
v_i_3443_ = v___x_3462_;
v_b_3444_ = v___x_3460_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5___boxed(lean_object* v_p_3522_, lean_object* v_mvarId_3523_, lean_object* v_as_3524_, lean_object* v_sz_3525_, lean_object* v_i_3526_, lean_object* v_b_3527_, lean_object* v___y_3528_, lean_object* v___y_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_){
_start:
{
size_t v_sz_boxed_3533_; size_t v_i_boxed_3534_; lean_object* v_res_3535_; 
v_sz_boxed_3533_ = lean_unbox_usize(v_sz_3525_);
lean_dec(v_sz_3525_);
v_i_boxed_3534_ = lean_unbox_usize(v_i_3526_);
lean_dec(v_i_3526_);
v_res_3535_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5(v_p_3522_, v_mvarId_3523_, v_as_3524_, v_sz_boxed_3533_, v_i_boxed_3534_, v_b_3527_, v___y_3528_, v___y_3529_, v___y_3530_, v___y_3531_);
lean_dec(v___y_3531_);
lean_dec_ref(v___y_3530_);
lean_dec(v___y_3529_);
lean_dec_ref(v___y_3528_);
lean_dec_ref(v_as_3524_);
return v_res_3535_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4(lean_object* v_p_3536_, lean_object* v_mvarId_3537_, lean_object* v_as_3538_, size_t v_sz_3539_, size_t v_i_3540_, lean_object* v_b_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_){
_start:
{
uint8_t v___x_3547_; 
v___x_3547_ = lean_usize_dec_lt(v_i_3540_, v_sz_3539_);
if (v___x_3547_ == 0)
{
lean_object* v___x_3548_; 
lean_dec(v_mvarId_3537_);
lean_dec_ref(v_p_3536_);
v___x_3548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3548_, 0, v_b_3541_);
return v___x_3548_;
}
else
{
lean_object* v_snd_3549_; lean_object* v___x_3551_; uint8_t v_isShared_3552_; uint8_t v_isSharedCheck_3617_; 
v_snd_3549_ = lean_ctor_get(v_b_3541_, 1);
v_isSharedCheck_3617_ = !lean_is_exclusive(v_b_3541_);
if (v_isSharedCheck_3617_ == 0)
{
lean_object* v_unused_3618_; 
v_unused_3618_ = lean_ctor_get(v_b_3541_, 0);
lean_dec(v_unused_3618_);
v___x_3551_ = v_b_3541_;
v_isShared_3552_ = v_isSharedCheck_3617_;
goto v_resetjp_3550_;
}
else
{
lean_inc(v_snd_3549_);
lean_dec(v_b_3541_);
v___x_3551_ = lean_box(0);
v_isShared_3552_ = v_isSharedCheck_3617_;
goto v_resetjp_3550_;
}
v_resetjp_3550_:
{
lean_object* v___x_3553_; lean_object* v_a_3555_; lean_object* v_a_3562_; 
v___x_3553_ = lean_box(0);
v_a_3562_ = lean_array_uget(v_as_3538_, v_i_3540_);
if (lean_obj_tag(v_a_3562_) == 0)
{
v_a_3555_ = v_snd_3549_;
goto v___jp_3554_;
}
else
{
lean_object* v_val_3563_; lean_object* v___x_3565_; uint8_t v_isShared_3566_; uint8_t v_isSharedCheck_3616_; 
v_val_3563_ = lean_ctor_get(v_a_3562_, 0);
v_isSharedCheck_3616_ = !lean_is_exclusive(v_a_3562_);
if (v_isSharedCheck_3616_ == 0)
{
v___x_3565_ = v_a_3562_;
v_isShared_3566_ = v_isSharedCheck_3616_;
goto v_resetjp_3564_;
}
else
{
lean_inc(v_val_3563_);
lean_dec(v_a_3562_);
v___x_3565_ = lean_box(0);
v_isShared_3566_ = v_isSharedCheck_3616_;
goto v_resetjp_3564_;
}
v_resetjp_3564_:
{
lean_object* v___x_3567_; 
lean_inc_ref(v_p_3536_);
lean_inc(v___y_3545_);
lean_inc_ref(v___y_3544_);
lean_inc(v___y_3543_);
lean_inc_ref(v___y_3542_);
lean_inc(v_val_3563_);
v___x_3567_ = lean_apply_6(v_p_3536_, v_val_3563_, v___y_3542_, v___y_3543_, v___y_3544_, v___y_3545_, lean_box(0));
if (lean_obj_tag(v___x_3567_) == 0)
{
lean_object* v_a_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; uint8_t v___x_3571_; 
v_a_3568_ = lean_ctor_get(v___x_3567_, 0);
lean_inc(v_a_3568_);
lean_dec_ref_known(v___x_3567_, 1);
v___x_3569_ = lean_box(0);
v___x_3570_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5___closed__0));
v___x_3571_ = lean_unbox(v_a_3568_);
lean_dec(v_a_3568_);
if (v___x_3571_ == 0)
{
lean_del_object(v___x_3565_);
lean_dec(v_val_3563_);
lean_dec(v_snd_3549_);
v_a_3555_ = v___x_3570_;
goto v___jp_3554_;
}
else
{
lean_object* v___x_3572_; lean_object* v___x_3573_; uint8_t v___x_3574_; lean_object* v___x_3575_; lean_object* v___f_3576_; lean_object* v___x_3577_; 
v___x_3572_ = l_Lean_LocalDecl_fvarId(v_val_3563_);
lean_dec(v_val_3563_);
v___x_3573_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5___closed__1));
v___x_3574_ = 0;
v___x_3575_ = lean_box(v___x_3574_);
lean_inc(v_mvarId_3537_);
v___f_3576_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3___lam__0___boxed), 10, 5);
lean_closure_set(v___f_3576_, 0, v_mvarId_3537_);
lean_closure_set(v___f_3576_, 1, v___x_3572_);
lean_closure_set(v___f_3576_, 2, v___x_3573_);
lean_closure_set(v___f_3576_, 3, v___x_3575_);
lean_closure_set(v___f_3576_, 4, v___x_3553_);
v___x_3577_ = l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1___redArg(v___f_3576_, v___y_3542_, v___y_3543_, v___y_3544_, v___y_3545_);
if (lean_obj_tag(v___x_3577_) == 0)
{
lean_object* v_a_3578_; lean_object* v___x_3580_; uint8_t v_isShared_3581_; uint8_t v_isSharedCheck_3599_; 
v_a_3578_ = lean_ctor_get(v___x_3577_, 0);
v_isSharedCheck_3599_ = !lean_is_exclusive(v___x_3577_);
if (v_isSharedCheck_3599_ == 0)
{
v___x_3580_ = v___x_3577_;
v_isShared_3581_ = v_isSharedCheck_3599_;
goto v_resetjp_3579_;
}
else
{
lean_inc(v_a_3578_);
lean_dec(v___x_3577_);
v___x_3580_ = lean_box(0);
v_isShared_3581_ = v_isSharedCheck_3599_;
goto v_resetjp_3579_;
}
v_resetjp_3579_:
{
if (lean_obj_tag(v_a_3578_) == 0)
{
lean_del_object(v___x_3580_);
lean_del_object(v___x_3565_);
lean_dec(v_snd_3549_);
v_a_3555_ = v___x_3570_;
goto v___jp_3554_;
}
else
{
lean_object* v___x_3583_; 
lean_del_object(v___x_3551_);
lean_dec(v_mvarId_3537_);
lean_dec_ref(v_p_3536_);
lean_inc_ref(v_a_3578_);
if (v_isShared_3566_ == 0)
{
lean_ctor_set(v___x_3565_, 0, v_a_3578_);
v___x_3583_ = v___x_3565_;
goto v_reusejp_3582_;
}
else
{
lean_object* v_reuseFailAlloc_3598_; 
v_reuseFailAlloc_3598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3598_, 0, v_a_3578_);
v___x_3583_ = v_reuseFailAlloc_3598_;
goto v_reusejp_3582_;
}
v_reusejp_3582_:
{
lean_object* v___x_3585_; uint8_t v_isShared_3586_; uint8_t v_isSharedCheck_3596_; 
v_isSharedCheck_3596_ = !lean_is_exclusive(v_a_3578_);
if (v_isSharedCheck_3596_ == 0)
{
lean_object* v_unused_3597_; 
v_unused_3597_ = lean_ctor_get(v_a_3578_, 0);
lean_dec(v_unused_3597_);
v___x_3585_ = v_a_3578_;
v_isShared_3586_ = v_isSharedCheck_3596_;
goto v_resetjp_3584_;
}
else
{
lean_dec(v_a_3578_);
v___x_3585_ = lean_box(0);
v_isShared_3586_ = v_isSharedCheck_3596_;
goto v_resetjp_3584_;
}
v_resetjp_3584_:
{
lean_object* v___x_3587_; lean_object* v___x_3589_; 
v___x_3587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3587_, 0, v___x_3583_);
lean_ctor_set(v___x_3587_, 1, v___x_3569_);
if (v_isShared_3586_ == 0)
{
lean_ctor_set_tag(v___x_3585_, 0);
lean_ctor_set(v___x_3585_, 0, v___x_3587_);
v___x_3589_ = v___x_3585_;
goto v_reusejp_3588_;
}
else
{
lean_object* v_reuseFailAlloc_3595_; 
v_reuseFailAlloc_3595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3595_, 0, v___x_3587_);
v___x_3589_ = v_reuseFailAlloc_3595_;
goto v_reusejp_3588_;
}
v_reusejp_3588_:
{
lean_object* v___x_3590_; lean_object* v___x_3591_; lean_object* v___x_3593_; 
v___x_3590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3590_, 0, v___x_3589_);
v___x_3591_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3591_, 0, v___x_3590_);
lean_ctor_set(v___x_3591_, 1, v_snd_3549_);
if (v_isShared_3581_ == 0)
{
lean_ctor_set(v___x_3580_, 0, v___x_3591_);
v___x_3593_ = v___x_3580_;
goto v_reusejp_3592_;
}
else
{
lean_object* v_reuseFailAlloc_3594_; 
v_reuseFailAlloc_3594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3594_, 0, v___x_3591_);
v___x_3593_ = v_reuseFailAlloc_3594_;
goto v_reusejp_3592_;
}
v_reusejp_3592_:
{
return v___x_3593_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3600_; lean_object* v___x_3602_; uint8_t v_isShared_3603_; uint8_t v_isSharedCheck_3607_; 
lean_del_object(v___x_3565_);
lean_del_object(v___x_3551_);
lean_dec(v_snd_3549_);
lean_dec(v_mvarId_3537_);
lean_dec_ref(v_p_3536_);
v_a_3600_ = lean_ctor_get(v___x_3577_, 0);
v_isSharedCheck_3607_ = !lean_is_exclusive(v___x_3577_);
if (v_isSharedCheck_3607_ == 0)
{
v___x_3602_ = v___x_3577_;
v_isShared_3603_ = v_isSharedCheck_3607_;
goto v_resetjp_3601_;
}
else
{
lean_inc(v_a_3600_);
lean_dec(v___x_3577_);
v___x_3602_ = lean_box(0);
v_isShared_3603_ = v_isSharedCheck_3607_;
goto v_resetjp_3601_;
}
v_resetjp_3601_:
{
lean_object* v___x_3605_; 
if (v_isShared_3603_ == 0)
{
v___x_3605_ = v___x_3602_;
goto v_reusejp_3604_;
}
else
{
lean_object* v_reuseFailAlloc_3606_; 
v_reuseFailAlloc_3606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3606_, 0, v_a_3600_);
v___x_3605_ = v_reuseFailAlloc_3606_;
goto v_reusejp_3604_;
}
v_reusejp_3604_:
{
return v___x_3605_;
}
}
}
}
}
else
{
lean_object* v_a_3608_; lean_object* v___x_3610_; uint8_t v_isShared_3611_; uint8_t v_isSharedCheck_3615_; 
lean_del_object(v___x_3565_);
lean_dec(v_val_3563_);
lean_del_object(v___x_3551_);
lean_dec(v_snd_3549_);
lean_dec(v_mvarId_3537_);
lean_dec_ref(v_p_3536_);
v_a_3608_ = lean_ctor_get(v___x_3567_, 0);
v_isSharedCheck_3615_ = !lean_is_exclusive(v___x_3567_);
if (v_isSharedCheck_3615_ == 0)
{
v___x_3610_ = v___x_3567_;
v_isShared_3611_ = v_isSharedCheck_3615_;
goto v_resetjp_3609_;
}
else
{
lean_inc(v_a_3608_);
lean_dec(v___x_3567_);
v___x_3610_ = lean_box(0);
v_isShared_3611_ = v_isSharedCheck_3615_;
goto v_resetjp_3609_;
}
v_resetjp_3609_:
{
lean_object* v___x_3613_; 
if (v_isShared_3611_ == 0)
{
v___x_3613_ = v___x_3610_;
goto v_reusejp_3612_;
}
else
{
lean_object* v_reuseFailAlloc_3614_; 
v_reuseFailAlloc_3614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3614_, 0, v_a_3608_);
v___x_3613_ = v_reuseFailAlloc_3614_;
goto v_reusejp_3612_;
}
v_reusejp_3612_:
{
return v___x_3613_;
}
}
}
}
}
v___jp_3554_:
{
lean_object* v___x_3557_; 
if (v_isShared_3552_ == 0)
{
lean_ctor_set(v___x_3551_, 1, v_a_3555_);
lean_ctor_set(v___x_3551_, 0, v___x_3553_);
v___x_3557_ = v___x_3551_;
goto v_reusejp_3556_;
}
else
{
lean_object* v_reuseFailAlloc_3561_; 
v_reuseFailAlloc_3561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3561_, 0, v___x_3553_);
lean_ctor_set(v_reuseFailAlloc_3561_, 1, v_a_3555_);
v___x_3557_ = v_reuseFailAlloc_3561_;
goto v_reusejp_3556_;
}
v_reusejp_3556_:
{
size_t v___x_3558_; size_t v___x_3559_; lean_object* v___x_3560_; 
v___x_3558_ = ((size_t)1ULL);
v___x_3559_ = lean_usize_add(v_i_3540_, v___x_3558_);
v___x_3560_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5(v_p_3536_, v_mvarId_3537_, v_as_3538_, v_sz_3539_, v___x_3559_, v___x_3557_, v___y_3542_, v___y_3543_, v___y_3544_, v___y_3545_);
return v___x_3560_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4___boxed(lean_object* v_p_3619_, lean_object* v_mvarId_3620_, lean_object* v_as_3621_, lean_object* v_sz_3622_, lean_object* v_i_3623_, lean_object* v_b_3624_, lean_object* v___y_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_){
_start:
{
size_t v_sz_boxed_3630_; size_t v_i_boxed_3631_; lean_object* v_res_3632_; 
v_sz_boxed_3630_ = lean_unbox_usize(v_sz_3622_);
lean_dec(v_sz_3622_);
v_i_boxed_3631_ = lean_unbox_usize(v_i_3623_);
lean_dec(v_i_3623_);
v_res_3632_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4(v_p_3619_, v_mvarId_3620_, v_as_3621_, v_sz_boxed_3630_, v_i_boxed_3631_, v_b_3624_, v___y_3625_, v___y_3626_, v___y_3627_, v___y_3628_);
lean_dec(v___y_3628_);
lean_dec_ref(v___y_3627_);
lean_dec(v___y_3626_);
lean_dec_ref(v___y_3625_);
lean_dec_ref(v_as_3621_);
return v_res_3632_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2(lean_object* v_init_3633_, lean_object* v_p_3634_, lean_object* v_mvarId_3635_, lean_object* v_n_3636_, lean_object* v_b_3637_, lean_object* v___y_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_, lean_object* v___y_3641_){
_start:
{
if (lean_obj_tag(v_n_3636_) == 0)
{
lean_object* v_cs_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; size_t v_sz_3646_; size_t v___x_3647_; lean_object* v___x_3648_; 
v_cs_3643_ = lean_ctor_get(v_n_3636_, 0);
v___x_3644_ = lean_box(0);
v___x_3645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3645_, 0, v___x_3644_);
lean_ctor_set(v___x_3645_, 1, v_b_3637_);
v_sz_3646_ = lean_array_size(v_cs_3643_);
v___x_3647_ = ((size_t)0ULL);
v___x_3648_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__3(v_init_3633_, v_p_3634_, v_mvarId_3635_, v_cs_3643_, v_sz_3646_, v___x_3647_, v___x_3645_, v___y_3638_, v___y_3639_, v___y_3640_, v___y_3641_);
if (lean_obj_tag(v___x_3648_) == 0)
{
lean_object* v_a_3649_; lean_object* v___x_3651_; uint8_t v_isShared_3652_; uint8_t v_isSharedCheck_3663_; 
v_a_3649_ = lean_ctor_get(v___x_3648_, 0);
v_isSharedCheck_3663_ = !lean_is_exclusive(v___x_3648_);
if (v_isSharedCheck_3663_ == 0)
{
v___x_3651_ = v___x_3648_;
v_isShared_3652_ = v_isSharedCheck_3663_;
goto v_resetjp_3650_;
}
else
{
lean_inc(v_a_3649_);
lean_dec(v___x_3648_);
v___x_3651_ = lean_box(0);
v_isShared_3652_ = v_isSharedCheck_3663_;
goto v_resetjp_3650_;
}
v_resetjp_3650_:
{
lean_object* v_fst_3653_; 
v_fst_3653_ = lean_ctor_get(v_a_3649_, 0);
if (lean_obj_tag(v_fst_3653_) == 0)
{
lean_object* v_snd_3654_; lean_object* v___x_3655_; lean_object* v___x_3657_; 
v_snd_3654_ = lean_ctor_get(v_a_3649_, 1);
lean_inc(v_snd_3654_);
lean_dec(v_a_3649_);
v___x_3655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3655_, 0, v_snd_3654_);
if (v_isShared_3652_ == 0)
{
lean_ctor_set(v___x_3651_, 0, v___x_3655_);
v___x_3657_ = v___x_3651_;
goto v_reusejp_3656_;
}
else
{
lean_object* v_reuseFailAlloc_3658_; 
v_reuseFailAlloc_3658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3658_, 0, v___x_3655_);
v___x_3657_ = v_reuseFailAlloc_3658_;
goto v_reusejp_3656_;
}
v_reusejp_3656_:
{
return v___x_3657_;
}
}
else
{
lean_object* v_val_3659_; lean_object* v___x_3661_; 
lean_inc_ref(v_fst_3653_);
lean_dec(v_a_3649_);
v_val_3659_ = lean_ctor_get(v_fst_3653_, 0);
lean_inc(v_val_3659_);
lean_dec_ref_known(v_fst_3653_, 1);
if (v_isShared_3652_ == 0)
{
lean_ctor_set(v___x_3651_, 0, v_val_3659_);
v___x_3661_ = v___x_3651_;
goto v_reusejp_3660_;
}
else
{
lean_object* v_reuseFailAlloc_3662_; 
v_reuseFailAlloc_3662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3662_, 0, v_val_3659_);
v___x_3661_ = v_reuseFailAlloc_3662_;
goto v_reusejp_3660_;
}
v_reusejp_3660_:
{
return v___x_3661_;
}
}
}
}
else
{
lean_object* v_a_3664_; lean_object* v___x_3666_; uint8_t v_isShared_3667_; uint8_t v_isSharedCheck_3671_; 
v_a_3664_ = lean_ctor_get(v___x_3648_, 0);
v_isSharedCheck_3671_ = !lean_is_exclusive(v___x_3648_);
if (v_isSharedCheck_3671_ == 0)
{
v___x_3666_ = v___x_3648_;
v_isShared_3667_ = v_isSharedCheck_3671_;
goto v_resetjp_3665_;
}
else
{
lean_inc(v_a_3664_);
lean_dec(v___x_3648_);
v___x_3666_ = lean_box(0);
v_isShared_3667_ = v_isSharedCheck_3671_;
goto v_resetjp_3665_;
}
v_resetjp_3665_:
{
lean_object* v___x_3669_; 
if (v_isShared_3667_ == 0)
{
v___x_3669_ = v___x_3666_;
goto v_reusejp_3668_;
}
else
{
lean_object* v_reuseFailAlloc_3670_; 
v_reuseFailAlloc_3670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3670_, 0, v_a_3664_);
v___x_3669_ = v_reuseFailAlloc_3670_;
goto v_reusejp_3668_;
}
v_reusejp_3668_:
{
return v___x_3669_;
}
}
}
}
else
{
lean_object* v_vs_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; size_t v_sz_3675_; size_t v___x_3676_; lean_object* v___x_3677_; 
v_vs_3672_ = lean_ctor_get(v_n_3636_, 0);
v___x_3673_ = lean_box(0);
v___x_3674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3674_, 0, v___x_3673_);
lean_ctor_set(v___x_3674_, 1, v_b_3637_);
v_sz_3675_ = lean_array_size(v_vs_3672_);
v___x_3676_ = ((size_t)0ULL);
v___x_3677_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4(v_p_3634_, v_mvarId_3635_, v_vs_3672_, v_sz_3675_, v___x_3676_, v___x_3674_, v___y_3638_, v___y_3639_, v___y_3640_, v___y_3641_);
if (lean_obj_tag(v___x_3677_) == 0)
{
lean_object* v_a_3678_; lean_object* v___x_3680_; uint8_t v_isShared_3681_; uint8_t v_isSharedCheck_3692_; 
v_a_3678_ = lean_ctor_get(v___x_3677_, 0);
v_isSharedCheck_3692_ = !lean_is_exclusive(v___x_3677_);
if (v_isSharedCheck_3692_ == 0)
{
v___x_3680_ = v___x_3677_;
v_isShared_3681_ = v_isSharedCheck_3692_;
goto v_resetjp_3679_;
}
else
{
lean_inc(v_a_3678_);
lean_dec(v___x_3677_);
v___x_3680_ = lean_box(0);
v_isShared_3681_ = v_isSharedCheck_3692_;
goto v_resetjp_3679_;
}
v_resetjp_3679_:
{
lean_object* v_fst_3682_; 
v_fst_3682_ = lean_ctor_get(v_a_3678_, 0);
if (lean_obj_tag(v_fst_3682_) == 0)
{
lean_object* v_snd_3683_; lean_object* v___x_3684_; lean_object* v___x_3686_; 
v_snd_3683_ = lean_ctor_get(v_a_3678_, 1);
lean_inc(v_snd_3683_);
lean_dec(v_a_3678_);
v___x_3684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3684_, 0, v_snd_3683_);
if (v_isShared_3681_ == 0)
{
lean_ctor_set(v___x_3680_, 0, v___x_3684_);
v___x_3686_ = v___x_3680_;
goto v_reusejp_3685_;
}
else
{
lean_object* v_reuseFailAlloc_3687_; 
v_reuseFailAlloc_3687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3687_, 0, v___x_3684_);
v___x_3686_ = v_reuseFailAlloc_3687_;
goto v_reusejp_3685_;
}
v_reusejp_3685_:
{
return v___x_3686_;
}
}
else
{
lean_object* v_val_3688_; lean_object* v___x_3690_; 
lean_inc_ref(v_fst_3682_);
lean_dec(v_a_3678_);
v_val_3688_ = lean_ctor_get(v_fst_3682_, 0);
lean_inc(v_val_3688_);
lean_dec_ref_known(v_fst_3682_, 1);
if (v_isShared_3681_ == 0)
{
lean_ctor_set(v___x_3680_, 0, v_val_3688_);
v___x_3690_ = v___x_3680_;
goto v_reusejp_3689_;
}
else
{
lean_object* v_reuseFailAlloc_3691_; 
v_reuseFailAlloc_3691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3691_, 0, v_val_3688_);
v___x_3690_ = v_reuseFailAlloc_3691_;
goto v_reusejp_3689_;
}
v_reusejp_3689_:
{
return v___x_3690_;
}
}
}
}
else
{
lean_object* v_a_3693_; lean_object* v___x_3695_; uint8_t v_isShared_3696_; uint8_t v_isSharedCheck_3700_; 
v_a_3693_ = lean_ctor_get(v___x_3677_, 0);
v_isSharedCheck_3700_ = !lean_is_exclusive(v___x_3677_);
if (v_isSharedCheck_3700_ == 0)
{
v___x_3695_ = v___x_3677_;
v_isShared_3696_ = v_isSharedCheck_3700_;
goto v_resetjp_3694_;
}
else
{
lean_inc(v_a_3693_);
lean_dec(v___x_3677_);
v___x_3695_ = lean_box(0);
v_isShared_3696_ = v_isSharedCheck_3700_;
goto v_resetjp_3694_;
}
v_resetjp_3694_:
{
lean_object* v___x_3698_; 
if (v_isShared_3696_ == 0)
{
v___x_3698_ = v___x_3695_;
goto v_reusejp_3697_;
}
else
{
lean_object* v_reuseFailAlloc_3699_; 
v_reuseFailAlloc_3699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3699_, 0, v_a_3693_);
v___x_3698_ = v_reuseFailAlloc_3699_;
goto v_reusejp_3697_;
}
v_reusejp_3697_:
{
return v___x_3698_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__3(lean_object* v_init_3701_, lean_object* v_p_3702_, lean_object* v_mvarId_3703_, lean_object* v_as_3704_, size_t v_sz_3705_, size_t v_i_3706_, lean_object* v_b_3707_, lean_object* v___y_3708_, lean_object* v___y_3709_, lean_object* v___y_3710_, lean_object* v___y_3711_){
_start:
{
uint8_t v___x_3713_; 
v___x_3713_ = lean_usize_dec_lt(v_i_3706_, v_sz_3705_);
if (v___x_3713_ == 0)
{
lean_object* v___x_3714_; 
lean_dec(v_mvarId_3703_);
lean_dec_ref(v_p_3702_);
v___x_3714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3714_, 0, v_b_3707_);
return v___x_3714_;
}
else
{
lean_object* v_snd_3715_; lean_object* v___x_3717_; uint8_t v_isShared_3718_; uint8_t v_isSharedCheck_3749_; 
v_snd_3715_ = lean_ctor_get(v_b_3707_, 1);
v_isSharedCheck_3749_ = !lean_is_exclusive(v_b_3707_);
if (v_isSharedCheck_3749_ == 0)
{
lean_object* v_unused_3750_; 
v_unused_3750_ = lean_ctor_get(v_b_3707_, 0);
lean_dec(v_unused_3750_);
v___x_3717_ = v_b_3707_;
v_isShared_3718_ = v_isSharedCheck_3749_;
goto v_resetjp_3716_;
}
else
{
lean_inc(v_snd_3715_);
lean_dec(v_b_3707_);
v___x_3717_ = lean_box(0);
v_isShared_3718_ = v_isSharedCheck_3749_;
goto v_resetjp_3716_;
}
v_resetjp_3716_:
{
lean_object* v_a_3719_; lean_object* v___x_3720_; 
v_a_3719_ = lean_array_uget_borrowed(v_as_3704_, v_i_3706_);
lean_inc(v_snd_3715_);
lean_inc(v_mvarId_3703_);
lean_inc_ref(v_p_3702_);
v___x_3720_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2(v_init_3701_, v_p_3702_, v_mvarId_3703_, v_a_3719_, v_snd_3715_, v___y_3708_, v___y_3709_, v___y_3710_, v___y_3711_);
if (lean_obj_tag(v___x_3720_) == 0)
{
lean_object* v_a_3721_; lean_object* v___x_3723_; uint8_t v_isShared_3724_; uint8_t v_isSharedCheck_3740_; 
v_a_3721_ = lean_ctor_get(v___x_3720_, 0);
v_isSharedCheck_3740_ = !lean_is_exclusive(v___x_3720_);
if (v_isSharedCheck_3740_ == 0)
{
v___x_3723_ = v___x_3720_;
v_isShared_3724_ = v_isSharedCheck_3740_;
goto v_resetjp_3722_;
}
else
{
lean_inc(v_a_3721_);
lean_dec(v___x_3720_);
v___x_3723_ = lean_box(0);
v_isShared_3724_ = v_isSharedCheck_3740_;
goto v_resetjp_3722_;
}
v_resetjp_3722_:
{
if (lean_obj_tag(v_a_3721_) == 0)
{
lean_object* v___x_3725_; lean_object* v___x_3727_; 
lean_dec(v_mvarId_3703_);
lean_dec_ref(v_p_3702_);
v___x_3725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3725_, 0, v_a_3721_);
if (v_isShared_3718_ == 0)
{
lean_ctor_set(v___x_3717_, 0, v___x_3725_);
v___x_3727_ = v___x_3717_;
goto v_reusejp_3726_;
}
else
{
lean_object* v_reuseFailAlloc_3731_; 
v_reuseFailAlloc_3731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3731_, 0, v___x_3725_);
lean_ctor_set(v_reuseFailAlloc_3731_, 1, v_snd_3715_);
v___x_3727_ = v_reuseFailAlloc_3731_;
goto v_reusejp_3726_;
}
v_reusejp_3726_:
{
lean_object* v___x_3729_; 
if (v_isShared_3724_ == 0)
{
lean_ctor_set(v___x_3723_, 0, v___x_3727_);
v___x_3729_ = v___x_3723_;
goto v_reusejp_3728_;
}
else
{
lean_object* v_reuseFailAlloc_3730_; 
v_reuseFailAlloc_3730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3730_, 0, v___x_3727_);
v___x_3729_ = v_reuseFailAlloc_3730_;
goto v_reusejp_3728_;
}
v_reusejp_3728_:
{
return v___x_3729_;
}
}
}
else
{
lean_object* v_a_3732_; lean_object* v___x_3733_; lean_object* v___x_3735_; 
lean_del_object(v___x_3723_);
lean_dec(v_snd_3715_);
v_a_3732_ = lean_ctor_get(v_a_3721_, 0);
lean_inc(v_a_3732_);
lean_dec_ref_known(v_a_3721_, 1);
v___x_3733_ = lean_box(0);
if (v_isShared_3718_ == 0)
{
lean_ctor_set(v___x_3717_, 1, v_a_3732_);
lean_ctor_set(v___x_3717_, 0, v___x_3733_);
v___x_3735_ = v___x_3717_;
goto v_reusejp_3734_;
}
else
{
lean_object* v_reuseFailAlloc_3739_; 
v_reuseFailAlloc_3739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3739_, 0, v___x_3733_);
lean_ctor_set(v_reuseFailAlloc_3739_, 1, v_a_3732_);
v___x_3735_ = v_reuseFailAlloc_3739_;
goto v_reusejp_3734_;
}
v_reusejp_3734_:
{
size_t v___x_3736_; size_t v___x_3737_; 
v___x_3736_ = ((size_t)1ULL);
v___x_3737_ = lean_usize_add(v_i_3706_, v___x_3736_);
v_i_3706_ = v___x_3737_;
v_b_3707_ = v___x_3735_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3741_; lean_object* v___x_3743_; uint8_t v_isShared_3744_; uint8_t v_isSharedCheck_3748_; 
lean_del_object(v___x_3717_);
lean_dec(v_snd_3715_);
lean_dec(v_mvarId_3703_);
lean_dec_ref(v_p_3702_);
v_a_3741_ = lean_ctor_get(v___x_3720_, 0);
v_isSharedCheck_3748_ = !lean_is_exclusive(v___x_3720_);
if (v_isSharedCheck_3748_ == 0)
{
v___x_3743_ = v___x_3720_;
v_isShared_3744_ = v_isSharedCheck_3748_;
goto v_resetjp_3742_;
}
else
{
lean_inc(v_a_3741_);
lean_dec(v___x_3720_);
v___x_3743_ = lean_box(0);
v_isShared_3744_ = v_isSharedCheck_3748_;
goto v_resetjp_3742_;
}
v_resetjp_3742_:
{
lean_object* v___x_3746_; 
if (v_isShared_3744_ == 0)
{
v___x_3746_ = v___x_3743_;
goto v_reusejp_3745_;
}
else
{
lean_object* v_reuseFailAlloc_3747_; 
v_reuseFailAlloc_3747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3747_, 0, v_a_3741_);
v___x_3746_ = v_reuseFailAlloc_3747_;
goto v_reusejp_3745_;
}
v_reusejp_3745_:
{
return v___x_3746_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__3___boxed(lean_object* v_init_3751_, lean_object* v_p_3752_, lean_object* v_mvarId_3753_, lean_object* v_as_3754_, lean_object* v_sz_3755_, lean_object* v_i_3756_, lean_object* v_b_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_){
_start:
{
size_t v_sz_boxed_3763_; size_t v_i_boxed_3764_; lean_object* v_res_3765_; 
v_sz_boxed_3763_ = lean_unbox_usize(v_sz_3755_);
lean_dec(v_sz_3755_);
v_i_boxed_3764_ = lean_unbox_usize(v_i_3756_);
lean_dec(v_i_3756_);
v_res_3765_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__3(v_init_3751_, v_p_3752_, v_mvarId_3753_, v_as_3754_, v_sz_boxed_3763_, v_i_boxed_3764_, v_b_3757_, v___y_3758_, v___y_3759_, v___y_3760_, v___y_3761_);
lean_dec(v___y_3761_);
lean_dec_ref(v___y_3760_);
lean_dec(v___y_3759_);
lean_dec_ref(v___y_3758_);
lean_dec_ref(v_as_3754_);
lean_dec_ref(v_init_3751_);
return v_res_3765_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2___boxed(lean_object* v_init_3766_, lean_object* v_p_3767_, lean_object* v_mvarId_3768_, lean_object* v_n_3769_, lean_object* v_b_3770_, lean_object* v___y_3771_, lean_object* v___y_3772_, lean_object* v___y_3773_, lean_object* v___y_3774_, lean_object* v___y_3775_){
_start:
{
lean_object* v_res_3776_; 
v_res_3776_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2(v_init_3766_, v_p_3767_, v_mvarId_3768_, v_n_3769_, v_b_3770_, v___y_3771_, v___y_3772_, v___y_3773_, v___y_3774_);
lean_dec(v___y_3774_);
lean_dec_ref(v___y_3773_);
lean_dec(v___y_3772_);
lean_dec_ref(v___y_3771_);
lean_dec_ref(v_n_3769_);
lean_dec_ref(v_init_3766_);
return v_res_3776_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3_spec__6(lean_object* v_p_3780_, lean_object* v_mvarId_3781_, lean_object* v_as_3782_, size_t v_sz_3783_, size_t v_i_3784_, lean_object* v_b_3785_, lean_object* v___y_3786_, lean_object* v___y_3787_, lean_object* v___y_3788_, lean_object* v___y_3789_){
_start:
{
uint8_t v___x_3791_; 
v___x_3791_ = lean_usize_dec_lt(v_i_3784_, v_sz_3783_);
if (v___x_3791_ == 0)
{
lean_object* v___x_3792_; 
lean_dec(v_mvarId_3781_);
lean_dec_ref(v_p_3780_);
v___x_3792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3792_, 0, v_b_3785_);
return v___x_3792_;
}
else
{
lean_object* v_snd_3793_; lean_object* v___x_3795_; uint8_t v_isShared_3796_; uint8_t v_isSharedCheck_3860_; 
v_snd_3793_ = lean_ctor_get(v_b_3785_, 1);
v_isSharedCheck_3860_ = !lean_is_exclusive(v_b_3785_);
if (v_isSharedCheck_3860_ == 0)
{
lean_object* v_unused_3861_; 
v_unused_3861_ = lean_ctor_get(v_b_3785_, 0);
lean_dec(v_unused_3861_);
v___x_3795_ = v_b_3785_;
v_isShared_3796_ = v_isSharedCheck_3860_;
goto v_resetjp_3794_;
}
else
{
lean_inc(v_snd_3793_);
lean_dec(v_b_3785_);
v___x_3795_ = lean_box(0);
v_isShared_3796_ = v_isSharedCheck_3860_;
goto v_resetjp_3794_;
}
v_resetjp_3794_:
{
lean_object* v___x_3797_; lean_object* v_a_3799_; lean_object* v_a_3806_; 
v___x_3797_ = lean_box(0);
v_a_3806_ = lean_array_uget(v_as_3782_, v_i_3784_);
if (lean_obj_tag(v_a_3806_) == 0)
{
v_a_3799_ = v_snd_3793_;
goto v___jp_3798_;
}
else
{
lean_object* v_val_3807_; lean_object* v___x_3809_; uint8_t v_isShared_3810_; uint8_t v_isSharedCheck_3859_; 
v_val_3807_ = lean_ctor_get(v_a_3806_, 0);
v_isSharedCheck_3859_ = !lean_is_exclusive(v_a_3806_);
if (v_isSharedCheck_3859_ == 0)
{
v___x_3809_ = v_a_3806_;
v_isShared_3810_ = v_isSharedCheck_3859_;
goto v_resetjp_3808_;
}
else
{
lean_inc(v_val_3807_);
lean_dec(v_a_3806_);
v___x_3809_ = lean_box(0);
v_isShared_3810_ = v_isSharedCheck_3859_;
goto v_resetjp_3808_;
}
v_resetjp_3808_:
{
lean_object* v___x_3811_; 
lean_inc_ref(v_p_3780_);
lean_inc(v___y_3789_);
lean_inc_ref(v___y_3788_);
lean_inc(v___y_3787_);
lean_inc_ref(v___y_3786_);
lean_inc(v_val_3807_);
v___x_3811_ = lean_apply_6(v_p_3780_, v_val_3807_, v___y_3786_, v___y_3787_, v___y_3788_, v___y_3789_, lean_box(0));
if (lean_obj_tag(v___x_3811_) == 0)
{
lean_object* v_a_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; uint8_t v___x_3815_; 
v_a_3812_ = lean_ctor_get(v___x_3811_, 0);
lean_inc(v_a_3812_);
lean_dec_ref_known(v___x_3811_, 1);
v___x_3813_ = lean_box(0);
v___x_3814_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3_spec__6___closed__0));
v___x_3815_ = lean_unbox(v_a_3812_);
lean_dec(v_a_3812_);
if (v___x_3815_ == 0)
{
lean_del_object(v___x_3809_);
lean_dec(v_val_3807_);
lean_dec(v_snd_3793_);
v_a_3799_ = v___x_3814_;
goto v___jp_3798_;
}
else
{
lean_object* v___x_3816_; lean_object* v___x_3817_; uint8_t v___x_3818_; lean_object* v___x_3819_; lean_object* v___f_3820_; lean_object* v___x_3821_; 
v___x_3816_ = l_Lean_LocalDecl_fvarId(v_val_3807_);
lean_dec(v_val_3807_);
v___x_3817_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5___closed__1));
v___x_3818_ = 0;
v___x_3819_ = lean_box(v___x_3818_);
lean_inc(v_mvarId_3781_);
v___f_3820_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3___lam__0___boxed), 10, 5);
lean_closure_set(v___f_3820_, 0, v_mvarId_3781_);
lean_closure_set(v___f_3820_, 1, v___x_3816_);
lean_closure_set(v___f_3820_, 2, v___x_3817_);
lean_closure_set(v___f_3820_, 3, v___x_3819_);
lean_closure_set(v___f_3820_, 4, v___x_3797_);
v___x_3821_ = l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1___redArg(v___f_3820_, v___y_3786_, v___y_3787_, v___y_3788_, v___y_3789_);
if (lean_obj_tag(v___x_3821_) == 0)
{
lean_object* v_a_3822_; lean_object* v___x_3824_; uint8_t v_isShared_3825_; uint8_t v_isSharedCheck_3842_; 
v_a_3822_ = lean_ctor_get(v___x_3821_, 0);
v_isSharedCheck_3842_ = !lean_is_exclusive(v___x_3821_);
if (v_isSharedCheck_3842_ == 0)
{
v___x_3824_ = v___x_3821_;
v_isShared_3825_ = v_isSharedCheck_3842_;
goto v_resetjp_3823_;
}
else
{
lean_inc(v_a_3822_);
lean_dec(v___x_3821_);
v___x_3824_ = lean_box(0);
v_isShared_3825_ = v_isSharedCheck_3842_;
goto v_resetjp_3823_;
}
v_resetjp_3823_:
{
if (lean_obj_tag(v_a_3822_) == 0)
{
lean_del_object(v___x_3824_);
lean_del_object(v___x_3809_);
lean_dec(v_snd_3793_);
v_a_3799_ = v___x_3814_;
goto v___jp_3798_;
}
else
{
lean_object* v___x_3827_; 
lean_del_object(v___x_3795_);
lean_dec(v_mvarId_3781_);
lean_dec_ref(v_p_3780_);
lean_inc_ref(v_a_3822_);
if (v_isShared_3810_ == 0)
{
lean_ctor_set(v___x_3809_, 0, v_a_3822_);
v___x_3827_ = v___x_3809_;
goto v_reusejp_3826_;
}
else
{
lean_object* v_reuseFailAlloc_3841_; 
v_reuseFailAlloc_3841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3841_, 0, v_a_3822_);
v___x_3827_ = v_reuseFailAlloc_3841_;
goto v_reusejp_3826_;
}
v_reusejp_3826_:
{
lean_object* v___x_3829_; uint8_t v_isShared_3830_; uint8_t v_isSharedCheck_3839_; 
v_isSharedCheck_3839_ = !lean_is_exclusive(v_a_3822_);
if (v_isSharedCheck_3839_ == 0)
{
lean_object* v_unused_3840_; 
v_unused_3840_ = lean_ctor_get(v_a_3822_, 0);
lean_dec(v_unused_3840_);
v___x_3829_ = v_a_3822_;
v_isShared_3830_ = v_isSharedCheck_3839_;
goto v_resetjp_3828_;
}
else
{
lean_dec(v_a_3822_);
v___x_3829_ = lean_box(0);
v_isShared_3830_ = v_isSharedCheck_3839_;
goto v_resetjp_3828_;
}
v_resetjp_3828_:
{
lean_object* v___x_3831_; lean_object* v___x_3833_; 
v___x_3831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3831_, 0, v___x_3827_);
lean_ctor_set(v___x_3831_, 1, v___x_3813_);
if (v_isShared_3830_ == 0)
{
lean_ctor_set(v___x_3829_, 0, v___x_3831_);
v___x_3833_ = v___x_3829_;
goto v_reusejp_3832_;
}
else
{
lean_object* v_reuseFailAlloc_3838_; 
v_reuseFailAlloc_3838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3838_, 0, v___x_3831_);
v___x_3833_ = v_reuseFailAlloc_3838_;
goto v_reusejp_3832_;
}
v_reusejp_3832_:
{
lean_object* v___x_3834_; lean_object* v___x_3836_; 
v___x_3834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3834_, 0, v___x_3833_);
lean_ctor_set(v___x_3834_, 1, v_snd_3793_);
if (v_isShared_3825_ == 0)
{
lean_ctor_set(v___x_3824_, 0, v___x_3834_);
v___x_3836_ = v___x_3824_;
goto v_reusejp_3835_;
}
else
{
lean_object* v_reuseFailAlloc_3837_; 
v_reuseFailAlloc_3837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3837_, 0, v___x_3834_);
v___x_3836_ = v_reuseFailAlloc_3837_;
goto v_reusejp_3835_;
}
v_reusejp_3835_:
{
return v___x_3836_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3843_; lean_object* v___x_3845_; uint8_t v_isShared_3846_; uint8_t v_isSharedCheck_3850_; 
lean_del_object(v___x_3809_);
lean_del_object(v___x_3795_);
lean_dec(v_snd_3793_);
lean_dec(v_mvarId_3781_);
lean_dec_ref(v_p_3780_);
v_a_3843_ = lean_ctor_get(v___x_3821_, 0);
v_isSharedCheck_3850_ = !lean_is_exclusive(v___x_3821_);
if (v_isSharedCheck_3850_ == 0)
{
v___x_3845_ = v___x_3821_;
v_isShared_3846_ = v_isSharedCheck_3850_;
goto v_resetjp_3844_;
}
else
{
lean_inc(v_a_3843_);
lean_dec(v___x_3821_);
v___x_3845_ = lean_box(0);
v_isShared_3846_ = v_isSharedCheck_3850_;
goto v_resetjp_3844_;
}
v_resetjp_3844_:
{
lean_object* v___x_3848_; 
if (v_isShared_3846_ == 0)
{
v___x_3848_ = v___x_3845_;
goto v_reusejp_3847_;
}
else
{
lean_object* v_reuseFailAlloc_3849_; 
v_reuseFailAlloc_3849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3849_, 0, v_a_3843_);
v___x_3848_ = v_reuseFailAlloc_3849_;
goto v_reusejp_3847_;
}
v_reusejp_3847_:
{
return v___x_3848_;
}
}
}
}
}
else
{
lean_object* v_a_3851_; lean_object* v___x_3853_; uint8_t v_isShared_3854_; uint8_t v_isSharedCheck_3858_; 
lean_del_object(v___x_3809_);
lean_dec(v_val_3807_);
lean_del_object(v___x_3795_);
lean_dec(v_snd_3793_);
lean_dec(v_mvarId_3781_);
lean_dec_ref(v_p_3780_);
v_a_3851_ = lean_ctor_get(v___x_3811_, 0);
v_isSharedCheck_3858_ = !lean_is_exclusive(v___x_3811_);
if (v_isSharedCheck_3858_ == 0)
{
v___x_3853_ = v___x_3811_;
v_isShared_3854_ = v_isSharedCheck_3858_;
goto v_resetjp_3852_;
}
else
{
lean_inc(v_a_3851_);
lean_dec(v___x_3811_);
v___x_3853_ = lean_box(0);
v_isShared_3854_ = v_isSharedCheck_3858_;
goto v_resetjp_3852_;
}
v_resetjp_3852_:
{
lean_object* v___x_3856_; 
if (v_isShared_3854_ == 0)
{
v___x_3856_ = v___x_3853_;
goto v_reusejp_3855_;
}
else
{
lean_object* v_reuseFailAlloc_3857_; 
v_reuseFailAlloc_3857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3857_, 0, v_a_3851_);
v___x_3856_ = v_reuseFailAlloc_3857_;
goto v_reusejp_3855_;
}
v_reusejp_3855_:
{
return v___x_3856_;
}
}
}
}
}
v___jp_3798_:
{
lean_object* v___x_3801_; 
if (v_isShared_3796_ == 0)
{
lean_ctor_set(v___x_3795_, 1, v_a_3799_);
lean_ctor_set(v___x_3795_, 0, v___x_3797_);
v___x_3801_ = v___x_3795_;
goto v_reusejp_3800_;
}
else
{
lean_object* v_reuseFailAlloc_3805_; 
v_reuseFailAlloc_3805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3805_, 0, v___x_3797_);
lean_ctor_set(v_reuseFailAlloc_3805_, 1, v_a_3799_);
v___x_3801_ = v_reuseFailAlloc_3805_;
goto v_reusejp_3800_;
}
v_reusejp_3800_:
{
size_t v___x_3802_; size_t v___x_3803_; 
v___x_3802_ = ((size_t)1ULL);
v___x_3803_ = lean_usize_add(v_i_3784_, v___x_3802_);
v_i_3784_ = v___x_3803_;
v_b_3785_ = v___x_3801_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3_spec__6___boxed(lean_object* v_p_3862_, lean_object* v_mvarId_3863_, lean_object* v_as_3864_, lean_object* v_sz_3865_, lean_object* v_i_3866_, lean_object* v_b_3867_, lean_object* v___y_3868_, lean_object* v___y_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_){
_start:
{
size_t v_sz_boxed_3873_; size_t v_i_boxed_3874_; lean_object* v_res_3875_; 
v_sz_boxed_3873_ = lean_unbox_usize(v_sz_3865_);
lean_dec(v_sz_3865_);
v_i_boxed_3874_ = lean_unbox_usize(v_i_3866_);
lean_dec(v_i_3866_);
v_res_3875_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3_spec__6(v_p_3862_, v_mvarId_3863_, v_as_3864_, v_sz_boxed_3873_, v_i_boxed_3874_, v_b_3867_, v___y_3868_, v___y_3869_, v___y_3870_, v___y_3871_);
lean_dec(v___y_3871_);
lean_dec_ref(v___y_3870_);
lean_dec(v___y_3869_);
lean_dec_ref(v___y_3868_);
lean_dec_ref(v_as_3864_);
return v_res_3875_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3(lean_object* v_p_3876_, lean_object* v_mvarId_3877_, lean_object* v_as_3878_, size_t v_sz_3879_, size_t v_i_3880_, lean_object* v_b_3881_, lean_object* v___y_3882_, lean_object* v___y_3883_, lean_object* v___y_3884_, lean_object* v___y_3885_){
_start:
{
uint8_t v___x_3887_; 
v___x_3887_ = lean_usize_dec_lt(v_i_3880_, v_sz_3879_);
if (v___x_3887_ == 0)
{
lean_object* v___x_3888_; 
lean_dec(v_mvarId_3877_);
lean_dec_ref(v_p_3876_);
v___x_3888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3888_, 0, v_b_3881_);
return v___x_3888_;
}
else
{
lean_object* v_snd_3889_; lean_object* v___x_3891_; uint8_t v_isShared_3892_; uint8_t v_isSharedCheck_3956_; 
v_snd_3889_ = lean_ctor_get(v_b_3881_, 1);
v_isSharedCheck_3956_ = !lean_is_exclusive(v_b_3881_);
if (v_isSharedCheck_3956_ == 0)
{
lean_object* v_unused_3957_; 
v_unused_3957_ = lean_ctor_get(v_b_3881_, 0);
lean_dec(v_unused_3957_);
v___x_3891_ = v_b_3881_;
v_isShared_3892_ = v_isSharedCheck_3956_;
goto v_resetjp_3890_;
}
else
{
lean_inc(v_snd_3889_);
lean_dec(v_b_3881_);
v___x_3891_ = lean_box(0);
v_isShared_3892_ = v_isSharedCheck_3956_;
goto v_resetjp_3890_;
}
v_resetjp_3890_:
{
lean_object* v___x_3893_; lean_object* v_a_3895_; lean_object* v_a_3902_; 
v___x_3893_ = lean_box(0);
v_a_3902_ = lean_array_uget(v_as_3878_, v_i_3880_);
if (lean_obj_tag(v_a_3902_) == 0)
{
v_a_3895_ = v_snd_3889_;
goto v___jp_3894_;
}
else
{
lean_object* v_val_3903_; lean_object* v___x_3905_; uint8_t v_isShared_3906_; uint8_t v_isSharedCheck_3955_; 
v_val_3903_ = lean_ctor_get(v_a_3902_, 0);
v_isSharedCheck_3955_ = !lean_is_exclusive(v_a_3902_);
if (v_isSharedCheck_3955_ == 0)
{
v___x_3905_ = v_a_3902_;
v_isShared_3906_ = v_isSharedCheck_3955_;
goto v_resetjp_3904_;
}
else
{
lean_inc(v_val_3903_);
lean_dec(v_a_3902_);
v___x_3905_ = lean_box(0);
v_isShared_3906_ = v_isSharedCheck_3955_;
goto v_resetjp_3904_;
}
v_resetjp_3904_:
{
lean_object* v___x_3907_; 
lean_inc_ref(v_p_3876_);
lean_inc(v___y_3885_);
lean_inc_ref(v___y_3884_);
lean_inc(v___y_3883_);
lean_inc_ref(v___y_3882_);
lean_inc(v_val_3903_);
v___x_3907_ = lean_apply_6(v_p_3876_, v_val_3903_, v___y_3882_, v___y_3883_, v___y_3884_, v___y_3885_, lean_box(0));
if (lean_obj_tag(v___x_3907_) == 0)
{
lean_object* v_a_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; uint8_t v___x_3911_; 
v_a_3908_ = lean_ctor_get(v___x_3907_, 0);
lean_inc(v_a_3908_);
lean_dec_ref_known(v___x_3907_, 1);
v___x_3909_ = lean_box(0);
v___x_3910_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3_spec__6___closed__0));
v___x_3911_ = lean_unbox(v_a_3908_);
lean_dec(v_a_3908_);
if (v___x_3911_ == 0)
{
lean_del_object(v___x_3905_);
lean_dec(v_val_3903_);
lean_dec(v_snd_3889_);
v_a_3895_ = v___x_3910_;
goto v___jp_3894_;
}
else
{
lean_object* v___x_3912_; lean_object* v___x_3913_; uint8_t v___x_3914_; lean_object* v___x_3915_; lean_object* v___f_3916_; lean_object* v___x_3917_; 
v___x_3912_ = l_Lean_LocalDecl_fvarId(v_val_3903_);
lean_dec(v_val_3903_);
v___x_3913_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5___closed__1));
v___x_3914_ = 0;
v___x_3915_ = lean_box(v___x_3914_);
lean_inc(v_mvarId_3877_);
v___f_3916_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3___lam__0___boxed), 10, 5);
lean_closure_set(v___f_3916_, 0, v_mvarId_3877_);
lean_closure_set(v___f_3916_, 1, v___x_3912_);
lean_closure_set(v___f_3916_, 2, v___x_3913_);
lean_closure_set(v___f_3916_, 3, v___x_3915_);
lean_closure_set(v___f_3916_, 4, v___x_3893_);
v___x_3917_ = l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1___redArg(v___f_3916_, v___y_3882_, v___y_3883_, v___y_3884_, v___y_3885_);
if (lean_obj_tag(v___x_3917_) == 0)
{
lean_object* v_a_3918_; lean_object* v___x_3920_; uint8_t v_isShared_3921_; uint8_t v_isSharedCheck_3938_; 
v_a_3918_ = lean_ctor_get(v___x_3917_, 0);
v_isSharedCheck_3938_ = !lean_is_exclusive(v___x_3917_);
if (v_isSharedCheck_3938_ == 0)
{
v___x_3920_ = v___x_3917_;
v_isShared_3921_ = v_isSharedCheck_3938_;
goto v_resetjp_3919_;
}
else
{
lean_inc(v_a_3918_);
lean_dec(v___x_3917_);
v___x_3920_ = lean_box(0);
v_isShared_3921_ = v_isSharedCheck_3938_;
goto v_resetjp_3919_;
}
v_resetjp_3919_:
{
if (lean_obj_tag(v_a_3918_) == 0)
{
lean_del_object(v___x_3920_);
lean_del_object(v___x_3905_);
lean_dec(v_snd_3889_);
v_a_3895_ = v___x_3910_;
goto v___jp_3894_;
}
else
{
lean_object* v___x_3923_; 
lean_del_object(v___x_3891_);
lean_dec(v_mvarId_3877_);
lean_dec_ref(v_p_3876_);
lean_inc_ref(v_a_3918_);
if (v_isShared_3906_ == 0)
{
lean_ctor_set(v___x_3905_, 0, v_a_3918_);
v___x_3923_ = v___x_3905_;
goto v_reusejp_3922_;
}
else
{
lean_object* v_reuseFailAlloc_3937_; 
v_reuseFailAlloc_3937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3937_, 0, v_a_3918_);
v___x_3923_ = v_reuseFailAlloc_3937_;
goto v_reusejp_3922_;
}
v_reusejp_3922_:
{
lean_object* v___x_3925_; uint8_t v_isShared_3926_; uint8_t v_isSharedCheck_3935_; 
v_isSharedCheck_3935_ = !lean_is_exclusive(v_a_3918_);
if (v_isSharedCheck_3935_ == 0)
{
lean_object* v_unused_3936_; 
v_unused_3936_ = lean_ctor_get(v_a_3918_, 0);
lean_dec(v_unused_3936_);
v___x_3925_ = v_a_3918_;
v_isShared_3926_ = v_isSharedCheck_3935_;
goto v_resetjp_3924_;
}
else
{
lean_dec(v_a_3918_);
v___x_3925_ = lean_box(0);
v_isShared_3926_ = v_isSharedCheck_3935_;
goto v_resetjp_3924_;
}
v_resetjp_3924_:
{
lean_object* v___x_3927_; lean_object* v___x_3929_; 
v___x_3927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3927_, 0, v___x_3923_);
lean_ctor_set(v___x_3927_, 1, v___x_3909_);
if (v_isShared_3926_ == 0)
{
lean_ctor_set(v___x_3925_, 0, v___x_3927_);
v___x_3929_ = v___x_3925_;
goto v_reusejp_3928_;
}
else
{
lean_object* v_reuseFailAlloc_3934_; 
v_reuseFailAlloc_3934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3934_, 0, v___x_3927_);
v___x_3929_ = v_reuseFailAlloc_3934_;
goto v_reusejp_3928_;
}
v_reusejp_3928_:
{
lean_object* v___x_3930_; lean_object* v___x_3932_; 
v___x_3930_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3930_, 0, v___x_3929_);
lean_ctor_set(v___x_3930_, 1, v_snd_3889_);
if (v_isShared_3921_ == 0)
{
lean_ctor_set(v___x_3920_, 0, v___x_3930_);
v___x_3932_ = v___x_3920_;
goto v_reusejp_3931_;
}
else
{
lean_object* v_reuseFailAlloc_3933_; 
v_reuseFailAlloc_3933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3933_, 0, v___x_3930_);
v___x_3932_ = v_reuseFailAlloc_3933_;
goto v_reusejp_3931_;
}
v_reusejp_3931_:
{
return v___x_3932_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3939_; lean_object* v___x_3941_; uint8_t v_isShared_3942_; uint8_t v_isSharedCheck_3946_; 
lean_del_object(v___x_3905_);
lean_del_object(v___x_3891_);
lean_dec(v_snd_3889_);
lean_dec(v_mvarId_3877_);
lean_dec_ref(v_p_3876_);
v_a_3939_ = lean_ctor_get(v___x_3917_, 0);
v_isSharedCheck_3946_ = !lean_is_exclusive(v___x_3917_);
if (v_isSharedCheck_3946_ == 0)
{
v___x_3941_ = v___x_3917_;
v_isShared_3942_ = v_isSharedCheck_3946_;
goto v_resetjp_3940_;
}
else
{
lean_inc(v_a_3939_);
lean_dec(v___x_3917_);
v___x_3941_ = lean_box(0);
v_isShared_3942_ = v_isSharedCheck_3946_;
goto v_resetjp_3940_;
}
v_resetjp_3940_:
{
lean_object* v___x_3944_; 
if (v_isShared_3942_ == 0)
{
v___x_3944_ = v___x_3941_;
goto v_reusejp_3943_;
}
else
{
lean_object* v_reuseFailAlloc_3945_; 
v_reuseFailAlloc_3945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3945_, 0, v_a_3939_);
v___x_3944_ = v_reuseFailAlloc_3945_;
goto v_reusejp_3943_;
}
v_reusejp_3943_:
{
return v___x_3944_;
}
}
}
}
}
else
{
lean_object* v_a_3947_; lean_object* v___x_3949_; uint8_t v_isShared_3950_; uint8_t v_isSharedCheck_3954_; 
lean_del_object(v___x_3905_);
lean_dec(v_val_3903_);
lean_del_object(v___x_3891_);
lean_dec(v_snd_3889_);
lean_dec(v_mvarId_3877_);
lean_dec_ref(v_p_3876_);
v_a_3947_ = lean_ctor_get(v___x_3907_, 0);
v_isSharedCheck_3954_ = !lean_is_exclusive(v___x_3907_);
if (v_isSharedCheck_3954_ == 0)
{
v___x_3949_ = v___x_3907_;
v_isShared_3950_ = v_isSharedCheck_3954_;
goto v_resetjp_3948_;
}
else
{
lean_inc(v_a_3947_);
lean_dec(v___x_3907_);
v___x_3949_ = lean_box(0);
v_isShared_3950_ = v_isSharedCheck_3954_;
goto v_resetjp_3948_;
}
v_resetjp_3948_:
{
lean_object* v___x_3952_; 
if (v_isShared_3950_ == 0)
{
v___x_3952_ = v___x_3949_;
goto v_reusejp_3951_;
}
else
{
lean_object* v_reuseFailAlloc_3953_; 
v_reuseFailAlloc_3953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3953_, 0, v_a_3947_);
v___x_3952_ = v_reuseFailAlloc_3953_;
goto v_reusejp_3951_;
}
v_reusejp_3951_:
{
return v___x_3952_;
}
}
}
}
}
v___jp_3894_:
{
lean_object* v___x_3897_; 
if (v_isShared_3892_ == 0)
{
lean_ctor_set(v___x_3891_, 1, v_a_3895_);
lean_ctor_set(v___x_3891_, 0, v___x_3893_);
v___x_3897_ = v___x_3891_;
goto v_reusejp_3896_;
}
else
{
lean_object* v_reuseFailAlloc_3901_; 
v_reuseFailAlloc_3901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3901_, 0, v___x_3893_);
lean_ctor_set(v_reuseFailAlloc_3901_, 1, v_a_3895_);
v___x_3897_ = v_reuseFailAlloc_3901_;
goto v_reusejp_3896_;
}
v_reusejp_3896_:
{
size_t v___x_3898_; size_t v___x_3899_; lean_object* v___x_3900_; 
v___x_3898_ = ((size_t)1ULL);
v___x_3899_ = lean_usize_add(v_i_3880_, v___x_3898_);
v___x_3900_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3_spec__6(v_p_3876_, v_mvarId_3877_, v_as_3878_, v_sz_3879_, v___x_3899_, v___x_3897_, v___y_3882_, v___y_3883_, v___y_3884_, v___y_3885_);
return v___x_3900_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3___boxed(lean_object* v_p_3958_, lean_object* v_mvarId_3959_, lean_object* v_as_3960_, lean_object* v_sz_3961_, lean_object* v_i_3962_, lean_object* v_b_3963_, lean_object* v___y_3964_, lean_object* v___y_3965_, lean_object* v___y_3966_, lean_object* v___y_3967_, lean_object* v___y_3968_){
_start:
{
size_t v_sz_boxed_3969_; size_t v_i_boxed_3970_; lean_object* v_res_3971_; 
v_sz_boxed_3969_ = lean_unbox_usize(v_sz_3961_);
lean_dec(v_sz_3961_);
v_i_boxed_3970_ = lean_unbox_usize(v_i_3962_);
lean_dec(v_i_3962_);
v_res_3971_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3(v_p_3958_, v_mvarId_3959_, v_as_3960_, v_sz_boxed_3969_, v_i_boxed_3970_, v_b_3963_, v___y_3964_, v___y_3965_, v___y_3966_, v___y_3967_);
lean_dec(v___y_3967_);
lean_dec_ref(v___y_3966_);
lean_dec(v___y_3965_);
lean_dec_ref(v___y_3964_);
lean_dec_ref(v_as_3960_);
return v_res_3971_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2(lean_object* v_p_3972_, lean_object* v_mvarId_3973_, lean_object* v_t_3974_, lean_object* v_init_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_, lean_object* v___y_3978_, lean_object* v___y_3979_){
_start:
{
lean_object* v_root_3981_; lean_object* v_tail_3982_; lean_object* v___x_3983_; 
v_root_3981_ = lean_ctor_get(v_t_3974_, 0);
v_tail_3982_ = lean_ctor_get(v_t_3974_, 1);
lean_inc(v_mvarId_3973_);
lean_inc_ref(v_p_3972_);
lean_inc_ref(v_init_3975_);
v___x_3983_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2(v_init_3975_, v_p_3972_, v_mvarId_3973_, v_root_3981_, v_init_3975_, v___y_3976_, v___y_3977_, v___y_3978_, v___y_3979_);
lean_dec_ref(v_init_3975_);
if (lean_obj_tag(v___x_3983_) == 0)
{
lean_object* v_a_3984_; lean_object* v___x_3986_; uint8_t v_isShared_3987_; uint8_t v_isSharedCheck_4020_; 
v_a_3984_ = lean_ctor_get(v___x_3983_, 0);
v_isSharedCheck_4020_ = !lean_is_exclusive(v___x_3983_);
if (v_isSharedCheck_4020_ == 0)
{
v___x_3986_ = v___x_3983_;
v_isShared_3987_ = v_isSharedCheck_4020_;
goto v_resetjp_3985_;
}
else
{
lean_inc(v_a_3984_);
lean_dec(v___x_3983_);
v___x_3986_ = lean_box(0);
v_isShared_3987_ = v_isSharedCheck_4020_;
goto v_resetjp_3985_;
}
v_resetjp_3985_:
{
if (lean_obj_tag(v_a_3984_) == 0)
{
lean_object* v_a_3988_; lean_object* v___x_3990_; 
lean_dec(v_mvarId_3973_);
lean_dec_ref(v_p_3972_);
v_a_3988_ = lean_ctor_get(v_a_3984_, 0);
lean_inc(v_a_3988_);
lean_dec_ref_known(v_a_3984_, 1);
if (v_isShared_3987_ == 0)
{
lean_ctor_set(v___x_3986_, 0, v_a_3988_);
v___x_3990_ = v___x_3986_;
goto v_reusejp_3989_;
}
else
{
lean_object* v_reuseFailAlloc_3991_; 
v_reuseFailAlloc_3991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3991_, 0, v_a_3988_);
v___x_3990_ = v_reuseFailAlloc_3991_;
goto v_reusejp_3989_;
}
v_reusejp_3989_:
{
return v___x_3990_;
}
}
else
{
lean_object* v_a_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; size_t v_sz_3995_; size_t v___x_3996_; lean_object* v___x_3997_; 
lean_del_object(v___x_3986_);
v_a_3992_ = lean_ctor_get(v_a_3984_, 0);
lean_inc(v_a_3992_);
lean_dec_ref_known(v_a_3984_, 1);
v___x_3993_ = lean_box(0);
v___x_3994_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3994_, 0, v___x_3993_);
lean_ctor_set(v___x_3994_, 1, v_a_3992_);
v_sz_3995_ = lean_array_size(v_tail_3982_);
v___x_3996_ = ((size_t)0ULL);
v___x_3997_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3(v_p_3972_, v_mvarId_3973_, v_tail_3982_, v_sz_3995_, v___x_3996_, v___x_3994_, v___y_3976_, v___y_3977_, v___y_3978_, v___y_3979_);
if (lean_obj_tag(v___x_3997_) == 0)
{
lean_object* v_a_3998_; lean_object* v___x_4000_; uint8_t v_isShared_4001_; uint8_t v_isSharedCheck_4011_; 
v_a_3998_ = lean_ctor_get(v___x_3997_, 0);
v_isSharedCheck_4011_ = !lean_is_exclusive(v___x_3997_);
if (v_isSharedCheck_4011_ == 0)
{
v___x_4000_ = v___x_3997_;
v_isShared_4001_ = v_isSharedCheck_4011_;
goto v_resetjp_3999_;
}
else
{
lean_inc(v_a_3998_);
lean_dec(v___x_3997_);
v___x_4000_ = lean_box(0);
v_isShared_4001_ = v_isSharedCheck_4011_;
goto v_resetjp_3999_;
}
v_resetjp_3999_:
{
lean_object* v_fst_4002_; 
v_fst_4002_ = lean_ctor_get(v_a_3998_, 0);
if (lean_obj_tag(v_fst_4002_) == 0)
{
lean_object* v_snd_4003_; lean_object* v___x_4005_; 
v_snd_4003_ = lean_ctor_get(v_a_3998_, 1);
lean_inc(v_snd_4003_);
lean_dec(v_a_3998_);
if (v_isShared_4001_ == 0)
{
lean_ctor_set(v___x_4000_, 0, v_snd_4003_);
v___x_4005_ = v___x_4000_;
goto v_reusejp_4004_;
}
else
{
lean_object* v_reuseFailAlloc_4006_; 
v_reuseFailAlloc_4006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4006_, 0, v_snd_4003_);
v___x_4005_ = v_reuseFailAlloc_4006_;
goto v_reusejp_4004_;
}
v_reusejp_4004_:
{
return v___x_4005_;
}
}
else
{
lean_object* v_val_4007_; lean_object* v___x_4009_; 
lean_inc_ref(v_fst_4002_);
lean_dec(v_a_3998_);
v_val_4007_ = lean_ctor_get(v_fst_4002_, 0);
lean_inc(v_val_4007_);
lean_dec_ref_known(v_fst_4002_, 1);
if (v_isShared_4001_ == 0)
{
lean_ctor_set(v___x_4000_, 0, v_val_4007_);
v___x_4009_ = v___x_4000_;
goto v_reusejp_4008_;
}
else
{
lean_object* v_reuseFailAlloc_4010_; 
v_reuseFailAlloc_4010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4010_, 0, v_val_4007_);
v___x_4009_ = v_reuseFailAlloc_4010_;
goto v_reusejp_4008_;
}
v_reusejp_4008_:
{
return v___x_4009_;
}
}
}
}
else
{
lean_object* v_a_4012_; lean_object* v___x_4014_; uint8_t v_isShared_4015_; uint8_t v_isSharedCheck_4019_; 
v_a_4012_ = lean_ctor_get(v___x_3997_, 0);
v_isSharedCheck_4019_ = !lean_is_exclusive(v___x_3997_);
if (v_isSharedCheck_4019_ == 0)
{
v___x_4014_ = v___x_3997_;
v_isShared_4015_ = v_isSharedCheck_4019_;
goto v_resetjp_4013_;
}
else
{
lean_inc(v_a_4012_);
lean_dec(v___x_3997_);
v___x_4014_ = lean_box(0);
v_isShared_4015_ = v_isSharedCheck_4019_;
goto v_resetjp_4013_;
}
v_resetjp_4013_:
{
lean_object* v___x_4017_; 
if (v_isShared_4015_ == 0)
{
v___x_4017_ = v___x_4014_;
goto v_reusejp_4016_;
}
else
{
lean_object* v_reuseFailAlloc_4018_; 
v_reuseFailAlloc_4018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4018_, 0, v_a_4012_);
v___x_4017_ = v_reuseFailAlloc_4018_;
goto v_reusejp_4016_;
}
v_reusejp_4016_:
{
return v___x_4017_;
}
}
}
}
}
}
else
{
lean_object* v_a_4021_; lean_object* v___x_4023_; uint8_t v_isShared_4024_; uint8_t v_isSharedCheck_4028_; 
lean_dec(v_mvarId_3973_);
lean_dec_ref(v_p_3972_);
v_a_4021_ = lean_ctor_get(v___x_3983_, 0);
v_isSharedCheck_4028_ = !lean_is_exclusive(v___x_3983_);
if (v_isSharedCheck_4028_ == 0)
{
v___x_4023_ = v___x_3983_;
v_isShared_4024_ = v_isSharedCheck_4028_;
goto v_resetjp_4022_;
}
else
{
lean_inc(v_a_4021_);
lean_dec(v___x_3983_);
v___x_4023_ = lean_box(0);
v_isShared_4024_ = v_isSharedCheck_4028_;
goto v_resetjp_4022_;
}
v_resetjp_4022_:
{
lean_object* v___x_4026_; 
if (v_isShared_4024_ == 0)
{
v___x_4026_ = v___x_4023_;
goto v_reusejp_4025_;
}
else
{
lean_object* v_reuseFailAlloc_4027_; 
v_reuseFailAlloc_4027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4027_, 0, v_a_4021_);
v___x_4026_ = v_reuseFailAlloc_4027_;
goto v_reusejp_4025_;
}
v_reusejp_4025_:
{
return v___x_4026_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2___boxed(lean_object* v_p_4029_, lean_object* v_mvarId_4030_, lean_object* v_t_4031_, lean_object* v_init_4032_, lean_object* v___y_4033_, lean_object* v___y_4034_, lean_object* v___y_4035_, lean_object* v___y_4036_, lean_object* v___y_4037_){
_start:
{
lean_object* v_res_4038_; 
v_res_4038_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2(v_p_4029_, v_mvarId_4030_, v_t_4031_, v_init_4032_, v___y_4033_, v___y_4034_, v___y_4035_, v___y_4036_);
lean_dec(v___y_4036_);
lean_dec_ref(v___y_4035_);
lean_dec(v___y_4034_);
lean_dec_ref(v___y_4033_);
lean_dec_ref(v_t_4031_);
return v_res_4038_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesRec___lam__0(lean_object* v_p_4042_, lean_object* v_mvarId_4043_, lean_object* v___y_4044_, lean_object* v___y_4045_, lean_object* v___y_4046_, lean_object* v___y_4047_){
_start:
{
lean_object* v_lctx_4049_; lean_object* v_decls_4050_; lean_object* v___x_4051_; lean_object* v___x_4052_; lean_object* v___x_4053_; 
v_lctx_4049_ = lean_ctor_get(v___y_4044_, 2);
v_decls_4050_ = lean_ctor_get(v_lctx_4049_, 1);
v___x_4051_ = lean_box(0);
v___x_4052_ = ((lean_object*)(l_Lean_MVarId_casesRec___lam__0___closed__0));
v___x_4053_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2(v_p_4042_, v_mvarId_4043_, v_decls_4050_, v___x_4052_, v___y_4044_, v___y_4045_, v___y_4046_, v___y_4047_);
if (lean_obj_tag(v___x_4053_) == 0)
{
lean_object* v_a_4054_; lean_object* v___x_4056_; uint8_t v_isShared_4057_; uint8_t v_isSharedCheck_4066_; 
v_a_4054_ = lean_ctor_get(v___x_4053_, 0);
v_isSharedCheck_4066_ = !lean_is_exclusive(v___x_4053_);
if (v_isSharedCheck_4066_ == 0)
{
v___x_4056_ = v___x_4053_;
v_isShared_4057_ = v_isSharedCheck_4066_;
goto v_resetjp_4055_;
}
else
{
lean_inc(v_a_4054_);
lean_dec(v___x_4053_);
v___x_4056_ = lean_box(0);
v_isShared_4057_ = v_isSharedCheck_4066_;
goto v_resetjp_4055_;
}
v_resetjp_4055_:
{
lean_object* v_fst_4058_; 
v_fst_4058_ = lean_ctor_get(v_a_4054_, 0);
lean_inc(v_fst_4058_);
lean_dec(v_a_4054_);
if (lean_obj_tag(v_fst_4058_) == 0)
{
lean_object* v___x_4060_; 
if (v_isShared_4057_ == 0)
{
lean_ctor_set(v___x_4056_, 0, v___x_4051_);
v___x_4060_ = v___x_4056_;
goto v_reusejp_4059_;
}
else
{
lean_object* v_reuseFailAlloc_4061_; 
v_reuseFailAlloc_4061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4061_, 0, v___x_4051_);
v___x_4060_ = v_reuseFailAlloc_4061_;
goto v_reusejp_4059_;
}
v_reusejp_4059_:
{
return v___x_4060_;
}
}
else
{
lean_object* v_val_4062_; lean_object* v___x_4064_; 
v_val_4062_ = lean_ctor_get(v_fst_4058_, 0);
lean_inc(v_val_4062_);
lean_dec_ref_known(v_fst_4058_, 1);
if (v_isShared_4057_ == 0)
{
lean_ctor_set(v___x_4056_, 0, v_val_4062_);
v___x_4064_ = v___x_4056_;
goto v_reusejp_4063_;
}
else
{
lean_object* v_reuseFailAlloc_4065_; 
v_reuseFailAlloc_4065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4065_, 0, v_val_4062_);
v___x_4064_ = v_reuseFailAlloc_4065_;
goto v_reusejp_4063_;
}
v_reusejp_4063_:
{
return v___x_4064_;
}
}
}
}
else
{
lean_object* v_a_4067_; lean_object* v___x_4069_; uint8_t v_isShared_4070_; uint8_t v_isSharedCheck_4074_; 
v_a_4067_ = lean_ctor_get(v___x_4053_, 0);
v_isSharedCheck_4074_ = !lean_is_exclusive(v___x_4053_);
if (v_isSharedCheck_4074_ == 0)
{
v___x_4069_ = v___x_4053_;
v_isShared_4070_ = v_isSharedCheck_4074_;
goto v_resetjp_4068_;
}
else
{
lean_inc(v_a_4067_);
lean_dec(v___x_4053_);
v___x_4069_ = lean_box(0);
v_isShared_4070_ = v_isSharedCheck_4074_;
goto v_resetjp_4068_;
}
v_resetjp_4068_:
{
lean_object* v___x_4072_; 
if (v_isShared_4070_ == 0)
{
v___x_4072_ = v___x_4069_;
goto v_reusejp_4071_;
}
else
{
lean_object* v_reuseFailAlloc_4073_; 
v_reuseFailAlloc_4073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4073_, 0, v_a_4067_);
v___x_4072_ = v_reuseFailAlloc_4073_;
goto v_reusejp_4071_;
}
v_reusejp_4071_:
{
return v___x_4072_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesRec___lam__0___boxed(lean_object* v_p_4075_, lean_object* v_mvarId_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_, lean_object* v___y_4079_, lean_object* v___y_4080_, lean_object* v___y_4081_){
_start:
{
lean_object* v_res_4082_; 
v_res_4082_ = l_Lean_MVarId_casesRec___lam__0(v_p_4075_, v_mvarId_4076_, v___y_4077_, v___y_4078_, v___y_4079_, v___y_4080_);
lean_dec(v___y_4080_);
lean_dec_ref(v___y_4079_);
lean_dec(v___y_4078_);
lean_dec_ref(v___y_4077_);
return v_res_4082_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesRec___lam__1(lean_object* v_p_4083_, lean_object* v_mvarId_4084_, lean_object* v___y_4085_, lean_object* v___y_4086_, lean_object* v___y_4087_, lean_object* v___y_4088_){
_start:
{
lean_object* v___f_4090_; lean_object* v___x_4091_; 
lean_inc(v_mvarId_4084_);
v___f_4090_ = lean_alloc_closure((void*)(l_Lean_MVarId_casesRec___lam__0___boxed), 7, 2);
lean_closure_set(v___f_4090_, 0, v_p_4083_);
lean_closure_set(v___f_4090_, 1, v_mvarId_4084_);
v___x_4091_ = l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2___redArg(v_mvarId_4084_, v___f_4090_, v___y_4085_, v___y_4086_, v___y_4087_, v___y_4088_);
return v___x_4091_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesRec___lam__1___boxed(lean_object* v_p_4092_, lean_object* v_mvarId_4093_, lean_object* v___y_4094_, lean_object* v___y_4095_, lean_object* v___y_4096_, lean_object* v___y_4097_, lean_object* v___y_4098_){
_start:
{
lean_object* v_res_4099_; 
v_res_4099_ = l_Lean_MVarId_casesRec___lam__1(v_p_4092_, v_mvarId_4093_, v___y_4094_, v___y_4095_, v___y_4096_, v___y_4097_);
lean_dec(v___y_4097_);
lean_dec_ref(v___y_4096_);
lean_dec(v___y_4095_);
lean_dec_ref(v___y_4094_);
return v_res_4099_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesRec(lean_object* v_mvarId_4100_, lean_object* v_p_4101_, lean_object* v_a_4102_, lean_object* v_a_4103_, lean_object* v_a_4104_, lean_object* v_a_4105_){
_start:
{
lean_object* v___f_4107_; lean_object* v___x_4108_; 
v___f_4107_ = lean_alloc_closure((void*)(l_Lean_MVarId_casesRec___lam__1___boxed), 7, 1);
lean_closure_set(v___f_4107_, 0, v_p_4101_);
v___x_4108_ = l_Lean_Meta_saturate(v_mvarId_4100_, v___f_4107_, v_a_4102_, v_a_4103_, v_a_4104_, v_a_4105_);
return v___x_4108_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesRec___boxed(lean_object* v_mvarId_4109_, lean_object* v_p_4110_, lean_object* v_a_4111_, lean_object* v_a_4112_, lean_object* v_a_4113_, lean_object* v_a_4114_, lean_object* v_a_4115_){
_start:
{
lean_object* v_res_4116_; 
v_res_4116_ = l_Lean_MVarId_casesRec(v_mvarId_4109_, v_p_4110_, v_a_4111_, v_a_4112_, v_a_4113_, v_a_4114_);
lean_dec(v_a_4114_);
lean_dec_ref(v_a_4113_);
lean_dec(v_a_4112_);
lean_dec_ref(v_a_4111_);
return v_res_4116_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0___redArg(lean_object* v_e_4117_, lean_object* v___y_4118_){
_start:
{
uint8_t v___x_4120_; 
v___x_4120_ = l_Lean_Expr_hasMVar(v_e_4117_);
if (v___x_4120_ == 0)
{
lean_object* v___x_4121_; 
v___x_4121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4121_, 0, v_e_4117_);
return v___x_4121_;
}
else
{
lean_object* v___x_4122_; lean_object* v_mctx_4123_; lean_object* v___x_4124_; lean_object* v_fst_4125_; lean_object* v_snd_4126_; lean_object* v___x_4127_; lean_object* v_cache_4128_; lean_object* v_zetaDeltaFVarIds_4129_; lean_object* v_postponed_4130_; lean_object* v_diag_4131_; lean_object* v___x_4133_; uint8_t v_isShared_4134_; uint8_t v_isSharedCheck_4140_; 
v___x_4122_ = lean_st_ref_get(v___y_4118_);
v_mctx_4123_ = lean_ctor_get(v___x_4122_, 0);
lean_inc_ref(v_mctx_4123_);
lean_dec(v___x_4122_);
v___x_4124_ = l_Lean_instantiateMVarsCore(v_mctx_4123_, v_e_4117_);
v_fst_4125_ = lean_ctor_get(v___x_4124_, 0);
lean_inc(v_fst_4125_);
v_snd_4126_ = lean_ctor_get(v___x_4124_, 1);
lean_inc(v_snd_4126_);
lean_dec_ref(v___x_4124_);
v___x_4127_ = lean_st_ref_take(v___y_4118_);
v_cache_4128_ = lean_ctor_get(v___x_4127_, 1);
v_zetaDeltaFVarIds_4129_ = lean_ctor_get(v___x_4127_, 2);
v_postponed_4130_ = lean_ctor_get(v___x_4127_, 3);
v_diag_4131_ = lean_ctor_get(v___x_4127_, 4);
v_isSharedCheck_4140_ = !lean_is_exclusive(v___x_4127_);
if (v_isSharedCheck_4140_ == 0)
{
lean_object* v_unused_4141_; 
v_unused_4141_ = lean_ctor_get(v___x_4127_, 0);
lean_dec(v_unused_4141_);
v___x_4133_ = v___x_4127_;
v_isShared_4134_ = v_isSharedCheck_4140_;
goto v_resetjp_4132_;
}
else
{
lean_inc(v_diag_4131_);
lean_inc(v_postponed_4130_);
lean_inc(v_zetaDeltaFVarIds_4129_);
lean_inc(v_cache_4128_);
lean_dec(v___x_4127_);
v___x_4133_ = lean_box(0);
v_isShared_4134_ = v_isSharedCheck_4140_;
goto v_resetjp_4132_;
}
v_resetjp_4132_:
{
lean_object* v___x_4136_; 
if (v_isShared_4134_ == 0)
{
lean_ctor_set(v___x_4133_, 0, v_snd_4126_);
v___x_4136_ = v___x_4133_;
goto v_reusejp_4135_;
}
else
{
lean_object* v_reuseFailAlloc_4139_; 
v_reuseFailAlloc_4139_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4139_, 0, v_snd_4126_);
lean_ctor_set(v_reuseFailAlloc_4139_, 1, v_cache_4128_);
lean_ctor_set(v_reuseFailAlloc_4139_, 2, v_zetaDeltaFVarIds_4129_);
lean_ctor_set(v_reuseFailAlloc_4139_, 3, v_postponed_4130_);
lean_ctor_set(v_reuseFailAlloc_4139_, 4, v_diag_4131_);
v___x_4136_ = v_reuseFailAlloc_4139_;
goto v_reusejp_4135_;
}
v_reusejp_4135_:
{
lean_object* v___x_4137_; lean_object* v___x_4138_; 
v___x_4137_ = lean_st_ref_put(v___y_4118_, v___x_4136_);
v___x_4138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4138_, 0, v_fst_4125_);
return v___x_4138_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0___redArg___boxed(lean_object* v_e_4142_, lean_object* v___y_4143_, lean_object* v___y_4144_){
_start:
{
lean_object* v_res_4145_; 
v_res_4145_ = l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0___redArg(v_e_4142_, v___y_4143_);
lean_dec(v___y_4143_);
return v_res_4145_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0(lean_object* v_e_4146_, lean_object* v___y_4147_, lean_object* v___y_4148_, lean_object* v___y_4149_, lean_object* v___y_4150_){
_start:
{
lean_object* v___x_4152_; 
v___x_4152_ = l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0___redArg(v_e_4146_, v___y_4148_);
return v___x_4152_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0___boxed(lean_object* v_e_4153_, lean_object* v___y_4154_, lean_object* v___y_4155_, lean_object* v___y_4156_, lean_object* v___y_4157_, lean_object* v___y_4158_){
_start:
{
lean_object* v_res_4159_; 
v_res_4159_ = l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0(v_e_4153_, v___y_4154_, v___y_4155_, v___y_4156_, v___y_4157_);
lean_dec(v___y_4157_);
lean_dec_ref(v___y_4156_);
lean_dec(v___y_4155_);
lean_dec_ref(v___y_4154_);
return v_res_4159_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesAnd___lam__0(lean_object* v_localDecl_4163_, lean_object* v___y_4164_, lean_object* v___y_4165_, lean_object* v___y_4166_, lean_object* v___y_4167_){
_start:
{
lean_object* v___x_4169_; lean_object* v___x_4170_; lean_object* v_a_4171_; lean_object* v___x_4173_; uint8_t v_isShared_4174_; uint8_t v_isSharedCheck_4182_; 
v___x_4169_ = l_Lean_LocalDecl_type(v_localDecl_4163_);
v___x_4170_ = l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0___redArg(v___x_4169_, v___y_4165_);
v_a_4171_ = lean_ctor_get(v___x_4170_, 0);
v_isSharedCheck_4182_ = !lean_is_exclusive(v___x_4170_);
if (v_isSharedCheck_4182_ == 0)
{
v___x_4173_ = v___x_4170_;
v_isShared_4174_ = v_isSharedCheck_4182_;
goto v_resetjp_4172_;
}
else
{
lean_inc(v_a_4171_);
lean_dec(v___x_4170_);
v___x_4173_ = lean_box(0);
v_isShared_4174_ = v_isSharedCheck_4182_;
goto v_resetjp_4172_;
}
v_resetjp_4172_:
{
lean_object* v___x_4175_; lean_object* v___x_4176_; uint8_t v___x_4177_; lean_object* v___x_4178_; lean_object* v___x_4180_; 
v___x_4175_ = ((lean_object*)(l_Lean_MVarId_casesAnd___lam__0___closed__1));
v___x_4176_ = lean_unsigned_to_nat(2u);
v___x_4177_ = l_Lean_Expr_isAppOfArity(v_a_4171_, v___x_4175_, v___x_4176_);
lean_dec(v_a_4171_);
v___x_4178_ = lean_box(v___x_4177_);
if (v_isShared_4174_ == 0)
{
lean_ctor_set(v___x_4173_, 0, v___x_4178_);
v___x_4180_ = v___x_4173_;
goto v_reusejp_4179_;
}
else
{
lean_object* v_reuseFailAlloc_4181_; 
v_reuseFailAlloc_4181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4181_, 0, v___x_4178_);
v___x_4180_ = v_reuseFailAlloc_4181_;
goto v_reusejp_4179_;
}
v_reusejp_4179_:
{
return v___x_4180_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesAnd___lam__0___boxed(lean_object* v_localDecl_4183_, lean_object* v___y_4184_, lean_object* v___y_4185_, lean_object* v___y_4186_, lean_object* v___y_4187_, lean_object* v___y_4188_){
_start:
{
lean_object* v_res_4189_; 
v_res_4189_ = l_Lean_MVarId_casesAnd___lam__0(v_localDecl_4183_, v___y_4184_, v___y_4185_, v___y_4186_, v___y_4187_);
lean_dec(v___y_4187_);
lean_dec_ref(v___y_4186_);
lean_dec(v___y_4185_);
lean_dec_ref(v___y_4184_);
lean_dec_ref(v_localDecl_4183_);
return v_res_4189_;
}
}
static lean_object* _init_l_Lean_MVarId_casesAnd___closed__3(void){
_start:
{
lean_object* v___x_4194_; lean_object* v___x_4195_; 
v___x_4194_ = ((lean_object*)(l_Lean_MVarId_casesAnd___closed__2));
v___x_4195_ = l_Lean_MessageData_ofFormat(v___x_4194_);
return v___x_4195_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesAnd(lean_object* v_mvarId_4196_, lean_object* v_a_4197_, lean_object* v_a_4198_, lean_object* v_a_4199_, lean_object* v_a_4200_){
_start:
{
lean_object* v___f_4202_; lean_object* v___x_4203_; 
v___f_4202_ = ((lean_object*)(l_Lean_MVarId_casesAnd___closed__0));
v___x_4203_ = l_Lean_MVarId_casesRec(v_mvarId_4196_, v___f_4202_, v_a_4197_, v_a_4198_, v_a_4199_, v_a_4200_);
if (lean_obj_tag(v___x_4203_) == 0)
{
lean_object* v_a_4204_; lean_object* v___x_4205_; lean_object* v___x_4206_; 
v_a_4204_ = lean_ctor_get(v___x_4203_, 0);
lean_inc(v_a_4204_);
lean_dec_ref_known(v___x_4203_, 1);
v___x_4205_ = lean_obj_once(&l_Lean_MVarId_casesAnd___closed__3, &l_Lean_MVarId_casesAnd___closed__3_once, _init_l_Lean_MVarId_casesAnd___closed__3);
v___x_4206_ = l_Lean_Meta_exactlyOne(v_a_4204_, v___x_4205_, v_a_4197_, v_a_4198_, v_a_4199_, v_a_4200_);
lean_dec(v_a_4204_);
return v___x_4206_;
}
else
{
lean_object* v_a_4207_; lean_object* v___x_4209_; uint8_t v_isShared_4210_; uint8_t v_isSharedCheck_4214_; 
v_a_4207_ = lean_ctor_get(v___x_4203_, 0);
v_isSharedCheck_4214_ = !lean_is_exclusive(v___x_4203_);
if (v_isSharedCheck_4214_ == 0)
{
v___x_4209_ = v___x_4203_;
v_isShared_4210_ = v_isSharedCheck_4214_;
goto v_resetjp_4208_;
}
else
{
lean_inc(v_a_4207_);
lean_dec(v___x_4203_);
v___x_4209_ = lean_box(0);
v_isShared_4210_ = v_isSharedCheck_4214_;
goto v_resetjp_4208_;
}
v_resetjp_4208_:
{
lean_object* v___x_4212_; 
if (v_isShared_4210_ == 0)
{
v___x_4212_ = v___x_4209_;
goto v_reusejp_4211_;
}
else
{
lean_object* v_reuseFailAlloc_4213_; 
v_reuseFailAlloc_4213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4213_, 0, v_a_4207_);
v___x_4212_ = v_reuseFailAlloc_4213_;
goto v_reusejp_4211_;
}
v_reusejp_4211_:
{
return v___x_4212_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesAnd___boxed(lean_object* v_mvarId_4215_, lean_object* v_a_4216_, lean_object* v_a_4217_, lean_object* v_a_4218_, lean_object* v_a_4219_, lean_object* v_a_4220_){
_start:
{
lean_object* v_res_4221_; 
v_res_4221_ = l_Lean_MVarId_casesAnd(v_mvarId_4215_, v_a_4216_, v_a_4217_, v_a_4218_, v_a_4219_);
lean_dec(v_a_4219_);
lean_dec_ref(v_a_4218_);
lean_dec(v_a_4217_);
lean_dec_ref(v_a_4216_);
return v_res_4221_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_substEqs___lam__0(lean_object* v_localDecl_4222_, lean_object* v___y_4223_, lean_object* v___y_4224_, lean_object* v___y_4225_, lean_object* v___y_4226_){
_start:
{
lean_object* v___x_4228_; lean_object* v___x_4229_; lean_object* v_a_4230_; lean_object* v___x_4232_; uint8_t v_isShared_4233_; uint8_t v_isSharedCheck_4244_; 
v___x_4228_ = l_Lean_LocalDecl_type(v_localDecl_4222_);
v___x_4229_ = l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0___redArg(v___x_4228_, v___y_4224_);
v_a_4230_ = lean_ctor_get(v___x_4229_, 0);
v_isSharedCheck_4244_ = !lean_is_exclusive(v___x_4229_);
if (v_isSharedCheck_4244_ == 0)
{
v___x_4232_ = v___x_4229_;
v_isShared_4233_ = v_isSharedCheck_4244_;
goto v_resetjp_4231_;
}
else
{
lean_inc(v_a_4230_);
lean_dec(v___x_4229_);
v___x_4232_ = lean_box(0);
v_isShared_4233_ = v_isSharedCheck_4244_;
goto v_resetjp_4231_;
}
v_resetjp_4231_:
{
uint8_t v___x_4234_; 
v___x_4234_ = l_Lean_Expr_isEq(v_a_4230_);
if (v___x_4234_ == 0)
{
uint8_t v___x_4235_; lean_object* v___x_4236_; lean_object* v___x_4238_; 
v___x_4235_ = l_Lean_Expr_isHEq(v_a_4230_);
lean_dec(v_a_4230_);
v___x_4236_ = lean_box(v___x_4235_);
if (v_isShared_4233_ == 0)
{
lean_ctor_set(v___x_4232_, 0, v___x_4236_);
v___x_4238_ = v___x_4232_;
goto v_reusejp_4237_;
}
else
{
lean_object* v_reuseFailAlloc_4239_; 
v_reuseFailAlloc_4239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4239_, 0, v___x_4236_);
v___x_4238_ = v_reuseFailAlloc_4239_;
goto v_reusejp_4237_;
}
v_reusejp_4237_:
{
return v___x_4238_;
}
}
else
{
lean_object* v___x_4240_; lean_object* v___x_4242_; 
lean_dec(v_a_4230_);
v___x_4240_ = lean_box(v___x_4234_);
if (v_isShared_4233_ == 0)
{
lean_ctor_set(v___x_4232_, 0, v___x_4240_);
v___x_4242_ = v___x_4232_;
goto v_reusejp_4241_;
}
else
{
lean_object* v_reuseFailAlloc_4243_; 
v_reuseFailAlloc_4243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4243_, 0, v___x_4240_);
v___x_4242_ = v_reuseFailAlloc_4243_;
goto v_reusejp_4241_;
}
v_reusejp_4241_:
{
return v___x_4242_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_substEqs___lam__0___boxed(lean_object* v_localDecl_4245_, lean_object* v___y_4246_, lean_object* v___y_4247_, lean_object* v___y_4248_, lean_object* v___y_4249_, lean_object* v___y_4250_){
_start:
{
lean_object* v_res_4251_; 
v_res_4251_ = l_Lean_MVarId_substEqs___lam__0(v_localDecl_4245_, v___y_4246_, v___y_4247_, v___y_4248_, v___y_4249_);
lean_dec(v___y_4249_);
lean_dec_ref(v___y_4248_);
lean_dec(v___y_4247_);
lean_dec_ref(v___y_4246_);
lean_dec_ref(v_localDecl_4245_);
return v_res_4251_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_substEqs(lean_object* v_mvarId_4253_, lean_object* v_a_4254_, lean_object* v_a_4255_, lean_object* v_a_4256_, lean_object* v_a_4257_){
_start:
{
lean_object* v___f_4259_; lean_object* v___x_4260_; 
v___f_4259_ = ((lean_object*)(l_Lean_MVarId_substEqs___closed__0));
v___x_4260_ = l_Lean_MVarId_casesRec(v_mvarId_4253_, v___f_4259_, v_a_4254_, v_a_4255_, v_a_4256_, v_a_4257_);
if (lean_obj_tag(v___x_4260_) == 0)
{
lean_object* v_a_4261_; lean_object* v___x_4262_; lean_object* v___x_4263_; 
v_a_4261_ = lean_ctor_get(v___x_4260_, 0);
lean_inc(v_a_4261_);
lean_dec_ref_known(v___x_4260_, 1);
v___x_4262_ = lean_obj_once(&l_Lean_MVarId_casesAnd___closed__3, &l_Lean_MVarId_casesAnd___closed__3_once, _init_l_Lean_MVarId_casesAnd___closed__3);
v___x_4263_ = l_Lean_Meta_ensureAtMostOne(v_a_4261_, v___x_4262_, v_a_4254_, v_a_4255_, v_a_4256_, v_a_4257_);
lean_dec(v_a_4261_);
return v___x_4263_;
}
else
{
lean_object* v_a_4264_; lean_object* v___x_4266_; uint8_t v_isShared_4267_; uint8_t v_isSharedCheck_4271_; 
v_a_4264_ = lean_ctor_get(v___x_4260_, 0);
v_isSharedCheck_4271_ = !lean_is_exclusive(v___x_4260_);
if (v_isSharedCheck_4271_ == 0)
{
v___x_4266_ = v___x_4260_;
v_isShared_4267_ = v_isSharedCheck_4271_;
goto v_resetjp_4265_;
}
else
{
lean_inc(v_a_4264_);
lean_dec(v___x_4260_);
v___x_4266_ = lean_box(0);
v_isShared_4267_ = v_isSharedCheck_4271_;
goto v_resetjp_4265_;
}
v_resetjp_4265_:
{
lean_object* v___x_4269_; 
if (v_isShared_4267_ == 0)
{
v___x_4269_ = v___x_4266_;
goto v_reusejp_4268_;
}
else
{
lean_object* v_reuseFailAlloc_4270_; 
v_reuseFailAlloc_4270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4270_, 0, v_a_4264_);
v___x_4269_ = v_reuseFailAlloc_4270_;
goto v_reusejp_4268_;
}
v_reusejp_4268_:
{
return v___x_4269_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_substEqs___boxed(lean_object* v_mvarId_4272_, lean_object* v_a_4273_, lean_object* v_a_4274_, lean_object* v_a_4275_, lean_object* v_a_4276_, lean_object* v_a_4277_){
_start:
{
lean_object* v_res_4278_; 
v_res_4278_ = l_Lean_MVarId_substEqs(v_mvarId_4272_, v_a_4273_, v_a_4274_, v_a_4275_, v_a_4276_);
lean_dec(v_a_4276_);
lean_dec_ref(v_a_4275_);
lean_dec(v_a_4274_);
lean_dec_ref(v_a_4273_);
return v_res_4278_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkByCasesSubgoal___lam__0(lean_object* v_goalType_4279_, lean_object* v_tag_4280_, lean_object* v_hyp_4281_, lean_object* v___y_4282_, lean_object* v___y_4283_, lean_object* v___y_4284_, lean_object* v___y_4285_){
_start:
{
lean_object* v___x_4287_; 
v___x_4287_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_goalType_4279_, v_tag_4280_, v___y_4282_, v___y_4283_, v___y_4284_, v___y_4285_);
if (lean_obj_tag(v___x_4287_) == 0)
{
lean_object* v_a_4288_; lean_object* v___x_4289_; lean_object* v___x_4290_; lean_object* v___x_4291_; uint8_t v___x_4292_; uint8_t v___x_4293_; uint8_t v___x_4294_; lean_object* v___x_4295_; 
v_a_4288_ = lean_ctor_get(v___x_4287_, 0);
lean_inc_n(v_a_4288_, 2);
lean_dec_ref_known(v___x_4287_, 1);
v___x_4289_ = lean_unsigned_to_nat(1u);
v___x_4290_ = lean_mk_empty_array_with_capacity(v___x_4289_);
lean_inc_ref(v_hyp_4281_);
v___x_4291_ = lean_array_push(v___x_4290_, v_hyp_4281_);
v___x_4292_ = 0;
v___x_4293_ = 1;
v___x_4294_ = 1;
v___x_4295_ = l_Lean_Meta_mkLambdaFVars(v___x_4291_, v_a_4288_, v___x_4292_, v___x_4293_, v___x_4292_, v___x_4293_, v___x_4294_, v___y_4282_, v___y_4283_, v___y_4284_, v___y_4285_);
lean_dec_ref(v___x_4291_);
if (lean_obj_tag(v___x_4295_) == 0)
{
lean_object* v_a_4296_; lean_object* v___x_4298_; uint8_t v_isShared_4299_; uint8_t v_isSharedCheck_4307_; 
v_a_4296_ = lean_ctor_get(v___x_4295_, 0);
v_isSharedCheck_4307_ = !lean_is_exclusive(v___x_4295_);
if (v_isSharedCheck_4307_ == 0)
{
v___x_4298_ = v___x_4295_;
v_isShared_4299_ = v_isSharedCheck_4307_;
goto v_resetjp_4297_;
}
else
{
lean_inc(v_a_4296_);
lean_dec(v___x_4295_);
v___x_4298_ = lean_box(0);
v_isShared_4299_ = v_isSharedCheck_4307_;
goto v_resetjp_4297_;
}
v_resetjp_4297_:
{
lean_object* v___x_4300_; lean_object* v___x_4301_; lean_object* v___x_4302_; lean_object* v___x_4303_; lean_object* v___x_4305_; 
v___x_4300_ = l_Lean_Expr_mvarId_x21(v_a_4288_);
lean_dec(v_a_4288_);
v___x_4301_ = l_Lean_Expr_fvarId_x21(v_hyp_4281_);
lean_dec_ref(v_hyp_4281_);
v___x_4302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4302_, 0, v___x_4300_);
lean_ctor_set(v___x_4302_, 1, v___x_4301_);
v___x_4303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4303_, 0, v_a_4296_);
lean_ctor_set(v___x_4303_, 1, v___x_4302_);
if (v_isShared_4299_ == 0)
{
lean_ctor_set(v___x_4298_, 0, v___x_4303_);
v___x_4305_ = v___x_4298_;
goto v_reusejp_4304_;
}
else
{
lean_object* v_reuseFailAlloc_4306_; 
v_reuseFailAlloc_4306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4306_, 0, v___x_4303_);
v___x_4305_ = v_reuseFailAlloc_4306_;
goto v_reusejp_4304_;
}
v_reusejp_4304_:
{
return v___x_4305_;
}
}
}
else
{
lean_object* v_a_4308_; lean_object* v___x_4310_; uint8_t v_isShared_4311_; uint8_t v_isSharedCheck_4315_; 
lean_dec(v_a_4288_);
lean_dec_ref(v_hyp_4281_);
v_a_4308_ = lean_ctor_get(v___x_4295_, 0);
v_isSharedCheck_4315_ = !lean_is_exclusive(v___x_4295_);
if (v_isSharedCheck_4315_ == 0)
{
v___x_4310_ = v___x_4295_;
v_isShared_4311_ = v_isSharedCheck_4315_;
goto v_resetjp_4309_;
}
else
{
lean_inc(v_a_4308_);
lean_dec(v___x_4295_);
v___x_4310_ = lean_box(0);
v_isShared_4311_ = v_isSharedCheck_4315_;
goto v_resetjp_4309_;
}
v_resetjp_4309_:
{
lean_object* v___x_4313_; 
if (v_isShared_4311_ == 0)
{
v___x_4313_ = v___x_4310_;
goto v_reusejp_4312_;
}
else
{
lean_object* v_reuseFailAlloc_4314_; 
v_reuseFailAlloc_4314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4314_, 0, v_a_4308_);
v___x_4313_ = v_reuseFailAlloc_4314_;
goto v_reusejp_4312_;
}
v_reusejp_4312_:
{
return v___x_4313_;
}
}
}
}
else
{
lean_object* v_a_4316_; lean_object* v___x_4318_; uint8_t v_isShared_4319_; uint8_t v_isSharedCheck_4323_; 
lean_dec_ref(v_hyp_4281_);
v_a_4316_ = lean_ctor_get(v___x_4287_, 0);
v_isSharedCheck_4323_ = !lean_is_exclusive(v___x_4287_);
if (v_isSharedCheck_4323_ == 0)
{
v___x_4318_ = v___x_4287_;
v_isShared_4319_ = v_isSharedCheck_4323_;
goto v_resetjp_4317_;
}
else
{
lean_inc(v_a_4316_);
lean_dec(v___x_4287_);
v___x_4318_ = lean_box(0);
v_isShared_4319_ = v_isSharedCheck_4323_;
goto v_resetjp_4317_;
}
v_resetjp_4317_:
{
lean_object* v___x_4321_; 
if (v_isShared_4319_ == 0)
{
v___x_4321_ = v___x_4318_;
goto v_reusejp_4320_;
}
else
{
lean_object* v_reuseFailAlloc_4322_; 
v_reuseFailAlloc_4322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4322_, 0, v_a_4316_);
v___x_4321_ = v_reuseFailAlloc_4322_;
goto v_reusejp_4320_;
}
v_reusejp_4320_:
{
return v___x_4321_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkByCasesSubgoal___lam__0___boxed(lean_object* v_goalType_4324_, lean_object* v_tag_4325_, lean_object* v_hyp_4326_, lean_object* v___y_4327_, lean_object* v___y_4328_, lean_object* v___y_4329_, lean_object* v___y_4330_, lean_object* v___y_4331_){
_start:
{
lean_object* v_res_4332_; 
v_res_4332_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkByCasesSubgoal___lam__0(v_goalType_4324_, v_tag_4325_, v_hyp_4326_, v___y_4327_, v___y_4328_, v___y_4329_, v___y_4330_);
lean_dec(v___y_4330_);
lean_dec_ref(v___y_4329_);
lean_dec(v___y_4328_);
lean_dec_ref(v___y_4327_);
return v_res_4332_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkByCasesSubgoal(lean_object* v_p_4333_, lean_object* v_hName_4334_, lean_object* v_goalType_4335_, lean_object* v_tag_4336_, lean_object* v_a_4337_, lean_object* v_a_4338_, lean_object* v_a_4339_, lean_object* v_a_4340_){
_start:
{
lean_object* v___f_4342_; lean_object* v___x_4343_; 
v___f_4342_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkByCasesSubgoal___lam__0___boxed), 8, 2);
lean_closure_set(v___f_4342_, 0, v_goalType_4335_);
lean_closure_set(v___f_4342_, 1, v_tag_4336_);
v___x_4343_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0___redArg(v_hName_4334_, v_p_4333_, v___f_4342_, v_a_4337_, v_a_4338_, v_a_4339_, v_a_4340_);
return v___x_4343_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkByCasesSubgoal___boxed(lean_object* v_p_4344_, lean_object* v_hName_4345_, lean_object* v_goalType_4346_, lean_object* v_tag_4347_, lean_object* v_a_4348_, lean_object* v_a_4349_, lean_object* v_a_4350_, lean_object* v_a_4351_, lean_object* v_a_4352_){
_start:
{
lean_object* v_res_4353_; 
v_res_4353_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkByCasesSubgoal(v_p_4344_, v_hName_4345_, v_goalType_4346_, v_tag_4347_, v_a_4348_, v_a_4349_, v_a_4350_, v_a_4351_);
lean_dec(v_a_4351_);
lean_dec_ref(v_a_4350_);
lean_dec(v_a_4349_);
lean_dec_ref(v_a_4348_);
return v_res_4353_;
}
}
static lean_object* _init_l_Lean_MVarId_byCases___lam__0___closed__7(void){
_start:
{
lean_object* v___x_4365_; lean_object* v___x_4366_; lean_object* v___x_4367_; 
v___x_4365_ = lean_box(0);
v___x_4366_ = ((lean_object*)(l_Lean_MVarId_byCases___lam__0___closed__6));
v___x_4367_ = l_Lean_Expr_const___override(v___x_4366_, v___x_4365_);
return v___x_4367_;
}
}
static lean_object* _init_l_Lean_MVarId_byCases___lam__0___closed__10(void){
_start:
{
lean_object* v___x_4371_; lean_object* v___x_4372_; 
v___x_4371_ = ((lean_object*)(l_Lean_MVarId_byCases___lam__0___closed__9));
v___x_4372_ = l_Lean_stringToMessageData(v___x_4371_);
return v___x_4372_;
}
}
static lean_object* _init_l_Lean_MVarId_byCases___lam__0___closed__11(void){
_start:
{
lean_object* v___x_4373_; lean_object* v___x_4374_; 
v___x_4373_ = lean_obj_once(&l_Lean_MVarId_byCases___lam__0___closed__10, &l_Lean_MVarId_byCases___lam__0___closed__10_once, _init_l_Lean_MVarId_byCases___lam__0___closed__10);
v___x_4374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4374_, 0, v___x_4373_);
return v___x_4374_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_byCases___lam__0(lean_object* v_mvarId_4375_, lean_object* v_p_4376_, lean_object* v_hName_4377_, lean_object* v___y_4378_, lean_object* v___y_4379_, lean_object* v___y_4380_, lean_object* v___y_4381_){
_start:
{
lean_object* v___x_4383_; 
lean_inc(v_mvarId_4375_);
v___x_4383_ = l_Lean_MVarId_getType(v_mvarId_4375_, v___y_4378_, v___y_4379_, v___y_4380_, v___y_4381_);
if (lean_obj_tag(v___x_4383_) == 0)
{
lean_object* v_a_4384_; lean_object* v___x_4385_; 
v_a_4384_ = lean_ctor_get(v___x_4383_, 0);
lean_inc(v_a_4384_);
lean_dec_ref_known(v___x_4383_, 1);
lean_inc(v_mvarId_4375_);
v___x_4385_ = l_Lean_MVarId_getTag(v_mvarId_4375_, v___y_4378_, v___y_4379_, v___y_4380_, v___y_4381_);
if (lean_obj_tag(v___x_4385_) == 0)
{
lean_object* v_a_4386_; lean_object* v___y_4388_; lean_object* v___y_4389_; lean_object* v___y_4390_; lean_object* v___y_4391_; lean_object* v___x_4439_; 
v_a_4386_ = lean_ctor_get(v___x_4385_, 0);
lean_inc(v_a_4386_);
lean_dec_ref_known(v___x_4385_, 1);
lean_inc(v_a_4384_);
v___x_4439_ = l_Lean_Meta_isProp(v_a_4384_, v___y_4378_, v___y_4379_, v___y_4380_, v___y_4381_);
if (lean_obj_tag(v___x_4439_) == 0)
{
lean_object* v_a_4440_; uint8_t v___x_4441_; 
v_a_4440_ = lean_ctor_get(v___x_4439_, 0);
lean_inc(v_a_4440_);
lean_dec_ref_known(v___x_4439_, 1);
v___x_4441_ = lean_unbox(v_a_4440_);
lean_dec(v_a_4440_);
if (v___x_4441_ == 0)
{
lean_object* v___x_4442_; lean_object* v___x_4443_; lean_object* v___x_4444_; 
v___x_4442_ = ((lean_object*)(l_Lean_MVarId_byCases___lam__0___closed__8));
v___x_4443_ = lean_obj_once(&l_Lean_MVarId_byCases___lam__0___closed__11, &l_Lean_MVarId_byCases___lam__0___closed__11_once, _init_l_Lean_MVarId_byCases___lam__0___closed__11);
lean_inc(v_mvarId_4375_);
v___x_4444_ = l_Lean_Meta_throwTacticEx___redArg(v___x_4442_, v_mvarId_4375_, v___x_4443_, v___y_4378_, v___y_4379_, v___y_4380_, v___y_4381_);
if (lean_obj_tag(v___x_4444_) == 0)
{
lean_dec_ref_known(v___x_4444_, 1);
v___y_4388_ = v___y_4378_;
v___y_4389_ = v___y_4379_;
v___y_4390_ = v___y_4380_;
v___y_4391_ = v___y_4381_;
goto v___jp_4387_;
}
else
{
lean_object* v_a_4445_; lean_object* v___x_4447_; uint8_t v_isShared_4448_; uint8_t v_isSharedCheck_4452_; 
lean_dec(v_a_4386_);
lean_dec(v_a_4384_);
lean_dec(v_hName_4377_);
lean_dec_ref(v_p_4376_);
lean_dec(v_mvarId_4375_);
v_a_4445_ = lean_ctor_get(v___x_4444_, 0);
v_isSharedCheck_4452_ = !lean_is_exclusive(v___x_4444_);
if (v_isSharedCheck_4452_ == 0)
{
v___x_4447_ = v___x_4444_;
v_isShared_4448_ = v_isSharedCheck_4452_;
goto v_resetjp_4446_;
}
else
{
lean_inc(v_a_4445_);
lean_dec(v___x_4444_);
v___x_4447_ = lean_box(0);
v_isShared_4448_ = v_isSharedCheck_4452_;
goto v_resetjp_4446_;
}
v_resetjp_4446_:
{
lean_object* v___x_4450_; 
if (v_isShared_4448_ == 0)
{
v___x_4450_ = v___x_4447_;
goto v_reusejp_4449_;
}
else
{
lean_object* v_reuseFailAlloc_4451_; 
v_reuseFailAlloc_4451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4451_, 0, v_a_4445_);
v___x_4450_ = v_reuseFailAlloc_4451_;
goto v_reusejp_4449_;
}
v_reusejp_4449_:
{
return v___x_4450_;
}
}
}
}
else
{
v___y_4388_ = v___y_4378_;
v___y_4389_ = v___y_4379_;
v___y_4390_ = v___y_4380_;
v___y_4391_ = v___y_4381_;
goto v___jp_4387_;
}
}
else
{
lean_object* v_a_4453_; lean_object* v___x_4455_; uint8_t v_isShared_4456_; uint8_t v_isSharedCheck_4460_; 
lean_dec(v_a_4386_);
lean_dec(v_a_4384_);
lean_dec(v_hName_4377_);
lean_dec_ref(v_p_4376_);
lean_dec(v_mvarId_4375_);
v_a_4453_ = lean_ctor_get(v___x_4439_, 0);
v_isSharedCheck_4460_ = !lean_is_exclusive(v___x_4439_);
if (v_isSharedCheck_4460_ == 0)
{
v___x_4455_ = v___x_4439_;
v_isShared_4456_ = v_isSharedCheck_4460_;
goto v_resetjp_4454_;
}
else
{
lean_inc(v_a_4453_);
lean_dec(v___x_4439_);
v___x_4455_ = lean_box(0);
v_isShared_4456_ = v_isSharedCheck_4460_;
goto v_resetjp_4454_;
}
v_resetjp_4454_:
{
lean_object* v___x_4458_; 
if (v_isShared_4456_ == 0)
{
v___x_4458_ = v___x_4455_;
goto v_reusejp_4457_;
}
else
{
lean_object* v_reuseFailAlloc_4459_; 
v_reuseFailAlloc_4459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4459_, 0, v_a_4453_);
v___x_4458_ = v_reuseFailAlloc_4459_;
goto v_reusejp_4457_;
}
v_reusejp_4457_:
{
return v___x_4458_;
}
}
}
v___jp_4387_:
{
lean_object* v___x_4392_; lean_object* v___x_4393_; lean_object* v___x_4394_; 
v___x_4392_ = ((lean_object*)(l_Lean_MVarId_byCases___lam__0___closed__1));
lean_inc(v_a_4386_);
v___x_4393_ = l_Lean_Name_append(v_a_4386_, v___x_4392_);
lean_inc(v_a_4384_);
lean_inc(v_hName_4377_);
lean_inc_ref(v_p_4376_);
v___x_4394_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkByCasesSubgoal(v_p_4376_, v_hName_4377_, v_a_4384_, v___x_4393_, v___y_4388_, v___y_4389_, v___y_4390_, v___y_4391_);
if (lean_obj_tag(v___x_4394_) == 0)
{
lean_object* v_a_4395_; lean_object* v_fst_4396_; lean_object* v_snd_4397_; lean_object* v___x_4398_; lean_object* v___x_4399_; lean_object* v___x_4400_; lean_object* v___x_4401_; 
v_a_4395_ = lean_ctor_get(v___x_4394_, 0);
lean_inc(v_a_4395_);
lean_dec_ref_known(v___x_4394_, 1);
v_fst_4396_ = lean_ctor_get(v_a_4395_, 0);
lean_inc(v_fst_4396_);
v_snd_4397_ = lean_ctor_get(v_a_4395_, 1);
lean_inc(v_snd_4397_);
lean_dec(v_a_4395_);
lean_inc_ref(v_p_4376_);
v___x_4398_ = l_Lean_mkNot(v_p_4376_);
v___x_4399_ = ((lean_object*)(l_Lean_MVarId_byCases___lam__0___closed__3));
v___x_4400_ = l_Lean_Name_append(v_a_4386_, v___x_4399_);
lean_inc(v_a_4384_);
v___x_4401_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkByCasesSubgoal(v___x_4398_, v_hName_4377_, v_a_4384_, v___x_4400_, v___y_4388_, v___y_4389_, v___y_4390_, v___y_4391_);
if (lean_obj_tag(v___x_4401_) == 0)
{
lean_object* v_a_4402_; lean_object* v_fst_4403_; lean_object* v_snd_4404_; lean_object* v___x_4406_; uint8_t v_isShared_4407_; uint8_t v_isSharedCheck_4422_; 
v_a_4402_ = lean_ctor_get(v___x_4401_, 0);
lean_inc(v_a_4402_);
lean_dec_ref_known(v___x_4401_, 1);
v_fst_4403_ = lean_ctor_get(v_a_4402_, 0);
v_snd_4404_ = lean_ctor_get(v_a_4402_, 1);
v_isSharedCheck_4422_ = !lean_is_exclusive(v_a_4402_);
if (v_isSharedCheck_4422_ == 0)
{
v___x_4406_ = v_a_4402_;
v_isShared_4407_ = v_isSharedCheck_4422_;
goto v_resetjp_4405_;
}
else
{
lean_inc(v_snd_4404_);
lean_inc(v_fst_4403_);
lean_dec(v_a_4402_);
v___x_4406_ = lean_box(0);
v_isShared_4407_ = v_isSharedCheck_4422_;
goto v_resetjp_4405_;
}
v_resetjp_4405_:
{
lean_object* v___x_4408_; lean_object* v___x_4409_; lean_object* v___x_4410_; lean_object* v___x_4412_; uint8_t v_isShared_4413_; uint8_t v_isSharedCheck_4420_; 
v___x_4408_ = lean_obj_once(&l_Lean_MVarId_byCases___lam__0___closed__7, &l_Lean_MVarId_byCases___lam__0___closed__7_once, _init_l_Lean_MVarId_byCases___lam__0___closed__7);
v___x_4409_ = l_Lean_mkApp4(v___x_4408_, v_p_4376_, v_a_4384_, v_fst_4396_, v_fst_4403_);
v___x_4410_ = l_Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1___redArg(v_mvarId_4375_, v___x_4409_, v___y_4389_);
v_isSharedCheck_4420_ = !lean_is_exclusive(v___x_4410_);
if (v_isSharedCheck_4420_ == 0)
{
lean_object* v_unused_4421_; 
v_unused_4421_ = lean_ctor_get(v___x_4410_, 0);
lean_dec(v_unused_4421_);
v___x_4412_ = v___x_4410_;
v_isShared_4413_ = v_isSharedCheck_4420_;
goto v_resetjp_4411_;
}
else
{
lean_dec(v___x_4410_);
v___x_4412_ = lean_box(0);
v_isShared_4413_ = v_isSharedCheck_4420_;
goto v_resetjp_4411_;
}
v_resetjp_4411_:
{
lean_object* v___x_4415_; 
if (v_isShared_4407_ == 0)
{
lean_ctor_set(v___x_4406_, 0, v_snd_4397_);
v___x_4415_ = v___x_4406_;
goto v_reusejp_4414_;
}
else
{
lean_object* v_reuseFailAlloc_4419_; 
v_reuseFailAlloc_4419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4419_, 0, v_snd_4397_);
lean_ctor_set(v_reuseFailAlloc_4419_, 1, v_snd_4404_);
v___x_4415_ = v_reuseFailAlloc_4419_;
goto v_reusejp_4414_;
}
v_reusejp_4414_:
{
lean_object* v___x_4417_; 
if (v_isShared_4413_ == 0)
{
lean_ctor_set(v___x_4412_, 0, v___x_4415_);
v___x_4417_ = v___x_4412_;
goto v_reusejp_4416_;
}
else
{
lean_object* v_reuseFailAlloc_4418_; 
v_reuseFailAlloc_4418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4418_, 0, v___x_4415_);
v___x_4417_ = v_reuseFailAlloc_4418_;
goto v_reusejp_4416_;
}
v_reusejp_4416_:
{
return v___x_4417_;
}
}
}
}
}
else
{
lean_object* v_a_4423_; lean_object* v___x_4425_; uint8_t v_isShared_4426_; uint8_t v_isSharedCheck_4430_; 
lean_dec(v_snd_4397_);
lean_dec(v_fst_4396_);
lean_dec(v_a_4384_);
lean_dec_ref(v_p_4376_);
lean_dec(v_mvarId_4375_);
v_a_4423_ = lean_ctor_get(v___x_4401_, 0);
v_isSharedCheck_4430_ = !lean_is_exclusive(v___x_4401_);
if (v_isSharedCheck_4430_ == 0)
{
v___x_4425_ = v___x_4401_;
v_isShared_4426_ = v_isSharedCheck_4430_;
goto v_resetjp_4424_;
}
else
{
lean_inc(v_a_4423_);
lean_dec(v___x_4401_);
v___x_4425_ = lean_box(0);
v_isShared_4426_ = v_isSharedCheck_4430_;
goto v_resetjp_4424_;
}
v_resetjp_4424_:
{
lean_object* v___x_4428_; 
if (v_isShared_4426_ == 0)
{
v___x_4428_ = v___x_4425_;
goto v_reusejp_4427_;
}
else
{
lean_object* v_reuseFailAlloc_4429_; 
v_reuseFailAlloc_4429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4429_, 0, v_a_4423_);
v___x_4428_ = v_reuseFailAlloc_4429_;
goto v_reusejp_4427_;
}
v_reusejp_4427_:
{
return v___x_4428_;
}
}
}
}
else
{
lean_object* v_a_4431_; lean_object* v___x_4433_; uint8_t v_isShared_4434_; uint8_t v_isSharedCheck_4438_; 
lean_dec(v_a_4386_);
lean_dec(v_a_4384_);
lean_dec(v_hName_4377_);
lean_dec_ref(v_p_4376_);
lean_dec(v_mvarId_4375_);
v_a_4431_ = lean_ctor_get(v___x_4394_, 0);
v_isSharedCheck_4438_ = !lean_is_exclusive(v___x_4394_);
if (v_isSharedCheck_4438_ == 0)
{
v___x_4433_ = v___x_4394_;
v_isShared_4434_ = v_isSharedCheck_4438_;
goto v_resetjp_4432_;
}
else
{
lean_inc(v_a_4431_);
lean_dec(v___x_4394_);
v___x_4433_ = lean_box(0);
v_isShared_4434_ = v_isSharedCheck_4438_;
goto v_resetjp_4432_;
}
v_resetjp_4432_:
{
lean_object* v___x_4436_; 
if (v_isShared_4434_ == 0)
{
v___x_4436_ = v___x_4433_;
goto v_reusejp_4435_;
}
else
{
lean_object* v_reuseFailAlloc_4437_; 
v_reuseFailAlloc_4437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4437_, 0, v_a_4431_);
v___x_4436_ = v_reuseFailAlloc_4437_;
goto v_reusejp_4435_;
}
v_reusejp_4435_:
{
return v___x_4436_;
}
}
}
}
}
else
{
lean_object* v_a_4461_; lean_object* v___x_4463_; uint8_t v_isShared_4464_; uint8_t v_isSharedCheck_4468_; 
lean_dec(v_a_4384_);
lean_dec(v_hName_4377_);
lean_dec_ref(v_p_4376_);
lean_dec(v_mvarId_4375_);
v_a_4461_ = lean_ctor_get(v___x_4385_, 0);
v_isSharedCheck_4468_ = !lean_is_exclusive(v___x_4385_);
if (v_isSharedCheck_4468_ == 0)
{
v___x_4463_ = v___x_4385_;
v_isShared_4464_ = v_isSharedCheck_4468_;
goto v_resetjp_4462_;
}
else
{
lean_inc(v_a_4461_);
lean_dec(v___x_4385_);
v___x_4463_ = lean_box(0);
v_isShared_4464_ = v_isSharedCheck_4468_;
goto v_resetjp_4462_;
}
v_resetjp_4462_:
{
lean_object* v___x_4466_; 
if (v_isShared_4464_ == 0)
{
v___x_4466_ = v___x_4463_;
goto v_reusejp_4465_;
}
else
{
lean_object* v_reuseFailAlloc_4467_; 
v_reuseFailAlloc_4467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4467_, 0, v_a_4461_);
v___x_4466_ = v_reuseFailAlloc_4467_;
goto v_reusejp_4465_;
}
v_reusejp_4465_:
{
return v___x_4466_;
}
}
}
}
else
{
lean_object* v_a_4469_; lean_object* v___x_4471_; uint8_t v_isShared_4472_; uint8_t v_isSharedCheck_4476_; 
lean_dec(v_hName_4377_);
lean_dec_ref(v_p_4376_);
lean_dec(v_mvarId_4375_);
v_a_4469_ = lean_ctor_get(v___x_4383_, 0);
v_isSharedCheck_4476_ = !lean_is_exclusive(v___x_4383_);
if (v_isSharedCheck_4476_ == 0)
{
v___x_4471_ = v___x_4383_;
v_isShared_4472_ = v_isSharedCheck_4476_;
goto v_resetjp_4470_;
}
else
{
lean_inc(v_a_4469_);
lean_dec(v___x_4383_);
v___x_4471_ = lean_box(0);
v_isShared_4472_ = v_isSharedCheck_4476_;
goto v_resetjp_4470_;
}
v_resetjp_4470_:
{
lean_object* v___x_4474_; 
if (v_isShared_4472_ == 0)
{
v___x_4474_ = v___x_4471_;
goto v_reusejp_4473_;
}
else
{
lean_object* v_reuseFailAlloc_4475_; 
v_reuseFailAlloc_4475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4475_, 0, v_a_4469_);
v___x_4474_ = v_reuseFailAlloc_4475_;
goto v_reusejp_4473_;
}
v_reusejp_4473_:
{
return v___x_4474_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_byCases___lam__0___boxed(lean_object* v_mvarId_4477_, lean_object* v_p_4478_, lean_object* v_hName_4479_, lean_object* v___y_4480_, lean_object* v___y_4481_, lean_object* v___y_4482_, lean_object* v___y_4483_, lean_object* v___y_4484_){
_start:
{
lean_object* v_res_4485_; 
v_res_4485_ = l_Lean_MVarId_byCases___lam__0(v_mvarId_4477_, v_p_4478_, v_hName_4479_, v___y_4480_, v___y_4481_, v___y_4482_, v___y_4483_);
lean_dec(v___y_4483_);
lean_dec_ref(v___y_4482_);
lean_dec(v___y_4481_);
lean_dec_ref(v___y_4480_);
return v_res_4485_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_byCases(lean_object* v_mvarId_4486_, lean_object* v_p_4487_, lean_object* v_hName_4488_, lean_object* v_a_4489_, lean_object* v_a_4490_, lean_object* v_a_4491_, lean_object* v_a_4492_){
_start:
{
lean_object* v___f_4494_; lean_object* v___x_4495_; 
lean_inc(v_mvarId_4486_);
v___f_4494_ = lean_alloc_closure((void*)(l_Lean_MVarId_byCases___lam__0___boxed), 8, 3);
lean_closure_set(v___f_4494_, 0, v_mvarId_4486_);
lean_closure_set(v___f_4494_, 1, v_p_4487_);
lean_closure_set(v___f_4494_, 2, v_hName_4488_);
v___x_4495_ = l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2___redArg(v_mvarId_4486_, v___f_4494_, v_a_4489_, v_a_4490_, v_a_4491_, v_a_4492_);
return v___x_4495_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_byCases___boxed(lean_object* v_mvarId_4496_, lean_object* v_p_4497_, lean_object* v_hName_4498_, lean_object* v_a_4499_, lean_object* v_a_4500_, lean_object* v_a_4501_, lean_object* v_a_4502_, lean_object* v_a_4503_){
_start:
{
lean_object* v_res_4504_; 
v_res_4504_ = l_Lean_MVarId_byCases(v_mvarId_4496_, v_p_4497_, v_hName_4498_, v_a_4499_, v_a_4500_, v_a_4501_, v_a_4502_);
lean_dec(v_a_4502_);
lean_dec_ref(v_a_4501_);
lean_dec(v_a_4500_);
lean_dec_ref(v_a_4499_);
return v_res_4504_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_byCasesDec___lam__0(lean_object* v_mvarId_4508_, lean_object* v_p_4509_, lean_object* v_hName_4510_, lean_object* v_dec_4511_, lean_object* v___y_4512_, lean_object* v___y_4513_, lean_object* v___y_4514_, lean_object* v___y_4515_){
_start:
{
lean_object* v___x_4517_; 
lean_inc(v_mvarId_4508_);
v___x_4517_ = l_Lean_MVarId_getType(v_mvarId_4508_, v___y_4512_, v___y_4513_, v___y_4514_, v___y_4515_);
if (lean_obj_tag(v___x_4517_) == 0)
{
lean_object* v_a_4518_; lean_object* v___x_4519_; 
v_a_4518_ = lean_ctor_get(v___x_4517_, 0);
lean_inc(v_a_4518_);
lean_dec_ref_known(v___x_4517_, 1);
lean_inc(v_mvarId_4508_);
v___x_4519_ = l_Lean_MVarId_getTag(v_mvarId_4508_, v___y_4512_, v___y_4513_, v___y_4514_, v___y_4515_);
if (lean_obj_tag(v___x_4519_) == 0)
{
lean_object* v_a_4520_; lean_object* v___x_4521_; 
v_a_4520_ = lean_ctor_get(v___x_4519_, 0);
lean_inc(v_a_4520_);
lean_dec_ref_known(v___x_4519_, 1);
lean_inc(v_a_4518_);
v___x_4521_ = l_Lean_Meta_getLevel(v_a_4518_, v___y_4512_, v___y_4513_, v___y_4514_, v___y_4515_);
if (lean_obj_tag(v___x_4521_) == 0)
{
lean_object* v_a_4522_; lean_object* v___x_4523_; lean_object* v___x_4524_; lean_object* v___x_4525_; 
v_a_4522_ = lean_ctor_get(v___x_4521_, 0);
lean_inc(v_a_4522_);
lean_dec_ref_known(v___x_4521_, 1);
v___x_4523_ = ((lean_object*)(l_Lean_MVarId_byCases___lam__0___closed__1));
lean_inc(v_a_4520_);
v___x_4524_ = l_Lean_Name_append(v_a_4520_, v___x_4523_);
lean_inc(v_a_4518_);
lean_inc(v_hName_4510_);
lean_inc_ref(v_p_4509_);
v___x_4525_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkByCasesSubgoal(v_p_4509_, v_hName_4510_, v_a_4518_, v___x_4524_, v___y_4512_, v___y_4513_, v___y_4514_, v___y_4515_);
if (lean_obj_tag(v___x_4525_) == 0)
{
lean_object* v_a_4526_; lean_object* v_fst_4527_; lean_object* v_snd_4528_; lean_object* v___x_4530_; uint8_t v_isShared_4531_; uint8_t v_isSharedCheck_4570_; 
v_a_4526_ = lean_ctor_get(v___x_4525_, 0);
lean_inc(v_a_4526_);
lean_dec_ref_known(v___x_4525_, 1);
v_fst_4527_ = lean_ctor_get(v_a_4526_, 0);
v_snd_4528_ = lean_ctor_get(v_a_4526_, 1);
v_isSharedCheck_4570_ = !lean_is_exclusive(v_a_4526_);
if (v_isSharedCheck_4570_ == 0)
{
v___x_4530_ = v_a_4526_;
v_isShared_4531_ = v_isSharedCheck_4570_;
goto v_resetjp_4529_;
}
else
{
lean_inc(v_snd_4528_);
lean_inc(v_fst_4527_);
lean_dec(v_a_4526_);
v___x_4530_ = lean_box(0);
v_isShared_4531_ = v_isSharedCheck_4570_;
goto v_resetjp_4529_;
}
v_resetjp_4529_:
{
lean_object* v___x_4532_; lean_object* v___x_4533_; lean_object* v___x_4534_; lean_object* v___x_4535_; 
lean_inc_ref(v_p_4509_);
v___x_4532_ = l_Lean_mkNot(v_p_4509_);
v___x_4533_ = ((lean_object*)(l_Lean_MVarId_byCases___lam__0___closed__3));
v___x_4534_ = l_Lean_Name_append(v_a_4520_, v___x_4533_);
lean_inc(v_a_4518_);
v___x_4535_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkByCasesSubgoal(v___x_4532_, v_hName_4510_, v_a_4518_, v___x_4534_, v___y_4512_, v___y_4513_, v___y_4514_, v___y_4515_);
if (lean_obj_tag(v___x_4535_) == 0)
{
lean_object* v_a_4536_; lean_object* v_fst_4537_; lean_object* v_snd_4538_; lean_object* v___x_4540_; uint8_t v_isShared_4541_; uint8_t v_isSharedCheck_4561_; 
v_a_4536_ = lean_ctor_get(v___x_4535_, 0);
lean_inc(v_a_4536_);
lean_dec_ref_known(v___x_4535_, 1);
v_fst_4537_ = lean_ctor_get(v_a_4536_, 0);
v_snd_4538_ = lean_ctor_get(v_a_4536_, 1);
v_isSharedCheck_4561_ = !lean_is_exclusive(v_a_4536_);
if (v_isSharedCheck_4561_ == 0)
{
v___x_4540_ = v_a_4536_;
v_isShared_4541_ = v_isSharedCheck_4561_;
goto v_resetjp_4539_;
}
else
{
lean_inc(v_snd_4538_);
lean_inc(v_fst_4537_);
lean_dec(v_a_4536_);
v___x_4540_ = lean_box(0);
v_isShared_4541_ = v_isSharedCheck_4561_;
goto v_resetjp_4539_;
}
v_resetjp_4539_:
{
lean_object* v___x_4542_; lean_object* v___x_4543_; lean_object* v___x_4545_; 
v___x_4542_ = ((lean_object*)(l_Lean_MVarId_byCasesDec___lam__0___closed__1));
v___x_4543_ = lean_box(0);
if (v_isShared_4531_ == 0)
{
lean_ctor_set_tag(v___x_4530_, 1);
lean_ctor_set(v___x_4530_, 1, v___x_4543_);
lean_ctor_set(v___x_4530_, 0, v_a_4522_);
v___x_4545_ = v___x_4530_;
goto v_reusejp_4544_;
}
else
{
lean_object* v_reuseFailAlloc_4560_; 
v_reuseFailAlloc_4560_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4560_, 0, v_a_4522_);
lean_ctor_set(v_reuseFailAlloc_4560_, 1, v___x_4543_);
v___x_4545_ = v_reuseFailAlloc_4560_;
goto v_reusejp_4544_;
}
v_reusejp_4544_:
{
lean_object* v___x_4546_; lean_object* v___x_4547_; lean_object* v___x_4548_; lean_object* v___x_4550_; uint8_t v_isShared_4551_; uint8_t v_isSharedCheck_4558_; 
v___x_4546_ = l_Lean_Expr_const___override(v___x_4542_, v___x_4545_);
v___x_4547_ = l_Lean_mkApp5(v___x_4546_, v_a_4518_, v_p_4509_, v_dec_4511_, v_fst_4527_, v_fst_4537_);
v___x_4548_ = l_Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1___redArg(v_mvarId_4508_, v___x_4547_, v___y_4513_);
v_isSharedCheck_4558_ = !lean_is_exclusive(v___x_4548_);
if (v_isSharedCheck_4558_ == 0)
{
lean_object* v_unused_4559_; 
v_unused_4559_ = lean_ctor_get(v___x_4548_, 0);
lean_dec(v_unused_4559_);
v___x_4550_ = v___x_4548_;
v_isShared_4551_ = v_isSharedCheck_4558_;
goto v_resetjp_4549_;
}
else
{
lean_dec(v___x_4548_);
v___x_4550_ = lean_box(0);
v_isShared_4551_ = v_isSharedCheck_4558_;
goto v_resetjp_4549_;
}
v_resetjp_4549_:
{
lean_object* v___x_4553_; 
if (v_isShared_4541_ == 0)
{
lean_ctor_set(v___x_4540_, 0, v_snd_4528_);
v___x_4553_ = v___x_4540_;
goto v_reusejp_4552_;
}
else
{
lean_object* v_reuseFailAlloc_4557_; 
v_reuseFailAlloc_4557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4557_, 0, v_snd_4528_);
lean_ctor_set(v_reuseFailAlloc_4557_, 1, v_snd_4538_);
v___x_4553_ = v_reuseFailAlloc_4557_;
goto v_reusejp_4552_;
}
v_reusejp_4552_:
{
lean_object* v___x_4555_; 
if (v_isShared_4551_ == 0)
{
lean_ctor_set(v___x_4550_, 0, v___x_4553_);
v___x_4555_ = v___x_4550_;
goto v_reusejp_4554_;
}
else
{
lean_object* v_reuseFailAlloc_4556_; 
v_reuseFailAlloc_4556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4556_, 0, v___x_4553_);
v___x_4555_ = v_reuseFailAlloc_4556_;
goto v_reusejp_4554_;
}
v_reusejp_4554_:
{
return v___x_4555_;
}
}
}
}
}
}
else
{
lean_object* v_a_4562_; lean_object* v___x_4564_; uint8_t v_isShared_4565_; uint8_t v_isSharedCheck_4569_; 
lean_del_object(v___x_4530_);
lean_dec(v_snd_4528_);
lean_dec(v_fst_4527_);
lean_dec(v_a_4522_);
lean_dec(v_a_4518_);
lean_dec_ref(v_dec_4511_);
lean_dec_ref(v_p_4509_);
lean_dec(v_mvarId_4508_);
v_a_4562_ = lean_ctor_get(v___x_4535_, 0);
v_isSharedCheck_4569_ = !lean_is_exclusive(v___x_4535_);
if (v_isSharedCheck_4569_ == 0)
{
v___x_4564_ = v___x_4535_;
v_isShared_4565_ = v_isSharedCheck_4569_;
goto v_resetjp_4563_;
}
else
{
lean_inc(v_a_4562_);
lean_dec(v___x_4535_);
v___x_4564_ = lean_box(0);
v_isShared_4565_ = v_isSharedCheck_4569_;
goto v_resetjp_4563_;
}
v_resetjp_4563_:
{
lean_object* v___x_4567_; 
if (v_isShared_4565_ == 0)
{
v___x_4567_ = v___x_4564_;
goto v_reusejp_4566_;
}
else
{
lean_object* v_reuseFailAlloc_4568_; 
v_reuseFailAlloc_4568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4568_, 0, v_a_4562_);
v___x_4567_ = v_reuseFailAlloc_4568_;
goto v_reusejp_4566_;
}
v_reusejp_4566_:
{
return v___x_4567_;
}
}
}
}
}
else
{
lean_object* v_a_4571_; lean_object* v___x_4573_; uint8_t v_isShared_4574_; uint8_t v_isSharedCheck_4578_; 
lean_dec(v_a_4522_);
lean_dec(v_a_4520_);
lean_dec(v_a_4518_);
lean_dec_ref(v_dec_4511_);
lean_dec(v_hName_4510_);
lean_dec_ref(v_p_4509_);
lean_dec(v_mvarId_4508_);
v_a_4571_ = lean_ctor_get(v___x_4525_, 0);
v_isSharedCheck_4578_ = !lean_is_exclusive(v___x_4525_);
if (v_isSharedCheck_4578_ == 0)
{
v___x_4573_ = v___x_4525_;
v_isShared_4574_ = v_isSharedCheck_4578_;
goto v_resetjp_4572_;
}
else
{
lean_inc(v_a_4571_);
lean_dec(v___x_4525_);
v___x_4573_ = lean_box(0);
v_isShared_4574_ = v_isSharedCheck_4578_;
goto v_resetjp_4572_;
}
v_resetjp_4572_:
{
lean_object* v___x_4576_; 
if (v_isShared_4574_ == 0)
{
v___x_4576_ = v___x_4573_;
goto v_reusejp_4575_;
}
else
{
lean_object* v_reuseFailAlloc_4577_; 
v_reuseFailAlloc_4577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4577_, 0, v_a_4571_);
v___x_4576_ = v_reuseFailAlloc_4577_;
goto v_reusejp_4575_;
}
v_reusejp_4575_:
{
return v___x_4576_;
}
}
}
}
else
{
lean_object* v_a_4579_; lean_object* v___x_4581_; uint8_t v_isShared_4582_; uint8_t v_isSharedCheck_4586_; 
lean_dec(v_a_4520_);
lean_dec(v_a_4518_);
lean_dec_ref(v_dec_4511_);
lean_dec(v_hName_4510_);
lean_dec_ref(v_p_4509_);
lean_dec(v_mvarId_4508_);
v_a_4579_ = lean_ctor_get(v___x_4521_, 0);
v_isSharedCheck_4586_ = !lean_is_exclusive(v___x_4521_);
if (v_isSharedCheck_4586_ == 0)
{
v___x_4581_ = v___x_4521_;
v_isShared_4582_ = v_isSharedCheck_4586_;
goto v_resetjp_4580_;
}
else
{
lean_inc(v_a_4579_);
lean_dec(v___x_4521_);
v___x_4581_ = lean_box(0);
v_isShared_4582_ = v_isSharedCheck_4586_;
goto v_resetjp_4580_;
}
v_resetjp_4580_:
{
lean_object* v___x_4584_; 
if (v_isShared_4582_ == 0)
{
v___x_4584_ = v___x_4581_;
goto v_reusejp_4583_;
}
else
{
lean_object* v_reuseFailAlloc_4585_; 
v_reuseFailAlloc_4585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4585_, 0, v_a_4579_);
v___x_4584_ = v_reuseFailAlloc_4585_;
goto v_reusejp_4583_;
}
v_reusejp_4583_:
{
return v___x_4584_;
}
}
}
}
else
{
lean_object* v_a_4587_; lean_object* v___x_4589_; uint8_t v_isShared_4590_; uint8_t v_isSharedCheck_4594_; 
lean_dec(v_a_4518_);
lean_dec_ref(v_dec_4511_);
lean_dec(v_hName_4510_);
lean_dec_ref(v_p_4509_);
lean_dec(v_mvarId_4508_);
v_a_4587_ = lean_ctor_get(v___x_4519_, 0);
v_isSharedCheck_4594_ = !lean_is_exclusive(v___x_4519_);
if (v_isSharedCheck_4594_ == 0)
{
v___x_4589_ = v___x_4519_;
v_isShared_4590_ = v_isSharedCheck_4594_;
goto v_resetjp_4588_;
}
else
{
lean_inc(v_a_4587_);
lean_dec(v___x_4519_);
v___x_4589_ = lean_box(0);
v_isShared_4590_ = v_isSharedCheck_4594_;
goto v_resetjp_4588_;
}
v_resetjp_4588_:
{
lean_object* v___x_4592_; 
if (v_isShared_4590_ == 0)
{
v___x_4592_ = v___x_4589_;
goto v_reusejp_4591_;
}
else
{
lean_object* v_reuseFailAlloc_4593_; 
v_reuseFailAlloc_4593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4593_, 0, v_a_4587_);
v___x_4592_ = v_reuseFailAlloc_4593_;
goto v_reusejp_4591_;
}
v_reusejp_4591_:
{
return v___x_4592_;
}
}
}
}
else
{
lean_object* v_a_4595_; lean_object* v___x_4597_; uint8_t v_isShared_4598_; uint8_t v_isSharedCheck_4602_; 
lean_dec_ref(v_dec_4511_);
lean_dec(v_hName_4510_);
lean_dec_ref(v_p_4509_);
lean_dec(v_mvarId_4508_);
v_a_4595_ = lean_ctor_get(v___x_4517_, 0);
v_isSharedCheck_4602_ = !lean_is_exclusive(v___x_4517_);
if (v_isSharedCheck_4602_ == 0)
{
v___x_4597_ = v___x_4517_;
v_isShared_4598_ = v_isSharedCheck_4602_;
goto v_resetjp_4596_;
}
else
{
lean_inc(v_a_4595_);
lean_dec(v___x_4517_);
v___x_4597_ = lean_box(0);
v_isShared_4598_ = v_isSharedCheck_4602_;
goto v_resetjp_4596_;
}
v_resetjp_4596_:
{
lean_object* v___x_4600_; 
if (v_isShared_4598_ == 0)
{
v___x_4600_ = v___x_4597_;
goto v_reusejp_4599_;
}
else
{
lean_object* v_reuseFailAlloc_4601_; 
v_reuseFailAlloc_4601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4601_, 0, v_a_4595_);
v___x_4600_ = v_reuseFailAlloc_4601_;
goto v_reusejp_4599_;
}
v_reusejp_4599_:
{
return v___x_4600_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_byCasesDec___lam__0___boxed(lean_object* v_mvarId_4603_, lean_object* v_p_4604_, lean_object* v_hName_4605_, lean_object* v_dec_4606_, lean_object* v___y_4607_, lean_object* v___y_4608_, lean_object* v___y_4609_, lean_object* v___y_4610_, lean_object* v___y_4611_){
_start:
{
lean_object* v_res_4612_; 
v_res_4612_ = l_Lean_MVarId_byCasesDec___lam__0(v_mvarId_4603_, v_p_4604_, v_hName_4605_, v_dec_4606_, v___y_4607_, v___y_4608_, v___y_4609_, v___y_4610_);
lean_dec(v___y_4610_);
lean_dec_ref(v___y_4609_);
lean_dec(v___y_4608_);
lean_dec_ref(v___y_4607_);
return v_res_4612_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_byCasesDec(lean_object* v_mvarId_4613_, lean_object* v_p_4614_, lean_object* v_dec_4615_, lean_object* v_hName_4616_, lean_object* v_a_4617_, lean_object* v_a_4618_, lean_object* v_a_4619_, lean_object* v_a_4620_){
_start:
{
lean_object* v___f_4622_; lean_object* v___x_4623_; 
lean_inc(v_mvarId_4613_);
v___f_4622_ = lean_alloc_closure((void*)(l_Lean_MVarId_byCasesDec___lam__0___boxed), 9, 4);
lean_closure_set(v___f_4622_, 0, v_mvarId_4613_);
lean_closure_set(v___f_4622_, 1, v_p_4614_);
lean_closure_set(v___f_4622_, 2, v_hName_4616_);
lean_closure_set(v___f_4622_, 3, v_dec_4615_);
v___x_4623_ = l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2___redArg(v_mvarId_4613_, v___f_4622_, v_a_4617_, v_a_4618_, v_a_4619_, v_a_4620_);
return v___x_4623_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_byCasesDec___boxed(lean_object* v_mvarId_4624_, lean_object* v_p_4625_, lean_object* v_dec_4626_, lean_object* v_hName_4627_, lean_object* v_a_4628_, lean_object* v_a_4629_, lean_object* v_a_4630_, lean_object* v_a_4631_, lean_object* v_a_4632_){
_start:
{
lean_object* v_res_4633_; 
v_res_4633_ = l_Lean_MVarId_byCasesDec(v_mvarId_4624_, v_p_4625_, v_dec_4626_, v_hName_4627_, v_a_4628_, v_a_4629_, v_a_4630_, v_a_4631_);
lean_dec(v_a_4631_);
lean_dec_ref(v_a_4630_);
lean_dec(v_a_4629_);
lean_dec_ref(v_a_4628_);
return v_res_4633_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4685_; lean_object* v___x_4686_; lean_object* v___x_4687_; 
v___x_4685_ = lean_unsigned_to_nat(4241171151u);
v___x_4686_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_));
v___x_4687_ = l_Lean_Name_num___override(v___x_4686_, v___x_4685_);
return v___x_4687_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4689_; lean_object* v___x_4690_; lean_object* v___x_4691_; 
v___x_4689_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_));
v___x_4690_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_);
v___x_4691_ = l_Lean_Name_str___override(v___x_4690_, v___x_4689_);
return v___x_4691_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4693_; lean_object* v___x_4694_; lean_object* v___x_4695_; 
v___x_4693_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_));
v___x_4694_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_);
v___x_4695_ = l_Lean_Name_str___override(v___x_4694_, v___x_4693_);
return v___x_4695_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4696_; lean_object* v___x_4697_; lean_object* v___x_4698_; 
v___x_4696_ = lean_unsigned_to_nat(2u);
v___x_4697_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_);
v___x_4698_ = l_Lean_Name_num___override(v___x_4697_, v___x_4696_);
return v___x_4698_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4700_; uint8_t v___x_4701_; lean_object* v___x_4702_; lean_object* v___x_4703_; 
v___x_4700_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_));
v___x_4701_ = 0;
v___x_4702_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_);
v___x_4703_ = l_Lean_registerTraceClass(v___x_4700_, v___x_4701_, v___x_4702_);
return v___x_4703_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2____boxed(lean_object* v_a_4704_){
_start:
{
lean_object* v_res_4705_; 
v_res_4705_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_();
return v_res_4705_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Induction(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Acyclic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_UnifyEq(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Constructions_SparseCasesOn(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Constructions_CtorIdx(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Cases(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Induction(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Acyclic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_UnifyEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Constructions_SparseCasesOn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Constructions_CtorIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Cases(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Induction(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Acyclic(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_UnifyEq(uint8_t builtin);
lean_object* initialize_Lean_Meta_Constructions_SparseCasesOn(uint8_t builtin);
lean_object* initialize_Lean_Meta_Constructions_CtorIdx(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Cases(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Induction(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Acyclic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_UnifyEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Constructions_SparseCasesOn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Constructions_CtorIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Cases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Cases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Cases(builtin);
}
#ifdef __cplusplus
}
#endif
