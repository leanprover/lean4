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
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
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
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
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
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_saveState___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
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
lean_object* lean_array_mk(lean_object*);
lean_object* l_Lean_MVarId_induction(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__2(lean_object*, uint8_t, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__3(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___lam__0___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__0;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4_spec__5(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected_spec__0_spec__0(lean_object* v_msgData_1_, lean_object* v___y_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_){
_start:
{
lean_object* v___x_7_; lean_object* v_env_8_; uint8_t v___x_9_; lean_object* v_env_10_; lean_object* v___x_11_; lean_object* v_toCold_12_; lean_object* v_mctx_13_; lean_object* v_lctx_14_; lean_object* v_options_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; 
v___x_7_ = lean_st_ref_get(v___y_5_);
v_env_8_ = lean_ctor_get(v___x_7_, 0);
lean_inc_ref(v_env_8_);
lean_dec(v___x_7_);
v___x_9_ = 0;
v_env_10_ = l_Lean_Environment_setRecordingDeps(v_env_8_, v___x_9_);
v___x_11_ = lean_st_ref_get(v___y_3_);
v_toCold_12_ = lean_ctor_get(v___y_4_, 0);
v_mctx_13_ = lean_ctor_get(v___x_11_, 0);
lean_inc_ref(v_mctx_13_);
lean_dec(v___x_11_);
v_lctx_14_ = lean_ctor_get(v___y_2_, 2);
v_options_15_ = lean_ctor_get(v_toCold_12_, 2);
lean_inc_ref(v_options_15_);
lean_inc_ref(v_lctx_14_);
v___x_16_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_16_, 0, v_env_10_);
lean_ctor_set(v___x_16_, 1, v_mctx_13_);
lean_ctor_set(v___x_16_, 2, v_lctx_14_);
lean_ctor_set(v___x_16_, 3, v_options_15_);
v___x_17_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_17_, 0, v___x_16_);
lean_ctor_set(v___x_17_, 1, v_msgData_1_);
v___x_18_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_18_, 0, v___x_17_);
return v___x_18_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1_ = stack[0].m_obj;
lean_object* v___y_2_ = stack[1].m_obj;
lean_object* v___y_3_ = stack[2].m_obj;
lean_object* v___y_4_ = stack[3].m_obj;
lean_object* v___y_5_ = stack[4].m_obj;
lean_object* v_res_19_;
v_res_19_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected_spec__0_spec__0(v_msgData_1_, v___y_2_, v___y_3_, v___y_4_, v___y_5_);
stack->m_obj
 = v_res_19_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected_spec__0_spec__0___boxed(lean_object* v_msgData_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected_spec__0_spec__0(v_msgData_20_, v___y_21_, v___y_22_, v___y_23_, v___y_24_);
lean_dec(v___y_24_);
lean_dec_ref(v___y_23_);
lean_dec(v___y_22_);
lean_dec_ref(v___y_21_);
return v_res_26_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected_spec__0___redArg(lean_object* v_msg_27_, lean_object* v___y_28_, lean_object* v___y_29_, lean_object* v___y_30_, lean_object* v___y_31_){
_start:
{
lean_object* v_ref_33_; lean_object* v___x_34_; lean_object* v_a_35_; lean_object* v___x_37_; uint8_t v_isShared_38_; uint8_t v_isSharedCheck_43_; 
v_ref_33_ = lean_ctor_get(v___y_30_, 2);
v___x_34_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected_spec__0_spec__0(v_msg_27_, v___y_28_, v___y_29_, v___y_30_, v___y_31_);
v_a_35_ = lean_ctor_get(v___x_34_, 0);
v_isSharedCheck_43_ = !lean_is_exclusive(v___x_34_);
if (v_isSharedCheck_43_ == 0)
{
v___x_37_ = v___x_34_;
v_isShared_38_ = v_isSharedCheck_43_;
goto v_resetjp_36_;
}
else
{
lean_inc(v_a_35_);
lean_dec(v___x_34_);
v___x_37_ = lean_box(0);
v_isShared_38_ = v_isSharedCheck_43_;
goto v_resetjp_36_;
}
v_resetjp_36_:
{
lean_object* v___x_39_; lean_object* v___x_41_; 
lean_inc(v_ref_33_);
v___x_39_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_39_, 0, v_ref_33_);
lean_ctor_set(v___x_39_, 1, v_a_35_);
if (v_isShared_38_ == 0)
{
lean_ctor_set_tag(v___x_37_, 1);
lean_ctor_set(v___x_37_, 0, v___x_39_);
v___x_41_ = v___x_37_;
goto v_reusejp_40_;
}
else
{
lean_object* v_reuseFailAlloc_42_; 
v_reuseFailAlloc_42_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_42_, 0, v___x_39_);
v___x_41_ = v_reuseFailAlloc_42_;
goto v_reusejp_40_;
}
v_reusejp_40_:
{
return v___x_41_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_27_ = stack[0].m_obj;
lean_object* v___y_28_ = stack[1].m_obj;
lean_object* v___y_29_ = stack[2].m_obj;
lean_object* v___y_30_ = stack[3].m_obj;
lean_object* v___y_31_ = stack[4].m_obj;
lean_object* v_res_44_;
v_res_44_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected_spec__0___redArg(v_msg_27_, v___y_28_, v___y_29_, v___y_30_, v___y_31_);
stack->m_obj
 = v_res_44_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected_spec__0___redArg___boxed(lean_object* v_msg_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_, lean_object* v___y_49_, lean_object* v___y_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected_spec__0___redArg(v_msg_45_, v___y_46_, v___y_47_, v___y_48_, v___y_49_);
lean_dec(v___y_49_);
lean_dec_ref(v___y_48_);
lean_dec(v___y_47_);
lean_dec_ref(v___y_46_);
return v_res_51_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg___closed__1(void){
_start:
{
lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_53_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg___closed__0));
v___x_54_ = l_Lean_stringToMessageData(v___x_53_);
return v___x_54_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg(lean_object* v_type_55_, lean_object* v_a_56_, lean_object* v_a_57_, lean_object* v_a_58_, lean_object* v_a_59_){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_61_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg___closed__1, &l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg___closed__1);
v___x_62_ = l_Lean_indentExpr(v_type_55_);
v___x_63_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_63_, 0, v___x_61_);
lean_ctor_set(v___x_63_, 1, v___x_62_);
v___x_64_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected_spec__0___redArg(v___x_63_, v_a_56_, v_a_57_, v_a_58_, v_a_59_);
return v___x_64_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_55_ = stack[0].m_obj;
lean_object* v_a_56_ = stack[1].m_obj;
lean_object* v_a_57_ = stack[2].m_obj;
lean_object* v_a_58_ = stack[3].m_obj;
lean_object* v_a_59_ = stack[4].m_obj;
lean_object* v_res_65_;
v_res_65_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg(v_type_55_, v_a_56_, v_a_57_, v_a_58_, v_a_59_);
stack->m_obj
 = v_res_65_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg___boxed(lean_object* v_type_66_, lean_object* v_a_67_, lean_object* v_a_68_, lean_object* v_a_69_, lean_object* v_a_70_, lean_object* v_a_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg(v_type_66_, v_a_67_, v_a_68_, v_a_69_, v_a_70_);
lean_dec(v_a_70_);
lean_dec_ref(v_a_69_);
lean_dec(v_a_68_);
lean_dec_ref(v_a_67_);
return v_res_72_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected(lean_object* v_00_u03b1_73_, lean_object* v_type_74_, lean_object* v_a_75_, lean_object* v_a_76_, lean_object* v_a_77_, lean_object* v_a_78_){
_start:
{
lean_object* v___x_80_; 
v___x_80_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg(v_type_74_, v_a_75_, v_a_76_, v_a_77_, v_a_78_);
return v___x_80_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_74_ = stack[1].m_obj;
lean_object* v_a_75_ = stack[2].m_obj;
lean_object* v_a_76_ = stack[3].m_obj;
lean_object* v_a_77_ = stack[4].m_obj;
lean_object* v_a_78_ = stack[5].m_obj;
lean_object* v_res_81_;
v_res_81_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected(lean_box(0), v_type_74_, v_a_75_, v_a_76_, v_a_77_, v_a_78_);
stack->m_obj
 = v_res_81_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___boxed(lean_object* v_00_u03b1_82_, lean_object* v_type_83_, lean_object* v_a_84_, lean_object* v_a_85_, lean_object* v_a_86_, lean_object* v_a_87_, lean_object* v_a_88_){
_start:
{
lean_object* v_res_89_; 
v_res_89_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected(v_00_u03b1_82_, v_type_83_, v_a_84_, v_a_85_, v_a_86_, v_a_87_);
lean_dec(v_a_87_);
lean_dec_ref(v_a_86_);
lean_dec(v_a_85_);
lean_dec_ref(v_a_84_);
return v_res_89_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected_spec__0(lean_object* v_00_u03b1_90_, lean_object* v_msg_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_){
_start:
{
lean_object* v___x_97_; 
v___x_97_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected_spec__0___redArg(v_msg_91_, v___y_92_, v___y_93_, v___y_94_, v___y_95_);
return v___x_97_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_91_ = stack[1].m_obj;
lean_object* v___y_92_ = stack[2].m_obj;
lean_object* v___y_93_ = stack[3].m_obj;
lean_object* v___y_94_ = stack[4].m_obj;
lean_object* v___y_95_ = stack[5].m_obj;
lean_object* v_res_98_;
v_res_98_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected_spec__0(lean_box(0), v_msg_91_, v___y_92_, v___y_93_, v___y_94_, v___y_95_);
stack->m_obj
 = v_res_98_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected_spec__0___boxed(lean_object* v_00_u03b1_99_, lean_object* v_msg_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_){
_start:
{
lean_object* v_res_106_; 
v_res_106_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected_spec__0(v_00_u03b1_99_, v_msg_100_, v___y_101_, v___y_102_, v___y_103_, v___y_104_);
lean_dec(v___y_104_);
lean_dec_ref(v___y_103_);
lean_dec(v___y_102_);
lean_dec_ref(v___y_101_);
return v_res_106_;
}
}
static lean_object* _init_l_Lean_Meta_getInductiveUniverseAndParams___closed__0(void){
_start:
{
lean_object* v___x_107_; lean_object* v_dummy_108_; 
v___x_107_ = lean_box(0);
v_dummy_108_ = l_Lean_Expr_sort___override(v___x_107_);
return v_dummy_108_;
}
}
lean_object* l_Lean_Meta_getInductiveUniverseAndParams(lean_object* v_type_109_, lean_object* v_a_110_, lean_object* v_a_111_, lean_object* v_a_112_, lean_object* v_a_113_){
_start:
{
lean_object* v___x_115_; 
v___x_115_ = l_Lean_Meta_whnfD(v_type_109_, v_a_110_, v_a_111_, v_a_112_, v_a_113_);
if (lean_obj_tag(v___x_115_) == 0)
{
lean_object* v_a_116_; lean_object* v___x_118_; uint8_t v_isShared_119_; uint8_t v_isSharedCheck_145_; 
v_a_116_ = lean_ctor_get(v___x_115_, 0);
v_isSharedCheck_145_ = !lean_is_exclusive(v___x_115_);
if (v_isSharedCheck_145_ == 0)
{
v___x_118_ = v___x_115_;
v_isShared_119_ = v_isSharedCheck_145_;
goto v_resetjp_117_;
}
else
{
lean_inc(v_a_116_);
lean_dec(v___x_115_);
v___x_118_ = lean_box(0);
v_isShared_119_ = v_isSharedCheck_145_;
goto v_resetjp_117_;
}
v_resetjp_117_:
{
lean_object* v___x_120_; 
v___x_120_ = l_Lean_Expr_getAppFn(v_a_116_);
if (lean_obj_tag(v___x_120_) == 4)
{
lean_object* v_declName_121_; lean_object* v_us_122_; lean_object* v___x_123_; lean_object* v_env_124_; uint8_t v___x_125_; lean_object* v___x_126_; 
v_declName_121_ = lean_ctor_get(v___x_120_, 0);
lean_inc(v_declName_121_);
v_us_122_ = lean_ctor_get(v___x_120_, 1);
lean_inc(v_us_122_);
lean_dec_ref_known(v___x_120_, 2);
v___x_123_ = lean_st_ref_get(v_a_113_);
v_env_124_ = lean_ctor_get(v___x_123_, 0);
lean_inc_ref(v_env_124_);
lean_dec(v___x_123_);
v___x_125_ = 0;
v___x_126_ = l_Lean_Environment_find_x3f(v_env_124_, v_declName_121_, v___x_125_);
if (lean_obj_tag(v___x_126_) == 0)
{
lean_object* v___x_127_; 
lean_dec(v_us_122_);
lean_del_object(v___x_118_);
v___x_127_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg(v_a_116_, v_a_110_, v_a_111_, v_a_112_, v_a_113_);
return v___x_127_;
}
else
{
lean_object* v_val_128_; 
v_val_128_ = lean_ctor_get(v___x_126_, 0);
lean_inc(v_val_128_);
lean_dec_ref_known(v___x_126_, 1);
if (lean_obj_tag(v_val_128_) == 5)
{
lean_object* v_val_129_; lean_object* v_numParams_130_; lean_object* v_nargs_131_; lean_object* v_dummy_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_141_; 
v_val_129_ = lean_ctor_get(v_val_128_, 0);
lean_inc_ref(v_val_129_);
lean_dec_ref_known(v_val_128_, 1);
v_numParams_130_ = lean_ctor_get(v_val_129_, 1);
lean_inc(v_numParams_130_);
lean_dec_ref(v_val_129_);
v_nargs_131_ = l_Lean_Expr_getAppNumArgs(v_a_116_);
v_dummy_132_ = lean_obj_once(&l_Lean_Meta_getInductiveUniverseAndParams___closed__0, &l_Lean_Meta_getInductiveUniverseAndParams___closed__0_once, _init_l_Lean_Meta_getInductiveUniverseAndParams___closed__0);
lean_inc(v_nargs_131_);
v___x_133_ = lean_mk_array(v_nargs_131_, v_dummy_132_);
v___x_134_ = lean_unsigned_to_nat(1u);
v___x_135_ = lean_nat_sub(v_nargs_131_, v___x_134_);
lean_dec(v_nargs_131_);
v___x_136_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_116_, v___x_133_, v___x_135_);
v___x_137_ = lean_unsigned_to_nat(0u);
v___x_138_ = l_Array_extract___redArg(v___x_136_, v___x_137_, v_numParams_130_);
lean_dec_ref(v___x_136_);
v___x_139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_139_, 0, v_us_122_);
lean_ctor_set(v___x_139_, 1, v___x_138_);
if (v_isShared_119_ == 0)
{
lean_ctor_set(v___x_118_, 0, v___x_139_);
v___x_141_ = v___x_118_;
goto v_reusejp_140_;
}
else
{
lean_object* v_reuseFailAlloc_142_; 
v_reuseFailAlloc_142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_142_, 0, v___x_139_);
v___x_141_ = v_reuseFailAlloc_142_;
goto v_reusejp_140_;
}
v_reusejp_140_:
{
return v___x_141_;
}
}
else
{
lean_object* v___x_143_; 
lean_dec(v_val_128_);
lean_dec(v_us_122_);
lean_del_object(v___x_118_);
v___x_143_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg(v_a_116_, v_a_110_, v_a_111_, v_a_112_, v_a_113_);
return v___x_143_;
}
}
}
else
{
lean_object* v___x_144_; 
lean_dec_ref(v___x_120_);
lean_del_object(v___x_118_);
v___x_144_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg(v_a_116_, v_a_110_, v_a_111_, v_a_112_, v_a_113_);
return v___x_144_;
}
}
}
else
{
lean_object* v_a_146_; lean_object* v___x_148_; uint8_t v_isShared_149_; uint8_t v_isSharedCheck_153_; 
v_a_146_ = lean_ctor_get(v___x_115_, 0);
v_isSharedCheck_153_ = !lean_is_exclusive(v___x_115_);
if (v_isSharedCheck_153_ == 0)
{
v___x_148_ = v___x_115_;
v_isShared_149_ = v_isSharedCheck_153_;
goto v_resetjp_147_;
}
else
{
lean_inc(v_a_146_);
lean_dec(v___x_115_);
v___x_148_ = lean_box(0);
v_isShared_149_ = v_isSharedCheck_153_;
goto v_resetjp_147_;
}
v_resetjp_147_:
{
lean_object* v___x_151_; 
if (v_isShared_149_ == 0)
{
v___x_151_ = v___x_148_;
goto v_reusejp_150_;
}
else
{
lean_object* v_reuseFailAlloc_152_; 
v_reuseFailAlloc_152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_152_, 0, v_a_146_);
v___x_151_ = v_reuseFailAlloc_152_;
goto v_reusejp_150_;
}
v_reusejp_150_:
{
return v___x_151_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_getInductiveUniverseAndParams_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_109_ = stack[0].m_obj;
lean_object* v_a_110_ = stack[1].m_obj;
lean_object* v_a_111_ = stack[2].m_obj;
lean_object* v_a_112_ = stack[3].m_obj;
lean_object* v_a_113_ = stack[4].m_obj;
lean_object* v_res_154_;
v_res_154_ = l_Lean_Meta_getInductiveUniverseAndParams(v_type_109_, v_a_110_, v_a_111_, v_a_112_, v_a_113_);
stack->m_obj
 = v_res_154_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInductiveUniverseAndParams___boxed(lean_object* v_type_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_, lean_object* v_a_160_){
_start:
{
lean_object* v_res_161_; 
v_res_161_ = l_Lean_Meta_getInductiveUniverseAndParams(v_type_155_, v_a_156_, v_a_157_, v_a_158_, v_a_159_);
lean_dec(v_a_159_);
lean_dec_ref(v_a_158_);
lean_dec(v_a_157_);
lean_dec_ref(v_a_156_);
return v_res_161_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof(lean_object* v_lhs_175_, lean_object* v_rhs_176_, lean_object* v_a_177_, lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_){
_start:
{
lean_object* v___x_182_; 
lean_inc(v_a_180_);
lean_inc_ref(v_a_179_);
lean_inc(v_a_178_);
lean_inc_ref(v_a_177_);
lean_inc_ref(v_lhs_175_);
v___x_182_ = lean_infer_type(v_lhs_175_, v_a_177_, v_a_178_, v_a_179_, v_a_180_);
if (lean_obj_tag(v___x_182_) == 0)
{
lean_object* v_a_183_; lean_object* v___x_184_; 
v_a_183_ = lean_ctor_get(v___x_182_, 0);
lean_inc(v_a_183_);
lean_dec_ref_known(v___x_182_, 1);
lean_inc(v_a_180_);
lean_inc_ref(v_a_179_);
lean_inc(v_a_178_);
lean_inc_ref(v_a_177_);
lean_inc_ref(v_rhs_176_);
v___x_184_ = lean_infer_type(v_rhs_176_, v_a_177_, v_a_178_, v_a_179_, v_a_180_);
if (lean_obj_tag(v___x_184_) == 0)
{
lean_object* v_a_185_; lean_object* v___x_186_; 
v_a_185_ = lean_ctor_get(v___x_184_, 0);
lean_inc(v_a_185_);
lean_dec_ref_known(v___x_184_, 1);
lean_inc(v_a_183_);
v___x_186_ = l_Lean_Meta_getLevel(v_a_183_, v_a_177_, v_a_178_, v_a_179_, v_a_180_);
if (lean_obj_tag(v___x_186_) == 0)
{
lean_object* v_a_187_; lean_object* v___x_188_; 
v_a_187_ = lean_ctor_get(v___x_186_, 0);
lean_inc(v_a_187_);
lean_dec_ref_known(v___x_186_, 1);
lean_inc(v_a_185_);
lean_inc(v_a_183_);
v___x_188_ = l_Lean_Meta_isExprDefEq(v_a_183_, v_a_185_, v_a_177_, v_a_178_, v_a_179_, v_a_180_);
if (lean_obj_tag(v___x_188_) == 0)
{
lean_object* v_a_189_; lean_object* v___x_191_; uint8_t v_isShared_192_; uint8_t v_isSharedCheck_218_; 
v_a_189_ = lean_ctor_get(v___x_188_, 0);
v_isSharedCheck_218_ = !lean_is_exclusive(v___x_188_);
if (v_isSharedCheck_218_ == 0)
{
v___x_191_ = v___x_188_;
v_isShared_192_ = v_isSharedCheck_218_;
goto v_resetjp_190_;
}
else
{
lean_inc(v_a_189_);
lean_dec(v___x_188_);
v___x_191_ = lean_box(0);
v_isShared_192_ = v_isSharedCheck_218_;
goto v_resetjp_190_;
}
v_resetjp_190_:
{
uint8_t v___x_193_; 
v___x_193_ = lean_unbox(v_a_189_);
lean_dec(v_a_189_);
if (v___x_193_ == 0)
{
lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_204_; 
v___x_194_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__1));
v___x_195_ = lean_box(0);
v___x_196_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_196_, 0, v_a_187_);
lean_ctor_set(v___x_196_, 1, v___x_195_);
lean_inc_ref(v___x_196_);
v___x_197_ = l_Lean_mkConst(v___x_194_, v___x_196_);
lean_inc_ref(v_lhs_175_);
lean_inc(v_a_183_);
v___x_198_ = l_Lean_mkApp4(v___x_197_, v_a_183_, v_lhs_175_, v_a_185_, v_rhs_176_);
v___x_199_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__3));
v___x_200_ = l_Lean_mkConst(v___x_199_, v___x_196_);
v___x_201_ = l_Lean_mkAppB(v___x_200_, v_a_183_, v_lhs_175_);
v___x_202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_202_, 0, v___x_198_);
lean_ctor_set(v___x_202_, 1, v___x_201_);
if (v_isShared_192_ == 0)
{
lean_ctor_set(v___x_191_, 0, v___x_202_);
v___x_204_ = v___x_191_;
goto v_reusejp_203_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v___x_202_);
v___x_204_ = v_reuseFailAlloc_205_;
goto v_reusejp_203_;
}
v_reusejp_203_:
{
return v___x_204_;
}
}
else
{
lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_216_; 
lean_dec(v_a_185_);
v___x_206_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__5));
v___x_207_ = lean_box(0);
v___x_208_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_208_, 0, v_a_187_);
lean_ctor_set(v___x_208_, 1, v___x_207_);
lean_inc_ref(v___x_208_);
v___x_209_ = l_Lean_mkConst(v___x_206_, v___x_208_);
lean_inc_ref(v_lhs_175_);
lean_inc(v_a_183_);
v___x_210_ = l_Lean_mkApp3(v___x_209_, v_a_183_, v_lhs_175_, v_rhs_176_);
v___x_211_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__6));
v___x_212_ = l_Lean_mkConst(v___x_211_, v___x_208_);
v___x_213_ = l_Lean_mkAppB(v___x_212_, v_a_183_, v_lhs_175_);
v___x_214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_214_, 0, v___x_210_);
lean_ctor_set(v___x_214_, 1, v___x_213_);
if (v_isShared_192_ == 0)
{
lean_ctor_set(v___x_191_, 0, v___x_214_);
v___x_216_ = v___x_191_;
goto v_reusejp_215_;
}
else
{
lean_object* v_reuseFailAlloc_217_; 
v_reuseFailAlloc_217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_217_, 0, v___x_214_);
v___x_216_ = v_reuseFailAlloc_217_;
goto v_reusejp_215_;
}
v_reusejp_215_:
{
return v___x_216_;
}
}
}
}
else
{
lean_object* v_a_219_; lean_object* v___x_221_; uint8_t v_isShared_222_; uint8_t v_isSharedCheck_226_; 
lean_dec(v_a_187_);
lean_dec(v_a_185_);
lean_dec(v_a_183_);
lean_dec_ref(v_rhs_176_);
lean_dec_ref(v_lhs_175_);
v_a_219_ = lean_ctor_get(v___x_188_, 0);
v_isSharedCheck_226_ = !lean_is_exclusive(v___x_188_);
if (v_isSharedCheck_226_ == 0)
{
v___x_221_ = v___x_188_;
v_isShared_222_ = v_isSharedCheck_226_;
goto v_resetjp_220_;
}
else
{
lean_inc(v_a_219_);
lean_dec(v___x_188_);
v___x_221_ = lean_box(0);
v_isShared_222_ = v_isSharedCheck_226_;
goto v_resetjp_220_;
}
v_resetjp_220_:
{
lean_object* v___x_224_; 
if (v_isShared_222_ == 0)
{
v___x_224_ = v___x_221_;
goto v_reusejp_223_;
}
else
{
lean_object* v_reuseFailAlloc_225_; 
v_reuseFailAlloc_225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_225_, 0, v_a_219_);
v___x_224_ = v_reuseFailAlloc_225_;
goto v_reusejp_223_;
}
v_reusejp_223_:
{
return v___x_224_;
}
}
}
}
else
{
lean_object* v_a_227_; lean_object* v___x_229_; uint8_t v_isShared_230_; uint8_t v_isSharedCheck_234_; 
lean_dec(v_a_185_);
lean_dec(v_a_183_);
lean_dec_ref(v_rhs_176_);
lean_dec_ref(v_lhs_175_);
v_a_227_ = lean_ctor_get(v___x_186_, 0);
v_isSharedCheck_234_ = !lean_is_exclusive(v___x_186_);
if (v_isSharedCheck_234_ == 0)
{
v___x_229_ = v___x_186_;
v_isShared_230_ = v_isSharedCheck_234_;
goto v_resetjp_228_;
}
else
{
lean_inc(v_a_227_);
lean_dec(v___x_186_);
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
else
{
lean_object* v_a_235_; lean_object* v___x_237_; uint8_t v_isShared_238_; uint8_t v_isSharedCheck_242_; 
lean_dec(v_a_183_);
lean_dec_ref(v_rhs_176_);
lean_dec_ref(v_lhs_175_);
v_a_235_ = lean_ctor_get(v___x_184_, 0);
v_isSharedCheck_242_ = !lean_is_exclusive(v___x_184_);
if (v_isSharedCheck_242_ == 0)
{
v___x_237_ = v___x_184_;
v_isShared_238_ = v_isSharedCheck_242_;
goto v_resetjp_236_;
}
else
{
lean_inc(v_a_235_);
lean_dec(v___x_184_);
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
lean_object* v_a_243_; lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_250_; 
lean_dec_ref(v_rhs_176_);
lean_dec_ref(v_lhs_175_);
v_a_243_ = lean_ctor_get(v___x_182_, 0);
v_isSharedCheck_250_ = !lean_is_exclusive(v___x_182_);
if (v_isSharedCheck_250_ == 0)
{
v___x_245_ = v___x_182_;
v_isShared_246_ = v_isSharedCheck_250_;
goto v_resetjp_244_;
}
else
{
lean_inc(v_a_243_);
lean_dec(v___x_182_);
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_250_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
lean_object* v___x_248_; 
if (v_isShared_246_ == 0)
{
v___x_248_ = v___x_245_;
goto v_reusejp_247_;
}
else
{
lean_object* v_reuseFailAlloc_249_; 
v_reuseFailAlloc_249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_249_, 0, v_a_243_);
v___x_248_ = v_reuseFailAlloc_249_;
goto v_reusejp_247_;
}
v_reusejp_247_:
{
return v___x_248_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof_0interp(lean_interpreter_value* stack)
{
lean_object* v_lhs_175_ = stack[0].m_obj;
lean_object* v_rhs_176_ = stack[1].m_obj;
lean_object* v_a_177_ = stack[2].m_obj;
lean_object* v_a_178_ = stack[3].m_obj;
lean_object* v_a_179_ = stack[4].m_obj;
lean_object* v_a_180_ = stack[5].m_obj;
lean_object* v_res_251_;
v_res_251_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof(v_lhs_175_, v_rhs_176_, v_a_177_, v_a_178_, v_a_179_, v_a_180_);
stack->m_obj
 = v_res_251_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___boxed(lean_object* v_lhs_252_, lean_object* v_rhs_253_, lean_object* v_a_254_, lean_object* v_a_255_, lean_object* v_a_256_, lean_object* v_a_257_, lean_object* v_a_258_){
_start:
{
lean_object* v_res_259_; 
v_res_259_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof(v_lhs_252_, v_rhs_253_, v_a_254_, v_a_255_, v_a_256_, v_a_257_);
lean_dec(v_a_257_);
lean_dec_ref(v_a_256_);
lean_dec(v_a_255_);
lean_dec_ref(v_a_254_);
return v_res_259_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0_spec__0___redArg___lam__0(lean_object* v_k_260_, lean_object* v_b_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_){
_start:
{
lean_object* v___x_267_; 
lean_inc(v___y_265_);
lean_inc_ref(v___y_264_);
lean_inc(v___y_263_);
lean_inc_ref(v___y_262_);
v___x_267_ = lean_apply_6(v_k_260_, v_b_261_, v___y_262_, v___y_263_, v___y_264_, v___y_265_, lean_box(0));
return v___x_267_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0_spec__0___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_260_ = stack[0].m_obj;
lean_object* v_b_261_ = stack[1].m_obj;
lean_object* v___y_262_ = stack[2].m_obj;
lean_object* v___y_263_ = stack[3].m_obj;
lean_object* v___y_264_ = stack[4].m_obj;
lean_object* v___y_265_ = stack[5].m_obj;
lean_object* v_res_268_;
v_res_268_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0_spec__0___redArg___lam__0(v_k_260_, v_b_261_, v___y_262_, v___y_263_, v___y_264_, v___y_265_);
stack->m_obj
 = v_res_268_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_k_269_, lean_object* v_b_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_){
_start:
{
lean_object* v_res_276_; 
v_res_276_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0_spec__0___redArg___lam__0(v_k_269_, v_b_270_, v___y_271_, v___y_272_, v___y_273_, v___y_274_);
lean_dec(v___y_274_);
lean_dec_ref(v___y_273_);
lean_dec(v___y_272_);
lean_dec_ref(v___y_271_);
return v_res_276_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0_spec__0___redArg(lean_object* v_name_277_, uint8_t v_bi_278_, lean_object* v_type_279_, lean_object* v_k_280_, uint8_t v_kind_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_){
_start:
{
lean_object* v___f_287_; lean_object* v___x_288_; 
v___f_287_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0_spec__0___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_287_, 0, v_k_280_);
v___x_288_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_277_, v_bi_278_, v_type_279_, v___f_287_, v_kind_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_);
if (lean_obj_tag(v___x_288_) == 0)
{
lean_object* v_a_289_; lean_object* v___x_291_; uint8_t v_isShared_292_; uint8_t v_isSharedCheck_296_; 
v_a_289_ = lean_ctor_get(v___x_288_, 0);
v_isSharedCheck_296_ = !lean_is_exclusive(v___x_288_);
if (v_isSharedCheck_296_ == 0)
{
v___x_291_ = v___x_288_;
v_isShared_292_ = v_isSharedCheck_296_;
goto v_resetjp_290_;
}
else
{
lean_inc(v_a_289_);
lean_dec(v___x_288_);
v___x_291_ = lean_box(0);
v_isShared_292_ = v_isSharedCheck_296_;
goto v_resetjp_290_;
}
v_resetjp_290_:
{
lean_object* v___x_294_; 
if (v_isShared_292_ == 0)
{
v___x_294_ = v___x_291_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v_a_289_);
v___x_294_ = v_reuseFailAlloc_295_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
return v___x_294_;
}
}
}
else
{
lean_object* v_a_297_; lean_object* v___x_299_; uint8_t v_isShared_300_; uint8_t v_isSharedCheck_304_; 
v_a_297_ = lean_ctor_get(v___x_288_, 0);
v_isSharedCheck_304_ = !lean_is_exclusive(v___x_288_);
if (v_isSharedCheck_304_ == 0)
{
v___x_299_ = v___x_288_;
v_isShared_300_ = v_isSharedCheck_304_;
goto v_resetjp_298_;
}
else
{
lean_inc(v_a_297_);
lean_dec(v___x_288_);
v___x_299_ = lean_box(0);
v_isShared_300_ = v_isSharedCheck_304_;
goto v_resetjp_298_;
}
v_resetjp_298_:
{
lean_object* v___x_302_; 
if (v_isShared_300_ == 0)
{
v___x_302_ = v___x_299_;
goto v_reusejp_301_;
}
else
{
lean_object* v_reuseFailAlloc_303_; 
v_reuseFailAlloc_303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_303_, 0, v_a_297_);
v___x_302_ = v_reuseFailAlloc_303_;
goto v_reusejp_301_;
}
v_reusejp_301_:
{
return v___x_302_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_277_ = stack[0].m_obj;
uint8_t v_bi_278_ = stack[1].m_num;
lean_object* v_type_279_ = stack[2].m_obj;
lean_object* v_k_280_ = stack[3].m_obj;
uint8_t v_kind_281_ = stack[4].m_num;
lean_object* v___y_282_ = stack[5].m_obj;
lean_object* v___y_283_ = stack[6].m_obj;
lean_object* v___y_284_ = stack[7].m_obj;
lean_object* v___y_285_ = stack[8].m_obj;
lean_object* v_res_305_;
v_res_305_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0_spec__0___redArg(v_name_277_, v_bi_278_, v_type_279_, v_k_280_, v_kind_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_);
stack->m_obj
 = v_res_305_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0_spec__0___redArg___boxed(lean_object* v_name_306_, lean_object* v_bi_307_, lean_object* v_type_308_, lean_object* v_k_309_, lean_object* v_kind_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_){
_start:
{
uint8_t v_bi_boxed_316_; uint8_t v_kind_boxed_317_; lean_object* v_res_318_; 
v_bi_boxed_316_ = lean_unbox(v_bi_307_);
v_kind_boxed_317_ = lean_unbox(v_kind_310_);
v_res_318_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0_spec__0___redArg(v_name_306_, v_bi_boxed_316_, v_type_308_, v_k_309_, v_kind_boxed_317_, v___y_311_, v___y_312_, v___y_313_, v___y_314_);
lean_dec(v___y_314_);
lean_dec_ref(v___y_313_);
lean_dec(v___y_312_);
lean_dec_ref(v___y_311_);
return v_res_318_;
}
}
lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0___redArg(lean_object* v_name_319_, lean_object* v_type_320_, lean_object* v_k_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_){
_start:
{
uint8_t v___x_327_; uint8_t v___x_328_; lean_object* v___x_329_; 
v___x_327_ = 0;
v___x_328_ = 0;
v___x_329_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0_spec__0___redArg(v_name_319_, v___x_327_, v_type_320_, v_k_321_, v___x_328_, v___y_322_, v___y_323_, v___y_324_, v___y_325_);
return v___x_329_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_319_ = stack[0].m_obj;
lean_object* v_type_320_ = stack[1].m_obj;
lean_object* v_k_321_ = stack[2].m_obj;
lean_object* v___y_322_ = stack[3].m_obj;
lean_object* v___y_323_ = stack[4].m_obj;
lean_object* v___y_324_ = stack[5].m_obj;
lean_object* v___y_325_ = stack[6].m_obj;
lean_object* v_res_330_;
v_res_330_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0___redArg(v_name_319_, v_type_320_, v_k_321_, v___y_322_, v___y_323_, v___y_324_, v___y_325_);
stack->m_obj
 = v_res_330_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0___redArg___boxed(lean_object* v_name_331_, lean_object* v_type_332_, lean_object* v_k_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_){
_start:
{
lean_object* v_res_339_; 
v_res_339_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0___redArg(v_name_331_, v_type_332_, v_k_333_, v___y_334_, v___y_335_, v___y_336_, v___y_337_);
lean_dec(v___y_337_);
lean_dec_ref(v___y_336_);
lean_dec(v___y_335_);
lean_dec_ref(v___y_334_);
return v_res_339_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___redArg___lam__0___boxed(lean_object* v_i_340_, lean_object* v_newEqs_341_, lean_object* v_newRefls_342_, lean_object* v_snd_343_, lean_object* v_targets_344_, lean_object* v_targetsNew_345_, lean_object* v_k_346_, lean_object* v_newEq_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_){
_start:
{
lean_object* v_res_353_; 
v_res_353_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___redArg___lam__0(v_i_340_, v_newEqs_341_, v_newRefls_342_, v_snd_343_, v_targets_344_, v_targetsNew_345_, v_k_346_, v_newEq_347_, v___y_348_, v___y_349_, v___y_350_, v___y_351_);
lean_dec(v___y_351_);
lean_dec_ref(v___y_350_);
lean_dec(v___y_349_);
lean_dec_ref(v___y_348_);
lean_dec(v_i_340_);
return v_res_353_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___redArg(lean_object* v_targets_357_, lean_object* v_targetsNew_358_, lean_object* v_k_359_, lean_object* v_i_360_, lean_object* v_newEqs_361_, lean_object* v_newRefls_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_){
_start:
{
lean_object* v___x_368_; uint8_t v___x_369_; 
v___x_368_ = lean_array_get_size(v_targets_357_);
v___x_369_ = lean_nat_dec_lt(v_i_360_, v___x_368_);
if (v___x_369_ == 0)
{
lean_object* v___x_370_; 
lean_dec(v_i_360_);
lean_dec_ref(v_targetsNew_358_);
lean_dec_ref(v_targets_357_);
lean_inc(v_a_366_);
lean_inc_ref(v_a_365_);
lean_inc(v_a_364_);
lean_inc_ref(v_a_363_);
v___x_370_ = lean_apply_7(v_k_359_, v_newEqs_361_, v_newRefls_362_, v_a_363_, v_a_364_, v_a_365_, v_a_366_, lean_box(0));
return v___x_370_;
}
else
{
lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_371_ = l_Lean_instInhabitedExpr;
v___x_372_ = lean_array_get_borrowed(v___x_371_, v_targets_357_, v_i_360_);
v___x_373_ = lean_array_get_borrowed(v___x_371_, v_targetsNew_358_, v_i_360_);
lean_inc(v___x_373_);
lean_inc(v___x_372_);
v___x_374_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof(v___x_372_, v___x_373_, v_a_363_, v_a_364_, v_a_365_, v_a_366_);
if (lean_obj_tag(v___x_374_) == 0)
{
lean_object* v_a_375_; lean_object* v_fst_376_; lean_object* v_snd_377_; lean_object* v___f_378_; lean_object* v___x_379_; lean_object* v___x_380_; 
v_a_375_ = lean_ctor_get(v___x_374_, 0);
lean_inc(v_a_375_);
lean_dec_ref_known(v___x_374_, 1);
v_fst_376_ = lean_ctor_get(v_a_375_, 0);
lean_inc(v_fst_376_);
v_snd_377_ = lean_ctor_get(v_a_375_, 1);
lean_inc(v_snd_377_);
lean_dec(v_a_375_);
v___f_378_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___redArg___lam__0___boxed), 13, 7);
lean_closure_set(v___f_378_, 0, v_i_360_);
lean_closure_set(v___f_378_, 1, v_newEqs_361_);
lean_closure_set(v___f_378_, 2, v_newRefls_362_);
lean_closure_set(v___f_378_, 3, v_snd_377_);
lean_closure_set(v___f_378_, 4, v_targets_357_);
lean_closure_set(v___f_378_, 5, v_targetsNew_358_);
lean_closure_set(v___f_378_, 6, v_k_359_);
v___x_379_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___redArg___closed__1));
v___x_380_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0___redArg(v___x_379_, v_fst_376_, v___f_378_, v_a_363_, v_a_364_, v_a_365_, v_a_366_);
return v___x_380_;
}
else
{
lean_object* v_a_381_; lean_object* v___x_383_; uint8_t v_isShared_384_; uint8_t v_isSharedCheck_388_; 
lean_dec_ref(v_newRefls_362_);
lean_dec_ref(v_newEqs_361_);
lean_dec(v_i_360_);
lean_dec_ref(v_k_359_);
lean_dec_ref(v_targetsNew_358_);
lean_dec_ref(v_targets_357_);
v_a_381_ = lean_ctor_get(v___x_374_, 0);
v_isSharedCheck_388_ = !lean_is_exclusive(v___x_374_);
if (v_isSharedCheck_388_ == 0)
{
v___x_383_ = v___x_374_;
v_isShared_384_ = v_isSharedCheck_388_;
goto v_resetjp_382_;
}
else
{
lean_inc(v_a_381_);
lean_dec(v___x_374_);
v___x_383_ = lean_box(0);
v_isShared_384_ = v_isSharedCheck_388_;
goto v_resetjp_382_;
}
v_resetjp_382_:
{
lean_object* v___x_386_; 
if (v_isShared_384_ == 0)
{
v___x_386_ = v___x_383_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_387_; 
v_reuseFailAlloc_387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_387_, 0, v_a_381_);
v___x_386_ = v_reuseFailAlloc_387_;
goto v_reusejp_385_;
}
v_reusejp_385_:
{
return v___x_386_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_targets_357_ = stack[0].m_obj;
lean_object* v_targetsNew_358_ = stack[1].m_obj;
lean_object* v_k_359_ = stack[2].m_obj;
lean_object* v_i_360_ = stack[3].m_obj;
lean_object* v_newEqs_361_ = stack[4].m_obj;
lean_object* v_newRefls_362_ = stack[5].m_obj;
lean_object* v_a_363_ = stack[6].m_obj;
lean_object* v_a_364_ = stack[7].m_obj;
lean_object* v_a_365_ = stack[8].m_obj;
lean_object* v_a_366_ = stack[9].m_obj;
lean_object* v_res_389_;
v_res_389_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___redArg(v_targets_357_, v_targetsNew_358_, v_k_359_, v_i_360_, v_newEqs_361_, v_newRefls_362_, v_a_363_, v_a_364_, v_a_365_, v_a_366_);
stack->m_obj
 = v_res_389_;
}
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___redArg___lam__0(lean_object* v_i_390_, lean_object* v_newEqs_391_, lean_object* v_newRefls_392_, lean_object* v_snd_393_, lean_object* v_targets_394_, lean_object* v_targetsNew_395_, lean_object* v_k_396_, lean_object* v_newEq_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_){
_start:
{
lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_403_ = lean_unsigned_to_nat(1u);
v___x_404_ = lean_nat_add(v_i_390_, v___x_403_);
v___x_405_ = lean_array_push(v_newEqs_391_, v_newEq_397_);
v___x_406_ = lean_array_push(v_newRefls_392_, v_snd_393_);
v___x_407_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___redArg(v_targets_394_, v_targetsNew_395_, v_k_396_, v___x_404_, v___x_405_, v___x_406_, v___y_398_, v___y_399_, v___y_400_, v___y_401_);
return v___x_407_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_i_390_ = stack[0].m_obj;
lean_object* v_newEqs_391_ = stack[1].m_obj;
lean_object* v_newRefls_392_ = stack[2].m_obj;
lean_object* v_snd_393_ = stack[3].m_obj;
lean_object* v_targets_394_ = stack[4].m_obj;
lean_object* v_targetsNew_395_ = stack[5].m_obj;
lean_object* v_k_396_ = stack[6].m_obj;
lean_object* v_newEq_397_ = stack[7].m_obj;
lean_object* v___y_398_ = stack[8].m_obj;
lean_object* v___y_399_ = stack[9].m_obj;
lean_object* v___y_400_ = stack[10].m_obj;
lean_object* v___y_401_ = stack[11].m_obj;
lean_object* v_res_408_;
v_res_408_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___redArg___lam__0(v_i_390_, v_newEqs_391_, v_newRefls_392_, v_snd_393_, v_targets_394_, v_targetsNew_395_, v_k_396_, v_newEq_397_, v___y_398_, v___y_399_, v___y_400_, v___y_401_);
stack->m_obj
 = v_res_408_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___redArg___boxed(lean_object* v_targets_409_, lean_object* v_targetsNew_410_, lean_object* v_k_411_, lean_object* v_i_412_, lean_object* v_newEqs_413_, lean_object* v_newRefls_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_, lean_object* v_a_418_, lean_object* v_a_419_){
_start:
{
lean_object* v_res_420_; 
v_res_420_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___redArg(v_targets_409_, v_targetsNew_410_, v_k_411_, v_i_412_, v_newEqs_413_, v_newRefls_414_, v_a_415_, v_a_416_, v_a_417_, v_a_418_);
lean_dec(v_a_418_);
lean_dec_ref(v_a_417_);
lean_dec(v_a_416_);
lean_dec_ref(v_a_415_);
return v_res_420_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop(lean_object* v_00_u03b1_421_, lean_object* v_targets_422_, lean_object* v_targetsNew_423_, lean_object* v_k_424_, lean_object* v_i_425_, lean_object* v_newEqs_426_, lean_object* v_newRefls_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_){
_start:
{
lean_object* v___x_433_; 
v___x_433_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___redArg(v_targets_422_, v_targetsNew_423_, v_k_424_, v_i_425_, v_newEqs_426_, v_newRefls_427_, v_a_428_, v_a_429_, v_a_430_, v_a_431_);
return v___x_433_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_0interp(lean_interpreter_value* stack)
{
lean_object* v_targets_422_ = stack[1].m_obj;
lean_object* v_targetsNew_423_ = stack[2].m_obj;
lean_object* v_k_424_ = stack[3].m_obj;
lean_object* v_i_425_ = stack[4].m_obj;
lean_object* v_newEqs_426_ = stack[5].m_obj;
lean_object* v_newRefls_427_ = stack[6].m_obj;
lean_object* v_a_428_ = stack[7].m_obj;
lean_object* v_a_429_ = stack[8].m_obj;
lean_object* v_a_430_ = stack[9].m_obj;
lean_object* v_a_431_ = stack[10].m_obj;
lean_object* v_res_434_;
v_res_434_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop(lean_box(0), v_targets_422_, v_targetsNew_423_, v_k_424_, v_i_425_, v_newEqs_426_, v_newRefls_427_, v_a_428_, v_a_429_, v_a_430_, v_a_431_);
stack->m_obj
 = v_res_434_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___boxed(lean_object* v_00_u03b1_435_, lean_object* v_targets_436_, lean_object* v_targetsNew_437_, lean_object* v_k_438_, lean_object* v_i_439_, lean_object* v_newEqs_440_, lean_object* v_newRefls_441_, lean_object* v_a_442_, lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_){
_start:
{
lean_object* v_res_447_; 
v_res_447_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop(v_00_u03b1_435_, v_targets_436_, v_targetsNew_437_, v_k_438_, v_i_439_, v_newEqs_440_, v_newRefls_441_, v_a_442_, v_a_443_, v_a_444_, v_a_445_);
lean_dec(v_a_445_);
lean_dec_ref(v_a_444_);
lean_dec(v_a_443_);
lean_dec_ref(v_a_442_);
return v_res_447_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0_spec__0(lean_object* v_00_u03b1_448_, lean_object* v_name_449_, uint8_t v_bi_450_, lean_object* v_type_451_, lean_object* v_k_452_, uint8_t v_kind_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_){
_start:
{
lean_object* v___x_459_; 
v___x_459_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0_spec__0___redArg(v_name_449_, v_bi_450_, v_type_451_, v_k_452_, v_kind_453_, v___y_454_, v___y_455_, v___y_456_, v___y_457_);
return v___x_459_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_449_ = stack[1].m_obj;
uint8_t v_bi_450_ = stack[2].m_num;
lean_object* v_type_451_ = stack[3].m_obj;
lean_object* v_k_452_ = stack[4].m_obj;
uint8_t v_kind_453_ = stack[5].m_num;
lean_object* v___y_454_ = stack[6].m_obj;
lean_object* v___y_455_ = stack[7].m_obj;
lean_object* v___y_456_ = stack[8].m_obj;
lean_object* v___y_457_ = stack[9].m_obj;
lean_object* v_res_460_;
v_res_460_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0_spec__0(lean_box(0), v_name_449_, v_bi_450_, v_type_451_, v_k_452_, v_kind_453_, v___y_454_, v___y_455_, v___y_456_, v___y_457_);
stack->m_obj
 = v_res_460_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0_spec__0___boxed(lean_object* v_00_u03b1_461_, lean_object* v_name_462_, lean_object* v_bi_463_, lean_object* v_type_464_, lean_object* v_k_465_, lean_object* v_kind_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_){
_start:
{
uint8_t v_bi_boxed_472_; uint8_t v_kind_boxed_473_; lean_object* v_res_474_; 
v_bi_boxed_472_ = lean_unbox(v_bi_463_);
v_kind_boxed_473_ = lean_unbox(v_kind_466_);
v_res_474_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0_spec__0(v_00_u03b1_461_, v_name_462_, v_bi_boxed_472_, v_type_464_, v_k_465_, v_kind_boxed_473_, v___y_467_, v___y_468_, v___y_469_, v___y_470_);
lean_dec(v___y_470_);
lean_dec_ref(v___y_469_);
lean_dec(v___y_468_);
lean_dec_ref(v___y_467_);
return v_res_474_;
}
}
lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0(lean_object* v_00_u03b1_475_, lean_object* v_name_476_, lean_object* v_type_477_, lean_object* v_k_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_){
_start:
{
lean_object* v___x_484_; 
v___x_484_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0___redArg(v_name_476_, v_type_477_, v_k_478_, v___y_479_, v___y_480_, v___y_481_, v___y_482_);
return v___x_484_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_476_ = stack[1].m_obj;
lean_object* v_type_477_ = stack[2].m_obj;
lean_object* v_k_478_ = stack[3].m_obj;
lean_object* v___y_479_ = stack[4].m_obj;
lean_object* v___y_480_ = stack[5].m_obj;
lean_object* v___y_481_ = stack[6].m_obj;
lean_object* v___y_482_ = stack[7].m_obj;
lean_object* v_res_485_;
v_res_485_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0(lean_box(0), v_name_476_, v_type_477_, v_k_478_, v___y_479_, v___y_480_, v___y_481_, v___y_482_);
stack->m_obj
 = v_res_485_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0___boxed(lean_object* v_00_u03b1_486_, lean_object* v_name_487_, lean_object* v_type_488_, lean_object* v_k_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_){
_start:
{
lean_object* v_res_495_; 
v_res_495_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0(v_00_u03b1_486_, v_name_487_, v_type_488_, v_k_489_, v___y_490_, v___y_491_, v___y_492_, v___y_493_);
lean_dec(v___y_493_);
lean_dec_ref(v___y_492_);
lean_dec(v___y_491_);
lean_dec_ref(v___y_490_);
return v_res_495_;
}
}
lean_object* l_Lean_Meta_withNewEqs___redArg(lean_object* v_targets_498_, lean_object* v_targetsNew_499_, lean_object* v_k_500_, lean_object* v_a_501_, lean_object* v_a_502_, lean_object* v_a_503_, lean_object* v_a_504_){
_start:
{
lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; 
v___x_506_ = lean_unsigned_to_nat(0u);
v___x_507_ = ((lean_object*)(l_Lean_Meta_withNewEqs___redArg___closed__0));
v___x_508_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___redArg(v_targets_498_, v_targetsNew_499_, v_k_500_, v___x_506_, v___x_507_, v___x_507_, v_a_501_, v_a_502_, v_a_503_, v_a_504_);
return v___x_508_;
}
}
LEAN_EXPORT void l_Lean_Meta_withNewEqs___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_targets_498_ = stack[0].m_obj;
lean_object* v_targetsNew_499_ = stack[1].m_obj;
lean_object* v_k_500_ = stack[2].m_obj;
lean_object* v_a_501_ = stack[3].m_obj;
lean_object* v_a_502_ = stack[4].m_obj;
lean_object* v_a_503_ = stack[5].m_obj;
lean_object* v_a_504_ = stack[6].m_obj;
lean_object* v_res_509_;
v_res_509_ = l_Lean_Meta_withNewEqs___redArg(v_targets_498_, v_targetsNew_499_, v_k_500_, v_a_501_, v_a_502_, v_a_503_, v_a_504_);
stack->m_obj
 = v_res_509_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewEqs___redArg___boxed(lean_object* v_targets_510_, lean_object* v_targetsNew_511_, lean_object* v_k_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v_a_517_){
_start:
{
lean_object* v_res_518_; 
v_res_518_ = l_Lean_Meta_withNewEqs___redArg(v_targets_510_, v_targetsNew_511_, v_k_512_, v_a_513_, v_a_514_, v_a_515_, v_a_516_);
lean_dec(v_a_516_);
lean_dec_ref(v_a_515_);
lean_dec(v_a_514_);
lean_dec_ref(v_a_513_);
return v_res_518_;
}
}
lean_object* l_Lean_Meta_withNewEqs(lean_object* v_00_u03b1_519_, lean_object* v_targets_520_, lean_object* v_targetsNew_521_, lean_object* v_k_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_, lean_object* v_a_526_){
_start:
{
lean_object* v___x_528_; 
v___x_528_ = l_Lean_Meta_withNewEqs___redArg(v_targets_520_, v_targetsNew_521_, v_k_522_, v_a_523_, v_a_524_, v_a_525_, v_a_526_);
return v___x_528_;
}
}
LEAN_EXPORT void l_Lean_Meta_withNewEqs_0interp(lean_interpreter_value* stack)
{
lean_object* v_targets_520_ = stack[1].m_obj;
lean_object* v_targetsNew_521_ = stack[2].m_obj;
lean_object* v_k_522_ = stack[3].m_obj;
lean_object* v_a_523_ = stack[4].m_obj;
lean_object* v_a_524_ = stack[5].m_obj;
lean_object* v_a_525_ = stack[6].m_obj;
lean_object* v_a_526_ = stack[7].m_obj;
lean_object* v_res_529_;
v_res_529_ = l_Lean_Meta_withNewEqs(lean_box(0), v_targets_520_, v_targetsNew_521_, v_k_522_, v_a_523_, v_a_524_, v_a_525_, v_a_526_);
stack->m_obj
 = v_res_529_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewEqs___boxed(lean_object* v_00_u03b1_530_, lean_object* v_targets_531_, lean_object* v_targetsNew_532_, lean_object* v_k_533_, lean_object* v_a_534_, lean_object* v_a_535_, lean_object* v_a_536_, lean_object* v_a_537_, lean_object* v_a_538_){
_start:
{
lean_object* v_res_539_; 
v_res_539_ = l_Lean_Meta_withNewEqs(v_00_u03b1_530_, v_targets_531_, v_targetsNew_532_, v_k_533_, v_a_534_, v_a_535_, v_a_536_, v_a_537_);
lean_dec(v_a_537_);
lean_dec_ref(v_a_536_);
lean_dec(v_a_535_);
lean_dec_ref(v_a_534_);
return v_res_539_;
}
}
lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_generalizeTargetsEq_spec__0___redArg___lam__0(lean_object* v_k_540_, lean_object* v_b_541_, lean_object* v_c_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_){
_start:
{
lean_object* v___x_548_; 
lean_inc(v___y_546_);
lean_inc_ref(v___y_545_);
lean_inc(v___y_544_);
lean_inc_ref(v___y_543_);
v___x_548_ = lean_apply_7(v_k_540_, v_b_541_, v_c_542_, v___y_543_, v___y_544_, v___y_545_, v___y_546_, lean_box(0));
return v___x_548_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_generalizeTargetsEq_spec__0___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_540_ = stack[0].m_obj;
lean_object* v_b_541_ = stack[1].m_obj;
lean_object* v_c_542_ = stack[2].m_obj;
lean_object* v___y_543_ = stack[3].m_obj;
lean_object* v___y_544_ = stack[4].m_obj;
lean_object* v___y_545_ = stack[5].m_obj;
lean_object* v___y_546_ = stack[6].m_obj;
lean_object* v_res_549_;
v_res_549_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_generalizeTargetsEq_spec__0___redArg___lam__0(v_k_540_, v_b_541_, v_c_542_, v___y_543_, v___y_544_, v___y_545_, v___y_546_);
stack->m_obj
 = v_res_549_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_generalizeTargetsEq_spec__0___redArg___lam__0___boxed(lean_object* v_k_550_, lean_object* v_b_551_, lean_object* v_c_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_){
_start:
{
lean_object* v_res_558_; 
v_res_558_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_generalizeTargetsEq_spec__0___redArg___lam__0(v_k_550_, v_b_551_, v_c_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_);
lean_dec(v___y_556_);
lean_dec_ref(v___y_555_);
lean_dec(v___y_554_);
lean_dec_ref(v___y_553_);
return v_res_558_;
}
}
lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_generalizeTargetsEq_spec__0___redArg(lean_object* v_type_559_, lean_object* v_k_560_, uint8_t v_cleanupAnnotations_561_, uint8_t v_whnfType_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_){
_start:
{
lean_object* v___f_568_; lean_object* v___x_569_; 
v___f_568_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_generalizeTargetsEq_spec__0___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_568_, 0, v_k_560_);
v___x_569_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_559_, v___f_568_, v_cleanupAnnotations_561_, v_whnfType_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_);
if (lean_obj_tag(v___x_569_) == 0)
{
lean_object* v_a_570_; lean_object* v___x_572_; uint8_t v_isShared_573_; uint8_t v_isSharedCheck_577_; 
v_a_570_ = lean_ctor_get(v___x_569_, 0);
v_isSharedCheck_577_ = !lean_is_exclusive(v___x_569_);
if (v_isSharedCheck_577_ == 0)
{
v___x_572_ = v___x_569_;
v_isShared_573_ = v_isSharedCheck_577_;
goto v_resetjp_571_;
}
else
{
lean_inc(v_a_570_);
lean_dec(v___x_569_);
v___x_572_ = lean_box(0);
v_isShared_573_ = v_isSharedCheck_577_;
goto v_resetjp_571_;
}
v_resetjp_571_:
{
lean_object* v___x_575_; 
if (v_isShared_573_ == 0)
{
v___x_575_ = v___x_572_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v_a_570_);
v___x_575_ = v_reuseFailAlloc_576_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
return v___x_575_;
}
}
}
else
{
lean_object* v_a_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_585_; 
v_a_578_ = lean_ctor_get(v___x_569_, 0);
v_isSharedCheck_585_ = !lean_is_exclusive(v___x_569_);
if (v_isSharedCheck_585_ == 0)
{
v___x_580_ = v___x_569_;
v_isShared_581_ = v_isSharedCheck_585_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_a_578_);
lean_dec(v___x_569_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_585_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
lean_object* v___x_583_; 
if (v_isShared_581_ == 0)
{
v___x_583_ = v___x_580_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v_a_578_);
v___x_583_ = v_reuseFailAlloc_584_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
return v___x_583_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_generalizeTargetsEq_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_559_ = stack[0].m_obj;
lean_object* v_k_560_ = stack[1].m_obj;
uint8_t v_cleanupAnnotations_561_ = stack[2].m_num;
uint8_t v_whnfType_562_ = stack[3].m_num;
lean_object* v___y_563_ = stack[4].m_obj;
lean_object* v___y_564_ = stack[5].m_obj;
lean_object* v___y_565_ = stack[6].m_obj;
lean_object* v___y_566_ = stack[7].m_obj;
lean_object* v_res_586_;
v_res_586_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_generalizeTargetsEq_spec__0___redArg(v_type_559_, v_k_560_, v_cleanupAnnotations_561_, v_whnfType_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_);
stack->m_obj
 = v_res_586_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_generalizeTargetsEq_spec__0___redArg___boxed(lean_object* v_type_587_, lean_object* v_k_588_, lean_object* v_cleanupAnnotations_589_, lean_object* v_whnfType_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_596_; uint8_t v_whnfType_boxed_597_; lean_object* v_res_598_; 
v_cleanupAnnotations_boxed_596_ = lean_unbox(v_cleanupAnnotations_589_);
v_whnfType_boxed_597_ = lean_unbox(v_whnfType_590_);
v_res_598_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_generalizeTargetsEq_spec__0___redArg(v_type_587_, v_k_588_, v_cleanupAnnotations_boxed_596_, v_whnfType_boxed_597_, v___y_591_, v___y_592_, v___y_593_, v___y_594_);
lean_dec(v___y_594_);
lean_dec_ref(v___y_593_);
lean_dec(v___y_592_);
lean_dec_ref(v___y_591_);
return v_res_598_;
}
}
lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_generalizeTargetsEq_spec__0(lean_object* v_00_u03b1_599_, lean_object* v_type_600_, lean_object* v_k_601_, uint8_t v_cleanupAnnotations_602_, uint8_t v_whnfType_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_){
_start:
{
lean_object* v___x_609_; 
v___x_609_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_generalizeTargetsEq_spec__0___redArg(v_type_600_, v_k_601_, v_cleanupAnnotations_602_, v_whnfType_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_);
return v___x_609_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_generalizeTargetsEq_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_600_ = stack[1].m_obj;
lean_object* v_k_601_ = stack[2].m_obj;
uint8_t v_cleanupAnnotations_602_ = stack[3].m_num;
uint8_t v_whnfType_603_ = stack[4].m_num;
lean_object* v___y_604_ = stack[5].m_obj;
lean_object* v___y_605_ = stack[6].m_obj;
lean_object* v___y_606_ = stack[7].m_obj;
lean_object* v___y_607_ = stack[8].m_obj;
lean_object* v_res_610_;
v_res_610_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_generalizeTargetsEq_spec__0(lean_box(0), v_type_600_, v_k_601_, v_cleanupAnnotations_602_, v_whnfType_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_);
stack->m_obj
 = v_res_610_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_generalizeTargetsEq_spec__0___boxed(lean_object* v_00_u03b1_611_, lean_object* v_type_612_, lean_object* v_k_613_, lean_object* v_cleanupAnnotations_614_, lean_object* v_whnfType_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_621_; uint8_t v_whnfType_boxed_622_; lean_object* v_res_623_; 
v_cleanupAnnotations_boxed_621_ = lean_unbox(v_cleanupAnnotations_614_);
v_whnfType_boxed_622_ = lean_unbox(v_whnfType_615_);
v_res_623_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_generalizeTargetsEq_spec__0(v_00_u03b1_611_, v_type_612_, v_k_613_, v_cleanupAnnotations_boxed_621_, v_whnfType_boxed_622_, v___y_616_, v___y_617_, v___y_618_, v___y_619_);
lean_dec(v___y_619_);
lean_dec_ref(v___y_618_);
lean_dec(v___y_617_);
lean_dec_ref(v___y_616_);
return v_res_623_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2___redArg(lean_object* v_mvarId_624_, lean_object* v_x_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_){
_start:
{
lean_object* v___x_631_; 
v___x_631_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_624_, v_x_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_);
if (lean_obj_tag(v___x_631_) == 0)
{
lean_object* v_a_632_; lean_object* v___x_634_; uint8_t v_isShared_635_; uint8_t v_isSharedCheck_639_; 
v_a_632_ = lean_ctor_get(v___x_631_, 0);
v_isSharedCheck_639_ = !lean_is_exclusive(v___x_631_);
if (v_isSharedCheck_639_ == 0)
{
v___x_634_ = v___x_631_;
v_isShared_635_ = v_isSharedCheck_639_;
goto v_resetjp_633_;
}
else
{
lean_inc(v_a_632_);
lean_dec(v___x_631_);
v___x_634_ = lean_box(0);
v_isShared_635_ = v_isSharedCheck_639_;
goto v_resetjp_633_;
}
v_resetjp_633_:
{
lean_object* v___x_637_; 
if (v_isShared_635_ == 0)
{
v___x_637_ = v___x_634_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v_a_632_);
v___x_637_ = v_reuseFailAlloc_638_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
return v___x_637_;
}
}
}
else
{
lean_object* v_a_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_647_; 
v_a_640_ = lean_ctor_get(v___x_631_, 0);
v_isSharedCheck_647_ = !lean_is_exclusive(v___x_631_);
if (v_isSharedCheck_647_ == 0)
{
v___x_642_ = v___x_631_;
v_isShared_643_ = v_isSharedCheck_647_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_a_640_);
lean_dec(v___x_631_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_647_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
lean_object* v___x_645_; 
if (v_isShared_643_ == 0)
{
v___x_645_ = v___x_642_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v_a_640_);
v___x_645_ = v_reuseFailAlloc_646_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
return v___x_645_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_624_ = stack[0].m_obj;
lean_object* v_x_625_ = stack[1].m_obj;
lean_object* v___y_626_ = stack[2].m_obj;
lean_object* v___y_627_ = stack[3].m_obj;
lean_object* v___y_628_ = stack[4].m_obj;
lean_object* v___y_629_ = stack[5].m_obj;
lean_object* v_res_648_;
v_res_648_ = l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2___redArg(v_mvarId_624_, v_x_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_);
stack->m_obj
 = v_res_648_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2___redArg___boxed(lean_object* v_mvarId_649_, lean_object* v_x_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_){
_start:
{
lean_object* v_res_656_; 
v_res_656_ = l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2___redArg(v_mvarId_649_, v_x_650_, v___y_651_, v___y_652_, v___y_653_, v___y_654_);
lean_dec(v___y_654_);
lean_dec_ref(v___y_653_);
lean_dec(v___y_652_);
lean_dec_ref(v___y_651_);
return v_res_656_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2(lean_object* v_00_u03b1_657_, lean_object* v_mvarId_658_, lean_object* v_x_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_){
_start:
{
lean_object* v___x_665_; 
v___x_665_ = l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2___redArg(v_mvarId_658_, v_x_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_);
return v___x_665_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_658_ = stack[1].m_obj;
lean_object* v_x_659_ = stack[2].m_obj;
lean_object* v___y_660_ = stack[3].m_obj;
lean_object* v___y_661_ = stack[4].m_obj;
lean_object* v___y_662_ = stack[5].m_obj;
lean_object* v___y_663_ = stack[6].m_obj;
lean_object* v_res_666_;
v_res_666_ = l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2(lean_box(0), v_mvarId_658_, v_x_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_);
stack->m_obj
 = v_res_666_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2___boxed(lean_object* v_00_u03b1_667_, lean_object* v_mvarId_668_, lean_object* v_x_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_){
_start:
{
lean_object* v_res_675_; 
v_res_675_ = l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2(v_00_u03b1_667_, v_mvarId_668_, v_x_669_, v___y_670_, v___y_671_, v___y_672_, v___y_673_);
lean_dec(v___y_673_);
lean_dec_ref(v___y_672_);
lean_dec(v___y_671_);
lean_dec_ref(v___y_670_);
return v_res_675_;
}
}
lean_object* l_Lean_Meta_generalizeTargetsEq___lam__0(lean_object* v_mvarId_676_, lean_object* v___x_677_, lean_object* v_eqs_678_, lean_object* v_eqRefls_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_){
_start:
{
lean_object* v___x_685_; 
v___x_685_ = l_Lean_MVarId_getType(v_mvarId_676_, v___y_680_, v___y_681_, v___y_682_, v___y_683_);
if (lean_obj_tag(v___x_685_) == 0)
{
lean_object* v_a_686_; uint8_t v___x_687_; uint8_t v___x_688_; uint8_t v___x_689_; lean_object* v___x_690_; 
v_a_686_ = lean_ctor_get(v___x_685_, 0);
lean_inc(v_a_686_);
lean_dec_ref_known(v___x_685_, 1);
v___x_687_ = 0;
v___x_688_ = 1;
v___x_689_ = 1;
v___x_690_ = l_Lean_Meta_mkForallFVars(v_eqs_678_, v_a_686_, v___x_687_, v___x_688_, v___x_688_, v___x_689_, v___y_680_, v___y_681_, v___y_682_, v___y_683_);
if (lean_obj_tag(v___x_690_) == 0)
{
lean_object* v_a_691_; lean_object* v___x_692_; 
v_a_691_ = lean_ctor_get(v___x_690_, 0);
lean_inc(v_a_691_);
lean_dec_ref_known(v___x_690_, 1);
v___x_692_ = l_Lean_Meta_mkForallFVars(v___x_677_, v_a_691_, v___x_687_, v___x_688_, v___x_688_, v___x_689_, v___y_680_, v___y_681_, v___y_682_, v___y_683_);
if (lean_obj_tag(v___x_692_) == 0)
{
lean_object* v_a_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_701_; 
v_a_693_ = lean_ctor_get(v___x_692_, 0);
v_isSharedCheck_701_ = !lean_is_exclusive(v___x_692_);
if (v_isSharedCheck_701_ == 0)
{
v___x_695_ = v___x_692_;
v_isShared_696_ = v_isSharedCheck_701_;
goto v_resetjp_694_;
}
else
{
lean_inc(v_a_693_);
lean_dec(v___x_692_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_701_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
lean_object* v___x_697_; lean_object* v___x_699_; 
v___x_697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_697_, 0, v_a_693_);
lean_ctor_set(v___x_697_, 1, v_eqRefls_679_);
if (v_isShared_696_ == 0)
{
lean_ctor_set(v___x_695_, 0, v___x_697_);
v___x_699_ = v___x_695_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v___x_697_);
v___x_699_ = v_reuseFailAlloc_700_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
return v___x_699_;
}
}
}
else
{
lean_object* v_a_702_; lean_object* v___x_704_; uint8_t v_isShared_705_; uint8_t v_isSharedCheck_709_; 
lean_dec_ref(v_eqRefls_679_);
v_a_702_ = lean_ctor_get(v___x_692_, 0);
v_isSharedCheck_709_ = !lean_is_exclusive(v___x_692_);
if (v_isSharedCheck_709_ == 0)
{
v___x_704_ = v___x_692_;
v_isShared_705_ = v_isSharedCheck_709_;
goto v_resetjp_703_;
}
else
{
lean_inc(v_a_702_);
lean_dec(v___x_692_);
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
else
{
lean_object* v_a_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_717_; 
lean_dec_ref(v_eqRefls_679_);
v_a_710_ = lean_ctor_get(v___x_690_, 0);
v_isSharedCheck_717_ = !lean_is_exclusive(v___x_690_);
if (v_isSharedCheck_717_ == 0)
{
v___x_712_ = v___x_690_;
v_isShared_713_ = v_isSharedCheck_717_;
goto v_resetjp_711_;
}
else
{
lean_inc(v_a_710_);
lean_dec(v___x_690_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_717_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
lean_object* v___x_715_; 
if (v_isShared_713_ == 0)
{
v___x_715_ = v___x_712_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v_a_710_);
v___x_715_ = v_reuseFailAlloc_716_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
return v___x_715_;
}
}
}
}
else
{
lean_object* v_a_718_; lean_object* v___x_720_; uint8_t v_isShared_721_; uint8_t v_isSharedCheck_725_; 
lean_dec_ref(v_eqRefls_679_);
v_a_718_ = lean_ctor_get(v___x_685_, 0);
v_isSharedCheck_725_ = !lean_is_exclusive(v___x_685_);
if (v_isSharedCheck_725_ == 0)
{
v___x_720_ = v___x_685_;
v_isShared_721_ = v_isSharedCheck_725_;
goto v_resetjp_719_;
}
else
{
lean_inc(v_a_718_);
lean_dec(v___x_685_);
v___x_720_ = lean_box(0);
v_isShared_721_ = v_isSharedCheck_725_;
goto v_resetjp_719_;
}
v_resetjp_719_:
{
lean_object* v___x_723_; 
if (v_isShared_721_ == 0)
{
v___x_723_ = v___x_720_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v_a_718_);
v___x_723_ = v_reuseFailAlloc_724_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
return v___x_723_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_generalizeTargetsEq___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_676_ = stack[0].m_obj;
lean_object* v___x_677_ = stack[1].m_obj;
lean_object* v_eqs_678_ = stack[2].m_obj;
lean_object* v_eqRefls_679_ = stack[3].m_obj;
lean_object* v___y_680_ = stack[4].m_obj;
lean_object* v___y_681_ = stack[5].m_obj;
lean_object* v___y_682_ = stack[6].m_obj;
lean_object* v___y_683_ = stack[7].m_obj;
lean_object* v_res_726_;
v_res_726_ = l_Lean_Meta_generalizeTargetsEq___lam__0(v_mvarId_676_, v___x_677_, v_eqs_678_, v_eqRefls_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_);
stack->m_obj
 = v_res_726_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeTargetsEq___lam__0___boxed(lean_object* v_mvarId_727_, lean_object* v___x_728_, lean_object* v_eqs_729_, lean_object* v_eqRefls_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_){
_start:
{
lean_object* v_res_736_; 
v_res_736_ = l_Lean_Meta_generalizeTargetsEq___lam__0(v_mvarId_727_, v___x_728_, v_eqs_729_, v_eqRefls_730_, v___y_731_, v___y_732_, v___y_733_, v___y_734_);
lean_dec(v___y_734_);
lean_dec_ref(v___y_733_);
lean_dec(v___y_732_);
lean_dec_ref(v___y_731_);
lean_dec_ref(v_eqs_729_);
lean_dec_ref(v___x_728_);
return v_res_736_;
}
}
static lean_object* _init_l_Lean_Meta_generalizeTargetsEq___lam__1___closed__1(void){
_start:
{
lean_object* v___x_738_; lean_object* v___x_739_; 
v___x_738_ = ((lean_object*)(l_Lean_Meta_generalizeTargetsEq___lam__1___closed__0));
v___x_739_ = l_Lean_stringToMessageData(v___x_738_);
return v___x_739_;
}
}
static lean_object* _init_l_Lean_Meta_generalizeTargetsEq___lam__1___closed__3(void){
_start:
{
lean_object* v___x_741_; lean_object* v___x_742_; 
v___x_741_ = ((lean_object*)(l_Lean_Meta_generalizeTargetsEq___lam__1___closed__2));
v___x_742_ = l_Lean_stringToMessageData(v___x_741_);
return v___x_742_;
}
}
lean_object* l_Lean_Meta_generalizeTargetsEq___lam__1(lean_object* v_targets_743_, lean_object* v_mvarId_744_, lean_object* v_targetsNew_745_, lean_object* v_x_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_){
_start:
{
lean_object* v___x_759_; lean_object* v___x_760_; uint8_t v___x_761_; 
v___x_759_ = lean_array_get_size(v_targets_743_);
v___x_760_ = lean_array_get_size(v_targetsNew_745_);
v___x_761_ = lean_nat_dec_le(v___x_759_, v___x_760_);
if (v___x_761_ == 0)
{
lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v_a_774_; lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_781_; 
lean_dec_ref(v_targetsNew_745_);
lean_dec(v_mvarId_744_);
lean_dec_ref(v_targets_743_);
v___x_762_ = lean_obj_once(&l_Lean_Meta_generalizeTargetsEq___lam__1___closed__1, &l_Lean_Meta_generalizeTargetsEq___lam__1___closed__1_once, _init_l_Lean_Meta_generalizeTargetsEq___lam__1___closed__1);
v___x_763_ = l_Nat_reprFast(v___x_759_);
v___x_764_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_764_, 0, v___x_763_);
v___x_765_ = l_Lean_MessageData_ofFormat(v___x_764_);
v___x_766_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_766_, 0, v___x_762_);
lean_ctor_set(v___x_766_, 1, v___x_765_);
v___x_767_ = lean_obj_once(&l_Lean_Meta_generalizeTargetsEq___lam__1___closed__3, &l_Lean_Meta_generalizeTargetsEq___lam__1___closed__3_once, _init_l_Lean_Meta_generalizeTargetsEq___lam__1___closed__3);
v___x_768_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_768_, 0, v___x_766_);
lean_ctor_set(v___x_768_, 1, v___x_767_);
v___x_769_ = l_Nat_reprFast(v___x_760_);
v___x_770_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_770_, 0, v___x_769_);
v___x_771_ = l_Lean_MessageData_ofFormat(v___x_770_);
v___x_772_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_772_, 0, v___x_768_);
lean_ctor_set(v___x_772_, 1, v___x_771_);
v___x_773_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected_spec__0___redArg(v___x_772_, v___y_747_, v___y_748_, v___y_749_, v___y_750_);
v_a_774_ = lean_ctor_get(v___x_773_, 0);
v_isSharedCheck_781_ = !lean_is_exclusive(v___x_773_);
if (v_isSharedCheck_781_ == 0)
{
v___x_776_ = v___x_773_;
v_isShared_777_ = v_isSharedCheck_781_;
goto v_resetjp_775_;
}
else
{
lean_inc(v_a_774_);
lean_dec(v___x_773_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_781_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
lean_object* v___x_779_; 
if (v_isShared_777_ == 0)
{
v___x_779_ = v___x_776_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v_a_774_);
v___x_779_ = v_reuseFailAlloc_780_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
return v___x_779_;
}
}
}
else
{
goto v___jp_752_;
}
v___jp_752_:
{
lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___f_757_; lean_object* v___x_758_; 
v___x_753_ = lean_array_get_size(v_targets_743_);
v___x_754_ = lean_unsigned_to_nat(0u);
v___x_755_ = l_Array_toSubarray___redArg(v_targetsNew_745_, v___x_754_, v___x_753_);
v___x_756_ = l_Subarray_copy___redArg(v___x_755_);
lean_inc_ref(v___x_756_);
v___f_757_ = lean_alloc_closure((void*)(l_Lean_Meta_generalizeTargetsEq___lam__0___boxed), 9, 2);
lean_closure_set(v___f_757_, 0, v_mvarId_744_);
lean_closure_set(v___f_757_, 1, v___x_756_);
v___x_758_ = l_Lean_Meta_withNewEqs___redArg(v_targets_743_, v___x_756_, v___f_757_, v___y_747_, v___y_748_, v___y_749_, v___y_750_);
return v___x_758_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_generalizeTargetsEq___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_targets_743_ = stack[0].m_obj;
lean_object* v_mvarId_744_ = stack[1].m_obj;
lean_object* v_targetsNew_745_ = stack[2].m_obj;
lean_object* v_x_746_ = stack[3].m_obj;
lean_object* v___y_747_ = stack[4].m_obj;
lean_object* v___y_748_ = stack[5].m_obj;
lean_object* v___y_749_ = stack[6].m_obj;
lean_object* v___y_750_ = stack[7].m_obj;
lean_object* v_res_782_;
v_res_782_ = l_Lean_Meta_generalizeTargetsEq___lam__1(v_targets_743_, v_mvarId_744_, v_targetsNew_745_, v_x_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_);
stack->m_obj
 = v_res_782_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeTargetsEq___lam__1___boxed(lean_object* v_targets_783_, lean_object* v_mvarId_784_, lean_object* v_targetsNew_785_, lean_object* v_x_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_){
_start:
{
lean_object* v_res_792_; 
v_res_792_ = l_Lean_Meta_generalizeTargetsEq___lam__1(v_targets_783_, v_mvarId_784_, v_targetsNew_785_, v_x_786_, v___y_787_, v___y_788_, v___y_789_, v___y_790_);
lean_dec(v___y_790_);
lean_dec_ref(v___y_789_);
lean_dec(v___y_788_);
lean_dec_ref(v___y_787_);
lean_dec_ref(v_x_786_);
return v_res_792_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__4_spec__5___redArg(lean_object* v_x_793_, lean_object* v_x_794_, lean_object* v_x_795_, lean_object* v_x_796_){
_start:
{
lean_object* v_ks_797_; lean_object* v_vs_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_822_; 
v_ks_797_ = lean_ctor_get(v_x_793_, 0);
v_vs_798_ = lean_ctor_get(v_x_793_, 1);
v_isSharedCheck_822_ = !lean_is_exclusive(v_x_793_);
if (v_isSharedCheck_822_ == 0)
{
v___x_800_ = v_x_793_;
v_isShared_801_ = v_isSharedCheck_822_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_vs_798_);
lean_inc(v_ks_797_);
lean_dec(v_x_793_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_822_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
lean_object* v___x_802_; uint8_t v___x_803_; 
v___x_802_ = lean_array_get_size(v_ks_797_);
v___x_803_ = lean_nat_dec_lt(v_x_794_, v___x_802_);
if (v___x_803_ == 0)
{
lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_807_; 
lean_dec(v_x_794_);
v___x_804_ = lean_array_push(v_ks_797_, v_x_795_);
v___x_805_ = lean_array_push(v_vs_798_, v_x_796_);
if (v_isShared_801_ == 0)
{
lean_ctor_set(v___x_800_, 1, v___x_805_);
lean_ctor_set(v___x_800_, 0, v___x_804_);
v___x_807_ = v___x_800_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v___x_804_);
lean_ctor_set(v_reuseFailAlloc_808_, 1, v___x_805_);
v___x_807_ = v_reuseFailAlloc_808_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
return v___x_807_;
}
}
else
{
lean_object* v_k_x27_809_; uint8_t v___x_810_; 
v_k_x27_809_ = lean_array_fget_borrowed(v_ks_797_, v_x_794_);
v___x_810_ = l_Lean_instBEqMVarId_beq(v_x_795_, v_k_x27_809_);
if (v___x_810_ == 0)
{
lean_object* v___x_812_; 
if (v_isShared_801_ == 0)
{
v___x_812_ = v___x_800_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v_ks_797_);
lean_ctor_set(v_reuseFailAlloc_816_, 1, v_vs_798_);
v___x_812_ = v_reuseFailAlloc_816_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
lean_object* v___x_813_; lean_object* v___x_814_; 
v___x_813_ = lean_unsigned_to_nat(1u);
v___x_814_ = lean_nat_add(v_x_794_, v___x_813_);
lean_dec(v_x_794_);
v_x_793_ = v___x_812_;
v_x_794_ = v___x_814_;
goto _start;
}
}
else
{
lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_820_; 
v___x_817_ = lean_array_fset(v_ks_797_, v_x_794_, v_x_795_);
v___x_818_ = lean_array_fset(v_vs_798_, v_x_794_, v_x_796_);
lean_dec(v_x_794_);
if (v_isShared_801_ == 0)
{
lean_ctor_set(v___x_800_, 1, v___x_818_);
lean_ctor_set(v___x_800_, 0, v___x_817_);
v___x_820_ = v___x_800_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v___x_817_);
lean_ctor_set(v_reuseFailAlloc_821_, 1, v___x_818_);
v___x_820_ = v_reuseFailAlloc_821_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
return v___x_820_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__4___redArg(lean_object* v_n_823_, lean_object* v_k_824_, lean_object* v_v_825_){
_start:
{
lean_object* v___x_826_; lean_object* v___x_827_; 
v___x_826_ = lean_unsigned_to_nat(0u);
v___x_827_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__4_spec__5___redArg(v_n_823_, v___x_826_, v_k_824_, v_v_825_);
return v___x_827_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_828_; 
v___x_828_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_828_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg(lean_object* v_x_829_, size_t v_x_830_, size_t v_x_831_, lean_object* v_x_832_, lean_object* v_x_833_){
_start:
{
if (lean_obj_tag(v_x_829_) == 0)
{
lean_object* v_es_834_; size_t v___x_835_; size_t v___x_836_; lean_object* v_j_837_; lean_object* v___x_838_; uint8_t v___x_839_; 
v_es_834_ = lean_ctor_get(v_x_829_, 0);
v___x_835_ = ((size_t)31ULL);
v___x_836_ = lean_usize_land(v_x_830_, v___x_835_);
v_j_837_ = lean_usize_to_nat(v___x_836_);
v___x_838_ = lean_array_get_size(v_es_834_);
v___x_839_ = lean_nat_dec_lt(v_j_837_, v___x_838_);
if (v___x_839_ == 0)
{
lean_dec(v_j_837_);
lean_dec(v_x_833_);
lean_dec(v_x_832_);
return v_x_829_;
}
else
{
lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_878_; 
lean_inc_ref(v_es_834_);
v_isSharedCheck_878_ = !lean_is_exclusive(v_x_829_);
if (v_isSharedCheck_878_ == 0)
{
lean_object* v_unused_879_; 
v_unused_879_ = lean_ctor_get(v_x_829_, 0);
lean_dec(v_unused_879_);
v___x_841_ = v_x_829_;
v_isShared_842_ = v_isSharedCheck_878_;
goto v_resetjp_840_;
}
else
{
lean_dec(v_x_829_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_878_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
lean_object* v_v_843_; lean_object* v___x_844_; lean_object* v_xs_x27_845_; lean_object* v___y_847_; 
v_v_843_ = lean_array_fget(v_es_834_, v_j_837_);
v___x_844_ = lean_box(0);
v_xs_x27_845_ = lean_array_fset(v_es_834_, v_j_837_, v___x_844_);
switch(lean_obj_tag(v_v_843_))
{
case 0:
{
lean_object* v_key_852_; lean_object* v_val_853_; lean_object* v___x_855_; uint8_t v_isShared_856_; uint8_t v_isSharedCheck_863_; 
v_key_852_ = lean_ctor_get(v_v_843_, 0);
v_val_853_ = lean_ctor_get(v_v_843_, 1);
v_isSharedCheck_863_ = !lean_is_exclusive(v_v_843_);
if (v_isSharedCheck_863_ == 0)
{
v___x_855_ = v_v_843_;
v_isShared_856_ = v_isSharedCheck_863_;
goto v_resetjp_854_;
}
else
{
lean_inc(v_val_853_);
lean_inc(v_key_852_);
lean_dec(v_v_843_);
v___x_855_ = lean_box(0);
v_isShared_856_ = v_isSharedCheck_863_;
goto v_resetjp_854_;
}
v_resetjp_854_:
{
uint8_t v___x_857_; 
v___x_857_ = l_Lean_instBEqMVarId_beq(v_x_832_, v_key_852_);
if (v___x_857_ == 0)
{
lean_object* v___x_858_; lean_object* v___x_859_; 
lean_del_object(v___x_855_);
v___x_858_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_852_, v_val_853_, v_x_832_, v_x_833_);
v___x_859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_859_, 0, v___x_858_);
v___y_847_ = v___x_859_;
goto v___jp_846_;
}
else
{
lean_object* v___x_861_; 
lean_dec(v_val_853_);
lean_dec(v_key_852_);
if (v_isShared_856_ == 0)
{
lean_ctor_set(v___x_855_, 1, v_x_833_);
lean_ctor_set(v___x_855_, 0, v_x_832_);
v___x_861_ = v___x_855_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v_x_832_);
lean_ctor_set(v_reuseFailAlloc_862_, 1, v_x_833_);
v___x_861_ = v_reuseFailAlloc_862_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
v___y_847_ = v___x_861_;
goto v___jp_846_;
}
}
}
}
case 1:
{
lean_object* v_node_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_876_; 
v_node_864_ = lean_ctor_get(v_v_843_, 0);
v_isSharedCheck_876_ = !lean_is_exclusive(v_v_843_);
if (v_isSharedCheck_876_ == 0)
{
v___x_866_ = v_v_843_;
v_isShared_867_ = v_isSharedCheck_876_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_node_864_);
lean_dec(v_v_843_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_876_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
size_t v___x_868_; size_t v___x_869_; size_t v___x_870_; size_t v___x_871_; lean_object* v___x_872_; lean_object* v___x_874_; 
v___x_868_ = ((size_t)5ULL);
v___x_869_ = lean_usize_shift_right(v_x_830_, v___x_868_);
v___x_870_ = ((size_t)1ULL);
v___x_871_ = lean_usize_add(v_x_831_, v___x_870_);
v___x_872_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg(v_node_864_, v___x_869_, v___x_871_, v_x_832_, v_x_833_);
if (v_isShared_867_ == 0)
{
lean_ctor_set(v___x_866_, 0, v___x_872_);
v___x_874_ = v___x_866_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v___x_872_);
v___x_874_ = v_reuseFailAlloc_875_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
v___y_847_ = v___x_874_;
goto v___jp_846_;
}
}
}
default: 
{
lean_object* v___x_877_; 
v___x_877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_877_, 0, v_x_832_);
lean_ctor_set(v___x_877_, 1, v_x_833_);
v___y_847_ = v___x_877_;
goto v___jp_846_;
}
}
v___jp_846_:
{
lean_object* v___x_848_; lean_object* v___x_850_; 
v___x_848_ = lean_array_fset(v_xs_x27_845_, v_j_837_, v___y_847_);
lean_dec(v_j_837_);
if (v_isShared_842_ == 0)
{
lean_ctor_set(v___x_841_, 0, v___x_848_);
v___x_850_ = v___x_841_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v___x_848_);
v___x_850_ = v_reuseFailAlloc_851_;
goto v_reusejp_849_;
}
v_reusejp_849_:
{
return v___x_850_;
}
}
}
}
}
else
{
lean_object* v_ks_880_; lean_object* v_vs_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_899_; 
v_ks_880_ = lean_ctor_get(v_x_829_, 0);
v_vs_881_ = lean_ctor_get(v_x_829_, 1);
v_isSharedCheck_899_ = !lean_is_exclusive(v_x_829_);
if (v_isSharedCheck_899_ == 0)
{
v___x_883_ = v_x_829_;
v_isShared_884_ = v_isSharedCheck_899_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_vs_881_);
lean_inc(v_ks_880_);
lean_dec(v_x_829_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_899_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
lean_object* v___x_886_; 
if (v_isShared_884_ == 0)
{
v___x_886_ = v___x_883_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v_ks_880_);
lean_ctor_set(v_reuseFailAlloc_898_, 1, v_vs_881_);
v___x_886_ = v_reuseFailAlloc_898_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
lean_object* v_newNode_887_; size_t v___x_888_; uint8_t v___x_889_; 
v_newNode_887_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__4___redArg(v___x_886_, v_x_832_, v_x_833_);
v___x_888_ = ((size_t)7ULL);
v___x_889_ = lean_usize_dec_le(v___x_888_, v_x_831_);
if (v___x_889_ == 0)
{
lean_object* v___x_890_; lean_object* v___x_891_; uint8_t v___x_892_; 
v___x_890_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_887_);
v___x_891_ = lean_unsigned_to_nat(4u);
v___x_892_ = lean_nat_dec_lt(v___x_890_, v___x_891_);
lean_dec(v___x_890_);
if (v___x_892_ == 0)
{
lean_object* v_ks_893_; lean_object* v_vs_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; 
v_ks_893_ = lean_ctor_get(v_newNode_887_, 0);
lean_inc_ref(v_ks_893_);
v_vs_894_ = lean_ctor_get(v_newNode_887_, 1);
lean_inc_ref(v_vs_894_);
lean_dec_ref(v_newNode_887_);
v___x_895_ = lean_unsigned_to_nat(0u);
v___x_896_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg___closed__0);
v___x_897_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__5___redArg(v_x_831_, v_ks_893_, v_vs_894_, v___x_895_, v___x_896_);
lean_dec_ref(v_vs_894_);
lean_dec_ref(v_ks_893_);
return v___x_897_;
}
else
{
return v_newNode_887_;
}
}
else
{
return v_newNode_887_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_829_ = stack[0].m_obj;
size_t v_x_830_ = stack[1].m_num;
size_t v_x_831_ = stack[2].m_num;
lean_object* v_x_832_ = stack[3].m_obj;
lean_object* v_x_833_ = stack[4].m_obj;
lean_object* v_res_900_;
v_res_900_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg(v_x_829_, v_x_830_, v_x_831_, v_x_832_, v_x_833_);
stack->m_obj
 = v_res_900_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__5___redArg(size_t v_depth_901_, lean_object* v_keys_902_, lean_object* v_vals_903_, lean_object* v_i_904_, lean_object* v_entries_905_){
_start:
{
lean_object* v___x_906_; uint8_t v___x_907_; 
v___x_906_ = lean_array_get_size(v_keys_902_);
v___x_907_ = lean_nat_dec_lt(v_i_904_, v___x_906_);
if (v___x_907_ == 0)
{
lean_dec(v_i_904_);
return v_entries_905_;
}
else
{
lean_object* v_k_908_; lean_object* v_v_909_; uint64_t v___x_910_; size_t v_h_911_; size_t v___x_912_; lean_object* v___x_913_; size_t v___x_914_; size_t v___x_915_; size_t v___x_916_; size_t v_h_917_; lean_object* v___x_918_; lean_object* v___x_919_; 
v_k_908_ = lean_array_fget_borrowed(v_keys_902_, v_i_904_);
v_v_909_ = lean_array_fget_borrowed(v_vals_903_, v_i_904_);
v___x_910_ = l_Lean_instHashableMVarId_hash(v_k_908_);
v_h_911_ = lean_uint64_to_usize(v___x_910_);
v___x_912_ = ((size_t)5ULL);
v___x_913_ = lean_unsigned_to_nat(1u);
v___x_914_ = ((size_t)1ULL);
v___x_915_ = lean_usize_sub(v_depth_901_, v___x_914_);
v___x_916_ = lean_usize_mul(v___x_912_, v___x_915_);
v_h_917_ = lean_usize_shift_right(v_h_911_, v___x_916_);
v___x_918_ = lean_nat_add(v_i_904_, v___x_913_);
lean_dec(v_i_904_);
lean_inc(v_v_909_);
lean_inc(v_k_908_);
v___x_919_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg(v_entries_905_, v_h_917_, v_depth_901_, v_k_908_, v_v_909_);
v_i_904_ = v___x_918_;
v_entries_905_ = v___x_919_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_901_ = stack[0].m_num;
lean_object* v_keys_902_ = stack[1].m_obj;
lean_object* v_vals_903_ = stack[2].m_obj;
lean_object* v_i_904_ = stack[3].m_obj;
lean_object* v_entries_905_ = stack[4].m_obj;
lean_object* v_res_921_;
v_res_921_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__5___redArg(v_depth_901_, v_keys_902_, v_vals_903_, v_i_904_, v_entries_905_);
stack->m_obj
 = v_res_921_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__5___redArg___boxed(lean_object* v_depth_922_, lean_object* v_keys_923_, lean_object* v_vals_924_, lean_object* v_i_925_, lean_object* v_entries_926_){
_start:
{
size_t v_depth_boxed_927_; lean_object* v_res_928_; 
v_depth_boxed_927_ = lean_unbox_usize(v_depth_922_);
lean_dec(v_depth_922_);
v_res_928_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__5___redArg(v_depth_boxed_927_, v_keys_923_, v_vals_924_, v_i_925_, v_entries_926_);
lean_dec_ref(v_vals_924_);
lean_dec_ref(v_keys_923_);
return v_res_928_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_x_929_, lean_object* v_x_930_, lean_object* v_x_931_, lean_object* v_x_932_, lean_object* v_x_933_){
_start:
{
size_t v_x_2778__boxed_934_; size_t v_x_2779__boxed_935_; lean_object* v_res_936_; 
v_x_2778__boxed_934_ = lean_unbox_usize(v_x_930_);
lean_dec(v_x_930_);
v_x_2779__boxed_935_ = lean_unbox_usize(v_x_931_);
lean_dec(v_x_931_);
v_res_936_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg(v_x_929_, v_x_2778__boxed_934_, v_x_2779__boxed_935_, v_x_932_, v_x_933_);
return v_res_936_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1___redArg(lean_object* v_x_937_, lean_object* v_x_938_, lean_object* v_x_939_){
_start:
{
uint64_t v___x_940_; size_t v___x_941_; size_t v___x_942_; lean_object* v___x_943_; 
v___x_940_ = l_Lean_instHashableMVarId_hash(v_x_938_);
v___x_941_ = lean_uint64_to_usize(v___x_940_);
v___x_942_ = ((size_t)1ULL);
v___x_943_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg(v_x_937_, v___x_941_, v___x_942_, v_x_938_, v_x_939_);
return v___x_943_;
}
}
lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1___redArg(lean_object* v_mvarId_944_, lean_object* v_val_945_, lean_object* v___y_946_){
_start:
{
lean_object* v___x_948_; lean_object* v_mctx_949_; lean_object* v_cache_950_; lean_object* v_zetaDeltaFVarIds_951_; lean_object* v_postponed_952_; lean_object* v_diag_953_; lean_object* v___x_955_; uint8_t v_isShared_956_; uint8_t v_isSharedCheck_983_; 
v___x_948_ = lean_st_ref_take(v___y_946_);
v_mctx_949_ = lean_ctor_get(v___x_948_, 0);
v_cache_950_ = lean_ctor_get(v___x_948_, 1);
v_zetaDeltaFVarIds_951_ = lean_ctor_get(v___x_948_, 2);
v_postponed_952_ = lean_ctor_get(v___x_948_, 3);
v_diag_953_ = lean_ctor_get(v___x_948_, 4);
v_isSharedCheck_983_ = !lean_is_exclusive(v___x_948_);
if (v_isSharedCheck_983_ == 0)
{
v___x_955_ = v___x_948_;
v_isShared_956_ = v_isSharedCheck_983_;
goto v_resetjp_954_;
}
else
{
lean_inc(v_diag_953_);
lean_inc(v_postponed_952_);
lean_inc(v_zetaDeltaFVarIds_951_);
lean_inc(v_cache_950_);
lean_inc(v_mctx_949_);
lean_dec(v___x_948_);
v___x_955_ = lean_box(0);
v_isShared_956_ = v_isSharedCheck_983_;
goto v_resetjp_954_;
}
v_resetjp_954_:
{
lean_object* v_depth_957_; lean_object* v_levelAssignDepth_958_; lean_object* v_lmvarCounter_959_; lean_object* v_mvarCounter_960_; lean_object* v_lDecls_961_; lean_object* v_decls_962_; lean_object* v_userNames_963_; lean_object* v_lAssignment_964_; lean_object* v_eAssignment_965_; lean_object* v_dAssignment_966_; lean_object* v_instanceTypedMVars_967_; lean_object* v_synthNormMemo_968_; lean_object* v___x_970_; uint8_t v_isShared_971_; uint8_t v_isSharedCheck_982_; 
v_depth_957_ = lean_ctor_get(v_mctx_949_, 0);
v_levelAssignDepth_958_ = lean_ctor_get(v_mctx_949_, 1);
v_lmvarCounter_959_ = lean_ctor_get(v_mctx_949_, 2);
v_mvarCounter_960_ = lean_ctor_get(v_mctx_949_, 3);
v_lDecls_961_ = lean_ctor_get(v_mctx_949_, 4);
v_decls_962_ = lean_ctor_get(v_mctx_949_, 5);
v_userNames_963_ = lean_ctor_get(v_mctx_949_, 6);
v_lAssignment_964_ = lean_ctor_get(v_mctx_949_, 7);
v_eAssignment_965_ = lean_ctor_get(v_mctx_949_, 8);
v_dAssignment_966_ = lean_ctor_get(v_mctx_949_, 9);
v_instanceTypedMVars_967_ = lean_ctor_get(v_mctx_949_, 10);
v_synthNormMemo_968_ = lean_ctor_get(v_mctx_949_, 11);
v_isSharedCheck_982_ = !lean_is_exclusive(v_mctx_949_);
if (v_isSharedCheck_982_ == 0)
{
v___x_970_ = v_mctx_949_;
v_isShared_971_ = v_isSharedCheck_982_;
goto v_resetjp_969_;
}
else
{
lean_inc(v_synthNormMemo_968_);
lean_inc(v_instanceTypedMVars_967_);
lean_inc(v_dAssignment_966_);
lean_inc(v_eAssignment_965_);
lean_inc(v_lAssignment_964_);
lean_inc(v_userNames_963_);
lean_inc(v_decls_962_);
lean_inc(v_lDecls_961_);
lean_inc(v_mvarCounter_960_);
lean_inc(v_lmvarCounter_959_);
lean_inc(v_levelAssignDepth_958_);
lean_inc(v_depth_957_);
lean_dec(v_mctx_949_);
v___x_970_ = lean_box(0);
v_isShared_971_ = v_isSharedCheck_982_;
goto v_resetjp_969_;
}
v_resetjp_969_:
{
lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_975_; 
v___x_972_ = lean_box(0);
v___x_973_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1___redArg(v_eAssignment_965_, v_mvarId_944_, v_val_945_);
if (v_isShared_971_ == 0)
{
lean_ctor_set(v___x_970_, 8, v___x_973_);
v___x_975_ = v___x_970_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v_depth_957_);
lean_ctor_set(v_reuseFailAlloc_981_, 1, v_levelAssignDepth_958_);
lean_ctor_set(v_reuseFailAlloc_981_, 2, v_lmvarCounter_959_);
lean_ctor_set(v_reuseFailAlloc_981_, 3, v_mvarCounter_960_);
lean_ctor_set(v_reuseFailAlloc_981_, 4, v_lDecls_961_);
lean_ctor_set(v_reuseFailAlloc_981_, 5, v_decls_962_);
lean_ctor_set(v_reuseFailAlloc_981_, 6, v_userNames_963_);
lean_ctor_set(v_reuseFailAlloc_981_, 7, v_lAssignment_964_);
lean_ctor_set(v_reuseFailAlloc_981_, 8, v___x_973_);
lean_ctor_set(v_reuseFailAlloc_981_, 9, v_dAssignment_966_);
lean_ctor_set(v_reuseFailAlloc_981_, 10, v_instanceTypedMVars_967_);
lean_ctor_set(v_reuseFailAlloc_981_, 11, v_synthNormMemo_968_);
v___x_975_ = v_reuseFailAlloc_981_;
goto v_reusejp_974_;
}
v_reusejp_974_:
{
lean_object* v___x_977_; 
if (v_isShared_956_ == 0)
{
lean_ctor_set(v___x_955_, 0, v___x_975_);
v___x_977_ = v___x_955_;
goto v_reusejp_976_;
}
else
{
lean_object* v_reuseFailAlloc_980_; 
v_reuseFailAlloc_980_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_980_, 0, v___x_975_);
lean_ctor_set(v_reuseFailAlloc_980_, 1, v_cache_950_);
lean_ctor_set(v_reuseFailAlloc_980_, 2, v_zetaDeltaFVarIds_951_);
lean_ctor_set(v_reuseFailAlloc_980_, 3, v_postponed_952_);
lean_ctor_set(v_reuseFailAlloc_980_, 4, v_diag_953_);
v___x_977_ = v_reuseFailAlloc_980_;
goto v_reusejp_976_;
}
v_reusejp_976_:
{
lean_object* v___x_978_; lean_object* v___x_979_; 
v___x_978_ = lean_st_ref_put(v___y_946_, v___x_977_);
v___x_979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_979_, 0, v___x_972_);
return v___x_979_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_944_ = stack[0].m_obj;
lean_object* v_val_945_ = stack[1].m_obj;
lean_object* v___y_946_ = stack[2].m_obj;
lean_object* v_res_984_;
v_res_984_ = l_Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1___redArg(v_mvarId_944_, v_val_945_, v___y_946_);
stack->m_obj
 = v_res_984_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1___redArg___boxed(lean_object* v_mvarId_985_, lean_object* v_val_986_, lean_object* v___y_987_, lean_object* v___y_988_){
_start:
{
lean_object* v_res_989_; 
v_res_989_ = l_Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1___redArg(v_mvarId_985_, v_val_986_, v___y_987_);
lean_dec(v___y_987_);
return v_res_989_;
}
}
lean_object* l_Lean_Meta_generalizeTargetsEq___lam__2(lean_object* v_mvarId_990_, lean_object* v___x_991_, lean_object* v_motiveType_992_, lean_object* v___f_993_, lean_object* v_targets_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_){
_start:
{
lean_object* v___x_1000_; 
lean_inc(v_mvarId_990_);
v___x_1000_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_990_, v___x_991_, v___y_995_, v___y_996_, v___y_997_, v___y_998_);
if (lean_obj_tag(v___x_1000_) == 0)
{
uint8_t v___x_1001_; lean_object* v___x_1002_; 
lean_dec_ref_known(v___x_1000_, 1);
v___x_1001_ = 0;
v___x_1002_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_generalizeTargetsEq_spec__0___redArg(v_motiveType_992_, v___f_993_, v___x_1001_, v___x_1001_, v___y_995_, v___y_996_, v___y_997_, v___y_998_);
if (lean_obj_tag(v___x_1002_) == 0)
{
lean_object* v_a_1003_; lean_object* v_fst_1004_; lean_object* v_snd_1005_; lean_object* v___x_1006_; 
v_a_1003_ = lean_ctor_get(v___x_1002_, 0);
lean_inc(v_a_1003_);
lean_dec_ref_known(v___x_1002_, 1);
v_fst_1004_ = lean_ctor_get(v_a_1003_, 0);
lean_inc(v_fst_1004_);
v_snd_1005_ = lean_ctor_get(v_a_1003_, 1);
lean_inc(v_snd_1005_);
lean_dec(v_a_1003_);
lean_inc(v_mvarId_990_);
v___x_1006_ = l_Lean_MVarId_getTag(v_mvarId_990_, v___y_995_, v___y_996_, v___y_997_, v___y_998_);
if (lean_obj_tag(v___x_1006_) == 0)
{
lean_object* v_a_1007_; lean_object* v___x_1008_; 
v_a_1007_ = lean_ctor_get(v___x_1006_, 0);
lean_inc(v_a_1007_);
lean_dec_ref_known(v___x_1006_, 1);
v___x_1008_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_fst_1004_, v_a_1007_, v___y_995_, v___y_996_, v___y_997_, v___y_998_);
if (lean_obj_tag(v___x_1008_) == 0)
{
lean_object* v_a_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1014_; uint8_t v_isShared_1015_; uint8_t v_isSharedCheck_1020_; 
v_a_1009_ = lean_ctor_get(v___x_1008_, 0);
lean_inc_n(v_a_1009_, 2);
lean_dec_ref_known(v___x_1008_, 1);
v___x_1010_ = l_Lean_mkAppN(v_a_1009_, v_targets_994_);
v___x_1011_ = l_Lean_mkAppN(v___x_1010_, v_snd_1005_);
lean_dec(v_snd_1005_);
v___x_1012_ = l_Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1___redArg(v_mvarId_990_, v___x_1011_, v___y_996_);
v_isSharedCheck_1020_ = !lean_is_exclusive(v___x_1012_);
if (v_isSharedCheck_1020_ == 0)
{
lean_object* v_unused_1021_; 
v_unused_1021_ = lean_ctor_get(v___x_1012_, 0);
lean_dec(v_unused_1021_);
v___x_1014_ = v___x_1012_;
v_isShared_1015_ = v_isSharedCheck_1020_;
goto v_resetjp_1013_;
}
else
{
lean_dec(v___x_1012_);
v___x_1014_ = lean_box(0);
v_isShared_1015_ = v_isSharedCheck_1020_;
goto v_resetjp_1013_;
}
v_resetjp_1013_:
{
lean_object* v___x_1016_; lean_object* v___x_1018_; 
v___x_1016_ = l_Lean_Expr_mvarId_x21(v_a_1009_);
lean_dec(v_a_1009_);
if (v_isShared_1015_ == 0)
{
lean_ctor_set(v___x_1014_, 0, v___x_1016_);
v___x_1018_ = v___x_1014_;
goto v_reusejp_1017_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v___x_1016_);
v___x_1018_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1017_;
}
v_reusejp_1017_:
{
return v___x_1018_;
}
}
}
else
{
lean_object* v_a_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1029_; 
lean_dec(v_snd_1005_);
lean_dec(v_mvarId_990_);
v_a_1022_ = lean_ctor_get(v___x_1008_, 0);
v_isSharedCheck_1029_ = !lean_is_exclusive(v___x_1008_);
if (v_isSharedCheck_1029_ == 0)
{
v___x_1024_ = v___x_1008_;
v_isShared_1025_ = v_isSharedCheck_1029_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_a_1022_);
lean_dec(v___x_1008_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1029_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v___x_1027_; 
if (v_isShared_1025_ == 0)
{
v___x_1027_ = v___x_1024_;
goto v_reusejp_1026_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v_a_1022_);
v___x_1027_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1026_;
}
v_reusejp_1026_:
{
return v___x_1027_;
}
}
}
}
else
{
lean_object* v_a_1030_; lean_object* v___x_1032_; uint8_t v_isShared_1033_; uint8_t v_isSharedCheck_1037_; 
lean_dec(v_snd_1005_);
lean_dec(v_fst_1004_);
lean_dec(v_mvarId_990_);
v_a_1030_ = lean_ctor_get(v___x_1006_, 0);
v_isSharedCheck_1037_ = !lean_is_exclusive(v___x_1006_);
if (v_isSharedCheck_1037_ == 0)
{
v___x_1032_ = v___x_1006_;
v_isShared_1033_ = v_isSharedCheck_1037_;
goto v_resetjp_1031_;
}
else
{
lean_inc(v_a_1030_);
lean_dec(v___x_1006_);
v___x_1032_ = lean_box(0);
v_isShared_1033_ = v_isSharedCheck_1037_;
goto v_resetjp_1031_;
}
v_resetjp_1031_:
{
lean_object* v___x_1035_; 
if (v_isShared_1033_ == 0)
{
v___x_1035_ = v___x_1032_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1036_; 
v_reuseFailAlloc_1036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1036_, 0, v_a_1030_);
v___x_1035_ = v_reuseFailAlloc_1036_;
goto v_reusejp_1034_;
}
v_reusejp_1034_:
{
return v___x_1035_;
}
}
}
}
else
{
lean_object* v_a_1038_; lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1045_; 
lean_dec(v_mvarId_990_);
v_a_1038_ = lean_ctor_get(v___x_1002_, 0);
v_isSharedCheck_1045_ = !lean_is_exclusive(v___x_1002_);
if (v_isSharedCheck_1045_ == 0)
{
v___x_1040_ = v___x_1002_;
v_isShared_1041_ = v_isSharedCheck_1045_;
goto v_resetjp_1039_;
}
else
{
lean_inc(v_a_1038_);
lean_dec(v___x_1002_);
v___x_1040_ = lean_box(0);
v_isShared_1041_ = v_isSharedCheck_1045_;
goto v_resetjp_1039_;
}
v_resetjp_1039_:
{
lean_object* v___x_1043_; 
if (v_isShared_1041_ == 0)
{
v___x_1043_ = v___x_1040_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1044_, 0, v_a_1038_);
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
else
{
lean_object* v_a_1046_; lean_object* v___x_1048_; uint8_t v_isShared_1049_; uint8_t v_isSharedCheck_1053_; 
lean_dec_ref(v___f_993_);
lean_dec_ref(v_motiveType_992_);
lean_dec(v_mvarId_990_);
v_a_1046_ = lean_ctor_get(v___x_1000_, 0);
v_isSharedCheck_1053_ = !lean_is_exclusive(v___x_1000_);
if (v_isSharedCheck_1053_ == 0)
{
v___x_1048_ = v___x_1000_;
v_isShared_1049_ = v_isSharedCheck_1053_;
goto v_resetjp_1047_;
}
else
{
lean_inc(v_a_1046_);
lean_dec(v___x_1000_);
v___x_1048_ = lean_box(0);
v_isShared_1049_ = v_isSharedCheck_1053_;
goto v_resetjp_1047_;
}
v_resetjp_1047_:
{
lean_object* v___x_1051_; 
if (v_isShared_1049_ == 0)
{
v___x_1051_ = v___x_1048_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1052_; 
v_reuseFailAlloc_1052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1052_, 0, v_a_1046_);
v___x_1051_ = v_reuseFailAlloc_1052_;
goto v_reusejp_1050_;
}
v_reusejp_1050_:
{
return v___x_1051_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_generalizeTargetsEq___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_990_ = stack[0].m_obj;
lean_object* v___x_991_ = stack[1].m_obj;
lean_object* v_motiveType_992_ = stack[2].m_obj;
lean_object* v___f_993_ = stack[3].m_obj;
lean_object* v_targets_994_ = stack[4].m_obj;
lean_object* v___y_995_ = stack[5].m_obj;
lean_object* v___y_996_ = stack[6].m_obj;
lean_object* v___y_997_ = stack[7].m_obj;
lean_object* v___y_998_ = stack[8].m_obj;
lean_object* v_res_1054_;
v_res_1054_ = l_Lean_Meta_generalizeTargetsEq___lam__2(v_mvarId_990_, v___x_991_, v_motiveType_992_, v___f_993_, v_targets_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_);
stack->m_obj
 = v_res_1054_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeTargetsEq___lam__2___boxed(lean_object* v_mvarId_1055_, lean_object* v___x_1056_, lean_object* v_motiveType_1057_, lean_object* v___f_1058_, lean_object* v_targets_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_){
_start:
{
lean_object* v_res_1065_; 
v_res_1065_ = l_Lean_Meta_generalizeTargetsEq___lam__2(v_mvarId_1055_, v___x_1056_, v_motiveType_1057_, v___f_1058_, v_targets_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_);
lean_dec(v___y_1063_);
lean_dec_ref(v___y_1062_);
lean_dec(v___y_1061_);
lean_dec_ref(v___y_1060_);
lean_dec_ref(v_targets_1059_);
return v_res_1065_;
}
}
lean_object* l_Lean_Meta_generalizeTargetsEq(lean_object* v_mvarId_1069_, lean_object* v_motiveType_1070_, lean_object* v_targets_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_){
_start:
{
lean_object* v___f_1077_; lean_object* v___x_1078_; lean_object* v___f_1079_; lean_object* v___x_1080_; 
lean_inc_n(v_mvarId_1069_, 2);
lean_inc_ref(v_targets_1071_);
v___f_1077_ = lean_alloc_closure((void*)(l_Lean_Meta_generalizeTargetsEq___lam__1___boxed), 9, 2);
lean_closure_set(v___f_1077_, 0, v_targets_1071_);
lean_closure_set(v___f_1077_, 1, v_mvarId_1069_);
v___x_1078_ = ((lean_object*)(l_Lean_Meta_generalizeTargetsEq___closed__1));
v___f_1079_ = lean_alloc_closure((void*)(l_Lean_Meta_generalizeTargetsEq___lam__2___boxed), 10, 5);
lean_closure_set(v___f_1079_, 0, v_mvarId_1069_);
lean_closure_set(v___f_1079_, 1, v___x_1078_);
lean_closure_set(v___f_1079_, 2, v_motiveType_1070_);
lean_closure_set(v___f_1079_, 3, v___f_1077_);
lean_closure_set(v___f_1079_, 4, v_targets_1071_);
v___x_1080_ = l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2___redArg(v_mvarId_1069_, v___f_1079_, v_a_1072_, v_a_1073_, v_a_1074_, v_a_1075_);
return v___x_1080_;
}
}
LEAN_EXPORT void l_Lean_Meta_generalizeTargetsEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1069_ = stack[0].m_obj;
lean_object* v_motiveType_1070_ = stack[1].m_obj;
lean_object* v_targets_1071_ = stack[2].m_obj;
lean_object* v_a_1072_ = stack[3].m_obj;
lean_object* v_a_1073_ = stack[4].m_obj;
lean_object* v_a_1074_ = stack[5].m_obj;
lean_object* v_a_1075_ = stack[6].m_obj;
lean_object* v_res_1081_;
v_res_1081_ = l_Lean_Meta_generalizeTargetsEq(v_mvarId_1069_, v_motiveType_1070_, v_targets_1071_, v_a_1072_, v_a_1073_, v_a_1074_, v_a_1075_);
stack->m_obj
 = v_res_1081_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeTargetsEq___boxed(lean_object* v_mvarId_1082_, lean_object* v_motiveType_1083_, lean_object* v_targets_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_){
_start:
{
lean_object* v_res_1090_; 
v_res_1090_ = l_Lean_Meta_generalizeTargetsEq(v_mvarId_1082_, v_motiveType_1083_, v_targets_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_);
lean_dec(v_a_1088_);
lean_dec_ref(v_a_1087_);
lean_dec(v_a_1086_);
lean_dec_ref(v_a_1085_);
return v_res_1090_;
}
}
lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1(lean_object* v_mvarId_1091_, lean_object* v_val_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_){
_start:
{
lean_object* v___x_1098_; 
v___x_1098_ = l_Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1___redArg(v_mvarId_1091_, v_val_1092_, v___y_1094_);
return v___x_1098_;
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1091_ = stack[0].m_obj;
lean_object* v_val_1092_ = stack[1].m_obj;
lean_object* v___y_1093_ = stack[2].m_obj;
lean_object* v___y_1094_ = stack[3].m_obj;
lean_object* v___y_1095_ = stack[4].m_obj;
lean_object* v___y_1096_ = stack[5].m_obj;
lean_object* v_res_1099_;
v_res_1099_ = l_Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1(v_mvarId_1091_, v_val_1092_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_);
stack->m_obj
 = v_res_1099_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1___boxed(lean_object* v_mvarId_1100_, lean_object* v_val_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_){
_start:
{
lean_object* v_res_1107_; 
v_res_1107_ = l_Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1(v_mvarId_1100_, v_val_1101_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_);
lean_dec(v___y_1105_);
lean_dec_ref(v___y_1104_);
lean_dec(v___y_1103_);
lean_dec_ref(v___y_1102_);
return v_res_1107_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1(lean_object* v_00_u03b2_1108_, lean_object* v_x_1109_, lean_object* v_x_1110_, lean_object* v_x_1111_){
_start:
{
lean_object* v___x_1112_; 
v___x_1112_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1___redArg(v_x_1109_, v_x_1110_, v_x_1111_);
return v___x_1112_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3(lean_object* v_00_u03b2_1113_, lean_object* v_x_1114_, size_t v_x_1115_, size_t v_x_1116_, lean_object* v_x_1117_, lean_object* v_x_1118_){
_start:
{
lean_object* v___x_1119_; 
v___x_1119_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg(v_x_1114_, v_x_1115_, v_x_1116_, v_x_1117_, v_x_1118_);
return v___x_1119_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1114_ = stack[1].m_obj;
size_t v_x_1115_ = stack[2].m_num;
size_t v_x_1116_ = stack[3].m_num;
lean_object* v_x_1117_ = stack[4].m_obj;
lean_object* v_x_1118_ = stack[5].m_obj;
lean_object* v_res_1120_;
v_res_1120_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3(lean_box(0), v_x_1114_, v_x_1115_, v_x_1116_, v_x_1117_, v_x_1118_);
stack->m_obj
 = v_res_1120_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1121_, lean_object* v_x_1122_, lean_object* v_x_1123_, lean_object* v_x_1124_, lean_object* v_x_1125_, lean_object* v_x_1126_){
_start:
{
size_t v_x_3371__boxed_1127_; size_t v_x_3372__boxed_1128_; lean_object* v_res_1129_; 
v_x_3371__boxed_1127_ = lean_unbox_usize(v_x_1123_);
lean_dec(v_x_1123_);
v_x_3372__boxed_1128_ = lean_unbox_usize(v_x_1124_);
lean_dec(v_x_1124_);
v_res_1129_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3(v_00_u03b2_1121_, v_x_1122_, v_x_3371__boxed_1127_, v_x_3372__boxed_1128_, v_x_1125_, v_x_1126_);
return v_res_1129_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_1130_, lean_object* v_n_1131_, lean_object* v_k_1132_, lean_object* v_v_1133_){
_start:
{
lean_object* v___x_1134_; 
v___x_1134_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__4___redArg(v_n_1131_, v_k_1132_, v_v_1133_);
return v___x_1134_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__5(lean_object* v_00_u03b2_1135_, size_t v_depth_1136_, lean_object* v_keys_1137_, lean_object* v_vals_1138_, lean_object* v_heq_1139_, lean_object* v_i_1140_, lean_object* v_entries_1141_){
_start:
{
lean_object* v___x_1142_; 
v___x_1142_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__5___redArg(v_depth_1136_, v_keys_1137_, v_vals_1138_, v_i_1140_, v_entries_1141_);
return v___x_1142_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__5_0interp(lean_interpreter_value* stack)
{
size_t v_depth_1136_ = stack[1].m_num;
lean_object* v_keys_1137_ = stack[2].m_obj;
lean_object* v_vals_1138_ = stack[3].m_obj;
lean_object* v_i_1140_ = stack[5].m_obj;
lean_object* v_entries_1141_ = stack[6].m_obj;
lean_object* v_res_1143_;
v_res_1143_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__5(lean_box(0), v_depth_1136_, v_keys_1137_, v_vals_1138_, lean_box(0), v_i_1140_, v_entries_1141_);
stack->m_obj
 = v_res_1143_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__5___boxed(lean_object* v_00_u03b2_1144_, lean_object* v_depth_1145_, lean_object* v_keys_1146_, lean_object* v_vals_1147_, lean_object* v_heq_1148_, lean_object* v_i_1149_, lean_object* v_entries_1150_){
_start:
{
size_t v_depth_boxed_1151_; lean_object* v_res_1152_; 
v_depth_boxed_1151_ = lean_unbox_usize(v_depth_1145_);
lean_dec(v_depth_1145_);
v_res_1152_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__5(v_00_u03b2_1144_, v_depth_boxed_1151_, v_keys_1146_, v_vals_1147_, v_heq_1148_, v_i_1149_, v_entries_1150_);
lean_dec_ref(v_vals_1147_);
lean_dec_ref(v_keys_1146_);
return v_res_1152_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_1153_, lean_object* v_x_1154_, lean_object* v_x_1155_, lean_object* v_x_1156_, lean_object* v_x_1157_){
_start:
{
lean_object* v___x_1158_; 
v___x_1158_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__4_spec__5___redArg(v_x_1154_, v_x_1155_, v_x_1156_, v_x_1157_);
return v___x_1158_;
}
}
lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__0(lean_object* v_newEqs_1159_, lean_object* v_mvarId_1160_, uint8_t v___x_1161_, lean_object* v_h_x27_1162_, lean_object* v_newIndices_1163_, lean_object* v___x_1164_, lean_object* v___x_1165_, lean_object* v___x_1166_, lean_object* v___x_1167_, lean_object* v_e_1168_, lean_object* v___x_1169_, lean_object* v_newEq_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_){
_start:
{
lean_object* v___x_1176_; lean_object* v___x_1177_; 
v___x_1176_ = lean_array_push(v_newEqs_1159_, v_newEq_1170_);
lean_inc(v_mvarId_1160_);
v___x_1177_ = l_Lean_MVarId_getType(v_mvarId_1160_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_);
if (lean_obj_tag(v___x_1177_) == 0)
{
lean_object* v_a_1178_; lean_object* v___x_1179_; 
v_a_1178_ = lean_ctor_get(v___x_1177_, 0);
lean_inc(v_a_1178_);
lean_dec_ref_known(v___x_1177_, 1);
lean_inc(v_mvarId_1160_);
v___x_1179_ = l_Lean_MVarId_getTag(v_mvarId_1160_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_);
if (lean_obj_tag(v___x_1179_) == 0)
{
lean_object* v_a_1180_; uint8_t v___x_1181_; uint8_t v___x_1182_; lean_object* v___x_1183_; 
v_a_1180_ = lean_ctor_get(v___x_1179_, 0);
lean_inc(v_a_1180_);
lean_dec_ref_known(v___x_1179_, 1);
v___x_1181_ = 1;
v___x_1182_ = 1;
v___x_1183_ = l_Lean_Meta_mkForallFVars(v___x_1176_, v_a_1178_, v___x_1161_, v___x_1181_, v___x_1181_, v___x_1182_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_);
if (lean_obj_tag(v___x_1183_) == 0)
{
lean_object* v_a_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; 
v_a_1184_ = lean_ctor_get(v___x_1183_, 0);
lean_inc(v_a_1184_);
lean_dec_ref_known(v___x_1183_, 1);
v___x_1185_ = lean_unsigned_to_nat(1u);
v___x_1186_ = lean_mk_empty_array_with_capacity(v___x_1185_);
v___x_1187_ = lean_array_push(v___x_1186_, v_h_x27_1162_);
v___x_1188_ = l_Lean_Meta_mkForallFVars(v___x_1187_, v_a_1184_, v___x_1161_, v___x_1181_, v___x_1181_, v___x_1182_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_);
lean_dec_ref(v___x_1187_);
if (lean_obj_tag(v___x_1188_) == 0)
{
lean_object* v_a_1189_; lean_object* v___x_1190_; 
v_a_1189_ = lean_ctor_get(v___x_1188_, 0);
lean_inc(v_a_1189_);
lean_dec_ref_known(v___x_1188_, 1);
v___x_1190_ = l_Lean_Meta_mkForallFVars(v_newIndices_1163_, v_a_1189_, v___x_1161_, v___x_1181_, v___x_1181_, v___x_1182_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_);
if (lean_obj_tag(v___x_1190_) == 0)
{
lean_object* v_a_1191_; uint8_t v___x_1192_; lean_object* v___x_1193_; 
v_a_1191_ = lean_ctor_get(v___x_1190_, 0);
lean_inc(v_a_1191_);
lean_dec_ref_known(v___x_1190_, 1);
v___x_1192_ = 2;
v___x_1193_ = l_Lean_Meta_mkFreshExprMVarAt(v___x_1164_, v___x_1165_, v_a_1191_, v___x_1192_, v_a_1180_, v___x_1166_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_);
if (lean_obj_tag(v___x_1193_) == 0)
{
lean_object* v_a_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; 
v_a_1194_ = lean_ctor_get(v___x_1193_, 0);
lean_inc_n(v_a_1194_, 2);
lean_dec_ref_known(v___x_1193_, 1);
v___x_1195_ = l_Lean_mkAppN(v_a_1194_, v___x_1167_);
v___x_1196_ = l_Lean_Expr_app___override(v___x_1195_, v_e_1168_);
v___x_1197_ = l_Lean_mkAppN(v___x_1196_, v___x_1169_);
v___x_1198_ = l_Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1___redArg(v_mvarId_1160_, v___x_1197_, v___y_1172_);
lean_dec_ref(v___x_1198_);
v___x_1199_ = l_Lean_Expr_mvarId_x21(v_a_1194_);
lean_dec(v_a_1194_);
v___x_1200_ = lean_array_get_size(v_newIndices_1163_);
v___x_1201_ = lean_box(0);
v___x_1202_ = l_Lean_Meta_introNCore(v___x_1199_, v___x_1200_, v___x_1201_, v___x_1161_, v___x_1181_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_);
if (lean_obj_tag(v___x_1202_) == 0)
{
lean_object* v_a_1203_; lean_object* v_fst_1204_; lean_object* v_snd_1205_; lean_object* v___x_1206_; 
v_a_1203_ = lean_ctor_get(v___x_1202_, 0);
lean_inc(v_a_1203_);
lean_dec_ref_known(v___x_1202_, 1);
v_fst_1204_ = lean_ctor_get(v_a_1203_, 0);
lean_inc(v_fst_1204_);
v_snd_1205_ = lean_ctor_get(v_a_1203_, 1);
lean_inc(v_snd_1205_);
lean_dec(v_a_1203_);
v___x_1206_ = l_Lean_Meta_intro1Core(v_snd_1205_, v___x_1181_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_);
if (lean_obj_tag(v___x_1206_) == 0)
{
lean_object* v_a_1207_; lean_object* v___x_1209_; uint8_t v_isShared_1210_; uint8_t v_isSharedCheck_1218_; 
v_a_1207_ = lean_ctor_get(v___x_1206_, 0);
v_isSharedCheck_1218_ = !lean_is_exclusive(v___x_1206_);
if (v_isSharedCheck_1218_ == 0)
{
v___x_1209_ = v___x_1206_;
v_isShared_1210_ = v_isSharedCheck_1218_;
goto v_resetjp_1208_;
}
else
{
lean_inc(v_a_1207_);
lean_dec(v___x_1206_);
v___x_1209_ = lean_box(0);
v_isShared_1210_ = v_isSharedCheck_1218_;
goto v_resetjp_1208_;
}
v_resetjp_1208_:
{
lean_object* v_fst_1211_; lean_object* v_snd_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1216_; 
v_fst_1211_ = lean_ctor_get(v_a_1207_, 0);
lean_inc(v_fst_1211_);
v_snd_1212_ = lean_ctor_get(v_a_1207_, 1);
lean_inc(v_snd_1212_);
lean_dec(v_a_1207_);
v___x_1213_ = lean_array_get_size(v___x_1176_);
lean_dec_ref(v___x_1176_);
v___x_1214_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1214_, 0, v_snd_1212_);
lean_ctor_set(v___x_1214_, 1, v_fst_1204_);
lean_ctor_set(v___x_1214_, 2, v_fst_1211_);
lean_ctor_set(v___x_1214_, 3, v___x_1213_);
if (v_isShared_1210_ == 0)
{
lean_ctor_set(v___x_1209_, 0, v___x_1214_);
v___x_1216_ = v___x_1209_;
goto v_reusejp_1215_;
}
else
{
lean_object* v_reuseFailAlloc_1217_; 
v_reuseFailAlloc_1217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1217_, 0, v___x_1214_);
v___x_1216_ = v_reuseFailAlloc_1217_;
goto v_reusejp_1215_;
}
v_reusejp_1215_:
{
return v___x_1216_;
}
}
}
else
{
lean_object* v_a_1219_; lean_object* v___x_1221_; uint8_t v_isShared_1222_; uint8_t v_isSharedCheck_1226_; 
lean_dec(v_fst_1204_);
lean_dec_ref(v___x_1176_);
v_a_1219_ = lean_ctor_get(v___x_1206_, 0);
v_isSharedCheck_1226_ = !lean_is_exclusive(v___x_1206_);
if (v_isSharedCheck_1226_ == 0)
{
v___x_1221_ = v___x_1206_;
v_isShared_1222_ = v_isSharedCheck_1226_;
goto v_resetjp_1220_;
}
else
{
lean_inc(v_a_1219_);
lean_dec(v___x_1206_);
v___x_1221_ = lean_box(0);
v_isShared_1222_ = v_isSharedCheck_1226_;
goto v_resetjp_1220_;
}
v_resetjp_1220_:
{
lean_object* v___x_1224_; 
if (v_isShared_1222_ == 0)
{
v___x_1224_ = v___x_1221_;
goto v_reusejp_1223_;
}
else
{
lean_object* v_reuseFailAlloc_1225_; 
v_reuseFailAlloc_1225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1225_, 0, v_a_1219_);
v___x_1224_ = v_reuseFailAlloc_1225_;
goto v_reusejp_1223_;
}
v_reusejp_1223_:
{
return v___x_1224_;
}
}
}
}
else
{
lean_object* v_a_1227_; lean_object* v___x_1229_; uint8_t v_isShared_1230_; uint8_t v_isSharedCheck_1234_; 
lean_dec_ref(v___x_1176_);
v_a_1227_ = lean_ctor_get(v___x_1202_, 0);
v_isSharedCheck_1234_ = !lean_is_exclusive(v___x_1202_);
if (v_isSharedCheck_1234_ == 0)
{
v___x_1229_ = v___x_1202_;
v_isShared_1230_ = v_isSharedCheck_1234_;
goto v_resetjp_1228_;
}
else
{
lean_inc(v_a_1227_);
lean_dec(v___x_1202_);
v___x_1229_ = lean_box(0);
v_isShared_1230_ = v_isSharedCheck_1234_;
goto v_resetjp_1228_;
}
v_resetjp_1228_:
{
lean_object* v___x_1232_; 
if (v_isShared_1230_ == 0)
{
v___x_1232_ = v___x_1229_;
goto v_reusejp_1231_;
}
else
{
lean_object* v_reuseFailAlloc_1233_; 
v_reuseFailAlloc_1233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1233_, 0, v_a_1227_);
v___x_1232_ = v_reuseFailAlloc_1233_;
goto v_reusejp_1231_;
}
v_reusejp_1231_:
{
return v___x_1232_;
}
}
}
}
else
{
lean_object* v_a_1235_; lean_object* v___x_1237_; uint8_t v_isShared_1238_; uint8_t v_isSharedCheck_1242_; 
lean_dec_ref(v___x_1176_);
lean_dec_ref(v_e_1168_);
lean_dec(v_mvarId_1160_);
v_a_1235_ = lean_ctor_get(v___x_1193_, 0);
v_isSharedCheck_1242_ = !lean_is_exclusive(v___x_1193_);
if (v_isSharedCheck_1242_ == 0)
{
v___x_1237_ = v___x_1193_;
v_isShared_1238_ = v_isSharedCheck_1242_;
goto v_resetjp_1236_;
}
else
{
lean_inc(v_a_1235_);
lean_dec(v___x_1193_);
v___x_1237_ = lean_box(0);
v_isShared_1238_ = v_isSharedCheck_1242_;
goto v_resetjp_1236_;
}
v_resetjp_1236_:
{
lean_object* v___x_1240_; 
if (v_isShared_1238_ == 0)
{
v___x_1240_ = v___x_1237_;
goto v_reusejp_1239_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v_a_1235_);
v___x_1240_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1239_;
}
v_reusejp_1239_:
{
return v___x_1240_;
}
}
}
}
else
{
lean_object* v_a_1243_; lean_object* v___x_1245_; uint8_t v_isShared_1246_; uint8_t v_isSharedCheck_1250_; 
lean_dec(v_a_1180_);
lean_dec_ref(v___x_1176_);
lean_dec_ref(v_e_1168_);
lean_dec(v___x_1166_);
lean_dec_ref(v___x_1165_);
lean_dec_ref(v___x_1164_);
lean_dec(v_mvarId_1160_);
v_a_1243_ = lean_ctor_get(v___x_1190_, 0);
v_isSharedCheck_1250_ = !lean_is_exclusive(v___x_1190_);
if (v_isSharedCheck_1250_ == 0)
{
v___x_1245_ = v___x_1190_;
v_isShared_1246_ = v_isSharedCheck_1250_;
goto v_resetjp_1244_;
}
else
{
lean_inc(v_a_1243_);
lean_dec(v___x_1190_);
v___x_1245_ = lean_box(0);
v_isShared_1246_ = v_isSharedCheck_1250_;
goto v_resetjp_1244_;
}
v_resetjp_1244_:
{
lean_object* v___x_1248_; 
if (v_isShared_1246_ == 0)
{
v___x_1248_ = v___x_1245_;
goto v_reusejp_1247_;
}
else
{
lean_object* v_reuseFailAlloc_1249_; 
v_reuseFailAlloc_1249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1249_, 0, v_a_1243_);
v___x_1248_ = v_reuseFailAlloc_1249_;
goto v_reusejp_1247_;
}
v_reusejp_1247_:
{
return v___x_1248_;
}
}
}
}
else
{
lean_object* v_a_1251_; lean_object* v___x_1253_; uint8_t v_isShared_1254_; uint8_t v_isSharedCheck_1258_; 
lean_dec(v_a_1180_);
lean_dec_ref(v___x_1176_);
lean_dec_ref(v_e_1168_);
lean_dec(v___x_1166_);
lean_dec_ref(v___x_1165_);
lean_dec_ref(v___x_1164_);
lean_dec(v_mvarId_1160_);
v_a_1251_ = lean_ctor_get(v___x_1188_, 0);
v_isSharedCheck_1258_ = !lean_is_exclusive(v___x_1188_);
if (v_isSharedCheck_1258_ == 0)
{
v___x_1253_ = v___x_1188_;
v_isShared_1254_ = v_isSharedCheck_1258_;
goto v_resetjp_1252_;
}
else
{
lean_inc(v_a_1251_);
lean_dec(v___x_1188_);
v___x_1253_ = lean_box(0);
v_isShared_1254_ = v_isSharedCheck_1258_;
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
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v_a_1251_);
v___x_1256_ = v_reuseFailAlloc_1257_;
goto v_reusejp_1255_;
}
v_reusejp_1255_:
{
return v___x_1256_;
}
}
}
}
else
{
lean_object* v_a_1259_; lean_object* v___x_1261_; uint8_t v_isShared_1262_; uint8_t v_isSharedCheck_1266_; 
lean_dec(v_a_1180_);
lean_dec_ref(v___x_1176_);
lean_dec_ref(v_e_1168_);
lean_dec(v___x_1166_);
lean_dec_ref(v___x_1165_);
lean_dec_ref(v___x_1164_);
lean_dec_ref(v_h_x27_1162_);
lean_dec(v_mvarId_1160_);
v_a_1259_ = lean_ctor_get(v___x_1183_, 0);
v_isSharedCheck_1266_ = !lean_is_exclusive(v___x_1183_);
if (v_isSharedCheck_1266_ == 0)
{
v___x_1261_ = v___x_1183_;
v_isShared_1262_ = v_isSharedCheck_1266_;
goto v_resetjp_1260_;
}
else
{
lean_inc(v_a_1259_);
lean_dec(v___x_1183_);
v___x_1261_ = lean_box(0);
v_isShared_1262_ = v_isSharedCheck_1266_;
goto v_resetjp_1260_;
}
v_resetjp_1260_:
{
lean_object* v___x_1264_; 
if (v_isShared_1262_ == 0)
{
v___x_1264_ = v___x_1261_;
goto v_reusejp_1263_;
}
else
{
lean_object* v_reuseFailAlloc_1265_; 
v_reuseFailAlloc_1265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1265_, 0, v_a_1259_);
v___x_1264_ = v_reuseFailAlloc_1265_;
goto v_reusejp_1263_;
}
v_reusejp_1263_:
{
return v___x_1264_;
}
}
}
}
else
{
lean_object* v_a_1267_; lean_object* v___x_1269_; uint8_t v_isShared_1270_; uint8_t v_isSharedCheck_1274_; 
lean_dec(v_a_1178_);
lean_dec_ref(v___x_1176_);
lean_dec_ref(v_e_1168_);
lean_dec(v___x_1166_);
lean_dec_ref(v___x_1165_);
lean_dec_ref(v___x_1164_);
lean_dec_ref(v_h_x27_1162_);
lean_dec(v_mvarId_1160_);
v_a_1267_ = lean_ctor_get(v___x_1179_, 0);
v_isSharedCheck_1274_ = !lean_is_exclusive(v___x_1179_);
if (v_isSharedCheck_1274_ == 0)
{
v___x_1269_ = v___x_1179_;
v_isShared_1270_ = v_isSharedCheck_1274_;
goto v_resetjp_1268_;
}
else
{
lean_inc(v_a_1267_);
lean_dec(v___x_1179_);
v___x_1269_ = lean_box(0);
v_isShared_1270_ = v_isSharedCheck_1274_;
goto v_resetjp_1268_;
}
v_resetjp_1268_:
{
lean_object* v___x_1272_; 
if (v_isShared_1270_ == 0)
{
v___x_1272_ = v___x_1269_;
goto v_reusejp_1271_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v_a_1267_);
v___x_1272_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1271_;
}
v_reusejp_1271_:
{
return v___x_1272_;
}
}
}
}
else
{
lean_object* v_a_1275_; lean_object* v___x_1277_; uint8_t v_isShared_1278_; uint8_t v_isSharedCheck_1282_; 
lean_dec_ref(v___x_1176_);
lean_dec_ref(v_e_1168_);
lean_dec(v___x_1166_);
lean_dec_ref(v___x_1165_);
lean_dec_ref(v___x_1164_);
lean_dec_ref(v_h_x27_1162_);
lean_dec(v_mvarId_1160_);
v_a_1275_ = lean_ctor_get(v___x_1177_, 0);
v_isSharedCheck_1282_ = !lean_is_exclusive(v___x_1177_);
if (v_isSharedCheck_1282_ == 0)
{
v___x_1277_ = v___x_1177_;
v_isShared_1278_ = v_isSharedCheck_1282_;
goto v_resetjp_1276_;
}
else
{
lean_inc(v_a_1275_);
lean_dec(v___x_1177_);
v___x_1277_ = lean_box(0);
v_isShared_1278_ = v_isSharedCheck_1282_;
goto v_resetjp_1276_;
}
v_resetjp_1276_:
{
lean_object* v___x_1280_; 
if (v_isShared_1278_ == 0)
{
v___x_1280_ = v___x_1277_;
goto v_reusejp_1279_;
}
else
{
lean_object* v_reuseFailAlloc_1281_; 
v_reuseFailAlloc_1281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1281_, 0, v_a_1275_);
v___x_1280_ = v_reuseFailAlloc_1281_;
goto v_reusejp_1279_;
}
v_reusejp_1279_:
{
return v___x_1280_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_newEqs_1159_ = stack[0].m_obj;
lean_object* v_mvarId_1160_ = stack[1].m_obj;
uint8_t v___x_1161_ = stack[2].m_num;
lean_object* v_h_x27_1162_ = stack[3].m_obj;
lean_object* v_newIndices_1163_ = stack[4].m_obj;
lean_object* v___x_1164_ = stack[5].m_obj;
lean_object* v___x_1165_ = stack[6].m_obj;
lean_object* v___x_1166_ = stack[7].m_obj;
lean_object* v___x_1167_ = stack[8].m_obj;
lean_object* v_e_1168_ = stack[9].m_obj;
lean_object* v___x_1169_ = stack[10].m_obj;
lean_object* v_newEq_1170_ = stack[11].m_obj;
lean_object* v___y_1171_ = stack[12].m_obj;
lean_object* v___y_1172_ = stack[13].m_obj;
lean_object* v___y_1173_ = stack[14].m_obj;
lean_object* v___y_1174_ = stack[15].m_obj;
lean_object* v_res_1283_;
v_res_1283_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__0(v_newEqs_1159_, v_mvarId_1160_, v___x_1161_, v_h_x27_1162_, v_newIndices_1163_, v___x_1164_, v___x_1165_, v___x_1166_, v___x_1167_, v_e_1168_, v___x_1169_, v_newEq_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_);
stack->m_obj
 = v_res_1283_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__0___boxed(lean_object** _args){
lean_object* v_newEqs_1284_ = _args[0];
lean_object* v_mvarId_1285_ = _args[1];
lean_object* v___x_1286_ = _args[2];
lean_object* v_h_x27_1287_ = _args[3];
lean_object* v_newIndices_1288_ = _args[4];
lean_object* v___x_1289_ = _args[5];
lean_object* v___x_1290_ = _args[6];
lean_object* v___x_1291_ = _args[7];
lean_object* v___x_1292_ = _args[8];
lean_object* v_e_1293_ = _args[9];
lean_object* v___x_1294_ = _args[10];
lean_object* v_newEq_1295_ = _args[11];
lean_object* v___y_1296_ = _args[12];
lean_object* v___y_1297_ = _args[13];
lean_object* v___y_1298_ = _args[14];
lean_object* v___y_1299_ = _args[15];
lean_object* v___y_1300_ = _args[16];
_start:
{
uint8_t v___x_6158__boxed_1301_; lean_object* v_res_1302_; 
v___x_6158__boxed_1301_ = lean_unbox(v___x_1286_);
v_res_1302_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__0(v_newEqs_1284_, v_mvarId_1285_, v___x_6158__boxed_1301_, v_h_x27_1287_, v_newIndices_1288_, v___x_1289_, v___x_1290_, v___x_1291_, v___x_1292_, v_e_1293_, v___x_1294_, v_newEq_1295_, v___y_1296_, v___y_1297_, v___y_1298_, v___y_1299_);
lean_dec(v___y_1299_);
lean_dec_ref(v___y_1298_);
lean_dec(v___y_1297_);
lean_dec_ref(v___y_1296_);
lean_dec_ref(v___x_1294_);
lean_dec_ref(v___x_1292_);
lean_dec_ref(v_newIndices_1288_);
return v_res_1302_;
}
}
lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__1(lean_object* v_e_1303_, lean_object* v_h_x27_1304_, lean_object* v_mvarId_1305_, uint8_t v___x_1306_, lean_object* v_newIndices_1307_, lean_object* v___x_1308_, lean_object* v___x_1309_, lean_object* v___x_1310_, lean_object* v___x_1311_, lean_object* v_newEqs_1312_, lean_object* v_newRefls_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_){
_start:
{
lean_object* v___x_1319_; 
lean_inc_ref(v_h_x27_1304_);
lean_inc_ref(v_e_1303_);
v___x_1319_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof(v_e_1303_, v_h_x27_1304_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_);
if (lean_obj_tag(v___x_1319_) == 0)
{
lean_object* v_a_1320_; lean_object* v_fst_1321_; lean_object* v_snd_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___f_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; 
v_a_1320_ = lean_ctor_get(v___x_1319_, 0);
lean_inc(v_a_1320_);
lean_dec_ref_known(v___x_1319_, 1);
v_fst_1321_ = lean_ctor_get(v_a_1320_, 0);
lean_inc(v_fst_1321_);
v_snd_1322_ = lean_ctor_get(v_a_1320_, 1);
lean_inc(v_snd_1322_);
lean_dec(v_a_1320_);
v___x_1323_ = lean_array_push(v_newRefls_1313_, v_snd_1322_);
v___x_1324_ = lean_box(v___x_1306_);
v___f_1325_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__0___boxed), 17, 11);
lean_closure_set(v___f_1325_, 0, v_newEqs_1312_);
lean_closure_set(v___f_1325_, 1, v_mvarId_1305_);
lean_closure_set(v___f_1325_, 2, v___x_1324_);
lean_closure_set(v___f_1325_, 3, v_h_x27_1304_);
lean_closure_set(v___f_1325_, 4, v_newIndices_1307_);
lean_closure_set(v___f_1325_, 5, v___x_1308_);
lean_closure_set(v___f_1325_, 6, v___x_1309_);
lean_closure_set(v___f_1325_, 7, v___x_1310_);
lean_closure_set(v___f_1325_, 8, v___x_1311_);
lean_closure_set(v___f_1325_, 9, v_e_1303_);
lean_closure_set(v___f_1325_, 10, v___x_1323_);
v___x_1326_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___redArg___closed__1));
v___x_1327_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0___redArg(v___x_1326_, v_fst_1321_, v___f_1325_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_);
return v___x_1327_;
}
else
{
lean_object* v_a_1328_; lean_object* v___x_1330_; uint8_t v_isShared_1331_; uint8_t v_isSharedCheck_1335_; 
lean_dec_ref(v_newRefls_1313_);
lean_dec_ref(v_newEqs_1312_);
lean_dec_ref(v___x_1311_);
lean_dec(v___x_1310_);
lean_dec_ref(v___x_1309_);
lean_dec_ref(v___x_1308_);
lean_dec_ref(v_newIndices_1307_);
lean_dec(v_mvarId_1305_);
lean_dec_ref(v_h_x27_1304_);
lean_dec_ref(v_e_1303_);
v_a_1328_ = lean_ctor_get(v___x_1319_, 0);
v_isSharedCheck_1335_ = !lean_is_exclusive(v___x_1319_);
if (v_isSharedCheck_1335_ == 0)
{
v___x_1330_ = v___x_1319_;
v_isShared_1331_ = v_isSharedCheck_1335_;
goto v_resetjp_1329_;
}
else
{
lean_inc(v_a_1328_);
lean_dec(v___x_1319_);
v___x_1330_ = lean_box(0);
v_isShared_1331_ = v_isSharedCheck_1335_;
goto v_resetjp_1329_;
}
v_resetjp_1329_:
{
lean_object* v___x_1333_; 
if (v_isShared_1331_ == 0)
{
v___x_1333_ = v___x_1330_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v_a_1328_);
v___x_1333_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
return v___x_1333_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1303_ = stack[0].m_obj;
lean_object* v_h_x27_1304_ = stack[1].m_obj;
lean_object* v_mvarId_1305_ = stack[2].m_obj;
uint8_t v___x_1306_ = stack[3].m_num;
lean_object* v_newIndices_1307_ = stack[4].m_obj;
lean_object* v___x_1308_ = stack[5].m_obj;
lean_object* v___x_1309_ = stack[6].m_obj;
lean_object* v___x_1310_ = stack[7].m_obj;
lean_object* v___x_1311_ = stack[8].m_obj;
lean_object* v_newEqs_1312_ = stack[9].m_obj;
lean_object* v_newRefls_1313_ = stack[10].m_obj;
lean_object* v___y_1314_ = stack[11].m_obj;
lean_object* v___y_1315_ = stack[12].m_obj;
lean_object* v___y_1316_ = stack[13].m_obj;
lean_object* v___y_1317_ = stack[14].m_obj;
lean_object* v_res_1336_;
v_res_1336_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__1(v_e_1303_, v_h_x27_1304_, v_mvarId_1305_, v___x_1306_, v_newIndices_1307_, v___x_1308_, v___x_1309_, v___x_1310_, v___x_1311_, v_newEqs_1312_, v_newRefls_1313_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_);
stack->m_obj
 = v_res_1336_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__1___boxed(lean_object* v_e_1337_, lean_object* v_h_x27_1338_, lean_object* v_mvarId_1339_, lean_object* v___x_1340_, lean_object* v_newIndices_1341_, lean_object* v___x_1342_, lean_object* v___x_1343_, lean_object* v___x_1344_, lean_object* v___x_1345_, lean_object* v_newEqs_1346_, lean_object* v_newRefls_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_){
_start:
{
uint8_t v___x_6539__boxed_1353_; lean_object* v_res_1354_; 
v___x_6539__boxed_1353_ = lean_unbox(v___x_1340_);
v_res_1354_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__1(v_e_1337_, v_h_x27_1338_, v_mvarId_1339_, v___x_6539__boxed_1353_, v_newIndices_1341_, v___x_1342_, v___x_1343_, v___x_1344_, v___x_1345_, v_newEqs_1346_, v_newRefls_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_);
lean_dec(v___y_1351_);
lean_dec_ref(v___y_1350_);
lean_dec(v___y_1349_);
lean_dec_ref(v___y_1348_);
return v_res_1354_;
}
}
lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__2(lean_object* v_e_1355_, lean_object* v_mvarId_1356_, uint8_t v___x_1357_, lean_object* v_newIndices_1358_, lean_object* v___x_1359_, lean_object* v___x_1360_, lean_object* v___x_1361_, lean_object* v___x_1362_, lean_object* v_h_x27_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_){
_start:
{
lean_object* v___x_1369_; lean_object* v___f_1370_; lean_object* v___x_1371_; 
v___x_1369_ = lean_box(v___x_1357_);
lean_inc_ref(v___x_1362_);
lean_inc_ref(v_newIndices_1358_);
v___f_1370_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__1___boxed), 16, 9);
lean_closure_set(v___f_1370_, 0, v_e_1355_);
lean_closure_set(v___f_1370_, 1, v_h_x27_1363_);
lean_closure_set(v___f_1370_, 2, v_mvarId_1356_);
lean_closure_set(v___f_1370_, 3, v___x_1369_);
lean_closure_set(v___f_1370_, 4, v_newIndices_1358_);
lean_closure_set(v___f_1370_, 5, v___x_1359_);
lean_closure_set(v___f_1370_, 6, v___x_1360_);
lean_closure_set(v___f_1370_, 7, v___x_1361_);
lean_closure_set(v___f_1370_, 8, v___x_1362_);
v___x_1371_ = l_Lean_Meta_withNewEqs___redArg(v___x_1362_, v_newIndices_1358_, v___f_1370_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_);
return v___x_1371_;
}
}
LEAN_EXPORT void l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1355_ = stack[0].m_obj;
lean_object* v_mvarId_1356_ = stack[1].m_obj;
uint8_t v___x_1357_ = stack[2].m_num;
lean_object* v_newIndices_1358_ = stack[3].m_obj;
lean_object* v___x_1359_ = stack[4].m_obj;
lean_object* v___x_1360_ = stack[5].m_obj;
lean_object* v___x_1361_ = stack[6].m_obj;
lean_object* v___x_1362_ = stack[7].m_obj;
lean_object* v_h_x27_1363_ = stack[8].m_obj;
lean_object* v___y_1364_ = stack[9].m_obj;
lean_object* v___y_1365_ = stack[10].m_obj;
lean_object* v___y_1366_ = stack[11].m_obj;
lean_object* v___y_1367_ = stack[12].m_obj;
lean_object* v_res_1372_;
v_res_1372_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__2(v_e_1355_, v_mvarId_1356_, v___x_1357_, v_newIndices_1358_, v___x_1359_, v___x_1360_, v___x_1361_, v___x_1362_, v_h_x27_1363_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_);
stack->m_obj
 = v_res_1372_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__2___boxed(lean_object* v_e_1373_, lean_object* v_mvarId_1374_, lean_object* v___x_1375_, lean_object* v_newIndices_1376_, lean_object* v___x_1377_, lean_object* v___x_1378_, lean_object* v___x_1379_, lean_object* v___x_1380_, lean_object* v_h_x27_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_){
_start:
{
uint8_t v___x_6641__boxed_1387_; lean_object* v_res_1388_; 
v___x_6641__boxed_1387_ = lean_unbox(v___x_1375_);
v_res_1388_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__2(v_e_1373_, v_mvarId_1374_, v___x_6641__boxed_1387_, v_newIndices_1376_, v___x_1377_, v___x_1378_, v___x_1379_, v___x_1380_, v_h_x27_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_);
lean_dec(v___y_1385_);
lean_dec_ref(v___y_1384_);
lean_dec(v___y_1383_);
lean_dec_ref(v___y_1382_);
return v_res_1388_;
}
}
lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__3(lean_object* v_e_1392_, lean_object* v_mvarId_1393_, uint8_t v___x_1394_, lean_object* v___x_1395_, lean_object* v___x_1396_, lean_object* v___x_1397_, lean_object* v___x_1398_, lean_object* v___x_1399_, lean_object* v_varName_x3f_1400_, lean_object* v_newIndices_1401_, lean_object* v_x_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_){
_start:
{
lean_object* v___x_1408_; lean_object* v___f_1409_; lean_object* v___x_1410_; 
v___x_1408_ = lean_box(v___x_1394_);
lean_inc_ref(v_newIndices_1401_);
v___f_1409_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__2___boxed), 14, 8);
lean_closure_set(v___f_1409_, 0, v_e_1392_);
lean_closure_set(v___f_1409_, 1, v_mvarId_1393_);
lean_closure_set(v___f_1409_, 2, v___x_1408_);
lean_closure_set(v___f_1409_, 3, v_newIndices_1401_);
lean_closure_set(v___f_1409_, 4, v___x_1395_);
lean_closure_set(v___f_1409_, 5, v___x_1396_);
lean_closure_set(v___f_1409_, 6, v___x_1397_);
lean_closure_set(v___f_1409_, 7, v___x_1398_);
v___x_1410_ = l_Lean_mkAppN(v___x_1399_, v_newIndices_1401_);
lean_dec_ref(v_newIndices_1401_);
if (lean_obj_tag(v_varName_x3f_1400_) == 1)
{
lean_object* v_val_1411_; lean_object* v___x_1412_; 
v_val_1411_ = lean_ctor_get(v_varName_x3f_1400_, 0);
lean_inc(v_val_1411_);
lean_dec_ref_known(v_varName_x3f_1400_, 1);
v___x_1412_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0___redArg(v_val_1411_, v___x_1410_, v___f_1409_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_);
return v___x_1412_;
}
else
{
lean_object* v___x_1413_; lean_object* v___x_1414_; 
lean_dec(v_varName_x3f_1400_);
v___x_1413_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__3___closed__1));
v___x_1414_ = l_Lean_Core_mkFreshUserName(v___x_1413_, v___y_1405_, v___y_1406_);
if (lean_obj_tag(v___x_1414_) == 0)
{
lean_object* v_a_1415_; lean_object* v___x_1416_; 
v_a_1415_ = lean_ctor_get(v___x_1414_, 0);
lean_inc(v_a_1415_);
lean_dec_ref_known(v___x_1414_, 1);
v___x_1416_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0___redArg(v_a_1415_, v___x_1410_, v___f_1409_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_);
return v___x_1416_;
}
else
{
lean_object* v_a_1417_; lean_object* v___x_1419_; uint8_t v_isShared_1420_; uint8_t v_isSharedCheck_1424_; 
lean_dec_ref(v___x_1410_);
lean_dec_ref(v___f_1409_);
v_a_1417_ = lean_ctor_get(v___x_1414_, 0);
v_isSharedCheck_1424_ = !lean_is_exclusive(v___x_1414_);
if (v_isSharedCheck_1424_ == 0)
{
v___x_1419_ = v___x_1414_;
v_isShared_1420_ = v_isSharedCheck_1424_;
goto v_resetjp_1418_;
}
else
{
lean_inc(v_a_1417_);
lean_dec(v___x_1414_);
v___x_1419_ = lean_box(0);
v_isShared_1420_ = v_isSharedCheck_1424_;
goto v_resetjp_1418_;
}
v_resetjp_1418_:
{
lean_object* v___x_1422_; 
if (v_isShared_1420_ == 0)
{
v___x_1422_ = v___x_1419_;
goto v_reusejp_1421_;
}
else
{
lean_object* v_reuseFailAlloc_1423_; 
v_reuseFailAlloc_1423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1423_, 0, v_a_1417_);
v___x_1422_ = v_reuseFailAlloc_1423_;
goto v_reusejp_1421_;
}
v_reusejp_1421_:
{
return v___x_1422_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1392_ = stack[0].m_obj;
lean_object* v_mvarId_1393_ = stack[1].m_obj;
uint8_t v___x_1394_ = stack[2].m_num;
lean_object* v___x_1395_ = stack[3].m_obj;
lean_object* v___x_1396_ = stack[4].m_obj;
lean_object* v___x_1397_ = stack[5].m_obj;
lean_object* v___x_1398_ = stack[6].m_obj;
lean_object* v___x_1399_ = stack[7].m_obj;
lean_object* v_varName_x3f_1400_ = stack[8].m_obj;
lean_object* v_newIndices_1401_ = stack[9].m_obj;
lean_object* v_x_1402_ = stack[10].m_obj;
lean_object* v___y_1403_ = stack[11].m_obj;
lean_object* v___y_1404_ = stack[12].m_obj;
lean_object* v___y_1405_ = stack[13].m_obj;
lean_object* v___y_1406_ = stack[14].m_obj;
lean_object* v_res_1425_;
v_res_1425_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__3(v_e_1392_, v_mvarId_1393_, v___x_1394_, v___x_1395_, v___x_1396_, v___x_1397_, v___x_1398_, v___x_1399_, v_varName_x3f_1400_, v_newIndices_1401_, v_x_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_);
stack->m_obj
 = v_res_1425_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__3___boxed(lean_object* v_e_1426_, lean_object* v_mvarId_1427_, lean_object* v___x_1428_, lean_object* v___x_1429_, lean_object* v___x_1430_, lean_object* v___x_1431_, lean_object* v___x_1432_, lean_object* v___x_1433_, lean_object* v_varName_x3f_1434_, lean_object* v_newIndices_1435_, lean_object* v_x_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_){
_start:
{
uint8_t v___x_6706__boxed_1442_; lean_object* v_res_1443_; 
v___x_6706__boxed_1442_ = lean_unbox(v___x_1428_);
v_res_1443_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__3(v_e_1426_, v_mvarId_1427_, v___x_6706__boxed_1442_, v___x_1429_, v___x_1430_, v___x_1431_, v___x_1432_, v___x_1433_, v_varName_x3f_1434_, v_newIndices_1435_, v_x_1436_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_);
lean_dec(v___y_1440_);
lean_dec_ref(v___y_1439_);
lean_dec(v___y_1438_);
lean_dec_ref(v___y_1437_);
lean_dec_ref(v_x_1436_);
return v_res_1443_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__4(void){
_start:
{
lean_object* v___x_1450_; lean_object* v___x_1451_; 
v___x_1450_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__3));
v___x_1451_ = l_Lean_MessageData_ofFormat(v___x_1450_);
return v___x_1451_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__5(void){
_start:
{
lean_object* v___x_1452_; lean_object* v___x_1453_; 
v___x_1452_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__4, &l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__4_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__4);
v___x_1453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1453_, 0, v___x_1452_);
return v___x_1453_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__8(void){
_start:
{
lean_object* v___x_1457_; lean_object* v___x_1458_; 
v___x_1457_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__7));
v___x_1458_ = l_Lean_MessageData_ofFormat(v___x_1457_);
return v___x_1458_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__9(void){
_start:
{
lean_object* v___x_1459_; lean_object* v___x_1460_; 
v___x_1459_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__8, &l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__8_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__8);
v___x_1460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1460_, 0, v___x_1459_);
return v___x_1460_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__12(void){
_start:
{
lean_object* v___x_1464_; lean_object* v___x_1465_; 
v___x_1464_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__11));
v___x_1465_ = l_Lean_MessageData_ofFormat(v___x_1464_);
return v___x_1465_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__13(void){
_start:
{
lean_object* v___x_1466_; lean_object* v___x_1467_; 
v___x_1466_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__12, &l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__12_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__12);
v___x_1467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1467_, 0, v___x_1466_);
return v___x_1467_;
}
}
lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0(lean_object* v_mvarId_1468_, lean_object* v_e_1469_, lean_object* v___x_1470_, lean_object* v___x_1471_, lean_object* v_varName_x3f_1472_, lean_object* v_x_1473_, lean_object* v_x_1474_, lean_object* v_x_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_){
_start:
{
if (lean_obj_tag(v_x_1473_) == 5)
{
lean_object* v_fn_1481_; lean_object* v_arg_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; 
v_fn_1481_ = lean_ctor_get(v_x_1473_, 0);
lean_inc_ref(v_fn_1481_);
v_arg_1482_ = lean_ctor_get(v_x_1473_, 1);
lean_inc_ref(v_arg_1482_);
lean_dec_ref_known(v_x_1473_, 2);
v___x_1483_ = lean_array_set(v_x_1474_, v_x_1475_, v_arg_1482_);
v___x_1484_ = lean_unsigned_to_nat(1u);
v___x_1485_ = lean_nat_sub(v_x_1475_, v___x_1484_);
lean_dec(v_x_1475_);
v_x_1473_ = v_fn_1481_;
v_x_1474_ = v___x_1483_;
v_x_1475_ = v___x_1485_;
goto _start;
}
else
{
lean_object* v___x_1487_; lean_object* v___y_1489_; lean_object* v___y_1490_; lean_object* v___y_1491_; lean_object* v___y_1492_; 
lean_dec(v_x_1475_);
v___x_1487_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__1));
if (lean_obj_tag(v_x_1473_) == 4)
{
lean_object* v_declName_1495_; lean_object* v___x_1496_; lean_object* v_env_1497_; uint8_t v___x_1498_; lean_object* v___x_1499_; 
v_declName_1495_ = lean_ctor_get(v_x_1473_, 0);
v___x_1496_ = lean_st_ref_get(v___y_1479_);
v_env_1497_ = lean_ctor_get(v___x_1496_, 0);
lean_inc_ref(v_env_1497_);
lean_dec(v___x_1496_);
v___x_1498_ = 0;
lean_inc(v_declName_1495_);
v___x_1499_ = l_Lean_Environment_find_x3f(v_env_1497_, v_declName_1495_, v___x_1498_);
if (lean_obj_tag(v___x_1499_) == 0)
{
lean_dec_ref_known(v_x_1473_, 2);
lean_dec_ref(v_x_1474_);
lean_dec(v_varName_x3f_1472_);
lean_dec_ref(v___x_1471_);
lean_dec_ref(v___x_1470_);
lean_dec_ref(v_e_1469_);
v___y_1489_ = v___y_1476_;
v___y_1490_ = v___y_1477_;
v___y_1491_ = v___y_1478_;
v___y_1492_ = v___y_1479_;
goto v___jp_1488_;
}
else
{
lean_object* v_val_1500_; 
v_val_1500_ = lean_ctor_get(v___x_1499_, 0);
lean_inc(v_val_1500_);
lean_dec_ref_known(v___x_1499_, 1);
if (lean_obj_tag(v_val_1500_) == 5)
{
lean_object* v_val_1501_; lean_object* v_numParams_1502_; lean_object* v_numIndices_1503_; lean_object* v___y_1505_; lean_object* v___y_1506_; lean_object* v___y_1507_; lean_object* v___y_1508_; lean_object* v___y_1529_; lean_object* v___y_1530_; lean_object* v___y_1531_; lean_object* v___y_1532_; lean_object* v___x_1546_; uint8_t v___x_1547_; 
v_val_1501_ = lean_ctor_get(v_val_1500_, 0);
lean_inc_ref(v_val_1501_);
lean_dec_ref_known(v_val_1500_, 1);
v_numParams_1502_ = lean_ctor_get(v_val_1501_, 1);
lean_inc(v_numParams_1502_);
v_numIndices_1503_ = lean_ctor_get(v_val_1501_, 2);
lean_inc(v_numIndices_1503_);
lean_dec_ref(v_val_1501_);
v___x_1546_ = lean_unsigned_to_nat(0u);
v___x_1547_ = lean_nat_dec_lt(v___x_1546_, v_numIndices_1503_);
if (v___x_1547_ == 0)
{
lean_object* v___x_1548_; lean_object* v___x_1549_; 
v___x_1548_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__13, &l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__13_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__13);
lean_inc(v_mvarId_1468_);
v___x_1549_ = l_Lean_Meta_throwTacticEx___redArg(v___x_1487_, v_mvarId_1468_, v___x_1548_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_);
if (lean_obj_tag(v___x_1549_) == 0)
{
lean_dec_ref_known(v___x_1549_, 1);
v___y_1529_ = v___y_1476_;
v___y_1530_ = v___y_1477_;
v___y_1531_ = v___y_1478_;
v___y_1532_ = v___y_1479_;
goto v___jp_1528_;
}
else
{
lean_object* v_a_1550_; lean_object* v___x_1552_; uint8_t v_isShared_1553_; uint8_t v_isSharedCheck_1557_; 
lean_dec(v_numIndices_1503_);
lean_dec(v_numParams_1502_);
lean_dec_ref_known(v_x_1473_, 2);
lean_dec_ref(v_x_1474_);
lean_dec(v_varName_x3f_1472_);
lean_dec_ref(v___x_1471_);
lean_dec_ref(v___x_1470_);
lean_dec_ref(v_e_1469_);
lean_dec(v_mvarId_1468_);
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
else
{
v___y_1529_ = v___y_1476_;
v___y_1530_ = v___y_1477_;
v___y_1531_ = v___y_1478_;
v___y_1532_ = v___y_1479_;
goto v___jp_1528_;
}
v___jp_1504_:
{
lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___f_1516_; lean_object* v___x_1517_; 
v___x_1509_ = lean_array_get_size(v_x_1474_);
v___x_1510_ = lean_nat_sub(v___x_1509_, v_numIndices_1503_);
lean_dec(v_numIndices_1503_);
v___x_1511_ = l_Array_extract___redArg(v_x_1474_, v___x_1510_, v___x_1509_);
v___x_1512_ = lean_unsigned_to_nat(0u);
v___x_1513_ = l_Array_extract___redArg(v_x_1474_, v___x_1512_, v_numParams_1502_);
lean_dec_ref(v_x_1474_);
v___x_1514_ = l_Lean_mkAppN(v_x_1473_, v___x_1513_);
lean_dec_ref(v___x_1513_);
v___x_1515_ = lean_box(v___x_1498_);
lean_inc_ref(v___x_1514_);
v___f_1516_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__3___boxed), 16, 9);
lean_closure_set(v___f_1516_, 0, v_e_1469_);
lean_closure_set(v___f_1516_, 1, v_mvarId_1468_);
lean_closure_set(v___f_1516_, 2, v___x_1515_);
lean_closure_set(v___f_1516_, 3, v___x_1470_);
lean_closure_set(v___f_1516_, 4, v___x_1471_);
lean_closure_set(v___f_1516_, 5, v___x_1512_);
lean_closure_set(v___f_1516_, 6, v___x_1511_);
lean_closure_set(v___f_1516_, 7, v___x_1514_);
lean_closure_set(v___f_1516_, 8, v_varName_x3f_1472_);
lean_inc(v___y_1508_);
lean_inc_ref(v___y_1507_);
lean_inc(v___y_1506_);
lean_inc_ref(v___y_1505_);
v___x_1517_ = lean_infer_type(v___x_1514_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_);
if (lean_obj_tag(v___x_1517_) == 0)
{
lean_object* v_a_1518_; lean_object* v___x_1519_; 
v_a_1518_ = lean_ctor_get(v___x_1517_, 0);
lean_inc(v_a_1518_);
lean_dec_ref_known(v___x_1517_, 1);
v___x_1519_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_generalizeTargetsEq_spec__0___redArg(v_a_1518_, v___f_1516_, v___x_1498_, v___x_1498_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_);
return v___x_1519_;
}
else
{
lean_object* v_a_1520_; lean_object* v___x_1522_; uint8_t v_isShared_1523_; uint8_t v_isSharedCheck_1527_; 
lean_dec_ref(v___f_1516_);
v_a_1520_ = lean_ctor_get(v___x_1517_, 0);
v_isSharedCheck_1527_ = !lean_is_exclusive(v___x_1517_);
if (v_isSharedCheck_1527_ == 0)
{
v___x_1522_ = v___x_1517_;
v_isShared_1523_ = v_isSharedCheck_1527_;
goto v_resetjp_1521_;
}
else
{
lean_inc(v_a_1520_);
lean_dec(v___x_1517_);
v___x_1522_ = lean_box(0);
v_isShared_1523_ = v_isSharedCheck_1527_;
goto v_resetjp_1521_;
}
v_resetjp_1521_:
{
lean_object* v___x_1525_; 
if (v_isShared_1523_ == 0)
{
v___x_1525_ = v___x_1522_;
goto v_reusejp_1524_;
}
else
{
lean_object* v_reuseFailAlloc_1526_; 
v_reuseFailAlloc_1526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1526_, 0, v_a_1520_);
v___x_1525_ = v_reuseFailAlloc_1526_;
goto v_reusejp_1524_;
}
v_reusejp_1524_:
{
return v___x_1525_;
}
}
}
}
v___jp_1528_:
{
lean_object* v___x_1533_; lean_object* v___x_1534_; uint8_t v___x_1535_; 
v___x_1533_ = lean_array_get_size(v_x_1474_);
v___x_1534_ = lean_nat_add(v_numIndices_1503_, v_numParams_1502_);
v___x_1535_ = lean_nat_dec_eq(v___x_1533_, v___x_1534_);
lean_dec(v___x_1534_);
if (v___x_1535_ == 0)
{
lean_object* v___x_1536_; lean_object* v___x_1537_; 
v___x_1536_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__9, &l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__9_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__9);
lean_inc(v_mvarId_1468_);
v___x_1537_ = l_Lean_Meta_throwTacticEx___redArg(v___x_1487_, v_mvarId_1468_, v___x_1536_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_);
if (lean_obj_tag(v___x_1537_) == 0)
{
lean_dec_ref_known(v___x_1537_, 1);
v___y_1505_ = v___y_1529_;
v___y_1506_ = v___y_1530_;
v___y_1507_ = v___y_1531_;
v___y_1508_ = v___y_1532_;
goto v___jp_1504_;
}
else
{
lean_object* v_a_1538_; lean_object* v___x_1540_; uint8_t v_isShared_1541_; uint8_t v_isSharedCheck_1545_; 
lean_dec(v_numIndices_1503_);
lean_dec(v_numParams_1502_);
lean_dec_ref_known(v_x_1473_, 2);
lean_dec_ref(v_x_1474_);
lean_dec(v_varName_x3f_1472_);
lean_dec_ref(v___x_1471_);
lean_dec_ref(v___x_1470_);
lean_dec_ref(v_e_1469_);
lean_dec(v_mvarId_1468_);
v_a_1538_ = lean_ctor_get(v___x_1537_, 0);
v_isSharedCheck_1545_ = !lean_is_exclusive(v___x_1537_);
if (v_isSharedCheck_1545_ == 0)
{
v___x_1540_ = v___x_1537_;
v_isShared_1541_ = v_isSharedCheck_1545_;
goto v_resetjp_1539_;
}
else
{
lean_inc(v_a_1538_);
lean_dec(v___x_1537_);
v___x_1540_ = lean_box(0);
v_isShared_1541_ = v_isSharedCheck_1545_;
goto v_resetjp_1539_;
}
v_resetjp_1539_:
{
lean_object* v___x_1543_; 
if (v_isShared_1541_ == 0)
{
v___x_1543_ = v___x_1540_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v_a_1538_);
v___x_1543_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1542_;
}
v_reusejp_1542_:
{
return v___x_1543_;
}
}
}
}
else
{
v___y_1505_ = v___y_1529_;
v___y_1506_ = v___y_1530_;
v___y_1507_ = v___y_1531_;
v___y_1508_ = v___y_1532_;
goto v___jp_1504_;
}
}
}
else
{
lean_dec(v_val_1500_);
lean_dec_ref_known(v_x_1473_, 2);
lean_dec_ref(v_x_1474_);
lean_dec(v_varName_x3f_1472_);
lean_dec_ref(v___x_1471_);
lean_dec_ref(v___x_1470_);
lean_dec_ref(v_e_1469_);
v___y_1489_ = v___y_1476_;
v___y_1490_ = v___y_1477_;
v___y_1491_ = v___y_1478_;
v___y_1492_ = v___y_1479_;
goto v___jp_1488_;
}
}
}
else
{
lean_dec_ref(v_x_1474_);
lean_dec_ref(v_x_1473_);
lean_dec(v_varName_x3f_1472_);
lean_dec_ref(v___x_1471_);
lean_dec_ref(v___x_1470_);
lean_dec_ref(v_e_1469_);
v___y_1489_ = v___y_1476_;
v___y_1490_ = v___y_1477_;
v___y_1491_ = v___y_1478_;
v___y_1492_ = v___y_1479_;
goto v___jp_1488_;
}
v___jp_1488_:
{
lean_object* v___x_1493_; lean_object* v___x_1494_; 
v___x_1493_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__5, &l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__5_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__5);
v___x_1494_ = l_Lean_Meta_throwTacticEx___redArg(v___x_1487_, v_mvarId_1468_, v___x_1493_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_);
return v___x_1494_;
}
}
}
}
LEAN_EXPORT void l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1468_ = stack[0].m_obj;
lean_object* v_e_1469_ = stack[1].m_obj;
lean_object* v___x_1470_ = stack[2].m_obj;
lean_object* v___x_1471_ = stack[3].m_obj;
lean_object* v_varName_x3f_1472_ = stack[4].m_obj;
lean_object* v_x_1473_ = stack[5].m_obj;
lean_object* v_x_1474_ = stack[6].m_obj;
lean_object* v_x_1475_ = stack[7].m_obj;
lean_object* v___y_1476_ = stack[8].m_obj;
lean_object* v___y_1477_ = stack[9].m_obj;
lean_object* v___y_1478_ = stack[10].m_obj;
lean_object* v___y_1479_ = stack[11].m_obj;
lean_object* v_res_1558_;
v_res_1558_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0(v_mvarId_1468_, v_e_1469_, v___x_1470_, v___x_1471_, v_varName_x3f_1472_, v_x_1473_, v_x_1474_, v_x_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_);
stack->m_obj
 = v_res_1558_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___boxed(lean_object* v_mvarId_1559_, lean_object* v_e_1560_, lean_object* v___x_1561_, lean_object* v___x_1562_, lean_object* v_varName_x3f_1563_, lean_object* v_x_1564_, lean_object* v_x_1565_, lean_object* v_x_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_){
_start:
{
lean_object* v_res_1572_; 
v_res_1572_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0(v_mvarId_1559_, v_e_1560_, v___x_1561_, v___x_1562_, v_varName_x3f_1563_, v_x_1564_, v_x_1565_, v_x_1566_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_);
lean_dec(v___y_1570_);
lean_dec_ref(v___y_1569_);
lean_dec(v___y_1568_);
lean_dec_ref(v___y_1567_);
return v_res_1572_;
}
}
lean_object* l_Lean_Meta_generalizeIndices_x27___lam__0(lean_object* v_mvarId_1573_, lean_object* v_e_1574_, lean_object* v_varName_x3f_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_){
_start:
{
lean_object* v_lctx_1581_; lean_object* v_localInstances_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; 
v_lctx_1581_ = lean_ctor_get(v___y_1576_, 2);
lean_inc_ref(v_lctx_1581_);
v_localInstances_1582_ = lean_ctor_get(v___y_1576_, 3);
lean_inc_ref(v_localInstances_1582_);
v___x_1583_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__1));
lean_inc(v_mvarId_1573_);
v___x_1584_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_1573_, v___x_1583_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_);
if (lean_obj_tag(v___x_1584_) == 0)
{
lean_object* v___x_1585_; 
lean_dec_ref_known(v___x_1584_, 1);
lean_inc(v___y_1579_);
lean_inc_ref(v___y_1578_);
lean_inc(v___y_1577_);
lean_inc_ref(v___y_1576_);
lean_inc_ref(v_e_1574_);
v___x_1585_ = lean_infer_type(v_e_1574_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_);
if (lean_obj_tag(v___x_1585_) == 0)
{
lean_object* v_a_1586_; lean_object* v___x_1587_; 
v_a_1586_ = lean_ctor_get(v___x_1585_, 0);
lean_inc(v_a_1586_);
lean_dec_ref_known(v___x_1585_, 1);
v___x_1587_ = l_Lean_Meta_whnfD(v_a_1586_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_);
if (lean_obj_tag(v___x_1587_) == 0)
{
lean_object* v_a_1588_; lean_object* v_dummy_1589_; lean_object* v_nargs_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; 
v_a_1588_ = lean_ctor_get(v___x_1587_, 0);
lean_inc(v_a_1588_);
lean_dec_ref_known(v___x_1587_, 1);
v_dummy_1589_ = lean_obj_once(&l_Lean_Meta_getInductiveUniverseAndParams___closed__0, &l_Lean_Meta_getInductiveUniverseAndParams___closed__0_once, _init_l_Lean_Meta_getInductiveUniverseAndParams___closed__0);
v_nargs_1590_ = l_Lean_Expr_getAppNumArgs(v_a_1588_);
lean_inc(v_nargs_1590_);
v___x_1591_ = lean_mk_array(v_nargs_1590_, v_dummy_1589_);
v___x_1592_ = lean_unsigned_to_nat(1u);
v___x_1593_ = lean_nat_sub(v_nargs_1590_, v___x_1592_);
lean_dec(v_nargs_1590_);
v___x_1594_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0(v_mvarId_1573_, v_e_1574_, v_lctx_1581_, v_localInstances_1582_, v_varName_x3f_1575_, v_a_1588_, v___x_1591_, v___x_1593_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_);
lean_dec(v___y_1579_);
lean_dec_ref(v___y_1578_);
lean_dec(v___y_1577_);
lean_dec_ref(v___y_1576_);
return v___x_1594_;
}
else
{
lean_object* v_a_1595_; lean_object* v___x_1597_; uint8_t v_isShared_1598_; uint8_t v_isSharedCheck_1602_; 
lean_dec_ref(v_localInstances_1582_);
lean_dec_ref(v_lctx_1581_);
lean_dec(v___y_1579_);
lean_dec_ref(v___y_1578_);
lean_dec(v___y_1577_);
lean_dec_ref(v___y_1576_);
lean_dec(v_varName_x3f_1575_);
lean_dec_ref(v_e_1574_);
lean_dec(v_mvarId_1573_);
v_a_1595_ = lean_ctor_get(v___x_1587_, 0);
v_isSharedCheck_1602_ = !lean_is_exclusive(v___x_1587_);
if (v_isSharedCheck_1602_ == 0)
{
v___x_1597_ = v___x_1587_;
v_isShared_1598_ = v_isSharedCheck_1602_;
goto v_resetjp_1596_;
}
else
{
lean_inc(v_a_1595_);
lean_dec(v___x_1587_);
v___x_1597_ = lean_box(0);
v_isShared_1598_ = v_isSharedCheck_1602_;
goto v_resetjp_1596_;
}
v_resetjp_1596_:
{
lean_object* v___x_1600_; 
if (v_isShared_1598_ == 0)
{
v___x_1600_ = v___x_1597_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v_a_1595_);
v___x_1600_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
return v___x_1600_;
}
}
}
}
else
{
lean_object* v_a_1603_; lean_object* v___x_1605_; uint8_t v_isShared_1606_; uint8_t v_isSharedCheck_1610_; 
lean_dec_ref(v_localInstances_1582_);
lean_dec_ref(v_lctx_1581_);
lean_dec(v___y_1579_);
lean_dec_ref(v___y_1578_);
lean_dec(v___y_1577_);
lean_dec_ref(v___y_1576_);
lean_dec(v_varName_x3f_1575_);
lean_dec_ref(v_e_1574_);
lean_dec(v_mvarId_1573_);
v_a_1603_ = lean_ctor_get(v___x_1585_, 0);
v_isSharedCheck_1610_ = !lean_is_exclusive(v___x_1585_);
if (v_isSharedCheck_1610_ == 0)
{
v___x_1605_ = v___x_1585_;
v_isShared_1606_ = v_isSharedCheck_1610_;
goto v_resetjp_1604_;
}
else
{
lean_inc(v_a_1603_);
lean_dec(v___x_1585_);
v___x_1605_ = lean_box(0);
v_isShared_1606_ = v_isSharedCheck_1610_;
goto v_resetjp_1604_;
}
v_resetjp_1604_:
{
lean_object* v___x_1608_; 
if (v_isShared_1606_ == 0)
{
v___x_1608_ = v___x_1605_;
goto v_reusejp_1607_;
}
else
{
lean_object* v_reuseFailAlloc_1609_; 
v_reuseFailAlloc_1609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1609_, 0, v_a_1603_);
v___x_1608_ = v_reuseFailAlloc_1609_;
goto v_reusejp_1607_;
}
v_reusejp_1607_:
{
return v___x_1608_;
}
}
}
}
else
{
lean_object* v_a_1611_; lean_object* v___x_1613_; uint8_t v_isShared_1614_; uint8_t v_isSharedCheck_1618_; 
lean_dec_ref(v_localInstances_1582_);
lean_dec_ref(v_lctx_1581_);
lean_dec(v___y_1579_);
lean_dec_ref(v___y_1578_);
lean_dec(v___y_1577_);
lean_dec_ref(v___y_1576_);
lean_dec(v_varName_x3f_1575_);
lean_dec_ref(v_e_1574_);
lean_dec(v_mvarId_1573_);
v_a_1611_ = lean_ctor_get(v___x_1584_, 0);
v_isSharedCheck_1618_ = !lean_is_exclusive(v___x_1584_);
if (v_isSharedCheck_1618_ == 0)
{
v___x_1613_ = v___x_1584_;
v_isShared_1614_ = v_isSharedCheck_1618_;
goto v_resetjp_1612_;
}
else
{
lean_inc(v_a_1611_);
lean_dec(v___x_1584_);
v___x_1613_ = lean_box(0);
v_isShared_1614_ = v_isSharedCheck_1618_;
goto v_resetjp_1612_;
}
v_resetjp_1612_:
{
lean_object* v___x_1616_; 
if (v_isShared_1614_ == 0)
{
v___x_1616_ = v___x_1613_;
goto v_reusejp_1615_;
}
else
{
lean_object* v_reuseFailAlloc_1617_; 
v_reuseFailAlloc_1617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1617_, 0, v_a_1611_);
v___x_1616_ = v_reuseFailAlloc_1617_;
goto v_reusejp_1615_;
}
v_reusejp_1615_:
{
return v___x_1616_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_generalizeIndices_x27___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1573_ = stack[0].m_obj;
lean_object* v_e_1574_ = stack[1].m_obj;
lean_object* v_varName_x3f_1575_ = stack[2].m_obj;
lean_object* v___y_1576_ = stack[3].m_obj;
lean_object* v___y_1577_ = stack[4].m_obj;
lean_object* v___y_1578_ = stack[5].m_obj;
lean_object* v___y_1579_ = stack[6].m_obj;
lean_object* v_res_1619_;
v_res_1619_ = l_Lean_Meta_generalizeIndices_x27___lam__0(v_mvarId_1573_, v_e_1574_, v_varName_x3f_1575_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_);
stack->m_obj
 = v_res_1619_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeIndices_x27___lam__0___boxed(lean_object* v_mvarId_1620_, lean_object* v_e_1621_, lean_object* v_varName_x3f_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_){
_start:
{
lean_object* v_res_1628_; 
v_res_1628_ = l_Lean_Meta_generalizeIndices_x27___lam__0(v_mvarId_1620_, v_e_1621_, v_varName_x3f_1622_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_);
return v_res_1628_;
}
}
lean_object* l_Lean_Meta_generalizeIndices_x27(lean_object* v_mvarId_1629_, lean_object* v_e_1630_, lean_object* v_varName_x3f_1631_, lean_object* v_a_1632_, lean_object* v_a_1633_, lean_object* v_a_1634_, lean_object* v_a_1635_){
_start:
{
lean_object* v___f_1637_; lean_object* v___x_1638_; 
lean_inc(v_mvarId_1629_);
v___f_1637_ = lean_alloc_closure((void*)(l_Lean_Meta_generalizeIndices_x27___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1637_, 0, v_mvarId_1629_);
lean_closure_set(v___f_1637_, 1, v_e_1630_);
lean_closure_set(v___f_1637_, 2, v_varName_x3f_1631_);
v___x_1638_ = l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2___redArg(v_mvarId_1629_, v___f_1637_, v_a_1632_, v_a_1633_, v_a_1634_, v_a_1635_);
return v___x_1638_;
}
}
LEAN_EXPORT void l_Lean_Meta_generalizeIndices_x27_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1629_ = stack[0].m_obj;
lean_object* v_e_1630_ = stack[1].m_obj;
lean_object* v_varName_x3f_1631_ = stack[2].m_obj;
lean_object* v_a_1632_ = stack[3].m_obj;
lean_object* v_a_1633_ = stack[4].m_obj;
lean_object* v_a_1634_ = stack[5].m_obj;
lean_object* v_a_1635_ = stack[6].m_obj;
lean_object* v_res_1639_;
v_res_1639_ = l_Lean_Meta_generalizeIndices_x27(v_mvarId_1629_, v_e_1630_, v_varName_x3f_1631_, v_a_1632_, v_a_1633_, v_a_1634_, v_a_1635_);
stack->m_obj
 = v_res_1639_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeIndices_x27___boxed(lean_object* v_mvarId_1640_, lean_object* v_e_1641_, lean_object* v_varName_x3f_1642_, lean_object* v_a_1643_, lean_object* v_a_1644_, lean_object* v_a_1645_, lean_object* v_a_1646_, lean_object* v_a_1647_){
_start:
{
lean_object* v_res_1648_; 
v_res_1648_ = l_Lean_Meta_generalizeIndices_x27(v_mvarId_1640_, v_e_1641_, v_varName_x3f_1642_, v_a_1643_, v_a_1644_, v_a_1645_, v_a_1646_);
lean_dec(v_a_1646_);
lean_dec_ref(v_a_1645_);
lean_dec(v_a_1644_);
lean_dec_ref(v_a_1643_);
return v_res_1648_;
}
}
lean_object* l_Lean_Meta_generalizeIndices___lam__0(lean_object* v_fvarId_1649_, lean_object* v_mvarId_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_){
_start:
{
lean_object* v___x_1656_; 
v___x_1656_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_1649_, v___y_1651_, v___y_1653_, v___y_1654_);
if (lean_obj_tag(v___x_1656_) == 0)
{
lean_object* v_a_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; 
v_a_1657_ = lean_ctor_get(v___x_1656_, 0);
lean_inc_n(v_a_1657_, 2);
lean_dec_ref_known(v___x_1656_, 1);
v___x_1658_ = l_Lean_LocalDecl_toExpr(v_a_1657_);
v___x_1659_ = l_Lean_LocalDecl_userName(v_a_1657_);
lean_dec(v_a_1657_);
v___x_1660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1660_, 0, v___x_1659_);
v___x_1661_ = l_Lean_Meta_generalizeIndices_x27(v_mvarId_1650_, v___x_1658_, v___x_1660_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_);
return v___x_1661_;
}
else
{
lean_object* v_a_1662_; lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_1669_; 
lean_dec(v_mvarId_1650_);
v_a_1662_ = lean_ctor_get(v___x_1656_, 0);
v_isSharedCheck_1669_ = !lean_is_exclusive(v___x_1656_);
if (v_isSharedCheck_1669_ == 0)
{
v___x_1664_ = v___x_1656_;
v_isShared_1665_ = v_isSharedCheck_1669_;
goto v_resetjp_1663_;
}
else
{
lean_inc(v_a_1662_);
lean_dec(v___x_1656_);
v___x_1664_ = lean_box(0);
v_isShared_1665_ = v_isSharedCheck_1669_;
goto v_resetjp_1663_;
}
v_resetjp_1663_:
{
lean_object* v___x_1667_; 
if (v_isShared_1665_ == 0)
{
v___x_1667_ = v___x_1664_;
goto v_reusejp_1666_;
}
else
{
lean_object* v_reuseFailAlloc_1668_; 
v_reuseFailAlloc_1668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1668_, 0, v_a_1662_);
v___x_1667_ = v_reuseFailAlloc_1668_;
goto v_reusejp_1666_;
}
v_reusejp_1666_:
{
return v___x_1667_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_generalizeIndices___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_1649_ = stack[0].m_obj;
lean_object* v_mvarId_1650_ = stack[1].m_obj;
lean_object* v___y_1651_ = stack[2].m_obj;
lean_object* v___y_1652_ = stack[3].m_obj;
lean_object* v___y_1653_ = stack[4].m_obj;
lean_object* v___y_1654_ = stack[5].m_obj;
lean_object* v_res_1670_;
v_res_1670_ = l_Lean_Meta_generalizeIndices___lam__0(v_fvarId_1649_, v_mvarId_1650_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_);
stack->m_obj
 = v_res_1670_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeIndices___lam__0___boxed(lean_object* v_fvarId_1671_, lean_object* v_mvarId_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_){
_start:
{
lean_object* v_res_1678_; 
v_res_1678_ = l_Lean_Meta_generalizeIndices___lam__0(v_fvarId_1671_, v_mvarId_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_);
lean_dec(v___y_1676_);
lean_dec_ref(v___y_1675_);
lean_dec(v___y_1674_);
lean_dec_ref(v___y_1673_);
return v_res_1678_;
}
}
lean_object* l_Lean_Meta_generalizeIndices(lean_object* v_mvarId_1679_, lean_object* v_fvarId_1680_, lean_object* v_a_1681_, lean_object* v_a_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_){
_start:
{
lean_object* v___f_1686_; lean_object* v___x_1687_; 
lean_inc(v_mvarId_1679_);
v___f_1686_ = lean_alloc_closure((void*)(l_Lean_Meta_generalizeIndices___lam__0___boxed), 7, 2);
lean_closure_set(v___f_1686_, 0, v_fvarId_1680_);
lean_closure_set(v___f_1686_, 1, v_mvarId_1679_);
v___x_1687_ = l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2___redArg(v_mvarId_1679_, v___f_1686_, v_a_1681_, v_a_1682_, v_a_1683_, v_a_1684_);
return v___x_1687_;
}
}
LEAN_EXPORT void l_Lean_Meta_generalizeIndices_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1679_ = stack[0].m_obj;
lean_object* v_fvarId_1680_ = stack[1].m_obj;
lean_object* v_a_1681_ = stack[2].m_obj;
lean_object* v_a_1682_ = stack[3].m_obj;
lean_object* v_a_1683_ = stack[4].m_obj;
lean_object* v_a_1684_ = stack[5].m_obj;
lean_object* v_res_1688_;
v_res_1688_ = l_Lean_Meta_generalizeIndices(v_mvarId_1679_, v_fvarId_1680_, v_a_1681_, v_a_1682_, v_a_1683_, v_a_1684_);
stack->m_obj
 = v_res_1688_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeIndices___boxed(lean_object* v_mvarId_1689_, lean_object* v_fvarId_1690_, lean_object* v_a_1691_, lean_object* v_a_1692_, lean_object* v_a_1693_, lean_object* v_a_1694_, lean_object* v_a_1695_){
_start:
{
lean_object* v_res_1696_; 
v_res_1696_ = l_Lean_Meta_generalizeIndices(v_mvarId_1689_, v_fvarId_1690_, v_a_1691_, v_a_1692_, v_a_1693_, v_a_1694_);
lean_dec(v_a_1694_);
lean_dec_ref(v_a_1693_);
lean_dec(v_a_1692_);
lean_dec_ref(v_a_1691_);
return v_res_1696_;
}
}
lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0___redArg(lean_object* v___x_1698_, lean_object* v_a_1699_, lean_object* v_x_1700_, lean_object* v_x_1701_, lean_object* v_x_1702_, lean_object* v___y_1703_){
_start:
{
if (lean_obj_tag(v_x_1700_) == 5)
{
lean_object* v_fn_1708_; lean_object* v_arg_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; 
v_fn_1708_ = lean_ctor_get(v_x_1700_, 0);
lean_inc_ref(v_fn_1708_);
v_arg_1709_ = lean_ctor_get(v_x_1700_, 1);
lean_inc_ref(v_arg_1709_);
lean_dec_ref_known(v_x_1700_, 2);
v___x_1710_ = lean_array_set(v_x_1701_, v_x_1702_, v_arg_1709_);
v___x_1711_ = lean_unsigned_to_nat(1u);
v___x_1712_ = lean_nat_sub(v_x_1702_, v___x_1711_);
lean_dec(v_x_1702_);
v_x_1700_ = v_fn_1708_;
v_x_1701_ = v___x_1710_;
v_x_1702_ = v___x_1712_;
goto _start;
}
else
{
lean_dec(v_x_1702_);
if (lean_obj_tag(v_x_1700_) == 4)
{
lean_object* v_declName_1714_; uint8_t v___x_1715_; uint8_t v___x_1716_; lean_object* v___x_1717_; lean_object* v_env_1718_; lean_object* v___x_1719_; 
v_declName_1714_ = lean_ctor_get(v_x_1700_, 0);
v___x_1715_ = 0;
v___x_1716_ = 1;
v___x_1717_ = lean_st_ref_get(v___y_1703_);
v_env_1718_ = lean_ctor_get(v___x_1717_, 0);
lean_inc_ref(v_env_1718_);
lean_dec(v___x_1717_);
lean_inc(v_declName_1714_);
v___x_1719_ = l_Lean_Environment_find_x3f(v_env_1718_, v_declName_1714_, v___x_1715_);
if (lean_obj_tag(v___x_1719_) == 0)
{
lean_dec_ref_known(v_x_1700_, 2);
lean_dec_ref(v_x_1701_);
lean_dec_ref(v_a_1699_);
lean_dec_ref(v___x_1698_);
goto v___jp_1705_;
}
else
{
lean_object* v_val_1720_; lean_object* v___x_1722_; uint8_t v_isShared_1723_; uint8_t v_isSharedCheck_1758_; 
v_val_1720_ = lean_ctor_get(v___x_1719_, 0);
v_isSharedCheck_1758_ = !lean_is_exclusive(v___x_1719_);
if (v_isSharedCheck_1758_ == 0)
{
v___x_1722_ = v___x_1719_;
v_isShared_1723_ = v_isSharedCheck_1758_;
goto v_resetjp_1721_;
}
else
{
lean_inc(v_val_1720_);
lean_dec(v___x_1719_);
v___x_1722_ = lean_box(0);
v_isShared_1723_ = v_isSharedCheck_1758_;
goto v_resetjp_1721_;
}
v_resetjp_1721_:
{
if (lean_obj_tag(v_val_1720_) == 5)
{
lean_object* v_val_1724_; lean_object* v___x_1726_; uint8_t v_isShared_1727_; uint8_t v_isSharedCheck_1757_; 
v_val_1724_ = lean_ctor_get(v_val_1720_, 0);
v_isSharedCheck_1757_ = !lean_is_exclusive(v_val_1720_);
if (v_isSharedCheck_1757_ == 0)
{
v___x_1726_ = v_val_1720_;
v_isShared_1727_ = v_isSharedCheck_1757_;
goto v_resetjp_1725_;
}
else
{
lean_inc(v_val_1724_);
lean_dec(v_val_1720_);
v___x_1726_ = lean_box(0);
v_isShared_1727_ = v_isSharedCheck_1757_;
goto v_resetjp_1725_;
}
v_resetjp_1725_:
{
lean_object* v_toConstantVal_1728_; lean_object* v_numParams_1729_; lean_object* v_numIndices_1730_; lean_object* v_ctors_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; uint8_t v___x_1734_; 
v_toConstantVal_1728_ = lean_ctor_get(v_val_1724_, 0);
v_numParams_1729_ = lean_ctor_get(v_val_1724_, 1);
v_numIndices_1730_ = lean_ctor_get(v_val_1724_, 2);
v_ctors_1731_ = lean_ctor_get(v_val_1724_, 4);
v___x_1732_ = lean_array_get_size(v_x_1701_);
v___x_1733_ = lean_nat_add(v_numIndices_1730_, v_numParams_1729_);
v___x_1734_ = lean_nat_dec_eq(v___x_1732_, v___x_1733_);
lean_dec(v___x_1733_);
if (v___x_1734_ == 0)
{
lean_object* v___x_1735_; lean_object* v___x_1737_; 
lean_dec_ref(v_val_1724_);
lean_del_object(v___x_1722_);
lean_dec_ref_known(v_x_1700_, 2);
lean_dec_ref(v_x_1701_);
lean_dec_ref(v_a_1699_);
lean_dec_ref(v___x_1698_);
v___x_1735_ = lean_box(0);
if (v_isShared_1727_ == 0)
{
lean_ctor_set_tag(v___x_1726_, 0);
lean_ctor_set(v___x_1726_, 0, v___x_1735_);
v___x_1737_ = v___x_1726_;
goto v_reusejp_1736_;
}
else
{
lean_object* v_reuseFailAlloc_1738_; 
v_reuseFailAlloc_1738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1738_, 0, v___x_1735_);
v___x_1737_ = v_reuseFailAlloc_1738_;
goto v_reusejp_1736_;
}
v_reusejp_1736_:
{
return v___x_1737_;
}
}
else
{
lean_object* v_name_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; uint8_t v___x_1742_; 
v_name_1739_ = lean_ctor_get(v_toConstantVal_1728_, 0);
v___x_1740_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0___redArg___closed__0));
lean_inc(v_name_1739_);
v___x_1741_ = l_Lean_Name_str___override(v_name_1739_, v___x_1740_);
v___x_1742_ = l_Lean_Environment_contains(v___x_1698_, v___x_1741_, v___x_1716_);
if (v___x_1742_ == 0)
{
lean_object* v___x_1743_; lean_object* v___x_1745_; 
lean_dec_ref(v_val_1724_);
lean_del_object(v___x_1722_);
lean_dec_ref_known(v_x_1700_, 2);
lean_dec_ref(v_x_1701_);
lean_dec_ref(v_a_1699_);
v___x_1743_ = lean_box(0);
if (v_isShared_1727_ == 0)
{
lean_ctor_set_tag(v___x_1726_, 0);
lean_ctor_set(v___x_1726_, 0, v___x_1743_);
v___x_1745_ = v___x_1726_;
goto v_reusejp_1744_;
}
else
{
lean_object* v_reuseFailAlloc_1746_; 
v_reuseFailAlloc_1746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1746_, 0, v___x_1743_);
v___x_1745_ = v_reuseFailAlloc_1746_;
goto v_reusejp_1744_;
}
v_reusejp_1744_:
{
return v___x_1745_;
}
}
else
{
lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1752_; 
v___x_1747_ = l_List_lengthTR___redArg(v_ctors_1731_);
v___x_1748_ = lean_nat_sub(v___x_1732_, v_numIndices_1730_);
v___x_1749_ = l_Array_extract___redArg(v_x_1701_, v___x_1748_, v___x_1732_);
v___x_1750_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1750_, 0, v_val_1724_);
lean_ctor_set(v___x_1750_, 1, v___x_1747_);
lean_ctor_set(v___x_1750_, 2, v_a_1699_);
lean_ctor_set(v___x_1750_, 3, v_x_1700_);
lean_ctor_set(v___x_1750_, 4, v_x_1701_);
lean_ctor_set(v___x_1750_, 5, v___x_1749_);
if (v_isShared_1723_ == 0)
{
lean_ctor_set(v___x_1722_, 0, v___x_1750_);
v___x_1752_ = v___x_1722_;
goto v_reusejp_1751_;
}
else
{
lean_object* v_reuseFailAlloc_1756_; 
v_reuseFailAlloc_1756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1756_, 0, v___x_1750_);
v___x_1752_ = v_reuseFailAlloc_1756_;
goto v_reusejp_1751_;
}
v_reusejp_1751_:
{
lean_object* v___x_1754_; 
if (v_isShared_1727_ == 0)
{
lean_ctor_set_tag(v___x_1726_, 0);
lean_ctor_set(v___x_1726_, 0, v___x_1752_);
v___x_1754_ = v___x_1726_;
goto v_reusejp_1753_;
}
else
{
lean_object* v_reuseFailAlloc_1755_; 
v_reuseFailAlloc_1755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1755_, 0, v___x_1752_);
v___x_1754_ = v_reuseFailAlloc_1755_;
goto v_reusejp_1753_;
}
v_reusejp_1753_:
{
return v___x_1754_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_1722_);
lean_dec(v_val_1720_);
lean_dec_ref_known(v_x_1700_, 2);
lean_dec_ref(v_x_1701_);
lean_dec_ref(v_a_1699_);
lean_dec_ref(v___x_1698_);
goto v___jp_1705_;
}
}
}
}
else
{
lean_dec_ref(v_x_1701_);
lean_dec_ref(v_x_1700_);
lean_dec_ref(v_a_1699_);
lean_dec_ref(v___x_1698_);
goto v___jp_1705_;
}
}
v___jp_1705_:
{
lean_object* v___x_1706_; lean_object* v___x_1707_; 
v___x_1706_ = lean_box(0);
v___x_1707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1707_, 0, v___x_1706_);
return v___x_1707_;
}
}
}
LEAN_EXPORT void l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1698_ = stack[0].m_obj;
lean_object* v_a_1699_ = stack[1].m_obj;
lean_object* v_x_1700_ = stack[2].m_obj;
lean_object* v_x_1701_ = stack[3].m_obj;
lean_object* v_x_1702_ = stack[4].m_obj;
lean_object* v___y_1703_ = stack[5].m_obj;
lean_object* v_res_1759_;
v_res_1759_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0___redArg(v___x_1698_, v_a_1699_, v_x_1700_, v_x_1701_, v_x_1702_, v___y_1703_);
stack->m_obj
 = v_res_1759_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0___redArg___boxed(lean_object* v___x_1760_, lean_object* v_a_1761_, lean_object* v_x_1762_, lean_object* v_x_1763_, lean_object* v_x_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_){
_start:
{
lean_object* v_res_1767_; 
v_res_1767_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0___redArg(v___x_1760_, v_a_1761_, v_x_1762_, v_x_1763_, v_x_1764_, v___y_1765_);
lean_dec(v___y_1765_);
return v_res_1767_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f(lean_object* v_majorFVarId_1768_, lean_object* v_a_1769_, lean_object* v_a_1770_, lean_object* v_a_1771_, lean_object* v_a_1772_){
_start:
{
lean_object* v___x_1774_; lean_object* v_env_1778_; lean_object* v___x_1779_; uint8_t v___x_1780_; uint8_t v___x_1781_; 
v___x_1774_ = lean_st_ref_get(v_a_1772_);
v_env_1778_ = lean_ctor_get(v___x_1774_, 0);
lean_inc_ref_n(v_env_1778_, 2);
lean_dec(v___x_1774_);
v___x_1779_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__5));
v___x_1780_ = 1;
v___x_1781_ = l_Lean_Environment_contains(v_env_1778_, v___x_1779_, v___x_1780_);
if (v___x_1781_ == 0)
{
lean_dec_ref(v_env_1778_);
lean_dec(v_majorFVarId_1768_);
goto v___jp_1775_;
}
else
{
lean_object* v___x_1782_; uint8_t v___x_1783_; 
v___x_1782_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__1));
lean_inc_ref(v_env_1778_);
v___x_1783_ = l_Lean_Environment_contains(v_env_1778_, v___x_1782_, v___x_1781_);
if (v___x_1783_ == 0)
{
lean_dec_ref(v_env_1778_);
lean_dec(v_majorFVarId_1768_);
goto v___jp_1775_;
}
else
{
lean_object* v___x_1784_; 
v___x_1784_ = l_Lean_FVarId_getDecl___redArg(v_majorFVarId_1768_, v_a_1769_, v_a_1771_, v_a_1772_);
if (lean_obj_tag(v___x_1784_) == 0)
{
lean_object* v_a_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; 
v_a_1785_ = lean_ctor_get(v___x_1784_, 0);
lean_inc(v_a_1785_);
lean_dec_ref_known(v___x_1784_, 1);
v___x_1786_ = l_Lean_LocalDecl_type(v_a_1785_);
lean_inc(v_a_1772_);
lean_inc_ref(v_a_1771_);
lean_inc(v_a_1770_);
lean_inc_ref(v_a_1769_);
v___x_1787_ = lean_whnf(v___x_1786_, v_a_1769_, v_a_1770_, v_a_1771_, v_a_1772_);
if (lean_obj_tag(v___x_1787_) == 0)
{
lean_object* v_a_1788_; lean_object* v_dummy_1789_; lean_object* v_nargs_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; 
v_a_1788_ = lean_ctor_get(v___x_1787_, 0);
lean_inc(v_a_1788_);
lean_dec_ref_known(v___x_1787_, 1);
v_dummy_1789_ = lean_obj_once(&l_Lean_Meta_getInductiveUniverseAndParams___closed__0, &l_Lean_Meta_getInductiveUniverseAndParams___closed__0_once, _init_l_Lean_Meta_getInductiveUniverseAndParams___closed__0);
v_nargs_1790_ = l_Lean_Expr_getAppNumArgs(v_a_1788_);
lean_inc(v_nargs_1790_);
v___x_1791_ = lean_mk_array(v_nargs_1790_, v_dummy_1789_);
v___x_1792_ = lean_unsigned_to_nat(1u);
v___x_1793_ = lean_nat_sub(v_nargs_1790_, v___x_1792_);
lean_dec(v_nargs_1790_);
v___x_1794_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0___redArg(v_env_1778_, v_a_1785_, v_a_1788_, v___x_1791_, v___x_1793_, v_a_1772_);
return v___x_1794_;
}
else
{
lean_object* v_a_1795_; lean_object* v___x_1797_; uint8_t v_isShared_1798_; uint8_t v_isSharedCheck_1802_; 
lean_dec(v_a_1785_);
lean_dec_ref(v_env_1778_);
v_a_1795_ = lean_ctor_get(v___x_1787_, 0);
v_isSharedCheck_1802_ = !lean_is_exclusive(v___x_1787_);
if (v_isSharedCheck_1802_ == 0)
{
v___x_1797_ = v___x_1787_;
v_isShared_1798_ = v_isSharedCheck_1802_;
goto v_resetjp_1796_;
}
else
{
lean_inc(v_a_1795_);
lean_dec(v___x_1787_);
v___x_1797_ = lean_box(0);
v_isShared_1798_ = v_isSharedCheck_1802_;
goto v_resetjp_1796_;
}
v_resetjp_1796_:
{
lean_object* v___x_1800_; 
if (v_isShared_1798_ == 0)
{
v___x_1800_ = v___x_1797_;
goto v_reusejp_1799_;
}
else
{
lean_object* v_reuseFailAlloc_1801_; 
v_reuseFailAlloc_1801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1801_, 0, v_a_1795_);
v___x_1800_ = v_reuseFailAlloc_1801_;
goto v_reusejp_1799_;
}
v_reusejp_1799_:
{
return v___x_1800_;
}
}
}
}
else
{
lean_object* v_a_1803_; lean_object* v___x_1805_; uint8_t v_isShared_1806_; uint8_t v_isSharedCheck_1810_; 
lean_dec_ref(v_env_1778_);
v_a_1803_ = lean_ctor_get(v___x_1784_, 0);
v_isSharedCheck_1810_ = !lean_is_exclusive(v___x_1784_);
if (v_isSharedCheck_1810_ == 0)
{
v___x_1805_ = v___x_1784_;
v_isShared_1806_ = v_isSharedCheck_1810_;
goto v_resetjp_1804_;
}
else
{
lean_inc(v_a_1803_);
lean_dec(v___x_1784_);
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
}
v___jp_1775_:
{
lean_object* v___x_1776_; lean_object* v___x_1777_; 
v___x_1776_ = lean_box(0);
v___x_1777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1777_, 0, v___x_1776_);
return v___x_1777_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_majorFVarId_1768_ = stack[0].m_obj;
lean_object* v_a_1769_ = stack[1].m_obj;
lean_object* v_a_1770_ = stack[2].m_obj;
lean_object* v_a_1771_ = stack[3].m_obj;
lean_object* v_a_1772_ = stack[4].m_obj;
lean_object* v_res_1811_;
v_res_1811_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f(v_majorFVarId_1768_, v_a_1769_, v_a_1770_, v_a_1771_, v_a_1772_);
stack->m_obj
 = v_res_1811_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f___boxed(lean_object* v_majorFVarId_1812_, lean_object* v_a_1813_, lean_object* v_a_1814_, lean_object* v_a_1815_, lean_object* v_a_1816_, lean_object* v_a_1817_){
_start:
{
lean_object* v_res_1818_; 
v_res_1818_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f(v_majorFVarId_1812_, v_a_1813_, v_a_1814_, v_a_1815_, v_a_1816_);
lean_dec(v_a_1816_);
lean_dec_ref(v_a_1815_);
lean_dec(v_a_1814_);
lean_dec_ref(v_a_1813_);
return v_res_1818_;
}
}
lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0(lean_object* v___x_1819_, lean_object* v_a_1820_, lean_object* v_x_1821_, lean_object* v_x_1822_, lean_object* v_x_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_){
_start:
{
lean_object* v___x_1829_; 
v___x_1829_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0___redArg(v___x_1819_, v_a_1820_, v_x_1821_, v_x_1822_, v_x_1823_, v___y_1827_);
return v___x_1829_;
}
}
LEAN_EXPORT void l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1819_ = stack[0].m_obj;
lean_object* v_a_1820_ = stack[1].m_obj;
lean_object* v_x_1821_ = stack[2].m_obj;
lean_object* v_x_1822_ = stack[3].m_obj;
lean_object* v_x_1823_ = stack[4].m_obj;
lean_object* v___y_1824_ = stack[5].m_obj;
lean_object* v___y_1825_ = stack[6].m_obj;
lean_object* v___y_1826_ = stack[7].m_obj;
lean_object* v___y_1827_ = stack[8].m_obj;
lean_object* v_res_1830_;
v_res_1830_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0(v___x_1819_, v_a_1820_, v_x_1821_, v_x_1822_, v_x_1823_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_);
stack->m_obj
 = v_res_1830_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0___boxed(lean_object* v___x_1831_, lean_object* v_a_1832_, lean_object* v_x_1833_, lean_object* v_x_1834_, lean_object* v_x_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_){
_start:
{
lean_object* v_res_1841_; 
v_res_1841_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0(v___x_1831_, v_a_1832_, v_x_1833_, v_x_1834_, v_x_1835_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_);
lean_dec(v___y_1839_);
lean_dec_ref(v___y_1838_);
lean_dec(v___y_1837_);
lean_dec_ref(v___y_1836_);
return v_res_1841_;
}
}
uint8_t l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0___redArg(lean_object* v___x_1842_, lean_object* v_i_1843_, lean_object* v_n_1844_, lean_object* v_i_1845_){
_start:
{
lean_object* v_zero_1846_; uint8_t v_isZero_1847_; 
v_zero_1846_ = lean_unsigned_to_nat(0u);
v_isZero_1847_ = lean_nat_dec_eq(v_i_1845_, v_zero_1846_);
if (v_isZero_1847_ == 1)
{
uint8_t v___x_1848_; 
lean_dec(v_i_1845_);
v___x_1848_ = 0;
return v___x_1848_;
}
else
{
lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; uint8_t v___x_1852_; 
v___x_1849_ = lean_nat_sub(v_n_1844_, v_i_1845_);
v___x_1850_ = lean_array_fget_borrowed(v___x_1842_, v_i_1843_);
v___x_1851_ = lean_array_fget_borrowed(v___x_1842_, v___x_1849_);
lean_dec(v___x_1849_);
v___x_1852_ = lean_expr_eqv(v___x_1850_, v___x_1851_);
if (v___x_1852_ == 0)
{
lean_object* v_one_1853_; lean_object* v_n_1854_; 
v_one_1853_ = lean_unsigned_to_nat(1u);
v_n_1854_ = lean_nat_sub(v_i_1845_, v_one_1853_);
lean_dec(v_i_1845_);
v_i_1845_ = v_n_1854_;
goto _start;
}
else
{
lean_dec(v_i_1845_);
return v___x_1852_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1842_ = stack[0].m_obj;
lean_object* v_i_1843_ = stack[1].m_obj;
lean_object* v_n_1844_ = stack[2].m_obj;
lean_object* v_i_1845_ = stack[3].m_obj;
uint8_t v_res_1856_;
v_res_1856_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0___redArg(v___x_1842_, v_i_1843_, v_n_1844_, v_i_1845_);
stack->m_num = v_res_1856_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0___redArg___boxed(lean_object* v___x_1857_, lean_object* v_i_1858_, lean_object* v_n_1859_, lean_object* v_i_1860_){
_start:
{
uint8_t v_res_1861_; lean_object* v_r_1862_; 
v_res_1861_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0___redArg(v___x_1857_, v_i_1858_, v_n_1859_, v_i_1860_);
lean_dec(v_n_1859_);
lean_dec(v_i_1858_);
lean_dec_ref(v___x_1857_);
v_r_1862_ = lean_box(v_res_1861_);
return v_r_1862_;
}
}
uint8_t l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1___redArg(lean_object* v___x_1863_, lean_object* v_n_1864_, lean_object* v_i_1865_){
_start:
{
lean_object* v_zero_1866_; uint8_t v_isZero_1867_; 
v_zero_1866_ = lean_unsigned_to_nat(0u);
v_isZero_1867_ = lean_nat_dec_eq(v_i_1865_, v_zero_1866_);
if (v_isZero_1867_ == 1)
{
uint8_t v___x_1868_; 
lean_dec(v_i_1865_);
v___x_1868_ = 0;
return v___x_1868_;
}
else
{
lean_object* v___x_1869_; uint8_t v___x_1870_; 
v___x_1869_ = lean_nat_sub(v_n_1864_, v_i_1865_);
lean_inc(v___x_1869_);
v___x_1870_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0___redArg(v___x_1863_, v___x_1869_, v___x_1869_, v___x_1869_);
lean_dec(v___x_1869_);
if (v___x_1870_ == 0)
{
lean_object* v_one_1871_; lean_object* v_n_1872_; 
v_one_1871_ = lean_unsigned_to_nat(1u);
v_n_1872_ = lean_nat_sub(v_i_1865_, v_one_1871_);
lean_dec(v_i_1865_);
v_i_1865_ = v_n_1872_;
goto _start;
}
else
{
lean_dec(v_i_1865_);
return v___x_1870_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1863_ = stack[0].m_obj;
lean_object* v_n_1864_ = stack[1].m_obj;
lean_object* v_i_1865_ = stack[2].m_obj;
uint8_t v_res_1874_;
v_res_1874_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1___redArg(v___x_1863_, v_n_1864_, v_i_1865_);
stack->m_num = v_res_1874_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1___redArg___boxed(lean_object* v___x_1875_, lean_object* v_n_1876_, lean_object* v_i_1877_){
_start:
{
uint8_t v_res_1878_; lean_object* v_r_1879_; 
v_res_1878_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1___redArg(v___x_1875_, v_n_1876_, v_i_1877_);
lean_dec(v_n_1876_);
lean_dec_ref(v___x_1875_);
v_r_1879_ = lean_box(v_res_1878_);
return v_r_1879_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5(lean_object* v___x_1880_, lean_object* v_as_1881_, size_t v_i_1882_, size_t v_stop_1883_){
_start:
{
uint8_t v___x_1884_; 
v___x_1884_ = lean_usize_dec_eq(v_i_1882_, v_stop_1883_);
if (v___x_1884_ == 0)
{
uint8_t v___x_1885_; lean_object* v___x_1886_; uint8_t v___x_1887_; 
v___x_1885_ = 1;
v___x_1886_ = lean_array_uget_borrowed(v_as_1881_, v_i_1882_);
v___x_1887_ = l_Lean_Expr_isFVar(v___x_1886_);
if (v___x_1887_ == 0)
{
return v___x_1885_;
}
else
{
lean_object* v___x_1888_; uint8_t v___x_1889_; 
v___x_1888_ = lean_unsigned_to_nat(0u);
v___x_1889_ = lean_nat_dec_eq(v___x_1880_, v___x_1888_);
if (v___x_1889_ == 0)
{
size_t v___x_1890_; size_t v___x_1891_; 
v___x_1890_ = ((size_t)1ULL);
v___x_1891_ = lean_usize_add(v_i_1882_, v___x_1890_);
v_i_1882_ = v___x_1891_;
goto _start;
}
else
{
return v___x_1885_;
}
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1880_ = stack[0].m_obj;
lean_object* v_as_1881_ = stack[1].m_obj;
size_t v_i_1882_ = stack[2].m_num;
size_t v_stop_1883_ = stack[3].m_num;
uint8_t v_res_1894_;
v_res_1894_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5(v___x_1880_, v_as_1881_, v_i_1882_, v_stop_1883_);
stack->m_num = v_res_1894_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5___boxed(lean_object* v___x_1895_, lean_object* v_as_1896_, lean_object* v_i_1897_, lean_object* v_stop_1898_){
_start:
{
size_t v_i_boxed_1899_; size_t v_stop_boxed_1900_; uint8_t v_res_1901_; lean_object* v_r_1902_; 
v_i_boxed_1899_ = lean_unbox_usize(v_i_1897_);
lean_dec(v_i_1897_);
v_stop_boxed_1900_ = lean_unbox_usize(v_stop_1898_);
lean_dec(v_stop_1898_);
v_res_1901_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5(v___x_1895_, v_as_1896_, v_i_boxed_1899_, v_stop_boxed_1900_);
lean_dec_ref(v_as_1896_);
lean_dec(v___x_1895_);
v_r_1902_ = lean_box(v_res_1901_);
return v_r_1902_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__2(lean_object* v_fvarId_1903_, uint8_t v___x_1904_, lean_object* v_as_1905_, size_t v_i_1906_, size_t v_stop_1907_){
_start:
{
uint8_t v___x_1908_; 
v___x_1908_ = lean_usize_dec_eq(v_i_1906_, v_stop_1907_);
if (v___x_1908_ == 0)
{
uint8_t v___x_1909_; uint8_t v___y_1911_; lean_object* v___x_1915_; lean_object* v___x_1916_; uint8_t v___x_1917_; 
v___x_1909_ = 1;
v___x_1915_ = lean_array_uget_borrowed(v_as_1905_, v_i_1906_);
v___x_1916_ = l_Lean_Expr_fvarId_x21(v___x_1915_);
v___x_1917_ = l_Lean_instBEqFVarId_beq(v___x_1916_, v_fvarId_1903_);
lean_dec(v___x_1916_);
if (v___x_1917_ == 0)
{
v___y_1911_ = v___x_1904_;
goto v___jp_1910_;
}
else
{
if (v___x_1904_ == 0)
{
v___y_1911_ = v___x_1917_;
goto v___jp_1910_;
}
else
{
return v___x_1909_;
}
}
v___jp_1910_:
{
if (v___y_1911_ == 0)
{
size_t v___x_1912_; size_t v___x_1913_; 
v___x_1912_ = ((size_t)1ULL);
v___x_1913_ = lean_usize_add(v_i_1906_, v___x_1912_);
v_i_1906_ = v___x_1913_;
goto _start;
}
else
{
return v___x_1909_;
}
}
}
else
{
uint8_t v___x_1918_; 
v___x_1918_ = 0;
return v___x_1918_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_1903_ = stack[0].m_obj;
uint8_t v___x_1904_ = stack[1].m_num;
lean_object* v_as_1905_ = stack[2].m_obj;
size_t v_i_1906_ = stack[3].m_num;
size_t v_stop_1907_ = stack[4].m_num;
uint8_t v_res_1919_;
v_res_1919_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__2(v_fvarId_1903_, v___x_1904_, v_as_1905_, v_i_1906_, v_stop_1907_);
stack->m_num = v_res_1919_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__2___boxed(lean_object* v_fvarId_1920_, lean_object* v___x_1921_, lean_object* v_as_1922_, lean_object* v_i_1923_, lean_object* v_stop_1924_){
_start:
{
uint8_t v___x_7603__boxed_1925_; size_t v_i_boxed_1926_; size_t v_stop_boxed_1927_; uint8_t v_res_1928_; lean_object* v_r_1929_; 
v___x_7603__boxed_1925_ = lean_unbox(v___x_1921_);
v_i_boxed_1926_ = lean_unbox_usize(v_i_1923_);
lean_dec(v_i_1923_);
v_stop_boxed_1927_ = lean_unbox_usize(v_stop_1924_);
lean_dec(v_stop_1924_);
v_res_1928_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__2(v_fvarId_1920_, v___x_7603__boxed_1925_, v_as_1922_, v_i_boxed_1926_, v_stop_boxed_1927_);
lean_dec_ref(v_as_1922_);
lean_dec(v_fvarId_1920_);
v_r_1929_ = lean_box(v_res_1928_);
return v_r_1929_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___lam__1(lean_object* v___x_1930_, lean_object* v___x_1931_, uint8_t v___x_1932_, lean_object* v___x_1933_, lean_object* v_fvarId_1934_){
_start:
{
uint8_t v___x_1935_; lean_object* v___y_1937_; 
v___x_1935_ = lean_nat_dec_lt(v___x_1930_, v___x_1931_);
if (v___x_1935_ == 0)
{
uint8_t v___x_1942_; 
lean_dec(v___x_1931_);
v___x_1942_ = 1;
return v___x_1942_;
}
else
{
lean_object* v___x_1943_; uint8_t v___x_1944_; 
v___x_1943_ = lean_array_get_size(v___x_1933_);
v___x_1944_ = lean_nat_dec_le(v___x_1931_, v___x_1943_);
if (v___x_1944_ == 0)
{
lean_dec(v___x_1931_);
v___y_1937_ = v___x_1943_;
goto v___jp_1936_;
}
else
{
v___y_1937_ = v___x_1931_;
goto v___jp_1936_;
}
}
v___jp_1936_:
{
uint8_t v___x_1938_; 
v___x_1938_ = lean_nat_dec_lt(v___x_1930_, v___y_1937_);
if (v___x_1938_ == 0)
{
lean_dec(v___y_1937_);
return v___x_1935_;
}
else
{
size_t v___x_1939_; size_t v___x_1940_; uint8_t v___x_1941_; 
v___x_1939_ = ((size_t)0ULL);
v___x_1940_ = lean_usize_of_nat(v___y_1937_);
lean_dec(v___y_1937_);
v___x_1941_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__2(v_fvarId_1934_, v___x_1932_, v___x_1933_, v___x_1939_, v___x_1940_);
if (v___x_1941_ == 0)
{
return v___x_1938_;
}
else
{
return v___x_1932_;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1930_ = stack[0].m_obj;
lean_object* v___x_1931_ = stack[1].m_obj;
uint8_t v___x_1932_ = stack[2].m_num;
lean_object* v___x_1933_ = stack[3].m_obj;
lean_object* v_fvarId_1934_ = stack[4].m_obj;
uint8_t v_res_1945_;
v_res_1945_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___lam__1(v___x_1930_, v___x_1931_, v___x_1932_, v___x_1933_, v_fvarId_1934_);
stack->m_num = v_res_1945_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___lam__1___boxed(lean_object* v___x_1946_, lean_object* v___x_1947_, lean_object* v___x_1948_, lean_object* v___x_1949_, lean_object* v_fvarId_1950_){
_start:
{
uint8_t v___x_7643__boxed_1951_; uint8_t v_res_1952_; lean_object* v_r_1953_; 
v___x_7643__boxed_1951_ = lean_unbox(v___x_1948_);
v_res_1952_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___lam__1(v___x_1946_, v___x_1947_, v___x_7643__boxed_1951_, v___x_1949_, v_fvarId_1950_);
lean_dec(v_fvarId_1950_);
lean_dec_ref(v___x_1949_);
lean_dec(v___x_1946_);
v_r_1953_ = lean_box(v_res_1952_);
return v_r_1953_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__3(lean_object* v___x_1954_, lean_object* v_as_1955_, size_t v_i_1956_, size_t v_stop_1957_){
_start:
{
uint8_t v___x_1958_; 
v___x_1958_ = lean_usize_dec_eq(v_i_1956_, v_stop_1957_);
if (v___x_1958_ == 0)
{
lean_object* v___x_1959_; lean_object* v___x_1960_; uint8_t v___x_1961_; 
v___x_1959_ = lean_array_uget_borrowed(v_as_1955_, v_i_1956_);
v___x_1960_ = l_Lean_Expr_fvarId_x21(v___x_1959_);
v___x_1961_ = l_Lean_instBEqFVarId_beq(v___x_1954_, v___x_1960_);
lean_dec(v___x_1960_);
if (v___x_1961_ == 0)
{
size_t v___x_1962_; size_t v___x_1963_; 
v___x_1962_ = ((size_t)1ULL);
v___x_1963_ = lean_usize_add(v_i_1956_, v___x_1962_);
v_i_1956_ = v___x_1963_;
goto _start;
}
else
{
return v___x_1961_;
}
}
else
{
uint8_t v___x_1965_; 
v___x_1965_ = 0;
return v___x_1965_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1954_ = stack[0].m_obj;
lean_object* v_as_1955_ = stack[1].m_obj;
size_t v_i_1956_ = stack[2].m_num;
size_t v_stop_1957_ = stack[3].m_num;
uint8_t v_res_1966_;
v_res_1966_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__3(v___x_1954_, v_as_1955_, v_i_1956_, v_stop_1957_);
stack->m_num = v_res_1966_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__3___boxed(lean_object* v___x_1967_, lean_object* v_as_1968_, lean_object* v_i_1969_, lean_object* v_stop_1970_){
_start:
{
size_t v_i_boxed_1971_; size_t v_stop_boxed_1972_; uint8_t v_res_1973_; lean_object* v_r_1974_; 
v_i_boxed_1971_ = lean_unbox_usize(v_i_1969_);
lean_dec(v_i_1969_);
v_stop_boxed_1972_ = lean_unbox_usize(v_stop_1970_);
lean_dec(v_stop_1970_);
v_res_1973_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__3(v___x_1967_, v_as_1968_, v_i_boxed_1971_, v_stop_boxed_1972_);
lean_dec_ref(v_as_1968_);
lean_dec(v___x_1967_);
v_r_1974_ = lean_box(v_res_1973_);
return v_r_1974_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___lam__0(uint8_t v___x_1975_, lean_object* v_x_1976_){
_start:
{
return v___x_1975_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_1975_ = stack[0].m_num;
lean_object* v_x_1976_ = stack[1].m_obj;
uint8_t v_res_1977_;
v_res_1977_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___lam__0(v___x_1975_, v_x_1976_);
stack->m_num = v_res_1977_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___lam__0___boxed(lean_object* v___x_1978_, lean_object* v_x_1979_){
_start:
{
uint8_t v___x_7720__boxed_1980_; uint8_t v_res_1981_; lean_object* v_r_1982_; 
v___x_7720__boxed_1980_ = lean_unbox(v___x_1978_);
v_res_1981_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___lam__0(v___x_7720__boxed_1980_, v_x_1979_);
lean_dec(v_x_1979_);
v_r_1982_ = lean_box(v_res_1981_);
return v_r_1982_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; 
v___x_1983_ = lean_box(0);
v___x_1984_ = lean_unsigned_to_nat(16u);
v___x_1985_ = lean_mk_array(v___x_1984_, v___x_1983_);
return v___x_1985_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; 
v___x_1986_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__0);
v___x_1987_ = lean_unsigned_to_nat(0u);
v___x_1988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1988_, 0, v___x_1987_);
lean_ctor_set(v___x_1988_, 1, v___x_1986_);
return v___x_1988_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg(uint8_t v___x_1989_, lean_object* v___x_1990_, lean_object* v___x_1991_, lean_object* v_ctx_1992_, lean_object* v_as_1993_, size_t v_i_1994_, size_t v_stop_1995_, lean_object* v___y_1996_){
_start:
{
uint8_t v___x_1998_; 
v___x_1998_ = lean_usize_dec_eq(v_i_1994_, v_stop_1995_);
if (v___x_1998_ == 0)
{
uint8_t v___x_1999_; uint8_t v_a_2001_; uint8_t v_a_2008_; uint8_t v_fst_2012_; lean_object* v_mctx_2013_; lean_object* v___y_2029_; uint8_t v_fst_2035_; lean_object* v_snd_2036_; lean_object* v___y_2053_; uint8_t v_fst_2058_; lean_object* v_mctx_2059_; lean_object* v___y_2075_; lean_object* v___x_2080_; 
v___x_1999_ = 1;
v___x_2080_ = lean_array_uget_borrowed(v_as_1993_, v_i_1994_);
if (lean_obj_tag(v___x_2080_) == 0)
{
v_a_2001_ = v___x_1989_;
goto v___jp_2000_;
}
else
{
lean_object* v_val_2081_; lean_object* v_majorDecl_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; uint8_t v___x_2085_; 
v_val_2081_ = lean_ctor_get(v___x_2080_, 0);
v_majorDecl_2082_ = lean_ctor_get(v_ctx_1992_, 2);
v___x_2083_ = l_Lean_LocalDecl_fvarId(v_val_2081_);
v___x_2084_ = l_Lean_LocalDecl_fvarId(v_majorDecl_2082_);
v___x_2085_ = l_Lean_instBEqFVarId_beq(v___x_2083_, v___x_2084_);
lean_dec(v___x_2084_);
if (v___x_2085_ == 0)
{
lean_object* v___x_2086_; lean_object* v___f_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___f_2090_; lean_object* v___y_2092_; uint8_t v_fst_2093_; lean_object* v_snd_2094_; lean_object* v___y_2100_; lean_object* v___y_2101_; lean_object* v___y_2136_; uint8_t v___x_2141_; 
v___x_2086_ = lean_box(v___x_1989_);
v___f_2087_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2087_, 0, v___x_2086_);
v___x_2088_ = lean_unsigned_to_nat(0u);
v___x_2089_ = lean_box(v___x_1989_);
lean_inc_ref(v___x_1990_);
lean_inc(v___x_1991_);
v___f_2090_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_2090_, 0, v___x_2088_);
lean_closure_set(v___f_2090_, 1, v___x_1991_);
lean_closure_set(v___f_2090_, 2, v___x_2089_);
lean_closure_set(v___f_2090_, 3, v___x_1990_);
v___x_2141_ = lean_nat_dec_lt(v___x_2088_, v___x_1991_);
if (v___x_2141_ == 0)
{
lean_dec(v___x_2083_);
goto v___jp_2105_;
}
else
{
lean_object* v___x_2142_; uint8_t v___x_2143_; 
v___x_2142_ = lean_array_get_size(v___x_1990_);
v___x_2143_ = lean_nat_dec_le(v___x_1991_, v___x_2142_);
if (v___x_2143_ == 0)
{
v___y_2136_ = v___x_2142_;
goto v___jp_2135_;
}
else
{
lean_inc(v___x_1991_);
v___y_2136_ = v___x_1991_;
goto v___jp_2135_;
}
}
v___jp_2091_:
{
if (v_fst_2093_ == 0)
{
uint8_t v___x_2095_; 
v___x_2095_ = l_Lean_Expr_hasFVar(v___y_2092_);
if (v___x_2095_ == 0)
{
uint8_t v___x_2096_; 
v___x_2096_ = l_Lean_Expr_hasMVar(v___y_2092_);
if (v___x_2096_ == 0)
{
lean_dec_ref(v___y_2092_);
lean_dec_ref(v___f_2090_);
lean_dec_ref(v___f_2087_);
v_fst_2035_ = v___x_2096_;
v_snd_2036_ = v_snd_2094_;
goto v___jp_2034_;
}
else
{
lean_object* v___x_2097_; 
v___x_2097_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_2090_, v___f_2087_, v___y_2092_, v_snd_2094_);
v___y_2053_ = v___x_2097_;
goto v___jp_2052_;
}
}
else
{
lean_object* v___x_2098_; 
v___x_2098_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_2090_, v___f_2087_, v___y_2092_, v_snd_2094_);
v___y_2053_ = v___x_2098_;
goto v___jp_2052_;
}
}
else
{
lean_dec_ref(v___y_2092_);
lean_dec_ref(v___f_2090_);
lean_dec_ref(v___f_2087_);
v_fst_2035_ = v_fst_2093_;
v_snd_2036_ = v_snd_2094_;
goto v___jp_2034_;
}
}
v___jp_2099_:
{
lean_object* v_fst_2102_; lean_object* v_snd_2103_; uint8_t v___x_2104_; 
v_fst_2102_ = lean_ctor_get(v___y_2101_, 0);
lean_inc(v_fst_2102_);
v_snd_2103_ = lean_ctor_get(v___y_2101_, 1);
lean_inc(v_snd_2103_);
lean_dec_ref(v___y_2101_);
v___x_2104_ = lean_unbox(v_fst_2102_);
lean_dec(v_fst_2102_);
v___y_2092_ = v___y_2100_;
v_fst_2093_ = v___x_2104_;
v_snd_2094_ = v_snd_2103_;
goto v___jp_2091_;
}
v___jp_2105_:
{
if (lean_obj_tag(v_val_2081_) == 0)
{
lean_object* v_type_2106_; lean_object* v___x_2107_; lean_object* v_mctx_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; uint8_t v___x_2111_; 
v_type_2106_ = lean_ctor_get(v_val_2081_, 3);
v___x_2107_ = lean_st_ref_get(v___y_1996_);
v_mctx_2108_ = lean_ctor_get(v___x_2107_, 0);
lean_inc_ref_n(v_mctx_2108_, 2);
lean_dec(v___x_2107_);
v___x_2109_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1);
v___x_2110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2110_, 0, v___x_2109_);
lean_ctor_set(v___x_2110_, 1, v_mctx_2108_);
v___x_2111_ = l_Lean_Expr_hasFVar(v_type_2106_);
if (v___x_2111_ == 0)
{
uint8_t v___x_2112_; 
v___x_2112_ = l_Lean_Expr_hasMVar(v_type_2106_);
if (v___x_2112_ == 0)
{
lean_dec_ref_known(v___x_2110_, 2);
lean_dec_ref(v___f_2090_);
lean_dec_ref(v___f_2087_);
v_fst_2058_ = v___x_2112_;
v_mctx_2059_ = v_mctx_2108_;
goto v___jp_2057_;
}
else
{
lean_object* v___x_2113_; 
lean_dec_ref(v_mctx_2108_);
lean_inc_ref(v_type_2106_);
v___x_2113_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_2090_, v___f_2087_, v_type_2106_, v___x_2110_);
v___y_2075_ = v___x_2113_;
goto v___jp_2074_;
}
}
else
{
lean_object* v___x_2114_; 
lean_dec_ref(v_mctx_2108_);
lean_inc_ref(v_type_2106_);
v___x_2114_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_2090_, v___f_2087_, v_type_2106_, v___x_2110_);
v___y_2075_ = v___x_2114_;
goto v___jp_2074_;
}
}
else
{
uint8_t v_nondep_2115_; 
v_nondep_2115_ = lean_ctor_get_uint8(v_val_2081_, sizeof(void*)*5);
if (v_nondep_2115_ == 0)
{
lean_object* v_type_2116_; lean_object* v_value_2117_; lean_object* v___x_2118_; lean_object* v_mctx_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; uint8_t v___x_2122_; 
v_type_2116_ = lean_ctor_get(v_val_2081_, 3);
v_value_2117_ = lean_ctor_get(v_val_2081_, 4);
v___x_2118_ = lean_st_ref_get(v___y_1996_);
v_mctx_2119_ = lean_ctor_get(v___x_2118_, 0);
lean_inc_ref(v_mctx_2119_);
lean_dec(v___x_2118_);
v___x_2120_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1);
v___x_2121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2121_, 0, v___x_2120_);
lean_ctor_set(v___x_2121_, 1, v_mctx_2119_);
v___x_2122_ = l_Lean_Expr_hasFVar(v_type_2116_);
if (v___x_2122_ == 0)
{
uint8_t v___x_2123_; 
v___x_2123_ = l_Lean_Expr_hasMVar(v_type_2116_);
if (v___x_2123_ == 0)
{
lean_inc_ref(v_value_2117_);
v___y_2092_ = v_value_2117_;
v_fst_2093_ = v___x_2123_;
v_snd_2094_ = v___x_2121_;
goto v___jp_2091_;
}
else
{
lean_object* v___x_2124_; 
lean_inc_ref(v_type_2116_);
lean_inc_ref(v___f_2087_);
lean_inc_ref(v___f_2090_);
v___x_2124_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_2090_, v___f_2087_, v_type_2116_, v___x_2121_);
lean_inc_ref(v_value_2117_);
v___y_2100_ = v_value_2117_;
v___y_2101_ = v___x_2124_;
goto v___jp_2099_;
}
}
else
{
lean_object* v___x_2125_; 
lean_inc_ref(v_type_2116_);
lean_inc_ref(v___f_2087_);
lean_inc_ref(v___f_2090_);
v___x_2125_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_2090_, v___f_2087_, v_type_2116_, v___x_2121_);
lean_inc_ref(v_value_2117_);
v___y_2100_ = v_value_2117_;
v___y_2101_ = v___x_2125_;
goto v___jp_2099_;
}
}
else
{
lean_object* v_type_2126_; lean_object* v___x_2127_; lean_object* v_mctx_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; uint8_t v___x_2131_; 
v_type_2126_ = lean_ctor_get(v_val_2081_, 3);
v___x_2127_ = lean_st_ref_get(v___y_1996_);
v_mctx_2128_ = lean_ctor_get(v___x_2127_, 0);
lean_inc_ref_n(v_mctx_2128_, 2);
lean_dec(v___x_2127_);
v___x_2129_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1);
v___x_2130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2130_, 0, v___x_2129_);
lean_ctor_set(v___x_2130_, 1, v_mctx_2128_);
v___x_2131_ = l_Lean_Expr_hasFVar(v_type_2126_);
if (v___x_2131_ == 0)
{
uint8_t v___x_2132_; 
v___x_2132_ = l_Lean_Expr_hasMVar(v_type_2126_);
if (v___x_2132_ == 0)
{
lean_dec_ref_known(v___x_2130_, 2);
lean_dec_ref(v___f_2090_);
lean_dec_ref(v___f_2087_);
v_fst_2012_ = v___x_2132_;
v_mctx_2013_ = v_mctx_2128_;
goto v___jp_2011_;
}
else
{
lean_object* v___x_2133_; 
lean_dec_ref(v_mctx_2128_);
lean_inc_ref(v_type_2126_);
v___x_2133_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_2090_, v___f_2087_, v_type_2126_, v___x_2130_);
v___y_2029_ = v___x_2133_;
goto v___jp_2028_;
}
}
else
{
lean_object* v___x_2134_; 
lean_dec_ref(v_mctx_2128_);
lean_inc_ref(v_type_2126_);
v___x_2134_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_2090_, v___f_2087_, v_type_2126_, v___x_2130_);
v___y_2029_ = v___x_2134_;
goto v___jp_2028_;
}
}
}
}
v___jp_2135_:
{
uint8_t v___x_2137_; 
v___x_2137_ = lean_nat_dec_lt(v___x_2088_, v___y_2136_);
if (v___x_2137_ == 0)
{
lean_dec(v___y_2136_);
lean_dec(v___x_2083_);
goto v___jp_2105_;
}
else
{
size_t v___x_2138_; size_t v___x_2139_; uint8_t v___x_2140_; 
v___x_2138_ = ((size_t)0ULL);
v___x_2139_ = lean_usize_of_nat(v___y_2136_);
lean_dec(v___y_2136_);
v___x_2140_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__3(v___x_2083_, v___x_1990_, v___x_2138_, v___x_2139_);
lean_dec(v___x_2083_);
if (v___x_2140_ == 0)
{
goto v___jp_2105_;
}
else
{
lean_dec_ref(v___f_2090_);
lean_dec_ref(v___f_2087_);
v_a_2008_ = v___x_2140_;
goto v___jp_2007_;
}
}
}
}
else
{
lean_dec(v___x_2083_);
v_a_2008_ = v___x_2085_;
goto v___jp_2007_;
}
}
v___jp_2000_:
{
if (v_a_2001_ == 0)
{
size_t v___x_2002_; size_t v___x_2003_; 
v___x_2002_ = ((size_t)1ULL);
v___x_2003_ = lean_usize_add(v_i_1994_, v___x_2002_);
v_i_1994_ = v___x_2003_;
goto _start;
}
else
{
lean_object* v___x_2005_; lean_object* v___x_2006_; 
lean_dec(v___x_1991_);
lean_dec_ref(v___x_1990_);
v___x_2005_ = lean_box(v___x_1999_);
v___x_2006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2006_, 0, v___x_2005_);
return v___x_2006_;
}
}
v___jp_2007_:
{
if (v_a_2008_ == 0)
{
lean_object* v___x_2009_; lean_object* v___x_2010_; 
lean_dec(v___x_1991_);
lean_dec_ref(v___x_1990_);
v___x_2009_ = lean_box(v___x_1999_);
v___x_2010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2010_, 0, v___x_2009_);
return v___x_2010_;
}
else
{
v_a_2001_ = v___x_1989_;
goto v___jp_2000_;
}
}
v___jp_2011_:
{
lean_object* v___x_2014_; lean_object* v_cache_2015_; lean_object* v_zetaDeltaFVarIds_2016_; lean_object* v_postponed_2017_; lean_object* v_diag_2018_; lean_object* v___x_2020_; uint8_t v_isShared_2021_; uint8_t v_isSharedCheck_2026_; 
v___x_2014_ = lean_st_ref_take(v___y_1996_);
v_cache_2015_ = lean_ctor_get(v___x_2014_, 1);
v_zetaDeltaFVarIds_2016_ = lean_ctor_get(v___x_2014_, 2);
v_postponed_2017_ = lean_ctor_get(v___x_2014_, 3);
v_diag_2018_ = lean_ctor_get(v___x_2014_, 4);
v_isSharedCheck_2026_ = !lean_is_exclusive(v___x_2014_);
if (v_isSharedCheck_2026_ == 0)
{
lean_object* v_unused_2027_; 
v_unused_2027_ = lean_ctor_get(v___x_2014_, 0);
lean_dec(v_unused_2027_);
v___x_2020_ = v___x_2014_;
v_isShared_2021_ = v_isSharedCheck_2026_;
goto v_resetjp_2019_;
}
else
{
lean_inc(v_diag_2018_);
lean_inc(v_postponed_2017_);
lean_inc(v_zetaDeltaFVarIds_2016_);
lean_inc(v_cache_2015_);
lean_dec(v___x_2014_);
v___x_2020_ = lean_box(0);
v_isShared_2021_ = v_isSharedCheck_2026_;
goto v_resetjp_2019_;
}
v_resetjp_2019_:
{
lean_object* v___x_2023_; 
if (v_isShared_2021_ == 0)
{
lean_ctor_set(v___x_2020_, 0, v_mctx_2013_);
v___x_2023_ = v___x_2020_;
goto v_reusejp_2022_;
}
else
{
lean_object* v_reuseFailAlloc_2025_; 
v_reuseFailAlloc_2025_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2025_, 0, v_mctx_2013_);
lean_ctor_set(v_reuseFailAlloc_2025_, 1, v_cache_2015_);
lean_ctor_set(v_reuseFailAlloc_2025_, 2, v_zetaDeltaFVarIds_2016_);
lean_ctor_set(v_reuseFailAlloc_2025_, 3, v_postponed_2017_);
lean_ctor_set(v_reuseFailAlloc_2025_, 4, v_diag_2018_);
v___x_2023_ = v_reuseFailAlloc_2025_;
goto v_reusejp_2022_;
}
v_reusejp_2022_:
{
lean_object* v___x_2024_; 
v___x_2024_ = lean_st_ref_put(v___y_1996_, v___x_2023_);
v_a_2008_ = v_fst_2012_;
goto v___jp_2007_;
}
}
}
v___jp_2028_:
{
lean_object* v_snd_2030_; lean_object* v_fst_2031_; lean_object* v_mctx_2032_; uint8_t v___x_2033_; 
v_snd_2030_ = lean_ctor_get(v___y_2029_, 1);
lean_inc(v_snd_2030_);
v_fst_2031_ = lean_ctor_get(v___y_2029_, 0);
lean_inc(v_fst_2031_);
lean_dec_ref(v___y_2029_);
v_mctx_2032_ = lean_ctor_get(v_snd_2030_, 1);
lean_inc_ref(v_mctx_2032_);
lean_dec(v_snd_2030_);
v___x_2033_ = lean_unbox(v_fst_2031_);
lean_dec(v_fst_2031_);
v_fst_2012_ = v___x_2033_;
v_mctx_2013_ = v_mctx_2032_;
goto v___jp_2011_;
}
v___jp_2034_:
{
lean_object* v_mctx_2037_; lean_object* v___x_2038_; lean_object* v_cache_2039_; lean_object* v_zetaDeltaFVarIds_2040_; lean_object* v_postponed_2041_; lean_object* v_diag_2042_; lean_object* v___x_2044_; uint8_t v_isShared_2045_; uint8_t v_isSharedCheck_2050_; 
v_mctx_2037_ = lean_ctor_get(v_snd_2036_, 1);
lean_inc_ref(v_mctx_2037_);
lean_dec_ref(v_snd_2036_);
v___x_2038_ = lean_st_ref_take(v___y_1996_);
v_cache_2039_ = lean_ctor_get(v___x_2038_, 1);
v_zetaDeltaFVarIds_2040_ = lean_ctor_get(v___x_2038_, 2);
v_postponed_2041_ = lean_ctor_get(v___x_2038_, 3);
v_diag_2042_ = lean_ctor_get(v___x_2038_, 4);
v_isSharedCheck_2050_ = !lean_is_exclusive(v___x_2038_);
if (v_isSharedCheck_2050_ == 0)
{
lean_object* v_unused_2051_; 
v_unused_2051_ = lean_ctor_get(v___x_2038_, 0);
lean_dec(v_unused_2051_);
v___x_2044_ = v___x_2038_;
v_isShared_2045_ = v_isSharedCheck_2050_;
goto v_resetjp_2043_;
}
else
{
lean_inc(v_diag_2042_);
lean_inc(v_postponed_2041_);
lean_inc(v_zetaDeltaFVarIds_2040_);
lean_inc(v_cache_2039_);
lean_dec(v___x_2038_);
v___x_2044_ = lean_box(0);
v_isShared_2045_ = v_isSharedCheck_2050_;
goto v_resetjp_2043_;
}
v_resetjp_2043_:
{
lean_object* v___x_2047_; 
if (v_isShared_2045_ == 0)
{
lean_ctor_set(v___x_2044_, 0, v_mctx_2037_);
v___x_2047_ = v___x_2044_;
goto v_reusejp_2046_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v_mctx_2037_);
lean_ctor_set(v_reuseFailAlloc_2049_, 1, v_cache_2039_);
lean_ctor_set(v_reuseFailAlloc_2049_, 2, v_zetaDeltaFVarIds_2040_);
lean_ctor_set(v_reuseFailAlloc_2049_, 3, v_postponed_2041_);
lean_ctor_set(v_reuseFailAlloc_2049_, 4, v_diag_2042_);
v___x_2047_ = v_reuseFailAlloc_2049_;
goto v_reusejp_2046_;
}
v_reusejp_2046_:
{
lean_object* v___x_2048_; 
v___x_2048_ = lean_st_ref_put(v___y_1996_, v___x_2047_);
v_a_2008_ = v_fst_2035_;
goto v___jp_2007_;
}
}
}
v___jp_2052_:
{
lean_object* v_fst_2054_; lean_object* v_snd_2055_; uint8_t v___x_2056_; 
v_fst_2054_ = lean_ctor_get(v___y_2053_, 0);
lean_inc(v_fst_2054_);
v_snd_2055_ = lean_ctor_get(v___y_2053_, 1);
lean_inc(v_snd_2055_);
lean_dec_ref(v___y_2053_);
v___x_2056_ = lean_unbox(v_fst_2054_);
lean_dec(v_fst_2054_);
v_fst_2035_ = v___x_2056_;
v_snd_2036_ = v_snd_2055_;
goto v___jp_2034_;
}
v___jp_2057_:
{
lean_object* v___x_2060_; lean_object* v_cache_2061_; lean_object* v_zetaDeltaFVarIds_2062_; lean_object* v_postponed_2063_; lean_object* v_diag_2064_; lean_object* v___x_2066_; uint8_t v_isShared_2067_; uint8_t v_isSharedCheck_2072_; 
v___x_2060_ = lean_st_ref_take(v___y_1996_);
v_cache_2061_ = lean_ctor_get(v___x_2060_, 1);
v_zetaDeltaFVarIds_2062_ = lean_ctor_get(v___x_2060_, 2);
v_postponed_2063_ = lean_ctor_get(v___x_2060_, 3);
v_diag_2064_ = lean_ctor_get(v___x_2060_, 4);
v_isSharedCheck_2072_ = !lean_is_exclusive(v___x_2060_);
if (v_isSharedCheck_2072_ == 0)
{
lean_object* v_unused_2073_; 
v_unused_2073_ = lean_ctor_get(v___x_2060_, 0);
lean_dec(v_unused_2073_);
v___x_2066_ = v___x_2060_;
v_isShared_2067_ = v_isSharedCheck_2072_;
goto v_resetjp_2065_;
}
else
{
lean_inc(v_diag_2064_);
lean_inc(v_postponed_2063_);
lean_inc(v_zetaDeltaFVarIds_2062_);
lean_inc(v_cache_2061_);
lean_dec(v___x_2060_);
v___x_2066_ = lean_box(0);
v_isShared_2067_ = v_isSharedCheck_2072_;
goto v_resetjp_2065_;
}
v_resetjp_2065_:
{
lean_object* v___x_2069_; 
if (v_isShared_2067_ == 0)
{
lean_ctor_set(v___x_2066_, 0, v_mctx_2059_);
v___x_2069_ = v___x_2066_;
goto v_reusejp_2068_;
}
else
{
lean_object* v_reuseFailAlloc_2071_; 
v_reuseFailAlloc_2071_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2071_, 0, v_mctx_2059_);
lean_ctor_set(v_reuseFailAlloc_2071_, 1, v_cache_2061_);
lean_ctor_set(v_reuseFailAlloc_2071_, 2, v_zetaDeltaFVarIds_2062_);
lean_ctor_set(v_reuseFailAlloc_2071_, 3, v_postponed_2063_);
lean_ctor_set(v_reuseFailAlloc_2071_, 4, v_diag_2064_);
v___x_2069_ = v_reuseFailAlloc_2071_;
goto v_reusejp_2068_;
}
v_reusejp_2068_:
{
lean_object* v___x_2070_; 
v___x_2070_ = lean_st_ref_put(v___y_1996_, v___x_2069_);
v_a_2008_ = v_fst_2058_;
goto v___jp_2007_;
}
}
}
v___jp_2074_:
{
lean_object* v_snd_2076_; lean_object* v_fst_2077_; lean_object* v_mctx_2078_; uint8_t v___x_2079_; 
v_snd_2076_ = lean_ctor_get(v___y_2075_, 1);
lean_inc(v_snd_2076_);
v_fst_2077_ = lean_ctor_get(v___y_2075_, 0);
lean_inc(v_fst_2077_);
lean_dec_ref(v___y_2075_);
v_mctx_2078_ = lean_ctor_get(v_snd_2076_, 1);
lean_inc_ref(v_mctx_2078_);
lean_dec(v_snd_2076_);
v___x_2079_ = lean_unbox(v_fst_2077_);
lean_dec(v_fst_2077_);
v_fst_2058_ = v___x_2079_;
v_mctx_2059_ = v_mctx_2078_;
goto v___jp_2057_;
}
}
else
{
uint8_t v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; 
lean_dec(v___x_1991_);
lean_dec_ref(v___x_1990_);
v___x_2144_ = 0;
v___x_2145_ = lean_box(v___x_2144_);
v___x_2146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2146_, 0, v___x_2145_);
return v___x_2146_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_1989_ = stack[0].m_num;
lean_object* v___x_1990_ = stack[1].m_obj;
lean_object* v___x_1991_ = stack[2].m_obj;
lean_object* v_ctx_1992_ = stack[3].m_obj;
lean_object* v_as_1993_ = stack[4].m_obj;
size_t v_i_1994_ = stack[5].m_num;
size_t v_stop_1995_ = stack[6].m_num;
lean_object* v___y_1996_ = stack[7].m_obj;
lean_object* v_res_2147_;
v_res_2147_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg(v___x_1989_, v___x_1990_, v___x_1991_, v_ctx_1992_, v_as_1993_, v_i_1994_, v_stop_1995_, v___y_1996_);
stack->m_obj
 = v_res_2147_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___boxed(lean_object* v___x_2148_, lean_object* v___x_2149_, lean_object* v___x_2150_, lean_object* v_ctx_2151_, lean_object* v_as_2152_, lean_object* v_i_2153_, lean_object* v_stop_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_){
_start:
{
uint8_t v___x_7754__boxed_2157_; size_t v_i_boxed_2158_; size_t v_stop_boxed_2159_; lean_object* v_res_2160_; 
v___x_7754__boxed_2157_ = lean_unbox(v___x_2148_);
v_i_boxed_2158_ = lean_unbox_usize(v_i_2153_);
lean_dec(v_i_2153_);
v_stop_boxed_2159_ = lean_unbox_usize(v_stop_2154_);
lean_dec(v_stop_2154_);
v_res_2160_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg(v___x_7754__boxed_2157_, v___x_2149_, v___x_2150_, v_ctx_2151_, v_as_2152_, v_i_boxed_2158_, v_stop_boxed_2159_, v___y_2155_);
lean_dec(v___y_2155_);
lean_dec_ref(v_as_2152_);
lean_dec_ref(v_ctx_2151_);
return v_res_2160_;
}
}
lean_object* l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4(uint8_t v___x_2161_, lean_object* v___x_2162_, lean_object* v___x_2163_, lean_object* v_ctx_2164_, lean_object* v_x_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_){
_start:
{
if (lean_obj_tag(v_x_2165_) == 0)
{
lean_object* v_cs_2171_; lean_object* v___x_2173_; uint8_t v_isShared_2174_; uint8_t v_isSharedCheck_2189_; 
v_cs_2171_ = lean_ctor_get(v_x_2165_, 0);
v_isSharedCheck_2189_ = !lean_is_exclusive(v_x_2165_);
if (v_isSharedCheck_2189_ == 0)
{
v___x_2173_ = v_x_2165_;
v_isShared_2174_ = v_isSharedCheck_2189_;
goto v_resetjp_2172_;
}
else
{
lean_inc(v_cs_2171_);
lean_dec(v_x_2165_);
v___x_2173_ = lean_box(0);
v_isShared_2174_ = v_isSharedCheck_2189_;
goto v_resetjp_2172_;
}
v_resetjp_2172_:
{
lean_object* v___x_2175_; lean_object* v___x_2176_; uint8_t v___x_2177_; 
v___x_2175_ = lean_unsigned_to_nat(0u);
v___x_2176_ = lean_array_get_size(v_cs_2171_);
v___x_2177_ = lean_nat_dec_lt(v___x_2175_, v___x_2176_);
if (v___x_2177_ == 0)
{
lean_object* v___x_2178_; lean_object* v___x_2180_; 
lean_dec_ref(v_cs_2171_);
lean_dec(v___x_2163_);
lean_dec_ref(v___x_2162_);
v___x_2178_ = lean_box(v___x_2177_);
if (v_isShared_2174_ == 0)
{
lean_ctor_set(v___x_2173_, 0, v___x_2178_);
v___x_2180_ = v___x_2173_;
goto v_reusejp_2179_;
}
else
{
lean_object* v_reuseFailAlloc_2181_; 
v_reuseFailAlloc_2181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2181_, 0, v___x_2178_);
v___x_2180_ = v_reuseFailAlloc_2181_;
goto v_reusejp_2179_;
}
v_reusejp_2179_:
{
return v___x_2180_;
}
}
else
{
if (v___x_2177_ == 0)
{
lean_object* v___x_2182_; lean_object* v___x_2184_; 
lean_dec_ref(v_cs_2171_);
lean_dec(v___x_2163_);
lean_dec_ref(v___x_2162_);
v___x_2182_ = lean_box(v___x_2177_);
if (v_isShared_2174_ == 0)
{
lean_ctor_set(v___x_2173_, 0, v___x_2182_);
v___x_2184_ = v___x_2173_;
goto v_reusejp_2183_;
}
else
{
lean_object* v_reuseFailAlloc_2185_; 
v_reuseFailAlloc_2185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2185_, 0, v___x_2182_);
v___x_2184_ = v_reuseFailAlloc_2185_;
goto v_reusejp_2183_;
}
v_reusejp_2183_:
{
return v___x_2184_;
}
}
else
{
size_t v___x_2186_; size_t v___x_2187_; lean_object* v___x_2188_; 
lean_del_object(v___x_2173_);
v___x_2186_ = ((size_t)0ULL);
v___x_2187_ = lean_usize_of_nat(v___x_2176_);
v___x_2188_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4_spec__5(v___x_2161_, v___x_2162_, v___x_2163_, v_ctx_2164_, v_cs_2171_, v___x_2186_, v___x_2187_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_);
lean_dec_ref(v_cs_2171_);
return v___x_2188_;
}
}
}
}
else
{
lean_object* v_vs_2190_; lean_object* v___x_2192_; uint8_t v_isShared_2193_; uint8_t v_isSharedCheck_2208_; 
v_vs_2190_ = lean_ctor_get(v_x_2165_, 0);
v_isSharedCheck_2208_ = !lean_is_exclusive(v_x_2165_);
if (v_isSharedCheck_2208_ == 0)
{
v___x_2192_ = v_x_2165_;
v_isShared_2193_ = v_isSharedCheck_2208_;
goto v_resetjp_2191_;
}
else
{
lean_inc(v_vs_2190_);
lean_dec(v_x_2165_);
v___x_2192_ = lean_box(0);
v_isShared_2193_ = v_isSharedCheck_2208_;
goto v_resetjp_2191_;
}
v_resetjp_2191_:
{
lean_object* v___x_2194_; lean_object* v___x_2195_; uint8_t v___x_2196_; 
v___x_2194_ = lean_unsigned_to_nat(0u);
v___x_2195_ = lean_array_get_size(v_vs_2190_);
v___x_2196_ = lean_nat_dec_lt(v___x_2194_, v___x_2195_);
if (v___x_2196_ == 0)
{
lean_object* v___x_2197_; lean_object* v___x_2199_; 
lean_dec_ref(v_vs_2190_);
lean_dec(v___x_2163_);
lean_dec_ref(v___x_2162_);
v___x_2197_ = lean_box(v___x_2196_);
if (v_isShared_2193_ == 0)
{
lean_ctor_set_tag(v___x_2192_, 0);
lean_ctor_set(v___x_2192_, 0, v___x_2197_);
v___x_2199_ = v___x_2192_;
goto v_reusejp_2198_;
}
else
{
lean_object* v_reuseFailAlloc_2200_; 
v_reuseFailAlloc_2200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2200_, 0, v___x_2197_);
v___x_2199_ = v_reuseFailAlloc_2200_;
goto v_reusejp_2198_;
}
v_reusejp_2198_:
{
return v___x_2199_;
}
}
else
{
if (v___x_2196_ == 0)
{
lean_object* v___x_2201_; lean_object* v___x_2203_; 
lean_dec_ref(v_vs_2190_);
lean_dec(v___x_2163_);
lean_dec_ref(v___x_2162_);
v___x_2201_ = lean_box(v___x_2196_);
if (v_isShared_2193_ == 0)
{
lean_ctor_set_tag(v___x_2192_, 0);
lean_ctor_set(v___x_2192_, 0, v___x_2201_);
v___x_2203_ = v___x_2192_;
goto v_reusejp_2202_;
}
else
{
lean_object* v_reuseFailAlloc_2204_; 
v_reuseFailAlloc_2204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2204_, 0, v___x_2201_);
v___x_2203_ = v_reuseFailAlloc_2204_;
goto v_reusejp_2202_;
}
v_reusejp_2202_:
{
return v___x_2203_;
}
}
else
{
size_t v___x_2205_; size_t v___x_2206_; lean_object* v___x_2207_; 
lean_del_object(v___x_2192_);
v___x_2205_ = ((size_t)0ULL);
v___x_2206_ = lean_usize_of_nat(v___x_2195_);
v___x_2207_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg(v___x_2161_, v___x_2162_, v___x_2163_, v_ctx_2164_, v_vs_2190_, v___x_2205_, v___x_2206_, v___y_2167_);
lean_dec_ref(v_vs_2190_);
return v___x_2207_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_2161_ = stack[0].m_num;
lean_object* v___x_2162_ = stack[1].m_obj;
lean_object* v___x_2163_ = stack[2].m_obj;
lean_object* v_ctx_2164_ = stack[3].m_obj;
lean_object* v_x_2165_ = stack[4].m_obj;
lean_object* v___y_2166_ = stack[5].m_obj;
lean_object* v___y_2167_ = stack[6].m_obj;
lean_object* v___y_2168_ = stack[7].m_obj;
lean_object* v___y_2169_ = stack[8].m_obj;
lean_object* v_res_2209_;
v_res_2209_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4(v___x_2161_, v___x_2162_, v___x_2163_, v_ctx_2164_, v_x_2165_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_);
stack->m_obj
 = v_res_2209_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4_spec__5(uint8_t v___x_2210_, lean_object* v___x_2211_, lean_object* v___x_2212_, lean_object* v_ctx_2213_, lean_object* v_as_2214_, size_t v_i_2215_, size_t v_stop_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_){
_start:
{
uint8_t v___x_2222_; 
v___x_2222_ = lean_usize_dec_eq(v_i_2215_, v_stop_2216_);
if (v___x_2222_ == 0)
{
uint8_t v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; 
v___x_2223_ = 1;
v___x_2224_ = lean_array_uget_borrowed(v_as_2214_, v_i_2215_);
lean_inc(v___x_2224_);
lean_inc(v___x_2212_);
lean_inc_ref(v___x_2211_);
v___x_2225_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4(v___x_2210_, v___x_2211_, v___x_2212_, v_ctx_2213_, v___x_2224_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_);
if (lean_obj_tag(v___x_2225_) == 0)
{
lean_object* v_a_2226_; lean_object* v___x_2228_; uint8_t v_isShared_2229_; uint8_t v_isSharedCheck_2238_; 
v_a_2226_ = lean_ctor_get(v___x_2225_, 0);
v_isSharedCheck_2238_ = !lean_is_exclusive(v___x_2225_);
if (v_isSharedCheck_2238_ == 0)
{
v___x_2228_ = v___x_2225_;
v_isShared_2229_ = v_isSharedCheck_2238_;
goto v_resetjp_2227_;
}
else
{
lean_inc(v_a_2226_);
lean_dec(v___x_2225_);
v___x_2228_ = lean_box(0);
v_isShared_2229_ = v_isSharedCheck_2238_;
goto v_resetjp_2227_;
}
v_resetjp_2227_:
{
uint8_t v___x_2230_; 
v___x_2230_ = lean_unbox(v_a_2226_);
lean_dec(v_a_2226_);
if (v___x_2230_ == 0)
{
size_t v___x_2231_; size_t v___x_2232_; 
lean_del_object(v___x_2228_);
v___x_2231_ = ((size_t)1ULL);
v___x_2232_ = lean_usize_add(v_i_2215_, v___x_2231_);
v_i_2215_ = v___x_2232_;
goto _start;
}
else
{
lean_object* v___x_2234_; lean_object* v___x_2236_; 
lean_dec(v___x_2212_);
lean_dec_ref(v___x_2211_);
v___x_2234_ = lean_box(v___x_2223_);
if (v_isShared_2229_ == 0)
{
lean_ctor_set(v___x_2228_, 0, v___x_2234_);
v___x_2236_ = v___x_2228_;
goto v_reusejp_2235_;
}
else
{
lean_object* v_reuseFailAlloc_2237_; 
v_reuseFailAlloc_2237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2237_, 0, v___x_2234_);
v___x_2236_ = v_reuseFailAlloc_2237_;
goto v_reusejp_2235_;
}
v_reusejp_2235_:
{
return v___x_2236_;
}
}
}
}
else
{
lean_dec(v___x_2212_);
lean_dec_ref(v___x_2211_);
return v___x_2225_;
}
}
else
{
uint8_t v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; 
lean_dec(v___x_2212_);
lean_dec_ref(v___x_2211_);
v___x_2239_ = 0;
v___x_2240_ = lean_box(v___x_2239_);
v___x_2241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2241_, 0, v___x_2240_);
return v___x_2241_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4_spec__5_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_2210_ = stack[0].m_num;
lean_object* v___x_2211_ = stack[1].m_obj;
lean_object* v___x_2212_ = stack[2].m_obj;
lean_object* v_ctx_2213_ = stack[3].m_obj;
lean_object* v_as_2214_ = stack[4].m_obj;
size_t v_i_2215_ = stack[5].m_num;
size_t v_stop_2216_ = stack[6].m_num;
lean_object* v___y_2217_ = stack[7].m_obj;
lean_object* v___y_2218_ = stack[8].m_obj;
lean_object* v___y_2219_ = stack[9].m_obj;
lean_object* v___y_2220_ = stack[10].m_obj;
lean_object* v_res_2242_;
v_res_2242_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4_spec__5(v___x_2210_, v___x_2211_, v___x_2212_, v_ctx_2213_, v_as_2214_, v_i_2215_, v_stop_2216_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_);
stack->m_obj
 = v_res_2242_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4_spec__5___boxed(lean_object* v___x_2243_, lean_object* v___x_2244_, lean_object* v___x_2245_, lean_object* v_ctx_2246_, lean_object* v_as_2247_, lean_object* v_i_2248_, lean_object* v_stop_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_){
_start:
{
uint8_t v___x_8198__boxed_2255_; size_t v_i_boxed_2256_; size_t v_stop_boxed_2257_; lean_object* v_res_2258_; 
v___x_8198__boxed_2255_ = lean_unbox(v___x_2243_);
v_i_boxed_2256_ = lean_unbox_usize(v_i_2248_);
lean_dec(v_i_2248_);
v_stop_boxed_2257_ = lean_unbox_usize(v_stop_2249_);
lean_dec(v_stop_2249_);
v_res_2258_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4_spec__5(v___x_8198__boxed_2255_, v___x_2244_, v___x_2245_, v_ctx_2246_, v_as_2247_, v_i_boxed_2256_, v_stop_boxed_2257_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_);
lean_dec(v___y_2253_);
lean_dec_ref(v___y_2252_);
lean_dec(v___y_2251_);
lean_dec_ref(v___y_2250_);
lean_dec_ref(v_as_2247_);
lean_dec_ref(v_ctx_2246_);
return v_res_2258_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4___boxed(lean_object* v___x_2259_, lean_object* v___x_2260_, lean_object* v___x_2261_, lean_object* v_ctx_2262_, lean_object* v_x_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_){
_start:
{
uint8_t v___x_8218__boxed_2269_; lean_object* v_res_2270_; 
v___x_8218__boxed_2269_ = lean_unbox(v___x_2259_);
v_res_2270_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4(v___x_8218__boxed_2269_, v___x_2260_, v___x_2261_, v_ctx_2262_, v_x_2263_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_);
lean_dec(v___y_2267_);
lean_dec_ref(v___y_2266_);
lean_dec(v___y_2265_);
lean_dec_ref(v___y_2264_);
lean_dec_ref(v_ctx_2262_);
return v_res_2270_;
}
}
lean_object* l_Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4(uint8_t v___x_2271_, lean_object* v___x_2272_, lean_object* v___x_2273_, lean_object* v_ctx_2274_, lean_object* v_t_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_){
_start:
{
lean_object* v_root_2281_; lean_object* v_tail_2282_; lean_object* v___x_2283_; 
v_root_2281_ = lean_ctor_get(v_t_2275_, 0);
lean_inc_ref(v_root_2281_);
v_tail_2282_ = lean_ctor_get(v_t_2275_, 1);
lean_inc_ref(v_tail_2282_);
lean_dec_ref(v_t_2275_);
lean_inc(v___x_2273_);
lean_inc_ref(v___x_2272_);
v___x_2283_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4(v___x_2271_, v___x_2272_, v___x_2273_, v_ctx_2274_, v_root_2281_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_);
if (lean_obj_tag(v___x_2283_) == 0)
{
lean_object* v_a_2284_; uint8_t v___x_2285_; 
v_a_2284_ = lean_ctor_get(v___x_2283_, 0);
v___x_2285_ = lean_unbox(v_a_2284_);
if (v___x_2285_ == 0)
{
lean_object* v___x_2287_; uint8_t v_isShared_2288_; uint8_t v_isSharedCheck_2303_; 
v_isSharedCheck_2303_ = !lean_is_exclusive(v___x_2283_);
if (v_isSharedCheck_2303_ == 0)
{
lean_object* v_unused_2304_; 
v_unused_2304_ = lean_ctor_get(v___x_2283_, 0);
lean_dec(v_unused_2304_);
v___x_2287_ = v___x_2283_;
v_isShared_2288_ = v_isSharedCheck_2303_;
goto v_resetjp_2286_;
}
else
{
lean_dec(v___x_2283_);
v___x_2287_ = lean_box(0);
v_isShared_2288_ = v_isSharedCheck_2303_;
goto v_resetjp_2286_;
}
v_resetjp_2286_:
{
lean_object* v___x_2289_; lean_object* v___x_2290_; uint8_t v___x_2291_; 
v___x_2289_ = lean_unsigned_to_nat(0u);
v___x_2290_ = lean_array_get_size(v_tail_2282_);
v___x_2291_ = lean_nat_dec_lt(v___x_2289_, v___x_2290_);
if (v___x_2291_ == 0)
{
lean_object* v___x_2292_; lean_object* v___x_2294_; 
lean_dec_ref(v_tail_2282_);
lean_dec(v___x_2273_);
lean_dec_ref(v___x_2272_);
v___x_2292_ = lean_box(v___x_2291_);
if (v_isShared_2288_ == 0)
{
lean_ctor_set(v___x_2287_, 0, v___x_2292_);
v___x_2294_ = v___x_2287_;
goto v_reusejp_2293_;
}
else
{
lean_object* v_reuseFailAlloc_2295_; 
v_reuseFailAlloc_2295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2295_, 0, v___x_2292_);
v___x_2294_ = v_reuseFailAlloc_2295_;
goto v_reusejp_2293_;
}
v_reusejp_2293_:
{
return v___x_2294_;
}
}
else
{
if (v___x_2291_ == 0)
{
lean_object* v___x_2296_; lean_object* v___x_2298_; 
lean_dec_ref(v_tail_2282_);
lean_dec(v___x_2273_);
lean_dec_ref(v___x_2272_);
v___x_2296_ = lean_box(v___x_2291_);
if (v_isShared_2288_ == 0)
{
lean_ctor_set(v___x_2287_, 0, v___x_2296_);
v___x_2298_ = v___x_2287_;
goto v_reusejp_2297_;
}
else
{
lean_object* v_reuseFailAlloc_2299_; 
v_reuseFailAlloc_2299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2299_, 0, v___x_2296_);
v___x_2298_ = v_reuseFailAlloc_2299_;
goto v_reusejp_2297_;
}
v_reusejp_2297_:
{
return v___x_2298_;
}
}
else
{
size_t v___x_2300_; size_t v___x_2301_; lean_object* v___x_2302_; 
lean_del_object(v___x_2287_);
v___x_2300_ = ((size_t)0ULL);
v___x_2301_ = lean_usize_of_nat(v___x_2290_);
v___x_2302_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg(v___x_2271_, v___x_2272_, v___x_2273_, v_ctx_2274_, v_tail_2282_, v___x_2300_, v___x_2301_, v___y_2277_);
lean_dec_ref(v_tail_2282_);
return v___x_2302_;
}
}
}
}
else
{
lean_dec_ref(v_tail_2282_);
lean_dec(v___x_2273_);
lean_dec_ref(v___x_2272_);
return v___x_2283_;
}
}
else
{
lean_dec_ref(v_tail_2282_);
lean_dec(v___x_2273_);
lean_dec_ref(v___x_2272_);
return v___x_2283_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_2271_ = stack[0].m_num;
lean_object* v___x_2272_ = stack[1].m_obj;
lean_object* v___x_2273_ = stack[2].m_obj;
lean_object* v_ctx_2274_ = stack[3].m_obj;
lean_object* v_t_2275_ = stack[4].m_obj;
lean_object* v___y_2276_ = stack[5].m_obj;
lean_object* v___y_2277_ = stack[6].m_obj;
lean_object* v___y_2278_ = stack[7].m_obj;
lean_object* v___y_2279_ = stack[8].m_obj;
lean_object* v_res_2305_;
v_res_2305_ = l_Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4(v___x_2271_, v___x_2272_, v___x_2273_, v_ctx_2274_, v_t_2275_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_);
stack->m_obj
 = v_res_2305_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4___boxed(lean_object* v___x_2306_, lean_object* v___x_2307_, lean_object* v___x_2308_, lean_object* v_ctx_2309_, lean_object* v_t_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_){
_start:
{
uint8_t v___x_8458__boxed_2316_; lean_object* v_res_2317_; 
v___x_8458__boxed_2316_ = lean_unbox(v___x_2306_);
v_res_2317_ = l_Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4(v___x_8458__boxed_2316_, v___x_2307_, v___x_2308_, v_ctx_2309_, v_t_2310_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_);
lean_dec(v___y_2314_);
lean_dec_ref(v___y_2313_);
lean_dec(v___y_2312_);
lean_dec_ref(v___y_2311_);
lean_dec_ref(v_ctx_2309_);
return v_res_2317_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices(lean_object* v_ctx_2318_, lean_object* v_a_2319_, lean_object* v_a_2320_, lean_object* v_a_2321_, lean_object* v_a_2322_){
_start:
{
lean_object* v_majorTypeIndices_2324_; lean_object* v___x_2325_; uint8_t v___y_2327_; lean_object* v___x_2349_; uint8_t v___x_2350_; 
v_majorTypeIndices_2324_ = lean_ctor_get(v_ctx_2318_, 5);
lean_inc_ref(v_majorTypeIndices_2324_);
v___x_2325_ = lean_array_get_size(v_majorTypeIndices_2324_);
v___x_2349_ = lean_unsigned_to_nat(0u);
v___x_2350_ = lean_nat_dec_eq(v___x_2325_, v___x_2349_);
if (v___x_2350_ == 0)
{
uint8_t v___x_2351_; 
v___x_2351_ = lean_nat_dec_lt(v___x_2349_, v___x_2325_);
if (v___x_2351_ == 0)
{
v___y_2327_ = v___x_2351_;
goto v___jp_2326_;
}
else
{
if (v___x_2351_ == 0)
{
v___y_2327_ = v___x_2351_;
goto v___jp_2326_;
}
else
{
size_t v___x_2352_; size_t v___x_2353_; uint8_t v___x_2354_; 
v___x_2352_ = ((size_t)0ULL);
v___x_2353_ = lean_usize_of_nat(v___x_2325_);
v___x_2354_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5(v___x_2325_, v_majorTypeIndices_2324_, v___x_2352_, v___x_2353_);
if (v___x_2354_ == 0)
{
v___y_2327_ = v___x_2354_;
goto v___jp_2326_;
}
else
{
lean_object* v___x_2355_; lean_object* v___x_2356_; 
lean_dec_ref(v_majorTypeIndices_2324_);
lean_dec_ref(v_ctx_2318_);
v___x_2355_ = lean_box(v___x_2350_);
v___x_2356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2356_, 0, v___x_2355_);
return v___x_2356_;
}
}
}
}
else
{
lean_object* v___x_2357_; lean_object* v___x_2358_; 
lean_dec_ref(v_majorTypeIndices_2324_);
lean_dec_ref(v_ctx_2318_);
v___x_2357_ = lean_box(v___x_2350_);
v___x_2358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2358_, 0, v___x_2357_);
return v___x_2358_;
}
v___jp_2326_:
{
uint8_t v___x_2328_; 
v___x_2328_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1___redArg(v_majorTypeIndices_2324_, v___x_2325_, v___x_2325_);
if (v___x_2328_ == 0)
{
lean_object* v_lctx_2329_; lean_object* v_decls_2330_; lean_object* v___x_2331_; 
v_lctx_2329_ = lean_ctor_get(v_a_2319_, 2);
v_decls_2330_ = lean_ctor_get(v_lctx_2329_, 1);
lean_inc_ref(v_decls_2330_);
v___x_2331_ = l_Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4(v___x_2328_, v_majorTypeIndices_2324_, v___x_2325_, v_ctx_2318_, v_decls_2330_, v_a_2319_, v_a_2320_, v_a_2321_, v_a_2322_);
lean_dec_ref(v_ctx_2318_);
if (lean_obj_tag(v___x_2331_) == 0)
{
lean_object* v_a_2332_; lean_object* v___x_2334_; uint8_t v_isShared_2335_; uint8_t v_isSharedCheck_2346_; 
v_a_2332_ = lean_ctor_get(v___x_2331_, 0);
v_isSharedCheck_2346_ = !lean_is_exclusive(v___x_2331_);
if (v_isSharedCheck_2346_ == 0)
{
v___x_2334_ = v___x_2331_;
v_isShared_2335_ = v_isSharedCheck_2346_;
goto v_resetjp_2333_;
}
else
{
lean_inc(v_a_2332_);
lean_dec(v___x_2331_);
v___x_2334_ = lean_box(0);
v_isShared_2335_ = v_isSharedCheck_2346_;
goto v_resetjp_2333_;
}
v_resetjp_2333_:
{
uint8_t v___x_2336_; 
v___x_2336_ = lean_unbox(v_a_2332_);
lean_dec(v_a_2332_);
if (v___x_2336_ == 0)
{
uint8_t v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2340_; 
v___x_2337_ = 1;
v___x_2338_ = lean_box(v___x_2337_);
if (v_isShared_2335_ == 0)
{
lean_ctor_set(v___x_2334_, 0, v___x_2338_);
v___x_2340_ = v___x_2334_;
goto v_reusejp_2339_;
}
else
{
lean_object* v_reuseFailAlloc_2341_; 
v_reuseFailAlloc_2341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2341_, 0, v___x_2338_);
v___x_2340_ = v_reuseFailAlloc_2341_;
goto v_reusejp_2339_;
}
v_reusejp_2339_:
{
return v___x_2340_;
}
}
else
{
lean_object* v___x_2342_; lean_object* v___x_2344_; 
v___x_2342_ = lean_box(v___x_2328_);
if (v_isShared_2335_ == 0)
{
lean_ctor_set(v___x_2334_, 0, v___x_2342_);
v___x_2344_ = v___x_2334_;
goto v_reusejp_2343_;
}
else
{
lean_object* v_reuseFailAlloc_2345_; 
v_reuseFailAlloc_2345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2345_, 0, v___x_2342_);
v___x_2344_ = v_reuseFailAlloc_2345_;
goto v_reusejp_2343_;
}
v_reusejp_2343_:
{
return v___x_2344_;
}
}
}
}
else
{
return v___x_2331_;
}
}
else
{
lean_object* v___x_2347_; lean_object* v___x_2348_; 
lean_dec_ref(v_majorTypeIndices_2324_);
lean_dec_ref(v_ctx_2318_);
v___x_2347_ = lean_box(v___y_2327_);
v___x_2348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2348_, 0, v___x_2347_);
return v___x_2348_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctx_2318_ = stack[0].m_obj;
lean_object* v_a_2319_ = stack[1].m_obj;
lean_object* v_a_2320_ = stack[2].m_obj;
lean_object* v_a_2321_ = stack[3].m_obj;
lean_object* v_a_2322_ = stack[4].m_obj;
lean_object* v_res_2359_;
v_res_2359_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices(v_ctx_2318_, v_a_2319_, v_a_2320_, v_a_2321_, v_a_2322_);
stack->m_obj
 = v_res_2359_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___boxed(lean_object* v_ctx_2360_, lean_object* v_a_2361_, lean_object* v_a_2362_, lean_object* v_a_2363_, lean_object* v_a_2364_, lean_object* v_a_2365_){
_start:
{
lean_object* v_res_2366_; 
v_res_2366_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices(v_ctx_2360_, v_a_2361_, v_a_2362_, v_a_2363_, v_a_2364_);
lean_dec(v_a_2364_);
lean_dec_ref(v_a_2363_);
lean_dec(v_a_2362_);
lean_dec_ref(v_a_2361_);
return v_res_2366_;
}
}
uint8_t l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0(lean_object* v___x_2367_, lean_object* v_i_2368_, lean_object* v_n_2369_, lean_object* v_i_2370_, lean_object* v_a_2371_){
_start:
{
uint8_t v___x_2372_; 
v___x_2372_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0___redArg(v___x_2367_, v_i_2368_, v_n_2369_, v_i_2370_);
return v___x_2372_;
}
}
LEAN_EXPORT void l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2367_ = stack[0].m_obj;
lean_object* v_i_2368_ = stack[1].m_obj;
lean_object* v_n_2369_ = stack[2].m_obj;
lean_object* v_i_2370_ = stack[3].m_obj;
uint8_t v_res_2373_;
v_res_2373_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0(v___x_2367_, v_i_2368_, v_n_2369_, v_i_2370_, lean_box(0));
stack->m_num = v_res_2373_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0___boxed(lean_object* v___x_2374_, lean_object* v_i_2375_, lean_object* v_n_2376_, lean_object* v_i_2377_, lean_object* v_a_2378_){
_start:
{
uint8_t v_res_2379_; lean_object* v_r_2380_; 
v_res_2379_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0(v___x_2374_, v_i_2375_, v_n_2376_, v_i_2377_, v_a_2378_);
lean_dec(v_n_2376_);
lean_dec(v_i_2375_);
lean_dec_ref(v___x_2374_);
v_r_2380_ = lean_box(v_res_2379_);
return v_r_2380_;
}
}
uint8_t l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1(lean_object* v___x_2381_, lean_object* v_n_2382_, lean_object* v_i_2383_, lean_object* v_a_2384_){
_start:
{
uint8_t v___x_2385_; 
v___x_2385_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1___redArg(v___x_2381_, v_n_2382_, v_i_2383_);
return v___x_2385_;
}
}
LEAN_EXPORT void l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2381_ = stack[0].m_obj;
lean_object* v_n_2382_ = stack[1].m_obj;
lean_object* v_i_2383_ = stack[2].m_obj;
uint8_t v_res_2386_;
v_res_2386_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1(v___x_2381_, v_n_2382_, v_i_2383_, lean_box(0));
stack->m_num = v_res_2386_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1___boxed(lean_object* v___x_2387_, lean_object* v_n_2388_, lean_object* v_i_2389_, lean_object* v_a_2390_){
_start:
{
uint8_t v_res_2391_; lean_object* v_r_2392_; 
v_res_2391_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1(v___x_2387_, v_n_2388_, v_i_2389_, v_a_2390_);
lean_dec(v_n_2388_);
lean_dec_ref(v___x_2387_);
v_r_2392_ = lean_box(v_res_2391_);
return v_r_2392_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5(uint8_t v___x_2393_, lean_object* v___x_2394_, lean_object* v___x_2395_, lean_object* v_ctx_2396_, lean_object* v_as_2397_, size_t v_i_2398_, size_t v_stop_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_){
_start:
{
lean_object* v___x_2405_; 
v___x_2405_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg(v___x_2393_, v___x_2394_, v___x_2395_, v_ctx_2396_, v_as_2397_, v_i_2398_, v_stop_2399_, v___y_2401_);
return v___x_2405_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_2393_ = stack[0].m_num;
lean_object* v___x_2394_ = stack[1].m_obj;
lean_object* v___x_2395_ = stack[2].m_obj;
lean_object* v_ctx_2396_ = stack[3].m_obj;
lean_object* v_as_2397_ = stack[4].m_obj;
size_t v_i_2398_ = stack[5].m_num;
size_t v_stop_2399_ = stack[6].m_num;
lean_object* v___y_2400_ = stack[7].m_obj;
lean_object* v___y_2401_ = stack[8].m_obj;
lean_object* v___y_2402_ = stack[9].m_obj;
lean_object* v___y_2403_ = stack[10].m_obj;
lean_object* v_res_2406_;
v_res_2406_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5(v___x_2393_, v___x_2394_, v___x_2395_, v_ctx_2396_, v_as_2397_, v_i_2398_, v_stop_2399_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_);
stack->m_obj
 = v_res_2406_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___boxed(lean_object* v___x_2407_, lean_object* v___x_2408_, lean_object* v___x_2409_, lean_object* v_ctx_2410_, lean_object* v_as_2411_, lean_object* v_i_2412_, lean_object* v_stop_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_){
_start:
{
uint8_t v___x_8693__boxed_2419_; size_t v_i_boxed_2420_; size_t v_stop_boxed_2421_; lean_object* v_res_2422_; 
v___x_8693__boxed_2419_ = lean_unbox(v___x_2407_);
v_i_boxed_2420_ = lean_unbox_usize(v_i_2412_);
lean_dec(v_i_2412_);
v_stop_boxed_2421_ = lean_unbox_usize(v_stop_2413_);
lean_dec(v_stop_2413_);
v_res_2422_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5(v___x_8693__boxed_2419_, v___x_2408_, v___x_2409_, v_ctx_2410_, v_as_2411_, v_i_boxed_2420_, v_stop_boxed_2421_, v___y_2414_, v___y_2415_, v___y_2416_, v___y_2417_);
lean_dec(v___y_2417_);
lean_dec_ref(v___y_2416_);
lean_dec(v___y_2415_);
lean_dec_ref(v___y_2414_);
lean_dec_ref(v_as_2411_);
lean_dec_ref(v_ctx_2410_);
return v_res_2422_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__0(lean_object* v_as_2423_, size_t v_i_2424_, size_t v_stop_2425_, lean_object* v_b_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_){
_start:
{
lean_object* v_a_2433_; uint8_t v___x_2437_; 
v___x_2437_ = lean_usize_dec_eq(v_i_2424_, v_stop_2425_);
if (v___x_2437_ == 0)
{
lean_object* v_toInductionSubgoal_2438_; lean_object* v_ctorName_2439_; lean_object* v_mvarId_2440_; lean_object* v_fields_2441_; lean_object* v_subst_2442_; lean_object* v___x_2444_; uint8_t v_isShared_2445_; uint8_t v_isSharedCheck_2495_; 
v_toInductionSubgoal_2438_ = lean_ctor_get(v_b_2426_, 0);
lean_inc_ref(v_toInductionSubgoal_2438_);
v_ctorName_2439_ = lean_ctor_get(v_b_2426_, 1);
v_mvarId_2440_ = lean_ctor_get(v_toInductionSubgoal_2438_, 0);
v_fields_2441_ = lean_ctor_get(v_toInductionSubgoal_2438_, 1);
v_subst_2442_ = lean_ctor_get(v_toInductionSubgoal_2438_, 2);
v_isSharedCheck_2495_ = !lean_is_exclusive(v_toInductionSubgoal_2438_);
if (v_isSharedCheck_2495_ == 0)
{
v___x_2444_ = v_toInductionSubgoal_2438_;
v_isShared_2445_ = v_isSharedCheck_2495_;
goto v_resetjp_2443_;
}
else
{
lean_inc(v_subst_2442_);
lean_inc(v_fields_2441_);
lean_inc(v_mvarId_2440_);
lean_dec(v_toInductionSubgoal_2438_);
v___x_2444_ = lean_box(0);
v_isShared_2445_ = v_isSharedCheck_2495_;
goto v_resetjp_2443_;
}
v_resetjp_2443_:
{
lean_object* v___x_2446_; lean_object* v___x_2447_; 
v___x_2446_ = lean_array_uget_borrowed(v_as_2423_, v_i_2424_);
lean_inc(v___x_2446_);
v___x_2447_ = l_Lean_Meta_FVarSubst_get(v_subst_2442_, v___x_2446_);
if (lean_obj_tag(v___x_2447_) == 1)
{
lean_object* v_fvarId_2448_; lean_object* v___x_2449_; 
v_fvarId_2448_ = lean_ctor_get(v___x_2447_, 0);
lean_inc(v_fvarId_2448_);
lean_dec_ref_known(v___x_2447_, 1);
v___x_2449_ = l_Lean_Meta_saveState___redArg(v___y_2428_, v___y_2430_);
if (lean_obj_tag(v___x_2449_) == 0)
{
lean_object* v_a_2450_; lean_object* v___x_2451_; 
v_a_2450_ = lean_ctor_get(v___x_2449_, 0);
lean_inc(v_a_2450_);
lean_dec_ref_known(v___x_2449_, 1);
v___x_2451_ = l_Lean_MVarId_clear(v_mvarId_2440_, v_fvarId_2448_, v___y_2427_, v___y_2428_, v___y_2429_, v___y_2430_);
if (lean_obj_tag(v___x_2451_) == 0)
{
lean_object* v___x_2453_; uint8_t v_isShared_2454_; uint8_t v_isSharedCheck_2463_; 
lean_inc(v_ctorName_2439_);
lean_dec(v_a_2450_);
v_isSharedCheck_2463_ = !lean_is_exclusive(v_b_2426_);
if (v_isSharedCheck_2463_ == 0)
{
lean_object* v_unused_2464_; lean_object* v_unused_2465_; 
v_unused_2464_ = lean_ctor_get(v_b_2426_, 1);
lean_dec(v_unused_2464_);
v_unused_2465_ = lean_ctor_get(v_b_2426_, 0);
lean_dec(v_unused_2465_);
v___x_2453_ = v_b_2426_;
v_isShared_2454_ = v_isSharedCheck_2463_;
goto v_resetjp_2452_;
}
else
{
lean_dec(v_b_2426_);
v___x_2453_ = lean_box(0);
v_isShared_2454_ = v_isSharedCheck_2463_;
goto v_resetjp_2452_;
}
v_resetjp_2452_:
{
lean_object* v_a_2455_; lean_object* v___x_2456_; lean_object* v___x_2458_; 
v_a_2455_ = lean_ctor_get(v___x_2451_, 0);
lean_inc(v_a_2455_);
lean_dec_ref_known(v___x_2451_, 1);
v___x_2456_ = l_Lean_Meta_FVarSubst_erase(v_subst_2442_, v___x_2446_);
if (v_isShared_2445_ == 0)
{
lean_ctor_set(v___x_2444_, 2, v___x_2456_);
lean_ctor_set(v___x_2444_, 0, v_a_2455_);
v___x_2458_ = v___x_2444_;
goto v_reusejp_2457_;
}
else
{
lean_object* v_reuseFailAlloc_2462_; 
v_reuseFailAlloc_2462_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2462_, 0, v_a_2455_);
lean_ctor_set(v_reuseFailAlloc_2462_, 1, v_fields_2441_);
lean_ctor_set(v_reuseFailAlloc_2462_, 2, v___x_2456_);
v___x_2458_ = v_reuseFailAlloc_2462_;
goto v_reusejp_2457_;
}
v_reusejp_2457_:
{
lean_object* v___x_2460_; 
if (v_isShared_2454_ == 0)
{
lean_ctor_set(v___x_2453_, 0, v___x_2458_);
v___x_2460_ = v___x_2453_;
goto v_reusejp_2459_;
}
else
{
lean_object* v_reuseFailAlloc_2461_; 
v_reuseFailAlloc_2461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2461_, 0, v___x_2458_);
lean_ctor_set(v_reuseFailAlloc_2461_, 1, v_ctorName_2439_);
v___x_2460_ = v_reuseFailAlloc_2461_;
goto v_reusejp_2459_;
}
v_reusejp_2459_:
{
v_a_2433_ = v___x_2460_;
goto v___jp_2432_;
}
}
}
}
else
{
lean_object* v_a_2466_; lean_object* v___x_2468_; uint8_t v_isShared_2469_; uint8_t v_isSharedCheck_2486_; 
lean_del_object(v___x_2444_);
lean_dec(v_subst_2442_);
lean_dec_ref(v_fields_2441_);
v_a_2466_ = lean_ctor_get(v___x_2451_, 0);
v_isSharedCheck_2486_ = !lean_is_exclusive(v___x_2451_);
if (v_isSharedCheck_2486_ == 0)
{
v___x_2468_ = v___x_2451_;
v_isShared_2469_ = v_isSharedCheck_2486_;
goto v_resetjp_2467_;
}
else
{
lean_inc(v_a_2466_);
lean_dec(v___x_2451_);
v___x_2468_ = lean_box(0);
v_isShared_2469_ = v_isSharedCheck_2486_;
goto v_resetjp_2467_;
}
v_resetjp_2467_:
{
lean_object* v___x_2471_; 
lean_inc(v_a_2466_);
if (v_isShared_2469_ == 0)
{
v___x_2471_ = v___x_2468_;
goto v_reusejp_2470_;
}
else
{
lean_object* v_reuseFailAlloc_2485_; 
v_reuseFailAlloc_2485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2485_, 0, v_a_2466_);
v___x_2471_ = v_reuseFailAlloc_2485_;
goto v_reusejp_2470_;
}
v_reusejp_2470_:
{
uint8_t v___y_2473_; uint8_t v___x_2483_; 
v___x_2483_ = l_Lean_Exception_isInterrupt(v_a_2466_);
if (v___x_2483_ == 0)
{
uint8_t v___x_2484_; 
v___x_2484_ = l_Lean_Exception_isRuntime(v_a_2466_);
v___y_2473_ = v___x_2484_;
goto v___jp_2472_;
}
else
{
lean_dec(v_a_2466_);
v___y_2473_ = v___x_2483_;
goto v___jp_2472_;
}
v___jp_2472_:
{
if (v___y_2473_ == 0)
{
lean_object* v___x_2474_; 
lean_dec_ref(v___x_2471_);
v___x_2474_ = l_Lean_Meta_SavedState_restore___redArg(v_a_2450_, v___y_2428_, v___y_2430_);
if (lean_obj_tag(v___x_2474_) == 0)
{
lean_dec_ref_known(v___x_2474_, 1);
v_a_2433_ = v_b_2426_;
goto v___jp_2432_;
}
else
{
lean_object* v_a_2475_; lean_object* v___x_2477_; uint8_t v_isShared_2478_; uint8_t v_isSharedCheck_2482_; 
lean_dec_ref(v_b_2426_);
v_a_2475_ = lean_ctor_get(v___x_2474_, 0);
v_isSharedCheck_2482_ = !lean_is_exclusive(v___x_2474_);
if (v_isSharedCheck_2482_ == 0)
{
v___x_2477_ = v___x_2474_;
v_isShared_2478_ = v_isSharedCheck_2482_;
goto v_resetjp_2476_;
}
else
{
lean_inc(v_a_2475_);
lean_dec(v___x_2474_);
v___x_2477_ = lean_box(0);
v_isShared_2478_ = v_isSharedCheck_2482_;
goto v_resetjp_2476_;
}
v_resetjp_2476_:
{
lean_object* v___x_2480_; 
if (v_isShared_2478_ == 0)
{
v___x_2480_ = v___x_2477_;
goto v_reusejp_2479_;
}
else
{
lean_object* v_reuseFailAlloc_2481_; 
v_reuseFailAlloc_2481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2481_, 0, v_a_2475_);
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
lean_dec(v_a_2450_);
lean_dec_ref(v_b_2426_);
return v___x_2471_;
}
}
}
}
}
}
else
{
lean_object* v_a_2487_; lean_object* v___x_2489_; uint8_t v_isShared_2490_; uint8_t v_isSharedCheck_2494_; 
lean_dec(v_fvarId_2448_);
lean_del_object(v___x_2444_);
lean_dec(v_subst_2442_);
lean_dec_ref(v_fields_2441_);
lean_dec(v_mvarId_2440_);
lean_dec_ref(v_b_2426_);
v_a_2487_ = lean_ctor_get(v___x_2449_, 0);
v_isSharedCheck_2494_ = !lean_is_exclusive(v___x_2449_);
if (v_isSharedCheck_2494_ == 0)
{
v___x_2489_ = v___x_2449_;
v_isShared_2490_ = v_isSharedCheck_2494_;
goto v_resetjp_2488_;
}
else
{
lean_inc(v_a_2487_);
lean_dec(v___x_2449_);
v___x_2489_ = lean_box(0);
v_isShared_2490_ = v_isSharedCheck_2494_;
goto v_resetjp_2488_;
}
v_resetjp_2488_:
{
lean_object* v___x_2492_; 
if (v_isShared_2490_ == 0)
{
v___x_2492_ = v___x_2489_;
goto v_reusejp_2491_;
}
else
{
lean_object* v_reuseFailAlloc_2493_; 
v_reuseFailAlloc_2493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2493_, 0, v_a_2487_);
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
lean_dec_ref(v___x_2447_);
lean_del_object(v___x_2444_);
lean_dec(v_subst_2442_);
lean_dec_ref(v_fields_2441_);
lean_dec(v_mvarId_2440_);
v_a_2433_ = v_b_2426_;
goto v___jp_2432_;
}
}
}
else
{
lean_object* v___x_2496_; 
v___x_2496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2496_, 0, v_b_2426_);
return v___x_2496_;
}
v___jp_2432_:
{
size_t v___x_2434_; size_t v___x_2435_; 
v___x_2434_ = ((size_t)1ULL);
v___x_2435_ = lean_usize_add(v_i_2424_, v___x_2434_);
v_i_2424_ = v___x_2435_;
v_b_2426_ = v_a_2433_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2423_ = stack[0].m_obj;
size_t v_i_2424_ = stack[1].m_num;
size_t v_stop_2425_ = stack[2].m_num;
lean_object* v_b_2426_ = stack[3].m_obj;
lean_object* v___y_2427_ = stack[4].m_obj;
lean_object* v___y_2428_ = stack[5].m_obj;
lean_object* v___y_2429_ = stack[6].m_obj;
lean_object* v___y_2430_ = stack[7].m_obj;
lean_object* v_res_2497_;
v_res_2497_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__0(v_as_2423_, v_i_2424_, v_stop_2425_, v_b_2426_, v___y_2427_, v___y_2428_, v___y_2429_, v___y_2430_);
stack->m_obj
 = v_res_2497_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__0___boxed(lean_object* v_as_2498_, lean_object* v_i_2499_, lean_object* v_stop_2500_, lean_object* v_b_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_){
_start:
{
size_t v_i_boxed_2507_; size_t v_stop_boxed_2508_; lean_object* v_res_2509_; 
v_i_boxed_2507_ = lean_unbox_usize(v_i_2499_);
lean_dec(v_i_2499_);
v_stop_boxed_2508_ = lean_unbox_usize(v_stop_2500_);
lean_dec(v_stop_2500_);
v_res_2509_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__0(v_as_2498_, v_i_boxed_2507_, v_stop_boxed_2508_, v_b_2501_, v___y_2502_, v___y_2503_, v___y_2504_, v___y_2505_);
lean_dec(v___y_2505_);
lean_dec_ref(v___y_2504_);
lean_dec(v___y_2503_);
lean_dec_ref(v___y_2502_);
lean_dec_ref(v_as_2498_);
return v_res_2509_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__1(lean_object* v_indicesFVarIds_2510_, size_t v_sz_2511_, size_t v_i_2512_, lean_object* v_bs_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_){
_start:
{
uint8_t v___x_2519_; 
v___x_2519_ = lean_usize_dec_lt(v_i_2512_, v_sz_2511_);
if (v___x_2519_ == 0)
{
lean_object* v___x_2520_; 
v___x_2520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2520_, 0, v_bs_2513_);
return v___x_2520_;
}
else
{
lean_object* v_v_2521_; lean_object* v___x_2522_; lean_object* v_bs_x27_2523_; lean_object* v_a_2525_; lean_object* v___y_2531_; lean_object* v___x_2541_; uint8_t v___x_2542_; 
v_v_2521_ = lean_array_uget(v_bs_2513_, v_i_2512_);
v___x_2522_ = lean_unsigned_to_nat(0u);
v_bs_x27_2523_ = lean_array_uset(v_bs_2513_, v_i_2512_, v___x_2522_);
v___x_2541_ = lean_array_get_size(v_indicesFVarIds_2510_);
v___x_2542_ = lean_nat_dec_lt(v___x_2522_, v___x_2541_);
if (v___x_2542_ == 0)
{
v_a_2525_ = v_v_2521_;
goto v___jp_2524_;
}
else
{
uint8_t v___x_2543_; 
v___x_2543_ = lean_nat_dec_le(v___x_2541_, v___x_2541_);
if (v___x_2543_ == 0)
{
if (v___x_2542_ == 0)
{
v_a_2525_ = v_v_2521_;
goto v___jp_2524_;
}
else
{
size_t v___x_2544_; size_t v___x_2545_; lean_object* v___x_2546_; 
v___x_2544_ = ((size_t)0ULL);
v___x_2545_ = lean_usize_of_nat(v___x_2541_);
v___x_2546_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__0(v_indicesFVarIds_2510_, v___x_2544_, v___x_2545_, v_v_2521_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_);
v___y_2531_ = v___x_2546_;
goto v___jp_2530_;
}
}
else
{
size_t v___x_2547_; size_t v___x_2548_; lean_object* v___x_2549_; 
v___x_2547_ = ((size_t)0ULL);
v___x_2548_ = lean_usize_of_nat(v___x_2541_);
v___x_2549_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__0(v_indicesFVarIds_2510_, v___x_2547_, v___x_2548_, v_v_2521_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_);
v___y_2531_ = v___x_2549_;
goto v___jp_2530_;
}
}
v___jp_2524_:
{
size_t v___x_2526_; size_t v___x_2527_; lean_object* v___x_2528_; 
v___x_2526_ = ((size_t)1ULL);
v___x_2527_ = lean_usize_add(v_i_2512_, v___x_2526_);
v___x_2528_ = lean_array_uset(v_bs_x27_2523_, v_i_2512_, v_a_2525_);
v_i_2512_ = v___x_2527_;
v_bs_2513_ = v___x_2528_;
goto _start;
}
v___jp_2530_:
{
if (lean_obj_tag(v___y_2531_) == 0)
{
lean_object* v_a_2532_; 
v_a_2532_ = lean_ctor_get(v___y_2531_, 0);
lean_inc(v_a_2532_);
lean_dec_ref_known(v___y_2531_, 1);
v_a_2525_ = v_a_2532_;
goto v___jp_2524_;
}
else
{
lean_object* v_a_2533_; lean_object* v___x_2535_; uint8_t v_isShared_2536_; uint8_t v_isSharedCheck_2540_; 
lean_dec_ref(v_bs_x27_2523_);
v_a_2533_ = lean_ctor_get(v___y_2531_, 0);
v_isSharedCheck_2540_ = !lean_is_exclusive(v___y_2531_);
if (v_isSharedCheck_2540_ == 0)
{
v___x_2535_ = v___y_2531_;
v_isShared_2536_ = v_isSharedCheck_2540_;
goto v_resetjp_2534_;
}
else
{
lean_inc(v_a_2533_);
lean_dec(v___y_2531_);
v___x_2535_ = lean_box(0);
v_isShared_2536_ = v_isSharedCheck_2540_;
goto v_resetjp_2534_;
}
v_resetjp_2534_:
{
lean_object* v___x_2538_; 
if (v_isShared_2536_ == 0)
{
v___x_2538_ = v___x_2535_;
goto v_reusejp_2537_;
}
else
{
lean_object* v_reuseFailAlloc_2539_; 
v_reuseFailAlloc_2539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2539_, 0, v_a_2533_);
v___x_2538_ = v_reuseFailAlloc_2539_;
goto v_reusejp_2537_;
}
v_reusejp_2537_:
{
return v___x_2538_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_indicesFVarIds_2510_ = stack[0].m_obj;
size_t v_sz_2511_ = stack[1].m_num;
size_t v_i_2512_ = stack[2].m_num;
lean_object* v_bs_2513_ = stack[3].m_obj;
lean_object* v___y_2514_ = stack[4].m_obj;
lean_object* v___y_2515_ = stack[5].m_obj;
lean_object* v___y_2516_ = stack[6].m_obj;
lean_object* v___y_2517_ = stack[7].m_obj;
lean_object* v_res_2550_;
v_res_2550_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__1(v_indicesFVarIds_2510_, v_sz_2511_, v_i_2512_, v_bs_2513_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_);
stack->m_obj
 = v_res_2550_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__1___boxed(lean_object* v_indicesFVarIds_2551_, lean_object* v_sz_2552_, lean_object* v_i_2553_, lean_object* v_bs_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_){
_start:
{
size_t v_sz_boxed_2560_; size_t v_i_boxed_2561_; lean_object* v_res_2562_; 
v_sz_boxed_2560_ = lean_unbox_usize(v_sz_2552_);
lean_dec(v_sz_2552_);
v_i_boxed_2561_ = lean_unbox_usize(v_i_2553_);
lean_dec(v_i_2553_);
v_res_2562_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__1(v_indicesFVarIds_2551_, v_sz_boxed_2560_, v_i_boxed_2561_, v_bs_2554_, v___y_2555_, v___y_2556_, v___y_2557_, v___y_2558_);
lean_dec(v___y_2558_);
lean_dec_ref(v___y_2557_);
lean_dec(v___y_2556_);
lean_dec_ref(v___y_2555_);
lean_dec_ref(v_indicesFVarIds_2551_);
return v_res_2562_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices(lean_object* v_s_u2081_2563_, lean_object* v_s_u2082_2564_, lean_object* v_a_2565_, lean_object* v_a_2566_, lean_object* v_a_2567_, lean_object* v_a_2568_){
_start:
{
lean_object* v_indicesFVarIds_2570_; size_t v_sz_2571_; size_t v___x_2572_; lean_object* v___x_2573_; 
v_indicesFVarIds_2570_ = lean_ctor_get(v_s_u2081_2563_, 1);
v_sz_2571_ = lean_array_size(v_s_u2082_2564_);
v___x_2572_ = ((size_t)0ULL);
v___x_2573_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__1(v_indicesFVarIds_2570_, v_sz_2571_, v___x_2572_, v_s_u2082_2564_, v_a_2565_, v_a_2566_, v_a_2567_, v_a_2568_);
return v___x_2573_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_u2081_2563_ = stack[0].m_obj;
lean_object* v_s_u2082_2564_ = stack[1].m_obj;
lean_object* v_a_2565_ = stack[2].m_obj;
lean_object* v_a_2566_ = stack[3].m_obj;
lean_object* v_a_2567_ = stack[4].m_obj;
lean_object* v_a_2568_ = stack[5].m_obj;
lean_object* v_res_2574_;
v_res_2574_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices(v_s_u2081_2563_, v_s_u2082_2564_, v_a_2565_, v_a_2566_, v_a_2567_, v_a_2568_);
stack->m_obj
 = v_res_2574_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices___boxed(lean_object* v_s_u2081_2575_, lean_object* v_s_u2082_2576_, lean_object* v_a_2577_, lean_object* v_a_2578_, lean_object* v_a_2579_, lean_object* v_a_2580_, lean_object* v_a_2581_){
_start:
{
lean_object* v_res_2582_; 
v_res_2582_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices(v_s_u2081_2575_, v_s_u2082_2576_, v_a_2577_, v_a_2578_, v_a_2579_, v_a_2580_);
lean_dec(v_a_2580_);
lean_dec_ref(v_a_2579_);
lean_dec(v_a_2578_);
lean_dec_ref(v_a_2577_);
lean_dec_ref(v_s_u2081_2575_);
return v_res_2582_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0___redArg(lean_object* v_ctorNames_2583_, lean_object* v_us_2584_, lean_object* v_params_2585_, lean_object* v_majorFVarId_2586_, size_t v_sz_2587_, size_t v_i_2588_, lean_object* v_bs_2589_){
_start:
{
uint8_t v___x_2590_; 
v___x_2590_ = lean_usize_dec_lt(v_i_2588_, v_sz_2587_);
if (v___x_2590_ == 0)
{
lean_dec(v_majorFVarId_2586_);
lean_dec(v_us_2584_);
return v_bs_2589_;
}
else
{
lean_object* v_v_2591_; lean_object* v___x_2592_; lean_object* v_bs_x27_2593_; lean_object* v___y_2595_; lean_object* v___x_2600_; lean_object* v___x_2601_; uint8_t v___x_2602_; 
v_v_2591_ = lean_array_uget(v_bs_2589_, v_i_2588_);
v___x_2592_ = lean_unsigned_to_nat(0u);
v_bs_x27_2593_ = lean_array_uset(v_bs_2589_, v_i_2588_, v___x_2592_);
v___x_2600_ = lean_usize_to_nat(v_i_2588_);
v___x_2601_ = lean_array_get_size(v_ctorNames_2583_);
v___x_2602_ = lean_nat_dec_lt(v___x_2600_, v___x_2601_);
if (v___x_2602_ == 0)
{
lean_object* v___x_2603_; lean_object* v___x_2604_; 
lean_dec(v___x_2600_);
v___x_2603_ = lean_box(0);
v___x_2604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2604_, 0, v_v_2591_);
lean_ctor_set(v___x_2604_, 1, v___x_2603_);
v___y_2595_ = v___x_2604_;
goto v___jp_2594_;
}
else
{
lean_object* v_mvarId_2605_; lean_object* v_fields_2606_; lean_object* v_subst_2607_; lean_object* v___x_2609_; uint8_t v_isShared_2610_; uint8_t v_isSharedCheck_2622_; 
v_mvarId_2605_ = lean_ctor_get(v_v_2591_, 0);
v_fields_2606_ = lean_ctor_get(v_v_2591_, 1);
v_subst_2607_ = lean_ctor_get(v_v_2591_, 2);
v_isSharedCheck_2622_ = !lean_is_exclusive(v_v_2591_);
if (v_isSharedCheck_2622_ == 0)
{
v___x_2609_ = v_v_2591_;
v_isShared_2610_ = v_isSharedCheck_2622_;
goto v_resetjp_2608_;
}
else
{
lean_inc(v_subst_2607_);
lean_inc(v_fields_2606_);
lean_inc(v_mvarId_2605_);
lean_dec(v_v_2591_);
v___x_2609_ = lean_box(0);
v_isShared_2610_ = v_isSharedCheck_2622_;
goto v_resetjp_2608_;
}
v_resetjp_2608_:
{
lean_object* v_ctorName_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v_ctorApp_2614_; lean_object* v___x_2615_; lean_object* v_subst_2616_; lean_object* v___x_2618_; 
v_ctorName_2611_ = lean_array_fget_borrowed(v_ctorNames_2583_, v___x_2600_);
lean_dec(v___x_2600_);
lean_inc(v_us_2584_);
lean_inc(v_ctorName_2611_);
v___x_2612_ = l_Lean_mkConst(v_ctorName_2611_, v_us_2584_);
v___x_2613_ = l_Lean_mkAppN(v___x_2612_, v_params_2585_);
v_ctorApp_2614_ = l_Lean_mkAppN(v___x_2613_, v_fields_2606_);
v___x_2615_ = l_Lean_Meta_FVarSubst_erase(v_subst_2607_, v_majorFVarId_2586_);
lean_inc(v_majorFVarId_2586_);
v_subst_2616_ = l_Lean_Meta_FVarSubst_insert(v___x_2615_, v_majorFVarId_2586_, v_ctorApp_2614_);
if (v_isShared_2610_ == 0)
{
lean_ctor_set(v___x_2609_, 2, v_subst_2616_);
v___x_2618_ = v___x_2609_;
goto v_reusejp_2617_;
}
else
{
lean_object* v_reuseFailAlloc_2621_; 
v_reuseFailAlloc_2621_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2621_, 0, v_mvarId_2605_);
lean_ctor_set(v_reuseFailAlloc_2621_, 1, v_fields_2606_);
lean_ctor_set(v_reuseFailAlloc_2621_, 2, v_subst_2616_);
v___x_2618_ = v_reuseFailAlloc_2621_;
goto v_reusejp_2617_;
}
v_reusejp_2617_:
{
lean_object* v___x_2619_; lean_object* v___x_2620_; 
lean_inc(v_ctorName_2611_);
v___x_2619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2619_, 0, v_ctorName_2611_);
v___x_2620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2620_, 0, v___x_2618_);
lean_ctor_set(v___x_2620_, 1, v___x_2619_);
v___y_2595_ = v___x_2620_;
goto v___jp_2594_;
}
}
}
v___jp_2594_:
{
size_t v___x_2596_; size_t v___x_2597_; lean_object* v___x_2598_; 
v___x_2596_ = ((size_t)1ULL);
v___x_2597_ = lean_usize_add(v_i_2588_, v___x_2596_);
v___x_2598_ = lean_array_uset(v_bs_x27_2593_, v_i_2588_, v___y_2595_);
v_i_2588_ = v___x_2597_;
v_bs_2589_ = v___x_2598_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorNames_2583_ = stack[0].m_obj;
lean_object* v_us_2584_ = stack[1].m_obj;
lean_object* v_params_2585_ = stack[2].m_obj;
lean_object* v_majorFVarId_2586_ = stack[3].m_obj;
size_t v_sz_2587_ = stack[4].m_num;
size_t v_i_2588_ = stack[5].m_num;
lean_object* v_bs_2589_ = stack[6].m_obj;
lean_object* v_res_2623_;
v_res_2623_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0___redArg(v_ctorNames_2583_, v_us_2584_, v_params_2585_, v_majorFVarId_2586_, v_sz_2587_, v_i_2588_, v_bs_2589_);
stack->m_obj
 = v_res_2623_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0___redArg___boxed(lean_object* v_ctorNames_2624_, lean_object* v_us_2625_, lean_object* v_params_2626_, lean_object* v_majorFVarId_2627_, lean_object* v_sz_2628_, lean_object* v_i_2629_, lean_object* v_bs_2630_){
_start:
{
size_t v_sz_boxed_2631_; size_t v_i_boxed_2632_; lean_object* v_res_2633_; 
v_sz_boxed_2631_ = lean_unbox_usize(v_sz_2628_);
lean_dec(v_sz_2628_);
v_i_boxed_2632_ = lean_unbox_usize(v_i_2629_);
lean_dec(v_i_2629_);
v_res_2633_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0___redArg(v_ctorNames_2624_, v_us_2625_, v_params_2626_, v_majorFVarId_2627_, v_sz_boxed_2631_, v_i_boxed_2632_, v_bs_2630_);
lean_dec_ref(v_params_2626_);
lean_dec_ref(v_ctorNames_2624_);
return v_res_2633_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals(lean_object* v_s_2634_, lean_object* v_ctorNames_2635_, lean_object* v_majorFVarId_2636_, lean_object* v_us_2637_, lean_object* v_params_2638_){
_start:
{
size_t v_sz_2639_; size_t v___x_2640_; lean_object* v___x_2641_; 
v_sz_2639_ = lean_array_size(v_s_2634_);
v___x_2640_ = ((size_t)0ULL);
v___x_2641_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0___redArg(v_ctorNames_2635_, v_us_2637_, v_params_2638_, v_majorFVarId_2636_, v_sz_2639_, v___x_2640_, v_s_2634_);
return v___x_2641_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals___boxed(lean_object* v_s_2642_, lean_object* v_ctorNames_2643_, lean_object* v_majorFVarId_2644_, lean_object* v_us_2645_, lean_object* v_params_2646_){
_start:
{
lean_object* v_res_2647_; 
v_res_2647_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals(v_s_2642_, v_ctorNames_2643_, v_majorFVarId_2644_, v_us_2645_, v_params_2646_);
lean_dec_ref(v_params_2646_);
lean_dec_ref(v_ctorNames_2643_);
return v_res_2647_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0(lean_object* v_ctorNames_2648_, lean_object* v_us_2649_, lean_object* v_params_2650_, lean_object* v_majorFVarId_2651_, lean_object* v_as_2652_, size_t v_sz_2653_, size_t v_i_2654_, lean_object* v_bs_2655_){
_start:
{
lean_object* v___x_2656_; 
v___x_2656_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0___redArg(v_ctorNames_2648_, v_us_2649_, v_params_2650_, v_majorFVarId_2651_, v_sz_2653_, v_i_2654_, v_bs_2655_);
return v___x_2656_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorNames_2648_ = stack[0].m_obj;
lean_object* v_us_2649_ = stack[1].m_obj;
lean_object* v_params_2650_ = stack[2].m_obj;
lean_object* v_majorFVarId_2651_ = stack[3].m_obj;
lean_object* v_as_2652_ = stack[4].m_obj;
size_t v_sz_2653_ = stack[5].m_num;
size_t v_i_2654_ = stack[6].m_num;
lean_object* v_bs_2655_ = stack[7].m_obj;
lean_object* v_res_2657_;
v_res_2657_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0(v_ctorNames_2648_, v_us_2649_, v_params_2650_, v_majorFVarId_2651_, v_as_2652_, v_sz_2653_, v_i_2654_, v_bs_2655_);
stack->m_obj
 = v_res_2657_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0___boxed(lean_object* v_ctorNames_2658_, lean_object* v_us_2659_, lean_object* v_params_2660_, lean_object* v_majorFVarId_2661_, lean_object* v_as_2662_, lean_object* v_sz_2663_, lean_object* v_i_2664_, lean_object* v_bs_2665_){
_start:
{
size_t v_sz_boxed_2666_; size_t v_i_boxed_2667_; lean_object* v_res_2668_; 
v_sz_boxed_2666_ = lean_unbox_usize(v_sz_2663_);
lean_dec(v_sz_2663_);
v_i_boxed_2667_ = lean_unbox_usize(v_i_2664_);
lean_dec(v_i_2664_);
v_res_2668_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0(v_ctorNames_2658_, v_us_2659_, v_params_2660_, v_majorFVarId_2661_, v_as_2662_, v_sz_boxed_2666_, v_i_boxed_2667_, v_bs_2665_);
lean_dec_ref(v_as_2662_);
lean_dec_ref(v_params_2660_);
lean_dec_ref(v_ctorNames_2658_);
return v_res_2668_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_2674_; lean_object* v___x_2675_; 
v___x_2674_ = l_Lean_maxRecDepthErrorMessage;
v___x_2675_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2675_, 0, v___x_2674_);
return v___x_2675_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_2676_; lean_object* v___x_2677_; 
v___x_2676_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__3);
v___x_2677_ = l_Lean_MessageData_ofFormat(v___x_2676_);
return v___x_2677_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; 
v___x_2678_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__4);
v___x_2679_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__2));
v___x_2680_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2680_, 0, v___x_2679_);
lean_ctor_set(v___x_2680_, 1, v___x_2678_);
return v___x_2680_;
}
}
lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg(lean_object* v_ref_2681_){
_start:
{
lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; 
v___x_2683_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__5);
v___x_2684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2684_, 0, v_ref_2681_);
lean_ctor_set(v___x_2684_, 1, v___x_2683_);
v___x_2685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2685_, 0, v___x_2684_);
return v___x_2685_;
}
}
LEAN_EXPORT void l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2681_ = stack[0].m_obj;
lean_object* v_res_2686_;
v_res_2686_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg(v_ref_2681_);
stack->m_obj
 = v_res_2686_;
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___boxed(lean_object* v_ref_2687_, lean_object* v___y_2688_){
_start:
{
lean_object* v_res_2689_; 
v_res_2689_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg(v_ref_2687_);
return v_res_2689_;
}
}
lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0(lean_object* v_00_u03b1_2690_, lean_object* v_ref_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_){
_start:
{
lean_object* v___x_2697_; 
v___x_2697_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg(v_ref_2691_);
return v___x_2697_;
}
}
LEAN_EXPORT void l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2691_ = stack[1].m_obj;
lean_object* v___y_2692_ = stack[2].m_obj;
lean_object* v___y_2693_ = stack[3].m_obj;
lean_object* v___y_2694_ = stack[4].m_obj;
lean_object* v___y_2695_ = stack[5].m_obj;
lean_object* v_res_2698_;
v_res_2698_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0(lean_box(0), v_ref_2691_, v___y_2692_, v___y_2693_, v___y_2694_, v___y_2695_);
stack->m_obj
 = v_res_2698_;
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___boxed(lean_object* v_00_u03b1_2699_, lean_object* v_ref_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_){
_start:
{
lean_object* v_res_2706_; 
v_res_2706_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0(v_00_u03b1_2699_, v_ref_2700_, v___y_2701_, v___y_2702_, v___y_2703_, v___y_2704_);
lean_dec(v___y_2704_);
lean_dec_ref(v___y_2703_);
lean_dec(v___y_2702_);
lean_dec_ref(v___y_2701_);
return v_res_2706_;
}
}
lean_object* l_Lean_Meta_Cases_unifyEqs_x3f(lean_object* v_numEqs_2708_, lean_object* v_mvarId_2709_, lean_object* v_subst_2710_, lean_object* v_caseName_x3f_2711_, lean_object* v_a_2712_, lean_object* v_a_2713_, lean_object* v_a_2714_, lean_object* v_a_2715_){
_start:
{
lean_object* v_toCold_2717_; lean_object* v_currRecDepth_2718_; lean_object* v_ref_2719_; uint16_t v_optionFlags_2720_; uint8_t v_suppressElabErrors_2721_; uint8_t v_isRecordingDeps_2722_; lean_object* v_maxRecDepth_2723_; lean_object* v___x_2724_; uint8_t v___x_2725_; uint8_t v___x_2771_; 
v_toCold_2717_ = lean_ctor_get(v_a_2714_, 0);
lean_inc_ref(v_toCold_2717_);
v_currRecDepth_2718_ = lean_ctor_get(v_a_2714_, 1);
lean_inc(v_currRecDepth_2718_);
v_ref_2719_ = lean_ctor_get(v_a_2714_, 2);
lean_inc(v_ref_2719_);
v_optionFlags_2720_ = lean_ctor_get_uint16(v_a_2714_, sizeof(void*)*3);
v_suppressElabErrors_2721_ = lean_ctor_get_uint8(v_a_2714_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2722_ = lean_ctor_get_uint8(v_a_2714_, sizeof(void*)*3 + 3);
lean_dec_ref(v_a_2714_);
v_maxRecDepth_2723_ = lean_ctor_get(v_toCold_2717_, 3);
v___x_2724_ = lean_unsigned_to_nat(0u);
v___x_2725_ = lean_nat_dec_eq(v_numEqs_2708_, v___x_2724_);
v___x_2771_ = lean_nat_dec_eq(v_maxRecDepth_2723_, v___x_2724_);
if (v___x_2771_ == 0)
{
uint8_t v___x_2772_; 
v___x_2772_ = lean_nat_dec_eq(v_currRecDepth_2718_, v_maxRecDepth_2723_);
if (v___x_2772_ == 0)
{
goto v___jp_2726_;
}
else
{
lean_object* v___x_2773_; 
lean_dec(v_currRecDepth_2718_);
lean_dec_ref(v_toCold_2717_);
lean_dec(v_caseName_x3f_2711_);
lean_dec(v_subst_2710_);
lean_dec(v_mvarId_2709_);
lean_dec(v_numEqs_2708_);
v___x_2773_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg(v_ref_2719_);
return v___x_2773_;
}
}
else
{
goto v___jp_2726_;
}
v___jp_2726_:
{
if (v___x_2725_ == 0)
{
lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; 
v___x_2727_ = lean_unsigned_to_nat(1u);
v___x_2728_ = lean_nat_add(v_currRecDepth_2718_, v___x_2727_);
lean_dec(v_currRecDepth_2718_);
v___x_2729_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2729_, 0, v_toCold_2717_);
lean_ctor_set(v___x_2729_, 1, v___x_2728_);
lean_ctor_set(v___x_2729_, 2, v_ref_2719_);
lean_ctor_set_uint16(v___x_2729_, sizeof(void*)*3, v_optionFlags_2720_);
lean_ctor_set_uint8(v___x_2729_, sizeof(void*)*3 + 2, v_suppressElabErrors_2721_);
lean_ctor_set_uint8(v___x_2729_, sizeof(void*)*3 + 3, v_isRecordingDeps_2722_);
v___x_2730_ = l_Lean_Meta_intro1Core(v_mvarId_2709_, v___x_2725_, v_a_2712_, v_a_2713_, v___x_2729_, v_a_2715_);
if (lean_obj_tag(v___x_2730_) == 0)
{
lean_object* v_a_2731_; lean_object* v_fst_2732_; lean_object* v_snd_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; 
v_a_2731_ = lean_ctor_get(v___x_2730_, 0);
lean_inc(v_a_2731_);
lean_dec_ref_known(v___x_2730_, 1);
v_fst_2732_ = lean_ctor_get(v_a_2731_, 0);
lean_inc(v_fst_2732_);
v_snd_2733_ = lean_ctor_get(v_a_2731_, 1);
lean_inc(v_snd_2733_);
lean_dec(v_a_2731_);
v___x_2734_ = ((lean_object*)(l_Lean_Meta_Cases_unifyEqs_x3f___closed__0));
lean_inc(v_caseName_x3f_2711_);
v___x_2735_ = l_Lean_Meta_unifyEq_x3f(v_snd_2733_, v_fst_2732_, v_subst_2710_, v___x_2734_, v_caseName_x3f_2711_, v_a_2712_, v_a_2713_, v___x_2729_, v_a_2715_);
if (lean_obj_tag(v___x_2735_) == 0)
{
lean_object* v_a_2736_; lean_object* v___x_2738_; uint8_t v_isShared_2739_; uint8_t v_isSharedCheck_2751_; 
v_a_2736_ = lean_ctor_get(v___x_2735_, 0);
v_isSharedCheck_2751_ = !lean_is_exclusive(v___x_2735_);
if (v_isSharedCheck_2751_ == 0)
{
v___x_2738_ = v___x_2735_;
v_isShared_2739_ = v_isSharedCheck_2751_;
goto v_resetjp_2737_;
}
else
{
lean_inc(v_a_2736_);
lean_dec(v___x_2735_);
v___x_2738_ = lean_box(0);
v_isShared_2739_ = v_isSharedCheck_2751_;
goto v_resetjp_2737_;
}
v_resetjp_2737_:
{
if (lean_obj_tag(v_a_2736_) == 1)
{
lean_object* v_val_2740_; lean_object* v_mvarId_2741_; lean_object* v_subst_2742_; lean_object* v_numNewEqs_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; 
lean_del_object(v___x_2738_);
v_val_2740_ = lean_ctor_get(v_a_2736_, 0);
lean_inc(v_val_2740_);
lean_dec_ref_known(v_a_2736_, 1);
v_mvarId_2741_ = lean_ctor_get(v_val_2740_, 0);
lean_inc(v_mvarId_2741_);
v_subst_2742_ = lean_ctor_get(v_val_2740_, 1);
lean_inc(v_subst_2742_);
v_numNewEqs_2743_ = lean_ctor_get(v_val_2740_, 2);
lean_inc(v_numNewEqs_2743_);
lean_dec(v_val_2740_);
v___x_2744_ = lean_nat_sub(v_numEqs_2708_, v___x_2727_);
lean_dec(v_numEqs_2708_);
v___x_2745_ = lean_nat_add(v___x_2744_, v_numNewEqs_2743_);
lean_dec(v_numNewEqs_2743_);
lean_dec(v___x_2744_);
v_numEqs_2708_ = v___x_2745_;
v_mvarId_2709_ = v_mvarId_2741_;
v_subst_2710_ = v_subst_2742_;
v_a_2714_ = v___x_2729_;
goto _start;
}
else
{
lean_object* v___x_2747_; lean_object* v___x_2749_; 
lean_dec(v_a_2736_);
lean_dec_ref_known(v___x_2729_, 3);
lean_dec(v_caseName_x3f_2711_);
lean_dec(v_numEqs_2708_);
v___x_2747_ = lean_box(0);
if (v_isShared_2739_ == 0)
{
lean_ctor_set(v___x_2738_, 0, v___x_2747_);
v___x_2749_ = v___x_2738_;
goto v_reusejp_2748_;
}
else
{
lean_object* v_reuseFailAlloc_2750_; 
v_reuseFailAlloc_2750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2750_, 0, v___x_2747_);
v___x_2749_ = v_reuseFailAlloc_2750_;
goto v_reusejp_2748_;
}
v_reusejp_2748_:
{
return v___x_2749_;
}
}
}
}
else
{
lean_object* v_a_2752_; lean_object* v___x_2754_; uint8_t v_isShared_2755_; uint8_t v_isSharedCheck_2759_; 
lean_dec_ref_known(v___x_2729_, 3);
lean_dec(v_caseName_x3f_2711_);
lean_dec(v_numEqs_2708_);
v_a_2752_ = lean_ctor_get(v___x_2735_, 0);
v_isSharedCheck_2759_ = !lean_is_exclusive(v___x_2735_);
if (v_isSharedCheck_2759_ == 0)
{
v___x_2754_ = v___x_2735_;
v_isShared_2755_ = v_isSharedCheck_2759_;
goto v_resetjp_2753_;
}
else
{
lean_inc(v_a_2752_);
lean_dec(v___x_2735_);
v___x_2754_ = lean_box(0);
v_isShared_2755_ = v_isSharedCheck_2759_;
goto v_resetjp_2753_;
}
v_resetjp_2753_:
{
lean_object* v___x_2757_; 
if (v_isShared_2755_ == 0)
{
v___x_2757_ = v___x_2754_;
goto v_reusejp_2756_;
}
else
{
lean_object* v_reuseFailAlloc_2758_; 
v_reuseFailAlloc_2758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2758_, 0, v_a_2752_);
v___x_2757_ = v_reuseFailAlloc_2758_;
goto v_reusejp_2756_;
}
v_reusejp_2756_:
{
return v___x_2757_;
}
}
}
}
else
{
lean_object* v_a_2760_; lean_object* v___x_2762_; uint8_t v_isShared_2763_; uint8_t v_isSharedCheck_2767_; 
lean_dec_ref_known(v___x_2729_, 3);
lean_dec(v_caseName_x3f_2711_);
lean_dec(v_subst_2710_);
lean_dec(v_numEqs_2708_);
v_a_2760_ = lean_ctor_get(v___x_2730_, 0);
v_isSharedCheck_2767_ = !lean_is_exclusive(v___x_2730_);
if (v_isSharedCheck_2767_ == 0)
{
v___x_2762_ = v___x_2730_;
v_isShared_2763_ = v_isSharedCheck_2767_;
goto v_resetjp_2761_;
}
else
{
lean_inc(v_a_2760_);
lean_dec(v___x_2730_);
v___x_2762_ = lean_box(0);
v_isShared_2763_ = v_isSharedCheck_2767_;
goto v_resetjp_2761_;
}
v_resetjp_2761_:
{
lean_object* v___x_2765_; 
if (v_isShared_2763_ == 0)
{
v___x_2765_ = v___x_2762_;
goto v_reusejp_2764_;
}
else
{
lean_object* v_reuseFailAlloc_2766_; 
v_reuseFailAlloc_2766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2766_, 0, v_a_2760_);
v___x_2765_ = v_reuseFailAlloc_2766_;
goto v_reusejp_2764_;
}
v_reusejp_2764_:
{
return v___x_2765_;
}
}
}
}
else
{
lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; 
lean_dec(v_ref_2719_);
lean_dec(v_currRecDepth_2718_);
lean_dec_ref(v_toCold_2717_);
lean_dec(v_caseName_x3f_2711_);
lean_dec(v_numEqs_2708_);
v___x_2768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2768_, 0, v_mvarId_2709_);
lean_ctor_set(v___x_2768_, 1, v_subst_2710_);
v___x_2769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2769_, 0, v___x_2768_);
v___x_2770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2770_, 0, v___x_2769_);
return v___x_2770_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Cases_unifyEqs_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_numEqs_2708_ = stack[0].m_obj;
lean_object* v_mvarId_2709_ = stack[1].m_obj;
lean_object* v_subst_2710_ = stack[2].m_obj;
lean_object* v_caseName_x3f_2711_ = stack[3].m_obj;
lean_object* v_a_2712_ = stack[4].m_obj;
lean_object* v_a_2713_ = stack[5].m_obj;
lean_object* v_a_2714_ = stack[6].m_obj;
lean_object* v_a_2715_ = stack[7].m_obj;
lean_object* v_res_2774_;
v_res_2774_ = l_Lean_Meta_Cases_unifyEqs_x3f(v_numEqs_2708_, v_mvarId_2709_, v_subst_2710_, v_caseName_x3f_2711_, v_a_2712_, v_a_2713_, v_a_2714_, v_a_2715_);
stack->m_obj
 = v_res_2774_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_unifyEqs_x3f___boxed(lean_object* v_numEqs_2775_, lean_object* v_mvarId_2776_, lean_object* v_subst_2777_, lean_object* v_caseName_x3f_2778_, lean_object* v_a_2779_, lean_object* v_a_2780_, lean_object* v_a_2781_, lean_object* v_a_2782_, lean_object* v_a_2783_){
_start:
{
lean_object* v_res_2784_; 
v_res_2784_ = l_Lean_Meta_Cases_unifyEqs_x3f(v_numEqs_2775_, v_mvarId_2776_, v_subst_2777_, v_caseName_x3f_2778_, v_a_2779_, v_a_2780_, v_a_2781_, v_a_2782_);
lean_dec(v_a_2782_);
lean_dec(v_a_2780_);
lean_dec_ref(v_a_2779_);
return v_res_2784_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__0(lean_object* v_snd_2785_, size_t v_sz_2786_, size_t v_i_2787_, lean_object* v_bs_2788_){
_start:
{
uint8_t v___x_2789_; 
v___x_2789_ = lean_usize_dec_lt(v_i_2787_, v_sz_2786_);
if (v___x_2789_ == 0)
{
lean_dec(v_snd_2785_);
return v_bs_2788_;
}
else
{
lean_object* v_v_2790_; lean_object* v___x_2791_; lean_object* v_bs_x27_2792_; lean_object* v___x_2793_; size_t v___x_2794_; size_t v___x_2795_; lean_object* v___x_2796_; 
v_v_2790_ = lean_array_uget(v_bs_2788_, v_i_2787_);
v___x_2791_ = lean_unsigned_to_nat(0u);
v_bs_x27_2792_ = lean_array_uset(v_bs_2788_, v_i_2787_, v___x_2791_);
lean_inc(v_snd_2785_);
v___x_2793_ = l_Lean_Meta_FVarSubst_apply(v_snd_2785_, v_v_2790_);
lean_dec(v_v_2790_);
v___x_2794_ = ((size_t)1ULL);
v___x_2795_ = lean_usize_add(v_i_2787_, v___x_2794_);
v___x_2796_ = lean_array_uset(v_bs_x27_2792_, v_i_2787_, v___x_2793_);
v_i_2787_ = v___x_2795_;
v_bs_2788_ = v___x_2796_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_snd_2785_ = stack[0].m_obj;
size_t v_sz_2786_ = stack[1].m_num;
size_t v_i_2787_ = stack[2].m_num;
lean_object* v_bs_2788_ = stack[3].m_obj;
lean_object* v_res_2798_;
v_res_2798_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__0(v_snd_2785_, v_sz_2786_, v_i_2787_, v_bs_2788_);
stack->m_obj
 = v_res_2798_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__0___boxed(lean_object* v_snd_2799_, lean_object* v_sz_2800_, lean_object* v_i_2801_, lean_object* v_bs_2802_){
_start:
{
size_t v_sz_boxed_2803_; size_t v_i_boxed_2804_; lean_object* v_res_2805_; 
v_sz_boxed_2803_ = lean_unbox_usize(v_sz_2800_);
lean_dec(v_sz_2800_);
v_i_boxed_2804_ = lean_unbox_usize(v_i_2801_);
lean_dec(v_i_2801_);
v_res_2805_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__0(v_snd_2799_, v_sz_boxed_2803_, v_i_boxed_2804_, v_bs_2802_);
return v_res_2805_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1_spec__1(lean_object* v_numEqs_2806_, lean_object* v_as_2807_, size_t v_i_2808_, size_t v_stop_2809_, lean_object* v_b_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_){
_start:
{
lean_object* v_a_2817_; uint8_t v___x_2821_; 
v___x_2821_ = lean_usize_dec_eq(v_i_2808_, v_stop_2809_);
if (v___x_2821_ == 0)
{
lean_object* v___x_2822_; lean_object* v_toInductionSubgoal_2823_; lean_object* v_ctorName_2824_; lean_object* v___x_2826_; uint8_t v_isShared_2827_; uint8_t v_isSharedCheck_2858_; 
v___x_2822_ = lean_array_uget(v_as_2807_, v_i_2808_);
v_toInductionSubgoal_2823_ = lean_ctor_get(v___x_2822_, 0);
v_ctorName_2824_ = lean_ctor_get(v___x_2822_, 1);
v_isSharedCheck_2858_ = !lean_is_exclusive(v___x_2822_);
if (v_isSharedCheck_2858_ == 0)
{
v___x_2826_ = v___x_2822_;
v_isShared_2827_ = v_isSharedCheck_2858_;
goto v_resetjp_2825_;
}
else
{
lean_inc(v_ctorName_2824_);
lean_inc(v_toInductionSubgoal_2823_);
lean_dec(v___x_2822_);
v___x_2826_ = lean_box(0);
v_isShared_2827_ = v_isSharedCheck_2858_;
goto v_resetjp_2825_;
}
v_resetjp_2825_:
{
lean_object* v_mvarId_2828_; lean_object* v_fields_2829_; lean_object* v_subst_2830_; lean_object* v___x_2832_; uint8_t v_isShared_2833_; uint8_t v_isSharedCheck_2857_; 
v_mvarId_2828_ = lean_ctor_get(v_toInductionSubgoal_2823_, 0);
v_fields_2829_ = lean_ctor_get(v_toInductionSubgoal_2823_, 1);
v_subst_2830_ = lean_ctor_get(v_toInductionSubgoal_2823_, 2);
v_isSharedCheck_2857_ = !lean_is_exclusive(v_toInductionSubgoal_2823_);
if (v_isSharedCheck_2857_ == 0)
{
v___x_2832_ = v_toInductionSubgoal_2823_;
v_isShared_2833_ = v_isSharedCheck_2857_;
goto v_resetjp_2831_;
}
else
{
lean_inc(v_subst_2830_);
lean_inc(v_fields_2829_);
lean_inc(v_mvarId_2828_);
lean_dec(v_toInductionSubgoal_2823_);
v___x_2832_ = lean_box(0);
v_isShared_2833_ = v_isSharedCheck_2857_;
goto v_resetjp_2831_;
}
v_resetjp_2831_:
{
lean_object* v___x_2834_; 
lean_inc_ref(v___y_2813_);
lean_inc(v_ctorName_2824_);
lean_inc(v_numEqs_2806_);
v___x_2834_ = l_Lean_Meta_Cases_unifyEqs_x3f(v_numEqs_2806_, v_mvarId_2828_, v_subst_2830_, v_ctorName_2824_, v___y_2811_, v___y_2812_, v___y_2813_, v___y_2814_);
if (lean_obj_tag(v___x_2834_) == 0)
{
lean_object* v_a_2835_; 
v_a_2835_ = lean_ctor_get(v___x_2834_, 0);
lean_inc(v_a_2835_);
lean_dec_ref_known(v___x_2834_, 1);
if (lean_obj_tag(v_a_2835_) == 0)
{
lean_del_object(v___x_2832_);
lean_dec_ref(v_fields_2829_);
lean_del_object(v___x_2826_);
lean_dec(v_ctorName_2824_);
v_a_2817_ = v_b_2810_;
goto v___jp_2816_;
}
else
{
lean_object* v_val_2836_; lean_object* v_fst_2837_; lean_object* v_snd_2838_; size_t v_sz_2839_; size_t v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2843_; 
v_val_2836_ = lean_ctor_get(v_a_2835_, 0);
lean_inc(v_val_2836_);
lean_dec_ref_known(v_a_2835_, 1);
v_fst_2837_ = lean_ctor_get(v_val_2836_, 0);
lean_inc(v_fst_2837_);
v_snd_2838_ = lean_ctor_get(v_val_2836_, 1);
lean_inc_n(v_snd_2838_, 2);
lean_dec(v_val_2836_);
v_sz_2839_ = lean_array_size(v_fields_2829_);
v___x_2840_ = ((size_t)0ULL);
v___x_2841_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__0(v_snd_2838_, v_sz_2839_, v___x_2840_, v_fields_2829_);
if (v_isShared_2833_ == 0)
{
lean_ctor_set(v___x_2832_, 2, v_snd_2838_);
lean_ctor_set(v___x_2832_, 1, v___x_2841_);
lean_ctor_set(v___x_2832_, 0, v_fst_2837_);
v___x_2843_ = v___x_2832_;
goto v_reusejp_2842_;
}
else
{
lean_object* v_reuseFailAlloc_2848_; 
v_reuseFailAlloc_2848_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2848_, 0, v_fst_2837_);
lean_ctor_set(v_reuseFailAlloc_2848_, 1, v___x_2841_);
lean_ctor_set(v_reuseFailAlloc_2848_, 2, v_snd_2838_);
v___x_2843_ = v_reuseFailAlloc_2848_;
goto v_reusejp_2842_;
}
v_reusejp_2842_:
{
lean_object* v___x_2845_; 
if (v_isShared_2827_ == 0)
{
lean_ctor_set(v___x_2826_, 0, v___x_2843_);
v___x_2845_ = v___x_2826_;
goto v_reusejp_2844_;
}
else
{
lean_object* v_reuseFailAlloc_2847_; 
v_reuseFailAlloc_2847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2847_, 0, v___x_2843_);
lean_ctor_set(v_reuseFailAlloc_2847_, 1, v_ctorName_2824_);
v___x_2845_ = v_reuseFailAlloc_2847_;
goto v_reusejp_2844_;
}
v_reusejp_2844_:
{
lean_object* v___x_2846_; 
v___x_2846_ = lean_array_push(v_b_2810_, v___x_2845_);
v_a_2817_ = v___x_2846_;
goto v___jp_2816_;
}
}
}
}
else
{
lean_object* v_a_2849_; lean_object* v___x_2851_; uint8_t v_isShared_2852_; uint8_t v_isSharedCheck_2856_; 
lean_del_object(v___x_2832_);
lean_dec_ref(v_fields_2829_);
lean_del_object(v___x_2826_);
lean_dec(v_ctorName_2824_);
lean_dec_ref(v_b_2810_);
lean_dec(v_numEqs_2806_);
v_a_2849_ = lean_ctor_get(v___x_2834_, 0);
v_isSharedCheck_2856_ = !lean_is_exclusive(v___x_2834_);
if (v_isSharedCheck_2856_ == 0)
{
v___x_2851_ = v___x_2834_;
v_isShared_2852_ = v_isSharedCheck_2856_;
goto v_resetjp_2850_;
}
else
{
lean_inc(v_a_2849_);
lean_dec(v___x_2834_);
v___x_2851_ = lean_box(0);
v_isShared_2852_ = v_isSharedCheck_2856_;
goto v_resetjp_2850_;
}
v_resetjp_2850_:
{
lean_object* v___x_2854_; 
if (v_isShared_2852_ == 0)
{
v___x_2854_ = v___x_2851_;
goto v_reusejp_2853_;
}
else
{
lean_object* v_reuseFailAlloc_2855_; 
v_reuseFailAlloc_2855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2855_, 0, v_a_2849_);
v___x_2854_ = v_reuseFailAlloc_2855_;
goto v_reusejp_2853_;
}
v_reusejp_2853_:
{
return v___x_2854_;
}
}
}
}
}
}
else
{
lean_object* v___x_2859_; 
lean_dec(v_numEqs_2806_);
v___x_2859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2859_, 0, v_b_2810_);
return v___x_2859_;
}
v___jp_2816_:
{
size_t v___x_2818_; size_t v___x_2819_; 
v___x_2818_ = ((size_t)1ULL);
v___x_2819_ = lean_usize_add(v_i_2808_, v___x_2818_);
v_i_2808_ = v___x_2819_;
v_b_2810_ = v_a_2817_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_numEqs_2806_ = stack[0].m_obj;
lean_object* v_as_2807_ = stack[1].m_obj;
size_t v_i_2808_ = stack[2].m_num;
size_t v_stop_2809_ = stack[3].m_num;
lean_object* v_b_2810_ = stack[4].m_obj;
lean_object* v___y_2811_ = stack[5].m_obj;
lean_object* v___y_2812_ = stack[6].m_obj;
lean_object* v___y_2813_ = stack[7].m_obj;
lean_object* v___y_2814_ = stack[8].m_obj;
lean_object* v_res_2860_;
v_res_2860_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1_spec__1(v_numEqs_2806_, v_as_2807_, v_i_2808_, v_stop_2809_, v_b_2810_, v___y_2811_, v___y_2812_, v___y_2813_, v___y_2814_);
stack->m_obj
 = v_res_2860_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1_spec__1___boxed(lean_object* v_numEqs_2861_, lean_object* v_as_2862_, lean_object* v_i_2863_, lean_object* v_stop_2864_, lean_object* v_b_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_){
_start:
{
size_t v_i_boxed_2871_; size_t v_stop_boxed_2872_; lean_object* v_res_2873_; 
v_i_boxed_2871_ = lean_unbox_usize(v_i_2863_);
lean_dec(v_i_2863_);
v_stop_boxed_2872_ = lean_unbox_usize(v_stop_2864_);
lean_dec(v_stop_2864_);
v_res_2873_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1_spec__1(v_numEqs_2861_, v_as_2862_, v_i_boxed_2871_, v_stop_boxed_2872_, v_b_2865_, v___y_2866_, v___y_2867_, v___y_2868_, v___y_2869_);
lean_dec(v___y_2869_);
lean_dec_ref(v___y_2868_);
lean_dec(v___y_2867_);
lean_dec_ref(v___y_2866_);
lean_dec_ref(v_as_2862_);
return v_res_2873_;
}
}
lean_object* l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1(lean_object* v_numEqs_2876_, lean_object* v_as_2877_, lean_object* v_start_2878_, lean_object* v_stop_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_){
_start:
{
lean_object* v___x_2885_; uint8_t v___x_2886_; 
v___x_2885_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1___closed__0));
v___x_2886_ = lean_nat_dec_lt(v_start_2878_, v_stop_2879_);
if (v___x_2886_ == 0)
{
lean_object* v___x_2887_; 
lean_dec(v_numEqs_2876_);
v___x_2887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2887_, 0, v___x_2885_);
return v___x_2887_;
}
else
{
lean_object* v___x_2888_; uint8_t v___x_2889_; 
v___x_2888_ = lean_array_get_size(v_as_2877_);
v___x_2889_ = lean_nat_dec_le(v_stop_2879_, v___x_2888_);
if (v___x_2889_ == 0)
{
uint8_t v___x_2890_; 
v___x_2890_ = lean_nat_dec_lt(v_start_2878_, v___x_2888_);
if (v___x_2890_ == 0)
{
lean_object* v___x_2891_; 
lean_dec(v_numEqs_2876_);
v___x_2891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2891_, 0, v___x_2885_);
return v___x_2891_;
}
else
{
size_t v___x_2892_; size_t v___x_2893_; lean_object* v___x_2894_; 
v___x_2892_ = lean_usize_of_nat(v_start_2878_);
v___x_2893_ = lean_usize_of_nat(v___x_2888_);
v___x_2894_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1_spec__1(v_numEqs_2876_, v_as_2877_, v___x_2892_, v___x_2893_, v___x_2885_, v___y_2880_, v___y_2881_, v___y_2882_, v___y_2883_);
return v___x_2894_;
}
}
else
{
size_t v___x_2895_; size_t v___x_2896_; lean_object* v___x_2897_; 
v___x_2895_ = lean_usize_of_nat(v_start_2878_);
v___x_2896_ = lean_usize_of_nat(v_stop_2879_);
v___x_2897_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1_spec__1(v_numEqs_2876_, v_as_2877_, v___x_2895_, v___x_2896_, v___x_2885_, v___y_2880_, v___y_2881_, v___y_2882_, v___y_2883_);
return v___x_2897_;
}
}
}
}
LEAN_EXPORT void l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_numEqs_2876_ = stack[0].m_obj;
lean_object* v_as_2877_ = stack[1].m_obj;
lean_object* v_start_2878_ = stack[2].m_obj;
lean_object* v_stop_2879_ = stack[3].m_obj;
lean_object* v___y_2880_ = stack[4].m_obj;
lean_object* v___y_2881_ = stack[5].m_obj;
lean_object* v___y_2882_ = stack[6].m_obj;
lean_object* v___y_2883_ = stack[7].m_obj;
lean_object* v_res_2898_;
v_res_2898_ = l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1(v_numEqs_2876_, v_as_2877_, v_start_2878_, v_stop_2879_, v___y_2880_, v___y_2881_, v___y_2882_, v___y_2883_);
stack->m_obj
 = v_res_2898_;
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1___boxed(lean_object* v_numEqs_2899_, lean_object* v_as_2900_, lean_object* v_start_2901_, lean_object* v_stop_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_){
_start:
{
lean_object* v_res_2908_; 
v_res_2908_ = l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1(v_numEqs_2899_, v_as_2900_, v_start_2901_, v_stop_2902_, v___y_2903_, v___y_2904_, v___y_2905_, v___y_2906_);
lean_dec(v___y_2906_);
lean_dec_ref(v___y_2905_);
lean_dec(v___y_2904_);
lean_dec_ref(v___y_2903_);
lean_dec(v_stop_2902_);
lean_dec(v_start_2901_);
lean_dec_ref(v_as_2900_);
return v_res_2908_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs(lean_object* v_numEqs_2909_, lean_object* v_subgoals_2910_, lean_object* v_a_2911_, lean_object* v_a_2912_, lean_object* v_a_2913_, lean_object* v_a_2914_){
_start:
{
lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; 
v___x_2916_ = lean_unsigned_to_nat(0u);
v___x_2917_ = lean_array_get_size(v_subgoals_2910_);
v___x_2918_ = l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1(v_numEqs_2909_, v_subgoals_2910_, v___x_2916_, v___x_2917_, v_a_2911_, v_a_2912_, v_a_2913_, v_a_2914_);
return v___x_2918_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_0interp(lean_interpreter_value* stack)
{
lean_object* v_numEqs_2909_ = stack[0].m_obj;
lean_object* v_subgoals_2910_ = stack[1].m_obj;
lean_object* v_a_2911_ = stack[2].m_obj;
lean_object* v_a_2912_ = stack[3].m_obj;
lean_object* v_a_2913_ = stack[4].m_obj;
lean_object* v_a_2914_ = stack[5].m_obj;
lean_object* v_res_2919_;
v_res_2919_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs(v_numEqs_2909_, v_subgoals_2910_, v_a_2911_, v_a_2912_, v_a_2913_, v_a_2914_);
stack->m_obj
 = v_res_2919_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs___boxed(lean_object* v_numEqs_2920_, lean_object* v_subgoals_2921_, lean_object* v_a_2922_, lean_object* v_a_2923_, lean_object* v_a_2924_, lean_object* v_a_2925_, lean_object* v_a_2926_){
_start:
{
lean_object* v_res_2927_; 
v_res_2927_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs(v_numEqs_2920_, v_subgoals_2921_, v_a_2922_, v_a_2923_, v_a_2924_, v_a_2925_);
lean_dec(v_a_2925_);
lean_dec_ref(v_a_2924_);
lean_dec(v_a_2923_);
lean_dec_ref(v_a_2922_);
lean_dec_ref(v_subgoals_2921_);
return v_res_2927_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0(lean_object* v___x_2939_, lean_object* v_ctx_2940_, lean_object* v_mvarId_2941_, lean_object* v_majorFVarId_2942_, lean_object* v_givenNames_2943_, uint8_t v_useNatCasesAuxOn_2944_, lean_object* v_interestingCtors_x3f_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_){
_start:
{
lean_object* v___x_2951_; 
lean_inc(v___y_2949_);
lean_inc_ref(v___y_2948_);
lean_inc(v___y_2947_);
lean_inc_ref(v___y_2946_);
v___x_2951_ = lean_infer_type(v___x_2939_, v___y_2946_, v___y_2947_, v___y_2948_, v___y_2949_);
if (lean_obj_tag(v___x_2951_) == 0)
{
lean_object* v_a_2952_; lean_object* v___x_2953_; 
v_a_2952_ = lean_ctor_get(v___x_2951_, 0);
lean_inc(v_a_2952_);
lean_dec_ref_known(v___x_2951_, 1);
v___x_2953_ = l_Lean_Meta_getInductiveUniverseAndParams(v_a_2952_, v___y_2946_, v___y_2947_, v___y_2948_, v___y_2949_);
if (lean_obj_tag(v___x_2953_) == 0)
{
lean_object* v_a_2954_; lean_object* v_fst_2955_; lean_object* v_snd_2956_; lean_object* v___y_2958_; lean_object* v___y_2959_; lean_object* v___y_2960_; lean_object* v___y_2961_; lean_object* v___y_2962_; lean_object* v___y_2985_; lean_object* v___y_2986_; lean_object* v___y_2987_; lean_object* v___y_2988_; lean_object* v___y_2994_; lean_object* v___y_2995_; lean_object* v___y_2996_; lean_object* v___y_2997_; 
v_a_2954_ = lean_ctor_get(v___x_2953_, 0);
lean_inc(v_a_2954_);
lean_dec_ref_known(v___x_2953_, 1);
v_fst_2955_ = lean_ctor_get(v_a_2954_, 0);
lean_inc(v_fst_2955_);
v_snd_2956_ = lean_ctor_get(v_a_2954_, 1);
lean_inc(v_snd_2956_);
lean_dec(v_a_2954_);
if (lean_obj_tag(v_interestingCtors_x3f_2945_) == 1)
{
lean_object* v_val_3007_; lean_object* v___x_3008_; lean_object* v_env_3009_; lean_object* v___x_3010_; uint8_t v___x_3011_; uint8_t v___x_3012_; lean_object* v___x_3013_; lean_object* v_inductiveVal_3014_; lean_object* v_toConstantVal_3015_; lean_object* v_ctors_3016_; lean_object* v_name_3017_; uint8_t v___y_3019_; 
v_val_3007_ = lean_ctor_get(v_interestingCtors_x3f_2945_, 0);
lean_inc(v_val_3007_);
lean_dec_ref_known(v_interestingCtors_x3f_2945_, 1);
v___x_3008_ = lean_st_ref_get(v___y_2949_);
v_env_3009_ = lean_ctor_get(v___x_3008_, 0);
lean_inc_ref(v_env_3009_);
lean_dec(v___x_3008_);
v___x_3010_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__5));
v___x_3011_ = 1;
v___x_3012_ = l_Lean_Environment_contains(v_env_3009_, v___x_3010_, v___x_3011_);
v___x_3013_ = lean_st_ref_get(v___y_2949_);
v_inductiveVal_3014_ = lean_ctor_get(v_ctx_2940_, 0);
v_toConstantVal_3015_ = lean_ctor_get(v_inductiveVal_3014_, 0);
v_ctors_3016_ = lean_ctor_get(v_inductiveVal_3014_, 4);
v_name_3017_ = lean_ctor_get(v_toConstantVal_3015_, 0);
if (v___x_3012_ == 0)
{
lean_dec(v___x_3013_);
v___y_3019_ = v___x_3012_;
goto v___jp_3018_;
}
else
{
lean_object* v_env_3053_; lean_object* v___x_3054_; uint8_t v___x_3055_; 
v_env_3053_ = lean_ctor_get(v___x_3013_, 0);
lean_inc_ref(v_env_3053_);
lean_dec(v___x_3013_);
lean_inc(v_name_3017_);
v___x_3054_ = l_Lean_mkCtorIdxName(v_name_3017_);
v___x_3055_ = l_Lean_Environment_contains(v_env_3053_, v___x_3054_, v___x_3011_);
v___y_3019_ = v___x_3055_;
goto v___jp_3018_;
}
v___jp_3018_:
{
if (v___y_3019_ == 0)
{
lean_dec(v_val_3007_);
v___y_2994_ = v___y_2946_;
v___y_2995_ = v___y_2947_;
v___y_2996_ = v___y_2948_;
v___y_2997_ = v___y_2949_;
goto v___jp_2993_;
}
else
{
lean_object* v___x_3020_; lean_object* v___x_3021_; uint8_t v___x_3022_; 
v___x_3020_ = lean_array_get_size(v_val_3007_);
v___x_3021_ = lean_unsigned_to_nat(0u);
v___x_3022_ = lean_nat_dec_eq(v___x_3020_, v___x_3021_);
if (v___x_3022_ == 0)
{
lean_object* v___x_3023_; uint8_t v___x_3024_; 
v___x_3023_ = l_List_lengthTR___redArg(v_ctors_3016_);
v___x_3024_ = lean_nat_dec_lt(v___x_3020_, v___x_3023_);
lean_dec(v___x_3023_);
if (v___x_3024_ == 0)
{
lean_dec(v_val_3007_);
v___y_2994_ = v___y_2946_;
v___y_2995_ = v___y_2947_;
v___y_2996_ = v___y_2948_;
v___y_2997_ = v___y_2949_;
goto v___jp_2993_;
}
else
{
lean_object* v___x_3025_; 
lean_inc(v_name_3017_);
lean_dec_ref(v_ctx_2940_);
lean_inc(v_val_3007_);
v___x_3025_ = l_Lean_Meta_mkSparseCasesOn(v_name_3017_, v_val_3007_, v___y_2946_, v___y_2947_, v___y_2948_, v___y_2949_);
if (lean_obj_tag(v___x_3025_) == 0)
{
lean_object* v_a_3026_; lean_object* v___x_3027_; 
v_a_3026_ = lean_ctor_get(v___x_3025_, 0);
lean_inc(v_a_3026_);
lean_dec_ref_known(v___x_3025_, 1);
lean_inc(v_majorFVarId_2942_);
v___x_3027_ = l_Lean_MVarId_induction(v_mvarId_2941_, v_majorFVarId_2942_, v_a_3026_, v_givenNames_2943_, v___y_2946_, v___y_2947_, v___y_2948_, v___y_2949_);
lean_dec(v___y_2949_);
lean_dec_ref(v___y_2948_);
lean_dec(v___y_2947_);
lean_dec_ref(v___y_2946_);
if (lean_obj_tag(v___x_3027_) == 0)
{
lean_object* v_a_3028_; lean_object* v___x_3030_; uint8_t v_isShared_3031_; uint8_t v_isSharedCheck_3036_; 
v_a_3028_ = lean_ctor_get(v___x_3027_, 0);
v_isSharedCheck_3036_ = !lean_is_exclusive(v___x_3027_);
if (v_isSharedCheck_3036_ == 0)
{
v___x_3030_ = v___x_3027_;
v_isShared_3031_ = v_isSharedCheck_3036_;
goto v_resetjp_3029_;
}
else
{
lean_inc(v_a_3028_);
lean_dec(v___x_3027_);
v___x_3030_ = lean_box(0);
v_isShared_3031_ = v_isSharedCheck_3036_;
goto v_resetjp_3029_;
}
v_resetjp_3029_:
{
lean_object* v___x_3032_; lean_object* v___x_3034_; 
v___x_3032_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals(v_a_3028_, v_val_3007_, v_majorFVarId_2942_, v_fst_2955_, v_snd_2956_);
lean_dec(v_snd_2956_);
lean_dec(v_val_3007_);
if (v_isShared_3031_ == 0)
{
lean_ctor_set(v___x_3030_, 0, v___x_3032_);
v___x_3034_ = v___x_3030_;
goto v_reusejp_3033_;
}
else
{
lean_object* v_reuseFailAlloc_3035_; 
v_reuseFailAlloc_3035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3035_, 0, v___x_3032_);
v___x_3034_ = v_reuseFailAlloc_3035_;
goto v_reusejp_3033_;
}
v_reusejp_3033_:
{
return v___x_3034_;
}
}
}
else
{
lean_object* v_a_3037_; lean_object* v___x_3039_; uint8_t v_isShared_3040_; uint8_t v_isSharedCheck_3044_; 
lean_dec(v_val_3007_);
lean_dec(v_snd_2956_);
lean_dec(v_fst_2955_);
lean_dec(v_majorFVarId_2942_);
v_a_3037_ = lean_ctor_get(v___x_3027_, 0);
v_isSharedCheck_3044_ = !lean_is_exclusive(v___x_3027_);
if (v_isSharedCheck_3044_ == 0)
{
v___x_3039_ = v___x_3027_;
v_isShared_3040_ = v_isSharedCheck_3044_;
goto v_resetjp_3038_;
}
else
{
lean_inc(v_a_3037_);
lean_dec(v___x_3027_);
v___x_3039_ = lean_box(0);
v_isShared_3040_ = v_isSharedCheck_3044_;
goto v_resetjp_3038_;
}
v_resetjp_3038_:
{
lean_object* v___x_3042_; 
if (v_isShared_3040_ == 0)
{
v___x_3042_ = v___x_3039_;
goto v_reusejp_3041_;
}
else
{
lean_object* v_reuseFailAlloc_3043_; 
v_reuseFailAlloc_3043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3043_, 0, v_a_3037_);
v___x_3042_ = v_reuseFailAlloc_3043_;
goto v_reusejp_3041_;
}
v_reusejp_3041_:
{
return v___x_3042_;
}
}
}
}
else
{
lean_object* v_a_3045_; lean_object* v___x_3047_; uint8_t v_isShared_3048_; uint8_t v_isSharedCheck_3052_; 
lean_dec(v_val_3007_);
lean_dec(v_snd_2956_);
lean_dec(v_fst_2955_);
lean_dec(v___y_2949_);
lean_dec_ref(v___y_2948_);
lean_dec(v___y_2947_);
lean_dec_ref(v___y_2946_);
lean_dec_ref(v_givenNames_2943_);
lean_dec(v_majorFVarId_2942_);
lean_dec(v_mvarId_2941_);
v_a_3045_ = lean_ctor_get(v___x_3025_, 0);
v_isSharedCheck_3052_ = !lean_is_exclusive(v___x_3025_);
if (v_isSharedCheck_3052_ == 0)
{
v___x_3047_ = v___x_3025_;
v_isShared_3048_ = v_isSharedCheck_3052_;
goto v_resetjp_3046_;
}
else
{
lean_inc(v_a_3045_);
lean_dec(v___x_3025_);
v___x_3047_ = lean_box(0);
v_isShared_3048_ = v_isSharedCheck_3052_;
goto v_resetjp_3046_;
}
v_resetjp_3046_:
{
lean_object* v___x_3050_; 
if (v_isShared_3048_ == 0)
{
v___x_3050_ = v___x_3047_;
goto v_reusejp_3049_;
}
else
{
lean_object* v_reuseFailAlloc_3051_; 
v_reuseFailAlloc_3051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3051_, 0, v_a_3045_);
v___x_3050_ = v_reuseFailAlloc_3051_;
goto v_reusejp_3049_;
}
v_reusejp_3049_:
{
return v___x_3050_;
}
}
}
}
}
else
{
lean_dec(v_val_3007_);
v___y_2994_ = v___y_2946_;
v___y_2995_ = v___y_2947_;
v___y_2996_ = v___y_2948_;
v___y_2997_ = v___y_2949_;
goto v___jp_2993_;
}
}
}
}
else
{
lean_dec(v_interestingCtors_x3f_2945_);
v___y_2994_ = v___y_2946_;
v___y_2995_ = v___y_2947_;
v___y_2996_ = v___y_2948_;
v___y_2997_ = v___y_2949_;
goto v___jp_2993_;
}
v___jp_2957_:
{
lean_object* v_inductiveVal_2963_; lean_object* v_ctors_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; 
v_inductiveVal_2963_ = lean_ctor_get(v_ctx_2940_, 0);
lean_inc_ref(v_inductiveVal_2963_);
lean_dec_ref(v_ctx_2940_);
v_ctors_2964_ = lean_ctor_get(v_inductiveVal_2963_, 4);
lean_inc(v_ctors_2964_);
lean_dec_ref(v_inductiveVal_2963_);
v___x_2965_ = lean_array_mk(v_ctors_2964_);
lean_inc(v_majorFVarId_2942_);
v___x_2966_ = l_Lean_MVarId_induction(v_mvarId_2941_, v_majorFVarId_2942_, v___y_2962_, v_givenNames_2943_, v___y_2958_, v___y_2959_, v___y_2960_, v___y_2961_);
lean_dec(v___y_2961_);
lean_dec_ref(v___y_2960_);
lean_dec(v___y_2959_);
lean_dec_ref(v___y_2958_);
if (lean_obj_tag(v___x_2966_) == 0)
{
lean_object* v_a_2967_; lean_object* v___x_2969_; uint8_t v_isShared_2970_; uint8_t v_isSharedCheck_2975_; 
v_a_2967_ = lean_ctor_get(v___x_2966_, 0);
v_isSharedCheck_2975_ = !lean_is_exclusive(v___x_2966_);
if (v_isSharedCheck_2975_ == 0)
{
v___x_2969_ = v___x_2966_;
v_isShared_2970_ = v_isSharedCheck_2975_;
goto v_resetjp_2968_;
}
else
{
lean_inc(v_a_2967_);
lean_dec(v___x_2966_);
v___x_2969_ = lean_box(0);
v_isShared_2970_ = v_isSharedCheck_2975_;
goto v_resetjp_2968_;
}
v_resetjp_2968_:
{
lean_object* v___x_2971_; lean_object* v___x_2973_; 
v___x_2971_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals(v_a_2967_, v___x_2965_, v_majorFVarId_2942_, v_fst_2955_, v_snd_2956_);
lean_dec(v_snd_2956_);
lean_dec_ref(v___x_2965_);
if (v_isShared_2970_ == 0)
{
lean_ctor_set(v___x_2969_, 0, v___x_2971_);
v___x_2973_ = v___x_2969_;
goto v_reusejp_2972_;
}
else
{
lean_object* v_reuseFailAlloc_2974_; 
v_reuseFailAlloc_2974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2974_, 0, v___x_2971_);
v___x_2973_ = v_reuseFailAlloc_2974_;
goto v_reusejp_2972_;
}
v_reusejp_2972_:
{
return v___x_2973_;
}
}
}
else
{
lean_object* v_a_2976_; lean_object* v___x_2978_; uint8_t v_isShared_2979_; uint8_t v_isSharedCheck_2983_; 
lean_dec_ref(v___x_2965_);
lean_dec(v_snd_2956_);
lean_dec(v_fst_2955_);
lean_dec(v_majorFVarId_2942_);
v_a_2976_ = lean_ctor_get(v___x_2966_, 0);
v_isSharedCheck_2983_ = !lean_is_exclusive(v___x_2966_);
if (v_isSharedCheck_2983_ == 0)
{
v___x_2978_ = v___x_2966_;
v_isShared_2979_ = v_isSharedCheck_2983_;
goto v_resetjp_2977_;
}
else
{
lean_inc(v_a_2976_);
lean_dec(v___x_2966_);
v___x_2978_ = lean_box(0);
v_isShared_2979_ = v_isSharedCheck_2983_;
goto v_resetjp_2977_;
}
v_resetjp_2977_:
{
lean_object* v___x_2981_; 
if (v_isShared_2979_ == 0)
{
v___x_2981_ = v___x_2978_;
goto v_reusejp_2980_;
}
else
{
lean_object* v_reuseFailAlloc_2982_; 
v_reuseFailAlloc_2982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2982_, 0, v_a_2976_);
v___x_2981_ = v_reuseFailAlloc_2982_;
goto v_reusejp_2980_;
}
v_reusejp_2980_:
{
return v___x_2981_;
}
}
}
}
v___jp_2984_:
{
lean_object* v_inductiveVal_2989_; lean_object* v_toConstantVal_2990_; lean_object* v_name_2991_; lean_object* v___x_2992_; 
v_inductiveVal_2989_ = lean_ctor_get(v_ctx_2940_, 0);
v_toConstantVal_2990_ = lean_ctor_get(v_inductiveVal_2989_, 0);
v_name_2991_ = lean_ctor_get(v_toConstantVal_2990_, 0);
lean_inc(v_name_2991_);
v___x_2992_ = l_Lean_mkCasesOnName(v_name_2991_);
v___y_2958_ = v___y_2985_;
v___y_2959_ = v___y_2986_;
v___y_2960_ = v___y_2987_;
v___y_2961_ = v___y_2988_;
v___y_2962_ = v___x_2992_;
goto v___jp_2957_;
}
v___jp_2993_:
{
lean_object* v___x_2998_; 
v___x_2998_ = lean_st_ref_get(v___y_2997_);
if (v_useNatCasesAuxOn_2944_ == 0)
{
lean_dec(v___x_2998_);
v___y_2985_ = v___y_2994_;
v___y_2986_ = v___y_2995_;
v___y_2987_ = v___y_2996_;
v___y_2988_ = v___y_2997_;
goto v___jp_2984_;
}
else
{
lean_object* v_inductiveVal_2999_; lean_object* v_toConstantVal_3000_; lean_object* v_env_3001_; lean_object* v_name_3002_; lean_object* v___x_3003_; uint8_t v___x_3004_; 
v_inductiveVal_2999_ = lean_ctor_get(v_ctx_2940_, 0);
v_toConstantVal_3000_ = lean_ctor_get(v_inductiveVal_2999_, 0);
v_env_3001_ = lean_ctor_get(v___x_2998_, 0);
lean_inc_ref(v_env_3001_);
lean_dec(v___x_2998_);
v_name_3002_ = lean_ctor_get(v_toConstantVal_3000_, 0);
v___x_3003_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__1));
v___x_3004_ = lean_name_eq(v_name_3002_, v___x_3003_);
if (v___x_3004_ == 0)
{
lean_dec_ref(v_env_3001_);
v___y_2985_ = v___y_2994_;
v___y_2986_ = v___y_2995_;
v___y_2987_ = v___y_2996_;
v___y_2988_ = v___y_2997_;
goto v___jp_2984_;
}
else
{
lean_object* v___x_3005_; uint8_t v___x_3006_; 
v___x_3005_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__3));
v___x_3006_ = l_Lean_Environment_contains(v_env_3001_, v___x_3005_, v___x_3004_);
if (v___x_3006_ == 0)
{
v___y_2985_ = v___y_2994_;
v___y_2986_ = v___y_2995_;
v___y_2987_ = v___y_2996_;
v___y_2988_ = v___y_2997_;
goto v___jp_2984_;
}
else
{
v___y_2958_ = v___y_2994_;
v___y_2959_ = v___y_2995_;
v___y_2960_ = v___y_2996_;
v___y_2961_ = v___y_2997_;
v___y_2962_ = v___x_3005_;
goto v___jp_2957_;
}
}
}
}
}
else
{
lean_object* v_a_3056_; lean_object* v___x_3058_; uint8_t v_isShared_3059_; uint8_t v_isSharedCheck_3063_; 
lean_dec(v___y_2949_);
lean_dec_ref(v___y_2948_);
lean_dec(v___y_2947_);
lean_dec_ref(v___y_2946_);
lean_dec(v_interestingCtors_x3f_2945_);
lean_dec_ref(v_givenNames_2943_);
lean_dec(v_majorFVarId_2942_);
lean_dec(v_mvarId_2941_);
lean_dec_ref(v_ctx_2940_);
v_a_3056_ = lean_ctor_get(v___x_2953_, 0);
v_isSharedCheck_3063_ = !lean_is_exclusive(v___x_2953_);
if (v_isSharedCheck_3063_ == 0)
{
v___x_3058_ = v___x_2953_;
v_isShared_3059_ = v_isSharedCheck_3063_;
goto v_resetjp_3057_;
}
else
{
lean_inc(v_a_3056_);
lean_dec(v___x_2953_);
v___x_3058_ = lean_box(0);
v_isShared_3059_ = v_isSharedCheck_3063_;
goto v_resetjp_3057_;
}
v_resetjp_3057_:
{
lean_object* v___x_3061_; 
if (v_isShared_3059_ == 0)
{
v___x_3061_ = v___x_3058_;
goto v_reusejp_3060_;
}
else
{
lean_object* v_reuseFailAlloc_3062_; 
v_reuseFailAlloc_3062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3062_, 0, v_a_3056_);
v___x_3061_ = v_reuseFailAlloc_3062_;
goto v_reusejp_3060_;
}
v_reusejp_3060_:
{
return v___x_3061_;
}
}
}
}
else
{
lean_object* v_a_3064_; lean_object* v___x_3066_; uint8_t v_isShared_3067_; uint8_t v_isSharedCheck_3071_; 
lean_dec(v___y_2949_);
lean_dec_ref(v___y_2948_);
lean_dec(v___y_2947_);
lean_dec_ref(v___y_2946_);
lean_dec(v_interestingCtors_x3f_2945_);
lean_dec_ref(v_givenNames_2943_);
lean_dec(v_majorFVarId_2942_);
lean_dec(v_mvarId_2941_);
lean_dec_ref(v_ctx_2940_);
v_a_3064_ = lean_ctor_get(v___x_2951_, 0);
v_isSharedCheck_3071_ = !lean_is_exclusive(v___x_2951_);
if (v_isSharedCheck_3071_ == 0)
{
v___x_3066_ = v___x_2951_;
v_isShared_3067_ = v_isSharedCheck_3071_;
goto v_resetjp_3065_;
}
else
{
lean_inc(v_a_3064_);
lean_dec(v___x_2951_);
v___x_3066_ = lean_box(0);
v_isShared_3067_ = v_isSharedCheck_3071_;
goto v_resetjp_3065_;
}
v_resetjp_3065_:
{
lean_object* v___x_3069_; 
if (v_isShared_3067_ == 0)
{
v___x_3069_ = v___x_3066_;
goto v_reusejp_3068_;
}
else
{
lean_object* v_reuseFailAlloc_3070_; 
v_reuseFailAlloc_3070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3070_, 0, v_a_3064_);
v___x_3069_ = v_reuseFailAlloc_3070_;
goto v_reusejp_3068_;
}
v_reusejp_3068_:
{
return v___x_3069_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2939_ = stack[0].m_obj;
lean_object* v_ctx_2940_ = stack[1].m_obj;
lean_object* v_mvarId_2941_ = stack[2].m_obj;
lean_object* v_majorFVarId_2942_ = stack[3].m_obj;
lean_object* v_givenNames_2943_ = stack[4].m_obj;
uint8_t v_useNatCasesAuxOn_2944_ = stack[5].m_num;
lean_object* v_interestingCtors_x3f_2945_ = stack[6].m_obj;
lean_object* v___y_2946_ = stack[7].m_obj;
lean_object* v___y_2947_ = stack[8].m_obj;
lean_object* v___y_2948_ = stack[9].m_obj;
lean_object* v___y_2949_ = stack[10].m_obj;
lean_object* v_res_3072_;
v_res_3072_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0(v___x_2939_, v_ctx_2940_, v_mvarId_2941_, v_majorFVarId_2942_, v_givenNames_2943_, v_useNatCasesAuxOn_2944_, v_interestingCtors_x3f_2945_, v___y_2946_, v___y_2947_, v___y_2948_, v___y_2949_);
stack->m_obj
 = v_res_3072_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___boxed(lean_object* v___x_3073_, lean_object* v_ctx_3074_, lean_object* v_mvarId_3075_, lean_object* v_majorFVarId_3076_, lean_object* v_givenNames_3077_, lean_object* v_useNatCasesAuxOn_3078_, lean_object* v_interestingCtors_x3f_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_){
_start:
{
uint8_t v_useNatCasesAuxOn_boxed_3085_; lean_object* v_res_3086_; 
v_useNatCasesAuxOn_boxed_3085_ = lean_unbox(v_useNatCasesAuxOn_3078_);
v_res_3086_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0(v___x_3073_, v_ctx_3074_, v_mvarId_3075_, v_majorFVarId_3076_, v_givenNames_3077_, v_useNatCasesAuxOn_boxed_3085_, v_interestingCtors_x3f_3079_, v___y_3080_, v___y_3081_, v___y_3082_, v___y_3083_);
return v_res_3086_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn(lean_object* v_mvarId_3087_, lean_object* v_majorFVarId_3088_, lean_object* v_givenNames_3089_, lean_object* v_ctx_3090_, uint8_t v_useNatCasesAuxOn_3091_, lean_object* v_interestingCtors_x3f_3092_, lean_object* v_a_3093_, lean_object* v_a_3094_, lean_object* v_a_3095_, lean_object* v_a_3096_){
_start:
{
lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___f_3100_; lean_object* v___x_3101_; 
lean_inc(v_majorFVarId_3088_);
v___x_3098_ = l_Lean_mkFVar(v_majorFVarId_3088_);
v___x_3099_ = lean_box(v_useNatCasesAuxOn_3091_);
lean_inc(v_mvarId_3087_);
v___f_3100_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___boxed), 12, 7);
lean_closure_set(v___f_3100_, 0, v___x_3098_);
lean_closure_set(v___f_3100_, 1, v_ctx_3090_);
lean_closure_set(v___f_3100_, 2, v_mvarId_3087_);
lean_closure_set(v___f_3100_, 3, v_majorFVarId_3088_);
lean_closure_set(v___f_3100_, 4, v_givenNames_3089_);
lean_closure_set(v___f_3100_, 5, v___x_3099_);
lean_closure_set(v___f_3100_, 6, v_interestingCtors_x3f_3092_);
v___x_3101_ = l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2___redArg(v_mvarId_3087_, v___f_3100_, v_a_3093_, v_a_3094_, v_a_3095_, v_a_3096_);
return v___x_3101_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_3087_ = stack[0].m_obj;
lean_object* v_majorFVarId_3088_ = stack[1].m_obj;
lean_object* v_givenNames_3089_ = stack[2].m_obj;
lean_object* v_ctx_3090_ = stack[3].m_obj;
uint8_t v_useNatCasesAuxOn_3091_ = stack[4].m_num;
lean_object* v_interestingCtors_x3f_3092_ = stack[5].m_obj;
lean_object* v_a_3093_ = stack[6].m_obj;
lean_object* v_a_3094_ = stack[7].m_obj;
lean_object* v_a_3095_ = stack[8].m_obj;
lean_object* v_a_3096_ = stack[9].m_obj;
lean_object* v_res_3102_;
v_res_3102_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn(v_mvarId_3087_, v_majorFVarId_3088_, v_givenNames_3089_, v_ctx_3090_, v_useNatCasesAuxOn_3091_, v_interestingCtors_x3f_3092_, v_a_3093_, v_a_3094_, v_a_3095_, v_a_3096_);
stack->m_obj
 = v_res_3102_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___boxed(lean_object* v_mvarId_3103_, lean_object* v_majorFVarId_3104_, lean_object* v_givenNames_3105_, lean_object* v_ctx_3106_, lean_object* v_useNatCasesAuxOn_3107_, lean_object* v_interestingCtors_x3f_3108_, lean_object* v_a_3109_, lean_object* v_a_3110_, lean_object* v_a_3111_, lean_object* v_a_3112_, lean_object* v_a_3113_){
_start:
{
uint8_t v_useNatCasesAuxOn_boxed_3114_; lean_object* v_res_3115_; 
v_useNatCasesAuxOn_boxed_3114_ = lean_unbox(v_useNatCasesAuxOn_3107_);
v_res_3115_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn(v_mvarId_3103_, v_majorFVarId_3104_, v_givenNames_3105_, v_ctx_3106_, v_useNatCasesAuxOn_boxed_3114_, v_interestingCtors_x3f_3108_, v_a_3109_, v_a_3110_, v_a_3111_, v_a_3112_);
lean_dec(v_a_3112_);
lean_dec_ref(v_a_3111_);
lean_dec(v_a_3110_);
lean_dec_ref(v_a_3109_);
return v_res_3115_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0___closed__0(void){
_start:
{
lean_object* v___x_3116_; double v___x_3117_; 
v___x_3116_ = lean_unsigned_to_nat(0u);
v___x_3117_ = lean_float_of_nat(v___x_3116_);
return v___x_3117_;
}
}
lean_object* l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0(lean_object* v_cls_3121_, lean_object* v_msg_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_){
_start:
{
lean_object* v_ref_3128_; lean_object* v___x_3129_; lean_object* v_a_3130_; lean_object* v___x_3132_; uint8_t v_isShared_3133_; uint8_t v_isSharedCheck_3175_; 
v_ref_3128_ = lean_ctor_get(v___y_3125_, 2);
v___x_3129_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected_spec__0_spec__0(v_msg_3122_, v___y_3123_, v___y_3124_, v___y_3125_, v___y_3126_);
v_a_3130_ = lean_ctor_get(v___x_3129_, 0);
v_isSharedCheck_3175_ = !lean_is_exclusive(v___x_3129_);
if (v_isSharedCheck_3175_ == 0)
{
v___x_3132_ = v___x_3129_;
v_isShared_3133_ = v_isSharedCheck_3175_;
goto v_resetjp_3131_;
}
else
{
lean_inc(v_a_3130_);
lean_dec(v___x_3129_);
v___x_3132_ = lean_box(0);
v_isShared_3133_ = v_isSharedCheck_3175_;
goto v_resetjp_3131_;
}
v_resetjp_3131_:
{
lean_object* v___x_3134_; lean_object* v_traceState_3135_; lean_object* v_env_3136_; lean_object* v_nextMacroScope_3137_; lean_object* v_ngen_3138_; lean_object* v_auxDeclNGen_3139_; lean_object* v_cache_3140_; lean_object* v_recordedDeps_3141_; lean_object* v_messages_3142_; lean_object* v_infoState_3143_; lean_object* v_snapshotTasks_3144_; lean_object* v___x_3146_; uint8_t v_isShared_3147_; uint8_t v_isSharedCheck_3174_; 
v___x_3134_ = lean_st_ref_take(v___y_3126_);
v_traceState_3135_ = lean_ctor_get(v___x_3134_, 4);
v_env_3136_ = lean_ctor_get(v___x_3134_, 0);
v_nextMacroScope_3137_ = lean_ctor_get(v___x_3134_, 1);
v_ngen_3138_ = lean_ctor_get(v___x_3134_, 2);
v_auxDeclNGen_3139_ = lean_ctor_get(v___x_3134_, 3);
v_cache_3140_ = lean_ctor_get(v___x_3134_, 5);
v_recordedDeps_3141_ = lean_ctor_get(v___x_3134_, 6);
v_messages_3142_ = lean_ctor_get(v___x_3134_, 7);
v_infoState_3143_ = lean_ctor_get(v___x_3134_, 8);
v_snapshotTasks_3144_ = lean_ctor_get(v___x_3134_, 9);
v_isSharedCheck_3174_ = !lean_is_exclusive(v___x_3134_);
if (v_isSharedCheck_3174_ == 0)
{
v___x_3146_ = v___x_3134_;
v_isShared_3147_ = v_isSharedCheck_3174_;
goto v_resetjp_3145_;
}
else
{
lean_inc(v_snapshotTasks_3144_);
lean_inc(v_infoState_3143_);
lean_inc(v_messages_3142_);
lean_inc(v_recordedDeps_3141_);
lean_inc(v_cache_3140_);
lean_inc(v_traceState_3135_);
lean_inc(v_auxDeclNGen_3139_);
lean_inc(v_ngen_3138_);
lean_inc(v_nextMacroScope_3137_);
lean_inc(v_env_3136_);
lean_dec(v___x_3134_);
v___x_3146_ = lean_box(0);
v_isShared_3147_ = v_isSharedCheck_3174_;
goto v_resetjp_3145_;
}
v_resetjp_3145_:
{
uint64_t v_tid_3148_; lean_object* v_traces_3149_; lean_object* v___x_3151_; uint8_t v_isShared_3152_; uint8_t v_isSharedCheck_3173_; 
v_tid_3148_ = lean_ctor_get_uint64(v_traceState_3135_, sizeof(void*)*1);
v_traces_3149_ = lean_ctor_get(v_traceState_3135_, 0);
v_isSharedCheck_3173_ = !lean_is_exclusive(v_traceState_3135_);
if (v_isSharedCheck_3173_ == 0)
{
v___x_3151_ = v_traceState_3135_;
v_isShared_3152_ = v_isSharedCheck_3173_;
goto v_resetjp_3150_;
}
else
{
lean_inc(v_traces_3149_);
lean_dec(v_traceState_3135_);
v___x_3151_ = lean_box(0);
v_isShared_3152_ = v_isSharedCheck_3173_;
goto v_resetjp_3150_;
}
v_resetjp_3150_:
{
lean_object* v___x_3153_; lean_object* v___x_3154_; double v___x_3155_; uint8_t v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3164_; 
v___x_3153_ = lean_box(0);
v___x_3154_ = lean_box(0);
v___x_3155_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0___closed__0);
v___x_3156_ = 0;
v___x_3157_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0___closed__1));
v___x_3158_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3158_, 0, v_cls_3121_);
lean_ctor_set(v___x_3158_, 1, v___x_3154_);
lean_ctor_set(v___x_3158_, 2, v___x_3157_);
lean_ctor_set_float(v___x_3158_, sizeof(void*)*3, v___x_3155_);
lean_ctor_set_float(v___x_3158_, sizeof(void*)*3 + 8, v___x_3155_);
lean_ctor_set_uint8(v___x_3158_, sizeof(void*)*3 + 16, v___x_3156_);
v___x_3159_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0___closed__2));
v___x_3160_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3160_, 0, v___x_3158_);
lean_ctor_set(v___x_3160_, 1, v_a_3130_);
lean_ctor_set(v___x_3160_, 2, v___x_3159_);
lean_inc(v_ref_3128_);
v___x_3161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3161_, 0, v_ref_3128_);
lean_ctor_set(v___x_3161_, 1, v___x_3160_);
v___x_3162_ = l_Lean_PersistentArray_push___redArg(v_traces_3149_, v___x_3161_);
if (v_isShared_3152_ == 0)
{
lean_ctor_set(v___x_3151_, 0, v___x_3162_);
v___x_3164_ = v___x_3151_;
goto v_reusejp_3163_;
}
else
{
lean_object* v_reuseFailAlloc_3172_; 
v_reuseFailAlloc_3172_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3172_, 0, v___x_3162_);
lean_ctor_set_uint64(v_reuseFailAlloc_3172_, sizeof(void*)*1, v_tid_3148_);
v___x_3164_ = v_reuseFailAlloc_3172_;
goto v_reusejp_3163_;
}
v_reusejp_3163_:
{
lean_object* v___x_3166_; 
if (v_isShared_3147_ == 0)
{
lean_ctor_set(v___x_3146_, 4, v___x_3164_);
v___x_3166_ = v___x_3146_;
goto v_reusejp_3165_;
}
else
{
lean_object* v_reuseFailAlloc_3171_; 
v_reuseFailAlloc_3171_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3171_, 0, v_env_3136_);
lean_ctor_set(v_reuseFailAlloc_3171_, 1, v_nextMacroScope_3137_);
lean_ctor_set(v_reuseFailAlloc_3171_, 2, v_ngen_3138_);
lean_ctor_set(v_reuseFailAlloc_3171_, 3, v_auxDeclNGen_3139_);
lean_ctor_set(v_reuseFailAlloc_3171_, 4, v___x_3164_);
lean_ctor_set(v_reuseFailAlloc_3171_, 5, v_cache_3140_);
lean_ctor_set(v_reuseFailAlloc_3171_, 6, v_recordedDeps_3141_);
lean_ctor_set(v_reuseFailAlloc_3171_, 7, v_messages_3142_);
lean_ctor_set(v_reuseFailAlloc_3171_, 8, v_infoState_3143_);
lean_ctor_set(v_reuseFailAlloc_3171_, 9, v_snapshotTasks_3144_);
v___x_3166_ = v_reuseFailAlloc_3171_;
goto v_reusejp_3165_;
}
v_reusejp_3165_:
{
lean_object* v___x_3167_; lean_object* v___x_3169_; 
v___x_3167_ = lean_st_ref_put(v___y_3126_, v___x_3166_);
if (v_isShared_3133_ == 0)
{
lean_ctor_set(v___x_3132_, 0, v___x_3153_);
v___x_3169_ = v___x_3132_;
goto v_reusejp_3168_;
}
else
{
lean_object* v_reuseFailAlloc_3170_; 
v_reuseFailAlloc_3170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3170_, 0, v___x_3153_);
v___x_3169_ = v_reuseFailAlloc_3170_;
goto v_reusejp_3168_;
}
v_reusejp_3168_:
{
return v___x_3169_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_3121_ = stack[0].m_obj;
lean_object* v_msg_3122_ = stack[1].m_obj;
lean_object* v___y_3123_ = stack[2].m_obj;
lean_object* v___y_3124_ = stack[3].m_obj;
lean_object* v___y_3125_ = stack[4].m_obj;
lean_object* v___y_3126_ = stack[5].m_obj;
lean_object* v_res_3176_;
v_res_3176_ = l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0(v_cls_3121_, v_msg_3122_, v___y_3123_, v___y_3124_, v___y_3125_, v___y_3126_);
stack->m_obj
 = v_res_3176_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0___boxed(lean_object* v_cls_3177_, lean_object* v_msg_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_){
_start:
{
lean_object* v_res_3184_; 
v_res_3184_ = l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0(v_cls_3177_, v_msg_3178_, v___y_3179_, v___y_3180_, v___y_3181_, v___y_3182_);
lean_dec(v___y_3182_);
lean_dec_ref(v___y_3181_);
lean_dec(v___y_3180_);
lean_dec_ref(v___y_3179_);
return v_res_3184_;
}
}
static lean_object* _init_l_Lean_Meta_Cases_cases___lam__0___closed__2(void){
_start:
{
lean_object* v___x_3188_; lean_object* v___x_3189_; 
v___x_3188_ = ((lean_object*)(l_Lean_Meta_Cases_cases___lam__0___closed__1));
v___x_3189_ = l_Lean_MessageData_ofFormat(v___x_3188_);
return v___x_3189_;
}
}
static lean_object* _init_l_Lean_Meta_Cases_cases___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3190_; lean_object* v___x_3191_; 
v___x_3190_ = lean_obj_once(&l_Lean_Meta_Cases_cases___lam__0___closed__2, &l_Lean_Meta_Cases_cases___lam__0___closed__2_once, _init_l_Lean_Meta_Cases_cases___lam__0___closed__2);
v___x_3191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3191_, 0, v___x_3190_);
return v___x_3191_;
}
}
static lean_object* _init_l_Lean_Meta_Cases_cases___lam__0___closed__9(void){
_start:
{
lean_object* v___x_3198_; lean_object* v___x_3199_; 
v___x_3198_ = ((lean_object*)(l_Lean_Meta_Cases_cases___lam__0___closed__8));
v___x_3199_ = l_Lean_stringToMessageData(v___x_3198_);
return v___x_3199_;
}
}
lean_object* l_Lean_Meta_Cases_cases___lam__0(lean_object* v_mvarId_3200_, lean_object* v___x_3201_, lean_object* v_majorFVarId_3202_, lean_object* v_givenNames_3203_, lean_object* v_interestingCtors_x3f_3204_, lean_object* v___x_3205_, uint8_t v_useNatCasesAuxOn_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_){
_start:
{
lean_object* v___x_3212_; 
lean_inc(v___x_3201_);
lean_inc(v_mvarId_3200_);
v___x_3212_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_3200_, v___x_3201_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_);
if (lean_obj_tag(v___x_3212_) == 0)
{
lean_object* v___x_3213_; 
lean_dec_ref_known(v___x_3212_, 1);
lean_inc(v_majorFVarId_3202_);
v___x_3213_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f(v_majorFVarId_3202_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_);
if (lean_obj_tag(v___x_3213_) == 0)
{
lean_object* v_a_3214_; 
v_a_3214_ = lean_ctor_get(v___x_3213_, 0);
lean_inc(v_a_3214_);
lean_dec_ref_known(v___x_3213_, 1);
if (lean_obj_tag(v_a_3214_) == 0)
{
lean_object* v___x_3215_; lean_object* v___x_3216_; 
lean_dec_ref(v___x_3205_);
lean_dec(v_interestingCtors_x3f_3204_);
lean_dec_ref(v_givenNames_3203_);
lean_dec(v_majorFVarId_3202_);
v___x_3215_ = lean_obj_once(&l_Lean_Meta_Cases_cases___lam__0___closed__3, &l_Lean_Meta_Cases_cases___lam__0___closed__3_once, _init_l_Lean_Meta_Cases_cases___lam__0___closed__3);
v___x_3216_ = l_Lean_Meta_throwTacticEx___redArg(v___x_3201_, v_mvarId_3200_, v___x_3215_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_);
return v___x_3216_;
}
else
{
lean_object* v_val_3217_; lean_object* v___x_3219_; uint8_t v_isShared_3220_; uint8_t v_isSharedCheck_3282_; 
lean_dec(v___x_3201_);
v_val_3217_ = lean_ctor_get(v_a_3214_, 0);
v_isSharedCheck_3282_ = !lean_is_exclusive(v_a_3214_);
if (v_isSharedCheck_3282_ == 0)
{
v___x_3219_ = v_a_3214_;
v_isShared_3220_ = v_isSharedCheck_3282_;
goto v_resetjp_3218_;
}
else
{
lean_inc(v_val_3217_);
lean_dec(v_a_3214_);
v___x_3219_ = lean_box(0);
v_isShared_3220_ = v_isSharedCheck_3282_;
goto v_resetjp_3218_;
}
v_resetjp_3218_:
{
lean_object* v___x_3221_; 
lean_inc(v_val_3217_);
v___x_3221_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices(v_val_3217_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_);
if (lean_obj_tag(v___x_3221_) == 0)
{
lean_object* v_a_3222_; uint8_t v___x_3223_; 
v_a_3222_ = lean_ctor_get(v___x_3221_, 0);
lean_inc(v_a_3222_);
lean_dec_ref_known(v___x_3221_, 1);
v___x_3223_ = lean_unbox(v_a_3222_);
if (v___x_3223_ == 0)
{
lean_object* v___x_3224_; 
v___x_3224_ = l_Lean_Meta_generalizeIndices(v_mvarId_3200_, v_majorFVarId_3202_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_);
if (lean_obj_tag(v___x_3224_) == 0)
{
lean_object* v_a_3225_; lean_object* v___y_3227_; lean_object* v___y_3228_; lean_object* v___y_3229_; lean_object* v___y_3230_; lean_object* v_toCold_3240_; lean_object* v_options_3241_; uint8_t v_hasTrace_3242_; 
v_a_3225_ = lean_ctor_get(v___x_3224_, 0);
lean_inc(v_a_3225_);
lean_dec_ref_known(v___x_3224_, 1);
v_toCold_3240_ = lean_ctor_get(v___y_3209_, 0);
v_options_3241_ = lean_ctor_get(v_toCold_3240_, 2);
v_hasTrace_3242_ = lean_ctor_get_uint8(v_options_3241_, sizeof(void*)*1);
if (v_hasTrace_3242_ == 0)
{
lean_del_object(v___x_3219_);
lean_dec_ref(v___x_3205_);
v___y_3227_ = v___y_3207_;
v___y_3228_ = v___y_3208_;
v___y_3229_ = v___y_3209_;
v___y_3230_ = v___y_3210_;
goto v___jp_3226_;
}
else
{
lean_object* v_inheritedTraceOptions_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; uint8_t v___x_3249_; 
v_inheritedTraceOptions_3243_ = lean_ctor_get(v_toCold_3240_, 11);
v___x_3244_ = ((lean_object*)(l_Lean_Meta_Cases_cases___lam__0___closed__4));
v___x_3245_ = ((lean_object*)(l_Lean_Meta_Cases_cases___lam__0___closed__5));
v___x_3246_ = l_Lean_Name_mkStr3(v___x_3244_, v___x_3245_, v___x_3205_);
v___x_3247_ = ((lean_object*)(l_Lean_Meta_Cases_cases___lam__0___closed__7));
lean_inc(v___x_3246_);
v___x_3248_ = l_Lean_Name_append(v___x_3247_, v___x_3246_);
v___x_3249_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3243_, v_options_3241_, v___x_3248_);
lean_dec(v___x_3248_);
if (v___x_3249_ == 0)
{
lean_dec(v___x_3246_);
lean_del_object(v___x_3219_);
v___y_3227_ = v___y_3207_;
v___y_3228_ = v___y_3208_;
v___y_3229_ = v___y_3209_;
v___y_3230_ = v___y_3210_;
goto v___jp_3226_;
}
else
{
lean_object* v_mvarId_3250_; lean_object* v___x_3251_; lean_object* v___x_3253_; 
v_mvarId_3250_ = lean_ctor_get(v_a_3225_, 0);
v___x_3251_ = lean_obj_once(&l_Lean_Meta_Cases_cases___lam__0___closed__9, &l_Lean_Meta_Cases_cases___lam__0___closed__9_once, _init_l_Lean_Meta_Cases_cases___lam__0___closed__9);
lean_inc(v_mvarId_3250_);
if (v_isShared_3220_ == 0)
{
lean_ctor_set(v___x_3219_, 0, v_mvarId_3250_);
v___x_3253_ = v___x_3219_;
goto v_reusejp_3252_;
}
else
{
lean_object* v_reuseFailAlloc_3264_; 
v_reuseFailAlloc_3264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3264_, 0, v_mvarId_3250_);
v___x_3253_ = v_reuseFailAlloc_3264_;
goto v_reusejp_3252_;
}
v_reusejp_3252_:
{
lean_object* v___x_3254_; lean_object* v___x_3255_; 
v___x_3254_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3254_, 0, v___x_3251_);
lean_ctor_set(v___x_3254_, 1, v___x_3253_);
v___x_3255_ = l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0(v___x_3246_, v___x_3254_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_);
if (lean_obj_tag(v___x_3255_) == 0)
{
lean_dec_ref_known(v___x_3255_, 1);
v___y_3227_ = v___y_3207_;
v___y_3228_ = v___y_3208_;
v___y_3229_ = v___y_3209_;
v___y_3230_ = v___y_3210_;
goto v___jp_3226_;
}
else
{
lean_object* v_a_3256_; lean_object* v___x_3258_; uint8_t v_isShared_3259_; uint8_t v_isSharedCheck_3263_; 
lean_dec(v_a_3225_);
lean_dec(v_a_3222_);
lean_dec(v_val_3217_);
lean_dec(v_interestingCtors_x3f_3204_);
lean_dec_ref(v_givenNames_3203_);
v_a_3256_ = lean_ctor_get(v___x_3255_, 0);
v_isSharedCheck_3263_ = !lean_is_exclusive(v___x_3255_);
if (v_isSharedCheck_3263_ == 0)
{
v___x_3258_ = v___x_3255_;
v_isShared_3259_ = v_isSharedCheck_3263_;
goto v_resetjp_3257_;
}
else
{
lean_inc(v_a_3256_);
lean_dec(v___x_3255_);
v___x_3258_ = lean_box(0);
v_isShared_3259_ = v_isSharedCheck_3263_;
goto v_resetjp_3257_;
}
v_resetjp_3257_:
{
lean_object* v___x_3261_; 
if (v_isShared_3259_ == 0)
{
v___x_3261_ = v___x_3258_;
goto v_reusejp_3260_;
}
else
{
lean_object* v_reuseFailAlloc_3262_; 
v_reuseFailAlloc_3262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3262_, 0, v_a_3256_);
v___x_3261_ = v_reuseFailAlloc_3262_;
goto v_reusejp_3260_;
}
v_reusejp_3260_:
{
return v___x_3261_;
}
}
}
}
}
}
v___jp_3226_:
{
lean_object* v_mvarId_3231_; lean_object* v_fvarId_3232_; lean_object* v_numEqs_3233_; uint8_t v___x_3234_; lean_object* v___x_3235_; 
v_mvarId_3231_ = lean_ctor_get(v_a_3225_, 0);
v_fvarId_3232_ = lean_ctor_get(v_a_3225_, 2);
v_numEqs_3233_ = lean_ctor_get(v_a_3225_, 3);
lean_inc(v_numEqs_3233_);
v___x_3234_ = lean_unbox(v_a_3222_);
lean_dec(v_a_3222_);
lean_inc(v_fvarId_3232_);
lean_inc(v_mvarId_3231_);
v___x_3235_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn(v_mvarId_3231_, v_fvarId_3232_, v_givenNames_3203_, v_val_3217_, v___x_3234_, v_interestingCtors_x3f_3204_, v___y_3227_, v___y_3228_, v___y_3229_, v___y_3230_);
if (lean_obj_tag(v___x_3235_) == 0)
{
lean_object* v_a_3236_; lean_object* v___x_3237_; 
v_a_3236_ = lean_ctor_get(v___x_3235_, 0);
lean_inc(v_a_3236_);
lean_dec_ref_known(v___x_3235_, 1);
v___x_3237_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices(v_a_3225_, v_a_3236_, v___y_3227_, v___y_3228_, v___y_3229_, v___y_3230_);
lean_dec(v_a_3225_);
if (lean_obj_tag(v___x_3237_) == 0)
{
lean_object* v_a_3238_; lean_object* v___x_3239_; 
v_a_3238_ = lean_ctor_get(v___x_3237_, 0);
lean_inc(v_a_3238_);
lean_dec_ref_known(v___x_3237_, 1);
v___x_3239_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs(v_numEqs_3233_, v_a_3238_, v___y_3227_, v___y_3228_, v___y_3229_, v___y_3230_);
lean_dec(v_a_3238_);
return v___x_3239_;
}
else
{
lean_dec(v_numEqs_3233_);
return v___x_3237_;
}
}
else
{
lean_dec(v_numEqs_3233_);
lean_dec(v_a_3225_);
return v___x_3235_;
}
}
}
else
{
lean_object* v_a_3265_; lean_object* v___x_3267_; uint8_t v_isShared_3268_; uint8_t v_isSharedCheck_3272_; 
lean_dec(v_a_3222_);
lean_del_object(v___x_3219_);
lean_dec(v_val_3217_);
lean_dec_ref(v___x_3205_);
lean_dec(v_interestingCtors_x3f_3204_);
lean_dec_ref(v_givenNames_3203_);
v_a_3265_ = lean_ctor_get(v___x_3224_, 0);
v_isSharedCheck_3272_ = !lean_is_exclusive(v___x_3224_);
if (v_isSharedCheck_3272_ == 0)
{
v___x_3267_ = v___x_3224_;
v_isShared_3268_ = v_isSharedCheck_3272_;
goto v_resetjp_3266_;
}
else
{
lean_inc(v_a_3265_);
lean_dec(v___x_3224_);
v___x_3267_ = lean_box(0);
v_isShared_3268_ = v_isSharedCheck_3272_;
goto v_resetjp_3266_;
}
v_resetjp_3266_:
{
lean_object* v___x_3270_; 
if (v_isShared_3268_ == 0)
{
v___x_3270_ = v___x_3267_;
goto v_reusejp_3269_;
}
else
{
lean_object* v_reuseFailAlloc_3271_; 
v_reuseFailAlloc_3271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3271_, 0, v_a_3265_);
v___x_3270_ = v_reuseFailAlloc_3271_;
goto v_reusejp_3269_;
}
v_reusejp_3269_:
{
return v___x_3270_;
}
}
}
}
else
{
lean_object* v___x_3273_; 
lean_dec(v_a_3222_);
lean_del_object(v___x_3219_);
lean_dec_ref(v___x_3205_);
v___x_3273_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn(v_mvarId_3200_, v_majorFVarId_3202_, v_givenNames_3203_, v_val_3217_, v_useNatCasesAuxOn_3206_, v_interestingCtors_x3f_3204_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_);
return v___x_3273_;
}
}
else
{
lean_object* v_a_3274_; lean_object* v___x_3276_; uint8_t v_isShared_3277_; uint8_t v_isSharedCheck_3281_; 
lean_del_object(v___x_3219_);
lean_dec(v_val_3217_);
lean_dec_ref(v___x_3205_);
lean_dec(v_interestingCtors_x3f_3204_);
lean_dec_ref(v_givenNames_3203_);
lean_dec(v_majorFVarId_3202_);
lean_dec(v_mvarId_3200_);
v_a_3274_ = lean_ctor_get(v___x_3221_, 0);
v_isSharedCheck_3281_ = !lean_is_exclusive(v___x_3221_);
if (v_isSharedCheck_3281_ == 0)
{
v___x_3276_ = v___x_3221_;
v_isShared_3277_ = v_isSharedCheck_3281_;
goto v_resetjp_3275_;
}
else
{
lean_inc(v_a_3274_);
lean_dec(v___x_3221_);
v___x_3276_ = lean_box(0);
v_isShared_3277_ = v_isSharedCheck_3281_;
goto v_resetjp_3275_;
}
v_resetjp_3275_:
{
lean_object* v___x_3279_; 
if (v_isShared_3277_ == 0)
{
v___x_3279_ = v___x_3276_;
goto v_reusejp_3278_;
}
else
{
lean_object* v_reuseFailAlloc_3280_; 
v_reuseFailAlloc_3280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3280_, 0, v_a_3274_);
v___x_3279_ = v_reuseFailAlloc_3280_;
goto v_reusejp_3278_;
}
v_reusejp_3278_:
{
return v___x_3279_;
}
}
}
}
}
}
else
{
lean_object* v_a_3283_; lean_object* v___x_3285_; uint8_t v_isShared_3286_; uint8_t v_isSharedCheck_3290_; 
lean_dec_ref(v___x_3205_);
lean_dec(v_interestingCtors_x3f_3204_);
lean_dec_ref(v_givenNames_3203_);
lean_dec(v_majorFVarId_3202_);
lean_dec(v___x_3201_);
lean_dec(v_mvarId_3200_);
v_a_3283_ = lean_ctor_get(v___x_3213_, 0);
v_isSharedCheck_3290_ = !lean_is_exclusive(v___x_3213_);
if (v_isSharedCheck_3290_ == 0)
{
v___x_3285_ = v___x_3213_;
v_isShared_3286_ = v_isSharedCheck_3290_;
goto v_resetjp_3284_;
}
else
{
lean_inc(v_a_3283_);
lean_dec(v___x_3213_);
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
lean_dec_ref(v___x_3205_);
lean_dec(v_interestingCtors_x3f_3204_);
lean_dec_ref(v_givenNames_3203_);
lean_dec(v_majorFVarId_3202_);
lean_dec(v___x_3201_);
lean_dec(v_mvarId_3200_);
v_a_3291_ = lean_ctor_get(v___x_3212_, 0);
v_isSharedCheck_3298_ = !lean_is_exclusive(v___x_3212_);
if (v_isSharedCheck_3298_ == 0)
{
v___x_3293_ = v___x_3212_;
v_isShared_3294_ = v_isSharedCheck_3298_;
goto v_resetjp_3292_;
}
else
{
lean_inc(v_a_3291_);
lean_dec(v___x_3212_);
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
}
LEAN_EXPORT void l_Lean_Meta_Cases_cases___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_3200_ = stack[0].m_obj;
lean_object* v___x_3201_ = stack[1].m_obj;
lean_object* v_majorFVarId_3202_ = stack[2].m_obj;
lean_object* v_givenNames_3203_ = stack[3].m_obj;
lean_object* v_interestingCtors_x3f_3204_ = stack[4].m_obj;
lean_object* v___x_3205_ = stack[5].m_obj;
uint8_t v_useNatCasesAuxOn_3206_ = stack[6].m_num;
lean_object* v___y_3207_ = stack[7].m_obj;
lean_object* v___y_3208_ = stack[8].m_obj;
lean_object* v___y_3209_ = stack[9].m_obj;
lean_object* v___y_3210_ = stack[10].m_obj;
lean_object* v_res_3299_;
v_res_3299_ = l_Lean_Meta_Cases_cases___lam__0(v_mvarId_3200_, v___x_3201_, v_majorFVarId_3202_, v_givenNames_3203_, v_interestingCtors_x3f_3204_, v___x_3205_, v_useNatCasesAuxOn_3206_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_);
stack->m_obj
 = v_res_3299_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_cases___lam__0___boxed(lean_object* v_mvarId_3300_, lean_object* v___x_3301_, lean_object* v_majorFVarId_3302_, lean_object* v_givenNames_3303_, lean_object* v_interestingCtors_x3f_3304_, lean_object* v___x_3305_, lean_object* v_useNatCasesAuxOn_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_){
_start:
{
uint8_t v_useNatCasesAuxOn_boxed_3312_; lean_object* v_res_3313_; 
v_useNatCasesAuxOn_boxed_3312_ = lean_unbox(v_useNatCasesAuxOn_3306_);
v_res_3313_ = l_Lean_Meta_Cases_cases___lam__0(v_mvarId_3300_, v___x_3301_, v_majorFVarId_3302_, v_givenNames_3303_, v_interestingCtors_x3f_3304_, v___x_3305_, v_useNatCasesAuxOn_boxed_3312_, v___y_3307_, v___y_3308_, v___y_3309_, v___y_3310_);
lean_dec(v___y_3310_);
lean_dec_ref(v___y_3309_);
lean_dec(v___y_3308_);
lean_dec_ref(v___y_3307_);
return v_res_3313_;
}
}
lean_object* l_Lean_Meta_Cases_cases(lean_object* v_mvarId_3317_, lean_object* v_majorFVarId_3318_, lean_object* v_givenNames_3319_, uint8_t v_useNatCasesAuxOn_3320_, lean_object* v_interestingCtors_x3f_3321_, lean_object* v_a_3322_, lean_object* v_a_3323_, lean_object* v_a_3324_, lean_object* v_a_3325_){
_start:
{
lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___f_3330_; lean_object* v___x_3331_; 
v___x_3327_ = ((lean_object*)(l_Lean_Meta_Cases_cases___closed__0));
v___x_3328_ = ((lean_object*)(l_Lean_Meta_Cases_cases___closed__1));
v___x_3329_ = lean_box(v_useNatCasesAuxOn_3320_);
lean_inc(v_mvarId_3317_);
v___f_3330_ = lean_alloc_closure((void*)(l_Lean_Meta_Cases_cases___lam__0___boxed), 12, 7);
lean_closure_set(v___f_3330_, 0, v_mvarId_3317_);
lean_closure_set(v___f_3330_, 1, v___x_3328_);
lean_closure_set(v___f_3330_, 2, v_majorFVarId_3318_);
lean_closure_set(v___f_3330_, 3, v_givenNames_3319_);
lean_closure_set(v___f_3330_, 4, v_interestingCtors_x3f_3321_);
lean_closure_set(v___f_3330_, 5, v___x_3327_);
lean_closure_set(v___f_3330_, 6, v___x_3329_);
v___x_3331_ = l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2___redArg(v_mvarId_3317_, v___f_3330_, v_a_3322_, v_a_3323_, v_a_3324_, v_a_3325_);
if (lean_obj_tag(v___x_3331_) == 0)
{
return v___x_3331_;
}
else
{
lean_object* v_a_3332_; uint8_t v___y_3334_; uint8_t v___x_3336_; 
v_a_3332_ = lean_ctor_get(v___x_3331_, 0);
v___x_3336_ = l_Lean_Exception_isInterrupt(v_a_3332_);
if (v___x_3336_ == 0)
{
uint8_t v___x_3337_; 
lean_inc(v_a_3332_);
v___x_3337_ = l_Lean_Exception_isRuntime(v_a_3332_);
v___y_3334_ = v___x_3337_;
goto v___jp_3333_;
}
else
{
v___y_3334_ = v___x_3336_;
goto v___jp_3333_;
}
v___jp_3333_:
{
if (v___y_3334_ == 0)
{
lean_object* v___x_3335_; 
lean_inc(v_a_3332_);
lean_dec_ref_known(v___x_3331_, 1);
v___x_3335_ = l_Lean_Meta_throwNestedTacticEx___redArg(v___x_3328_, v_a_3332_, v_a_3322_, v_a_3323_, v_a_3324_, v_a_3325_);
return v___x_3335_;
}
else
{
return v___x_3331_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Cases_cases_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_3317_ = stack[0].m_obj;
lean_object* v_majorFVarId_3318_ = stack[1].m_obj;
lean_object* v_givenNames_3319_ = stack[2].m_obj;
uint8_t v_useNatCasesAuxOn_3320_ = stack[3].m_num;
lean_object* v_interestingCtors_x3f_3321_ = stack[4].m_obj;
lean_object* v_a_3322_ = stack[5].m_obj;
lean_object* v_a_3323_ = stack[6].m_obj;
lean_object* v_a_3324_ = stack[7].m_obj;
lean_object* v_a_3325_ = stack[8].m_obj;
lean_object* v_res_3338_;
v_res_3338_ = l_Lean_Meta_Cases_cases(v_mvarId_3317_, v_majorFVarId_3318_, v_givenNames_3319_, v_useNatCasesAuxOn_3320_, v_interestingCtors_x3f_3321_, v_a_3322_, v_a_3323_, v_a_3324_, v_a_3325_);
stack->m_obj
 = v_res_3338_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_cases___boxed(lean_object* v_mvarId_3339_, lean_object* v_majorFVarId_3340_, lean_object* v_givenNames_3341_, lean_object* v_useNatCasesAuxOn_3342_, lean_object* v_interestingCtors_x3f_3343_, lean_object* v_a_3344_, lean_object* v_a_3345_, lean_object* v_a_3346_, lean_object* v_a_3347_, lean_object* v_a_3348_){
_start:
{
uint8_t v_useNatCasesAuxOn_boxed_3349_; lean_object* v_res_3350_; 
v_useNatCasesAuxOn_boxed_3349_ = lean_unbox(v_useNatCasesAuxOn_3342_);
v_res_3350_ = l_Lean_Meta_Cases_cases(v_mvarId_3339_, v_majorFVarId_3340_, v_givenNames_3341_, v_useNatCasesAuxOn_boxed_3349_, v_interestingCtors_x3f_3343_, v_a_3344_, v_a_3345_, v_a_3346_, v_a_3347_);
lean_dec(v_a_3347_);
lean_dec_ref(v_a_3346_);
lean_dec(v_a_3345_);
lean_dec_ref(v_a_3344_);
return v_res_3350_;
}
}
lean_object* l_Lean_MVarId_cases(lean_object* v_mvarId_3351_, lean_object* v_majorFVarId_3352_, lean_object* v_givenNames_3353_, uint8_t v_useNatCasesAuxOn_3354_, lean_object* v_interestingCtors_x3f_3355_, lean_object* v_a_3356_, lean_object* v_a_3357_, lean_object* v_a_3358_, lean_object* v_a_3359_){
_start:
{
lean_object* v___x_3361_; 
v___x_3361_ = l_Lean_Meta_Cases_cases(v_mvarId_3351_, v_majorFVarId_3352_, v_givenNames_3353_, v_useNatCasesAuxOn_3354_, v_interestingCtors_x3f_3355_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_);
return v___x_3361_;
}
}
LEAN_EXPORT void l_Lean_MVarId_cases_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_3351_ = stack[0].m_obj;
lean_object* v_majorFVarId_3352_ = stack[1].m_obj;
lean_object* v_givenNames_3353_ = stack[2].m_obj;
uint8_t v_useNatCasesAuxOn_3354_ = stack[3].m_num;
lean_object* v_interestingCtors_x3f_3355_ = stack[4].m_obj;
lean_object* v_a_3356_ = stack[5].m_obj;
lean_object* v_a_3357_ = stack[6].m_obj;
lean_object* v_a_3358_ = stack[7].m_obj;
lean_object* v_a_3359_ = stack[8].m_obj;
lean_object* v_res_3362_;
v_res_3362_ = l_Lean_MVarId_cases(v_mvarId_3351_, v_majorFVarId_3352_, v_givenNames_3353_, v_useNatCasesAuxOn_3354_, v_interestingCtors_x3f_3355_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_);
stack->m_obj
 = v_res_3362_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_cases___boxed(lean_object* v_mvarId_3363_, lean_object* v_majorFVarId_3364_, lean_object* v_givenNames_3365_, lean_object* v_useNatCasesAuxOn_3366_, lean_object* v_interestingCtors_x3f_3367_, lean_object* v_a_3368_, lean_object* v_a_3369_, lean_object* v_a_3370_, lean_object* v_a_3371_, lean_object* v_a_3372_){
_start:
{
uint8_t v_useNatCasesAuxOn_boxed_3373_; lean_object* v_res_3374_; 
v_useNatCasesAuxOn_boxed_3373_ = lean_unbox(v_useNatCasesAuxOn_3366_);
v_res_3374_ = l_Lean_MVarId_cases(v_mvarId_3363_, v_majorFVarId_3364_, v_givenNames_3365_, v_useNatCasesAuxOn_boxed_3373_, v_interestingCtors_x3f_3367_, v_a_3368_, v_a_3369_, v_a_3370_, v_a_3371_);
lean_dec(v_a_3371_);
lean_dec_ref(v_a_3370_);
lean_dec(v_a_3369_);
lean_dec_ref(v_a_3368_);
return v_res_3374_;
}
}
lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1___redArg(lean_object* v_x_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_){
_start:
{
lean_object* v___x_3381_; 
v___x_3381_ = l_Lean_Meta_saveState___redArg(v___y_3377_, v___y_3379_);
if (lean_obj_tag(v___x_3381_) == 0)
{
lean_object* v_a_3382_; lean_object* v___x_3383_; 
v_a_3382_ = lean_ctor_get(v___x_3381_, 0);
lean_inc(v_a_3382_);
lean_dec_ref_known(v___x_3381_, 1);
lean_inc(v___y_3379_);
lean_inc_ref(v___y_3378_);
lean_inc(v___y_3377_);
lean_inc_ref(v___y_3376_);
v___x_3383_ = lean_apply_5(v_x_3375_, v___y_3376_, v___y_3377_, v___y_3378_, v___y_3379_, lean_box(0));
if (lean_obj_tag(v___x_3383_) == 0)
{
lean_object* v_a_3384_; lean_object* v___x_3386_; uint8_t v_isShared_3387_; uint8_t v_isSharedCheck_3392_; 
lean_dec(v_a_3382_);
v_a_3384_ = lean_ctor_get(v___x_3383_, 0);
v_isSharedCheck_3392_ = !lean_is_exclusive(v___x_3383_);
if (v_isSharedCheck_3392_ == 0)
{
v___x_3386_ = v___x_3383_;
v_isShared_3387_ = v_isSharedCheck_3392_;
goto v_resetjp_3385_;
}
else
{
lean_inc(v_a_3384_);
lean_dec(v___x_3383_);
v___x_3386_ = lean_box(0);
v_isShared_3387_ = v_isSharedCheck_3392_;
goto v_resetjp_3385_;
}
v_resetjp_3385_:
{
lean_object* v___x_3388_; lean_object* v___x_3390_; 
v___x_3388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3388_, 0, v_a_3384_);
if (v_isShared_3387_ == 0)
{
lean_ctor_set(v___x_3386_, 0, v___x_3388_);
v___x_3390_ = v___x_3386_;
goto v_reusejp_3389_;
}
else
{
lean_object* v_reuseFailAlloc_3391_; 
v_reuseFailAlloc_3391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3391_, 0, v___x_3388_);
v___x_3390_ = v_reuseFailAlloc_3391_;
goto v_reusejp_3389_;
}
v_reusejp_3389_:
{
return v___x_3390_;
}
}
}
else
{
lean_object* v_a_3393_; lean_object* v___x_3395_; uint8_t v_isShared_3396_; uint8_t v_isSharedCheck_3422_; 
v_a_3393_ = lean_ctor_get(v___x_3383_, 0);
v_isSharedCheck_3422_ = !lean_is_exclusive(v___x_3383_);
if (v_isSharedCheck_3422_ == 0)
{
v___x_3395_ = v___x_3383_;
v_isShared_3396_ = v_isSharedCheck_3422_;
goto v_resetjp_3394_;
}
else
{
lean_inc(v_a_3393_);
lean_dec(v___x_3383_);
v___x_3395_ = lean_box(0);
v_isShared_3396_ = v_isSharedCheck_3422_;
goto v_resetjp_3394_;
}
v_resetjp_3394_:
{
uint8_t v___y_3398_; uint8_t v___x_3420_; 
v___x_3420_ = l_Lean_Exception_isInterrupt(v_a_3393_);
if (v___x_3420_ == 0)
{
uint8_t v___x_3421_; 
lean_inc(v_a_3393_);
v___x_3421_ = l_Lean_Exception_isRuntime(v_a_3393_);
v___y_3398_ = v___x_3421_;
goto v___jp_3397_;
}
else
{
v___y_3398_ = v___x_3420_;
goto v___jp_3397_;
}
v___jp_3397_:
{
if (v___y_3398_ == 0)
{
lean_object* v___x_3399_; 
lean_del_object(v___x_3395_);
lean_dec(v_a_3393_);
v___x_3399_ = l_Lean_Meta_SavedState_restore___redArg(v_a_3382_, v___y_3377_, v___y_3379_);
if (lean_obj_tag(v___x_3399_) == 0)
{
lean_object* v___x_3401_; uint8_t v_isShared_3402_; uint8_t v_isSharedCheck_3407_; 
v_isSharedCheck_3407_ = !lean_is_exclusive(v___x_3399_);
if (v_isSharedCheck_3407_ == 0)
{
lean_object* v_unused_3408_; 
v_unused_3408_ = lean_ctor_get(v___x_3399_, 0);
lean_dec(v_unused_3408_);
v___x_3401_ = v___x_3399_;
v_isShared_3402_ = v_isSharedCheck_3407_;
goto v_resetjp_3400_;
}
else
{
lean_dec(v___x_3399_);
v___x_3401_ = lean_box(0);
v_isShared_3402_ = v_isSharedCheck_3407_;
goto v_resetjp_3400_;
}
v_resetjp_3400_:
{
lean_object* v___x_3403_; lean_object* v___x_3405_; 
v___x_3403_ = lean_box(0);
if (v_isShared_3402_ == 0)
{
lean_ctor_set(v___x_3401_, 0, v___x_3403_);
v___x_3405_ = v___x_3401_;
goto v_reusejp_3404_;
}
else
{
lean_object* v_reuseFailAlloc_3406_; 
v_reuseFailAlloc_3406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3406_, 0, v___x_3403_);
v___x_3405_ = v_reuseFailAlloc_3406_;
goto v_reusejp_3404_;
}
v_reusejp_3404_:
{
return v___x_3405_;
}
}
}
else
{
lean_object* v_a_3409_; lean_object* v___x_3411_; uint8_t v_isShared_3412_; uint8_t v_isSharedCheck_3416_; 
v_a_3409_ = lean_ctor_get(v___x_3399_, 0);
v_isSharedCheck_3416_ = !lean_is_exclusive(v___x_3399_);
if (v_isSharedCheck_3416_ == 0)
{
v___x_3411_ = v___x_3399_;
v_isShared_3412_ = v_isSharedCheck_3416_;
goto v_resetjp_3410_;
}
else
{
lean_inc(v_a_3409_);
lean_dec(v___x_3399_);
v___x_3411_ = lean_box(0);
v_isShared_3412_ = v_isSharedCheck_3416_;
goto v_resetjp_3410_;
}
v_resetjp_3410_:
{
lean_object* v___x_3414_; 
if (v_isShared_3412_ == 0)
{
v___x_3414_ = v___x_3411_;
goto v_reusejp_3413_;
}
else
{
lean_object* v_reuseFailAlloc_3415_; 
v_reuseFailAlloc_3415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3415_, 0, v_a_3409_);
v___x_3414_ = v_reuseFailAlloc_3415_;
goto v_reusejp_3413_;
}
v_reusejp_3413_:
{
return v___x_3414_;
}
}
}
}
else
{
lean_object* v___x_3418_; 
lean_dec(v_a_3382_);
if (v_isShared_3396_ == 0)
{
v___x_3418_ = v___x_3395_;
goto v_reusejp_3417_;
}
else
{
lean_object* v_reuseFailAlloc_3419_; 
v_reuseFailAlloc_3419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3419_, 0, v_a_3393_);
v___x_3418_ = v_reuseFailAlloc_3419_;
goto v_reusejp_3417_;
}
v_reusejp_3417_:
{
return v___x_3418_;
}
}
}
}
}
}
else
{
lean_object* v_a_3423_; lean_object* v___x_3425_; uint8_t v_isShared_3426_; uint8_t v_isSharedCheck_3430_; 
lean_dec_ref(v_x_3375_);
v_a_3423_ = lean_ctor_get(v___x_3381_, 0);
v_isSharedCheck_3430_ = !lean_is_exclusive(v___x_3381_);
if (v_isSharedCheck_3430_ == 0)
{
v___x_3425_ = v___x_3381_;
v_isShared_3426_ = v_isSharedCheck_3430_;
goto v_resetjp_3424_;
}
else
{
lean_inc(v_a_3423_);
lean_dec(v___x_3381_);
v___x_3425_ = lean_box(0);
v_isShared_3426_ = v_isSharedCheck_3430_;
goto v_resetjp_3424_;
}
v_resetjp_3424_:
{
lean_object* v___x_3428_; 
if (v_isShared_3426_ == 0)
{
v___x_3428_ = v___x_3425_;
goto v_reusejp_3427_;
}
else
{
lean_object* v_reuseFailAlloc_3429_; 
v_reuseFailAlloc_3429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3429_, 0, v_a_3423_);
v___x_3428_ = v_reuseFailAlloc_3429_;
goto v_reusejp_3427_;
}
v_reusejp_3427_:
{
return v___x_3428_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3375_ = stack[0].m_obj;
lean_object* v___y_3376_ = stack[1].m_obj;
lean_object* v___y_3377_ = stack[2].m_obj;
lean_object* v___y_3378_ = stack[3].m_obj;
lean_object* v___y_3379_ = stack[4].m_obj;
lean_object* v_res_3431_;
v_res_3431_ = l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1___redArg(v_x_3375_, v___y_3376_, v___y_3377_, v___y_3378_, v___y_3379_);
stack->m_obj
 = v_res_3431_;
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1___redArg___boxed(lean_object* v_x_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_){
_start:
{
lean_object* v_res_3438_; 
v_res_3438_ = l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1___redArg(v_x_3432_, v___y_3433_, v___y_3434_, v___y_3435_, v___y_3436_);
lean_dec(v___y_3436_);
lean_dec_ref(v___y_3435_);
lean_dec(v___y_3434_);
lean_dec_ref(v___y_3433_);
return v_res_3438_;
}
}
lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1(lean_object* v_00_u03b1_3439_, lean_object* v_x_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_, lean_object* v___y_3444_){
_start:
{
lean_object* v___x_3446_; 
v___x_3446_ = l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1___redArg(v_x_3440_, v___y_3441_, v___y_3442_, v___y_3443_, v___y_3444_);
return v___x_3446_;
}
}
LEAN_EXPORT void l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3440_ = stack[1].m_obj;
lean_object* v___y_3441_ = stack[2].m_obj;
lean_object* v___y_3442_ = stack[3].m_obj;
lean_object* v___y_3443_ = stack[4].m_obj;
lean_object* v___y_3444_ = stack[5].m_obj;
lean_object* v_res_3447_;
v_res_3447_ = l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1(lean_box(0), v_x_3440_, v___y_3441_, v___y_3442_, v___y_3443_, v___y_3444_);
stack->m_obj
 = v_res_3447_;
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1___boxed(lean_object* v_00_u03b1_3448_, lean_object* v_x_3449_, lean_object* v___y_3450_, lean_object* v___y_3451_, lean_object* v___y_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_){
_start:
{
lean_object* v_res_3455_; 
v_res_3455_ = l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1(v_00_u03b1_3448_, v_x_3449_, v___y_3450_, v___y_3451_, v___y_3452_, v___y_3453_);
lean_dec(v___y_3453_);
lean_dec_ref(v___y_3452_);
lean_dec(v___y_3451_);
lean_dec_ref(v___y_3450_);
return v_res_3455_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_MVarId_casesRec_spec__0(lean_object* v_a_3456_, lean_object* v_a_3457_){
_start:
{
if (lean_obj_tag(v_a_3456_) == 0)
{
lean_object* v___x_3458_; 
v___x_3458_ = l_List_reverse___redArg(v_a_3457_);
return v___x_3458_;
}
else
{
lean_object* v_head_3459_; lean_object* v_toInductionSubgoal_3460_; lean_object* v_tail_3461_; lean_object* v___x_3463_; uint8_t v_isShared_3464_; uint8_t v_isSharedCheck_3470_; 
v_head_3459_ = lean_ctor_get(v_a_3456_, 0);
v_toInductionSubgoal_3460_ = lean_ctor_get(v_head_3459_, 0);
lean_inc_ref(v_toInductionSubgoal_3460_);
v_tail_3461_ = lean_ctor_get(v_a_3456_, 1);
v_isSharedCheck_3470_ = !lean_is_exclusive(v_a_3456_);
if (v_isSharedCheck_3470_ == 0)
{
lean_object* v_unused_3471_; 
v_unused_3471_ = lean_ctor_get(v_a_3456_, 0);
lean_dec(v_unused_3471_);
v___x_3463_ = v_a_3456_;
v_isShared_3464_ = v_isSharedCheck_3470_;
goto v_resetjp_3462_;
}
else
{
lean_inc(v_tail_3461_);
lean_dec(v_a_3456_);
v___x_3463_ = lean_box(0);
v_isShared_3464_ = v_isSharedCheck_3470_;
goto v_resetjp_3462_;
}
v_resetjp_3462_:
{
lean_object* v_mvarId_3465_; lean_object* v___x_3467_; 
v_mvarId_3465_ = lean_ctor_get(v_toInductionSubgoal_3460_, 0);
lean_inc(v_mvarId_3465_);
lean_dec_ref(v_toInductionSubgoal_3460_);
if (v_isShared_3464_ == 0)
{
lean_ctor_set(v___x_3463_, 1, v_a_3457_);
lean_ctor_set(v___x_3463_, 0, v_mvarId_3465_);
v___x_3467_ = v___x_3463_;
goto v_reusejp_3466_;
}
else
{
lean_object* v_reuseFailAlloc_3469_; 
v_reuseFailAlloc_3469_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3469_, 0, v_mvarId_3465_);
lean_ctor_set(v_reuseFailAlloc_3469_, 1, v_a_3457_);
v___x_3467_ = v_reuseFailAlloc_3469_;
goto v_reusejp_3466_;
}
v_reusejp_3466_:
{
v_a_3456_ = v_tail_3461_;
v_a_3457_ = v___x_3467_;
goto _start;
}
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3___lam__0(lean_object* v_mvarId_3472_, lean_object* v___x_3473_, lean_object* v___x_3474_, uint8_t v___x_3475_, lean_object* v___x_3476_, lean_object* v___y_3477_, lean_object* v___y_3478_, lean_object* v___y_3479_, lean_object* v___y_3480_){
_start:
{
lean_object* v___x_3482_; 
v___x_3482_ = l_Lean_Meta_Cases_cases(v_mvarId_3472_, v___x_3473_, v___x_3474_, v___x_3475_, v___x_3476_, v___y_3477_, v___y_3478_, v___y_3479_, v___y_3480_);
if (lean_obj_tag(v___x_3482_) == 0)
{
lean_object* v_a_3483_; lean_object* v___x_3485_; uint8_t v_isShared_3486_; uint8_t v_isSharedCheck_3493_; 
v_a_3483_ = lean_ctor_get(v___x_3482_, 0);
v_isSharedCheck_3493_ = !lean_is_exclusive(v___x_3482_);
if (v_isSharedCheck_3493_ == 0)
{
v___x_3485_ = v___x_3482_;
v_isShared_3486_ = v_isSharedCheck_3493_;
goto v_resetjp_3484_;
}
else
{
lean_inc(v_a_3483_);
lean_dec(v___x_3482_);
v___x_3485_ = lean_box(0);
v_isShared_3486_ = v_isSharedCheck_3493_;
goto v_resetjp_3484_;
}
v_resetjp_3484_:
{
lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3491_; 
v___x_3487_ = lean_array_to_list(v_a_3483_);
v___x_3488_ = lean_box(0);
v___x_3489_ = l_List_mapTR_loop___at___00Lean_MVarId_casesRec_spec__0(v___x_3487_, v___x_3488_);
if (v_isShared_3486_ == 0)
{
lean_ctor_set(v___x_3485_, 0, v___x_3489_);
v___x_3491_ = v___x_3485_;
goto v_reusejp_3490_;
}
else
{
lean_object* v_reuseFailAlloc_3492_; 
v_reuseFailAlloc_3492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3492_, 0, v___x_3489_);
v___x_3491_ = v_reuseFailAlloc_3492_;
goto v_reusejp_3490_;
}
v_reusejp_3490_:
{
return v___x_3491_;
}
}
}
else
{
lean_object* v_a_3494_; lean_object* v___x_3496_; uint8_t v_isShared_3497_; uint8_t v_isSharedCheck_3501_; 
v_a_3494_ = lean_ctor_get(v___x_3482_, 0);
v_isSharedCheck_3501_ = !lean_is_exclusive(v___x_3482_);
if (v_isSharedCheck_3501_ == 0)
{
v___x_3496_ = v___x_3482_;
v_isShared_3497_ = v_isSharedCheck_3501_;
goto v_resetjp_3495_;
}
else
{
lean_inc(v_a_3494_);
lean_dec(v___x_3482_);
v___x_3496_ = lean_box(0);
v_isShared_3497_ = v_isSharedCheck_3501_;
goto v_resetjp_3495_;
}
v_resetjp_3495_:
{
lean_object* v___x_3499_; 
if (v_isShared_3497_ == 0)
{
v___x_3499_ = v___x_3496_;
goto v_reusejp_3498_;
}
else
{
lean_object* v_reuseFailAlloc_3500_; 
v_reuseFailAlloc_3500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3500_, 0, v_a_3494_);
v___x_3499_ = v_reuseFailAlloc_3500_;
goto v_reusejp_3498_;
}
v_reusejp_3498_:
{
return v___x_3499_;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_3472_ = stack[0].m_obj;
lean_object* v___x_3473_ = stack[1].m_obj;
lean_object* v___x_3474_ = stack[2].m_obj;
uint8_t v___x_3475_ = stack[3].m_num;
lean_object* v___x_3476_ = stack[4].m_obj;
lean_object* v___y_3477_ = stack[5].m_obj;
lean_object* v___y_3478_ = stack[6].m_obj;
lean_object* v___y_3479_ = stack[7].m_obj;
lean_object* v___y_3480_ = stack[8].m_obj;
lean_object* v_res_3502_;
v_res_3502_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3___lam__0(v_mvarId_3472_, v___x_3473_, v___x_3474_, v___x_3475_, v___x_3476_, v___y_3477_, v___y_3478_, v___y_3479_, v___y_3480_);
stack->m_obj
 = v_res_3502_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3___lam__0___boxed(lean_object* v_mvarId_3503_, lean_object* v___x_3504_, lean_object* v___x_3505_, lean_object* v___x_3506_, lean_object* v___x_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_, lean_object* v___y_3510_, lean_object* v___y_3511_, lean_object* v___y_3512_){
_start:
{
uint8_t v___x_6332__boxed_3513_; lean_object* v_res_3514_; 
v___x_6332__boxed_3513_ = lean_unbox(v___x_3506_);
v_res_3514_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3___lam__0(v_mvarId_3503_, v___x_3504_, v___x_3505_, v___x_6332__boxed_3513_, v___x_3507_, v___y_3508_, v___y_3509_, v___y_3510_, v___y_3511_);
lean_dec(v___y_3511_);
lean_dec_ref(v___y_3510_);
lean_dec(v___y_3509_);
lean_dec_ref(v___y_3508_);
return v_res_3514_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5(lean_object* v_p_3520_, lean_object* v_mvarId_3521_, lean_object* v_as_3522_, size_t v_sz_3523_, size_t v_i_3524_, lean_object* v_b_3525_, lean_object* v___y_3526_, lean_object* v___y_3527_, lean_object* v___y_3528_, lean_object* v___y_3529_){
_start:
{
uint8_t v___x_3531_; 
v___x_3531_ = lean_usize_dec_lt(v_i_3524_, v_sz_3523_);
if (v___x_3531_ == 0)
{
lean_object* v___x_3532_; 
lean_dec(v_mvarId_3521_);
lean_dec_ref(v_p_3520_);
v___x_3532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3532_, 0, v_b_3525_);
return v___x_3532_;
}
else
{
lean_object* v_snd_3533_; lean_object* v___x_3535_; uint8_t v_isShared_3536_; uint8_t v_isSharedCheck_3601_; 
v_snd_3533_ = lean_ctor_get(v_b_3525_, 1);
v_isSharedCheck_3601_ = !lean_is_exclusive(v_b_3525_);
if (v_isSharedCheck_3601_ == 0)
{
lean_object* v_unused_3602_; 
v_unused_3602_ = lean_ctor_get(v_b_3525_, 0);
lean_dec(v_unused_3602_);
v___x_3535_ = v_b_3525_;
v_isShared_3536_ = v_isSharedCheck_3601_;
goto v_resetjp_3534_;
}
else
{
lean_inc(v_snd_3533_);
lean_dec(v_b_3525_);
v___x_3535_ = lean_box(0);
v_isShared_3536_ = v_isSharedCheck_3601_;
goto v_resetjp_3534_;
}
v_resetjp_3534_:
{
lean_object* v___x_3537_; lean_object* v_a_3539_; lean_object* v_a_3546_; 
v___x_3537_ = lean_box(0);
v_a_3546_ = lean_array_uget(v_as_3522_, v_i_3524_);
if (lean_obj_tag(v_a_3546_) == 0)
{
v_a_3539_ = v_snd_3533_;
goto v___jp_3538_;
}
else
{
lean_object* v_val_3547_; lean_object* v___x_3549_; uint8_t v_isShared_3550_; uint8_t v_isSharedCheck_3600_; 
v_val_3547_ = lean_ctor_get(v_a_3546_, 0);
v_isSharedCheck_3600_ = !lean_is_exclusive(v_a_3546_);
if (v_isSharedCheck_3600_ == 0)
{
v___x_3549_ = v_a_3546_;
v_isShared_3550_ = v_isSharedCheck_3600_;
goto v_resetjp_3548_;
}
else
{
lean_inc(v_val_3547_);
lean_dec(v_a_3546_);
v___x_3549_ = lean_box(0);
v_isShared_3550_ = v_isSharedCheck_3600_;
goto v_resetjp_3548_;
}
v_resetjp_3548_:
{
lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; 
v___x_3551_ = lean_box(0);
v___x_3552_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5___closed__0));
lean_inc_ref(v_p_3520_);
lean_inc(v___y_3529_);
lean_inc_ref(v___y_3528_);
lean_inc(v___y_3527_);
lean_inc_ref(v___y_3526_);
lean_inc(v_val_3547_);
v___x_3553_ = lean_apply_6(v_p_3520_, v_val_3547_, v___y_3526_, v___y_3527_, v___y_3528_, v___y_3529_, lean_box(0));
if (lean_obj_tag(v___x_3553_) == 0)
{
lean_object* v_a_3554_; uint8_t v___x_3555_; 
v_a_3554_ = lean_ctor_get(v___x_3553_, 0);
lean_inc(v_a_3554_);
lean_dec_ref_known(v___x_3553_, 1);
v___x_3555_ = lean_unbox(v_a_3554_);
lean_dec(v_a_3554_);
if (v___x_3555_ == 0)
{
lean_del_object(v___x_3549_);
lean_dec(v_val_3547_);
lean_dec(v_snd_3533_);
v_a_3539_ = v___x_3552_;
goto v___jp_3538_;
}
else
{
lean_object* v___x_3556_; lean_object* v___x_3557_; uint8_t v___x_3558_; lean_object* v___x_3559_; lean_object* v___f_3560_; lean_object* v___x_3561_; 
v___x_3556_ = l_Lean_LocalDecl_fvarId(v_val_3547_);
lean_dec(v_val_3547_);
v___x_3557_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5___closed__1));
v___x_3558_ = 0;
v___x_3559_ = lean_box(v___x_3558_);
lean_inc(v_mvarId_3521_);
v___f_3560_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3___lam__0___boxed), 10, 5);
lean_closure_set(v___f_3560_, 0, v_mvarId_3521_);
lean_closure_set(v___f_3560_, 1, v___x_3556_);
lean_closure_set(v___f_3560_, 2, v___x_3557_);
lean_closure_set(v___f_3560_, 3, v___x_3559_);
lean_closure_set(v___f_3560_, 4, v___x_3537_);
v___x_3561_ = l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1___redArg(v___f_3560_, v___y_3526_, v___y_3527_, v___y_3528_, v___y_3529_);
if (lean_obj_tag(v___x_3561_) == 0)
{
lean_object* v_a_3562_; lean_object* v___x_3564_; uint8_t v_isShared_3565_; uint8_t v_isSharedCheck_3583_; 
v_a_3562_ = lean_ctor_get(v___x_3561_, 0);
v_isSharedCheck_3583_ = !lean_is_exclusive(v___x_3561_);
if (v_isSharedCheck_3583_ == 0)
{
v___x_3564_ = v___x_3561_;
v_isShared_3565_ = v_isSharedCheck_3583_;
goto v_resetjp_3563_;
}
else
{
lean_inc(v_a_3562_);
lean_dec(v___x_3561_);
v___x_3564_ = lean_box(0);
v_isShared_3565_ = v_isSharedCheck_3583_;
goto v_resetjp_3563_;
}
v_resetjp_3563_:
{
if (lean_obj_tag(v_a_3562_) == 0)
{
lean_del_object(v___x_3564_);
lean_del_object(v___x_3549_);
lean_dec(v_snd_3533_);
v_a_3539_ = v___x_3552_;
goto v___jp_3538_;
}
else
{
lean_object* v___x_3567_; 
lean_del_object(v___x_3535_);
lean_dec(v_mvarId_3521_);
lean_dec_ref(v_p_3520_);
lean_inc_ref(v_a_3562_);
if (v_isShared_3550_ == 0)
{
lean_ctor_set(v___x_3549_, 0, v_a_3562_);
v___x_3567_ = v___x_3549_;
goto v_reusejp_3566_;
}
else
{
lean_object* v_reuseFailAlloc_3582_; 
v_reuseFailAlloc_3582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3582_, 0, v_a_3562_);
v___x_3567_ = v_reuseFailAlloc_3582_;
goto v_reusejp_3566_;
}
v_reusejp_3566_:
{
lean_object* v___x_3569_; uint8_t v_isShared_3570_; uint8_t v_isSharedCheck_3580_; 
v_isSharedCheck_3580_ = !lean_is_exclusive(v_a_3562_);
if (v_isSharedCheck_3580_ == 0)
{
lean_object* v_unused_3581_; 
v_unused_3581_ = lean_ctor_get(v_a_3562_, 0);
lean_dec(v_unused_3581_);
v___x_3569_ = v_a_3562_;
v_isShared_3570_ = v_isSharedCheck_3580_;
goto v_resetjp_3568_;
}
else
{
lean_dec(v_a_3562_);
v___x_3569_ = lean_box(0);
v_isShared_3570_ = v_isSharedCheck_3580_;
goto v_resetjp_3568_;
}
v_resetjp_3568_:
{
lean_object* v___x_3571_; lean_object* v___x_3573_; 
v___x_3571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3571_, 0, v___x_3567_);
lean_ctor_set(v___x_3571_, 1, v___x_3551_);
if (v_isShared_3570_ == 0)
{
lean_ctor_set_tag(v___x_3569_, 0);
lean_ctor_set(v___x_3569_, 0, v___x_3571_);
v___x_3573_ = v___x_3569_;
goto v_reusejp_3572_;
}
else
{
lean_object* v_reuseFailAlloc_3579_; 
v_reuseFailAlloc_3579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3579_, 0, v___x_3571_);
v___x_3573_ = v_reuseFailAlloc_3579_;
goto v_reusejp_3572_;
}
v_reusejp_3572_:
{
lean_object* v___x_3574_; lean_object* v___x_3575_; lean_object* v___x_3577_; 
v___x_3574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3574_, 0, v___x_3573_);
v___x_3575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3575_, 0, v___x_3574_);
lean_ctor_set(v___x_3575_, 1, v_snd_3533_);
if (v_isShared_3565_ == 0)
{
lean_ctor_set(v___x_3564_, 0, v___x_3575_);
v___x_3577_ = v___x_3564_;
goto v_reusejp_3576_;
}
else
{
lean_object* v_reuseFailAlloc_3578_; 
v_reuseFailAlloc_3578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3578_, 0, v___x_3575_);
v___x_3577_ = v_reuseFailAlloc_3578_;
goto v_reusejp_3576_;
}
v_reusejp_3576_:
{
return v___x_3577_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3584_; lean_object* v___x_3586_; uint8_t v_isShared_3587_; uint8_t v_isSharedCheck_3591_; 
lean_del_object(v___x_3549_);
lean_del_object(v___x_3535_);
lean_dec(v_snd_3533_);
lean_dec(v_mvarId_3521_);
lean_dec_ref(v_p_3520_);
v_a_3584_ = lean_ctor_get(v___x_3561_, 0);
v_isSharedCheck_3591_ = !lean_is_exclusive(v___x_3561_);
if (v_isSharedCheck_3591_ == 0)
{
v___x_3586_ = v___x_3561_;
v_isShared_3587_ = v_isSharedCheck_3591_;
goto v_resetjp_3585_;
}
else
{
lean_inc(v_a_3584_);
lean_dec(v___x_3561_);
v___x_3586_ = lean_box(0);
v_isShared_3587_ = v_isSharedCheck_3591_;
goto v_resetjp_3585_;
}
v_resetjp_3585_:
{
lean_object* v___x_3589_; 
if (v_isShared_3587_ == 0)
{
v___x_3589_ = v___x_3586_;
goto v_reusejp_3588_;
}
else
{
lean_object* v_reuseFailAlloc_3590_; 
v_reuseFailAlloc_3590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3590_, 0, v_a_3584_);
v___x_3589_ = v_reuseFailAlloc_3590_;
goto v_reusejp_3588_;
}
v_reusejp_3588_:
{
return v___x_3589_;
}
}
}
}
}
else
{
lean_object* v_a_3592_; lean_object* v___x_3594_; uint8_t v_isShared_3595_; uint8_t v_isSharedCheck_3599_; 
lean_del_object(v___x_3549_);
lean_dec(v_val_3547_);
lean_del_object(v___x_3535_);
lean_dec(v_snd_3533_);
lean_dec(v_mvarId_3521_);
lean_dec_ref(v_p_3520_);
v_a_3592_ = lean_ctor_get(v___x_3553_, 0);
v_isSharedCheck_3599_ = !lean_is_exclusive(v___x_3553_);
if (v_isSharedCheck_3599_ == 0)
{
v___x_3594_ = v___x_3553_;
v_isShared_3595_ = v_isSharedCheck_3599_;
goto v_resetjp_3593_;
}
else
{
lean_inc(v_a_3592_);
lean_dec(v___x_3553_);
v___x_3594_ = lean_box(0);
v_isShared_3595_ = v_isSharedCheck_3599_;
goto v_resetjp_3593_;
}
v_resetjp_3593_:
{
lean_object* v___x_3597_; 
if (v_isShared_3595_ == 0)
{
v___x_3597_ = v___x_3594_;
goto v_reusejp_3596_;
}
else
{
lean_object* v_reuseFailAlloc_3598_; 
v_reuseFailAlloc_3598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3598_, 0, v_a_3592_);
v___x_3597_ = v_reuseFailAlloc_3598_;
goto v_reusejp_3596_;
}
v_reusejp_3596_:
{
return v___x_3597_;
}
}
}
}
}
v___jp_3538_:
{
lean_object* v___x_3541_; 
if (v_isShared_3536_ == 0)
{
lean_ctor_set(v___x_3535_, 1, v_a_3539_);
lean_ctor_set(v___x_3535_, 0, v___x_3537_);
v___x_3541_ = v___x_3535_;
goto v_reusejp_3540_;
}
else
{
lean_object* v_reuseFailAlloc_3545_; 
v_reuseFailAlloc_3545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3545_, 0, v___x_3537_);
lean_ctor_set(v_reuseFailAlloc_3545_, 1, v_a_3539_);
v___x_3541_ = v_reuseFailAlloc_3545_;
goto v_reusejp_3540_;
}
v_reusejp_3540_:
{
size_t v___x_3542_; size_t v___x_3543_; 
v___x_3542_ = ((size_t)1ULL);
v___x_3543_ = lean_usize_add(v_i_3524_, v___x_3542_);
v_i_3524_ = v___x_3543_;
v_b_3525_ = v___x_3541_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_3520_ = stack[0].m_obj;
lean_object* v_mvarId_3521_ = stack[1].m_obj;
lean_object* v_as_3522_ = stack[2].m_obj;
size_t v_sz_3523_ = stack[3].m_num;
size_t v_i_3524_ = stack[4].m_num;
lean_object* v_b_3525_ = stack[5].m_obj;
lean_object* v___y_3526_ = stack[6].m_obj;
lean_object* v___y_3527_ = stack[7].m_obj;
lean_object* v___y_3528_ = stack[8].m_obj;
lean_object* v___y_3529_ = stack[9].m_obj;
lean_object* v_res_3603_;
v_res_3603_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5(v_p_3520_, v_mvarId_3521_, v_as_3522_, v_sz_3523_, v_i_3524_, v_b_3525_, v___y_3526_, v___y_3527_, v___y_3528_, v___y_3529_);
stack->m_obj
 = v_res_3603_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5___boxed(lean_object* v_p_3604_, lean_object* v_mvarId_3605_, lean_object* v_as_3606_, lean_object* v_sz_3607_, lean_object* v_i_3608_, lean_object* v_b_3609_, lean_object* v___y_3610_, lean_object* v___y_3611_, lean_object* v___y_3612_, lean_object* v___y_3613_, lean_object* v___y_3614_){
_start:
{
size_t v_sz_boxed_3615_; size_t v_i_boxed_3616_; lean_object* v_res_3617_; 
v_sz_boxed_3615_ = lean_unbox_usize(v_sz_3607_);
lean_dec(v_sz_3607_);
v_i_boxed_3616_ = lean_unbox_usize(v_i_3608_);
lean_dec(v_i_3608_);
v_res_3617_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5(v_p_3604_, v_mvarId_3605_, v_as_3606_, v_sz_boxed_3615_, v_i_boxed_3616_, v_b_3609_, v___y_3610_, v___y_3611_, v___y_3612_, v___y_3613_);
lean_dec(v___y_3613_);
lean_dec_ref(v___y_3612_);
lean_dec(v___y_3611_);
lean_dec_ref(v___y_3610_);
lean_dec_ref(v_as_3606_);
return v_res_3617_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4(lean_object* v_p_3618_, lean_object* v_mvarId_3619_, lean_object* v_as_3620_, size_t v_sz_3621_, size_t v_i_3622_, lean_object* v_b_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_){
_start:
{
uint8_t v___x_3629_; 
v___x_3629_ = lean_usize_dec_lt(v_i_3622_, v_sz_3621_);
if (v___x_3629_ == 0)
{
lean_object* v___x_3630_; 
lean_dec(v_mvarId_3619_);
lean_dec_ref(v_p_3618_);
v___x_3630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3630_, 0, v_b_3623_);
return v___x_3630_;
}
else
{
lean_object* v_snd_3631_; lean_object* v___x_3633_; uint8_t v_isShared_3634_; uint8_t v_isSharedCheck_3699_; 
v_snd_3631_ = lean_ctor_get(v_b_3623_, 1);
v_isSharedCheck_3699_ = !lean_is_exclusive(v_b_3623_);
if (v_isSharedCheck_3699_ == 0)
{
lean_object* v_unused_3700_; 
v_unused_3700_ = lean_ctor_get(v_b_3623_, 0);
lean_dec(v_unused_3700_);
v___x_3633_ = v_b_3623_;
v_isShared_3634_ = v_isSharedCheck_3699_;
goto v_resetjp_3632_;
}
else
{
lean_inc(v_snd_3631_);
lean_dec(v_b_3623_);
v___x_3633_ = lean_box(0);
v_isShared_3634_ = v_isSharedCheck_3699_;
goto v_resetjp_3632_;
}
v_resetjp_3632_:
{
lean_object* v___x_3635_; lean_object* v_a_3637_; lean_object* v_a_3644_; 
v___x_3635_ = lean_box(0);
v_a_3644_ = lean_array_uget(v_as_3620_, v_i_3622_);
if (lean_obj_tag(v_a_3644_) == 0)
{
v_a_3637_ = v_snd_3631_;
goto v___jp_3636_;
}
else
{
lean_object* v_val_3645_; lean_object* v___x_3647_; uint8_t v_isShared_3648_; uint8_t v_isSharedCheck_3698_; 
v_val_3645_ = lean_ctor_get(v_a_3644_, 0);
v_isSharedCheck_3698_ = !lean_is_exclusive(v_a_3644_);
if (v_isSharedCheck_3698_ == 0)
{
v___x_3647_ = v_a_3644_;
v_isShared_3648_ = v_isSharedCheck_3698_;
goto v_resetjp_3646_;
}
else
{
lean_inc(v_val_3645_);
lean_dec(v_a_3644_);
v___x_3647_ = lean_box(0);
v_isShared_3648_ = v_isSharedCheck_3698_;
goto v_resetjp_3646_;
}
v_resetjp_3646_:
{
lean_object* v___x_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; 
v___x_3649_ = lean_box(0);
v___x_3650_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5___closed__0));
lean_inc_ref(v_p_3618_);
lean_inc(v___y_3627_);
lean_inc_ref(v___y_3626_);
lean_inc(v___y_3625_);
lean_inc_ref(v___y_3624_);
lean_inc(v_val_3645_);
v___x_3651_ = lean_apply_6(v_p_3618_, v_val_3645_, v___y_3624_, v___y_3625_, v___y_3626_, v___y_3627_, lean_box(0));
if (lean_obj_tag(v___x_3651_) == 0)
{
lean_object* v_a_3652_; uint8_t v___x_3653_; 
v_a_3652_ = lean_ctor_get(v___x_3651_, 0);
lean_inc(v_a_3652_);
lean_dec_ref_known(v___x_3651_, 1);
v___x_3653_ = lean_unbox(v_a_3652_);
lean_dec(v_a_3652_);
if (v___x_3653_ == 0)
{
lean_del_object(v___x_3647_);
lean_dec(v_val_3645_);
lean_dec(v_snd_3631_);
v_a_3637_ = v___x_3650_;
goto v___jp_3636_;
}
else
{
lean_object* v___x_3654_; lean_object* v___x_3655_; uint8_t v___x_3656_; lean_object* v___x_3657_; lean_object* v___f_3658_; lean_object* v___x_3659_; 
v___x_3654_ = l_Lean_LocalDecl_fvarId(v_val_3645_);
lean_dec(v_val_3645_);
v___x_3655_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5___closed__1));
v___x_3656_ = 0;
v___x_3657_ = lean_box(v___x_3656_);
lean_inc(v_mvarId_3619_);
v___f_3658_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3___lam__0___boxed), 10, 5);
lean_closure_set(v___f_3658_, 0, v_mvarId_3619_);
lean_closure_set(v___f_3658_, 1, v___x_3654_);
lean_closure_set(v___f_3658_, 2, v___x_3655_);
lean_closure_set(v___f_3658_, 3, v___x_3657_);
lean_closure_set(v___f_3658_, 4, v___x_3635_);
v___x_3659_ = l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1___redArg(v___f_3658_, v___y_3624_, v___y_3625_, v___y_3626_, v___y_3627_);
if (lean_obj_tag(v___x_3659_) == 0)
{
lean_object* v_a_3660_; lean_object* v___x_3662_; uint8_t v_isShared_3663_; uint8_t v_isSharedCheck_3681_; 
v_a_3660_ = lean_ctor_get(v___x_3659_, 0);
v_isSharedCheck_3681_ = !lean_is_exclusive(v___x_3659_);
if (v_isSharedCheck_3681_ == 0)
{
v___x_3662_ = v___x_3659_;
v_isShared_3663_ = v_isSharedCheck_3681_;
goto v_resetjp_3661_;
}
else
{
lean_inc(v_a_3660_);
lean_dec(v___x_3659_);
v___x_3662_ = lean_box(0);
v_isShared_3663_ = v_isSharedCheck_3681_;
goto v_resetjp_3661_;
}
v_resetjp_3661_:
{
if (lean_obj_tag(v_a_3660_) == 0)
{
lean_del_object(v___x_3662_);
lean_del_object(v___x_3647_);
lean_dec(v_snd_3631_);
v_a_3637_ = v___x_3650_;
goto v___jp_3636_;
}
else
{
lean_object* v___x_3665_; 
lean_del_object(v___x_3633_);
lean_dec(v_mvarId_3619_);
lean_dec_ref(v_p_3618_);
lean_inc_ref(v_a_3660_);
if (v_isShared_3648_ == 0)
{
lean_ctor_set(v___x_3647_, 0, v_a_3660_);
v___x_3665_ = v___x_3647_;
goto v_reusejp_3664_;
}
else
{
lean_object* v_reuseFailAlloc_3680_; 
v_reuseFailAlloc_3680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3680_, 0, v_a_3660_);
v___x_3665_ = v_reuseFailAlloc_3680_;
goto v_reusejp_3664_;
}
v_reusejp_3664_:
{
lean_object* v___x_3667_; uint8_t v_isShared_3668_; uint8_t v_isSharedCheck_3678_; 
v_isSharedCheck_3678_ = !lean_is_exclusive(v_a_3660_);
if (v_isSharedCheck_3678_ == 0)
{
lean_object* v_unused_3679_; 
v_unused_3679_ = lean_ctor_get(v_a_3660_, 0);
lean_dec(v_unused_3679_);
v___x_3667_ = v_a_3660_;
v_isShared_3668_ = v_isSharedCheck_3678_;
goto v_resetjp_3666_;
}
else
{
lean_dec(v_a_3660_);
v___x_3667_ = lean_box(0);
v_isShared_3668_ = v_isSharedCheck_3678_;
goto v_resetjp_3666_;
}
v_resetjp_3666_:
{
lean_object* v___x_3669_; lean_object* v___x_3671_; 
v___x_3669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3669_, 0, v___x_3665_);
lean_ctor_set(v___x_3669_, 1, v___x_3649_);
if (v_isShared_3668_ == 0)
{
lean_ctor_set_tag(v___x_3667_, 0);
lean_ctor_set(v___x_3667_, 0, v___x_3669_);
v___x_3671_ = v___x_3667_;
goto v_reusejp_3670_;
}
else
{
lean_object* v_reuseFailAlloc_3677_; 
v_reuseFailAlloc_3677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3677_, 0, v___x_3669_);
v___x_3671_ = v_reuseFailAlloc_3677_;
goto v_reusejp_3670_;
}
v_reusejp_3670_:
{
lean_object* v___x_3672_; lean_object* v___x_3673_; lean_object* v___x_3675_; 
v___x_3672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3672_, 0, v___x_3671_);
v___x_3673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3673_, 0, v___x_3672_);
lean_ctor_set(v___x_3673_, 1, v_snd_3631_);
if (v_isShared_3663_ == 0)
{
lean_ctor_set(v___x_3662_, 0, v___x_3673_);
v___x_3675_ = v___x_3662_;
goto v_reusejp_3674_;
}
else
{
lean_object* v_reuseFailAlloc_3676_; 
v_reuseFailAlloc_3676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3676_, 0, v___x_3673_);
v___x_3675_ = v_reuseFailAlloc_3676_;
goto v_reusejp_3674_;
}
v_reusejp_3674_:
{
return v___x_3675_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3682_; lean_object* v___x_3684_; uint8_t v_isShared_3685_; uint8_t v_isSharedCheck_3689_; 
lean_del_object(v___x_3647_);
lean_del_object(v___x_3633_);
lean_dec(v_snd_3631_);
lean_dec(v_mvarId_3619_);
lean_dec_ref(v_p_3618_);
v_a_3682_ = lean_ctor_get(v___x_3659_, 0);
v_isSharedCheck_3689_ = !lean_is_exclusive(v___x_3659_);
if (v_isSharedCheck_3689_ == 0)
{
v___x_3684_ = v___x_3659_;
v_isShared_3685_ = v_isSharedCheck_3689_;
goto v_resetjp_3683_;
}
else
{
lean_inc(v_a_3682_);
lean_dec(v___x_3659_);
v___x_3684_ = lean_box(0);
v_isShared_3685_ = v_isSharedCheck_3689_;
goto v_resetjp_3683_;
}
v_resetjp_3683_:
{
lean_object* v___x_3687_; 
if (v_isShared_3685_ == 0)
{
v___x_3687_ = v___x_3684_;
goto v_reusejp_3686_;
}
else
{
lean_object* v_reuseFailAlloc_3688_; 
v_reuseFailAlloc_3688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3688_, 0, v_a_3682_);
v___x_3687_ = v_reuseFailAlloc_3688_;
goto v_reusejp_3686_;
}
v_reusejp_3686_:
{
return v___x_3687_;
}
}
}
}
}
else
{
lean_object* v_a_3690_; lean_object* v___x_3692_; uint8_t v_isShared_3693_; uint8_t v_isSharedCheck_3697_; 
lean_del_object(v___x_3647_);
lean_dec(v_val_3645_);
lean_del_object(v___x_3633_);
lean_dec(v_snd_3631_);
lean_dec(v_mvarId_3619_);
lean_dec_ref(v_p_3618_);
v_a_3690_ = lean_ctor_get(v___x_3651_, 0);
v_isSharedCheck_3697_ = !lean_is_exclusive(v___x_3651_);
if (v_isSharedCheck_3697_ == 0)
{
v___x_3692_ = v___x_3651_;
v_isShared_3693_ = v_isSharedCheck_3697_;
goto v_resetjp_3691_;
}
else
{
lean_inc(v_a_3690_);
lean_dec(v___x_3651_);
v___x_3692_ = lean_box(0);
v_isShared_3693_ = v_isSharedCheck_3697_;
goto v_resetjp_3691_;
}
v_resetjp_3691_:
{
lean_object* v___x_3695_; 
if (v_isShared_3693_ == 0)
{
v___x_3695_ = v___x_3692_;
goto v_reusejp_3694_;
}
else
{
lean_object* v_reuseFailAlloc_3696_; 
v_reuseFailAlloc_3696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3696_, 0, v_a_3690_);
v___x_3695_ = v_reuseFailAlloc_3696_;
goto v_reusejp_3694_;
}
v_reusejp_3694_:
{
return v___x_3695_;
}
}
}
}
}
v___jp_3636_:
{
lean_object* v___x_3639_; 
if (v_isShared_3634_ == 0)
{
lean_ctor_set(v___x_3633_, 1, v_a_3637_);
lean_ctor_set(v___x_3633_, 0, v___x_3635_);
v___x_3639_ = v___x_3633_;
goto v_reusejp_3638_;
}
else
{
lean_object* v_reuseFailAlloc_3643_; 
v_reuseFailAlloc_3643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3643_, 0, v___x_3635_);
lean_ctor_set(v_reuseFailAlloc_3643_, 1, v_a_3637_);
v___x_3639_ = v_reuseFailAlloc_3643_;
goto v_reusejp_3638_;
}
v_reusejp_3638_:
{
size_t v___x_3640_; size_t v___x_3641_; lean_object* v___x_3642_; 
v___x_3640_ = ((size_t)1ULL);
v___x_3641_ = lean_usize_add(v_i_3622_, v___x_3640_);
v___x_3642_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5(v_p_3618_, v_mvarId_3619_, v_as_3620_, v_sz_3621_, v___x_3641_, v___x_3639_, v___y_3624_, v___y_3625_, v___y_3626_, v___y_3627_);
return v___x_3642_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_3618_ = stack[0].m_obj;
lean_object* v_mvarId_3619_ = stack[1].m_obj;
lean_object* v_as_3620_ = stack[2].m_obj;
size_t v_sz_3621_ = stack[3].m_num;
size_t v_i_3622_ = stack[4].m_num;
lean_object* v_b_3623_ = stack[5].m_obj;
lean_object* v___y_3624_ = stack[6].m_obj;
lean_object* v___y_3625_ = stack[7].m_obj;
lean_object* v___y_3626_ = stack[8].m_obj;
lean_object* v___y_3627_ = stack[9].m_obj;
lean_object* v_res_3701_;
v_res_3701_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4(v_p_3618_, v_mvarId_3619_, v_as_3620_, v_sz_3621_, v_i_3622_, v_b_3623_, v___y_3624_, v___y_3625_, v___y_3626_, v___y_3627_);
stack->m_obj
 = v_res_3701_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4___boxed(lean_object* v_p_3702_, lean_object* v_mvarId_3703_, lean_object* v_as_3704_, lean_object* v_sz_3705_, lean_object* v_i_3706_, lean_object* v_b_3707_, lean_object* v___y_3708_, lean_object* v___y_3709_, lean_object* v___y_3710_, lean_object* v___y_3711_, lean_object* v___y_3712_){
_start:
{
size_t v_sz_boxed_3713_; size_t v_i_boxed_3714_; lean_object* v_res_3715_; 
v_sz_boxed_3713_ = lean_unbox_usize(v_sz_3705_);
lean_dec(v_sz_3705_);
v_i_boxed_3714_ = lean_unbox_usize(v_i_3706_);
lean_dec(v_i_3706_);
v_res_3715_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4(v_p_3702_, v_mvarId_3703_, v_as_3704_, v_sz_boxed_3713_, v_i_boxed_3714_, v_b_3707_, v___y_3708_, v___y_3709_, v___y_3710_, v___y_3711_);
lean_dec(v___y_3711_);
lean_dec_ref(v___y_3710_);
lean_dec(v___y_3709_);
lean_dec_ref(v___y_3708_);
lean_dec_ref(v_as_3704_);
return v_res_3715_;
}
}
lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2(lean_object* v_init_3716_, lean_object* v_p_3717_, lean_object* v_mvarId_3718_, lean_object* v_n_3719_, lean_object* v_b_3720_, lean_object* v___y_3721_, lean_object* v___y_3722_, lean_object* v___y_3723_, lean_object* v___y_3724_){
_start:
{
if (lean_obj_tag(v_n_3719_) == 0)
{
lean_object* v_cs_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; size_t v_sz_3729_; size_t v___x_3730_; lean_object* v___x_3731_; 
v_cs_3726_ = lean_ctor_get(v_n_3719_, 0);
v___x_3727_ = lean_box(0);
v___x_3728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3728_, 0, v___x_3727_);
lean_ctor_set(v___x_3728_, 1, v_b_3720_);
v_sz_3729_ = lean_array_size(v_cs_3726_);
v___x_3730_ = ((size_t)0ULL);
v___x_3731_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__3(v_init_3716_, v_p_3717_, v_mvarId_3718_, v_cs_3726_, v_sz_3729_, v___x_3730_, v___x_3728_, v___y_3721_, v___y_3722_, v___y_3723_, v___y_3724_);
if (lean_obj_tag(v___x_3731_) == 0)
{
lean_object* v_a_3732_; lean_object* v___x_3734_; uint8_t v_isShared_3735_; uint8_t v_isSharedCheck_3746_; 
v_a_3732_ = lean_ctor_get(v___x_3731_, 0);
v_isSharedCheck_3746_ = !lean_is_exclusive(v___x_3731_);
if (v_isSharedCheck_3746_ == 0)
{
v___x_3734_ = v___x_3731_;
v_isShared_3735_ = v_isSharedCheck_3746_;
goto v_resetjp_3733_;
}
else
{
lean_inc(v_a_3732_);
lean_dec(v___x_3731_);
v___x_3734_ = lean_box(0);
v_isShared_3735_ = v_isSharedCheck_3746_;
goto v_resetjp_3733_;
}
v_resetjp_3733_:
{
lean_object* v_fst_3736_; 
v_fst_3736_ = lean_ctor_get(v_a_3732_, 0);
if (lean_obj_tag(v_fst_3736_) == 0)
{
lean_object* v_snd_3737_; lean_object* v___x_3738_; lean_object* v___x_3740_; 
v_snd_3737_ = lean_ctor_get(v_a_3732_, 1);
lean_inc(v_snd_3737_);
lean_dec(v_a_3732_);
v___x_3738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3738_, 0, v_snd_3737_);
if (v_isShared_3735_ == 0)
{
lean_ctor_set(v___x_3734_, 0, v___x_3738_);
v___x_3740_ = v___x_3734_;
goto v_reusejp_3739_;
}
else
{
lean_object* v_reuseFailAlloc_3741_; 
v_reuseFailAlloc_3741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3741_, 0, v___x_3738_);
v___x_3740_ = v_reuseFailAlloc_3741_;
goto v_reusejp_3739_;
}
v_reusejp_3739_:
{
return v___x_3740_;
}
}
else
{
lean_object* v_val_3742_; lean_object* v___x_3744_; 
lean_inc_ref(v_fst_3736_);
lean_dec(v_a_3732_);
v_val_3742_ = lean_ctor_get(v_fst_3736_, 0);
lean_inc(v_val_3742_);
lean_dec_ref_known(v_fst_3736_, 1);
if (v_isShared_3735_ == 0)
{
lean_ctor_set(v___x_3734_, 0, v_val_3742_);
v___x_3744_ = v___x_3734_;
goto v_reusejp_3743_;
}
else
{
lean_object* v_reuseFailAlloc_3745_; 
v_reuseFailAlloc_3745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3745_, 0, v_val_3742_);
v___x_3744_ = v_reuseFailAlloc_3745_;
goto v_reusejp_3743_;
}
v_reusejp_3743_:
{
return v___x_3744_;
}
}
}
}
else
{
lean_object* v_a_3747_; lean_object* v___x_3749_; uint8_t v_isShared_3750_; uint8_t v_isSharedCheck_3754_; 
v_a_3747_ = lean_ctor_get(v___x_3731_, 0);
v_isSharedCheck_3754_ = !lean_is_exclusive(v___x_3731_);
if (v_isSharedCheck_3754_ == 0)
{
v___x_3749_ = v___x_3731_;
v_isShared_3750_ = v_isSharedCheck_3754_;
goto v_resetjp_3748_;
}
else
{
lean_inc(v_a_3747_);
lean_dec(v___x_3731_);
v___x_3749_ = lean_box(0);
v_isShared_3750_ = v_isSharedCheck_3754_;
goto v_resetjp_3748_;
}
v_resetjp_3748_:
{
lean_object* v___x_3752_; 
if (v_isShared_3750_ == 0)
{
v___x_3752_ = v___x_3749_;
goto v_reusejp_3751_;
}
else
{
lean_object* v_reuseFailAlloc_3753_; 
v_reuseFailAlloc_3753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3753_, 0, v_a_3747_);
v___x_3752_ = v_reuseFailAlloc_3753_;
goto v_reusejp_3751_;
}
v_reusejp_3751_:
{
return v___x_3752_;
}
}
}
}
else
{
lean_object* v_vs_3755_; lean_object* v___x_3756_; lean_object* v___x_3757_; size_t v_sz_3758_; size_t v___x_3759_; lean_object* v___x_3760_; 
v_vs_3755_ = lean_ctor_get(v_n_3719_, 0);
v___x_3756_ = lean_box(0);
v___x_3757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3757_, 0, v___x_3756_);
lean_ctor_set(v___x_3757_, 1, v_b_3720_);
v_sz_3758_ = lean_array_size(v_vs_3755_);
v___x_3759_ = ((size_t)0ULL);
v___x_3760_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4(v_p_3717_, v_mvarId_3718_, v_vs_3755_, v_sz_3758_, v___x_3759_, v___x_3757_, v___y_3721_, v___y_3722_, v___y_3723_, v___y_3724_);
if (lean_obj_tag(v___x_3760_) == 0)
{
lean_object* v_a_3761_; lean_object* v___x_3763_; uint8_t v_isShared_3764_; uint8_t v_isSharedCheck_3775_; 
v_a_3761_ = lean_ctor_get(v___x_3760_, 0);
v_isSharedCheck_3775_ = !lean_is_exclusive(v___x_3760_);
if (v_isSharedCheck_3775_ == 0)
{
v___x_3763_ = v___x_3760_;
v_isShared_3764_ = v_isSharedCheck_3775_;
goto v_resetjp_3762_;
}
else
{
lean_inc(v_a_3761_);
lean_dec(v___x_3760_);
v___x_3763_ = lean_box(0);
v_isShared_3764_ = v_isSharedCheck_3775_;
goto v_resetjp_3762_;
}
v_resetjp_3762_:
{
lean_object* v_fst_3765_; 
v_fst_3765_ = lean_ctor_get(v_a_3761_, 0);
if (lean_obj_tag(v_fst_3765_) == 0)
{
lean_object* v_snd_3766_; lean_object* v___x_3767_; lean_object* v___x_3769_; 
v_snd_3766_ = lean_ctor_get(v_a_3761_, 1);
lean_inc(v_snd_3766_);
lean_dec(v_a_3761_);
v___x_3767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3767_, 0, v_snd_3766_);
if (v_isShared_3764_ == 0)
{
lean_ctor_set(v___x_3763_, 0, v___x_3767_);
v___x_3769_ = v___x_3763_;
goto v_reusejp_3768_;
}
else
{
lean_object* v_reuseFailAlloc_3770_; 
v_reuseFailAlloc_3770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3770_, 0, v___x_3767_);
v___x_3769_ = v_reuseFailAlloc_3770_;
goto v_reusejp_3768_;
}
v_reusejp_3768_:
{
return v___x_3769_;
}
}
else
{
lean_object* v_val_3771_; lean_object* v___x_3773_; 
lean_inc_ref(v_fst_3765_);
lean_dec(v_a_3761_);
v_val_3771_ = lean_ctor_get(v_fst_3765_, 0);
lean_inc(v_val_3771_);
lean_dec_ref_known(v_fst_3765_, 1);
if (v_isShared_3764_ == 0)
{
lean_ctor_set(v___x_3763_, 0, v_val_3771_);
v___x_3773_ = v___x_3763_;
goto v_reusejp_3772_;
}
else
{
lean_object* v_reuseFailAlloc_3774_; 
v_reuseFailAlloc_3774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3774_, 0, v_val_3771_);
v___x_3773_ = v_reuseFailAlloc_3774_;
goto v_reusejp_3772_;
}
v_reusejp_3772_:
{
return v___x_3773_;
}
}
}
}
else
{
lean_object* v_a_3776_; lean_object* v___x_3778_; uint8_t v_isShared_3779_; uint8_t v_isSharedCheck_3783_; 
v_a_3776_ = lean_ctor_get(v___x_3760_, 0);
v_isSharedCheck_3783_ = !lean_is_exclusive(v___x_3760_);
if (v_isSharedCheck_3783_ == 0)
{
v___x_3778_ = v___x_3760_;
v_isShared_3779_ = v_isSharedCheck_3783_;
goto v_resetjp_3777_;
}
else
{
lean_inc(v_a_3776_);
lean_dec(v___x_3760_);
v___x_3778_ = lean_box(0);
v_isShared_3779_ = v_isSharedCheck_3783_;
goto v_resetjp_3777_;
}
v_resetjp_3777_:
{
lean_object* v___x_3781_; 
if (v_isShared_3779_ == 0)
{
v___x_3781_ = v___x_3778_;
goto v_reusejp_3780_;
}
else
{
lean_object* v_reuseFailAlloc_3782_; 
v_reuseFailAlloc_3782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3782_, 0, v_a_3776_);
v___x_3781_ = v_reuseFailAlloc_3782_;
goto v_reusejp_3780_;
}
v_reusejp_3780_:
{
return v___x_3781_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_3716_ = stack[0].m_obj;
lean_object* v_p_3717_ = stack[1].m_obj;
lean_object* v_mvarId_3718_ = stack[2].m_obj;
lean_object* v_n_3719_ = stack[3].m_obj;
lean_object* v_b_3720_ = stack[4].m_obj;
lean_object* v___y_3721_ = stack[5].m_obj;
lean_object* v___y_3722_ = stack[6].m_obj;
lean_object* v___y_3723_ = stack[7].m_obj;
lean_object* v___y_3724_ = stack[8].m_obj;
lean_object* v_res_3784_;
v_res_3784_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2(v_init_3716_, v_p_3717_, v_mvarId_3718_, v_n_3719_, v_b_3720_, v___y_3721_, v___y_3722_, v___y_3723_, v___y_3724_);
stack->m_obj
 = v_res_3784_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__3(lean_object* v_init_3785_, lean_object* v_p_3786_, lean_object* v_mvarId_3787_, lean_object* v_as_3788_, size_t v_sz_3789_, size_t v_i_3790_, lean_object* v_b_3791_, lean_object* v___y_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_){
_start:
{
uint8_t v___x_3797_; 
v___x_3797_ = lean_usize_dec_lt(v_i_3790_, v_sz_3789_);
if (v___x_3797_ == 0)
{
lean_object* v___x_3798_; 
lean_dec(v_mvarId_3787_);
lean_dec_ref(v_p_3786_);
v___x_3798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3798_, 0, v_b_3791_);
return v___x_3798_;
}
else
{
lean_object* v_snd_3799_; lean_object* v___x_3801_; uint8_t v_isShared_3802_; uint8_t v_isSharedCheck_3833_; 
v_snd_3799_ = lean_ctor_get(v_b_3791_, 1);
v_isSharedCheck_3833_ = !lean_is_exclusive(v_b_3791_);
if (v_isSharedCheck_3833_ == 0)
{
lean_object* v_unused_3834_; 
v_unused_3834_ = lean_ctor_get(v_b_3791_, 0);
lean_dec(v_unused_3834_);
v___x_3801_ = v_b_3791_;
v_isShared_3802_ = v_isSharedCheck_3833_;
goto v_resetjp_3800_;
}
else
{
lean_inc(v_snd_3799_);
lean_dec(v_b_3791_);
v___x_3801_ = lean_box(0);
v_isShared_3802_ = v_isSharedCheck_3833_;
goto v_resetjp_3800_;
}
v_resetjp_3800_:
{
lean_object* v___x_3803_; lean_object* v_a_3804_; lean_object* v___x_3805_; 
v___x_3803_ = lean_box(0);
v_a_3804_ = lean_array_uget_borrowed(v_as_3788_, v_i_3790_);
lean_inc(v_snd_3799_);
lean_inc(v_mvarId_3787_);
lean_inc_ref(v_p_3786_);
v___x_3805_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2(v_init_3785_, v_p_3786_, v_mvarId_3787_, v_a_3804_, v_snd_3799_, v___y_3792_, v___y_3793_, v___y_3794_, v___y_3795_);
if (lean_obj_tag(v___x_3805_) == 0)
{
lean_object* v_a_3806_; lean_object* v___x_3808_; uint8_t v_isShared_3809_; uint8_t v_isSharedCheck_3824_; 
v_a_3806_ = lean_ctor_get(v___x_3805_, 0);
v_isSharedCheck_3824_ = !lean_is_exclusive(v___x_3805_);
if (v_isSharedCheck_3824_ == 0)
{
v___x_3808_ = v___x_3805_;
v_isShared_3809_ = v_isSharedCheck_3824_;
goto v_resetjp_3807_;
}
else
{
lean_inc(v_a_3806_);
lean_dec(v___x_3805_);
v___x_3808_ = lean_box(0);
v_isShared_3809_ = v_isSharedCheck_3824_;
goto v_resetjp_3807_;
}
v_resetjp_3807_:
{
if (lean_obj_tag(v_a_3806_) == 0)
{
lean_object* v___x_3810_; lean_object* v___x_3812_; 
lean_dec(v_mvarId_3787_);
lean_dec_ref(v_p_3786_);
v___x_3810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3810_, 0, v_a_3806_);
if (v_isShared_3802_ == 0)
{
lean_ctor_set(v___x_3801_, 0, v___x_3810_);
v___x_3812_ = v___x_3801_;
goto v_reusejp_3811_;
}
else
{
lean_object* v_reuseFailAlloc_3816_; 
v_reuseFailAlloc_3816_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3816_, 0, v___x_3810_);
lean_ctor_set(v_reuseFailAlloc_3816_, 1, v_snd_3799_);
v___x_3812_ = v_reuseFailAlloc_3816_;
goto v_reusejp_3811_;
}
v_reusejp_3811_:
{
lean_object* v___x_3814_; 
if (v_isShared_3809_ == 0)
{
lean_ctor_set(v___x_3808_, 0, v___x_3812_);
v___x_3814_ = v___x_3808_;
goto v_reusejp_3813_;
}
else
{
lean_object* v_reuseFailAlloc_3815_; 
v_reuseFailAlloc_3815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3815_, 0, v___x_3812_);
v___x_3814_ = v_reuseFailAlloc_3815_;
goto v_reusejp_3813_;
}
v_reusejp_3813_:
{
return v___x_3814_;
}
}
}
else
{
lean_object* v_a_3817_; lean_object* v___x_3819_; 
lean_del_object(v___x_3808_);
lean_dec(v_snd_3799_);
v_a_3817_ = lean_ctor_get(v_a_3806_, 0);
lean_inc(v_a_3817_);
lean_dec_ref_known(v_a_3806_, 1);
if (v_isShared_3802_ == 0)
{
lean_ctor_set(v___x_3801_, 1, v_a_3817_);
lean_ctor_set(v___x_3801_, 0, v___x_3803_);
v___x_3819_ = v___x_3801_;
goto v_reusejp_3818_;
}
else
{
lean_object* v_reuseFailAlloc_3823_; 
v_reuseFailAlloc_3823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3823_, 0, v___x_3803_);
lean_ctor_set(v_reuseFailAlloc_3823_, 1, v_a_3817_);
v___x_3819_ = v_reuseFailAlloc_3823_;
goto v_reusejp_3818_;
}
v_reusejp_3818_:
{
size_t v___x_3820_; size_t v___x_3821_; 
v___x_3820_ = ((size_t)1ULL);
v___x_3821_ = lean_usize_add(v_i_3790_, v___x_3820_);
v_i_3790_ = v___x_3821_;
v_b_3791_ = v___x_3819_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3825_; lean_object* v___x_3827_; uint8_t v_isShared_3828_; uint8_t v_isSharedCheck_3832_; 
lean_del_object(v___x_3801_);
lean_dec(v_snd_3799_);
lean_dec(v_mvarId_3787_);
lean_dec_ref(v_p_3786_);
v_a_3825_ = lean_ctor_get(v___x_3805_, 0);
v_isSharedCheck_3832_ = !lean_is_exclusive(v___x_3805_);
if (v_isSharedCheck_3832_ == 0)
{
v___x_3827_ = v___x_3805_;
v_isShared_3828_ = v_isSharedCheck_3832_;
goto v_resetjp_3826_;
}
else
{
lean_inc(v_a_3825_);
lean_dec(v___x_3805_);
v___x_3827_ = lean_box(0);
v_isShared_3828_ = v_isSharedCheck_3832_;
goto v_resetjp_3826_;
}
v_resetjp_3826_:
{
lean_object* v___x_3830_; 
if (v_isShared_3828_ == 0)
{
v___x_3830_ = v___x_3827_;
goto v_reusejp_3829_;
}
else
{
lean_object* v_reuseFailAlloc_3831_; 
v_reuseFailAlloc_3831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3831_, 0, v_a_3825_);
v___x_3830_ = v_reuseFailAlloc_3831_;
goto v_reusejp_3829_;
}
v_reusejp_3829_:
{
return v___x_3830_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_3785_ = stack[0].m_obj;
lean_object* v_p_3786_ = stack[1].m_obj;
lean_object* v_mvarId_3787_ = stack[2].m_obj;
lean_object* v_as_3788_ = stack[3].m_obj;
size_t v_sz_3789_ = stack[4].m_num;
size_t v_i_3790_ = stack[5].m_num;
lean_object* v_b_3791_ = stack[6].m_obj;
lean_object* v___y_3792_ = stack[7].m_obj;
lean_object* v___y_3793_ = stack[8].m_obj;
lean_object* v___y_3794_ = stack[9].m_obj;
lean_object* v___y_3795_ = stack[10].m_obj;
lean_object* v_res_3835_;
v_res_3835_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__3(v_init_3785_, v_p_3786_, v_mvarId_3787_, v_as_3788_, v_sz_3789_, v_i_3790_, v_b_3791_, v___y_3792_, v___y_3793_, v___y_3794_, v___y_3795_);
stack->m_obj
 = v_res_3835_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__3___boxed(lean_object* v_init_3836_, lean_object* v_p_3837_, lean_object* v_mvarId_3838_, lean_object* v_as_3839_, lean_object* v_sz_3840_, lean_object* v_i_3841_, lean_object* v_b_3842_, lean_object* v___y_3843_, lean_object* v___y_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_, lean_object* v___y_3847_){
_start:
{
size_t v_sz_boxed_3848_; size_t v_i_boxed_3849_; lean_object* v_res_3850_; 
v_sz_boxed_3848_ = lean_unbox_usize(v_sz_3840_);
lean_dec(v_sz_3840_);
v_i_boxed_3849_ = lean_unbox_usize(v_i_3841_);
lean_dec(v_i_3841_);
v_res_3850_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__3(v_init_3836_, v_p_3837_, v_mvarId_3838_, v_as_3839_, v_sz_boxed_3848_, v_i_boxed_3849_, v_b_3842_, v___y_3843_, v___y_3844_, v___y_3845_, v___y_3846_);
lean_dec(v___y_3846_);
lean_dec_ref(v___y_3845_);
lean_dec(v___y_3844_);
lean_dec_ref(v___y_3843_);
lean_dec_ref(v_as_3839_);
lean_dec_ref(v_init_3836_);
return v_res_3850_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2___boxed(lean_object* v_init_3851_, lean_object* v_p_3852_, lean_object* v_mvarId_3853_, lean_object* v_n_3854_, lean_object* v_b_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_, lean_object* v___y_3858_, lean_object* v___y_3859_, lean_object* v___y_3860_){
_start:
{
lean_object* v_res_3861_; 
v_res_3861_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2(v_init_3851_, v_p_3852_, v_mvarId_3853_, v_n_3854_, v_b_3855_, v___y_3856_, v___y_3857_, v___y_3858_, v___y_3859_);
lean_dec(v___y_3859_);
lean_dec_ref(v___y_3858_);
lean_dec(v___y_3857_);
lean_dec_ref(v___y_3856_);
lean_dec_ref(v_n_3854_);
lean_dec_ref(v_init_3851_);
return v_res_3861_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3_spec__6(lean_object* v_p_3865_, lean_object* v_mvarId_3866_, lean_object* v_as_3867_, size_t v_sz_3868_, size_t v_i_3869_, lean_object* v_b_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_, lean_object* v___y_3874_){
_start:
{
uint8_t v___x_3876_; 
v___x_3876_ = lean_usize_dec_lt(v_i_3869_, v_sz_3868_);
if (v___x_3876_ == 0)
{
lean_object* v___x_3877_; 
lean_dec(v_mvarId_3866_);
lean_dec_ref(v_p_3865_);
v___x_3877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3877_, 0, v_b_3870_);
return v___x_3877_;
}
else
{
lean_object* v_snd_3878_; lean_object* v___x_3880_; uint8_t v_isShared_3881_; uint8_t v_isSharedCheck_3945_; 
v_snd_3878_ = lean_ctor_get(v_b_3870_, 1);
v_isSharedCheck_3945_ = !lean_is_exclusive(v_b_3870_);
if (v_isSharedCheck_3945_ == 0)
{
lean_object* v_unused_3946_; 
v_unused_3946_ = lean_ctor_get(v_b_3870_, 0);
lean_dec(v_unused_3946_);
v___x_3880_ = v_b_3870_;
v_isShared_3881_ = v_isSharedCheck_3945_;
goto v_resetjp_3879_;
}
else
{
lean_inc(v_snd_3878_);
lean_dec(v_b_3870_);
v___x_3880_ = lean_box(0);
v_isShared_3881_ = v_isSharedCheck_3945_;
goto v_resetjp_3879_;
}
v_resetjp_3879_:
{
lean_object* v___x_3882_; lean_object* v_a_3884_; lean_object* v_a_3891_; 
v___x_3882_ = lean_box(0);
v_a_3891_ = lean_array_uget(v_as_3867_, v_i_3869_);
if (lean_obj_tag(v_a_3891_) == 0)
{
v_a_3884_ = v_snd_3878_;
goto v___jp_3883_;
}
else
{
lean_object* v_val_3892_; lean_object* v___x_3894_; uint8_t v_isShared_3895_; uint8_t v_isSharedCheck_3944_; 
v_val_3892_ = lean_ctor_get(v_a_3891_, 0);
v_isSharedCheck_3944_ = !lean_is_exclusive(v_a_3891_);
if (v_isSharedCheck_3944_ == 0)
{
v___x_3894_ = v_a_3891_;
v_isShared_3895_ = v_isSharedCheck_3944_;
goto v_resetjp_3893_;
}
else
{
lean_inc(v_val_3892_);
lean_dec(v_a_3891_);
v___x_3894_ = lean_box(0);
v_isShared_3895_ = v_isSharedCheck_3944_;
goto v_resetjp_3893_;
}
v_resetjp_3893_:
{
lean_object* v___x_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; 
v___x_3896_ = lean_box(0);
v___x_3897_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3_spec__6___closed__0));
lean_inc_ref(v_p_3865_);
lean_inc(v___y_3874_);
lean_inc_ref(v___y_3873_);
lean_inc(v___y_3872_);
lean_inc_ref(v___y_3871_);
lean_inc(v_val_3892_);
v___x_3898_ = lean_apply_6(v_p_3865_, v_val_3892_, v___y_3871_, v___y_3872_, v___y_3873_, v___y_3874_, lean_box(0));
if (lean_obj_tag(v___x_3898_) == 0)
{
lean_object* v_a_3899_; uint8_t v___x_3900_; 
v_a_3899_ = lean_ctor_get(v___x_3898_, 0);
lean_inc(v_a_3899_);
lean_dec_ref_known(v___x_3898_, 1);
v___x_3900_ = lean_unbox(v_a_3899_);
lean_dec(v_a_3899_);
if (v___x_3900_ == 0)
{
lean_del_object(v___x_3894_);
lean_dec(v_val_3892_);
lean_dec(v_snd_3878_);
v_a_3884_ = v___x_3897_;
goto v___jp_3883_;
}
else
{
lean_object* v___x_3901_; lean_object* v___x_3902_; uint8_t v___x_3903_; lean_object* v___x_3904_; lean_object* v___f_3905_; lean_object* v___x_3906_; 
v___x_3901_ = l_Lean_LocalDecl_fvarId(v_val_3892_);
lean_dec(v_val_3892_);
v___x_3902_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5___closed__1));
v___x_3903_ = 0;
v___x_3904_ = lean_box(v___x_3903_);
lean_inc(v_mvarId_3866_);
v___f_3905_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3___lam__0___boxed), 10, 5);
lean_closure_set(v___f_3905_, 0, v_mvarId_3866_);
lean_closure_set(v___f_3905_, 1, v___x_3901_);
lean_closure_set(v___f_3905_, 2, v___x_3902_);
lean_closure_set(v___f_3905_, 3, v___x_3904_);
lean_closure_set(v___f_3905_, 4, v___x_3882_);
v___x_3906_ = l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1___redArg(v___f_3905_, v___y_3871_, v___y_3872_, v___y_3873_, v___y_3874_);
if (lean_obj_tag(v___x_3906_) == 0)
{
lean_object* v_a_3907_; lean_object* v___x_3909_; uint8_t v_isShared_3910_; uint8_t v_isSharedCheck_3927_; 
v_a_3907_ = lean_ctor_get(v___x_3906_, 0);
v_isSharedCheck_3927_ = !lean_is_exclusive(v___x_3906_);
if (v_isSharedCheck_3927_ == 0)
{
v___x_3909_ = v___x_3906_;
v_isShared_3910_ = v_isSharedCheck_3927_;
goto v_resetjp_3908_;
}
else
{
lean_inc(v_a_3907_);
lean_dec(v___x_3906_);
v___x_3909_ = lean_box(0);
v_isShared_3910_ = v_isSharedCheck_3927_;
goto v_resetjp_3908_;
}
v_resetjp_3908_:
{
if (lean_obj_tag(v_a_3907_) == 0)
{
lean_del_object(v___x_3909_);
lean_del_object(v___x_3894_);
lean_dec(v_snd_3878_);
v_a_3884_ = v___x_3897_;
goto v___jp_3883_;
}
else
{
lean_object* v___x_3912_; 
lean_del_object(v___x_3880_);
lean_dec(v_mvarId_3866_);
lean_dec_ref(v_p_3865_);
lean_inc_ref(v_a_3907_);
if (v_isShared_3895_ == 0)
{
lean_ctor_set(v___x_3894_, 0, v_a_3907_);
v___x_3912_ = v___x_3894_;
goto v_reusejp_3911_;
}
else
{
lean_object* v_reuseFailAlloc_3926_; 
v_reuseFailAlloc_3926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3926_, 0, v_a_3907_);
v___x_3912_ = v_reuseFailAlloc_3926_;
goto v_reusejp_3911_;
}
v_reusejp_3911_:
{
lean_object* v___x_3914_; uint8_t v_isShared_3915_; uint8_t v_isSharedCheck_3924_; 
v_isSharedCheck_3924_ = !lean_is_exclusive(v_a_3907_);
if (v_isSharedCheck_3924_ == 0)
{
lean_object* v_unused_3925_; 
v_unused_3925_ = lean_ctor_get(v_a_3907_, 0);
lean_dec(v_unused_3925_);
v___x_3914_ = v_a_3907_;
v_isShared_3915_ = v_isSharedCheck_3924_;
goto v_resetjp_3913_;
}
else
{
lean_dec(v_a_3907_);
v___x_3914_ = lean_box(0);
v_isShared_3915_ = v_isSharedCheck_3924_;
goto v_resetjp_3913_;
}
v_resetjp_3913_:
{
lean_object* v___x_3916_; lean_object* v___x_3918_; 
v___x_3916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3916_, 0, v___x_3912_);
lean_ctor_set(v___x_3916_, 1, v___x_3896_);
if (v_isShared_3915_ == 0)
{
lean_ctor_set(v___x_3914_, 0, v___x_3916_);
v___x_3918_ = v___x_3914_;
goto v_reusejp_3917_;
}
else
{
lean_object* v_reuseFailAlloc_3923_; 
v_reuseFailAlloc_3923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3923_, 0, v___x_3916_);
v___x_3918_ = v_reuseFailAlloc_3923_;
goto v_reusejp_3917_;
}
v_reusejp_3917_:
{
lean_object* v___x_3919_; lean_object* v___x_3921_; 
v___x_3919_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3919_, 0, v___x_3918_);
lean_ctor_set(v___x_3919_, 1, v_snd_3878_);
if (v_isShared_3910_ == 0)
{
lean_ctor_set(v___x_3909_, 0, v___x_3919_);
v___x_3921_ = v___x_3909_;
goto v_reusejp_3920_;
}
else
{
lean_object* v_reuseFailAlloc_3922_; 
v_reuseFailAlloc_3922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3922_, 0, v___x_3919_);
v___x_3921_ = v_reuseFailAlloc_3922_;
goto v_reusejp_3920_;
}
v_reusejp_3920_:
{
return v___x_3921_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3928_; lean_object* v___x_3930_; uint8_t v_isShared_3931_; uint8_t v_isSharedCheck_3935_; 
lean_del_object(v___x_3894_);
lean_del_object(v___x_3880_);
lean_dec(v_snd_3878_);
lean_dec(v_mvarId_3866_);
lean_dec_ref(v_p_3865_);
v_a_3928_ = lean_ctor_get(v___x_3906_, 0);
v_isSharedCheck_3935_ = !lean_is_exclusive(v___x_3906_);
if (v_isSharedCheck_3935_ == 0)
{
v___x_3930_ = v___x_3906_;
v_isShared_3931_ = v_isSharedCheck_3935_;
goto v_resetjp_3929_;
}
else
{
lean_inc(v_a_3928_);
lean_dec(v___x_3906_);
v___x_3930_ = lean_box(0);
v_isShared_3931_ = v_isSharedCheck_3935_;
goto v_resetjp_3929_;
}
v_resetjp_3929_:
{
lean_object* v___x_3933_; 
if (v_isShared_3931_ == 0)
{
v___x_3933_ = v___x_3930_;
goto v_reusejp_3932_;
}
else
{
lean_object* v_reuseFailAlloc_3934_; 
v_reuseFailAlloc_3934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3934_, 0, v_a_3928_);
v___x_3933_ = v_reuseFailAlloc_3934_;
goto v_reusejp_3932_;
}
v_reusejp_3932_:
{
return v___x_3933_;
}
}
}
}
}
else
{
lean_object* v_a_3936_; lean_object* v___x_3938_; uint8_t v_isShared_3939_; uint8_t v_isSharedCheck_3943_; 
lean_del_object(v___x_3894_);
lean_dec(v_val_3892_);
lean_del_object(v___x_3880_);
lean_dec(v_snd_3878_);
lean_dec(v_mvarId_3866_);
lean_dec_ref(v_p_3865_);
v_a_3936_ = lean_ctor_get(v___x_3898_, 0);
v_isSharedCheck_3943_ = !lean_is_exclusive(v___x_3898_);
if (v_isSharedCheck_3943_ == 0)
{
v___x_3938_ = v___x_3898_;
v_isShared_3939_ = v_isSharedCheck_3943_;
goto v_resetjp_3937_;
}
else
{
lean_inc(v_a_3936_);
lean_dec(v___x_3898_);
v___x_3938_ = lean_box(0);
v_isShared_3939_ = v_isSharedCheck_3943_;
goto v_resetjp_3937_;
}
v_resetjp_3937_:
{
lean_object* v___x_3941_; 
if (v_isShared_3939_ == 0)
{
v___x_3941_ = v___x_3938_;
goto v_reusejp_3940_;
}
else
{
lean_object* v_reuseFailAlloc_3942_; 
v_reuseFailAlloc_3942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3942_, 0, v_a_3936_);
v___x_3941_ = v_reuseFailAlloc_3942_;
goto v_reusejp_3940_;
}
v_reusejp_3940_:
{
return v___x_3941_;
}
}
}
}
}
v___jp_3883_:
{
lean_object* v___x_3886_; 
if (v_isShared_3881_ == 0)
{
lean_ctor_set(v___x_3880_, 1, v_a_3884_);
lean_ctor_set(v___x_3880_, 0, v___x_3882_);
v___x_3886_ = v___x_3880_;
goto v_reusejp_3885_;
}
else
{
lean_object* v_reuseFailAlloc_3890_; 
v_reuseFailAlloc_3890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3890_, 0, v___x_3882_);
lean_ctor_set(v_reuseFailAlloc_3890_, 1, v_a_3884_);
v___x_3886_ = v_reuseFailAlloc_3890_;
goto v_reusejp_3885_;
}
v_reusejp_3885_:
{
size_t v___x_3887_; size_t v___x_3888_; 
v___x_3887_ = ((size_t)1ULL);
v___x_3888_ = lean_usize_add(v_i_3869_, v___x_3887_);
v_i_3869_ = v___x_3888_;
v_b_3870_ = v___x_3886_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_3865_ = stack[0].m_obj;
lean_object* v_mvarId_3866_ = stack[1].m_obj;
lean_object* v_as_3867_ = stack[2].m_obj;
size_t v_sz_3868_ = stack[3].m_num;
size_t v_i_3869_ = stack[4].m_num;
lean_object* v_b_3870_ = stack[5].m_obj;
lean_object* v___y_3871_ = stack[6].m_obj;
lean_object* v___y_3872_ = stack[7].m_obj;
lean_object* v___y_3873_ = stack[8].m_obj;
lean_object* v___y_3874_ = stack[9].m_obj;
lean_object* v_res_3947_;
v_res_3947_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3_spec__6(v_p_3865_, v_mvarId_3866_, v_as_3867_, v_sz_3868_, v_i_3869_, v_b_3870_, v___y_3871_, v___y_3872_, v___y_3873_, v___y_3874_);
stack->m_obj
 = v_res_3947_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3_spec__6___boxed(lean_object* v_p_3948_, lean_object* v_mvarId_3949_, lean_object* v_as_3950_, lean_object* v_sz_3951_, lean_object* v_i_3952_, lean_object* v_b_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_, lean_object* v___y_3958_){
_start:
{
size_t v_sz_boxed_3959_; size_t v_i_boxed_3960_; lean_object* v_res_3961_; 
v_sz_boxed_3959_ = lean_unbox_usize(v_sz_3951_);
lean_dec(v_sz_3951_);
v_i_boxed_3960_ = lean_unbox_usize(v_i_3952_);
lean_dec(v_i_3952_);
v_res_3961_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3_spec__6(v_p_3948_, v_mvarId_3949_, v_as_3950_, v_sz_boxed_3959_, v_i_boxed_3960_, v_b_3953_, v___y_3954_, v___y_3955_, v___y_3956_, v___y_3957_);
lean_dec(v___y_3957_);
lean_dec_ref(v___y_3956_);
lean_dec(v___y_3955_);
lean_dec_ref(v___y_3954_);
lean_dec_ref(v_as_3950_);
return v_res_3961_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3(lean_object* v_p_3962_, lean_object* v_mvarId_3963_, lean_object* v_as_3964_, size_t v_sz_3965_, size_t v_i_3966_, lean_object* v_b_3967_, lean_object* v___y_3968_, lean_object* v___y_3969_, lean_object* v___y_3970_, lean_object* v___y_3971_){
_start:
{
uint8_t v___x_3973_; 
v___x_3973_ = lean_usize_dec_lt(v_i_3966_, v_sz_3965_);
if (v___x_3973_ == 0)
{
lean_object* v___x_3974_; 
lean_dec(v_mvarId_3963_);
lean_dec_ref(v_p_3962_);
v___x_3974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3974_, 0, v_b_3967_);
return v___x_3974_;
}
else
{
lean_object* v_snd_3975_; lean_object* v___x_3977_; uint8_t v_isShared_3978_; uint8_t v_isSharedCheck_4042_; 
v_snd_3975_ = lean_ctor_get(v_b_3967_, 1);
v_isSharedCheck_4042_ = !lean_is_exclusive(v_b_3967_);
if (v_isSharedCheck_4042_ == 0)
{
lean_object* v_unused_4043_; 
v_unused_4043_ = lean_ctor_get(v_b_3967_, 0);
lean_dec(v_unused_4043_);
v___x_3977_ = v_b_3967_;
v_isShared_3978_ = v_isSharedCheck_4042_;
goto v_resetjp_3976_;
}
else
{
lean_inc(v_snd_3975_);
lean_dec(v_b_3967_);
v___x_3977_ = lean_box(0);
v_isShared_3978_ = v_isSharedCheck_4042_;
goto v_resetjp_3976_;
}
v_resetjp_3976_:
{
lean_object* v___x_3979_; lean_object* v_a_3981_; lean_object* v_a_3988_; 
v___x_3979_ = lean_box(0);
v_a_3988_ = lean_array_uget(v_as_3964_, v_i_3966_);
if (lean_obj_tag(v_a_3988_) == 0)
{
v_a_3981_ = v_snd_3975_;
goto v___jp_3980_;
}
else
{
lean_object* v_val_3989_; lean_object* v___x_3991_; uint8_t v_isShared_3992_; uint8_t v_isSharedCheck_4041_; 
v_val_3989_ = lean_ctor_get(v_a_3988_, 0);
v_isSharedCheck_4041_ = !lean_is_exclusive(v_a_3988_);
if (v_isSharedCheck_4041_ == 0)
{
v___x_3991_ = v_a_3988_;
v_isShared_3992_ = v_isSharedCheck_4041_;
goto v_resetjp_3990_;
}
else
{
lean_inc(v_val_3989_);
lean_dec(v_a_3988_);
v___x_3991_ = lean_box(0);
v_isShared_3992_ = v_isSharedCheck_4041_;
goto v_resetjp_3990_;
}
v_resetjp_3990_:
{
lean_object* v___x_3993_; lean_object* v___x_3994_; lean_object* v___x_3995_; 
v___x_3993_ = lean_box(0);
v___x_3994_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3_spec__6___closed__0));
lean_inc_ref(v_p_3962_);
lean_inc(v___y_3971_);
lean_inc_ref(v___y_3970_);
lean_inc(v___y_3969_);
lean_inc_ref(v___y_3968_);
lean_inc(v_val_3989_);
v___x_3995_ = lean_apply_6(v_p_3962_, v_val_3989_, v___y_3968_, v___y_3969_, v___y_3970_, v___y_3971_, lean_box(0));
if (lean_obj_tag(v___x_3995_) == 0)
{
lean_object* v_a_3996_; uint8_t v___x_3997_; 
v_a_3996_ = lean_ctor_get(v___x_3995_, 0);
lean_inc(v_a_3996_);
lean_dec_ref_known(v___x_3995_, 1);
v___x_3997_ = lean_unbox(v_a_3996_);
lean_dec(v_a_3996_);
if (v___x_3997_ == 0)
{
lean_del_object(v___x_3991_);
lean_dec(v_val_3989_);
lean_dec(v_snd_3975_);
v_a_3981_ = v___x_3994_;
goto v___jp_3980_;
}
else
{
lean_object* v___x_3998_; lean_object* v___x_3999_; uint8_t v___x_4000_; lean_object* v___x_4001_; lean_object* v___f_4002_; lean_object* v___x_4003_; 
v___x_3998_ = l_Lean_LocalDecl_fvarId(v_val_3989_);
lean_dec(v_val_3989_);
v___x_3999_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5___closed__1));
v___x_4000_ = 0;
v___x_4001_ = lean_box(v___x_4000_);
lean_inc(v_mvarId_3963_);
v___f_4002_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3___lam__0___boxed), 10, 5);
lean_closure_set(v___f_4002_, 0, v_mvarId_3963_);
lean_closure_set(v___f_4002_, 1, v___x_3998_);
lean_closure_set(v___f_4002_, 2, v___x_3999_);
lean_closure_set(v___f_4002_, 3, v___x_4001_);
lean_closure_set(v___f_4002_, 4, v___x_3979_);
v___x_4003_ = l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1___redArg(v___f_4002_, v___y_3968_, v___y_3969_, v___y_3970_, v___y_3971_);
if (lean_obj_tag(v___x_4003_) == 0)
{
lean_object* v_a_4004_; lean_object* v___x_4006_; uint8_t v_isShared_4007_; uint8_t v_isSharedCheck_4024_; 
v_a_4004_ = lean_ctor_get(v___x_4003_, 0);
v_isSharedCheck_4024_ = !lean_is_exclusive(v___x_4003_);
if (v_isSharedCheck_4024_ == 0)
{
v___x_4006_ = v___x_4003_;
v_isShared_4007_ = v_isSharedCheck_4024_;
goto v_resetjp_4005_;
}
else
{
lean_inc(v_a_4004_);
lean_dec(v___x_4003_);
v___x_4006_ = lean_box(0);
v_isShared_4007_ = v_isSharedCheck_4024_;
goto v_resetjp_4005_;
}
v_resetjp_4005_:
{
if (lean_obj_tag(v_a_4004_) == 0)
{
lean_del_object(v___x_4006_);
lean_del_object(v___x_3991_);
lean_dec(v_snd_3975_);
v_a_3981_ = v___x_3994_;
goto v___jp_3980_;
}
else
{
lean_object* v___x_4009_; 
lean_del_object(v___x_3977_);
lean_dec(v_mvarId_3963_);
lean_dec_ref(v_p_3962_);
lean_inc_ref(v_a_4004_);
if (v_isShared_3992_ == 0)
{
lean_ctor_set(v___x_3991_, 0, v_a_4004_);
v___x_4009_ = v___x_3991_;
goto v_reusejp_4008_;
}
else
{
lean_object* v_reuseFailAlloc_4023_; 
v_reuseFailAlloc_4023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4023_, 0, v_a_4004_);
v___x_4009_ = v_reuseFailAlloc_4023_;
goto v_reusejp_4008_;
}
v_reusejp_4008_:
{
lean_object* v___x_4011_; uint8_t v_isShared_4012_; uint8_t v_isSharedCheck_4021_; 
v_isSharedCheck_4021_ = !lean_is_exclusive(v_a_4004_);
if (v_isSharedCheck_4021_ == 0)
{
lean_object* v_unused_4022_; 
v_unused_4022_ = lean_ctor_get(v_a_4004_, 0);
lean_dec(v_unused_4022_);
v___x_4011_ = v_a_4004_;
v_isShared_4012_ = v_isSharedCheck_4021_;
goto v_resetjp_4010_;
}
else
{
lean_dec(v_a_4004_);
v___x_4011_ = lean_box(0);
v_isShared_4012_ = v_isSharedCheck_4021_;
goto v_resetjp_4010_;
}
v_resetjp_4010_:
{
lean_object* v___x_4013_; lean_object* v___x_4015_; 
v___x_4013_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4013_, 0, v___x_4009_);
lean_ctor_set(v___x_4013_, 1, v___x_3993_);
if (v_isShared_4012_ == 0)
{
lean_ctor_set(v___x_4011_, 0, v___x_4013_);
v___x_4015_ = v___x_4011_;
goto v_reusejp_4014_;
}
else
{
lean_object* v_reuseFailAlloc_4020_; 
v_reuseFailAlloc_4020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4020_, 0, v___x_4013_);
v___x_4015_ = v_reuseFailAlloc_4020_;
goto v_reusejp_4014_;
}
v_reusejp_4014_:
{
lean_object* v___x_4016_; lean_object* v___x_4018_; 
v___x_4016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4016_, 0, v___x_4015_);
lean_ctor_set(v___x_4016_, 1, v_snd_3975_);
if (v_isShared_4007_ == 0)
{
lean_ctor_set(v___x_4006_, 0, v___x_4016_);
v___x_4018_ = v___x_4006_;
goto v_reusejp_4017_;
}
else
{
lean_object* v_reuseFailAlloc_4019_; 
v_reuseFailAlloc_4019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4019_, 0, v___x_4016_);
v___x_4018_ = v_reuseFailAlloc_4019_;
goto v_reusejp_4017_;
}
v_reusejp_4017_:
{
return v___x_4018_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4025_; lean_object* v___x_4027_; uint8_t v_isShared_4028_; uint8_t v_isSharedCheck_4032_; 
lean_del_object(v___x_3991_);
lean_del_object(v___x_3977_);
lean_dec(v_snd_3975_);
lean_dec(v_mvarId_3963_);
lean_dec_ref(v_p_3962_);
v_a_4025_ = lean_ctor_get(v___x_4003_, 0);
v_isSharedCheck_4032_ = !lean_is_exclusive(v___x_4003_);
if (v_isSharedCheck_4032_ == 0)
{
v___x_4027_ = v___x_4003_;
v_isShared_4028_ = v_isSharedCheck_4032_;
goto v_resetjp_4026_;
}
else
{
lean_inc(v_a_4025_);
lean_dec(v___x_4003_);
v___x_4027_ = lean_box(0);
v_isShared_4028_ = v_isSharedCheck_4032_;
goto v_resetjp_4026_;
}
v_resetjp_4026_:
{
lean_object* v___x_4030_; 
if (v_isShared_4028_ == 0)
{
v___x_4030_ = v___x_4027_;
goto v_reusejp_4029_;
}
else
{
lean_object* v_reuseFailAlloc_4031_; 
v_reuseFailAlloc_4031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4031_, 0, v_a_4025_);
v___x_4030_ = v_reuseFailAlloc_4031_;
goto v_reusejp_4029_;
}
v_reusejp_4029_:
{
return v___x_4030_;
}
}
}
}
}
else
{
lean_object* v_a_4033_; lean_object* v___x_4035_; uint8_t v_isShared_4036_; uint8_t v_isSharedCheck_4040_; 
lean_del_object(v___x_3991_);
lean_dec(v_val_3989_);
lean_del_object(v___x_3977_);
lean_dec(v_snd_3975_);
lean_dec(v_mvarId_3963_);
lean_dec_ref(v_p_3962_);
v_a_4033_ = lean_ctor_get(v___x_3995_, 0);
v_isSharedCheck_4040_ = !lean_is_exclusive(v___x_3995_);
if (v_isSharedCheck_4040_ == 0)
{
v___x_4035_ = v___x_3995_;
v_isShared_4036_ = v_isSharedCheck_4040_;
goto v_resetjp_4034_;
}
else
{
lean_inc(v_a_4033_);
lean_dec(v___x_3995_);
v___x_4035_ = lean_box(0);
v_isShared_4036_ = v_isSharedCheck_4040_;
goto v_resetjp_4034_;
}
v_resetjp_4034_:
{
lean_object* v___x_4038_; 
if (v_isShared_4036_ == 0)
{
v___x_4038_ = v___x_4035_;
goto v_reusejp_4037_;
}
else
{
lean_object* v_reuseFailAlloc_4039_; 
v_reuseFailAlloc_4039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4039_, 0, v_a_4033_);
v___x_4038_ = v_reuseFailAlloc_4039_;
goto v_reusejp_4037_;
}
v_reusejp_4037_:
{
return v___x_4038_;
}
}
}
}
}
v___jp_3980_:
{
lean_object* v___x_3983_; 
if (v_isShared_3978_ == 0)
{
lean_ctor_set(v___x_3977_, 1, v_a_3981_);
lean_ctor_set(v___x_3977_, 0, v___x_3979_);
v___x_3983_ = v___x_3977_;
goto v_reusejp_3982_;
}
else
{
lean_object* v_reuseFailAlloc_3987_; 
v_reuseFailAlloc_3987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3987_, 0, v___x_3979_);
lean_ctor_set(v_reuseFailAlloc_3987_, 1, v_a_3981_);
v___x_3983_ = v_reuseFailAlloc_3987_;
goto v_reusejp_3982_;
}
v_reusejp_3982_:
{
size_t v___x_3984_; size_t v___x_3985_; lean_object* v___x_3986_; 
v___x_3984_ = ((size_t)1ULL);
v___x_3985_ = lean_usize_add(v_i_3966_, v___x_3984_);
v___x_3986_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3_spec__6(v_p_3962_, v_mvarId_3963_, v_as_3964_, v_sz_3965_, v___x_3985_, v___x_3983_, v___y_3968_, v___y_3969_, v___y_3970_, v___y_3971_);
return v___x_3986_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_3962_ = stack[0].m_obj;
lean_object* v_mvarId_3963_ = stack[1].m_obj;
lean_object* v_as_3964_ = stack[2].m_obj;
size_t v_sz_3965_ = stack[3].m_num;
size_t v_i_3966_ = stack[4].m_num;
lean_object* v_b_3967_ = stack[5].m_obj;
lean_object* v___y_3968_ = stack[6].m_obj;
lean_object* v___y_3969_ = stack[7].m_obj;
lean_object* v___y_3970_ = stack[8].m_obj;
lean_object* v___y_3971_ = stack[9].m_obj;
lean_object* v_res_4044_;
v_res_4044_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3(v_p_3962_, v_mvarId_3963_, v_as_3964_, v_sz_3965_, v_i_3966_, v_b_3967_, v___y_3968_, v___y_3969_, v___y_3970_, v___y_3971_);
stack->m_obj
 = v_res_4044_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3___boxed(lean_object* v_p_4045_, lean_object* v_mvarId_4046_, lean_object* v_as_4047_, lean_object* v_sz_4048_, lean_object* v_i_4049_, lean_object* v_b_4050_, lean_object* v___y_4051_, lean_object* v___y_4052_, lean_object* v___y_4053_, lean_object* v___y_4054_, lean_object* v___y_4055_){
_start:
{
size_t v_sz_boxed_4056_; size_t v_i_boxed_4057_; lean_object* v_res_4058_; 
v_sz_boxed_4056_ = lean_unbox_usize(v_sz_4048_);
lean_dec(v_sz_4048_);
v_i_boxed_4057_ = lean_unbox_usize(v_i_4049_);
lean_dec(v_i_4049_);
v_res_4058_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3(v_p_4045_, v_mvarId_4046_, v_as_4047_, v_sz_boxed_4056_, v_i_boxed_4057_, v_b_4050_, v___y_4051_, v___y_4052_, v___y_4053_, v___y_4054_);
lean_dec(v___y_4054_);
lean_dec_ref(v___y_4053_);
lean_dec(v___y_4052_);
lean_dec_ref(v___y_4051_);
lean_dec_ref(v_as_4047_);
return v_res_4058_;
}
}
lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2(lean_object* v_p_4059_, lean_object* v_mvarId_4060_, lean_object* v_t_4061_, lean_object* v_init_4062_, lean_object* v___y_4063_, lean_object* v___y_4064_, lean_object* v___y_4065_, lean_object* v___y_4066_){
_start:
{
lean_object* v_root_4068_; lean_object* v_tail_4069_; lean_object* v___x_4070_; 
v_root_4068_ = lean_ctor_get(v_t_4061_, 0);
v_tail_4069_ = lean_ctor_get(v_t_4061_, 1);
lean_inc(v_mvarId_4060_);
lean_inc_ref(v_p_4059_);
lean_inc_ref(v_init_4062_);
v___x_4070_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2(v_init_4062_, v_p_4059_, v_mvarId_4060_, v_root_4068_, v_init_4062_, v___y_4063_, v___y_4064_, v___y_4065_, v___y_4066_);
lean_dec_ref(v_init_4062_);
if (lean_obj_tag(v___x_4070_) == 0)
{
lean_object* v_a_4071_; lean_object* v___x_4073_; uint8_t v_isShared_4074_; uint8_t v_isSharedCheck_4107_; 
v_a_4071_ = lean_ctor_get(v___x_4070_, 0);
v_isSharedCheck_4107_ = !lean_is_exclusive(v___x_4070_);
if (v_isSharedCheck_4107_ == 0)
{
v___x_4073_ = v___x_4070_;
v_isShared_4074_ = v_isSharedCheck_4107_;
goto v_resetjp_4072_;
}
else
{
lean_inc(v_a_4071_);
lean_dec(v___x_4070_);
v___x_4073_ = lean_box(0);
v_isShared_4074_ = v_isSharedCheck_4107_;
goto v_resetjp_4072_;
}
v_resetjp_4072_:
{
if (lean_obj_tag(v_a_4071_) == 0)
{
lean_object* v_a_4075_; lean_object* v___x_4077_; 
lean_dec(v_mvarId_4060_);
lean_dec_ref(v_p_4059_);
v_a_4075_ = lean_ctor_get(v_a_4071_, 0);
lean_inc(v_a_4075_);
lean_dec_ref_known(v_a_4071_, 1);
if (v_isShared_4074_ == 0)
{
lean_ctor_set(v___x_4073_, 0, v_a_4075_);
v___x_4077_ = v___x_4073_;
goto v_reusejp_4076_;
}
else
{
lean_object* v_reuseFailAlloc_4078_; 
v_reuseFailAlloc_4078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4078_, 0, v_a_4075_);
v___x_4077_ = v_reuseFailAlloc_4078_;
goto v_reusejp_4076_;
}
v_reusejp_4076_:
{
return v___x_4077_;
}
}
else
{
lean_object* v_a_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; size_t v_sz_4082_; size_t v___x_4083_; lean_object* v___x_4084_; 
lean_del_object(v___x_4073_);
v_a_4079_ = lean_ctor_get(v_a_4071_, 0);
lean_inc(v_a_4079_);
lean_dec_ref_known(v_a_4071_, 1);
v___x_4080_ = lean_box(0);
v___x_4081_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4081_, 0, v___x_4080_);
lean_ctor_set(v___x_4081_, 1, v_a_4079_);
v_sz_4082_ = lean_array_size(v_tail_4069_);
v___x_4083_ = ((size_t)0ULL);
v___x_4084_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3(v_p_4059_, v_mvarId_4060_, v_tail_4069_, v_sz_4082_, v___x_4083_, v___x_4081_, v___y_4063_, v___y_4064_, v___y_4065_, v___y_4066_);
if (lean_obj_tag(v___x_4084_) == 0)
{
lean_object* v_a_4085_; lean_object* v___x_4087_; uint8_t v_isShared_4088_; uint8_t v_isSharedCheck_4098_; 
v_a_4085_ = lean_ctor_get(v___x_4084_, 0);
v_isSharedCheck_4098_ = !lean_is_exclusive(v___x_4084_);
if (v_isSharedCheck_4098_ == 0)
{
v___x_4087_ = v___x_4084_;
v_isShared_4088_ = v_isSharedCheck_4098_;
goto v_resetjp_4086_;
}
else
{
lean_inc(v_a_4085_);
lean_dec(v___x_4084_);
v___x_4087_ = lean_box(0);
v_isShared_4088_ = v_isSharedCheck_4098_;
goto v_resetjp_4086_;
}
v_resetjp_4086_:
{
lean_object* v_fst_4089_; 
v_fst_4089_ = lean_ctor_get(v_a_4085_, 0);
if (lean_obj_tag(v_fst_4089_) == 0)
{
lean_object* v_snd_4090_; lean_object* v___x_4092_; 
v_snd_4090_ = lean_ctor_get(v_a_4085_, 1);
lean_inc(v_snd_4090_);
lean_dec(v_a_4085_);
if (v_isShared_4088_ == 0)
{
lean_ctor_set(v___x_4087_, 0, v_snd_4090_);
v___x_4092_ = v___x_4087_;
goto v_reusejp_4091_;
}
else
{
lean_object* v_reuseFailAlloc_4093_; 
v_reuseFailAlloc_4093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4093_, 0, v_snd_4090_);
v___x_4092_ = v_reuseFailAlloc_4093_;
goto v_reusejp_4091_;
}
v_reusejp_4091_:
{
return v___x_4092_;
}
}
else
{
lean_object* v_val_4094_; lean_object* v___x_4096_; 
lean_inc_ref(v_fst_4089_);
lean_dec(v_a_4085_);
v_val_4094_ = lean_ctor_get(v_fst_4089_, 0);
lean_inc(v_val_4094_);
lean_dec_ref_known(v_fst_4089_, 1);
if (v_isShared_4088_ == 0)
{
lean_ctor_set(v___x_4087_, 0, v_val_4094_);
v___x_4096_ = v___x_4087_;
goto v_reusejp_4095_;
}
else
{
lean_object* v_reuseFailAlloc_4097_; 
v_reuseFailAlloc_4097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4097_, 0, v_val_4094_);
v___x_4096_ = v_reuseFailAlloc_4097_;
goto v_reusejp_4095_;
}
v_reusejp_4095_:
{
return v___x_4096_;
}
}
}
}
else
{
lean_object* v_a_4099_; lean_object* v___x_4101_; uint8_t v_isShared_4102_; uint8_t v_isSharedCheck_4106_; 
v_a_4099_ = lean_ctor_get(v___x_4084_, 0);
v_isSharedCheck_4106_ = !lean_is_exclusive(v___x_4084_);
if (v_isSharedCheck_4106_ == 0)
{
v___x_4101_ = v___x_4084_;
v_isShared_4102_ = v_isSharedCheck_4106_;
goto v_resetjp_4100_;
}
else
{
lean_inc(v_a_4099_);
lean_dec(v___x_4084_);
v___x_4101_ = lean_box(0);
v_isShared_4102_ = v_isSharedCheck_4106_;
goto v_resetjp_4100_;
}
v_resetjp_4100_:
{
lean_object* v___x_4104_; 
if (v_isShared_4102_ == 0)
{
v___x_4104_ = v___x_4101_;
goto v_reusejp_4103_;
}
else
{
lean_object* v_reuseFailAlloc_4105_; 
v_reuseFailAlloc_4105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4105_, 0, v_a_4099_);
v___x_4104_ = v_reuseFailAlloc_4105_;
goto v_reusejp_4103_;
}
v_reusejp_4103_:
{
return v___x_4104_;
}
}
}
}
}
}
else
{
lean_object* v_a_4108_; lean_object* v___x_4110_; uint8_t v_isShared_4111_; uint8_t v_isSharedCheck_4115_; 
lean_dec(v_mvarId_4060_);
lean_dec_ref(v_p_4059_);
v_a_4108_ = lean_ctor_get(v___x_4070_, 0);
v_isSharedCheck_4115_ = !lean_is_exclusive(v___x_4070_);
if (v_isSharedCheck_4115_ == 0)
{
v___x_4110_ = v___x_4070_;
v_isShared_4111_ = v_isSharedCheck_4115_;
goto v_resetjp_4109_;
}
else
{
lean_inc(v_a_4108_);
lean_dec(v___x_4070_);
v___x_4110_ = lean_box(0);
v_isShared_4111_ = v_isSharedCheck_4115_;
goto v_resetjp_4109_;
}
v_resetjp_4109_:
{
lean_object* v___x_4113_; 
if (v_isShared_4111_ == 0)
{
v___x_4113_ = v___x_4110_;
goto v_reusejp_4112_;
}
else
{
lean_object* v_reuseFailAlloc_4114_; 
v_reuseFailAlloc_4114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4114_, 0, v_a_4108_);
v___x_4113_ = v_reuseFailAlloc_4114_;
goto v_reusejp_4112_;
}
v_reusejp_4112_:
{
return v___x_4113_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_4059_ = stack[0].m_obj;
lean_object* v_mvarId_4060_ = stack[1].m_obj;
lean_object* v_t_4061_ = stack[2].m_obj;
lean_object* v_init_4062_ = stack[3].m_obj;
lean_object* v___y_4063_ = stack[4].m_obj;
lean_object* v___y_4064_ = stack[5].m_obj;
lean_object* v___y_4065_ = stack[6].m_obj;
lean_object* v___y_4066_ = stack[7].m_obj;
lean_object* v_res_4116_;
v_res_4116_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2(v_p_4059_, v_mvarId_4060_, v_t_4061_, v_init_4062_, v___y_4063_, v___y_4064_, v___y_4065_, v___y_4066_);
stack->m_obj
 = v_res_4116_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2___boxed(lean_object* v_p_4117_, lean_object* v_mvarId_4118_, lean_object* v_t_4119_, lean_object* v_init_4120_, lean_object* v___y_4121_, lean_object* v___y_4122_, lean_object* v___y_4123_, lean_object* v___y_4124_, lean_object* v___y_4125_){
_start:
{
lean_object* v_res_4126_; 
v_res_4126_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2(v_p_4117_, v_mvarId_4118_, v_t_4119_, v_init_4120_, v___y_4121_, v___y_4122_, v___y_4123_, v___y_4124_);
lean_dec(v___y_4124_);
lean_dec_ref(v___y_4123_);
lean_dec(v___y_4122_);
lean_dec_ref(v___y_4121_);
lean_dec_ref(v_t_4119_);
return v_res_4126_;
}
}
lean_object* l_Lean_MVarId_casesRec___lam__0(lean_object* v_p_4130_, lean_object* v_mvarId_4131_, lean_object* v___y_4132_, lean_object* v___y_4133_, lean_object* v___y_4134_, lean_object* v___y_4135_){
_start:
{
lean_object* v_lctx_4137_; lean_object* v_decls_4138_; lean_object* v___x_4139_; lean_object* v___x_4140_; lean_object* v___x_4141_; 
v_lctx_4137_ = lean_ctor_get(v___y_4132_, 2);
v_decls_4138_ = lean_ctor_get(v_lctx_4137_, 1);
v___x_4139_ = lean_box(0);
v___x_4140_ = ((lean_object*)(l_Lean_MVarId_casesRec___lam__0___closed__0));
v___x_4141_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2(v_p_4130_, v_mvarId_4131_, v_decls_4138_, v___x_4140_, v___y_4132_, v___y_4133_, v___y_4134_, v___y_4135_);
if (lean_obj_tag(v___x_4141_) == 0)
{
lean_object* v_a_4142_; lean_object* v___x_4144_; uint8_t v_isShared_4145_; uint8_t v_isSharedCheck_4154_; 
v_a_4142_ = lean_ctor_get(v___x_4141_, 0);
v_isSharedCheck_4154_ = !lean_is_exclusive(v___x_4141_);
if (v_isSharedCheck_4154_ == 0)
{
v___x_4144_ = v___x_4141_;
v_isShared_4145_ = v_isSharedCheck_4154_;
goto v_resetjp_4143_;
}
else
{
lean_inc(v_a_4142_);
lean_dec(v___x_4141_);
v___x_4144_ = lean_box(0);
v_isShared_4145_ = v_isSharedCheck_4154_;
goto v_resetjp_4143_;
}
v_resetjp_4143_:
{
lean_object* v_fst_4146_; 
v_fst_4146_ = lean_ctor_get(v_a_4142_, 0);
lean_inc(v_fst_4146_);
lean_dec(v_a_4142_);
if (lean_obj_tag(v_fst_4146_) == 0)
{
lean_object* v___x_4148_; 
if (v_isShared_4145_ == 0)
{
lean_ctor_set(v___x_4144_, 0, v___x_4139_);
v___x_4148_ = v___x_4144_;
goto v_reusejp_4147_;
}
else
{
lean_object* v_reuseFailAlloc_4149_; 
v_reuseFailAlloc_4149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4149_, 0, v___x_4139_);
v___x_4148_ = v_reuseFailAlloc_4149_;
goto v_reusejp_4147_;
}
v_reusejp_4147_:
{
return v___x_4148_;
}
}
else
{
lean_object* v_val_4150_; lean_object* v___x_4152_; 
v_val_4150_ = lean_ctor_get(v_fst_4146_, 0);
lean_inc(v_val_4150_);
lean_dec_ref_known(v_fst_4146_, 1);
if (v_isShared_4145_ == 0)
{
lean_ctor_set(v___x_4144_, 0, v_val_4150_);
v___x_4152_ = v___x_4144_;
goto v_reusejp_4151_;
}
else
{
lean_object* v_reuseFailAlloc_4153_; 
v_reuseFailAlloc_4153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4153_, 0, v_val_4150_);
v___x_4152_ = v_reuseFailAlloc_4153_;
goto v_reusejp_4151_;
}
v_reusejp_4151_:
{
return v___x_4152_;
}
}
}
}
else
{
lean_object* v_a_4155_; lean_object* v___x_4157_; uint8_t v_isShared_4158_; uint8_t v_isSharedCheck_4162_; 
v_a_4155_ = lean_ctor_get(v___x_4141_, 0);
v_isSharedCheck_4162_ = !lean_is_exclusive(v___x_4141_);
if (v_isSharedCheck_4162_ == 0)
{
v___x_4157_ = v___x_4141_;
v_isShared_4158_ = v_isSharedCheck_4162_;
goto v_resetjp_4156_;
}
else
{
lean_inc(v_a_4155_);
lean_dec(v___x_4141_);
v___x_4157_ = lean_box(0);
v_isShared_4158_ = v_isSharedCheck_4162_;
goto v_resetjp_4156_;
}
v_resetjp_4156_:
{
lean_object* v___x_4160_; 
if (v_isShared_4158_ == 0)
{
v___x_4160_ = v___x_4157_;
goto v_reusejp_4159_;
}
else
{
lean_object* v_reuseFailAlloc_4161_; 
v_reuseFailAlloc_4161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4161_, 0, v_a_4155_);
v___x_4160_ = v_reuseFailAlloc_4161_;
goto v_reusejp_4159_;
}
v_reusejp_4159_:
{
return v___x_4160_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_casesRec___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_4130_ = stack[0].m_obj;
lean_object* v_mvarId_4131_ = stack[1].m_obj;
lean_object* v___y_4132_ = stack[2].m_obj;
lean_object* v___y_4133_ = stack[3].m_obj;
lean_object* v___y_4134_ = stack[4].m_obj;
lean_object* v___y_4135_ = stack[5].m_obj;
lean_object* v_res_4163_;
v_res_4163_ = l_Lean_MVarId_casesRec___lam__0(v_p_4130_, v_mvarId_4131_, v___y_4132_, v___y_4133_, v___y_4134_, v___y_4135_);
stack->m_obj
 = v_res_4163_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesRec___lam__0___boxed(lean_object* v_p_4164_, lean_object* v_mvarId_4165_, lean_object* v___y_4166_, lean_object* v___y_4167_, lean_object* v___y_4168_, lean_object* v___y_4169_, lean_object* v___y_4170_){
_start:
{
lean_object* v_res_4171_; 
v_res_4171_ = l_Lean_MVarId_casesRec___lam__0(v_p_4164_, v_mvarId_4165_, v___y_4166_, v___y_4167_, v___y_4168_, v___y_4169_);
lean_dec(v___y_4169_);
lean_dec_ref(v___y_4168_);
lean_dec(v___y_4167_);
lean_dec_ref(v___y_4166_);
return v_res_4171_;
}
}
lean_object* l_Lean_MVarId_casesRec___lam__1(lean_object* v_p_4172_, lean_object* v_mvarId_4173_, lean_object* v___y_4174_, lean_object* v___y_4175_, lean_object* v___y_4176_, lean_object* v___y_4177_){
_start:
{
lean_object* v___f_4179_; lean_object* v___x_4180_; 
lean_inc(v_mvarId_4173_);
v___f_4179_ = lean_alloc_closure((void*)(l_Lean_MVarId_casesRec___lam__0___boxed), 7, 2);
lean_closure_set(v___f_4179_, 0, v_p_4172_);
lean_closure_set(v___f_4179_, 1, v_mvarId_4173_);
v___x_4180_ = l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2___redArg(v_mvarId_4173_, v___f_4179_, v___y_4174_, v___y_4175_, v___y_4176_, v___y_4177_);
return v___x_4180_;
}
}
LEAN_EXPORT void l_Lean_MVarId_casesRec___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_4172_ = stack[0].m_obj;
lean_object* v_mvarId_4173_ = stack[1].m_obj;
lean_object* v___y_4174_ = stack[2].m_obj;
lean_object* v___y_4175_ = stack[3].m_obj;
lean_object* v___y_4176_ = stack[4].m_obj;
lean_object* v___y_4177_ = stack[5].m_obj;
lean_object* v_res_4181_;
v_res_4181_ = l_Lean_MVarId_casesRec___lam__1(v_p_4172_, v_mvarId_4173_, v___y_4174_, v___y_4175_, v___y_4176_, v___y_4177_);
stack->m_obj
 = v_res_4181_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesRec___lam__1___boxed(lean_object* v_p_4182_, lean_object* v_mvarId_4183_, lean_object* v___y_4184_, lean_object* v___y_4185_, lean_object* v___y_4186_, lean_object* v___y_4187_, lean_object* v___y_4188_){
_start:
{
lean_object* v_res_4189_; 
v_res_4189_ = l_Lean_MVarId_casesRec___lam__1(v_p_4182_, v_mvarId_4183_, v___y_4184_, v___y_4185_, v___y_4186_, v___y_4187_);
lean_dec(v___y_4187_);
lean_dec_ref(v___y_4186_);
lean_dec(v___y_4185_);
lean_dec_ref(v___y_4184_);
return v_res_4189_;
}
}
lean_object* l_Lean_MVarId_casesRec(lean_object* v_mvarId_4190_, lean_object* v_p_4191_, lean_object* v_a_4192_, lean_object* v_a_4193_, lean_object* v_a_4194_, lean_object* v_a_4195_){
_start:
{
lean_object* v___f_4197_; lean_object* v___x_4198_; 
v___f_4197_ = lean_alloc_closure((void*)(l_Lean_MVarId_casesRec___lam__1___boxed), 7, 1);
lean_closure_set(v___f_4197_, 0, v_p_4191_);
v___x_4198_ = l_Lean_Meta_saturate(v_mvarId_4190_, v___f_4197_, v_a_4192_, v_a_4193_, v_a_4194_, v_a_4195_);
return v___x_4198_;
}
}
LEAN_EXPORT void l_Lean_MVarId_casesRec_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_4190_ = stack[0].m_obj;
lean_object* v_p_4191_ = stack[1].m_obj;
lean_object* v_a_4192_ = stack[2].m_obj;
lean_object* v_a_4193_ = stack[3].m_obj;
lean_object* v_a_4194_ = stack[4].m_obj;
lean_object* v_a_4195_ = stack[5].m_obj;
lean_object* v_res_4199_;
v_res_4199_ = l_Lean_MVarId_casesRec(v_mvarId_4190_, v_p_4191_, v_a_4192_, v_a_4193_, v_a_4194_, v_a_4195_);
stack->m_obj
 = v_res_4199_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesRec___boxed(lean_object* v_mvarId_4200_, lean_object* v_p_4201_, lean_object* v_a_4202_, lean_object* v_a_4203_, lean_object* v_a_4204_, lean_object* v_a_4205_, lean_object* v_a_4206_){
_start:
{
lean_object* v_res_4207_; 
v_res_4207_ = l_Lean_MVarId_casesRec(v_mvarId_4200_, v_p_4201_, v_a_4202_, v_a_4203_, v_a_4204_, v_a_4205_);
lean_dec(v_a_4205_);
lean_dec_ref(v_a_4204_);
lean_dec(v_a_4203_);
lean_dec_ref(v_a_4202_);
return v_res_4207_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0___redArg(lean_object* v_e_4208_, lean_object* v___y_4209_){
_start:
{
uint8_t v___x_4211_; 
v___x_4211_ = l_Lean_Expr_hasMVar(v_e_4208_);
if (v___x_4211_ == 0)
{
lean_object* v___x_4212_; 
v___x_4212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4212_, 0, v_e_4208_);
return v___x_4212_;
}
else
{
lean_object* v___x_4213_; lean_object* v_mctx_4214_; lean_object* v___x_4215_; lean_object* v_fst_4216_; lean_object* v_snd_4217_; lean_object* v___x_4218_; lean_object* v_cache_4219_; lean_object* v_zetaDeltaFVarIds_4220_; lean_object* v_postponed_4221_; lean_object* v_diag_4222_; lean_object* v___x_4224_; uint8_t v_isShared_4225_; uint8_t v_isSharedCheck_4231_; 
v___x_4213_ = lean_st_ref_get(v___y_4209_);
v_mctx_4214_ = lean_ctor_get(v___x_4213_, 0);
lean_inc_ref(v_mctx_4214_);
lean_dec(v___x_4213_);
v___x_4215_ = l_Lean_instantiateMVarsCore(v_mctx_4214_, v_e_4208_);
v_fst_4216_ = lean_ctor_get(v___x_4215_, 0);
lean_inc(v_fst_4216_);
v_snd_4217_ = lean_ctor_get(v___x_4215_, 1);
lean_inc(v_snd_4217_);
lean_dec_ref(v___x_4215_);
v___x_4218_ = lean_st_ref_take(v___y_4209_);
v_cache_4219_ = lean_ctor_get(v___x_4218_, 1);
v_zetaDeltaFVarIds_4220_ = lean_ctor_get(v___x_4218_, 2);
v_postponed_4221_ = lean_ctor_get(v___x_4218_, 3);
v_diag_4222_ = lean_ctor_get(v___x_4218_, 4);
v_isSharedCheck_4231_ = !lean_is_exclusive(v___x_4218_);
if (v_isSharedCheck_4231_ == 0)
{
lean_object* v_unused_4232_; 
v_unused_4232_ = lean_ctor_get(v___x_4218_, 0);
lean_dec(v_unused_4232_);
v___x_4224_ = v___x_4218_;
v_isShared_4225_ = v_isSharedCheck_4231_;
goto v_resetjp_4223_;
}
else
{
lean_inc(v_diag_4222_);
lean_inc(v_postponed_4221_);
lean_inc(v_zetaDeltaFVarIds_4220_);
lean_inc(v_cache_4219_);
lean_dec(v___x_4218_);
v___x_4224_ = lean_box(0);
v_isShared_4225_ = v_isSharedCheck_4231_;
goto v_resetjp_4223_;
}
v_resetjp_4223_:
{
lean_object* v___x_4227_; 
if (v_isShared_4225_ == 0)
{
lean_ctor_set(v___x_4224_, 0, v_snd_4217_);
v___x_4227_ = v___x_4224_;
goto v_reusejp_4226_;
}
else
{
lean_object* v_reuseFailAlloc_4230_; 
v_reuseFailAlloc_4230_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4230_, 0, v_snd_4217_);
lean_ctor_set(v_reuseFailAlloc_4230_, 1, v_cache_4219_);
lean_ctor_set(v_reuseFailAlloc_4230_, 2, v_zetaDeltaFVarIds_4220_);
lean_ctor_set(v_reuseFailAlloc_4230_, 3, v_postponed_4221_);
lean_ctor_set(v_reuseFailAlloc_4230_, 4, v_diag_4222_);
v___x_4227_ = v_reuseFailAlloc_4230_;
goto v_reusejp_4226_;
}
v_reusejp_4226_:
{
lean_object* v___x_4228_; lean_object* v___x_4229_; 
v___x_4228_ = lean_st_ref_put(v___y_4209_, v___x_4227_);
v___x_4229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4229_, 0, v_fst_4216_);
return v___x_4229_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_4208_ = stack[0].m_obj;
lean_object* v___y_4209_ = stack[1].m_obj;
lean_object* v_res_4233_;
v_res_4233_ = l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0___redArg(v_e_4208_, v___y_4209_);
stack->m_obj
 = v_res_4233_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0___redArg___boxed(lean_object* v_e_4234_, lean_object* v___y_4235_, lean_object* v___y_4236_){
_start:
{
lean_object* v_res_4237_; 
v_res_4237_ = l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0___redArg(v_e_4234_, v___y_4235_);
lean_dec(v___y_4235_);
return v_res_4237_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0(lean_object* v_e_4238_, lean_object* v___y_4239_, lean_object* v___y_4240_, lean_object* v___y_4241_, lean_object* v___y_4242_){
_start:
{
lean_object* v___x_4244_; 
v___x_4244_ = l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0___redArg(v_e_4238_, v___y_4240_);
return v___x_4244_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_4238_ = stack[0].m_obj;
lean_object* v___y_4239_ = stack[1].m_obj;
lean_object* v___y_4240_ = stack[2].m_obj;
lean_object* v___y_4241_ = stack[3].m_obj;
lean_object* v___y_4242_ = stack[4].m_obj;
lean_object* v_res_4245_;
v_res_4245_ = l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0(v_e_4238_, v___y_4239_, v___y_4240_, v___y_4241_, v___y_4242_);
stack->m_obj
 = v_res_4245_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0___boxed(lean_object* v_e_4246_, lean_object* v___y_4247_, lean_object* v___y_4248_, lean_object* v___y_4249_, lean_object* v___y_4250_, lean_object* v___y_4251_){
_start:
{
lean_object* v_res_4252_; 
v_res_4252_ = l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0(v_e_4246_, v___y_4247_, v___y_4248_, v___y_4249_, v___y_4250_);
lean_dec(v___y_4250_);
lean_dec_ref(v___y_4249_);
lean_dec(v___y_4248_);
lean_dec_ref(v___y_4247_);
return v_res_4252_;
}
}
lean_object* l_Lean_MVarId_casesAnd___lam__0(lean_object* v_localDecl_4256_, lean_object* v___y_4257_, lean_object* v___y_4258_, lean_object* v___y_4259_, lean_object* v___y_4260_){
_start:
{
lean_object* v___x_4262_; lean_object* v___x_4263_; lean_object* v_a_4264_; lean_object* v___x_4266_; uint8_t v_isShared_4267_; uint8_t v_isSharedCheck_4275_; 
v___x_4262_ = l_Lean_LocalDecl_type(v_localDecl_4256_);
v___x_4263_ = l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0___redArg(v___x_4262_, v___y_4258_);
v_a_4264_ = lean_ctor_get(v___x_4263_, 0);
v_isSharedCheck_4275_ = !lean_is_exclusive(v___x_4263_);
if (v_isSharedCheck_4275_ == 0)
{
v___x_4266_ = v___x_4263_;
v_isShared_4267_ = v_isSharedCheck_4275_;
goto v_resetjp_4265_;
}
else
{
lean_inc(v_a_4264_);
lean_dec(v___x_4263_);
v___x_4266_ = lean_box(0);
v_isShared_4267_ = v_isSharedCheck_4275_;
goto v_resetjp_4265_;
}
v_resetjp_4265_:
{
lean_object* v___x_4268_; lean_object* v___x_4269_; uint8_t v___x_4270_; lean_object* v___x_4271_; lean_object* v___x_4273_; 
v___x_4268_ = ((lean_object*)(l_Lean_MVarId_casesAnd___lam__0___closed__1));
v___x_4269_ = lean_unsigned_to_nat(2u);
v___x_4270_ = l_Lean_Expr_isAppOfArity(v_a_4264_, v___x_4268_, v___x_4269_);
lean_dec(v_a_4264_);
v___x_4271_ = lean_box(v___x_4270_);
if (v_isShared_4267_ == 0)
{
lean_ctor_set(v___x_4266_, 0, v___x_4271_);
v___x_4273_ = v___x_4266_;
goto v_reusejp_4272_;
}
else
{
lean_object* v_reuseFailAlloc_4274_; 
v_reuseFailAlloc_4274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4274_, 0, v___x_4271_);
v___x_4273_ = v_reuseFailAlloc_4274_;
goto v_reusejp_4272_;
}
v_reusejp_4272_:
{
return v___x_4273_;
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_casesAnd___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_localDecl_4256_ = stack[0].m_obj;
lean_object* v___y_4257_ = stack[1].m_obj;
lean_object* v___y_4258_ = stack[2].m_obj;
lean_object* v___y_4259_ = stack[3].m_obj;
lean_object* v___y_4260_ = stack[4].m_obj;
lean_object* v_res_4276_;
v_res_4276_ = l_Lean_MVarId_casesAnd___lam__0(v_localDecl_4256_, v___y_4257_, v___y_4258_, v___y_4259_, v___y_4260_);
stack->m_obj
 = v_res_4276_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesAnd___lam__0___boxed(lean_object* v_localDecl_4277_, lean_object* v___y_4278_, lean_object* v___y_4279_, lean_object* v___y_4280_, lean_object* v___y_4281_, lean_object* v___y_4282_){
_start:
{
lean_object* v_res_4283_; 
v_res_4283_ = l_Lean_MVarId_casesAnd___lam__0(v_localDecl_4277_, v___y_4278_, v___y_4279_, v___y_4280_, v___y_4281_);
lean_dec(v___y_4281_);
lean_dec_ref(v___y_4280_);
lean_dec(v___y_4279_);
lean_dec_ref(v___y_4278_);
lean_dec_ref(v_localDecl_4277_);
return v_res_4283_;
}
}
static lean_object* _init_l_Lean_MVarId_casesAnd___closed__3(void){
_start:
{
lean_object* v___x_4288_; lean_object* v___x_4289_; 
v___x_4288_ = ((lean_object*)(l_Lean_MVarId_casesAnd___closed__2));
v___x_4289_ = l_Lean_MessageData_ofFormat(v___x_4288_);
return v___x_4289_;
}
}
lean_object* l_Lean_MVarId_casesAnd(lean_object* v_mvarId_4290_, lean_object* v_a_4291_, lean_object* v_a_4292_, lean_object* v_a_4293_, lean_object* v_a_4294_){
_start:
{
lean_object* v___f_4296_; lean_object* v___x_4297_; 
v___f_4296_ = ((lean_object*)(l_Lean_MVarId_casesAnd___closed__0));
v___x_4297_ = l_Lean_MVarId_casesRec(v_mvarId_4290_, v___f_4296_, v_a_4291_, v_a_4292_, v_a_4293_, v_a_4294_);
if (lean_obj_tag(v___x_4297_) == 0)
{
lean_object* v_a_4298_; lean_object* v___x_4299_; lean_object* v___x_4300_; 
v_a_4298_ = lean_ctor_get(v___x_4297_, 0);
lean_inc(v_a_4298_);
lean_dec_ref_known(v___x_4297_, 1);
v___x_4299_ = lean_obj_once(&l_Lean_MVarId_casesAnd___closed__3, &l_Lean_MVarId_casesAnd___closed__3_once, _init_l_Lean_MVarId_casesAnd___closed__3);
v___x_4300_ = l_Lean_Meta_exactlyOne(v_a_4298_, v___x_4299_, v_a_4291_, v_a_4292_, v_a_4293_, v_a_4294_);
lean_dec(v_a_4298_);
return v___x_4300_;
}
else
{
lean_object* v_a_4301_; lean_object* v___x_4303_; uint8_t v_isShared_4304_; uint8_t v_isSharedCheck_4308_; 
v_a_4301_ = lean_ctor_get(v___x_4297_, 0);
v_isSharedCheck_4308_ = !lean_is_exclusive(v___x_4297_);
if (v_isSharedCheck_4308_ == 0)
{
v___x_4303_ = v___x_4297_;
v_isShared_4304_ = v_isSharedCheck_4308_;
goto v_resetjp_4302_;
}
else
{
lean_inc(v_a_4301_);
lean_dec(v___x_4297_);
v___x_4303_ = lean_box(0);
v_isShared_4304_ = v_isSharedCheck_4308_;
goto v_resetjp_4302_;
}
v_resetjp_4302_:
{
lean_object* v___x_4306_; 
if (v_isShared_4304_ == 0)
{
v___x_4306_ = v___x_4303_;
goto v_reusejp_4305_;
}
else
{
lean_object* v_reuseFailAlloc_4307_; 
v_reuseFailAlloc_4307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4307_, 0, v_a_4301_);
v___x_4306_ = v_reuseFailAlloc_4307_;
goto v_reusejp_4305_;
}
v_reusejp_4305_:
{
return v___x_4306_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_casesAnd_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_4290_ = stack[0].m_obj;
lean_object* v_a_4291_ = stack[1].m_obj;
lean_object* v_a_4292_ = stack[2].m_obj;
lean_object* v_a_4293_ = stack[3].m_obj;
lean_object* v_a_4294_ = stack[4].m_obj;
lean_object* v_res_4309_;
v_res_4309_ = l_Lean_MVarId_casesAnd(v_mvarId_4290_, v_a_4291_, v_a_4292_, v_a_4293_, v_a_4294_);
stack->m_obj
 = v_res_4309_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesAnd___boxed(lean_object* v_mvarId_4310_, lean_object* v_a_4311_, lean_object* v_a_4312_, lean_object* v_a_4313_, lean_object* v_a_4314_, lean_object* v_a_4315_){
_start:
{
lean_object* v_res_4316_; 
v_res_4316_ = l_Lean_MVarId_casesAnd(v_mvarId_4310_, v_a_4311_, v_a_4312_, v_a_4313_, v_a_4314_);
lean_dec(v_a_4314_);
lean_dec_ref(v_a_4313_);
lean_dec(v_a_4312_);
lean_dec_ref(v_a_4311_);
return v_res_4316_;
}
}
lean_object* l_Lean_MVarId_substEqs___lam__0(lean_object* v_localDecl_4317_, lean_object* v___y_4318_, lean_object* v___y_4319_, lean_object* v___y_4320_, lean_object* v___y_4321_){
_start:
{
lean_object* v___x_4323_; lean_object* v___x_4324_; lean_object* v_a_4325_; lean_object* v___x_4327_; uint8_t v_isShared_4328_; uint8_t v_isSharedCheck_4339_; 
v___x_4323_ = l_Lean_LocalDecl_type(v_localDecl_4317_);
v___x_4324_ = l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0___redArg(v___x_4323_, v___y_4319_);
v_a_4325_ = lean_ctor_get(v___x_4324_, 0);
v_isSharedCheck_4339_ = !lean_is_exclusive(v___x_4324_);
if (v_isSharedCheck_4339_ == 0)
{
v___x_4327_ = v___x_4324_;
v_isShared_4328_ = v_isSharedCheck_4339_;
goto v_resetjp_4326_;
}
else
{
lean_inc(v_a_4325_);
lean_dec(v___x_4324_);
v___x_4327_ = lean_box(0);
v_isShared_4328_ = v_isSharedCheck_4339_;
goto v_resetjp_4326_;
}
v_resetjp_4326_:
{
uint8_t v___x_4329_; 
v___x_4329_ = l_Lean_Expr_isEq(v_a_4325_);
if (v___x_4329_ == 0)
{
uint8_t v___x_4330_; lean_object* v___x_4331_; lean_object* v___x_4333_; 
v___x_4330_ = l_Lean_Expr_isHEq(v_a_4325_);
lean_dec(v_a_4325_);
v___x_4331_ = lean_box(v___x_4330_);
if (v_isShared_4328_ == 0)
{
lean_ctor_set(v___x_4327_, 0, v___x_4331_);
v___x_4333_ = v___x_4327_;
goto v_reusejp_4332_;
}
else
{
lean_object* v_reuseFailAlloc_4334_; 
v_reuseFailAlloc_4334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4334_, 0, v___x_4331_);
v___x_4333_ = v_reuseFailAlloc_4334_;
goto v_reusejp_4332_;
}
v_reusejp_4332_:
{
return v___x_4333_;
}
}
else
{
lean_object* v___x_4335_; lean_object* v___x_4337_; 
lean_dec(v_a_4325_);
v___x_4335_ = lean_box(v___x_4329_);
if (v_isShared_4328_ == 0)
{
lean_ctor_set(v___x_4327_, 0, v___x_4335_);
v___x_4337_ = v___x_4327_;
goto v_reusejp_4336_;
}
else
{
lean_object* v_reuseFailAlloc_4338_; 
v_reuseFailAlloc_4338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4338_, 0, v___x_4335_);
v___x_4337_ = v_reuseFailAlloc_4338_;
goto v_reusejp_4336_;
}
v_reusejp_4336_:
{
return v___x_4337_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_substEqs___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_localDecl_4317_ = stack[0].m_obj;
lean_object* v___y_4318_ = stack[1].m_obj;
lean_object* v___y_4319_ = stack[2].m_obj;
lean_object* v___y_4320_ = stack[3].m_obj;
lean_object* v___y_4321_ = stack[4].m_obj;
lean_object* v_res_4340_;
v_res_4340_ = l_Lean_MVarId_substEqs___lam__0(v_localDecl_4317_, v___y_4318_, v___y_4319_, v___y_4320_, v___y_4321_);
stack->m_obj
 = v_res_4340_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_substEqs___lam__0___boxed(lean_object* v_localDecl_4341_, lean_object* v___y_4342_, lean_object* v___y_4343_, lean_object* v___y_4344_, lean_object* v___y_4345_, lean_object* v___y_4346_){
_start:
{
lean_object* v_res_4347_; 
v_res_4347_ = l_Lean_MVarId_substEqs___lam__0(v_localDecl_4341_, v___y_4342_, v___y_4343_, v___y_4344_, v___y_4345_);
lean_dec(v___y_4345_);
lean_dec_ref(v___y_4344_);
lean_dec(v___y_4343_);
lean_dec_ref(v___y_4342_);
lean_dec_ref(v_localDecl_4341_);
return v_res_4347_;
}
}
lean_object* l_Lean_MVarId_substEqs(lean_object* v_mvarId_4349_, lean_object* v_a_4350_, lean_object* v_a_4351_, lean_object* v_a_4352_, lean_object* v_a_4353_){
_start:
{
lean_object* v___f_4355_; lean_object* v___x_4356_; 
v___f_4355_ = ((lean_object*)(l_Lean_MVarId_substEqs___closed__0));
v___x_4356_ = l_Lean_MVarId_casesRec(v_mvarId_4349_, v___f_4355_, v_a_4350_, v_a_4351_, v_a_4352_, v_a_4353_);
if (lean_obj_tag(v___x_4356_) == 0)
{
lean_object* v_a_4357_; lean_object* v___x_4358_; lean_object* v___x_4359_; 
v_a_4357_ = lean_ctor_get(v___x_4356_, 0);
lean_inc(v_a_4357_);
lean_dec_ref_known(v___x_4356_, 1);
v___x_4358_ = lean_obj_once(&l_Lean_MVarId_casesAnd___closed__3, &l_Lean_MVarId_casesAnd___closed__3_once, _init_l_Lean_MVarId_casesAnd___closed__3);
v___x_4359_ = l_Lean_Meta_ensureAtMostOne(v_a_4357_, v___x_4358_, v_a_4350_, v_a_4351_, v_a_4352_, v_a_4353_);
lean_dec(v_a_4357_);
return v___x_4359_;
}
else
{
lean_object* v_a_4360_; lean_object* v___x_4362_; uint8_t v_isShared_4363_; uint8_t v_isSharedCheck_4367_; 
v_a_4360_ = lean_ctor_get(v___x_4356_, 0);
v_isSharedCheck_4367_ = !lean_is_exclusive(v___x_4356_);
if (v_isSharedCheck_4367_ == 0)
{
v___x_4362_ = v___x_4356_;
v_isShared_4363_ = v_isSharedCheck_4367_;
goto v_resetjp_4361_;
}
else
{
lean_inc(v_a_4360_);
lean_dec(v___x_4356_);
v___x_4362_ = lean_box(0);
v_isShared_4363_ = v_isSharedCheck_4367_;
goto v_resetjp_4361_;
}
v_resetjp_4361_:
{
lean_object* v___x_4365_; 
if (v_isShared_4363_ == 0)
{
v___x_4365_ = v___x_4362_;
goto v_reusejp_4364_;
}
else
{
lean_object* v_reuseFailAlloc_4366_; 
v_reuseFailAlloc_4366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4366_, 0, v_a_4360_);
v___x_4365_ = v_reuseFailAlloc_4366_;
goto v_reusejp_4364_;
}
v_reusejp_4364_:
{
return v___x_4365_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_substEqs_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_4349_ = stack[0].m_obj;
lean_object* v_a_4350_ = stack[1].m_obj;
lean_object* v_a_4351_ = stack[2].m_obj;
lean_object* v_a_4352_ = stack[3].m_obj;
lean_object* v_a_4353_ = stack[4].m_obj;
lean_object* v_res_4368_;
v_res_4368_ = l_Lean_MVarId_substEqs(v_mvarId_4349_, v_a_4350_, v_a_4351_, v_a_4352_, v_a_4353_);
stack->m_obj
 = v_res_4368_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_substEqs___boxed(lean_object* v_mvarId_4369_, lean_object* v_a_4370_, lean_object* v_a_4371_, lean_object* v_a_4372_, lean_object* v_a_4373_, lean_object* v_a_4374_){
_start:
{
lean_object* v_res_4375_; 
v_res_4375_ = l_Lean_MVarId_substEqs(v_mvarId_4369_, v_a_4370_, v_a_4371_, v_a_4372_, v_a_4373_);
lean_dec(v_a_4373_);
lean_dec_ref(v_a_4372_);
lean_dec(v_a_4371_);
lean_dec_ref(v_a_4370_);
return v_res_4375_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkByCasesSubgoal___lam__0(lean_object* v_goalType_4376_, lean_object* v_tag_4377_, lean_object* v_hyp_4378_, lean_object* v___y_4379_, lean_object* v___y_4380_, lean_object* v___y_4381_, lean_object* v___y_4382_){
_start:
{
lean_object* v___x_4384_; 
v___x_4384_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_goalType_4376_, v_tag_4377_, v___y_4379_, v___y_4380_, v___y_4381_, v___y_4382_);
if (lean_obj_tag(v___x_4384_) == 0)
{
lean_object* v_a_4385_; lean_object* v___x_4386_; lean_object* v___x_4387_; lean_object* v___x_4388_; uint8_t v___x_4389_; uint8_t v___x_4390_; uint8_t v___x_4391_; lean_object* v___x_4392_; 
v_a_4385_ = lean_ctor_get(v___x_4384_, 0);
lean_inc_n(v_a_4385_, 2);
lean_dec_ref_known(v___x_4384_, 1);
v___x_4386_ = lean_unsigned_to_nat(1u);
v___x_4387_ = lean_mk_empty_array_with_capacity(v___x_4386_);
lean_inc_ref(v_hyp_4378_);
v___x_4388_ = lean_array_push(v___x_4387_, v_hyp_4378_);
v___x_4389_ = 0;
v___x_4390_ = 1;
v___x_4391_ = 1;
v___x_4392_ = l_Lean_Meta_mkLambdaFVars(v___x_4388_, v_a_4385_, v___x_4389_, v___x_4390_, v___x_4389_, v___x_4390_, v___x_4391_, v___y_4379_, v___y_4380_, v___y_4381_, v___y_4382_);
lean_dec_ref(v___x_4388_);
if (lean_obj_tag(v___x_4392_) == 0)
{
lean_object* v_a_4393_; lean_object* v___x_4395_; uint8_t v_isShared_4396_; uint8_t v_isSharedCheck_4404_; 
v_a_4393_ = lean_ctor_get(v___x_4392_, 0);
v_isSharedCheck_4404_ = !lean_is_exclusive(v___x_4392_);
if (v_isSharedCheck_4404_ == 0)
{
v___x_4395_ = v___x_4392_;
v_isShared_4396_ = v_isSharedCheck_4404_;
goto v_resetjp_4394_;
}
else
{
lean_inc(v_a_4393_);
lean_dec(v___x_4392_);
v___x_4395_ = lean_box(0);
v_isShared_4396_ = v_isSharedCheck_4404_;
goto v_resetjp_4394_;
}
v_resetjp_4394_:
{
lean_object* v___x_4397_; lean_object* v___x_4398_; lean_object* v___x_4399_; lean_object* v___x_4400_; lean_object* v___x_4402_; 
v___x_4397_ = l_Lean_Expr_mvarId_x21(v_a_4385_);
lean_dec(v_a_4385_);
v___x_4398_ = l_Lean_Expr_fvarId_x21(v_hyp_4378_);
lean_dec_ref(v_hyp_4378_);
v___x_4399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4399_, 0, v___x_4397_);
lean_ctor_set(v___x_4399_, 1, v___x_4398_);
v___x_4400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4400_, 0, v_a_4393_);
lean_ctor_set(v___x_4400_, 1, v___x_4399_);
if (v_isShared_4396_ == 0)
{
lean_ctor_set(v___x_4395_, 0, v___x_4400_);
v___x_4402_ = v___x_4395_;
goto v_reusejp_4401_;
}
else
{
lean_object* v_reuseFailAlloc_4403_; 
v_reuseFailAlloc_4403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4403_, 0, v___x_4400_);
v___x_4402_ = v_reuseFailAlloc_4403_;
goto v_reusejp_4401_;
}
v_reusejp_4401_:
{
return v___x_4402_;
}
}
}
else
{
lean_object* v_a_4405_; lean_object* v___x_4407_; uint8_t v_isShared_4408_; uint8_t v_isSharedCheck_4412_; 
lean_dec(v_a_4385_);
lean_dec_ref(v_hyp_4378_);
v_a_4405_ = lean_ctor_get(v___x_4392_, 0);
v_isSharedCheck_4412_ = !lean_is_exclusive(v___x_4392_);
if (v_isSharedCheck_4412_ == 0)
{
v___x_4407_ = v___x_4392_;
v_isShared_4408_ = v_isSharedCheck_4412_;
goto v_resetjp_4406_;
}
else
{
lean_inc(v_a_4405_);
lean_dec(v___x_4392_);
v___x_4407_ = lean_box(0);
v_isShared_4408_ = v_isSharedCheck_4412_;
goto v_resetjp_4406_;
}
v_resetjp_4406_:
{
lean_object* v___x_4410_; 
if (v_isShared_4408_ == 0)
{
v___x_4410_ = v___x_4407_;
goto v_reusejp_4409_;
}
else
{
lean_object* v_reuseFailAlloc_4411_; 
v_reuseFailAlloc_4411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4411_, 0, v_a_4405_);
v___x_4410_ = v_reuseFailAlloc_4411_;
goto v_reusejp_4409_;
}
v_reusejp_4409_:
{
return v___x_4410_;
}
}
}
}
else
{
lean_object* v_a_4413_; lean_object* v___x_4415_; uint8_t v_isShared_4416_; uint8_t v_isSharedCheck_4420_; 
lean_dec_ref(v_hyp_4378_);
v_a_4413_ = lean_ctor_get(v___x_4384_, 0);
v_isSharedCheck_4420_ = !lean_is_exclusive(v___x_4384_);
if (v_isSharedCheck_4420_ == 0)
{
v___x_4415_ = v___x_4384_;
v_isShared_4416_ = v_isSharedCheck_4420_;
goto v_resetjp_4414_;
}
else
{
lean_inc(v_a_4413_);
lean_dec(v___x_4384_);
v___x_4415_ = lean_box(0);
v_isShared_4416_ = v_isSharedCheck_4420_;
goto v_resetjp_4414_;
}
v_resetjp_4414_:
{
lean_object* v___x_4418_; 
if (v_isShared_4416_ == 0)
{
v___x_4418_ = v___x_4415_;
goto v_reusejp_4417_;
}
else
{
lean_object* v_reuseFailAlloc_4419_; 
v_reuseFailAlloc_4419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4419_, 0, v_a_4413_);
v___x_4418_ = v_reuseFailAlloc_4419_;
goto v_reusejp_4417_;
}
v_reusejp_4417_:
{
return v___x_4418_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkByCasesSubgoal___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_goalType_4376_ = stack[0].m_obj;
lean_object* v_tag_4377_ = stack[1].m_obj;
lean_object* v_hyp_4378_ = stack[2].m_obj;
lean_object* v___y_4379_ = stack[3].m_obj;
lean_object* v___y_4380_ = stack[4].m_obj;
lean_object* v___y_4381_ = stack[5].m_obj;
lean_object* v___y_4382_ = stack[6].m_obj;
lean_object* v_res_4421_;
v_res_4421_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkByCasesSubgoal___lam__0(v_goalType_4376_, v_tag_4377_, v_hyp_4378_, v___y_4379_, v___y_4380_, v___y_4381_, v___y_4382_);
stack->m_obj
 = v_res_4421_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkByCasesSubgoal___lam__0___boxed(lean_object* v_goalType_4422_, lean_object* v_tag_4423_, lean_object* v_hyp_4424_, lean_object* v___y_4425_, lean_object* v___y_4426_, lean_object* v___y_4427_, lean_object* v___y_4428_, lean_object* v___y_4429_){
_start:
{
lean_object* v_res_4430_; 
v_res_4430_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkByCasesSubgoal___lam__0(v_goalType_4422_, v_tag_4423_, v_hyp_4424_, v___y_4425_, v___y_4426_, v___y_4427_, v___y_4428_);
lean_dec(v___y_4428_);
lean_dec_ref(v___y_4427_);
lean_dec(v___y_4426_);
lean_dec_ref(v___y_4425_);
return v_res_4430_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkByCasesSubgoal(lean_object* v_p_4431_, lean_object* v_hName_4432_, lean_object* v_goalType_4433_, lean_object* v_tag_4434_, lean_object* v_a_4435_, lean_object* v_a_4436_, lean_object* v_a_4437_, lean_object* v_a_4438_){
_start:
{
lean_object* v___f_4440_; lean_object* v___x_4441_; 
v___f_4440_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkByCasesSubgoal___lam__0___boxed), 8, 2);
lean_closure_set(v___f_4440_, 0, v_goalType_4433_);
lean_closure_set(v___f_4440_, 1, v_tag_4434_);
v___x_4441_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0___redArg(v_hName_4432_, v_p_4431_, v___f_4440_, v_a_4435_, v_a_4436_, v_a_4437_, v_a_4438_);
return v___x_4441_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkByCasesSubgoal_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_4431_ = stack[0].m_obj;
lean_object* v_hName_4432_ = stack[1].m_obj;
lean_object* v_goalType_4433_ = stack[2].m_obj;
lean_object* v_tag_4434_ = stack[3].m_obj;
lean_object* v_a_4435_ = stack[4].m_obj;
lean_object* v_a_4436_ = stack[5].m_obj;
lean_object* v_a_4437_ = stack[6].m_obj;
lean_object* v_a_4438_ = stack[7].m_obj;
lean_object* v_res_4442_;
v_res_4442_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkByCasesSubgoal(v_p_4431_, v_hName_4432_, v_goalType_4433_, v_tag_4434_, v_a_4435_, v_a_4436_, v_a_4437_, v_a_4438_);
stack->m_obj
 = v_res_4442_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkByCasesSubgoal___boxed(lean_object* v_p_4443_, lean_object* v_hName_4444_, lean_object* v_goalType_4445_, lean_object* v_tag_4446_, lean_object* v_a_4447_, lean_object* v_a_4448_, lean_object* v_a_4449_, lean_object* v_a_4450_, lean_object* v_a_4451_){
_start:
{
lean_object* v_res_4452_; 
v_res_4452_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkByCasesSubgoal(v_p_4443_, v_hName_4444_, v_goalType_4445_, v_tag_4446_, v_a_4447_, v_a_4448_, v_a_4449_, v_a_4450_);
lean_dec(v_a_4450_);
lean_dec_ref(v_a_4449_);
lean_dec(v_a_4448_);
lean_dec_ref(v_a_4447_);
return v_res_4452_;
}
}
static lean_object* _init_l_Lean_MVarId_byCases___lam__0___closed__7(void){
_start:
{
lean_object* v___x_4464_; lean_object* v___x_4465_; lean_object* v___x_4466_; 
v___x_4464_ = lean_box(0);
v___x_4465_ = ((lean_object*)(l_Lean_MVarId_byCases___lam__0___closed__6));
v___x_4466_ = l_Lean_Expr_const___override(v___x_4465_, v___x_4464_);
return v___x_4466_;
}
}
static lean_object* _init_l_Lean_MVarId_byCases___lam__0___closed__10(void){
_start:
{
lean_object* v___x_4470_; lean_object* v___x_4471_; 
v___x_4470_ = ((lean_object*)(l_Lean_MVarId_byCases___lam__0___closed__9));
v___x_4471_ = l_Lean_stringToMessageData(v___x_4470_);
return v___x_4471_;
}
}
static lean_object* _init_l_Lean_MVarId_byCases___lam__0___closed__11(void){
_start:
{
lean_object* v___x_4472_; lean_object* v___x_4473_; 
v___x_4472_ = lean_obj_once(&l_Lean_MVarId_byCases___lam__0___closed__10, &l_Lean_MVarId_byCases___lam__0___closed__10_once, _init_l_Lean_MVarId_byCases___lam__0___closed__10);
v___x_4473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4473_, 0, v___x_4472_);
return v___x_4473_;
}
}
lean_object* l_Lean_MVarId_byCases___lam__0(lean_object* v_mvarId_4474_, lean_object* v_p_4475_, lean_object* v_hName_4476_, lean_object* v___y_4477_, lean_object* v___y_4478_, lean_object* v___y_4479_, lean_object* v___y_4480_){
_start:
{
lean_object* v___x_4482_; 
lean_inc(v_mvarId_4474_);
v___x_4482_ = l_Lean_MVarId_getType(v_mvarId_4474_, v___y_4477_, v___y_4478_, v___y_4479_, v___y_4480_);
if (lean_obj_tag(v___x_4482_) == 0)
{
lean_object* v_a_4483_; lean_object* v___x_4484_; 
v_a_4483_ = lean_ctor_get(v___x_4482_, 0);
lean_inc(v_a_4483_);
lean_dec_ref_known(v___x_4482_, 1);
lean_inc(v_mvarId_4474_);
v___x_4484_ = l_Lean_MVarId_getTag(v_mvarId_4474_, v___y_4477_, v___y_4478_, v___y_4479_, v___y_4480_);
if (lean_obj_tag(v___x_4484_) == 0)
{
lean_object* v_a_4485_; lean_object* v___y_4487_; lean_object* v___y_4488_; lean_object* v___y_4489_; lean_object* v___y_4490_; lean_object* v___x_4538_; 
v_a_4485_ = lean_ctor_get(v___x_4484_, 0);
lean_inc(v_a_4485_);
lean_dec_ref_known(v___x_4484_, 1);
lean_inc(v_a_4483_);
v___x_4538_ = l_Lean_Meta_isProp(v_a_4483_, v___y_4477_, v___y_4478_, v___y_4479_, v___y_4480_);
if (lean_obj_tag(v___x_4538_) == 0)
{
lean_object* v_a_4539_; uint8_t v___x_4540_; 
v_a_4539_ = lean_ctor_get(v___x_4538_, 0);
lean_inc(v_a_4539_);
lean_dec_ref_known(v___x_4538_, 1);
v___x_4540_ = lean_unbox(v_a_4539_);
lean_dec(v_a_4539_);
if (v___x_4540_ == 0)
{
lean_object* v___x_4541_; lean_object* v___x_4542_; lean_object* v___x_4543_; 
v___x_4541_ = ((lean_object*)(l_Lean_MVarId_byCases___lam__0___closed__8));
v___x_4542_ = lean_obj_once(&l_Lean_MVarId_byCases___lam__0___closed__11, &l_Lean_MVarId_byCases___lam__0___closed__11_once, _init_l_Lean_MVarId_byCases___lam__0___closed__11);
lean_inc(v_mvarId_4474_);
v___x_4543_ = l_Lean_Meta_throwTacticEx___redArg(v___x_4541_, v_mvarId_4474_, v___x_4542_, v___y_4477_, v___y_4478_, v___y_4479_, v___y_4480_);
if (lean_obj_tag(v___x_4543_) == 0)
{
lean_dec_ref_known(v___x_4543_, 1);
v___y_4487_ = v___y_4477_;
v___y_4488_ = v___y_4478_;
v___y_4489_ = v___y_4479_;
v___y_4490_ = v___y_4480_;
goto v___jp_4486_;
}
else
{
lean_object* v_a_4544_; lean_object* v___x_4546_; uint8_t v_isShared_4547_; uint8_t v_isSharedCheck_4551_; 
lean_dec(v_a_4485_);
lean_dec(v_a_4483_);
lean_dec(v_hName_4476_);
lean_dec_ref(v_p_4475_);
lean_dec(v_mvarId_4474_);
v_a_4544_ = lean_ctor_get(v___x_4543_, 0);
v_isSharedCheck_4551_ = !lean_is_exclusive(v___x_4543_);
if (v_isSharedCheck_4551_ == 0)
{
v___x_4546_ = v___x_4543_;
v_isShared_4547_ = v_isSharedCheck_4551_;
goto v_resetjp_4545_;
}
else
{
lean_inc(v_a_4544_);
lean_dec(v___x_4543_);
v___x_4546_ = lean_box(0);
v_isShared_4547_ = v_isSharedCheck_4551_;
goto v_resetjp_4545_;
}
v_resetjp_4545_:
{
lean_object* v___x_4549_; 
if (v_isShared_4547_ == 0)
{
v___x_4549_ = v___x_4546_;
goto v_reusejp_4548_;
}
else
{
lean_object* v_reuseFailAlloc_4550_; 
v_reuseFailAlloc_4550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4550_, 0, v_a_4544_);
v___x_4549_ = v_reuseFailAlloc_4550_;
goto v_reusejp_4548_;
}
v_reusejp_4548_:
{
return v___x_4549_;
}
}
}
}
else
{
v___y_4487_ = v___y_4477_;
v___y_4488_ = v___y_4478_;
v___y_4489_ = v___y_4479_;
v___y_4490_ = v___y_4480_;
goto v___jp_4486_;
}
}
else
{
lean_object* v_a_4552_; lean_object* v___x_4554_; uint8_t v_isShared_4555_; uint8_t v_isSharedCheck_4559_; 
lean_dec(v_a_4485_);
lean_dec(v_a_4483_);
lean_dec(v_hName_4476_);
lean_dec_ref(v_p_4475_);
lean_dec(v_mvarId_4474_);
v_a_4552_ = lean_ctor_get(v___x_4538_, 0);
v_isSharedCheck_4559_ = !lean_is_exclusive(v___x_4538_);
if (v_isSharedCheck_4559_ == 0)
{
v___x_4554_ = v___x_4538_;
v_isShared_4555_ = v_isSharedCheck_4559_;
goto v_resetjp_4553_;
}
else
{
lean_inc(v_a_4552_);
lean_dec(v___x_4538_);
v___x_4554_ = lean_box(0);
v_isShared_4555_ = v_isSharedCheck_4559_;
goto v_resetjp_4553_;
}
v_resetjp_4553_:
{
lean_object* v___x_4557_; 
if (v_isShared_4555_ == 0)
{
v___x_4557_ = v___x_4554_;
goto v_reusejp_4556_;
}
else
{
lean_object* v_reuseFailAlloc_4558_; 
v_reuseFailAlloc_4558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4558_, 0, v_a_4552_);
v___x_4557_ = v_reuseFailAlloc_4558_;
goto v_reusejp_4556_;
}
v_reusejp_4556_:
{
return v___x_4557_;
}
}
}
v___jp_4486_:
{
lean_object* v___x_4491_; lean_object* v___x_4492_; lean_object* v___x_4493_; 
v___x_4491_ = ((lean_object*)(l_Lean_MVarId_byCases___lam__0___closed__1));
lean_inc(v_a_4485_);
v___x_4492_ = l_Lean_Name_append(v_a_4485_, v___x_4491_);
lean_inc(v_a_4483_);
lean_inc(v_hName_4476_);
lean_inc_ref(v_p_4475_);
v___x_4493_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkByCasesSubgoal(v_p_4475_, v_hName_4476_, v_a_4483_, v___x_4492_, v___y_4487_, v___y_4488_, v___y_4489_, v___y_4490_);
if (lean_obj_tag(v___x_4493_) == 0)
{
lean_object* v_a_4494_; lean_object* v_fst_4495_; lean_object* v_snd_4496_; lean_object* v___x_4497_; lean_object* v___x_4498_; lean_object* v___x_4499_; lean_object* v___x_4500_; 
v_a_4494_ = lean_ctor_get(v___x_4493_, 0);
lean_inc(v_a_4494_);
lean_dec_ref_known(v___x_4493_, 1);
v_fst_4495_ = lean_ctor_get(v_a_4494_, 0);
lean_inc(v_fst_4495_);
v_snd_4496_ = lean_ctor_get(v_a_4494_, 1);
lean_inc(v_snd_4496_);
lean_dec(v_a_4494_);
lean_inc_ref(v_p_4475_);
v___x_4497_ = l_Lean_mkNot(v_p_4475_);
v___x_4498_ = ((lean_object*)(l_Lean_MVarId_byCases___lam__0___closed__3));
v___x_4499_ = l_Lean_Name_append(v_a_4485_, v___x_4498_);
lean_inc(v_a_4483_);
v___x_4500_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkByCasesSubgoal(v___x_4497_, v_hName_4476_, v_a_4483_, v___x_4499_, v___y_4487_, v___y_4488_, v___y_4489_, v___y_4490_);
if (lean_obj_tag(v___x_4500_) == 0)
{
lean_object* v_a_4501_; lean_object* v_fst_4502_; lean_object* v_snd_4503_; lean_object* v___x_4505_; uint8_t v_isShared_4506_; uint8_t v_isSharedCheck_4521_; 
v_a_4501_ = lean_ctor_get(v___x_4500_, 0);
lean_inc(v_a_4501_);
lean_dec_ref_known(v___x_4500_, 1);
v_fst_4502_ = lean_ctor_get(v_a_4501_, 0);
v_snd_4503_ = lean_ctor_get(v_a_4501_, 1);
v_isSharedCheck_4521_ = !lean_is_exclusive(v_a_4501_);
if (v_isSharedCheck_4521_ == 0)
{
v___x_4505_ = v_a_4501_;
v_isShared_4506_ = v_isSharedCheck_4521_;
goto v_resetjp_4504_;
}
else
{
lean_inc(v_snd_4503_);
lean_inc(v_fst_4502_);
lean_dec(v_a_4501_);
v___x_4505_ = lean_box(0);
v_isShared_4506_ = v_isSharedCheck_4521_;
goto v_resetjp_4504_;
}
v_resetjp_4504_:
{
lean_object* v___x_4507_; lean_object* v___x_4508_; lean_object* v___x_4509_; lean_object* v___x_4511_; uint8_t v_isShared_4512_; uint8_t v_isSharedCheck_4519_; 
v___x_4507_ = lean_obj_once(&l_Lean_MVarId_byCases___lam__0___closed__7, &l_Lean_MVarId_byCases___lam__0___closed__7_once, _init_l_Lean_MVarId_byCases___lam__0___closed__7);
v___x_4508_ = l_Lean_mkApp4(v___x_4507_, v_p_4475_, v_a_4483_, v_fst_4495_, v_fst_4502_);
v___x_4509_ = l_Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1___redArg(v_mvarId_4474_, v___x_4508_, v___y_4488_);
v_isSharedCheck_4519_ = !lean_is_exclusive(v___x_4509_);
if (v_isSharedCheck_4519_ == 0)
{
lean_object* v_unused_4520_; 
v_unused_4520_ = lean_ctor_get(v___x_4509_, 0);
lean_dec(v_unused_4520_);
v___x_4511_ = v___x_4509_;
v_isShared_4512_ = v_isSharedCheck_4519_;
goto v_resetjp_4510_;
}
else
{
lean_dec(v___x_4509_);
v___x_4511_ = lean_box(0);
v_isShared_4512_ = v_isSharedCheck_4519_;
goto v_resetjp_4510_;
}
v_resetjp_4510_:
{
lean_object* v___x_4514_; 
if (v_isShared_4506_ == 0)
{
lean_ctor_set(v___x_4505_, 0, v_snd_4496_);
v___x_4514_ = v___x_4505_;
goto v_reusejp_4513_;
}
else
{
lean_object* v_reuseFailAlloc_4518_; 
v_reuseFailAlloc_4518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4518_, 0, v_snd_4496_);
lean_ctor_set(v_reuseFailAlloc_4518_, 1, v_snd_4503_);
v___x_4514_ = v_reuseFailAlloc_4518_;
goto v_reusejp_4513_;
}
v_reusejp_4513_:
{
lean_object* v___x_4516_; 
if (v_isShared_4512_ == 0)
{
lean_ctor_set(v___x_4511_, 0, v___x_4514_);
v___x_4516_ = v___x_4511_;
goto v_reusejp_4515_;
}
else
{
lean_object* v_reuseFailAlloc_4517_; 
v_reuseFailAlloc_4517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4517_, 0, v___x_4514_);
v___x_4516_ = v_reuseFailAlloc_4517_;
goto v_reusejp_4515_;
}
v_reusejp_4515_:
{
return v___x_4516_;
}
}
}
}
}
else
{
lean_object* v_a_4522_; lean_object* v___x_4524_; uint8_t v_isShared_4525_; uint8_t v_isSharedCheck_4529_; 
lean_dec(v_snd_4496_);
lean_dec(v_fst_4495_);
lean_dec(v_a_4483_);
lean_dec_ref(v_p_4475_);
lean_dec(v_mvarId_4474_);
v_a_4522_ = lean_ctor_get(v___x_4500_, 0);
v_isSharedCheck_4529_ = !lean_is_exclusive(v___x_4500_);
if (v_isSharedCheck_4529_ == 0)
{
v___x_4524_ = v___x_4500_;
v_isShared_4525_ = v_isSharedCheck_4529_;
goto v_resetjp_4523_;
}
else
{
lean_inc(v_a_4522_);
lean_dec(v___x_4500_);
v___x_4524_ = lean_box(0);
v_isShared_4525_ = v_isSharedCheck_4529_;
goto v_resetjp_4523_;
}
v_resetjp_4523_:
{
lean_object* v___x_4527_; 
if (v_isShared_4525_ == 0)
{
v___x_4527_ = v___x_4524_;
goto v_reusejp_4526_;
}
else
{
lean_object* v_reuseFailAlloc_4528_; 
v_reuseFailAlloc_4528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4528_, 0, v_a_4522_);
v___x_4527_ = v_reuseFailAlloc_4528_;
goto v_reusejp_4526_;
}
v_reusejp_4526_:
{
return v___x_4527_;
}
}
}
}
else
{
lean_object* v_a_4530_; lean_object* v___x_4532_; uint8_t v_isShared_4533_; uint8_t v_isSharedCheck_4537_; 
lean_dec(v_a_4485_);
lean_dec(v_a_4483_);
lean_dec(v_hName_4476_);
lean_dec_ref(v_p_4475_);
lean_dec(v_mvarId_4474_);
v_a_4530_ = lean_ctor_get(v___x_4493_, 0);
v_isSharedCheck_4537_ = !lean_is_exclusive(v___x_4493_);
if (v_isSharedCheck_4537_ == 0)
{
v___x_4532_ = v___x_4493_;
v_isShared_4533_ = v_isSharedCheck_4537_;
goto v_resetjp_4531_;
}
else
{
lean_inc(v_a_4530_);
lean_dec(v___x_4493_);
v___x_4532_ = lean_box(0);
v_isShared_4533_ = v_isSharedCheck_4537_;
goto v_resetjp_4531_;
}
v_resetjp_4531_:
{
lean_object* v___x_4535_; 
if (v_isShared_4533_ == 0)
{
v___x_4535_ = v___x_4532_;
goto v_reusejp_4534_;
}
else
{
lean_object* v_reuseFailAlloc_4536_; 
v_reuseFailAlloc_4536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4536_, 0, v_a_4530_);
v___x_4535_ = v_reuseFailAlloc_4536_;
goto v_reusejp_4534_;
}
v_reusejp_4534_:
{
return v___x_4535_;
}
}
}
}
}
else
{
lean_object* v_a_4560_; lean_object* v___x_4562_; uint8_t v_isShared_4563_; uint8_t v_isSharedCheck_4567_; 
lean_dec(v_a_4483_);
lean_dec(v_hName_4476_);
lean_dec_ref(v_p_4475_);
lean_dec(v_mvarId_4474_);
v_a_4560_ = lean_ctor_get(v___x_4484_, 0);
v_isSharedCheck_4567_ = !lean_is_exclusive(v___x_4484_);
if (v_isSharedCheck_4567_ == 0)
{
v___x_4562_ = v___x_4484_;
v_isShared_4563_ = v_isSharedCheck_4567_;
goto v_resetjp_4561_;
}
else
{
lean_inc(v_a_4560_);
lean_dec(v___x_4484_);
v___x_4562_ = lean_box(0);
v_isShared_4563_ = v_isSharedCheck_4567_;
goto v_resetjp_4561_;
}
v_resetjp_4561_:
{
lean_object* v___x_4565_; 
if (v_isShared_4563_ == 0)
{
v___x_4565_ = v___x_4562_;
goto v_reusejp_4564_;
}
else
{
lean_object* v_reuseFailAlloc_4566_; 
v_reuseFailAlloc_4566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4566_, 0, v_a_4560_);
v___x_4565_ = v_reuseFailAlloc_4566_;
goto v_reusejp_4564_;
}
v_reusejp_4564_:
{
return v___x_4565_;
}
}
}
}
else
{
lean_object* v_a_4568_; lean_object* v___x_4570_; uint8_t v_isShared_4571_; uint8_t v_isSharedCheck_4575_; 
lean_dec(v_hName_4476_);
lean_dec_ref(v_p_4475_);
lean_dec(v_mvarId_4474_);
v_a_4568_ = lean_ctor_get(v___x_4482_, 0);
v_isSharedCheck_4575_ = !lean_is_exclusive(v___x_4482_);
if (v_isSharedCheck_4575_ == 0)
{
v___x_4570_ = v___x_4482_;
v_isShared_4571_ = v_isSharedCheck_4575_;
goto v_resetjp_4569_;
}
else
{
lean_inc(v_a_4568_);
lean_dec(v___x_4482_);
v___x_4570_ = lean_box(0);
v_isShared_4571_ = v_isSharedCheck_4575_;
goto v_resetjp_4569_;
}
v_resetjp_4569_:
{
lean_object* v___x_4573_; 
if (v_isShared_4571_ == 0)
{
v___x_4573_ = v___x_4570_;
goto v_reusejp_4572_;
}
else
{
lean_object* v_reuseFailAlloc_4574_; 
v_reuseFailAlloc_4574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4574_, 0, v_a_4568_);
v___x_4573_ = v_reuseFailAlloc_4574_;
goto v_reusejp_4572_;
}
v_reusejp_4572_:
{
return v___x_4573_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_byCases___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_4474_ = stack[0].m_obj;
lean_object* v_p_4475_ = stack[1].m_obj;
lean_object* v_hName_4476_ = stack[2].m_obj;
lean_object* v___y_4477_ = stack[3].m_obj;
lean_object* v___y_4478_ = stack[4].m_obj;
lean_object* v___y_4479_ = stack[5].m_obj;
lean_object* v___y_4480_ = stack[6].m_obj;
lean_object* v_res_4576_;
v_res_4576_ = l_Lean_MVarId_byCases___lam__0(v_mvarId_4474_, v_p_4475_, v_hName_4476_, v___y_4477_, v___y_4478_, v___y_4479_, v___y_4480_);
stack->m_obj
 = v_res_4576_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_byCases___lam__0___boxed(lean_object* v_mvarId_4577_, lean_object* v_p_4578_, lean_object* v_hName_4579_, lean_object* v___y_4580_, lean_object* v___y_4581_, lean_object* v___y_4582_, lean_object* v___y_4583_, lean_object* v___y_4584_){
_start:
{
lean_object* v_res_4585_; 
v_res_4585_ = l_Lean_MVarId_byCases___lam__0(v_mvarId_4577_, v_p_4578_, v_hName_4579_, v___y_4580_, v___y_4581_, v___y_4582_, v___y_4583_);
lean_dec(v___y_4583_);
lean_dec_ref(v___y_4582_);
lean_dec(v___y_4581_);
lean_dec_ref(v___y_4580_);
return v_res_4585_;
}
}
lean_object* l_Lean_MVarId_byCases(lean_object* v_mvarId_4586_, lean_object* v_p_4587_, lean_object* v_hName_4588_, lean_object* v_a_4589_, lean_object* v_a_4590_, lean_object* v_a_4591_, lean_object* v_a_4592_){
_start:
{
lean_object* v___f_4594_; lean_object* v___x_4595_; 
lean_inc(v_mvarId_4586_);
v___f_4594_ = lean_alloc_closure((void*)(l_Lean_MVarId_byCases___lam__0___boxed), 8, 3);
lean_closure_set(v___f_4594_, 0, v_mvarId_4586_);
lean_closure_set(v___f_4594_, 1, v_p_4587_);
lean_closure_set(v___f_4594_, 2, v_hName_4588_);
v___x_4595_ = l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2___redArg(v_mvarId_4586_, v___f_4594_, v_a_4589_, v_a_4590_, v_a_4591_, v_a_4592_);
return v___x_4595_;
}
}
LEAN_EXPORT void l_Lean_MVarId_byCases_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_4586_ = stack[0].m_obj;
lean_object* v_p_4587_ = stack[1].m_obj;
lean_object* v_hName_4588_ = stack[2].m_obj;
lean_object* v_a_4589_ = stack[3].m_obj;
lean_object* v_a_4590_ = stack[4].m_obj;
lean_object* v_a_4591_ = stack[5].m_obj;
lean_object* v_a_4592_ = stack[6].m_obj;
lean_object* v_res_4596_;
v_res_4596_ = l_Lean_MVarId_byCases(v_mvarId_4586_, v_p_4587_, v_hName_4588_, v_a_4589_, v_a_4590_, v_a_4591_, v_a_4592_);
stack->m_obj
 = v_res_4596_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_byCases___boxed(lean_object* v_mvarId_4597_, lean_object* v_p_4598_, lean_object* v_hName_4599_, lean_object* v_a_4600_, lean_object* v_a_4601_, lean_object* v_a_4602_, lean_object* v_a_4603_, lean_object* v_a_4604_){
_start:
{
lean_object* v_res_4605_; 
v_res_4605_ = l_Lean_MVarId_byCases(v_mvarId_4597_, v_p_4598_, v_hName_4599_, v_a_4600_, v_a_4601_, v_a_4602_, v_a_4603_);
lean_dec(v_a_4603_);
lean_dec_ref(v_a_4602_);
lean_dec(v_a_4601_);
lean_dec_ref(v_a_4600_);
return v_res_4605_;
}
}
lean_object* l_Lean_MVarId_byCasesDec___lam__0(lean_object* v_mvarId_4609_, lean_object* v_p_4610_, lean_object* v_hName_4611_, lean_object* v_dec_4612_, lean_object* v___y_4613_, lean_object* v___y_4614_, lean_object* v___y_4615_, lean_object* v___y_4616_){
_start:
{
lean_object* v___x_4618_; 
lean_inc(v_mvarId_4609_);
v___x_4618_ = l_Lean_MVarId_getType(v_mvarId_4609_, v___y_4613_, v___y_4614_, v___y_4615_, v___y_4616_);
if (lean_obj_tag(v___x_4618_) == 0)
{
lean_object* v_a_4619_; lean_object* v___x_4620_; 
v_a_4619_ = lean_ctor_get(v___x_4618_, 0);
lean_inc(v_a_4619_);
lean_dec_ref_known(v___x_4618_, 1);
lean_inc(v_mvarId_4609_);
v___x_4620_ = l_Lean_MVarId_getTag(v_mvarId_4609_, v___y_4613_, v___y_4614_, v___y_4615_, v___y_4616_);
if (lean_obj_tag(v___x_4620_) == 0)
{
lean_object* v_a_4621_; lean_object* v___x_4622_; 
v_a_4621_ = lean_ctor_get(v___x_4620_, 0);
lean_inc(v_a_4621_);
lean_dec_ref_known(v___x_4620_, 1);
lean_inc(v_a_4619_);
v___x_4622_ = l_Lean_Meta_getLevel(v_a_4619_, v___y_4613_, v___y_4614_, v___y_4615_, v___y_4616_);
if (lean_obj_tag(v___x_4622_) == 0)
{
lean_object* v_a_4623_; lean_object* v___x_4624_; lean_object* v___x_4625_; lean_object* v___x_4626_; 
v_a_4623_ = lean_ctor_get(v___x_4622_, 0);
lean_inc(v_a_4623_);
lean_dec_ref_known(v___x_4622_, 1);
v___x_4624_ = ((lean_object*)(l_Lean_MVarId_byCases___lam__0___closed__1));
lean_inc(v_a_4621_);
v___x_4625_ = l_Lean_Name_append(v_a_4621_, v___x_4624_);
lean_inc(v_a_4619_);
lean_inc(v_hName_4611_);
lean_inc_ref(v_p_4610_);
v___x_4626_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkByCasesSubgoal(v_p_4610_, v_hName_4611_, v_a_4619_, v___x_4625_, v___y_4613_, v___y_4614_, v___y_4615_, v___y_4616_);
if (lean_obj_tag(v___x_4626_) == 0)
{
lean_object* v_a_4627_; lean_object* v_fst_4628_; lean_object* v_snd_4629_; lean_object* v___x_4631_; uint8_t v_isShared_4632_; uint8_t v_isSharedCheck_4671_; 
v_a_4627_ = lean_ctor_get(v___x_4626_, 0);
lean_inc(v_a_4627_);
lean_dec_ref_known(v___x_4626_, 1);
v_fst_4628_ = lean_ctor_get(v_a_4627_, 0);
v_snd_4629_ = lean_ctor_get(v_a_4627_, 1);
v_isSharedCheck_4671_ = !lean_is_exclusive(v_a_4627_);
if (v_isSharedCheck_4671_ == 0)
{
v___x_4631_ = v_a_4627_;
v_isShared_4632_ = v_isSharedCheck_4671_;
goto v_resetjp_4630_;
}
else
{
lean_inc(v_snd_4629_);
lean_inc(v_fst_4628_);
lean_dec(v_a_4627_);
v___x_4631_ = lean_box(0);
v_isShared_4632_ = v_isSharedCheck_4671_;
goto v_resetjp_4630_;
}
v_resetjp_4630_:
{
lean_object* v___x_4633_; lean_object* v___x_4634_; lean_object* v___x_4635_; lean_object* v___x_4636_; 
lean_inc_ref(v_p_4610_);
v___x_4633_ = l_Lean_mkNot(v_p_4610_);
v___x_4634_ = ((lean_object*)(l_Lean_MVarId_byCases___lam__0___closed__3));
v___x_4635_ = l_Lean_Name_append(v_a_4621_, v___x_4634_);
lean_inc(v_a_4619_);
v___x_4636_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkByCasesSubgoal(v___x_4633_, v_hName_4611_, v_a_4619_, v___x_4635_, v___y_4613_, v___y_4614_, v___y_4615_, v___y_4616_);
if (lean_obj_tag(v___x_4636_) == 0)
{
lean_object* v_a_4637_; lean_object* v_fst_4638_; lean_object* v_snd_4639_; lean_object* v___x_4641_; uint8_t v_isShared_4642_; uint8_t v_isSharedCheck_4662_; 
v_a_4637_ = lean_ctor_get(v___x_4636_, 0);
lean_inc(v_a_4637_);
lean_dec_ref_known(v___x_4636_, 1);
v_fst_4638_ = lean_ctor_get(v_a_4637_, 0);
v_snd_4639_ = lean_ctor_get(v_a_4637_, 1);
v_isSharedCheck_4662_ = !lean_is_exclusive(v_a_4637_);
if (v_isSharedCheck_4662_ == 0)
{
v___x_4641_ = v_a_4637_;
v_isShared_4642_ = v_isSharedCheck_4662_;
goto v_resetjp_4640_;
}
else
{
lean_inc(v_snd_4639_);
lean_inc(v_fst_4638_);
lean_dec(v_a_4637_);
v___x_4641_ = lean_box(0);
v_isShared_4642_ = v_isSharedCheck_4662_;
goto v_resetjp_4640_;
}
v_resetjp_4640_:
{
lean_object* v___x_4643_; lean_object* v___x_4644_; lean_object* v___x_4646_; 
v___x_4643_ = ((lean_object*)(l_Lean_MVarId_byCasesDec___lam__0___closed__1));
v___x_4644_ = lean_box(0);
if (v_isShared_4632_ == 0)
{
lean_ctor_set_tag(v___x_4631_, 1);
lean_ctor_set(v___x_4631_, 1, v___x_4644_);
lean_ctor_set(v___x_4631_, 0, v_a_4623_);
v___x_4646_ = v___x_4631_;
goto v_reusejp_4645_;
}
else
{
lean_object* v_reuseFailAlloc_4661_; 
v_reuseFailAlloc_4661_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4661_, 0, v_a_4623_);
lean_ctor_set(v_reuseFailAlloc_4661_, 1, v___x_4644_);
v___x_4646_ = v_reuseFailAlloc_4661_;
goto v_reusejp_4645_;
}
v_reusejp_4645_:
{
lean_object* v___x_4647_; lean_object* v___x_4648_; lean_object* v___x_4649_; lean_object* v___x_4651_; uint8_t v_isShared_4652_; uint8_t v_isSharedCheck_4659_; 
v___x_4647_ = l_Lean_Expr_const___override(v___x_4643_, v___x_4646_);
v___x_4648_ = l_Lean_mkApp5(v___x_4647_, v_a_4619_, v_p_4610_, v_dec_4612_, v_fst_4628_, v_fst_4638_);
v___x_4649_ = l_Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1___redArg(v_mvarId_4609_, v___x_4648_, v___y_4614_);
v_isSharedCheck_4659_ = !lean_is_exclusive(v___x_4649_);
if (v_isSharedCheck_4659_ == 0)
{
lean_object* v_unused_4660_; 
v_unused_4660_ = lean_ctor_get(v___x_4649_, 0);
lean_dec(v_unused_4660_);
v___x_4651_ = v___x_4649_;
v_isShared_4652_ = v_isSharedCheck_4659_;
goto v_resetjp_4650_;
}
else
{
lean_dec(v___x_4649_);
v___x_4651_ = lean_box(0);
v_isShared_4652_ = v_isSharedCheck_4659_;
goto v_resetjp_4650_;
}
v_resetjp_4650_:
{
lean_object* v___x_4654_; 
if (v_isShared_4642_ == 0)
{
lean_ctor_set(v___x_4641_, 0, v_snd_4629_);
v___x_4654_ = v___x_4641_;
goto v_reusejp_4653_;
}
else
{
lean_object* v_reuseFailAlloc_4658_; 
v_reuseFailAlloc_4658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4658_, 0, v_snd_4629_);
lean_ctor_set(v_reuseFailAlloc_4658_, 1, v_snd_4639_);
v___x_4654_ = v_reuseFailAlloc_4658_;
goto v_reusejp_4653_;
}
v_reusejp_4653_:
{
lean_object* v___x_4656_; 
if (v_isShared_4652_ == 0)
{
lean_ctor_set(v___x_4651_, 0, v___x_4654_);
v___x_4656_ = v___x_4651_;
goto v_reusejp_4655_;
}
else
{
lean_object* v_reuseFailAlloc_4657_; 
v_reuseFailAlloc_4657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4657_, 0, v___x_4654_);
v___x_4656_ = v_reuseFailAlloc_4657_;
goto v_reusejp_4655_;
}
v_reusejp_4655_:
{
return v___x_4656_;
}
}
}
}
}
}
else
{
lean_object* v_a_4663_; lean_object* v___x_4665_; uint8_t v_isShared_4666_; uint8_t v_isSharedCheck_4670_; 
lean_del_object(v___x_4631_);
lean_dec(v_snd_4629_);
lean_dec(v_fst_4628_);
lean_dec(v_a_4623_);
lean_dec(v_a_4619_);
lean_dec_ref(v_dec_4612_);
lean_dec_ref(v_p_4610_);
lean_dec(v_mvarId_4609_);
v_a_4663_ = lean_ctor_get(v___x_4636_, 0);
v_isSharedCheck_4670_ = !lean_is_exclusive(v___x_4636_);
if (v_isSharedCheck_4670_ == 0)
{
v___x_4665_ = v___x_4636_;
v_isShared_4666_ = v_isSharedCheck_4670_;
goto v_resetjp_4664_;
}
else
{
lean_inc(v_a_4663_);
lean_dec(v___x_4636_);
v___x_4665_ = lean_box(0);
v_isShared_4666_ = v_isSharedCheck_4670_;
goto v_resetjp_4664_;
}
v_resetjp_4664_:
{
lean_object* v___x_4668_; 
if (v_isShared_4666_ == 0)
{
v___x_4668_ = v___x_4665_;
goto v_reusejp_4667_;
}
else
{
lean_object* v_reuseFailAlloc_4669_; 
v_reuseFailAlloc_4669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4669_, 0, v_a_4663_);
v___x_4668_ = v_reuseFailAlloc_4669_;
goto v_reusejp_4667_;
}
v_reusejp_4667_:
{
return v___x_4668_;
}
}
}
}
}
else
{
lean_object* v_a_4672_; lean_object* v___x_4674_; uint8_t v_isShared_4675_; uint8_t v_isSharedCheck_4679_; 
lean_dec(v_a_4623_);
lean_dec(v_a_4621_);
lean_dec(v_a_4619_);
lean_dec_ref(v_dec_4612_);
lean_dec(v_hName_4611_);
lean_dec_ref(v_p_4610_);
lean_dec(v_mvarId_4609_);
v_a_4672_ = lean_ctor_get(v___x_4626_, 0);
v_isSharedCheck_4679_ = !lean_is_exclusive(v___x_4626_);
if (v_isSharedCheck_4679_ == 0)
{
v___x_4674_ = v___x_4626_;
v_isShared_4675_ = v_isSharedCheck_4679_;
goto v_resetjp_4673_;
}
else
{
lean_inc(v_a_4672_);
lean_dec(v___x_4626_);
v___x_4674_ = lean_box(0);
v_isShared_4675_ = v_isSharedCheck_4679_;
goto v_resetjp_4673_;
}
v_resetjp_4673_:
{
lean_object* v___x_4677_; 
if (v_isShared_4675_ == 0)
{
v___x_4677_ = v___x_4674_;
goto v_reusejp_4676_;
}
else
{
lean_object* v_reuseFailAlloc_4678_; 
v_reuseFailAlloc_4678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4678_, 0, v_a_4672_);
v___x_4677_ = v_reuseFailAlloc_4678_;
goto v_reusejp_4676_;
}
v_reusejp_4676_:
{
return v___x_4677_;
}
}
}
}
else
{
lean_object* v_a_4680_; lean_object* v___x_4682_; uint8_t v_isShared_4683_; uint8_t v_isSharedCheck_4687_; 
lean_dec(v_a_4621_);
lean_dec(v_a_4619_);
lean_dec_ref(v_dec_4612_);
lean_dec(v_hName_4611_);
lean_dec_ref(v_p_4610_);
lean_dec(v_mvarId_4609_);
v_a_4680_ = lean_ctor_get(v___x_4622_, 0);
v_isSharedCheck_4687_ = !lean_is_exclusive(v___x_4622_);
if (v_isSharedCheck_4687_ == 0)
{
v___x_4682_ = v___x_4622_;
v_isShared_4683_ = v_isSharedCheck_4687_;
goto v_resetjp_4681_;
}
else
{
lean_inc(v_a_4680_);
lean_dec(v___x_4622_);
v___x_4682_ = lean_box(0);
v_isShared_4683_ = v_isSharedCheck_4687_;
goto v_resetjp_4681_;
}
v_resetjp_4681_:
{
lean_object* v___x_4685_; 
if (v_isShared_4683_ == 0)
{
v___x_4685_ = v___x_4682_;
goto v_reusejp_4684_;
}
else
{
lean_object* v_reuseFailAlloc_4686_; 
v_reuseFailAlloc_4686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4686_, 0, v_a_4680_);
v___x_4685_ = v_reuseFailAlloc_4686_;
goto v_reusejp_4684_;
}
v_reusejp_4684_:
{
return v___x_4685_;
}
}
}
}
else
{
lean_object* v_a_4688_; lean_object* v___x_4690_; uint8_t v_isShared_4691_; uint8_t v_isSharedCheck_4695_; 
lean_dec(v_a_4619_);
lean_dec_ref(v_dec_4612_);
lean_dec(v_hName_4611_);
lean_dec_ref(v_p_4610_);
lean_dec(v_mvarId_4609_);
v_a_4688_ = lean_ctor_get(v___x_4620_, 0);
v_isSharedCheck_4695_ = !lean_is_exclusive(v___x_4620_);
if (v_isSharedCheck_4695_ == 0)
{
v___x_4690_ = v___x_4620_;
v_isShared_4691_ = v_isSharedCheck_4695_;
goto v_resetjp_4689_;
}
else
{
lean_inc(v_a_4688_);
lean_dec(v___x_4620_);
v___x_4690_ = lean_box(0);
v_isShared_4691_ = v_isSharedCheck_4695_;
goto v_resetjp_4689_;
}
v_resetjp_4689_:
{
lean_object* v___x_4693_; 
if (v_isShared_4691_ == 0)
{
v___x_4693_ = v___x_4690_;
goto v_reusejp_4692_;
}
else
{
lean_object* v_reuseFailAlloc_4694_; 
v_reuseFailAlloc_4694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4694_, 0, v_a_4688_);
v___x_4693_ = v_reuseFailAlloc_4694_;
goto v_reusejp_4692_;
}
v_reusejp_4692_:
{
return v___x_4693_;
}
}
}
}
else
{
lean_object* v_a_4696_; lean_object* v___x_4698_; uint8_t v_isShared_4699_; uint8_t v_isSharedCheck_4703_; 
lean_dec_ref(v_dec_4612_);
lean_dec(v_hName_4611_);
lean_dec_ref(v_p_4610_);
lean_dec(v_mvarId_4609_);
v_a_4696_ = lean_ctor_get(v___x_4618_, 0);
v_isSharedCheck_4703_ = !lean_is_exclusive(v___x_4618_);
if (v_isSharedCheck_4703_ == 0)
{
v___x_4698_ = v___x_4618_;
v_isShared_4699_ = v_isSharedCheck_4703_;
goto v_resetjp_4697_;
}
else
{
lean_inc(v_a_4696_);
lean_dec(v___x_4618_);
v___x_4698_ = lean_box(0);
v_isShared_4699_ = v_isSharedCheck_4703_;
goto v_resetjp_4697_;
}
v_resetjp_4697_:
{
lean_object* v___x_4701_; 
if (v_isShared_4699_ == 0)
{
v___x_4701_ = v___x_4698_;
goto v_reusejp_4700_;
}
else
{
lean_object* v_reuseFailAlloc_4702_; 
v_reuseFailAlloc_4702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4702_, 0, v_a_4696_);
v___x_4701_ = v_reuseFailAlloc_4702_;
goto v_reusejp_4700_;
}
v_reusejp_4700_:
{
return v___x_4701_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_byCasesDec___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_4609_ = stack[0].m_obj;
lean_object* v_p_4610_ = stack[1].m_obj;
lean_object* v_hName_4611_ = stack[2].m_obj;
lean_object* v_dec_4612_ = stack[3].m_obj;
lean_object* v___y_4613_ = stack[4].m_obj;
lean_object* v___y_4614_ = stack[5].m_obj;
lean_object* v___y_4615_ = stack[6].m_obj;
lean_object* v___y_4616_ = stack[7].m_obj;
lean_object* v_res_4704_;
v_res_4704_ = l_Lean_MVarId_byCasesDec___lam__0(v_mvarId_4609_, v_p_4610_, v_hName_4611_, v_dec_4612_, v___y_4613_, v___y_4614_, v___y_4615_, v___y_4616_);
stack->m_obj
 = v_res_4704_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_byCasesDec___lam__0___boxed(lean_object* v_mvarId_4705_, lean_object* v_p_4706_, lean_object* v_hName_4707_, lean_object* v_dec_4708_, lean_object* v___y_4709_, lean_object* v___y_4710_, lean_object* v___y_4711_, lean_object* v___y_4712_, lean_object* v___y_4713_){
_start:
{
lean_object* v_res_4714_; 
v_res_4714_ = l_Lean_MVarId_byCasesDec___lam__0(v_mvarId_4705_, v_p_4706_, v_hName_4707_, v_dec_4708_, v___y_4709_, v___y_4710_, v___y_4711_, v___y_4712_);
lean_dec(v___y_4712_);
lean_dec_ref(v___y_4711_);
lean_dec(v___y_4710_);
lean_dec_ref(v___y_4709_);
return v_res_4714_;
}
}
lean_object* l_Lean_MVarId_byCasesDec(lean_object* v_mvarId_4715_, lean_object* v_p_4716_, lean_object* v_dec_4717_, lean_object* v_hName_4718_, lean_object* v_a_4719_, lean_object* v_a_4720_, lean_object* v_a_4721_, lean_object* v_a_4722_){
_start:
{
lean_object* v___f_4724_; lean_object* v___x_4725_; 
lean_inc(v_mvarId_4715_);
v___f_4724_ = lean_alloc_closure((void*)(l_Lean_MVarId_byCasesDec___lam__0___boxed), 9, 4);
lean_closure_set(v___f_4724_, 0, v_mvarId_4715_);
lean_closure_set(v___f_4724_, 1, v_p_4716_);
lean_closure_set(v___f_4724_, 2, v_hName_4718_);
lean_closure_set(v___f_4724_, 3, v_dec_4717_);
v___x_4725_ = l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2___redArg(v_mvarId_4715_, v___f_4724_, v_a_4719_, v_a_4720_, v_a_4721_, v_a_4722_);
return v___x_4725_;
}
}
LEAN_EXPORT void l_Lean_MVarId_byCasesDec_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_4715_ = stack[0].m_obj;
lean_object* v_p_4716_ = stack[1].m_obj;
lean_object* v_dec_4717_ = stack[2].m_obj;
lean_object* v_hName_4718_ = stack[3].m_obj;
lean_object* v_a_4719_ = stack[4].m_obj;
lean_object* v_a_4720_ = stack[5].m_obj;
lean_object* v_a_4721_ = stack[6].m_obj;
lean_object* v_a_4722_ = stack[7].m_obj;
lean_object* v_res_4726_;
v_res_4726_ = l_Lean_MVarId_byCasesDec(v_mvarId_4715_, v_p_4716_, v_dec_4717_, v_hName_4718_, v_a_4719_, v_a_4720_, v_a_4721_, v_a_4722_);
stack->m_obj
 = v_res_4726_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_byCasesDec___boxed(lean_object* v_mvarId_4727_, lean_object* v_p_4728_, lean_object* v_dec_4729_, lean_object* v_hName_4730_, lean_object* v_a_4731_, lean_object* v_a_4732_, lean_object* v_a_4733_, lean_object* v_a_4734_, lean_object* v_a_4735_){
_start:
{
lean_object* v_res_4736_; 
v_res_4736_ = l_Lean_MVarId_byCasesDec(v_mvarId_4727_, v_p_4728_, v_dec_4729_, v_hName_4730_, v_a_4731_, v_a_4732_, v_a_4733_, v_a_4734_);
lean_dec(v_a_4734_);
lean_dec_ref(v_a_4733_);
lean_dec(v_a_4732_);
lean_dec_ref(v_a_4731_);
return v_res_4736_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4788_; lean_object* v___x_4789_; lean_object* v___x_4790_; 
v___x_4788_ = lean_unsigned_to_nat(4241171151u);
v___x_4789_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_));
v___x_4790_ = l_Lean_Name_num___override(v___x_4789_, v___x_4788_);
return v___x_4790_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4792_; lean_object* v___x_4793_; lean_object* v___x_4794_; 
v___x_4792_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_));
v___x_4793_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_);
v___x_4794_ = l_Lean_Name_str___override(v___x_4793_, v___x_4792_);
return v___x_4794_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4796_; lean_object* v___x_4797_; lean_object* v___x_4798_; 
v___x_4796_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_));
v___x_4797_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_);
v___x_4798_ = l_Lean_Name_str___override(v___x_4797_, v___x_4796_);
return v___x_4798_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4799_; lean_object* v___x_4800_; lean_object* v___x_4801_; 
v___x_4799_ = lean_unsigned_to_nat(2u);
v___x_4800_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_);
v___x_4801_ = l_Lean_Name_num___override(v___x_4800_, v___x_4799_);
return v___x_4801_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4803_; uint8_t v___x_4804_; lean_object* v___x_4805_; lean_object* v___x_4806_; 
v___x_4803_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_));
v___x_4804_ = 0;
v___x_4805_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_);
v___x_4806_ = l_Lean_registerTraceClass(v___x_4803_, v___x_4804_, v___x_4805_);
return v___x_4806_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4807_;
v_res_4807_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_();
stack->m_obj
 = v_res_4807_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2____boxed(lean_object* v_a_4808_){
_start:
{
lean_object* v_res_4809_; 
v_res_4809_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_();
return v_res_4809_;
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
