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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected_spec__0_spec__0(lean_object* v_msgData_1_, lean_object* v___y_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_){
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected_spec__0_spec__0___boxed(lean_object* v_msgData_19_, lean_object* v___y_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected_spec__0_spec__0(v_msgData_19_, v___y_20_, v___y_21_, v___y_22_, v___y_23_);
lean_dec(v___y_23_);
lean_dec_ref(v___y_22_);
lean_dec(v___y_21_);
lean_dec_ref(v___y_20_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected_spec__0___redArg(lean_object* v_msg_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_, lean_object* v___y_30_){
_start:
{
lean_object* v_ref_32_; lean_object* v___x_33_; lean_object* v_a_34_; lean_object* v___x_36_; uint8_t v_isShared_37_; uint8_t v_isSharedCheck_42_; 
v_ref_32_ = lean_ctor_get(v___y_29_, 2);
v___x_33_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected_spec__0_spec__0(v_msg_26_, v___y_27_, v___y_28_, v___y_29_, v___y_30_);
v_a_34_ = lean_ctor_get(v___x_33_, 0);
v_isSharedCheck_42_ = !lean_is_exclusive(v___x_33_);
if (v_isSharedCheck_42_ == 0)
{
v___x_36_ = v___x_33_;
v_isShared_37_ = v_isSharedCheck_42_;
goto v_resetjp_35_;
}
else
{
lean_inc(v_a_34_);
lean_dec(v___x_33_);
v___x_36_ = lean_box(0);
v_isShared_37_ = v_isSharedCheck_42_;
goto v_resetjp_35_;
}
v_resetjp_35_:
{
lean_object* v___x_38_; lean_object* v___x_40_; 
lean_inc(v_ref_32_);
v___x_38_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_38_, 0, v_ref_32_);
lean_ctor_set(v___x_38_, 1, v_a_34_);
if (v_isShared_37_ == 0)
{
lean_ctor_set_tag(v___x_36_, 1);
lean_ctor_set(v___x_36_, 0, v___x_38_);
v___x_40_ = v___x_36_;
goto v_reusejp_39_;
}
else
{
lean_object* v_reuseFailAlloc_41_; 
v_reuseFailAlloc_41_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_41_, 0, v___x_38_);
v___x_40_ = v_reuseFailAlloc_41_;
goto v_reusejp_39_;
}
v_reusejp_39_:
{
return v___x_40_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected_spec__0___redArg___boxed(lean_object* v_msg_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_){
_start:
{
lean_object* v_res_49_; 
v_res_49_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected_spec__0___redArg(v_msg_43_, v___y_44_, v___y_45_, v___y_46_, v___y_47_);
lean_dec(v___y_47_);
lean_dec_ref(v___y_46_);
lean_dec(v___y_45_);
lean_dec_ref(v___y_44_);
return v_res_49_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg___closed__1(void){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_51_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg___closed__0));
v___x_52_ = l_Lean_stringToMessageData(v___x_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg(lean_object* v_type_53_, lean_object* v_a_54_, lean_object* v_a_55_, lean_object* v_a_56_, lean_object* v_a_57_){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_59_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg___closed__1, &l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg___closed__1);
v___x_60_ = l_Lean_indentExpr(v_type_53_);
v___x_61_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_61_, 0, v___x_59_);
lean_ctor_set(v___x_61_, 1, v___x_60_);
v___x_62_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected_spec__0___redArg(v___x_61_, v_a_54_, v_a_55_, v_a_56_, v_a_57_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg___boxed(lean_object* v_type_63_, lean_object* v_a_64_, lean_object* v_a_65_, lean_object* v_a_66_, lean_object* v_a_67_, lean_object* v_a_68_){
_start:
{
lean_object* v_res_69_; 
v_res_69_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg(v_type_63_, v_a_64_, v_a_65_, v_a_66_, v_a_67_);
lean_dec(v_a_67_);
lean_dec_ref(v_a_66_);
lean_dec(v_a_65_);
lean_dec_ref(v_a_64_);
return v_res_69_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected(lean_object* v_00_u03b1_70_, lean_object* v_type_71_, lean_object* v_a_72_, lean_object* v_a_73_, lean_object* v_a_74_, lean_object* v_a_75_){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg(v_type_71_, v_a_72_, v_a_73_, v_a_74_, v_a_75_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___boxed(lean_object* v_00_u03b1_78_, lean_object* v_type_79_, lean_object* v_a_80_, lean_object* v_a_81_, lean_object* v_a_82_, lean_object* v_a_83_, lean_object* v_a_84_){
_start:
{
lean_object* v_res_85_; 
v_res_85_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected(v_00_u03b1_78_, v_type_79_, v_a_80_, v_a_81_, v_a_82_, v_a_83_);
lean_dec(v_a_83_);
lean_dec_ref(v_a_82_);
lean_dec(v_a_81_);
lean_dec_ref(v_a_80_);
return v_res_85_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected_spec__0(lean_object* v_00_u03b1_86_, lean_object* v_msg_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_){
_start:
{
lean_object* v___x_93_; 
v___x_93_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected_spec__0___redArg(v_msg_87_, v___y_88_, v___y_89_, v___y_90_, v___y_91_);
return v___x_93_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected_spec__0___boxed(lean_object* v_00_u03b1_94_, lean_object* v_msg_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_){
_start:
{
lean_object* v_res_101_; 
v_res_101_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected_spec__0(v_00_u03b1_94_, v_msg_95_, v___y_96_, v___y_97_, v___y_98_, v___y_99_);
lean_dec(v___y_99_);
lean_dec_ref(v___y_98_);
lean_dec(v___y_97_);
lean_dec_ref(v___y_96_);
return v_res_101_;
}
}
static lean_object* _init_l_Lean_Meta_getInductiveUniverseAndParams___closed__0(void){
_start:
{
lean_object* v___x_102_; lean_object* v_dummy_103_; 
v___x_102_ = lean_box(0);
v_dummy_103_ = l_Lean_Expr_sort___override(v___x_102_);
return v_dummy_103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInductiveUniverseAndParams(lean_object* v_type_104_, lean_object* v_a_105_, lean_object* v_a_106_, lean_object* v_a_107_, lean_object* v_a_108_){
_start:
{
lean_object* v___x_110_; 
v___x_110_ = l_Lean_Meta_whnfD(v_type_104_, v_a_105_, v_a_106_, v_a_107_, v_a_108_);
if (lean_obj_tag(v___x_110_) == 0)
{
lean_object* v_a_111_; lean_object* v___x_113_; uint8_t v_isShared_114_; uint8_t v_isSharedCheck_140_; 
v_a_111_ = lean_ctor_get(v___x_110_, 0);
v_isSharedCheck_140_ = !lean_is_exclusive(v___x_110_);
if (v_isSharedCheck_140_ == 0)
{
v___x_113_ = v___x_110_;
v_isShared_114_ = v_isSharedCheck_140_;
goto v_resetjp_112_;
}
else
{
lean_inc(v_a_111_);
lean_dec(v___x_110_);
v___x_113_ = lean_box(0);
v_isShared_114_ = v_isSharedCheck_140_;
goto v_resetjp_112_;
}
v_resetjp_112_:
{
lean_object* v___x_115_; 
v___x_115_ = l_Lean_Expr_getAppFn(v_a_111_);
if (lean_obj_tag(v___x_115_) == 4)
{
lean_object* v_declName_116_; lean_object* v_us_117_; lean_object* v___x_118_; lean_object* v_env_119_; uint8_t v___x_120_; lean_object* v___x_121_; 
v_declName_116_ = lean_ctor_get(v___x_115_, 0);
lean_inc(v_declName_116_);
v_us_117_ = lean_ctor_get(v___x_115_, 1);
lean_inc(v_us_117_);
lean_dec_ref_known(v___x_115_, 2);
v___x_118_ = lean_st_ref_get(v_a_108_);
v_env_119_ = lean_ctor_get(v___x_118_, 0);
lean_inc_ref(v_env_119_);
lean_dec(v___x_118_);
v___x_120_ = 0;
v___x_121_ = l_Lean_Environment_find_x3f(v_env_119_, v_declName_116_, v___x_120_);
if (lean_obj_tag(v___x_121_) == 0)
{
lean_object* v___x_122_; 
lean_dec(v_us_117_);
lean_del_object(v___x_113_);
v___x_122_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg(v_a_111_, v_a_105_, v_a_106_, v_a_107_, v_a_108_);
return v___x_122_;
}
else
{
lean_object* v_val_123_; 
v_val_123_ = lean_ctor_get(v___x_121_, 0);
lean_inc(v_val_123_);
lean_dec_ref_known(v___x_121_, 1);
if (lean_obj_tag(v_val_123_) == 5)
{
lean_object* v_val_124_; lean_object* v_numParams_125_; lean_object* v_nargs_126_; lean_object* v_dummy_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_136_; 
v_val_124_ = lean_ctor_get(v_val_123_, 0);
lean_inc_ref(v_val_124_);
lean_dec_ref_known(v_val_123_, 1);
v_numParams_125_ = lean_ctor_get(v_val_124_, 1);
lean_inc(v_numParams_125_);
lean_dec_ref(v_val_124_);
v_nargs_126_ = l_Lean_Expr_getAppNumArgs(v_a_111_);
v_dummy_127_ = lean_obj_once(&l_Lean_Meta_getInductiveUniverseAndParams___closed__0, &l_Lean_Meta_getInductiveUniverseAndParams___closed__0_once, _init_l_Lean_Meta_getInductiveUniverseAndParams___closed__0);
lean_inc(v_nargs_126_);
v___x_128_ = lean_mk_array(v_nargs_126_, v_dummy_127_);
v___x_129_ = lean_unsigned_to_nat(1u);
v___x_130_ = lean_nat_sub(v_nargs_126_, v___x_129_);
lean_dec(v_nargs_126_);
v___x_131_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_111_, v___x_128_, v___x_130_);
v___x_132_ = lean_unsigned_to_nat(0u);
v___x_133_ = l_Array_extract___redArg(v___x_131_, v___x_132_, v_numParams_125_);
lean_dec_ref(v___x_131_);
v___x_134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_134_, 0, v_us_117_);
lean_ctor_set(v___x_134_, 1, v___x_133_);
if (v_isShared_114_ == 0)
{
lean_ctor_set(v___x_113_, 0, v___x_134_);
v___x_136_ = v___x_113_;
goto v_reusejp_135_;
}
else
{
lean_object* v_reuseFailAlloc_137_; 
v_reuseFailAlloc_137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_137_, 0, v___x_134_);
v___x_136_ = v_reuseFailAlloc_137_;
goto v_reusejp_135_;
}
v_reusejp_135_:
{
return v___x_136_;
}
}
else
{
lean_object* v___x_138_; 
lean_dec(v_val_123_);
lean_dec(v_us_117_);
lean_del_object(v___x_113_);
v___x_138_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg(v_a_111_, v_a_105_, v_a_106_, v_a_107_, v_a_108_);
return v___x_138_;
}
}
}
else
{
lean_object* v___x_139_; 
lean_dec_ref(v___x_115_);
lean_del_object(v___x_113_);
v___x_139_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg(v_a_111_, v_a_105_, v_a_106_, v_a_107_, v_a_108_);
return v___x_139_;
}
}
}
else
{
lean_object* v_a_141_; lean_object* v___x_143_; uint8_t v_isShared_144_; uint8_t v_isSharedCheck_148_; 
v_a_141_ = lean_ctor_get(v___x_110_, 0);
v_isSharedCheck_148_ = !lean_is_exclusive(v___x_110_);
if (v_isSharedCheck_148_ == 0)
{
v___x_143_ = v___x_110_;
v_isShared_144_ = v_isSharedCheck_148_;
goto v_resetjp_142_;
}
else
{
lean_inc(v_a_141_);
lean_dec(v___x_110_);
v___x_143_ = lean_box(0);
v_isShared_144_ = v_isSharedCheck_148_;
goto v_resetjp_142_;
}
v_resetjp_142_:
{
lean_object* v___x_146_; 
if (v_isShared_144_ == 0)
{
v___x_146_ = v___x_143_;
goto v_reusejp_145_;
}
else
{
lean_object* v_reuseFailAlloc_147_; 
v_reuseFailAlloc_147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_147_, 0, v_a_141_);
v___x_146_ = v_reuseFailAlloc_147_;
goto v_reusejp_145_;
}
v_reusejp_145_:
{
return v___x_146_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInductiveUniverseAndParams___boxed(lean_object* v_type_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_, lean_object* v_a_153_, lean_object* v_a_154_){
_start:
{
lean_object* v_res_155_; 
v_res_155_ = l_Lean_Meta_getInductiveUniverseAndParams(v_type_149_, v_a_150_, v_a_151_, v_a_152_, v_a_153_);
lean_dec(v_a_153_);
lean_dec_ref(v_a_152_);
lean_dec(v_a_151_);
lean_dec_ref(v_a_150_);
return v_res_155_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof(lean_object* v_lhs_169_, lean_object* v_rhs_170_, lean_object* v_a_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_){
_start:
{
lean_object* v___x_176_; 
lean_inc(v_a_174_);
lean_inc_ref(v_a_173_);
lean_inc(v_a_172_);
lean_inc_ref(v_a_171_);
lean_inc_ref(v_lhs_169_);
v___x_176_ = lean_infer_type(v_lhs_169_, v_a_171_, v_a_172_, v_a_173_, v_a_174_);
if (lean_obj_tag(v___x_176_) == 0)
{
lean_object* v_a_177_; lean_object* v___x_178_; 
v_a_177_ = lean_ctor_get(v___x_176_, 0);
lean_inc(v_a_177_);
lean_dec_ref_known(v___x_176_, 1);
lean_inc(v_a_174_);
lean_inc_ref(v_a_173_);
lean_inc(v_a_172_);
lean_inc_ref(v_a_171_);
lean_inc_ref(v_rhs_170_);
v___x_178_ = lean_infer_type(v_rhs_170_, v_a_171_, v_a_172_, v_a_173_, v_a_174_);
if (lean_obj_tag(v___x_178_) == 0)
{
lean_object* v_a_179_; lean_object* v___x_180_; 
v_a_179_ = lean_ctor_get(v___x_178_, 0);
lean_inc(v_a_179_);
lean_dec_ref_known(v___x_178_, 1);
lean_inc(v_a_177_);
v___x_180_ = l_Lean_Meta_getLevel(v_a_177_, v_a_171_, v_a_172_, v_a_173_, v_a_174_);
if (lean_obj_tag(v___x_180_) == 0)
{
lean_object* v_a_181_; lean_object* v___x_182_; 
v_a_181_ = lean_ctor_get(v___x_180_, 0);
lean_inc(v_a_181_);
lean_dec_ref_known(v___x_180_, 1);
lean_inc(v_a_179_);
lean_inc(v_a_177_);
v___x_182_ = l_Lean_Meta_isExprDefEq(v_a_177_, v_a_179_, v_a_171_, v_a_172_, v_a_173_, v_a_174_);
if (lean_obj_tag(v___x_182_) == 0)
{
lean_object* v_a_183_; lean_object* v___x_185_; uint8_t v_isShared_186_; uint8_t v_isSharedCheck_212_; 
v_a_183_ = lean_ctor_get(v___x_182_, 0);
v_isSharedCheck_212_ = !lean_is_exclusive(v___x_182_);
if (v_isSharedCheck_212_ == 0)
{
v___x_185_ = v___x_182_;
v_isShared_186_ = v_isSharedCheck_212_;
goto v_resetjp_184_;
}
else
{
lean_inc(v_a_183_);
lean_dec(v___x_182_);
v___x_185_ = lean_box(0);
v_isShared_186_ = v_isSharedCheck_212_;
goto v_resetjp_184_;
}
v_resetjp_184_:
{
uint8_t v___x_187_; 
v___x_187_ = lean_unbox(v_a_183_);
lean_dec(v_a_183_);
if (v___x_187_ == 0)
{
lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_198_; 
v___x_188_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__1));
v___x_189_ = lean_box(0);
v___x_190_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_190_, 0, v_a_181_);
lean_ctor_set(v___x_190_, 1, v___x_189_);
lean_inc_ref(v___x_190_);
v___x_191_ = l_Lean_mkConst(v___x_188_, v___x_190_);
lean_inc_ref(v_lhs_169_);
lean_inc(v_a_177_);
v___x_192_ = l_Lean_mkApp4(v___x_191_, v_a_177_, v_lhs_169_, v_a_179_, v_rhs_170_);
v___x_193_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__3));
v___x_194_ = l_Lean_mkConst(v___x_193_, v___x_190_);
v___x_195_ = l_Lean_mkAppB(v___x_194_, v_a_177_, v_lhs_169_);
v___x_196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_196_, 0, v___x_192_);
lean_ctor_set(v___x_196_, 1, v___x_195_);
if (v_isShared_186_ == 0)
{
lean_ctor_set(v___x_185_, 0, v___x_196_);
v___x_198_ = v___x_185_;
goto v_reusejp_197_;
}
else
{
lean_object* v_reuseFailAlloc_199_; 
v_reuseFailAlloc_199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_199_, 0, v___x_196_);
v___x_198_ = v_reuseFailAlloc_199_;
goto v_reusejp_197_;
}
v_reusejp_197_:
{
return v___x_198_;
}
}
else
{
lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_210_; 
lean_dec(v_a_179_);
v___x_200_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__5));
v___x_201_ = lean_box(0);
v___x_202_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_202_, 0, v_a_181_);
lean_ctor_set(v___x_202_, 1, v___x_201_);
lean_inc_ref(v___x_202_);
v___x_203_ = l_Lean_mkConst(v___x_200_, v___x_202_);
lean_inc_ref(v_lhs_169_);
lean_inc(v_a_177_);
v___x_204_ = l_Lean_mkApp3(v___x_203_, v_a_177_, v_lhs_169_, v_rhs_170_);
v___x_205_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__6));
v___x_206_ = l_Lean_mkConst(v___x_205_, v___x_202_);
v___x_207_ = l_Lean_mkAppB(v___x_206_, v_a_177_, v_lhs_169_);
v___x_208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_208_, 0, v___x_204_);
lean_ctor_set(v___x_208_, 1, v___x_207_);
if (v_isShared_186_ == 0)
{
lean_ctor_set(v___x_185_, 0, v___x_208_);
v___x_210_ = v___x_185_;
goto v_reusejp_209_;
}
else
{
lean_object* v_reuseFailAlloc_211_; 
v_reuseFailAlloc_211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_211_, 0, v___x_208_);
v___x_210_ = v_reuseFailAlloc_211_;
goto v_reusejp_209_;
}
v_reusejp_209_:
{
return v___x_210_;
}
}
}
}
else
{
lean_object* v_a_213_; lean_object* v___x_215_; uint8_t v_isShared_216_; uint8_t v_isSharedCheck_220_; 
lean_dec(v_a_181_);
lean_dec(v_a_179_);
lean_dec(v_a_177_);
lean_dec_ref(v_rhs_170_);
lean_dec_ref(v_lhs_169_);
v_a_213_ = lean_ctor_get(v___x_182_, 0);
v_isSharedCheck_220_ = !lean_is_exclusive(v___x_182_);
if (v_isSharedCheck_220_ == 0)
{
v___x_215_ = v___x_182_;
v_isShared_216_ = v_isSharedCheck_220_;
goto v_resetjp_214_;
}
else
{
lean_inc(v_a_213_);
lean_dec(v___x_182_);
v___x_215_ = lean_box(0);
v_isShared_216_ = v_isSharedCheck_220_;
goto v_resetjp_214_;
}
v_resetjp_214_:
{
lean_object* v___x_218_; 
if (v_isShared_216_ == 0)
{
v___x_218_ = v___x_215_;
goto v_reusejp_217_;
}
else
{
lean_object* v_reuseFailAlloc_219_; 
v_reuseFailAlloc_219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_219_, 0, v_a_213_);
v___x_218_ = v_reuseFailAlloc_219_;
goto v_reusejp_217_;
}
v_reusejp_217_:
{
return v___x_218_;
}
}
}
}
else
{
lean_object* v_a_221_; lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_228_; 
lean_dec(v_a_179_);
lean_dec(v_a_177_);
lean_dec_ref(v_rhs_170_);
lean_dec_ref(v_lhs_169_);
v_a_221_ = lean_ctor_get(v___x_180_, 0);
v_isSharedCheck_228_ = !lean_is_exclusive(v___x_180_);
if (v_isSharedCheck_228_ == 0)
{
v___x_223_ = v___x_180_;
v_isShared_224_ = v_isSharedCheck_228_;
goto v_resetjp_222_;
}
else
{
lean_inc(v_a_221_);
lean_dec(v___x_180_);
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
}
else
{
lean_object* v_a_229_; lean_object* v___x_231_; uint8_t v_isShared_232_; uint8_t v_isSharedCheck_236_; 
lean_dec(v_a_177_);
lean_dec_ref(v_rhs_170_);
lean_dec_ref(v_lhs_169_);
v_a_229_ = lean_ctor_get(v___x_178_, 0);
v_isSharedCheck_236_ = !lean_is_exclusive(v___x_178_);
if (v_isSharedCheck_236_ == 0)
{
v___x_231_ = v___x_178_;
v_isShared_232_ = v_isSharedCheck_236_;
goto v_resetjp_230_;
}
else
{
lean_inc(v_a_229_);
lean_dec(v___x_178_);
v___x_231_ = lean_box(0);
v_isShared_232_ = v_isSharedCheck_236_;
goto v_resetjp_230_;
}
v_resetjp_230_:
{
lean_object* v___x_234_; 
if (v_isShared_232_ == 0)
{
v___x_234_ = v___x_231_;
goto v_reusejp_233_;
}
else
{
lean_object* v_reuseFailAlloc_235_; 
v_reuseFailAlloc_235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_235_, 0, v_a_229_);
v___x_234_ = v_reuseFailAlloc_235_;
goto v_reusejp_233_;
}
v_reusejp_233_:
{
return v___x_234_;
}
}
}
}
else
{
lean_object* v_a_237_; lean_object* v___x_239_; uint8_t v_isShared_240_; uint8_t v_isSharedCheck_244_; 
lean_dec_ref(v_rhs_170_);
lean_dec_ref(v_lhs_169_);
v_a_237_ = lean_ctor_get(v___x_176_, 0);
v_isSharedCheck_244_ = !lean_is_exclusive(v___x_176_);
if (v_isSharedCheck_244_ == 0)
{
v___x_239_ = v___x_176_;
v_isShared_240_ = v_isSharedCheck_244_;
goto v_resetjp_238_;
}
else
{
lean_inc(v_a_237_);
lean_dec(v___x_176_);
v___x_239_ = lean_box(0);
v_isShared_240_ = v_isSharedCheck_244_;
goto v_resetjp_238_;
}
v_resetjp_238_:
{
lean_object* v___x_242_; 
if (v_isShared_240_ == 0)
{
v___x_242_ = v___x_239_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v_a_237_);
v___x_242_ = v_reuseFailAlloc_243_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
return v___x_242_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___boxed(lean_object* v_lhs_245_, lean_object* v_rhs_246_, lean_object* v_a_247_, lean_object* v_a_248_, lean_object* v_a_249_, lean_object* v_a_250_, lean_object* v_a_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof(v_lhs_245_, v_rhs_246_, v_a_247_, v_a_248_, v_a_249_, v_a_250_);
lean_dec(v_a_250_);
lean_dec_ref(v_a_249_);
lean_dec(v_a_248_);
lean_dec_ref(v_a_247_);
return v_res_252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0_spec__0___redArg___lam__0(lean_object* v_k_253_, lean_object* v_b_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_){
_start:
{
lean_object* v___x_260_; 
lean_inc(v___y_258_);
lean_inc_ref(v___y_257_);
lean_inc(v___y_256_);
lean_inc_ref(v___y_255_);
v___x_260_ = lean_apply_6(v_k_253_, v_b_254_, v___y_255_, v___y_256_, v___y_257_, v___y_258_, lean_box(0));
return v___x_260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_k_261_, lean_object* v_b_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_){
_start:
{
lean_object* v_res_268_; 
v_res_268_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0_spec__0___redArg___lam__0(v_k_261_, v_b_262_, v___y_263_, v___y_264_, v___y_265_, v___y_266_);
lean_dec(v___y_266_);
lean_dec_ref(v___y_265_);
lean_dec(v___y_264_);
lean_dec_ref(v___y_263_);
return v_res_268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0_spec__0___redArg(lean_object* v_name_269_, uint8_t v_bi_270_, lean_object* v_type_271_, lean_object* v_k_272_, uint8_t v_kind_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_){
_start:
{
lean_object* v___f_279_; lean_object* v___x_280_; 
v___f_279_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0_spec__0___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_279_, 0, v_k_272_);
v___x_280_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_269_, v_bi_270_, v_type_271_, v___f_279_, v_kind_273_, v___y_274_, v___y_275_, v___y_276_, v___y_277_);
if (lean_obj_tag(v___x_280_) == 0)
{
lean_object* v_a_281_; lean_object* v___x_283_; uint8_t v_isShared_284_; uint8_t v_isSharedCheck_288_; 
v_a_281_ = lean_ctor_get(v___x_280_, 0);
v_isSharedCheck_288_ = !lean_is_exclusive(v___x_280_);
if (v_isSharedCheck_288_ == 0)
{
v___x_283_ = v___x_280_;
v_isShared_284_ = v_isSharedCheck_288_;
goto v_resetjp_282_;
}
else
{
lean_inc(v_a_281_);
lean_dec(v___x_280_);
v___x_283_ = lean_box(0);
v_isShared_284_ = v_isSharedCheck_288_;
goto v_resetjp_282_;
}
v_resetjp_282_:
{
lean_object* v___x_286_; 
if (v_isShared_284_ == 0)
{
v___x_286_ = v___x_283_;
goto v_reusejp_285_;
}
else
{
lean_object* v_reuseFailAlloc_287_; 
v_reuseFailAlloc_287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_287_, 0, v_a_281_);
v___x_286_ = v_reuseFailAlloc_287_;
goto v_reusejp_285_;
}
v_reusejp_285_:
{
return v___x_286_;
}
}
}
else
{
lean_object* v_a_289_; lean_object* v___x_291_; uint8_t v_isShared_292_; uint8_t v_isSharedCheck_296_; 
v_a_289_ = lean_ctor_get(v___x_280_, 0);
v_isSharedCheck_296_ = !lean_is_exclusive(v___x_280_);
if (v_isSharedCheck_296_ == 0)
{
v___x_291_ = v___x_280_;
v_isShared_292_ = v_isSharedCheck_296_;
goto v_resetjp_290_;
}
else
{
lean_inc(v_a_289_);
lean_dec(v___x_280_);
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
v_reuseFailAlloc_295_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0_spec__0___redArg___boxed(lean_object* v_name_297_, lean_object* v_bi_298_, lean_object* v_type_299_, lean_object* v_k_300_, lean_object* v_kind_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_){
_start:
{
uint8_t v_bi_boxed_307_; uint8_t v_kind_boxed_308_; lean_object* v_res_309_; 
v_bi_boxed_307_ = lean_unbox(v_bi_298_);
v_kind_boxed_308_ = lean_unbox(v_kind_301_);
v_res_309_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0_spec__0___redArg(v_name_297_, v_bi_boxed_307_, v_type_299_, v_k_300_, v_kind_boxed_308_, v___y_302_, v___y_303_, v___y_304_, v___y_305_);
lean_dec(v___y_305_);
lean_dec_ref(v___y_304_);
lean_dec(v___y_303_);
lean_dec_ref(v___y_302_);
return v_res_309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0___redArg(lean_object* v_name_310_, lean_object* v_type_311_, lean_object* v_k_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_){
_start:
{
uint8_t v___x_318_; uint8_t v___x_319_; lean_object* v___x_320_; 
v___x_318_ = 0;
v___x_319_ = 0;
v___x_320_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0_spec__0___redArg(v_name_310_, v___x_318_, v_type_311_, v_k_312_, v___x_319_, v___y_313_, v___y_314_, v___y_315_, v___y_316_);
return v___x_320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0___redArg___boxed(lean_object* v_name_321_, lean_object* v_type_322_, lean_object* v_k_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_){
_start:
{
lean_object* v_res_329_; 
v_res_329_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0___redArg(v_name_321_, v_type_322_, v_k_323_, v___y_324_, v___y_325_, v___y_326_, v___y_327_);
lean_dec(v___y_327_);
lean_dec_ref(v___y_326_);
lean_dec(v___y_325_);
lean_dec_ref(v___y_324_);
return v_res_329_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___redArg___lam__0___boxed(lean_object* v_i_330_, lean_object* v_newEqs_331_, lean_object* v_newRefls_332_, lean_object* v_snd_333_, lean_object* v_targets_334_, lean_object* v_targetsNew_335_, lean_object* v_k_336_, lean_object* v_newEq_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_){
_start:
{
lean_object* v_res_343_; 
v_res_343_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___redArg___lam__0(v_i_330_, v_newEqs_331_, v_newRefls_332_, v_snd_333_, v_targets_334_, v_targetsNew_335_, v_k_336_, v_newEq_337_, v___y_338_, v___y_339_, v___y_340_, v___y_341_);
lean_dec(v___y_341_);
lean_dec_ref(v___y_340_);
lean_dec(v___y_339_);
lean_dec_ref(v___y_338_);
lean_dec(v_i_330_);
return v_res_343_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___redArg(lean_object* v_targets_347_, lean_object* v_targetsNew_348_, lean_object* v_k_349_, lean_object* v_i_350_, lean_object* v_newEqs_351_, lean_object* v_newRefls_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_a_356_){
_start:
{
lean_object* v___x_358_; uint8_t v___x_359_; 
v___x_358_ = lean_array_get_size(v_targets_347_);
v___x_359_ = lean_nat_dec_lt(v_i_350_, v___x_358_);
if (v___x_359_ == 0)
{
lean_object* v___x_360_; 
lean_dec(v_i_350_);
lean_dec_ref(v_targetsNew_348_);
lean_dec_ref(v_targets_347_);
lean_inc(v_a_356_);
lean_inc_ref(v_a_355_);
lean_inc(v_a_354_);
lean_inc_ref(v_a_353_);
v___x_360_ = lean_apply_7(v_k_349_, v_newEqs_351_, v_newRefls_352_, v_a_353_, v_a_354_, v_a_355_, v_a_356_, lean_box(0));
return v___x_360_;
}
else
{
lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; 
v___x_361_ = l_Lean_instInhabitedExpr;
v___x_362_ = lean_array_get_borrowed(v___x_361_, v_targets_347_, v_i_350_);
v___x_363_ = lean_array_get_borrowed(v___x_361_, v_targetsNew_348_, v_i_350_);
lean_inc(v___x_363_);
lean_inc(v___x_362_);
v___x_364_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof(v___x_362_, v___x_363_, v_a_353_, v_a_354_, v_a_355_, v_a_356_);
if (lean_obj_tag(v___x_364_) == 0)
{
lean_object* v_a_365_; lean_object* v_fst_366_; lean_object* v_snd_367_; lean_object* v___f_368_; lean_object* v___x_369_; lean_object* v___x_370_; 
v_a_365_ = lean_ctor_get(v___x_364_, 0);
lean_inc(v_a_365_);
lean_dec_ref_known(v___x_364_, 1);
v_fst_366_ = lean_ctor_get(v_a_365_, 0);
lean_inc(v_fst_366_);
v_snd_367_ = lean_ctor_get(v_a_365_, 1);
lean_inc(v_snd_367_);
lean_dec(v_a_365_);
v___f_368_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___redArg___lam__0___boxed), 13, 7);
lean_closure_set(v___f_368_, 0, v_i_350_);
lean_closure_set(v___f_368_, 1, v_newEqs_351_);
lean_closure_set(v___f_368_, 2, v_newRefls_352_);
lean_closure_set(v___f_368_, 3, v_snd_367_);
lean_closure_set(v___f_368_, 4, v_targets_347_);
lean_closure_set(v___f_368_, 5, v_targetsNew_348_);
lean_closure_set(v___f_368_, 6, v_k_349_);
v___x_369_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___redArg___closed__1));
v___x_370_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0___redArg(v___x_369_, v_fst_366_, v___f_368_, v_a_353_, v_a_354_, v_a_355_, v_a_356_);
return v___x_370_;
}
else
{
lean_object* v_a_371_; lean_object* v___x_373_; uint8_t v_isShared_374_; uint8_t v_isSharedCheck_378_; 
lean_dec_ref(v_newRefls_352_);
lean_dec_ref(v_newEqs_351_);
lean_dec(v_i_350_);
lean_dec_ref(v_k_349_);
lean_dec_ref(v_targetsNew_348_);
lean_dec_ref(v_targets_347_);
v_a_371_ = lean_ctor_get(v___x_364_, 0);
v_isSharedCheck_378_ = !lean_is_exclusive(v___x_364_);
if (v_isSharedCheck_378_ == 0)
{
v___x_373_ = v___x_364_;
v_isShared_374_ = v_isSharedCheck_378_;
goto v_resetjp_372_;
}
else
{
lean_inc(v_a_371_);
lean_dec(v___x_364_);
v___x_373_ = lean_box(0);
v_isShared_374_ = v_isSharedCheck_378_;
goto v_resetjp_372_;
}
v_resetjp_372_:
{
lean_object* v___x_376_; 
if (v_isShared_374_ == 0)
{
v___x_376_ = v___x_373_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v_a_371_);
v___x_376_ = v_reuseFailAlloc_377_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
return v___x_376_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___redArg___lam__0(lean_object* v_i_379_, lean_object* v_newEqs_380_, lean_object* v_newRefls_381_, lean_object* v_snd_382_, lean_object* v_targets_383_, lean_object* v_targetsNew_384_, lean_object* v_k_385_, lean_object* v_newEq_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_){
_start:
{
lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; 
v___x_392_ = lean_unsigned_to_nat(1u);
v___x_393_ = lean_nat_add(v_i_379_, v___x_392_);
v___x_394_ = lean_array_push(v_newEqs_380_, v_newEq_386_);
v___x_395_ = lean_array_push(v_newRefls_381_, v_snd_382_);
v___x_396_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___redArg(v_targets_383_, v_targetsNew_384_, v_k_385_, v___x_393_, v___x_394_, v___x_395_, v___y_387_, v___y_388_, v___y_389_, v___y_390_);
return v___x_396_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___redArg___boxed(lean_object* v_targets_397_, lean_object* v_targetsNew_398_, lean_object* v_k_399_, lean_object* v_i_400_, lean_object* v_newEqs_401_, lean_object* v_newRefls_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_){
_start:
{
lean_object* v_res_408_; 
v_res_408_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___redArg(v_targets_397_, v_targetsNew_398_, v_k_399_, v_i_400_, v_newEqs_401_, v_newRefls_402_, v_a_403_, v_a_404_, v_a_405_, v_a_406_);
lean_dec(v_a_406_);
lean_dec_ref(v_a_405_);
lean_dec(v_a_404_);
lean_dec_ref(v_a_403_);
return v_res_408_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop(lean_object* v_00_u03b1_409_, lean_object* v_targets_410_, lean_object* v_targetsNew_411_, lean_object* v_k_412_, lean_object* v_i_413_, lean_object* v_newEqs_414_, lean_object* v_newRefls_415_, lean_object* v_a_416_, lean_object* v_a_417_, lean_object* v_a_418_, lean_object* v_a_419_){
_start:
{
lean_object* v___x_421_; 
v___x_421_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___redArg(v_targets_410_, v_targetsNew_411_, v_k_412_, v_i_413_, v_newEqs_414_, v_newRefls_415_, v_a_416_, v_a_417_, v_a_418_, v_a_419_);
return v___x_421_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___boxed(lean_object* v_00_u03b1_422_, lean_object* v_targets_423_, lean_object* v_targetsNew_424_, lean_object* v_k_425_, lean_object* v_i_426_, lean_object* v_newEqs_427_, lean_object* v_newRefls_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_){
_start:
{
lean_object* v_res_434_; 
v_res_434_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop(v_00_u03b1_422_, v_targets_423_, v_targetsNew_424_, v_k_425_, v_i_426_, v_newEqs_427_, v_newRefls_428_, v_a_429_, v_a_430_, v_a_431_, v_a_432_);
lean_dec(v_a_432_);
lean_dec_ref(v_a_431_);
lean_dec(v_a_430_);
lean_dec_ref(v_a_429_);
return v_res_434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0_spec__0(lean_object* v_00_u03b1_435_, lean_object* v_name_436_, uint8_t v_bi_437_, lean_object* v_type_438_, lean_object* v_k_439_, uint8_t v_kind_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_){
_start:
{
lean_object* v___x_446_; 
v___x_446_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0_spec__0___redArg(v_name_436_, v_bi_437_, v_type_438_, v_k_439_, v_kind_440_, v___y_441_, v___y_442_, v___y_443_, v___y_444_);
return v___x_446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0_spec__0___boxed(lean_object* v_00_u03b1_447_, lean_object* v_name_448_, lean_object* v_bi_449_, lean_object* v_type_450_, lean_object* v_k_451_, lean_object* v_kind_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_){
_start:
{
uint8_t v_bi_boxed_458_; uint8_t v_kind_boxed_459_; lean_object* v_res_460_; 
v_bi_boxed_458_ = lean_unbox(v_bi_449_);
v_kind_boxed_459_ = lean_unbox(v_kind_452_);
v_res_460_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0_spec__0(v_00_u03b1_447_, v_name_448_, v_bi_boxed_458_, v_type_450_, v_k_451_, v_kind_boxed_459_, v___y_453_, v___y_454_, v___y_455_, v___y_456_);
lean_dec(v___y_456_);
lean_dec_ref(v___y_455_);
lean_dec(v___y_454_);
lean_dec_ref(v___y_453_);
return v_res_460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0(lean_object* v_00_u03b1_461_, lean_object* v_name_462_, lean_object* v_type_463_, lean_object* v_k_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_){
_start:
{
lean_object* v___x_470_; 
v___x_470_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0___redArg(v_name_462_, v_type_463_, v_k_464_, v___y_465_, v___y_466_, v___y_467_, v___y_468_);
return v___x_470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0___boxed(lean_object* v_00_u03b1_471_, lean_object* v_name_472_, lean_object* v_type_473_, lean_object* v_k_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_){
_start:
{
lean_object* v_res_480_; 
v_res_480_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0(v_00_u03b1_471_, v_name_472_, v_type_473_, v_k_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_);
lean_dec(v___y_478_);
lean_dec_ref(v___y_477_);
lean_dec(v___y_476_);
lean_dec_ref(v___y_475_);
return v_res_480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewEqs___redArg(lean_object* v_targets_483_, lean_object* v_targetsNew_484_, lean_object* v_k_485_, lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_){
_start:
{
lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_491_ = lean_unsigned_to_nat(0u);
v___x_492_ = ((lean_object*)(l_Lean_Meta_withNewEqs___redArg___closed__0));
v___x_493_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___redArg(v_targets_483_, v_targetsNew_484_, v_k_485_, v___x_491_, v___x_492_, v___x_492_, v_a_486_, v_a_487_, v_a_488_, v_a_489_);
return v___x_493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewEqs___redArg___boxed(lean_object* v_targets_494_, lean_object* v_targetsNew_495_, lean_object* v_k_496_, lean_object* v_a_497_, lean_object* v_a_498_, lean_object* v_a_499_, lean_object* v_a_500_, lean_object* v_a_501_){
_start:
{
lean_object* v_res_502_; 
v_res_502_ = l_Lean_Meta_withNewEqs___redArg(v_targets_494_, v_targetsNew_495_, v_k_496_, v_a_497_, v_a_498_, v_a_499_, v_a_500_);
lean_dec(v_a_500_);
lean_dec_ref(v_a_499_);
lean_dec(v_a_498_);
lean_dec_ref(v_a_497_);
return v_res_502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewEqs(lean_object* v_00_u03b1_503_, lean_object* v_targets_504_, lean_object* v_targetsNew_505_, lean_object* v_k_506_, lean_object* v_a_507_, lean_object* v_a_508_, lean_object* v_a_509_, lean_object* v_a_510_){
_start:
{
lean_object* v___x_512_; 
v___x_512_ = l_Lean_Meta_withNewEqs___redArg(v_targets_504_, v_targetsNew_505_, v_k_506_, v_a_507_, v_a_508_, v_a_509_, v_a_510_);
return v___x_512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewEqs___boxed(lean_object* v_00_u03b1_513_, lean_object* v_targets_514_, lean_object* v_targetsNew_515_, lean_object* v_k_516_, lean_object* v_a_517_, lean_object* v_a_518_, lean_object* v_a_519_, lean_object* v_a_520_, lean_object* v_a_521_){
_start:
{
lean_object* v_res_522_; 
v_res_522_ = l_Lean_Meta_withNewEqs(v_00_u03b1_513_, v_targets_514_, v_targetsNew_515_, v_k_516_, v_a_517_, v_a_518_, v_a_519_, v_a_520_);
lean_dec(v_a_520_);
lean_dec_ref(v_a_519_);
lean_dec(v_a_518_);
lean_dec_ref(v_a_517_);
return v_res_522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_generalizeTargetsEq_spec__0___redArg___lam__0(lean_object* v_k_523_, lean_object* v_b_524_, lean_object* v_c_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_){
_start:
{
lean_object* v___x_531_; 
lean_inc(v___y_529_);
lean_inc_ref(v___y_528_);
lean_inc(v___y_527_);
lean_inc_ref(v___y_526_);
v___x_531_ = lean_apply_7(v_k_523_, v_b_524_, v_c_525_, v___y_526_, v___y_527_, v___y_528_, v___y_529_, lean_box(0));
return v___x_531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_generalizeTargetsEq_spec__0___redArg___lam__0___boxed(lean_object* v_k_532_, lean_object* v_b_533_, lean_object* v_c_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_){
_start:
{
lean_object* v_res_540_; 
v_res_540_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_generalizeTargetsEq_spec__0___redArg___lam__0(v_k_532_, v_b_533_, v_c_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_);
lean_dec(v___y_538_);
lean_dec_ref(v___y_537_);
lean_dec(v___y_536_);
lean_dec_ref(v___y_535_);
return v_res_540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_generalizeTargetsEq_spec__0___redArg(lean_object* v_type_541_, lean_object* v_k_542_, uint8_t v_cleanupAnnotations_543_, uint8_t v_whnfType_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_){
_start:
{
lean_object* v___f_550_; lean_object* v___x_551_; 
v___f_550_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_generalizeTargetsEq_spec__0___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_550_, 0, v_k_542_);
v___x_551_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_541_, v___f_550_, v_cleanupAnnotations_543_, v_whnfType_544_, v___y_545_, v___y_546_, v___y_547_, v___y_548_);
if (lean_obj_tag(v___x_551_) == 0)
{
lean_object* v_a_552_; lean_object* v___x_554_; uint8_t v_isShared_555_; uint8_t v_isSharedCheck_559_; 
v_a_552_ = lean_ctor_get(v___x_551_, 0);
v_isSharedCheck_559_ = !lean_is_exclusive(v___x_551_);
if (v_isSharedCheck_559_ == 0)
{
v___x_554_ = v___x_551_;
v_isShared_555_ = v_isSharedCheck_559_;
goto v_resetjp_553_;
}
else
{
lean_inc(v_a_552_);
lean_dec(v___x_551_);
v___x_554_ = lean_box(0);
v_isShared_555_ = v_isSharedCheck_559_;
goto v_resetjp_553_;
}
v_resetjp_553_:
{
lean_object* v___x_557_; 
if (v_isShared_555_ == 0)
{
v___x_557_ = v___x_554_;
goto v_reusejp_556_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v_a_552_);
v___x_557_ = v_reuseFailAlloc_558_;
goto v_reusejp_556_;
}
v_reusejp_556_:
{
return v___x_557_;
}
}
}
else
{
lean_object* v_a_560_; lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_567_; 
v_a_560_ = lean_ctor_get(v___x_551_, 0);
v_isSharedCheck_567_ = !lean_is_exclusive(v___x_551_);
if (v_isSharedCheck_567_ == 0)
{
v___x_562_ = v___x_551_;
v_isShared_563_ = v_isSharedCheck_567_;
goto v_resetjp_561_;
}
else
{
lean_inc(v_a_560_);
lean_dec(v___x_551_);
v___x_562_ = lean_box(0);
v_isShared_563_ = v_isSharedCheck_567_;
goto v_resetjp_561_;
}
v_resetjp_561_:
{
lean_object* v___x_565_; 
if (v_isShared_563_ == 0)
{
v___x_565_ = v___x_562_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v_a_560_);
v___x_565_ = v_reuseFailAlloc_566_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
return v___x_565_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_generalizeTargetsEq_spec__0___redArg___boxed(lean_object* v_type_568_, lean_object* v_k_569_, lean_object* v_cleanupAnnotations_570_, lean_object* v_whnfType_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_577_; uint8_t v_whnfType_boxed_578_; lean_object* v_res_579_; 
v_cleanupAnnotations_boxed_577_ = lean_unbox(v_cleanupAnnotations_570_);
v_whnfType_boxed_578_ = lean_unbox(v_whnfType_571_);
v_res_579_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_generalizeTargetsEq_spec__0___redArg(v_type_568_, v_k_569_, v_cleanupAnnotations_boxed_577_, v_whnfType_boxed_578_, v___y_572_, v___y_573_, v___y_574_, v___y_575_);
lean_dec(v___y_575_);
lean_dec_ref(v___y_574_);
lean_dec(v___y_573_);
lean_dec_ref(v___y_572_);
return v_res_579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_generalizeTargetsEq_spec__0(lean_object* v_00_u03b1_580_, lean_object* v_type_581_, lean_object* v_k_582_, uint8_t v_cleanupAnnotations_583_, uint8_t v_whnfType_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_){
_start:
{
lean_object* v___x_590_; 
v___x_590_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_generalizeTargetsEq_spec__0___redArg(v_type_581_, v_k_582_, v_cleanupAnnotations_583_, v_whnfType_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_);
return v___x_590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_generalizeTargetsEq_spec__0___boxed(lean_object* v_00_u03b1_591_, lean_object* v_type_592_, lean_object* v_k_593_, lean_object* v_cleanupAnnotations_594_, lean_object* v_whnfType_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_601_; uint8_t v_whnfType_boxed_602_; lean_object* v_res_603_; 
v_cleanupAnnotations_boxed_601_ = lean_unbox(v_cleanupAnnotations_594_);
v_whnfType_boxed_602_ = lean_unbox(v_whnfType_595_);
v_res_603_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_generalizeTargetsEq_spec__0(v_00_u03b1_591_, v_type_592_, v_k_593_, v_cleanupAnnotations_boxed_601_, v_whnfType_boxed_602_, v___y_596_, v___y_597_, v___y_598_, v___y_599_);
lean_dec(v___y_599_);
lean_dec_ref(v___y_598_);
lean_dec(v___y_597_);
lean_dec_ref(v___y_596_);
return v_res_603_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2___redArg(lean_object* v_mvarId_604_, lean_object* v_x_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_){
_start:
{
lean_object* v___x_611_; 
v___x_611_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_604_, v_x_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_);
if (lean_obj_tag(v___x_611_) == 0)
{
lean_object* v_a_612_; lean_object* v___x_614_; uint8_t v_isShared_615_; uint8_t v_isSharedCheck_619_; 
v_a_612_ = lean_ctor_get(v___x_611_, 0);
v_isSharedCheck_619_ = !lean_is_exclusive(v___x_611_);
if (v_isSharedCheck_619_ == 0)
{
v___x_614_ = v___x_611_;
v_isShared_615_ = v_isSharedCheck_619_;
goto v_resetjp_613_;
}
else
{
lean_inc(v_a_612_);
lean_dec(v___x_611_);
v___x_614_ = lean_box(0);
v_isShared_615_ = v_isSharedCheck_619_;
goto v_resetjp_613_;
}
v_resetjp_613_:
{
lean_object* v___x_617_; 
if (v_isShared_615_ == 0)
{
v___x_617_ = v___x_614_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v_a_612_);
v___x_617_ = v_reuseFailAlloc_618_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
return v___x_617_;
}
}
}
else
{
lean_object* v_a_620_; lean_object* v___x_622_; uint8_t v_isShared_623_; uint8_t v_isSharedCheck_627_; 
v_a_620_ = lean_ctor_get(v___x_611_, 0);
v_isSharedCheck_627_ = !lean_is_exclusive(v___x_611_);
if (v_isSharedCheck_627_ == 0)
{
v___x_622_ = v___x_611_;
v_isShared_623_ = v_isSharedCheck_627_;
goto v_resetjp_621_;
}
else
{
lean_inc(v_a_620_);
lean_dec(v___x_611_);
v___x_622_ = lean_box(0);
v_isShared_623_ = v_isSharedCheck_627_;
goto v_resetjp_621_;
}
v_resetjp_621_:
{
lean_object* v___x_625_; 
if (v_isShared_623_ == 0)
{
v___x_625_ = v___x_622_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v_a_620_);
v___x_625_ = v_reuseFailAlloc_626_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
return v___x_625_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2___redArg___boxed(lean_object* v_mvarId_628_, lean_object* v_x_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_){
_start:
{
lean_object* v_res_635_; 
v_res_635_ = l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2___redArg(v_mvarId_628_, v_x_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_);
lean_dec(v___y_633_);
lean_dec_ref(v___y_632_);
lean_dec(v___y_631_);
lean_dec_ref(v___y_630_);
return v_res_635_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2(lean_object* v_00_u03b1_636_, lean_object* v_mvarId_637_, lean_object* v_x_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_){
_start:
{
lean_object* v___x_644_; 
v___x_644_ = l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2___redArg(v_mvarId_637_, v_x_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_);
return v___x_644_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2___boxed(lean_object* v_00_u03b1_645_, lean_object* v_mvarId_646_, lean_object* v_x_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_){
_start:
{
lean_object* v_res_653_; 
v_res_653_ = l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2(v_00_u03b1_645_, v_mvarId_646_, v_x_647_, v___y_648_, v___y_649_, v___y_650_, v___y_651_);
lean_dec(v___y_651_);
lean_dec_ref(v___y_650_);
lean_dec(v___y_649_);
lean_dec_ref(v___y_648_);
return v_res_653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeTargetsEq___lam__0(lean_object* v_mvarId_654_, lean_object* v___x_655_, lean_object* v_eqs_656_, lean_object* v_eqRefls_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_){
_start:
{
lean_object* v___x_663_; 
v___x_663_ = l_Lean_MVarId_getType(v_mvarId_654_, v___y_658_, v___y_659_, v___y_660_, v___y_661_);
if (lean_obj_tag(v___x_663_) == 0)
{
lean_object* v_a_664_; uint8_t v___x_665_; uint8_t v___x_666_; uint8_t v___x_667_; lean_object* v___x_668_; 
v_a_664_ = lean_ctor_get(v___x_663_, 0);
lean_inc(v_a_664_);
lean_dec_ref_known(v___x_663_, 1);
v___x_665_ = 0;
v___x_666_ = 1;
v___x_667_ = 1;
v___x_668_ = l_Lean_Meta_mkForallFVars(v_eqs_656_, v_a_664_, v___x_665_, v___x_666_, v___x_666_, v___x_667_, v___y_658_, v___y_659_, v___y_660_, v___y_661_);
if (lean_obj_tag(v___x_668_) == 0)
{
lean_object* v_a_669_; lean_object* v___x_670_; 
v_a_669_ = lean_ctor_get(v___x_668_, 0);
lean_inc(v_a_669_);
lean_dec_ref_known(v___x_668_, 1);
v___x_670_ = l_Lean_Meta_mkForallFVars(v___x_655_, v_a_669_, v___x_665_, v___x_666_, v___x_666_, v___x_667_, v___y_658_, v___y_659_, v___y_660_, v___y_661_);
if (lean_obj_tag(v___x_670_) == 0)
{
lean_object* v_a_671_; lean_object* v___x_673_; uint8_t v_isShared_674_; uint8_t v_isSharedCheck_679_; 
v_a_671_ = lean_ctor_get(v___x_670_, 0);
v_isSharedCheck_679_ = !lean_is_exclusive(v___x_670_);
if (v_isSharedCheck_679_ == 0)
{
v___x_673_ = v___x_670_;
v_isShared_674_ = v_isSharedCheck_679_;
goto v_resetjp_672_;
}
else
{
lean_inc(v_a_671_);
lean_dec(v___x_670_);
v___x_673_ = lean_box(0);
v_isShared_674_ = v_isSharedCheck_679_;
goto v_resetjp_672_;
}
v_resetjp_672_:
{
lean_object* v___x_675_; lean_object* v___x_677_; 
v___x_675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_675_, 0, v_a_671_);
lean_ctor_set(v___x_675_, 1, v_eqRefls_657_);
if (v_isShared_674_ == 0)
{
lean_ctor_set(v___x_673_, 0, v___x_675_);
v___x_677_ = v___x_673_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v___x_675_);
v___x_677_ = v_reuseFailAlloc_678_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
return v___x_677_;
}
}
}
else
{
lean_object* v_a_680_; lean_object* v___x_682_; uint8_t v_isShared_683_; uint8_t v_isSharedCheck_687_; 
lean_dec_ref(v_eqRefls_657_);
v_a_680_ = lean_ctor_get(v___x_670_, 0);
v_isSharedCheck_687_ = !lean_is_exclusive(v___x_670_);
if (v_isSharedCheck_687_ == 0)
{
v___x_682_ = v___x_670_;
v_isShared_683_ = v_isSharedCheck_687_;
goto v_resetjp_681_;
}
else
{
lean_inc(v_a_680_);
lean_dec(v___x_670_);
v___x_682_ = lean_box(0);
v_isShared_683_ = v_isSharedCheck_687_;
goto v_resetjp_681_;
}
v_resetjp_681_:
{
lean_object* v___x_685_; 
if (v_isShared_683_ == 0)
{
v___x_685_ = v___x_682_;
goto v_reusejp_684_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v_a_680_);
v___x_685_ = v_reuseFailAlloc_686_;
goto v_reusejp_684_;
}
v_reusejp_684_:
{
return v___x_685_;
}
}
}
}
else
{
lean_object* v_a_688_; lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_695_; 
lean_dec_ref(v_eqRefls_657_);
v_a_688_ = lean_ctor_get(v___x_668_, 0);
v_isSharedCheck_695_ = !lean_is_exclusive(v___x_668_);
if (v_isSharedCheck_695_ == 0)
{
v___x_690_ = v___x_668_;
v_isShared_691_ = v_isSharedCheck_695_;
goto v_resetjp_689_;
}
else
{
lean_inc(v_a_688_);
lean_dec(v___x_668_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_695_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
lean_object* v___x_693_; 
if (v_isShared_691_ == 0)
{
v___x_693_ = v___x_690_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v_a_688_);
v___x_693_ = v_reuseFailAlloc_694_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
return v___x_693_;
}
}
}
}
else
{
lean_object* v_a_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_703_; 
lean_dec_ref(v_eqRefls_657_);
v_a_696_ = lean_ctor_get(v___x_663_, 0);
v_isSharedCheck_703_ = !lean_is_exclusive(v___x_663_);
if (v_isSharedCheck_703_ == 0)
{
v___x_698_ = v___x_663_;
v_isShared_699_ = v_isSharedCheck_703_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_a_696_);
lean_dec(v___x_663_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_703_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v___x_701_; 
if (v_isShared_699_ == 0)
{
v___x_701_ = v___x_698_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v_a_696_);
v___x_701_ = v_reuseFailAlloc_702_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
return v___x_701_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeTargetsEq___lam__0___boxed(lean_object* v_mvarId_704_, lean_object* v___x_705_, lean_object* v_eqs_706_, lean_object* v_eqRefls_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_){
_start:
{
lean_object* v_res_713_; 
v_res_713_ = l_Lean_Meta_generalizeTargetsEq___lam__0(v_mvarId_704_, v___x_705_, v_eqs_706_, v_eqRefls_707_, v___y_708_, v___y_709_, v___y_710_, v___y_711_);
lean_dec(v___y_711_);
lean_dec_ref(v___y_710_);
lean_dec(v___y_709_);
lean_dec_ref(v___y_708_);
lean_dec_ref(v_eqs_706_);
lean_dec_ref(v___x_705_);
return v_res_713_;
}
}
static lean_object* _init_l_Lean_Meta_generalizeTargetsEq___lam__1___closed__1(void){
_start:
{
lean_object* v___x_715_; lean_object* v___x_716_; 
v___x_715_ = ((lean_object*)(l_Lean_Meta_generalizeTargetsEq___lam__1___closed__0));
v___x_716_ = l_Lean_stringToMessageData(v___x_715_);
return v___x_716_;
}
}
static lean_object* _init_l_Lean_Meta_generalizeTargetsEq___lam__1___closed__3(void){
_start:
{
lean_object* v___x_718_; lean_object* v___x_719_; 
v___x_718_ = ((lean_object*)(l_Lean_Meta_generalizeTargetsEq___lam__1___closed__2));
v___x_719_ = l_Lean_stringToMessageData(v___x_718_);
return v___x_719_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeTargetsEq___lam__1(lean_object* v_targets_720_, lean_object* v_mvarId_721_, lean_object* v_targetsNew_722_, lean_object* v_x_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_){
_start:
{
lean_object* v___x_736_; lean_object* v___x_737_; uint8_t v___x_738_; 
v___x_736_ = lean_array_get_size(v_targets_720_);
v___x_737_ = lean_array_get_size(v_targetsNew_722_);
v___x_738_ = lean_nat_dec_le(v___x_736_, v___x_737_);
if (v___x_738_ == 0)
{
lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v_a_751_; lean_object* v___x_753_; uint8_t v_isShared_754_; uint8_t v_isSharedCheck_758_; 
lean_dec_ref(v_targetsNew_722_);
lean_dec(v_mvarId_721_);
lean_dec_ref(v_targets_720_);
v___x_739_ = lean_obj_once(&l_Lean_Meta_generalizeTargetsEq___lam__1___closed__1, &l_Lean_Meta_generalizeTargetsEq___lam__1___closed__1_once, _init_l_Lean_Meta_generalizeTargetsEq___lam__1___closed__1);
v___x_740_ = l_Nat_reprFast(v___x_736_);
v___x_741_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_741_, 0, v___x_740_);
v___x_742_ = l_Lean_MessageData_ofFormat(v___x_741_);
v___x_743_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_743_, 0, v___x_739_);
lean_ctor_set(v___x_743_, 1, v___x_742_);
v___x_744_ = lean_obj_once(&l_Lean_Meta_generalizeTargetsEq___lam__1___closed__3, &l_Lean_Meta_generalizeTargetsEq___lam__1___closed__3_once, _init_l_Lean_Meta_generalizeTargetsEq___lam__1___closed__3);
v___x_745_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_745_, 0, v___x_743_);
lean_ctor_set(v___x_745_, 1, v___x_744_);
v___x_746_ = l_Nat_reprFast(v___x_737_);
v___x_747_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_747_, 0, v___x_746_);
v___x_748_ = l_Lean_MessageData_ofFormat(v___x_747_);
v___x_749_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_749_, 0, v___x_745_);
lean_ctor_set(v___x_749_, 1, v___x_748_);
v___x_750_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected_spec__0___redArg(v___x_749_, v___y_724_, v___y_725_, v___y_726_, v___y_727_);
v_a_751_ = lean_ctor_get(v___x_750_, 0);
v_isSharedCheck_758_ = !lean_is_exclusive(v___x_750_);
if (v_isSharedCheck_758_ == 0)
{
v___x_753_ = v___x_750_;
v_isShared_754_ = v_isSharedCheck_758_;
goto v_resetjp_752_;
}
else
{
lean_inc(v_a_751_);
lean_dec(v___x_750_);
v___x_753_ = lean_box(0);
v_isShared_754_ = v_isSharedCheck_758_;
goto v_resetjp_752_;
}
v_resetjp_752_:
{
lean_object* v___x_756_; 
if (v_isShared_754_ == 0)
{
v___x_756_ = v___x_753_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v_a_751_);
v___x_756_ = v_reuseFailAlloc_757_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
return v___x_756_;
}
}
}
else
{
goto v___jp_729_;
}
v___jp_729_:
{
lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___f_734_; lean_object* v___x_735_; 
v___x_730_ = lean_array_get_size(v_targets_720_);
v___x_731_ = lean_unsigned_to_nat(0u);
v___x_732_ = l_Array_toSubarray___redArg(v_targetsNew_722_, v___x_731_, v___x_730_);
v___x_733_ = l_Subarray_copy___redArg(v___x_732_);
lean_inc_ref(v___x_733_);
v___f_734_ = lean_alloc_closure((void*)(l_Lean_Meta_generalizeTargetsEq___lam__0___boxed), 9, 2);
lean_closure_set(v___f_734_, 0, v_mvarId_721_);
lean_closure_set(v___f_734_, 1, v___x_733_);
v___x_735_ = l_Lean_Meta_withNewEqs___redArg(v_targets_720_, v___x_733_, v___f_734_, v___y_724_, v___y_725_, v___y_726_, v___y_727_);
return v___x_735_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeTargetsEq___lam__1___boxed(lean_object* v_targets_759_, lean_object* v_mvarId_760_, lean_object* v_targetsNew_761_, lean_object* v_x_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_){
_start:
{
lean_object* v_res_768_; 
v_res_768_ = l_Lean_Meta_generalizeTargetsEq___lam__1(v_targets_759_, v_mvarId_760_, v_targetsNew_761_, v_x_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_);
lean_dec(v___y_766_);
lean_dec_ref(v___y_765_);
lean_dec(v___y_764_);
lean_dec_ref(v___y_763_);
lean_dec_ref(v_x_762_);
return v_res_768_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__4_spec__5___redArg(lean_object* v_x_769_, lean_object* v_x_770_, lean_object* v_x_771_, lean_object* v_x_772_){
_start:
{
lean_object* v_ks_773_; lean_object* v_vs_774_; lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_798_; 
v_ks_773_ = lean_ctor_get(v_x_769_, 0);
v_vs_774_ = lean_ctor_get(v_x_769_, 1);
v_isSharedCheck_798_ = !lean_is_exclusive(v_x_769_);
if (v_isSharedCheck_798_ == 0)
{
v___x_776_ = v_x_769_;
v_isShared_777_ = v_isSharedCheck_798_;
goto v_resetjp_775_;
}
else
{
lean_inc(v_vs_774_);
lean_inc(v_ks_773_);
lean_dec(v_x_769_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_798_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
lean_object* v___x_778_; uint8_t v___x_779_; 
v___x_778_ = lean_array_get_size(v_ks_773_);
v___x_779_ = lean_nat_dec_lt(v_x_770_, v___x_778_);
if (v___x_779_ == 0)
{
lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_783_; 
lean_dec(v_x_770_);
v___x_780_ = lean_array_push(v_ks_773_, v_x_771_);
v___x_781_ = lean_array_push(v_vs_774_, v_x_772_);
if (v_isShared_777_ == 0)
{
lean_ctor_set(v___x_776_, 1, v___x_781_);
lean_ctor_set(v___x_776_, 0, v___x_780_);
v___x_783_ = v___x_776_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v___x_780_);
lean_ctor_set(v_reuseFailAlloc_784_, 1, v___x_781_);
v___x_783_ = v_reuseFailAlloc_784_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
return v___x_783_;
}
}
else
{
lean_object* v_k_x27_785_; uint8_t v___x_786_; 
v_k_x27_785_ = lean_array_fget_borrowed(v_ks_773_, v_x_770_);
v___x_786_ = l_Lean_instBEqMVarId_beq(v_x_771_, v_k_x27_785_);
if (v___x_786_ == 0)
{
lean_object* v___x_788_; 
if (v_isShared_777_ == 0)
{
v___x_788_ = v___x_776_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v_ks_773_);
lean_ctor_set(v_reuseFailAlloc_792_, 1, v_vs_774_);
v___x_788_ = v_reuseFailAlloc_792_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
lean_object* v___x_789_; lean_object* v___x_790_; 
v___x_789_ = lean_unsigned_to_nat(1u);
v___x_790_ = lean_nat_add(v_x_770_, v___x_789_);
lean_dec(v_x_770_);
v_x_769_ = v___x_788_;
v_x_770_ = v___x_790_;
goto _start;
}
}
else
{
lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_796_; 
v___x_793_ = lean_array_fset(v_ks_773_, v_x_770_, v_x_771_);
v___x_794_ = lean_array_fset(v_vs_774_, v_x_770_, v_x_772_);
lean_dec(v_x_770_);
if (v_isShared_777_ == 0)
{
lean_ctor_set(v___x_776_, 1, v___x_794_);
lean_ctor_set(v___x_776_, 0, v___x_793_);
v___x_796_ = v___x_776_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v___x_793_);
lean_ctor_set(v_reuseFailAlloc_797_, 1, v___x_794_);
v___x_796_ = v_reuseFailAlloc_797_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
return v___x_796_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__4___redArg(lean_object* v_n_799_, lean_object* v_k_800_, lean_object* v_v_801_){
_start:
{
lean_object* v___x_802_; lean_object* v___x_803_; 
v___x_802_ = lean_unsigned_to_nat(0u);
v___x_803_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__4_spec__5___redArg(v_n_799_, v___x_802_, v_k_800_, v_v_801_);
return v___x_803_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_804_; 
v___x_804_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_804_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg(lean_object* v_x_805_, size_t v_x_806_, size_t v_x_807_, lean_object* v_x_808_, lean_object* v_x_809_){
_start:
{
if (lean_obj_tag(v_x_805_) == 0)
{
lean_object* v_es_810_; size_t v___x_811_; size_t v___x_812_; lean_object* v_j_813_; lean_object* v___x_814_; uint8_t v___x_815_; 
v_es_810_ = lean_ctor_get(v_x_805_, 0);
v___x_811_ = ((size_t)31ULL);
v___x_812_ = lean_usize_land(v_x_806_, v___x_811_);
v_j_813_ = lean_usize_to_nat(v___x_812_);
v___x_814_ = lean_array_get_size(v_es_810_);
v___x_815_ = lean_nat_dec_lt(v_j_813_, v___x_814_);
if (v___x_815_ == 0)
{
lean_dec(v_j_813_);
lean_dec(v_x_809_);
lean_dec(v_x_808_);
return v_x_805_;
}
else
{
lean_object* v___x_817_; uint8_t v_isShared_818_; uint8_t v_isSharedCheck_854_; 
lean_inc_ref(v_es_810_);
v_isSharedCheck_854_ = !lean_is_exclusive(v_x_805_);
if (v_isSharedCheck_854_ == 0)
{
lean_object* v_unused_855_; 
v_unused_855_ = lean_ctor_get(v_x_805_, 0);
lean_dec(v_unused_855_);
v___x_817_ = v_x_805_;
v_isShared_818_ = v_isSharedCheck_854_;
goto v_resetjp_816_;
}
else
{
lean_dec(v_x_805_);
v___x_817_ = lean_box(0);
v_isShared_818_ = v_isSharedCheck_854_;
goto v_resetjp_816_;
}
v_resetjp_816_:
{
lean_object* v_v_819_; lean_object* v___x_820_; lean_object* v_xs_x27_821_; lean_object* v___y_823_; 
v_v_819_ = lean_array_fget(v_es_810_, v_j_813_);
v___x_820_ = lean_box(0);
v_xs_x27_821_ = lean_array_fset(v_es_810_, v_j_813_, v___x_820_);
switch(lean_obj_tag(v_v_819_))
{
case 0:
{
lean_object* v_key_828_; lean_object* v_val_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_839_; 
v_key_828_ = lean_ctor_get(v_v_819_, 0);
v_val_829_ = lean_ctor_get(v_v_819_, 1);
v_isSharedCheck_839_ = !lean_is_exclusive(v_v_819_);
if (v_isSharedCheck_839_ == 0)
{
v___x_831_ = v_v_819_;
v_isShared_832_ = v_isSharedCheck_839_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_val_829_);
lean_inc(v_key_828_);
lean_dec(v_v_819_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_839_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
uint8_t v___x_833_; 
v___x_833_ = l_Lean_instBEqMVarId_beq(v_x_808_, v_key_828_);
if (v___x_833_ == 0)
{
lean_object* v___x_834_; lean_object* v___x_835_; 
lean_del_object(v___x_831_);
v___x_834_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_828_, v_val_829_, v_x_808_, v_x_809_);
v___x_835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_835_, 0, v___x_834_);
v___y_823_ = v___x_835_;
goto v___jp_822_;
}
else
{
lean_object* v___x_837_; 
lean_dec(v_val_829_);
lean_dec(v_key_828_);
if (v_isShared_832_ == 0)
{
lean_ctor_set(v___x_831_, 1, v_x_809_);
lean_ctor_set(v___x_831_, 0, v_x_808_);
v___x_837_ = v___x_831_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v_x_808_);
lean_ctor_set(v_reuseFailAlloc_838_, 1, v_x_809_);
v___x_837_ = v_reuseFailAlloc_838_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
v___y_823_ = v___x_837_;
goto v___jp_822_;
}
}
}
}
case 1:
{
lean_object* v_node_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_852_; 
v_node_840_ = lean_ctor_get(v_v_819_, 0);
v_isSharedCheck_852_ = !lean_is_exclusive(v_v_819_);
if (v_isSharedCheck_852_ == 0)
{
v___x_842_ = v_v_819_;
v_isShared_843_ = v_isSharedCheck_852_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_node_840_);
lean_dec(v_v_819_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_852_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
size_t v___x_844_; size_t v___x_845_; size_t v___x_846_; size_t v___x_847_; lean_object* v___x_848_; lean_object* v___x_850_; 
v___x_844_ = ((size_t)5ULL);
v___x_845_ = lean_usize_shift_right(v_x_806_, v___x_844_);
v___x_846_ = ((size_t)1ULL);
v___x_847_ = lean_usize_add(v_x_807_, v___x_846_);
v___x_848_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg(v_node_840_, v___x_845_, v___x_847_, v_x_808_, v_x_809_);
if (v_isShared_843_ == 0)
{
lean_ctor_set(v___x_842_, 0, v___x_848_);
v___x_850_ = v___x_842_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v___x_848_);
v___x_850_ = v_reuseFailAlloc_851_;
goto v_reusejp_849_;
}
v_reusejp_849_:
{
v___y_823_ = v___x_850_;
goto v___jp_822_;
}
}
}
default: 
{
lean_object* v___x_853_; 
v___x_853_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_853_, 0, v_x_808_);
lean_ctor_set(v___x_853_, 1, v_x_809_);
v___y_823_ = v___x_853_;
goto v___jp_822_;
}
}
v___jp_822_:
{
lean_object* v___x_824_; lean_object* v___x_826_; 
v___x_824_ = lean_array_fset(v_xs_x27_821_, v_j_813_, v___y_823_);
lean_dec(v_j_813_);
if (v_isShared_818_ == 0)
{
lean_ctor_set(v___x_817_, 0, v___x_824_);
v___x_826_ = v___x_817_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v___x_824_);
v___x_826_ = v_reuseFailAlloc_827_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
return v___x_826_;
}
}
}
}
}
else
{
lean_object* v_ks_856_; lean_object* v_vs_857_; lean_object* v___x_859_; uint8_t v_isShared_860_; uint8_t v_isSharedCheck_875_; 
v_ks_856_ = lean_ctor_get(v_x_805_, 0);
v_vs_857_ = lean_ctor_get(v_x_805_, 1);
v_isSharedCheck_875_ = !lean_is_exclusive(v_x_805_);
if (v_isSharedCheck_875_ == 0)
{
v___x_859_ = v_x_805_;
v_isShared_860_ = v_isSharedCheck_875_;
goto v_resetjp_858_;
}
else
{
lean_inc(v_vs_857_);
lean_inc(v_ks_856_);
lean_dec(v_x_805_);
v___x_859_ = lean_box(0);
v_isShared_860_ = v_isSharedCheck_875_;
goto v_resetjp_858_;
}
v_resetjp_858_:
{
lean_object* v___x_862_; 
if (v_isShared_860_ == 0)
{
v___x_862_ = v___x_859_;
goto v_reusejp_861_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v_ks_856_);
lean_ctor_set(v_reuseFailAlloc_874_, 1, v_vs_857_);
v___x_862_ = v_reuseFailAlloc_874_;
goto v_reusejp_861_;
}
v_reusejp_861_:
{
lean_object* v_newNode_863_; size_t v___x_864_; uint8_t v___x_865_; 
v_newNode_863_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__4___redArg(v___x_862_, v_x_808_, v_x_809_);
v___x_864_ = ((size_t)7ULL);
v___x_865_ = lean_usize_dec_le(v___x_864_, v_x_807_);
if (v___x_865_ == 0)
{
lean_object* v___x_866_; lean_object* v___x_867_; uint8_t v___x_868_; 
v___x_866_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_863_);
v___x_867_ = lean_unsigned_to_nat(4u);
v___x_868_ = lean_nat_dec_lt(v___x_866_, v___x_867_);
lean_dec(v___x_866_);
if (v___x_868_ == 0)
{
lean_object* v_ks_869_; lean_object* v_vs_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; 
v_ks_869_ = lean_ctor_get(v_newNode_863_, 0);
lean_inc_ref(v_ks_869_);
v_vs_870_ = lean_ctor_get(v_newNode_863_, 1);
lean_inc_ref(v_vs_870_);
lean_dec_ref(v_newNode_863_);
v___x_871_ = lean_unsigned_to_nat(0u);
v___x_872_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg___closed__0);
v___x_873_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__5___redArg(v_x_807_, v_ks_869_, v_vs_870_, v___x_871_, v___x_872_);
lean_dec_ref(v_vs_870_);
lean_dec_ref(v_ks_869_);
return v___x_873_;
}
else
{
return v_newNode_863_;
}
}
else
{
return v_newNode_863_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__5___redArg(size_t v_depth_876_, lean_object* v_keys_877_, lean_object* v_vals_878_, lean_object* v_i_879_, lean_object* v_entries_880_){
_start:
{
lean_object* v___x_881_; uint8_t v___x_882_; 
v___x_881_ = lean_array_get_size(v_keys_877_);
v___x_882_ = lean_nat_dec_lt(v_i_879_, v___x_881_);
if (v___x_882_ == 0)
{
lean_dec(v_i_879_);
return v_entries_880_;
}
else
{
lean_object* v_k_883_; lean_object* v_v_884_; uint64_t v___x_885_; size_t v_h_886_; size_t v___x_887_; lean_object* v___x_888_; size_t v___x_889_; size_t v___x_890_; size_t v___x_891_; size_t v_h_892_; lean_object* v___x_893_; lean_object* v___x_894_; 
v_k_883_ = lean_array_fget_borrowed(v_keys_877_, v_i_879_);
v_v_884_ = lean_array_fget_borrowed(v_vals_878_, v_i_879_);
v___x_885_ = l_Lean_instHashableMVarId_hash(v_k_883_);
v_h_886_ = lean_uint64_to_usize(v___x_885_);
v___x_887_ = ((size_t)5ULL);
v___x_888_ = lean_unsigned_to_nat(1u);
v___x_889_ = ((size_t)1ULL);
v___x_890_ = lean_usize_sub(v_depth_876_, v___x_889_);
v___x_891_ = lean_usize_mul(v___x_887_, v___x_890_);
v_h_892_ = lean_usize_shift_right(v_h_886_, v___x_891_);
v___x_893_ = lean_nat_add(v_i_879_, v___x_888_);
lean_dec(v_i_879_);
lean_inc(v_v_884_);
lean_inc(v_k_883_);
v___x_894_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg(v_entries_880_, v_h_892_, v_depth_876_, v_k_883_, v_v_884_);
v_i_879_ = v___x_893_;
v_entries_880_ = v___x_894_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__5___redArg___boxed(lean_object* v_depth_896_, lean_object* v_keys_897_, lean_object* v_vals_898_, lean_object* v_i_899_, lean_object* v_entries_900_){
_start:
{
size_t v_depth_boxed_901_; lean_object* v_res_902_; 
v_depth_boxed_901_ = lean_unbox_usize(v_depth_896_);
lean_dec(v_depth_896_);
v_res_902_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__5___redArg(v_depth_boxed_901_, v_keys_897_, v_vals_898_, v_i_899_, v_entries_900_);
lean_dec_ref(v_vals_898_);
lean_dec_ref(v_keys_897_);
return v_res_902_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_x_903_, lean_object* v_x_904_, lean_object* v_x_905_, lean_object* v_x_906_, lean_object* v_x_907_){
_start:
{
size_t v_x_2558__boxed_908_; size_t v_x_2559__boxed_909_; lean_object* v_res_910_; 
v_x_2558__boxed_908_ = lean_unbox_usize(v_x_904_);
lean_dec(v_x_904_);
v_x_2559__boxed_909_ = lean_unbox_usize(v_x_905_);
lean_dec(v_x_905_);
v_res_910_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg(v_x_903_, v_x_2558__boxed_908_, v_x_2559__boxed_909_, v_x_906_, v_x_907_);
return v_res_910_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1___redArg(lean_object* v_x_911_, lean_object* v_x_912_, lean_object* v_x_913_){
_start:
{
uint64_t v___x_914_; size_t v___x_915_; size_t v___x_916_; lean_object* v___x_917_; 
v___x_914_ = l_Lean_instHashableMVarId_hash(v_x_912_);
v___x_915_ = lean_uint64_to_usize(v___x_914_);
v___x_916_ = ((size_t)1ULL);
v___x_917_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg(v_x_911_, v___x_915_, v___x_916_, v_x_912_, v_x_913_);
return v___x_917_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1___redArg(lean_object* v_mvarId_918_, lean_object* v_val_919_, lean_object* v___y_920_){
_start:
{
lean_object* v___x_922_; lean_object* v_mctx_923_; lean_object* v_cache_924_; lean_object* v_zetaDeltaFVarIds_925_; lean_object* v_postponed_926_; lean_object* v_diag_927_; lean_object* v___x_929_; uint8_t v_isShared_930_; uint8_t v_isSharedCheck_957_; 
v___x_922_ = lean_st_ref_take(v___y_920_);
v_mctx_923_ = lean_ctor_get(v___x_922_, 0);
v_cache_924_ = lean_ctor_get(v___x_922_, 1);
v_zetaDeltaFVarIds_925_ = lean_ctor_get(v___x_922_, 2);
v_postponed_926_ = lean_ctor_get(v___x_922_, 3);
v_diag_927_ = lean_ctor_get(v___x_922_, 4);
v_isSharedCheck_957_ = !lean_is_exclusive(v___x_922_);
if (v_isSharedCheck_957_ == 0)
{
v___x_929_ = v___x_922_;
v_isShared_930_ = v_isSharedCheck_957_;
goto v_resetjp_928_;
}
else
{
lean_inc(v_diag_927_);
lean_inc(v_postponed_926_);
lean_inc(v_zetaDeltaFVarIds_925_);
lean_inc(v_cache_924_);
lean_inc(v_mctx_923_);
lean_dec(v___x_922_);
v___x_929_ = lean_box(0);
v_isShared_930_ = v_isSharedCheck_957_;
goto v_resetjp_928_;
}
v_resetjp_928_:
{
lean_object* v_depth_931_; lean_object* v_levelAssignDepth_932_; lean_object* v_lmvarCounter_933_; lean_object* v_mvarCounter_934_; lean_object* v_lDecls_935_; lean_object* v_decls_936_; lean_object* v_userNames_937_; lean_object* v_lAssignment_938_; lean_object* v_eAssignment_939_; lean_object* v_dAssignment_940_; lean_object* v_instanceTypedMVars_941_; lean_object* v_synthNormMemo_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_956_; 
v_depth_931_ = lean_ctor_get(v_mctx_923_, 0);
v_levelAssignDepth_932_ = lean_ctor_get(v_mctx_923_, 1);
v_lmvarCounter_933_ = lean_ctor_get(v_mctx_923_, 2);
v_mvarCounter_934_ = lean_ctor_get(v_mctx_923_, 3);
v_lDecls_935_ = lean_ctor_get(v_mctx_923_, 4);
v_decls_936_ = lean_ctor_get(v_mctx_923_, 5);
v_userNames_937_ = lean_ctor_get(v_mctx_923_, 6);
v_lAssignment_938_ = lean_ctor_get(v_mctx_923_, 7);
v_eAssignment_939_ = lean_ctor_get(v_mctx_923_, 8);
v_dAssignment_940_ = lean_ctor_get(v_mctx_923_, 9);
v_instanceTypedMVars_941_ = lean_ctor_get(v_mctx_923_, 10);
v_synthNormMemo_942_ = lean_ctor_get(v_mctx_923_, 11);
v_isSharedCheck_956_ = !lean_is_exclusive(v_mctx_923_);
if (v_isSharedCheck_956_ == 0)
{
v___x_944_ = v_mctx_923_;
v_isShared_945_ = v_isSharedCheck_956_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_synthNormMemo_942_);
lean_inc(v_instanceTypedMVars_941_);
lean_inc(v_dAssignment_940_);
lean_inc(v_eAssignment_939_);
lean_inc(v_lAssignment_938_);
lean_inc(v_userNames_937_);
lean_inc(v_decls_936_);
lean_inc(v_lDecls_935_);
lean_inc(v_mvarCounter_934_);
lean_inc(v_lmvarCounter_933_);
lean_inc(v_levelAssignDepth_932_);
lean_inc(v_depth_931_);
lean_dec(v_mctx_923_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_956_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_949_; 
v___x_946_ = lean_box(0);
v___x_947_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1___redArg(v_eAssignment_939_, v_mvarId_918_, v_val_919_);
if (v_isShared_945_ == 0)
{
lean_ctor_set(v___x_944_, 8, v___x_947_);
v___x_949_ = v___x_944_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v_depth_931_);
lean_ctor_set(v_reuseFailAlloc_955_, 1, v_levelAssignDepth_932_);
lean_ctor_set(v_reuseFailAlloc_955_, 2, v_lmvarCounter_933_);
lean_ctor_set(v_reuseFailAlloc_955_, 3, v_mvarCounter_934_);
lean_ctor_set(v_reuseFailAlloc_955_, 4, v_lDecls_935_);
lean_ctor_set(v_reuseFailAlloc_955_, 5, v_decls_936_);
lean_ctor_set(v_reuseFailAlloc_955_, 6, v_userNames_937_);
lean_ctor_set(v_reuseFailAlloc_955_, 7, v_lAssignment_938_);
lean_ctor_set(v_reuseFailAlloc_955_, 8, v___x_947_);
lean_ctor_set(v_reuseFailAlloc_955_, 9, v_dAssignment_940_);
lean_ctor_set(v_reuseFailAlloc_955_, 10, v_instanceTypedMVars_941_);
lean_ctor_set(v_reuseFailAlloc_955_, 11, v_synthNormMemo_942_);
v___x_949_ = v_reuseFailAlloc_955_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
lean_object* v___x_951_; 
if (v_isShared_930_ == 0)
{
lean_ctor_set(v___x_929_, 0, v___x_949_);
v___x_951_ = v___x_929_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v___x_949_);
lean_ctor_set(v_reuseFailAlloc_954_, 1, v_cache_924_);
lean_ctor_set(v_reuseFailAlloc_954_, 2, v_zetaDeltaFVarIds_925_);
lean_ctor_set(v_reuseFailAlloc_954_, 3, v_postponed_926_);
lean_ctor_set(v_reuseFailAlloc_954_, 4, v_diag_927_);
v___x_951_ = v_reuseFailAlloc_954_;
goto v_reusejp_950_;
}
v_reusejp_950_:
{
lean_object* v___x_952_; lean_object* v___x_953_; 
v___x_952_ = lean_st_ref_put(v___y_920_, v___x_951_);
v___x_953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_953_, 0, v___x_946_);
return v___x_953_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1___redArg___boxed(lean_object* v_mvarId_958_, lean_object* v_val_959_, lean_object* v___y_960_, lean_object* v___y_961_){
_start:
{
lean_object* v_res_962_; 
v_res_962_ = l_Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1___redArg(v_mvarId_958_, v_val_959_, v___y_960_);
lean_dec(v___y_960_);
return v_res_962_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeTargetsEq___lam__2(lean_object* v_mvarId_963_, lean_object* v___x_964_, lean_object* v_motiveType_965_, lean_object* v___f_966_, lean_object* v_targets_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_){
_start:
{
lean_object* v___x_973_; 
lean_inc(v_mvarId_963_);
v___x_973_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_963_, v___x_964_, v___y_968_, v___y_969_, v___y_970_, v___y_971_);
if (lean_obj_tag(v___x_973_) == 0)
{
uint8_t v___x_974_; lean_object* v___x_975_; 
lean_dec_ref_known(v___x_973_, 1);
v___x_974_ = 0;
v___x_975_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_generalizeTargetsEq_spec__0___redArg(v_motiveType_965_, v___f_966_, v___x_974_, v___x_974_, v___y_968_, v___y_969_, v___y_970_, v___y_971_);
if (lean_obj_tag(v___x_975_) == 0)
{
lean_object* v_a_976_; lean_object* v_fst_977_; lean_object* v_snd_978_; lean_object* v___x_979_; 
v_a_976_ = lean_ctor_get(v___x_975_, 0);
lean_inc(v_a_976_);
lean_dec_ref_known(v___x_975_, 1);
v_fst_977_ = lean_ctor_get(v_a_976_, 0);
lean_inc(v_fst_977_);
v_snd_978_ = lean_ctor_get(v_a_976_, 1);
lean_inc(v_snd_978_);
lean_dec(v_a_976_);
lean_inc(v_mvarId_963_);
v___x_979_ = l_Lean_MVarId_getTag(v_mvarId_963_, v___y_968_, v___y_969_, v___y_970_, v___y_971_);
if (lean_obj_tag(v___x_979_) == 0)
{
lean_object* v_a_980_; lean_object* v___x_981_; 
v_a_980_ = lean_ctor_get(v___x_979_, 0);
lean_inc(v_a_980_);
lean_dec_ref_known(v___x_979_, 1);
v___x_981_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_fst_977_, v_a_980_, v___y_968_, v___y_969_, v___y_970_, v___y_971_);
if (lean_obj_tag(v___x_981_) == 0)
{
lean_object* v_a_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_993_; 
v_a_982_ = lean_ctor_get(v___x_981_, 0);
lean_inc_n(v_a_982_, 2);
lean_dec_ref_known(v___x_981_, 1);
v___x_983_ = l_Lean_mkAppN(v_a_982_, v_targets_967_);
v___x_984_ = l_Lean_mkAppN(v___x_983_, v_snd_978_);
lean_dec(v_snd_978_);
v___x_985_ = l_Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1___redArg(v_mvarId_963_, v___x_984_, v___y_969_);
v_isSharedCheck_993_ = !lean_is_exclusive(v___x_985_);
if (v_isSharedCheck_993_ == 0)
{
lean_object* v_unused_994_; 
v_unused_994_ = lean_ctor_get(v___x_985_, 0);
lean_dec(v_unused_994_);
v___x_987_ = v___x_985_;
v_isShared_988_ = v_isSharedCheck_993_;
goto v_resetjp_986_;
}
else
{
lean_dec(v___x_985_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_993_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
lean_object* v___x_989_; lean_object* v___x_991_; 
v___x_989_ = l_Lean_Expr_mvarId_x21(v_a_982_);
lean_dec(v_a_982_);
if (v_isShared_988_ == 0)
{
lean_ctor_set(v___x_987_, 0, v___x_989_);
v___x_991_ = v___x_987_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_992_; 
v_reuseFailAlloc_992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_992_, 0, v___x_989_);
v___x_991_ = v_reuseFailAlloc_992_;
goto v_reusejp_990_;
}
v_reusejp_990_:
{
return v___x_991_;
}
}
}
else
{
lean_object* v_a_995_; lean_object* v___x_997_; uint8_t v_isShared_998_; uint8_t v_isSharedCheck_1002_; 
lean_dec(v_snd_978_);
lean_dec(v_mvarId_963_);
v_a_995_ = lean_ctor_get(v___x_981_, 0);
v_isSharedCheck_1002_ = !lean_is_exclusive(v___x_981_);
if (v_isSharedCheck_1002_ == 0)
{
v___x_997_ = v___x_981_;
v_isShared_998_ = v_isSharedCheck_1002_;
goto v_resetjp_996_;
}
else
{
lean_inc(v_a_995_);
lean_dec(v___x_981_);
v___x_997_ = lean_box(0);
v_isShared_998_ = v_isSharedCheck_1002_;
goto v_resetjp_996_;
}
v_resetjp_996_:
{
lean_object* v___x_1000_; 
if (v_isShared_998_ == 0)
{
v___x_1000_ = v___x_997_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v_a_995_);
v___x_1000_ = v_reuseFailAlloc_1001_;
goto v_reusejp_999_;
}
v_reusejp_999_:
{
return v___x_1000_;
}
}
}
}
else
{
lean_object* v_a_1003_; lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1010_; 
lean_dec(v_snd_978_);
lean_dec(v_fst_977_);
lean_dec(v_mvarId_963_);
v_a_1003_ = lean_ctor_get(v___x_979_, 0);
v_isSharedCheck_1010_ = !lean_is_exclusive(v___x_979_);
if (v_isSharedCheck_1010_ == 0)
{
v___x_1005_ = v___x_979_;
v_isShared_1006_ = v_isSharedCheck_1010_;
goto v_resetjp_1004_;
}
else
{
lean_inc(v_a_1003_);
lean_dec(v___x_979_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1010_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
lean_object* v___x_1008_; 
if (v_isShared_1006_ == 0)
{
v___x_1008_ = v___x_1005_;
goto v_reusejp_1007_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v_a_1003_);
v___x_1008_ = v_reuseFailAlloc_1009_;
goto v_reusejp_1007_;
}
v_reusejp_1007_:
{
return v___x_1008_;
}
}
}
}
else
{
lean_object* v_a_1011_; lean_object* v___x_1013_; uint8_t v_isShared_1014_; uint8_t v_isSharedCheck_1018_; 
lean_dec(v_mvarId_963_);
v_a_1011_ = lean_ctor_get(v___x_975_, 0);
v_isSharedCheck_1018_ = !lean_is_exclusive(v___x_975_);
if (v_isSharedCheck_1018_ == 0)
{
v___x_1013_ = v___x_975_;
v_isShared_1014_ = v_isSharedCheck_1018_;
goto v_resetjp_1012_;
}
else
{
lean_inc(v_a_1011_);
lean_dec(v___x_975_);
v___x_1013_ = lean_box(0);
v_isShared_1014_ = v_isSharedCheck_1018_;
goto v_resetjp_1012_;
}
v_resetjp_1012_:
{
lean_object* v___x_1016_; 
if (v_isShared_1014_ == 0)
{
v___x_1016_ = v___x_1013_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v_a_1011_);
v___x_1016_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
return v___x_1016_;
}
}
}
}
else
{
lean_object* v_a_1019_; lean_object* v___x_1021_; uint8_t v_isShared_1022_; uint8_t v_isSharedCheck_1026_; 
lean_dec_ref(v___f_966_);
lean_dec_ref(v_motiveType_965_);
lean_dec(v_mvarId_963_);
v_a_1019_ = lean_ctor_get(v___x_973_, 0);
v_isSharedCheck_1026_ = !lean_is_exclusive(v___x_973_);
if (v_isSharedCheck_1026_ == 0)
{
v___x_1021_ = v___x_973_;
v_isShared_1022_ = v_isSharedCheck_1026_;
goto v_resetjp_1020_;
}
else
{
lean_inc(v_a_1019_);
lean_dec(v___x_973_);
v___x_1021_ = lean_box(0);
v_isShared_1022_ = v_isSharedCheck_1026_;
goto v_resetjp_1020_;
}
v_resetjp_1020_:
{
lean_object* v___x_1024_; 
if (v_isShared_1022_ == 0)
{
v___x_1024_ = v___x_1021_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v_a_1019_);
v___x_1024_ = v_reuseFailAlloc_1025_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
return v___x_1024_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeTargetsEq___lam__2___boxed(lean_object* v_mvarId_1027_, lean_object* v___x_1028_, lean_object* v_motiveType_1029_, lean_object* v___f_1030_, lean_object* v_targets_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_){
_start:
{
lean_object* v_res_1037_; 
v_res_1037_ = l_Lean_Meta_generalizeTargetsEq___lam__2(v_mvarId_1027_, v___x_1028_, v_motiveType_1029_, v___f_1030_, v_targets_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_);
lean_dec(v___y_1035_);
lean_dec_ref(v___y_1034_);
lean_dec(v___y_1033_);
lean_dec_ref(v___y_1032_);
lean_dec_ref(v_targets_1031_);
return v_res_1037_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeTargetsEq(lean_object* v_mvarId_1041_, lean_object* v_motiveType_1042_, lean_object* v_targets_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_){
_start:
{
lean_object* v___f_1049_; lean_object* v___x_1050_; lean_object* v___f_1051_; lean_object* v___x_1052_; 
lean_inc_n(v_mvarId_1041_, 2);
lean_inc_ref(v_targets_1043_);
v___f_1049_ = lean_alloc_closure((void*)(l_Lean_Meta_generalizeTargetsEq___lam__1___boxed), 9, 2);
lean_closure_set(v___f_1049_, 0, v_targets_1043_);
lean_closure_set(v___f_1049_, 1, v_mvarId_1041_);
v___x_1050_ = ((lean_object*)(l_Lean_Meta_generalizeTargetsEq___closed__1));
v___f_1051_ = lean_alloc_closure((void*)(l_Lean_Meta_generalizeTargetsEq___lam__2___boxed), 10, 5);
lean_closure_set(v___f_1051_, 0, v_mvarId_1041_);
lean_closure_set(v___f_1051_, 1, v___x_1050_);
lean_closure_set(v___f_1051_, 2, v_motiveType_1042_);
lean_closure_set(v___f_1051_, 3, v___f_1049_);
lean_closure_set(v___f_1051_, 4, v_targets_1043_);
v___x_1052_ = l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2___redArg(v_mvarId_1041_, v___f_1051_, v_a_1044_, v_a_1045_, v_a_1046_, v_a_1047_);
return v___x_1052_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeTargetsEq___boxed(lean_object* v_mvarId_1053_, lean_object* v_motiveType_1054_, lean_object* v_targets_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_){
_start:
{
lean_object* v_res_1061_; 
v_res_1061_ = l_Lean_Meta_generalizeTargetsEq(v_mvarId_1053_, v_motiveType_1054_, v_targets_1055_, v_a_1056_, v_a_1057_, v_a_1058_, v_a_1059_);
lean_dec(v_a_1059_);
lean_dec_ref(v_a_1058_);
lean_dec(v_a_1057_);
lean_dec_ref(v_a_1056_);
return v_res_1061_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1(lean_object* v_mvarId_1062_, lean_object* v_val_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_){
_start:
{
lean_object* v___x_1069_; 
v___x_1069_ = l_Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1___redArg(v_mvarId_1062_, v_val_1063_, v___y_1065_);
return v___x_1069_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1___boxed(lean_object* v_mvarId_1070_, lean_object* v_val_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_){
_start:
{
lean_object* v_res_1077_; 
v_res_1077_ = l_Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1(v_mvarId_1070_, v_val_1071_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_);
lean_dec(v___y_1075_);
lean_dec_ref(v___y_1074_);
lean_dec(v___y_1073_);
lean_dec_ref(v___y_1072_);
return v_res_1077_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1(lean_object* v_00_u03b2_1078_, lean_object* v_x_1079_, lean_object* v_x_1080_, lean_object* v_x_1081_){
_start:
{
lean_object* v___x_1082_; 
v___x_1082_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1___redArg(v_x_1079_, v_x_1080_, v_x_1081_);
return v___x_1082_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3(lean_object* v_00_u03b2_1083_, lean_object* v_x_1084_, size_t v_x_1085_, size_t v_x_1086_, lean_object* v_x_1087_, lean_object* v_x_1088_){
_start:
{
lean_object* v___x_1089_; 
v___x_1089_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg(v_x_1084_, v_x_1085_, v_x_1086_, v_x_1087_, v_x_1088_);
return v___x_1089_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1090_, lean_object* v_x_1091_, lean_object* v_x_1092_, lean_object* v_x_1093_, lean_object* v_x_1094_, lean_object* v_x_1095_){
_start:
{
size_t v_x_2945__boxed_1096_; size_t v_x_2946__boxed_1097_; lean_object* v_res_1098_; 
v_x_2945__boxed_1096_ = lean_unbox_usize(v_x_1092_);
lean_dec(v_x_1092_);
v_x_2946__boxed_1097_ = lean_unbox_usize(v_x_1093_);
lean_dec(v_x_1093_);
v_res_1098_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3(v_00_u03b2_1090_, v_x_1091_, v_x_2945__boxed_1096_, v_x_2946__boxed_1097_, v_x_1094_, v_x_1095_);
return v_res_1098_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_1099_, lean_object* v_n_1100_, lean_object* v_k_1101_, lean_object* v_v_1102_){
_start:
{
lean_object* v___x_1103_; 
v___x_1103_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__4___redArg(v_n_1100_, v_k_1101_, v_v_1102_);
return v___x_1103_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__5(lean_object* v_00_u03b2_1104_, size_t v_depth_1105_, lean_object* v_keys_1106_, lean_object* v_vals_1107_, lean_object* v_heq_1108_, lean_object* v_i_1109_, lean_object* v_entries_1110_){
_start:
{
lean_object* v___x_1111_; 
v___x_1111_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__5___redArg(v_depth_1105_, v_keys_1106_, v_vals_1107_, v_i_1109_, v_entries_1110_);
return v___x_1111_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__5___boxed(lean_object* v_00_u03b2_1112_, lean_object* v_depth_1113_, lean_object* v_keys_1114_, lean_object* v_vals_1115_, lean_object* v_heq_1116_, lean_object* v_i_1117_, lean_object* v_entries_1118_){
_start:
{
size_t v_depth_boxed_1119_; lean_object* v_res_1120_; 
v_depth_boxed_1119_ = lean_unbox_usize(v_depth_1113_);
lean_dec(v_depth_1113_);
v_res_1120_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__5(v_00_u03b2_1112_, v_depth_boxed_1119_, v_keys_1114_, v_vals_1115_, v_heq_1116_, v_i_1117_, v_entries_1118_);
lean_dec_ref(v_vals_1115_);
lean_dec_ref(v_keys_1114_);
return v_res_1120_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_1121_, lean_object* v_x_1122_, lean_object* v_x_1123_, lean_object* v_x_1124_, lean_object* v_x_1125_){
_start:
{
lean_object* v___x_1126_; 
v___x_1126_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__4_spec__5___redArg(v_x_1122_, v_x_1123_, v_x_1124_, v_x_1125_);
return v___x_1126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__0(lean_object* v_newEqs_1127_, lean_object* v_mvarId_1128_, uint8_t v___x_1129_, lean_object* v_h_x27_1130_, lean_object* v_newIndices_1131_, lean_object* v___x_1132_, lean_object* v___x_1133_, lean_object* v___x_1134_, lean_object* v___x_1135_, lean_object* v_e_1136_, lean_object* v___x_1137_, lean_object* v_newEq_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_){
_start:
{
lean_object* v___x_1144_; lean_object* v___x_1145_; 
v___x_1144_ = lean_array_push(v_newEqs_1127_, v_newEq_1138_);
lean_inc(v_mvarId_1128_);
v___x_1145_ = l_Lean_MVarId_getType(v_mvarId_1128_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_);
if (lean_obj_tag(v___x_1145_) == 0)
{
lean_object* v_a_1146_; lean_object* v___x_1147_; 
v_a_1146_ = lean_ctor_get(v___x_1145_, 0);
lean_inc(v_a_1146_);
lean_dec_ref_known(v___x_1145_, 1);
lean_inc(v_mvarId_1128_);
v___x_1147_ = l_Lean_MVarId_getTag(v_mvarId_1128_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_);
if (lean_obj_tag(v___x_1147_) == 0)
{
lean_object* v_a_1148_; uint8_t v___x_1149_; uint8_t v___x_1150_; lean_object* v___x_1151_; 
v_a_1148_ = lean_ctor_get(v___x_1147_, 0);
lean_inc(v_a_1148_);
lean_dec_ref_known(v___x_1147_, 1);
v___x_1149_ = 1;
v___x_1150_ = 1;
v___x_1151_ = l_Lean_Meta_mkForallFVars(v___x_1144_, v_a_1146_, v___x_1129_, v___x_1149_, v___x_1149_, v___x_1150_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_);
if (lean_obj_tag(v___x_1151_) == 0)
{
lean_object* v_a_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; 
v_a_1152_ = lean_ctor_get(v___x_1151_, 0);
lean_inc(v_a_1152_);
lean_dec_ref_known(v___x_1151_, 1);
v___x_1153_ = lean_unsigned_to_nat(1u);
v___x_1154_ = lean_mk_empty_array_with_capacity(v___x_1153_);
v___x_1155_ = lean_array_push(v___x_1154_, v_h_x27_1130_);
v___x_1156_ = l_Lean_Meta_mkForallFVars(v___x_1155_, v_a_1152_, v___x_1129_, v___x_1149_, v___x_1149_, v___x_1150_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_);
lean_dec_ref(v___x_1155_);
if (lean_obj_tag(v___x_1156_) == 0)
{
lean_object* v_a_1157_; lean_object* v___x_1158_; 
v_a_1157_ = lean_ctor_get(v___x_1156_, 0);
lean_inc(v_a_1157_);
lean_dec_ref_known(v___x_1156_, 1);
v___x_1158_ = l_Lean_Meta_mkForallFVars(v_newIndices_1131_, v_a_1157_, v___x_1129_, v___x_1149_, v___x_1149_, v___x_1150_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_);
if (lean_obj_tag(v___x_1158_) == 0)
{
lean_object* v_a_1159_; uint8_t v___x_1160_; lean_object* v___x_1161_; 
v_a_1159_ = lean_ctor_get(v___x_1158_, 0);
lean_inc(v_a_1159_);
lean_dec_ref_known(v___x_1158_, 1);
v___x_1160_ = 2;
v___x_1161_ = l_Lean_Meta_mkFreshExprMVarAt(v___x_1132_, v___x_1133_, v_a_1159_, v___x_1160_, v_a_1148_, v___x_1134_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_);
if (lean_obj_tag(v___x_1161_) == 0)
{
lean_object* v_a_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; 
v_a_1162_ = lean_ctor_get(v___x_1161_, 0);
lean_inc_n(v_a_1162_, 2);
lean_dec_ref_known(v___x_1161_, 1);
v___x_1163_ = l_Lean_mkAppN(v_a_1162_, v___x_1135_);
v___x_1164_ = l_Lean_Expr_app___override(v___x_1163_, v_e_1136_);
v___x_1165_ = l_Lean_mkAppN(v___x_1164_, v___x_1137_);
v___x_1166_ = l_Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1___redArg(v_mvarId_1128_, v___x_1165_, v___y_1140_);
lean_dec_ref(v___x_1166_);
v___x_1167_ = l_Lean_Expr_mvarId_x21(v_a_1162_);
lean_dec(v_a_1162_);
v___x_1168_ = lean_array_get_size(v_newIndices_1131_);
v___x_1169_ = lean_box(0);
v___x_1170_ = l_Lean_Meta_introNCore(v___x_1167_, v___x_1168_, v___x_1169_, v___x_1129_, v___x_1149_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_);
if (lean_obj_tag(v___x_1170_) == 0)
{
lean_object* v_a_1171_; lean_object* v_fst_1172_; lean_object* v_snd_1173_; lean_object* v___x_1174_; 
v_a_1171_ = lean_ctor_get(v___x_1170_, 0);
lean_inc(v_a_1171_);
lean_dec_ref_known(v___x_1170_, 1);
v_fst_1172_ = lean_ctor_get(v_a_1171_, 0);
lean_inc(v_fst_1172_);
v_snd_1173_ = lean_ctor_get(v_a_1171_, 1);
lean_inc(v_snd_1173_);
lean_dec(v_a_1171_);
v___x_1174_ = l_Lean_Meta_intro1Core(v_snd_1173_, v___x_1149_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_);
if (lean_obj_tag(v___x_1174_) == 0)
{
lean_object* v_a_1175_; lean_object* v___x_1177_; uint8_t v_isShared_1178_; uint8_t v_isSharedCheck_1186_; 
v_a_1175_ = lean_ctor_get(v___x_1174_, 0);
v_isSharedCheck_1186_ = !lean_is_exclusive(v___x_1174_);
if (v_isSharedCheck_1186_ == 0)
{
v___x_1177_ = v___x_1174_;
v_isShared_1178_ = v_isSharedCheck_1186_;
goto v_resetjp_1176_;
}
else
{
lean_inc(v_a_1175_);
lean_dec(v___x_1174_);
v___x_1177_ = lean_box(0);
v_isShared_1178_ = v_isSharedCheck_1186_;
goto v_resetjp_1176_;
}
v_resetjp_1176_:
{
lean_object* v_fst_1179_; lean_object* v_snd_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1184_; 
v_fst_1179_ = lean_ctor_get(v_a_1175_, 0);
lean_inc(v_fst_1179_);
v_snd_1180_ = lean_ctor_get(v_a_1175_, 1);
lean_inc(v_snd_1180_);
lean_dec(v_a_1175_);
v___x_1181_ = lean_array_get_size(v___x_1144_);
lean_dec_ref(v___x_1144_);
v___x_1182_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1182_, 0, v_snd_1180_);
lean_ctor_set(v___x_1182_, 1, v_fst_1172_);
lean_ctor_set(v___x_1182_, 2, v_fst_1179_);
lean_ctor_set(v___x_1182_, 3, v___x_1181_);
if (v_isShared_1178_ == 0)
{
lean_ctor_set(v___x_1177_, 0, v___x_1182_);
v___x_1184_ = v___x_1177_;
goto v_reusejp_1183_;
}
else
{
lean_object* v_reuseFailAlloc_1185_; 
v_reuseFailAlloc_1185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1185_, 0, v___x_1182_);
v___x_1184_ = v_reuseFailAlloc_1185_;
goto v_reusejp_1183_;
}
v_reusejp_1183_:
{
return v___x_1184_;
}
}
}
else
{
lean_object* v_a_1187_; lean_object* v___x_1189_; uint8_t v_isShared_1190_; uint8_t v_isSharedCheck_1194_; 
lean_dec(v_fst_1172_);
lean_dec_ref(v___x_1144_);
v_a_1187_ = lean_ctor_get(v___x_1174_, 0);
v_isSharedCheck_1194_ = !lean_is_exclusive(v___x_1174_);
if (v_isSharedCheck_1194_ == 0)
{
v___x_1189_ = v___x_1174_;
v_isShared_1190_ = v_isSharedCheck_1194_;
goto v_resetjp_1188_;
}
else
{
lean_inc(v_a_1187_);
lean_dec(v___x_1174_);
v___x_1189_ = lean_box(0);
v_isShared_1190_ = v_isSharedCheck_1194_;
goto v_resetjp_1188_;
}
v_resetjp_1188_:
{
lean_object* v___x_1192_; 
if (v_isShared_1190_ == 0)
{
v___x_1192_ = v___x_1189_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v_a_1187_);
v___x_1192_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1191_;
}
v_reusejp_1191_:
{
return v___x_1192_;
}
}
}
}
else
{
lean_object* v_a_1195_; lean_object* v___x_1197_; uint8_t v_isShared_1198_; uint8_t v_isSharedCheck_1202_; 
lean_dec_ref(v___x_1144_);
v_a_1195_ = lean_ctor_get(v___x_1170_, 0);
v_isSharedCheck_1202_ = !lean_is_exclusive(v___x_1170_);
if (v_isSharedCheck_1202_ == 0)
{
v___x_1197_ = v___x_1170_;
v_isShared_1198_ = v_isSharedCheck_1202_;
goto v_resetjp_1196_;
}
else
{
lean_inc(v_a_1195_);
lean_dec(v___x_1170_);
v___x_1197_ = lean_box(0);
v_isShared_1198_ = v_isSharedCheck_1202_;
goto v_resetjp_1196_;
}
v_resetjp_1196_:
{
lean_object* v___x_1200_; 
if (v_isShared_1198_ == 0)
{
v___x_1200_ = v___x_1197_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1201_; 
v_reuseFailAlloc_1201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1201_, 0, v_a_1195_);
v___x_1200_ = v_reuseFailAlloc_1201_;
goto v_reusejp_1199_;
}
v_reusejp_1199_:
{
return v___x_1200_;
}
}
}
}
else
{
lean_object* v_a_1203_; lean_object* v___x_1205_; uint8_t v_isShared_1206_; uint8_t v_isSharedCheck_1210_; 
lean_dec_ref(v___x_1144_);
lean_dec_ref(v_e_1136_);
lean_dec(v_mvarId_1128_);
v_a_1203_ = lean_ctor_get(v___x_1161_, 0);
v_isSharedCheck_1210_ = !lean_is_exclusive(v___x_1161_);
if (v_isSharedCheck_1210_ == 0)
{
v___x_1205_ = v___x_1161_;
v_isShared_1206_ = v_isSharedCheck_1210_;
goto v_resetjp_1204_;
}
else
{
lean_inc(v_a_1203_);
lean_dec(v___x_1161_);
v___x_1205_ = lean_box(0);
v_isShared_1206_ = v_isSharedCheck_1210_;
goto v_resetjp_1204_;
}
v_resetjp_1204_:
{
lean_object* v___x_1208_; 
if (v_isShared_1206_ == 0)
{
v___x_1208_ = v___x_1205_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v_a_1203_);
v___x_1208_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
return v___x_1208_;
}
}
}
}
else
{
lean_object* v_a_1211_; lean_object* v___x_1213_; uint8_t v_isShared_1214_; uint8_t v_isSharedCheck_1218_; 
lean_dec(v_a_1148_);
lean_dec_ref(v___x_1144_);
lean_dec_ref(v_e_1136_);
lean_dec(v___x_1134_);
lean_dec_ref(v___x_1133_);
lean_dec_ref(v___x_1132_);
lean_dec(v_mvarId_1128_);
v_a_1211_ = lean_ctor_get(v___x_1158_, 0);
v_isSharedCheck_1218_ = !lean_is_exclusive(v___x_1158_);
if (v_isSharedCheck_1218_ == 0)
{
v___x_1213_ = v___x_1158_;
v_isShared_1214_ = v_isSharedCheck_1218_;
goto v_resetjp_1212_;
}
else
{
lean_inc(v_a_1211_);
lean_dec(v___x_1158_);
v___x_1213_ = lean_box(0);
v_isShared_1214_ = v_isSharedCheck_1218_;
goto v_resetjp_1212_;
}
v_resetjp_1212_:
{
lean_object* v___x_1216_; 
if (v_isShared_1214_ == 0)
{
v___x_1216_ = v___x_1213_;
goto v_reusejp_1215_;
}
else
{
lean_object* v_reuseFailAlloc_1217_; 
v_reuseFailAlloc_1217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1217_, 0, v_a_1211_);
v___x_1216_ = v_reuseFailAlloc_1217_;
goto v_reusejp_1215_;
}
v_reusejp_1215_:
{
return v___x_1216_;
}
}
}
}
else
{
lean_object* v_a_1219_; lean_object* v___x_1221_; uint8_t v_isShared_1222_; uint8_t v_isSharedCheck_1226_; 
lean_dec(v_a_1148_);
lean_dec_ref(v___x_1144_);
lean_dec_ref(v_e_1136_);
lean_dec(v___x_1134_);
lean_dec_ref(v___x_1133_);
lean_dec_ref(v___x_1132_);
lean_dec(v_mvarId_1128_);
v_a_1219_ = lean_ctor_get(v___x_1156_, 0);
v_isSharedCheck_1226_ = !lean_is_exclusive(v___x_1156_);
if (v_isSharedCheck_1226_ == 0)
{
v___x_1221_ = v___x_1156_;
v_isShared_1222_ = v_isSharedCheck_1226_;
goto v_resetjp_1220_;
}
else
{
lean_inc(v_a_1219_);
lean_dec(v___x_1156_);
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
lean_dec(v_a_1148_);
lean_dec_ref(v___x_1144_);
lean_dec_ref(v_e_1136_);
lean_dec(v___x_1134_);
lean_dec_ref(v___x_1133_);
lean_dec_ref(v___x_1132_);
lean_dec_ref(v_h_x27_1130_);
lean_dec(v_mvarId_1128_);
v_a_1227_ = lean_ctor_get(v___x_1151_, 0);
v_isSharedCheck_1234_ = !lean_is_exclusive(v___x_1151_);
if (v_isSharedCheck_1234_ == 0)
{
v___x_1229_ = v___x_1151_;
v_isShared_1230_ = v_isSharedCheck_1234_;
goto v_resetjp_1228_;
}
else
{
lean_inc(v_a_1227_);
lean_dec(v___x_1151_);
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
lean_dec(v_a_1146_);
lean_dec_ref(v___x_1144_);
lean_dec_ref(v_e_1136_);
lean_dec(v___x_1134_);
lean_dec_ref(v___x_1133_);
lean_dec_ref(v___x_1132_);
lean_dec_ref(v_h_x27_1130_);
lean_dec(v_mvarId_1128_);
v_a_1235_ = lean_ctor_get(v___x_1147_, 0);
v_isSharedCheck_1242_ = !lean_is_exclusive(v___x_1147_);
if (v_isSharedCheck_1242_ == 0)
{
v___x_1237_ = v___x_1147_;
v_isShared_1238_ = v_isSharedCheck_1242_;
goto v_resetjp_1236_;
}
else
{
lean_inc(v_a_1235_);
lean_dec(v___x_1147_);
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
lean_dec_ref(v___x_1144_);
lean_dec_ref(v_e_1136_);
lean_dec(v___x_1134_);
lean_dec_ref(v___x_1133_);
lean_dec_ref(v___x_1132_);
lean_dec_ref(v_h_x27_1130_);
lean_dec(v_mvarId_1128_);
v_a_1243_ = lean_ctor_get(v___x_1145_, 0);
v_isSharedCheck_1250_ = !lean_is_exclusive(v___x_1145_);
if (v_isSharedCheck_1250_ == 0)
{
v___x_1245_ = v___x_1145_;
v_isShared_1246_ = v_isSharedCheck_1250_;
goto v_resetjp_1244_;
}
else
{
lean_inc(v_a_1243_);
lean_dec(v___x_1145_);
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
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__0___boxed(lean_object** _args){
lean_object* v_newEqs_1251_ = _args[0];
lean_object* v_mvarId_1252_ = _args[1];
lean_object* v___x_1253_ = _args[2];
lean_object* v_h_x27_1254_ = _args[3];
lean_object* v_newIndices_1255_ = _args[4];
lean_object* v___x_1256_ = _args[5];
lean_object* v___x_1257_ = _args[6];
lean_object* v___x_1258_ = _args[7];
lean_object* v___x_1259_ = _args[8];
lean_object* v_e_1260_ = _args[9];
lean_object* v___x_1261_ = _args[10];
lean_object* v_newEq_1262_ = _args[11];
lean_object* v___y_1263_ = _args[12];
lean_object* v___y_1264_ = _args[13];
lean_object* v___y_1265_ = _args[14];
lean_object* v___y_1266_ = _args[15];
lean_object* v___y_1267_ = _args[16];
_start:
{
uint8_t v___x_6158__boxed_1268_; lean_object* v_res_1269_; 
v___x_6158__boxed_1268_ = lean_unbox(v___x_1253_);
v_res_1269_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__0(v_newEqs_1251_, v_mvarId_1252_, v___x_6158__boxed_1268_, v_h_x27_1254_, v_newIndices_1255_, v___x_1256_, v___x_1257_, v___x_1258_, v___x_1259_, v_e_1260_, v___x_1261_, v_newEq_1262_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_);
lean_dec(v___y_1266_);
lean_dec_ref(v___y_1265_);
lean_dec(v___y_1264_);
lean_dec_ref(v___y_1263_);
lean_dec_ref(v___x_1261_);
lean_dec_ref(v___x_1259_);
lean_dec_ref(v_newIndices_1255_);
return v_res_1269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__1(lean_object* v_e_1270_, lean_object* v_h_x27_1271_, lean_object* v_mvarId_1272_, uint8_t v___x_1273_, lean_object* v_newIndices_1274_, lean_object* v___x_1275_, lean_object* v___x_1276_, lean_object* v___x_1277_, lean_object* v___x_1278_, lean_object* v_newEqs_1279_, lean_object* v_newRefls_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_){
_start:
{
lean_object* v___x_1286_; 
lean_inc_ref(v_h_x27_1271_);
lean_inc_ref(v_e_1270_);
v___x_1286_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof(v_e_1270_, v_h_x27_1271_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_);
if (lean_obj_tag(v___x_1286_) == 0)
{
lean_object* v_a_1287_; lean_object* v_fst_1288_; lean_object* v_snd_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___f_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; 
v_a_1287_ = lean_ctor_get(v___x_1286_, 0);
lean_inc(v_a_1287_);
lean_dec_ref_known(v___x_1286_, 1);
v_fst_1288_ = lean_ctor_get(v_a_1287_, 0);
lean_inc(v_fst_1288_);
v_snd_1289_ = lean_ctor_get(v_a_1287_, 1);
lean_inc(v_snd_1289_);
lean_dec(v_a_1287_);
v___x_1290_ = lean_array_push(v_newRefls_1280_, v_snd_1289_);
v___x_1291_ = lean_box(v___x_1273_);
v___f_1292_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__0___boxed), 17, 11);
lean_closure_set(v___f_1292_, 0, v_newEqs_1279_);
lean_closure_set(v___f_1292_, 1, v_mvarId_1272_);
lean_closure_set(v___f_1292_, 2, v___x_1291_);
lean_closure_set(v___f_1292_, 3, v_h_x27_1271_);
lean_closure_set(v___f_1292_, 4, v_newIndices_1274_);
lean_closure_set(v___f_1292_, 5, v___x_1275_);
lean_closure_set(v___f_1292_, 6, v___x_1276_);
lean_closure_set(v___f_1292_, 7, v___x_1277_);
lean_closure_set(v___f_1292_, 8, v___x_1278_);
lean_closure_set(v___f_1292_, 9, v_e_1270_);
lean_closure_set(v___f_1292_, 10, v___x_1290_);
v___x_1293_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___redArg___closed__1));
v___x_1294_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0___redArg(v___x_1293_, v_fst_1288_, v___f_1292_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_);
return v___x_1294_;
}
else
{
lean_object* v_a_1295_; lean_object* v___x_1297_; uint8_t v_isShared_1298_; uint8_t v_isSharedCheck_1302_; 
lean_dec_ref(v_newRefls_1280_);
lean_dec_ref(v_newEqs_1279_);
lean_dec_ref(v___x_1278_);
lean_dec(v___x_1277_);
lean_dec_ref(v___x_1276_);
lean_dec_ref(v___x_1275_);
lean_dec_ref(v_newIndices_1274_);
lean_dec(v_mvarId_1272_);
lean_dec_ref(v_h_x27_1271_);
lean_dec_ref(v_e_1270_);
v_a_1295_ = lean_ctor_get(v___x_1286_, 0);
v_isSharedCheck_1302_ = !lean_is_exclusive(v___x_1286_);
if (v_isSharedCheck_1302_ == 0)
{
v___x_1297_ = v___x_1286_;
v_isShared_1298_ = v_isSharedCheck_1302_;
goto v_resetjp_1296_;
}
else
{
lean_inc(v_a_1295_);
lean_dec(v___x_1286_);
v___x_1297_ = lean_box(0);
v_isShared_1298_ = v_isSharedCheck_1302_;
goto v_resetjp_1296_;
}
v_resetjp_1296_:
{
lean_object* v___x_1300_; 
if (v_isShared_1298_ == 0)
{
v___x_1300_ = v___x_1297_;
goto v_reusejp_1299_;
}
else
{
lean_object* v_reuseFailAlloc_1301_; 
v_reuseFailAlloc_1301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1301_, 0, v_a_1295_);
v___x_1300_ = v_reuseFailAlloc_1301_;
goto v_reusejp_1299_;
}
v_reusejp_1299_:
{
return v___x_1300_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__1___boxed(lean_object* v_e_1303_, lean_object* v_h_x27_1304_, lean_object* v_mvarId_1305_, lean_object* v___x_1306_, lean_object* v_newIndices_1307_, lean_object* v___x_1308_, lean_object* v___x_1309_, lean_object* v___x_1310_, lean_object* v___x_1311_, lean_object* v_newEqs_1312_, lean_object* v_newRefls_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_){
_start:
{
uint8_t v___x_6410__boxed_1319_; lean_object* v_res_1320_; 
v___x_6410__boxed_1319_ = lean_unbox(v___x_1306_);
v_res_1320_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__1(v_e_1303_, v_h_x27_1304_, v_mvarId_1305_, v___x_6410__boxed_1319_, v_newIndices_1307_, v___x_1308_, v___x_1309_, v___x_1310_, v___x_1311_, v_newEqs_1312_, v_newRefls_1313_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_);
lean_dec(v___y_1317_);
lean_dec_ref(v___y_1316_);
lean_dec(v___y_1315_);
lean_dec_ref(v___y_1314_);
return v_res_1320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__2(lean_object* v_e_1321_, lean_object* v_mvarId_1322_, uint8_t v___x_1323_, lean_object* v_newIndices_1324_, lean_object* v___x_1325_, lean_object* v___x_1326_, lean_object* v___x_1327_, lean_object* v___x_1328_, lean_object* v_h_x27_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_){
_start:
{
lean_object* v___x_1335_; lean_object* v___f_1336_; lean_object* v___x_1337_; 
v___x_1335_ = lean_box(v___x_1323_);
lean_inc_ref(v___x_1328_);
lean_inc_ref(v_newIndices_1324_);
v___f_1336_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__1___boxed), 16, 9);
lean_closure_set(v___f_1336_, 0, v_e_1321_);
lean_closure_set(v___f_1336_, 1, v_h_x27_1329_);
lean_closure_set(v___f_1336_, 2, v_mvarId_1322_);
lean_closure_set(v___f_1336_, 3, v___x_1335_);
lean_closure_set(v___f_1336_, 4, v_newIndices_1324_);
lean_closure_set(v___f_1336_, 5, v___x_1325_);
lean_closure_set(v___f_1336_, 6, v___x_1326_);
lean_closure_set(v___f_1336_, 7, v___x_1327_);
lean_closure_set(v___f_1336_, 8, v___x_1328_);
v___x_1337_ = l_Lean_Meta_withNewEqs___redArg(v___x_1328_, v_newIndices_1324_, v___f_1336_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_);
return v___x_1337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__2___boxed(lean_object* v_e_1338_, lean_object* v_mvarId_1339_, lean_object* v___x_1340_, lean_object* v_newIndices_1341_, lean_object* v___x_1342_, lean_object* v___x_1343_, lean_object* v___x_1344_, lean_object* v___x_1345_, lean_object* v_h_x27_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_){
_start:
{
uint8_t v___x_6475__boxed_1352_; lean_object* v_res_1353_; 
v___x_6475__boxed_1352_ = lean_unbox(v___x_1340_);
v_res_1353_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__2(v_e_1338_, v_mvarId_1339_, v___x_6475__boxed_1352_, v_newIndices_1341_, v___x_1342_, v___x_1343_, v___x_1344_, v___x_1345_, v_h_x27_1346_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_);
lean_dec(v___y_1350_);
lean_dec_ref(v___y_1349_);
lean_dec(v___y_1348_);
lean_dec_ref(v___y_1347_);
return v_res_1353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__3(lean_object* v_e_1357_, lean_object* v_mvarId_1358_, uint8_t v___x_1359_, lean_object* v___x_1360_, lean_object* v___x_1361_, lean_object* v___x_1362_, lean_object* v___x_1363_, lean_object* v___x_1364_, lean_object* v_varName_x3f_1365_, lean_object* v_newIndices_1366_, lean_object* v_x_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_){
_start:
{
lean_object* v___x_1373_; lean_object* v___f_1374_; lean_object* v___x_1375_; 
v___x_1373_ = lean_box(v___x_1359_);
lean_inc_ref(v_newIndices_1366_);
v___f_1374_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__2___boxed), 14, 8);
lean_closure_set(v___f_1374_, 0, v_e_1357_);
lean_closure_set(v___f_1374_, 1, v_mvarId_1358_);
lean_closure_set(v___f_1374_, 2, v___x_1373_);
lean_closure_set(v___f_1374_, 3, v_newIndices_1366_);
lean_closure_set(v___f_1374_, 4, v___x_1360_);
lean_closure_set(v___f_1374_, 5, v___x_1361_);
lean_closure_set(v___f_1374_, 6, v___x_1362_);
lean_closure_set(v___f_1374_, 7, v___x_1363_);
v___x_1375_ = l_Lean_mkAppN(v___x_1364_, v_newIndices_1366_);
lean_dec_ref(v_newIndices_1366_);
if (lean_obj_tag(v_varName_x3f_1365_) == 1)
{
lean_object* v_val_1376_; lean_object* v___x_1377_; 
v_val_1376_ = lean_ctor_get(v_varName_x3f_1365_, 0);
lean_inc(v_val_1376_);
lean_dec_ref_known(v_varName_x3f_1365_, 1);
v___x_1377_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0___redArg(v_val_1376_, v___x_1375_, v___f_1374_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_);
return v___x_1377_;
}
else
{
lean_object* v___x_1378_; lean_object* v___x_1379_; 
lean_dec(v_varName_x3f_1365_);
v___x_1378_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__3___closed__1));
v___x_1379_ = l_Lean_Core_mkFreshUserName(v___x_1378_, v___y_1370_, v___y_1371_);
if (lean_obj_tag(v___x_1379_) == 0)
{
lean_object* v_a_1380_; lean_object* v___x_1381_; 
v_a_1380_ = lean_ctor_get(v___x_1379_, 0);
lean_inc(v_a_1380_);
lean_dec_ref_known(v___x_1379_, 1);
v___x_1381_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0___redArg(v_a_1380_, v___x_1375_, v___f_1374_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_);
return v___x_1381_;
}
else
{
lean_object* v_a_1382_; lean_object* v___x_1384_; uint8_t v_isShared_1385_; uint8_t v_isSharedCheck_1389_; 
lean_dec_ref(v___x_1375_);
lean_dec_ref(v___f_1374_);
v_a_1382_ = lean_ctor_get(v___x_1379_, 0);
v_isSharedCheck_1389_ = !lean_is_exclusive(v___x_1379_);
if (v_isSharedCheck_1389_ == 0)
{
v___x_1384_ = v___x_1379_;
v_isShared_1385_ = v_isSharedCheck_1389_;
goto v_resetjp_1383_;
}
else
{
lean_inc(v_a_1382_);
lean_dec(v___x_1379_);
v___x_1384_ = lean_box(0);
v_isShared_1385_ = v_isSharedCheck_1389_;
goto v_resetjp_1383_;
}
v_resetjp_1383_:
{
lean_object* v___x_1387_; 
if (v_isShared_1385_ == 0)
{
v___x_1387_ = v___x_1384_;
goto v_reusejp_1386_;
}
else
{
lean_object* v_reuseFailAlloc_1388_; 
v_reuseFailAlloc_1388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1388_, 0, v_a_1382_);
v___x_1387_ = v_reuseFailAlloc_1388_;
goto v_reusejp_1386_;
}
v_reusejp_1386_:
{
return v___x_1387_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__3___boxed(lean_object* v_e_1390_, lean_object* v_mvarId_1391_, lean_object* v___x_1392_, lean_object* v___x_1393_, lean_object* v___x_1394_, lean_object* v___x_1395_, lean_object* v___x_1396_, lean_object* v___x_1397_, lean_object* v_varName_x3f_1398_, lean_object* v_newIndices_1399_, lean_object* v_x_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_){
_start:
{
uint8_t v___x_6517__boxed_1406_; lean_object* v_res_1407_; 
v___x_6517__boxed_1406_ = lean_unbox(v___x_1392_);
v_res_1407_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__3(v_e_1390_, v_mvarId_1391_, v___x_6517__boxed_1406_, v___x_1393_, v___x_1394_, v___x_1395_, v___x_1396_, v___x_1397_, v_varName_x3f_1398_, v_newIndices_1399_, v_x_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_);
lean_dec(v___y_1404_);
lean_dec_ref(v___y_1403_);
lean_dec(v___y_1402_);
lean_dec_ref(v___y_1401_);
lean_dec_ref(v_x_1400_);
return v_res_1407_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__4(void){
_start:
{
lean_object* v___x_1414_; lean_object* v___x_1415_; 
v___x_1414_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__3));
v___x_1415_ = l_Lean_MessageData_ofFormat(v___x_1414_);
return v___x_1415_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__5(void){
_start:
{
lean_object* v___x_1416_; lean_object* v___x_1417_; 
v___x_1416_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__4, &l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__4_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__4);
v___x_1417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1417_, 0, v___x_1416_);
return v___x_1417_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__8(void){
_start:
{
lean_object* v___x_1421_; lean_object* v___x_1422_; 
v___x_1421_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__7));
v___x_1422_ = l_Lean_MessageData_ofFormat(v___x_1421_);
return v___x_1422_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__9(void){
_start:
{
lean_object* v___x_1423_; lean_object* v___x_1424_; 
v___x_1423_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__8, &l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__8_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__8);
v___x_1424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1424_, 0, v___x_1423_);
return v___x_1424_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__12(void){
_start:
{
lean_object* v___x_1428_; lean_object* v___x_1429_; 
v___x_1428_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__11));
v___x_1429_ = l_Lean_MessageData_ofFormat(v___x_1428_);
return v___x_1429_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__13(void){
_start:
{
lean_object* v___x_1430_; lean_object* v___x_1431_; 
v___x_1430_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__12, &l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__12_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__12);
v___x_1431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1431_, 0, v___x_1430_);
return v___x_1431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0(lean_object* v_mvarId_1432_, lean_object* v_e_1433_, lean_object* v___x_1434_, lean_object* v___x_1435_, lean_object* v_varName_x3f_1436_, lean_object* v_x_1437_, lean_object* v_x_1438_, lean_object* v_x_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_){
_start:
{
if (lean_obj_tag(v_x_1437_) == 5)
{
lean_object* v_fn_1445_; lean_object* v_arg_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; 
v_fn_1445_ = lean_ctor_get(v_x_1437_, 0);
lean_inc_ref(v_fn_1445_);
v_arg_1446_ = lean_ctor_get(v_x_1437_, 1);
lean_inc_ref(v_arg_1446_);
lean_dec_ref_known(v_x_1437_, 2);
v___x_1447_ = lean_array_set(v_x_1438_, v_x_1439_, v_arg_1446_);
v___x_1448_ = lean_unsigned_to_nat(1u);
v___x_1449_ = lean_nat_sub(v_x_1439_, v___x_1448_);
lean_dec(v_x_1439_);
v_x_1437_ = v_fn_1445_;
v_x_1438_ = v___x_1447_;
v_x_1439_ = v___x_1449_;
goto _start;
}
else
{
lean_object* v___x_1451_; lean_object* v___y_1453_; lean_object* v___y_1454_; lean_object* v___y_1455_; lean_object* v___y_1456_; 
lean_dec(v_x_1439_);
v___x_1451_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__1));
if (lean_obj_tag(v_x_1437_) == 4)
{
lean_object* v_declName_1459_; lean_object* v___x_1460_; lean_object* v_env_1461_; uint8_t v___x_1462_; lean_object* v___x_1463_; 
v_declName_1459_ = lean_ctor_get(v_x_1437_, 0);
v___x_1460_ = lean_st_ref_get(v___y_1443_);
v_env_1461_ = lean_ctor_get(v___x_1460_, 0);
lean_inc_ref(v_env_1461_);
lean_dec(v___x_1460_);
v___x_1462_ = 0;
lean_inc(v_declName_1459_);
v___x_1463_ = l_Lean_Environment_find_x3f(v_env_1461_, v_declName_1459_, v___x_1462_);
if (lean_obj_tag(v___x_1463_) == 0)
{
lean_dec_ref_known(v_x_1437_, 2);
lean_dec_ref(v_x_1438_);
lean_dec(v_varName_x3f_1436_);
lean_dec_ref(v___x_1435_);
lean_dec_ref(v___x_1434_);
lean_dec_ref(v_e_1433_);
v___y_1453_ = v___y_1440_;
v___y_1454_ = v___y_1441_;
v___y_1455_ = v___y_1442_;
v___y_1456_ = v___y_1443_;
goto v___jp_1452_;
}
else
{
lean_object* v_val_1464_; 
v_val_1464_ = lean_ctor_get(v___x_1463_, 0);
lean_inc(v_val_1464_);
lean_dec_ref_known(v___x_1463_, 1);
if (lean_obj_tag(v_val_1464_) == 5)
{
lean_object* v_val_1465_; lean_object* v_numParams_1466_; lean_object* v_numIndices_1467_; lean_object* v___y_1469_; lean_object* v___y_1470_; lean_object* v___y_1471_; lean_object* v___y_1472_; lean_object* v___y_1493_; lean_object* v___y_1494_; lean_object* v___y_1495_; lean_object* v___y_1496_; lean_object* v___x_1510_; uint8_t v___x_1511_; 
v_val_1465_ = lean_ctor_get(v_val_1464_, 0);
lean_inc_ref(v_val_1465_);
lean_dec_ref_known(v_val_1464_, 1);
v_numParams_1466_ = lean_ctor_get(v_val_1465_, 1);
lean_inc(v_numParams_1466_);
v_numIndices_1467_ = lean_ctor_get(v_val_1465_, 2);
lean_inc(v_numIndices_1467_);
lean_dec_ref(v_val_1465_);
v___x_1510_ = lean_unsigned_to_nat(0u);
v___x_1511_ = lean_nat_dec_lt(v___x_1510_, v_numIndices_1467_);
if (v___x_1511_ == 0)
{
lean_object* v___x_1512_; lean_object* v___x_1513_; 
v___x_1512_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__13, &l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__13_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__13);
lean_inc(v_mvarId_1432_);
v___x_1513_ = l_Lean_Meta_throwTacticEx___redArg(v___x_1451_, v_mvarId_1432_, v___x_1512_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_);
if (lean_obj_tag(v___x_1513_) == 0)
{
lean_dec_ref_known(v___x_1513_, 1);
v___y_1493_ = v___y_1440_;
v___y_1494_ = v___y_1441_;
v___y_1495_ = v___y_1442_;
v___y_1496_ = v___y_1443_;
goto v___jp_1492_;
}
else
{
lean_object* v_a_1514_; lean_object* v___x_1516_; uint8_t v_isShared_1517_; uint8_t v_isSharedCheck_1521_; 
lean_dec(v_numIndices_1467_);
lean_dec(v_numParams_1466_);
lean_dec_ref_known(v_x_1437_, 2);
lean_dec_ref(v_x_1438_);
lean_dec(v_varName_x3f_1436_);
lean_dec_ref(v___x_1435_);
lean_dec_ref(v___x_1434_);
lean_dec_ref(v_e_1433_);
lean_dec(v_mvarId_1432_);
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
else
{
v___y_1493_ = v___y_1440_;
v___y_1494_ = v___y_1441_;
v___y_1495_ = v___y_1442_;
v___y_1496_ = v___y_1443_;
goto v___jp_1492_;
}
v___jp_1468_:
{
lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___f_1480_; lean_object* v___x_1481_; 
v___x_1473_ = lean_array_get_size(v_x_1438_);
v___x_1474_ = lean_nat_sub(v___x_1473_, v_numIndices_1467_);
lean_dec(v_numIndices_1467_);
v___x_1475_ = l_Array_extract___redArg(v_x_1438_, v___x_1474_, v___x_1473_);
v___x_1476_ = lean_unsigned_to_nat(0u);
v___x_1477_ = l_Array_extract___redArg(v_x_1438_, v___x_1476_, v_numParams_1466_);
lean_dec_ref(v_x_1438_);
v___x_1478_ = l_Lean_mkAppN(v_x_1437_, v___x_1477_);
lean_dec_ref(v___x_1477_);
v___x_1479_ = lean_box(v___x_1462_);
lean_inc_ref(v___x_1478_);
v___f_1480_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__3___boxed), 16, 9);
lean_closure_set(v___f_1480_, 0, v_e_1433_);
lean_closure_set(v___f_1480_, 1, v_mvarId_1432_);
lean_closure_set(v___f_1480_, 2, v___x_1479_);
lean_closure_set(v___f_1480_, 3, v___x_1434_);
lean_closure_set(v___f_1480_, 4, v___x_1435_);
lean_closure_set(v___f_1480_, 5, v___x_1476_);
lean_closure_set(v___f_1480_, 6, v___x_1475_);
lean_closure_set(v___f_1480_, 7, v___x_1478_);
lean_closure_set(v___f_1480_, 8, v_varName_x3f_1436_);
lean_inc(v___y_1472_);
lean_inc_ref(v___y_1471_);
lean_inc(v___y_1470_);
lean_inc_ref(v___y_1469_);
v___x_1481_ = lean_infer_type(v___x_1478_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_);
if (lean_obj_tag(v___x_1481_) == 0)
{
lean_object* v_a_1482_; lean_object* v___x_1483_; 
v_a_1482_ = lean_ctor_get(v___x_1481_, 0);
lean_inc(v_a_1482_);
lean_dec_ref_known(v___x_1481_, 1);
v___x_1483_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_generalizeTargetsEq_spec__0___redArg(v_a_1482_, v___f_1480_, v___x_1462_, v___x_1462_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_);
return v___x_1483_;
}
else
{
lean_object* v_a_1484_; lean_object* v___x_1486_; uint8_t v_isShared_1487_; uint8_t v_isSharedCheck_1491_; 
lean_dec_ref(v___f_1480_);
v_a_1484_ = lean_ctor_get(v___x_1481_, 0);
v_isSharedCheck_1491_ = !lean_is_exclusive(v___x_1481_);
if (v_isSharedCheck_1491_ == 0)
{
v___x_1486_ = v___x_1481_;
v_isShared_1487_ = v_isSharedCheck_1491_;
goto v_resetjp_1485_;
}
else
{
lean_inc(v_a_1484_);
lean_dec(v___x_1481_);
v___x_1486_ = lean_box(0);
v_isShared_1487_ = v_isSharedCheck_1491_;
goto v_resetjp_1485_;
}
v_resetjp_1485_:
{
lean_object* v___x_1489_; 
if (v_isShared_1487_ == 0)
{
v___x_1489_ = v___x_1486_;
goto v_reusejp_1488_;
}
else
{
lean_object* v_reuseFailAlloc_1490_; 
v_reuseFailAlloc_1490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1490_, 0, v_a_1484_);
v___x_1489_ = v_reuseFailAlloc_1490_;
goto v_reusejp_1488_;
}
v_reusejp_1488_:
{
return v___x_1489_;
}
}
}
}
v___jp_1492_:
{
lean_object* v___x_1497_; lean_object* v___x_1498_; uint8_t v___x_1499_; 
v___x_1497_ = lean_array_get_size(v_x_1438_);
v___x_1498_ = lean_nat_add(v_numIndices_1467_, v_numParams_1466_);
v___x_1499_ = lean_nat_dec_eq(v___x_1497_, v___x_1498_);
lean_dec(v___x_1498_);
if (v___x_1499_ == 0)
{
lean_object* v___x_1500_; lean_object* v___x_1501_; 
v___x_1500_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__9, &l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__9_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__9);
lean_inc(v_mvarId_1432_);
v___x_1501_ = l_Lean_Meta_throwTacticEx___redArg(v___x_1451_, v_mvarId_1432_, v___x_1500_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_);
if (lean_obj_tag(v___x_1501_) == 0)
{
lean_dec_ref_known(v___x_1501_, 1);
v___y_1469_ = v___y_1493_;
v___y_1470_ = v___y_1494_;
v___y_1471_ = v___y_1495_;
v___y_1472_ = v___y_1496_;
goto v___jp_1468_;
}
else
{
lean_object* v_a_1502_; lean_object* v___x_1504_; uint8_t v_isShared_1505_; uint8_t v_isSharedCheck_1509_; 
lean_dec(v_numIndices_1467_);
lean_dec(v_numParams_1466_);
lean_dec_ref_known(v_x_1437_, 2);
lean_dec_ref(v_x_1438_);
lean_dec(v_varName_x3f_1436_);
lean_dec_ref(v___x_1435_);
lean_dec_ref(v___x_1434_);
lean_dec_ref(v_e_1433_);
lean_dec(v_mvarId_1432_);
v_a_1502_ = lean_ctor_get(v___x_1501_, 0);
v_isSharedCheck_1509_ = !lean_is_exclusive(v___x_1501_);
if (v_isSharedCheck_1509_ == 0)
{
v___x_1504_ = v___x_1501_;
v_isShared_1505_ = v_isSharedCheck_1509_;
goto v_resetjp_1503_;
}
else
{
lean_inc(v_a_1502_);
lean_dec(v___x_1501_);
v___x_1504_ = lean_box(0);
v_isShared_1505_ = v_isSharedCheck_1509_;
goto v_resetjp_1503_;
}
v_resetjp_1503_:
{
lean_object* v___x_1507_; 
if (v_isShared_1505_ == 0)
{
v___x_1507_ = v___x_1504_;
goto v_reusejp_1506_;
}
else
{
lean_object* v_reuseFailAlloc_1508_; 
v_reuseFailAlloc_1508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1508_, 0, v_a_1502_);
v___x_1507_ = v_reuseFailAlloc_1508_;
goto v_reusejp_1506_;
}
v_reusejp_1506_:
{
return v___x_1507_;
}
}
}
}
else
{
v___y_1469_ = v___y_1493_;
v___y_1470_ = v___y_1494_;
v___y_1471_ = v___y_1495_;
v___y_1472_ = v___y_1496_;
goto v___jp_1468_;
}
}
}
else
{
lean_dec(v_val_1464_);
lean_dec_ref_known(v_x_1437_, 2);
lean_dec_ref(v_x_1438_);
lean_dec(v_varName_x3f_1436_);
lean_dec_ref(v___x_1435_);
lean_dec_ref(v___x_1434_);
lean_dec_ref(v_e_1433_);
v___y_1453_ = v___y_1440_;
v___y_1454_ = v___y_1441_;
v___y_1455_ = v___y_1442_;
v___y_1456_ = v___y_1443_;
goto v___jp_1452_;
}
}
}
else
{
lean_dec_ref(v_x_1438_);
lean_dec_ref(v_x_1437_);
lean_dec(v_varName_x3f_1436_);
lean_dec_ref(v___x_1435_);
lean_dec_ref(v___x_1434_);
lean_dec_ref(v_e_1433_);
v___y_1453_ = v___y_1440_;
v___y_1454_ = v___y_1441_;
v___y_1455_ = v___y_1442_;
v___y_1456_ = v___y_1443_;
goto v___jp_1452_;
}
v___jp_1452_:
{
lean_object* v___x_1457_; lean_object* v___x_1458_; 
v___x_1457_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__5, &l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__5_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__5);
v___x_1458_ = l_Lean_Meta_throwTacticEx___redArg(v___x_1451_, v_mvarId_1432_, v___x_1457_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_);
return v___x_1458_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___boxed(lean_object* v_mvarId_1522_, lean_object* v_e_1523_, lean_object* v___x_1524_, lean_object* v___x_1525_, lean_object* v_varName_x3f_1526_, lean_object* v_x_1527_, lean_object* v_x_1528_, lean_object* v_x_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_){
_start:
{
lean_object* v_res_1535_; 
v_res_1535_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0(v_mvarId_1522_, v_e_1523_, v___x_1524_, v___x_1525_, v_varName_x3f_1526_, v_x_1527_, v_x_1528_, v_x_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_);
lean_dec(v___y_1533_);
lean_dec_ref(v___y_1532_);
lean_dec(v___y_1531_);
lean_dec_ref(v___y_1530_);
return v_res_1535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeIndices_x27___lam__0(lean_object* v_mvarId_1536_, lean_object* v_e_1537_, lean_object* v_varName_x3f_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_){
_start:
{
lean_object* v_lctx_1544_; lean_object* v_localInstances_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; 
v_lctx_1544_ = lean_ctor_get(v___y_1539_, 2);
lean_inc_ref(v_lctx_1544_);
v_localInstances_1545_ = lean_ctor_get(v___y_1539_, 3);
lean_inc_ref(v_localInstances_1545_);
v___x_1546_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__1));
lean_inc(v_mvarId_1536_);
v___x_1547_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_1536_, v___x_1546_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_);
if (lean_obj_tag(v___x_1547_) == 0)
{
lean_object* v___x_1548_; 
lean_dec_ref_known(v___x_1547_, 1);
lean_inc(v___y_1542_);
lean_inc_ref(v___y_1541_);
lean_inc(v___y_1540_);
lean_inc_ref(v___y_1539_);
lean_inc_ref(v_e_1537_);
v___x_1548_ = lean_infer_type(v_e_1537_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_);
if (lean_obj_tag(v___x_1548_) == 0)
{
lean_object* v_a_1549_; lean_object* v___x_1550_; 
v_a_1549_ = lean_ctor_get(v___x_1548_, 0);
lean_inc(v_a_1549_);
lean_dec_ref_known(v___x_1548_, 1);
v___x_1550_ = l_Lean_Meta_whnfD(v_a_1549_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_);
if (lean_obj_tag(v___x_1550_) == 0)
{
lean_object* v_a_1551_; lean_object* v_dummy_1552_; lean_object* v_nargs_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; 
v_a_1551_ = lean_ctor_get(v___x_1550_, 0);
lean_inc(v_a_1551_);
lean_dec_ref_known(v___x_1550_, 1);
v_dummy_1552_ = lean_obj_once(&l_Lean_Meta_getInductiveUniverseAndParams___closed__0, &l_Lean_Meta_getInductiveUniverseAndParams___closed__0_once, _init_l_Lean_Meta_getInductiveUniverseAndParams___closed__0);
v_nargs_1553_ = l_Lean_Expr_getAppNumArgs(v_a_1551_);
lean_inc(v_nargs_1553_);
v___x_1554_ = lean_mk_array(v_nargs_1553_, v_dummy_1552_);
v___x_1555_ = lean_unsigned_to_nat(1u);
v___x_1556_ = lean_nat_sub(v_nargs_1553_, v___x_1555_);
lean_dec(v_nargs_1553_);
v___x_1557_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0(v_mvarId_1536_, v_e_1537_, v_lctx_1544_, v_localInstances_1545_, v_varName_x3f_1538_, v_a_1551_, v___x_1554_, v___x_1556_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_);
lean_dec(v___y_1542_);
lean_dec_ref(v___y_1541_);
lean_dec(v___y_1540_);
lean_dec_ref(v___y_1539_);
return v___x_1557_;
}
else
{
lean_object* v_a_1558_; lean_object* v___x_1560_; uint8_t v_isShared_1561_; uint8_t v_isSharedCheck_1565_; 
lean_dec_ref(v_localInstances_1545_);
lean_dec_ref(v_lctx_1544_);
lean_dec(v___y_1542_);
lean_dec_ref(v___y_1541_);
lean_dec(v___y_1540_);
lean_dec_ref(v___y_1539_);
lean_dec(v_varName_x3f_1538_);
lean_dec_ref(v_e_1537_);
lean_dec(v_mvarId_1536_);
v_a_1558_ = lean_ctor_get(v___x_1550_, 0);
v_isSharedCheck_1565_ = !lean_is_exclusive(v___x_1550_);
if (v_isSharedCheck_1565_ == 0)
{
v___x_1560_ = v___x_1550_;
v_isShared_1561_ = v_isSharedCheck_1565_;
goto v_resetjp_1559_;
}
else
{
lean_inc(v_a_1558_);
lean_dec(v___x_1550_);
v___x_1560_ = lean_box(0);
v_isShared_1561_ = v_isSharedCheck_1565_;
goto v_resetjp_1559_;
}
v_resetjp_1559_:
{
lean_object* v___x_1563_; 
if (v_isShared_1561_ == 0)
{
v___x_1563_ = v___x_1560_;
goto v_reusejp_1562_;
}
else
{
lean_object* v_reuseFailAlloc_1564_; 
v_reuseFailAlloc_1564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1564_, 0, v_a_1558_);
v___x_1563_ = v_reuseFailAlloc_1564_;
goto v_reusejp_1562_;
}
v_reusejp_1562_:
{
return v___x_1563_;
}
}
}
}
else
{
lean_object* v_a_1566_; lean_object* v___x_1568_; uint8_t v_isShared_1569_; uint8_t v_isSharedCheck_1573_; 
lean_dec_ref(v_localInstances_1545_);
lean_dec_ref(v_lctx_1544_);
lean_dec(v___y_1542_);
lean_dec_ref(v___y_1541_);
lean_dec(v___y_1540_);
lean_dec_ref(v___y_1539_);
lean_dec(v_varName_x3f_1538_);
lean_dec_ref(v_e_1537_);
lean_dec(v_mvarId_1536_);
v_a_1566_ = lean_ctor_get(v___x_1548_, 0);
v_isSharedCheck_1573_ = !lean_is_exclusive(v___x_1548_);
if (v_isSharedCheck_1573_ == 0)
{
v___x_1568_ = v___x_1548_;
v_isShared_1569_ = v_isSharedCheck_1573_;
goto v_resetjp_1567_;
}
else
{
lean_inc(v_a_1566_);
lean_dec(v___x_1548_);
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
else
{
lean_object* v_a_1574_; lean_object* v___x_1576_; uint8_t v_isShared_1577_; uint8_t v_isSharedCheck_1581_; 
lean_dec_ref(v_localInstances_1545_);
lean_dec_ref(v_lctx_1544_);
lean_dec(v___y_1542_);
lean_dec_ref(v___y_1541_);
lean_dec(v___y_1540_);
lean_dec_ref(v___y_1539_);
lean_dec(v_varName_x3f_1538_);
lean_dec_ref(v_e_1537_);
lean_dec(v_mvarId_1536_);
v_a_1574_ = lean_ctor_get(v___x_1547_, 0);
v_isSharedCheck_1581_ = !lean_is_exclusive(v___x_1547_);
if (v_isSharedCheck_1581_ == 0)
{
v___x_1576_ = v___x_1547_;
v_isShared_1577_ = v_isSharedCheck_1581_;
goto v_resetjp_1575_;
}
else
{
lean_inc(v_a_1574_);
lean_dec(v___x_1547_);
v___x_1576_ = lean_box(0);
v_isShared_1577_ = v_isSharedCheck_1581_;
goto v_resetjp_1575_;
}
v_resetjp_1575_:
{
lean_object* v___x_1579_; 
if (v_isShared_1577_ == 0)
{
v___x_1579_ = v___x_1576_;
goto v_reusejp_1578_;
}
else
{
lean_object* v_reuseFailAlloc_1580_; 
v_reuseFailAlloc_1580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1580_, 0, v_a_1574_);
v___x_1579_ = v_reuseFailAlloc_1580_;
goto v_reusejp_1578_;
}
v_reusejp_1578_:
{
return v___x_1579_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeIndices_x27___lam__0___boxed(lean_object* v_mvarId_1582_, lean_object* v_e_1583_, lean_object* v_varName_x3f_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_){
_start:
{
lean_object* v_res_1590_; 
v_res_1590_ = l_Lean_Meta_generalizeIndices_x27___lam__0(v_mvarId_1582_, v_e_1583_, v_varName_x3f_1584_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_);
return v_res_1590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeIndices_x27(lean_object* v_mvarId_1591_, lean_object* v_e_1592_, lean_object* v_varName_x3f_1593_, lean_object* v_a_1594_, lean_object* v_a_1595_, lean_object* v_a_1596_, lean_object* v_a_1597_){
_start:
{
lean_object* v___f_1599_; lean_object* v___x_1600_; 
lean_inc(v_mvarId_1591_);
v___f_1599_ = lean_alloc_closure((void*)(l_Lean_Meta_generalizeIndices_x27___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1599_, 0, v_mvarId_1591_);
lean_closure_set(v___f_1599_, 1, v_e_1592_);
lean_closure_set(v___f_1599_, 2, v_varName_x3f_1593_);
v___x_1600_ = l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2___redArg(v_mvarId_1591_, v___f_1599_, v_a_1594_, v_a_1595_, v_a_1596_, v_a_1597_);
return v___x_1600_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeIndices_x27___boxed(lean_object* v_mvarId_1601_, lean_object* v_e_1602_, lean_object* v_varName_x3f_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_, lean_object* v_a_1607_, lean_object* v_a_1608_){
_start:
{
lean_object* v_res_1609_; 
v_res_1609_ = l_Lean_Meta_generalizeIndices_x27(v_mvarId_1601_, v_e_1602_, v_varName_x3f_1603_, v_a_1604_, v_a_1605_, v_a_1606_, v_a_1607_);
lean_dec(v_a_1607_);
lean_dec_ref(v_a_1606_);
lean_dec(v_a_1605_);
lean_dec_ref(v_a_1604_);
return v_res_1609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeIndices___lam__0(lean_object* v_fvarId_1610_, lean_object* v_mvarId_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_){
_start:
{
lean_object* v___x_1617_; 
v___x_1617_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_1610_, v___y_1612_, v___y_1614_, v___y_1615_);
if (lean_obj_tag(v___x_1617_) == 0)
{
lean_object* v_a_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; 
v_a_1618_ = lean_ctor_get(v___x_1617_, 0);
lean_inc_n(v_a_1618_, 2);
lean_dec_ref_known(v___x_1617_, 1);
v___x_1619_ = l_Lean_LocalDecl_toExpr(v_a_1618_);
v___x_1620_ = l_Lean_LocalDecl_userName(v_a_1618_);
lean_dec(v_a_1618_);
v___x_1621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1621_, 0, v___x_1620_);
v___x_1622_ = l_Lean_Meta_generalizeIndices_x27(v_mvarId_1611_, v___x_1619_, v___x_1621_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_);
return v___x_1622_;
}
else
{
lean_object* v_a_1623_; lean_object* v___x_1625_; uint8_t v_isShared_1626_; uint8_t v_isSharedCheck_1630_; 
lean_dec(v_mvarId_1611_);
v_a_1623_ = lean_ctor_get(v___x_1617_, 0);
v_isSharedCheck_1630_ = !lean_is_exclusive(v___x_1617_);
if (v_isSharedCheck_1630_ == 0)
{
v___x_1625_ = v___x_1617_;
v_isShared_1626_ = v_isSharedCheck_1630_;
goto v_resetjp_1624_;
}
else
{
lean_inc(v_a_1623_);
lean_dec(v___x_1617_);
v___x_1625_ = lean_box(0);
v_isShared_1626_ = v_isSharedCheck_1630_;
goto v_resetjp_1624_;
}
v_resetjp_1624_:
{
lean_object* v___x_1628_; 
if (v_isShared_1626_ == 0)
{
v___x_1628_ = v___x_1625_;
goto v_reusejp_1627_;
}
else
{
lean_object* v_reuseFailAlloc_1629_; 
v_reuseFailAlloc_1629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1629_, 0, v_a_1623_);
v___x_1628_ = v_reuseFailAlloc_1629_;
goto v_reusejp_1627_;
}
v_reusejp_1627_:
{
return v___x_1628_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeIndices___lam__0___boxed(lean_object* v_fvarId_1631_, lean_object* v_mvarId_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_){
_start:
{
lean_object* v_res_1638_; 
v_res_1638_ = l_Lean_Meta_generalizeIndices___lam__0(v_fvarId_1631_, v_mvarId_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_);
lean_dec(v___y_1636_);
lean_dec_ref(v___y_1635_);
lean_dec(v___y_1634_);
lean_dec_ref(v___y_1633_);
return v_res_1638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeIndices(lean_object* v_mvarId_1639_, lean_object* v_fvarId_1640_, lean_object* v_a_1641_, lean_object* v_a_1642_, lean_object* v_a_1643_, lean_object* v_a_1644_){
_start:
{
lean_object* v___f_1646_; lean_object* v___x_1647_; 
lean_inc(v_mvarId_1639_);
v___f_1646_ = lean_alloc_closure((void*)(l_Lean_Meta_generalizeIndices___lam__0___boxed), 7, 2);
lean_closure_set(v___f_1646_, 0, v_fvarId_1640_);
lean_closure_set(v___f_1646_, 1, v_mvarId_1639_);
v___x_1647_ = l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2___redArg(v_mvarId_1639_, v___f_1646_, v_a_1641_, v_a_1642_, v_a_1643_, v_a_1644_);
return v___x_1647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeIndices___boxed(lean_object* v_mvarId_1648_, lean_object* v_fvarId_1649_, lean_object* v_a_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_){
_start:
{
lean_object* v_res_1655_; 
v_res_1655_ = l_Lean_Meta_generalizeIndices(v_mvarId_1648_, v_fvarId_1649_, v_a_1650_, v_a_1651_, v_a_1652_, v_a_1653_);
lean_dec(v_a_1653_);
lean_dec_ref(v_a_1652_);
lean_dec(v_a_1651_);
lean_dec_ref(v_a_1650_);
return v_res_1655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0___redArg(lean_object* v___x_1657_, lean_object* v_a_1658_, lean_object* v_x_1659_, lean_object* v_x_1660_, lean_object* v_x_1661_, lean_object* v___y_1662_){
_start:
{
if (lean_obj_tag(v_x_1659_) == 5)
{
lean_object* v_fn_1667_; lean_object* v_arg_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; 
v_fn_1667_ = lean_ctor_get(v_x_1659_, 0);
lean_inc_ref(v_fn_1667_);
v_arg_1668_ = lean_ctor_get(v_x_1659_, 1);
lean_inc_ref(v_arg_1668_);
lean_dec_ref_known(v_x_1659_, 2);
v___x_1669_ = lean_array_set(v_x_1660_, v_x_1661_, v_arg_1668_);
v___x_1670_ = lean_unsigned_to_nat(1u);
v___x_1671_ = lean_nat_sub(v_x_1661_, v___x_1670_);
lean_dec(v_x_1661_);
v_x_1659_ = v_fn_1667_;
v_x_1660_ = v___x_1669_;
v_x_1661_ = v___x_1671_;
goto _start;
}
else
{
lean_dec(v_x_1661_);
if (lean_obj_tag(v_x_1659_) == 4)
{
lean_object* v_declName_1673_; uint8_t v___x_1674_; uint8_t v___x_1675_; lean_object* v___x_1676_; lean_object* v_env_1677_; lean_object* v___x_1678_; 
v_declName_1673_ = lean_ctor_get(v_x_1659_, 0);
v___x_1674_ = 0;
v___x_1675_ = 1;
v___x_1676_ = lean_st_ref_get(v___y_1662_);
v_env_1677_ = lean_ctor_get(v___x_1676_, 0);
lean_inc_ref(v_env_1677_);
lean_dec(v___x_1676_);
lean_inc(v_declName_1673_);
v___x_1678_ = l_Lean_Environment_find_x3f(v_env_1677_, v_declName_1673_, v___x_1674_);
if (lean_obj_tag(v___x_1678_) == 0)
{
lean_dec_ref_known(v_x_1659_, 2);
lean_dec_ref(v_x_1660_);
lean_dec_ref(v_a_1658_);
lean_dec_ref(v___x_1657_);
goto v___jp_1664_;
}
else
{
lean_object* v_val_1679_; lean_object* v___x_1681_; uint8_t v_isShared_1682_; uint8_t v_isSharedCheck_1717_; 
v_val_1679_ = lean_ctor_get(v___x_1678_, 0);
v_isSharedCheck_1717_ = !lean_is_exclusive(v___x_1678_);
if (v_isSharedCheck_1717_ == 0)
{
v___x_1681_ = v___x_1678_;
v_isShared_1682_ = v_isSharedCheck_1717_;
goto v_resetjp_1680_;
}
else
{
lean_inc(v_val_1679_);
lean_dec(v___x_1678_);
v___x_1681_ = lean_box(0);
v_isShared_1682_ = v_isSharedCheck_1717_;
goto v_resetjp_1680_;
}
v_resetjp_1680_:
{
if (lean_obj_tag(v_val_1679_) == 5)
{
lean_object* v_val_1683_; lean_object* v___x_1685_; uint8_t v_isShared_1686_; uint8_t v_isSharedCheck_1716_; 
v_val_1683_ = lean_ctor_get(v_val_1679_, 0);
v_isSharedCheck_1716_ = !lean_is_exclusive(v_val_1679_);
if (v_isSharedCheck_1716_ == 0)
{
v___x_1685_ = v_val_1679_;
v_isShared_1686_ = v_isSharedCheck_1716_;
goto v_resetjp_1684_;
}
else
{
lean_inc(v_val_1683_);
lean_dec(v_val_1679_);
v___x_1685_ = lean_box(0);
v_isShared_1686_ = v_isSharedCheck_1716_;
goto v_resetjp_1684_;
}
v_resetjp_1684_:
{
lean_object* v_toConstantVal_1687_; lean_object* v_numParams_1688_; lean_object* v_numIndices_1689_; lean_object* v_ctors_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; uint8_t v___x_1693_; 
v_toConstantVal_1687_ = lean_ctor_get(v_val_1683_, 0);
v_numParams_1688_ = lean_ctor_get(v_val_1683_, 1);
v_numIndices_1689_ = lean_ctor_get(v_val_1683_, 2);
v_ctors_1690_ = lean_ctor_get(v_val_1683_, 4);
v___x_1691_ = lean_array_get_size(v_x_1660_);
v___x_1692_ = lean_nat_add(v_numIndices_1689_, v_numParams_1688_);
v___x_1693_ = lean_nat_dec_eq(v___x_1691_, v___x_1692_);
lean_dec(v___x_1692_);
if (v___x_1693_ == 0)
{
lean_object* v___x_1694_; lean_object* v___x_1696_; 
lean_dec_ref(v_val_1683_);
lean_del_object(v___x_1681_);
lean_dec_ref_known(v_x_1659_, 2);
lean_dec_ref(v_x_1660_);
lean_dec_ref(v_a_1658_);
lean_dec_ref(v___x_1657_);
v___x_1694_ = lean_box(0);
if (v_isShared_1686_ == 0)
{
lean_ctor_set_tag(v___x_1685_, 0);
lean_ctor_set(v___x_1685_, 0, v___x_1694_);
v___x_1696_ = v___x_1685_;
goto v_reusejp_1695_;
}
else
{
lean_object* v_reuseFailAlloc_1697_; 
v_reuseFailAlloc_1697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1697_, 0, v___x_1694_);
v___x_1696_ = v_reuseFailAlloc_1697_;
goto v_reusejp_1695_;
}
v_reusejp_1695_:
{
return v___x_1696_;
}
}
else
{
lean_object* v_name_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; uint8_t v___x_1701_; 
v_name_1698_ = lean_ctor_get(v_toConstantVal_1687_, 0);
v___x_1699_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0___redArg___closed__0));
lean_inc(v_name_1698_);
v___x_1700_ = l_Lean_Name_str___override(v_name_1698_, v___x_1699_);
v___x_1701_ = l_Lean_Environment_contains(v___x_1657_, v___x_1700_, v___x_1675_);
if (v___x_1701_ == 0)
{
lean_object* v___x_1702_; lean_object* v___x_1704_; 
lean_dec_ref(v_val_1683_);
lean_del_object(v___x_1681_);
lean_dec_ref_known(v_x_1659_, 2);
lean_dec_ref(v_x_1660_);
lean_dec_ref(v_a_1658_);
v___x_1702_ = lean_box(0);
if (v_isShared_1686_ == 0)
{
lean_ctor_set_tag(v___x_1685_, 0);
lean_ctor_set(v___x_1685_, 0, v___x_1702_);
v___x_1704_ = v___x_1685_;
goto v_reusejp_1703_;
}
else
{
lean_object* v_reuseFailAlloc_1705_; 
v_reuseFailAlloc_1705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1705_, 0, v___x_1702_);
v___x_1704_ = v_reuseFailAlloc_1705_;
goto v_reusejp_1703_;
}
v_reusejp_1703_:
{
return v___x_1704_;
}
}
else
{
lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1711_; 
v___x_1706_ = l_List_lengthTR___redArg(v_ctors_1690_);
v___x_1707_ = lean_nat_sub(v___x_1691_, v_numIndices_1689_);
v___x_1708_ = l_Array_extract___redArg(v_x_1660_, v___x_1707_, v___x_1691_);
v___x_1709_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1709_, 0, v_val_1683_);
lean_ctor_set(v___x_1709_, 1, v___x_1706_);
lean_ctor_set(v___x_1709_, 2, v_a_1658_);
lean_ctor_set(v___x_1709_, 3, v_x_1659_);
lean_ctor_set(v___x_1709_, 4, v_x_1660_);
lean_ctor_set(v___x_1709_, 5, v___x_1708_);
if (v_isShared_1682_ == 0)
{
lean_ctor_set(v___x_1681_, 0, v___x_1709_);
v___x_1711_ = v___x_1681_;
goto v_reusejp_1710_;
}
else
{
lean_object* v_reuseFailAlloc_1715_; 
v_reuseFailAlloc_1715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1715_, 0, v___x_1709_);
v___x_1711_ = v_reuseFailAlloc_1715_;
goto v_reusejp_1710_;
}
v_reusejp_1710_:
{
lean_object* v___x_1713_; 
if (v_isShared_1686_ == 0)
{
lean_ctor_set_tag(v___x_1685_, 0);
lean_ctor_set(v___x_1685_, 0, v___x_1711_);
v___x_1713_ = v___x_1685_;
goto v_reusejp_1712_;
}
else
{
lean_object* v_reuseFailAlloc_1714_; 
v_reuseFailAlloc_1714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1714_, 0, v___x_1711_);
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
else
{
lean_del_object(v___x_1681_);
lean_dec(v_val_1679_);
lean_dec_ref_known(v_x_1659_, 2);
lean_dec_ref(v_x_1660_);
lean_dec_ref(v_a_1658_);
lean_dec_ref(v___x_1657_);
goto v___jp_1664_;
}
}
}
}
else
{
lean_dec_ref(v_x_1660_);
lean_dec_ref(v_x_1659_);
lean_dec_ref(v_a_1658_);
lean_dec_ref(v___x_1657_);
goto v___jp_1664_;
}
}
v___jp_1664_:
{
lean_object* v___x_1665_; lean_object* v___x_1666_; 
v___x_1665_ = lean_box(0);
v___x_1666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1666_, 0, v___x_1665_);
return v___x_1666_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0___redArg___boxed(lean_object* v___x_1718_, lean_object* v_a_1719_, lean_object* v_x_1720_, lean_object* v_x_1721_, lean_object* v_x_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_){
_start:
{
lean_object* v_res_1725_; 
v_res_1725_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0___redArg(v___x_1718_, v_a_1719_, v_x_1720_, v_x_1721_, v_x_1722_, v___y_1723_);
lean_dec(v___y_1723_);
return v_res_1725_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f(lean_object* v_majorFVarId_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_){
_start:
{
lean_object* v___x_1732_; lean_object* v_env_1736_; lean_object* v___x_1737_; uint8_t v___x_1738_; uint8_t v___x_1739_; 
v___x_1732_ = lean_st_ref_get(v_a_1730_);
v_env_1736_ = lean_ctor_get(v___x_1732_, 0);
lean_inc_ref_n(v_env_1736_, 2);
lean_dec(v___x_1732_);
v___x_1737_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__5));
v___x_1738_ = 1;
v___x_1739_ = l_Lean_Environment_contains(v_env_1736_, v___x_1737_, v___x_1738_);
if (v___x_1739_ == 0)
{
lean_dec_ref(v_env_1736_);
lean_dec(v_majorFVarId_1726_);
goto v___jp_1733_;
}
else
{
lean_object* v___x_1740_; uint8_t v___x_1741_; 
v___x_1740_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__1));
lean_inc_ref(v_env_1736_);
v___x_1741_ = l_Lean_Environment_contains(v_env_1736_, v___x_1740_, v___x_1739_);
if (v___x_1741_ == 0)
{
lean_dec_ref(v_env_1736_);
lean_dec(v_majorFVarId_1726_);
goto v___jp_1733_;
}
else
{
lean_object* v___x_1742_; 
v___x_1742_ = l_Lean_FVarId_getDecl___redArg(v_majorFVarId_1726_, v_a_1727_, v_a_1729_, v_a_1730_);
if (lean_obj_tag(v___x_1742_) == 0)
{
lean_object* v_a_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; 
v_a_1743_ = lean_ctor_get(v___x_1742_, 0);
lean_inc(v_a_1743_);
lean_dec_ref_known(v___x_1742_, 1);
v___x_1744_ = l_Lean_LocalDecl_type(v_a_1743_);
lean_inc(v_a_1730_);
lean_inc_ref(v_a_1729_);
lean_inc(v_a_1728_);
lean_inc_ref(v_a_1727_);
v___x_1745_ = lean_whnf(v___x_1744_, v_a_1727_, v_a_1728_, v_a_1729_, v_a_1730_);
if (lean_obj_tag(v___x_1745_) == 0)
{
lean_object* v_a_1746_; lean_object* v_dummy_1747_; lean_object* v_nargs_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; 
v_a_1746_ = lean_ctor_get(v___x_1745_, 0);
lean_inc(v_a_1746_);
lean_dec_ref_known(v___x_1745_, 1);
v_dummy_1747_ = lean_obj_once(&l_Lean_Meta_getInductiveUniverseAndParams___closed__0, &l_Lean_Meta_getInductiveUniverseAndParams___closed__0_once, _init_l_Lean_Meta_getInductiveUniverseAndParams___closed__0);
v_nargs_1748_ = l_Lean_Expr_getAppNumArgs(v_a_1746_);
lean_inc(v_nargs_1748_);
v___x_1749_ = lean_mk_array(v_nargs_1748_, v_dummy_1747_);
v___x_1750_ = lean_unsigned_to_nat(1u);
v___x_1751_ = lean_nat_sub(v_nargs_1748_, v___x_1750_);
lean_dec(v_nargs_1748_);
v___x_1752_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0___redArg(v_env_1736_, v_a_1743_, v_a_1746_, v___x_1749_, v___x_1751_, v_a_1730_);
return v___x_1752_;
}
else
{
lean_object* v_a_1753_; lean_object* v___x_1755_; uint8_t v_isShared_1756_; uint8_t v_isSharedCheck_1760_; 
lean_dec(v_a_1743_);
lean_dec_ref(v_env_1736_);
v_a_1753_ = lean_ctor_get(v___x_1745_, 0);
v_isSharedCheck_1760_ = !lean_is_exclusive(v___x_1745_);
if (v_isSharedCheck_1760_ == 0)
{
v___x_1755_ = v___x_1745_;
v_isShared_1756_ = v_isSharedCheck_1760_;
goto v_resetjp_1754_;
}
else
{
lean_inc(v_a_1753_);
lean_dec(v___x_1745_);
v___x_1755_ = lean_box(0);
v_isShared_1756_ = v_isSharedCheck_1760_;
goto v_resetjp_1754_;
}
v_resetjp_1754_:
{
lean_object* v___x_1758_; 
if (v_isShared_1756_ == 0)
{
v___x_1758_ = v___x_1755_;
goto v_reusejp_1757_;
}
else
{
lean_object* v_reuseFailAlloc_1759_; 
v_reuseFailAlloc_1759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1759_, 0, v_a_1753_);
v___x_1758_ = v_reuseFailAlloc_1759_;
goto v_reusejp_1757_;
}
v_reusejp_1757_:
{
return v___x_1758_;
}
}
}
}
else
{
lean_object* v_a_1761_; lean_object* v___x_1763_; uint8_t v_isShared_1764_; uint8_t v_isSharedCheck_1768_; 
lean_dec_ref(v_env_1736_);
v_a_1761_ = lean_ctor_get(v___x_1742_, 0);
v_isSharedCheck_1768_ = !lean_is_exclusive(v___x_1742_);
if (v_isSharedCheck_1768_ == 0)
{
v___x_1763_ = v___x_1742_;
v_isShared_1764_ = v_isSharedCheck_1768_;
goto v_resetjp_1762_;
}
else
{
lean_inc(v_a_1761_);
lean_dec(v___x_1742_);
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
v___jp_1733_:
{
lean_object* v___x_1734_; lean_object* v___x_1735_; 
v___x_1734_ = lean_box(0);
v___x_1735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1735_, 0, v___x_1734_);
return v___x_1735_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f___boxed(lean_object* v_majorFVarId_1769_, lean_object* v_a_1770_, lean_object* v_a_1771_, lean_object* v_a_1772_, lean_object* v_a_1773_, lean_object* v_a_1774_){
_start:
{
lean_object* v_res_1775_; 
v_res_1775_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f(v_majorFVarId_1769_, v_a_1770_, v_a_1771_, v_a_1772_, v_a_1773_);
lean_dec(v_a_1773_);
lean_dec_ref(v_a_1772_);
lean_dec(v_a_1771_);
lean_dec_ref(v_a_1770_);
return v_res_1775_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0(lean_object* v___x_1776_, lean_object* v_a_1777_, lean_object* v_x_1778_, lean_object* v_x_1779_, lean_object* v_x_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_){
_start:
{
lean_object* v___x_1786_; 
v___x_1786_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0___redArg(v___x_1776_, v_a_1777_, v_x_1778_, v_x_1779_, v_x_1780_, v___y_1784_);
return v___x_1786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0___boxed(lean_object* v___x_1787_, lean_object* v_a_1788_, lean_object* v_x_1789_, lean_object* v_x_1790_, lean_object* v_x_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_){
_start:
{
lean_object* v_res_1797_; 
v_res_1797_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0(v___x_1787_, v_a_1788_, v_x_1789_, v_x_1790_, v_x_1791_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_);
lean_dec(v___y_1795_);
lean_dec_ref(v___y_1794_);
lean_dec(v___y_1793_);
lean_dec_ref(v___y_1792_);
return v_res_1797_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0___redArg(lean_object* v___x_1798_, lean_object* v_i_1799_, lean_object* v_n_1800_, lean_object* v_i_1801_){
_start:
{
lean_object* v_zero_1802_; uint8_t v_isZero_1803_; 
v_zero_1802_ = lean_unsigned_to_nat(0u);
v_isZero_1803_ = lean_nat_dec_eq(v_i_1801_, v_zero_1802_);
if (v_isZero_1803_ == 1)
{
uint8_t v___x_1804_; 
lean_dec(v_i_1801_);
v___x_1804_ = 0;
return v___x_1804_;
}
else
{
lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; uint8_t v___x_1808_; 
v___x_1805_ = lean_nat_sub(v_n_1800_, v_i_1801_);
v___x_1806_ = lean_array_fget_borrowed(v___x_1798_, v_i_1799_);
v___x_1807_ = lean_array_fget_borrowed(v___x_1798_, v___x_1805_);
lean_dec(v___x_1805_);
v___x_1808_ = lean_expr_eqv(v___x_1806_, v___x_1807_);
if (v___x_1808_ == 0)
{
lean_object* v_one_1809_; lean_object* v_n_1810_; 
v_one_1809_ = lean_unsigned_to_nat(1u);
v_n_1810_ = lean_nat_sub(v_i_1801_, v_one_1809_);
lean_dec(v_i_1801_);
v_i_1801_ = v_n_1810_;
goto _start;
}
else
{
lean_dec(v_i_1801_);
return v___x_1808_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0___redArg___boxed(lean_object* v___x_1812_, lean_object* v_i_1813_, lean_object* v_n_1814_, lean_object* v_i_1815_){
_start:
{
uint8_t v_res_1816_; lean_object* v_r_1817_; 
v_res_1816_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0___redArg(v___x_1812_, v_i_1813_, v_n_1814_, v_i_1815_);
lean_dec(v_n_1814_);
lean_dec(v_i_1813_);
lean_dec_ref(v___x_1812_);
v_r_1817_ = lean_box(v_res_1816_);
return v_r_1817_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1___redArg(lean_object* v___x_1818_, lean_object* v_n_1819_, lean_object* v_i_1820_){
_start:
{
lean_object* v_zero_1821_; uint8_t v_isZero_1822_; 
v_zero_1821_ = lean_unsigned_to_nat(0u);
v_isZero_1822_ = lean_nat_dec_eq(v_i_1820_, v_zero_1821_);
if (v_isZero_1822_ == 1)
{
uint8_t v___x_1823_; 
lean_dec(v_i_1820_);
v___x_1823_ = 0;
return v___x_1823_;
}
else
{
lean_object* v___x_1824_; uint8_t v___x_1825_; 
v___x_1824_ = lean_nat_sub(v_n_1819_, v_i_1820_);
lean_inc(v___x_1824_);
v___x_1825_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0___redArg(v___x_1818_, v___x_1824_, v___x_1824_, v___x_1824_);
lean_dec(v___x_1824_);
if (v___x_1825_ == 0)
{
lean_object* v_one_1826_; lean_object* v_n_1827_; 
v_one_1826_ = lean_unsigned_to_nat(1u);
v_n_1827_ = lean_nat_sub(v_i_1820_, v_one_1826_);
lean_dec(v_i_1820_);
v_i_1820_ = v_n_1827_;
goto _start;
}
else
{
lean_dec(v_i_1820_);
return v___x_1825_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1___redArg___boxed(lean_object* v___x_1829_, lean_object* v_n_1830_, lean_object* v_i_1831_){
_start:
{
uint8_t v_res_1832_; lean_object* v_r_1833_; 
v_res_1832_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1___redArg(v___x_1829_, v_n_1830_, v_i_1831_);
lean_dec(v_n_1830_);
lean_dec_ref(v___x_1829_);
v_r_1833_ = lean_box(v_res_1832_);
return v_r_1833_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5(lean_object* v___x_1834_, lean_object* v_as_1835_, size_t v_i_1836_, size_t v_stop_1837_){
_start:
{
uint8_t v___x_1838_; 
v___x_1838_ = lean_usize_dec_eq(v_i_1836_, v_stop_1837_);
if (v___x_1838_ == 0)
{
uint8_t v___x_1839_; lean_object* v___x_1840_; uint8_t v___x_1841_; 
v___x_1839_ = 1;
v___x_1840_ = lean_array_uget_borrowed(v_as_1835_, v_i_1836_);
v___x_1841_ = l_Lean_Expr_isFVar(v___x_1840_);
if (v___x_1841_ == 0)
{
return v___x_1839_;
}
else
{
lean_object* v___x_1842_; uint8_t v___x_1843_; 
v___x_1842_ = lean_unsigned_to_nat(0u);
v___x_1843_ = lean_nat_dec_eq(v___x_1834_, v___x_1842_);
if (v___x_1843_ == 0)
{
size_t v___x_1844_; size_t v___x_1845_; 
v___x_1844_ = ((size_t)1ULL);
v___x_1845_ = lean_usize_add(v_i_1836_, v___x_1844_);
v_i_1836_ = v___x_1845_;
goto _start;
}
else
{
return v___x_1839_;
}
}
}
else
{
uint8_t v___x_1847_; 
v___x_1847_ = 0;
return v___x_1847_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5___boxed(lean_object* v___x_1848_, lean_object* v_as_1849_, lean_object* v_i_1850_, lean_object* v_stop_1851_){
_start:
{
size_t v_i_boxed_1852_; size_t v_stop_boxed_1853_; uint8_t v_res_1854_; lean_object* v_r_1855_; 
v_i_boxed_1852_ = lean_unbox_usize(v_i_1850_);
lean_dec(v_i_1850_);
v_stop_boxed_1853_ = lean_unbox_usize(v_stop_1851_);
lean_dec(v_stop_1851_);
v_res_1854_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5(v___x_1848_, v_as_1849_, v_i_boxed_1852_, v_stop_boxed_1853_);
lean_dec_ref(v_as_1849_);
lean_dec(v___x_1848_);
v_r_1855_ = lean_box(v_res_1854_);
return v_r_1855_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__2(lean_object* v_fvarId_1856_, uint8_t v___x_1857_, lean_object* v_as_1858_, size_t v_i_1859_, size_t v_stop_1860_){
_start:
{
uint8_t v___x_1861_; 
v___x_1861_ = lean_usize_dec_eq(v_i_1859_, v_stop_1860_);
if (v___x_1861_ == 0)
{
uint8_t v___x_1862_; uint8_t v___y_1864_; lean_object* v___x_1868_; lean_object* v___x_1869_; uint8_t v___x_1870_; 
v___x_1862_ = 1;
v___x_1868_ = lean_array_uget_borrowed(v_as_1858_, v_i_1859_);
v___x_1869_ = l_Lean_Expr_fvarId_x21(v___x_1868_);
v___x_1870_ = l_Lean_instBEqFVarId_beq(v___x_1869_, v_fvarId_1856_);
lean_dec(v___x_1869_);
if (v___x_1870_ == 0)
{
v___y_1864_ = v___x_1857_;
goto v___jp_1863_;
}
else
{
if (v___x_1857_ == 0)
{
v___y_1864_ = v___x_1870_;
goto v___jp_1863_;
}
else
{
return v___x_1862_;
}
}
v___jp_1863_:
{
if (v___y_1864_ == 0)
{
size_t v___x_1865_; size_t v___x_1866_; 
v___x_1865_ = ((size_t)1ULL);
v___x_1866_ = lean_usize_add(v_i_1859_, v___x_1865_);
v_i_1859_ = v___x_1866_;
goto _start;
}
else
{
return v___x_1862_;
}
}
}
else
{
uint8_t v___x_1871_; 
v___x_1871_ = 0;
return v___x_1871_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__2___boxed(lean_object* v_fvarId_1872_, lean_object* v___x_1873_, lean_object* v_as_1874_, lean_object* v_i_1875_, lean_object* v_stop_1876_){
_start:
{
uint8_t v___x_7575__boxed_1877_; size_t v_i_boxed_1878_; size_t v_stop_boxed_1879_; uint8_t v_res_1880_; lean_object* v_r_1881_; 
v___x_7575__boxed_1877_ = lean_unbox(v___x_1873_);
v_i_boxed_1878_ = lean_unbox_usize(v_i_1875_);
lean_dec(v_i_1875_);
v_stop_boxed_1879_ = lean_unbox_usize(v_stop_1876_);
lean_dec(v_stop_1876_);
v_res_1880_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__2(v_fvarId_1872_, v___x_7575__boxed_1877_, v_as_1874_, v_i_boxed_1878_, v_stop_boxed_1879_);
lean_dec_ref(v_as_1874_);
lean_dec(v_fvarId_1872_);
v_r_1881_ = lean_box(v_res_1880_);
return v_r_1881_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___lam__1(lean_object* v___x_1882_, lean_object* v___x_1883_, uint8_t v___x_1884_, lean_object* v___x_1885_, lean_object* v_fvarId_1886_){
_start:
{
uint8_t v___x_1887_; lean_object* v___y_1889_; 
v___x_1887_ = lean_nat_dec_lt(v___x_1882_, v___x_1883_);
if (v___x_1887_ == 0)
{
uint8_t v___x_1894_; 
lean_dec(v___x_1883_);
v___x_1894_ = 1;
return v___x_1894_;
}
else
{
lean_object* v___x_1895_; uint8_t v___x_1896_; 
v___x_1895_ = lean_array_get_size(v___x_1885_);
v___x_1896_ = lean_nat_dec_le(v___x_1883_, v___x_1895_);
if (v___x_1896_ == 0)
{
lean_dec(v___x_1883_);
v___y_1889_ = v___x_1895_;
goto v___jp_1888_;
}
else
{
v___y_1889_ = v___x_1883_;
goto v___jp_1888_;
}
}
v___jp_1888_:
{
uint8_t v___x_1890_; 
v___x_1890_ = lean_nat_dec_lt(v___x_1882_, v___y_1889_);
if (v___x_1890_ == 0)
{
lean_dec(v___y_1889_);
return v___x_1887_;
}
else
{
size_t v___x_1891_; size_t v___x_1892_; uint8_t v___x_1893_; 
v___x_1891_ = ((size_t)0ULL);
v___x_1892_ = lean_usize_of_nat(v___y_1889_);
lean_dec(v___y_1889_);
v___x_1893_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__2(v_fvarId_1886_, v___x_1884_, v___x_1885_, v___x_1891_, v___x_1892_);
if (v___x_1893_ == 0)
{
return v___x_1890_;
}
else
{
return v___x_1884_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___lam__1___boxed(lean_object* v___x_1897_, lean_object* v___x_1898_, lean_object* v___x_1899_, lean_object* v___x_1900_, lean_object* v_fvarId_1901_){
_start:
{
uint8_t v___x_7602__boxed_1902_; uint8_t v_res_1903_; lean_object* v_r_1904_; 
v___x_7602__boxed_1902_ = lean_unbox(v___x_1899_);
v_res_1903_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___lam__1(v___x_1897_, v___x_1898_, v___x_7602__boxed_1902_, v___x_1900_, v_fvarId_1901_);
lean_dec(v_fvarId_1901_);
lean_dec_ref(v___x_1900_);
lean_dec(v___x_1897_);
v_r_1904_ = lean_box(v_res_1903_);
return v_r_1904_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__3(lean_object* v___x_1905_, lean_object* v_as_1906_, size_t v_i_1907_, size_t v_stop_1908_){
_start:
{
uint8_t v___x_1909_; 
v___x_1909_ = lean_usize_dec_eq(v_i_1907_, v_stop_1908_);
if (v___x_1909_ == 0)
{
lean_object* v___x_1910_; lean_object* v___x_1911_; uint8_t v___x_1912_; 
v___x_1910_ = lean_array_uget_borrowed(v_as_1906_, v_i_1907_);
v___x_1911_ = l_Lean_Expr_fvarId_x21(v___x_1910_);
v___x_1912_ = l_Lean_instBEqFVarId_beq(v___x_1905_, v___x_1911_);
lean_dec(v___x_1911_);
if (v___x_1912_ == 0)
{
size_t v___x_1913_; size_t v___x_1914_; 
v___x_1913_ = ((size_t)1ULL);
v___x_1914_ = lean_usize_add(v_i_1907_, v___x_1913_);
v_i_1907_ = v___x_1914_;
goto _start;
}
else
{
return v___x_1912_;
}
}
else
{
uint8_t v___x_1916_; 
v___x_1916_ = 0;
return v___x_1916_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__3___boxed(lean_object* v___x_1917_, lean_object* v_as_1918_, lean_object* v_i_1919_, lean_object* v_stop_1920_){
_start:
{
size_t v_i_boxed_1921_; size_t v_stop_boxed_1922_; uint8_t v_res_1923_; lean_object* v_r_1924_; 
v_i_boxed_1921_ = lean_unbox_usize(v_i_1919_);
lean_dec(v_i_1919_);
v_stop_boxed_1922_ = lean_unbox_usize(v_stop_1920_);
lean_dec(v_stop_1920_);
v_res_1923_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__3(v___x_1917_, v_as_1918_, v_i_boxed_1921_, v_stop_boxed_1922_);
lean_dec_ref(v_as_1918_);
lean_dec(v___x_1917_);
v_r_1924_ = lean_box(v_res_1923_);
return v_r_1924_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___lam__0(uint8_t v___x_1925_, lean_object* v_x_1926_){
_start:
{
return v___x_1925_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___lam__0___boxed(lean_object* v___x_1927_, lean_object* v_x_1928_){
_start:
{
uint8_t v___x_7651__boxed_1929_; uint8_t v_res_1930_; lean_object* v_r_1931_; 
v___x_7651__boxed_1929_ = lean_unbox(v___x_1927_);
v_res_1930_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___lam__0(v___x_7651__boxed_1929_, v_x_1928_);
lean_dec(v_x_1928_);
v_r_1931_ = lean_box(v_res_1930_);
return v_r_1931_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; 
v___x_1932_ = lean_box(0);
v___x_1933_ = lean_unsigned_to_nat(16u);
v___x_1934_ = lean_mk_array(v___x_1933_, v___x_1932_);
return v___x_1934_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; 
v___x_1935_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__0);
v___x_1936_ = lean_unsigned_to_nat(0u);
v___x_1937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1937_, 0, v___x_1936_);
lean_ctor_set(v___x_1937_, 1, v___x_1935_);
return v___x_1937_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg(uint8_t v___x_1938_, lean_object* v___x_1939_, lean_object* v___x_1940_, lean_object* v_ctx_1941_, lean_object* v_as_1942_, size_t v_i_1943_, size_t v_stop_1944_, lean_object* v___y_1945_){
_start:
{
uint8_t v___x_1947_; 
v___x_1947_ = lean_usize_dec_eq(v_i_1943_, v_stop_1944_);
if (v___x_1947_ == 0)
{
uint8_t v___x_1948_; uint8_t v_a_1950_; uint8_t v_a_1957_; uint8_t v_fst_1961_; lean_object* v_mctx_1962_; lean_object* v___y_1978_; uint8_t v_fst_1984_; lean_object* v_snd_1985_; lean_object* v___y_2002_; uint8_t v_fst_2007_; lean_object* v_mctx_2008_; lean_object* v___y_2024_; lean_object* v___x_2029_; 
v___x_1948_ = 1;
v___x_2029_ = lean_array_uget_borrowed(v_as_1942_, v_i_1943_);
if (lean_obj_tag(v___x_2029_) == 0)
{
v_a_1950_ = v___x_1938_;
goto v___jp_1949_;
}
else
{
lean_object* v_val_2030_; lean_object* v_majorDecl_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; uint8_t v___x_2034_; 
v_val_2030_ = lean_ctor_get(v___x_2029_, 0);
v_majorDecl_2031_ = lean_ctor_get(v_ctx_1941_, 2);
v___x_2032_ = l_Lean_LocalDecl_fvarId(v_val_2030_);
v___x_2033_ = l_Lean_LocalDecl_fvarId(v_majorDecl_2031_);
v___x_2034_ = l_Lean_instBEqFVarId_beq(v___x_2032_, v___x_2033_);
lean_dec(v___x_2033_);
if (v___x_2034_ == 0)
{
lean_object* v___x_2035_; lean_object* v___f_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___f_2039_; lean_object* v___y_2041_; uint8_t v_fst_2042_; lean_object* v_snd_2043_; lean_object* v___y_2049_; lean_object* v___y_2050_; lean_object* v___y_2085_; uint8_t v___x_2090_; 
v___x_2035_ = lean_box(v___x_1938_);
v___f_2036_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2036_, 0, v___x_2035_);
v___x_2037_ = lean_unsigned_to_nat(0u);
v___x_2038_ = lean_box(v___x_1938_);
lean_inc_ref(v___x_1939_);
lean_inc(v___x_1940_);
v___f_2039_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_2039_, 0, v___x_2037_);
lean_closure_set(v___f_2039_, 1, v___x_1940_);
lean_closure_set(v___f_2039_, 2, v___x_2038_);
lean_closure_set(v___f_2039_, 3, v___x_1939_);
v___x_2090_ = lean_nat_dec_lt(v___x_2037_, v___x_1940_);
if (v___x_2090_ == 0)
{
lean_dec(v___x_2032_);
goto v___jp_2054_;
}
else
{
lean_object* v___x_2091_; uint8_t v___x_2092_; 
v___x_2091_ = lean_array_get_size(v___x_1939_);
v___x_2092_ = lean_nat_dec_le(v___x_1940_, v___x_2091_);
if (v___x_2092_ == 0)
{
v___y_2085_ = v___x_2091_;
goto v___jp_2084_;
}
else
{
lean_inc(v___x_1940_);
v___y_2085_ = v___x_1940_;
goto v___jp_2084_;
}
}
v___jp_2040_:
{
if (v_fst_2042_ == 0)
{
uint8_t v___x_2044_; 
v___x_2044_ = l_Lean_Expr_hasFVar(v___y_2041_);
if (v___x_2044_ == 0)
{
uint8_t v___x_2045_; 
v___x_2045_ = l_Lean_Expr_hasMVar(v___y_2041_);
if (v___x_2045_ == 0)
{
lean_dec_ref(v___y_2041_);
lean_dec_ref(v___f_2039_);
lean_dec_ref(v___f_2036_);
v_fst_1984_ = v___x_2045_;
v_snd_1985_ = v_snd_2043_;
goto v___jp_1983_;
}
else
{
lean_object* v___x_2046_; 
v___x_2046_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_2039_, v___f_2036_, v___y_2041_, v_snd_2043_);
v___y_2002_ = v___x_2046_;
goto v___jp_2001_;
}
}
else
{
lean_object* v___x_2047_; 
v___x_2047_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_2039_, v___f_2036_, v___y_2041_, v_snd_2043_);
v___y_2002_ = v___x_2047_;
goto v___jp_2001_;
}
}
else
{
lean_dec_ref(v___y_2041_);
lean_dec_ref(v___f_2039_);
lean_dec_ref(v___f_2036_);
v_fst_1984_ = v_fst_2042_;
v_snd_1985_ = v_snd_2043_;
goto v___jp_1983_;
}
}
v___jp_2048_:
{
lean_object* v_fst_2051_; lean_object* v_snd_2052_; uint8_t v___x_2053_; 
v_fst_2051_ = lean_ctor_get(v___y_2050_, 0);
lean_inc(v_fst_2051_);
v_snd_2052_ = lean_ctor_get(v___y_2050_, 1);
lean_inc(v_snd_2052_);
lean_dec_ref(v___y_2050_);
v___x_2053_ = lean_unbox(v_fst_2051_);
lean_dec(v_fst_2051_);
v___y_2041_ = v___y_2049_;
v_fst_2042_ = v___x_2053_;
v_snd_2043_ = v_snd_2052_;
goto v___jp_2040_;
}
v___jp_2054_:
{
if (lean_obj_tag(v_val_2030_) == 0)
{
lean_object* v_type_2055_; lean_object* v___x_2056_; lean_object* v_mctx_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; uint8_t v___x_2060_; 
v_type_2055_ = lean_ctor_get(v_val_2030_, 3);
v___x_2056_ = lean_st_ref_get(v___y_1945_);
v_mctx_2057_ = lean_ctor_get(v___x_2056_, 0);
lean_inc_ref_n(v_mctx_2057_, 2);
lean_dec(v___x_2056_);
v___x_2058_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1);
v___x_2059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2059_, 0, v___x_2058_);
lean_ctor_set(v___x_2059_, 1, v_mctx_2057_);
v___x_2060_ = l_Lean_Expr_hasFVar(v_type_2055_);
if (v___x_2060_ == 0)
{
uint8_t v___x_2061_; 
v___x_2061_ = l_Lean_Expr_hasMVar(v_type_2055_);
if (v___x_2061_ == 0)
{
lean_dec_ref_known(v___x_2059_, 2);
lean_dec_ref(v___f_2039_);
lean_dec_ref(v___f_2036_);
v_fst_2007_ = v___x_2061_;
v_mctx_2008_ = v_mctx_2057_;
goto v___jp_2006_;
}
else
{
lean_object* v___x_2062_; 
lean_dec_ref(v_mctx_2057_);
lean_inc_ref(v_type_2055_);
v___x_2062_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_2039_, v___f_2036_, v_type_2055_, v___x_2059_);
v___y_2024_ = v___x_2062_;
goto v___jp_2023_;
}
}
else
{
lean_object* v___x_2063_; 
lean_dec_ref(v_mctx_2057_);
lean_inc_ref(v_type_2055_);
v___x_2063_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_2039_, v___f_2036_, v_type_2055_, v___x_2059_);
v___y_2024_ = v___x_2063_;
goto v___jp_2023_;
}
}
else
{
uint8_t v_nondep_2064_; 
v_nondep_2064_ = lean_ctor_get_uint8(v_val_2030_, sizeof(void*)*5);
if (v_nondep_2064_ == 0)
{
lean_object* v_type_2065_; lean_object* v_value_2066_; lean_object* v___x_2067_; lean_object* v_mctx_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; uint8_t v___x_2071_; 
v_type_2065_ = lean_ctor_get(v_val_2030_, 3);
v_value_2066_ = lean_ctor_get(v_val_2030_, 4);
v___x_2067_ = lean_st_ref_get(v___y_1945_);
v_mctx_2068_ = lean_ctor_get(v___x_2067_, 0);
lean_inc_ref(v_mctx_2068_);
lean_dec(v___x_2067_);
v___x_2069_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1);
v___x_2070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2070_, 0, v___x_2069_);
lean_ctor_set(v___x_2070_, 1, v_mctx_2068_);
v___x_2071_ = l_Lean_Expr_hasFVar(v_type_2065_);
if (v___x_2071_ == 0)
{
uint8_t v___x_2072_; 
v___x_2072_ = l_Lean_Expr_hasMVar(v_type_2065_);
if (v___x_2072_ == 0)
{
lean_inc_ref(v_value_2066_);
v___y_2041_ = v_value_2066_;
v_fst_2042_ = v___x_2072_;
v_snd_2043_ = v___x_2070_;
goto v___jp_2040_;
}
else
{
lean_object* v___x_2073_; 
lean_inc_ref(v_type_2065_);
lean_inc_ref(v___f_2036_);
lean_inc_ref(v___f_2039_);
v___x_2073_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_2039_, v___f_2036_, v_type_2065_, v___x_2070_);
lean_inc_ref(v_value_2066_);
v___y_2049_ = v_value_2066_;
v___y_2050_ = v___x_2073_;
goto v___jp_2048_;
}
}
else
{
lean_object* v___x_2074_; 
lean_inc_ref(v_type_2065_);
lean_inc_ref(v___f_2036_);
lean_inc_ref(v___f_2039_);
v___x_2074_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_2039_, v___f_2036_, v_type_2065_, v___x_2070_);
lean_inc_ref(v_value_2066_);
v___y_2049_ = v_value_2066_;
v___y_2050_ = v___x_2074_;
goto v___jp_2048_;
}
}
else
{
lean_object* v_type_2075_; lean_object* v___x_2076_; lean_object* v_mctx_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; uint8_t v___x_2080_; 
v_type_2075_ = lean_ctor_get(v_val_2030_, 3);
v___x_2076_ = lean_st_ref_get(v___y_1945_);
v_mctx_2077_ = lean_ctor_get(v___x_2076_, 0);
lean_inc_ref_n(v_mctx_2077_, 2);
lean_dec(v___x_2076_);
v___x_2078_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1);
v___x_2079_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2079_, 0, v___x_2078_);
lean_ctor_set(v___x_2079_, 1, v_mctx_2077_);
v___x_2080_ = l_Lean_Expr_hasFVar(v_type_2075_);
if (v___x_2080_ == 0)
{
uint8_t v___x_2081_; 
v___x_2081_ = l_Lean_Expr_hasMVar(v_type_2075_);
if (v___x_2081_ == 0)
{
lean_dec_ref_known(v___x_2079_, 2);
lean_dec_ref(v___f_2039_);
lean_dec_ref(v___f_2036_);
v_fst_1961_ = v___x_2081_;
v_mctx_1962_ = v_mctx_2077_;
goto v___jp_1960_;
}
else
{
lean_object* v___x_2082_; 
lean_dec_ref(v_mctx_2077_);
lean_inc_ref(v_type_2075_);
v___x_2082_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_2039_, v___f_2036_, v_type_2075_, v___x_2079_);
v___y_1978_ = v___x_2082_;
goto v___jp_1977_;
}
}
else
{
lean_object* v___x_2083_; 
lean_dec_ref(v_mctx_2077_);
lean_inc_ref(v_type_2075_);
v___x_2083_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_2039_, v___f_2036_, v_type_2075_, v___x_2079_);
v___y_1978_ = v___x_2083_;
goto v___jp_1977_;
}
}
}
}
v___jp_2084_:
{
uint8_t v___x_2086_; 
v___x_2086_ = lean_nat_dec_lt(v___x_2037_, v___y_2085_);
if (v___x_2086_ == 0)
{
lean_dec(v___y_2085_);
lean_dec(v___x_2032_);
goto v___jp_2054_;
}
else
{
size_t v___x_2087_; size_t v___x_2088_; uint8_t v___x_2089_; 
v___x_2087_ = ((size_t)0ULL);
v___x_2088_ = lean_usize_of_nat(v___y_2085_);
lean_dec(v___y_2085_);
v___x_2089_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__3(v___x_2032_, v___x_1939_, v___x_2087_, v___x_2088_);
lean_dec(v___x_2032_);
if (v___x_2089_ == 0)
{
goto v___jp_2054_;
}
else
{
lean_dec_ref(v___f_2039_);
lean_dec_ref(v___f_2036_);
v_a_1957_ = v___x_2089_;
goto v___jp_1956_;
}
}
}
}
else
{
lean_dec(v___x_2032_);
v_a_1957_ = v___x_2034_;
goto v___jp_1956_;
}
}
v___jp_1949_:
{
if (v_a_1950_ == 0)
{
size_t v___x_1951_; size_t v___x_1952_; 
v___x_1951_ = ((size_t)1ULL);
v___x_1952_ = lean_usize_add(v_i_1943_, v___x_1951_);
v_i_1943_ = v___x_1952_;
goto _start;
}
else
{
lean_object* v___x_1954_; lean_object* v___x_1955_; 
lean_dec(v___x_1940_);
lean_dec_ref(v___x_1939_);
v___x_1954_ = lean_box(v___x_1948_);
v___x_1955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1955_, 0, v___x_1954_);
return v___x_1955_;
}
}
v___jp_1956_:
{
if (v_a_1957_ == 0)
{
lean_object* v___x_1958_; lean_object* v___x_1959_; 
lean_dec(v___x_1940_);
lean_dec_ref(v___x_1939_);
v___x_1958_ = lean_box(v___x_1948_);
v___x_1959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1959_, 0, v___x_1958_);
return v___x_1959_;
}
else
{
v_a_1950_ = v___x_1938_;
goto v___jp_1949_;
}
}
v___jp_1960_:
{
lean_object* v___x_1963_; lean_object* v_cache_1964_; lean_object* v_zetaDeltaFVarIds_1965_; lean_object* v_postponed_1966_; lean_object* v_diag_1967_; lean_object* v___x_1969_; uint8_t v_isShared_1970_; uint8_t v_isSharedCheck_1975_; 
v___x_1963_ = lean_st_ref_take(v___y_1945_);
v_cache_1964_ = lean_ctor_get(v___x_1963_, 1);
v_zetaDeltaFVarIds_1965_ = lean_ctor_get(v___x_1963_, 2);
v_postponed_1966_ = lean_ctor_get(v___x_1963_, 3);
v_diag_1967_ = lean_ctor_get(v___x_1963_, 4);
v_isSharedCheck_1975_ = !lean_is_exclusive(v___x_1963_);
if (v_isSharedCheck_1975_ == 0)
{
lean_object* v_unused_1976_; 
v_unused_1976_ = lean_ctor_get(v___x_1963_, 0);
lean_dec(v_unused_1976_);
v___x_1969_ = v___x_1963_;
v_isShared_1970_ = v_isSharedCheck_1975_;
goto v_resetjp_1968_;
}
else
{
lean_inc(v_diag_1967_);
lean_inc(v_postponed_1966_);
lean_inc(v_zetaDeltaFVarIds_1965_);
lean_inc(v_cache_1964_);
lean_dec(v___x_1963_);
v___x_1969_ = lean_box(0);
v_isShared_1970_ = v_isSharedCheck_1975_;
goto v_resetjp_1968_;
}
v_resetjp_1968_:
{
lean_object* v___x_1972_; 
if (v_isShared_1970_ == 0)
{
lean_ctor_set(v___x_1969_, 0, v_mctx_1962_);
v___x_1972_ = v___x_1969_;
goto v_reusejp_1971_;
}
else
{
lean_object* v_reuseFailAlloc_1974_; 
v_reuseFailAlloc_1974_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1974_, 0, v_mctx_1962_);
lean_ctor_set(v_reuseFailAlloc_1974_, 1, v_cache_1964_);
lean_ctor_set(v_reuseFailAlloc_1974_, 2, v_zetaDeltaFVarIds_1965_);
lean_ctor_set(v_reuseFailAlloc_1974_, 3, v_postponed_1966_);
lean_ctor_set(v_reuseFailAlloc_1974_, 4, v_diag_1967_);
v___x_1972_ = v_reuseFailAlloc_1974_;
goto v_reusejp_1971_;
}
v_reusejp_1971_:
{
lean_object* v___x_1973_; 
v___x_1973_ = lean_st_ref_put(v___y_1945_, v___x_1972_);
v_a_1957_ = v_fst_1961_;
goto v___jp_1956_;
}
}
}
v___jp_1977_:
{
lean_object* v_snd_1979_; lean_object* v_fst_1980_; lean_object* v_mctx_1981_; uint8_t v___x_1982_; 
v_snd_1979_ = lean_ctor_get(v___y_1978_, 1);
lean_inc(v_snd_1979_);
v_fst_1980_ = lean_ctor_get(v___y_1978_, 0);
lean_inc(v_fst_1980_);
lean_dec_ref(v___y_1978_);
v_mctx_1981_ = lean_ctor_get(v_snd_1979_, 1);
lean_inc_ref(v_mctx_1981_);
lean_dec(v_snd_1979_);
v___x_1982_ = lean_unbox(v_fst_1980_);
lean_dec(v_fst_1980_);
v_fst_1961_ = v___x_1982_;
v_mctx_1962_ = v_mctx_1981_;
goto v___jp_1960_;
}
v___jp_1983_:
{
lean_object* v_mctx_1986_; lean_object* v___x_1987_; lean_object* v_cache_1988_; lean_object* v_zetaDeltaFVarIds_1989_; lean_object* v_postponed_1990_; lean_object* v_diag_1991_; lean_object* v___x_1993_; uint8_t v_isShared_1994_; uint8_t v_isSharedCheck_1999_; 
v_mctx_1986_ = lean_ctor_get(v_snd_1985_, 1);
lean_inc_ref(v_mctx_1986_);
lean_dec_ref(v_snd_1985_);
v___x_1987_ = lean_st_ref_take(v___y_1945_);
v_cache_1988_ = lean_ctor_get(v___x_1987_, 1);
v_zetaDeltaFVarIds_1989_ = lean_ctor_get(v___x_1987_, 2);
v_postponed_1990_ = lean_ctor_get(v___x_1987_, 3);
v_diag_1991_ = lean_ctor_get(v___x_1987_, 4);
v_isSharedCheck_1999_ = !lean_is_exclusive(v___x_1987_);
if (v_isSharedCheck_1999_ == 0)
{
lean_object* v_unused_2000_; 
v_unused_2000_ = lean_ctor_get(v___x_1987_, 0);
lean_dec(v_unused_2000_);
v___x_1993_ = v___x_1987_;
v_isShared_1994_ = v_isSharedCheck_1999_;
goto v_resetjp_1992_;
}
else
{
lean_inc(v_diag_1991_);
lean_inc(v_postponed_1990_);
lean_inc(v_zetaDeltaFVarIds_1989_);
lean_inc(v_cache_1988_);
lean_dec(v___x_1987_);
v___x_1993_ = lean_box(0);
v_isShared_1994_ = v_isSharedCheck_1999_;
goto v_resetjp_1992_;
}
v_resetjp_1992_:
{
lean_object* v___x_1996_; 
if (v_isShared_1994_ == 0)
{
lean_ctor_set(v___x_1993_, 0, v_mctx_1986_);
v___x_1996_ = v___x_1993_;
goto v_reusejp_1995_;
}
else
{
lean_object* v_reuseFailAlloc_1998_; 
v_reuseFailAlloc_1998_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1998_, 0, v_mctx_1986_);
lean_ctor_set(v_reuseFailAlloc_1998_, 1, v_cache_1988_);
lean_ctor_set(v_reuseFailAlloc_1998_, 2, v_zetaDeltaFVarIds_1989_);
lean_ctor_set(v_reuseFailAlloc_1998_, 3, v_postponed_1990_);
lean_ctor_set(v_reuseFailAlloc_1998_, 4, v_diag_1991_);
v___x_1996_ = v_reuseFailAlloc_1998_;
goto v_reusejp_1995_;
}
v_reusejp_1995_:
{
lean_object* v___x_1997_; 
v___x_1997_ = lean_st_ref_put(v___y_1945_, v___x_1996_);
v_a_1957_ = v_fst_1984_;
goto v___jp_1956_;
}
}
}
v___jp_2001_:
{
lean_object* v_fst_2003_; lean_object* v_snd_2004_; uint8_t v___x_2005_; 
v_fst_2003_ = lean_ctor_get(v___y_2002_, 0);
lean_inc(v_fst_2003_);
v_snd_2004_ = lean_ctor_get(v___y_2002_, 1);
lean_inc(v_snd_2004_);
lean_dec_ref(v___y_2002_);
v___x_2005_ = lean_unbox(v_fst_2003_);
lean_dec(v_fst_2003_);
v_fst_1984_ = v___x_2005_;
v_snd_1985_ = v_snd_2004_;
goto v___jp_1983_;
}
v___jp_2006_:
{
lean_object* v___x_2009_; lean_object* v_cache_2010_; lean_object* v_zetaDeltaFVarIds_2011_; lean_object* v_postponed_2012_; lean_object* v_diag_2013_; lean_object* v___x_2015_; uint8_t v_isShared_2016_; uint8_t v_isSharedCheck_2021_; 
v___x_2009_ = lean_st_ref_take(v___y_1945_);
v_cache_2010_ = lean_ctor_get(v___x_2009_, 1);
v_zetaDeltaFVarIds_2011_ = lean_ctor_get(v___x_2009_, 2);
v_postponed_2012_ = lean_ctor_get(v___x_2009_, 3);
v_diag_2013_ = lean_ctor_get(v___x_2009_, 4);
v_isSharedCheck_2021_ = !lean_is_exclusive(v___x_2009_);
if (v_isSharedCheck_2021_ == 0)
{
lean_object* v_unused_2022_; 
v_unused_2022_ = lean_ctor_get(v___x_2009_, 0);
lean_dec(v_unused_2022_);
v___x_2015_ = v___x_2009_;
v_isShared_2016_ = v_isSharedCheck_2021_;
goto v_resetjp_2014_;
}
else
{
lean_inc(v_diag_2013_);
lean_inc(v_postponed_2012_);
lean_inc(v_zetaDeltaFVarIds_2011_);
lean_inc(v_cache_2010_);
lean_dec(v___x_2009_);
v___x_2015_ = lean_box(0);
v_isShared_2016_ = v_isSharedCheck_2021_;
goto v_resetjp_2014_;
}
v_resetjp_2014_:
{
lean_object* v___x_2018_; 
if (v_isShared_2016_ == 0)
{
lean_ctor_set(v___x_2015_, 0, v_mctx_2008_);
v___x_2018_ = v___x_2015_;
goto v_reusejp_2017_;
}
else
{
lean_object* v_reuseFailAlloc_2020_; 
v_reuseFailAlloc_2020_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2020_, 0, v_mctx_2008_);
lean_ctor_set(v_reuseFailAlloc_2020_, 1, v_cache_2010_);
lean_ctor_set(v_reuseFailAlloc_2020_, 2, v_zetaDeltaFVarIds_2011_);
lean_ctor_set(v_reuseFailAlloc_2020_, 3, v_postponed_2012_);
lean_ctor_set(v_reuseFailAlloc_2020_, 4, v_diag_2013_);
v___x_2018_ = v_reuseFailAlloc_2020_;
goto v_reusejp_2017_;
}
v_reusejp_2017_:
{
lean_object* v___x_2019_; 
v___x_2019_ = lean_st_ref_put(v___y_1945_, v___x_2018_);
v_a_1957_ = v_fst_2007_;
goto v___jp_1956_;
}
}
}
v___jp_2023_:
{
lean_object* v_snd_2025_; lean_object* v_fst_2026_; lean_object* v_mctx_2027_; uint8_t v___x_2028_; 
v_snd_2025_ = lean_ctor_get(v___y_2024_, 1);
lean_inc(v_snd_2025_);
v_fst_2026_ = lean_ctor_get(v___y_2024_, 0);
lean_inc(v_fst_2026_);
lean_dec_ref(v___y_2024_);
v_mctx_2027_ = lean_ctor_get(v_snd_2025_, 1);
lean_inc_ref(v_mctx_2027_);
lean_dec(v_snd_2025_);
v___x_2028_ = lean_unbox(v_fst_2026_);
lean_dec(v_fst_2026_);
v_fst_2007_ = v___x_2028_;
v_mctx_2008_ = v_mctx_2027_;
goto v___jp_2006_;
}
}
else
{
uint8_t v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; 
lean_dec(v___x_1940_);
lean_dec_ref(v___x_1939_);
v___x_2093_ = 0;
v___x_2094_ = lean_box(v___x_2093_);
v___x_2095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2095_, 0, v___x_2094_);
return v___x_2095_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___boxed(lean_object* v___x_2096_, lean_object* v___x_2097_, lean_object* v___x_2098_, lean_object* v_ctx_2099_, lean_object* v_as_2100_, lean_object* v_i_2101_, lean_object* v_stop_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_){
_start:
{
uint8_t v___x_7681__boxed_2105_; size_t v_i_boxed_2106_; size_t v_stop_boxed_2107_; lean_object* v_res_2108_; 
v___x_7681__boxed_2105_ = lean_unbox(v___x_2096_);
v_i_boxed_2106_ = lean_unbox_usize(v_i_2101_);
lean_dec(v_i_2101_);
v_stop_boxed_2107_ = lean_unbox_usize(v_stop_2102_);
lean_dec(v_stop_2102_);
v_res_2108_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg(v___x_7681__boxed_2105_, v___x_2097_, v___x_2098_, v_ctx_2099_, v_as_2100_, v_i_boxed_2106_, v_stop_boxed_2107_, v___y_2103_);
lean_dec(v___y_2103_);
lean_dec_ref(v_as_2100_);
lean_dec_ref(v_ctx_2099_);
return v_res_2108_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4(uint8_t v___x_2109_, lean_object* v___x_2110_, lean_object* v___x_2111_, lean_object* v_ctx_2112_, lean_object* v_x_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_){
_start:
{
if (lean_obj_tag(v_x_2113_) == 0)
{
lean_object* v_cs_2119_; lean_object* v___x_2121_; uint8_t v_isShared_2122_; uint8_t v_isSharedCheck_2137_; 
v_cs_2119_ = lean_ctor_get(v_x_2113_, 0);
v_isSharedCheck_2137_ = !lean_is_exclusive(v_x_2113_);
if (v_isSharedCheck_2137_ == 0)
{
v___x_2121_ = v_x_2113_;
v_isShared_2122_ = v_isSharedCheck_2137_;
goto v_resetjp_2120_;
}
else
{
lean_inc(v_cs_2119_);
lean_dec(v_x_2113_);
v___x_2121_ = lean_box(0);
v_isShared_2122_ = v_isSharedCheck_2137_;
goto v_resetjp_2120_;
}
v_resetjp_2120_:
{
lean_object* v___x_2123_; lean_object* v___x_2124_; uint8_t v___x_2125_; 
v___x_2123_ = lean_unsigned_to_nat(0u);
v___x_2124_ = lean_array_get_size(v_cs_2119_);
v___x_2125_ = lean_nat_dec_lt(v___x_2123_, v___x_2124_);
if (v___x_2125_ == 0)
{
lean_object* v___x_2126_; lean_object* v___x_2128_; 
lean_dec_ref(v_cs_2119_);
lean_dec(v___x_2111_);
lean_dec_ref(v___x_2110_);
v___x_2126_ = lean_box(v___x_2125_);
if (v_isShared_2122_ == 0)
{
lean_ctor_set(v___x_2121_, 0, v___x_2126_);
v___x_2128_ = v___x_2121_;
goto v_reusejp_2127_;
}
else
{
lean_object* v_reuseFailAlloc_2129_; 
v_reuseFailAlloc_2129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2129_, 0, v___x_2126_);
v___x_2128_ = v_reuseFailAlloc_2129_;
goto v_reusejp_2127_;
}
v_reusejp_2127_:
{
return v___x_2128_;
}
}
else
{
if (v___x_2125_ == 0)
{
lean_object* v___x_2130_; lean_object* v___x_2132_; 
lean_dec_ref(v_cs_2119_);
lean_dec(v___x_2111_);
lean_dec_ref(v___x_2110_);
v___x_2130_ = lean_box(v___x_2125_);
if (v_isShared_2122_ == 0)
{
lean_ctor_set(v___x_2121_, 0, v___x_2130_);
v___x_2132_ = v___x_2121_;
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
size_t v___x_2134_; size_t v___x_2135_; lean_object* v___x_2136_; 
lean_del_object(v___x_2121_);
v___x_2134_ = ((size_t)0ULL);
v___x_2135_ = lean_usize_of_nat(v___x_2124_);
v___x_2136_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4_spec__5(v___x_2109_, v___x_2110_, v___x_2111_, v_ctx_2112_, v_cs_2119_, v___x_2134_, v___x_2135_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_);
lean_dec_ref(v_cs_2119_);
return v___x_2136_;
}
}
}
}
else
{
lean_object* v_vs_2138_; lean_object* v___x_2140_; uint8_t v_isShared_2141_; uint8_t v_isSharedCheck_2156_; 
v_vs_2138_ = lean_ctor_get(v_x_2113_, 0);
v_isSharedCheck_2156_ = !lean_is_exclusive(v_x_2113_);
if (v_isSharedCheck_2156_ == 0)
{
v___x_2140_ = v_x_2113_;
v_isShared_2141_ = v_isSharedCheck_2156_;
goto v_resetjp_2139_;
}
else
{
lean_inc(v_vs_2138_);
lean_dec(v_x_2113_);
v___x_2140_ = lean_box(0);
v_isShared_2141_ = v_isSharedCheck_2156_;
goto v_resetjp_2139_;
}
v_resetjp_2139_:
{
lean_object* v___x_2142_; lean_object* v___x_2143_; uint8_t v___x_2144_; 
v___x_2142_ = lean_unsigned_to_nat(0u);
v___x_2143_ = lean_array_get_size(v_vs_2138_);
v___x_2144_ = lean_nat_dec_lt(v___x_2142_, v___x_2143_);
if (v___x_2144_ == 0)
{
lean_object* v___x_2145_; lean_object* v___x_2147_; 
lean_dec_ref(v_vs_2138_);
lean_dec(v___x_2111_);
lean_dec_ref(v___x_2110_);
v___x_2145_ = lean_box(v___x_2144_);
if (v_isShared_2141_ == 0)
{
lean_ctor_set_tag(v___x_2140_, 0);
lean_ctor_set(v___x_2140_, 0, v___x_2145_);
v___x_2147_ = v___x_2140_;
goto v_reusejp_2146_;
}
else
{
lean_object* v_reuseFailAlloc_2148_; 
v_reuseFailAlloc_2148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2148_, 0, v___x_2145_);
v___x_2147_ = v_reuseFailAlloc_2148_;
goto v_reusejp_2146_;
}
v_reusejp_2146_:
{
return v___x_2147_;
}
}
else
{
if (v___x_2144_ == 0)
{
lean_object* v___x_2149_; lean_object* v___x_2151_; 
lean_dec_ref(v_vs_2138_);
lean_dec(v___x_2111_);
lean_dec_ref(v___x_2110_);
v___x_2149_ = lean_box(v___x_2144_);
if (v_isShared_2141_ == 0)
{
lean_ctor_set_tag(v___x_2140_, 0);
lean_ctor_set(v___x_2140_, 0, v___x_2149_);
v___x_2151_ = v___x_2140_;
goto v_reusejp_2150_;
}
else
{
lean_object* v_reuseFailAlloc_2152_; 
v_reuseFailAlloc_2152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2152_, 0, v___x_2149_);
v___x_2151_ = v_reuseFailAlloc_2152_;
goto v_reusejp_2150_;
}
v_reusejp_2150_:
{
return v___x_2151_;
}
}
else
{
size_t v___x_2153_; size_t v___x_2154_; lean_object* v___x_2155_; 
lean_del_object(v___x_2140_);
v___x_2153_ = ((size_t)0ULL);
v___x_2154_ = lean_usize_of_nat(v___x_2143_);
v___x_2155_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg(v___x_2109_, v___x_2110_, v___x_2111_, v_ctx_2112_, v_vs_2138_, v___x_2153_, v___x_2154_, v___y_2115_);
lean_dec_ref(v_vs_2138_);
return v___x_2155_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4_spec__5(uint8_t v___x_2157_, lean_object* v___x_2158_, lean_object* v___x_2159_, lean_object* v_ctx_2160_, lean_object* v_as_2161_, size_t v_i_2162_, size_t v_stop_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_){
_start:
{
uint8_t v___x_2169_; 
v___x_2169_ = lean_usize_dec_eq(v_i_2162_, v_stop_2163_);
if (v___x_2169_ == 0)
{
uint8_t v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; 
v___x_2170_ = 1;
v___x_2171_ = lean_array_uget_borrowed(v_as_2161_, v_i_2162_);
lean_inc(v___x_2171_);
lean_inc(v___x_2159_);
lean_inc_ref(v___x_2158_);
v___x_2172_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4(v___x_2157_, v___x_2158_, v___x_2159_, v_ctx_2160_, v___x_2171_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_);
if (lean_obj_tag(v___x_2172_) == 0)
{
lean_object* v_a_2173_; lean_object* v___x_2175_; uint8_t v_isShared_2176_; uint8_t v_isSharedCheck_2185_; 
v_a_2173_ = lean_ctor_get(v___x_2172_, 0);
v_isSharedCheck_2185_ = !lean_is_exclusive(v___x_2172_);
if (v_isSharedCheck_2185_ == 0)
{
v___x_2175_ = v___x_2172_;
v_isShared_2176_ = v_isSharedCheck_2185_;
goto v_resetjp_2174_;
}
else
{
lean_inc(v_a_2173_);
lean_dec(v___x_2172_);
v___x_2175_ = lean_box(0);
v_isShared_2176_ = v_isSharedCheck_2185_;
goto v_resetjp_2174_;
}
v_resetjp_2174_:
{
uint8_t v___x_2177_; 
v___x_2177_ = lean_unbox(v_a_2173_);
lean_dec(v_a_2173_);
if (v___x_2177_ == 0)
{
size_t v___x_2178_; size_t v___x_2179_; 
lean_del_object(v___x_2175_);
v___x_2178_ = ((size_t)1ULL);
v___x_2179_ = lean_usize_add(v_i_2162_, v___x_2178_);
v_i_2162_ = v___x_2179_;
goto _start;
}
else
{
lean_object* v___x_2181_; lean_object* v___x_2183_; 
lean_dec(v___x_2159_);
lean_dec_ref(v___x_2158_);
v___x_2181_ = lean_box(v___x_2170_);
if (v_isShared_2176_ == 0)
{
lean_ctor_set(v___x_2175_, 0, v___x_2181_);
v___x_2183_ = v___x_2175_;
goto v_reusejp_2182_;
}
else
{
lean_object* v_reuseFailAlloc_2184_; 
v_reuseFailAlloc_2184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2184_, 0, v___x_2181_);
v___x_2183_ = v_reuseFailAlloc_2184_;
goto v_reusejp_2182_;
}
v_reusejp_2182_:
{
return v___x_2183_;
}
}
}
}
else
{
lean_dec(v___x_2159_);
lean_dec_ref(v___x_2158_);
return v___x_2172_;
}
}
else
{
uint8_t v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; 
lean_dec(v___x_2159_);
lean_dec_ref(v___x_2158_);
v___x_2186_ = 0;
v___x_2187_ = lean_box(v___x_2186_);
v___x_2188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2188_, 0, v___x_2187_);
return v___x_2188_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4_spec__5___boxed(lean_object* v___x_2189_, lean_object* v___x_2190_, lean_object* v___x_2191_, lean_object* v_ctx_2192_, lean_object* v_as_2193_, lean_object* v_i_2194_, lean_object* v_stop_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_){
_start:
{
uint8_t v___x_7976__boxed_2201_; size_t v_i_boxed_2202_; size_t v_stop_boxed_2203_; lean_object* v_res_2204_; 
v___x_7976__boxed_2201_ = lean_unbox(v___x_2189_);
v_i_boxed_2202_ = lean_unbox_usize(v_i_2194_);
lean_dec(v_i_2194_);
v_stop_boxed_2203_ = lean_unbox_usize(v_stop_2195_);
lean_dec(v_stop_2195_);
v_res_2204_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4_spec__5(v___x_7976__boxed_2201_, v___x_2190_, v___x_2191_, v_ctx_2192_, v_as_2193_, v_i_boxed_2202_, v_stop_boxed_2203_, v___y_2196_, v___y_2197_, v___y_2198_, v___y_2199_);
lean_dec(v___y_2199_);
lean_dec_ref(v___y_2198_);
lean_dec(v___y_2197_);
lean_dec_ref(v___y_2196_);
lean_dec_ref(v_as_2193_);
lean_dec_ref(v_ctx_2192_);
return v_res_2204_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4___boxed(lean_object* v___x_2205_, lean_object* v___x_2206_, lean_object* v___x_2207_, lean_object* v_ctx_2208_, lean_object* v_x_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_){
_start:
{
uint8_t v___x_7996__boxed_2215_; lean_object* v_res_2216_; 
v___x_7996__boxed_2215_ = lean_unbox(v___x_2205_);
v_res_2216_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4(v___x_7996__boxed_2215_, v___x_2206_, v___x_2207_, v_ctx_2208_, v_x_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_);
lean_dec(v___y_2213_);
lean_dec_ref(v___y_2212_);
lean_dec(v___y_2211_);
lean_dec_ref(v___y_2210_);
lean_dec_ref(v_ctx_2208_);
return v_res_2216_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4(uint8_t v___x_2217_, lean_object* v___x_2218_, lean_object* v___x_2219_, lean_object* v_ctx_2220_, lean_object* v_t_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_){
_start:
{
lean_object* v_root_2227_; lean_object* v_tail_2228_; lean_object* v___x_2229_; 
v_root_2227_ = lean_ctor_get(v_t_2221_, 0);
lean_inc_ref(v_root_2227_);
v_tail_2228_ = lean_ctor_get(v_t_2221_, 1);
lean_inc_ref(v_tail_2228_);
lean_dec_ref(v_t_2221_);
lean_inc(v___x_2219_);
lean_inc_ref(v___x_2218_);
v___x_2229_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4(v___x_2217_, v___x_2218_, v___x_2219_, v_ctx_2220_, v_root_2227_, v___y_2222_, v___y_2223_, v___y_2224_, v___y_2225_);
if (lean_obj_tag(v___x_2229_) == 0)
{
lean_object* v_a_2230_; uint8_t v___x_2231_; 
v_a_2230_ = lean_ctor_get(v___x_2229_, 0);
v___x_2231_ = lean_unbox(v_a_2230_);
if (v___x_2231_ == 0)
{
lean_object* v___x_2233_; uint8_t v_isShared_2234_; uint8_t v_isSharedCheck_2249_; 
v_isSharedCheck_2249_ = !lean_is_exclusive(v___x_2229_);
if (v_isSharedCheck_2249_ == 0)
{
lean_object* v_unused_2250_; 
v_unused_2250_ = lean_ctor_get(v___x_2229_, 0);
lean_dec(v_unused_2250_);
v___x_2233_ = v___x_2229_;
v_isShared_2234_ = v_isSharedCheck_2249_;
goto v_resetjp_2232_;
}
else
{
lean_dec(v___x_2229_);
v___x_2233_ = lean_box(0);
v_isShared_2234_ = v_isSharedCheck_2249_;
goto v_resetjp_2232_;
}
v_resetjp_2232_:
{
lean_object* v___x_2235_; lean_object* v___x_2236_; uint8_t v___x_2237_; 
v___x_2235_ = lean_unsigned_to_nat(0u);
v___x_2236_ = lean_array_get_size(v_tail_2228_);
v___x_2237_ = lean_nat_dec_lt(v___x_2235_, v___x_2236_);
if (v___x_2237_ == 0)
{
lean_object* v___x_2238_; lean_object* v___x_2240_; 
lean_dec_ref(v_tail_2228_);
lean_dec(v___x_2219_);
lean_dec_ref(v___x_2218_);
v___x_2238_ = lean_box(v___x_2237_);
if (v_isShared_2234_ == 0)
{
lean_ctor_set(v___x_2233_, 0, v___x_2238_);
v___x_2240_ = v___x_2233_;
goto v_reusejp_2239_;
}
else
{
lean_object* v_reuseFailAlloc_2241_; 
v_reuseFailAlloc_2241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2241_, 0, v___x_2238_);
v___x_2240_ = v_reuseFailAlloc_2241_;
goto v_reusejp_2239_;
}
v_reusejp_2239_:
{
return v___x_2240_;
}
}
else
{
if (v___x_2237_ == 0)
{
lean_object* v___x_2242_; lean_object* v___x_2244_; 
lean_dec_ref(v_tail_2228_);
lean_dec(v___x_2219_);
lean_dec_ref(v___x_2218_);
v___x_2242_ = lean_box(v___x_2237_);
if (v_isShared_2234_ == 0)
{
lean_ctor_set(v___x_2233_, 0, v___x_2242_);
v___x_2244_ = v___x_2233_;
goto v_reusejp_2243_;
}
else
{
lean_object* v_reuseFailAlloc_2245_; 
v_reuseFailAlloc_2245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2245_, 0, v___x_2242_);
v___x_2244_ = v_reuseFailAlloc_2245_;
goto v_reusejp_2243_;
}
v_reusejp_2243_:
{
return v___x_2244_;
}
}
else
{
size_t v___x_2246_; size_t v___x_2247_; lean_object* v___x_2248_; 
lean_del_object(v___x_2233_);
v___x_2246_ = ((size_t)0ULL);
v___x_2247_ = lean_usize_of_nat(v___x_2236_);
v___x_2248_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg(v___x_2217_, v___x_2218_, v___x_2219_, v_ctx_2220_, v_tail_2228_, v___x_2246_, v___x_2247_, v___y_2223_);
lean_dec_ref(v_tail_2228_);
return v___x_2248_;
}
}
}
}
else
{
lean_dec_ref(v_tail_2228_);
lean_dec(v___x_2219_);
lean_dec_ref(v___x_2218_);
return v___x_2229_;
}
}
else
{
lean_dec_ref(v_tail_2228_);
lean_dec(v___x_2219_);
lean_dec_ref(v___x_2218_);
return v___x_2229_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4___boxed(lean_object* v___x_2251_, lean_object* v___x_2252_, lean_object* v___x_2253_, lean_object* v_ctx_2254_, lean_object* v_t_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_){
_start:
{
uint8_t v___x_8144__boxed_2261_; lean_object* v_res_2262_; 
v___x_8144__boxed_2261_ = lean_unbox(v___x_2251_);
v_res_2262_ = l_Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4(v___x_8144__boxed_2261_, v___x_2252_, v___x_2253_, v_ctx_2254_, v_t_2255_, v___y_2256_, v___y_2257_, v___y_2258_, v___y_2259_);
lean_dec(v___y_2259_);
lean_dec_ref(v___y_2258_);
lean_dec(v___y_2257_);
lean_dec_ref(v___y_2256_);
lean_dec_ref(v_ctx_2254_);
return v_res_2262_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices(lean_object* v_ctx_2263_, lean_object* v_a_2264_, lean_object* v_a_2265_, lean_object* v_a_2266_, lean_object* v_a_2267_){
_start:
{
lean_object* v_majorTypeIndices_2269_; lean_object* v___x_2270_; uint8_t v___y_2272_; lean_object* v___x_2294_; uint8_t v___x_2295_; 
v_majorTypeIndices_2269_ = lean_ctor_get(v_ctx_2263_, 5);
lean_inc_ref(v_majorTypeIndices_2269_);
v___x_2270_ = lean_array_get_size(v_majorTypeIndices_2269_);
v___x_2294_ = lean_unsigned_to_nat(0u);
v___x_2295_ = lean_nat_dec_eq(v___x_2270_, v___x_2294_);
if (v___x_2295_ == 0)
{
uint8_t v___x_2296_; 
v___x_2296_ = lean_nat_dec_lt(v___x_2294_, v___x_2270_);
if (v___x_2296_ == 0)
{
v___y_2272_ = v___x_2296_;
goto v___jp_2271_;
}
else
{
if (v___x_2296_ == 0)
{
v___y_2272_ = v___x_2296_;
goto v___jp_2271_;
}
else
{
size_t v___x_2297_; size_t v___x_2298_; uint8_t v___x_2299_; 
v___x_2297_ = ((size_t)0ULL);
v___x_2298_ = lean_usize_of_nat(v___x_2270_);
v___x_2299_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5(v___x_2270_, v_majorTypeIndices_2269_, v___x_2297_, v___x_2298_);
if (v___x_2299_ == 0)
{
v___y_2272_ = v___x_2299_;
goto v___jp_2271_;
}
else
{
lean_object* v___x_2300_; lean_object* v___x_2301_; 
lean_dec_ref(v_majorTypeIndices_2269_);
lean_dec_ref(v_ctx_2263_);
v___x_2300_ = lean_box(v___x_2295_);
v___x_2301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2301_, 0, v___x_2300_);
return v___x_2301_;
}
}
}
}
else
{
lean_object* v___x_2302_; lean_object* v___x_2303_; 
lean_dec_ref(v_majorTypeIndices_2269_);
lean_dec_ref(v_ctx_2263_);
v___x_2302_ = lean_box(v___x_2295_);
v___x_2303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2303_, 0, v___x_2302_);
return v___x_2303_;
}
v___jp_2271_:
{
uint8_t v___x_2273_; 
v___x_2273_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1___redArg(v_majorTypeIndices_2269_, v___x_2270_, v___x_2270_);
if (v___x_2273_ == 0)
{
lean_object* v_lctx_2274_; lean_object* v_decls_2275_; lean_object* v___x_2276_; 
v_lctx_2274_ = lean_ctor_get(v_a_2264_, 2);
v_decls_2275_ = lean_ctor_get(v_lctx_2274_, 1);
lean_inc_ref(v_decls_2275_);
v___x_2276_ = l_Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4(v___x_2273_, v_majorTypeIndices_2269_, v___x_2270_, v_ctx_2263_, v_decls_2275_, v_a_2264_, v_a_2265_, v_a_2266_, v_a_2267_);
lean_dec_ref(v_ctx_2263_);
if (lean_obj_tag(v___x_2276_) == 0)
{
lean_object* v_a_2277_; lean_object* v___x_2279_; uint8_t v_isShared_2280_; uint8_t v_isSharedCheck_2291_; 
v_a_2277_ = lean_ctor_get(v___x_2276_, 0);
v_isSharedCheck_2291_ = !lean_is_exclusive(v___x_2276_);
if (v_isSharedCheck_2291_ == 0)
{
v___x_2279_ = v___x_2276_;
v_isShared_2280_ = v_isSharedCheck_2291_;
goto v_resetjp_2278_;
}
else
{
lean_inc(v_a_2277_);
lean_dec(v___x_2276_);
v___x_2279_ = lean_box(0);
v_isShared_2280_ = v_isSharedCheck_2291_;
goto v_resetjp_2278_;
}
v_resetjp_2278_:
{
uint8_t v___x_2281_; 
v___x_2281_ = lean_unbox(v_a_2277_);
lean_dec(v_a_2277_);
if (v___x_2281_ == 0)
{
uint8_t v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2285_; 
v___x_2282_ = 1;
v___x_2283_ = lean_box(v___x_2282_);
if (v_isShared_2280_ == 0)
{
lean_ctor_set(v___x_2279_, 0, v___x_2283_);
v___x_2285_ = v___x_2279_;
goto v_reusejp_2284_;
}
else
{
lean_object* v_reuseFailAlloc_2286_; 
v_reuseFailAlloc_2286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2286_, 0, v___x_2283_);
v___x_2285_ = v_reuseFailAlloc_2286_;
goto v_reusejp_2284_;
}
v_reusejp_2284_:
{
return v___x_2285_;
}
}
else
{
lean_object* v___x_2287_; lean_object* v___x_2289_; 
v___x_2287_ = lean_box(v___x_2273_);
if (v_isShared_2280_ == 0)
{
lean_ctor_set(v___x_2279_, 0, v___x_2287_);
v___x_2289_ = v___x_2279_;
goto v_reusejp_2288_;
}
else
{
lean_object* v_reuseFailAlloc_2290_; 
v_reuseFailAlloc_2290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2290_, 0, v___x_2287_);
v___x_2289_ = v_reuseFailAlloc_2290_;
goto v_reusejp_2288_;
}
v_reusejp_2288_:
{
return v___x_2289_;
}
}
}
}
else
{
return v___x_2276_;
}
}
else
{
lean_object* v___x_2292_; lean_object* v___x_2293_; 
lean_dec_ref(v_majorTypeIndices_2269_);
lean_dec_ref(v_ctx_2263_);
v___x_2292_ = lean_box(v___y_2272_);
v___x_2293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2293_, 0, v___x_2292_);
return v___x_2293_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___boxed(lean_object* v_ctx_2304_, lean_object* v_a_2305_, lean_object* v_a_2306_, lean_object* v_a_2307_, lean_object* v_a_2308_, lean_object* v_a_2309_){
_start:
{
lean_object* v_res_2310_; 
v_res_2310_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices(v_ctx_2304_, v_a_2305_, v_a_2306_, v_a_2307_, v_a_2308_);
lean_dec(v_a_2308_);
lean_dec_ref(v_a_2307_);
lean_dec(v_a_2306_);
lean_dec_ref(v_a_2305_);
return v_res_2310_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0(lean_object* v___x_2311_, lean_object* v_i_2312_, lean_object* v_n_2313_, lean_object* v_i_2314_, lean_object* v_a_2315_){
_start:
{
uint8_t v___x_2316_; 
v___x_2316_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0___redArg(v___x_2311_, v_i_2312_, v_n_2313_, v_i_2314_);
return v___x_2316_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0___boxed(lean_object* v___x_2317_, lean_object* v_i_2318_, lean_object* v_n_2319_, lean_object* v_i_2320_, lean_object* v_a_2321_){
_start:
{
uint8_t v_res_2322_; lean_object* v_r_2323_; 
v_res_2322_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0(v___x_2317_, v_i_2318_, v_n_2319_, v_i_2320_, v_a_2321_);
lean_dec(v_n_2319_);
lean_dec(v_i_2318_);
lean_dec_ref(v___x_2317_);
v_r_2323_ = lean_box(v_res_2322_);
return v_r_2323_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1(lean_object* v___x_2324_, lean_object* v_n_2325_, lean_object* v_i_2326_, lean_object* v_a_2327_){
_start:
{
uint8_t v___x_2328_; 
v___x_2328_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1___redArg(v___x_2324_, v_n_2325_, v_i_2326_);
return v___x_2328_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1___boxed(lean_object* v___x_2329_, lean_object* v_n_2330_, lean_object* v_i_2331_, lean_object* v_a_2332_){
_start:
{
uint8_t v_res_2333_; lean_object* v_r_2334_; 
v_res_2333_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1(v___x_2329_, v_n_2330_, v_i_2331_, v_a_2332_);
lean_dec(v_n_2330_);
lean_dec_ref(v___x_2329_);
v_r_2334_ = lean_box(v_res_2333_);
return v_r_2334_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5(uint8_t v___x_2335_, lean_object* v___x_2336_, lean_object* v___x_2337_, lean_object* v_ctx_2338_, lean_object* v_as_2339_, size_t v_i_2340_, size_t v_stop_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_){
_start:
{
lean_object* v___x_2347_; 
v___x_2347_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg(v___x_2335_, v___x_2336_, v___x_2337_, v_ctx_2338_, v_as_2339_, v_i_2340_, v_stop_2341_, v___y_2343_);
return v___x_2347_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___boxed(lean_object* v___x_2348_, lean_object* v___x_2349_, lean_object* v___x_2350_, lean_object* v_ctx_2351_, lean_object* v_as_2352_, lean_object* v_i_2353_, lean_object* v_stop_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_){
_start:
{
uint8_t v___x_8297__boxed_2360_; size_t v_i_boxed_2361_; size_t v_stop_boxed_2362_; lean_object* v_res_2363_; 
v___x_8297__boxed_2360_ = lean_unbox(v___x_2348_);
v_i_boxed_2361_ = lean_unbox_usize(v_i_2353_);
lean_dec(v_i_2353_);
v_stop_boxed_2362_ = lean_unbox_usize(v_stop_2354_);
lean_dec(v_stop_2354_);
v_res_2363_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5(v___x_8297__boxed_2360_, v___x_2349_, v___x_2350_, v_ctx_2351_, v_as_2352_, v_i_boxed_2361_, v_stop_boxed_2362_, v___y_2355_, v___y_2356_, v___y_2357_, v___y_2358_);
lean_dec(v___y_2358_);
lean_dec_ref(v___y_2357_);
lean_dec(v___y_2356_);
lean_dec_ref(v___y_2355_);
lean_dec_ref(v_as_2352_);
lean_dec_ref(v_ctx_2351_);
return v_res_2363_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__0(lean_object* v_as_2364_, size_t v_i_2365_, size_t v_stop_2366_, lean_object* v_b_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_){
_start:
{
lean_object* v_a_2374_; uint8_t v___x_2378_; 
v___x_2378_ = lean_usize_dec_eq(v_i_2365_, v_stop_2366_);
if (v___x_2378_ == 0)
{
lean_object* v_toInductionSubgoal_2379_; lean_object* v_ctorName_2380_; lean_object* v_mvarId_2381_; lean_object* v_fields_2382_; lean_object* v_subst_2383_; lean_object* v___x_2385_; uint8_t v_isShared_2386_; uint8_t v_isSharedCheck_2436_; 
v_toInductionSubgoal_2379_ = lean_ctor_get(v_b_2367_, 0);
lean_inc_ref(v_toInductionSubgoal_2379_);
v_ctorName_2380_ = lean_ctor_get(v_b_2367_, 1);
v_mvarId_2381_ = lean_ctor_get(v_toInductionSubgoal_2379_, 0);
v_fields_2382_ = lean_ctor_get(v_toInductionSubgoal_2379_, 1);
v_subst_2383_ = lean_ctor_get(v_toInductionSubgoal_2379_, 2);
v_isSharedCheck_2436_ = !lean_is_exclusive(v_toInductionSubgoal_2379_);
if (v_isSharedCheck_2436_ == 0)
{
v___x_2385_ = v_toInductionSubgoal_2379_;
v_isShared_2386_ = v_isSharedCheck_2436_;
goto v_resetjp_2384_;
}
else
{
lean_inc(v_subst_2383_);
lean_inc(v_fields_2382_);
lean_inc(v_mvarId_2381_);
lean_dec(v_toInductionSubgoal_2379_);
v___x_2385_ = lean_box(0);
v_isShared_2386_ = v_isSharedCheck_2436_;
goto v_resetjp_2384_;
}
v_resetjp_2384_:
{
lean_object* v___x_2387_; lean_object* v___x_2388_; 
v___x_2387_ = lean_array_uget_borrowed(v_as_2364_, v_i_2365_);
lean_inc(v___x_2387_);
v___x_2388_ = l_Lean_Meta_FVarSubst_get(v_subst_2383_, v___x_2387_);
if (lean_obj_tag(v___x_2388_) == 1)
{
lean_object* v_fvarId_2389_; lean_object* v___x_2390_; 
v_fvarId_2389_ = lean_ctor_get(v___x_2388_, 0);
lean_inc(v_fvarId_2389_);
lean_dec_ref_known(v___x_2388_, 1);
v___x_2390_ = l_Lean_Meta_saveState___redArg(v___y_2369_, v___y_2371_);
if (lean_obj_tag(v___x_2390_) == 0)
{
lean_object* v_a_2391_; lean_object* v___x_2392_; 
v_a_2391_ = lean_ctor_get(v___x_2390_, 0);
lean_inc(v_a_2391_);
lean_dec_ref_known(v___x_2390_, 1);
v___x_2392_ = l_Lean_MVarId_clear(v_mvarId_2381_, v_fvarId_2389_, v___y_2368_, v___y_2369_, v___y_2370_, v___y_2371_);
if (lean_obj_tag(v___x_2392_) == 0)
{
lean_object* v___x_2394_; uint8_t v_isShared_2395_; uint8_t v_isSharedCheck_2404_; 
lean_inc(v_ctorName_2380_);
lean_dec(v_a_2391_);
v_isSharedCheck_2404_ = !lean_is_exclusive(v_b_2367_);
if (v_isSharedCheck_2404_ == 0)
{
lean_object* v_unused_2405_; lean_object* v_unused_2406_; 
v_unused_2405_ = lean_ctor_get(v_b_2367_, 1);
lean_dec(v_unused_2405_);
v_unused_2406_ = lean_ctor_get(v_b_2367_, 0);
lean_dec(v_unused_2406_);
v___x_2394_ = v_b_2367_;
v_isShared_2395_ = v_isSharedCheck_2404_;
goto v_resetjp_2393_;
}
else
{
lean_dec(v_b_2367_);
v___x_2394_ = lean_box(0);
v_isShared_2395_ = v_isSharedCheck_2404_;
goto v_resetjp_2393_;
}
v_resetjp_2393_:
{
lean_object* v_a_2396_; lean_object* v___x_2397_; lean_object* v___x_2399_; 
v_a_2396_ = lean_ctor_get(v___x_2392_, 0);
lean_inc(v_a_2396_);
lean_dec_ref_known(v___x_2392_, 1);
v___x_2397_ = l_Lean_Meta_FVarSubst_erase(v_subst_2383_, v___x_2387_);
if (v_isShared_2386_ == 0)
{
lean_ctor_set(v___x_2385_, 2, v___x_2397_);
lean_ctor_set(v___x_2385_, 0, v_a_2396_);
v___x_2399_ = v___x_2385_;
goto v_reusejp_2398_;
}
else
{
lean_object* v_reuseFailAlloc_2403_; 
v_reuseFailAlloc_2403_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2403_, 0, v_a_2396_);
lean_ctor_set(v_reuseFailAlloc_2403_, 1, v_fields_2382_);
lean_ctor_set(v_reuseFailAlloc_2403_, 2, v___x_2397_);
v___x_2399_ = v_reuseFailAlloc_2403_;
goto v_reusejp_2398_;
}
v_reusejp_2398_:
{
lean_object* v___x_2401_; 
if (v_isShared_2395_ == 0)
{
lean_ctor_set(v___x_2394_, 0, v___x_2399_);
v___x_2401_ = v___x_2394_;
goto v_reusejp_2400_;
}
else
{
lean_object* v_reuseFailAlloc_2402_; 
v_reuseFailAlloc_2402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2402_, 0, v___x_2399_);
lean_ctor_set(v_reuseFailAlloc_2402_, 1, v_ctorName_2380_);
v___x_2401_ = v_reuseFailAlloc_2402_;
goto v_reusejp_2400_;
}
v_reusejp_2400_:
{
v_a_2374_ = v___x_2401_;
goto v___jp_2373_;
}
}
}
}
else
{
lean_object* v_a_2407_; lean_object* v___x_2409_; uint8_t v_isShared_2410_; uint8_t v_isSharedCheck_2427_; 
lean_del_object(v___x_2385_);
lean_dec(v_subst_2383_);
lean_dec_ref(v_fields_2382_);
v_a_2407_ = lean_ctor_get(v___x_2392_, 0);
v_isSharedCheck_2427_ = !lean_is_exclusive(v___x_2392_);
if (v_isSharedCheck_2427_ == 0)
{
v___x_2409_ = v___x_2392_;
v_isShared_2410_ = v_isSharedCheck_2427_;
goto v_resetjp_2408_;
}
else
{
lean_inc(v_a_2407_);
lean_dec(v___x_2392_);
v___x_2409_ = lean_box(0);
v_isShared_2410_ = v_isSharedCheck_2427_;
goto v_resetjp_2408_;
}
v_resetjp_2408_:
{
lean_object* v___x_2412_; 
lean_inc(v_a_2407_);
if (v_isShared_2410_ == 0)
{
v___x_2412_ = v___x_2409_;
goto v_reusejp_2411_;
}
else
{
lean_object* v_reuseFailAlloc_2426_; 
v_reuseFailAlloc_2426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2426_, 0, v_a_2407_);
v___x_2412_ = v_reuseFailAlloc_2426_;
goto v_reusejp_2411_;
}
v_reusejp_2411_:
{
uint8_t v___y_2414_; uint8_t v___x_2424_; 
v___x_2424_ = l_Lean_Exception_isInterrupt(v_a_2407_);
if (v___x_2424_ == 0)
{
uint8_t v___x_2425_; 
v___x_2425_ = l_Lean_Exception_isRuntime(v_a_2407_);
v___y_2414_ = v___x_2425_;
goto v___jp_2413_;
}
else
{
lean_dec(v_a_2407_);
v___y_2414_ = v___x_2424_;
goto v___jp_2413_;
}
v___jp_2413_:
{
if (v___y_2414_ == 0)
{
lean_object* v___x_2415_; 
lean_dec_ref(v___x_2412_);
v___x_2415_ = l_Lean_Meta_SavedState_restore___redArg(v_a_2391_, v___y_2369_, v___y_2371_);
if (lean_obj_tag(v___x_2415_) == 0)
{
lean_dec_ref_known(v___x_2415_, 1);
v_a_2374_ = v_b_2367_;
goto v___jp_2373_;
}
else
{
lean_object* v_a_2416_; lean_object* v___x_2418_; uint8_t v_isShared_2419_; uint8_t v_isSharedCheck_2423_; 
lean_dec_ref(v_b_2367_);
v_a_2416_ = lean_ctor_get(v___x_2415_, 0);
v_isSharedCheck_2423_ = !lean_is_exclusive(v___x_2415_);
if (v_isSharedCheck_2423_ == 0)
{
v___x_2418_ = v___x_2415_;
v_isShared_2419_ = v_isSharedCheck_2423_;
goto v_resetjp_2417_;
}
else
{
lean_inc(v_a_2416_);
lean_dec(v___x_2415_);
v___x_2418_ = lean_box(0);
v_isShared_2419_ = v_isSharedCheck_2423_;
goto v_resetjp_2417_;
}
v_resetjp_2417_:
{
lean_object* v___x_2421_; 
if (v_isShared_2419_ == 0)
{
v___x_2421_ = v___x_2418_;
goto v_reusejp_2420_;
}
else
{
lean_object* v_reuseFailAlloc_2422_; 
v_reuseFailAlloc_2422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2422_, 0, v_a_2416_);
v___x_2421_ = v_reuseFailAlloc_2422_;
goto v_reusejp_2420_;
}
v_reusejp_2420_:
{
return v___x_2421_;
}
}
}
}
else
{
lean_dec(v_a_2391_);
lean_dec_ref(v_b_2367_);
return v___x_2412_;
}
}
}
}
}
}
else
{
lean_object* v_a_2428_; lean_object* v___x_2430_; uint8_t v_isShared_2431_; uint8_t v_isSharedCheck_2435_; 
lean_dec(v_fvarId_2389_);
lean_del_object(v___x_2385_);
lean_dec(v_subst_2383_);
lean_dec_ref(v_fields_2382_);
lean_dec(v_mvarId_2381_);
lean_dec_ref(v_b_2367_);
v_a_2428_ = lean_ctor_get(v___x_2390_, 0);
v_isSharedCheck_2435_ = !lean_is_exclusive(v___x_2390_);
if (v_isSharedCheck_2435_ == 0)
{
v___x_2430_ = v___x_2390_;
v_isShared_2431_ = v_isSharedCheck_2435_;
goto v_resetjp_2429_;
}
else
{
lean_inc(v_a_2428_);
lean_dec(v___x_2390_);
v___x_2430_ = lean_box(0);
v_isShared_2431_ = v_isSharedCheck_2435_;
goto v_resetjp_2429_;
}
v_resetjp_2429_:
{
lean_object* v___x_2433_; 
if (v_isShared_2431_ == 0)
{
v___x_2433_ = v___x_2430_;
goto v_reusejp_2432_;
}
else
{
lean_object* v_reuseFailAlloc_2434_; 
v_reuseFailAlloc_2434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2434_, 0, v_a_2428_);
v___x_2433_ = v_reuseFailAlloc_2434_;
goto v_reusejp_2432_;
}
v_reusejp_2432_:
{
return v___x_2433_;
}
}
}
}
else
{
lean_dec_ref(v___x_2388_);
lean_del_object(v___x_2385_);
lean_dec(v_subst_2383_);
lean_dec_ref(v_fields_2382_);
lean_dec(v_mvarId_2381_);
v_a_2374_ = v_b_2367_;
goto v___jp_2373_;
}
}
}
else
{
lean_object* v___x_2437_; 
v___x_2437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2437_, 0, v_b_2367_);
return v___x_2437_;
}
v___jp_2373_:
{
size_t v___x_2375_; size_t v___x_2376_; 
v___x_2375_ = ((size_t)1ULL);
v___x_2376_ = lean_usize_add(v_i_2365_, v___x_2375_);
v_i_2365_ = v___x_2376_;
v_b_2367_ = v_a_2374_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__0___boxed(lean_object* v_as_2438_, lean_object* v_i_2439_, lean_object* v_stop_2440_, lean_object* v_b_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_){
_start:
{
size_t v_i_boxed_2447_; size_t v_stop_boxed_2448_; lean_object* v_res_2449_; 
v_i_boxed_2447_ = lean_unbox_usize(v_i_2439_);
lean_dec(v_i_2439_);
v_stop_boxed_2448_ = lean_unbox_usize(v_stop_2440_);
lean_dec(v_stop_2440_);
v_res_2449_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__0(v_as_2438_, v_i_boxed_2447_, v_stop_boxed_2448_, v_b_2441_, v___y_2442_, v___y_2443_, v___y_2444_, v___y_2445_);
lean_dec(v___y_2445_);
lean_dec_ref(v___y_2444_);
lean_dec(v___y_2443_);
lean_dec_ref(v___y_2442_);
lean_dec_ref(v_as_2438_);
return v_res_2449_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__1(lean_object* v_indicesFVarIds_2450_, size_t v_sz_2451_, size_t v_i_2452_, lean_object* v_bs_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_){
_start:
{
uint8_t v___x_2459_; 
v___x_2459_ = lean_usize_dec_lt(v_i_2452_, v_sz_2451_);
if (v___x_2459_ == 0)
{
lean_object* v___x_2460_; 
v___x_2460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2460_, 0, v_bs_2453_);
return v___x_2460_;
}
else
{
lean_object* v_v_2461_; lean_object* v___x_2462_; lean_object* v_bs_x27_2463_; lean_object* v_a_2465_; lean_object* v___y_2471_; lean_object* v___x_2481_; uint8_t v___x_2482_; 
v_v_2461_ = lean_array_uget(v_bs_2453_, v_i_2452_);
v___x_2462_ = lean_unsigned_to_nat(0u);
v_bs_x27_2463_ = lean_array_uset(v_bs_2453_, v_i_2452_, v___x_2462_);
v___x_2481_ = lean_array_get_size(v_indicesFVarIds_2450_);
v___x_2482_ = lean_nat_dec_lt(v___x_2462_, v___x_2481_);
if (v___x_2482_ == 0)
{
v_a_2465_ = v_v_2461_;
goto v___jp_2464_;
}
else
{
uint8_t v___x_2483_; 
v___x_2483_ = lean_nat_dec_le(v___x_2481_, v___x_2481_);
if (v___x_2483_ == 0)
{
if (v___x_2482_ == 0)
{
v_a_2465_ = v_v_2461_;
goto v___jp_2464_;
}
else
{
size_t v___x_2484_; size_t v___x_2485_; lean_object* v___x_2486_; 
v___x_2484_ = ((size_t)0ULL);
v___x_2485_ = lean_usize_of_nat(v___x_2481_);
v___x_2486_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__0(v_indicesFVarIds_2450_, v___x_2484_, v___x_2485_, v_v_2461_, v___y_2454_, v___y_2455_, v___y_2456_, v___y_2457_);
v___y_2471_ = v___x_2486_;
goto v___jp_2470_;
}
}
else
{
size_t v___x_2487_; size_t v___x_2488_; lean_object* v___x_2489_; 
v___x_2487_ = ((size_t)0ULL);
v___x_2488_ = lean_usize_of_nat(v___x_2481_);
v___x_2489_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__0(v_indicesFVarIds_2450_, v___x_2487_, v___x_2488_, v_v_2461_, v___y_2454_, v___y_2455_, v___y_2456_, v___y_2457_);
v___y_2471_ = v___x_2489_;
goto v___jp_2470_;
}
}
v___jp_2464_:
{
size_t v___x_2466_; size_t v___x_2467_; lean_object* v___x_2468_; 
v___x_2466_ = ((size_t)1ULL);
v___x_2467_ = lean_usize_add(v_i_2452_, v___x_2466_);
v___x_2468_ = lean_array_uset(v_bs_x27_2463_, v_i_2452_, v_a_2465_);
v_i_2452_ = v___x_2467_;
v_bs_2453_ = v___x_2468_;
goto _start;
}
v___jp_2470_:
{
if (lean_obj_tag(v___y_2471_) == 0)
{
lean_object* v_a_2472_; 
v_a_2472_ = lean_ctor_get(v___y_2471_, 0);
lean_inc(v_a_2472_);
lean_dec_ref_known(v___y_2471_, 1);
v_a_2465_ = v_a_2472_;
goto v___jp_2464_;
}
else
{
lean_object* v_a_2473_; lean_object* v___x_2475_; uint8_t v_isShared_2476_; uint8_t v_isSharedCheck_2480_; 
lean_dec_ref(v_bs_x27_2463_);
v_a_2473_ = lean_ctor_get(v___y_2471_, 0);
v_isSharedCheck_2480_ = !lean_is_exclusive(v___y_2471_);
if (v_isSharedCheck_2480_ == 0)
{
v___x_2475_ = v___y_2471_;
v_isShared_2476_ = v_isSharedCheck_2480_;
goto v_resetjp_2474_;
}
else
{
lean_inc(v_a_2473_);
lean_dec(v___y_2471_);
v___x_2475_ = lean_box(0);
v_isShared_2476_ = v_isSharedCheck_2480_;
goto v_resetjp_2474_;
}
v_resetjp_2474_:
{
lean_object* v___x_2478_; 
if (v_isShared_2476_ == 0)
{
v___x_2478_ = v___x_2475_;
goto v_reusejp_2477_;
}
else
{
lean_object* v_reuseFailAlloc_2479_; 
v_reuseFailAlloc_2479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2479_, 0, v_a_2473_);
v___x_2478_ = v_reuseFailAlloc_2479_;
goto v_reusejp_2477_;
}
v_reusejp_2477_:
{
return v___x_2478_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__1___boxed(lean_object* v_indicesFVarIds_2490_, lean_object* v_sz_2491_, lean_object* v_i_2492_, lean_object* v_bs_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_){
_start:
{
size_t v_sz_boxed_2499_; size_t v_i_boxed_2500_; lean_object* v_res_2501_; 
v_sz_boxed_2499_ = lean_unbox_usize(v_sz_2491_);
lean_dec(v_sz_2491_);
v_i_boxed_2500_ = lean_unbox_usize(v_i_2492_);
lean_dec(v_i_2492_);
v_res_2501_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__1(v_indicesFVarIds_2490_, v_sz_boxed_2499_, v_i_boxed_2500_, v_bs_2493_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_);
lean_dec(v___y_2497_);
lean_dec_ref(v___y_2496_);
lean_dec(v___y_2495_);
lean_dec_ref(v___y_2494_);
lean_dec_ref(v_indicesFVarIds_2490_);
return v_res_2501_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices(lean_object* v_s_u2081_2502_, lean_object* v_s_u2082_2503_, lean_object* v_a_2504_, lean_object* v_a_2505_, lean_object* v_a_2506_, lean_object* v_a_2507_){
_start:
{
lean_object* v_indicesFVarIds_2509_; size_t v_sz_2510_; size_t v___x_2511_; lean_object* v___x_2512_; 
v_indicesFVarIds_2509_ = lean_ctor_get(v_s_u2081_2502_, 1);
v_sz_2510_ = lean_array_size(v_s_u2082_2503_);
v___x_2511_ = ((size_t)0ULL);
v___x_2512_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__1(v_indicesFVarIds_2509_, v_sz_2510_, v___x_2511_, v_s_u2082_2503_, v_a_2504_, v_a_2505_, v_a_2506_, v_a_2507_);
return v___x_2512_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices___boxed(lean_object* v_s_u2081_2513_, lean_object* v_s_u2082_2514_, lean_object* v_a_2515_, lean_object* v_a_2516_, lean_object* v_a_2517_, lean_object* v_a_2518_, lean_object* v_a_2519_){
_start:
{
lean_object* v_res_2520_; 
v_res_2520_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices(v_s_u2081_2513_, v_s_u2082_2514_, v_a_2515_, v_a_2516_, v_a_2517_, v_a_2518_);
lean_dec(v_a_2518_);
lean_dec_ref(v_a_2517_);
lean_dec(v_a_2516_);
lean_dec_ref(v_a_2515_);
lean_dec_ref(v_s_u2081_2513_);
return v_res_2520_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0___redArg(lean_object* v_ctorNames_2521_, lean_object* v_us_2522_, lean_object* v_params_2523_, lean_object* v_majorFVarId_2524_, size_t v_sz_2525_, size_t v_i_2526_, lean_object* v_bs_2527_){
_start:
{
uint8_t v___x_2528_; 
v___x_2528_ = lean_usize_dec_lt(v_i_2526_, v_sz_2525_);
if (v___x_2528_ == 0)
{
lean_dec(v_majorFVarId_2524_);
lean_dec(v_us_2522_);
return v_bs_2527_;
}
else
{
lean_object* v_v_2529_; lean_object* v___x_2530_; lean_object* v_bs_x27_2531_; lean_object* v___y_2533_; lean_object* v___x_2538_; lean_object* v___x_2539_; uint8_t v___x_2540_; 
v_v_2529_ = lean_array_uget(v_bs_2527_, v_i_2526_);
v___x_2530_ = lean_unsigned_to_nat(0u);
v_bs_x27_2531_ = lean_array_uset(v_bs_2527_, v_i_2526_, v___x_2530_);
v___x_2538_ = lean_usize_to_nat(v_i_2526_);
v___x_2539_ = lean_array_get_size(v_ctorNames_2521_);
v___x_2540_ = lean_nat_dec_lt(v___x_2538_, v___x_2539_);
if (v___x_2540_ == 0)
{
lean_object* v___x_2541_; lean_object* v___x_2542_; 
lean_dec(v___x_2538_);
v___x_2541_ = lean_box(0);
v___x_2542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2542_, 0, v_v_2529_);
lean_ctor_set(v___x_2542_, 1, v___x_2541_);
v___y_2533_ = v___x_2542_;
goto v___jp_2532_;
}
else
{
lean_object* v_mvarId_2543_; lean_object* v_fields_2544_; lean_object* v_subst_2545_; lean_object* v___x_2547_; uint8_t v_isShared_2548_; uint8_t v_isSharedCheck_2560_; 
v_mvarId_2543_ = lean_ctor_get(v_v_2529_, 0);
v_fields_2544_ = lean_ctor_get(v_v_2529_, 1);
v_subst_2545_ = lean_ctor_get(v_v_2529_, 2);
v_isSharedCheck_2560_ = !lean_is_exclusive(v_v_2529_);
if (v_isSharedCheck_2560_ == 0)
{
v___x_2547_ = v_v_2529_;
v_isShared_2548_ = v_isSharedCheck_2560_;
goto v_resetjp_2546_;
}
else
{
lean_inc(v_subst_2545_);
lean_inc(v_fields_2544_);
lean_inc(v_mvarId_2543_);
lean_dec(v_v_2529_);
v___x_2547_ = lean_box(0);
v_isShared_2548_ = v_isSharedCheck_2560_;
goto v_resetjp_2546_;
}
v_resetjp_2546_:
{
lean_object* v_ctorName_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v_ctorApp_2552_; lean_object* v___x_2553_; lean_object* v_subst_2554_; lean_object* v___x_2556_; 
v_ctorName_2549_ = lean_array_fget_borrowed(v_ctorNames_2521_, v___x_2538_);
lean_dec(v___x_2538_);
lean_inc(v_us_2522_);
lean_inc(v_ctorName_2549_);
v___x_2550_ = l_Lean_mkConst(v_ctorName_2549_, v_us_2522_);
v___x_2551_ = l_Lean_mkAppN(v___x_2550_, v_params_2523_);
v_ctorApp_2552_ = l_Lean_mkAppN(v___x_2551_, v_fields_2544_);
v___x_2553_ = l_Lean_Meta_FVarSubst_erase(v_subst_2545_, v_majorFVarId_2524_);
lean_inc(v_majorFVarId_2524_);
v_subst_2554_ = l_Lean_Meta_FVarSubst_insert(v___x_2553_, v_majorFVarId_2524_, v_ctorApp_2552_);
if (v_isShared_2548_ == 0)
{
lean_ctor_set(v___x_2547_, 2, v_subst_2554_);
v___x_2556_ = v___x_2547_;
goto v_reusejp_2555_;
}
else
{
lean_object* v_reuseFailAlloc_2559_; 
v_reuseFailAlloc_2559_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2559_, 0, v_mvarId_2543_);
lean_ctor_set(v_reuseFailAlloc_2559_, 1, v_fields_2544_);
lean_ctor_set(v_reuseFailAlloc_2559_, 2, v_subst_2554_);
v___x_2556_ = v_reuseFailAlloc_2559_;
goto v_reusejp_2555_;
}
v_reusejp_2555_:
{
lean_object* v___x_2557_; lean_object* v___x_2558_; 
lean_inc(v_ctorName_2549_);
v___x_2557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2557_, 0, v_ctorName_2549_);
v___x_2558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2558_, 0, v___x_2556_);
lean_ctor_set(v___x_2558_, 1, v___x_2557_);
v___y_2533_ = v___x_2558_;
goto v___jp_2532_;
}
}
}
v___jp_2532_:
{
size_t v___x_2534_; size_t v___x_2535_; lean_object* v___x_2536_; 
v___x_2534_ = ((size_t)1ULL);
v___x_2535_ = lean_usize_add(v_i_2526_, v___x_2534_);
v___x_2536_ = lean_array_uset(v_bs_x27_2531_, v_i_2526_, v___y_2533_);
v_i_2526_ = v___x_2535_;
v_bs_2527_ = v___x_2536_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0___redArg___boxed(lean_object* v_ctorNames_2561_, lean_object* v_us_2562_, lean_object* v_params_2563_, lean_object* v_majorFVarId_2564_, lean_object* v_sz_2565_, lean_object* v_i_2566_, lean_object* v_bs_2567_){
_start:
{
size_t v_sz_boxed_2568_; size_t v_i_boxed_2569_; lean_object* v_res_2570_; 
v_sz_boxed_2568_ = lean_unbox_usize(v_sz_2565_);
lean_dec(v_sz_2565_);
v_i_boxed_2569_ = lean_unbox_usize(v_i_2566_);
lean_dec(v_i_2566_);
v_res_2570_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0___redArg(v_ctorNames_2561_, v_us_2562_, v_params_2563_, v_majorFVarId_2564_, v_sz_boxed_2568_, v_i_boxed_2569_, v_bs_2567_);
lean_dec_ref(v_params_2563_);
lean_dec_ref(v_ctorNames_2561_);
return v_res_2570_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals(lean_object* v_s_2571_, lean_object* v_ctorNames_2572_, lean_object* v_majorFVarId_2573_, lean_object* v_us_2574_, lean_object* v_params_2575_){
_start:
{
size_t v_sz_2576_; size_t v___x_2577_; lean_object* v___x_2578_; 
v_sz_2576_ = lean_array_size(v_s_2571_);
v___x_2577_ = ((size_t)0ULL);
v___x_2578_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0___redArg(v_ctorNames_2572_, v_us_2574_, v_params_2575_, v_majorFVarId_2573_, v_sz_2576_, v___x_2577_, v_s_2571_);
return v___x_2578_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals___boxed(lean_object* v_s_2579_, lean_object* v_ctorNames_2580_, lean_object* v_majorFVarId_2581_, lean_object* v_us_2582_, lean_object* v_params_2583_){
_start:
{
lean_object* v_res_2584_; 
v_res_2584_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals(v_s_2579_, v_ctorNames_2580_, v_majorFVarId_2581_, v_us_2582_, v_params_2583_);
lean_dec_ref(v_params_2583_);
lean_dec_ref(v_ctorNames_2580_);
return v_res_2584_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0(lean_object* v_ctorNames_2585_, lean_object* v_us_2586_, lean_object* v_params_2587_, lean_object* v_majorFVarId_2588_, lean_object* v_as_2589_, size_t v_sz_2590_, size_t v_i_2591_, lean_object* v_bs_2592_){
_start:
{
lean_object* v___x_2593_; 
v___x_2593_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0___redArg(v_ctorNames_2585_, v_us_2586_, v_params_2587_, v_majorFVarId_2588_, v_sz_2590_, v_i_2591_, v_bs_2592_);
return v___x_2593_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0___boxed(lean_object* v_ctorNames_2594_, lean_object* v_us_2595_, lean_object* v_params_2596_, lean_object* v_majorFVarId_2597_, lean_object* v_as_2598_, lean_object* v_sz_2599_, lean_object* v_i_2600_, lean_object* v_bs_2601_){
_start:
{
size_t v_sz_boxed_2602_; size_t v_i_boxed_2603_; lean_object* v_res_2604_; 
v_sz_boxed_2602_ = lean_unbox_usize(v_sz_2599_);
lean_dec(v_sz_2599_);
v_i_boxed_2603_ = lean_unbox_usize(v_i_2600_);
lean_dec(v_i_2600_);
v_res_2604_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0(v_ctorNames_2594_, v_us_2595_, v_params_2596_, v_majorFVarId_2597_, v_as_2598_, v_sz_boxed_2602_, v_i_boxed_2603_, v_bs_2601_);
lean_dec_ref(v_as_2598_);
lean_dec_ref(v_params_2596_);
lean_dec_ref(v_ctorNames_2594_);
return v_res_2604_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_2610_; lean_object* v___x_2611_; 
v___x_2610_ = l_Lean_maxRecDepthErrorMessage;
v___x_2611_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2611_, 0, v___x_2610_);
return v___x_2611_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_2612_; lean_object* v___x_2613_; 
v___x_2612_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__3);
v___x_2613_ = l_Lean_MessageData_ofFormat(v___x_2612_);
return v___x_2613_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; 
v___x_2614_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__4);
v___x_2615_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__2));
v___x_2616_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2616_, 0, v___x_2615_);
lean_ctor_set(v___x_2616_, 1, v___x_2614_);
return v___x_2616_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg(lean_object* v_ref_2617_){
_start:
{
lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; 
v___x_2619_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__5);
v___x_2620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2620_, 0, v_ref_2617_);
lean_ctor_set(v___x_2620_, 1, v___x_2619_);
v___x_2621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2621_, 0, v___x_2620_);
return v___x_2621_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___boxed(lean_object* v_ref_2622_, lean_object* v___y_2623_){
_start:
{
lean_object* v_res_2624_; 
v_res_2624_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg(v_ref_2622_);
return v_res_2624_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0(lean_object* v_00_u03b1_2625_, lean_object* v_ref_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_){
_start:
{
lean_object* v___x_2632_; 
v___x_2632_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg(v_ref_2626_);
return v___x_2632_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___boxed(lean_object* v_00_u03b1_2633_, lean_object* v_ref_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_){
_start:
{
lean_object* v_res_2640_; 
v_res_2640_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0(v_00_u03b1_2633_, v_ref_2634_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_);
lean_dec(v___y_2638_);
lean_dec_ref(v___y_2637_);
lean_dec(v___y_2636_);
lean_dec_ref(v___y_2635_);
return v_res_2640_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_unifyEqs_x3f(lean_object* v_numEqs_2642_, lean_object* v_mvarId_2643_, lean_object* v_subst_2644_, lean_object* v_caseName_x3f_2645_, lean_object* v_a_2646_, lean_object* v_a_2647_, lean_object* v_a_2648_, lean_object* v_a_2649_){
_start:
{
lean_object* v_toCold_2651_; lean_object* v_currRecDepth_2652_; lean_object* v_ref_2653_; uint16_t v_optionFlags_2654_; uint8_t v_suppressElabErrors_2655_; uint8_t v_isRecordingDeps_2656_; lean_object* v_maxRecDepth_2657_; lean_object* v___x_2658_; uint8_t v___x_2659_; uint8_t v___x_2705_; 
v_toCold_2651_ = lean_ctor_get(v_a_2648_, 0);
lean_inc_ref(v_toCold_2651_);
v_currRecDepth_2652_ = lean_ctor_get(v_a_2648_, 1);
lean_inc(v_currRecDepth_2652_);
v_ref_2653_ = lean_ctor_get(v_a_2648_, 2);
lean_inc(v_ref_2653_);
v_optionFlags_2654_ = lean_ctor_get_uint16(v_a_2648_, sizeof(void*)*3);
v_suppressElabErrors_2655_ = lean_ctor_get_uint8(v_a_2648_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2656_ = lean_ctor_get_uint8(v_a_2648_, sizeof(void*)*3 + 3);
lean_dec_ref(v_a_2648_);
v_maxRecDepth_2657_ = lean_ctor_get(v_toCold_2651_, 3);
v___x_2658_ = lean_unsigned_to_nat(0u);
v___x_2659_ = lean_nat_dec_eq(v_numEqs_2642_, v___x_2658_);
v___x_2705_ = lean_nat_dec_eq(v_maxRecDepth_2657_, v___x_2658_);
if (v___x_2705_ == 0)
{
uint8_t v___x_2706_; 
v___x_2706_ = lean_nat_dec_eq(v_currRecDepth_2652_, v_maxRecDepth_2657_);
if (v___x_2706_ == 0)
{
goto v___jp_2660_;
}
else
{
lean_object* v___x_2707_; 
lean_dec(v_currRecDepth_2652_);
lean_dec_ref(v_toCold_2651_);
lean_dec(v_caseName_x3f_2645_);
lean_dec(v_subst_2644_);
lean_dec(v_mvarId_2643_);
lean_dec(v_numEqs_2642_);
v___x_2707_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg(v_ref_2653_);
return v___x_2707_;
}
}
else
{
goto v___jp_2660_;
}
v___jp_2660_:
{
if (v___x_2659_ == 0)
{
lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; 
v___x_2661_ = lean_unsigned_to_nat(1u);
v___x_2662_ = lean_nat_add(v_currRecDepth_2652_, v___x_2661_);
lean_dec(v_currRecDepth_2652_);
v___x_2663_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2663_, 0, v_toCold_2651_);
lean_ctor_set(v___x_2663_, 1, v___x_2662_);
lean_ctor_set(v___x_2663_, 2, v_ref_2653_);
lean_ctor_set_uint16(v___x_2663_, sizeof(void*)*3, v_optionFlags_2654_);
lean_ctor_set_uint8(v___x_2663_, sizeof(void*)*3 + 2, v_suppressElabErrors_2655_);
lean_ctor_set_uint8(v___x_2663_, sizeof(void*)*3 + 3, v_isRecordingDeps_2656_);
v___x_2664_ = l_Lean_Meta_intro1Core(v_mvarId_2643_, v___x_2659_, v_a_2646_, v_a_2647_, v___x_2663_, v_a_2649_);
if (lean_obj_tag(v___x_2664_) == 0)
{
lean_object* v_a_2665_; lean_object* v_fst_2666_; lean_object* v_snd_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; 
v_a_2665_ = lean_ctor_get(v___x_2664_, 0);
lean_inc(v_a_2665_);
lean_dec_ref_known(v___x_2664_, 1);
v_fst_2666_ = lean_ctor_get(v_a_2665_, 0);
lean_inc(v_fst_2666_);
v_snd_2667_ = lean_ctor_get(v_a_2665_, 1);
lean_inc(v_snd_2667_);
lean_dec(v_a_2665_);
v___x_2668_ = ((lean_object*)(l_Lean_Meta_Cases_unifyEqs_x3f___closed__0));
lean_inc(v_caseName_x3f_2645_);
v___x_2669_ = l_Lean_Meta_unifyEq_x3f(v_snd_2667_, v_fst_2666_, v_subst_2644_, v___x_2668_, v_caseName_x3f_2645_, v_a_2646_, v_a_2647_, v___x_2663_, v_a_2649_);
if (lean_obj_tag(v___x_2669_) == 0)
{
lean_object* v_a_2670_; lean_object* v___x_2672_; uint8_t v_isShared_2673_; uint8_t v_isSharedCheck_2685_; 
v_a_2670_ = lean_ctor_get(v___x_2669_, 0);
v_isSharedCheck_2685_ = !lean_is_exclusive(v___x_2669_);
if (v_isSharedCheck_2685_ == 0)
{
v___x_2672_ = v___x_2669_;
v_isShared_2673_ = v_isSharedCheck_2685_;
goto v_resetjp_2671_;
}
else
{
lean_inc(v_a_2670_);
lean_dec(v___x_2669_);
v___x_2672_ = lean_box(0);
v_isShared_2673_ = v_isSharedCheck_2685_;
goto v_resetjp_2671_;
}
v_resetjp_2671_:
{
if (lean_obj_tag(v_a_2670_) == 1)
{
lean_object* v_val_2674_; lean_object* v_mvarId_2675_; lean_object* v_subst_2676_; lean_object* v_numNewEqs_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; 
lean_del_object(v___x_2672_);
v_val_2674_ = lean_ctor_get(v_a_2670_, 0);
lean_inc(v_val_2674_);
lean_dec_ref_known(v_a_2670_, 1);
v_mvarId_2675_ = lean_ctor_get(v_val_2674_, 0);
lean_inc(v_mvarId_2675_);
v_subst_2676_ = lean_ctor_get(v_val_2674_, 1);
lean_inc(v_subst_2676_);
v_numNewEqs_2677_ = lean_ctor_get(v_val_2674_, 2);
lean_inc(v_numNewEqs_2677_);
lean_dec(v_val_2674_);
v___x_2678_ = lean_nat_sub(v_numEqs_2642_, v___x_2661_);
lean_dec(v_numEqs_2642_);
v___x_2679_ = lean_nat_add(v___x_2678_, v_numNewEqs_2677_);
lean_dec(v_numNewEqs_2677_);
lean_dec(v___x_2678_);
v_numEqs_2642_ = v___x_2679_;
v_mvarId_2643_ = v_mvarId_2675_;
v_subst_2644_ = v_subst_2676_;
v_a_2648_ = v___x_2663_;
goto _start;
}
else
{
lean_object* v___x_2681_; lean_object* v___x_2683_; 
lean_dec(v_a_2670_);
lean_dec_ref_known(v___x_2663_, 3);
lean_dec(v_caseName_x3f_2645_);
lean_dec(v_numEqs_2642_);
v___x_2681_ = lean_box(0);
if (v_isShared_2673_ == 0)
{
lean_ctor_set(v___x_2672_, 0, v___x_2681_);
v___x_2683_ = v___x_2672_;
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
lean_object* v_a_2686_; lean_object* v___x_2688_; uint8_t v_isShared_2689_; uint8_t v_isSharedCheck_2693_; 
lean_dec_ref_known(v___x_2663_, 3);
lean_dec(v_caseName_x3f_2645_);
lean_dec(v_numEqs_2642_);
v_a_2686_ = lean_ctor_get(v___x_2669_, 0);
v_isSharedCheck_2693_ = !lean_is_exclusive(v___x_2669_);
if (v_isSharedCheck_2693_ == 0)
{
v___x_2688_ = v___x_2669_;
v_isShared_2689_ = v_isSharedCheck_2693_;
goto v_resetjp_2687_;
}
else
{
lean_inc(v_a_2686_);
lean_dec(v___x_2669_);
v___x_2688_ = lean_box(0);
v_isShared_2689_ = v_isSharedCheck_2693_;
goto v_resetjp_2687_;
}
v_resetjp_2687_:
{
lean_object* v___x_2691_; 
if (v_isShared_2689_ == 0)
{
v___x_2691_ = v___x_2688_;
goto v_reusejp_2690_;
}
else
{
lean_object* v_reuseFailAlloc_2692_; 
v_reuseFailAlloc_2692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2692_, 0, v_a_2686_);
v___x_2691_ = v_reuseFailAlloc_2692_;
goto v_reusejp_2690_;
}
v_reusejp_2690_:
{
return v___x_2691_;
}
}
}
}
else
{
lean_object* v_a_2694_; lean_object* v___x_2696_; uint8_t v_isShared_2697_; uint8_t v_isSharedCheck_2701_; 
lean_dec_ref_known(v___x_2663_, 3);
lean_dec(v_caseName_x3f_2645_);
lean_dec(v_subst_2644_);
lean_dec(v_numEqs_2642_);
v_a_2694_ = lean_ctor_get(v___x_2664_, 0);
v_isSharedCheck_2701_ = !lean_is_exclusive(v___x_2664_);
if (v_isSharedCheck_2701_ == 0)
{
v___x_2696_ = v___x_2664_;
v_isShared_2697_ = v_isSharedCheck_2701_;
goto v_resetjp_2695_;
}
else
{
lean_inc(v_a_2694_);
lean_dec(v___x_2664_);
v___x_2696_ = lean_box(0);
v_isShared_2697_ = v_isSharedCheck_2701_;
goto v_resetjp_2695_;
}
v_resetjp_2695_:
{
lean_object* v___x_2699_; 
if (v_isShared_2697_ == 0)
{
v___x_2699_ = v___x_2696_;
goto v_reusejp_2698_;
}
else
{
lean_object* v_reuseFailAlloc_2700_; 
v_reuseFailAlloc_2700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2700_, 0, v_a_2694_);
v___x_2699_ = v_reuseFailAlloc_2700_;
goto v_reusejp_2698_;
}
v_reusejp_2698_:
{
return v___x_2699_;
}
}
}
}
else
{
lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; 
lean_dec(v_ref_2653_);
lean_dec(v_currRecDepth_2652_);
lean_dec_ref(v_toCold_2651_);
lean_dec(v_caseName_x3f_2645_);
lean_dec(v_numEqs_2642_);
v___x_2702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2702_, 0, v_mvarId_2643_);
lean_ctor_set(v___x_2702_, 1, v_subst_2644_);
v___x_2703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2703_, 0, v___x_2702_);
v___x_2704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2704_, 0, v___x_2703_);
return v___x_2704_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_unifyEqs_x3f___boxed(lean_object* v_numEqs_2708_, lean_object* v_mvarId_2709_, lean_object* v_subst_2710_, lean_object* v_caseName_x3f_2711_, lean_object* v_a_2712_, lean_object* v_a_2713_, lean_object* v_a_2714_, lean_object* v_a_2715_, lean_object* v_a_2716_){
_start:
{
lean_object* v_res_2717_; 
v_res_2717_ = l_Lean_Meta_Cases_unifyEqs_x3f(v_numEqs_2708_, v_mvarId_2709_, v_subst_2710_, v_caseName_x3f_2711_, v_a_2712_, v_a_2713_, v_a_2714_, v_a_2715_);
lean_dec(v_a_2715_);
lean_dec(v_a_2713_);
lean_dec_ref(v_a_2712_);
return v_res_2717_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__0(lean_object* v_snd_2718_, size_t v_sz_2719_, size_t v_i_2720_, lean_object* v_bs_2721_){
_start:
{
uint8_t v___x_2722_; 
v___x_2722_ = lean_usize_dec_lt(v_i_2720_, v_sz_2719_);
if (v___x_2722_ == 0)
{
lean_dec(v_snd_2718_);
return v_bs_2721_;
}
else
{
lean_object* v_v_2723_; lean_object* v___x_2724_; lean_object* v_bs_x27_2725_; lean_object* v___x_2726_; size_t v___x_2727_; size_t v___x_2728_; lean_object* v___x_2729_; 
v_v_2723_ = lean_array_uget(v_bs_2721_, v_i_2720_);
v___x_2724_ = lean_unsigned_to_nat(0u);
v_bs_x27_2725_ = lean_array_uset(v_bs_2721_, v_i_2720_, v___x_2724_);
lean_inc(v_snd_2718_);
v___x_2726_ = l_Lean_Meta_FVarSubst_apply(v_snd_2718_, v_v_2723_);
lean_dec(v_v_2723_);
v___x_2727_ = ((size_t)1ULL);
v___x_2728_ = lean_usize_add(v_i_2720_, v___x_2727_);
v___x_2729_ = lean_array_uset(v_bs_x27_2725_, v_i_2720_, v___x_2726_);
v_i_2720_ = v___x_2728_;
v_bs_2721_ = v___x_2729_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__0___boxed(lean_object* v_snd_2731_, lean_object* v_sz_2732_, lean_object* v_i_2733_, lean_object* v_bs_2734_){
_start:
{
size_t v_sz_boxed_2735_; size_t v_i_boxed_2736_; lean_object* v_res_2737_; 
v_sz_boxed_2735_ = lean_unbox_usize(v_sz_2732_);
lean_dec(v_sz_2732_);
v_i_boxed_2736_ = lean_unbox_usize(v_i_2733_);
lean_dec(v_i_2733_);
v_res_2737_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__0(v_snd_2731_, v_sz_boxed_2735_, v_i_boxed_2736_, v_bs_2734_);
return v_res_2737_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1_spec__1(lean_object* v_numEqs_2738_, lean_object* v_as_2739_, size_t v_i_2740_, size_t v_stop_2741_, lean_object* v_b_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_){
_start:
{
lean_object* v_a_2749_; uint8_t v___x_2753_; 
v___x_2753_ = lean_usize_dec_eq(v_i_2740_, v_stop_2741_);
if (v___x_2753_ == 0)
{
lean_object* v___x_2754_; lean_object* v_toInductionSubgoal_2755_; lean_object* v_ctorName_2756_; lean_object* v___x_2758_; uint8_t v_isShared_2759_; uint8_t v_isSharedCheck_2790_; 
v___x_2754_ = lean_array_uget(v_as_2739_, v_i_2740_);
v_toInductionSubgoal_2755_ = lean_ctor_get(v___x_2754_, 0);
v_ctorName_2756_ = lean_ctor_get(v___x_2754_, 1);
v_isSharedCheck_2790_ = !lean_is_exclusive(v___x_2754_);
if (v_isSharedCheck_2790_ == 0)
{
v___x_2758_ = v___x_2754_;
v_isShared_2759_ = v_isSharedCheck_2790_;
goto v_resetjp_2757_;
}
else
{
lean_inc(v_ctorName_2756_);
lean_inc(v_toInductionSubgoal_2755_);
lean_dec(v___x_2754_);
v___x_2758_ = lean_box(0);
v_isShared_2759_ = v_isSharedCheck_2790_;
goto v_resetjp_2757_;
}
v_resetjp_2757_:
{
lean_object* v_mvarId_2760_; lean_object* v_fields_2761_; lean_object* v_subst_2762_; lean_object* v___x_2764_; uint8_t v_isShared_2765_; uint8_t v_isSharedCheck_2789_; 
v_mvarId_2760_ = lean_ctor_get(v_toInductionSubgoal_2755_, 0);
v_fields_2761_ = lean_ctor_get(v_toInductionSubgoal_2755_, 1);
v_subst_2762_ = lean_ctor_get(v_toInductionSubgoal_2755_, 2);
v_isSharedCheck_2789_ = !lean_is_exclusive(v_toInductionSubgoal_2755_);
if (v_isSharedCheck_2789_ == 0)
{
v___x_2764_ = v_toInductionSubgoal_2755_;
v_isShared_2765_ = v_isSharedCheck_2789_;
goto v_resetjp_2763_;
}
else
{
lean_inc(v_subst_2762_);
lean_inc(v_fields_2761_);
lean_inc(v_mvarId_2760_);
lean_dec(v_toInductionSubgoal_2755_);
v___x_2764_ = lean_box(0);
v_isShared_2765_ = v_isSharedCheck_2789_;
goto v_resetjp_2763_;
}
v_resetjp_2763_:
{
lean_object* v___x_2766_; 
lean_inc_ref(v___y_2745_);
lean_inc(v_ctorName_2756_);
lean_inc(v_numEqs_2738_);
v___x_2766_ = l_Lean_Meta_Cases_unifyEqs_x3f(v_numEqs_2738_, v_mvarId_2760_, v_subst_2762_, v_ctorName_2756_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_);
if (lean_obj_tag(v___x_2766_) == 0)
{
lean_object* v_a_2767_; 
v_a_2767_ = lean_ctor_get(v___x_2766_, 0);
lean_inc(v_a_2767_);
lean_dec_ref_known(v___x_2766_, 1);
if (lean_obj_tag(v_a_2767_) == 0)
{
lean_del_object(v___x_2764_);
lean_dec_ref(v_fields_2761_);
lean_del_object(v___x_2758_);
lean_dec(v_ctorName_2756_);
v_a_2749_ = v_b_2742_;
goto v___jp_2748_;
}
else
{
lean_object* v_val_2768_; lean_object* v_fst_2769_; lean_object* v_snd_2770_; size_t v_sz_2771_; size_t v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2775_; 
v_val_2768_ = lean_ctor_get(v_a_2767_, 0);
lean_inc(v_val_2768_);
lean_dec_ref_known(v_a_2767_, 1);
v_fst_2769_ = lean_ctor_get(v_val_2768_, 0);
lean_inc(v_fst_2769_);
v_snd_2770_ = lean_ctor_get(v_val_2768_, 1);
lean_inc_n(v_snd_2770_, 2);
lean_dec(v_val_2768_);
v_sz_2771_ = lean_array_size(v_fields_2761_);
v___x_2772_ = ((size_t)0ULL);
v___x_2773_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__0(v_snd_2770_, v_sz_2771_, v___x_2772_, v_fields_2761_);
if (v_isShared_2765_ == 0)
{
lean_ctor_set(v___x_2764_, 2, v_snd_2770_);
lean_ctor_set(v___x_2764_, 1, v___x_2773_);
lean_ctor_set(v___x_2764_, 0, v_fst_2769_);
v___x_2775_ = v___x_2764_;
goto v_reusejp_2774_;
}
else
{
lean_object* v_reuseFailAlloc_2780_; 
v_reuseFailAlloc_2780_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2780_, 0, v_fst_2769_);
lean_ctor_set(v_reuseFailAlloc_2780_, 1, v___x_2773_);
lean_ctor_set(v_reuseFailAlloc_2780_, 2, v_snd_2770_);
v___x_2775_ = v_reuseFailAlloc_2780_;
goto v_reusejp_2774_;
}
v_reusejp_2774_:
{
lean_object* v___x_2777_; 
if (v_isShared_2759_ == 0)
{
lean_ctor_set(v___x_2758_, 0, v___x_2775_);
v___x_2777_ = v___x_2758_;
goto v_reusejp_2776_;
}
else
{
lean_object* v_reuseFailAlloc_2779_; 
v_reuseFailAlloc_2779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2779_, 0, v___x_2775_);
lean_ctor_set(v_reuseFailAlloc_2779_, 1, v_ctorName_2756_);
v___x_2777_ = v_reuseFailAlloc_2779_;
goto v_reusejp_2776_;
}
v_reusejp_2776_:
{
lean_object* v___x_2778_; 
v___x_2778_ = lean_array_push(v_b_2742_, v___x_2777_);
v_a_2749_ = v___x_2778_;
goto v___jp_2748_;
}
}
}
}
else
{
lean_object* v_a_2781_; lean_object* v___x_2783_; uint8_t v_isShared_2784_; uint8_t v_isSharedCheck_2788_; 
lean_del_object(v___x_2764_);
lean_dec_ref(v_fields_2761_);
lean_del_object(v___x_2758_);
lean_dec(v_ctorName_2756_);
lean_dec_ref(v_b_2742_);
lean_dec(v_numEqs_2738_);
v_a_2781_ = lean_ctor_get(v___x_2766_, 0);
v_isSharedCheck_2788_ = !lean_is_exclusive(v___x_2766_);
if (v_isSharedCheck_2788_ == 0)
{
v___x_2783_ = v___x_2766_;
v_isShared_2784_ = v_isSharedCheck_2788_;
goto v_resetjp_2782_;
}
else
{
lean_inc(v_a_2781_);
lean_dec(v___x_2766_);
v___x_2783_ = lean_box(0);
v_isShared_2784_ = v_isSharedCheck_2788_;
goto v_resetjp_2782_;
}
v_resetjp_2782_:
{
lean_object* v___x_2786_; 
if (v_isShared_2784_ == 0)
{
v___x_2786_ = v___x_2783_;
goto v_reusejp_2785_;
}
else
{
lean_object* v_reuseFailAlloc_2787_; 
v_reuseFailAlloc_2787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2787_, 0, v_a_2781_);
v___x_2786_ = v_reuseFailAlloc_2787_;
goto v_reusejp_2785_;
}
v_reusejp_2785_:
{
return v___x_2786_;
}
}
}
}
}
}
else
{
lean_object* v___x_2791_; 
lean_dec(v_numEqs_2738_);
v___x_2791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2791_, 0, v_b_2742_);
return v___x_2791_;
}
v___jp_2748_:
{
size_t v___x_2750_; size_t v___x_2751_; 
v___x_2750_ = ((size_t)1ULL);
v___x_2751_ = lean_usize_add(v_i_2740_, v___x_2750_);
v_i_2740_ = v___x_2751_;
v_b_2742_ = v_a_2749_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1_spec__1___boxed(lean_object* v_numEqs_2792_, lean_object* v_as_2793_, lean_object* v_i_2794_, lean_object* v_stop_2795_, lean_object* v_b_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_){
_start:
{
size_t v_i_boxed_2802_; size_t v_stop_boxed_2803_; lean_object* v_res_2804_; 
v_i_boxed_2802_ = lean_unbox_usize(v_i_2794_);
lean_dec(v_i_2794_);
v_stop_boxed_2803_ = lean_unbox_usize(v_stop_2795_);
lean_dec(v_stop_2795_);
v_res_2804_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1_spec__1(v_numEqs_2792_, v_as_2793_, v_i_boxed_2802_, v_stop_boxed_2803_, v_b_2796_, v___y_2797_, v___y_2798_, v___y_2799_, v___y_2800_);
lean_dec(v___y_2800_);
lean_dec_ref(v___y_2799_);
lean_dec(v___y_2798_);
lean_dec_ref(v___y_2797_);
lean_dec_ref(v_as_2793_);
return v_res_2804_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1(lean_object* v_numEqs_2807_, lean_object* v_as_2808_, lean_object* v_start_2809_, lean_object* v_stop_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_){
_start:
{
lean_object* v___x_2816_; uint8_t v___x_2817_; 
v___x_2816_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1___closed__0));
v___x_2817_ = lean_nat_dec_lt(v_start_2809_, v_stop_2810_);
if (v___x_2817_ == 0)
{
lean_object* v___x_2818_; 
lean_dec(v_numEqs_2807_);
v___x_2818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2818_, 0, v___x_2816_);
return v___x_2818_;
}
else
{
lean_object* v___x_2819_; uint8_t v___x_2820_; 
v___x_2819_ = lean_array_get_size(v_as_2808_);
v___x_2820_ = lean_nat_dec_le(v_stop_2810_, v___x_2819_);
if (v___x_2820_ == 0)
{
uint8_t v___x_2821_; 
v___x_2821_ = lean_nat_dec_lt(v_start_2809_, v___x_2819_);
if (v___x_2821_ == 0)
{
lean_object* v___x_2822_; 
lean_dec(v_numEqs_2807_);
v___x_2822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2822_, 0, v___x_2816_);
return v___x_2822_;
}
else
{
size_t v___x_2823_; size_t v___x_2824_; lean_object* v___x_2825_; 
v___x_2823_ = lean_usize_of_nat(v_start_2809_);
v___x_2824_ = lean_usize_of_nat(v___x_2819_);
v___x_2825_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1_spec__1(v_numEqs_2807_, v_as_2808_, v___x_2823_, v___x_2824_, v___x_2816_, v___y_2811_, v___y_2812_, v___y_2813_, v___y_2814_);
return v___x_2825_;
}
}
else
{
size_t v___x_2826_; size_t v___x_2827_; lean_object* v___x_2828_; 
v___x_2826_ = lean_usize_of_nat(v_start_2809_);
v___x_2827_ = lean_usize_of_nat(v_stop_2810_);
v___x_2828_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1_spec__1(v_numEqs_2807_, v_as_2808_, v___x_2826_, v___x_2827_, v___x_2816_, v___y_2811_, v___y_2812_, v___y_2813_, v___y_2814_);
return v___x_2828_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1___boxed(lean_object* v_numEqs_2829_, lean_object* v_as_2830_, lean_object* v_start_2831_, lean_object* v_stop_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_){
_start:
{
lean_object* v_res_2838_; 
v_res_2838_ = l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1(v_numEqs_2829_, v_as_2830_, v_start_2831_, v_stop_2832_, v___y_2833_, v___y_2834_, v___y_2835_, v___y_2836_);
lean_dec(v___y_2836_);
lean_dec_ref(v___y_2835_);
lean_dec(v___y_2834_);
lean_dec_ref(v___y_2833_);
lean_dec(v_stop_2832_);
lean_dec(v_start_2831_);
lean_dec_ref(v_as_2830_);
return v_res_2838_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs(lean_object* v_numEqs_2839_, lean_object* v_subgoals_2840_, lean_object* v_a_2841_, lean_object* v_a_2842_, lean_object* v_a_2843_, lean_object* v_a_2844_){
_start:
{
lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; 
v___x_2846_ = lean_unsigned_to_nat(0u);
v___x_2847_ = lean_array_get_size(v_subgoals_2840_);
v___x_2848_ = l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1(v_numEqs_2839_, v_subgoals_2840_, v___x_2846_, v___x_2847_, v_a_2841_, v_a_2842_, v_a_2843_, v_a_2844_);
return v___x_2848_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs___boxed(lean_object* v_numEqs_2849_, lean_object* v_subgoals_2850_, lean_object* v_a_2851_, lean_object* v_a_2852_, lean_object* v_a_2853_, lean_object* v_a_2854_, lean_object* v_a_2855_){
_start:
{
lean_object* v_res_2856_; 
v_res_2856_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs(v_numEqs_2849_, v_subgoals_2850_, v_a_2851_, v_a_2852_, v_a_2853_, v_a_2854_);
lean_dec(v_a_2854_);
lean_dec_ref(v_a_2853_);
lean_dec(v_a_2852_);
lean_dec_ref(v_a_2851_);
lean_dec_ref(v_subgoals_2850_);
return v_res_2856_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0(lean_object* v___x_2868_, lean_object* v_ctx_2869_, lean_object* v_mvarId_2870_, lean_object* v_majorFVarId_2871_, lean_object* v_givenNames_2872_, uint8_t v_useNatCasesAuxOn_2873_, lean_object* v_interestingCtors_x3f_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_){
_start:
{
lean_object* v___x_2880_; 
lean_inc(v___y_2878_);
lean_inc_ref(v___y_2877_);
lean_inc(v___y_2876_);
lean_inc_ref(v___y_2875_);
v___x_2880_ = lean_infer_type(v___x_2868_, v___y_2875_, v___y_2876_, v___y_2877_, v___y_2878_);
if (lean_obj_tag(v___x_2880_) == 0)
{
lean_object* v_a_2881_; lean_object* v___x_2882_; 
v_a_2881_ = lean_ctor_get(v___x_2880_, 0);
lean_inc(v_a_2881_);
lean_dec_ref_known(v___x_2880_, 1);
v___x_2882_ = l_Lean_Meta_getInductiveUniverseAndParams(v_a_2881_, v___y_2875_, v___y_2876_, v___y_2877_, v___y_2878_);
if (lean_obj_tag(v___x_2882_) == 0)
{
lean_object* v_a_2883_; lean_object* v_fst_2884_; lean_object* v_snd_2885_; lean_object* v___y_2887_; lean_object* v___y_2888_; lean_object* v___y_2889_; lean_object* v___y_2890_; lean_object* v___y_2891_; lean_object* v___y_2914_; lean_object* v___y_2915_; lean_object* v___y_2916_; lean_object* v___y_2917_; lean_object* v___y_2923_; lean_object* v___y_2924_; lean_object* v___y_2925_; lean_object* v___y_2926_; 
v_a_2883_ = lean_ctor_get(v___x_2882_, 0);
lean_inc(v_a_2883_);
lean_dec_ref_known(v___x_2882_, 1);
v_fst_2884_ = lean_ctor_get(v_a_2883_, 0);
lean_inc(v_fst_2884_);
v_snd_2885_ = lean_ctor_get(v_a_2883_, 1);
lean_inc(v_snd_2885_);
lean_dec(v_a_2883_);
if (lean_obj_tag(v_interestingCtors_x3f_2874_) == 1)
{
lean_object* v_val_2936_; lean_object* v___x_2937_; lean_object* v_env_2938_; lean_object* v___x_2939_; uint8_t v___x_2940_; uint8_t v___x_2941_; lean_object* v___x_2942_; lean_object* v_inductiveVal_2943_; lean_object* v_toConstantVal_2944_; lean_object* v_ctors_2945_; lean_object* v_name_2946_; uint8_t v___y_2948_; 
v_val_2936_ = lean_ctor_get(v_interestingCtors_x3f_2874_, 0);
lean_inc(v_val_2936_);
lean_dec_ref_known(v_interestingCtors_x3f_2874_, 1);
v___x_2937_ = lean_st_ref_get(v___y_2878_);
v_env_2938_ = lean_ctor_get(v___x_2937_, 0);
lean_inc_ref(v_env_2938_);
lean_dec(v___x_2937_);
v___x_2939_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__5));
v___x_2940_ = 1;
v___x_2941_ = l_Lean_Environment_contains(v_env_2938_, v___x_2939_, v___x_2940_);
v___x_2942_ = lean_st_ref_get(v___y_2878_);
v_inductiveVal_2943_ = lean_ctor_get(v_ctx_2869_, 0);
v_toConstantVal_2944_ = lean_ctor_get(v_inductiveVal_2943_, 0);
v_ctors_2945_ = lean_ctor_get(v_inductiveVal_2943_, 4);
v_name_2946_ = lean_ctor_get(v_toConstantVal_2944_, 0);
if (v___x_2941_ == 0)
{
lean_dec(v___x_2942_);
v___y_2948_ = v___x_2941_;
goto v___jp_2947_;
}
else
{
lean_object* v_env_2982_; lean_object* v___x_2983_; uint8_t v___x_2984_; 
v_env_2982_ = lean_ctor_get(v___x_2942_, 0);
lean_inc_ref(v_env_2982_);
lean_dec(v___x_2942_);
lean_inc(v_name_2946_);
v___x_2983_ = l_Lean_mkCtorIdxName(v_name_2946_);
v___x_2984_ = l_Lean_Environment_contains(v_env_2982_, v___x_2983_, v___x_2940_);
v___y_2948_ = v___x_2984_;
goto v___jp_2947_;
}
v___jp_2947_:
{
if (v___y_2948_ == 0)
{
lean_dec(v_val_2936_);
v___y_2923_ = v___y_2875_;
v___y_2924_ = v___y_2876_;
v___y_2925_ = v___y_2877_;
v___y_2926_ = v___y_2878_;
goto v___jp_2922_;
}
else
{
lean_object* v___x_2949_; lean_object* v___x_2950_; uint8_t v___x_2951_; 
v___x_2949_ = lean_array_get_size(v_val_2936_);
v___x_2950_ = lean_unsigned_to_nat(0u);
v___x_2951_ = lean_nat_dec_eq(v___x_2949_, v___x_2950_);
if (v___x_2951_ == 0)
{
lean_object* v___x_2952_; uint8_t v___x_2953_; 
v___x_2952_ = l_List_lengthTR___redArg(v_ctors_2945_);
v___x_2953_ = lean_nat_dec_lt(v___x_2949_, v___x_2952_);
lean_dec(v___x_2952_);
if (v___x_2953_ == 0)
{
lean_dec(v_val_2936_);
v___y_2923_ = v___y_2875_;
v___y_2924_ = v___y_2876_;
v___y_2925_ = v___y_2877_;
v___y_2926_ = v___y_2878_;
goto v___jp_2922_;
}
else
{
lean_object* v___x_2954_; 
lean_inc(v_name_2946_);
lean_dec_ref(v_ctx_2869_);
lean_inc(v_val_2936_);
v___x_2954_ = l_Lean_Meta_mkSparseCasesOn(v_name_2946_, v_val_2936_, v___y_2875_, v___y_2876_, v___y_2877_, v___y_2878_);
if (lean_obj_tag(v___x_2954_) == 0)
{
lean_object* v_a_2955_; lean_object* v___x_2956_; 
v_a_2955_ = lean_ctor_get(v___x_2954_, 0);
lean_inc(v_a_2955_);
lean_dec_ref_known(v___x_2954_, 1);
lean_inc(v_majorFVarId_2871_);
v___x_2956_ = l_Lean_MVarId_induction(v_mvarId_2870_, v_majorFVarId_2871_, v_a_2955_, v_givenNames_2872_, v___y_2875_, v___y_2876_, v___y_2877_, v___y_2878_);
lean_dec(v___y_2878_);
lean_dec_ref(v___y_2877_);
lean_dec(v___y_2876_);
lean_dec_ref(v___y_2875_);
if (lean_obj_tag(v___x_2956_) == 0)
{
lean_object* v_a_2957_; lean_object* v___x_2959_; uint8_t v_isShared_2960_; uint8_t v_isSharedCheck_2965_; 
v_a_2957_ = lean_ctor_get(v___x_2956_, 0);
v_isSharedCheck_2965_ = !lean_is_exclusive(v___x_2956_);
if (v_isSharedCheck_2965_ == 0)
{
v___x_2959_ = v___x_2956_;
v_isShared_2960_ = v_isSharedCheck_2965_;
goto v_resetjp_2958_;
}
else
{
lean_inc(v_a_2957_);
lean_dec(v___x_2956_);
v___x_2959_ = lean_box(0);
v_isShared_2960_ = v_isSharedCheck_2965_;
goto v_resetjp_2958_;
}
v_resetjp_2958_:
{
lean_object* v___x_2961_; lean_object* v___x_2963_; 
v___x_2961_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals(v_a_2957_, v_val_2936_, v_majorFVarId_2871_, v_fst_2884_, v_snd_2885_);
lean_dec(v_snd_2885_);
lean_dec(v_val_2936_);
if (v_isShared_2960_ == 0)
{
lean_ctor_set(v___x_2959_, 0, v___x_2961_);
v___x_2963_ = v___x_2959_;
goto v_reusejp_2962_;
}
else
{
lean_object* v_reuseFailAlloc_2964_; 
v_reuseFailAlloc_2964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2964_, 0, v___x_2961_);
v___x_2963_ = v_reuseFailAlloc_2964_;
goto v_reusejp_2962_;
}
v_reusejp_2962_:
{
return v___x_2963_;
}
}
}
else
{
lean_object* v_a_2966_; lean_object* v___x_2968_; uint8_t v_isShared_2969_; uint8_t v_isSharedCheck_2973_; 
lean_dec(v_val_2936_);
lean_dec(v_snd_2885_);
lean_dec(v_fst_2884_);
lean_dec(v_majorFVarId_2871_);
v_a_2966_ = lean_ctor_get(v___x_2956_, 0);
v_isSharedCheck_2973_ = !lean_is_exclusive(v___x_2956_);
if (v_isSharedCheck_2973_ == 0)
{
v___x_2968_ = v___x_2956_;
v_isShared_2969_ = v_isSharedCheck_2973_;
goto v_resetjp_2967_;
}
else
{
lean_inc(v_a_2966_);
lean_dec(v___x_2956_);
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
lean_dec(v_val_2936_);
lean_dec(v_snd_2885_);
lean_dec(v_fst_2884_);
lean_dec(v___y_2878_);
lean_dec_ref(v___y_2877_);
lean_dec(v___y_2876_);
lean_dec_ref(v___y_2875_);
lean_dec_ref(v_givenNames_2872_);
lean_dec(v_majorFVarId_2871_);
lean_dec(v_mvarId_2870_);
v_a_2974_ = lean_ctor_get(v___x_2954_, 0);
v_isSharedCheck_2981_ = !lean_is_exclusive(v___x_2954_);
if (v_isSharedCheck_2981_ == 0)
{
v___x_2976_ = v___x_2954_;
v_isShared_2977_ = v_isSharedCheck_2981_;
goto v_resetjp_2975_;
}
else
{
lean_inc(v_a_2974_);
lean_dec(v___x_2954_);
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
}
else
{
lean_dec(v_val_2936_);
v___y_2923_ = v___y_2875_;
v___y_2924_ = v___y_2876_;
v___y_2925_ = v___y_2877_;
v___y_2926_ = v___y_2878_;
goto v___jp_2922_;
}
}
}
}
else
{
lean_dec(v_interestingCtors_x3f_2874_);
v___y_2923_ = v___y_2875_;
v___y_2924_ = v___y_2876_;
v___y_2925_ = v___y_2877_;
v___y_2926_ = v___y_2878_;
goto v___jp_2922_;
}
v___jp_2886_:
{
lean_object* v_inductiveVal_2892_; lean_object* v_ctors_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; 
v_inductiveVal_2892_ = lean_ctor_get(v_ctx_2869_, 0);
lean_inc_ref(v_inductiveVal_2892_);
lean_dec_ref(v_ctx_2869_);
v_ctors_2893_ = lean_ctor_get(v_inductiveVal_2892_, 4);
lean_inc(v_ctors_2893_);
lean_dec_ref(v_inductiveVal_2892_);
v___x_2894_ = lean_array_mk(v_ctors_2893_);
lean_inc(v_majorFVarId_2871_);
v___x_2895_ = l_Lean_MVarId_induction(v_mvarId_2870_, v_majorFVarId_2871_, v___y_2891_, v_givenNames_2872_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_);
lean_dec(v___y_2890_);
lean_dec_ref(v___y_2889_);
lean_dec(v___y_2888_);
lean_dec_ref(v___y_2887_);
if (lean_obj_tag(v___x_2895_) == 0)
{
lean_object* v_a_2896_; lean_object* v___x_2898_; uint8_t v_isShared_2899_; uint8_t v_isSharedCheck_2904_; 
v_a_2896_ = lean_ctor_get(v___x_2895_, 0);
v_isSharedCheck_2904_ = !lean_is_exclusive(v___x_2895_);
if (v_isSharedCheck_2904_ == 0)
{
v___x_2898_ = v___x_2895_;
v_isShared_2899_ = v_isSharedCheck_2904_;
goto v_resetjp_2897_;
}
else
{
lean_inc(v_a_2896_);
lean_dec(v___x_2895_);
v___x_2898_ = lean_box(0);
v_isShared_2899_ = v_isSharedCheck_2904_;
goto v_resetjp_2897_;
}
v_resetjp_2897_:
{
lean_object* v___x_2900_; lean_object* v___x_2902_; 
v___x_2900_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals(v_a_2896_, v___x_2894_, v_majorFVarId_2871_, v_fst_2884_, v_snd_2885_);
lean_dec(v_snd_2885_);
lean_dec_ref(v___x_2894_);
if (v_isShared_2899_ == 0)
{
lean_ctor_set(v___x_2898_, 0, v___x_2900_);
v___x_2902_ = v___x_2898_;
goto v_reusejp_2901_;
}
else
{
lean_object* v_reuseFailAlloc_2903_; 
v_reuseFailAlloc_2903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2903_, 0, v___x_2900_);
v___x_2902_ = v_reuseFailAlloc_2903_;
goto v_reusejp_2901_;
}
v_reusejp_2901_:
{
return v___x_2902_;
}
}
}
else
{
lean_object* v_a_2905_; lean_object* v___x_2907_; uint8_t v_isShared_2908_; uint8_t v_isSharedCheck_2912_; 
lean_dec_ref(v___x_2894_);
lean_dec(v_snd_2885_);
lean_dec(v_fst_2884_);
lean_dec(v_majorFVarId_2871_);
v_a_2905_ = lean_ctor_get(v___x_2895_, 0);
v_isSharedCheck_2912_ = !lean_is_exclusive(v___x_2895_);
if (v_isSharedCheck_2912_ == 0)
{
v___x_2907_ = v___x_2895_;
v_isShared_2908_ = v_isSharedCheck_2912_;
goto v_resetjp_2906_;
}
else
{
lean_inc(v_a_2905_);
lean_dec(v___x_2895_);
v___x_2907_ = lean_box(0);
v_isShared_2908_ = v_isSharedCheck_2912_;
goto v_resetjp_2906_;
}
v_resetjp_2906_:
{
lean_object* v___x_2910_; 
if (v_isShared_2908_ == 0)
{
v___x_2910_ = v___x_2907_;
goto v_reusejp_2909_;
}
else
{
lean_object* v_reuseFailAlloc_2911_; 
v_reuseFailAlloc_2911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2911_, 0, v_a_2905_);
v___x_2910_ = v_reuseFailAlloc_2911_;
goto v_reusejp_2909_;
}
v_reusejp_2909_:
{
return v___x_2910_;
}
}
}
}
v___jp_2913_:
{
lean_object* v_inductiveVal_2918_; lean_object* v_toConstantVal_2919_; lean_object* v_name_2920_; lean_object* v___x_2921_; 
v_inductiveVal_2918_ = lean_ctor_get(v_ctx_2869_, 0);
v_toConstantVal_2919_ = lean_ctor_get(v_inductiveVal_2918_, 0);
v_name_2920_ = lean_ctor_get(v_toConstantVal_2919_, 0);
lean_inc(v_name_2920_);
v___x_2921_ = l_Lean_mkCasesOnName(v_name_2920_);
v___y_2887_ = v___y_2914_;
v___y_2888_ = v___y_2915_;
v___y_2889_ = v___y_2916_;
v___y_2890_ = v___y_2917_;
v___y_2891_ = v___x_2921_;
goto v___jp_2886_;
}
v___jp_2922_:
{
lean_object* v___x_2927_; 
v___x_2927_ = lean_st_ref_get(v___y_2926_);
if (v_useNatCasesAuxOn_2873_ == 0)
{
lean_dec(v___x_2927_);
v___y_2914_ = v___y_2923_;
v___y_2915_ = v___y_2924_;
v___y_2916_ = v___y_2925_;
v___y_2917_ = v___y_2926_;
goto v___jp_2913_;
}
else
{
lean_object* v_inductiveVal_2928_; lean_object* v_toConstantVal_2929_; lean_object* v_env_2930_; lean_object* v_name_2931_; lean_object* v___x_2932_; uint8_t v___x_2933_; 
v_inductiveVal_2928_ = lean_ctor_get(v_ctx_2869_, 0);
v_toConstantVal_2929_ = lean_ctor_get(v_inductiveVal_2928_, 0);
v_env_2930_ = lean_ctor_get(v___x_2927_, 0);
lean_inc_ref(v_env_2930_);
lean_dec(v___x_2927_);
v_name_2931_ = lean_ctor_get(v_toConstantVal_2929_, 0);
v___x_2932_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__1));
v___x_2933_ = lean_name_eq(v_name_2931_, v___x_2932_);
if (v___x_2933_ == 0)
{
lean_dec_ref(v_env_2930_);
v___y_2914_ = v___y_2923_;
v___y_2915_ = v___y_2924_;
v___y_2916_ = v___y_2925_;
v___y_2917_ = v___y_2926_;
goto v___jp_2913_;
}
else
{
lean_object* v___x_2934_; uint8_t v___x_2935_; 
v___x_2934_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__3));
v___x_2935_ = l_Lean_Environment_contains(v_env_2930_, v___x_2934_, v___x_2933_);
if (v___x_2935_ == 0)
{
v___y_2914_ = v___y_2923_;
v___y_2915_ = v___y_2924_;
v___y_2916_ = v___y_2925_;
v___y_2917_ = v___y_2926_;
goto v___jp_2913_;
}
else
{
v___y_2887_ = v___y_2923_;
v___y_2888_ = v___y_2924_;
v___y_2889_ = v___y_2925_;
v___y_2890_ = v___y_2926_;
v___y_2891_ = v___x_2934_;
goto v___jp_2886_;
}
}
}
}
}
else
{
lean_object* v_a_2985_; lean_object* v___x_2987_; uint8_t v_isShared_2988_; uint8_t v_isSharedCheck_2992_; 
lean_dec(v___y_2878_);
lean_dec_ref(v___y_2877_);
lean_dec(v___y_2876_);
lean_dec_ref(v___y_2875_);
lean_dec(v_interestingCtors_x3f_2874_);
lean_dec_ref(v_givenNames_2872_);
lean_dec(v_majorFVarId_2871_);
lean_dec(v_mvarId_2870_);
lean_dec_ref(v_ctx_2869_);
v_a_2985_ = lean_ctor_get(v___x_2882_, 0);
v_isSharedCheck_2992_ = !lean_is_exclusive(v___x_2882_);
if (v_isSharedCheck_2992_ == 0)
{
v___x_2987_ = v___x_2882_;
v_isShared_2988_ = v_isSharedCheck_2992_;
goto v_resetjp_2986_;
}
else
{
lean_inc(v_a_2985_);
lean_dec(v___x_2882_);
v___x_2987_ = lean_box(0);
v_isShared_2988_ = v_isSharedCheck_2992_;
goto v_resetjp_2986_;
}
v_resetjp_2986_:
{
lean_object* v___x_2990_; 
if (v_isShared_2988_ == 0)
{
v___x_2990_ = v___x_2987_;
goto v_reusejp_2989_;
}
else
{
lean_object* v_reuseFailAlloc_2991_; 
v_reuseFailAlloc_2991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2991_, 0, v_a_2985_);
v___x_2990_ = v_reuseFailAlloc_2991_;
goto v_reusejp_2989_;
}
v_reusejp_2989_:
{
return v___x_2990_;
}
}
}
}
else
{
lean_object* v_a_2993_; lean_object* v___x_2995_; uint8_t v_isShared_2996_; uint8_t v_isSharedCheck_3000_; 
lean_dec(v___y_2878_);
lean_dec_ref(v___y_2877_);
lean_dec(v___y_2876_);
lean_dec_ref(v___y_2875_);
lean_dec(v_interestingCtors_x3f_2874_);
lean_dec_ref(v_givenNames_2872_);
lean_dec(v_majorFVarId_2871_);
lean_dec(v_mvarId_2870_);
lean_dec_ref(v_ctx_2869_);
v_a_2993_ = lean_ctor_get(v___x_2880_, 0);
v_isSharedCheck_3000_ = !lean_is_exclusive(v___x_2880_);
if (v_isSharedCheck_3000_ == 0)
{
v___x_2995_ = v___x_2880_;
v_isShared_2996_ = v_isSharedCheck_3000_;
goto v_resetjp_2994_;
}
else
{
lean_inc(v_a_2993_);
lean_dec(v___x_2880_);
v___x_2995_ = lean_box(0);
v_isShared_2996_ = v_isSharedCheck_3000_;
goto v_resetjp_2994_;
}
v_resetjp_2994_:
{
lean_object* v___x_2998_; 
if (v_isShared_2996_ == 0)
{
v___x_2998_ = v___x_2995_;
goto v_reusejp_2997_;
}
else
{
lean_object* v_reuseFailAlloc_2999_; 
v_reuseFailAlloc_2999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2999_, 0, v_a_2993_);
v___x_2998_ = v_reuseFailAlloc_2999_;
goto v_reusejp_2997_;
}
v_reusejp_2997_:
{
return v___x_2998_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___boxed(lean_object* v___x_3001_, lean_object* v_ctx_3002_, lean_object* v_mvarId_3003_, lean_object* v_majorFVarId_3004_, lean_object* v_givenNames_3005_, lean_object* v_useNatCasesAuxOn_3006_, lean_object* v_interestingCtors_x3f_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_, lean_object* v___y_3012_){
_start:
{
uint8_t v_useNatCasesAuxOn_boxed_3013_; lean_object* v_res_3014_; 
v_useNatCasesAuxOn_boxed_3013_ = lean_unbox(v_useNatCasesAuxOn_3006_);
v_res_3014_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0(v___x_3001_, v_ctx_3002_, v_mvarId_3003_, v_majorFVarId_3004_, v_givenNames_3005_, v_useNatCasesAuxOn_boxed_3013_, v_interestingCtors_x3f_3007_, v___y_3008_, v___y_3009_, v___y_3010_, v___y_3011_);
return v_res_3014_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn(lean_object* v_mvarId_3015_, lean_object* v_majorFVarId_3016_, lean_object* v_givenNames_3017_, lean_object* v_ctx_3018_, uint8_t v_useNatCasesAuxOn_3019_, lean_object* v_interestingCtors_x3f_3020_, lean_object* v_a_3021_, lean_object* v_a_3022_, lean_object* v_a_3023_, lean_object* v_a_3024_){
_start:
{
lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___f_3028_; lean_object* v___x_3029_; 
lean_inc(v_majorFVarId_3016_);
v___x_3026_ = l_Lean_mkFVar(v_majorFVarId_3016_);
v___x_3027_ = lean_box(v_useNatCasesAuxOn_3019_);
lean_inc(v_mvarId_3015_);
v___f_3028_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___boxed), 12, 7);
lean_closure_set(v___f_3028_, 0, v___x_3026_);
lean_closure_set(v___f_3028_, 1, v_ctx_3018_);
lean_closure_set(v___f_3028_, 2, v_mvarId_3015_);
lean_closure_set(v___f_3028_, 3, v_majorFVarId_3016_);
lean_closure_set(v___f_3028_, 4, v_givenNames_3017_);
lean_closure_set(v___f_3028_, 5, v___x_3027_);
lean_closure_set(v___f_3028_, 6, v_interestingCtors_x3f_3020_);
v___x_3029_ = l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2___redArg(v_mvarId_3015_, v___f_3028_, v_a_3021_, v_a_3022_, v_a_3023_, v_a_3024_);
return v___x_3029_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___boxed(lean_object* v_mvarId_3030_, lean_object* v_majorFVarId_3031_, lean_object* v_givenNames_3032_, lean_object* v_ctx_3033_, lean_object* v_useNatCasesAuxOn_3034_, lean_object* v_interestingCtors_x3f_3035_, lean_object* v_a_3036_, lean_object* v_a_3037_, lean_object* v_a_3038_, lean_object* v_a_3039_, lean_object* v_a_3040_){
_start:
{
uint8_t v_useNatCasesAuxOn_boxed_3041_; lean_object* v_res_3042_; 
v_useNatCasesAuxOn_boxed_3041_ = lean_unbox(v_useNatCasesAuxOn_3034_);
v_res_3042_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn(v_mvarId_3030_, v_majorFVarId_3031_, v_givenNames_3032_, v_ctx_3033_, v_useNatCasesAuxOn_boxed_3041_, v_interestingCtors_x3f_3035_, v_a_3036_, v_a_3037_, v_a_3038_, v_a_3039_);
lean_dec(v_a_3039_);
lean_dec_ref(v_a_3038_);
lean_dec(v_a_3037_);
lean_dec_ref(v_a_3036_);
return v_res_3042_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0___closed__0(void){
_start:
{
lean_object* v___x_3043_; double v___x_3044_; 
v___x_3043_ = lean_unsigned_to_nat(0u);
v___x_3044_ = lean_float_of_nat(v___x_3043_);
return v___x_3044_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0(lean_object* v_cls_3048_, lean_object* v_msg_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_){
_start:
{
lean_object* v_ref_3055_; lean_object* v___x_3056_; lean_object* v_a_3057_; lean_object* v___x_3059_; uint8_t v_isShared_3060_; uint8_t v_isSharedCheck_3102_; 
v_ref_3055_ = lean_ctor_get(v___y_3052_, 2);
v___x_3056_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected_spec__0_spec__0(v_msg_3049_, v___y_3050_, v___y_3051_, v___y_3052_, v___y_3053_);
v_a_3057_ = lean_ctor_get(v___x_3056_, 0);
v_isSharedCheck_3102_ = !lean_is_exclusive(v___x_3056_);
if (v_isSharedCheck_3102_ == 0)
{
v___x_3059_ = v___x_3056_;
v_isShared_3060_ = v_isSharedCheck_3102_;
goto v_resetjp_3058_;
}
else
{
lean_inc(v_a_3057_);
lean_dec(v___x_3056_);
v___x_3059_ = lean_box(0);
v_isShared_3060_ = v_isSharedCheck_3102_;
goto v_resetjp_3058_;
}
v_resetjp_3058_:
{
lean_object* v___x_3061_; lean_object* v_traceState_3062_; lean_object* v_env_3063_; lean_object* v_nextMacroScope_3064_; lean_object* v_ngen_3065_; lean_object* v_auxDeclNGen_3066_; lean_object* v_cache_3067_; lean_object* v_recordedDeps_3068_; lean_object* v_messages_3069_; lean_object* v_infoState_3070_; lean_object* v_snapshotTasks_3071_; lean_object* v___x_3073_; uint8_t v_isShared_3074_; uint8_t v_isSharedCheck_3101_; 
v___x_3061_ = lean_st_ref_take(v___y_3053_);
v_traceState_3062_ = lean_ctor_get(v___x_3061_, 4);
v_env_3063_ = lean_ctor_get(v___x_3061_, 0);
v_nextMacroScope_3064_ = lean_ctor_get(v___x_3061_, 1);
v_ngen_3065_ = lean_ctor_get(v___x_3061_, 2);
v_auxDeclNGen_3066_ = lean_ctor_get(v___x_3061_, 3);
v_cache_3067_ = lean_ctor_get(v___x_3061_, 5);
v_recordedDeps_3068_ = lean_ctor_get(v___x_3061_, 6);
v_messages_3069_ = lean_ctor_get(v___x_3061_, 7);
v_infoState_3070_ = lean_ctor_get(v___x_3061_, 8);
v_snapshotTasks_3071_ = lean_ctor_get(v___x_3061_, 9);
v_isSharedCheck_3101_ = !lean_is_exclusive(v___x_3061_);
if (v_isSharedCheck_3101_ == 0)
{
v___x_3073_ = v___x_3061_;
v_isShared_3074_ = v_isSharedCheck_3101_;
goto v_resetjp_3072_;
}
else
{
lean_inc(v_snapshotTasks_3071_);
lean_inc(v_infoState_3070_);
lean_inc(v_messages_3069_);
lean_inc(v_recordedDeps_3068_);
lean_inc(v_cache_3067_);
lean_inc(v_traceState_3062_);
lean_inc(v_auxDeclNGen_3066_);
lean_inc(v_ngen_3065_);
lean_inc(v_nextMacroScope_3064_);
lean_inc(v_env_3063_);
lean_dec(v___x_3061_);
v___x_3073_ = lean_box(0);
v_isShared_3074_ = v_isSharedCheck_3101_;
goto v_resetjp_3072_;
}
v_resetjp_3072_:
{
uint64_t v_tid_3075_; lean_object* v_traces_3076_; lean_object* v___x_3078_; uint8_t v_isShared_3079_; uint8_t v_isSharedCheck_3100_; 
v_tid_3075_ = lean_ctor_get_uint64(v_traceState_3062_, sizeof(void*)*1);
v_traces_3076_ = lean_ctor_get(v_traceState_3062_, 0);
v_isSharedCheck_3100_ = !lean_is_exclusive(v_traceState_3062_);
if (v_isSharedCheck_3100_ == 0)
{
v___x_3078_ = v_traceState_3062_;
v_isShared_3079_ = v_isSharedCheck_3100_;
goto v_resetjp_3077_;
}
else
{
lean_inc(v_traces_3076_);
lean_dec(v_traceState_3062_);
v___x_3078_ = lean_box(0);
v_isShared_3079_ = v_isSharedCheck_3100_;
goto v_resetjp_3077_;
}
v_resetjp_3077_:
{
lean_object* v___x_3080_; lean_object* v___x_3081_; double v___x_3082_; uint8_t v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3091_; 
v___x_3080_ = lean_box(0);
v___x_3081_ = lean_box(0);
v___x_3082_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0___closed__0);
v___x_3083_ = 0;
v___x_3084_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0___closed__1));
v___x_3085_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3085_, 0, v_cls_3048_);
lean_ctor_set(v___x_3085_, 1, v___x_3081_);
lean_ctor_set(v___x_3085_, 2, v___x_3084_);
lean_ctor_set_float(v___x_3085_, sizeof(void*)*3, v___x_3082_);
lean_ctor_set_float(v___x_3085_, sizeof(void*)*3 + 8, v___x_3082_);
lean_ctor_set_uint8(v___x_3085_, sizeof(void*)*3 + 16, v___x_3083_);
v___x_3086_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0___closed__2));
v___x_3087_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3087_, 0, v___x_3085_);
lean_ctor_set(v___x_3087_, 1, v_a_3057_);
lean_ctor_set(v___x_3087_, 2, v___x_3086_);
lean_inc(v_ref_3055_);
v___x_3088_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3088_, 0, v_ref_3055_);
lean_ctor_set(v___x_3088_, 1, v___x_3087_);
v___x_3089_ = l_Lean_PersistentArray_push___redArg(v_traces_3076_, v___x_3088_);
if (v_isShared_3079_ == 0)
{
lean_ctor_set(v___x_3078_, 0, v___x_3089_);
v___x_3091_ = v___x_3078_;
goto v_reusejp_3090_;
}
else
{
lean_object* v_reuseFailAlloc_3099_; 
v_reuseFailAlloc_3099_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3099_, 0, v___x_3089_);
lean_ctor_set_uint64(v_reuseFailAlloc_3099_, sizeof(void*)*1, v_tid_3075_);
v___x_3091_ = v_reuseFailAlloc_3099_;
goto v_reusejp_3090_;
}
v_reusejp_3090_:
{
lean_object* v___x_3093_; 
if (v_isShared_3074_ == 0)
{
lean_ctor_set(v___x_3073_, 4, v___x_3091_);
v___x_3093_ = v___x_3073_;
goto v_reusejp_3092_;
}
else
{
lean_object* v_reuseFailAlloc_3098_; 
v_reuseFailAlloc_3098_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3098_, 0, v_env_3063_);
lean_ctor_set(v_reuseFailAlloc_3098_, 1, v_nextMacroScope_3064_);
lean_ctor_set(v_reuseFailAlloc_3098_, 2, v_ngen_3065_);
lean_ctor_set(v_reuseFailAlloc_3098_, 3, v_auxDeclNGen_3066_);
lean_ctor_set(v_reuseFailAlloc_3098_, 4, v___x_3091_);
lean_ctor_set(v_reuseFailAlloc_3098_, 5, v_cache_3067_);
lean_ctor_set(v_reuseFailAlloc_3098_, 6, v_recordedDeps_3068_);
lean_ctor_set(v_reuseFailAlloc_3098_, 7, v_messages_3069_);
lean_ctor_set(v_reuseFailAlloc_3098_, 8, v_infoState_3070_);
lean_ctor_set(v_reuseFailAlloc_3098_, 9, v_snapshotTasks_3071_);
v___x_3093_ = v_reuseFailAlloc_3098_;
goto v_reusejp_3092_;
}
v_reusejp_3092_:
{
lean_object* v___x_3094_; lean_object* v___x_3096_; 
v___x_3094_ = lean_st_ref_put(v___y_3053_, v___x_3093_);
if (v_isShared_3060_ == 0)
{
lean_ctor_set(v___x_3059_, 0, v___x_3080_);
v___x_3096_ = v___x_3059_;
goto v_reusejp_3095_;
}
else
{
lean_object* v_reuseFailAlloc_3097_; 
v_reuseFailAlloc_3097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3097_, 0, v___x_3080_);
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
lean_object* v_val_3143_; lean_object* v___x_3145_; uint8_t v_isShared_3146_; uint8_t v_isSharedCheck_3208_; 
lean_dec(v___x_3127_);
v_val_3143_ = lean_ctor_get(v_a_3140_, 0);
v_isSharedCheck_3208_ = !lean_is_exclusive(v_a_3140_);
if (v_isSharedCheck_3208_ == 0)
{
v___x_3145_ = v_a_3140_;
v_isShared_3146_ = v_isSharedCheck_3208_;
goto v_resetjp_3144_;
}
else
{
lean_inc(v_val_3143_);
lean_dec(v_a_3140_);
v___x_3145_ = lean_box(0);
v_isShared_3146_ = v_isSharedCheck_3208_;
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
lean_object* v_a_3151_; lean_object* v___y_3153_; lean_object* v___y_3154_; lean_object* v___y_3155_; lean_object* v___y_3156_; lean_object* v_toCold_3166_; lean_object* v_options_3167_; uint8_t v_hasTrace_3168_; 
v_a_3151_ = lean_ctor_get(v___x_3150_, 0);
lean_inc(v_a_3151_);
lean_dec_ref_known(v___x_3150_, 1);
v_toCold_3166_ = lean_ctor_get(v___y_3135_, 0);
v_options_3167_ = lean_ctor_get(v_toCold_3166_, 2);
v_hasTrace_3168_ = lean_ctor_get_uint8(v_options_3167_, sizeof(void*)*1);
if (v_hasTrace_3168_ == 0)
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
lean_object* v_inheritedTraceOptions_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; uint8_t v___x_3175_; 
v_inheritedTraceOptions_3169_ = lean_ctor_get(v_toCold_3166_, 11);
v___x_3170_ = ((lean_object*)(l_Lean_Meta_Cases_cases___lam__0___closed__4));
v___x_3171_ = ((lean_object*)(l_Lean_Meta_Cases_cases___lam__0___closed__5));
v___x_3172_ = l_Lean_Name_mkStr3(v___x_3170_, v___x_3171_, v___x_3131_);
v___x_3173_ = ((lean_object*)(l_Lean_Meta_Cases_cases___lam__0___closed__7));
lean_inc(v___x_3172_);
v___x_3174_ = l_Lean_Name_append(v___x_3173_, v___x_3172_);
v___x_3175_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3169_, v_options_3167_, v___x_3174_);
lean_dec(v___x_3174_);
if (v___x_3175_ == 0)
{
lean_dec(v___x_3172_);
lean_del_object(v___x_3145_);
v___y_3153_ = v___y_3133_;
v___y_3154_ = v___y_3134_;
v___y_3155_ = v___y_3135_;
v___y_3156_ = v___y_3136_;
goto v___jp_3152_;
}
else
{
lean_object* v_mvarId_3176_; lean_object* v___x_3177_; lean_object* v___x_3179_; 
v_mvarId_3176_ = lean_ctor_get(v_a_3151_, 0);
v___x_3177_ = lean_obj_once(&l_Lean_Meta_Cases_cases___lam__0___closed__9, &l_Lean_Meta_Cases_cases___lam__0___closed__9_once, _init_l_Lean_Meta_Cases_cases___lam__0___closed__9);
lean_inc(v_mvarId_3176_);
if (v_isShared_3146_ == 0)
{
lean_ctor_set(v___x_3145_, 0, v_mvarId_3176_);
v___x_3179_ = v___x_3145_;
goto v_reusejp_3178_;
}
else
{
lean_object* v_reuseFailAlloc_3190_; 
v_reuseFailAlloc_3190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3190_, 0, v_mvarId_3176_);
v___x_3179_ = v_reuseFailAlloc_3190_;
goto v_reusejp_3178_;
}
v_reusejp_3178_:
{
lean_object* v___x_3180_; lean_object* v___x_3181_; 
v___x_3180_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3180_, 0, v___x_3177_);
lean_ctor_set(v___x_3180_, 1, v___x_3179_);
v___x_3181_ = l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0(v___x_3172_, v___x_3180_, v___y_3133_, v___y_3134_, v___y_3135_, v___y_3136_);
if (lean_obj_tag(v___x_3181_) == 0)
{
lean_dec_ref_known(v___x_3181_, 1);
v___y_3153_ = v___y_3133_;
v___y_3154_ = v___y_3134_;
v___y_3155_ = v___y_3135_;
v___y_3156_ = v___y_3136_;
goto v___jp_3152_;
}
else
{
lean_object* v_a_3182_; lean_object* v___x_3184_; uint8_t v_isShared_3185_; uint8_t v_isSharedCheck_3189_; 
lean_dec(v_a_3151_);
lean_dec(v_a_3148_);
lean_dec(v_val_3143_);
lean_dec(v_interestingCtors_x3f_3130_);
lean_dec_ref(v_givenNames_3129_);
v_a_3182_ = lean_ctor_get(v___x_3181_, 0);
v_isSharedCheck_3189_ = !lean_is_exclusive(v___x_3181_);
if (v_isSharedCheck_3189_ == 0)
{
v___x_3184_ = v___x_3181_;
v_isShared_3185_ = v_isSharedCheck_3189_;
goto v_resetjp_3183_;
}
else
{
lean_inc(v_a_3182_);
lean_dec(v___x_3181_);
v___x_3184_ = lean_box(0);
v_isShared_3185_ = v_isSharedCheck_3189_;
goto v_resetjp_3183_;
}
v_resetjp_3183_:
{
lean_object* v___x_3187_; 
if (v_isShared_3185_ == 0)
{
v___x_3187_ = v___x_3184_;
goto v_reusejp_3186_;
}
else
{
lean_object* v_reuseFailAlloc_3188_; 
v_reuseFailAlloc_3188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3188_, 0, v_a_3182_);
v___x_3187_ = v_reuseFailAlloc_3188_;
goto v_reusejp_3186_;
}
v_reusejp_3186_:
{
return v___x_3187_;
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
lean_object* v_a_3191_; lean_object* v___x_3193_; uint8_t v_isShared_3194_; uint8_t v_isSharedCheck_3198_; 
lean_dec(v_a_3148_);
lean_del_object(v___x_3145_);
lean_dec(v_val_3143_);
lean_dec_ref(v___x_3131_);
lean_dec(v_interestingCtors_x3f_3130_);
lean_dec_ref(v_givenNames_3129_);
v_a_3191_ = lean_ctor_get(v___x_3150_, 0);
v_isSharedCheck_3198_ = !lean_is_exclusive(v___x_3150_);
if (v_isSharedCheck_3198_ == 0)
{
v___x_3193_ = v___x_3150_;
v_isShared_3194_ = v_isSharedCheck_3198_;
goto v_resetjp_3192_;
}
else
{
lean_inc(v_a_3191_);
lean_dec(v___x_3150_);
v___x_3193_ = lean_box(0);
v_isShared_3194_ = v_isSharedCheck_3198_;
goto v_resetjp_3192_;
}
v_resetjp_3192_:
{
lean_object* v___x_3196_; 
if (v_isShared_3194_ == 0)
{
v___x_3196_ = v___x_3193_;
goto v_reusejp_3195_;
}
else
{
lean_object* v_reuseFailAlloc_3197_; 
v_reuseFailAlloc_3197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3197_, 0, v_a_3191_);
v___x_3196_ = v_reuseFailAlloc_3197_;
goto v_reusejp_3195_;
}
v_reusejp_3195_:
{
return v___x_3196_;
}
}
}
}
else
{
lean_object* v___x_3199_; 
lean_dec(v_a_3148_);
lean_del_object(v___x_3145_);
lean_dec_ref(v___x_3131_);
v___x_3199_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn(v_mvarId_3126_, v_majorFVarId_3128_, v_givenNames_3129_, v_val_3143_, v_useNatCasesAuxOn_3132_, v_interestingCtors_x3f_3130_, v___y_3133_, v___y_3134_, v___y_3135_, v___y_3136_);
return v___x_3199_;
}
}
else
{
lean_object* v_a_3200_; lean_object* v___x_3202_; uint8_t v_isShared_3203_; uint8_t v_isSharedCheck_3207_; 
lean_del_object(v___x_3145_);
lean_dec(v_val_3143_);
lean_dec_ref(v___x_3131_);
lean_dec(v_interestingCtors_x3f_3130_);
lean_dec_ref(v_givenNames_3129_);
lean_dec(v_majorFVarId_3128_);
lean_dec(v_mvarId_3126_);
v_a_3200_ = lean_ctor_get(v___x_3147_, 0);
v_isSharedCheck_3207_ = !lean_is_exclusive(v___x_3147_);
if (v_isSharedCheck_3207_ == 0)
{
v___x_3202_ = v___x_3147_;
v_isShared_3203_ = v_isSharedCheck_3207_;
goto v_resetjp_3201_;
}
else
{
lean_inc(v_a_3200_);
lean_dec(v___x_3147_);
v___x_3202_ = lean_box(0);
v_isShared_3203_ = v_isSharedCheck_3207_;
goto v_resetjp_3201_;
}
v_resetjp_3201_:
{
lean_object* v___x_3205_; 
if (v_isShared_3203_ == 0)
{
v___x_3205_ = v___x_3202_;
goto v_reusejp_3204_;
}
else
{
lean_object* v_reuseFailAlloc_3206_; 
v_reuseFailAlloc_3206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3206_, 0, v_a_3200_);
v___x_3205_ = v_reuseFailAlloc_3206_;
goto v_reusejp_3204_;
}
v_reusejp_3204_:
{
return v___x_3205_;
}
}
}
}
}
}
else
{
lean_object* v_a_3209_; lean_object* v___x_3211_; uint8_t v_isShared_3212_; uint8_t v_isSharedCheck_3216_; 
lean_dec_ref(v___x_3131_);
lean_dec(v_interestingCtors_x3f_3130_);
lean_dec_ref(v_givenNames_3129_);
lean_dec(v_majorFVarId_3128_);
lean_dec(v___x_3127_);
lean_dec(v_mvarId_3126_);
v_a_3209_ = lean_ctor_get(v___x_3139_, 0);
v_isSharedCheck_3216_ = !lean_is_exclusive(v___x_3139_);
if (v_isSharedCheck_3216_ == 0)
{
v___x_3211_ = v___x_3139_;
v_isShared_3212_ = v_isSharedCheck_3216_;
goto v_resetjp_3210_;
}
else
{
lean_inc(v_a_3209_);
lean_dec(v___x_3139_);
v___x_3211_ = lean_box(0);
v_isShared_3212_ = v_isSharedCheck_3216_;
goto v_resetjp_3210_;
}
v_resetjp_3210_:
{
lean_object* v___x_3214_; 
if (v_isShared_3212_ == 0)
{
v___x_3214_ = v___x_3211_;
goto v_reusejp_3213_;
}
else
{
lean_object* v_reuseFailAlloc_3215_; 
v_reuseFailAlloc_3215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3215_, 0, v_a_3209_);
v___x_3214_ = v_reuseFailAlloc_3215_;
goto v_reusejp_3213_;
}
v_reusejp_3213_:
{
return v___x_3214_;
}
}
}
}
else
{
lean_object* v_a_3217_; lean_object* v___x_3219_; uint8_t v_isShared_3220_; uint8_t v_isSharedCheck_3224_; 
lean_dec_ref(v___x_3131_);
lean_dec(v_interestingCtors_x3f_3130_);
lean_dec_ref(v_givenNames_3129_);
lean_dec(v_majorFVarId_3128_);
lean_dec(v___x_3127_);
lean_dec(v_mvarId_3126_);
v_a_3217_ = lean_ctor_get(v___x_3138_, 0);
v_isSharedCheck_3224_ = !lean_is_exclusive(v___x_3138_);
if (v_isSharedCheck_3224_ == 0)
{
v___x_3219_ = v___x_3138_;
v_isShared_3220_ = v_isSharedCheck_3224_;
goto v_resetjp_3218_;
}
else
{
lean_inc(v_a_3217_);
lean_dec(v___x_3138_);
v___x_3219_ = lean_box(0);
v_isShared_3220_ = v_isSharedCheck_3224_;
goto v_resetjp_3218_;
}
v_resetjp_3218_:
{
lean_object* v___x_3222_; 
if (v_isShared_3220_ == 0)
{
v___x_3222_ = v___x_3219_;
goto v_reusejp_3221_;
}
else
{
lean_object* v_reuseFailAlloc_3223_; 
v_reuseFailAlloc_3223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3223_, 0, v_a_3217_);
v___x_3222_ = v_reuseFailAlloc_3223_;
goto v_reusejp_3221_;
}
v_reusejp_3221_:
{
return v___x_3222_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_cases___lam__0___boxed(lean_object* v_mvarId_3225_, lean_object* v___x_3226_, lean_object* v_majorFVarId_3227_, lean_object* v_givenNames_3228_, lean_object* v_interestingCtors_x3f_3229_, lean_object* v___x_3230_, lean_object* v_useNatCasesAuxOn_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_){
_start:
{
uint8_t v_useNatCasesAuxOn_boxed_3237_; lean_object* v_res_3238_; 
v_useNatCasesAuxOn_boxed_3237_ = lean_unbox(v_useNatCasesAuxOn_3231_);
v_res_3238_ = l_Lean_Meta_Cases_cases___lam__0(v_mvarId_3225_, v___x_3226_, v_majorFVarId_3227_, v_givenNames_3228_, v_interestingCtors_x3f_3229_, v___x_3230_, v_useNatCasesAuxOn_boxed_3237_, v___y_3232_, v___y_3233_, v___y_3234_, v___y_3235_);
lean_dec(v___y_3235_);
lean_dec_ref(v___y_3234_);
lean_dec(v___y_3233_);
lean_dec_ref(v___y_3232_);
return v_res_3238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_cases(lean_object* v_mvarId_3242_, lean_object* v_majorFVarId_3243_, lean_object* v_givenNames_3244_, uint8_t v_useNatCasesAuxOn_3245_, lean_object* v_interestingCtors_x3f_3246_, lean_object* v_a_3247_, lean_object* v_a_3248_, lean_object* v_a_3249_, lean_object* v_a_3250_){
_start:
{
lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___f_3255_; lean_object* v___x_3256_; 
v___x_3252_ = ((lean_object*)(l_Lean_Meta_Cases_cases___closed__0));
v___x_3253_ = ((lean_object*)(l_Lean_Meta_Cases_cases___closed__1));
v___x_3254_ = lean_box(v_useNatCasesAuxOn_3245_);
lean_inc(v_mvarId_3242_);
v___f_3255_ = lean_alloc_closure((void*)(l_Lean_Meta_Cases_cases___lam__0___boxed), 12, 7);
lean_closure_set(v___f_3255_, 0, v_mvarId_3242_);
lean_closure_set(v___f_3255_, 1, v___x_3253_);
lean_closure_set(v___f_3255_, 2, v_majorFVarId_3243_);
lean_closure_set(v___f_3255_, 3, v_givenNames_3244_);
lean_closure_set(v___f_3255_, 4, v_interestingCtors_x3f_3246_);
lean_closure_set(v___f_3255_, 5, v___x_3252_);
lean_closure_set(v___f_3255_, 6, v___x_3254_);
v___x_3256_ = l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2___redArg(v_mvarId_3242_, v___f_3255_, v_a_3247_, v_a_3248_, v_a_3249_, v_a_3250_);
if (lean_obj_tag(v___x_3256_) == 0)
{
return v___x_3256_;
}
else
{
lean_object* v_a_3257_; uint8_t v___y_3259_; uint8_t v___x_3261_; 
v_a_3257_ = lean_ctor_get(v___x_3256_, 0);
v___x_3261_ = l_Lean_Exception_isInterrupt(v_a_3257_);
if (v___x_3261_ == 0)
{
uint8_t v___x_3262_; 
lean_inc(v_a_3257_);
v___x_3262_ = l_Lean_Exception_isRuntime(v_a_3257_);
v___y_3259_ = v___x_3262_;
goto v___jp_3258_;
}
else
{
v___y_3259_ = v___x_3261_;
goto v___jp_3258_;
}
v___jp_3258_:
{
if (v___y_3259_ == 0)
{
lean_object* v___x_3260_; 
lean_inc(v_a_3257_);
lean_dec_ref_known(v___x_3256_, 1);
v___x_3260_ = l_Lean_Meta_throwNestedTacticEx___redArg(v___x_3253_, v_a_3257_, v_a_3247_, v_a_3248_, v_a_3249_, v_a_3250_);
return v___x_3260_;
}
else
{
return v___x_3256_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_cases___boxed(lean_object* v_mvarId_3263_, lean_object* v_majorFVarId_3264_, lean_object* v_givenNames_3265_, lean_object* v_useNatCasesAuxOn_3266_, lean_object* v_interestingCtors_x3f_3267_, lean_object* v_a_3268_, lean_object* v_a_3269_, lean_object* v_a_3270_, lean_object* v_a_3271_, lean_object* v_a_3272_){
_start:
{
uint8_t v_useNatCasesAuxOn_boxed_3273_; lean_object* v_res_3274_; 
v_useNatCasesAuxOn_boxed_3273_ = lean_unbox(v_useNatCasesAuxOn_3266_);
v_res_3274_ = l_Lean_Meta_Cases_cases(v_mvarId_3263_, v_majorFVarId_3264_, v_givenNames_3265_, v_useNatCasesAuxOn_boxed_3273_, v_interestingCtors_x3f_3267_, v_a_3268_, v_a_3269_, v_a_3270_, v_a_3271_);
lean_dec(v_a_3271_);
lean_dec_ref(v_a_3270_);
lean_dec(v_a_3269_);
lean_dec_ref(v_a_3268_);
return v_res_3274_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_cases(lean_object* v_mvarId_3275_, lean_object* v_majorFVarId_3276_, lean_object* v_givenNames_3277_, uint8_t v_useNatCasesAuxOn_3278_, lean_object* v_interestingCtors_x3f_3279_, lean_object* v_a_3280_, lean_object* v_a_3281_, lean_object* v_a_3282_, lean_object* v_a_3283_){
_start:
{
lean_object* v___x_3285_; 
v___x_3285_ = l_Lean_Meta_Cases_cases(v_mvarId_3275_, v_majorFVarId_3276_, v_givenNames_3277_, v_useNatCasesAuxOn_3278_, v_interestingCtors_x3f_3279_, v_a_3280_, v_a_3281_, v_a_3282_, v_a_3283_);
return v___x_3285_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_cases___boxed(lean_object* v_mvarId_3286_, lean_object* v_majorFVarId_3287_, lean_object* v_givenNames_3288_, lean_object* v_useNatCasesAuxOn_3289_, lean_object* v_interestingCtors_x3f_3290_, lean_object* v_a_3291_, lean_object* v_a_3292_, lean_object* v_a_3293_, lean_object* v_a_3294_, lean_object* v_a_3295_){
_start:
{
uint8_t v_useNatCasesAuxOn_boxed_3296_; lean_object* v_res_3297_; 
v_useNatCasesAuxOn_boxed_3296_ = lean_unbox(v_useNatCasesAuxOn_3289_);
v_res_3297_ = l_Lean_MVarId_cases(v_mvarId_3286_, v_majorFVarId_3287_, v_givenNames_3288_, v_useNatCasesAuxOn_boxed_3296_, v_interestingCtors_x3f_3290_, v_a_3291_, v_a_3292_, v_a_3293_, v_a_3294_);
lean_dec(v_a_3294_);
lean_dec_ref(v_a_3293_);
lean_dec(v_a_3292_);
lean_dec_ref(v_a_3291_);
return v_res_3297_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1___redArg(lean_object* v_x_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_){
_start:
{
lean_object* v___x_3304_; 
v___x_3304_ = l_Lean_Meta_saveState___redArg(v___y_3300_, v___y_3302_);
if (lean_obj_tag(v___x_3304_) == 0)
{
lean_object* v_a_3305_; lean_object* v___x_3306_; 
v_a_3305_ = lean_ctor_get(v___x_3304_, 0);
lean_inc(v_a_3305_);
lean_dec_ref_known(v___x_3304_, 1);
lean_inc(v___y_3302_);
lean_inc_ref(v___y_3301_);
lean_inc(v___y_3300_);
lean_inc_ref(v___y_3299_);
v___x_3306_ = lean_apply_5(v_x_3298_, v___y_3299_, v___y_3300_, v___y_3301_, v___y_3302_, lean_box(0));
if (lean_obj_tag(v___x_3306_) == 0)
{
lean_object* v_a_3307_; lean_object* v___x_3309_; uint8_t v_isShared_3310_; uint8_t v_isSharedCheck_3315_; 
lean_dec(v_a_3305_);
v_a_3307_ = lean_ctor_get(v___x_3306_, 0);
v_isSharedCheck_3315_ = !lean_is_exclusive(v___x_3306_);
if (v_isSharedCheck_3315_ == 0)
{
v___x_3309_ = v___x_3306_;
v_isShared_3310_ = v_isSharedCheck_3315_;
goto v_resetjp_3308_;
}
else
{
lean_inc(v_a_3307_);
lean_dec(v___x_3306_);
v___x_3309_ = lean_box(0);
v_isShared_3310_ = v_isSharedCheck_3315_;
goto v_resetjp_3308_;
}
v_resetjp_3308_:
{
lean_object* v___x_3311_; lean_object* v___x_3313_; 
v___x_3311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3311_, 0, v_a_3307_);
if (v_isShared_3310_ == 0)
{
lean_ctor_set(v___x_3309_, 0, v___x_3311_);
v___x_3313_ = v___x_3309_;
goto v_reusejp_3312_;
}
else
{
lean_object* v_reuseFailAlloc_3314_; 
v_reuseFailAlloc_3314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3314_, 0, v___x_3311_);
v___x_3313_ = v_reuseFailAlloc_3314_;
goto v_reusejp_3312_;
}
v_reusejp_3312_:
{
return v___x_3313_;
}
}
}
else
{
lean_object* v_a_3316_; lean_object* v___x_3318_; uint8_t v_isShared_3319_; uint8_t v_isSharedCheck_3345_; 
v_a_3316_ = lean_ctor_get(v___x_3306_, 0);
v_isSharedCheck_3345_ = !lean_is_exclusive(v___x_3306_);
if (v_isSharedCheck_3345_ == 0)
{
v___x_3318_ = v___x_3306_;
v_isShared_3319_ = v_isSharedCheck_3345_;
goto v_resetjp_3317_;
}
else
{
lean_inc(v_a_3316_);
lean_dec(v___x_3306_);
v___x_3318_ = lean_box(0);
v_isShared_3319_ = v_isSharedCheck_3345_;
goto v_resetjp_3317_;
}
v_resetjp_3317_:
{
uint8_t v___y_3321_; uint8_t v___x_3343_; 
v___x_3343_ = l_Lean_Exception_isInterrupt(v_a_3316_);
if (v___x_3343_ == 0)
{
uint8_t v___x_3344_; 
lean_inc(v_a_3316_);
v___x_3344_ = l_Lean_Exception_isRuntime(v_a_3316_);
v___y_3321_ = v___x_3344_;
goto v___jp_3320_;
}
else
{
v___y_3321_ = v___x_3343_;
goto v___jp_3320_;
}
v___jp_3320_:
{
if (v___y_3321_ == 0)
{
lean_object* v___x_3322_; 
lean_del_object(v___x_3318_);
lean_dec(v_a_3316_);
v___x_3322_ = l_Lean_Meta_SavedState_restore___redArg(v_a_3305_, v___y_3300_, v___y_3302_);
if (lean_obj_tag(v___x_3322_) == 0)
{
lean_object* v___x_3324_; uint8_t v_isShared_3325_; uint8_t v_isSharedCheck_3330_; 
v_isSharedCheck_3330_ = !lean_is_exclusive(v___x_3322_);
if (v_isSharedCheck_3330_ == 0)
{
lean_object* v_unused_3331_; 
v_unused_3331_ = lean_ctor_get(v___x_3322_, 0);
lean_dec(v_unused_3331_);
v___x_3324_ = v___x_3322_;
v_isShared_3325_ = v_isSharedCheck_3330_;
goto v_resetjp_3323_;
}
else
{
lean_dec(v___x_3322_);
v___x_3324_ = lean_box(0);
v_isShared_3325_ = v_isSharedCheck_3330_;
goto v_resetjp_3323_;
}
v_resetjp_3323_:
{
lean_object* v___x_3326_; lean_object* v___x_3328_; 
v___x_3326_ = lean_box(0);
if (v_isShared_3325_ == 0)
{
lean_ctor_set(v___x_3324_, 0, v___x_3326_);
v___x_3328_ = v___x_3324_;
goto v_reusejp_3327_;
}
else
{
lean_object* v_reuseFailAlloc_3329_; 
v_reuseFailAlloc_3329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3329_, 0, v___x_3326_);
v___x_3328_ = v_reuseFailAlloc_3329_;
goto v_reusejp_3327_;
}
v_reusejp_3327_:
{
return v___x_3328_;
}
}
}
else
{
lean_object* v_a_3332_; lean_object* v___x_3334_; uint8_t v_isShared_3335_; uint8_t v_isSharedCheck_3339_; 
v_a_3332_ = lean_ctor_get(v___x_3322_, 0);
v_isSharedCheck_3339_ = !lean_is_exclusive(v___x_3322_);
if (v_isSharedCheck_3339_ == 0)
{
v___x_3334_ = v___x_3322_;
v_isShared_3335_ = v_isSharedCheck_3339_;
goto v_resetjp_3333_;
}
else
{
lean_inc(v_a_3332_);
lean_dec(v___x_3322_);
v___x_3334_ = lean_box(0);
v_isShared_3335_ = v_isSharedCheck_3339_;
goto v_resetjp_3333_;
}
v_resetjp_3333_:
{
lean_object* v___x_3337_; 
if (v_isShared_3335_ == 0)
{
v___x_3337_ = v___x_3334_;
goto v_reusejp_3336_;
}
else
{
lean_object* v_reuseFailAlloc_3338_; 
v_reuseFailAlloc_3338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3338_, 0, v_a_3332_);
v___x_3337_ = v_reuseFailAlloc_3338_;
goto v_reusejp_3336_;
}
v_reusejp_3336_:
{
return v___x_3337_;
}
}
}
}
else
{
lean_object* v___x_3341_; 
lean_dec(v_a_3305_);
if (v_isShared_3319_ == 0)
{
v___x_3341_ = v___x_3318_;
goto v_reusejp_3340_;
}
else
{
lean_object* v_reuseFailAlloc_3342_; 
v_reuseFailAlloc_3342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3342_, 0, v_a_3316_);
v___x_3341_ = v_reuseFailAlloc_3342_;
goto v_reusejp_3340_;
}
v_reusejp_3340_:
{
return v___x_3341_;
}
}
}
}
}
}
else
{
lean_object* v_a_3346_; lean_object* v___x_3348_; uint8_t v_isShared_3349_; uint8_t v_isSharedCheck_3353_; 
lean_dec_ref(v_x_3298_);
v_a_3346_ = lean_ctor_get(v___x_3304_, 0);
v_isSharedCheck_3353_ = !lean_is_exclusive(v___x_3304_);
if (v_isSharedCheck_3353_ == 0)
{
v___x_3348_ = v___x_3304_;
v_isShared_3349_ = v_isSharedCheck_3353_;
goto v_resetjp_3347_;
}
else
{
lean_inc(v_a_3346_);
lean_dec(v___x_3304_);
v___x_3348_ = lean_box(0);
v_isShared_3349_ = v_isSharedCheck_3353_;
goto v_resetjp_3347_;
}
v_resetjp_3347_:
{
lean_object* v___x_3351_; 
if (v_isShared_3349_ == 0)
{
v___x_3351_ = v___x_3348_;
goto v_reusejp_3350_;
}
else
{
lean_object* v_reuseFailAlloc_3352_; 
v_reuseFailAlloc_3352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3352_, 0, v_a_3346_);
v___x_3351_ = v_reuseFailAlloc_3352_;
goto v_reusejp_3350_;
}
v_reusejp_3350_:
{
return v___x_3351_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1___redArg___boxed(lean_object* v_x_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_){
_start:
{
lean_object* v_res_3360_; 
v_res_3360_ = l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1___redArg(v_x_3354_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_);
lean_dec(v___y_3358_);
lean_dec_ref(v___y_3357_);
lean_dec(v___y_3356_);
lean_dec_ref(v___y_3355_);
return v_res_3360_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1(lean_object* v_00_u03b1_3361_, lean_object* v_x_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_){
_start:
{
lean_object* v___x_3368_; 
v___x_3368_ = l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1___redArg(v_x_3362_, v___y_3363_, v___y_3364_, v___y_3365_, v___y_3366_);
return v___x_3368_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1___boxed(lean_object* v_00_u03b1_3369_, lean_object* v_x_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_){
_start:
{
lean_object* v_res_3376_; 
v_res_3376_ = l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1(v_00_u03b1_3369_, v_x_3370_, v___y_3371_, v___y_3372_, v___y_3373_, v___y_3374_);
lean_dec(v___y_3374_);
lean_dec_ref(v___y_3373_);
lean_dec(v___y_3372_);
lean_dec_ref(v___y_3371_);
return v_res_3376_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_MVarId_casesRec_spec__0(lean_object* v_a_3377_, lean_object* v_a_3378_){
_start:
{
if (lean_obj_tag(v_a_3377_) == 0)
{
lean_object* v___x_3379_; 
v___x_3379_ = l_List_reverse___redArg(v_a_3378_);
return v___x_3379_;
}
else
{
lean_object* v_head_3380_; lean_object* v_toInductionSubgoal_3381_; lean_object* v_tail_3382_; lean_object* v___x_3384_; uint8_t v_isShared_3385_; uint8_t v_isSharedCheck_3391_; 
v_head_3380_ = lean_ctor_get(v_a_3377_, 0);
v_toInductionSubgoal_3381_ = lean_ctor_get(v_head_3380_, 0);
lean_inc_ref(v_toInductionSubgoal_3381_);
v_tail_3382_ = lean_ctor_get(v_a_3377_, 1);
v_isSharedCheck_3391_ = !lean_is_exclusive(v_a_3377_);
if (v_isSharedCheck_3391_ == 0)
{
lean_object* v_unused_3392_; 
v_unused_3392_ = lean_ctor_get(v_a_3377_, 0);
lean_dec(v_unused_3392_);
v___x_3384_ = v_a_3377_;
v_isShared_3385_ = v_isSharedCheck_3391_;
goto v_resetjp_3383_;
}
else
{
lean_inc(v_tail_3382_);
lean_dec(v_a_3377_);
v___x_3384_ = lean_box(0);
v_isShared_3385_ = v_isSharedCheck_3391_;
goto v_resetjp_3383_;
}
v_resetjp_3383_:
{
lean_object* v_mvarId_3386_; lean_object* v___x_3388_; 
v_mvarId_3386_ = lean_ctor_get(v_toInductionSubgoal_3381_, 0);
lean_inc(v_mvarId_3386_);
lean_dec_ref(v_toInductionSubgoal_3381_);
if (v_isShared_3385_ == 0)
{
lean_ctor_set(v___x_3384_, 1, v_a_3378_);
lean_ctor_set(v___x_3384_, 0, v_mvarId_3386_);
v___x_3388_ = v___x_3384_;
goto v_reusejp_3387_;
}
else
{
lean_object* v_reuseFailAlloc_3390_; 
v_reuseFailAlloc_3390_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3390_, 0, v_mvarId_3386_);
lean_ctor_set(v_reuseFailAlloc_3390_, 1, v_a_3378_);
v___x_3388_ = v_reuseFailAlloc_3390_;
goto v_reusejp_3387_;
}
v_reusejp_3387_:
{
v_a_3377_ = v_tail_3382_;
v_a_3378_ = v___x_3388_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3___lam__0(lean_object* v_mvarId_3393_, lean_object* v___x_3394_, lean_object* v___x_3395_, uint8_t v___x_3396_, lean_object* v___x_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_){
_start:
{
lean_object* v___x_3403_; 
v___x_3403_ = l_Lean_Meta_Cases_cases(v_mvarId_3393_, v___x_3394_, v___x_3395_, v___x_3396_, v___x_3397_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_);
if (lean_obj_tag(v___x_3403_) == 0)
{
lean_object* v_a_3404_; lean_object* v___x_3406_; uint8_t v_isShared_3407_; uint8_t v_isSharedCheck_3414_; 
v_a_3404_ = lean_ctor_get(v___x_3403_, 0);
v_isSharedCheck_3414_ = !lean_is_exclusive(v___x_3403_);
if (v_isSharedCheck_3414_ == 0)
{
v___x_3406_ = v___x_3403_;
v_isShared_3407_ = v_isSharedCheck_3414_;
goto v_resetjp_3405_;
}
else
{
lean_inc(v_a_3404_);
lean_dec(v___x_3403_);
v___x_3406_ = lean_box(0);
v_isShared_3407_ = v_isSharedCheck_3414_;
goto v_resetjp_3405_;
}
v_resetjp_3405_:
{
lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3412_; 
v___x_3408_ = lean_array_to_list(v_a_3404_);
v___x_3409_ = lean_box(0);
v___x_3410_ = l_List_mapTR_loop___at___00Lean_MVarId_casesRec_spec__0(v___x_3408_, v___x_3409_);
if (v_isShared_3407_ == 0)
{
lean_ctor_set(v___x_3406_, 0, v___x_3410_);
v___x_3412_ = v___x_3406_;
goto v_reusejp_3411_;
}
else
{
lean_object* v_reuseFailAlloc_3413_; 
v_reuseFailAlloc_3413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3413_, 0, v___x_3410_);
v___x_3412_ = v_reuseFailAlloc_3413_;
goto v_reusejp_3411_;
}
v_reusejp_3411_:
{
return v___x_3412_;
}
}
}
else
{
lean_object* v_a_3415_; lean_object* v___x_3417_; uint8_t v_isShared_3418_; uint8_t v_isSharedCheck_3422_; 
v_a_3415_ = lean_ctor_get(v___x_3403_, 0);
v_isSharedCheck_3422_ = !lean_is_exclusive(v___x_3403_);
if (v_isSharedCheck_3422_ == 0)
{
v___x_3417_ = v___x_3403_;
v_isShared_3418_ = v_isSharedCheck_3422_;
goto v_resetjp_3416_;
}
else
{
lean_inc(v_a_3415_);
lean_dec(v___x_3403_);
v___x_3417_ = lean_box(0);
v_isShared_3418_ = v_isSharedCheck_3422_;
goto v_resetjp_3416_;
}
v_resetjp_3416_:
{
lean_object* v___x_3420_; 
if (v_isShared_3418_ == 0)
{
v___x_3420_ = v___x_3417_;
goto v_reusejp_3419_;
}
else
{
lean_object* v_reuseFailAlloc_3421_; 
v_reuseFailAlloc_3421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3421_, 0, v_a_3415_);
v___x_3420_ = v_reuseFailAlloc_3421_;
goto v_reusejp_3419_;
}
v_reusejp_3419_:
{
return v___x_3420_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3___lam__0___boxed(lean_object* v_mvarId_3423_, lean_object* v___x_3424_, lean_object* v___x_3425_, lean_object* v___x_3426_, lean_object* v___x_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_){
_start:
{
uint8_t v___x_6247__boxed_3433_; lean_object* v_res_3434_; 
v___x_6247__boxed_3433_ = lean_unbox(v___x_3426_);
v_res_3434_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3___lam__0(v_mvarId_3423_, v___x_3424_, v___x_3425_, v___x_6247__boxed_3433_, v___x_3427_, v___y_3428_, v___y_3429_, v___y_3430_, v___y_3431_);
lean_dec(v___y_3431_);
lean_dec_ref(v___y_3430_);
lean_dec(v___y_3429_);
lean_dec_ref(v___y_3428_);
return v_res_3434_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5(lean_object* v_p_3440_, lean_object* v_mvarId_3441_, lean_object* v_as_3442_, size_t v_sz_3443_, size_t v_i_3444_, lean_object* v_b_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_){
_start:
{
uint8_t v___x_3451_; 
v___x_3451_ = lean_usize_dec_lt(v_i_3444_, v_sz_3443_);
if (v___x_3451_ == 0)
{
lean_object* v___x_3452_; 
lean_dec(v_mvarId_3441_);
lean_dec_ref(v_p_3440_);
v___x_3452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3452_, 0, v_b_3445_);
return v___x_3452_;
}
else
{
lean_object* v_snd_3453_; lean_object* v___x_3455_; uint8_t v_isShared_3456_; uint8_t v_isSharedCheck_3521_; 
v_snd_3453_ = lean_ctor_get(v_b_3445_, 1);
v_isSharedCheck_3521_ = !lean_is_exclusive(v_b_3445_);
if (v_isSharedCheck_3521_ == 0)
{
lean_object* v_unused_3522_; 
v_unused_3522_ = lean_ctor_get(v_b_3445_, 0);
lean_dec(v_unused_3522_);
v___x_3455_ = v_b_3445_;
v_isShared_3456_ = v_isSharedCheck_3521_;
goto v_resetjp_3454_;
}
else
{
lean_inc(v_snd_3453_);
lean_dec(v_b_3445_);
v___x_3455_ = lean_box(0);
v_isShared_3456_ = v_isSharedCheck_3521_;
goto v_resetjp_3454_;
}
v_resetjp_3454_:
{
lean_object* v___x_3457_; lean_object* v_a_3459_; lean_object* v_a_3466_; 
v___x_3457_ = lean_box(0);
v_a_3466_ = lean_array_uget(v_as_3442_, v_i_3444_);
if (lean_obj_tag(v_a_3466_) == 0)
{
v_a_3459_ = v_snd_3453_;
goto v___jp_3458_;
}
else
{
lean_object* v_val_3467_; lean_object* v___x_3469_; uint8_t v_isShared_3470_; uint8_t v_isSharedCheck_3520_; 
v_val_3467_ = lean_ctor_get(v_a_3466_, 0);
v_isSharedCheck_3520_ = !lean_is_exclusive(v_a_3466_);
if (v_isSharedCheck_3520_ == 0)
{
v___x_3469_ = v_a_3466_;
v_isShared_3470_ = v_isSharedCheck_3520_;
goto v_resetjp_3468_;
}
else
{
lean_inc(v_val_3467_);
lean_dec(v_a_3466_);
v___x_3469_ = lean_box(0);
v_isShared_3470_ = v_isSharedCheck_3520_;
goto v_resetjp_3468_;
}
v_resetjp_3468_:
{
lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; 
v___x_3471_ = lean_box(0);
v___x_3472_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5___closed__0));
lean_inc_ref(v_p_3440_);
lean_inc(v___y_3449_);
lean_inc_ref(v___y_3448_);
lean_inc(v___y_3447_);
lean_inc_ref(v___y_3446_);
lean_inc(v_val_3467_);
v___x_3473_ = lean_apply_6(v_p_3440_, v_val_3467_, v___y_3446_, v___y_3447_, v___y_3448_, v___y_3449_, lean_box(0));
if (lean_obj_tag(v___x_3473_) == 0)
{
lean_object* v_a_3474_; uint8_t v___x_3475_; 
v_a_3474_ = lean_ctor_get(v___x_3473_, 0);
lean_inc(v_a_3474_);
lean_dec_ref_known(v___x_3473_, 1);
v___x_3475_ = lean_unbox(v_a_3474_);
lean_dec(v_a_3474_);
if (v___x_3475_ == 0)
{
lean_del_object(v___x_3469_);
lean_dec(v_val_3467_);
lean_dec(v_snd_3453_);
v_a_3459_ = v___x_3472_;
goto v___jp_3458_;
}
else
{
lean_object* v___x_3476_; lean_object* v___x_3477_; uint8_t v___x_3478_; lean_object* v___x_3479_; lean_object* v___f_3480_; lean_object* v___x_3481_; 
v___x_3476_ = l_Lean_LocalDecl_fvarId(v_val_3467_);
lean_dec(v_val_3467_);
v___x_3477_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5___closed__1));
v___x_3478_ = 0;
v___x_3479_ = lean_box(v___x_3478_);
lean_inc(v_mvarId_3441_);
v___f_3480_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3___lam__0___boxed), 10, 5);
lean_closure_set(v___f_3480_, 0, v_mvarId_3441_);
lean_closure_set(v___f_3480_, 1, v___x_3476_);
lean_closure_set(v___f_3480_, 2, v___x_3477_);
lean_closure_set(v___f_3480_, 3, v___x_3479_);
lean_closure_set(v___f_3480_, 4, v___x_3457_);
v___x_3481_ = l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1___redArg(v___f_3480_, v___y_3446_, v___y_3447_, v___y_3448_, v___y_3449_);
if (lean_obj_tag(v___x_3481_) == 0)
{
lean_object* v_a_3482_; lean_object* v___x_3484_; uint8_t v_isShared_3485_; uint8_t v_isSharedCheck_3503_; 
v_a_3482_ = lean_ctor_get(v___x_3481_, 0);
v_isSharedCheck_3503_ = !lean_is_exclusive(v___x_3481_);
if (v_isSharedCheck_3503_ == 0)
{
v___x_3484_ = v___x_3481_;
v_isShared_3485_ = v_isSharedCheck_3503_;
goto v_resetjp_3483_;
}
else
{
lean_inc(v_a_3482_);
lean_dec(v___x_3481_);
v___x_3484_ = lean_box(0);
v_isShared_3485_ = v_isSharedCheck_3503_;
goto v_resetjp_3483_;
}
v_resetjp_3483_:
{
if (lean_obj_tag(v_a_3482_) == 0)
{
lean_del_object(v___x_3484_);
lean_del_object(v___x_3469_);
lean_dec(v_snd_3453_);
v_a_3459_ = v___x_3472_;
goto v___jp_3458_;
}
else
{
lean_object* v___x_3487_; 
lean_del_object(v___x_3455_);
lean_dec(v_mvarId_3441_);
lean_dec_ref(v_p_3440_);
lean_inc_ref(v_a_3482_);
if (v_isShared_3470_ == 0)
{
lean_ctor_set(v___x_3469_, 0, v_a_3482_);
v___x_3487_ = v___x_3469_;
goto v_reusejp_3486_;
}
else
{
lean_object* v_reuseFailAlloc_3502_; 
v_reuseFailAlloc_3502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3502_, 0, v_a_3482_);
v___x_3487_ = v_reuseFailAlloc_3502_;
goto v_reusejp_3486_;
}
v_reusejp_3486_:
{
lean_object* v___x_3489_; uint8_t v_isShared_3490_; uint8_t v_isSharedCheck_3500_; 
v_isSharedCheck_3500_ = !lean_is_exclusive(v_a_3482_);
if (v_isSharedCheck_3500_ == 0)
{
lean_object* v_unused_3501_; 
v_unused_3501_ = lean_ctor_get(v_a_3482_, 0);
lean_dec(v_unused_3501_);
v___x_3489_ = v_a_3482_;
v_isShared_3490_ = v_isSharedCheck_3500_;
goto v_resetjp_3488_;
}
else
{
lean_dec(v_a_3482_);
v___x_3489_ = lean_box(0);
v_isShared_3490_ = v_isSharedCheck_3500_;
goto v_resetjp_3488_;
}
v_resetjp_3488_:
{
lean_object* v___x_3491_; lean_object* v___x_3493_; 
v___x_3491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3491_, 0, v___x_3487_);
lean_ctor_set(v___x_3491_, 1, v___x_3471_);
if (v_isShared_3490_ == 0)
{
lean_ctor_set_tag(v___x_3489_, 0);
lean_ctor_set(v___x_3489_, 0, v___x_3491_);
v___x_3493_ = v___x_3489_;
goto v_reusejp_3492_;
}
else
{
lean_object* v_reuseFailAlloc_3499_; 
v_reuseFailAlloc_3499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3499_, 0, v___x_3491_);
v___x_3493_ = v_reuseFailAlloc_3499_;
goto v_reusejp_3492_;
}
v_reusejp_3492_:
{
lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3497_; 
v___x_3494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3494_, 0, v___x_3493_);
v___x_3495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3495_, 0, v___x_3494_);
lean_ctor_set(v___x_3495_, 1, v_snd_3453_);
if (v_isShared_3485_ == 0)
{
lean_ctor_set(v___x_3484_, 0, v___x_3495_);
v___x_3497_ = v___x_3484_;
goto v_reusejp_3496_;
}
else
{
lean_object* v_reuseFailAlloc_3498_; 
v_reuseFailAlloc_3498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3498_, 0, v___x_3495_);
v___x_3497_ = v_reuseFailAlloc_3498_;
goto v_reusejp_3496_;
}
v_reusejp_3496_:
{
return v___x_3497_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3504_; lean_object* v___x_3506_; uint8_t v_isShared_3507_; uint8_t v_isSharedCheck_3511_; 
lean_del_object(v___x_3469_);
lean_del_object(v___x_3455_);
lean_dec(v_snd_3453_);
lean_dec(v_mvarId_3441_);
lean_dec_ref(v_p_3440_);
v_a_3504_ = lean_ctor_get(v___x_3481_, 0);
v_isSharedCheck_3511_ = !lean_is_exclusive(v___x_3481_);
if (v_isSharedCheck_3511_ == 0)
{
v___x_3506_ = v___x_3481_;
v_isShared_3507_ = v_isSharedCheck_3511_;
goto v_resetjp_3505_;
}
else
{
lean_inc(v_a_3504_);
lean_dec(v___x_3481_);
v___x_3506_ = lean_box(0);
v_isShared_3507_ = v_isSharedCheck_3511_;
goto v_resetjp_3505_;
}
v_resetjp_3505_:
{
lean_object* v___x_3509_; 
if (v_isShared_3507_ == 0)
{
v___x_3509_ = v___x_3506_;
goto v_reusejp_3508_;
}
else
{
lean_object* v_reuseFailAlloc_3510_; 
v_reuseFailAlloc_3510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3510_, 0, v_a_3504_);
v___x_3509_ = v_reuseFailAlloc_3510_;
goto v_reusejp_3508_;
}
v_reusejp_3508_:
{
return v___x_3509_;
}
}
}
}
}
else
{
lean_object* v_a_3512_; lean_object* v___x_3514_; uint8_t v_isShared_3515_; uint8_t v_isSharedCheck_3519_; 
lean_del_object(v___x_3469_);
lean_dec(v_val_3467_);
lean_del_object(v___x_3455_);
lean_dec(v_snd_3453_);
lean_dec(v_mvarId_3441_);
lean_dec_ref(v_p_3440_);
v_a_3512_ = lean_ctor_get(v___x_3473_, 0);
v_isSharedCheck_3519_ = !lean_is_exclusive(v___x_3473_);
if (v_isSharedCheck_3519_ == 0)
{
v___x_3514_ = v___x_3473_;
v_isShared_3515_ = v_isSharedCheck_3519_;
goto v_resetjp_3513_;
}
else
{
lean_inc(v_a_3512_);
lean_dec(v___x_3473_);
v___x_3514_ = lean_box(0);
v_isShared_3515_ = v_isSharedCheck_3519_;
goto v_resetjp_3513_;
}
v_resetjp_3513_:
{
lean_object* v___x_3517_; 
if (v_isShared_3515_ == 0)
{
v___x_3517_ = v___x_3514_;
goto v_reusejp_3516_;
}
else
{
lean_object* v_reuseFailAlloc_3518_; 
v_reuseFailAlloc_3518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3518_, 0, v_a_3512_);
v___x_3517_ = v_reuseFailAlloc_3518_;
goto v_reusejp_3516_;
}
v_reusejp_3516_:
{
return v___x_3517_;
}
}
}
}
}
v___jp_3458_:
{
lean_object* v___x_3461_; 
if (v_isShared_3456_ == 0)
{
lean_ctor_set(v___x_3455_, 1, v_a_3459_);
lean_ctor_set(v___x_3455_, 0, v___x_3457_);
v___x_3461_ = v___x_3455_;
goto v_reusejp_3460_;
}
else
{
lean_object* v_reuseFailAlloc_3465_; 
v_reuseFailAlloc_3465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3465_, 0, v___x_3457_);
lean_ctor_set(v_reuseFailAlloc_3465_, 1, v_a_3459_);
v___x_3461_ = v_reuseFailAlloc_3465_;
goto v_reusejp_3460_;
}
v_reusejp_3460_:
{
size_t v___x_3462_; size_t v___x_3463_; 
v___x_3462_ = ((size_t)1ULL);
v___x_3463_ = lean_usize_add(v_i_3444_, v___x_3462_);
v_i_3444_ = v___x_3463_;
v_b_3445_ = v___x_3461_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5___boxed(lean_object* v_p_3523_, lean_object* v_mvarId_3524_, lean_object* v_as_3525_, lean_object* v_sz_3526_, lean_object* v_i_3527_, lean_object* v_b_3528_, lean_object* v___y_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_){
_start:
{
size_t v_sz_boxed_3534_; size_t v_i_boxed_3535_; lean_object* v_res_3536_; 
v_sz_boxed_3534_ = lean_unbox_usize(v_sz_3526_);
lean_dec(v_sz_3526_);
v_i_boxed_3535_ = lean_unbox_usize(v_i_3527_);
lean_dec(v_i_3527_);
v_res_3536_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5(v_p_3523_, v_mvarId_3524_, v_as_3525_, v_sz_boxed_3534_, v_i_boxed_3535_, v_b_3528_, v___y_3529_, v___y_3530_, v___y_3531_, v___y_3532_);
lean_dec(v___y_3532_);
lean_dec_ref(v___y_3531_);
lean_dec(v___y_3530_);
lean_dec_ref(v___y_3529_);
lean_dec_ref(v_as_3525_);
return v_res_3536_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4(lean_object* v_p_3537_, lean_object* v_mvarId_3538_, lean_object* v_as_3539_, size_t v_sz_3540_, size_t v_i_3541_, lean_object* v_b_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_){
_start:
{
uint8_t v___x_3548_; 
v___x_3548_ = lean_usize_dec_lt(v_i_3541_, v_sz_3540_);
if (v___x_3548_ == 0)
{
lean_object* v___x_3549_; 
lean_dec(v_mvarId_3538_);
lean_dec_ref(v_p_3537_);
v___x_3549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3549_, 0, v_b_3542_);
return v___x_3549_;
}
else
{
lean_object* v_snd_3550_; lean_object* v___x_3552_; uint8_t v_isShared_3553_; uint8_t v_isSharedCheck_3618_; 
v_snd_3550_ = lean_ctor_get(v_b_3542_, 1);
v_isSharedCheck_3618_ = !lean_is_exclusive(v_b_3542_);
if (v_isSharedCheck_3618_ == 0)
{
lean_object* v_unused_3619_; 
v_unused_3619_ = lean_ctor_get(v_b_3542_, 0);
lean_dec(v_unused_3619_);
v___x_3552_ = v_b_3542_;
v_isShared_3553_ = v_isSharedCheck_3618_;
goto v_resetjp_3551_;
}
else
{
lean_inc(v_snd_3550_);
lean_dec(v_b_3542_);
v___x_3552_ = lean_box(0);
v_isShared_3553_ = v_isSharedCheck_3618_;
goto v_resetjp_3551_;
}
v_resetjp_3551_:
{
lean_object* v___x_3554_; lean_object* v_a_3556_; lean_object* v_a_3563_; 
v___x_3554_ = lean_box(0);
v_a_3563_ = lean_array_uget(v_as_3539_, v_i_3541_);
if (lean_obj_tag(v_a_3563_) == 0)
{
v_a_3556_ = v_snd_3550_;
goto v___jp_3555_;
}
else
{
lean_object* v_val_3564_; lean_object* v___x_3566_; uint8_t v_isShared_3567_; uint8_t v_isSharedCheck_3617_; 
v_val_3564_ = lean_ctor_get(v_a_3563_, 0);
v_isSharedCheck_3617_ = !lean_is_exclusive(v_a_3563_);
if (v_isSharedCheck_3617_ == 0)
{
v___x_3566_ = v_a_3563_;
v_isShared_3567_ = v_isSharedCheck_3617_;
goto v_resetjp_3565_;
}
else
{
lean_inc(v_val_3564_);
lean_dec(v_a_3563_);
v___x_3566_ = lean_box(0);
v_isShared_3567_ = v_isSharedCheck_3617_;
goto v_resetjp_3565_;
}
v_resetjp_3565_:
{
lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; 
v___x_3568_ = lean_box(0);
v___x_3569_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5___closed__0));
lean_inc_ref(v_p_3537_);
lean_inc(v___y_3546_);
lean_inc_ref(v___y_3545_);
lean_inc(v___y_3544_);
lean_inc_ref(v___y_3543_);
lean_inc(v_val_3564_);
v___x_3570_ = lean_apply_6(v_p_3537_, v_val_3564_, v___y_3543_, v___y_3544_, v___y_3545_, v___y_3546_, lean_box(0));
if (lean_obj_tag(v___x_3570_) == 0)
{
lean_object* v_a_3571_; uint8_t v___x_3572_; 
v_a_3571_ = lean_ctor_get(v___x_3570_, 0);
lean_inc(v_a_3571_);
lean_dec_ref_known(v___x_3570_, 1);
v___x_3572_ = lean_unbox(v_a_3571_);
lean_dec(v_a_3571_);
if (v___x_3572_ == 0)
{
lean_del_object(v___x_3566_);
lean_dec(v_val_3564_);
lean_dec(v_snd_3550_);
v_a_3556_ = v___x_3569_;
goto v___jp_3555_;
}
else
{
lean_object* v___x_3573_; lean_object* v___x_3574_; uint8_t v___x_3575_; lean_object* v___x_3576_; lean_object* v___f_3577_; lean_object* v___x_3578_; 
v___x_3573_ = l_Lean_LocalDecl_fvarId(v_val_3564_);
lean_dec(v_val_3564_);
v___x_3574_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5___closed__1));
v___x_3575_ = 0;
v___x_3576_ = lean_box(v___x_3575_);
lean_inc(v_mvarId_3538_);
v___f_3577_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3___lam__0___boxed), 10, 5);
lean_closure_set(v___f_3577_, 0, v_mvarId_3538_);
lean_closure_set(v___f_3577_, 1, v___x_3573_);
lean_closure_set(v___f_3577_, 2, v___x_3574_);
lean_closure_set(v___f_3577_, 3, v___x_3576_);
lean_closure_set(v___f_3577_, 4, v___x_3554_);
v___x_3578_ = l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1___redArg(v___f_3577_, v___y_3543_, v___y_3544_, v___y_3545_, v___y_3546_);
if (lean_obj_tag(v___x_3578_) == 0)
{
lean_object* v_a_3579_; lean_object* v___x_3581_; uint8_t v_isShared_3582_; uint8_t v_isSharedCheck_3600_; 
v_a_3579_ = lean_ctor_get(v___x_3578_, 0);
v_isSharedCheck_3600_ = !lean_is_exclusive(v___x_3578_);
if (v_isSharedCheck_3600_ == 0)
{
v___x_3581_ = v___x_3578_;
v_isShared_3582_ = v_isSharedCheck_3600_;
goto v_resetjp_3580_;
}
else
{
lean_inc(v_a_3579_);
lean_dec(v___x_3578_);
v___x_3581_ = lean_box(0);
v_isShared_3582_ = v_isSharedCheck_3600_;
goto v_resetjp_3580_;
}
v_resetjp_3580_:
{
if (lean_obj_tag(v_a_3579_) == 0)
{
lean_del_object(v___x_3581_);
lean_del_object(v___x_3566_);
lean_dec(v_snd_3550_);
v_a_3556_ = v___x_3569_;
goto v___jp_3555_;
}
else
{
lean_object* v___x_3584_; 
lean_del_object(v___x_3552_);
lean_dec(v_mvarId_3538_);
lean_dec_ref(v_p_3537_);
lean_inc_ref(v_a_3579_);
if (v_isShared_3567_ == 0)
{
lean_ctor_set(v___x_3566_, 0, v_a_3579_);
v___x_3584_ = v___x_3566_;
goto v_reusejp_3583_;
}
else
{
lean_object* v_reuseFailAlloc_3599_; 
v_reuseFailAlloc_3599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3599_, 0, v_a_3579_);
v___x_3584_ = v_reuseFailAlloc_3599_;
goto v_reusejp_3583_;
}
v_reusejp_3583_:
{
lean_object* v___x_3586_; uint8_t v_isShared_3587_; uint8_t v_isSharedCheck_3597_; 
v_isSharedCheck_3597_ = !lean_is_exclusive(v_a_3579_);
if (v_isSharedCheck_3597_ == 0)
{
lean_object* v_unused_3598_; 
v_unused_3598_ = lean_ctor_get(v_a_3579_, 0);
lean_dec(v_unused_3598_);
v___x_3586_ = v_a_3579_;
v_isShared_3587_ = v_isSharedCheck_3597_;
goto v_resetjp_3585_;
}
else
{
lean_dec(v_a_3579_);
v___x_3586_ = lean_box(0);
v_isShared_3587_ = v_isSharedCheck_3597_;
goto v_resetjp_3585_;
}
v_resetjp_3585_:
{
lean_object* v___x_3588_; lean_object* v___x_3590_; 
v___x_3588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3588_, 0, v___x_3584_);
lean_ctor_set(v___x_3588_, 1, v___x_3568_);
if (v_isShared_3587_ == 0)
{
lean_ctor_set_tag(v___x_3586_, 0);
lean_ctor_set(v___x_3586_, 0, v___x_3588_);
v___x_3590_ = v___x_3586_;
goto v_reusejp_3589_;
}
else
{
lean_object* v_reuseFailAlloc_3596_; 
v_reuseFailAlloc_3596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3596_, 0, v___x_3588_);
v___x_3590_ = v_reuseFailAlloc_3596_;
goto v_reusejp_3589_;
}
v_reusejp_3589_:
{
lean_object* v___x_3591_; lean_object* v___x_3592_; lean_object* v___x_3594_; 
v___x_3591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3591_, 0, v___x_3590_);
v___x_3592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3592_, 0, v___x_3591_);
lean_ctor_set(v___x_3592_, 1, v_snd_3550_);
if (v_isShared_3582_ == 0)
{
lean_ctor_set(v___x_3581_, 0, v___x_3592_);
v___x_3594_ = v___x_3581_;
goto v_reusejp_3593_;
}
else
{
lean_object* v_reuseFailAlloc_3595_; 
v_reuseFailAlloc_3595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3595_, 0, v___x_3592_);
v___x_3594_ = v_reuseFailAlloc_3595_;
goto v_reusejp_3593_;
}
v_reusejp_3593_:
{
return v___x_3594_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3601_; lean_object* v___x_3603_; uint8_t v_isShared_3604_; uint8_t v_isSharedCheck_3608_; 
lean_del_object(v___x_3566_);
lean_del_object(v___x_3552_);
lean_dec(v_snd_3550_);
lean_dec(v_mvarId_3538_);
lean_dec_ref(v_p_3537_);
v_a_3601_ = lean_ctor_get(v___x_3578_, 0);
v_isSharedCheck_3608_ = !lean_is_exclusive(v___x_3578_);
if (v_isSharedCheck_3608_ == 0)
{
v___x_3603_ = v___x_3578_;
v_isShared_3604_ = v_isSharedCheck_3608_;
goto v_resetjp_3602_;
}
else
{
lean_inc(v_a_3601_);
lean_dec(v___x_3578_);
v___x_3603_ = lean_box(0);
v_isShared_3604_ = v_isSharedCheck_3608_;
goto v_resetjp_3602_;
}
v_resetjp_3602_:
{
lean_object* v___x_3606_; 
if (v_isShared_3604_ == 0)
{
v___x_3606_ = v___x_3603_;
goto v_reusejp_3605_;
}
else
{
lean_object* v_reuseFailAlloc_3607_; 
v_reuseFailAlloc_3607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3607_, 0, v_a_3601_);
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
else
{
lean_object* v_a_3609_; lean_object* v___x_3611_; uint8_t v_isShared_3612_; uint8_t v_isSharedCheck_3616_; 
lean_del_object(v___x_3566_);
lean_dec(v_val_3564_);
lean_del_object(v___x_3552_);
lean_dec(v_snd_3550_);
lean_dec(v_mvarId_3538_);
lean_dec_ref(v_p_3537_);
v_a_3609_ = lean_ctor_get(v___x_3570_, 0);
v_isSharedCheck_3616_ = !lean_is_exclusive(v___x_3570_);
if (v_isSharedCheck_3616_ == 0)
{
v___x_3611_ = v___x_3570_;
v_isShared_3612_ = v_isSharedCheck_3616_;
goto v_resetjp_3610_;
}
else
{
lean_inc(v_a_3609_);
lean_dec(v___x_3570_);
v___x_3611_ = lean_box(0);
v_isShared_3612_ = v_isSharedCheck_3616_;
goto v_resetjp_3610_;
}
v_resetjp_3610_:
{
lean_object* v___x_3614_; 
if (v_isShared_3612_ == 0)
{
v___x_3614_ = v___x_3611_;
goto v_reusejp_3613_;
}
else
{
lean_object* v_reuseFailAlloc_3615_; 
v_reuseFailAlloc_3615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3615_, 0, v_a_3609_);
v___x_3614_ = v_reuseFailAlloc_3615_;
goto v_reusejp_3613_;
}
v_reusejp_3613_:
{
return v___x_3614_;
}
}
}
}
}
v___jp_3555_:
{
lean_object* v___x_3558_; 
if (v_isShared_3553_ == 0)
{
lean_ctor_set(v___x_3552_, 1, v_a_3556_);
lean_ctor_set(v___x_3552_, 0, v___x_3554_);
v___x_3558_ = v___x_3552_;
goto v_reusejp_3557_;
}
else
{
lean_object* v_reuseFailAlloc_3562_; 
v_reuseFailAlloc_3562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3562_, 0, v___x_3554_);
lean_ctor_set(v_reuseFailAlloc_3562_, 1, v_a_3556_);
v___x_3558_ = v_reuseFailAlloc_3562_;
goto v_reusejp_3557_;
}
v_reusejp_3557_:
{
size_t v___x_3559_; size_t v___x_3560_; lean_object* v___x_3561_; 
v___x_3559_ = ((size_t)1ULL);
v___x_3560_ = lean_usize_add(v_i_3541_, v___x_3559_);
v___x_3561_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5(v_p_3537_, v_mvarId_3538_, v_as_3539_, v_sz_3540_, v___x_3560_, v___x_3558_, v___y_3543_, v___y_3544_, v___y_3545_, v___y_3546_);
return v___x_3561_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4___boxed(lean_object* v_p_3620_, lean_object* v_mvarId_3621_, lean_object* v_as_3622_, lean_object* v_sz_3623_, lean_object* v_i_3624_, lean_object* v_b_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_){
_start:
{
size_t v_sz_boxed_3631_; size_t v_i_boxed_3632_; lean_object* v_res_3633_; 
v_sz_boxed_3631_ = lean_unbox_usize(v_sz_3623_);
lean_dec(v_sz_3623_);
v_i_boxed_3632_ = lean_unbox_usize(v_i_3624_);
lean_dec(v_i_3624_);
v_res_3633_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4(v_p_3620_, v_mvarId_3621_, v_as_3622_, v_sz_boxed_3631_, v_i_boxed_3632_, v_b_3625_, v___y_3626_, v___y_3627_, v___y_3628_, v___y_3629_);
lean_dec(v___y_3629_);
lean_dec_ref(v___y_3628_);
lean_dec(v___y_3627_);
lean_dec_ref(v___y_3626_);
lean_dec_ref(v_as_3622_);
return v_res_3633_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2(lean_object* v_init_3634_, lean_object* v_p_3635_, lean_object* v_mvarId_3636_, lean_object* v_n_3637_, lean_object* v_b_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_, lean_object* v___y_3641_, lean_object* v___y_3642_){
_start:
{
if (lean_obj_tag(v_n_3637_) == 0)
{
lean_object* v_cs_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; size_t v_sz_3647_; size_t v___x_3648_; lean_object* v___x_3649_; 
v_cs_3644_ = lean_ctor_get(v_n_3637_, 0);
v___x_3645_ = lean_box(0);
v___x_3646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3646_, 0, v___x_3645_);
lean_ctor_set(v___x_3646_, 1, v_b_3638_);
v_sz_3647_ = lean_array_size(v_cs_3644_);
v___x_3648_ = ((size_t)0ULL);
v___x_3649_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__3(v_init_3634_, v_p_3635_, v_mvarId_3636_, v_cs_3644_, v_sz_3647_, v___x_3648_, v___x_3646_, v___y_3639_, v___y_3640_, v___y_3641_, v___y_3642_);
if (lean_obj_tag(v___x_3649_) == 0)
{
lean_object* v_a_3650_; lean_object* v___x_3652_; uint8_t v_isShared_3653_; uint8_t v_isSharedCheck_3664_; 
v_a_3650_ = lean_ctor_get(v___x_3649_, 0);
v_isSharedCheck_3664_ = !lean_is_exclusive(v___x_3649_);
if (v_isSharedCheck_3664_ == 0)
{
v___x_3652_ = v___x_3649_;
v_isShared_3653_ = v_isSharedCheck_3664_;
goto v_resetjp_3651_;
}
else
{
lean_inc(v_a_3650_);
lean_dec(v___x_3649_);
v___x_3652_ = lean_box(0);
v_isShared_3653_ = v_isSharedCheck_3664_;
goto v_resetjp_3651_;
}
v_resetjp_3651_:
{
lean_object* v_fst_3654_; 
v_fst_3654_ = lean_ctor_get(v_a_3650_, 0);
if (lean_obj_tag(v_fst_3654_) == 0)
{
lean_object* v_snd_3655_; lean_object* v___x_3656_; lean_object* v___x_3658_; 
v_snd_3655_ = lean_ctor_get(v_a_3650_, 1);
lean_inc(v_snd_3655_);
lean_dec(v_a_3650_);
v___x_3656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3656_, 0, v_snd_3655_);
if (v_isShared_3653_ == 0)
{
lean_ctor_set(v___x_3652_, 0, v___x_3656_);
v___x_3658_ = v___x_3652_;
goto v_reusejp_3657_;
}
else
{
lean_object* v_reuseFailAlloc_3659_; 
v_reuseFailAlloc_3659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3659_, 0, v___x_3656_);
v___x_3658_ = v_reuseFailAlloc_3659_;
goto v_reusejp_3657_;
}
v_reusejp_3657_:
{
return v___x_3658_;
}
}
else
{
lean_object* v_val_3660_; lean_object* v___x_3662_; 
lean_inc_ref(v_fst_3654_);
lean_dec(v_a_3650_);
v_val_3660_ = lean_ctor_get(v_fst_3654_, 0);
lean_inc(v_val_3660_);
lean_dec_ref_known(v_fst_3654_, 1);
if (v_isShared_3653_ == 0)
{
lean_ctor_set(v___x_3652_, 0, v_val_3660_);
v___x_3662_ = v___x_3652_;
goto v_reusejp_3661_;
}
else
{
lean_object* v_reuseFailAlloc_3663_; 
v_reuseFailAlloc_3663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3663_, 0, v_val_3660_);
v___x_3662_ = v_reuseFailAlloc_3663_;
goto v_reusejp_3661_;
}
v_reusejp_3661_:
{
return v___x_3662_;
}
}
}
}
else
{
lean_object* v_a_3665_; lean_object* v___x_3667_; uint8_t v_isShared_3668_; uint8_t v_isSharedCheck_3672_; 
v_a_3665_ = lean_ctor_get(v___x_3649_, 0);
v_isSharedCheck_3672_ = !lean_is_exclusive(v___x_3649_);
if (v_isSharedCheck_3672_ == 0)
{
v___x_3667_ = v___x_3649_;
v_isShared_3668_ = v_isSharedCheck_3672_;
goto v_resetjp_3666_;
}
else
{
lean_inc(v_a_3665_);
lean_dec(v___x_3649_);
v___x_3667_ = lean_box(0);
v_isShared_3668_ = v_isSharedCheck_3672_;
goto v_resetjp_3666_;
}
v_resetjp_3666_:
{
lean_object* v___x_3670_; 
if (v_isShared_3668_ == 0)
{
v___x_3670_ = v___x_3667_;
goto v_reusejp_3669_;
}
else
{
lean_object* v_reuseFailAlloc_3671_; 
v_reuseFailAlloc_3671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3671_, 0, v_a_3665_);
v___x_3670_ = v_reuseFailAlloc_3671_;
goto v_reusejp_3669_;
}
v_reusejp_3669_:
{
return v___x_3670_;
}
}
}
}
else
{
lean_object* v_vs_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; size_t v_sz_3676_; size_t v___x_3677_; lean_object* v___x_3678_; 
v_vs_3673_ = lean_ctor_get(v_n_3637_, 0);
v___x_3674_ = lean_box(0);
v___x_3675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3675_, 0, v___x_3674_);
lean_ctor_set(v___x_3675_, 1, v_b_3638_);
v_sz_3676_ = lean_array_size(v_vs_3673_);
v___x_3677_ = ((size_t)0ULL);
v___x_3678_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4(v_p_3635_, v_mvarId_3636_, v_vs_3673_, v_sz_3676_, v___x_3677_, v___x_3675_, v___y_3639_, v___y_3640_, v___y_3641_, v___y_3642_);
if (lean_obj_tag(v___x_3678_) == 0)
{
lean_object* v_a_3679_; lean_object* v___x_3681_; uint8_t v_isShared_3682_; uint8_t v_isSharedCheck_3693_; 
v_a_3679_ = lean_ctor_get(v___x_3678_, 0);
v_isSharedCheck_3693_ = !lean_is_exclusive(v___x_3678_);
if (v_isSharedCheck_3693_ == 0)
{
v___x_3681_ = v___x_3678_;
v_isShared_3682_ = v_isSharedCheck_3693_;
goto v_resetjp_3680_;
}
else
{
lean_inc(v_a_3679_);
lean_dec(v___x_3678_);
v___x_3681_ = lean_box(0);
v_isShared_3682_ = v_isSharedCheck_3693_;
goto v_resetjp_3680_;
}
v_resetjp_3680_:
{
lean_object* v_fst_3683_; 
v_fst_3683_ = lean_ctor_get(v_a_3679_, 0);
if (lean_obj_tag(v_fst_3683_) == 0)
{
lean_object* v_snd_3684_; lean_object* v___x_3685_; lean_object* v___x_3687_; 
v_snd_3684_ = lean_ctor_get(v_a_3679_, 1);
lean_inc(v_snd_3684_);
lean_dec(v_a_3679_);
v___x_3685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3685_, 0, v_snd_3684_);
if (v_isShared_3682_ == 0)
{
lean_ctor_set(v___x_3681_, 0, v___x_3685_);
v___x_3687_ = v___x_3681_;
goto v_reusejp_3686_;
}
else
{
lean_object* v_reuseFailAlloc_3688_; 
v_reuseFailAlloc_3688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3688_, 0, v___x_3685_);
v___x_3687_ = v_reuseFailAlloc_3688_;
goto v_reusejp_3686_;
}
v_reusejp_3686_:
{
return v___x_3687_;
}
}
else
{
lean_object* v_val_3689_; lean_object* v___x_3691_; 
lean_inc_ref(v_fst_3683_);
lean_dec(v_a_3679_);
v_val_3689_ = lean_ctor_get(v_fst_3683_, 0);
lean_inc(v_val_3689_);
lean_dec_ref_known(v_fst_3683_, 1);
if (v_isShared_3682_ == 0)
{
lean_ctor_set(v___x_3681_, 0, v_val_3689_);
v___x_3691_ = v___x_3681_;
goto v_reusejp_3690_;
}
else
{
lean_object* v_reuseFailAlloc_3692_; 
v_reuseFailAlloc_3692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3692_, 0, v_val_3689_);
v___x_3691_ = v_reuseFailAlloc_3692_;
goto v_reusejp_3690_;
}
v_reusejp_3690_:
{
return v___x_3691_;
}
}
}
}
else
{
lean_object* v_a_3694_; lean_object* v___x_3696_; uint8_t v_isShared_3697_; uint8_t v_isSharedCheck_3701_; 
v_a_3694_ = lean_ctor_get(v___x_3678_, 0);
v_isSharedCheck_3701_ = !lean_is_exclusive(v___x_3678_);
if (v_isSharedCheck_3701_ == 0)
{
v___x_3696_ = v___x_3678_;
v_isShared_3697_ = v_isSharedCheck_3701_;
goto v_resetjp_3695_;
}
else
{
lean_inc(v_a_3694_);
lean_dec(v___x_3678_);
v___x_3696_ = lean_box(0);
v_isShared_3697_ = v_isSharedCheck_3701_;
goto v_resetjp_3695_;
}
v_resetjp_3695_:
{
lean_object* v___x_3699_; 
if (v_isShared_3697_ == 0)
{
v___x_3699_ = v___x_3696_;
goto v_reusejp_3698_;
}
else
{
lean_object* v_reuseFailAlloc_3700_; 
v_reuseFailAlloc_3700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3700_, 0, v_a_3694_);
v___x_3699_ = v_reuseFailAlloc_3700_;
goto v_reusejp_3698_;
}
v_reusejp_3698_:
{
return v___x_3699_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__3(lean_object* v_init_3702_, lean_object* v_p_3703_, lean_object* v_mvarId_3704_, lean_object* v_as_3705_, size_t v_sz_3706_, size_t v_i_3707_, lean_object* v_b_3708_, lean_object* v___y_3709_, lean_object* v___y_3710_, lean_object* v___y_3711_, lean_object* v___y_3712_){
_start:
{
uint8_t v___x_3714_; 
v___x_3714_ = lean_usize_dec_lt(v_i_3707_, v_sz_3706_);
if (v___x_3714_ == 0)
{
lean_object* v___x_3715_; 
lean_dec(v_mvarId_3704_);
lean_dec_ref(v_p_3703_);
v___x_3715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3715_, 0, v_b_3708_);
return v___x_3715_;
}
else
{
lean_object* v_snd_3716_; lean_object* v___x_3718_; uint8_t v_isShared_3719_; uint8_t v_isSharedCheck_3750_; 
v_snd_3716_ = lean_ctor_get(v_b_3708_, 1);
v_isSharedCheck_3750_ = !lean_is_exclusive(v_b_3708_);
if (v_isSharedCheck_3750_ == 0)
{
lean_object* v_unused_3751_; 
v_unused_3751_ = lean_ctor_get(v_b_3708_, 0);
lean_dec(v_unused_3751_);
v___x_3718_ = v_b_3708_;
v_isShared_3719_ = v_isSharedCheck_3750_;
goto v_resetjp_3717_;
}
else
{
lean_inc(v_snd_3716_);
lean_dec(v_b_3708_);
v___x_3718_ = lean_box(0);
v_isShared_3719_ = v_isSharedCheck_3750_;
goto v_resetjp_3717_;
}
v_resetjp_3717_:
{
lean_object* v___x_3720_; lean_object* v_a_3721_; lean_object* v___x_3722_; 
v___x_3720_ = lean_box(0);
v_a_3721_ = lean_array_uget_borrowed(v_as_3705_, v_i_3707_);
lean_inc(v_snd_3716_);
lean_inc(v_mvarId_3704_);
lean_inc_ref(v_p_3703_);
v___x_3722_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2(v_init_3702_, v_p_3703_, v_mvarId_3704_, v_a_3721_, v_snd_3716_, v___y_3709_, v___y_3710_, v___y_3711_, v___y_3712_);
if (lean_obj_tag(v___x_3722_) == 0)
{
lean_object* v_a_3723_; lean_object* v___x_3725_; uint8_t v_isShared_3726_; uint8_t v_isSharedCheck_3741_; 
v_a_3723_ = lean_ctor_get(v___x_3722_, 0);
v_isSharedCheck_3741_ = !lean_is_exclusive(v___x_3722_);
if (v_isSharedCheck_3741_ == 0)
{
v___x_3725_ = v___x_3722_;
v_isShared_3726_ = v_isSharedCheck_3741_;
goto v_resetjp_3724_;
}
else
{
lean_inc(v_a_3723_);
lean_dec(v___x_3722_);
v___x_3725_ = lean_box(0);
v_isShared_3726_ = v_isSharedCheck_3741_;
goto v_resetjp_3724_;
}
v_resetjp_3724_:
{
if (lean_obj_tag(v_a_3723_) == 0)
{
lean_object* v___x_3727_; lean_object* v___x_3729_; 
lean_dec(v_mvarId_3704_);
lean_dec_ref(v_p_3703_);
v___x_3727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3727_, 0, v_a_3723_);
if (v_isShared_3719_ == 0)
{
lean_ctor_set(v___x_3718_, 0, v___x_3727_);
v___x_3729_ = v___x_3718_;
goto v_reusejp_3728_;
}
else
{
lean_object* v_reuseFailAlloc_3733_; 
v_reuseFailAlloc_3733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3733_, 0, v___x_3727_);
lean_ctor_set(v_reuseFailAlloc_3733_, 1, v_snd_3716_);
v___x_3729_ = v_reuseFailAlloc_3733_;
goto v_reusejp_3728_;
}
v_reusejp_3728_:
{
lean_object* v___x_3731_; 
if (v_isShared_3726_ == 0)
{
lean_ctor_set(v___x_3725_, 0, v___x_3729_);
v___x_3731_ = v___x_3725_;
goto v_reusejp_3730_;
}
else
{
lean_object* v_reuseFailAlloc_3732_; 
v_reuseFailAlloc_3732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3732_, 0, v___x_3729_);
v___x_3731_ = v_reuseFailAlloc_3732_;
goto v_reusejp_3730_;
}
v_reusejp_3730_:
{
return v___x_3731_;
}
}
}
else
{
lean_object* v_a_3734_; lean_object* v___x_3736_; 
lean_del_object(v___x_3725_);
lean_dec(v_snd_3716_);
v_a_3734_ = lean_ctor_get(v_a_3723_, 0);
lean_inc(v_a_3734_);
lean_dec_ref_known(v_a_3723_, 1);
if (v_isShared_3719_ == 0)
{
lean_ctor_set(v___x_3718_, 1, v_a_3734_);
lean_ctor_set(v___x_3718_, 0, v___x_3720_);
v___x_3736_ = v___x_3718_;
goto v_reusejp_3735_;
}
else
{
lean_object* v_reuseFailAlloc_3740_; 
v_reuseFailAlloc_3740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3740_, 0, v___x_3720_);
lean_ctor_set(v_reuseFailAlloc_3740_, 1, v_a_3734_);
v___x_3736_ = v_reuseFailAlloc_3740_;
goto v_reusejp_3735_;
}
v_reusejp_3735_:
{
size_t v___x_3737_; size_t v___x_3738_; 
v___x_3737_ = ((size_t)1ULL);
v___x_3738_ = lean_usize_add(v_i_3707_, v___x_3737_);
v_i_3707_ = v___x_3738_;
v_b_3708_ = v___x_3736_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3742_; lean_object* v___x_3744_; uint8_t v_isShared_3745_; uint8_t v_isSharedCheck_3749_; 
lean_del_object(v___x_3718_);
lean_dec(v_snd_3716_);
lean_dec(v_mvarId_3704_);
lean_dec_ref(v_p_3703_);
v_a_3742_ = lean_ctor_get(v___x_3722_, 0);
v_isSharedCheck_3749_ = !lean_is_exclusive(v___x_3722_);
if (v_isSharedCheck_3749_ == 0)
{
v___x_3744_ = v___x_3722_;
v_isShared_3745_ = v_isSharedCheck_3749_;
goto v_resetjp_3743_;
}
else
{
lean_inc(v_a_3742_);
lean_dec(v___x_3722_);
v___x_3744_ = lean_box(0);
v_isShared_3745_ = v_isSharedCheck_3749_;
goto v_resetjp_3743_;
}
v_resetjp_3743_:
{
lean_object* v___x_3747_; 
if (v_isShared_3745_ == 0)
{
v___x_3747_ = v___x_3744_;
goto v_reusejp_3746_;
}
else
{
lean_object* v_reuseFailAlloc_3748_; 
v_reuseFailAlloc_3748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3748_, 0, v_a_3742_);
v___x_3747_ = v_reuseFailAlloc_3748_;
goto v_reusejp_3746_;
}
v_reusejp_3746_:
{
return v___x_3747_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__3___boxed(lean_object* v_init_3752_, lean_object* v_p_3753_, lean_object* v_mvarId_3754_, lean_object* v_as_3755_, lean_object* v_sz_3756_, lean_object* v_i_3757_, lean_object* v_b_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_, lean_object* v___y_3763_){
_start:
{
size_t v_sz_boxed_3764_; size_t v_i_boxed_3765_; lean_object* v_res_3766_; 
v_sz_boxed_3764_ = lean_unbox_usize(v_sz_3756_);
lean_dec(v_sz_3756_);
v_i_boxed_3765_ = lean_unbox_usize(v_i_3757_);
lean_dec(v_i_3757_);
v_res_3766_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__3(v_init_3752_, v_p_3753_, v_mvarId_3754_, v_as_3755_, v_sz_boxed_3764_, v_i_boxed_3765_, v_b_3758_, v___y_3759_, v___y_3760_, v___y_3761_, v___y_3762_);
lean_dec(v___y_3762_);
lean_dec_ref(v___y_3761_);
lean_dec(v___y_3760_);
lean_dec_ref(v___y_3759_);
lean_dec_ref(v_as_3755_);
lean_dec_ref(v_init_3752_);
return v_res_3766_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2___boxed(lean_object* v_init_3767_, lean_object* v_p_3768_, lean_object* v_mvarId_3769_, lean_object* v_n_3770_, lean_object* v_b_3771_, lean_object* v___y_3772_, lean_object* v___y_3773_, lean_object* v___y_3774_, lean_object* v___y_3775_, lean_object* v___y_3776_){
_start:
{
lean_object* v_res_3777_; 
v_res_3777_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2(v_init_3767_, v_p_3768_, v_mvarId_3769_, v_n_3770_, v_b_3771_, v___y_3772_, v___y_3773_, v___y_3774_, v___y_3775_);
lean_dec(v___y_3775_);
lean_dec_ref(v___y_3774_);
lean_dec(v___y_3773_);
lean_dec_ref(v___y_3772_);
lean_dec_ref(v_n_3770_);
lean_dec_ref(v_init_3767_);
return v_res_3777_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3_spec__6(lean_object* v_p_3781_, lean_object* v_mvarId_3782_, lean_object* v_as_3783_, size_t v_sz_3784_, size_t v_i_3785_, lean_object* v_b_3786_, lean_object* v___y_3787_, lean_object* v___y_3788_, lean_object* v___y_3789_, lean_object* v___y_3790_){
_start:
{
uint8_t v___x_3792_; 
v___x_3792_ = lean_usize_dec_lt(v_i_3785_, v_sz_3784_);
if (v___x_3792_ == 0)
{
lean_object* v___x_3793_; 
lean_dec(v_mvarId_3782_);
lean_dec_ref(v_p_3781_);
v___x_3793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3793_, 0, v_b_3786_);
return v___x_3793_;
}
else
{
lean_object* v_snd_3794_; lean_object* v___x_3796_; uint8_t v_isShared_3797_; uint8_t v_isSharedCheck_3861_; 
v_snd_3794_ = lean_ctor_get(v_b_3786_, 1);
v_isSharedCheck_3861_ = !lean_is_exclusive(v_b_3786_);
if (v_isSharedCheck_3861_ == 0)
{
lean_object* v_unused_3862_; 
v_unused_3862_ = lean_ctor_get(v_b_3786_, 0);
lean_dec(v_unused_3862_);
v___x_3796_ = v_b_3786_;
v_isShared_3797_ = v_isSharedCheck_3861_;
goto v_resetjp_3795_;
}
else
{
lean_inc(v_snd_3794_);
lean_dec(v_b_3786_);
v___x_3796_ = lean_box(0);
v_isShared_3797_ = v_isSharedCheck_3861_;
goto v_resetjp_3795_;
}
v_resetjp_3795_:
{
lean_object* v___x_3798_; lean_object* v_a_3800_; lean_object* v_a_3807_; 
v___x_3798_ = lean_box(0);
v_a_3807_ = lean_array_uget(v_as_3783_, v_i_3785_);
if (lean_obj_tag(v_a_3807_) == 0)
{
v_a_3800_ = v_snd_3794_;
goto v___jp_3799_;
}
else
{
lean_object* v_val_3808_; lean_object* v___x_3810_; uint8_t v_isShared_3811_; uint8_t v_isSharedCheck_3860_; 
v_val_3808_ = lean_ctor_get(v_a_3807_, 0);
v_isSharedCheck_3860_ = !lean_is_exclusive(v_a_3807_);
if (v_isSharedCheck_3860_ == 0)
{
v___x_3810_ = v_a_3807_;
v_isShared_3811_ = v_isSharedCheck_3860_;
goto v_resetjp_3809_;
}
else
{
lean_inc(v_val_3808_);
lean_dec(v_a_3807_);
v___x_3810_ = lean_box(0);
v_isShared_3811_ = v_isSharedCheck_3860_;
goto v_resetjp_3809_;
}
v_resetjp_3809_:
{
lean_object* v___x_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; 
v___x_3812_ = lean_box(0);
v___x_3813_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3_spec__6___closed__0));
lean_inc_ref(v_p_3781_);
lean_inc(v___y_3790_);
lean_inc_ref(v___y_3789_);
lean_inc(v___y_3788_);
lean_inc_ref(v___y_3787_);
lean_inc(v_val_3808_);
v___x_3814_ = lean_apply_6(v_p_3781_, v_val_3808_, v___y_3787_, v___y_3788_, v___y_3789_, v___y_3790_, lean_box(0));
if (lean_obj_tag(v___x_3814_) == 0)
{
lean_object* v_a_3815_; uint8_t v___x_3816_; 
v_a_3815_ = lean_ctor_get(v___x_3814_, 0);
lean_inc(v_a_3815_);
lean_dec_ref_known(v___x_3814_, 1);
v___x_3816_ = lean_unbox(v_a_3815_);
lean_dec(v_a_3815_);
if (v___x_3816_ == 0)
{
lean_del_object(v___x_3810_);
lean_dec(v_val_3808_);
lean_dec(v_snd_3794_);
v_a_3800_ = v___x_3813_;
goto v___jp_3799_;
}
else
{
lean_object* v___x_3817_; lean_object* v___x_3818_; uint8_t v___x_3819_; lean_object* v___x_3820_; lean_object* v___f_3821_; lean_object* v___x_3822_; 
v___x_3817_ = l_Lean_LocalDecl_fvarId(v_val_3808_);
lean_dec(v_val_3808_);
v___x_3818_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5___closed__1));
v___x_3819_ = 0;
v___x_3820_ = lean_box(v___x_3819_);
lean_inc(v_mvarId_3782_);
v___f_3821_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3___lam__0___boxed), 10, 5);
lean_closure_set(v___f_3821_, 0, v_mvarId_3782_);
lean_closure_set(v___f_3821_, 1, v___x_3817_);
lean_closure_set(v___f_3821_, 2, v___x_3818_);
lean_closure_set(v___f_3821_, 3, v___x_3820_);
lean_closure_set(v___f_3821_, 4, v___x_3798_);
v___x_3822_ = l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1___redArg(v___f_3821_, v___y_3787_, v___y_3788_, v___y_3789_, v___y_3790_);
if (lean_obj_tag(v___x_3822_) == 0)
{
lean_object* v_a_3823_; lean_object* v___x_3825_; uint8_t v_isShared_3826_; uint8_t v_isSharedCheck_3843_; 
v_a_3823_ = lean_ctor_get(v___x_3822_, 0);
v_isSharedCheck_3843_ = !lean_is_exclusive(v___x_3822_);
if (v_isSharedCheck_3843_ == 0)
{
v___x_3825_ = v___x_3822_;
v_isShared_3826_ = v_isSharedCheck_3843_;
goto v_resetjp_3824_;
}
else
{
lean_inc(v_a_3823_);
lean_dec(v___x_3822_);
v___x_3825_ = lean_box(0);
v_isShared_3826_ = v_isSharedCheck_3843_;
goto v_resetjp_3824_;
}
v_resetjp_3824_:
{
if (lean_obj_tag(v_a_3823_) == 0)
{
lean_del_object(v___x_3825_);
lean_del_object(v___x_3810_);
lean_dec(v_snd_3794_);
v_a_3800_ = v___x_3813_;
goto v___jp_3799_;
}
else
{
lean_object* v___x_3828_; 
lean_del_object(v___x_3796_);
lean_dec(v_mvarId_3782_);
lean_dec_ref(v_p_3781_);
lean_inc_ref(v_a_3823_);
if (v_isShared_3811_ == 0)
{
lean_ctor_set(v___x_3810_, 0, v_a_3823_);
v___x_3828_ = v___x_3810_;
goto v_reusejp_3827_;
}
else
{
lean_object* v_reuseFailAlloc_3842_; 
v_reuseFailAlloc_3842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3842_, 0, v_a_3823_);
v___x_3828_ = v_reuseFailAlloc_3842_;
goto v_reusejp_3827_;
}
v_reusejp_3827_:
{
lean_object* v___x_3830_; uint8_t v_isShared_3831_; uint8_t v_isSharedCheck_3840_; 
v_isSharedCheck_3840_ = !lean_is_exclusive(v_a_3823_);
if (v_isSharedCheck_3840_ == 0)
{
lean_object* v_unused_3841_; 
v_unused_3841_ = lean_ctor_get(v_a_3823_, 0);
lean_dec(v_unused_3841_);
v___x_3830_ = v_a_3823_;
v_isShared_3831_ = v_isSharedCheck_3840_;
goto v_resetjp_3829_;
}
else
{
lean_dec(v_a_3823_);
v___x_3830_ = lean_box(0);
v_isShared_3831_ = v_isSharedCheck_3840_;
goto v_resetjp_3829_;
}
v_resetjp_3829_:
{
lean_object* v___x_3832_; lean_object* v___x_3834_; 
v___x_3832_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3832_, 0, v___x_3828_);
lean_ctor_set(v___x_3832_, 1, v___x_3812_);
if (v_isShared_3831_ == 0)
{
lean_ctor_set(v___x_3830_, 0, v___x_3832_);
v___x_3834_ = v___x_3830_;
goto v_reusejp_3833_;
}
else
{
lean_object* v_reuseFailAlloc_3839_; 
v_reuseFailAlloc_3839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3839_, 0, v___x_3832_);
v___x_3834_ = v_reuseFailAlloc_3839_;
goto v_reusejp_3833_;
}
v_reusejp_3833_:
{
lean_object* v___x_3835_; lean_object* v___x_3837_; 
v___x_3835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3835_, 0, v___x_3834_);
lean_ctor_set(v___x_3835_, 1, v_snd_3794_);
if (v_isShared_3826_ == 0)
{
lean_ctor_set(v___x_3825_, 0, v___x_3835_);
v___x_3837_ = v___x_3825_;
goto v_reusejp_3836_;
}
else
{
lean_object* v_reuseFailAlloc_3838_; 
v_reuseFailAlloc_3838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3838_, 0, v___x_3835_);
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
else
{
lean_object* v_a_3844_; lean_object* v___x_3846_; uint8_t v_isShared_3847_; uint8_t v_isSharedCheck_3851_; 
lean_del_object(v___x_3810_);
lean_del_object(v___x_3796_);
lean_dec(v_snd_3794_);
lean_dec(v_mvarId_3782_);
lean_dec_ref(v_p_3781_);
v_a_3844_ = lean_ctor_get(v___x_3822_, 0);
v_isSharedCheck_3851_ = !lean_is_exclusive(v___x_3822_);
if (v_isSharedCheck_3851_ == 0)
{
v___x_3846_ = v___x_3822_;
v_isShared_3847_ = v_isSharedCheck_3851_;
goto v_resetjp_3845_;
}
else
{
lean_inc(v_a_3844_);
lean_dec(v___x_3822_);
v___x_3846_ = lean_box(0);
v_isShared_3847_ = v_isSharedCheck_3851_;
goto v_resetjp_3845_;
}
v_resetjp_3845_:
{
lean_object* v___x_3849_; 
if (v_isShared_3847_ == 0)
{
v___x_3849_ = v___x_3846_;
goto v_reusejp_3848_;
}
else
{
lean_object* v_reuseFailAlloc_3850_; 
v_reuseFailAlloc_3850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3850_, 0, v_a_3844_);
v___x_3849_ = v_reuseFailAlloc_3850_;
goto v_reusejp_3848_;
}
v_reusejp_3848_:
{
return v___x_3849_;
}
}
}
}
}
else
{
lean_object* v_a_3852_; lean_object* v___x_3854_; uint8_t v_isShared_3855_; uint8_t v_isSharedCheck_3859_; 
lean_del_object(v___x_3810_);
lean_dec(v_val_3808_);
lean_del_object(v___x_3796_);
lean_dec(v_snd_3794_);
lean_dec(v_mvarId_3782_);
lean_dec_ref(v_p_3781_);
v_a_3852_ = lean_ctor_get(v___x_3814_, 0);
v_isSharedCheck_3859_ = !lean_is_exclusive(v___x_3814_);
if (v_isSharedCheck_3859_ == 0)
{
v___x_3854_ = v___x_3814_;
v_isShared_3855_ = v_isSharedCheck_3859_;
goto v_resetjp_3853_;
}
else
{
lean_inc(v_a_3852_);
lean_dec(v___x_3814_);
v___x_3854_ = lean_box(0);
v_isShared_3855_ = v_isSharedCheck_3859_;
goto v_resetjp_3853_;
}
v_resetjp_3853_:
{
lean_object* v___x_3857_; 
if (v_isShared_3855_ == 0)
{
v___x_3857_ = v___x_3854_;
goto v_reusejp_3856_;
}
else
{
lean_object* v_reuseFailAlloc_3858_; 
v_reuseFailAlloc_3858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3858_, 0, v_a_3852_);
v___x_3857_ = v_reuseFailAlloc_3858_;
goto v_reusejp_3856_;
}
v_reusejp_3856_:
{
return v___x_3857_;
}
}
}
}
}
v___jp_3799_:
{
lean_object* v___x_3802_; 
if (v_isShared_3797_ == 0)
{
lean_ctor_set(v___x_3796_, 1, v_a_3800_);
lean_ctor_set(v___x_3796_, 0, v___x_3798_);
v___x_3802_ = v___x_3796_;
goto v_reusejp_3801_;
}
else
{
lean_object* v_reuseFailAlloc_3806_; 
v_reuseFailAlloc_3806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3806_, 0, v___x_3798_);
lean_ctor_set(v_reuseFailAlloc_3806_, 1, v_a_3800_);
v___x_3802_ = v_reuseFailAlloc_3806_;
goto v_reusejp_3801_;
}
v_reusejp_3801_:
{
size_t v___x_3803_; size_t v___x_3804_; 
v___x_3803_ = ((size_t)1ULL);
v___x_3804_ = lean_usize_add(v_i_3785_, v___x_3803_);
v_i_3785_ = v___x_3804_;
v_b_3786_ = v___x_3802_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3_spec__6___boxed(lean_object* v_p_3863_, lean_object* v_mvarId_3864_, lean_object* v_as_3865_, lean_object* v_sz_3866_, lean_object* v_i_3867_, lean_object* v_b_3868_, lean_object* v___y_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_){
_start:
{
size_t v_sz_boxed_3874_; size_t v_i_boxed_3875_; lean_object* v_res_3876_; 
v_sz_boxed_3874_ = lean_unbox_usize(v_sz_3866_);
lean_dec(v_sz_3866_);
v_i_boxed_3875_ = lean_unbox_usize(v_i_3867_);
lean_dec(v_i_3867_);
v_res_3876_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3_spec__6(v_p_3863_, v_mvarId_3864_, v_as_3865_, v_sz_boxed_3874_, v_i_boxed_3875_, v_b_3868_, v___y_3869_, v___y_3870_, v___y_3871_, v___y_3872_);
lean_dec(v___y_3872_);
lean_dec_ref(v___y_3871_);
lean_dec(v___y_3870_);
lean_dec_ref(v___y_3869_);
lean_dec_ref(v_as_3865_);
return v_res_3876_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3(lean_object* v_p_3877_, lean_object* v_mvarId_3878_, lean_object* v_as_3879_, size_t v_sz_3880_, size_t v_i_3881_, lean_object* v_b_3882_, lean_object* v___y_3883_, lean_object* v___y_3884_, lean_object* v___y_3885_, lean_object* v___y_3886_){
_start:
{
uint8_t v___x_3888_; 
v___x_3888_ = lean_usize_dec_lt(v_i_3881_, v_sz_3880_);
if (v___x_3888_ == 0)
{
lean_object* v___x_3889_; 
lean_dec(v_mvarId_3878_);
lean_dec_ref(v_p_3877_);
v___x_3889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3889_, 0, v_b_3882_);
return v___x_3889_;
}
else
{
lean_object* v_snd_3890_; lean_object* v___x_3892_; uint8_t v_isShared_3893_; uint8_t v_isSharedCheck_3957_; 
v_snd_3890_ = lean_ctor_get(v_b_3882_, 1);
v_isSharedCheck_3957_ = !lean_is_exclusive(v_b_3882_);
if (v_isSharedCheck_3957_ == 0)
{
lean_object* v_unused_3958_; 
v_unused_3958_ = lean_ctor_get(v_b_3882_, 0);
lean_dec(v_unused_3958_);
v___x_3892_ = v_b_3882_;
v_isShared_3893_ = v_isSharedCheck_3957_;
goto v_resetjp_3891_;
}
else
{
lean_inc(v_snd_3890_);
lean_dec(v_b_3882_);
v___x_3892_ = lean_box(0);
v_isShared_3893_ = v_isSharedCheck_3957_;
goto v_resetjp_3891_;
}
v_resetjp_3891_:
{
lean_object* v___x_3894_; lean_object* v_a_3896_; lean_object* v_a_3903_; 
v___x_3894_ = lean_box(0);
v_a_3903_ = lean_array_uget(v_as_3879_, v_i_3881_);
if (lean_obj_tag(v_a_3903_) == 0)
{
v_a_3896_ = v_snd_3890_;
goto v___jp_3895_;
}
else
{
lean_object* v_val_3904_; lean_object* v___x_3906_; uint8_t v_isShared_3907_; uint8_t v_isSharedCheck_3956_; 
v_val_3904_ = lean_ctor_get(v_a_3903_, 0);
v_isSharedCheck_3956_ = !lean_is_exclusive(v_a_3903_);
if (v_isSharedCheck_3956_ == 0)
{
v___x_3906_ = v_a_3903_;
v_isShared_3907_ = v_isSharedCheck_3956_;
goto v_resetjp_3905_;
}
else
{
lean_inc(v_val_3904_);
lean_dec(v_a_3903_);
v___x_3906_ = lean_box(0);
v_isShared_3907_ = v_isSharedCheck_3956_;
goto v_resetjp_3905_;
}
v_resetjp_3905_:
{
lean_object* v___x_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; 
v___x_3908_ = lean_box(0);
v___x_3909_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3_spec__6___closed__0));
lean_inc_ref(v_p_3877_);
lean_inc(v___y_3886_);
lean_inc_ref(v___y_3885_);
lean_inc(v___y_3884_);
lean_inc_ref(v___y_3883_);
lean_inc(v_val_3904_);
v___x_3910_ = lean_apply_6(v_p_3877_, v_val_3904_, v___y_3883_, v___y_3884_, v___y_3885_, v___y_3886_, lean_box(0));
if (lean_obj_tag(v___x_3910_) == 0)
{
lean_object* v_a_3911_; uint8_t v___x_3912_; 
v_a_3911_ = lean_ctor_get(v___x_3910_, 0);
lean_inc(v_a_3911_);
lean_dec_ref_known(v___x_3910_, 1);
v___x_3912_ = lean_unbox(v_a_3911_);
lean_dec(v_a_3911_);
if (v___x_3912_ == 0)
{
lean_del_object(v___x_3906_);
lean_dec(v_val_3904_);
lean_dec(v_snd_3890_);
v_a_3896_ = v___x_3909_;
goto v___jp_3895_;
}
else
{
lean_object* v___x_3913_; lean_object* v___x_3914_; uint8_t v___x_3915_; lean_object* v___x_3916_; lean_object* v___f_3917_; lean_object* v___x_3918_; 
v___x_3913_ = l_Lean_LocalDecl_fvarId(v_val_3904_);
lean_dec(v_val_3904_);
v___x_3914_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5___closed__1));
v___x_3915_ = 0;
v___x_3916_ = lean_box(v___x_3915_);
lean_inc(v_mvarId_3878_);
v___f_3917_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3___lam__0___boxed), 10, 5);
lean_closure_set(v___f_3917_, 0, v_mvarId_3878_);
lean_closure_set(v___f_3917_, 1, v___x_3913_);
lean_closure_set(v___f_3917_, 2, v___x_3914_);
lean_closure_set(v___f_3917_, 3, v___x_3916_);
lean_closure_set(v___f_3917_, 4, v___x_3894_);
v___x_3918_ = l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1___redArg(v___f_3917_, v___y_3883_, v___y_3884_, v___y_3885_, v___y_3886_);
if (lean_obj_tag(v___x_3918_) == 0)
{
lean_object* v_a_3919_; lean_object* v___x_3921_; uint8_t v_isShared_3922_; uint8_t v_isSharedCheck_3939_; 
v_a_3919_ = lean_ctor_get(v___x_3918_, 0);
v_isSharedCheck_3939_ = !lean_is_exclusive(v___x_3918_);
if (v_isSharedCheck_3939_ == 0)
{
v___x_3921_ = v___x_3918_;
v_isShared_3922_ = v_isSharedCheck_3939_;
goto v_resetjp_3920_;
}
else
{
lean_inc(v_a_3919_);
lean_dec(v___x_3918_);
v___x_3921_ = lean_box(0);
v_isShared_3922_ = v_isSharedCheck_3939_;
goto v_resetjp_3920_;
}
v_resetjp_3920_:
{
if (lean_obj_tag(v_a_3919_) == 0)
{
lean_del_object(v___x_3921_);
lean_del_object(v___x_3906_);
lean_dec(v_snd_3890_);
v_a_3896_ = v___x_3909_;
goto v___jp_3895_;
}
else
{
lean_object* v___x_3924_; 
lean_del_object(v___x_3892_);
lean_dec(v_mvarId_3878_);
lean_dec_ref(v_p_3877_);
lean_inc_ref(v_a_3919_);
if (v_isShared_3907_ == 0)
{
lean_ctor_set(v___x_3906_, 0, v_a_3919_);
v___x_3924_ = v___x_3906_;
goto v_reusejp_3923_;
}
else
{
lean_object* v_reuseFailAlloc_3938_; 
v_reuseFailAlloc_3938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3938_, 0, v_a_3919_);
v___x_3924_ = v_reuseFailAlloc_3938_;
goto v_reusejp_3923_;
}
v_reusejp_3923_:
{
lean_object* v___x_3926_; uint8_t v_isShared_3927_; uint8_t v_isSharedCheck_3936_; 
v_isSharedCheck_3936_ = !lean_is_exclusive(v_a_3919_);
if (v_isSharedCheck_3936_ == 0)
{
lean_object* v_unused_3937_; 
v_unused_3937_ = lean_ctor_get(v_a_3919_, 0);
lean_dec(v_unused_3937_);
v___x_3926_ = v_a_3919_;
v_isShared_3927_ = v_isSharedCheck_3936_;
goto v_resetjp_3925_;
}
else
{
lean_dec(v_a_3919_);
v___x_3926_ = lean_box(0);
v_isShared_3927_ = v_isSharedCheck_3936_;
goto v_resetjp_3925_;
}
v_resetjp_3925_:
{
lean_object* v___x_3928_; lean_object* v___x_3930_; 
v___x_3928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3928_, 0, v___x_3924_);
lean_ctor_set(v___x_3928_, 1, v___x_3908_);
if (v_isShared_3927_ == 0)
{
lean_ctor_set(v___x_3926_, 0, v___x_3928_);
v___x_3930_ = v___x_3926_;
goto v_reusejp_3929_;
}
else
{
lean_object* v_reuseFailAlloc_3935_; 
v_reuseFailAlloc_3935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3935_, 0, v___x_3928_);
v___x_3930_ = v_reuseFailAlloc_3935_;
goto v_reusejp_3929_;
}
v_reusejp_3929_:
{
lean_object* v___x_3931_; lean_object* v___x_3933_; 
v___x_3931_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3931_, 0, v___x_3930_);
lean_ctor_set(v___x_3931_, 1, v_snd_3890_);
if (v_isShared_3922_ == 0)
{
lean_ctor_set(v___x_3921_, 0, v___x_3931_);
v___x_3933_ = v___x_3921_;
goto v_reusejp_3932_;
}
else
{
lean_object* v_reuseFailAlloc_3934_; 
v_reuseFailAlloc_3934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3934_, 0, v___x_3931_);
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
}
}
else
{
lean_object* v_a_3940_; lean_object* v___x_3942_; uint8_t v_isShared_3943_; uint8_t v_isSharedCheck_3947_; 
lean_del_object(v___x_3906_);
lean_del_object(v___x_3892_);
lean_dec(v_snd_3890_);
lean_dec(v_mvarId_3878_);
lean_dec_ref(v_p_3877_);
v_a_3940_ = lean_ctor_get(v___x_3918_, 0);
v_isSharedCheck_3947_ = !lean_is_exclusive(v___x_3918_);
if (v_isSharedCheck_3947_ == 0)
{
v___x_3942_ = v___x_3918_;
v_isShared_3943_ = v_isSharedCheck_3947_;
goto v_resetjp_3941_;
}
else
{
lean_inc(v_a_3940_);
lean_dec(v___x_3918_);
v___x_3942_ = lean_box(0);
v_isShared_3943_ = v_isSharedCheck_3947_;
goto v_resetjp_3941_;
}
v_resetjp_3941_:
{
lean_object* v___x_3945_; 
if (v_isShared_3943_ == 0)
{
v___x_3945_ = v___x_3942_;
goto v_reusejp_3944_;
}
else
{
lean_object* v_reuseFailAlloc_3946_; 
v_reuseFailAlloc_3946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3946_, 0, v_a_3940_);
v___x_3945_ = v_reuseFailAlloc_3946_;
goto v_reusejp_3944_;
}
v_reusejp_3944_:
{
return v___x_3945_;
}
}
}
}
}
else
{
lean_object* v_a_3948_; lean_object* v___x_3950_; uint8_t v_isShared_3951_; uint8_t v_isSharedCheck_3955_; 
lean_del_object(v___x_3906_);
lean_dec(v_val_3904_);
lean_del_object(v___x_3892_);
lean_dec(v_snd_3890_);
lean_dec(v_mvarId_3878_);
lean_dec_ref(v_p_3877_);
v_a_3948_ = lean_ctor_get(v___x_3910_, 0);
v_isSharedCheck_3955_ = !lean_is_exclusive(v___x_3910_);
if (v_isSharedCheck_3955_ == 0)
{
v___x_3950_ = v___x_3910_;
v_isShared_3951_ = v_isSharedCheck_3955_;
goto v_resetjp_3949_;
}
else
{
lean_inc(v_a_3948_);
lean_dec(v___x_3910_);
v___x_3950_ = lean_box(0);
v_isShared_3951_ = v_isSharedCheck_3955_;
goto v_resetjp_3949_;
}
v_resetjp_3949_:
{
lean_object* v___x_3953_; 
if (v_isShared_3951_ == 0)
{
v___x_3953_ = v___x_3950_;
goto v_reusejp_3952_;
}
else
{
lean_object* v_reuseFailAlloc_3954_; 
v_reuseFailAlloc_3954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3954_, 0, v_a_3948_);
v___x_3953_ = v_reuseFailAlloc_3954_;
goto v_reusejp_3952_;
}
v_reusejp_3952_:
{
return v___x_3953_;
}
}
}
}
}
v___jp_3895_:
{
lean_object* v___x_3898_; 
if (v_isShared_3893_ == 0)
{
lean_ctor_set(v___x_3892_, 1, v_a_3896_);
lean_ctor_set(v___x_3892_, 0, v___x_3894_);
v___x_3898_ = v___x_3892_;
goto v_reusejp_3897_;
}
else
{
lean_object* v_reuseFailAlloc_3902_; 
v_reuseFailAlloc_3902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3902_, 0, v___x_3894_);
lean_ctor_set(v_reuseFailAlloc_3902_, 1, v_a_3896_);
v___x_3898_ = v_reuseFailAlloc_3902_;
goto v_reusejp_3897_;
}
v_reusejp_3897_:
{
size_t v___x_3899_; size_t v___x_3900_; lean_object* v___x_3901_; 
v___x_3899_ = ((size_t)1ULL);
v___x_3900_ = lean_usize_add(v_i_3881_, v___x_3899_);
v___x_3901_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3_spec__6(v_p_3877_, v_mvarId_3878_, v_as_3879_, v_sz_3880_, v___x_3900_, v___x_3898_, v___y_3883_, v___y_3884_, v___y_3885_, v___y_3886_);
return v___x_3901_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3___boxed(lean_object* v_p_3959_, lean_object* v_mvarId_3960_, lean_object* v_as_3961_, lean_object* v_sz_3962_, lean_object* v_i_3963_, lean_object* v_b_3964_, lean_object* v___y_3965_, lean_object* v___y_3966_, lean_object* v___y_3967_, lean_object* v___y_3968_, lean_object* v___y_3969_){
_start:
{
size_t v_sz_boxed_3970_; size_t v_i_boxed_3971_; lean_object* v_res_3972_; 
v_sz_boxed_3970_ = lean_unbox_usize(v_sz_3962_);
lean_dec(v_sz_3962_);
v_i_boxed_3971_ = lean_unbox_usize(v_i_3963_);
lean_dec(v_i_3963_);
v_res_3972_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3(v_p_3959_, v_mvarId_3960_, v_as_3961_, v_sz_boxed_3970_, v_i_boxed_3971_, v_b_3964_, v___y_3965_, v___y_3966_, v___y_3967_, v___y_3968_);
lean_dec(v___y_3968_);
lean_dec_ref(v___y_3967_);
lean_dec(v___y_3966_);
lean_dec_ref(v___y_3965_);
lean_dec_ref(v_as_3961_);
return v_res_3972_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2(lean_object* v_p_3973_, lean_object* v_mvarId_3974_, lean_object* v_t_3975_, lean_object* v_init_3976_, lean_object* v___y_3977_, lean_object* v___y_3978_, lean_object* v___y_3979_, lean_object* v___y_3980_){
_start:
{
lean_object* v_root_3982_; lean_object* v_tail_3983_; lean_object* v___x_3984_; 
v_root_3982_ = lean_ctor_get(v_t_3975_, 0);
v_tail_3983_ = lean_ctor_get(v_t_3975_, 1);
lean_inc(v_mvarId_3974_);
lean_inc_ref(v_p_3973_);
lean_inc_ref(v_init_3976_);
v___x_3984_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2(v_init_3976_, v_p_3973_, v_mvarId_3974_, v_root_3982_, v_init_3976_, v___y_3977_, v___y_3978_, v___y_3979_, v___y_3980_);
lean_dec_ref(v_init_3976_);
if (lean_obj_tag(v___x_3984_) == 0)
{
lean_object* v_a_3985_; lean_object* v___x_3987_; uint8_t v_isShared_3988_; uint8_t v_isSharedCheck_4021_; 
v_a_3985_ = lean_ctor_get(v___x_3984_, 0);
v_isSharedCheck_4021_ = !lean_is_exclusive(v___x_3984_);
if (v_isSharedCheck_4021_ == 0)
{
v___x_3987_ = v___x_3984_;
v_isShared_3988_ = v_isSharedCheck_4021_;
goto v_resetjp_3986_;
}
else
{
lean_inc(v_a_3985_);
lean_dec(v___x_3984_);
v___x_3987_ = lean_box(0);
v_isShared_3988_ = v_isSharedCheck_4021_;
goto v_resetjp_3986_;
}
v_resetjp_3986_:
{
if (lean_obj_tag(v_a_3985_) == 0)
{
lean_object* v_a_3989_; lean_object* v___x_3991_; 
lean_dec(v_mvarId_3974_);
lean_dec_ref(v_p_3973_);
v_a_3989_ = lean_ctor_get(v_a_3985_, 0);
lean_inc(v_a_3989_);
lean_dec_ref_known(v_a_3985_, 1);
if (v_isShared_3988_ == 0)
{
lean_ctor_set(v___x_3987_, 0, v_a_3989_);
v___x_3991_ = v___x_3987_;
goto v_reusejp_3990_;
}
else
{
lean_object* v_reuseFailAlloc_3992_; 
v_reuseFailAlloc_3992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3992_, 0, v_a_3989_);
v___x_3991_ = v_reuseFailAlloc_3992_;
goto v_reusejp_3990_;
}
v_reusejp_3990_:
{
return v___x_3991_;
}
}
else
{
lean_object* v_a_3993_; lean_object* v___x_3994_; lean_object* v___x_3995_; size_t v_sz_3996_; size_t v___x_3997_; lean_object* v___x_3998_; 
lean_del_object(v___x_3987_);
v_a_3993_ = lean_ctor_get(v_a_3985_, 0);
lean_inc(v_a_3993_);
lean_dec_ref_known(v_a_3985_, 1);
v___x_3994_ = lean_box(0);
v___x_3995_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3995_, 0, v___x_3994_);
lean_ctor_set(v___x_3995_, 1, v_a_3993_);
v_sz_3996_ = lean_array_size(v_tail_3983_);
v___x_3997_ = ((size_t)0ULL);
v___x_3998_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3(v_p_3973_, v_mvarId_3974_, v_tail_3983_, v_sz_3996_, v___x_3997_, v___x_3995_, v___y_3977_, v___y_3978_, v___y_3979_, v___y_3980_);
if (lean_obj_tag(v___x_3998_) == 0)
{
lean_object* v_a_3999_; lean_object* v___x_4001_; uint8_t v_isShared_4002_; uint8_t v_isSharedCheck_4012_; 
v_a_3999_ = lean_ctor_get(v___x_3998_, 0);
v_isSharedCheck_4012_ = !lean_is_exclusive(v___x_3998_);
if (v_isSharedCheck_4012_ == 0)
{
v___x_4001_ = v___x_3998_;
v_isShared_4002_ = v_isSharedCheck_4012_;
goto v_resetjp_4000_;
}
else
{
lean_inc(v_a_3999_);
lean_dec(v___x_3998_);
v___x_4001_ = lean_box(0);
v_isShared_4002_ = v_isSharedCheck_4012_;
goto v_resetjp_4000_;
}
v_resetjp_4000_:
{
lean_object* v_fst_4003_; 
v_fst_4003_ = lean_ctor_get(v_a_3999_, 0);
if (lean_obj_tag(v_fst_4003_) == 0)
{
lean_object* v_snd_4004_; lean_object* v___x_4006_; 
v_snd_4004_ = lean_ctor_get(v_a_3999_, 1);
lean_inc(v_snd_4004_);
lean_dec(v_a_3999_);
if (v_isShared_4002_ == 0)
{
lean_ctor_set(v___x_4001_, 0, v_snd_4004_);
v___x_4006_ = v___x_4001_;
goto v_reusejp_4005_;
}
else
{
lean_object* v_reuseFailAlloc_4007_; 
v_reuseFailAlloc_4007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4007_, 0, v_snd_4004_);
v___x_4006_ = v_reuseFailAlloc_4007_;
goto v_reusejp_4005_;
}
v_reusejp_4005_:
{
return v___x_4006_;
}
}
else
{
lean_object* v_val_4008_; lean_object* v___x_4010_; 
lean_inc_ref(v_fst_4003_);
lean_dec(v_a_3999_);
v_val_4008_ = lean_ctor_get(v_fst_4003_, 0);
lean_inc(v_val_4008_);
lean_dec_ref_known(v_fst_4003_, 1);
if (v_isShared_4002_ == 0)
{
lean_ctor_set(v___x_4001_, 0, v_val_4008_);
v___x_4010_ = v___x_4001_;
goto v_reusejp_4009_;
}
else
{
lean_object* v_reuseFailAlloc_4011_; 
v_reuseFailAlloc_4011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4011_, 0, v_val_4008_);
v___x_4010_ = v_reuseFailAlloc_4011_;
goto v_reusejp_4009_;
}
v_reusejp_4009_:
{
return v___x_4010_;
}
}
}
}
else
{
lean_object* v_a_4013_; lean_object* v___x_4015_; uint8_t v_isShared_4016_; uint8_t v_isSharedCheck_4020_; 
v_a_4013_ = lean_ctor_get(v___x_3998_, 0);
v_isSharedCheck_4020_ = !lean_is_exclusive(v___x_3998_);
if (v_isSharedCheck_4020_ == 0)
{
v___x_4015_ = v___x_3998_;
v_isShared_4016_ = v_isSharedCheck_4020_;
goto v_resetjp_4014_;
}
else
{
lean_inc(v_a_4013_);
lean_dec(v___x_3998_);
v___x_4015_ = lean_box(0);
v_isShared_4016_ = v_isSharedCheck_4020_;
goto v_resetjp_4014_;
}
v_resetjp_4014_:
{
lean_object* v___x_4018_; 
if (v_isShared_4016_ == 0)
{
v___x_4018_ = v___x_4015_;
goto v_reusejp_4017_;
}
else
{
lean_object* v_reuseFailAlloc_4019_; 
v_reuseFailAlloc_4019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4019_, 0, v_a_4013_);
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
else
{
lean_object* v_a_4022_; lean_object* v___x_4024_; uint8_t v_isShared_4025_; uint8_t v_isSharedCheck_4029_; 
lean_dec(v_mvarId_3974_);
lean_dec_ref(v_p_3973_);
v_a_4022_ = lean_ctor_get(v___x_3984_, 0);
v_isSharedCheck_4029_ = !lean_is_exclusive(v___x_3984_);
if (v_isSharedCheck_4029_ == 0)
{
v___x_4024_ = v___x_3984_;
v_isShared_4025_ = v_isSharedCheck_4029_;
goto v_resetjp_4023_;
}
else
{
lean_inc(v_a_4022_);
lean_dec(v___x_3984_);
v___x_4024_ = lean_box(0);
v_isShared_4025_ = v_isSharedCheck_4029_;
goto v_resetjp_4023_;
}
v_resetjp_4023_:
{
lean_object* v___x_4027_; 
if (v_isShared_4025_ == 0)
{
v___x_4027_ = v___x_4024_;
goto v_reusejp_4026_;
}
else
{
lean_object* v_reuseFailAlloc_4028_; 
v_reuseFailAlloc_4028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4028_, 0, v_a_4022_);
v___x_4027_ = v_reuseFailAlloc_4028_;
goto v_reusejp_4026_;
}
v_reusejp_4026_:
{
return v___x_4027_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2___boxed(lean_object* v_p_4030_, lean_object* v_mvarId_4031_, lean_object* v_t_4032_, lean_object* v_init_4033_, lean_object* v___y_4034_, lean_object* v___y_4035_, lean_object* v___y_4036_, lean_object* v___y_4037_, lean_object* v___y_4038_){
_start:
{
lean_object* v_res_4039_; 
v_res_4039_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2(v_p_4030_, v_mvarId_4031_, v_t_4032_, v_init_4033_, v___y_4034_, v___y_4035_, v___y_4036_, v___y_4037_);
lean_dec(v___y_4037_);
lean_dec_ref(v___y_4036_);
lean_dec(v___y_4035_);
lean_dec_ref(v___y_4034_);
lean_dec_ref(v_t_4032_);
return v_res_4039_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesRec___lam__0(lean_object* v_p_4043_, lean_object* v_mvarId_4044_, lean_object* v___y_4045_, lean_object* v___y_4046_, lean_object* v___y_4047_, lean_object* v___y_4048_){
_start:
{
lean_object* v_lctx_4050_; lean_object* v_decls_4051_; lean_object* v___x_4052_; lean_object* v___x_4053_; lean_object* v___x_4054_; 
v_lctx_4050_ = lean_ctor_get(v___y_4045_, 2);
v_decls_4051_ = lean_ctor_get(v_lctx_4050_, 1);
v___x_4052_ = lean_box(0);
v___x_4053_ = ((lean_object*)(l_Lean_MVarId_casesRec___lam__0___closed__0));
v___x_4054_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2(v_p_4043_, v_mvarId_4044_, v_decls_4051_, v___x_4053_, v___y_4045_, v___y_4046_, v___y_4047_, v___y_4048_);
if (lean_obj_tag(v___x_4054_) == 0)
{
lean_object* v_a_4055_; lean_object* v___x_4057_; uint8_t v_isShared_4058_; uint8_t v_isSharedCheck_4067_; 
v_a_4055_ = lean_ctor_get(v___x_4054_, 0);
v_isSharedCheck_4067_ = !lean_is_exclusive(v___x_4054_);
if (v_isSharedCheck_4067_ == 0)
{
v___x_4057_ = v___x_4054_;
v_isShared_4058_ = v_isSharedCheck_4067_;
goto v_resetjp_4056_;
}
else
{
lean_inc(v_a_4055_);
lean_dec(v___x_4054_);
v___x_4057_ = lean_box(0);
v_isShared_4058_ = v_isSharedCheck_4067_;
goto v_resetjp_4056_;
}
v_resetjp_4056_:
{
lean_object* v_fst_4059_; 
v_fst_4059_ = lean_ctor_get(v_a_4055_, 0);
lean_inc(v_fst_4059_);
lean_dec(v_a_4055_);
if (lean_obj_tag(v_fst_4059_) == 0)
{
lean_object* v___x_4061_; 
if (v_isShared_4058_ == 0)
{
lean_ctor_set(v___x_4057_, 0, v___x_4052_);
v___x_4061_ = v___x_4057_;
goto v_reusejp_4060_;
}
else
{
lean_object* v_reuseFailAlloc_4062_; 
v_reuseFailAlloc_4062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4062_, 0, v___x_4052_);
v___x_4061_ = v_reuseFailAlloc_4062_;
goto v_reusejp_4060_;
}
v_reusejp_4060_:
{
return v___x_4061_;
}
}
else
{
lean_object* v_val_4063_; lean_object* v___x_4065_; 
v_val_4063_ = lean_ctor_get(v_fst_4059_, 0);
lean_inc(v_val_4063_);
lean_dec_ref_known(v_fst_4059_, 1);
if (v_isShared_4058_ == 0)
{
lean_ctor_set(v___x_4057_, 0, v_val_4063_);
v___x_4065_ = v___x_4057_;
goto v_reusejp_4064_;
}
else
{
lean_object* v_reuseFailAlloc_4066_; 
v_reuseFailAlloc_4066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4066_, 0, v_val_4063_);
v___x_4065_ = v_reuseFailAlloc_4066_;
goto v_reusejp_4064_;
}
v_reusejp_4064_:
{
return v___x_4065_;
}
}
}
}
else
{
lean_object* v_a_4068_; lean_object* v___x_4070_; uint8_t v_isShared_4071_; uint8_t v_isSharedCheck_4075_; 
v_a_4068_ = lean_ctor_get(v___x_4054_, 0);
v_isSharedCheck_4075_ = !lean_is_exclusive(v___x_4054_);
if (v_isSharedCheck_4075_ == 0)
{
v___x_4070_ = v___x_4054_;
v_isShared_4071_ = v_isSharedCheck_4075_;
goto v_resetjp_4069_;
}
else
{
lean_inc(v_a_4068_);
lean_dec(v___x_4054_);
v___x_4070_ = lean_box(0);
v_isShared_4071_ = v_isSharedCheck_4075_;
goto v_resetjp_4069_;
}
v_resetjp_4069_:
{
lean_object* v___x_4073_; 
if (v_isShared_4071_ == 0)
{
v___x_4073_ = v___x_4070_;
goto v_reusejp_4072_;
}
else
{
lean_object* v_reuseFailAlloc_4074_; 
v_reuseFailAlloc_4074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4074_, 0, v_a_4068_);
v___x_4073_ = v_reuseFailAlloc_4074_;
goto v_reusejp_4072_;
}
v_reusejp_4072_:
{
return v___x_4073_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesRec___lam__0___boxed(lean_object* v_p_4076_, lean_object* v_mvarId_4077_, lean_object* v___y_4078_, lean_object* v___y_4079_, lean_object* v___y_4080_, lean_object* v___y_4081_, lean_object* v___y_4082_){
_start:
{
lean_object* v_res_4083_; 
v_res_4083_ = l_Lean_MVarId_casesRec___lam__0(v_p_4076_, v_mvarId_4077_, v___y_4078_, v___y_4079_, v___y_4080_, v___y_4081_);
lean_dec(v___y_4081_);
lean_dec_ref(v___y_4080_);
lean_dec(v___y_4079_);
lean_dec_ref(v___y_4078_);
return v_res_4083_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesRec___lam__1(lean_object* v_p_4084_, lean_object* v_mvarId_4085_, lean_object* v___y_4086_, lean_object* v___y_4087_, lean_object* v___y_4088_, lean_object* v___y_4089_){
_start:
{
lean_object* v___f_4091_; lean_object* v___x_4092_; 
lean_inc(v_mvarId_4085_);
v___f_4091_ = lean_alloc_closure((void*)(l_Lean_MVarId_casesRec___lam__0___boxed), 7, 2);
lean_closure_set(v___f_4091_, 0, v_p_4084_);
lean_closure_set(v___f_4091_, 1, v_mvarId_4085_);
v___x_4092_ = l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2___redArg(v_mvarId_4085_, v___f_4091_, v___y_4086_, v___y_4087_, v___y_4088_, v___y_4089_);
return v___x_4092_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesRec___lam__1___boxed(lean_object* v_p_4093_, lean_object* v_mvarId_4094_, lean_object* v___y_4095_, lean_object* v___y_4096_, lean_object* v___y_4097_, lean_object* v___y_4098_, lean_object* v___y_4099_){
_start:
{
lean_object* v_res_4100_; 
v_res_4100_ = l_Lean_MVarId_casesRec___lam__1(v_p_4093_, v_mvarId_4094_, v___y_4095_, v___y_4096_, v___y_4097_, v___y_4098_);
lean_dec(v___y_4098_);
lean_dec_ref(v___y_4097_);
lean_dec(v___y_4096_);
lean_dec_ref(v___y_4095_);
return v_res_4100_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesRec(lean_object* v_mvarId_4101_, lean_object* v_p_4102_, lean_object* v_a_4103_, lean_object* v_a_4104_, lean_object* v_a_4105_, lean_object* v_a_4106_){
_start:
{
lean_object* v___f_4108_; lean_object* v___x_4109_; 
v___f_4108_ = lean_alloc_closure((void*)(l_Lean_MVarId_casesRec___lam__1___boxed), 7, 1);
lean_closure_set(v___f_4108_, 0, v_p_4102_);
v___x_4109_ = l_Lean_Meta_saturate(v_mvarId_4101_, v___f_4108_, v_a_4103_, v_a_4104_, v_a_4105_, v_a_4106_);
return v___x_4109_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesRec___boxed(lean_object* v_mvarId_4110_, lean_object* v_p_4111_, lean_object* v_a_4112_, lean_object* v_a_4113_, lean_object* v_a_4114_, lean_object* v_a_4115_, lean_object* v_a_4116_){
_start:
{
lean_object* v_res_4117_; 
v_res_4117_ = l_Lean_MVarId_casesRec(v_mvarId_4110_, v_p_4111_, v_a_4112_, v_a_4113_, v_a_4114_, v_a_4115_);
lean_dec(v_a_4115_);
lean_dec_ref(v_a_4114_);
lean_dec(v_a_4113_);
lean_dec_ref(v_a_4112_);
return v_res_4117_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0___redArg(lean_object* v_e_4118_, lean_object* v___y_4119_){
_start:
{
uint8_t v___x_4121_; 
v___x_4121_ = l_Lean_Expr_hasMVar(v_e_4118_);
if (v___x_4121_ == 0)
{
lean_object* v___x_4122_; 
v___x_4122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4122_, 0, v_e_4118_);
return v___x_4122_;
}
else
{
lean_object* v___x_4123_; lean_object* v_mctx_4124_; lean_object* v___x_4125_; lean_object* v_fst_4126_; lean_object* v_snd_4127_; lean_object* v___x_4128_; lean_object* v_cache_4129_; lean_object* v_zetaDeltaFVarIds_4130_; lean_object* v_postponed_4131_; lean_object* v_diag_4132_; lean_object* v___x_4134_; uint8_t v_isShared_4135_; uint8_t v_isSharedCheck_4141_; 
v___x_4123_ = lean_st_ref_get(v___y_4119_);
v_mctx_4124_ = lean_ctor_get(v___x_4123_, 0);
lean_inc_ref(v_mctx_4124_);
lean_dec(v___x_4123_);
v___x_4125_ = l_Lean_instantiateMVarsCore(v_mctx_4124_, v_e_4118_);
v_fst_4126_ = lean_ctor_get(v___x_4125_, 0);
lean_inc(v_fst_4126_);
v_snd_4127_ = lean_ctor_get(v___x_4125_, 1);
lean_inc(v_snd_4127_);
lean_dec_ref(v___x_4125_);
v___x_4128_ = lean_st_ref_take(v___y_4119_);
v_cache_4129_ = lean_ctor_get(v___x_4128_, 1);
v_zetaDeltaFVarIds_4130_ = lean_ctor_get(v___x_4128_, 2);
v_postponed_4131_ = lean_ctor_get(v___x_4128_, 3);
v_diag_4132_ = lean_ctor_get(v___x_4128_, 4);
v_isSharedCheck_4141_ = !lean_is_exclusive(v___x_4128_);
if (v_isSharedCheck_4141_ == 0)
{
lean_object* v_unused_4142_; 
v_unused_4142_ = lean_ctor_get(v___x_4128_, 0);
lean_dec(v_unused_4142_);
v___x_4134_ = v___x_4128_;
v_isShared_4135_ = v_isSharedCheck_4141_;
goto v_resetjp_4133_;
}
else
{
lean_inc(v_diag_4132_);
lean_inc(v_postponed_4131_);
lean_inc(v_zetaDeltaFVarIds_4130_);
lean_inc(v_cache_4129_);
lean_dec(v___x_4128_);
v___x_4134_ = lean_box(0);
v_isShared_4135_ = v_isSharedCheck_4141_;
goto v_resetjp_4133_;
}
v_resetjp_4133_:
{
lean_object* v___x_4137_; 
if (v_isShared_4135_ == 0)
{
lean_ctor_set(v___x_4134_, 0, v_snd_4127_);
v___x_4137_ = v___x_4134_;
goto v_reusejp_4136_;
}
else
{
lean_object* v_reuseFailAlloc_4140_; 
v_reuseFailAlloc_4140_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4140_, 0, v_snd_4127_);
lean_ctor_set(v_reuseFailAlloc_4140_, 1, v_cache_4129_);
lean_ctor_set(v_reuseFailAlloc_4140_, 2, v_zetaDeltaFVarIds_4130_);
lean_ctor_set(v_reuseFailAlloc_4140_, 3, v_postponed_4131_);
lean_ctor_set(v_reuseFailAlloc_4140_, 4, v_diag_4132_);
v___x_4137_ = v_reuseFailAlloc_4140_;
goto v_reusejp_4136_;
}
v_reusejp_4136_:
{
lean_object* v___x_4138_; lean_object* v___x_4139_; 
v___x_4138_ = lean_st_ref_put(v___y_4119_, v___x_4137_);
v___x_4139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4139_, 0, v_fst_4126_);
return v___x_4139_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0___redArg___boxed(lean_object* v_e_4143_, lean_object* v___y_4144_, lean_object* v___y_4145_){
_start:
{
lean_object* v_res_4146_; 
v_res_4146_ = l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0___redArg(v_e_4143_, v___y_4144_);
lean_dec(v___y_4144_);
return v_res_4146_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0(lean_object* v_e_4147_, lean_object* v___y_4148_, lean_object* v___y_4149_, lean_object* v___y_4150_, lean_object* v___y_4151_){
_start:
{
lean_object* v___x_4153_; 
v___x_4153_ = l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0___redArg(v_e_4147_, v___y_4149_);
return v___x_4153_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0___boxed(lean_object* v_e_4154_, lean_object* v___y_4155_, lean_object* v___y_4156_, lean_object* v___y_4157_, lean_object* v___y_4158_, lean_object* v___y_4159_){
_start:
{
lean_object* v_res_4160_; 
v_res_4160_ = l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0(v_e_4154_, v___y_4155_, v___y_4156_, v___y_4157_, v___y_4158_);
lean_dec(v___y_4158_);
lean_dec_ref(v___y_4157_);
lean_dec(v___y_4156_);
lean_dec_ref(v___y_4155_);
return v_res_4160_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesAnd___lam__0(lean_object* v_localDecl_4164_, lean_object* v___y_4165_, lean_object* v___y_4166_, lean_object* v___y_4167_, lean_object* v___y_4168_){
_start:
{
lean_object* v___x_4170_; lean_object* v___x_4171_; lean_object* v_a_4172_; lean_object* v___x_4174_; uint8_t v_isShared_4175_; uint8_t v_isSharedCheck_4183_; 
v___x_4170_ = l_Lean_LocalDecl_type(v_localDecl_4164_);
v___x_4171_ = l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0___redArg(v___x_4170_, v___y_4166_);
v_a_4172_ = lean_ctor_get(v___x_4171_, 0);
v_isSharedCheck_4183_ = !lean_is_exclusive(v___x_4171_);
if (v_isSharedCheck_4183_ == 0)
{
v___x_4174_ = v___x_4171_;
v_isShared_4175_ = v_isSharedCheck_4183_;
goto v_resetjp_4173_;
}
else
{
lean_inc(v_a_4172_);
lean_dec(v___x_4171_);
v___x_4174_ = lean_box(0);
v_isShared_4175_ = v_isSharedCheck_4183_;
goto v_resetjp_4173_;
}
v_resetjp_4173_:
{
lean_object* v___x_4176_; lean_object* v___x_4177_; uint8_t v___x_4178_; lean_object* v___x_4179_; lean_object* v___x_4181_; 
v___x_4176_ = ((lean_object*)(l_Lean_MVarId_casesAnd___lam__0___closed__1));
v___x_4177_ = lean_unsigned_to_nat(2u);
v___x_4178_ = l_Lean_Expr_isAppOfArity(v_a_4172_, v___x_4176_, v___x_4177_);
lean_dec(v_a_4172_);
v___x_4179_ = lean_box(v___x_4178_);
if (v_isShared_4175_ == 0)
{
lean_ctor_set(v___x_4174_, 0, v___x_4179_);
v___x_4181_ = v___x_4174_;
goto v_reusejp_4180_;
}
else
{
lean_object* v_reuseFailAlloc_4182_; 
v_reuseFailAlloc_4182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4182_, 0, v___x_4179_);
v___x_4181_ = v_reuseFailAlloc_4182_;
goto v_reusejp_4180_;
}
v_reusejp_4180_:
{
return v___x_4181_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesAnd___lam__0___boxed(lean_object* v_localDecl_4184_, lean_object* v___y_4185_, lean_object* v___y_4186_, lean_object* v___y_4187_, lean_object* v___y_4188_, lean_object* v___y_4189_){
_start:
{
lean_object* v_res_4190_; 
v_res_4190_ = l_Lean_MVarId_casesAnd___lam__0(v_localDecl_4184_, v___y_4185_, v___y_4186_, v___y_4187_, v___y_4188_);
lean_dec(v___y_4188_);
lean_dec_ref(v___y_4187_);
lean_dec(v___y_4186_);
lean_dec_ref(v___y_4185_);
lean_dec_ref(v_localDecl_4184_);
return v_res_4190_;
}
}
static lean_object* _init_l_Lean_MVarId_casesAnd___closed__3(void){
_start:
{
lean_object* v___x_4195_; lean_object* v___x_4196_; 
v___x_4195_ = ((lean_object*)(l_Lean_MVarId_casesAnd___closed__2));
v___x_4196_ = l_Lean_MessageData_ofFormat(v___x_4195_);
return v___x_4196_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesAnd(lean_object* v_mvarId_4197_, lean_object* v_a_4198_, lean_object* v_a_4199_, lean_object* v_a_4200_, lean_object* v_a_4201_){
_start:
{
lean_object* v___f_4203_; lean_object* v___x_4204_; 
v___f_4203_ = ((lean_object*)(l_Lean_MVarId_casesAnd___closed__0));
v___x_4204_ = l_Lean_MVarId_casesRec(v_mvarId_4197_, v___f_4203_, v_a_4198_, v_a_4199_, v_a_4200_, v_a_4201_);
if (lean_obj_tag(v___x_4204_) == 0)
{
lean_object* v_a_4205_; lean_object* v___x_4206_; lean_object* v___x_4207_; 
v_a_4205_ = lean_ctor_get(v___x_4204_, 0);
lean_inc(v_a_4205_);
lean_dec_ref_known(v___x_4204_, 1);
v___x_4206_ = lean_obj_once(&l_Lean_MVarId_casesAnd___closed__3, &l_Lean_MVarId_casesAnd___closed__3_once, _init_l_Lean_MVarId_casesAnd___closed__3);
v___x_4207_ = l_Lean_Meta_exactlyOne(v_a_4205_, v___x_4206_, v_a_4198_, v_a_4199_, v_a_4200_, v_a_4201_);
lean_dec(v_a_4205_);
return v___x_4207_;
}
else
{
lean_object* v_a_4208_; lean_object* v___x_4210_; uint8_t v_isShared_4211_; uint8_t v_isSharedCheck_4215_; 
v_a_4208_ = lean_ctor_get(v___x_4204_, 0);
v_isSharedCheck_4215_ = !lean_is_exclusive(v___x_4204_);
if (v_isSharedCheck_4215_ == 0)
{
v___x_4210_ = v___x_4204_;
v_isShared_4211_ = v_isSharedCheck_4215_;
goto v_resetjp_4209_;
}
else
{
lean_inc(v_a_4208_);
lean_dec(v___x_4204_);
v___x_4210_ = lean_box(0);
v_isShared_4211_ = v_isSharedCheck_4215_;
goto v_resetjp_4209_;
}
v_resetjp_4209_:
{
lean_object* v___x_4213_; 
if (v_isShared_4211_ == 0)
{
v___x_4213_ = v___x_4210_;
goto v_reusejp_4212_;
}
else
{
lean_object* v_reuseFailAlloc_4214_; 
v_reuseFailAlloc_4214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4214_, 0, v_a_4208_);
v___x_4213_ = v_reuseFailAlloc_4214_;
goto v_reusejp_4212_;
}
v_reusejp_4212_:
{
return v___x_4213_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesAnd___boxed(lean_object* v_mvarId_4216_, lean_object* v_a_4217_, lean_object* v_a_4218_, lean_object* v_a_4219_, lean_object* v_a_4220_, lean_object* v_a_4221_){
_start:
{
lean_object* v_res_4222_; 
v_res_4222_ = l_Lean_MVarId_casesAnd(v_mvarId_4216_, v_a_4217_, v_a_4218_, v_a_4219_, v_a_4220_);
lean_dec(v_a_4220_);
lean_dec_ref(v_a_4219_);
lean_dec(v_a_4218_);
lean_dec_ref(v_a_4217_);
return v_res_4222_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_substEqs___lam__0(lean_object* v_localDecl_4223_, lean_object* v___y_4224_, lean_object* v___y_4225_, lean_object* v___y_4226_, lean_object* v___y_4227_){
_start:
{
lean_object* v___x_4229_; lean_object* v___x_4230_; lean_object* v_a_4231_; lean_object* v___x_4233_; uint8_t v_isShared_4234_; uint8_t v_isSharedCheck_4245_; 
v___x_4229_ = l_Lean_LocalDecl_type(v_localDecl_4223_);
v___x_4230_ = l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0___redArg(v___x_4229_, v___y_4225_);
v_a_4231_ = lean_ctor_get(v___x_4230_, 0);
v_isSharedCheck_4245_ = !lean_is_exclusive(v___x_4230_);
if (v_isSharedCheck_4245_ == 0)
{
v___x_4233_ = v___x_4230_;
v_isShared_4234_ = v_isSharedCheck_4245_;
goto v_resetjp_4232_;
}
else
{
lean_inc(v_a_4231_);
lean_dec(v___x_4230_);
v___x_4233_ = lean_box(0);
v_isShared_4234_ = v_isSharedCheck_4245_;
goto v_resetjp_4232_;
}
v_resetjp_4232_:
{
uint8_t v___x_4235_; 
v___x_4235_ = l_Lean_Expr_isEq(v_a_4231_);
if (v___x_4235_ == 0)
{
uint8_t v___x_4236_; lean_object* v___x_4237_; lean_object* v___x_4239_; 
v___x_4236_ = l_Lean_Expr_isHEq(v_a_4231_);
lean_dec(v_a_4231_);
v___x_4237_ = lean_box(v___x_4236_);
if (v_isShared_4234_ == 0)
{
lean_ctor_set(v___x_4233_, 0, v___x_4237_);
v___x_4239_ = v___x_4233_;
goto v_reusejp_4238_;
}
else
{
lean_object* v_reuseFailAlloc_4240_; 
v_reuseFailAlloc_4240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4240_, 0, v___x_4237_);
v___x_4239_ = v_reuseFailAlloc_4240_;
goto v_reusejp_4238_;
}
v_reusejp_4238_:
{
return v___x_4239_;
}
}
else
{
lean_object* v___x_4241_; lean_object* v___x_4243_; 
lean_dec(v_a_4231_);
v___x_4241_ = lean_box(v___x_4235_);
if (v_isShared_4234_ == 0)
{
lean_ctor_set(v___x_4233_, 0, v___x_4241_);
v___x_4243_ = v___x_4233_;
goto v_reusejp_4242_;
}
else
{
lean_object* v_reuseFailAlloc_4244_; 
v_reuseFailAlloc_4244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4244_, 0, v___x_4241_);
v___x_4243_ = v_reuseFailAlloc_4244_;
goto v_reusejp_4242_;
}
v_reusejp_4242_:
{
return v___x_4243_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_substEqs___lam__0___boxed(lean_object* v_localDecl_4246_, lean_object* v___y_4247_, lean_object* v___y_4248_, lean_object* v___y_4249_, lean_object* v___y_4250_, lean_object* v___y_4251_){
_start:
{
lean_object* v_res_4252_; 
v_res_4252_ = l_Lean_MVarId_substEqs___lam__0(v_localDecl_4246_, v___y_4247_, v___y_4248_, v___y_4249_, v___y_4250_);
lean_dec(v___y_4250_);
lean_dec_ref(v___y_4249_);
lean_dec(v___y_4248_);
lean_dec_ref(v___y_4247_);
lean_dec_ref(v_localDecl_4246_);
return v_res_4252_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_substEqs(lean_object* v_mvarId_4254_, lean_object* v_a_4255_, lean_object* v_a_4256_, lean_object* v_a_4257_, lean_object* v_a_4258_){
_start:
{
lean_object* v___f_4260_; lean_object* v___x_4261_; 
v___f_4260_ = ((lean_object*)(l_Lean_MVarId_substEqs___closed__0));
v___x_4261_ = l_Lean_MVarId_casesRec(v_mvarId_4254_, v___f_4260_, v_a_4255_, v_a_4256_, v_a_4257_, v_a_4258_);
if (lean_obj_tag(v___x_4261_) == 0)
{
lean_object* v_a_4262_; lean_object* v___x_4263_; lean_object* v___x_4264_; 
v_a_4262_ = lean_ctor_get(v___x_4261_, 0);
lean_inc(v_a_4262_);
lean_dec_ref_known(v___x_4261_, 1);
v___x_4263_ = lean_obj_once(&l_Lean_MVarId_casesAnd___closed__3, &l_Lean_MVarId_casesAnd___closed__3_once, _init_l_Lean_MVarId_casesAnd___closed__3);
v___x_4264_ = l_Lean_Meta_ensureAtMostOne(v_a_4262_, v___x_4263_, v_a_4255_, v_a_4256_, v_a_4257_, v_a_4258_);
lean_dec(v_a_4262_);
return v___x_4264_;
}
else
{
lean_object* v_a_4265_; lean_object* v___x_4267_; uint8_t v_isShared_4268_; uint8_t v_isSharedCheck_4272_; 
v_a_4265_ = lean_ctor_get(v___x_4261_, 0);
v_isSharedCheck_4272_ = !lean_is_exclusive(v___x_4261_);
if (v_isSharedCheck_4272_ == 0)
{
v___x_4267_ = v___x_4261_;
v_isShared_4268_ = v_isSharedCheck_4272_;
goto v_resetjp_4266_;
}
else
{
lean_inc(v_a_4265_);
lean_dec(v___x_4261_);
v___x_4267_ = lean_box(0);
v_isShared_4268_ = v_isSharedCheck_4272_;
goto v_resetjp_4266_;
}
v_resetjp_4266_:
{
lean_object* v___x_4270_; 
if (v_isShared_4268_ == 0)
{
v___x_4270_ = v___x_4267_;
goto v_reusejp_4269_;
}
else
{
lean_object* v_reuseFailAlloc_4271_; 
v_reuseFailAlloc_4271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4271_, 0, v_a_4265_);
v___x_4270_ = v_reuseFailAlloc_4271_;
goto v_reusejp_4269_;
}
v_reusejp_4269_:
{
return v___x_4270_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_substEqs___boxed(lean_object* v_mvarId_4273_, lean_object* v_a_4274_, lean_object* v_a_4275_, lean_object* v_a_4276_, lean_object* v_a_4277_, lean_object* v_a_4278_){
_start:
{
lean_object* v_res_4279_; 
v_res_4279_ = l_Lean_MVarId_substEqs(v_mvarId_4273_, v_a_4274_, v_a_4275_, v_a_4276_, v_a_4277_);
lean_dec(v_a_4277_);
lean_dec_ref(v_a_4276_);
lean_dec(v_a_4275_);
lean_dec_ref(v_a_4274_);
return v_res_4279_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkByCasesSubgoal___lam__0(lean_object* v_goalType_4280_, lean_object* v_tag_4281_, lean_object* v_hyp_4282_, lean_object* v___y_4283_, lean_object* v___y_4284_, lean_object* v___y_4285_, lean_object* v___y_4286_){
_start:
{
lean_object* v___x_4288_; 
v___x_4288_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_goalType_4280_, v_tag_4281_, v___y_4283_, v___y_4284_, v___y_4285_, v___y_4286_);
if (lean_obj_tag(v___x_4288_) == 0)
{
lean_object* v_a_4289_; lean_object* v___x_4290_; lean_object* v___x_4291_; lean_object* v___x_4292_; uint8_t v___x_4293_; uint8_t v___x_4294_; uint8_t v___x_4295_; lean_object* v___x_4296_; 
v_a_4289_ = lean_ctor_get(v___x_4288_, 0);
lean_inc_n(v_a_4289_, 2);
lean_dec_ref_known(v___x_4288_, 1);
v___x_4290_ = lean_unsigned_to_nat(1u);
v___x_4291_ = lean_mk_empty_array_with_capacity(v___x_4290_);
lean_inc_ref(v_hyp_4282_);
v___x_4292_ = lean_array_push(v___x_4291_, v_hyp_4282_);
v___x_4293_ = 0;
v___x_4294_ = 1;
v___x_4295_ = 1;
v___x_4296_ = l_Lean_Meta_mkLambdaFVars(v___x_4292_, v_a_4289_, v___x_4293_, v___x_4294_, v___x_4293_, v___x_4294_, v___x_4295_, v___y_4283_, v___y_4284_, v___y_4285_, v___y_4286_);
lean_dec_ref(v___x_4292_);
if (lean_obj_tag(v___x_4296_) == 0)
{
lean_object* v_a_4297_; lean_object* v___x_4299_; uint8_t v_isShared_4300_; uint8_t v_isSharedCheck_4308_; 
v_a_4297_ = lean_ctor_get(v___x_4296_, 0);
v_isSharedCheck_4308_ = !lean_is_exclusive(v___x_4296_);
if (v_isSharedCheck_4308_ == 0)
{
v___x_4299_ = v___x_4296_;
v_isShared_4300_ = v_isSharedCheck_4308_;
goto v_resetjp_4298_;
}
else
{
lean_inc(v_a_4297_);
lean_dec(v___x_4296_);
v___x_4299_ = lean_box(0);
v_isShared_4300_ = v_isSharedCheck_4308_;
goto v_resetjp_4298_;
}
v_resetjp_4298_:
{
lean_object* v___x_4301_; lean_object* v___x_4302_; lean_object* v___x_4303_; lean_object* v___x_4304_; lean_object* v___x_4306_; 
v___x_4301_ = l_Lean_Expr_mvarId_x21(v_a_4289_);
lean_dec(v_a_4289_);
v___x_4302_ = l_Lean_Expr_fvarId_x21(v_hyp_4282_);
lean_dec_ref(v_hyp_4282_);
v___x_4303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4303_, 0, v___x_4301_);
lean_ctor_set(v___x_4303_, 1, v___x_4302_);
v___x_4304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4304_, 0, v_a_4297_);
lean_ctor_set(v___x_4304_, 1, v___x_4303_);
if (v_isShared_4300_ == 0)
{
lean_ctor_set(v___x_4299_, 0, v___x_4304_);
v___x_4306_ = v___x_4299_;
goto v_reusejp_4305_;
}
else
{
lean_object* v_reuseFailAlloc_4307_; 
v_reuseFailAlloc_4307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4307_, 0, v___x_4304_);
v___x_4306_ = v_reuseFailAlloc_4307_;
goto v_reusejp_4305_;
}
v_reusejp_4305_:
{
return v___x_4306_;
}
}
}
else
{
lean_object* v_a_4309_; lean_object* v___x_4311_; uint8_t v_isShared_4312_; uint8_t v_isSharedCheck_4316_; 
lean_dec(v_a_4289_);
lean_dec_ref(v_hyp_4282_);
v_a_4309_ = lean_ctor_get(v___x_4296_, 0);
v_isSharedCheck_4316_ = !lean_is_exclusive(v___x_4296_);
if (v_isSharedCheck_4316_ == 0)
{
v___x_4311_ = v___x_4296_;
v_isShared_4312_ = v_isSharedCheck_4316_;
goto v_resetjp_4310_;
}
else
{
lean_inc(v_a_4309_);
lean_dec(v___x_4296_);
v___x_4311_ = lean_box(0);
v_isShared_4312_ = v_isSharedCheck_4316_;
goto v_resetjp_4310_;
}
v_resetjp_4310_:
{
lean_object* v___x_4314_; 
if (v_isShared_4312_ == 0)
{
v___x_4314_ = v___x_4311_;
goto v_reusejp_4313_;
}
else
{
lean_object* v_reuseFailAlloc_4315_; 
v_reuseFailAlloc_4315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4315_, 0, v_a_4309_);
v___x_4314_ = v_reuseFailAlloc_4315_;
goto v_reusejp_4313_;
}
v_reusejp_4313_:
{
return v___x_4314_;
}
}
}
}
else
{
lean_object* v_a_4317_; lean_object* v___x_4319_; uint8_t v_isShared_4320_; uint8_t v_isSharedCheck_4324_; 
lean_dec_ref(v_hyp_4282_);
v_a_4317_ = lean_ctor_get(v___x_4288_, 0);
v_isSharedCheck_4324_ = !lean_is_exclusive(v___x_4288_);
if (v_isSharedCheck_4324_ == 0)
{
v___x_4319_ = v___x_4288_;
v_isShared_4320_ = v_isSharedCheck_4324_;
goto v_resetjp_4318_;
}
else
{
lean_inc(v_a_4317_);
lean_dec(v___x_4288_);
v___x_4319_ = lean_box(0);
v_isShared_4320_ = v_isSharedCheck_4324_;
goto v_resetjp_4318_;
}
v_resetjp_4318_:
{
lean_object* v___x_4322_; 
if (v_isShared_4320_ == 0)
{
v___x_4322_ = v___x_4319_;
goto v_reusejp_4321_;
}
else
{
lean_object* v_reuseFailAlloc_4323_; 
v_reuseFailAlloc_4323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4323_, 0, v_a_4317_);
v___x_4322_ = v_reuseFailAlloc_4323_;
goto v_reusejp_4321_;
}
v_reusejp_4321_:
{
return v___x_4322_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkByCasesSubgoal___lam__0___boxed(lean_object* v_goalType_4325_, lean_object* v_tag_4326_, lean_object* v_hyp_4327_, lean_object* v___y_4328_, lean_object* v___y_4329_, lean_object* v___y_4330_, lean_object* v___y_4331_, lean_object* v___y_4332_){
_start:
{
lean_object* v_res_4333_; 
v_res_4333_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkByCasesSubgoal___lam__0(v_goalType_4325_, v_tag_4326_, v_hyp_4327_, v___y_4328_, v___y_4329_, v___y_4330_, v___y_4331_);
lean_dec(v___y_4331_);
lean_dec_ref(v___y_4330_);
lean_dec(v___y_4329_);
lean_dec_ref(v___y_4328_);
return v_res_4333_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkByCasesSubgoal(lean_object* v_p_4334_, lean_object* v_hName_4335_, lean_object* v_goalType_4336_, lean_object* v_tag_4337_, lean_object* v_a_4338_, lean_object* v_a_4339_, lean_object* v_a_4340_, lean_object* v_a_4341_){
_start:
{
lean_object* v___f_4343_; lean_object* v___x_4344_; 
v___f_4343_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkByCasesSubgoal___lam__0___boxed), 8, 2);
lean_closure_set(v___f_4343_, 0, v_goalType_4336_);
lean_closure_set(v___f_4343_, 1, v_tag_4337_);
v___x_4344_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0___redArg(v_hName_4335_, v_p_4334_, v___f_4343_, v_a_4338_, v_a_4339_, v_a_4340_, v_a_4341_);
return v___x_4344_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkByCasesSubgoal___boxed(lean_object* v_p_4345_, lean_object* v_hName_4346_, lean_object* v_goalType_4347_, lean_object* v_tag_4348_, lean_object* v_a_4349_, lean_object* v_a_4350_, lean_object* v_a_4351_, lean_object* v_a_4352_, lean_object* v_a_4353_){
_start:
{
lean_object* v_res_4354_; 
v_res_4354_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkByCasesSubgoal(v_p_4345_, v_hName_4346_, v_goalType_4347_, v_tag_4348_, v_a_4349_, v_a_4350_, v_a_4351_, v_a_4352_);
lean_dec(v_a_4352_);
lean_dec_ref(v_a_4351_);
lean_dec(v_a_4350_);
lean_dec_ref(v_a_4349_);
return v_res_4354_;
}
}
static lean_object* _init_l_Lean_MVarId_byCases___lam__0___closed__7(void){
_start:
{
lean_object* v___x_4366_; lean_object* v___x_4367_; lean_object* v___x_4368_; 
v___x_4366_ = lean_box(0);
v___x_4367_ = ((lean_object*)(l_Lean_MVarId_byCases___lam__0___closed__6));
v___x_4368_ = l_Lean_Expr_const___override(v___x_4367_, v___x_4366_);
return v___x_4368_;
}
}
static lean_object* _init_l_Lean_MVarId_byCases___lam__0___closed__10(void){
_start:
{
lean_object* v___x_4372_; lean_object* v___x_4373_; 
v___x_4372_ = ((lean_object*)(l_Lean_MVarId_byCases___lam__0___closed__9));
v___x_4373_ = l_Lean_stringToMessageData(v___x_4372_);
return v___x_4373_;
}
}
static lean_object* _init_l_Lean_MVarId_byCases___lam__0___closed__11(void){
_start:
{
lean_object* v___x_4374_; lean_object* v___x_4375_; 
v___x_4374_ = lean_obj_once(&l_Lean_MVarId_byCases___lam__0___closed__10, &l_Lean_MVarId_byCases___lam__0___closed__10_once, _init_l_Lean_MVarId_byCases___lam__0___closed__10);
v___x_4375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4375_, 0, v___x_4374_);
return v___x_4375_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_byCases___lam__0(lean_object* v_mvarId_4376_, lean_object* v_p_4377_, lean_object* v_hName_4378_, lean_object* v___y_4379_, lean_object* v___y_4380_, lean_object* v___y_4381_, lean_object* v___y_4382_){
_start:
{
lean_object* v___x_4384_; 
lean_inc(v_mvarId_4376_);
v___x_4384_ = l_Lean_MVarId_getType(v_mvarId_4376_, v___y_4379_, v___y_4380_, v___y_4381_, v___y_4382_);
if (lean_obj_tag(v___x_4384_) == 0)
{
lean_object* v_a_4385_; lean_object* v___x_4386_; 
v_a_4385_ = lean_ctor_get(v___x_4384_, 0);
lean_inc(v_a_4385_);
lean_dec_ref_known(v___x_4384_, 1);
lean_inc(v_mvarId_4376_);
v___x_4386_ = l_Lean_MVarId_getTag(v_mvarId_4376_, v___y_4379_, v___y_4380_, v___y_4381_, v___y_4382_);
if (lean_obj_tag(v___x_4386_) == 0)
{
lean_object* v_a_4387_; lean_object* v___y_4389_; lean_object* v___y_4390_; lean_object* v___y_4391_; lean_object* v___y_4392_; lean_object* v___x_4440_; 
v_a_4387_ = lean_ctor_get(v___x_4386_, 0);
lean_inc(v_a_4387_);
lean_dec_ref_known(v___x_4386_, 1);
lean_inc(v_a_4385_);
v___x_4440_ = l_Lean_Meta_isProp(v_a_4385_, v___y_4379_, v___y_4380_, v___y_4381_, v___y_4382_);
if (lean_obj_tag(v___x_4440_) == 0)
{
lean_object* v_a_4441_; uint8_t v___x_4442_; 
v_a_4441_ = lean_ctor_get(v___x_4440_, 0);
lean_inc(v_a_4441_);
lean_dec_ref_known(v___x_4440_, 1);
v___x_4442_ = lean_unbox(v_a_4441_);
lean_dec(v_a_4441_);
if (v___x_4442_ == 0)
{
lean_object* v___x_4443_; lean_object* v___x_4444_; lean_object* v___x_4445_; 
v___x_4443_ = ((lean_object*)(l_Lean_MVarId_byCases___lam__0___closed__8));
v___x_4444_ = lean_obj_once(&l_Lean_MVarId_byCases___lam__0___closed__11, &l_Lean_MVarId_byCases___lam__0___closed__11_once, _init_l_Lean_MVarId_byCases___lam__0___closed__11);
lean_inc(v_mvarId_4376_);
v___x_4445_ = l_Lean_Meta_throwTacticEx___redArg(v___x_4443_, v_mvarId_4376_, v___x_4444_, v___y_4379_, v___y_4380_, v___y_4381_, v___y_4382_);
if (lean_obj_tag(v___x_4445_) == 0)
{
lean_dec_ref_known(v___x_4445_, 1);
v___y_4389_ = v___y_4379_;
v___y_4390_ = v___y_4380_;
v___y_4391_ = v___y_4381_;
v___y_4392_ = v___y_4382_;
goto v___jp_4388_;
}
else
{
lean_object* v_a_4446_; lean_object* v___x_4448_; uint8_t v_isShared_4449_; uint8_t v_isSharedCheck_4453_; 
lean_dec(v_a_4387_);
lean_dec(v_a_4385_);
lean_dec(v_hName_4378_);
lean_dec_ref(v_p_4377_);
lean_dec(v_mvarId_4376_);
v_a_4446_ = lean_ctor_get(v___x_4445_, 0);
v_isSharedCheck_4453_ = !lean_is_exclusive(v___x_4445_);
if (v_isSharedCheck_4453_ == 0)
{
v___x_4448_ = v___x_4445_;
v_isShared_4449_ = v_isSharedCheck_4453_;
goto v_resetjp_4447_;
}
else
{
lean_inc(v_a_4446_);
lean_dec(v___x_4445_);
v___x_4448_ = lean_box(0);
v_isShared_4449_ = v_isSharedCheck_4453_;
goto v_resetjp_4447_;
}
v_resetjp_4447_:
{
lean_object* v___x_4451_; 
if (v_isShared_4449_ == 0)
{
v___x_4451_ = v___x_4448_;
goto v_reusejp_4450_;
}
else
{
lean_object* v_reuseFailAlloc_4452_; 
v_reuseFailAlloc_4452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4452_, 0, v_a_4446_);
v___x_4451_ = v_reuseFailAlloc_4452_;
goto v_reusejp_4450_;
}
v_reusejp_4450_:
{
return v___x_4451_;
}
}
}
}
else
{
v___y_4389_ = v___y_4379_;
v___y_4390_ = v___y_4380_;
v___y_4391_ = v___y_4381_;
v___y_4392_ = v___y_4382_;
goto v___jp_4388_;
}
}
else
{
lean_object* v_a_4454_; lean_object* v___x_4456_; uint8_t v_isShared_4457_; uint8_t v_isSharedCheck_4461_; 
lean_dec(v_a_4387_);
lean_dec(v_a_4385_);
lean_dec(v_hName_4378_);
lean_dec_ref(v_p_4377_);
lean_dec(v_mvarId_4376_);
v_a_4454_ = lean_ctor_get(v___x_4440_, 0);
v_isSharedCheck_4461_ = !lean_is_exclusive(v___x_4440_);
if (v_isSharedCheck_4461_ == 0)
{
v___x_4456_ = v___x_4440_;
v_isShared_4457_ = v_isSharedCheck_4461_;
goto v_resetjp_4455_;
}
else
{
lean_inc(v_a_4454_);
lean_dec(v___x_4440_);
v___x_4456_ = lean_box(0);
v_isShared_4457_ = v_isSharedCheck_4461_;
goto v_resetjp_4455_;
}
v_resetjp_4455_:
{
lean_object* v___x_4459_; 
if (v_isShared_4457_ == 0)
{
v___x_4459_ = v___x_4456_;
goto v_reusejp_4458_;
}
else
{
lean_object* v_reuseFailAlloc_4460_; 
v_reuseFailAlloc_4460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4460_, 0, v_a_4454_);
v___x_4459_ = v_reuseFailAlloc_4460_;
goto v_reusejp_4458_;
}
v_reusejp_4458_:
{
return v___x_4459_;
}
}
}
v___jp_4388_:
{
lean_object* v___x_4393_; lean_object* v___x_4394_; lean_object* v___x_4395_; 
v___x_4393_ = ((lean_object*)(l_Lean_MVarId_byCases___lam__0___closed__1));
lean_inc(v_a_4387_);
v___x_4394_ = l_Lean_Name_append(v_a_4387_, v___x_4393_);
lean_inc(v_a_4385_);
lean_inc(v_hName_4378_);
lean_inc_ref(v_p_4377_);
v___x_4395_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkByCasesSubgoal(v_p_4377_, v_hName_4378_, v_a_4385_, v___x_4394_, v___y_4389_, v___y_4390_, v___y_4391_, v___y_4392_);
if (lean_obj_tag(v___x_4395_) == 0)
{
lean_object* v_a_4396_; lean_object* v_fst_4397_; lean_object* v_snd_4398_; lean_object* v___x_4399_; lean_object* v___x_4400_; lean_object* v___x_4401_; lean_object* v___x_4402_; 
v_a_4396_ = lean_ctor_get(v___x_4395_, 0);
lean_inc(v_a_4396_);
lean_dec_ref_known(v___x_4395_, 1);
v_fst_4397_ = lean_ctor_get(v_a_4396_, 0);
lean_inc(v_fst_4397_);
v_snd_4398_ = lean_ctor_get(v_a_4396_, 1);
lean_inc(v_snd_4398_);
lean_dec(v_a_4396_);
lean_inc_ref(v_p_4377_);
v___x_4399_ = l_Lean_mkNot(v_p_4377_);
v___x_4400_ = ((lean_object*)(l_Lean_MVarId_byCases___lam__0___closed__3));
v___x_4401_ = l_Lean_Name_append(v_a_4387_, v___x_4400_);
lean_inc(v_a_4385_);
v___x_4402_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkByCasesSubgoal(v___x_4399_, v_hName_4378_, v_a_4385_, v___x_4401_, v___y_4389_, v___y_4390_, v___y_4391_, v___y_4392_);
if (lean_obj_tag(v___x_4402_) == 0)
{
lean_object* v_a_4403_; lean_object* v_fst_4404_; lean_object* v_snd_4405_; lean_object* v___x_4407_; uint8_t v_isShared_4408_; uint8_t v_isSharedCheck_4423_; 
v_a_4403_ = lean_ctor_get(v___x_4402_, 0);
lean_inc(v_a_4403_);
lean_dec_ref_known(v___x_4402_, 1);
v_fst_4404_ = lean_ctor_get(v_a_4403_, 0);
v_snd_4405_ = lean_ctor_get(v_a_4403_, 1);
v_isSharedCheck_4423_ = !lean_is_exclusive(v_a_4403_);
if (v_isSharedCheck_4423_ == 0)
{
v___x_4407_ = v_a_4403_;
v_isShared_4408_ = v_isSharedCheck_4423_;
goto v_resetjp_4406_;
}
else
{
lean_inc(v_snd_4405_);
lean_inc(v_fst_4404_);
lean_dec(v_a_4403_);
v___x_4407_ = lean_box(0);
v_isShared_4408_ = v_isSharedCheck_4423_;
goto v_resetjp_4406_;
}
v_resetjp_4406_:
{
lean_object* v___x_4409_; lean_object* v___x_4410_; lean_object* v___x_4411_; lean_object* v___x_4413_; uint8_t v_isShared_4414_; uint8_t v_isSharedCheck_4421_; 
v___x_4409_ = lean_obj_once(&l_Lean_MVarId_byCases___lam__0___closed__7, &l_Lean_MVarId_byCases___lam__0___closed__7_once, _init_l_Lean_MVarId_byCases___lam__0___closed__7);
v___x_4410_ = l_Lean_mkApp4(v___x_4409_, v_p_4377_, v_a_4385_, v_fst_4397_, v_fst_4404_);
v___x_4411_ = l_Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1___redArg(v_mvarId_4376_, v___x_4410_, v___y_4390_);
v_isSharedCheck_4421_ = !lean_is_exclusive(v___x_4411_);
if (v_isSharedCheck_4421_ == 0)
{
lean_object* v_unused_4422_; 
v_unused_4422_ = lean_ctor_get(v___x_4411_, 0);
lean_dec(v_unused_4422_);
v___x_4413_ = v___x_4411_;
v_isShared_4414_ = v_isSharedCheck_4421_;
goto v_resetjp_4412_;
}
else
{
lean_dec(v___x_4411_);
v___x_4413_ = lean_box(0);
v_isShared_4414_ = v_isSharedCheck_4421_;
goto v_resetjp_4412_;
}
v_resetjp_4412_:
{
lean_object* v___x_4416_; 
if (v_isShared_4408_ == 0)
{
lean_ctor_set(v___x_4407_, 0, v_snd_4398_);
v___x_4416_ = v___x_4407_;
goto v_reusejp_4415_;
}
else
{
lean_object* v_reuseFailAlloc_4420_; 
v_reuseFailAlloc_4420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4420_, 0, v_snd_4398_);
lean_ctor_set(v_reuseFailAlloc_4420_, 1, v_snd_4405_);
v___x_4416_ = v_reuseFailAlloc_4420_;
goto v_reusejp_4415_;
}
v_reusejp_4415_:
{
lean_object* v___x_4418_; 
if (v_isShared_4414_ == 0)
{
lean_ctor_set(v___x_4413_, 0, v___x_4416_);
v___x_4418_ = v___x_4413_;
goto v_reusejp_4417_;
}
else
{
lean_object* v_reuseFailAlloc_4419_; 
v_reuseFailAlloc_4419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4419_, 0, v___x_4416_);
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
else
{
lean_object* v_a_4424_; lean_object* v___x_4426_; uint8_t v_isShared_4427_; uint8_t v_isSharedCheck_4431_; 
lean_dec(v_snd_4398_);
lean_dec(v_fst_4397_);
lean_dec(v_a_4385_);
lean_dec_ref(v_p_4377_);
lean_dec(v_mvarId_4376_);
v_a_4424_ = lean_ctor_get(v___x_4402_, 0);
v_isSharedCheck_4431_ = !lean_is_exclusive(v___x_4402_);
if (v_isSharedCheck_4431_ == 0)
{
v___x_4426_ = v___x_4402_;
v_isShared_4427_ = v_isSharedCheck_4431_;
goto v_resetjp_4425_;
}
else
{
lean_inc(v_a_4424_);
lean_dec(v___x_4402_);
v___x_4426_ = lean_box(0);
v_isShared_4427_ = v_isSharedCheck_4431_;
goto v_resetjp_4425_;
}
v_resetjp_4425_:
{
lean_object* v___x_4429_; 
if (v_isShared_4427_ == 0)
{
v___x_4429_ = v___x_4426_;
goto v_reusejp_4428_;
}
else
{
lean_object* v_reuseFailAlloc_4430_; 
v_reuseFailAlloc_4430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4430_, 0, v_a_4424_);
v___x_4429_ = v_reuseFailAlloc_4430_;
goto v_reusejp_4428_;
}
v_reusejp_4428_:
{
return v___x_4429_;
}
}
}
}
else
{
lean_object* v_a_4432_; lean_object* v___x_4434_; uint8_t v_isShared_4435_; uint8_t v_isSharedCheck_4439_; 
lean_dec(v_a_4387_);
lean_dec(v_a_4385_);
lean_dec(v_hName_4378_);
lean_dec_ref(v_p_4377_);
lean_dec(v_mvarId_4376_);
v_a_4432_ = lean_ctor_get(v___x_4395_, 0);
v_isSharedCheck_4439_ = !lean_is_exclusive(v___x_4395_);
if (v_isSharedCheck_4439_ == 0)
{
v___x_4434_ = v___x_4395_;
v_isShared_4435_ = v_isSharedCheck_4439_;
goto v_resetjp_4433_;
}
else
{
lean_inc(v_a_4432_);
lean_dec(v___x_4395_);
v___x_4434_ = lean_box(0);
v_isShared_4435_ = v_isSharedCheck_4439_;
goto v_resetjp_4433_;
}
v_resetjp_4433_:
{
lean_object* v___x_4437_; 
if (v_isShared_4435_ == 0)
{
v___x_4437_ = v___x_4434_;
goto v_reusejp_4436_;
}
else
{
lean_object* v_reuseFailAlloc_4438_; 
v_reuseFailAlloc_4438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4438_, 0, v_a_4432_);
v___x_4437_ = v_reuseFailAlloc_4438_;
goto v_reusejp_4436_;
}
v_reusejp_4436_:
{
return v___x_4437_;
}
}
}
}
}
else
{
lean_object* v_a_4462_; lean_object* v___x_4464_; uint8_t v_isShared_4465_; uint8_t v_isSharedCheck_4469_; 
lean_dec(v_a_4385_);
lean_dec(v_hName_4378_);
lean_dec_ref(v_p_4377_);
lean_dec(v_mvarId_4376_);
v_a_4462_ = lean_ctor_get(v___x_4386_, 0);
v_isSharedCheck_4469_ = !lean_is_exclusive(v___x_4386_);
if (v_isSharedCheck_4469_ == 0)
{
v___x_4464_ = v___x_4386_;
v_isShared_4465_ = v_isSharedCheck_4469_;
goto v_resetjp_4463_;
}
else
{
lean_inc(v_a_4462_);
lean_dec(v___x_4386_);
v___x_4464_ = lean_box(0);
v_isShared_4465_ = v_isSharedCheck_4469_;
goto v_resetjp_4463_;
}
v_resetjp_4463_:
{
lean_object* v___x_4467_; 
if (v_isShared_4465_ == 0)
{
v___x_4467_ = v___x_4464_;
goto v_reusejp_4466_;
}
else
{
lean_object* v_reuseFailAlloc_4468_; 
v_reuseFailAlloc_4468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4468_, 0, v_a_4462_);
v___x_4467_ = v_reuseFailAlloc_4468_;
goto v_reusejp_4466_;
}
v_reusejp_4466_:
{
return v___x_4467_;
}
}
}
}
else
{
lean_object* v_a_4470_; lean_object* v___x_4472_; uint8_t v_isShared_4473_; uint8_t v_isSharedCheck_4477_; 
lean_dec(v_hName_4378_);
lean_dec_ref(v_p_4377_);
lean_dec(v_mvarId_4376_);
v_a_4470_ = lean_ctor_get(v___x_4384_, 0);
v_isSharedCheck_4477_ = !lean_is_exclusive(v___x_4384_);
if (v_isSharedCheck_4477_ == 0)
{
v___x_4472_ = v___x_4384_;
v_isShared_4473_ = v_isSharedCheck_4477_;
goto v_resetjp_4471_;
}
else
{
lean_inc(v_a_4470_);
lean_dec(v___x_4384_);
v___x_4472_ = lean_box(0);
v_isShared_4473_ = v_isSharedCheck_4477_;
goto v_resetjp_4471_;
}
v_resetjp_4471_:
{
lean_object* v___x_4475_; 
if (v_isShared_4473_ == 0)
{
v___x_4475_ = v___x_4472_;
goto v_reusejp_4474_;
}
else
{
lean_object* v_reuseFailAlloc_4476_; 
v_reuseFailAlloc_4476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4476_, 0, v_a_4470_);
v___x_4475_ = v_reuseFailAlloc_4476_;
goto v_reusejp_4474_;
}
v_reusejp_4474_:
{
return v___x_4475_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_byCases___lam__0___boxed(lean_object* v_mvarId_4478_, lean_object* v_p_4479_, lean_object* v_hName_4480_, lean_object* v___y_4481_, lean_object* v___y_4482_, lean_object* v___y_4483_, lean_object* v___y_4484_, lean_object* v___y_4485_){
_start:
{
lean_object* v_res_4486_; 
v_res_4486_ = l_Lean_MVarId_byCases___lam__0(v_mvarId_4478_, v_p_4479_, v_hName_4480_, v___y_4481_, v___y_4482_, v___y_4483_, v___y_4484_);
lean_dec(v___y_4484_);
lean_dec_ref(v___y_4483_);
lean_dec(v___y_4482_);
lean_dec_ref(v___y_4481_);
return v_res_4486_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_byCases(lean_object* v_mvarId_4487_, lean_object* v_p_4488_, lean_object* v_hName_4489_, lean_object* v_a_4490_, lean_object* v_a_4491_, lean_object* v_a_4492_, lean_object* v_a_4493_){
_start:
{
lean_object* v___f_4495_; lean_object* v___x_4496_; 
lean_inc(v_mvarId_4487_);
v___f_4495_ = lean_alloc_closure((void*)(l_Lean_MVarId_byCases___lam__0___boxed), 8, 3);
lean_closure_set(v___f_4495_, 0, v_mvarId_4487_);
lean_closure_set(v___f_4495_, 1, v_p_4488_);
lean_closure_set(v___f_4495_, 2, v_hName_4489_);
v___x_4496_ = l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2___redArg(v_mvarId_4487_, v___f_4495_, v_a_4490_, v_a_4491_, v_a_4492_, v_a_4493_);
return v___x_4496_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_byCases___boxed(lean_object* v_mvarId_4497_, lean_object* v_p_4498_, lean_object* v_hName_4499_, lean_object* v_a_4500_, lean_object* v_a_4501_, lean_object* v_a_4502_, lean_object* v_a_4503_, lean_object* v_a_4504_){
_start:
{
lean_object* v_res_4505_; 
v_res_4505_ = l_Lean_MVarId_byCases(v_mvarId_4497_, v_p_4498_, v_hName_4499_, v_a_4500_, v_a_4501_, v_a_4502_, v_a_4503_);
lean_dec(v_a_4503_);
lean_dec_ref(v_a_4502_);
lean_dec(v_a_4501_);
lean_dec_ref(v_a_4500_);
return v_res_4505_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_byCasesDec___lam__0(lean_object* v_mvarId_4509_, lean_object* v_p_4510_, lean_object* v_hName_4511_, lean_object* v_dec_4512_, lean_object* v___y_4513_, lean_object* v___y_4514_, lean_object* v___y_4515_, lean_object* v___y_4516_){
_start:
{
lean_object* v___x_4518_; 
lean_inc(v_mvarId_4509_);
v___x_4518_ = l_Lean_MVarId_getType(v_mvarId_4509_, v___y_4513_, v___y_4514_, v___y_4515_, v___y_4516_);
if (lean_obj_tag(v___x_4518_) == 0)
{
lean_object* v_a_4519_; lean_object* v___x_4520_; 
v_a_4519_ = lean_ctor_get(v___x_4518_, 0);
lean_inc(v_a_4519_);
lean_dec_ref_known(v___x_4518_, 1);
lean_inc(v_mvarId_4509_);
v___x_4520_ = l_Lean_MVarId_getTag(v_mvarId_4509_, v___y_4513_, v___y_4514_, v___y_4515_, v___y_4516_);
if (lean_obj_tag(v___x_4520_) == 0)
{
lean_object* v_a_4521_; lean_object* v___x_4522_; 
v_a_4521_ = lean_ctor_get(v___x_4520_, 0);
lean_inc(v_a_4521_);
lean_dec_ref_known(v___x_4520_, 1);
lean_inc(v_a_4519_);
v___x_4522_ = l_Lean_Meta_getLevel(v_a_4519_, v___y_4513_, v___y_4514_, v___y_4515_, v___y_4516_);
if (lean_obj_tag(v___x_4522_) == 0)
{
lean_object* v_a_4523_; lean_object* v___x_4524_; lean_object* v___x_4525_; lean_object* v___x_4526_; 
v_a_4523_ = lean_ctor_get(v___x_4522_, 0);
lean_inc(v_a_4523_);
lean_dec_ref_known(v___x_4522_, 1);
v___x_4524_ = ((lean_object*)(l_Lean_MVarId_byCases___lam__0___closed__1));
lean_inc(v_a_4521_);
v___x_4525_ = l_Lean_Name_append(v_a_4521_, v___x_4524_);
lean_inc(v_a_4519_);
lean_inc(v_hName_4511_);
lean_inc_ref(v_p_4510_);
v___x_4526_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkByCasesSubgoal(v_p_4510_, v_hName_4511_, v_a_4519_, v___x_4525_, v___y_4513_, v___y_4514_, v___y_4515_, v___y_4516_);
if (lean_obj_tag(v___x_4526_) == 0)
{
lean_object* v_a_4527_; lean_object* v_fst_4528_; lean_object* v_snd_4529_; lean_object* v___x_4531_; uint8_t v_isShared_4532_; uint8_t v_isSharedCheck_4571_; 
v_a_4527_ = lean_ctor_get(v___x_4526_, 0);
lean_inc(v_a_4527_);
lean_dec_ref_known(v___x_4526_, 1);
v_fst_4528_ = lean_ctor_get(v_a_4527_, 0);
v_snd_4529_ = lean_ctor_get(v_a_4527_, 1);
v_isSharedCheck_4571_ = !lean_is_exclusive(v_a_4527_);
if (v_isSharedCheck_4571_ == 0)
{
v___x_4531_ = v_a_4527_;
v_isShared_4532_ = v_isSharedCheck_4571_;
goto v_resetjp_4530_;
}
else
{
lean_inc(v_snd_4529_);
lean_inc(v_fst_4528_);
lean_dec(v_a_4527_);
v___x_4531_ = lean_box(0);
v_isShared_4532_ = v_isSharedCheck_4571_;
goto v_resetjp_4530_;
}
v_resetjp_4530_:
{
lean_object* v___x_4533_; lean_object* v___x_4534_; lean_object* v___x_4535_; lean_object* v___x_4536_; 
lean_inc_ref(v_p_4510_);
v___x_4533_ = l_Lean_mkNot(v_p_4510_);
v___x_4534_ = ((lean_object*)(l_Lean_MVarId_byCases___lam__0___closed__3));
v___x_4535_ = l_Lean_Name_append(v_a_4521_, v___x_4534_);
lean_inc(v_a_4519_);
v___x_4536_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkByCasesSubgoal(v___x_4533_, v_hName_4511_, v_a_4519_, v___x_4535_, v___y_4513_, v___y_4514_, v___y_4515_, v___y_4516_);
if (lean_obj_tag(v___x_4536_) == 0)
{
lean_object* v_a_4537_; lean_object* v_fst_4538_; lean_object* v_snd_4539_; lean_object* v___x_4541_; uint8_t v_isShared_4542_; uint8_t v_isSharedCheck_4562_; 
v_a_4537_ = lean_ctor_get(v___x_4536_, 0);
lean_inc(v_a_4537_);
lean_dec_ref_known(v___x_4536_, 1);
v_fst_4538_ = lean_ctor_get(v_a_4537_, 0);
v_snd_4539_ = lean_ctor_get(v_a_4537_, 1);
v_isSharedCheck_4562_ = !lean_is_exclusive(v_a_4537_);
if (v_isSharedCheck_4562_ == 0)
{
v___x_4541_ = v_a_4537_;
v_isShared_4542_ = v_isSharedCheck_4562_;
goto v_resetjp_4540_;
}
else
{
lean_inc(v_snd_4539_);
lean_inc(v_fst_4538_);
lean_dec(v_a_4537_);
v___x_4541_ = lean_box(0);
v_isShared_4542_ = v_isSharedCheck_4562_;
goto v_resetjp_4540_;
}
v_resetjp_4540_:
{
lean_object* v___x_4543_; lean_object* v___x_4544_; lean_object* v___x_4546_; 
v___x_4543_ = ((lean_object*)(l_Lean_MVarId_byCasesDec___lam__0___closed__1));
v___x_4544_ = lean_box(0);
if (v_isShared_4532_ == 0)
{
lean_ctor_set_tag(v___x_4531_, 1);
lean_ctor_set(v___x_4531_, 1, v___x_4544_);
lean_ctor_set(v___x_4531_, 0, v_a_4523_);
v___x_4546_ = v___x_4531_;
goto v_reusejp_4545_;
}
else
{
lean_object* v_reuseFailAlloc_4561_; 
v_reuseFailAlloc_4561_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4561_, 0, v_a_4523_);
lean_ctor_set(v_reuseFailAlloc_4561_, 1, v___x_4544_);
v___x_4546_ = v_reuseFailAlloc_4561_;
goto v_reusejp_4545_;
}
v_reusejp_4545_:
{
lean_object* v___x_4547_; lean_object* v___x_4548_; lean_object* v___x_4549_; lean_object* v___x_4551_; uint8_t v_isShared_4552_; uint8_t v_isSharedCheck_4559_; 
v___x_4547_ = l_Lean_Expr_const___override(v___x_4543_, v___x_4546_);
v___x_4548_ = l_Lean_mkApp5(v___x_4547_, v_a_4519_, v_p_4510_, v_dec_4512_, v_fst_4528_, v_fst_4538_);
v___x_4549_ = l_Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1___redArg(v_mvarId_4509_, v___x_4548_, v___y_4514_);
v_isSharedCheck_4559_ = !lean_is_exclusive(v___x_4549_);
if (v_isSharedCheck_4559_ == 0)
{
lean_object* v_unused_4560_; 
v_unused_4560_ = lean_ctor_get(v___x_4549_, 0);
lean_dec(v_unused_4560_);
v___x_4551_ = v___x_4549_;
v_isShared_4552_ = v_isSharedCheck_4559_;
goto v_resetjp_4550_;
}
else
{
lean_dec(v___x_4549_);
v___x_4551_ = lean_box(0);
v_isShared_4552_ = v_isSharedCheck_4559_;
goto v_resetjp_4550_;
}
v_resetjp_4550_:
{
lean_object* v___x_4554_; 
if (v_isShared_4542_ == 0)
{
lean_ctor_set(v___x_4541_, 0, v_snd_4529_);
v___x_4554_ = v___x_4541_;
goto v_reusejp_4553_;
}
else
{
lean_object* v_reuseFailAlloc_4558_; 
v_reuseFailAlloc_4558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4558_, 0, v_snd_4529_);
lean_ctor_set(v_reuseFailAlloc_4558_, 1, v_snd_4539_);
v___x_4554_ = v_reuseFailAlloc_4558_;
goto v_reusejp_4553_;
}
v_reusejp_4553_:
{
lean_object* v___x_4556_; 
if (v_isShared_4552_ == 0)
{
lean_ctor_set(v___x_4551_, 0, v___x_4554_);
v___x_4556_ = v___x_4551_;
goto v_reusejp_4555_;
}
else
{
lean_object* v_reuseFailAlloc_4557_; 
v_reuseFailAlloc_4557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4557_, 0, v___x_4554_);
v___x_4556_ = v_reuseFailAlloc_4557_;
goto v_reusejp_4555_;
}
v_reusejp_4555_:
{
return v___x_4556_;
}
}
}
}
}
}
else
{
lean_object* v_a_4563_; lean_object* v___x_4565_; uint8_t v_isShared_4566_; uint8_t v_isSharedCheck_4570_; 
lean_del_object(v___x_4531_);
lean_dec(v_snd_4529_);
lean_dec(v_fst_4528_);
lean_dec(v_a_4523_);
lean_dec(v_a_4519_);
lean_dec_ref(v_dec_4512_);
lean_dec_ref(v_p_4510_);
lean_dec(v_mvarId_4509_);
v_a_4563_ = lean_ctor_get(v___x_4536_, 0);
v_isSharedCheck_4570_ = !lean_is_exclusive(v___x_4536_);
if (v_isSharedCheck_4570_ == 0)
{
v___x_4565_ = v___x_4536_;
v_isShared_4566_ = v_isSharedCheck_4570_;
goto v_resetjp_4564_;
}
else
{
lean_inc(v_a_4563_);
lean_dec(v___x_4536_);
v___x_4565_ = lean_box(0);
v_isShared_4566_ = v_isSharedCheck_4570_;
goto v_resetjp_4564_;
}
v_resetjp_4564_:
{
lean_object* v___x_4568_; 
if (v_isShared_4566_ == 0)
{
v___x_4568_ = v___x_4565_;
goto v_reusejp_4567_;
}
else
{
lean_object* v_reuseFailAlloc_4569_; 
v_reuseFailAlloc_4569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4569_, 0, v_a_4563_);
v___x_4568_ = v_reuseFailAlloc_4569_;
goto v_reusejp_4567_;
}
v_reusejp_4567_:
{
return v___x_4568_;
}
}
}
}
}
else
{
lean_object* v_a_4572_; lean_object* v___x_4574_; uint8_t v_isShared_4575_; uint8_t v_isSharedCheck_4579_; 
lean_dec(v_a_4523_);
lean_dec(v_a_4521_);
lean_dec(v_a_4519_);
lean_dec_ref(v_dec_4512_);
lean_dec(v_hName_4511_);
lean_dec_ref(v_p_4510_);
lean_dec(v_mvarId_4509_);
v_a_4572_ = lean_ctor_get(v___x_4526_, 0);
v_isSharedCheck_4579_ = !lean_is_exclusive(v___x_4526_);
if (v_isSharedCheck_4579_ == 0)
{
v___x_4574_ = v___x_4526_;
v_isShared_4575_ = v_isSharedCheck_4579_;
goto v_resetjp_4573_;
}
else
{
lean_inc(v_a_4572_);
lean_dec(v___x_4526_);
v___x_4574_ = lean_box(0);
v_isShared_4575_ = v_isSharedCheck_4579_;
goto v_resetjp_4573_;
}
v_resetjp_4573_:
{
lean_object* v___x_4577_; 
if (v_isShared_4575_ == 0)
{
v___x_4577_ = v___x_4574_;
goto v_reusejp_4576_;
}
else
{
lean_object* v_reuseFailAlloc_4578_; 
v_reuseFailAlloc_4578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4578_, 0, v_a_4572_);
v___x_4577_ = v_reuseFailAlloc_4578_;
goto v_reusejp_4576_;
}
v_reusejp_4576_:
{
return v___x_4577_;
}
}
}
}
else
{
lean_object* v_a_4580_; lean_object* v___x_4582_; uint8_t v_isShared_4583_; uint8_t v_isSharedCheck_4587_; 
lean_dec(v_a_4521_);
lean_dec(v_a_4519_);
lean_dec_ref(v_dec_4512_);
lean_dec(v_hName_4511_);
lean_dec_ref(v_p_4510_);
lean_dec(v_mvarId_4509_);
v_a_4580_ = lean_ctor_get(v___x_4522_, 0);
v_isSharedCheck_4587_ = !lean_is_exclusive(v___x_4522_);
if (v_isSharedCheck_4587_ == 0)
{
v___x_4582_ = v___x_4522_;
v_isShared_4583_ = v_isSharedCheck_4587_;
goto v_resetjp_4581_;
}
else
{
lean_inc(v_a_4580_);
lean_dec(v___x_4522_);
v___x_4582_ = lean_box(0);
v_isShared_4583_ = v_isSharedCheck_4587_;
goto v_resetjp_4581_;
}
v_resetjp_4581_:
{
lean_object* v___x_4585_; 
if (v_isShared_4583_ == 0)
{
v___x_4585_ = v___x_4582_;
goto v_reusejp_4584_;
}
else
{
lean_object* v_reuseFailAlloc_4586_; 
v_reuseFailAlloc_4586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4586_, 0, v_a_4580_);
v___x_4585_ = v_reuseFailAlloc_4586_;
goto v_reusejp_4584_;
}
v_reusejp_4584_:
{
return v___x_4585_;
}
}
}
}
else
{
lean_object* v_a_4588_; lean_object* v___x_4590_; uint8_t v_isShared_4591_; uint8_t v_isSharedCheck_4595_; 
lean_dec(v_a_4519_);
lean_dec_ref(v_dec_4512_);
lean_dec(v_hName_4511_);
lean_dec_ref(v_p_4510_);
lean_dec(v_mvarId_4509_);
v_a_4588_ = lean_ctor_get(v___x_4520_, 0);
v_isSharedCheck_4595_ = !lean_is_exclusive(v___x_4520_);
if (v_isSharedCheck_4595_ == 0)
{
v___x_4590_ = v___x_4520_;
v_isShared_4591_ = v_isSharedCheck_4595_;
goto v_resetjp_4589_;
}
else
{
lean_inc(v_a_4588_);
lean_dec(v___x_4520_);
v___x_4590_ = lean_box(0);
v_isShared_4591_ = v_isSharedCheck_4595_;
goto v_resetjp_4589_;
}
v_resetjp_4589_:
{
lean_object* v___x_4593_; 
if (v_isShared_4591_ == 0)
{
v___x_4593_ = v___x_4590_;
goto v_reusejp_4592_;
}
else
{
lean_object* v_reuseFailAlloc_4594_; 
v_reuseFailAlloc_4594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4594_, 0, v_a_4588_);
v___x_4593_ = v_reuseFailAlloc_4594_;
goto v_reusejp_4592_;
}
v_reusejp_4592_:
{
return v___x_4593_;
}
}
}
}
else
{
lean_object* v_a_4596_; lean_object* v___x_4598_; uint8_t v_isShared_4599_; uint8_t v_isSharedCheck_4603_; 
lean_dec_ref(v_dec_4512_);
lean_dec(v_hName_4511_);
lean_dec_ref(v_p_4510_);
lean_dec(v_mvarId_4509_);
v_a_4596_ = lean_ctor_get(v___x_4518_, 0);
v_isSharedCheck_4603_ = !lean_is_exclusive(v___x_4518_);
if (v_isSharedCheck_4603_ == 0)
{
v___x_4598_ = v___x_4518_;
v_isShared_4599_ = v_isSharedCheck_4603_;
goto v_resetjp_4597_;
}
else
{
lean_inc(v_a_4596_);
lean_dec(v___x_4518_);
v___x_4598_ = lean_box(0);
v_isShared_4599_ = v_isSharedCheck_4603_;
goto v_resetjp_4597_;
}
v_resetjp_4597_:
{
lean_object* v___x_4601_; 
if (v_isShared_4599_ == 0)
{
v___x_4601_ = v___x_4598_;
goto v_reusejp_4600_;
}
else
{
lean_object* v_reuseFailAlloc_4602_; 
v_reuseFailAlloc_4602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4602_, 0, v_a_4596_);
v___x_4601_ = v_reuseFailAlloc_4602_;
goto v_reusejp_4600_;
}
v_reusejp_4600_:
{
return v___x_4601_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_byCasesDec___lam__0___boxed(lean_object* v_mvarId_4604_, lean_object* v_p_4605_, lean_object* v_hName_4606_, lean_object* v_dec_4607_, lean_object* v___y_4608_, lean_object* v___y_4609_, lean_object* v___y_4610_, lean_object* v___y_4611_, lean_object* v___y_4612_){
_start:
{
lean_object* v_res_4613_; 
v_res_4613_ = l_Lean_MVarId_byCasesDec___lam__0(v_mvarId_4604_, v_p_4605_, v_hName_4606_, v_dec_4607_, v___y_4608_, v___y_4609_, v___y_4610_, v___y_4611_);
lean_dec(v___y_4611_);
lean_dec_ref(v___y_4610_);
lean_dec(v___y_4609_);
lean_dec_ref(v___y_4608_);
return v_res_4613_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_byCasesDec(lean_object* v_mvarId_4614_, lean_object* v_p_4615_, lean_object* v_dec_4616_, lean_object* v_hName_4617_, lean_object* v_a_4618_, lean_object* v_a_4619_, lean_object* v_a_4620_, lean_object* v_a_4621_){
_start:
{
lean_object* v___f_4623_; lean_object* v___x_4624_; 
lean_inc(v_mvarId_4614_);
v___f_4623_ = lean_alloc_closure((void*)(l_Lean_MVarId_byCasesDec___lam__0___boxed), 9, 4);
lean_closure_set(v___f_4623_, 0, v_mvarId_4614_);
lean_closure_set(v___f_4623_, 1, v_p_4615_);
lean_closure_set(v___f_4623_, 2, v_hName_4617_);
lean_closure_set(v___f_4623_, 3, v_dec_4616_);
v___x_4624_ = l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2___redArg(v_mvarId_4614_, v___f_4623_, v_a_4618_, v_a_4619_, v_a_4620_, v_a_4621_);
return v___x_4624_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_byCasesDec___boxed(lean_object* v_mvarId_4625_, lean_object* v_p_4626_, lean_object* v_dec_4627_, lean_object* v_hName_4628_, lean_object* v_a_4629_, lean_object* v_a_4630_, lean_object* v_a_4631_, lean_object* v_a_4632_, lean_object* v_a_4633_){
_start:
{
lean_object* v_res_4634_; 
v_res_4634_ = l_Lean_MVarId_byCasesDec(v_mvarId_4625_, v_p_4626_, v_dec_4627_, v_hName_4628_, v_a_4629_, v_a_4630_, v_a_4631_, v_a_4632_);
lean_dec(v_a_4632_);
lean_dec_ref(v_a_4631_);
lean_dec(v_a_4630_);
lean_dec_ref(v_a_4629_);
return v_res_4634_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4686_; lean_object* v___x_4687_; lean_object* v___x_4688_; 
v___x_4686_ = lean_unsigned_to_nat(4241171151u);
v___x_4687_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_));
v___x_4688_ = l_Lean_Name_num___override(v___x_4687_, v___x_4686_);
return v___x_4688_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4690_; lean_object* v___x_4691_; lean_object* v___x_4692_; 
v___x_4690_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_));
v___x_4691_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_);
v___x_4692_ = l_Lean_Name_str___override(v___x_4691_, v___x_4690_);
return v___x_4692_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4694_; lean_object* v___x_4695_; lean_object* v___x_4696_; 
v___x_4694_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_));
v___x_4695_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_);
v___x_4696_ = l_Lean_Name_str___override(v___x_4695_, v___x_4694_);
return v___x_4696_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4697_; lean_object* v___x_4698_; lean_object* v___x_4699_; 
v___x_4697_ = lean_unsigned_to_nat(2u);
v___x_4698_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_);
v___x_4699_ = l_Lean_Name_num___override(v___x_4698_, v___x_4697_);
return v___x_4699_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4701_; uint8_t v___x_4702_; lean_object* v___x_4703_; lean_object* v___x_4704_; 
v___x_4701_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_));
v___x_4702_ = 0;
v___x_4703_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_);
v___x_4704_ = l_Lean_registerTraceClass(v___x_4701_, v___x_4702_, v___x_4703_);
return v___x_4704_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2____boxed(lean_object* v_a_4705_){
_start:
{
lean_object* v_res_4706_; 
v_res_4706_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_();
return v_res_4706_;
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
