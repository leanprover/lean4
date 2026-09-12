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
lean_object* v___x_7_; lean_object* v_env_8_; lean_object* v___x_9_; lean_object* v_toCold_10_; lean_object* v_mctx_11_; lean_object* v_lctx_12_; lean_object* v_options_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; 
v___x_7_ = lean_st_ref_get(v___y_5_);
v_env_8_ = lean_ctor_get(v___x_7_, 0);
lean_inc_ref(v_env_8_);
lean_dec(v___x_7_);
v___x_9_ = lean_st_ref_get(v___y_3_);
v_toCold_10_ = lean_ctor_get(v___y_4_, 0);
v_mctx_11_ = lean_ctor_get(v___x_9_, 0);
lean_inc_ref(v_mctx_11_);
lean_dec(v___x_9_);
v_lctx_12_ = lean_ctor_get(v___y_2_, 2);
v_options_13_ = lean_ctor_get(v_toCold_10_, 2);
lean_inc_ref(v_options_13_);
lean_inc_ref(v_lctx_12_);
v___x_14_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_14_, 0, v_env_8_);
lean_ctor_set(v___x_14_, 1, v_mctx_11_);
lean_ctor_set(v___x_14_, 2, v_lctx_12_);
lean_ctor_set(v___x_14_, 3, v_options_13_);
v___x_15_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_15_, 0, v___x_14_);
lean_ctor_set(v___x_15_, 1, v_msgData_1_);
v___x_16_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_16_, 0, v___x_15_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected_spec__0_spec__0___boxed(lean_object* v_msgData_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_, lean_object* v___y_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected_spec__0_spec__0(v_msgData_17_, v___y_18_, v___y_19_, v___y_20_, v___y_21_);
lean_dec(v___y_21_);
lean_dec_ref(v___y_20_);
lean_dec(v___y_19_);
lean_dec_ref(v___y_18_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected_spec__0___redArg(lean_object* v_msg_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_){
_start:
{
lean_object* v_ref_30_; lean_object* v___x_31_; lean_object* v_a_32_; lean_object* v___x_34_; uint8_t v_isShared_35_; uint8_t v_isSharedCheck_40_; 
v_ref_30_ = lean_ctor_get(v___y_27_, 2);
v___x_31_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected_spec__0_spec__0(v_msg_24_, v___y_25_, v___y_26_, v___y_27_, v___y_28_);
v_a_32_ = lean_ctor_get(v___x_31_, 0);
v_isSharedCheck_40_ = !lean_is_exclusive(v___x_31_);
if (v_isSharedCheck_40_ == 0)
{
v___x_34_ = v___x_31_;
v_isShared_35_ = v_isSharedCheck_40_;
goto v_resetjp_33_;
}
else
{
lean_inc(v_a_32_);
lean_dec(v___x_31_);
v___x_34_ = lean_box(0);
v_isShared_35_ = v_isSharedCheck_40_;
goto v_resetjp_33_;
}
v_resetjp_33_:
{
lean_object* v___x_36_; lean_object* v___x_38_; 
lean_inc(v_ref_30_);
v___x_36_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_36_, 0, v_ref_30_);
lean_ctor_set(v___x_36_, 1, v_a_32_);
if (v_isShared_35_ == 0)
{
lean_ctor_set_tag(v___x_34_, 1);
lean_ctor_set(v___x_34_, 0, v___x_36_);
v___x_38_ = v___x_34_;
goto v_reusejp_37_;
}
else
{
lean_object* v_reuseFailAlloc_39_; 
v_reuseFailAlloc_39_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_39_, 0, v___x_36_);
v___x_38_ = v_reuseFailAlloc_39_;
goto v_reusejp_37_;
}
v_reusejp_37_:
{
return v___x_38_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected_spec__0___redArg___boxed(lean_object* v_msg_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_){
_start:
{
lean_object* v_res_47_; 
v_res_47_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected_spec__0___redArg(v_msg_41_, v___y_42_, v___y_43_, v___y_44_, v___y_45_);
lean_dec(v___y_45_);
lean_dec_ref(v___y_44_);
lean_dec(v___y_43_);
lean_dec_ref(v___y_42_);
return v_res_47_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg___closed__1(void){
_start:
{
lean_object* v___x_49_; lean_object* v___x_50_; 
v___x_49_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg___closed__0));
v___x_50_ = l_Lean_stringToMessageData(v___x_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg(lean_object* v_type_51_, lean_object* v_a_52_, lean_object* v_a_53_, lean_object* v_a_54_, lean_object* v_a_55_){
_start:
{
lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_57_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg___closed__1, &l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg___closed__1);
v___x_58_ = l_Lean_indentExpr(v_type_51_);
v___x_59_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_59_, 0, v___x_57_);
lean_ctor_set(v___x_59_, 1, v___x_58_);
v___x_60_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected_spec__0___redArg(v___x_59_, v_a_52_, v_a_53_, v_a_54_, v_a_55_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg___boxed(lean_object* v_type_61_, lean_object* v_a_62_, lean_object* v_a_63_, lean_object* v_a_64_, lean_object* v_a_65_, lean_object* v_a_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg(v_type_61_, v_a_62_, v_a_63_, v_a_64_, v_a_65_);
lean_dec(v_a_65_);
lean_dec_ref(v_a_64_);
lean_dec(v_a_63_);
lean_dec_ref(v_a_62_);
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected(lean_object* v_00_u03b1_68_, lean_object* v_type_69_, lean_object* v_a_70_, lean_object* v_a_71_, lean_object* v_a_72_, lean_object* v_a_73_){
_start:
{
lean_object* v___x_75_; 
v___x_75_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg(v_type_69_, v_a_70_, v_a_71_, v_a_72_, v_a_73_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___boxed(lean_object* v_00_u03b1_76_, lean_object* v_type_77_, lean_object* v_a_78_, lean_object* v_a_79_, lean_object* v_a_80_, lean_object* v_a_81_, lean_object* v_a_82_){
_start:
{
lean_object* v_res_83_; 
v_res_83_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected(v_00_u03b1_76_, v_type_77_, v_a_78_, v_a_79_, v_a_80_, v_a_81_);
lean_dec(v_a_81_);
lean_dec_ref(v_a_80_);
lean_dec(v_a_79_);
lean_dec_ref(v_a_78_);
return v_res_83_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected_spec__0(lean_object* v_00_u03b1_84_, lean_object* v_msg_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_){
_start:
{
lean_object* v___x_91_; 
v___x_91_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected_spec__0___redArg(v_msg_85_, v___y_86_, v___y_87_, v___y_88_, v___y_89_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected_spec__0___boxed(lean_object* v_00_u03b1_92_, lean_object* v_msg_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_){
_start:
{
lean_object* v_res_99_; 
v_res_99_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected_spec__0(v_00_u03b1_92_, v_msg_93_, v___y_94_, v___y_95_, v___y_96_, v___y_97_);
lean_dec(v___y_97_);
lean_dec_ref(v___y_96_);
lean_dec(v___y_95_);
lean_dec_ref(v___y_94_);
return v_res_99_;
}
}
static lean_object* _init_l_Lean_Meta_getInductiveUniverseAndParams___closed__0(void){
_start:
{
lean_object* v___x_100_; lean_object* v_dummy_101_; 
v___x_100_ = lean_box(0);
v_dummy_101_ = l_Lean_Expr_sort___override(v___x_100_);
return v_dummy_101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInductiveUniverseAndParams(lean_object* v_type_102_, lean_object* v_a_103_, lean_object* v_a_104_, lean_object* v_a_105_, lean_object* v_a_106_){
_start:
{
lean_object* v___x_108_; 
v___x_108_ = l_Lean_Meta_whnfD(v_type_102_, v_a_103_, v_a_104_, v_a_105_, v_a_106_);
if (lean_obj_tag(v___x_108_) == 0)
{
lean_object* v_a_109_; lean_object* v___x_111_; uint8_t v_isShared_112_; uint8_t v_isSharedCheck_138_; 
v_a_109_ = lean_ctor_get(v___x_108_, 0);
v_isSharedCheck_138_ = !lean_is_exclusive(v___x_108_);
if (v_isSharedCheck_138_ == 0)
{
v___x_111_ = v___x_108_;
v_isShared_112_ = v_isSharedCheck_138_;
goto v_resetjp_110_;
}
else
{
lean_inc(v_a_109_);
lean_dec(v___x_108_);
v___x_111_ = lean_box(0);
v_isShared_112_ = v_isSharedCheck_138_;
goto v_resetjp_110_;
}
v_resetjp_110_:
{
lean_object* v___x_113_; 
v___x_113_ = l_Lean_Expr_getAppFn(v_a_109_);
if (lean_obj_tag(v___x_113_) == 4)
{
lean_object* v_declName_114_; lean_object* v_us_115_; lean_object* v___x_116_; lean_object* v_env_117_; uint8_t v___x_118_; lean_object* v___x_119_; 
v_declName_114_ = lean_ctor_get(v___x_113_, 0);
lean_inc(v_declName_114_);
v_us_115_ = lean_ctor_get(v___x_113_, 1);
lean_inc(v_us_115_);
lean_dec_ref_known(v___x_113_, 2);
v___x_116_ = lean_st_ref_get(v_a_106_);
v_env_117_ = lean_ctor_get(v___x_116_, 0);
lean_inc_ref(v_env_117_);
lean_dec(v___x_116_);
v___x_118_ = 0;
v___x_119_ = l_Lean_Environment_find_x3f(v_env_117_, v_declName_114_, v___x_118_);
if (lean_obj_tag(v___x_119_) == 0)
{
lean_object* v___x_120_; 
lean_dec(v_us_115_);
lean_del_object(v___x_111_);
v___x_120_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg(v_a_109_, v_a_103_, v_a_104_, v_a_105_, v_a_106_);
return v___x_120_;
}
else
{
lean_object* v_val_121_; 
v_val_121_ = lean_ctor_get(v___x_119_, 0);
lean_inc(v_val_121_);
lean_dec_ref_known(v___x_119_, 1);
if (lean_obj_tag(v_val_121_) == 5)
{
lean_object* v_val_122_; lean_object* v_numParams_123_; lean_object* v_nargs_124_; lean_object* v_dummy_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_134_; 
v_val_122_ = lean_ctor_get(v_val_121_, 0);
lean_inc_ref(v_val_122_);
lean_dec_ref_known(v_val_121_, 1);
v_numParams_123_ = lean_ctor_get(v_val_122_, 1);
lean_inc(v_numParams_123_);
lean_dec_ref(v_val_122_);
v_nargs_124_ = l_Lean_Expr_getAppNumArgs(v_a_109_);
v_dummy_125_ = lean_obj_once(&l_Lean_Meta_getInductiveUniverseAndParams___closed__0, &l_Lean_Meta_getInductiveUniverseAndParams___closed__0_once, _init_l_Lean_Meta_getInductiveUniverseAndParams___closed__0);
lean_inc(v_nargs_124_);
v___x_126_ = lean_mk_array(v_nargs_124_, v_dummy_125_);
v___x_127_ = lean_unsigned_to_nat(1u);
v___x_128_ = lean_nat_sub(v_nargs_124_, v___x_127_);
lean_dec(v_nargs_124_);
v___x_129_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_109_, v___x_126_, v___x_128_);
v___x_130_ = lean_unsigned_to_nat(0u);
v___x_131_ = l_Array_extract___redArg(v___x_129_, v___x_130_, v_numParams_123_);
lean_dec_ref(v___x_129_);
v___x_132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_132_, 0, v_us_115_);
lean_ctor_set(v___x_132_, 1, v___x_131_);
if (v_isShared_112_ == 0)
{
lean_ctor_set(v___x_111_, 0, v___x_132_);
v___x_134_ = v___x_111_;
goto v_reusejp_133_;
}
else
{
lean_object* v_reuseFailAlloc_135_; 
v_reuseFailAlloc_135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_135_, 0, v___x_132_);
v___x_134_ = v_reuseFailAlloc_135_;
goto v_reusejp_133_;
}
v_reusejp_133_:
{
return v___x_134_;
}
}
else
{
lean_object* v___x_136_; 
lean_dec(v_val_121_);
lean_dec(v_us_115_);
lean_del_object(v___x_111_);
v___x_136_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg(v_a_109_, v_a_103_, v_a_104_, v_a_105_, v_a_106_);
return v___x_136_;
}
}
}
else
{
lean_object* v___x_137_; 
lean_dec_ref(v___x_113_);
lean_del_object(v___x_111_);
v___x_137_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___redArg(v_a_109_, v_a_103_, v_a_104_, v_a_105_, v_a_106_);
return v___x_137_;
}
}
}
else
{
lean_object* v_a_139_; lean_object* v___x_141_; uint8_t v_isShared_142_; uint8_t v_isSharedCheck_146_; 
v_a_139_ = lean_ctor_get(v___x_108_, 0);
v_isSharedCheck_146_ = !lean_is_exclusive(v___x_108_);
if (v_isSharedCheck_146_ == 0)
{
v___x_141_ = v___x_108_;
v_isShared_142_ = v_isSharedCheck_146_;
goto v_resetjp_140_;
}
else
{
lean_inc(v_a_139_);
lean_dec(v___x_108_);
v___x_141_ = lean_box(0);
v_isShared_142_ = v_isSharedCheck_146_;
goto v_resetjp_140_;
}
v_resetjp_140_:
{
lean_object* v___x_144_; 
if (v_isShared_142_ == 0)
{
v___x_144_ = v___x_141_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_145_, 0, v_a_139_);
v___x_144_ = v_reuseFailAlloc_145_;
goto v_reusejp_143_;
}
v_reusejp_143_:
{
return v___x_144_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInductiveUniverseAndParams___boxed(lean_object* v_type_147_, lean_object* v_a_148_, lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_){
_start:
{
lean_object* v_res_153_; 
v_res_153_ = l_Lean_Meta_getInductiveUniverseAndParams(v_type_147_, v_a_148_, v_a_149_, v_a_150_, v_a_151_);
lean_dec(v_a_151_);
lean_dec_ref(v_a_150_);
lean_dec(v_a_149_);
lean_dec_ref(v_a_148_);
return v_res_153_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof(lean_object* v_lhs_167_, lean_object* v_rhs_168_, lean_object* v_a_169_, lean_object* v_a_170_, lean_object* v_a_171_, lean_object* v_a_172_){
_start:
{
lean_object* v___x_174_; 
lean_inc(v_a_172_);
lean_inc_ref(v_a_171_);
lean_inc(v_a_170_);
lean_inc_ref(v_a_169_);
lean_inc_ref(v_lhs_167_);
v___x_174_ = lean_infer_type(v_lhs_167_, v_a_169_, v_a_170_, v_a_171_, v_a_172_);
if (lean_obj_tag(v___x_174_) == 0)
{
lean_object* v_a_175_; lean_object* v___x_176_; 
v_a_175_ = lean_ctor_get(v___x_174_, 0);
lean_inc(v_a_175_);
lean_dec_ref_known(v___x_174_, 1);
lean_inc(v_a_172_);
lean_inc_ref(v_a_171_);
lean_inc(v_a_170_);
lean_inc_ref(v_a_169_);
lean_inc_ref(v_rhs_168_);
v___x_176_ = lean_infer_type(v_rhs_168_, v_a_169_, v_a_170_, v_a_171_, v_a_172_);
if (lean_obj_tag(v___x_176_) == 0)
{
lean_object* v_a_177_; lean_object* v___x_178_; 
v_a_177_ = lean_ctor_get(v___x_176_, 0);
lean_inc(v_a_177_);
lean_dec_ref_known(v___x_176_, 1);
lean_inc(v_a_175_);
v___x_178_ = l_Lean_Meta_getLevel(v_a_175_, v_a_169_, v_a_170_, v_a_171_, v_a_172_);
if (lean_obj_tag(v___x_178_) == 0)
{
lean_object* v_a_179_; lean_object* v___x_180_; 
v_a_179_ = lean_ctor_get(v___x_178_, 0);
lean_inc(v_a_179_);
lean_dec_ref_known(v___x_178_, 1);
lean_inc(v_a_177_);
lean_inc(v_a_175_);
v___x_180_ = l_Lean_Meta_isExprDefEq(v_a_175_, v_a_177_, v_a_169_, v_a_170_, v_a_171_, v_a_172_);
if (lean_obj_tag(v___x_180_) == 0)
{
lean_object* v_a_181_; lean_object* v___x_183_; uint8_t v_isShared_184_; uint8_t v_isSharedCheck_210_; 
v_a_181_ = lean_ctor_get(v___x_180_, 0);
v_isSharedCheck_210_ = !lean_is_exclusive(v___x_180_);
if (v_isSharedCheck_210_ == 0)
{
v___x_183_ = v___x_180_;
v_isShared_184_ = v_isSharedCheck_210_;
goto v_resetjp_182_;
}
else
{
lean_inc(v_a_181_);
lean_dec(v___x_180_);
v___x_183_ = lean_box(0);
v_isShared_184_ = v_isSharedCheck_210_;
goto v_resetjp_182_;
}
v_resetjp_182_:
{
uint8_t v___x_185_; 
v___x_185_ = lean_unbox(v_a_181_);
lean_dec(v_a_181_);
if (v___x_185_ == 0)
{
lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_196_; 
v___x_186_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__1));
v___x_187_ = lean_box(0);
v___x_188_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_188_, 0, v_a_179_);
lean_ctor_set(v___x_188_, 1, v___x_187_);
lean_inc_ref(v___x_188_);
v___x_189_ = l_Lean_mkConst(v___x_186_, v___x_188_);
lean_inc_ref(v_lhs_167_);
lean_inc(v_a_175_);
v___x_190_ = l_Lean_mkApp4(v___x_189_, v_a_175_, v_lhs_167_, v_a_177_, v_rhs_168_);
v___x_191_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__3));
v___x_192_ = l_Lean_mkConst(v___x_191_, v___x_188_);
v___x_193_ = l_Lean_mkAppB(v___x_192_, v_a_175_, v_lhs_167_);
v___x_194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_194_, 0, v___x_190_);
lean_ctor_set(v___x_194_, 1, v___x_193_);
if (v_isShared_184_ == 0)
{
lean_ctor_set(v___x_183_, 0, v___x_194_);
v___x_196_ = v___x_183_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_197_; 
v_reuseFailAlloc_197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_197_, 0, v___x_194_);
v___x_196_ = v_reuseFailAlloc_197_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
return v___x_196_;
}
}
else
{
lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_208_; 
lean_dec(v_a_177_);
v___x_198_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__5));
v___x_199_ = lean_box(0);
v___x_200_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_200_, 0, v_a_179_);
lean_ctor_set(v___x_200_, 1, v___x_199_);
lean_inc_ref(v___x_200_);
v___x_201_ = l_Lean_mkConst(v___x_198_, v___x_200_);
lean_inc_ref(v_lhs_167_);
lean_inc(v_a_175_);
v___x_202_ = l_Lean_mkApp3(v___x_201_, v_a_175_, v_lhs_167_, v_rhs_168_);
v___x_203_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__6));
v___x_204_ = l_Lean_mkConst(v___x_203_, v___x_200_);
v___x_205_ = l_Lean_mkAppB(v___x_204_, v_a_175_, v_lhs_167_);
v___x_206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_206_, 0, v___x_202_);
lean_ctor_set(v___x_206_, 1, v___x_205_);
if (v_isShared_184_ == 0)
{
lean_ctor_set(v___x_183_, 0, v___x_206_);
v___x_208_ = v___x_183_;
goto v_reusejp_207_;
}
else
{
lean_object* v_reuseFailAlloc_209_; 
v_reuseFailAlloc_209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_209_, 0, v___x_206_);
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
lean_object* v_a_211_; lean_object* v___x_213_; uint8_t v_isShared_214_; uint8_t v_isSharedCheck_218_; 
lean_dec(v_a_179_);
lean_dec(v_a_177_);
lean_dec(v_a_175_);
lean_dec_ref(v_rhs_168_);
lean_dec_ref(v_lhs_167_);
v_a_211_ = lean_ctor_get(v___x_180_, 0);
v_isSharedCheck_218_ = !lean_is_exclusive(v___x_180_);
if (v_isSharedCheck_218_ == 0)
{
v___x_213_ = v___x_180_;
v_isShared_214_ = v_isSharedCheck_218_;
goto v_resetjp_212_;
}
else
{
lean_inc(v_a_211_);
lean_dec(v___x_180_);
v___x_213_ = lean_box(0);
v_isShared_214_ = v_isSharedCheck_218_;
goto v_resetjp_212_;
}
v_resetjp_212_:
{
lean_object* v___x_216_; 
if (v_isShared_214_ == 0)
{
v___x_216_ = v___x_213_;
goto v_reusejp_215_;
}
else
{
lean_object* v_reuseFailAlloc_217_; 
v_reuseFailAlloc_217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_217_, 0, v_a_211_);
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
lean_dec(v_a_177_);
lean_dec(v_a_175_);
lean_dec_ref(v_rhs_168_);
lean_dec_ref(v_lhs_167_);
v_a_219_ = lean_ctor_get(v___x_178_, 0);
v_isSharedCheck_226_ = !lean_is_exclusive(v___x_178_);
if (v_isSharedCheck_226_ == 0)
{
v___x_221_ = v___x_178_;
v_isShared_222_ = v_isSharedCheck_226_;
goto v_resetjp_220_;
}
else
{
lean_inc(v_a_219_);
lean_dec(v___x_178_);
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
lean_dec(v_a_175_);
lean_dec_ref(v_rhs_168_);
lean_dec_ref(v_lhs_167_);
v_a_227_ = lean_ctor_get(v___x_176_, 0);
v_isSharedCheck_234_ = !lean_is_exclusive(v___x_176_);
if (v_isSharedCheck_234_ == 0)
{
v___x_229_ = v___x_176_;
v_isShared_230_ = v_isSharedCheck_234_;
goto v_resetjp_228_;
}
else
{
lean_inc(v_a_227_);
lean_dec(v___x_176_);
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
lean_dec_ref(v_rhs_168_);
lean_dec_ref(v_lhs_167_);
v_a_235_ = lean_ctor_get(v___x_174_, 0);
v_isSharedCheck_242_ = !lean_is_exclusive(v___x_174_);
if (v_isSharedCheck_242_ == 0)
{
v___x_237_ = v___x_174_;
v_isShared_238_ = v_isSharedCheck_242_;
goto v_resetjp_236_;
}
else
{
lean_inc(v_a_235_);
lean_dec(v___x_174_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___boxed(lean_object* v_lhs_243_, lean_object* v_rhs_244_, lean_object* v_a_245_, lean_object* v_a_246_, lean_object* v_a_247_, lean_object* v_a_248_, lean_object* v_a_249_){
_start:
{
lean_object* v_res_250_; 
v_res_250_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof(v_lhs_243_, v_rhs_244_, v_a_245_, v_a_246_, v_a_247_, v_a_248_);
lean_dec(v_a_248_);
lean_dec_ref(v_a_247_);
lean_dec(v_a_246_);
lean_dec_ref(v_a_245_);
return v_res_250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0_spec__0___redArg___lam__0(lean_object* v_k_251_, lean_object* v_b_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_){
_start:
{
lean_object* v___x_258_; 
lean_inc(v___y_256_);
lean_inc_ref(v___y_255_);
lean_inc(v___y_254_);
lean_inc_ref(v___y_253_);
v___x_258_ = lean_apply_6(v_k_251_, v_b_252_, v___y_253_, v___y_254_, v___y_255_, v___y_256_, lean_box(0));
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_k_259_, lean_object* v_b_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_){
_start:
{
lean_object* v_res_266_; 
v_res_266_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0_spec__0___redArg___lam__0(v_k_259_, v_b_260_, v___y_261_, v___y_262_, v___y_263_, v___y_264_);
lean_dec(v___y_264_);
lean_dec_ref(v___y_263_);
lean_dec(v___y_262_);
lean_dec_ref(v___y_261_);
return v_res_266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0_spec__0___redArg(lean_object* v_name_267_, uint8_t v_bi_268_, lean_object* v_type_269_, lean_object* v_k_270_, uint8_t v_kind_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_){
_start:
{
lean_object* v___f_277_; lean_object* v___x_278_; 
v___f_277_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0_spec__0___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_277_, 0, v_k_270_);
v___x_278_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_267_, v_bi_268_, v_type_269_, v___f_277_, v_kind_271_, v___y_272_, v___y_273_, v___y_274_, v___y_275_);
if (lean_obj_tag(v___x_278_) == 0)
{
lean_object* v_a_279_; lean_object* v___x_281_; uint8_t v_isShared_282_; uint8_t v_isSharedCheck_286_; 
v_a_279_ = lean_ctor_get(v___x_278_, 0);
v_isSharedCheck_286_ = !lean_is_exclusive(v___x_278_);
if (v_isSharedCheck_286_ == 0)
{
v___x_281_ = v___x_278_;
v_isShared_282_ = v_isSharedCheck_286_;
goto v_resetjp_280_;
}
else
{
lean_inc(v_a_279_);
lean_dec(v___x_278_);
v___x_281_ = lean_box(0);
v_isShared_282_ = v_isSharedCheck_286_;
goto v_resetjp_280_;
}
v_resetjp_280_:
{
lean_object* v___x_284_; 
if (v_isShared_282_ == 0)
{
v___x_284_ = v___x_281_;
goto v_reusejp_283_;
}
else
{
lean_object* v_reuseFailAlloc_285_; 
v_reuseFailAlloc_285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_285_, 0, v_a_279_);
v___x_284_ = v_reuseFailAlloc_285_;
goto v_reusejp_283_;
}
v_reusejp_283_:
{
return v___x_284_;
}
}
}
else
{
lean_object* v_a_287_; lean_object* v___x_289_; uint8_t v_isShared_290_; uint8_t v_isSharedCheck_294_; 
v_a_287_ = lean_ctor_get(v___x_278_, 0);
v_isSharedCheck_294_ = !lean_is_exclusive(v___x_278_);
if (v_isSharedCheck_294_ == 0)
{
v___x_289_ = v___x_278_;
v_isShared_290_ = v_isSharedCheck_294_;
goto v_resetjp_288_;
}
else
{
lean_inc(v_a_287_);
lean_dec(v___x_278_);
v___x_289_ = lean_box(0);
v_isShared_290_ = v_isSharedCheck_294_;
goto v_resetjp_288_;
}
v_resetjp_288_:
{
lean_object* v___x_292_; 
if (v_isShared_290_ == 0)
{
v___x_292_ = v___x_289_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v_a_287_);
v___x_292_ = v_reuseFailAlloc_293_;
goto v_reusejp_291_;
}
v_reusejp_291_:
{
return v___x_292_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0_spec__0___redArg___boxed(lean_object* v_name_295_, lean_object* v_bi_296_, lean_object* v_type_297_, lean_object* v_k_298_, lean_object* v_kind_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_){
_start:
{
uint8_t v_bi_boxed_305_; uint8_t v_kind_boxed_306_; lean_object* v_res_307_; 
v_bi_boxed_305_ = lean_unbox(v_bi_296_);
v_kind_boxed_306_ = lean_unbox(v_kind_299_);
v_res_307_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0_spec__0___redArg(v_name_295_, v_bi_boxed_305_, v_type_297_, v_k_298_, v_kind_boxed_306_, v___y_300_, v___y_301_, v___y_302_, v___y_303_);
lean_dec(v___y_303_);
lean_dec_ref(v___y_302_);
lean_dec(v___y_301_);
lean_dec_ref(v___y_300_);
return v_res_307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0___redArg(lean_object* v_name_308_, lean_object* v_type_309_, lean_object* v_k_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_){
_start:
{
uint8_t v___x_316_; uint8_t v___x_317_; lean_object* v___x_318_; 
v___x_316_ = 0;
v___x_317_ = 0;
v___x_318_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0_spec__0___redArg(v_name_308_, v___x_316_, v_type_309_, v_k_310_, v___x_317_, v___y_311_, v___y_312_, v___y_313_, v___y_314_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0___redArg___boxed(lean_object* v_name_319_, lean_object* v_type_320_, lean_object* v_k_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_){
_start:
{
lean_object* v_res_327_; 
v_res_327_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0___redArg(v_name_319_, v_type_320_, v_k_321_, v___y_322_, v___y_323_, v___y_324_, v___y_325_);
lean_dec(v___y_325_);
lean_dec_ref(v___y_324_);
lean_dec(v___y_323_);
lean_dec_ref(v___y_322_);
return v_res_327_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___redArg___lam__0___boxed(lean_object* v_i_328_, lean_object* v_newEqs_329_, lean_object* v_newRefls_330_, lean_object* v_snd_331_, lean_object* v_targets_332_, lean_object* v_targetsNew_333_, lean_object* v_k_334_, lean_object* v_newEq_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___redArg___lam__0(v_i_328_, v_newEqs_329_, v_newRefls_330_, v_snd_331_, v_targets_332_, v_targetsNew_333_, v_k_334_, v_newEq_335_, v___y_336_, v___y_337_, v___y_338_, v___y_339_);
lean_dec(v___y_339_);
lean_dec_ref(v___y_338_);
lean_dec(v___y_337_);
lean_dec_ref(v___y_336_);
lean_dec(v_i_328_);
return v_res_341_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___redArg(lean_object* v_targets_345_, lean_object* v_targetsNew_346_, lean_object* v_k_347_, lean_object* v_i_348_, lean_object* v_newEqs_349_, lean_object* v_newRefls_350_, lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_){
_start:
{
lean_object* v___x_356_; uint8_t v___x_357_; 
v___x_356_ = lean_array_get_size(v_targets_345_);
v___x_357_ = lean_nat_dec_lt(v_i_348_, v___x_356_);
if (v___x_357_ == 0)
{
lean_object* v___x_358_; 
lean_dec(v_i_348_);
lean_dec_ref(v_targetsNew_346_);
lean_dec_ref(v_targets_345_);
lean_inc(v_a_354_);
lean_inc_ref(v_a_353_);
lean_inc(v_a_352_);
lean_inc_ref(v_a_351_);
v___x_358_ = lean_apply_7(v_k_347_, v_newEqs_349_, v_newRefls_350_, v_a_351_, v_a_352_, v_a_353_, v_a_354_, lean_box(0));
return v___x_358_;
}
else
{
lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; 
v___x_359_ = l_Lean_instInhabitedExpr;
v___x_360_ = lean_array_get_borrowed(v___x_359_, v_targets_345_, v_i_348_);
v___x_361_ = lean_array_get_borrowed(v___x_359_, v_targetsNew_346_, v_i_348_);
lean_inc(v___x_361_);
lean_inc(v___x_360_);
v___x_362_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof(v___x_360_, v___x_361_, v_a_351_, v_a_352_, v_a_353_, v_a_354_);
if (lean_obj_tag(v___x_362_) == 0)
{
lean_object* v_a_363_; lean_object* v_fst_364_; lean_object* v_snd_365_; lean_object* v___f_366_; lean_object* v___x_367_; lean_object* v___x_368_; 
v_a_363_ = lean_ctor_get(v___x_362_, 0);
lean_inc(v_a_363_);
lean_dec_ref_known(v___x_362_, 1);
v_fst_364_ = lean_ctor_get(v_a_363_, 0);
lean_inc(v_fst_364_);
v_snd_365_ = lean_ctor_get(v_a_363_, 1);
lean_inc(v_snd_365_);
lean_dec(v_a_363_);
v___f_366_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___redArg___lam__0___boxed), 13, 7);
lean_closure_set(v___f_366_, 0, v_i_348_);
lean_closure_set(v___f_366_, 1, v_newEqs_349_);
lean_closure_set(v___f_366_, 2, v_newRefls_350_);
lean_closure_set(v___f_366_, 3, v_snd_365_);
lean_closure_set(v___f_366_, 4, v_targets_345_);
lean_closure_set(v___f_366_, 5, v_targetsNew_346_);
lean_closure_set(v___f_366_, 6, v_k_347_);
v___x_367_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___redArg___closed__1));
v___x_368_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0___redArg(v___x_367_, v_fst_364_, v___f_366_, v_a_351_, v_a_352_, v_a_353_, v_a_354_);
return v___x_368_;
}
else
{
lean_object* v_a_369_; lean_object* v___x_371_; uint8_t v_isShared_372_; uint8_t v_isSharedCheck_376_; 
lean_dec_ref(v_newRefls_350_);
lean_dec_ref(v_newEqs_349_);
lean_dec(v_i_348_);
lean_dec_ref(v_k_347_);
lean_dec_ref(v_targetsNew_346_);
lean_dec_ref(v_targets_345_);
v_a_369_ = lean_ctor_get(v___x_362_, 0);
v_isSharedCheck_376_ = !lean_is_exclusive(v___x_362_);
if (v_isSharedCheck_376_ == 0)
{
v___x_371_ = v___x_362_;
v_isShared_372_ = v_isSharedCheck_376_;
goto v_resetjp_370_;
}
else
{
lean_inc(v_a_369_);
lean_dec(v___x_362_);
v___x_371_ = lean_box(0);
v_isShared_372_ = v_isSharedCheck_376_;
goto v_resetjp_370_;
}
v_resetjp_370_:
{
lean_object* v___x_374_; 
if (v_isShared_372_ == 0)
{
v___x_374_ = v___x_371_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v_a_369_);
v___x_374_ = v_reuseFailAlloc_375_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
return v___x_374_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___redArg___lam__0(lean_object* v_i_377_, lean_object* v_newEqs_378_, lean_object* v_newRefls_379_, lean_object* v_snd_380_, lean_object* v_targets_381_, lean_object* v_targetsNew_382_, lean_object* v_k_383_, lean_object* v_newEq_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_){
_start:
{
lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_390_ = lean_unsigned_to_nat(1u);
v___x_391_ = lean_nat_add(v_i_377_, v___x_390_);
v___x_392_ = lean_array_push(v_newEqs_378_, v_newEq_384_);
v___x_393_ = lean_array_push(v_newRefls_379_, v_snd_380_);
v___x_394_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___redArg(v_targets_381_, v_targetsNew_382_, v_k_383_, v___x_391_, v___x_392_, v___x_393_, v___y_385_, v___y_386_, v___y_387_, v___y_388_);
return v___x_394_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___redArg___boxed(lean_object* v_targets_395_, lean_object* v_targetsNew_396_, lean_object* v_k_397_, lean_object* v_i_398_, lean_object* v_newEqs_399_, lean_object* v_newRefls_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_){
_start:
{
lean_object* v_res_406_; 
v_res_406_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___redArg(v_targets_395_, v_targetsNew_396_, v_k_397_, v_i_398_, v_newEqs_399_, v_newRefls_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_);
lean_dec(v_a_404_);
lean_dec_ref(v_a_403_);
lean_dec(v_a_402_);
lean_dec_ref(v_a_401_);
return v_res_406_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop(lean_object* v_00_u03b1_407_, lean_object* v_targets_408_, lean_object* v_targetsNew_409_, lean_object* v_k_410_, lean_object* v_i_411_, lean_object* v_newEqs_412_, lean_object* v_newRefls_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_){
_start:
{
lean_object* v___x_419_; 
v___x_419_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___redArg(v_targets_408_, v_targetsNew_409_, v_k_410_, v_i_411_, v_newEqs_412_, v_newRefls_413_, v_a_414_, v_a_415_, v_a_416_, v_a_417_);
return v___x_419_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___boxed(lean_object* v_00_u03b1_420_, lean_object* v_targets_421_, lean_object* v_targetsNew_422_, lean_object* v_k_423_, lean_object* v_i_424_, lean_object* v_newEqs_425_, lean_object* v_newRefls_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_){
_start:
{
lean_object* v_res_432_; 
v_res_432_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop(v_00_u03b1_420_, v_targets_421_, v_targetsNew_422_, v_k_423_, v_i_424_, v_newEqs_425_, v_newRefls_426_, v_a_427_, v_a_428_, v_a_429_, v_a_430_);
lean_dec(v_a_430_);
lean_dec_ref(v_a_429_);
lean_dec(v_a_428_);
lean_dec_ref(v_a_427_);
return v_res_432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0_spec__0(lean_object* v_00_u03b1_433_, lean_object* v_name_434_, uint8_t v_bi_435_, lean_object* v_type_436_, lean_object* v_k_437_, uint8_t v_kind_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_){
_start:
{
lean_object* v___x_444_; 
v___x_444_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0_spec__0___redArg(v_name_434_, v_bi_435_, v_type_436_, v_k_437_, v_kind_438_, v___y_439_, v___y_440_, v___y_441_, v___y_442_);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0_spec__0___boxed(lean_object* v_00_u03b1_445_, lean_object* v_name_446_, lean_object* v_bi_447_, lean_object* v_type_448_, lean_object* v_k_449_, lean_object* v_kind_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_){
_start:
{
uint8_t v_bi_boxed_456_; uint8_t v_kind_boxed_457_; lean_object* v_res_458_; 
v_bi_boxed_456_ = lean_unbox(v_bi_447_);
v_kind_boxed_457_ = lean_unbox(v_kind_450_);
v_res_458_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0_spec__0(v_00_u03b1_445_, v_name_446_, v_bi_boxed_456_, v_type_448_, v_k_449_, v_kind_boxed_457_, v___y_451_, v___y_452_, v___y_453_, v___y_454_);
lean_dec(v___y_454_);
lean_dec_ref(v___y_453_);
lean_dec(v___y_452_);
lean_dec_ref(v___y_451_);
return v_res_458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0(lean_object* v_00_u03b1_459_, lean_object* v_name_460_, lean_object* v_type_461_, lean_object* v_k_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_){
_start:
{
lean_object* v___x_468_; 
v___x_468_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0___redArg(v_name_460_, v_type_461_, v_k_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_);
return v___x_468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0___boxed(lean_object* v_00_u03b1_469_, lean_object* v_name_470_, lean_object* v_type_471_, lean_object* v_k_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_){
_start:
{
lean_object* v_res_478_; 
v_res_478_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0(v_00_u03b1_469_, v_name_470_, v_type_471_, v_k_472_, v___y_473_, v___y_474_, v___y_475_, v___y_476_);
lean_dec(v___y_476_);
lean_dec_ref(v___y_475_);
lean_dec(v___y_474_);
lean_dec_ref(v___y_473_);
return v_res_478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewEqs___redArg(lean_object* v_targets_481_, lean_object* v_targetsNew_482_, lean_object* v_k_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_a_487_){
_start:
{
lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; 
v___x_489_ = lean_unsigned_to_nat(0u);
v___x_490_ = ((lean_object*)(l_Lean_Meta_withNewEqs___redArg___closed__0));
v___x_491_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___redArg(v_targets_481_, v_targetsNew_482_, v_k_483_, v___x_489_, v___x_490_, v___x_490_, v_a_484_, v_a_485_, v_a_486_, v_a_487_);
return v___x_491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewEqs___redArg___boxed(lean_object* v_targets_492_, lean_object* v_targetsNew_493_, lean_object* v_k_494_, lean_object* v_a_495_, lean_object* v_a_496_, lean_object* v_a_497_, lean_object* v_a_498_, lean_object* v_a_499_){
_start:
{
lean_object* v_res_500_; 
v_res_500_ = l_Lean_Meta_withNewEqs___redArg(v_targets_492_, v_targetsNew_493_, v_k_494_, v_a_495_, v_a_496_, v_a_497_, v_a_498_);
lean_dec(v_a_498_);
lean_dec_ref(v_a_497_);
lean_dec(v_a_496_);
lean_dec_ref(v_a_495_);
return v_res_500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewEqs(lean_object* v_00_u03b1_501_, lean_object* v_targets_502_, lean_object* v_targetsNew_503_, lean_object* v_k_504_, lean_object* v_a_505_, lean_object* v_a_506_, lean_object* v_a_507_, lean_object* v_a_508_){
_start:
{
lean_object* v___x_510_; 
v___x_510_ = l_Lean_Meta_withNewEqs___redArg(v_targets_502_, v_targetsNew_503_, v_k_504_, v_a_505_, v_a_506_, v_a_507_, v_a_508_);
return v___x_510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewEqs___boxed(lean_object* v_00_u03b1_511_, lean_object* v_targets_512_, lean_object* v_targetsNew_513_, lean_object* v_k_514_, lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v_a_517_, lean_object* v_a_518_, lean_object* v_a_519_){
_start:
{
lean_object* v_res_520_; 
v_res_520_ = l_Lean_Meta_withNewEqs(v_00_u03b1_511_, v_targets_512_, v_targetsNew_513_, v_k_514_, v_a_515_, v_a_516_, v_a_517_, v_a_518_);
lean_dec(v_a_518_);
lean_dec_ref(v_a_517_);
lean_dec(v_a_516_);
lean_dec_ref(v_a_515_);
return v_res_520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_generalizeTargetsEq_spec__0___redArg___lam__0(lean_object* v_k_521_, lean_object* v_b_522_, lean_object* v_c_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_){
_start:
{
lean_object* v___x_529_; 
lean_inc(v___y_527_);
lean_inc_ref(v___y_526_);
lean_inc(v___y_525_);
lean_inc_ref(v___y_524_);
v___x_529_ = lean_apply_7(v_k_521_, v_b_522_, v_c_523_, v___y_524_, v___y_525_, v___y_526_, v___y_527_, lean_box(0));
return v___x_529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_generalizeTargetsEq_spec__0___redArg___lam__0___boxed(lean_object* v_k_530_, lean_object* v_b_531_, lean_object* v_c_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_){
_start:
{
lean_object* v_res_538_; 
v_res_538_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_generalizeTargetsEq_spec__0___redArg___lam__0(v_k_530_, v_b_531_, v_c_532_, v___y_533_, v___y_534_, v___y_535_, v___y_536_);
lean_dec(v___y_536_);
lean_dec_ref(v___y_535_);
lean_dec(v___y_534_);
lean_dec_ref(v___y_533_);
return v_res_538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_generalizeTargetsEq_spec__0___redArg(lean_object* v_type_539_, lean_object* v_k_540_, uint8_t v_cleanupAnnotations_541_, uint8_t v_whnfType_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_){
_start:
{
lean_object* v___f_548_; lean_object* v___x_549_; 
v___f_548_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_generalizeTargetsEq_spec__0___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_548_, 0, v_k_540_);
v___x_549_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_539_, v___f_548_, v_cleanupAnnotations_541_, v_whnfType_542_, v___y_543_, v___y_544_, v___y_545_, v___y_546_);
if (lean_obj_tag(v___x_549_) == 0)
{
lean_object* v_a_550_; lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_557_; 
v_a_550_ = lean_ctor_get(v___x_549_, 0);
v_isSharedCheck_557_ = !lean_is_exclusive(v___x_549_);
if (v_isSharedCheck_557_ == 0)
{
v___x_552_ = v___x_549_;
v_isShared_553_ = v_isSharedCheck_557_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_a_550_);
lean_dec(v___x_549_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_557_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
lean_object* v___x_555_; 
if (v_isShared_553_ == 0)
{
v___x_555_ = v___x_552_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v_a_550_);
v___x_555_ = v_reuseFailAlloc_556_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
return v___x_555_;
}
}
}
else
{
lean_object* v_a_558_; lean_object* v___x_560_; uint8_t v_isShared_561_; uint8_t v_isSharedCheck_565_; 
v_a_558_ = lean_ctor_get(v___x_549_, 0);
v_isSharedCheck_565_ = !lean_is_exclusive(v___x_549_);
if (v_isSharedCheck_565_ == 0)
{
v___x_560_ = v___x_549_;
v_isShared_561_ = v_isSharedCheck_565_;
goto v_resetjp_559_;
}
else
{
lean_inc(v_a_558_);
lean_dec(v___x_549_);
v___x_560_ = lean_box(0);
v_isShared_561_ = v_isSharedCheck_565_;
goto v_resetjp_559_;
}
v_resetjp_559_:
{
lean_object* v___x_563_; 
if (v_isShared_561_ == 0)
{
v___x_563_ = v___x_560_;
goto v_reusejp_562_;
}
else
{
lean_object* v_reuseFailAlloc_564_; 
v_reuseFailAlloc_564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v_a_558_);
v___x_563_ = v_reuseFailAlloc_564_;
goto v_reusejp_562_;
}
v_reusejp_562_:
{
return v___x_563_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_generalizeTargetsEq_spec__0___redArg___boxed(lean_object* v_type_566_, lean_object* v_k_567_, lean_object* v_cleanupAnnotations_568_, lean_object* v_whnfType_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_575_; uint8_t v_whnfType_boxed_576_; lean_object* v_res_577_; 
v_cleanupAnnotations_boxed_575_ = lean_unbox(v_cleanupAnnotations_568_);
v_whnfType_boxed_576_ = lean_unbox(v_whnfType_569_);
v_res_577_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_generalizeTargetsEq_spec__0___redArg(v_type_566_, v_k_567_, v_cleanupAnnotations_boxed_575_, v_whnfType_boxed_576_, v___y_570_, v___y_571_, v___y_572_, v___y_573_);
lean_dec(v___y_573_);
lean_dec_ref(v___y_572_);
lean_dec(v___y_571_);
lean_dec_ref(v___y_570_);
return v_res_577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_generalizeTargetsEq_spec__0(lean_object* v_00_u03b1_578_, lean_object* v_type_579_, lean_object* v_k_580_, uint8_t v_cleanupAnnotations_581_, uint8_t v_whnfType_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_){
_start:
{
lean_object* v___x_588_; 
v___x_588_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_generalizeTargetsEq_spec__0___redArg(v_type_579_, v_k_580_, v_cleanupAnnotations_581_, v_whnfType_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_);
return v___x_588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_generalizeTargetsEq_spec__0___boxed(lean_object* v_00_u03b1_589_, lean_object* v_type_590_, lean_object* v_k_591_, lean_object* v_cleanupAnnotations_592_, lean_object* v_whnfType_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_599_; uint8_t v_whnfType_boxed_600_; lean_object* v_res_601_; 
v_cleanupAnnotations_boxed_599_ = lean_unbox(v_cleanupAnnotations_592_);
v_whnfType_boxed_600_ = lean_unbox(v_whnfType_593_);
v_res_601_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_generalizeTargetsEq_spec__0(v_00_u03b1_589_, v_type_590_, v_k_591_, v_cleanupAnnotations_boxed_599_, v_whnfType_boxed_600_, v___y_594_, v___y_595_, v___y_596_, v___y_597_);
lean_dec(v___y_597_);
lean_dec_ref(v___y_596_);
lean_dec(v___y_595_);
lean_dec_ref(v___y_594_);
return v_res_601_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2___redArg(lean_object* v_mvarId_602_, lean_object* v_x_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_){
_start:
{
lean_object* v___x_609_; 
v___x_609_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_602_, v_x_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_);
if (lean_obj_tag(v___x_609_) == 0)
{
lean_object* v_a_610_; lean_object* v___x_612_; uint8_t v_isShared_613_; uint8_t v_isSharedCheck_617_; 
v_a_610_ = lean_ctor_get(v___x_609_, 0);
v_isSharedCheck_617_ = !lean_is_exclusive(v___x_609_);
if (v_isSharedCheck_617_ == 0)
{
v___x_612_ = v___x_609_;
v_isShared_613_ = v_isSharedCheck_617_;
goto v_resetjp_611_;
}
else
{
lean_inc(v_a_610_);
lean_dec(v___x_609_);
v___x_612_ = lean_box(0);
v_isShared_613_ = v_isSharedCheck_617_;
goto v_resetjp_611_;
}
v_resetjp_611_:
{
lean_object* v___x_615_; 
if (v_isShared_613_ == 0)
{
v___x_615_ = v___x_612_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v_a_610_);
v___x_615_ = v_reuseFailAlloc_616_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
return v___x_615_;
}
}
}
else
{
lean_object* v_a_618_; lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_625_; 
v_a_618_ = lean_ctor_get(v___x_609_, 0);
v_isSharedCheck_625_ = !lean_is_exclusive(v___x_609_);
if (v_isSharedCheck_625_ == 0)
{
v___x_620_ = v___x_609_;
v_isShared_621_ = v_isSharedCheck_625_;
goto v_resetjp_619_;
}
else
{
lean_inc(v_a_618_);
lean_dec(v___x_609_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_625_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
lean_object* v___x_623_; 
if (v_isShared_621_ == 0)
{
v___x_623_ = v___x_620_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v_a_618_);
v___x_623_ = v_reuseFailAlloc_624_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
return v___x_623_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2___redArg___boxed(lean_object* v_mvarId_626_, lean_object* v_x_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_){
_start:
{
lean_object* v_res_633_; 
v_res_633_ = l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2___redArg(v_mvarId_626_, v_x_627_, v___y_628_, v___y_629_, v___y_630_, v___y_631_);
lean_dec(v___y_631_);
lean_dec_ref(v___y_630_);
lean_dec(v___y_629_);
lean_dec_ref(v___y_628_);
return v_res_633_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2(lean_object* v_00_u03b1_634_, lean_object* v_mvarId_635_, lean_object* v_x_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_){
_start:
{
lean_object* v___x_642_; 
v___x_642_ = l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2___redArg(v_mvarId_635_, v_x_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_);
return v___x_642_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2___boxed(lean_object* v_00_u03b1_643_, lean_object* v_mvarId_644_, lean_object* v_x_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_){
_start:
{
lean_object* v_res_651_; 
v_res_651_ = l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2(v_00_u03b1_643_, v_mvarId_644_, v_x_645_, v___y_646_, v___y_647_, v___y_648_, v___y_649_);
lean_dec(v___y_649_);
lean_dec_ref(v___y_648_);
lean_dec(v___y_647_);
lean_dec_ref(v___y_646_);
return v_res_651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeTargetsEq___lam__0(lean_object* v_mvarId_652_, lean_object* v___x_653_, lean_object* v_eqs_654_, lean_object* v_eqRefls_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_){
_start:
{
lean_object* v___x_661_; 
v___x_661_ = l_Lean_MVarId_getType(v_mvarId_652_, v___y_656_, v___y_657_, v___y_658_, v___y_659_);
if (lean_obj_tag(v___x_661_) == 0)
{
lean_object* v_a_662_; uint8_t v___x_663_; uint8_t v___x_664_; uint8_t v___x_665_; lean_object* v___x_666_; 
v_a_662_ = lean_ctor_get(v___x_661_, 0);
lean_inc(v_a_662_);
lean_dec_ref_known(v___x_661_, 1);
v___x_663_ = 0;
v___x_664_ = 1;
v___x_665_ = 1;
v___x_666_ = l_Lean_Meta_mkForallFVars(v_eqs_654_, v_a_662_, v___x_663_, v___x_664_, v___x_664_, v___x_665_, v___y_656_, v___y_657_, v___y_658_, v___y_659_);
if (lean_obj_tag(v___x_666_) == 0)
{
lean_object* v_a_667_; lean_object* v___x_668_; 
v_a_667_ = lean_ctor_get(v___x_666_, 0);
lean_inc(v_a_667_);
lean_dec_ref_known(v___x_666_, 1);
v___x_668_ = l_Lean_Meta_mkForallFVars(v___x_653_, v_a_667_, v___x_663_, v___x_664_, v___x_664_, v___x_665_, v___y_656_, v___y_657_, v___y_658_, v___y_659_);
if (lean_obj_tag(v___x_668_) == 0)
{
lean_object* v_a_669_; lean_object* v___x_671_; uint8_t v_isShared_672_; uint8_t v_isSharedCheck_677_; 
v_a_669_ = lean_ctor_get(v___x_668_, 0);
v_isSharedCheck_677_ = !lean_is_exclusive(v___x_668_);
if (v_isSharedCheck_677_ == 0)
{
v___x_671_ = v___x_668_;
v_isShared_672_ = v_isSharedCheck_677_;
goto v_resetjp_670_;
}
else
{
lean_inc(v_a_669_);
lean_dec(v___x_668_);
v___x_671_ = lean_box(0);
v_isShared_672_ = v_isSharedCheck_677_;
goto v_resetjp_670_;
}
v_resetjp_670_:
{
lean_object* v___x_673_; lean_object* v___x_675_; 
v___x_673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_673_, 0, v_a_669_);
lean_ctor_set(v___x_673_, 1, v_eqRefls_655_);
if (v_isShared_672_ == 0)
{
lean_ctor_set(v___x_671_, 0, v___x_673_);
v___x_675_ = v___x_671_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v___x_673_);
v___x_675_ = v_reuseFailAlloc_676_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
return v___x_675_;
}
}
}
else
{
lean_object* v_a_678_; lean_object* v___x_680_; uint8_t v_isShared_681_; uint8_t v_isSharedCheck_685_; 
lean_dec_ref(v_eqRefls_655_);
v_a_678_ = lean_ctor_get(v___x_668_, 0);
v_isSharedCheck_685_ = !lean_is_exclusive(v___x_668_);
if (v_isSharedCheck_685_ == 0)
{
v___x_680_ = v___x_668_;
v_isShared_681_ = v_isSharedCheck_685_;
goto v_resetjp_679_;
}
else
{
lean_inc(v_a_678_);
lean_dec(v___x_668_);
v___x_680_ = lean_box(0);
v_isShared_681_ = v_isSharedCheck_685_;
goto v_resetjp_679_;
}
v_resetjp_679_:
{
lean_object* v___x_683_; 
if (v_isShared_681_ == 0)
{
v___x_683_ = v___x_680_;
goto v_reusejp_682_;
}
else
{
lean_object* v_reuseFailAlloc_684_; 
v_reuseFailAlloc_684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_684_, 0, v_a_678_);
v___x_683_ = v_reuseFailAlloc_684_;
goto v_reusejp_682_;
}
v_reusejp_682_:
{
return v___x_683_;
}
}
}
}
else
{
lean_object* v_a_686_; lean_object* v___x_688_; uint8_t v_isShared_689_; uint8_t v_isSharedCheck_693_; 
lean_dec_ref(v_eqRefls_655_);
v_a_686_ = lean_ctor_get(v___x_666_, 0);
v_isSharedCheck_693_ = !lean_is_exclusive(v___x_666_);
if (v_isSharedCheck_693_ == 0)
{
v___x_688_ = v___x_666_;
v_isShared_689_ = v_isSharedCheck_693_;
goto v_resetjp_687_;
}
else
{
lean_inc(v_a_686_);
lean_dec(v___x_666_);
v___x_688_ = lean_box(0);
v_isShared_689_ = v_isSharedCheck_693_;
goto v_resetjp_687_;
}
v_resetjp_687_:
{
lean_object* v___x_691_; 
if (v_isShared_689_ == 0)
{
v___x_691_ = v___x_688_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v_a_686_);
v___x_691_ = v_reuseFailAlloc_692_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
return v___x_691_;
}
}
}
}
else
{
lean_object* v_a_694_; lean_object* v___x_696_; uint8_t v_isShared_697_; uint8_t v_isSharedCheck_701_; 
lean_dec_ref(v_eqRefls_655_);
v_a_694_ = lean_ctor_get(v___x_661_, 0);
v_isSharedCheck_701_ = !lean_is_exclusive(v___x_661_);
if (v_isSharedCheck_701_ == 0)
{
v___x_696_ = v___x_661_;
v_isShared_697_ = v_isSharedCheck_701_;
goto v_resetjp_695_;
}
else
{
lean_inc(v_a_694_);
lean_dec(v___x_661_);
v___x_696_ = lean_box(0);
v_isShared_697_ = v_isSharedCheck_701_;
goto v_resetjp_695_;
}
v_resetjp_695_:
{
lean_object* v___x_699_; 
if (v_isShared_697_ == 0)
{
v___x_699_ = v___x_696_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v_a_694_);
v___x_699_ = v_reuseFailAlloc_700_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
return v___x_699_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeTargetsEq___lam__0___boxed(lean_object* v_mvarId_702_, lean_object* v___x_703_, lean_object* v_eqs_704_, lean_object* v_eqRefls_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l_Lean_Meta_generalizeTargetsEq___lam__0(v_mvarId_702_, v___x_703_, v_eqs_704_, v_eqRefls_705_, v___y_706_, v___y_707_, v___y_708_, v___y_709_);
lean_dec(v___y_709_);
lean_dec_ref(v___y_708_);
lean_dec(v___y_707_);
lean_dec_ref(v___y_706_);
lean_dec_ref(v_eqs_704_);
lean_dec_ref(v___x_703_);
return v_res_711_;
}
}
static lean_object* _init_l_Lean_Meta_generalizeTargetsEq___lam__1___closed__1(void){
_start:
{
lean_object* v___x_713_; lean_object* v___x_714_; 
v___x_713_ = ((lean_object*)(l_Lean_Meta_generalizeTargetsEq___lam__1___closed__0));
v___x_714_ = l_Lean_stringToMessageData(v___x_713_);
return v___x_714_;
}
}
static lean_object* _init_l_Lean_Meta_generalizeTargetsEq___lam__1___closed__3(void){
_start:
{
lean_object* v___x_716_; lean_object* v___x_717_; 
v___x_716_ = ((lean_object*)(l_Lean_Meta_generalizeTargetsEq___lam__1___closed__2));
v___x_717_ = l_Lean_stringToMessageData(v___x_716_);
return v___x_717_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeTargetsEq___lam__1(lean_object* v_targets_718_, lean_object* v_mvarId_719_, lean_object* v_targetsNew_720_, lean_object* v_x_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_){
_start:
{
lean_object* v___x_734_; lean_object* v___x_735_; uint8_t v___x_736_; 
v___x_734_ = lean_array_get_size(v_targets_718_);
v___x_735_ = lean_array_get_size(v_targetsNew_720_);
v___x_736_ = lean_nat_dec_le(v___x_734_, v___x_735_);
if (v___x_736_ == 0)
{
lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v_a_749_; lean_object* v___x_751_; uint8_t v_isShared_752_; uint8_t v_isSharedCheck_756_; 
lean_dec_ref(v_targetsNew_720_);
lean_dec(v_mvarId_719_);
lean_dec_ref(v_targets_718_);
v___x_737_ = lean_obj_once(&l_Lean_Meta_generalizeTargetsEq___lam__1___closed__1, &l_Lean_Meta_generalizeTargetsEq___lam__1___closed__1_once, _init_l_Lean_Meta_generalizeTargetsEq___lam__1___closed__1);
v___x_738_ = l_Nat_reprFast(v___x_734_);
v___x_739_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_739_, 0, v___x_738_);
v___x_740_ = l_Lean_MessageData_ofFormat(v___x_739_);
v___x_741_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_741_, 0, v___x_737_);
lean_ctor_set(v___x_741_, 1, v___x_740_);
v___x_742_ = lean_obj_once(&l_Lean_Meta_generalizeTargetsEq___lam__1___closed__3, &l_Lean_Meta_generalizeTargetsEq___lam__1___closed__3_once, _init_l_Lean_Meta_generalizeTargetsEq___lam__1___closed__3);
v___x_743_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_743_, 0, v___x_741_);
lean_ctor_set(v___x_743_, 1, v___x_742_);
v___x_744_ = l_Nat_reprFast(v___x_735_);
v___x_745_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_745_, 0, v___x_744_);
v___x_746_ = l_Lean_MessageData_ofFormat(v___x_745_);
v___x_747_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_747_, 0, v___x_743_);
lean_ctor_set(v___x_747_, 1, v___x_746_);
v___x_748_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected_spec__0___redArg(v___x_747_, v___y_722_, v___y_723_, v___y_724_, v___y_725_);
v_a_749_ = lean_ctor_get(v___x_748_, 0);
v_isSharedCheck_756_ = !lean_is_exclusive(v___x_748_);
if (v_isSharedCheck_756_ == 0)
{
v___x_751_ = v___x_748_;
v_isShared_752_ = v_isSharedCheck_756_;
goto v_resetjp_750_;
}
else
{
lean_inc(v_a_749_);
lean_dec(v___x_748_);
v___x_751_ = lean_box(0);
v_isShared_752_ = v_isSharedCheck_756_;
goto v_resetjp_750_;
}
v_resetjp_750_:
{
lean_object* v___x_754_; 
if (v_isShared_752_ == 0)
{
v___x_754_ = v___x_751_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v_a_749_);
v___x_754_ = v_reuseFailAlloc_755_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
return v___x_754_;
}
}
}
else
{
goto v___jp_727_;
}
v___jp_727_:
{
lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___f_732_; lean_object* v___x_733_; 
v___x_728_ = lean_array_get_size(v_targets_718_);
v___x_729_ = lean_unsigned_to_nat(0u);
v___x_730_ = l_Array_toSubarray___redArg(v_targetsNew_720_, v___x_729_, v___x_728_);
v___x_731_ = l_Subarray_copy___redArg(v___x_730_);
lean_inc_ref(v___x_731_);
v___f_732_ = lean_alloc_closure((void*)(l_Lean_Meta_generalizeTargetsEq___lam__0___boxed), 9, 2);
lean_closure_set(v___f_732_, 0, v_mvarId_719_);
lean_closure_set(v___f_732_, 1, v___x_731_);
v___x_733_ = l_Lean_Meta_withNewEqs___redArg(v_targets_718_, v___x_731_, v___f_732_, v___y_722_, v___y_723_, v___y_724_, v___y_725_);
return v___x_733_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeTargetsEq___lam__1___boxed(lean_object* v_targets_757_, lean_object* v_mvarId_758_, lean_object* v_targetsNew_759_, lean_object* v_x_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_){
_start:
{
lean_object* v_res_766_; 
v_res_766_ = l_Lean_Meta_generalizeTargetsEq___lam__1(v_targets_757_, v_mvarId_758_, v_targetsNew_759_, v_x_760_, v___y_761_, v___y_762_, v___y_763_, v___y_764_);
lean_dec(v___y_764_);
lean_dec_ref(v___y_763_);
lean_dec(v___y_762_);
lean_dec_ref(v___y_761_);
lean_dec_ref(v_x_760_);
return v_res_766_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__4_spec__5___redArg(lean_object* v_x_767_, lean_object* v_x_768_, lean_object* v_x_769_, lean_object* v_x_770_){
_start:
{
lean_object* v_ks_771_; lean_object* v_vs_772_; lean_object* v___x_774_; uint8_t v_isShared_775_; uint8_t v_isSharedCheck_796_; 
v_ks_771_ = lean_ctor_get(v_x_767_, 0);
v_vs_772_ = lean_ctor_get(v_x_767_, 1);
v_isSharedCheck_796_ = !lean_is_exclusive(v_x_767_);
if (v_isSharedCheck_796_ == 0)
{
v___x_774_ = v_x_767_;
v_isShared_775_ = v_isSharedCheck_796_;
goto v_resetjp_773_;
}
else
{
lean_inc(v_vs_772_);
lean_inc(v_ks_771_);
lean_dec(v_x_767_);
v___x_774_ = lean_box(0);
v_isShared_775_ = v_isSharedCheck_796_;
goto v_resetjp_773_;
}
v_resetjp_773_:
{
lean_object* v___x_776_; uint8_t v___x_777_; 
v___x_776_ = lean_array_get_size(v_ks_771_);
v___x_777_ = lean_nat_dec_lt(v_x_768_, v___x_776_);
if (v___x_777_ == 0)
{
lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_781_; 
lean_dec(v_x_768_);
v___x_778_ = lean_array_push(v_ks_771_, v_x_769_);
v___x_779_ = lean_array_push(v_vs_772_, v_x_770_);
if (v_isShared_775_ == 0)
{
lean_ctor_set(v___x_774_, 1, v___x_779_);
lean_ctor_set(v___x_774_, 0, v___x_778_);
v___x_781_ = v___x_774_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v___x_778_);
lean_ctor_set(v_reuseFailAlloc_782_, 1, v___x_779_);
v___x_781_ = v_reuseFailAlloc_782_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
return v___x_781_;
}
}
else
{
lean_object* v_k_x27_783_; uint8_t v___x_784_; 
v_k_x27_783_ = lean_array_fget_borrowed(v_ks_771_, v_x_768_);
v___x_784_ = l_Lean_instBEqMVarId_beq(v_x_769_, v_k_x27_783_);
if (v___x_784_ == 0)
{
lean_object* v___x_786_; 
if (v_isShared_775_ == 0)
{
v___x_786_ = v___x_774_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v_ks_771_);
lean_ctor_set(v_reuseFailAlloc_790_, 1, v_vs_772_);
v___x_786_ = v_reuseFailAlloc_790_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
lean_object* v___x_787_; lean_object* v___x_788_; 
v___x_787_ = lean_unsigned_to_nat(1u);
v___x_788_ = lean_nat_add(v_x_768_, v___x_787_);
lean_dec(v_x_768_);
v_x_767_ = v___x_786_;
v_x_768_ = v___x_788_;
goto _start;
}
}
else
{
lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_794_; 
v___x_791_ = lean_array_fset(v_ks_771_, v_x_768_, v_x_769_);
v___x_792_ = lean_array_fset(v_vs_772_, v_x_768_, v_x_770_);
lean_dec(v_x_768_);
if (v_isShared_775_ == 0)
{
lean_ctor_set(v___x_774_, 1, v___x_792_);
lean_ctor_set(v___x_774_, 0, v___x_791_);
v___x_794_ = v___x_774_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v___x_791_);
lean_ctor_set(v_reuseFailAlloc_795_, 1, v___x_792_);
v___x_794_ = v_reuseFailAlloc_795_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
return v___x_794_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__4___redArg(lean_object* v_n_797_, lean_object* v_k_798_, lean_object* v_v_799_){
_start:
{
lean_object* v___x_800_; lean_object* v___x_801_; 
v___x_800_ = lean_unsigned_to_nat(0u);
v___x_801_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__4_spec__5___redArg(v_n_797_, v___x_800_, v_k_798_, v_v_799_);
return v___x_801_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_802_; 
v___x_802_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_802_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg(lean_object* v_x_803_, size_t v_x_804_, size_t v_x_805_, lean_object* v_x_806_, lean_object* v_x_807_){
_start:
{
if (lean_obj_tag(v_x_803_) == 0)
{
lean_object* v_es_808_; size_t v___x_809_; size_t v___x_810_; lean_object* v_j_811_; lean_object* v___x_812_; uint8_t v___x_813_; 
v_es_808_ = lean_ctor_get(v_x_803_, 0);
v___x_809_ = ((size_t)31ULL);
v___x_810_ = lean_usize_land(v_x_804_, v___x_809_);
v_j_811_ = lean_usize_to_nat(v___x_810_);
v___x_812_ = lean_array_get_size(v_es_808_);
v___x_813_ = lean_nat_dec_lt(v_j_811_, v___x_812_);
if (v___x_813_ == 0)
{
lean_dec(v_j_811_);
lean_dec(v_x_807_);
lean_dec(v_x_806_);
return v_x_803_;
}
else
{
lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_852_; 
lean_inc_ref(v_es_808_);
v_isSharedCheck_852_ = !lean_is_exclusive(v_x_803_);
if (v_isSharedCheck_852_ == 0)
{
lean_object* v_unused_853_; 
v_unused_853_ = lean_ctor_get(v_x_803_, 0);
lean_dec(v_unused_853_);
v___x_815_ = v_x_803_;
v_isShared_816_ = v_isSharedCheck_852_;
goto v_resetjp_814_;
}
else
{
lean_dec(v_x_803_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_852_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
lean_object* v_v_817_; lean_object* v___x_818_; lean_object* v_xs_x27_819_; lean_object* v___y_821_; 
v_v_817_ = lean_array_fget(v_es_808_, v_j_811_);
v___x_818_ = lean_box(0);
v_xs_x27_819_ = lean_array_fset(v_es_808_, v_j_811_, v___x_818_);
switch(lean_obj_tag(v_v_817_))
{
case 0:
{
lean_object* v_key_826_; lean_object* v_val_827_; lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_837_; 
v_key_826_ = lean_ctor_get(v_v_817_, 0);
v_val_827_ = lean_ctor_get(v_v_817_, 1);
v_isSharedCheck_837_ = !lean_is_exclusive(v_v_817_);
if (v_isSharedCheck_837_ == 0)
{
v___x_829_ = v_v_817_;
v_isShared_830_ = v_isSharedCheck_837_;
goto v_resetjp_828_;
}
else
{
lean_inc(v_val_827_);
lean_inc(v_key_826_);
lean_dec(v_v_817_);
v___x_829_ = lean_box(0);
v_isShared_830_ = v_isSharedCheck_837_;
goto v_resetjp_828_;
}
v_resetjp_828_:
{
uint8_t v___x_831_; 
v___x_831_ = l_Lean_instBEqMVarId_beq(v_x_806_, v_key_826_);
if (v___x_831_ == 0)
{
lean_object* v___x_832_; lean_object* v___x_833_; 
lean_del_object(v___x_829_);
v___x_832_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_826_, v_val_827_, v_x_806_, v_x_807_);
v___x_833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_833_, 0, v___x_832_);
v___y_821_ = v___x_833_;
goto v___jp_820_;
}
else
{
lean_object* v___x_835_; 
lean_dec(v_val_827_);
lean_dec(v_key_826_);
if (v_isShared_830_ == 0)
{
lean_ctor_set(v___x_829_, 1, v_x_807_);
lean_ctor_set(v___x_829_, 0, v_x_806_);
v___x_835_ = v___x_829_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v_x_806_);
lean_ctor_set(v_reuseFailAlloc_836_, 1, v_x_807_);
v___x_835_ = v_reuseFailAlloc_836_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
v___y_821_ = v___x_835_;
goto v___jp_820_;
}
}
}
}
case 1:
{
lean_object* v_node_838_; lean_object* v___x_840_; uint8_t v_isShared_841_; uint8_t v_isSharedCheck_850_; 
v_node_838_ = lean_ctor_get(v_v_817_, 0);
v_isSharedCheck_850_ = !lean_is_exclusive(v_v_817_);
if (v_isSharedCheck_850_ == 0)
{
v___x_840_ = v_v_817_;
v_isShared_841_ = v_isSharedCheck_850_;
goto v_resetjp_839_;
}
else
{
lean_inc(v_node_838_);
lean_dec(v_v_817_);
v___x_840_ = lean_box(0);
v_isShared_841_ = v_isSharedCheck_850_;
goto v_resetjp_839_;
}
v_resetjp_839_:
{
size_t v___x_842_; size_t v___x_843_; size_t v___x_844_; size_t v___x_845_; lean_object* v___x_846_; lean_object* v___x_848_; 
v___x_842_ = ((size_t)5ULL);
v___x_843_ = lean_usize_shift_right(v_x_804_, v___x_842_);
v___x_844_ = ((size_t)1ULL);
v___x_845_ = lean_usize_add(v_x_805_, v___x_844_);
v___x_846_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg(v_node_838_, v___x_843_, v___x_845_, v_x_806_, v_x_807_);
if (v_isShared_841_ == 0)
{
lean_ctor_set(v___x_840_, 0, v___x_846_);
v___x_848_ = v___x_840_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v___x_846_);
v___x_848_ = v_reuseFailAlloc_849_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
v___y_821_ = v___x_848_;
goto v___jp_820_;
}
}
}
default: 
{
lean_object* v___x_851_; 
v___x_851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_851_, 0, v_x_806_);
lean_ctor_set(v___x_851_, 1, v_x_807_);
v___y_821_ = v___x_851_;
goto v___jp_820_;
}
}
v___jp_820_:
{
lean_object* v___x_822_; lean_object* v___x_824_; 
v___x_822_ = lean_array_fset(v_xs_x27_819_, v_j_811_, v___y_821_);
lean_dec(v_j_811_);
if (v_isShared_816_ == 0)
{
lean_ctor_set(v___x_815_, 0, v___x_822_);
v___x_824_ = v___x_815_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v___x_822_);
v___x_824_ = v_reuseFailAlloc_825_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
return v___x_824_;
}
}
}
}
}
else
{
lean_object* v_ks_854_; lean_object* v_vs_855_; lean_object* v___x_857_; uint8_t v_isShared_858_; uint8_t v_isSharedCheck_873_; 
v_ks_854_ = lean_ctor_get(v_x_803_, 0);
v_vs_855_ = lean_ctor_get(v_x_803_, 1);
v_isSharedCheck_873_ = !lean_is_exclusive(v_x_803_);
if (v_isSharedCheck_873_ == 0)
{
v___x_857_ = v_x_803_;
v_isShared_858_ = v_isSharedCheck_873_;
goto v_resetjp_856_;
}
else
{
lean_inc(v_vs_855_);
lean_inc(v_ks_854_);
lean_dec(v_x_803_);
v___x_857_ = lean_box(0);
v_isShared_858_ = v_isSharedCheck_873_;
goto v_resetjp_856_;
}
v_resetjp_856_:
{
lean_object* v___x_860_; 
if (v_isShared_858_ == 0)
{
v___x_860_ = v___x_857_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v_ks_854_);
lean_ctor_set(v_reuseFailAlloc_872_, 1, v_vs_855_);
v___x_860_ = v_reuseFailAlloc_872_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
lean_object* v_newNode_861_; size_t v___x_862_; uint8_t v___x_863_; 
v_newNode_861_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__4___redArg(v___x_860_, v_x_806_, v_x_807_);
v___x_862_ = ((size_t)7ULL);
v___x_863_ = lean_usize_dec_le(v___x_862_, v_x_805_);
if (v___x_863_ == 0)
{
lean_object* v___x_864_; lean_object* v___x_865_; uint8_t v___x_866_; 
v___x_864_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_861_);
v___x_865_ = lean_unsigned_to_nat(4u);
v___x_866_ = lean_nat_dec_lt(v___x_864_, v___x_865_);
lean_dec(v___x_864_);
if (v___x_866_ == 0)
{
lean_object* v_ks_867_; lean_object* v_vs_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; 
v_ks_867_ = lean_ctor_get(v_newNode_861_, 0);
lean_inc_ref(v_ks_867_);
v_vs_868_ = lean_ctor_get(v_newNode_861_, 1);
lean_inc_ref(v_vs_868_);
lean_dec_ref(v_newNode_861_);
v___x_869_ = lean_unsigned_to_nat(0u);
v___x_870_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg___closed__0);
v___x_871_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__5___redArg(v_x_805_, v_ks_867_, v_vs_868_, v___x_869_, v___x_870_);
lean_dec_ref(v_vs_868_);
lean_dec_ref(v_ks_867_);
return v___x_871_;
}
else
{
return v_newNode_861_;
}
}
else
{
return v_newNode_861_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__5___redArg(size_t v_depth_874_, lean_object* v_keys_875_, lean_object* v_vals_876_, lean_object* v_i_877_, lean_object* v_entries_878_){
_start:
{
lean_object* v___x_879_; uint8_t v___x_880_; 
v___x_879_ = lean_array_get_size(v_keys_875_);
v___x_880_ = lean_nat_dec_lt(v_i_877_, v___x_879_);
if (v___x_880_ == 0)
{
lean_dec(v_i_877_);
return v_entries_878_;
}
else
{
lean_object* v_k_881_; lean_object* v_v_882_; uint64_t v___x_883_; size_t v_h_884_; size_t v___x_885_; lean_object* v___x_886_; size_t v___x_887_; size_t v___x_888_; size_t v___x_889_; size_t v_h_890_; lean_object* v___x_891_; lean_object* v___x_892_; 
v_k_881_ = lean_array_fget_borrowed(v_keys_875_, v_i_877_);
v_v_882_ = lean_array_fget_borrowed(v_vals_876_, v_i_877_);
v___x_883_ = l_Lean_instHashableMVarId_hash(v_k_881_);
v_h_884_ = lean_uint64_to_usize(v___x_883_);
v___x_885_ = ((size_t)5ULL);
v___x_886_ = lean_unsigned_to_nat(1u);
v___x_887_ = ((size_t)1ULL);
v___x_888_ = lean_usize_sub(v_depth_874_, v___x_887_);
v___x_889_ = lean_usize_mul(v___x_885_, v___x_888_);
v_h_890_ = lean_usize_shift_right(v_h_884_, v___x_889_);
v___x_891_ = lean_nat_add(v_i_877_, v___x_886_);
lean_dec(v_i_877_);
lean_inc(v_v_882_);
lean_inc(v_k_881_);
v___x_892_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg(v_entries_878_, v_h_890_, v_depth_874_, v_k_881_, v_v_882_);
v_i_877_ = v___x_891_;
v_entries_878_ = v___x_892_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__5___redArg___boxed(lean_object* v_depth_894_, lean_object* v_keys_895_, lean_object* v_vals_896_, lean_object* v_i_897_, lean_object* v_entries_898_){
_start:
{
size_t v_depth_boxed_899_; lean_object* v_res_900_; 
v_depth_boxed_899_ = lean_unbox_usize(v_depth_894_);
lean_dec(v_depth_894_);
v_res_900_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__5___redArg(v_depth_boxed_899_, v_keys_895_, v_vals_896_, v_i_897_, v_entries_898_);
lean_dec_ref(v_vals_896_);
lean_dec_ref(v_keys_895_);
return v_res_900_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_x_901_, lean_object* v_x_902_, lean_object* v_x_903_, lean_object* v_x_904_, lean_object* v_x_905_){
_start:
{
size_t v_x_2554__boxed_906_; size_t v_x_2555__boxed_907_; lean_object* v_res_908_; 
v_x_2554__boxed_906_ = lean_unbox_usize(v_x_902_);
lean_dec(v_x_902_);
v_x_2555__boxed_907_ = lean_unbox_usize(v_x_903_);
lean_dec(v_x_903_);
v_res_908_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg(v_x_901_, v_x_2554__boxed_906_, v_x_2555__boxed_907_, v_x_904_, v_x_905_);
return v_res_908_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1___redArg(lean_object* v_x_909_, lean_object* v_x_910_, lean_object* v_x_911_){
_start:
{
uint64_t v___x_912_; size_t v___x_913_; size_t v___x_914_; lean_object* v___x_915_; 
v___x_912_ = l_Lean_instHashableMVarId_hash(v_x_910_);
v___x_913_ = lean_uint64_to_usize(v___x_912_);
v___x_914_ = ((size_t)1ULL);
v___x_915_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg(v_x_909_, v___x_913_, v___x_914_, v_x_910_, v_x_911_);
return v___x_915_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1___redArg(lean_object* v_mvarId_916_, lean_object* v_val_917_, lean_object* v___y_918_){
_start:
{
lean_object* v___x_920_; lean_object* v_mctx_921_; lean_object* v_cache_922_; lean_object* v_zetaDeltaFVarIds_923_; lean_object* v_postponed_924_; lean_object* v_diag_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_954_; 
v___x_920_ = lean_st_ref_take(v___y_918_);
v_mctx_921_ = lean_ctor_get(v___x_920_, 0);
v_cache_922_ = lean_ctor_get(v___x_920_, 1);
v_zetaDeltaFVarIds_923_ = lean_ctor_get(v___x_920_, 2);
v_postponed_924_ = lean_ctor_get(v___x_920_, 3);
v_diag_925_ = lean_ctor_get(v___x_920_, 4);
v_isSharedCheck_954_ = !lean_is_exclusive(v___x_920_);
if (v_isSharedCheck_954_ == 0)
{
v___x_927_ = v___x_920_;
v_isShared_928_ = v_isSharedCheck_954_;
goto v_resetjp_926_;
}
else
{
lean_inc(v_diag_925_);
lean_inc(v_postponed_924_);
lean_inc(v_zetaDeltaFVarIds_923_);
lean_inc(v_cache_922_);
lean_inc(v_mctx_921_);
lean_dec(v___x_920_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_954_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
lean_object* v_depth_929_; lean_object* v_levelAssignDepth_930_; lean_object* v_lmvarCounter_931_; lean_object* v_mvarCounter_932_; lean_object* v_lDecls_933_; lean_object* v_decls_934_; lean_object* v_userNames_935_; lean_object* v_lAssignment_936_; lean_object* v_eAssignment_937_; lean_object* v_dAssignment_938_; lean_object* v_instanceTypedMVars_939_; lean_object* v___x_941_; uint8_t v_isShared_942_; uint8_t v_isSharedCheck_953_; 
v_depth_929_ = lean_ctor_get(v_mctx_921_, 0);
v_levelAssignDepth_930_ = lean_ctor_get(v_mctx_921_, 1);
v_lmvarCounter_931_ = lean_ctor_get(v_mctx_921_, 2);
v_mvarCounter_932_ = lean_ctor_get(v_mctx_921_, 3);
v_lDecls_933_ = lean_ctor_get(v_mctx_921_, 4);
v_decls_934_ = lean_ctor_get(v_mctx_921_, 5);
v_userNames_935_ = lean_ctor_get(v_mctx_921_, 6);
v_lAssignment_936_ = lean_ctor_get(v_mctx_921_, 7);
v_eAssignment_937_ = lean_ctor_get(v_mctx_921_, 8);
v_dAssignment_938_ = lean_ctor_get(v_mctx_921_, 9);
v_instanceTypedMVars_939_ = lean_ctor_get(v_mctx_921_, 10);
v_isSharedCheck_953_ = !lean_is_exclusive(v_mctx_921_);
if (v_isSharedCheck_953_ == 0)
{
v___x_941_ = v_mctx_921_;
v_isShared_942_ = v_isSharedCheck_953_;
goto v_resetjp_940_;
}
else
{
lean_inc(v_instanceTypedMVars_939_);
lean_inc(v_dAssignment_938_);
lean_inc(v_eAssignment_937_);
lean_inc(v_lAssignment_936_);
lean_inc(v_userNames_935_);
lean_inc(v_decls_934_);
lean_inc(v_lDecls_933_);
lean_inc(v_mvarCounter_932_);
lean_inc(v_lmvarCounter_931_);
lean_inc(v_levelAssignDepth_930_);
lean_inc(v_depth_929_);
lean_dec(v_mctx_921_);
v___x_941_ = lean_box(0);
v_isShared_942_ = v_isSharedCheck_953_;
goto v_resetjp_940_;
}
v_resetjp_940_:
{
lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_946_; 
v___x_943_ = lean_box(0);
v___x_944_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1___redArg(v_eAssignment_937_, v_mvarId_916_, v_val_917_);
if (v_isShared_942_ == 0)
{
lean_ctor_set(v___x_941_, 8, v___x_944_);
v___x_946_ = v___x_941_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v_depth_929_);
lean_ctor_set(v_reuseFailAlloc_952_, 1, v_levelAssignDepth_930_);
lean_ctor_set(v_reuseFailAlloc_952_, 2, v_lmvarCounter_931_);
lean_ctor_set(v_reuseFailAlloc_952_, 3, v_mvarCounter_932_);
lean_ctor_set(v_reuseFailAlloc_952_, 4, v_lDecls_933_);
lean_ctor_set(v_reuseFailAlloc_952_, 5, v_decls_934_);
lean_ctor_set(v_reuseFailAlloc_952_, 6, v_userNames_935_);
lean_ctor_set(v_reuseFailAlloc_952_, 7, v_lAssignment_936_);
lean_ctor_set(v_reuseFailAlloc_952_, 8, v___x_944_);
lean_ctor_set(v_reuseFailAlloc_952_, 9, v_dAssignment_938_);
lean_ctor_set(v_reuseFailAlloc_952_, 10, v_instanceTypedMVars_939_);
v___x_946_ = v_reuseFailAlloc_952_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
lean_object* v___x_948_; 
if (v_isShared_928_ == 0)
{
lean_ctor_set(v___x_927_, 0, v___x_946_);
v___x_948_ = v___x_927_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v___x_946_);
lean_ctor_set(v_reuseFailAlloc_951_, 1, v_cache_922_);
lean_ctor_set(v_reuseFailAlloc_951_, 2, v_zetaDeltaFVarIds_923_);
lean_ctor_set(v_reuseFailAlloc_951_, 3, v_postponed_924_);
lean_ctor_set(v_reuseFailAlloc_951_, 4, v_diag_925_);
v___x_948_ = v_reuseFailAlloc_951_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
lean_object* v___x_949_; lean_object* v___x_950_; 
v___x_949_ = lean_st_ref_put(v___y_918_, v___x_948_);
v___x_950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_950_, 0, v___x_943_);
return v___x_950_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1___redArg___boxed(lean_object* v_mvarId_955_, lean_object* v_val_956_, lean_object* v___y_957_, lean_object* v___y_958_){
_start:
{
lean_object* v_res_959_; 
v_res_959_ = l_Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1___redArg(v_mvarId_955_, v_val_956_, v___y_957_);
lean_dec(v___y_957_);
return v_res_959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeTargetsEq___lam__2(lean_object* v_mvarId_960_, lean_object* v___x_961_, lean_object* v_motiveType_962_, lean_object* v___f_963_, lean_object* v_targets_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_){
_start:
{
lean_object* v___x_970_; 
lean_inc(v_mvarId_960_);
v___x_970_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_960_, v___x_961_, v___y_965_, v___y_966_, v___y_967_, v___y_968_);
if (lean_obj_tag(v___x_970_) == 0)
{
uint8_t v___x_971_; lean_object* v___x_972_; 
lean_dec_ref_known(v___x_970_, 1);
v___x_971_ = 0;
v___x_972_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_generalizeTargetsEq_spec__0___redArg(v_motiveType_962_, v___f_963_, v___x_971_, v___x_971_, v___y_965_, v___y_966_, v___y_967_, v___y_968_);
if (lean_obj_tag(v___x_972_) == 0)
{
lean_object* v_a_973_; lean_object* v_fst_974_; lean_object* v_snd_975_; lean_object* v___x_976_; 
v_a_973_ = lean_ctor_get(v___x_972_, 0);
lean_inc(v_a_973_);
lean_dec_ref_known(v___x_972_, 1);
v_fst_974_ = lean_ctor_get(v_a_973_, 0);
lean_inc(v_fst_974_);
v_snd_975_ = lean_ctor_get(v_a_973_, 1);
lean_inc(v_snd_975_);
lean_dec(v_a_973_);
lean_inc(v_mvarId_960_);
v___x_976_ = l_Lean_MVarId_getTag(v_mvarId_960_, v___y_965_, v___y_966_, v___y_967_, v___y_968_);
if (lean_obj_tag(v___x_976_) == 0)
{
lean_object* v_a_977_; lean_object* v___x_978_; 
v_a_977_ = lean_ctor_get(v___x_976_, 0);
lean_inc(v_a_977_);
lean_dec_ref_known(v___x_976_, 1);
v___x_978_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_fst_974_, v_a_977_, v___y_965_, v___y_966_, v___y_967_, v___y_968_);
if (lean_obj_tag(v___x_978_) == 0)
{
lean_object* v_a_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_984_; uint8_t v_isShared_985_; uint8_t v_isSharedCheck_990_; 
v_a_979_ = lean_ctor_get(v___x_978_, 0);
lean_inc_n(v_a_979_, 2);
lean_dec_ref_known(v___x_978_, 1);
v___x_980_ = l_Lean_mkAppN(v_a_979_, v_targets_964_);
v___x_981_ = l_Lean_mkAppN(v___x_980_, v_snd_975_);
lean_dec(v_snd_975_);
v___x_982_ = l_Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1___redArg(v_mvarId_960_, v___x_981_, v___y_966_);
v_isSharedCheck_990_ = !lean_is_exclusive(v___x_982_);
if (v_isSharedCheck_990_ == 0)
{
lean_object* v_unused_991_; 
v_unused_991_ = lean_ctor_get(v___x_982_, 0);
lean_dec(v_unused_991_);
v___x_984_ = v___x_982_;
v_isShared_985_ = v_isSharedCheck_990_;
goto v_resetjp_983_;
}
else
{
lean_dec(v___x_982_);
v___x_984_ = lean_box(0);
v_isShared_985_ = v_isSharedCheck_990_;
goto v_resetjp_983_;
}
v_resetjp_983_:
{
lean_object* v___x_986_; lean_object* v___x_988_; 
v___x_986_ = l_Lean_Expr_mvarId_x21(v_a_979_);
lean_dec(v_a_979_);
if (v_isShared_985_ == 0)
{
lean_ctor_set(v___x_984_, 0, v___x_986_);
v___x_988_ = v___x_984_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v___x_986_);
v___x_988_ = v_reuseFailAlloc_989_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
return v___x_988_;
}
}
}
else
{
lean_object* v_a_992_; lean_object* v___x_994_; uint8_t v_isShared_995_; uint8_t v_isSharedCheck_999_; 
lean_dec(v_snd_975_);
lean_dec(v_mvarId_960_);
v_a_992_ = lean_ctor_get(v___x_978_, 0);
v_isSharedCheck_999_ = !lean_is_exclusive(v___x_978_);
if (v_isSharedCheck_999_ == 0)
{
v___x_994_ = v___x_978_;
v_isShared_995_ = v_isSharedCheck_999_;
goto v_resetjp_993_;
}
else
{
lean_inc(v_a_992_);
lean_dec(v___x_978_);
v___x_994_ = lean_box(0);
v_isShared_995_ = v_isSharedCheck_999_;
goto v_resetjp_993_;
}
v_resetjp_993_:
{
lean_object* v___x_997_; 
if (v_isShared_995_ == 0)
{
v___x_997_ = v___x_994_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v_a_992_);
v___x_997_ = v_reuseFailAlloc_998_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
return v___x_997_;
}
}
}
}
else
{
lean_object* v_a_1000_; lean_object* v___x_1002_; uint8_t v_isShared_1003_; uint8_t v_isSharedCheck_1007_; 
lean_dec(v_snd_975_);
lean_dec(v_fst_974_);
lean_dec(v_mvarId_960_);
v_a_1000_ = lean_ctor_get(v___x_976_, 0);
v_isSharedCheck_1007_ = !lean_is_exclusive(v___x_976_);
if (v_isSharedCheck_1007_ == 0)
{
v___x_1002_ = v___x_976_;
v_isShared_1003_ = v_isSharedCheck_1007_;
goto v_resetjp_1001_;
}
else
{
lean_inc(v_a_1000_);
lean_dec(v___x_976_);
v___x_1002_ = lean_box(0);
v_isShared_1003_ = v_isSharedCheck_1007_;
goto v_resetjp_1001_;
}
v_resetjp_1001_:
{
lean_object* v___x_1005_; 
if (v_isShared_1003_ == 0)
{
v___x_1005_ = v___x_1002_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1006_; 
v_reuseFailAlloc_1006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1006_, 0, v_a_1000_);
v___x_1005_ = v_reuseFailAlloc_1006_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
return v___x_1005_;
}
}
}
}
else
{
lean_object* v_a_1008_; lean_object* v___x_1010_; uint8_t v_isShared_1011_; uint8_t v_isSharedCheck_1015_; 
lean_dec(v_mvarId_960_);
v_a_1008_ = lean_ctor_get(v___x_972_, 0);
v_isSharedCheck_1015_ = !lean_is_exclusive(v___x_972_);
if (v_isSharedCheck_1015_ == 0)
{
v___x_1010_ = v___x_972_;
v_isShared_1011_ = v_isSharedCheck_1015_;
goto v_resetjp_1009_;
}
else
{
lean_inc(v_a_1008_);
lean_dec(v___x_972_);
v___x_1010_ = lean_box(0);
v_isShared_1011_ = v_isSharedCheck_1015_;
goto v_resetjp_1009_;
}
v_resetjp_1009_:
{
lean_object* v___x_1013_; 
if (v_isShared_1011_ == 0)
{
v___x_1013_ = v___x_1010_;
goto v_reusejp_1012_;
}
else
{
lean_object* v_reuseFailAlloc_1014_; 
v_reuseFailAlloc_1014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1014_, 0, v_a_1008_);
v___x_1013_ = v_reuseFailAlloc_1014_;
goto v_reusejp_1012_;
}
v_reusejp_1012_:
{
return v___x_1013_;
}
}
}
}
else
{
lean_object* v_a_1016_; lean_object* v___x_1018_; uint8_t v_isShared_1019_; uint8_t v_isSharedCheck_1023_; 
lean_dec_ref(v___f_963_);
lean_dec_ref(v_motiveType_962_);
lean_dec(v_mvarId_960_);
v_a_1016_ = lean_ctor_get(v___x_970_, 0);
v_isSharedCheck_1023_ = !lean_is_exclusive(v___x_970_);
if (v_isSharedCheck_1023_ == 0)
{
v___x_1018_ = v___x_970_;
v_isShared_1019_ = v_isSharedCheck_1023_;
goto v_resetjp_1017_;
}
else
{
lean_inc(v_a_1016_);
lean_dec(v___x_970_);
v___x_1018_ = lean_box(0);
v_isShared_1019_ = v_isSharedCheck_1023_;
goto v_resetjp_1017_;
}
v_resetjp_1017_:
{
lean_object* v___x_1021_; 
if (v_isShared_1019_ == 0)
{
v___x_1021_ = v___x_1018_;
goto v_reusejp_1020_;
}
else
{
lean_object* v_reuseFailAlloc_1022_; 
v_reuseFailAlloc_1022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1022_, 0, v_a_1016_);
v___x_1021_ = v_reuseFailAlloc_1022_;
goto v_reusejp_1020_;
}
v_reusejp_1020_:
{
return v___x_1021_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeTargetsEq___lam__2___boxed(lean_object* v_mvarId_1024_, lean_object* v___x_1025_, lean_object* v_motiveType_1026_, lean_object* v___f_1027_, lean_object* v_targets_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_){
_start:
{
lean_object* v_res_1034_; 
v_res_1034_ = l_Lean_Meta_generalizeTargetsEq___lam__2(v_mvarId_1024_, v___x_1025_, v_motiveType_1026_, v___f_1027_, v_targets_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_);
lean_dec(v___y_1032_);
lean_dec_ref(v___y_1031_);
lean_dec(v___y_1030_);
lean_dec_ref(v___y_1029_);
lean_dec_ref(v_targets_1028_);
return v_res_1034_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeTargetsEq(lean_object* v_mvarId_1038_, lean_object* v_motiveType_1039_, lean_object* v_targets_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_){
_start:
{
lean_object* v___f_1046_; lean_object* v___x_1047_; lean_object* v___f_1048_; lean_object* v___x_1049_; 
lean_inc_n(v_mvarId_1038_, 2);
lean_inc_ref(v_targets_1040_);
v___f_1046_ = lean_alloc_closure((void*)(l_Lean_Meta_generalizeTargetsEq___lam__1___boxed), 9, 2);
lean_closure_set(v___f_1046_, 0, v_targets_1040_);
lean_closure_set(v___f_1046_, 1, v_mvarId_1038_);
v___x_1047_ = ((lean_object*)(l_Lean_Meta_generalizeTargetsEq___closed__1));
v___f_1048_ = lean_alloc_closure((void*)(l_Lean_Meta_generalizeTargetsEq___lam__2___boxed), 10, 5);
lean_closure_set(v___f_1048_, 0, v_mvarId_1038_);
lean_closure_set(v___f_1048_, 1, v___x_1047_);
lean_closure_set(v___f_1048_, 2, v_motiveType_1039_);
lean_closure_set(v___f_1048_, 3, v___f_1046_);
lean_closure_set(v___f_1048_, 4, v_targets_1040_);
v___x_1049_ = l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2___redArg(v_mvarId_1038_, v___f_1048_, v_a_1041_, v_a_1042_, v_a_1043_, v_a_1044_);
return v___x_1049_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeTargetsEq___boxed(lean_object* v_mvarId_1050_, lean_object* v_motiveType_1051_, lean_object* v_targets_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_){
_start:
{
lean_object* v_res_1058_; 
v_res_1058_ = l_Lean_Meta_generalizeTargetsEq(v_mvarId_1050_, v_motiveType_1051_, v_targets_1052_, v_a_1053_, v_a_1054_, v_a_1055_, v_a_1056_);
lean_dec(v_a_1056_);
lean_dec_ref(v_a_1055_);
lean_dec(v_a_1054_);
lean_dec_ref(v_a_1053_);
return v_res_1058_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1(lean_object* v_mvarId_1059_, lean_object* v_val_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_){
_start:
{
lean_object* v___x_1066_; 
v___x_1066_ = l_Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1___redArg(v_mvarId_1059_, v_val_1060_, v___y_1062_);
return v___x_1066_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1___boxed(lean_object* v_mvarId_1067_, lean_object* v_val_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_){
_start:
{
lean_object* v_res_1074_; 
v_res_1074_ = l_Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1(v_mvarId_1067_, v_val_1068_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_);
lean_dec(v___y_1072_);
lean_dec_ref(v___y_1071_);
lean_dec(v___y_1070_);
lean_dec_ref(v___y_1069_);
return v_res_1074_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1(lean_object* v_00_u03b2_1075_, lean_object* v_x_1076_, lean_object* v_x_1077_, lean_object* v_x_1078_){
_start:
{
lean_object* v___x_1079_; 
v___x_1079_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1___redArg(v_x_1076_, v_x_1077_, v_x_1078_);
return v___x_1079_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3(lean_object* v_00_u03b2_1080_, lean_object* v_x_1081_, size_t v_x_1082_, size_t v_x_1083_, lean_object* v_x_1084_, lean_object* v_x_1085_){
_start:
{
lean_object* v___x_1086_; 
v___x_1086_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg(v_x_1081_, v_x_1082_, v_x_1083_, v_x_1084_, v_x_1085_);
return v___x_1086_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1087_, lean_object* v_x_1088_, lean_object* v_x_1089_, lean_object* v_x_1090_, lean_object* v_x_1091_, lean_object* v_x_1092_){
_start:
{
size_t v_x_2941__boxed_1093_; size_t v_x_2942__boxed_1094_; lean_object* v_res_1095_; 
v_x_2941__boxed_1093_ = lean_unbox_usize(v_x_1089_);
lean_dec(v_x_1089_);
v_x_2942__boxed_1094_ = lean_unbox_usize(v_x_1090_);
lean_dec(v_x_1090_);
v_res_1095_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3(v_00_u03b2_1087_, v_x_1088_, v_x_2941__boxed_1093_, v_x_2942__boxed_1094_, v_x_1091_, v_x_1092_);
return v_res_1095_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_1096_, lean_object* v_n_1097_, lean_object* v_k_1098_, lean_object* v_v_1099_){
_start:
{
lean_object* v___x_1100_; 
v___x_1100_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__4___redArg(v_n_1097_, v_k_1098_, v_v_1099_);
return v___x_1100_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__5(lean_object* v_00_u03b2_1101_, size_t v_depth_1102_, lean_object* v_keys_1103_, lean_object* v_vals_1104_, lean_object* v_heq_1105_, lean_object* v_i_1106_, lean_object* v_entries_1107_){
_start:
{
lean_object* v___x_1108_; 
v___x_1108_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__5___redArg(v_depth_1102_, v_keys_1103_, v_vals_1104_, v_i_1106_, v_entries_1107_);
return v___x_1108_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__5___boxed(lean_object* v_00_u03b2_1109_, lean_object* v_depth_1110_, lean_object* v_keys_1111_, lean_object* v_vals_1112_, lean_object* v_heq_1113_, lean_object* v_i_1114_, lean_object* v_entries_1115_){
_start:
{
size_t v_depth_boxed_1116_; lean_object* v_res_1117_; 
v_depth_boxed_1116_ = lean_unbox_usize(v_depth_1110_);
lean_dec(v_depth_1110_);
v_res_1117_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__5(v_00_u03b2_1109_, v_depth_boxed_1116_, v_keys_1111_, v_vals_1112_, v_heq_1113_, v_i_1114_, v_entries_1115_);
lean_dec_ref(v_vals_1112_);
lean_dec_ref(v_keys_1111_);
return v_res_1117_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_1118_, lean_object* v_x_1119_, lean_object* v_x_1120_, lean_object* v_x_1121_, lean_object* v_x_1122_){
_start:
{
lean_object* v___x_1123_; 
v___x_1123_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__4_spec__5___redArg(v_x_1119_, v_x_1120_, v_x_1121_, v_x_1122_);
return v___x_1123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__0(lean_object* v_newEqs_1124_, lean_object* v_mvarId_1125_, uint8_t v___x_1126_, lean_object* v_h_x27_1127_, lean_object* v_newIndices_1128_, lean_object* v___x_1129_, lean_object* v___x_1130_, lean_object* v___x_1131_, lean_object* v___x_1132_, lean_object* v_e_1133_, lean_object* v___x_1134_, lean_object* v_newEq_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_){
_start:
{
lean_object* v___x_1141_; lean_object* v___x_1142_; 
v___x_1141_ = lean_array_push(v_newEqs_1124_, v_newEq_1135_);
lean_inc(v_mvarId_1125_);
v___x_1142_ = l_Lean_MVarId_getType(v_mvarId_1125_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_);
if (lean_obj_tag(v___x_1142_) == 0)
{
lean_object* v_a_1143_; lean_object* v___x_1144_; 
v_a_1143_ = lean_ctor_get(v___x_1142_, 0);
lean_inc(v_a_1143_);
lean_dec_ref_known(v___x_1142_, 1);
lean_inc(v_mvarId_1125_);
v___x_1144_ = l_Lean_MVarId_getTag(v_mvarId_1125_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_);
if (lean_obj_tag(v___x_1144_) == 0)
{
lean_object* v_a_1145_; uint8_t v___x_1146_; uint8_t v___x_1147_; lean_object* v___x_1148_; 
v_a_1145_ = lean_ctor_get(v___x_1144_, 0);
lean_inc(v_a_1145_);
lean_dec_ref_known(v___x_1144_, 1);
v___x_1146_ = 1;
v___x_1147_ = 1;
v___x_1148_ = l_Lean_Meta_mkForallFVars(v___x_1141_, v_a_1143_, v___x_1126_, v___x_1146_, v___x_1146_, v___x_1147_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_);
if (lean_obj_tag(v___x_1148_) == 0)
{
lean_object* v_a_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; 
v_a_1149_ = lean_ctor_get(v___x_1148_, 0);
lean_inc(v_a_1149_);
lean_dec_ref_known(v___x_1148_, 1);
v___x_1150_ = lean_unsigned_to_nat(1u);
v___x_1151_ = lean_mk_empty_array_with_capacity(v___x_1150_);
v___x_1152_ = lean_array_push(v___x_1151_, v_h_x27_1127_);
v___x_1153_ = l_Lean_Meta_mkForallFVars(v___x_1152_, v_a_1149_, v___x_1126_, v___x_1146_, v___x_1146_, v___x_1147_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_);
lean_dec_ref(v___x_1152_);
if (lean_obj_tag(v___x_1153_) == 0)
{
lean_object* v_a_1154_; lean_object* v___x_1155_; 
v_a_1154_ = lean_ctor_get(v___x_1153_, 0);
lean_inc(v_a_1154_);
lean_dec_ref_known(v___x_1153_, 1);
v___x_1155_ = l_Lean_Meta_mkForallFVars(v_newIndices_1128_, v_a_1154_, v___x_1126_, v___x_1146_, v___x_1146_, v___x_1147_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_);
if (lean_obj_tag(v___x_1155_) == 0)
{
lean_object* v_a_1156_; uint8_t v___x_1157_; lean_object* v___x_1158_; 
v_a_1156_ = lean_ctor_get(v___x_1155_, 0);
lean_inc(v_a_1156_);
lean_dec_ref_known(v___x_1155_, 1);
v___x_1157_ = 2;
v___x_1158_ = l_Lean_Meta_mkFreshExprMVarAt(v___x_1129_, v___x_1130_, v_a_1156_, v___x_1157_, v_a_1145_, v___x_1131_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_);
if (lean_obj_tag(v___x_1158_) == 0)
{
lean_object* v_a_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; 
v_a_1159_ = lean_ctor_get(v___x_1158_, 0);
lean_inc_n(v_a_1159_, 2);
lean_dec_ref_known(v___x_1158_, 1);
v___x_1160_ = l_Lean_mkAppN(v_a_1159_, v___x_1132_);
v___x_1161_ = l_Lean_Expr_app___override(v___x_1160_, v_e_1133_);
v___x_1162_ = l_Lean_mkAppN(v___x_1161_, v___x_1134_);
v___x_1163_ = l_Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1___redArg(v_mvarId_1125_, v___x_1162_, v___y_1137_);
lean_dec_ref(v___x_1163_);
v___x_1164_ = l_Lean_Expr_mvarId_x21(v_a_1159_);
lean_dec(v_a_1159_);
v___x_1165_ = lean_array_get_size(v_newIndices_1128_);
v___x_1166_ = lean_box(0);
v___x_1167_ = l_Lean_Meta_introNCore(v___x_1164_, v___x_1165_, v___x_1166_, v___x_1126_, v___x_1146_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_);
if (lean_obj_tag(v___x_1167_) == 0)
{
lean_object* v_a_1168_; lean_object* v_fst_1169_; lean_object* v_snd_1170_; lean_object* v___x_1171_; 
v_a_1168_ = lean_ctor_get(v___x_1167_, 0);
lean_inc(v_a_1168_);
lean_dec_ref_known(v___x_1167_, 1);
v_fst_1169_ = lean_ctor_get(v_a_1168_, 0);
lean_inc(v_fst_1169_);
v_snd_1170_ = lean_ctor_get(v_a_1168_, 1);
lean_inc(v_snd_1170_);
lean_dec(v_a_1168_);
v___x_1171_ = l_Lean_Meta_intro1Core(v_snd_1170_, v___x_1146_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_);
if (lean_obj_tag(v___x_1171_) == 0)
{
lean_object* v_a_1172_; lean_object* v___x_1174_; uint8_t v_isShared_1175_; uint8_t v_isSharedCheck_1183_; 
v_a_1172_ = lean_ctor_get(v___x_1171_, 0);
v_isSharedCheck_1183_ = !lean_is_exclusive(v___x_1171_);
if (v_isSharedCheck_1183_ == 0)
{
v___x_1174_ = v___x_1171_;
v_isShared_1175_ = v_isSharedCheck_1183_;
goto v_resetjp_1173_;
}
else
{
lean_inc(v_a_1172_);
lean_dec(v___x_1171_);
v___x_1174_ = lean_box(0);
v_isShared_1175_ = v_isSharedCheck_1183_;
goto v_resetjp_1173_;
}
v_resetjp_1173_:
{
lean_object* v_fst_1176_; lean_object* v_snd_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1181_; 
v_fst_1176_ = lean_ctor_get(v_a_1172_, 0);
lean_inc(v_fst_1176_);
v_snd_1177_ = lean_ctor_get(v_a_1172_, 1);
lean_inc(v_snd_1177_);
lean_dec(v_a_1172_);
v___x_1178_ = lean_array_get_size(v___x_1141_);
lean_dec_ref(v___x_1141_);
v___x_1179_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1179_, 0, v_snd_1177_);
lean_ctor_set(v___x_1179_, 1, v_fst_1169_);
lean_ctor_set(v___x_1179_, 2, v_fst_1176_);
lean_ctor_set(v___x_1179_, 3, v___x_1178_);
if (v_isShared_1175_ == 0)
{
lean_ctor_set(v___x_1174_, 0, v___x_1179_);
v___x_1181_ = v___x_1174_;
goto v_reusejp_1180_;
}
else
{
lean_object* v_reuseFailAlloc_1182_; 
v_reuseFailAlloc_1182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1182_, 0, v___x_1179_);
v___x_1181_ = v_reuseFailAlloc_1182_;
goto v_reusejp_1180_;
}
v_reusejp_1180_:
{
return v___x_1181_;
}
}
}
else
{
lean_object* v_a_1184_; lean_object* v___x_1186_; uint8_t v_isShared_1187_; uint8_t v_isSharedCheck_1191_; 
lean_dec(v_fst_1169_);
lean_dec_ref(v___x_1141_);
v_a_1184_ = lean_ctor_get(v___x_1171_, 0);
v_isSharedCheck_1191_ = !lean_is_exclusive(v___x_1171_);
if (v_isSharedCheck_1191_ == 0)
{
v___x_1186_ = v___x_1171_;
v_isShared_1187_ = v_isSharedCheck_1191_;
goto v_resetjp_1185_;
}
else
{
lean_inc(v_a_1184_);
lean_dec(v___x_1171_);
v___x_1186_ = lean_box(0);
v_isShared_1187_ = v_isSharedCheck_1191_;
goto v_resetjp_1185_;
}
v_resetjp_1185_:
{
lean_object* v___x_1189_; 
if (v_isShared_1187_ == 0)
{
v___x_1189_ = v___x_1186_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v_a_1184_);
v___x_1189_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
return v___x_1189_;
}
}
}
}
else
{
lean_object* v_a_1192_; lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1199_; 
lean_dec_ref(v___x_1141_);
v_a_1192_ = lean_ctor_get(v___x_1167_, 0);
v_isSharedCheck_1199_ = !lean_is_exclusive(v___x_1167_);
if (v_isSharedCheck_1199_ == 0)
{
v___x_1194_ = v___x_1167_;
v_isShared_1195_ = v_isSharedCheck_1199_;
goto v_resetjp_1193_;
}
else
{
lean_inc(v_a_1192_);
lean_dec(v___x_1167_);
v___x_1194_ = lean_box(0);
v_isShared_1195_ = v_isSharedCheck_1199_;
goto v_resetjp_1193_;
}
v_resetjp_1193_:
{
lean_object* v___x_1197_; 
if (v_isShared_1195_ == 0)
{
v___x_1197_ = v___x_1194_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v_a_1192_);
v___x_1197_ = v_reuseFailAlloc_1198_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
return v___x_1197_;
}
}
}
}
else
{
lean_object* v_a_1200_; lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1207_; 
lean_dec_ref(v___x_1141_);
lean_dec_ref(v_e_1133_);
lean_dec(v_mvarId_1125_);
v_a_1200_ = lean_ctor_get(v___x_1158_, 0);
v_isSharedCheck_1207_ = !lean_is_exclusive(v___x_1158_);
if (v_isSharedCheck_1207_ == 0)
{
v___x_1202_ = v___x_1158_;
v_isShared_1203_ = v_isSharedCheck_1207_;
goto v_resetjp_1201_;
}
else
{
lean_inc(v_a_1200_);
lean_dec(v___x_1158_);
v___x_1202_ = lean_box(0);
v_isShared_1203_ = v_isSharedCheck_1207_;
goto v_resetjp_1201_;
}
v_resetjp_1201_:
{
lean_object* v___x_1205_; 
if (v_isShared_1203_ == 0)
{
v___x_1205_ = v___x_1202_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v_a_1200_);
v___x_1205_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
return v___x_1205_;
}
}
}
}
else
{
lean_object* v_a_1208_; lean_object* v___x_1210_; uint8_t v_isShared_1211_; uint8_t v_isSharedCheck_1215_; 
lean_dec(v_a_1145_);
lean_dec_ref(v___x_1141_);
lean_dec_ref(v_e_1133_);
lean_dec(v___x_1131_);
lean_dec_ref(v___x_1130_);
lean_dec_ref(v___x_1129_);
lean_dec(v_mvarId_1125_);
v_a_1208_ = lean_ctor_get(v___x_1155_, 0);
v_isSharedCheck_1215_ = !lean_is_exclusive(v___x_1155_);
if (v_isSharedCheck_1215_ == 0)
{
v___x_1210_ = v___x_1155_;
v_isShared_1211_ = v_isSharedCheck_1215_;
goto v_resetjp_1209_;
}
else
{
lean_inc(v_a_1208_);
lean_dec(v___x_1155_);
v___x_1210_ = lean_box(0);
v_isShared_1211_ = v_isSharedCheck_1215_;
goto v_resetjp_1209_;
}
v_resetjp_1209_:
{
lean_object* v___x_1213_; 
if (v_isShared_1211_ == 0)
{
v___x_1213_ = v___x_1210_;
goto v_reusejp_1212_;
}
else
{
lean_object* v_reuseFailAlloc_1214_; 
v_reuseFailAlloc_1214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1214_, 0, v_a_1208_);
v___x_1213_ = v_reuseFailAlloc_1214_;
goto v_reusejp_1212_;
}
v_reusejp_1212_:
{
return v___x_1213_;
}
}
}
}
else
{
lean_object* v_a_1216_; lean_object* v___x_1218_; uint8_t v_isShared_1219_; uint8_t v_isSharedCheck_1223_; 
lean_dec(v_a_1145_);
lean_dec_ref(v___x_1141_);
lean_dec_ref(v_e_1133_);
lean_dec(v___x_1131_);
lean_dec_ref(v___x_1130_);
lean_dec_ref(v___x_1129_);
lean_dec(v_mvarId_1125_);
v_a_1216_ = lean_ctor_get(v___x_1153_, 0);
v_isSharedCheck_1223_ = !lean_is_exclusive(v___x_1153_);
if (v_isSharedCheck_1223_ == 0)
{
v___x_1218_ = v___x_1153_;
v_isShared_1219_ = v_isSharedCheck_1223_;
goto v_resetjp_1217_;
}
else
{
lean_inc(v_a_1216_);
lean_dec(v___x_1153_);
v___x_1218_ = lean_box(0);
v_isShared_1219_ = v_isSharedCheck_1223_;
goto v_resetjp_1217_;
}
v_resetjp_1217_:
{
lean_object* v___x_1221_; 
if (v_isShared_1219_ == 0)
{
v___x_1221_ = v___x_1218_;
goto v_reusejp_1220_;
}
else
{
lean_object* v_reuseFailAlloc_1222_; 
v_reuseFailAlloc_1222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1222_, 0, v_a_1216_);
v___x_1221_ = v_reuseFailAlloc_1222_;
goto v_reusejp_1220_;
}
v_reusejp_1220_:
{
return v___x_1221_;
}
}
}
}
else
{
lean_object* v_a_1224_; lean_object* v___x_1226_; uint8_t v_isShared_1227_; uint8_t v_isSharedCheck_1231_; 
lean_dec(v_a_1145_);
lean_dec_ref(v___x_1141_);
lean_dec_ref(v_e_1133_);
lean_dec(v___x_1131_);
lean_dec_ref(v___x_1130_);
lean_dec_ref(v___x_1129_);
lean_dec_ref(v_h_x27_1127_);
lean_dec(v_mvarId_1125_);
v_a_1224_ = lean_ctor_get(v___x_1148_, 0);
v_isSharedCheck_1231_ = !lean_is_exclusive(v___x_1148_);
if (v_isSharedCheck_1231_ == 0)
{
v___x_1226_ = v___x_1148_;
v_isShared_1227_ = v_isSharedCheck_1231_;
goto v_resetjp_1225_;
}
else
{
lean_inc(v_a_1224_);
lean_dec(v___x_1148_);
v___x_1226_ = lean_box(0);
v_isShared_1227_ = v_isSharedCheck_1231_;
goto v_resetjp_1225_;
}
v_resetjp_1225_:
{
lean_object* v___x_1229_; 
if (v_isShared_1227_ == 0)
{
v___x_1229_ = v___x_1226_;
goto v_reusejp_1228_;
}
else
{
lean_object* v_reuseFailAlloc_1230_; 
v_reuseFailAlloc_1230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1230_, 0, v_a_1224_);
v___x_1229_ = v_reuseFailAlloc_1230_;
goto v_reusejp_1228_;
}
v_reusejp_1228_:
{
return v___x_1229_;
}
}
}
}
else
{
lean_object* v_a_1232_; lean_object* v___x_1234_; uint8_t v_isShared_1235_; uint8_t v_isSharedCheck_1239_; 
lean_dec(v_a_1143_);
lean_dec_ref(v___x_1141_);
lean_dec_ref(v_e_1133_);
lean_dec(v___x_1131_);
lean_dec_ref(v___x_1130_);
lean_dec_ref(v___x_1129_);
lean_dec_ref(v_h_x27_1127_);
lean_dec(v_mvarId_1125_);
v_a_1232_ = lean_ctor_get(v___x_1144_, 0);
v_isSharedCheck_1239_ = !lean_is_exclusive(v___x_1144_);
if (v_isSharedCheck_1239_ == 0)
{
v___x_1234_ = v___x_1144_;
v_isShared_1235_ = v_isSharedCheck_1239_;
goto v_resetjp_1233_;
}
else
{
lean_inc(v_a_1232_);
lean_dec(v___x_1144_);
v___x_1234_ = lean_box(0);
v_isShared_1235_ = v_isSharedCheck_1239_;
goto v_resetjp_1233_;
}
v_resetjp_1233_:
{
lean_object* v___x_1237_; 
if (v_isShared_1235_ == 0)
{
v___x_1237_ = v___x_1234_;
goto v_reusejp_1236_;
}
else
{
lean_object* v_reuseFailAlloc_1238_; 
v_reuseFailAlloc_1238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1238_, 0, v_a_1232_);
v___x_1237_ = v_reuseFailAlloc_1238_;
goto v_reusejp_1236_;
}
v_reusejp_1236_:
{
return v___x_1237_;
}
}
}
}
else
{
lean_object* v_a_1240_; lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1247_; 
lean_dec_ref(v___x_1141_);
lean_dec_ref(v_e_1133_);
lean_dec(v___x_1131_);
lean_dec_ref(v___x_1130_);
lean_dec_ref(v___x_1129_);
lean_dec_ref(v_h_x27_1127_);
lean_dec(v_mvarId_1125_);
v_a_1240_ = lean_ctor_get(v___x_1142_, 0);
v_isSharedCheck_1247_ = !lean_is_exclusive(v___x_1142_);
if (v_isSharedCheck_1247_ == 0)
{
v___x_1242_ = v___x_1142_;
v_isShared_1243_ = v_isSharedCheck_1247_;
goto v_resetjp_1241_;
}
else
{
lean_inc(v_a_1240_);
lean_dec(v___x_1142_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1247_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
lean_object* v___x_1245_; 
if (v_isShared_1243_ == 0)
{
v___x_1245_ = v___x_1242_;
goto v_reusejp_1244_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v_a_1240_);
v___x_1245_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1244_;
}
v_reusejp_1244_:
{
return v___x_1245_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__0___boxed(lean_object** _args){
lean_object* v_newEqs_1248_ = _args[0];
lean_object* v_mvarId_1249_ = _args[1];
lean_object* v___x_1250_ = _args[2];
lean_object* v_h_x27_1251_ = _args[3];
lean_object* v_newIndices_1252_ = _args[4];
lean_object* v___x_1253_ = _args[5];
lean_object* v___x_1254_ = _args[6];
lean_object* v___x_1255_ = _args[7];
lean_object* v___x_1256_ = _args[8];
lean_object* v_e_1257_ = _args[9];
lean_object* v___x_1258_ = _args[10];
lean_object* v_newEq_1259_ = _args[11];
lean_object* v___y_1260_ = _args[12];
lean_object* v___y_1261_ = _args[13];
lean_object* v___y_1262_ = _args[14];
lean_object* v___y_1263_ = _args[15];
lean_object* v___y_1264_ = _args[16];
_start:
{
uint8_t v___x_6157__boxed_1265_; lean_object* v_res_1266_; 
v___x_6157__boxed_1265_ = lean_unbox(v___x_1250_);
v_res_1266_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__0(v_newEqs_1248_, v_mvarId_1249_, v___x_6157__boxed_1265_, v_h_x27_1251_, v_newIndices_1252_, v___x_1253_, v___x_1254_, v___x_1255_, v___x_1256_, v_e_1257_, v___x_1258_, v_newEq_1259_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_);
lean_dec(v___y_1263_);
lean_dec_ref(v___y_1262_);
lean_dec(v___y_1261_);
lean_dec_ref(v___y_1260_);
lean_dec_ref(v___x_1258_);
lean_dec_ref(v___x_1256_);
lean_dec_ref(v_newIndices_1252_);
return v_res_1266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__1(lean_object* v_e_1267_, lean_object* v_h_x27_1268_, lean_object* v_mvarId_1269_, uint8_t v___x_1270_, lean_object* v_newIndices_1271_, lean_object* v___x_1272_, lean_object* v___x_1273_, lean_object* v___x_1274_, lean_object* v___x_1275_, lean_object* v_newEqs_1276_, lean_object* v_newRefls_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_){
_start:
{
lean_object* v___x_1283_; 
lean_inc_ref(v_h_x27_1268_);
lean_inc_ref(v_e_1267_);
v___x_1283_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof(v_e_1267_, v_h_x27_1268_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_);
if (lean_obj_tag(v___x_1283_) == 0)
{
lean_object* v_a_1284_; lean_object* v_fst_1285_; lean_object* v_snd_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___f_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; 
v_a_1284_ = lean_ctor_get(v___x_1283_, 0);
lean_inc(v_a_1284_);
lean_dec_ref_known(v___x_1283_, 1);
v_fst_1285_ = lean_ctor_get(v_a_1284_, 0);
lean_inc(v_fst_1285_);
v_snd_1286_ = lean_ctor_get(v_a_1284_, 1);
lean_inc(v_snd_1286_);
lean_dec(v_a_1284_);
v___x_1287_ = lean_array_push(v_newRefls_1277_, v_snd_1286_);
v___x_1288_ = lean_box(v___x_1270_);
v___f_1289_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__0___boxed), 17, 11);
lean_closure_set(v___f_1289_, 0, v_newEqs_1276_);
lean_closure_set(v___f_1289_, 1, v_mvarId_1269_);
lean_closure_set(v___f_1289_, 2, v___x_1288_);
lean_closure_set(v___f_1289_, 3, v_h_x27_1268_);
lean_closure_set(v___f_1289_, 4, v_newIndices_1271_);
lean_closure_set(v___f_1289_, 5, v___x_1272_);
lean_closure_set(v___f_1289_, 6, v___x_1273_);
lean_closure_set(v___f_1289_, 7, v___x_1274_);
lean_closure_set(v___f_1289_, 8, v___x_1275_);
lean_closure_set(v___f_1289_, 9, v_e_1267_);
lean_closure_set(v___f_1289_, 10, v___x_1287_);
v___x_1290_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___redArg___closed__1));
v___x_1291_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0___redArg(v___x_1290_, v_fst_1285_, v___f_1289_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_);
return v___x_1291_;
}
else
{
lean_object* v_a_1292_; lean_object* v___x_1294_; uint8_t v_isShared_1295_; uint8_t v_isSharedCheck_1299_; 
lean_dec_ref(v_newRefls_1277_);
lean_dec_ref(v_newEqs_1276_);
lean_dec_ref(v___x_1275_);
lean_dec(v___x_1274_);
lean_dec_ref(v___x_1273_);
lean_dec_ref(v___x_1272_);
lean_dec_ref(v_newIndices_1271_);
lean_dec(v_mvarId_1269_);
lean_dec_ref(v_h_x27_1268_);
lean_dec_ref(v_e_1267_);
v_a_1292_ = lean_ctor_get(v___x_1283_, 0);
v_isSharedCheck_1299_ = !lean_is_exclusive(v___x_1283_);
if (v_isSharedCheck_1299_ == 0)
{
v___x_1294_ = v___x_1283_;
v_isShared_1295_ = v_isSharedCheck_1299_;
goto v_resetjp_1293_;
}
else
{
lean_inc(v_a_1292_);
lean_dec(v___x_1283_);
v___x_1294_ = lean_box(0);
v_isShared_1295_ = v_isSharedCheck_1299_;
goto v_resetjp_1293_;
}
v_resetjp_1293_:
{
lean_object* v___x_1297_; 
if (v_isShared_1295_ == 0)
{
v___x_1297_ = v___x_1294_;
goto v_reusejp_1296_;
}
else
{
lean_object* v_reuseFailAlloc_1298_; 
v_reuseFailAlloc_1298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1298_, 0, v_a_1292_);
v___x_1297_ = v_reuseFailAlloc_1298_;
goto v_reusejp_1296_;
}
v_reusejp_1296_:
{
return v___x_1297_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__1___boxed(lean_object* v_e_1300_, lean_object* v_h_x27_1301_, lean_object* v_mvarId_1302_, lean_object* v___x_1303_, lean_object* v_newIndices_1304_, lean_object* v___x_1305_, lean_object* v___x_1306_, lean_object* v___x_1307_, lean_object* v___x_1308_, lean_object* v_newEqs_1309_, lean_object* v_newRefls_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_){
_start:
{
uint8_t v___x_6409__boxed_1316_; lean_object* v_res_1317_; 
v___x_6409__boxed_1316_ = lean_unbox(v___x_1303_);
v_res_1317_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__1(v_e_1300_, v_h_x27_1301_, v_mvarId_1302_, v___x_6409__boxed_1316_, v_newIndices_1304_, v___x_1305_, v___x_1306_, v___x_1307_, v___x_1308_, v_newEqs_1309_, v_newRefls_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_);
lean_dec(v___y_1314_);
lean_dec_ref(v___y_1313_);
lean_dec(v___y_1312_);
lean_dec_ref(v___y_1311_);
return v_res_1317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__2(lean_object* v_e_1318_, lean_object* v_mvarId_1319_, uint8_t v___x_1320_, lean_object* v_newIndices_1321_, lean_object* v___x_1322_, lean_object* v___x_1323_, lean_object* v___x_1324_, lean_object* v___x_1325_, lean_object* v_h_x27_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_){
_start:
{
lean_object* v___x_1332_; lean_object* v___f_1333_; lean_object* v___x_1334_; 
v___x_1332_ = lean_box(v___x_1320_);
lean_inc_ref(v___x_1325_);
lean_inc_ref(v_newIndices_1321_);
v___f_1333_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__1___boxed), 16, 9);
lean_closure_set(v___f_1333_, 0, v_e_1318_);
lean_closure_set(v___f_1333_, 1, v_h_x27_1326_);
lean_closure_set(v___f_1333_, 2, v_mvarId_1319_);
lean_closure_set(v___f_1333_, 3, v___x_1332_);
lean_closure_set(v___f_1333_, 4, v_newIndices_1321_);
lean_closure_set(v___f_1333_, 5, v___x_1322_);
lean_closure_set(v___f_1333_, 6, v___x_1323_);
lean_closure_set(v___f_1333_, 7, v___x_1324_);
lean_closure_set(v___f_1333_, 8, v___x_1325_);
v___x_1334_ = l_Lean_Meta_withNewEqs___redArg(v___x_1325_, v_newIndices_1321_, v___f_1333_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_);
return v___x_1334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__2___boxed(lean_object* v_e_1335_, lean_object* v_mvarId_1336_, lean_object* v___x_1337_, lean_object* v_newIndices_1338_, lean_object* v___x_1339_, lean_object* v___x_1340_, lean_object* v___x_1341_, lean_object* v___x_1342_, lean_object* v_h_x27_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_){
_start:
{
uint8_t v___x_6474__boxed_1349_; lean_object* v_res_1350_; 
v___x_6474__boxed_1349_ = lean_unbox(v___x_1337_);
v_res_1350_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__2(v_e_1335_, v_mvarId_1336_, v___x_6474__boxed_1349_, v_newIndices_1338_, v___x_1339_, v___x_1340_, v___x_1341_, v___x_1342_, v_h_x27_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_);
lean_dec(v___y_1347_);
lean_dec_ref(v___y_1346_);
lean_dec(v___y_1345_);
lean_dec_ref(v___y_1344_);
return v_res_1350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__3(lean_object* v_e_1354_, lean_object* v_mvarId_1355_, uint8_t v___x_1356_, lean_object* v___x_1357_, lean_object* v___x_1358_, lean_object* v___x_1359_, lean_object* v___x_1360_, lean_object* v___x_1361_, lean_object* v_varName_x3f_1362_, lean_object* v_newIndices_1363_, lean_object* v_x_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_){
_start:
{
lean_object* v___x_1370_; lean_object* v___f_1371_; lean_object* v___x_1372_; 
v___x_1370_ = lean_box(v___x_1356_);
lean_inc_ref(v_newIndices_1363_);
v___f_1371_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__2___boxed), 14, 8);
lean_closure_set(v___f_1371_, 0, v_e_1354_);
lean_closure_set(v___f_1371_, 1, v_mvarId_1355_);
lean_closure_set(v___f_1371_, 2, v___x_1370_);
lean_closure_set(v___f_1371_, 3, v_newIndices_1363_);
lean_closure_set(v___f_1371_, 4, v___x_1357_);
lean_closure_set(v___f_1371_, 5, v___x_1358_);
lean_closure_set(v___f_1371_, 6, v___x_1359_);
lean_closure_set(v___f_1371_, 7, v___x_1360_);
v___x_1372_ = l_Lean_mkAppN(v___x_1361_, v_newIndices_1363_);
lean_dec_ref(v_newIndices_1363_);
if (lean_obj_tag(v_varName_x3f_1362_) == 1)
{
lean_object* v_val_1373_; lean_object* v___x_1374_; 
v_val_1373_ = lean_ctor_get(v_varName_x3f_1362_, 0);
lean_inc(v_val_1373_);
lean_dec_ref_known(v_varName_x3f_1362_, 1);
v___x_1374_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0___redArg(v_val_1373_, v___x_1372_, v___f_1371_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_);
return v___x_1374_;
}
else
{
lean_object* v___x_1375_; lean_object* v___x_1376_; 
lean_dec(v_varName_x3f_1362_);
v___x_1375_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__3___closed__1));
v___x_1376_ = l_Lean_Core_mkFreshUserName(v___x_1375_, v___y_1367_, v___y_1368_);
if (lean_obj_tag(v___x_1376_) == 0)
{
lean_object* v_a_1377_; lean_object* v___x_1378_; 
v_a_1377_ = lean_ctor_get(v___x_1376_, 0);
lean_inc(v_a_1377_);
lean_dec_ref_known(v___x_1376_, 1);
v___x_1378_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0___redArg(v_a_1377_, v___x_1372_, v___f_1371_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_);
return v___x_1378_;
}
else
{
lean_object* v_a_1379_; lean_object* v___x_1381_; uint8_t v_isShared_1382_; uint8_t v_isSharedCheck_1386_; 
lean_dec_ref(v___x_1372_);
lean_dec_ref(v___f_1371_);
v_a_1379_ = lean_ctor_get(v___x_1376_, 0);
v_isSharedCheck_1386_ = !lean_is_exclusive(v___x_1376_);
if (v_isSharedCheck_1386_ == 0)
{
v___x_1381_ = v___x_1376_;
v_isShared_1382_ = v_isSharedCheck_1386_;
goto v_resetjp_1380_;
}
else
{
lean_inc(v_a_1379_);
lean_dec(v___x_1376_);
v___x_1381_ = lean_box(0);
v_isShared_1382_ = v_isSharedCheck_1386_;
goto v_resetjp_1380_;
}
v_resetjp_1380_:
{
lean_object* v___x_1384_; 
if (v_isShared_1382_ == 0)
{
v___x_1384_ = v___x_1381_;
goto v_reusejp_1383_;
}
else
{
lean_object* v_reuseFailAlloc_1385_; 
v_reuseFailAlloc_1385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1385_, 0, v_a_1379_);
v___x_1384_ = v_reuseFailAlloc_1385_;
goto v_reusejp_1383_;
}
v_reusejp_1383_:
{
return v___x_1384_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__3___boxed(lean_object* v_e_1387_, lean_object* v_mvarId_1388_, lean_object* v___x_1389_, lean_object* v___x_1390_, lean_object* v___x_1391_, lean_object* v___x_1392_, lean_object* v___x_1393_, lean_object* v___x_1394_, lean_object* v_varName_x3f_1395_, lean_object* v_newIndices_1396_, lean_object* v_x_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_){
_start:
{
uint8_t v___x_6516__boxed_1403_; lean_object* v_res_1404_; 
v___x_6516__boxed_1403_ = lean_unbox(v___x_1389_);
v_res_1404_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__3(v_e_1387_, v_mvarId_1388_, v___x_6516__boxed_1403_, v___x_1390_, v___x_1391_, v___x_1392_, v___x_1393_, v___x_1394_, v_varName_x3f_1395_, v_newIndices_1396_, v_x_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_);
lean_dec(v___y_1401_);
lean_dec_ref(v___y_1400_);
lean_dec(v___y_1399_);
lean_dec_ref(v___y_1398_);
lean_dec_ref(v_x_1397_);
return v_res_1404_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__4(void){
_start:
{
lean_object* v___x_1411_; lean_object* v___x_1412_; 
v___x_1411_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__3));
v___x_1412_ = l_Lean_MessageData_ofFormat(v___x_1411_);
return v___x_1412_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__5(void){
_start:
{
lean_object* v___x_1413_; lean_object* v___x_1414_; 
v___x_1413_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__4, &l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__4_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__4);
v___x_1414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1414_, 0, v___x_1413_);
return v___x_1414_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__8(void){
_start:
{
lean_object* v___x_1418_; lean_object* v___x_1419_; 
v___x_1418_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__7));
v___x_1419_ = l_Lean_MessageData_ofFormat(v___x_1418_);
return v___x_1419_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__9(void){
_start:
{
lean_object* v___x_1420_; lean_object* v___x_1421_; 
v___x_1420_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__8, &l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__8_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__8);
v___x_1421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1421_, 0, v___x_1420_);
return v___x_1421_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__12(void){
_start:
{
lean_object* v___x_1425_; lean_object* v___x_1426_; 
v___x_1425_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__11));
v___x_1426_ = l_Lean_MessageData_ofFormat(v___x_1425_);
return v___x_1426_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__13(void){
_start:
{
lean_object* v___x_1427_; lean_object* v___x_1428_; 
v___x_1427_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__12, &l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__12_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__12);
v___x_1428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1428_, 0, v___x_1427_);
return v___x_1428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0(lean_object* v_mvarId_1429_, lean_object* v_e_1430_, lean_object* v___x_1431_, lean_object* v___x_1432_, lean_object* v_varName_x3f_1433_, lean_object* v_x_1434_, lean_object* v_x_1435_, lean_object* v_x_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_){
_start:
{
if (lean_obj_tag(v_x_1434_) == 5)
{
lean_object* v_fn_1442_; lean_object* v_arg_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; 
v_fn_1442_ = lean_ctor_get(v_x_1434_, 0);
lean_inc_ref(v_fn_1442_);
v_arg_1443_ = lean_ctor_get(v_x_1434_, 1);
lean_inc_ref(v_arg_1443_);
lean_dec_ref_known(v_x_1434_, 2);
v___x_1444_ = lean_array_set(v_x_1435_, v_x_1436_, v_arg_1443_);
v___x_1445_ = lean_unsigned_to_nat(1u);
v___x_1446_ = lean_nat_sub(v_x_1436_, v___x_1445_);
lean_dec(v_x_1436_);
v_x_1434_ = v_fn_1442_;
v_x_1435_ = v___x_1444_;
v_x_1436_ = v___x_1446_;
goto _start;
}
else
{
lean_object* v___x_1448_; lean_object* v___y_1450_; lean_object* v___y_1451_; lean_object* v___y_1452_; lean_object* v___y_1453_; 
lean_dec(v_x_1436_);
v___x_1448_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__1));
if (lean_obj_tag(v_x_1434_) == 4)
{
lean_object* v_declName_1456_; lean_object* v___x_1457_; lean_object* v_env_1458_; uint8_t v___x_1459_; lean_object* v___x_1460_; 
v_declName_1456_ = lean_ctor_get(v_x_1434_, 0);
v___x_1457_ = lean_st_ref_get(v___y_1440_);
v_env_1458_ = lean_ctor_get(v___x_1457_, 0);
lean_inc_ref(v_env_1458_);
lean_dec(v___x_1457_);
v___x_1459_ = 0;
lean_inc(v_declName_1456_);
v___x_1460_ = l_Lean_Environment_find_x3f(v_env_1458_, v_declName_1456_, v___x_1459_);
if (lean_obj_tag(v___x_1460_) == 0)
{
lean_dec_ref_known(v_x_1434_, 2);
lean_dec_ref(v_x_1435_);
lean_dec(v_varName_x3f_1433_);
lean_dec_ref(v___x_1432_);
lean_dec_ref(v___x_1431_);
lean_dec_ref(v_e_1430_);
v___y_1450_ = v___y_1437_;
v___y_1451_ = v___y_1438_;
v___y_1452_ = v___y_1439_;
v___y_1453_ = v___y_1440_;
goto v___jp_1449_;
}
else
{
lean_object* v_val_1461_; 
v_val_1461_ = lean_ctor_get(v___x_1460_, 0);
lean_inc(v_val_1461_);
lean_dec_ref_known(v___x_1460_, 1);
if (lean_obj_tag(v_val_1461_) == 5)
{
lean_object* v_val_1462_; lean_object* v_numParams_1463_; lean_object* v_numIndices_1464_; lean_object* v___y_1466_; lean_object* v___y_1467_; lean_object* v___y_1468_; lean_object* v___y_1469_; lean_object* v___y_1490_; lean_object* v___y_1491_; lean_object* v___y_1492_; lean_object* v___y_1493_; lean_object* v___x_1507_; uint8_t v___x_1508_; 
v_val_1462_ = lean_ctor_get(v_val_1461_, 0);
lean_inc_ref(v_val_1462_);
lean_dec_ref_known(v_val_1461_, 1);
v_numParams_1463_ = lean_ctor_get(v_val_1462_, 1);
lean_inc(v_numParams_1463_);
v_numIndices_1464_ = lean_ctor_get(v_val_1462_, 2);
lean_inc(v_numIndices_1464_);
lean_dec_ref(v_val_1462_);
v___x_1507_ = lean_unsigned_to_nat(0u);
v___x_1508_ = lean_nat_dec_lt(v___x_1507_, v_numIndices_1464_);
if (v___x_1508_ == 0)
{
lean_object* v___x_1509_; lean_object* v___x_1510_; 
v___x_1509_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__13, &l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__13_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__13);
lean_inc(v_mvarId_1429_);
v___x_1510_ = l_Lean_Meta_throwTacticEx___redArg(v___x_1448_, v_mvarId_1429_, v___x_1509_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_);
if (lean_obj_tag(v___x_1510_) == 0)
{
lean_dec_ref_known(v___x_1510_, 1);
v___y_1490_ = v___y_1437_;
v___y_1491_ = v___y_1438_;
v___y_1492_ = v___y_1439_;
v___y_1493_ = v___y_1440_;
goto v___jp_1489_;
}
else
{
lean_object* v_a_1511_; lean_object* v___x_1513_; uint8_t v_isShared_1514_; uint8_t v_isSharedCheck_1518_; 
lean_dec(v_numIndices_1464_);
lean_dec(v_numParams_1463_);
lean_dec_ref_known(v_x_1434_, 2);
lean_dec_ref(v_x_1435_);
lean_dec(v_varName_x3f_1433_);
lean_dec_ref(v___x_1432_);
lean_dec_ref(v___x_1431_);
lean_dec_ref(v_e_1430_);
lean_dec(v_mvarId_1429_);
v_a_1511_ = lean_ctor_get(v___x_1510_, 0);
v_isSharedCheck_1518_ = !lean_is_exclusive(v___x_1510_);
if (v_isSharedCheck_1518_ == 0)
{
v___x_1513_ = v___x_1510_;
v_isShared_1514_ = v_isSharedCheck_1518_;
goto v_resetjp_1512_;
}
else
{
lean_inc(v_a_1511_);
lean_dec(v___x_1510_);
v___x_1513_ = lean_box(0);
v_isShared_1514_ = v_isSharedCheck_1518_;
goto v_resetjp_1512_;
}
v_resetjp_1512_:
{
lean_object* v___x_1516_; 
if (v_isShared_1514_ == 0)
{
v___x_1516_ = v___x_1513_;
goto v_reusejp_1515_;
}
else
{
lean_object* v_reuseFailAlloc_1517_; 
v_reuseFailAlloc_1517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1517_, 0, v_a_1511_);
v___x_1516_ = v_reuseFailAlloc_1517_;
goto v_reusejp_1515_;
}
v_reusejp_1515_:
{
return v___x_1516_;
}
}
}
}
else
{
v___y_1490_ = v___y_1437_;
v___y_1491_ = v___y_1438_;
v___y_1492_ = v___y_1439_;
v___y_1493_ = v___y_1440_;
goto v___jp_1489_;
}
v___jp_1465_:
{
lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___f_1477_; lean_object* v___x_1478_; 
v___x_1470_ = lean_array_get_size(v_x_1435_);
v___x_1471_ = lean_nat_sub(v___x_1470_, v_numIndices_1464_);
lean_dec(v_numIndices_1464_);
v___x_1472_ = l_Array_extract___redArg(v_x_1435_, v___x_1471_, v___x_1470_);
v___x_1473_ = lean_unsigned_to_nat(0u);
v___x_1474_ = l_Array_extract___redArg(v_x_1435_, v___x_1473_, v_numParams_1463_);
lean_dec_ref(v_x_1435_);
v___x_1475_ = l_Lean_mkAppN(v_x_1434_, v___x_1474_);
lean_dec_ref(v___x_1474_);
v___x_1476_ = lean_box(v___x_1459_);
lean_inc_ref(v___x_1475_);
v___f_1477_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__3___boxed), 16, 9);
lean_closure_set(v___f_1477_, 0, v_e_1430_);
lean_closure_set(v___f_1477_, 1, v_mvarId_1429_);
lean_closure_set(v___f_1477_, 2, v___x_1476_);
lean_closure_set(v___f_1477_, 3, v___x_1431_);
lean_closure_set(v___f_1477_, 4, v___x_1432_);
lean_closure_set(v___f_1477_, 5, v___x_1473_);
lean_closure_set(v___f_1477_, 6, v___x_1472_);
lean_closure_set(v___f_1477_, 7, v___x_1475_);
lean_closure_set(v___f_1477_, 8, v_varName_x3f_1433_);
lean_inc(v___y_1469_);
lean_inc_ref(v___y_1468_);
lean_inc(v___y_1467_);
lean_inc_ref(v___y_1466_);
v___x_1478_ = lean_infer_type(v___x_1475_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_);
if (lean_obj_tag(v___x_1478_) == 0)
{
lean_object* v_a_1479_; lean_object* v___x_1480_; 
v_a_1479_ = lean_ctor_get(v___x_1478_, 0);
lean_inc(v_a_1479_);
lean_dec_ref_known(v___x_1478_, 1);
v___x_1480_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_generalizeTargetsEq_spec__0___redArg(v_a_1479_, v___f_1477_, v___x_1459_, v___x_1459_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_);
return v___x_1480_;
}
else
{
lean_object* v_a_1481_; lean_object* v___x_1483_; uint8_t v_isShared_1484_; uint8_t v_isSharedCheck_1488_; 
lean_dec_ref(v___f_1477_);
v_a_1481_ = lean_ctor_get(v___x_1478_, 0);
v_isSharedCheck_1488_ = !lean_is_exclusive(v___x_1478_);
if (v_isSharedCheck_1488_ == 0)
{
v___x_1483_ = v___x_1478_;
v_isShared_1484_ = v_isSharedCheck_1488_;
goto v_resetjp_1482_;
}
else
{
lean_inc(v_a_1481_);
lean_dec(v___x_1478_);
v___x_1483_ = lean_box(0);
v_isShared_1484_ = v_isSharedCheck_1488_;
goto v_resetjp_1482_;
}
v_resetjp_1482_:
{
lean_object* v___x_1486_; 
if (v_isShared_1484_ == 0)
{
v___x_1486_ = v___x_1483_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v_a_1481_);
v___x_1486_ = v_reuseFailAlloc_1487_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
return v___x_1486_;
}
}
}
}
v___jp_1489_:
{
lean_object* v___x_1494_; lean_object* v___x_1495_; uint8_t v___x_1496_; 
v___x_1494_ = lean_array_get_size(v_x_1435_);
v___x_1495_ = lean_nat_add(v_numIndices_1464_, v_numParams_1463_);
v___x_1496_ = lean_nat_dec_eq(v___x_1494_, v___x_1495_);
lean_dec(v___x_1495_);
if (v___x_1496_ == 0)
{
lean_object* v___x_1497_; lean_object* v___x_1498_; 
v___x_1497_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__9, &l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__9_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__9);
lean_inc(v_mvarId_1429_);
v___x_1498_ = l_Lean_Meta_throwTacticEx___redArg(v___x_1448_, v_mvarId_1429_, v___x_1497_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_);
if (lean_obj_tag(v___x_1498_) == 0)
{
lean_dec_ref_known(v___x_1498_, 1);
v___y_1466_ = v___y_1490_;
v___y_1467_ = v___y_1491_;
v___y_1468_ = v___y_1492_;
v___y_1469_ = v___y_1493_;
goto v___jp_1465_;
}
else
{
lean_object* v_a_1499_; lean_object* v___x_1501_; uint8_t v_isShared_1502_; uint8_t v_isSharedCheck_1506_; 
lean_dec(v_numIndices_1464_);
lean_dec(v_numParams_1463_);
lean_dec_ref_known(v_x_1434_, 2);
lean_dec_ref(v_x_1435_);
lean_dec(v_varName_x3f_1433_);
lean_dec_ref(v___x_1432_);
lean_dec_ref(v___x_1431_);
lean_dec_ref(v_e_1430_);
lean_dec(v_mvarId_1429_);
v_a_1499_ = lean_ctor_get(v___x_1498_, 0);
v_isSharedCheck_1506_ = !lean_is_exclusive(v___x_1498_);
if (v_isSharedCheck_1506_ == 0)
{
v___x_1501_ = v___x_1498_;
v_isShared_1502_ = v_isSharedCheck_1506_;
goto v_resetjp_1500_;
}
else
{
lean_inc(v_a_1499_);
lean_dec(v___x_1498_);
v___x_1501_ = lean_box(0);
v_isShared_1502_ = v_isSharedCheck_1506_;
goto v_resetjp_1500_;
}
v_resetjp_1500_:
{
lean_object* v___x_1504_; 
if (v_isShared_1502_ == 0)
{
v___x_1504_ = v___x_1501_;
goto v_reusejp_1503_;
}
else
{
lean_object* v_reuseFailAlloc_1505_; 
v_reuseFailAlloc_1505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1505_, 0, v_a_1499_);
v___x_1504_ = v_reuseFailAlloc_1505_;
goto v_reusejp_1503_;
}
v_reusejp_1503_:
{
return v___x_1504_;
}
}
}
}
else
{
v___y_1466_ = v___y_1490_;
v___y_1467_ = v___y_1491_;
v___y_1468_ = v___y_1492_;
v___y_1469_ = v___y_1493_;
goto v___jp_1465_;
}
}
}
else
{
lean_dec(v_val_1461_);
lean_dec_ref_known(v_x_1434_, 2);
lean_dec_ref(v_x_1435_);
lean_dec(v_varName_x3f_1433_);
lean_dec_ref(v___x_1432_);
lean_dec_ref(v___x_1431_);
lean_dec_ref(v_e_1430_);
v___y_1450_ = v___y_1437_;
v___y_1451_ = v___y_1438_;
v___y_1452_ = v___y_1439_;
v___y_1453_ = v___y_1440_;
goto v___jp_1449_;
}
}
}
else
{
lean_dec_ref(v_x_1435_);
lean_dec_ref(v_x_1434_);
lean_dec(v_varName_x3f_1433_);
lean_dec_ref(v___x_1432_);
lean_dec_ref(v___x_1431_);
lean_dec_ref(v_e_1430_);
v___y_1450_ = v___y_1437_;
v___y_1451_ = v___y_1438_;
v___y_1452_ = v___y_1439_;
v___y_1453_ = v___y_1440_;
goto v___jp_1449_;
}
v___jp_1449_:
{
lean_object* v___x_1454_; lean_object* v___x_1455_; 
v___x_1454_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__5, &l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__5_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__5);
v___x_1455_ = l_Lean_Meta_throwTacticEx___redArg(v___x_1448_, v_mvarId_1429_, v___x_1454_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_);
return v___x_1455_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___boxed(lean_object* v_mvarId_1519_, lean_object* v_e_1520_, lean_object* v___x_1521_, lean_object* v___x_1522_, lean_object* v_varName_x3f_1523_, lean_object* v_x_1524_, lean_object* v_x_1525_, lean_object* v_x_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_){
_start:
{
lean_object* v_res_1532_; 
v_res_1532_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0(v_mvarId_1519_, v_e_1520_, v___x_1521_, v___x_1522_, v_varName_x3f_1523_, v_x_1524_, v_x_1525_, v_x_1526_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_);
lean_dec(v___y_1530_);
lean_dec_ref(v___y_1529_);
lean_dec(v___y_1528_);
lean_dec_ref(v___y_1527_);
return v_res_1532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeIndices_x27___lam__0(lean_object* v_mvarId_1533_, lean_object* v_e_1534_, lean_object* v_varName_x3f_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_){
_start:
{
lean_object* v_lctx_1541_; lean_object* v_localInstances_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; 
v_lctx_1541_ = lean_ctor_get(v___y_1536_, 2);
lean_inc_ref(v_lctx_1541_);
v_localInstances_1542_ = lean_ctor_get(v___y_1536_, 3);
lean_inc_ref(v_localInstances_1542_);
v___x_1543_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__1));
lean_inc(v_mvarId_1533_);
v___x_1544_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_1533_, v___x_1543_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_);
if (lean_obj_tag(v___x_1544_) == 0)
{
lean_object* v___x_1545_; 
lean_dec_ref_known(v___x_1544_, 1);
lean_inc(v___y_1539_);
lean_inc_ref(v___y_1538_);
lean_inc(v___y_1537_);
lean_inc_ref(v___y_1536_);
lean_inc_ref(v_e_1534_);
v___x_1545_ = lean_infer_type(v_e_1534_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_);
if (lean_obj_tag(v___x_1545_) == 0)
{
lean_object* v_a_1546_; lean_object* v___x_1547_; 
v_a_1546_ = lean_ctor_get(v___x_1545_, 0);
lean_inc(v_a_1546_);
lean_dec_ref_known(v___x_1545_, 1);
v___x_1547_ = l_Lean_Meta_whnfD(v_a_1546_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_);
if (lean_obj_tag(v___x_1547_) == 0)
{
lean_object* v_a_1548_; lean_object* v_dummy_1549_; lean_object* v_nargs_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; 
v_a_1548_ = lean_ctor_get(v___x_1547_, 0);
lean_inc(v_a_1548_);
lean_dec_ref_known(v___x_1547_, 1);
v_dummy_1549_ = lean_obj_once(&l_Lean_Meta_getInductiveUniverseAndParams___closed__0, &l_Lean_Meta_getInductiveUniverseAndParams___closed__0_once, _init_l_Lean_Meta_getInductiveUniverseAndParams___closed__0);
v_nargs_1550_ = l_Lean_Expr_getAppNumArgs(v_a_1548_);
lean_inc(v_nargs_1550_);
v___x_1551_ = lean_mk_array(v_nargs_1550_, v_dummy_1549_);
v___x_1552_ = lean_unsigned_to_nat(1u);
v___x_1553_ = lean_nat_sub(v_nargs_1550_, v___x_1552_);
lean_dec(v_nargs_1550_);
v___x_1554_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0(v_mvarId_1533_, v_e_1534_, v_lctx_1541_, v_localInstances_1542_, v_varName_x3f_1535_, v_a_1548_, v___x_1551_, v___x_1553_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_);
lean_dec(v___y_1539_);
lean_dec_ref(v___y_1538_);
lean_dec(v___y_1537_);
lean_dec_ref(v___y_1536_);
return v___x_1554_;
}
else
{
lean_object* v_a_1555_; lean_object* v___x_1557_; uint8_t v_isShared_1558_; uint8_t v_isSharedCheck_1562_; 
lean_dec_ref(v_localInstances_1542_);
lean_dec_ref(v_lctx_1541_);
lean_dec(v___y_1539_);
lean_dec_ref(v___y_1538_);
lean_dec(v___y_1537_);
lean_dec_ref(v___y_1536_);
lean_dec(v_varName_x3f_1535_);
lean_dec_ref(v_e_1534_);
lean_dec(v_mvarId_1533_);
v_a_1555_ = lean_ctor_get(v___x_1547_, 0);
v_isSharedCheck_1562_ = !lean_is_exclusive(v___x_1547_);
if (v_isSharedCheck_1562_ == 0)
{
v___x_1557_ = v___x_1547_;
v_isShared_1558_ = v_isSharedCheck_1562_;
goto v_resetjp_1556_;
}
else
{
lean_inc(v_a_1555_);
lean_dec(v___x_1547_);
v___x_1557_ = lean_box(0);
v_isShared_1558_ = v_isSharedCheck_1562_;
goto v_resetjp_1556_;
}
v_resetjp_1556_:
{
lean_object* v___x_1560_; 
if (v_isShared_1558_ == 0)
{
v___x_1560_ = v___x_1557_;
goto v_reusejp_1559_;
}
else
{
lean_object* v_reuseFailAlloc_1561_; 
v_reuseFailAlloc_1561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1561_, 0, v_a_1555_);
v___x_1560_ = v_reuseFailAlloc_1561_;
goto v_reusejp_1559_;
}
v_reusejp_1559_:
{
return v___x_1560_;
}
}
}
}
else
{
lean_object* v_a_1563_; lean_object* v___x_1565_; uint8_t v_isShared_1566_; uint8_t v_isSharedCheck_1570_; 
lean_dec_ref(v_localInstances_1542_);
lean_dec_ref(v_lctx_1541_);
lean_dec(v___y_1539_);
lean_dec_ref(v___y_1538_);
lean_dec(v___y_1537_);
lean_dec_ref(v___y_1536_);
lean_dec(v_varName_x3f_1535_);
lean_dec_ref(v_e_1534_);
lean_dec(v_mvarId_1533_);
v_a_1563_ = lean_ctor_get(v___x_1545_, 0);
v_isSharedCheck_1570_ = !lean_is_exclusive(v___x_1545_);
if (v_isSharedCheck_1570_ == 0)
{
v___x_1565_ = v___x_1545_;
v_isShared_1566_ = v_isSharedCheck_1570_;
goto v_resetjp_1564_;
}
else
{
lean_inc(v_a_1563_);
lean_dec(v___x_1545_);
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
else
{
lean_object* v_a_1571_; lean_object* v___x_1573_; uint8_t v_isShared_1574_; uint8_t v_isSharedCheck_1578_; 
lean_dec_ref(v_localInstances_1542_);
lean_dec_ref(v_lctx_1541_);
lean_dec(v___y_1539_);
lean_dec_ref(v___y_1538_);
lean_dec(v___y_1537_);
lean_dec_ref(v___y_1536_);
lean_dec(v_varName_x3f_1535_);
lean_dec_ref(v_e_1534_);
lean_dec(v_mvarId_1533_);
v_a_1571_ = lean_ctor_get(v___x_1544_, 0);
v_isSharedCheck_1578_ = !lean_is_exclusive(v___x_1544_);
if (v_isSharedCheck_1578_ == 0)
{
v___x_1573_ = v___x_1544_;
v_isShared_1574_ = v_isSharedCheck_1578_;
goto v_resetjp_1572_;
}
else
{
lean_inc(v_a_1571_);
lean_dec(v___x_1544_);
v___x_1573_ = lean_box(0);
v_isShared_1574_ = v_isSharedCheck_1578_;
goto v_resetjp_1572_;
}
v_resetjp_1572_:
{
lean_object* v___x_1576_; 
if (v_isShared_1574_ == 0)
{
v___x_1576_ = v___x_1573_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1577_; 
v_reuseFailAlloc_1577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1577_, 0, v_a_1571_);
v___x_1576_ = v_reuseFailAlloc_1577_;
goto v_reusejp_1575_;
}
v_reusejp_1575_:
{
return v___x_1576_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeIndices_x27___lam__0___boxed(lean_object* v_mvarId_1579_, lean_object* v_e_1580_, lean_object* v_varName_x3f_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_){
_start:
{
lean_object* v_res_1587_; 
v_res_1587_ = l_Lean_Meta_generalizeIndices_x27___lam__0(v_mvarId_1579_, v_e_1580_, v_varName_x3f_1581_, v___y_1582_, v___y_1583_, v___y_1584_, v___y_1585_);
return v_res_1587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeIndices_x27(lean_object* v_mvarId_1588_, lean_object* v_e_1589_, lean_object* v_varName_x3f_1590_, lean_object* v_a_1591_, lean_object* v_a_1592_, lean_object* v_a_1593_, lean_object* v_a_1594_){
_start:
{
lean_object* v___f_1596_; lean_object* v___x_1597_; 
lean_inc(v_mvarId_1588_);
v___f_1596_ = lean_alloc_closure((void*)(l_Lean_Meta_generalizeIndices_x27___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1596_, 0, v_mvarId_1588_);
lean_closure_set(v___f_1596_, 1, v_e_1589_);
lean_closure_set(v___f_1596_, 2, v_varName_x3f_1590_);
v___x_1597_ = l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2___redArg(v_mvarId_1588_, v___f_1596_, v_a_1591_, v_a_1592_, v_a_1593_, v_a_1594_);
return v___x_1597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeIndices_x27___boxed(lean_object* v_mvarId_1598_, lean_object* v_e_1599_, lean_object* v_varName_x3f_1600_, lean_object* v_a_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_){
_start:
{
lean_object* v_res_1606_; 
v_res_1606_ = l_Lean_Meta_generalizeIndices_x27(v_mvarId_1598_, v_e_1599_, v_varName_x3f_1600_, v_a_1601_, v_a_1602_, v_a_1603_, v_a_1604_);
lean_dec(v_a_1604_);
lean_dec_ref(v_a_1603_);
lean_dec(v_a_1602_);
lean_dec_ref(v_a_1601_);
return v_res_1606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeIndices___lam__0(lean_object* v_fvarId_1607_, lean_object* v_mvarId_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_){
_start:
{
lean_object* v___x_1614_; 
v___x_1614_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_1607_, v___y_1609_, v___y_1611_, v___y_1612_);
if (lean_obj_tag(v___x_1614_) == 0)
{
lean_object* v_a_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; 
v_a_1615_ = lean_ctor_get(v___x_1614_, 0);
lean_inc_n(v_a_1615_, 2);
lean_dec_ref_known(v___x_1614_, 1);
v___x_1616_ = l_Lean_LocalDecl_toExpr(v_a_1615_);
v___x_1617_ = l_Lean_LocalDecl_userName(v_a_1615_);
lean_dec(v_a_1615_);
v___x_1618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1618_, 0, v___x_1617_);
v___x_1619_ = l_Lean_Meta_generalizeIndices_x27(v_mvarId_1608_, v___x_1616_, v___x_1618_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_);
return v___x_1619_;
}
else
{
lean_object* v_a_1620_; lean_object* v___x_1622_; uint8_t v_isShared_1623_; uint8_t v_isSharedCheck_1627_; 
lean_dec(v_mvarId_1608_);
v_a_1620_ = lean_ctor_get(v___x_1614_, 0);
v_isSharedCheck_1627_ = !lean_is_exclusive(v___x_1614_);
if (v_isSharedCheck_1627_ == 0)
{
v___x_1622_ = v___x_1614_;
v_isShared_1623_ = v_isSharedCheck_1627_;
goto v_resetjp_1621_;
}
else
{
lean_inc(v_a_1620_);
lean_dec(v___x_1614_);
v___x_1622_ = lean_box(0);
v_isShared_1623_ = v_isSharedCheck_1627_;
goto v_resetjp_1621_;
}
v_resetjp_1621_:
{
lean_object* v___x_1625_; 
if (v_isShared_1623_ == 0)
{
v___x_1625_ = v___x_1622_;
goto v_reusejp_1624_;
}
else
{
lean_object* v_reuseFailAlloc_1626_; 
v_reuseFailAlloc_1626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1626_, 0, v_a_1620_);
v___x_1625_ = v_reuseFailAlloc_1626_;
goto v_reusejp_1624_;
}
v_reusejp_1624_:
{
return v___x_1625_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeIndices___lam__0___boxed(lean_object* v_fvarId_1628_, lean_object* v_mvarId_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_){
_start:
{
lean_object* v_res_1635_; 
v_res_1635_ = l_Lean_Meta_generalizeIndices___lam__0(v_fvarId_1628_, v_mvarId_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_);
lean_dec(v___y_1633_);
lean_dec_ref(v___y_1632_);
lean_dec(v___y_1631_);
lean_dec_ref(v___y_1630_);
return v_res_1635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeIndices(lean_object* v_mvarId_1636_, lean_object* v_fvarId_1637_, lean_object* v_a_1638_, lean_object* v_a_1639_, lean_object* v_a_1640_, lean_object* v_a_1641_){
_start:
{
lean_object* v___f_1643_; lean_object* v___x_1644_; 
lean_inc(v_mvarId_1636_);
v___f_1643_ = lean_alloc_closure((void*)(l_Lean_Meta_generalizeIndices___lam__0___boxed), 7, 2);
lean_closure_set(v___f_1643_, 0, v_fvarId_1637_);
lean_closure_set(v___f_1643_, 1, v_mvarId_1636_);
v___x_1644_ = l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2___redArg(v_mvarId_1636_, v___f_1643_, v_a_1638_, v_a_1639_, v_a_1640_, v_a_1641_);
return v___x_1644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeIndices___boxed(lean_object* v_mvarId_1645_, lean_object* v_fvarId_1646_, lean_object* v_a_1647_, lean_object* v_a_1648_, lean_object* v_a_1649_, lean_object* v_a_1650_, lean_object* v_a_1651_){
_start:
{
lean_object* v_res_1652_; 
v_res_1652_ = l_Lean_Meta_generalizeIndices(v_mvarId_1645_, v_fvarId_1646_, v_a_1647_, v_a_1648_, v_a_1649_, v_a_1650_);
lean_dec(v_a_1650_);
lean_dec_ref(v_a_1649_);
lean_dec(v_a_1648_);
lean_dec_ref(v_a_1647_);
return v_res_1652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0___redArg(lean_object* v___x_1654_, lean_object* v_a_1655_, lean_object* v_x_1656_, lean_object* v_x_1657_, lean_object* v_x_1658_, lean_object* v___y_1659_){
_start:
{
if (lean_obj_tag(v_x_1656_) == 5)
{
lean_object* v_fn_1664_; lean_object* v_arg_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; 
v_fn_1664_ = lean_ctor_get(v_x_1656_, 0);
lean_inc_ref(v_fn_1664_);
v_arg_1665_ = lean_ctor_get(v_x_1656_, 1);
lean_inc_ref(v_arg_1665_);
lean_dec_ref_known(v_x_1656_, 2);
v___x_1666_ = lean_array_set(v_x_1657_, v_x_1658_, v_arg_1665_);
v___x_1667_ = lean_unsigned_to_nat(1u);
v___x_1668_ = lean_nat_sub(v_x_1658_, v___x_1667_);
lean_dec(v_x_1658_);
v_x_1656_ = v_fn_1664_;
v_x_1657_ = v___x_1666_;
v_x_1658_ = v___x_1668_;
goto _start;
}
else
{
lean_dec(v_x_1658_);
if (lean_obj_tag(v_x_1656_) == 4)
{
lean_object* v_declName_1670_; uint8_t v___x_1671_; uint8_t v___x_1672_; lean_object* v___x_1673_; lean_object* v_env_1674_; lean_object* v___x_1675_; 
v_declName_1670_ = lean_ctor_get(v_x_1656_, 0);
v___x_1671_ = 0;
v___x_1672_ = 1;
v___x_1673_ = lean_st_ref_get(v___y_1659_);
v_env_1674_ = lean_ctor_get(v___x_1673_, 0);
lean_inc_ref(v_env_1674_);
lean_dec(v___x_1673_);
lean_inc(v_declName_1670_);
v___x_1675_ = l_Lean_Environment_find_x3f(v_env_1674_, v_declName_1670_, v___x_1671_);
if (lean_obj_tag(v___x_1675_) == 0)
{
lean_dec_ref_known(v_x_1656_, 2);
lean_dec_ref(v_x_1657_);
lean_dec_ref(v_a_1655_);
lean_dec_ref(v___x_1654_);
goto v___jp_1661_;
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
v___x_1688_ = lean_array_get_size(v_x_1657_);
v___x_1689_ = lean_nat_add(v_numIndices_1686_, v_numParams_1685_);
v___x_1690_ = lean_nat_dec_eq(v___x_1688_, v___x_1689_);
lean_dec(v___x_1689_);
if (v___x_1690_ == 0)
{
lean_object* v___x_1691_; lean_object* v___x_1693_; 
lean_dec_ref(v_val_1680_);
lean_del_object(v___x_1678_);
lean_dec_ref_known(v_x_1656_, 2);
lean_dec_ref(v_x_1657_);
lean_dec_ref(v_a_1655_);
lean_dec_ref(v___x_1654_);
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
v___x_1698_ = l_Lean_Environment_contains(v___x_1654_, v___x_1697_, v___x_1672_);
if (v___x_1698_ == 0)
{
lean_object* v___x_1699_; lean_object* v___x_1701_; 
lean_dec_ref(v_val_1680_);
lean_del_object(v___x_1678_);
lean_dec_ref_known(v_x_1656_, 2);
lean_dec_ref(v_x_1657_);
lean_dec_ref(v_a_1655_);
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
v___x_1705_ = l_Array_extract___redArg(v_x_1657_, v___x_1704_, v___x_1688_);
v___x_1706_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1706_, 0, v_val_1680_);
lean_ctor_set(v___x_1706_, 1, v___x_1703_);
lean_ctor_set(v___x_1706_, 2, v_a_1655_);
lean_ctor_set(v___x_1706_, 3, v_x_1656_);
lean_ctor_set(v___x_1706_, 4, v_x_1657_);
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
lean_dec_ref_known(v_x_1656_, 2);
lean_dec_ref(v_x_1657_);
lean_dec_ref(v_a_1655_);
lean_dec_ref(v___x_1654_);
goto v___jp_1661_;
}
}
}
}
else
{
lean_dec_ref(v_x_1657_);
lean_dec_ref(v_x_1656_);
lean_dec_ref(v_a_1655_);
lean_dec_ref(v___x_1654_);
goto v___jp_1661_;
}
}
v___jp_1661_:
{
lean_object* v___x_1662_; lean_object* v___x_1663_; 
v___x_1662_ = lean_box(0);
v___x_1663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1663_, 0, v___x_1662_);
return v___x_1663_;
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
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5(lean_object* v___x_1831_, lean_object* v_as_1832_, size_t v_i_1833_, size_t v_stop_1834_){
_start:
{
uint8_t v___x_1835_; 
v___x_1835_ = lean_usize_dec_eq(v_i_1833_, v_stop_1834_);
if (v___x_1835_ == 0)
{
uint8_t v___x_1836_; lean_object* v___x_1837_; uint8_t v___x_1838_; 
v___x_1836_ = 1;
v___x_1837_ = lean_array_uget_borrowed(v_as_1832_, v_i_1833_);
v___x_1838_ = l_Lean_Expr_isFVar(v___x_1837_);
if (v___x_1838_ == 0)
{
return v___x_1836_;
}
else
{
lean_object* v___x_1839_; uint8_t v___x_1840_; 
v___x_1839_ = lean_unsigned_to_nat(0u);
v___x_1840_ = lean_nat_dec_eq(v___x_1831_, v___x_1839_);
if (v___x_1840_ == 0)
{
size_t v___x_1841_; size_t v___x_1842_; 
v___x_1841_ = ((size_t)1ULL);
v___x_1842_ = lean_usize_add(v_i_1833_, v___x_1841_);
v_i_1833_ = v___x_1842_;
goto _start;
}
else
{
return v___x_1836_;
}
}
}
else
{
uint8_t v___x_1844_; 
v___x_1844_ = 0;
return v___x_1844_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5___boxed(lean_object* v___x_1845_, lean_object* v_as_1846_, lean_object* v_i_1847_, lean_object* v_stop_1848_){
_start:
{
size_t v_i_boxed_1849_; size_t v_stop_boxed_1850_; uint8_t v_res_1851_; lean_object* v_r_1852_; 
v_i_boxed_1849_ = lean_unbox_usize(v_i_1847_);
lean_dec(v_i_1847_);
v_stop_boxed_1850_ = lean_unbox_usize(v_stop_1848_);
lean_dec(v_stop_1848_);
v_res_1851_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5(v___x_1845_, v_as_1846_, v_i_boxed_1849_, v_stop_boxed_1850_);
lean_dec_ref(v_as_1846_);
lean_dec(v___x_1845_);
v_r_1852_ = lean_box(v_res_1851_);
return v_r_1852_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__2(lean_object* v_fvarId_1853_, uint8_t v___x_1854_, lean_object* v_as_1855_, size_t v_i_1856_, size_t v_stop_1857_){
_start:
{
uint8_t v___x_1858_; 
v___x_1858_ = lean_usize_dec_eq(v_i_1856_, v_stop_1857_);
if (v___x_1858_ == 0)
{
uint8_t v___x_1859_; uint8_t v___y_1861_; lean_object* v___x_1865_; lean_object* v___x_1866_; uint8_t v___x_1867_; 
v___x_1859_ = 1;
v___x_1865_ = lean_array_uget_borrowed(v_as_1855_, v_i_1856_);
v___x_1866_ = l_Lean_Expr_fvarId_x21(v___x_1865_);
v___x_1867_ = l_Lean_instBEqFVarId_beq(v___x_1866_, v_fvarId_1853_);
lean_dec(v___x_1866_);
if (v___x_1867_ == 0)
{
v___y_1861_ = v___x_1854_;
goto v___jp_1860_;
}
else
{
if (v___x_1854_ == 0)
{
v___y_1861_ = v___x_1867_;
goto v___jp_1860_;
}
else
{
return v___x_1859_;
}
}
v___jp_1860_:
{
if (v___y_1861_ == 0)
{
size_t v___x_1862_; size_t v___x_1863_; 
v___x_1862_ = ((size_t)1ULL);
v___x_1863_ = lean_usize_add(v_i_1856_, v___x_1862_);
v_i_1856_ = v___x_1863_;
goto _start;
}
else
{
return v___x_1859_;
}
}
}
else
{
uint8_t v___x_1868_; 
v___x_1868_ = 0;
return v___x_1868_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__2___boxed(lean_object* v_fvarId_1869_, lean_object* v___x_1870_, lean_object* v_as_1871_, lean_object* v_i_1872_, lean_object* v_stop_1873_){
_start:
{
uint8_t v___x_7575__boxed_1874_; size_t v_i_boxed_1875_; size_t v_stop_boxed_1876_; uint8_t v_res_1877_; lean_object* v_r_1878_; 
v___x_7575__boxed_1874_ = lean_unbox(v___x_1870_);
v_i_boxed_1875_ = lean_unbox_usize(v_i_1872_);
lean_dec(v_i_1872_);
v_stop_boxed_1876_ = lean_unbox_usize(v_stop_1873_);
lean_dec(v_stop_1873_);
v_res_1877_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__2(v_fvarId_1869_, v___x_7575__boxed_1874_, v_as_1871_, v_i_boxed_1875_, v_stop_boxed_1876_);
lean_dec_ref(v_as_1871_);
lean_dec(v_fvarId_1869_);
v_r_1878_ = lean_box(v_res_1877_);
return v_r_1878_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___lam__1(lean_object* v___x_1879_, lean_object* v___x_1880_, uint8_t v___x_1881_, lean_object* v___x_1882_, lean_object* v_fvarId_1883_){
_start:
{
uint8_t v___x_1884_; lean_object* v___y_1886_; 
v___x_1884_ = lean_nat_dec_lt(v___x_1879_, v___x_1880_);
if (v___x_1884_ == 0)
{
uint8_t v___x_1891_; 
lean_dec(v___x_1880_);
v___x_1891_ = 1;
return v___x_1891_;
}
else
{
lean_object* v___x_1892_; uint8_t v___x_1893_; 
v___x_1892_ = lean_array_get_size(v___x_1882_);
v___x_1893_ = lean_nat_dec_le(v___x_1880_, v___x_1892_);
if (v___x_1893_ == 0)
{
lean_dec(v___x_1880_);
v___y_1886_ = v___x_1892_;
goto v___jp_1885_;
}
else
{
v___y_1886_ = v___x_1880_;
goto v___jp_1885_;
}
}
v___jp_1885_:
{
uint8_t v___x_1887_; 
v___x_1887_ = lean_nat_dec_lt(v___x_1879_, v___y_1886_);
if (v___x_1887_ == 0)
{
lean_dec(v___y_1886_);
return v___x_1884_;
}
else
{
size_t v___x_1888_; size_t v___x_1889_; uint8_t v___x_1890_; 
v___x_1888_ = ((size_t)0ULL);
v___x_1889_ = lean_usize_of_nat(v___y_1886_);
lean_dec(v___y_1886_);
v___x_1890_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__2(v_fvarId_1883_, v___x_1881_, v___x_1882_, v___x_1888_, v___x_1889_);
if (v___x_1890_ == 0)
{
return v___x_1887_;
}
else
{
return v___x_1881_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___lam__1___boxed(lean_object* v___x_1894_, lean_object* v___x_1895_, lean_object* v___x_1896_, lean_object* v___x_1897_, lean_object* v_fvarId_1898_){
_start:
{
uint8_t v___x_7602__boxed_1899_; uint8_t v_res_1900_; lean_object* v_r_1901_; 
v___x_7602__boxed_1899_ = lean_unbox(v___x_1896_);
v_res_1900_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___lam__1(v___x_1894_, v___x_1895_, v___x_7602__boxed_1899_, v___x_1897_, v_fvarId_1898_);
lean_dec(v_fvarId_1898_);
lean_dec_ref(v___x_1897_);
lean_dec(v___x_1894_);
v_r_1901_ = lean_box(v_res_1900_);
return v_r_1901_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__3(lean_object* v___x_1902_, lean_object* v_as_1903_, size_t v_i_1904_, size_t v_stop_1905_){
_start:
{
uint8_t v___x_1906_; 
v___x_1906_ = lean_usize_dec_eq(v_i_1904_, v_stop_1905_);
if (v___x_1906_ == 0)
{
lean_object* v___x_1907_; lean_object* v___x_1908_; uint8_t v___x_1909_; 
v___x_1907_ = lean_array_uget_borrowed(v_as_1903_, v_i_1904_);
v___x_1908_ = l_Lean_Expr_fvarId_x21(v___x_1907_);
v___x_1909_ = l_Lean_instBEqFVarId_beq(v___x_1902_, v___x_1908_);
lean_dec(v___x_1908_);
if (v___x_1909_ == 0)
{
size_t v___x_1910_; size_t v___x_1911_; 
v___x_1910_ = ((size_t)1ULL);
v___x_1911_ = lean_usize_add(v_i_1904_, v___x_1910_);
v_i_1904_ = v___x_1911_;
goto _start;
}
else
{
return v___x_1909_;
}
}
else
{
uint8_t v___x_1913_; 
v___x_1913_ = 0;
return v___x_1913_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__3___boxed(lean_object* v___x_1914_, lean_object* v_as_1915_, lean_object* v_i_1916_, lean_object* v_stop_1917_){
_start:
{
size_t v_i_boxed_1918_; size_t v_stop_boxed_1919_; uint8_t v_res_1920_; lean_object* v_r_1921_; 
v_i_boxed_1918_ = lean_unbox_usize(v_i_1916_);
lean_dec(v_i_1916_);
v_stop_boxed_1919_ = lean_unbox_usize(v_stop_1917_);
lean_dec(v_stop_1917_);
v_res_1920_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__3(v___x_1914_, v_as_1915_, v_i_boxed_1918_, v_stop_boxed_1919_);
lean_dec_ref(v_as_1915_);
lean_dec(v___x_1914_);
v_r_1921_ = lean_box(v_res_1920_);
return v_r_1921_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___lam__0(uint8_t v___x_1922_, lean_object* v_x_1923_){
_start:
{
return v___x_1922_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___lam__0___boxed(lean_object* v___x_1924_, lean_object* v_x_1925_){
_start:
{
uint8_t v___x_7651__boxed_1926_; uint8_t v_res_1927_; lean_object* v_r_1928_; 
v___x_7651__boxed_1926_ = lean_unbox(v___x_1924_);
v_res_1927_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___lam__0(v___x_7651__boxed_1926_, v_x_1925_);
lean_dec(v_x_1925_);
v_r_1928_ = lean_box(v_res_1927_);
return v_r_1928_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; 
v___x_1929_ = lean_box(0);
v___x_1930_ = lean_unsigned_to_nat(16u);
v___x_1931_ = lean_mk_array(v___x_1930_, v___x_1929_);
return v___x_1931_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; 
v___x_1932_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__0);
v___x_1933_ = lean_unsigned_to_nat(0u);
v___x_1934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1934_, 0, v___x_1933_);
lean_ctor_set(v___x_1934_, 1, v___x_1932_);
return v___x_1934_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg(uint8_t v___x_1935_, lean_object* v___x_1936_, lean_object* v___x_1937_, lean_object* v_ctx_1938_, lean_object* v_as_1939_, size_t v_i_1940_, size_t v_stop_1941_, lean_object* v___y_1942_){
_start:
{
uint8_t v___x_1944_; 
v___x_1944_ = lean_usize_dec_eq(v_i_1940_, v_stop_1941_);
if (v___x_1944_ == 0)
{
uint8_t v___x_1945_; uint8_t v_a_1947_; uint8_t v_a_1954_; uint8_t v_fst_1958_; lean_object* v_mctx_1959_; lean_object* v___y_1975_; uint8_t v_fst_1981_; lean_object* v_snd_1982_; lean_object* v___y_1999_; uint8_t v_fst_2004_; lean_object* v_mctx_2005_; lean_object* v___y_2021_; lean_object* v___x_2026_; 
v___x_1945_ = 1;
v___x_2026_ = lean_array_uget_borrowed(v_as_1939_, v_i_1940_);
if (lean_obj_tag(v___x_2026_) == 0)
{
v_a_1947_ = v___x_1935_;
goto v___jp_1946_;
}
else
{
lean_object* v_val_2027_; lean_object* v_majorDecl_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; uint8_t v___x_2031_; 
v_val_2027_ = lean_ctor_get(v___x_2026_, 0);
v_majorDecl_2028_ = lean_ctor_get(v_ctx_1938_, 2);
v___x_2029_ = l_Lean_LocalDecl_fvarId(v_val_2027_);
v___x_2030_ = l_Lean_LocalDecl_fvarId(v_majorDecl_2028_);
v___x_2031_ = l_Lean_instBEqFVarId_beq(v___x_2029_, v___x_2030_);
lean_dec(v___x_2030_);
if (v___x_2031_ == 0)
{
lean_object* v___x_2032_; lean_object* v___f_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___f_2036_; lean_object* v___y_2038_; uint8_t v_fst_2039_; lean_object* v_snd_2040_; lean_object* v___y_2046_; lean_object* v___y_2047_; lean_object* v___y_2082_; uint8_t v___x_2087_; 
v___x_2032_ = lean_box(v___x_1935_);
v___f_2033_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2033_, 0, v___x_2032_);
v___x_2034_ = lean_unsigned_to_nat(0u);
v___x_2035_ = lean_box(v___x_1935_);
lean_inc_ref(v___x_1936_);
lean_inc(v___x_1937_);
v___f_2036_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_2036_, 0, v___x_2034_);
lean_closure_set(v___f_2036_, 1, v___x_1937_);
lean_closure_set(v___f_2036_, 2, v___x_2035_);
lean_closure_set(v___f_2036_, 3, v___x_1936_);
v___x_2087_ = lean_nat_dec_lt(v___x_2034_, v___x_1937_);
if (v___x_2087_ == 0)
{
lean_dec(v___x_2029_);
goto v___jp_2051_;
}
else
{
lean_object* v___x_2088_; uint8_t v___x_2089_; 
v___x_2088_ = lean_array_get_size(v___x_1936_);
v___x_2089_ = lean_nat_dec_le(v___x_1937_, v___x_2088_);
if (v___x_2089_ == 0)
{
v___y_2082_ = v___x_2088_;
goto v___jp_2081_;
}
else
{
lean_inc(v___x_1937_);
v___y_2082_ = v___x_1937_;
goto v___jp_2081_;
}
}
v___jp_2037_:
{
if (v_fst_2039_ == 0)
{
uint8_t v___x_2041_; 
v___x_2041_ = l_Lean_Expr_hasFVar(v___y_2038_);
if (v___x_2041_ == 0)
{
uint8_t v___x_2042_; 
v___x_2042_ = l_Lean_Expr_hasMVar(v___y_2038_);
if (v___x_2042_ == 0)
{
lean_dec_ref(v___y_2038_);
lean_dec_ref(v___f_2036_);
lean_dec_ref(v___f_2033_);
v_fst_1981_ = v___x_2042_;
v_snd_1982_ = v_snd_2040_;
goto v___jp_1980_;
}
else
{
lean_object* v___x_2043_; 
v___x_2043_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_2036_, v___f_2033_, v___y_2038_, v_snd_2040_);
v___y_1999_ = v___x_2043_;
goto v___jp_1998_;
}
}
else
{
lean_object* v___x_2044_; 
v___x_2044_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_2036_, v___f_2033_, v___y_2038_, v_snd_2040_);
v___y_1999_ = v___x_2044_;
goto v___jp_1998_;
}
}
else
{
lean_dec_ref(v___y_2038_);
lean_dec_ref(v___f_2036_);
lean_dec_ref(v___f_2033_);
v_fst_1981_ = v_fst_2039_;
v_snd_1982_ = v_snd_2040_;
goto v___jp_1980_;
}
}
v___jp_2045_:
{
lean_object* v_fst_2048_; lean_object* v_snd_2049_; uint8_t v___x_2050_; 
v_fst_2048_ = lean_ctor_get(v___y_2047_, 0);
lean_inc(v_fst_2048_);
v_snd_2049_ = lean_ctor_get(v___y_2047_, 1);
lean_inc(v_snd_2049_);
lean_dec_ref(v___y_2047_);
v___x_2050_ = lean_unbox(v_fst_2048_);
lean_dec(v_fst_2048_);
v___y_2038_ = v___y_2046_;
v_fst_2039_ = v___x_2050_;
v_snd_2040_ = v_snd_2049_;
goto v___jp_2037_;
}
v___jp_2051_:
{
if (lean_obj_tag(v_val_2027_) == 0)
{
lean_object* v_type_2052_; lean_object* v___x_2053_; lean_object* v_mctx_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; uint8_t v___x_2057_; 
v_type_2052_ = lean_ctor_get(v_val_2027_, 3);
v___x_2053_ = lean_st_ref_get(v___y_1942_);
v_mctx_2054_ = lean_ctor_get(v___x_2053_, 0);
lean_inc_ref_n(v_mctx_2054_, 2);
lean_dec(v___x_2053_);
v___x_2055_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1);
v___x_2056_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2056_, 0, v___x_2055_);
lean_ctor_set(v___x_2056_, 1, v_mctx_2054_);
v___x_2057_ = l_Lean_Expr_hasFVar(v_type_2052_);
if (v___x_2057_ == 0)
{
uint8_t v___x_2058_; 
v___x_2058_ = l_Lean_Expr_hasMVar(v_type_2052_);
if (v___x_2058_ == 0)
{
lean_dec_ref_known(v___x_2056_, 2);
lean_dec_ref(v___f_2036_);
lean_dec_ref(v___f_2033_);
v_fst_2004_ = v___x_2058_;
v_mctx_2005_ = v_mctx_2054_;
goto v___jp_2003_;
}
else
{
lean_object* v___x_2059_; 
lean_dec_ref(v_mctx_2054_);
lean_inc_ref(v_type_2052_);
v___x_2059_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_2036_, v___f_2033_, v_type_2052_, v___x_2056_);
v___y_2021_ = v___x_2059_;
goto v___jp_2020_;
}
}
else
{
lean_object* v___x_2060_; 
lean_dec_ref(v_mctx_2054_);
lean_inc_ref(v_type_2052_);
v___x_2060_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_2036_, v___f_2033_, v_type_2052_, v___x_2056_);
v___y_2021_ = v___x_2060_;
goto v___jp_2020_;
}
}
else
{
uint8_t v_nondep_2061_; 
v_nondep_2061_ = lean_ctor_get_uint8(v_val_2027_, sizeof(void*)*5);
if (v_nondep_2061_ == 0)
{
lean_object* v_type_2062_; lean_object* v_value_2063_; lean_object* v___x_2064_; lean_object* v_mctx_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; uint8_t v___x_2068_; 
v_type_2062_ = lean_ctor_get(v_val_2027_, 3);
v_value_2063_ = lean_ctor_get(v_val_2027_, 4);
v___x_2064_ = lean_st_ref_get(v___y_1942_);
v_mctx_2065_ = lean_ctor_get(v___x_2064_, 0);
lean_inc_ref(v_mctx_2065_);
lean_dec(v___x_2064_);
v___x_2066_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1);
v___x_2067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2067_, 0, v___x_2066_);
lean_ctor_set(v___x_2067_, 1, v_mctx_2065_);
v___x_2068_ = l_Lean_Expr_hasFVar(v_type_2062_);
if (v___x_2068_ == 0)
{
uint8_t v___x_2069_; 
v___x_2069_ = l_Lean_Expr_hasMVar(v_type_2062_);
if (v___x_2069_ == 0)
{
lean_inc_ref(v_value_2063_);
v___y_2038_ = v_value_2063_;
v_fst_2039_ = v___x_2069_;
v_snd_2040_ = v___x_2067_;
goto v___jp_2037_;
}
else
{
lean_object* v___x_2070_; 
lean_inc_ref(v_type_2062_);
lean_inc_ref(v___f_2033_);
lean_inc_ref(v___f_2036_);
v___x_2070_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_2036_, v___f_2033_, v_type_2062_, v___x_2067_);
lean_inc_ref(v_value_2063_);
v___y_2046_ = v_value_2063_;
v___y_2047_ = v___x_2070_;
goto v___jp_2045_;
}
}
else
{
lean_object* v___x_2071_; 
lean_inc_ref(v_type_2062_);
lean_inc_ref(v___f_2033_);
lean_inc_ref(v___f_2036_);
v___x_2071_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_2036_, v___f_2033_, v_type_2062_, v___x_2067_);
lean_inc_ref(v_value_2063_);
v___y_2046_ = v_value_2063_;
v___y_2047_ = v___x_2071_;
goto v___jp_2045_;
}
}
else
{
lean_object* v_type_2072_; lean_object* v___x_2073_; lean_object* v_mctx_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; uint8_t v___x_2077_; 
v_type_2072_ = lean_ctor_get(v_val_2027_, 3);
v___x_2073_ = lean_st_ref_get(v___y_1942_);
v_mctx_2074_ = lean_ctor_get(v___x_2073_, 0);
lean_inc_ref_n(v_mctx_2074_, 2);
lean_dec(v___x_2073_);
v___x_2075_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1);
v___x_2076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2076_, 0, v___x_2075_);
lean_ctor_set(v___x_2076_, 1, v_mctx_2074_);
v___x_2077_ = l_Lean_Expr_hasFVar(v_type_2072_);
if (v___x_2077_ == 0)
{
uint8_t v___x_2078_; 
v___x_2078_ = l_Lean_Expr_hasMVar(v_type_2072_);
if (v___x_2078_ == 0)
{
lean_dec_ref_known(v___x_2076_, 2);
lean_dec_ref(v___f_2036_);
lean_dec_ref(v___f_2033_);
v_fst_1958_ = v___x_2078_;
v_mctx_1959_ = v_mctx_2074_;
goto v___jp_1957_;
}
else
{
lean_object* v___x_2079_; 
lean_dec_ref(v_mctx_2074_);
lean_inc_ref(v_type_2072_);
v___x_2079_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_2036_, v___f_2033_, v_type_2072_, v___x_2076_);
v___y_1975_ = v___x_2079_;
goto v___jp_1974_;
}
}
else
{
lean_object* v___x_2080_; 
lean_dec_ref(v_mctx_2074_);
lean_inc_ref(v_type_2072_);
v___x_2080_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_2036_, v___f_2033_, v_type_2072_, v___x_2076_);
v___y_1975_ = v___x_2080_;
goto v___jp_1974_;
}
}
}
}
v___jp_2081_:
{
uint8_t v___x_2083_; 
v___x_2083_ = lean_nat_dec_lt(v___x_2034_, v___y_2082_);
if (v___x_2083_ == 0)
{
lean_dec(v___y_2082_);
lean_dec(v___x_2029_);
goto v___jp_2051_;
}
else
{
size_t v___x_2084_; size_t v___x_2085_; uint8_t v___x_2086_; 
v___x_2084_ = ((size_t)0ULL);
v___x_2085_ = lean_usize_of_nat(v___y_2082_);
lean_dec(v___y_2082_);
v___x_2086_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__3(v___x_2029_, v___x_1936_, v___x_2084_, v___x_2085_);
lean_dec(v___x_2029_);
if (v___x_2086_ == 0)
{
goto v___jp_2051_;
}
else
{
lean_dec_ref(v___f_2036_);
lean_dec_ref(v___f_2033_);
v_a_1954_ = v___x_2086_;
goto v___jp_1953_;
}
}
}
}
else
{
lean_dec(v___x_2029_);
v_a_1954_ = v___x_2031_;
goto v___jp_1953_;
}
}
v___jp_1946_:
{
if (v_a_1947_ == 0)
{
size_t v___x_1948_; size_t v___x_1949_; 
v___x_1948_ = ((size_t)1ULL);
v___x_1949_ = lean_usize_add(v_i_1940_, v___x_1948_);
v_i_1940_ = v___x_1949_;
goto _start;
}
else
{
lean_object* v___x_1951_; lean_object* v___x_1952_; 
lean_dec(v___x_1937_);
lean_dec_ref(v___x_1936_);
v___x_1951_ = lean_box(v___x_1945_);
v___x_1952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1952_, 0, v___x_1951_);
return v___x_1952_;
}
}
v___jp_1953_:
{
if (v_a_1954_ == 0)
{
lean_object* v___x_1955_; lean_object* v___x_1956_; 
lean_dec(v___x_1937_);
lean_dec_ref(v___x_1936_);
v___x_1955_ = lean_box(v___x_1945_);
v___x_1956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1956_, 0, v___x_1955_);
return v___x_1956_;
}
else
{
v_a_1947_ = v___x_1935_;
goto v___jp_1946_;
}
}
v___jp_1957_:
{
lean_object* v___x_1960_; lean_object* v_cache_1961_; lean_object* v_zetaDeltaFVarIds_1962_; lean_object* v_postponed_1963_; lean_object* v_diag_1964_; lean_object* v___x_1966_; uint8_t v_isShared_1967_; uint8_t v_isSharedCheck_1972_; 
v___x_1960_ = lean_st_ref_take(v___y_1942_);
v_cache_1961_ = lean_ctor_get(v___x_1960_, 1);
v_zetaDeltaFVarIds_1962_ = lean_ctor_get(v___x_1960_, 2);
v_postponed_1963_ = lean_ctor_get(v___x_1960_, 3);
v_diag_1964_ = lean_ctor_get(v___x_1960_, 4);
v_isSharedCheck_1972_ = !lean_is_exclusive(v___x_1960_);
if (v_isSharedCheck_1972_ == 0)
{
lean_object* v_unused_1973_; 
v_unused_1973_ = lean_ctor_get(v___x_1960_, 0);
lean_dec(v_unused_1973_);
v___x_1966_ = v___x_1960_;
v_isShared_1967_ = v_isSharedCheck_1972_;
goto v_resetjp_1965_;
}
else
{
lean_inc(v_diag_1964_);
lean_inc(v_postponed_1963_);
lean_inc(v_zetaDeltaFVarIds_1962_);
lean_inc(v_cache_1961_);
lean_dec(v___x_1960_);
v___x_1966_ = lean_box(0);
v_isShared_1967_ = v_isSharedCheck_1972_;
goto v_resetjp_1965_;
}
v_resetjp_1965_:
{
lean_object* v___x_1969_; 
if (v_isShared_1967_ == 0)
{
lean_ctor_set(v___x_1966_, 0, v_mctx_1959_);
v___x_1969_ = v___x_1966_;
goto v_reusejp_1968_;
}
else
{
lean_object* v_reuseFailAlloc_1971_; 
v_reuseFailAlloc_1971_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1971_, 0, v_mctx_1959_);
lean_ctor_set(v_reuseFailAlloc_1971_, 1, v_cache_1961_);
lean_ctor_set(v_reuseFailAlloc_1971_, 2, v_zetaDeltaFVarIds_1962_);
lean_ctor_set(v_reuseFailAlloc_1971_, 3, v_postponed_1963_);
lean_ctor_set(v_reuseFailAlloc_1971_, 4, v_diag_1964_);
v___x_1969_ = v_reuseFailAlloc_1971_;
goto v_reusejp_1968_;
}
v_reusejp_1968_:
{
lean_object* v___x_1970_; 
v___x_1970_ = lean_st_ref_put(v___y_1942_, v___x_1969_);
v_a_1954_ = v_fst_1958_;
goto v___jp_1953_;
}
}
}
v___jp_1974_:
{
lean_object* v_snd_1976_; lean_object* v_fst_1977_; lean_object* v_mctx_1978_; uint8_t v___x_1979_; 
v_snd_1976_ = lean_ctor_get(v___y_1975_, 1);
lean_inc(v_snd_1976_);
v_fst_1977_ = lean_ctor_get(v___y_1975_, 0);
lean_inc(v_fst_1977_);
lean_dec_ref(v___y_1975_);
v_mctx_1978_ = lean_ctor_get(v_snd_1976_, 1);
lean_inc_ref(v_mctx_1978_);
lean_dec(v_snd_1976_);
v___x_1979_ = lean_unbox(v_fst_1977_);
lean_dec(v_fst_1977_);
v_fst_1958_ = v___x_1979_;
v_mctx_1959_ = v_mctx_1978_;
goto v___jp_1957_;
}
v___jp_1980_:
{
lean_object* v_mctx_1983_; lean_object* v___x_1984_; lean_object* v_cache_1985_; lean_object* v_zetaDeltaFVarIds_1986_; lean_object* v_postponed_1987_; lean_object* v_diag_1988_; lean_object* v___x_1990_; uint8_t v_isShared_1991_; uint8_t v_isSharedCheck_1996_; 
v_mctx_1983_ = lean_ctor_get(v_snd_1982_, 1);
lean_inc_ref(v_mctx_1983_);
lean_dec_ref(v_snd_1982_);
v___x_1984_ = lean_st_ref_take(v___y_1942_);
v_cache_1985_ = lean_ctor_get(v___x_1984_, 1);
v_zetaDeltaFVarIds_1986_ = lean_ctor_get(v___x_1984_, 2);
v_postponed_1987_ = lean_ctor_get(v___x_1984_, 3);
v_diag_1988_ = lean_ctor_get(v___x_1984_, 4);
v_isSharedCheck_1996_ = !lean_is_exclusive(v___x_1984_);
if (v_isSharedCheck_1996_ == 0)
{
lean_object* v_unused_1997_; 
v_unused_1997_ = lean_ctor_get(v___x_1984_, 0);
lean_dec(v_unused_1997_);
v___x_1990_ = v___x_1984_;
v_isShared_1991_ = v_isSharedCheck_1996_;
goto v_resetjp_1989_;
}
else
{
lean_inc(v_diag_1988_);
lean_inc(v_postponed_1987_);
lean_inc(v_zetaDeltaFVarIds_1986_);
lean_inc(v_cache_1985_);
lean_dec(v___x_1984_);
v___x_1990_ = lean_box(0);
v_isShared_1991_ = v_isSharedCheck_1996_;
goto v_resetjp_1989_;
}
v_resetjp_1989_:
{
lean_object* v___x_1993_; 
if (v_isShared_1991_ == 0)
{
lean_ctor_set(v___x_1990_, 0, v_mctx_1983_);
v___x_1993_ = v___x_1990_;
goto v_reusejp_1992_;
}
else
{
lean_object* v_reuseFailAlloc_1995_; 
v_reuseFailAlloc_1995_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1995_, 0, v_mctx_1983_);
lean_ctor_set(v_reuseFailAlloc_1995_, 1, v_cache_1985_);
lean_ctor_set(v_reuseFailAlloc_1995_, 2, v_zetaDeltaFVarIds_1986_);
lean_ctor_set(v_reuseFailAlloc_1995_, 3, v_postponed_1987_);
lean_ctor_set(v_reuseFailAlloc_1995_, 4, v_diag_1988_);
v___x_1993_ = v_reuseFailAlloc_1995_;
goto v_reusejp_1992_;
}
v_reusejp_1992_:
{
lean_object* v___x_1994_; 
v___x_1994_ = lean_st_ref_put(v___y_1942_, v___x_1993_);
v_a_1954_ = v_fst_1981_;
goto v___jp_1953_;
}
}
}
v___jp_1998_:
{
lean_object* v_fst_2000_; lean_object* v_snd_2001_; uint8_t v___x_2002_; 
v_fst_2000_ = lean_ctor_get(v___y_1999_, 0);
lean_inc(v_fst_2000_);
v_snd_2001_ = lean_ctor_get(v___y_1999_, 1);
lean_inc(v_snd_2001_);
lean_dec_ref(v___y_1999_);
v___x_2002_ = lean_unbox(v_fst_2000_);
lean_dec(v_fst_2000_);
v_fst_1981_ = v___x_2002_;
v_snd_1982_ = v_snd_2001_;
goto v___jp_1980_;
}
v___jp_2003_:
{
lean_object* v___x_2006_; lean_object* v_cache_2007_; lean_object* v_zetaDeltaFVarIds_2008_; lean_object* v_postponed_2009_; lean_object* v_diag_2010_; lean_object* v___x_2012_; uint8_t v_isShared_2013_; uint8_t v_isSharedCheck_2018_; 
v___x_2006_ = lean_st_ref_take(v___y_1942_);
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
v___x_2016_ = lean_st_ref_put(v___y_1942_, v___x_2015_);
v_a_1954_ = v_fst_2004_;
goto v___jp_1953_;
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
uint8_t v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; 
lean_dec(v___x_1937_);
lean_dec_ref(v___x_1936_);
v___x_2090_ = 0;
v___x_2091_ = lean_box(v___x_2090_);
v___x_2092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2092_, 0, v___x_2091_);
return v___x_2092_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___boxed(lean_object* v___x_2093_, lean_object* v___x_2094_, lean_object* v___x_2095_, lean_object* v_ctx_2096_, lean_object* v_as_2097_, lean_object* v_i_2098_, lean_object* v_stop_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_){
_start:
{
uint8_t v___x_7681__boxed_2102_; size_t v_i_boxed_2103_; size_t v_stop_boxed_2104_; lean_object* v_res_2105_; 
v___x_7681__boxed_2102_ = lean_unbox(v___x_2093_);
v_i_boxed_2103_ = lean_unbox_usize(v_i_2098_);
lean_dec(v_i_2098_);
v_stop_boxed_2104_ = lean_unbox_usize(v_stop_2099_);
lean_dec(v_stop_2099_);
v_res_2105_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg(v___x_7681__boxed_2102_, v___x_2094_, v___x_2095_, v_ctx_2096_, v_as_2097_, v_i_boxed_2103_, v_stop_boxed_2104_, v___y_2100_);
lean_dec(v___y_2100_);
lean_dec_ref(v_as_2097_);
lean_dec_ref(v_ctx_2096_);
return v_res_2105_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4(uint8_t v___x_2106_, lean_object* v___x_2107_, lean_object* v___x_2108_, lean_object* v_ctx_2109_, lean_object* v_x_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_){
_start:
{
if (lean_obj_tag(v_x_2110_) == 0)
{
lean_object* v_cs_2116_; lean_object* v___x_2118_; uint8_t v_isShared_2119_; uint8_t v_isSharedCheck_2134_; 
v_cs_2116_ = lean_ctor_get(v_x_2110_, 0);
v_isSharedCheck_2134_ = !lean_is_exclusive(v_x_2110_);
if (v_isSharedCheck_2134_ == 0)
{
v___x_2118_ = v_x_2110_;
v_isShared_2119_ = v_isSharedCheck_2134_;
goto v_resetjp_2117_;
}
else
{
lean_inc(v_cs_2116_);
lean_dec(v_x_2110_);
v___x_2118_ = lean_box(0);
v_isShared_2119_ = v_isSharedCheck_2134_;
goto v_resetjp_2117_;
}
v_resetjp_2117_:
{
lean_object* v___x_2120_; lean_object* v___x_2121_; uint8_t v___x_2122_; 
v___x_2120_ = lean_unsigned_to_nat(0u);
v___x_2121_ = lean_array_get_size(v_cs_2116_);
v___x_2122_ = lean_nat_dec_lt(v___x_2120_, v___x_2121_);
if (v___x_2122_ == 0)
{
lean_object* v___x_2123_; lean_object* v___x_2125_; 
lean_dec_ref(v_cs_2116_);
lean_dec(v___x_2108_);
lean_dec_ref(v___x_2107_);
v___x_2123_ = lean_box(v___x_2122_);
if (v_isShared_2119_ == 0)
{
lean_ctor_set(v___x_2118_, 0, v___x_2123_);
v___x_2125_ = v___x_2118_;
goto v_reusejp_2124_;
}
else
{
lean_object* v_reuseFailAlloc_2126_; 
v_reuseFailAlloc_2126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2126_, 0, v___x_2123_);
v___x_2125_ = v_reuseFailAlloc_2126_;
goto v_reusejp_2124_;
}
v_reusejp_2124_:
{
return v___x_2125_;
}
}
else
{
if (v___x_2122_ == 0)
{
lean_object* v___x_2127_; lean_object* v___x_2129_; 
lean_dec_ref(v_cs_2116_);
lean_dec(v___x_2108_);
lean_dec_ref(v___x_2107_);
v___x_2127_ = lean_box(v___x_2122_);
if (v_isShared_2119_ == 0)
{
lean_ctor_set(v___x_2118_, 0, v___x_2127_);
v___x_2129_ = v___x_2118_;
goto v_reusejp_2128_;
}
else
{
lean_object* v_reuseFailAlloc_2130_; 
v_reuseFailAlloc_2130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2130_, 0, v___x_2127_);
v___x_2129_ = v_reuseFailAlloc_2130_;
goto v_reusejp_2128_;
}
v_reusejp_2128_:
{
return v___x_2129_;
}
}
else
{
size_t v___x_2131_; size_t v___x_2132_; lean_object* v___x_2133_; 
lean_del_object(v___x_2118_);
v___x_2131_ = ((size_t)0ULL);
v___x_2132_ = lean_usize_of_nat(v___x_2121_);
v___x_2133_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4_spec__5(v___x_2106_, v___x_2107_, v___x_2108_, v_ctx_2109_, v_cs_2116_, v___x_2131_, v___x_2132_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_);
lean_dec_ref(v_cs_2116_);
return v___x_2133_;
}
}
}
}
else
{
lean_object* v_vs_2135_; lean_object* v___x_2137_; uint8_t v_isShared_2138_; uint8_t v_isSharedCheck_2153_; 
v_vs_2135_ = lean_ctor_get(v_x_2110_, 0);
v_isSharedCheck_2153_ = !lean_is_exclusive(v_x_2110_);
if (v_isSharedCheck_2153_ == 0)
{
v___x_2137_ = v_x_2110_;
v_isShared_2138_ = v_isSharedCheck_2153_;
goto v_resetjp_2136_;
}
else
{
lean_inc(v_vs_2135_);
lean_dec(v_x_2110_);
v___x_2137_ = lean_box(0);
v_isShared_2138_ = v_isSharedCheck_2153_;
goto v_resetjp_2136_;
}
v_resetjp_2136_:
{
lean_object* v___x_2139_; lean_object* v___x_2140_; uint8_t v___x_2141_; 
v___x_2139_ = lean_unsigned_to_nat(0u);
v___x_2140_ = lean_array_get_size(v_vs_2135_);
v___x_2141_ = lean_nat_dec_lt(v___x_2139_, v___x_2140_);
if (v___x_2141_ == 0)
{
lean_object* v___x_2142_; lean_object* v___x_2144_; 
lean_dec_ref(v_vs_2135_);
lean_dec(v___x_2108_);
lean_dec_ref(v___x_2107_);
v___x_2142_ = lean_box(v___x_2141_);
if (v_isShared_2138_ == 0)
{
lean_ctor_set_tag(v___x_2137_, 0);
lean_ctor_set(v___x_2137_, 0, v___x_2142_);
v___x_2144_ = v___x_2137_;
goto v_reusejp_2143_;
}
else
{
lean_object* v_reuseFailAlloc_2145_; 
v_reuseFailAlloc_2145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2145_, 0, v___x_2142_);
v___x_2144_ = v_reuseFailAlloc_2145_;
goto v_reusejp_2143_;
}
v_reusejp_2143_:
{
return v___x_2144_;
}
}
else
{
if (v___x_2141_ == 0)
{
lean_object* v___x_2146_; lean_object* v___x_2148_; 
lean_dec_ref(v_vs_2135_);
lean_dec(v___x_2108_);
lean_dec_ref(v___x_2107_);
v___x_2146_ = lean_box(v___x_2141_);
if (v_isShared_2138_ == 0)
{
lean_ctor_set_tag(v___x_2137_, 0);
lean_ctor_set(v___x_2137_, 0, v___x_2146_);
v___x_2148_ = v___x_2137_;
goto v_reusejp_2147_;
}
else
{
lean_object* v_reuseFailAlloc_2149_; 
v_reuseFailAlloc_2149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2149_, 0, v___x_2146_);
v___x_2148_ = v_reuseFailAlloc_2149_;
goto v_reusejp_2147_;
}
v_reusejp_2147_:
{
return v___x_2148_;
}
}
else
{
size_t v___x_2150_; size_t v___x_2151_; lean_object* v___x_2152_; 
lean_del_object(v___x_2137_);
v___x_2150_ = ((size_t)0ULL);
v___x_2151_ = lean_usize_of_nat(v___x_2140_);
v___x_2152_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg(v___x_2106_, v___x_2107_, v___x_2108_, v_ctx_2109_, v_vs_2135_, v___x_2150_, v___x_2151_, v___y_2112_);
lean_dec_ref(v_vs_2135_);
return v___x_2152_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4_spec__5(uint8_t v___x_2154_, lean_object* v___x_2155_, lean_object* v___x_2156_, lean_object* v_ctx_2157_, lean_object* v_as_2158_, size_t v_i_2159_, size_t v_stop_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_){
_start:
{
uint8_t v___x_2166_; 
v___x_2166_ = lean_usize_dec_eq(v_i_2159_, v_stop_2160_);
if (v___x_2166_ == 0)
{
uint8_t v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; 
v___x_2167_ = 1;
v___x_2168_ = lean_array_uget_borrowed(v_as_2158_, v_i_2159_);
lean_inc(v___x_2168_);
lean_inc(v___x_2156_);
lean_inc_ref(v___x_2155_);
v___x_2169_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4(v___x_2154_, v___x_2155_, v___x_2156_, v_ctx_2157_, v___x_2168_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_);
if (lean_obj_tag(v___x_2169_) == 0)
{
lean_object* v_a_2170_; lean_object* v___x_2172_; uint8_t v_isShared_2173_; uint8_t v_isSharedCheck_2182_; 
v_a_2170_ = lean_ctor_get(v___x_2169_, 0);
v_isSharedCheck_2182_ = !lean_is_exclusive(v___x_2169_);
if (v_isSharedCheck_2182_ == 0)
{
v___x_2172_ = v___x_2169_;
v_isShared_2173_ = v_isSharedCheck_2182_;
goto v_resetjp_2171_;
}
else
{
lean_inc(v_a_2170_);
lean_dec(v___x_2169_);
v___x_2172_ = lean_box(0);
v_isShared_2173_ = v_isSharedCheck_2182_;
goto v_resetjp_2171_;
}
v_resetjp_2171_:
{
uint8_t v___x_2174_; 
v___x_2174_ = lean_unbox(v_a_2170_);
lean_dec(v_a_2170_);
if (v___x_2174_ == 0)
{
size_t v___x_2175_; size_t v___x_2176_; 
lean_del_object(v___x_2172_);
v___x_2175_ = ((size_t)1ULL);
v___x_2176_ = lean_usize_add(v_i_2159_, v___x_2175_);
v_i_2159_ = v___x_2176_;
goto _start;
}
else
{
lean_object* v___x_2178_; lean_object* v___x_2180_; 
lean_dec(v___x_2156_);
lean_dec_ref(v___x_2155_);
v___x_2178_ = lean_box(v___x_2167_);
if (v_isShared_2173_ == 0)
{
lean_ctor_set(v___x_2172_, 0, v___x_2178_);
v___x_2180_ = v___x_2172_;
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
}
}
else
{
lean_dec(v___x_2156_);
lean_dec_ref(v___x_2155_);
return v___x_2169_;
}
}
else
{
uint8_t v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; 
lean_dec(v___x_2156_);
lean_dec_ref(v___x_2155_);
v___x_2183_ = 0;
v___x_2184_ = lean_box(v___x_2183_);
v___x_2185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2185_, 0, v___x_2184_);
return v___x_2185_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4_spec__5___boxed(lean_object* v___x_2186_, lean_object* v___x_2187_, lean_object* v___x_2188_, lean_object* v_ctx_2189_, lean_object* v_as_2190_, lean_object* v_i_2191_, lean_object* v_stop_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_){
_start:
{
uint8_t v___x_7976__boxed_2198_; size_t v_i_boxed_2199_; size_t v_stop_boxed_2200_; lean_object* v_res_2201_; 
v___x_7976__boxed_2198_ = lean_unbox(v___x_2186_);
v_i_boxed_2199_ = lean_unbox_usize(v_i_2191_);
lean_dec(v_i_2191_);
v_stop_boxed_2200_ = lean_unbox_usize(v_stop_2192_);
lean_dec(v_stop_2192_);
v_res_2201_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4_spec__5(v___x_7976__boxed_2198_, v___x_2187_, v___x_2188_, v_ctx_2189_, v_as_2190_, v_i_boxed_2199_, v_stop_boxed_2200_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_);
lean_dec(v___y_2196_);
lean_dec_ref(v___y_2195_);
lean_dec(v___y_2194_);
lean_dec_ref(v___y_2193_);
lean_dec_ref(v_as_2190_);
lean_dec_ref(v_ctx_2189_);
return v_res_2201_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4___boxed(lean_object* v___x_2202_, lean_object* v___x_2203_, lean_object* v___x_2204_, lean_object* v_ctx_2205_, lean_object* v_x_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_){
_start:
{
uint8_t v___x_7996__boxed_2212_; lean_object* v_res_2213_; 
v___x_7996__boxed_2212_ = lean_unbox(v___x_2202_);
v_res_2213_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4(v___x_7996__boxed_2212_, v___x_2203_, v___x_2204_, v_ctx_2205_, v_x_2206_, v___y_2207_, v___y_2208_, v___y_2209_, v___y_2210_);
lean_dec(v___y_2210_);
lean_dec_ref(v___y_2209_);
lean_dec(v___y_2208_);
lean_dec_ref(v___y_2207_);
lean_dec_ref(v_ctx_2205_);
return v_res_2213_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4(uint8_t v___x_2214_, lean_object* v___x_2215_, lean_object* v___x_2216_, lean_object* v_ctx_2217_, lean_object* v_t_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_){
_start:
{
lean_object* v_root_2224_; lean_object* v_tail_2225_; lean_object* v___x_2226_; 
v_root_2224_ = lean_ctor_get(v_t_2218_, 0);
lean_inc_ref(v_root_2224_);
v_tail_2225_ = lean_ctor_get(v_t_2218_, 1);
lean_inc_ref(v_tail_2225_);
lean_dec_ref(v_t_2218_);
lean_inc(v___x_2216_);
lean_inc_ref(v___x_2215_);
v___x_2226_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4(v___x_2214_, v___x_2215_, v___x_2216_, v_ctx_2217_, v_root_2224_, v___y_2219_, v___y_2220_, v___y_2221_, v___y_2222_);
if (lean_obj_tag(v___x_2226_) == 0)
{
lean_object* v_a_2227_; uint8_t v___x_2228_; 
v_a_2227_ = lean_ctor_get(v___x_2226_, 0);
lean_inc(v_a_2227_);
v___x_2228_ = lean_unbox(v_a_2227_);
lean_dec(v_a_2227_);
if (v___x_2228_ == 0)
{
lean_object* v___x_2230_; uint8_t v_isShared_2231_; uint8_t v_isSharedCheck_2246_; 
v_isSharedCheck_2246_ = !lean_is_exclusive(v___x_2226_);
if (v_isSharedCheck_2246_ == 0)
{
lean_object* v_unused_2247_; 
v_unused_2247_ = lean_ctor_get(v___x_2226_, 0);
lean_dec(v_unused_2247_);
v___x_2230_ = v___x_2226_;
v_isShared_2231_ = v_isSharedCheck_2246_;
goto v_resetjp_2229_;
}
else
{
lean_dec(v___x_2226_);
v___x_2230_ = lean_box(0);
v_isShared_2231_ = v_isSharedCheck_2246_;
goto v_resetjp_2229_;
}
v_resetjp_2229_:
{
lean_object* v___x_2232_; lean_object* v___x_2233_; uint8_t v___x_2234_; 
v___x_2232_ = lean_unsigned_to_nat(0u);
v___x_2233_ = lean_array_get_size(v_tail_2225_);
v___x_2234_ = lean_nat_dec_lt(v___x_2232_, v___x_2233_);
if (v___x_2234_ == 0)
{
lean_object* v___x_2235_; lean_object* v___x_2237_; 
lean_dec_ref(v_tail_2225_);
lean_dec(v___x_2216_);
lean_dec_ref(v___x_2215_);
v___x_2235_ = lean_box(v___x_2234_);
if (v_isShared_2231_ == 0)
{
lean_ctor_set(v___x_2230_, 0, v___x_2235_);
v___x_2237_ = v___x_2230_;
goto v_reusejp_2236_;
}
else
{
lean_object* v_reuseFailAlloc_2238_; 
v_reuseFailAlloc_2238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2238_, 0, v___x_2235_);
v___x_2237_ = v_reuseFailAlloc_2238_;
goto v_reusejp_2236_;
}
v_reusejp_2236_:
{
return v___x_2237_;
}
}
else
{
if (v___x_2234_ == 0)
{
lean_object* v___x_2239_; lean_object* v___x_2241_; 
lean_dec_ref(v_tail_2225_);
lean_dec(v___x_2216_);
lean_dec_ref(v___x_2215_);
v___x_2239_ = lean_box(v___x_2234_);
if (v_isShared_2231_ == 0)
{
lean_ctor_set(v___x_2230_, 0, v___x_2239_);
v___x_2241_ = v___x_2230_;
goto v_reusejp_2240_;
}
else
{
lean_object* v_reuseFailAlloc_2242_; 
v_reuseFailAlloc_2242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2242_, 0, v___x_2239_);
v___x_2241_ = v_reuseFailAlloc_2242_;
goto v_reusejp_2240_;
}
v_reusejp_2240_:
{
return v___x_2241_;
}
}
else
{
size_t v___x_2243_; size_t v___x_2244_; lean_object* v___x_2245_; 
lean_del_object(v___x_2230_);
v___x_2243_ = ((size_t)0ULL);
v___x_2244_ = lean_usize_of_nat(v___x_2233_);
v___x_2245_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg(v___x_2214_, v___x_2215_, v___x_2216_, v_ctx_2217_, v_tail_2225_, v___x_2243_, v___x_2244_, v___y_2220_);
lean_dec_ref(v_tail_2225_);
return v___x_2245_;
}
}
}
}
else
{
lean_dec_ref(v_tail_2225_);
lean_dec(v___x_2216_);
lean_dec_ref(v___x_2215_);
return v___x_2226_;
}
}
else
{
lean_dec_ref(v_tail_2225_);
lean_dec(v___x_2216_);
lean_dec_ref(v___x_2215_);
return v___x_2226_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4___boxed(lean_object* v___x_2248_, lean_object* v___x_2249_, lean_object* v___x_2250_, lean_object* v_ctx_2251_, lean_object* v_t_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_){
_start:
{
uint8_t v___x_8144__boxed_2258_; lean_object* v_res_2259_; 
v___x_8144__boxed_2258_ = lean_unbox(v___x_2248_);
v_res_2259_ = l_Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4(v___x_8144__boxed_2258_, v___x_2249_, v___x_2250_, v_ctx_2251_, v_t_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_);
lean_dec(v___y_2256_);
lean_dec_ref(v___y_2255_);
lean_dec(v___y_2254_);
lean_dec_ref(v___y_2253_);
lean_dec_ref(v_ctx_2251_);
return v_res_2259_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices(lean_object* v_ctx_2260_, lean_object* v_a_2261_, lean_object* v_a_2262_, lean_object* v_a_2263_, lean_object* v_a_2264_){
_start:
{
lean_object* v_majorTypeIndices_2266_; lean_object* v___x_2267_; uint8_t v___y_2269_; lean_object* v___x_2291_; uint8_t v___x_2292_; 
v_majorTypeIndices_2266_ = lean_ctor_get(v_ctx_2260_, 5);
lean_inc_ref(v_majorTypeIndices_2266_);
v___x_2267_ = lean_array_get_size(v_majorTypeIndices_2266_);
v___x_2291_ = lean_unsigned_to_nat(0u);
v___x_2292_ = lean_nat_dec_eq(v___x_2267_, v___x_2291_);
if (v___x_2292_ == 0)
{
uint8_t v___x_2293_; 
v___x_2293_ = lean_nat_dec_lt(v___x_2291_, v___x_2267_);
if (v___x_2293_ == 0)
{
v___y_2269_ = v___x_2293_;
goto v___jp_2268_;
}
else
{
if (v___x_2293_ == 0)
{
v___y_2269_ = v___x_2293_;
goto v___jp_2268_;
}
else
{
size_t v___x_2294_; size_t v___x_2295_; uint8_t v___x_2296_; 
v___x_2294_ = ((size_t)0ULL);
v___x_2295_ = lean_usize_of_nat(v___x_2267_);
v___x_2296_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5(v___x_2267_, v_majorTypeIndices_2266_, v___x_2294_, v___x_2295_);
if (v___x_2296_ == 0)
{
v___y_2269_ = v___x_2296_;
goto v___jp_2268_;
}
else
{
lean_object* v___x_2297_; lean_object* v___x_2298_; 
lean_dec_ref(v_majorTypeIndices_2266_);
lean_dec_ref(v_ctx_2260_);
v___x_2297_ = lean_box(v___x_2292_);
v___x_2298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2298_, 0, v___x_2297_);
return v___x_2298_;
}
}
}
}
else
{
lean_object* v___x_2299_; lean_object* v___x_2300_; 
lean_dec_ref(v_majorTypeIndices_2266_);
lean_dec_ref(v_ctx_2260_);
v___x_2299_ = lean_box(v___x_2292_);
v___x_2300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2300_, 0, v___x_2299_);
return v___x_2300_;
}
v___jp_2268_:
{
uint8_t v___x_2270_; 
v___x_2270_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1___redArg(v_majorTypeIndices_2266_, v___x_2267_, v___x_2267_);
if (v___x_2270_ == 0)
{
lean_object* v_lctx_2271_; lean_object* v_decls_2272_; lean_object* v___x_2273_; 
v_lctx_2271_ = lean_ctor_get(v_a_2261_, 2);
v_decls_2272_ = lean_ctor_get(v_lctx_2271_, 1);
lean_inc_ref(v_decls_2272_);
v___x_2273_ = l_Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4(v___x_2270_, v_majorTypeIndices_2266_, v___x_2267_, v_ctx_2260_, v_decls_2272_, v_a_2261_, v_a_2262_, v_a_2263_, v_a_2264_);
lean_dec_ref(v_ctx_2260_);
if (lean_obj_tag(v___x_2273_) == 0)
{
lean_object* v_a_2274_; lean_object* v___x_2276_; uint8_t v_isShared_2277_; uint8_t v_isSharedCheck_2288_; 
v_a_2274_ = lean_ctor_get(v___x_2273_, 0);
v_isSharedCheck_2288_ = !lean_is_exclusive(v___x_2273_);
if (v_isSharedCheck_2288_ == 0)
{
v___x_2276_ = v___x_2273_;
v_isShared_2277_ = v_isSharedCheck_2288_;
goto v_resetjp_2275_;
}
else
{
lean_inc(v_a_2274_);
lean_dec(v___x_2273_);
v___x_2276_ = lean_box(0);
v_isShared_2277_ = v_isSharedCheck_2288_;
goto v_resetjp_2275_;
}
v_resetjp_2275_:
{
uint8_t v___x_2278_; 
v___x_2278_ = lean_unbox(v_a_2274_);
lean_dec(v_a_2274_);
if (v___x_2278_ == 0)
{
uint8_t v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2282_; 
v___x_2279_ = 1;
v___x_2280_ = lean_box(v___x_2279_);
if (v_isShared_2277_ == 0)
{
lean_ctor_set(v___x_2276_, 0, v___x_2280_);
v___x_2282_ = v___x_2276_;
goto v_reusejp_2281_;
}
else
{
lean_object* v_reuseFailAlloc_2283_; 
v_reuseFailAlloc_2283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2283_, 0, v___x_2280_);
v___x_2282_ = v_reuseFailAlloc_2283_;
goto v_reusejp_2281_;
}
v_reusejp_2281_:
{
return v___x_2282_;
}
}
else
{
lean_object* v___x_2284_; lean_object* v___x_2286_; 
v___x_2284_ = lean_box(v___x_2270_);
if (v_isShared_2277_ == 0)
{
lean_ctor_set(v___x_2276_, 0, v___x_2284_);
v___x_2286_ = v___x_2276_;
goto v_reusejp_2285_;
}
else
{
lean_object* v_reuseFailAlloc_2287_; 
v_reuseFailAlloc_2287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2287_, 0, v___x_2284_);
v___x_2286_ = v_reuseFailAlloc_2287_;
goto v_reusejp_2285_;
}
v_reusejp_2285_:
{
return v___x_2286_;
}
}
}
}
else
{
return v___x_2273_;
}
}
else
{
lean_object* v___x_2289_; lean_object* v___x_2290_; 
lean_dec_ref(v_majorTypeIndices_2266_);
lean_dec_ref(v_ctx_2260_);
v___x_2289_ = lean_box(v___y_2269_);
v___x_2290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2290_, 0, v___x_2289_);
return v___x_2290_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___boxed(lean_object* v_ctx_2301_, lean_object* v_a_2302_, lean_object* v_a_2303_, lean_object* v_a_2304_, lean_object* v_a_2305_, lean_object* v_a_2306_){
_start:
{
lean_object* v_res_2307_; 
v_res_2307_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices(v_ctx_2301_, v_a_2302_, v_a_2303_, v_a_2304_, v_a_2305_);
lean_dec(v_a_2305_);
lean_dec_ref(v_a_2304_);
lean_dec(v_a_2303_);
lean_dec_ref(v_a_2302_);
return v_res_2307_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0(lean_object* v___x_2308_, lean_object* v_i_2309_, lean_object* v_n_2310_, lean_object* v_i_2311_, lean_object* v_a_2312_){
_start:
{
uint8_t v___x_2313_; 
v___x_2313_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0___redArg(v___x_2308_, v_i_2309_, v_n_2310_, v_i_2311_);
return v___x_2313_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0___boxed(lean_object* v___x_2314_, lean_object* v_i_2315_, lean_object* v_n_2316_, lean_object* v_i_2317_, lean_object* v_a_2318_){
_start:
{
uint8_t v_res_2319_; lean_object* v_r_2320_; 
v_res_2319_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0(v___x_2314_, v_i_2315_, v_n_2316_, v_i_2317_, v_a_2318_);
lean_dec(v_n_2316_);
lean_dec(v_i_2315_);
lean_dec_ref(v___x_2314_);
v_r_2320_ = lean_box(v_res_2319_);
return v_r_2320_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1(lean_object* v___x_2321_, lean_object* v_n_2322_, lean_object* v_i_2323_, lean_object* v_a_2324_){
_start:
{
uint8_t v___x_2325_; 
v___x_2325_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1___redArg(v___x_2321_, v_n_2322_, v_i_2323_);
return v___x_2325_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1___boxed(lean_object* v___x_2326_, lean_object* v_n_2327_, lean_object* v_i_2328_, lean_object* v_a_2329_){
_start:
{
uint8_t v_res_2330_; lean_object* v_r_2331_; 
v_res_2330_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1(v___x_2326_, v_n_2327_, v_i_2328_, v_a_2329_);
lean_dec(v_n_2327_);
lean_dec_ref(v___x_2326_);
v_r_2331_ = lean_box(v_res_2330_);
return v_r_2331_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5(uint8_t v___x_2332_, lean_object* v___x_2333_, lean_object* v___x_2334_, lean_object* v_ctx_2335_, lean_object* v_as_2336_, size_t v_i_2337_, size_t v_stop_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_){
_start:
{
lean_object* v___x_2344_; 
v___x_2344_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg(v___x_2332_, v___x_2333_, v___x_2334_, v_ctx_2335_, v_as_2336_, v_i_2337_, v_stop_2338_, v___y_2340_);
return v___x_2344_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___boxed(lean_object* v___x_2345_, lean_object* v___x_2346_, lean_object* v___x_2347_, lean_object* v_ctx_2348_, lean_object* v_as_2349_, lean_object* v_i_2350_, lean_object* v_stop_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_){
_start:
{
uint8_t v___x_8297__boxed_2357_; size_t v_i_boxed_2358_; size_t v_stop_boxed_2359_; lean_object* v_res_2360_; 
v___x_8297__boxed_2357_ = lean_unbox(v___x_2345_);
v_i_boxed_2358_ = lean_unbox_usize(v_i_2350_);
lean_dec(v_i_2350_);
v_stop_boxed_2359_ = lean_unbox_usize(v_stop_2351_);
lean_dec(v_stop_2351_);
v_res_2360_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5(v___x_8297__boxed_2357_, v___x_2346_, v___x_2347_, v_ctx_2348_, v_as_2349_, v_i_boxed_2358_, v_stop_boxed_2359_, v___y_2352_, v___y_2353_, v___y_2354_, v___y_2355_);
lean_dec(v___y_2355_);
lean_dec_ref(v___y_2354_);
lean_dec(v___y_2353_);
lean_dec_ref(v___y_2352_);
lean_dec_ref(v_as_2349_);
lean_dec_ref(v_ctx_2348_);
return v_res_2360_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__0(lean_object* v_as_2361_, size_t v_i_2362_, size_t v_stop_2363_, lean_object* v_b_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_){
_start:
{
lean_object* v_a_2371_; uint8_t v___x_2375_; 
v___x_2375_ = lean_usize_dec_eq(v_i_2362_, v_stop_2363_);
if (v___x_2375_ == 0)
{
lean_object* v_toInductionSubgoal_2376_; lean_object* v_ctorName_2377_; lean_object* v_mvarId_2378_; lean_object* v_fields_2379_; lean_object* v_subst_2380_; lean_object* v___x_2382_; uint8_t v_isShared_2383_; uint8_t v_isSharedCheck_2433_; 
v_toInductionSubgoal_2376_ = lean_ctor_get(v_b_2364_, 0);
lean_inc_ref(v_toInductionSubgoal_2376_);
v_ctorName_2377_ = lean_ctor_get(v_b_2364_, 1);
v_mvarId_2378_ = lean_ctor_get(v_toInductionSubgoal_2376_, 0);
v_fields_2379_ = lean_ctor_get(v_toInductionSubgoal_2376_, 1);
v_subst_2380_ = lean_ctor_get(v_toInductionSubgoal_2376_, 2);
v_isSharedCheck_2433_ = !lean_is_exclusive(v_toInductionSubgoal_2376_);
if (v_isSharedCheck_2433_ == 0)
{
v___x_2382_ = v_toInductionSubgoal_2376_;
v_isShared_2383_ = v_isSharedCheck_2433_;
goto v_resetjp_2381_;
}
else
{
lean_inc(v_subst_2380_);
lean_inc(v_fields_2379_);
lean_inc(v_mvarId_2378_);
lean_dec(v_toInductionSubgoal_2376_);
v___x_2382_ = lean_box(0);
v_isShared_2383_ = v_isSharedCheck_2433_;
goto v_resetjp_2381_;
}
v_resetjp_2381_:
{
lean_object* v___x_2384_; lean_object* v___x_2385_; 
v___x_2384_ = lean_array_uget_borrowed(v_as_2361_, v_i_2362_);
lean_inc(v___x_2384_);
v___x_2385_ = l_Lean_Meta_FVarSubst_get(v_subst_2380_, v___x_2384_);
if (lean_obj_tag(v___x_2385_) == 1)
{
lean_object* v_fvarId_2386_; lean_object* v___x_2387_; 
v_fvarId_2386_ = lean_ctor_get(v___x_2385_, 0);
lean_inc(v_fvarId_2386_);
lean_dec_ref_known(v___x_2385_, 1);
v___x_2387_ = l_Lean_Meta_saveState___redArg(v___y_2366_, v___y_2368_);
if (lean_obj_tag(v___x_2387_) == 0)
{
lean_object* v_a_2388_; lean_object* v___x_2389_; 
v_a_2388_ = lean_ctor_get(v___x_2387_, 0);
lean_inc(v_a_2388_);
lean_dec_ref_known(v___x_2387_, 1);
v___x_2389_ = l_Lean_MVarId_clear(v_mvarId_2378_, v_fvarId_2386_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_);
if (lean_obj_tag(v___x_2389_) == 0)
{
lean_object* v___x_2391_; uint8_t v_isShared_2392_; uint8_t v_isSharedCheck_2401_; 
lean_inc(v_ctorName_2377_);
lean_dec(v_a_2388_);
v_isSharedCheck_2401_ = !lean_is_exclusive(v_b_2364_);
if (v_isSharedCheck_2401_ == 0)
{
lean_object* v_unused_2402_; lean_object* v_unused_2403_; 
v_unused_2402_ = lean_ctor_get(v_b_2364_, 1);
lean_dec(v_unused_2402_);
v_unused_2403_ = lean_ctor_get(v_b_2364_, 0);
lean_dec(v_unused_2403_);
v___x_2391_ = v_b_2364_;
v_isShared_2392_ = v_isSharedCheck_2401_;
goto v_resetjp_2390_;
}
else
{
lean_dec(v_b_2364_);
v___x_2391_ = lean_box(0);
v_isShared_2392_ = v_isSharedCheck_2401_;
goto v_resetjp_2390_;
}
v_resetjp_2390_:
{
lean_object* v_a_2393_; lean_object* v___x_2394_; lean_object* v___x_2396_; 
v_a_2393_ = lean_ctor_get(v___x_2389_, 0);
lean_inc(v_a_2393_);
lean_dec_ref_known(v___x_2389_, 1);
v___x_2394_ = l_Lean_Meta_FVarSubst_erase(v_subst_2380_, v___x_2384_);
if (v_isShared_2383_ == 0)
{
lean_ctor_set(v___x_2382_, 2, v___x_2394_);
lean_ctor_set(v___x_2382_, 0, v_a_2393_);
v___x_2396_ = v___x_2382_;
goto v_reusejp_2395_;
}
else
{
lean_object* v_reuseFailAlloc_2400_; 
v_reuseFailAlloc_2400_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2400_, 0, v_a_2393_);
lean_ctor_set(v_reuseFailAlloc_2400_, 1, v_fields_2379_);
lean_ctor_set(v_reuseFailAlloc_2400_, 2, v___x_2394_);
v___x_2396_ = v_reuseFailAlloc_2400_;
goto v_reusejp_2395_;
}
v_reusejp_2395_:
{
lean_object* v___x_2398_; 
if (v_isShared_2392_ == 0)
{
lean_ctor_set(v___x_2391_, 0, v___x_2396_);
v___x_2398_ = v___x_2391_;
goto v_reusejp_2397_;
}
else
{
lean_object* v_reuseFailAlloc_2399_; 
v_reuseFailAlloc_2399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2399_, 0, v___x_2396_);
lean_ctor_set(v_reuseFailAlloc_2399_, 1, v_ctorName_2377_);
v___x_2398_ = v_reuseFailAlloc_2399_;
goto v_reusejp_2397_;
}
v_reusejp_2397_:
{
v_a_2371_ = v___x_2398_;
goto v___jp_2370_;
}
}
}
}
else
{
lean_object* v_a_2404_; lean_object* v___x_2406_; uint8_t v_isShared_2407_; uint8_t v_isSharedCheck_2424_; 
lean_del_object(v___x_2382_);
lean_dec(v_subst_2380_);
lean_dec_ref(v_fields_2379_);
v_a_2404_ = lean_ctor_get(v___x_2389_, 0);
v_isSharedCheck_2424_ = !lean_is_exclusive(v___x_2389_);
if (v_isSharedCheck_2424_ == 0)
{
v___x_2406_ = v___x_2389_;
v_isShared_2407_ = v_isSharedCheck_2424_;
goto v_resetjp_2405_;
}
else
{
lean_inc(v_a_2404_);
lean_dec(v___x_2389_);
v___x_2406_ = lean_box(0);
v_isShared_2407_ = v_isSharedCheck_2424_;
goto v_resetjp_2405_;
}
v_resetjp_2405_:
{
lean_object* v___x_2409_; 
lean_inc(v_a_2404_);
if (v_isShared_2407_ == 0)
{
v___x_2409_ = v___x_2406_;
goto v_reusejp_2408_;
}
else
{
lean_object* v_reuseFailAlloc_2423_; 
v_reuseFailAlloc_2423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2423_, 0, v_a_2404_);
v___x_2409_ = v_reuseFailAlloc_2423_;
goto v_reusejp_2408_;
}
v_reusejp_2408_:
{
uint8_t v___y_2411_; uint8_t v___x_2421_; 
v___x_2421_ = l_Lean_Exception_isInterrupt(v_a_2404_);
if (v___x_2421_ == 0)
{
uint8_t v___x_2422_; 
v___x_2422_ = l_Lean_Exception_isRuntime(v_a_2404_);
v___y_2411_ = v___x_2422_;
goto v___jp_2410_;
}
else
{
lean_dec(v_a_2404_);
v___y_2411_ = v___x_2421_;
goto v___jp_2410_;
}
v___jp_2410_:
{
if (v___y_2411_ == 0)
{
lean_object* v___x_2412_; 
lean_dec_ref(v___x_2409_);
v___x_2412_ = l_Lean_Meta_SavedState_restore___redArg(v_a_2388_, v___y_2366_, v___y_2368_);
lean_dec(v_a_2388_);
if (lean_obj_tag(v___x_2412_) == 0)
{
lean_dec_ref_known(v___x_2412_, 1);
v_a_2371_ = v_b_2364_;
goto v___jp_2370_;
}
else
{
lean_object* v_a_2413_; lean_object* v___x_2415_; uint8_t v_isShared_2416_; uint8_t v_isSharedCheck_2420_; 
lean_dec_ref(v_b_2364_);
v_a_2413_ = lean_ctor_get(v___x_2412_, 0);
v_isSharedCheck_2420_ = !lean_is_exclusive(v___x_2412_);
if (v_isSharedCheck_2420_ == 0)
{
v___x_2415_ = v___x_2412_;
v_isShared_2416_ = v_isSharedCheck_2420_;
goto v_resetjp_2414_;
}
else
{
lean_inc(v_a_2413_);
lean_dec(v___x_2412_);
v___x_2415_ = lean_box(0);
v_isShared_2416_ = v_isSharedCheck_2420_;
goto v_resetjp_2414_;
}
v_resetjp_2414_:
{
lean_object* v___x_2418_; 
if (v_isShared_2416_ == 0)
{
v___x_2418_ = v___x_2415_;
goto v_reusejp_2417_;
}
else
{
lean_object* v_reuseFailAlloc_2419_; 
v_reuseFailAlloc_2419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2419_, 0, v_a_2413_);
v___x_2418_ = v_reuseFailAlloc_2419_;
goto v_reusejp_2417_;
}
v_reusejp_2417_:
{
return v___x_2418_;
}
}
}
}
else
{
lean_dec(v_a_2388_);
lean_dec_ref(v_b_2364_);
return v___x_2409_;
}
}
}
}
}
}
else
{
lean_object* v_a_2425_; lean_object* v___x_2427_; uint8_t v_isShared_2428_; uint8_t v_isSharedCheck_2432_; 
lean_dec(v_fvarId_2386_);
lean_del_object(v___x_2382_);
lean_dec(v_subst_2380_);
lean_dec_ref(v_fields_2379_);
lean_dec(v_mvarId_2378_);
lean_dec_ref(v_b_2364_);
v_a_2425_ = lean_ctor_get(v___x_2387_, 0);
v_isSharedCheck_2432_ = !lean_is_exclusive(v___x_2387_);
if (v_isSharedCheck_2432_ == 0)
{
v___x_2427_ = v___x_2387_;
v_isShared_2428_ = v_isSharedCheck_2432_;
goto v_resetjp_2426_;
}
else
{
lean_inc(v_a_2425_);
lean_dec(v___x_2387_);
v___x_2427_ = lean_box(0);
v_isShared_2428_ = v_isSharedCheck_2432_;
goto v_resetjp_2426_;
}
v_resetjp_2426_:
{
lean_object* v___x_2430_; 
if (v_isShared_2428_ == 0)
{
v___x_2430_ = v___x_2427_;
goto v_reusejp_2429_;
}
else
{
lean_object* v_reuseFailAlloc_2431_; 
v_reuseFailAlloc_2431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2431_, 0, v_a_2425_);
v___x_2430_ = v_reuseFailAlloc_2431_;
goto v_reusejp_2429_;
}
v_reusejp_2429_:
{
return v___x_2430_;
}
}
}
}
else
{
lean_dec_ref(v___x_2385_);
lean_del_object(v___x_2382_);
lean_dec(v_subst_2380_);
lean_dec_ref(v_fields_2379_);
lean_dec(v_mvarId_2378_);
v_a_2371_ = v_b_2364_;
goto v___jp_2370_;
}
}
}
else
{
lean_object* v___x_2434_; 
v___x_2434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2434_, 0, v_b_2364_);
return v___x_2434_;
}
v___jp_2370_:
{
size_t v___x_2372_; size_t v___x_2373_; 
v___x_2372_ = ((size_t)1ULL);
v___x_2373_ = lean_usize_add(v_i_2362_, v___x_2372_);
v_i_2362_ = v___x_2373_;
v_b_2364_ = v_a_2371_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__0___boxed(lean_object* v_as_2435_, lean_object* v_i_2436_, lean_object* v_stop_2437_, lean_object* v_b_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_){
_start:
{
size_t v_i_boxed_2444_; size_t v_stop_boxed_2445_; lean_object* v_res_2446_; 
v_i_boxed_2444_ = lean_unbox_usize(v_i_2436_);
lean_dec(v_i_2436_);
v_stop_boxed_2445_ = lean_unbox_usize(v_stop_2437_);
lean_dec(v_stop_2437_);
v_res_2446_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__0(v_as_2435_, v_i_boxed_2444_, v_stop_boxed_2445_, v_b_2438_, v___y_2439_, v___y_2440_, v___y_2441_, v___y_2442_);
lean_dec(v___y_2442_);
lean_dec_ref(v___y_2441_);
lean_dec(v___y_2440_);
lean_dec_ref(v___y_2439_);
lean_dec_ref(v_as_2435_);
return v_res_2446_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__1(lean_object* v_indicesFVarIds_2447_, size_t v_sz_2448_, size_t v_i_2449_, lean_object* v_bs_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_){
_start:
{
uint8_t v___x_2456_; 
v___x_2456_ = lean_usize_dec_lt(v_i_2449_, v_sz_2448_);
if (v___x_2456_ == 0)
{
lean_object* v___x_2457_; 
v___x_2457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2457_, 0, v_bs_2450_);
return v___x_2457_;
}
else
{
lean_object* v_v_2458_; lean_object* v___x_2459_; lean_object* v_bs_x27_2460_; lean_object* v_a_2462_; lean_object* v___y_2468_; lean_object* v___x_2478_; uint8_t v___x_2479_; 
v_v_2458_ = lean_array_uget(v_bs_2450_, v_i_2449_);
v___x_2459_ = lean_unsigned_to_nat(0u);
v_bs_x27_2460_ = lean_array_uset(v_bs_2450_, v_i_2449_, v___x_2459_);
v___x_2478_ = lean_array_get_size(v_indicesFVarIds_2447_);
v___x_2479_ = lean_nat_dec_lt(v___x_2459_, v___x_2478_);
if (v___x_2479_ == 0)
{
v_a_2462_ = v_v_2458_;
goto v___jp_2461_;
}
else
{
uint8_t v___x_2480_; 
v___x_2480_ = lean_nat_dec_le(v___x_2478_, v___x_2478_);
if (v___x_2480_ == 0)
{
if (v___x_2479_ == 0)
{
v_a_2462_ = v_v_2458_;
goto v___jp_2461_;
}
else
{
size_t v___x_2481_; size_t v___x_2482_; lean_object* v___x_2483_; 
v___x_2481_ = ((size_t)0ULL);
v___x_2482_ = lean_usize_of_nat(v___x_2478_);
v___x_2483_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__0(v_indicesFVarIds_2447_, v___x_2481_, v___x_2482_, v_v_2458_, v___y_2451_, v___y_2452_, v___y_2453_, v___y_2454_);
v___y_2468_ = v___x_2483_;
goto v___jp_2467_;
}
}
else
{
size_t v___x_2484_; size_t v___x_2485_; lean_object* v___x_2486_; 
v___x_2484_ = ((size_t)0ULL);
v___x_2485_ = lean_usize_of_nat(v___x_2478_);
v___x_2486_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__0(v_indicesFVarIds_2447_, v___x_2484_, v___x_2485_, v_v_2458_, v___y_2451_, v___y_2452_, v___y_2453_, v___y_2454_);
v___y_2468_ = v___x_2486_;
goto v___jp_2467_;
}
}
v___jp_2461_:
{
size_t v___x_2463_; size_t v___x_2464_; lean_object* v___x_2465_; 
v___x_2463_ = ((size_t)1ULL);
v___x_2464_ = lean_usize_add(v_i_2449_, v___x_2463_);
v___x_2465_ = lean_array_uset(v_bs_x27_2460_, v_i_2449_, v_a_2462_);
v_i_2449_ = v___x_2464_;
v_bs_2450_ = v___x_2465_;
goto _start;
}
v___jp_2467_:
{
if (lean_obj_tag(v___y_2468_) == 0)
{
lean_object* v_a_2469_; 
v_a_2469_ = lean_ctor_get(v___y_2468_, 0);
lean_inc(v_a_2469_);
lean_dec_ref_known(v___y_2468_, 1);
v_a_2462_ = v_a_2469_;
goto v___jp_2461_;
}
else
{
lean_object* v_a_2470_; lean_object* v___x_2472_; uint8_t v_isShared_2473_; uint8_t v_isSharedCheck_2477_; 
lean_dec_ref(v_bs_x27_2460_);
v_a_2470_ = lean_ctor_get(v___y_2468_, 0);
v_isSharedCheck_2477_ = !lean_is_exclusive(v___y_2468_);
if (v_isSharedCheck_2477_ == 0)
{
v___x_2472_ = v___y_2468_;
v_isShared_2473_ = v_isSharedCheck_2477_;
goto v_resetjp_2471_;
}
else
{
lean_inc(v_a_2470_);
lean_dec(v___y_2468_);
v___x_2472_ = lean_box(0);
v_isShared_2473_ = v_isSharedCheck_2477_;
goto v_resetjp_2471_;
}
v_resetjp_2471_:
{
lean_object* v___x_2475_; 
if (v_isShared_2473_ == 0)
{
v___x_2475_ = v___x_2472_;
goto v_reusejp_2474_;
}
else
{
lean_object* v_reuseFailAlloc_2476_; 
v_reuseFailAlloc_2476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2476_, 0, v_a_2470_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__1___boxed(lean_object* v_indicesFVarIds_2487_, lean_object* v_sz_2488_, lean_object* v_i_2489_, lean_object* v_bs_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_){
_start:
{
size_t v_sz_boxed_2496_; size_t v_i_boxed_2497_; lean_object* v_res_2498_; 
v_sz_boxed_2496_ = lean_unbox_usize(v_sz_2488_);
lean_dec(v_sz_2488_);
v_i_boxed_2497_ = lean_unbox_usize(v_i_2489_);
lean_dec(v_i_2489_);
v_res_2498_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__1(v_indicesFVarIds_2487_, v_sz_boxed_2496_, v_i_boxed_2497_, v_bs_2490_, v___y_2491_, v___y_2492_, v___y_2493_, v___y_2494_);
lean_dec(v___y_2494_);
lean_dec_ref(v___y_2493_);
lean_dec(v___y_2492_);
lean_dec_ref(v___y_2491_);
lean_dec_ref(v_indicesFVarIds_2487_);
return v_res_2498_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices(lean_object* v_s_u2081_2499_, lean_object* v_s_u2082_2500_, lean_object* v_a_2501_, lean_object* v_a_2502_, lean_object* v_a_2503_, lean_object* v_a_2504_){
_start:
{
lean_object* v_indicesFVarIds_2506_; size_t v_sz_2507_; size_t v___x_2508_; lean_object* v___x_2509_; 
v_indicesFVarIds_2506_ = lean_ctor_get(v_s_u2081_2499_, 1);
v_sz_2507_ = lean_array_size(v_s_u2082_2500_);
v___x_2508_ = ((size_t)0ULL);
v___x_2509_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__1(v_indicesFVarIds_2506_, v_sz_2507_, v___x_2508_, v_s_u2082_2500_, v_a_2501_, v_a_2502_, v_a_2503_, v_a_2504_);
return v___x_2509_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices___boxed(lean_object* v_s_u2081_2510_, lean_object* v_s_u2082_2511_, lean_object* v_a_2512_, lean_object* v_a_2513_, lean_object* v_a_2514_, lean_object* v_a_2515_, lean_object* v_a_2516_){
_start:
{
lean_object* v_res_2517_; 
v_res_2517_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices(v_s_u2081_2510_, v_s_u2082_2511_, v_a_2512_, v_a_2513_, v_a_2514_, v_a_2515_);
lean_dec(v_a_2515_);
lean_dec_ref(v_a_2514_);
lean_dec(v_a_2513_);
lean_dec_ref(v_a_2512_);
lean_dec_ref(v_s_u2081_2510_);
return v_res_2517_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0___redArg(lean_object* v_ctorNames_2518_, lean_object* v_us_2519_, lean_object* v_params_2520_, lean_object* v_majorFVarId_2521_, size_t v_sz_2522_, size_t v_i_2523_, lean_object* v_bs_2524_){
_start:
{
uint8_t v___x_2525_; 
v___x_2525_ = lean_usize_dec_lt(v_i_2523_, v_sz_2522_);
if (v___x_2525_ == 0)
{
lean_dec(v_majorFVarId_2521_);
lean_dec(v_us_2519_);
return v_bs_2524_;
}
else
{
lean_object* v_v_2526_; lean_object* v___x_2527_; lean_object* v_bs_x27_2528_; lean_object* v___y_2530_; lean_object* v___x_2535_; lean_object* v___x_2536_; uint8_t v___x_2537_; 
v_v_2526_ = lean_array_uget(v_bs_2524_, v_i_2523_);
v___x_2527_ = lean_unsigned_to_nat(0u);
v_bs_x27_2528_ = lean_array_uset(v_bs_2524_, v_i_2523_, v___x_2527_);
v___x_2535_ = lean_usize_to_nat(v_i_2523_);
v___x_2536_ = lean_array_get_size(v_ctorNames_2518_);
v___x_2537_ = lean_nat_dec_lt(v___x_2535_, v___x_2536_);
if (v___x_2537_ == 0)
{
lean_object* v___x_2538_; lean_object* v___x_2539_; 
lean_dec(v___x_2535_);
v___x_2538_ = lean_box(0);
v___x_2539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2539_, 0, v_v_2526_);
lean_ctor_set(v___x_2539_, 1, v___x_2538_);
v___y_2530_ = v___x_2539_;
goto v___jp_2529_;
}
else
{
lean_object* v_mvarId_2540_; lean_object* v_fields_2541_; lean_object* v_subst_2542_; lean_object* v___x_2544_; uint8_t v_isShared_2545_; uint8_t v_isSharedCheck_2557_; 
v_mvarId_2540_ = lean_ctor_get(v_v_2526_, 0);
v_fields_2541_ = lean_ctor_get(v_v_2526_, 1);
v_subst_2542_ = lean_ctor_get(v_v_2526_, 2);
v_isSharedCheck_2557_ = !lean_is_exclusive(v_v_2526_);
if (v_isSharedCheck_2557_ == 0)
{
v___x_2544_ = v_v_2526_;
v_isShared_2545_ = v_isSharedCheck_2557_;
goto v_resetjp_2543_;
}
else
{
lean_inc(v_subst_2542_);
lean_inc(v_fields_2541_);
lean_inc(v_mvarId_2540_);
lean_dec(v_v_2526_);
v___x_2544_ = lean_box(0);
v_isShared_2545_ = v_isSharedCheck_2557_;
goto v_resetjp_2543_;
}
v_resetjp_2543_:
{
lean_object* v_ctorName_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v_ctorApp_2549_; lean_object* v___x_2550_; lean_object* v_subst_2551_; lean_object* v___x_2553_; 
v_ctorName_2546_ = lean_array_fget_borrowed(v_ctorNames_2518_, v___x_2535_);
lean_dec(v___x_2535_);
lean_inc(v_us_2519_);
lean_inc(v_ctorName_2546_);
v___x_2547_ = l_Lean_mkConst(v_ctorName_2546_, v_us_2519_);
v___x_2548_ = l_Lean_mkAppN(v___x_2547_, v_params_2520_);
v_ctorApp_2549_ = l_Lean_mkAppN(v___x_2548_, v_fields_2541_);
v___x_2550_ = l_Lean_Meta_FVarSubst_erase(v_subst_2542_, v_majorFVarId_2521_);
lean_inc(v_majorFVarId_2521_);
v_subst_2551_ = l_Lean_Meta_FVarSubst_insert(v___x_2550_, v_majorFVarId_2521_, v_ctorApp_2549_);
if (v_isShared_2545_ == 0)
{
lean_ctor_set(v___x_2544_, 2, v_subst_2551_);
v___x_2553_ = v___x_2544_;
goto v_reusejp_2552_;
}
else
{
lean_object* v_reuseFailAlloc_2556_; 
v_reuseFailAlloc_2556_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2556_, 0, v_mvarId_2540_);
lean_ctor_set(v_reuseFailAlloc_2556_, 1, v_fields_2541_);
lean_ctor_set(v_reuseFailAlloc_2556_, 2, v_subst_2551_);
v___x_2553_ = v_reuseFailAlloc_2556_;
goto v_reusejp_2552_;
}
v_reusejp_2552_:
{
lean_object* v___x_2554_; lean_object* v___x_2555_; 
lean_inc(v_ctorName_2546_);
v___x_2554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2554_, 0, v_ctorName_2546_);
v___x_2555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2555_, 0, v___x_2553_);
lean_ctor_set(v___x_2555_, 1, v___x_2554_);
v___y_2530_ = v___x_2555_;
goto v___jp_2529_;
}
}
}
v___jp_2529_:
{
size_t v___x_2531_; size_t v___x_2532_; lean_object* v___x_2533_; 
v___x_2531_ = ((size_t)1ULL);
v___x_2532_ = lean_usize_add(v_i_2523_, v___x_2531_);
v___x_2533_ = lean_array_uset(v_bs_x27_2528_, v_i_2523_, v___y_2530_);
v_i_2523_ = v___x_2532_;
v_bs_2524_ = v___x_2533_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0___redArg___boxed(lean_object* v_ctorNames_2558_, lean_object* v_us_2559_, lean_object* v_params_2560_, lean_object* v_majorFVarId_2561_, lean_object* v_sz_2562_, lean_object* v_i_2563_, lean_object* v_bs_2564_){
_start:
{
size_t v_sz_boxed_2565_; size_t v_i_boxed_2566_; lean_object* v_res_2567_; 
v_sz_boxed_2565_ = lean_unbox_usize(v_sz_2562_);
lean_dec(v_sz_2562_);
v_i_boxed_2566_ = lean_unbox_usize(v_i_2563_);
lean_dec(v_i_2563_);
v_res_2567_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0___redArg(v_ctorNames_2558_, v_us_2559_, v_params_2560_, v_majorFVarId_2561_, v_sz_boxed_2565_, v_i_boxed_2566_, v_bs_2564_);
lean_dec_ref(v_params_2560_);
lean_dec_ref(v_ctorNames_2558_);
return v_res_2567_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals(lean_object* v_s_2568_, lean_object* v_ctorNames_2569_, lean_object* v_majorFVarId_2570_, lean_object* v_us_2571_, lean_object* v_params_2572_){
_start:
{
size_t v_sz_2573_; size_t v___x_2574_; lean_object* v___x_2575_; 
v_sz_2573_ = lean_array_size(v_s_2568_);
v___x_2574_ = ((size_t)0ULL);
v___x_2575_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0___redArg(v_ctorNames_2569_, v_us_2571_, v_params_2572_, v_majorFVarId_2570_, v_sz_2573_, v___x_2574_, v_s_2568_);
return v___x_2575_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals___boxed(lean_object* v_s_2576_, lean_object* v_ctorNames_2577_, lean_object* v_majorFVarId_2578_, lean_object* v_us_2579_, lean_object* v_params_2580_){
_start:
{
lean_object* v_res_2581_; 
v_res_2581_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals(v_s_2576_, v_ctorNames_2577_, v_majorFVarId_2578_, v_us_2579_, v_params_2580_);
lean_dec_ref(v_params_2580_);
lean_dec_ref(v_ctorNames_2577_);
return v_res_2581_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0(lean_object* v_ctorNames_2582_, lean_object* v_us_2583_, lean_object* v_params_2584_, lean_object* v_majorFVarId_2585_, lean_object* v_as_2586_, size_t v_sz_2587_, size_t v_i_2588_, lean_object* v_bs_2589_){
_start:
{
lean_object* v___x_2590_; 
v___x_2590_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0___redArg(v_ctorNames_2582_, v_us_2583_, v_params_2584_, v_majorFVarId_2585_, v_sz_2587_, v_i_2588_, v_bs_2589_);
return v___x_2590_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0___boxed(lean_object* v_ctorNames_2591_, lean_object* v_us_2592_, lean_object* v_params_2593_, lean_object* v_majorFVarId_2594_, lean_object* v_as_2595_, lean_object* v_sz_2596_, lean_object* v_i_2597_, lean_object* v_bs_2598_){
_start:
{
size_t v_sz_boxed_2599_; size_t v_i_boxed_2600_; lean_object* v_res_2601_; 
v_sz_boxed_2599_ = lean_unbox_usize(v_sz_2596_);
lean_dec(v_sz_2596_);
v_i_boxed_2600_ = lean_unbox_usize(v_i_2597_);
lean_dec(v_i_2597_);
v_res_2601_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0(v_ctorNames_2591_, v_us_2592_, v_params_2593_, v_majorFVarId_2594_, v_as_2595_, v_sz_boxed_2599_, v_i_boxed_2600_, v_bs_2598_);
lean_dec_ref(v_as_2595_);
lean_dec_ref(v_params_2593_);
lean_dec_ref(v_ctorNames_2591_);
return v_res_2601_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_2607_; lean_object* v___x_2608_; 
v___x_2607_ = l_Lean_maxRecDepthErrorMessage;
v___x_2608_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2608_, 0, v___x_2607_);
return v___x_2608_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_2609_; lean_object* v___x_2610_; 
v___x_2609_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__3);
v___x_2610_ = l_Lean_MessageData_ofFormat(v___x_2609_);
return v___x_2610_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; 
v___x_2611_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__4);
v___x_2612_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__2));
v___x_2613_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2613_, 0, v___x_2612_);
lean_ctor_set(v___x_2613_, 1, v___x_2611_);
return v___x_2613_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg(lean_object* v_ref_2614_){
_start:
{
lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; 
v___x_2616_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__5);
v___x_2617_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2617_, 0, v_ref_2614_);
lean_ctor_set(v___x_2617_, 1, v___x_2616_);
v___x_2618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2618_, 0, v___x_2617_);
return v___x_2618_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___boxed(lean_object* v_ref_2619_, lean_object* v___y_2620_){
_start:
{
lean_object* v_res_2621_; 
v_res_2621_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg(v_ref_2619_);
return v_res_2621_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0(lean_object* v_00_u03b1_2622_, lean_object* v_ref_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_){
_start:
{
lean_object* v___x_2629_; 
v___x_2629_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg(v_ref_2623_);
return v___x_2629_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___boxed(lean_object* v_00_u03b1_2630_, lean_object* v_ref_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_){
_start:
{
lean_object* v_res_2637_; 
v_res_2637_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0(v_00_u03b1_2630_, v_ref_2631_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_);
lean_dec(v___y_2635_);
lean_dec_ref(v___y_2634_);
lean_dec(v___y_2633_);
lean_dec_ref(v___y_2632_);
return v_res_2637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_unifyEqs_x3f(lean_object* v_numEqs_2639_, lean_object* v_mvarId_2640_, lean_object* v_subst_2641_, lean_object* v_caseName_x3f_2642_, lean_object* v_a_2643_, lean_object* v_a_2644_, lean_object* v_a_2645_, lean_object* v_a_2646_){
_start:
{
lean_object* v_toCold_2648_; lean_object* v_currRecDepth_2649_; lean_object* v_ref_2650_; uint8_t v_diag_2651_; uint8_t v_suppressElabErrors_2652_; lean_object* v_maxRecDepth_2653_; lean_object* v___x_2654_; uint8_t v___x_2655_; uint8_t v___x_2701_; 
v_toCold_2648_ = lean_ctor_get(v_a_2645_, 0);
lean_inc_ref(v_toCold_2648_);
v_currRecDepth_2649_ = lean_ctor_get(v_a_2645_, 1);
lean_inc(v_currRecDepth_2649_);
v_ref_2650_ = lean_ctor_get(v_a_2645_, 2);
lean_inc(v_ref_2650_);
v_diag_2651_ = lean_ctor_get_uint8(v_a_2645_, sizeof(void*)*3);
v_suppressElabErrors_2652_ = lean_ctor_get_uint8(v_a_2645_, sizeof(void*)*3 + 1);
lean_dec_ref(v_a_2645_);
v_maxRecDepth_2653_ = lean_ctor_get(v_toCold_2648_, 3);
v___x_2654_ = lean_unsigned_to_nat(0u);
v___x_2655_ = lean_nat_dec_eq(v_numEqs_2639_, v___x_2654_);
v___x_2701_ = lean_nat_dec_eq(v_maxRecDepth_2653_, v___x_2654_);
if (v___x_2701_ == 0)
{
uint8_t v___x_2702_; 
v___x_2702_ = lean_nat_dec_eq(v_currRecDepth_2649_, v_maxRecDepth_2653_);
if (v___x_2702_ == 0)
{
goto v___jp_2656_;
}
else
{
lean_object* v___x_2703_; 
lean_dec(v_currRecDepth_2649_);
lean_dec_ref(v_toCold_2648_);
lean_dec(v_caseName_x3f_2642_);
lean_dec(v_subst_2641_);
lean_dec(v_mvarId_2640_);
lean_dec(v_numEqs_2639_);
v___x_2703_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg(v_ref_2650_);
return v___x_2703_;
}
}
else
{
goto v___jp_2656_;
}
v___jp_2656_:
{
if (v___x_2655_ == 0)
{
lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; 
v___x_2657_ = lean_unsigned_to_nat(1u);
v___x_2658_ = lean_nat_add(v_currRecDepth_2649_, v___x_2657_);
lean_dec(v_currRecDepth_2649_);
v___x_2659_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2659_, 0, v_toCold_2648_);
lean_ctor_set(v___x_2659_, 1, v___x_2658_);
lean_ctor_set(v___x_2659_, 2, v_ref_2650_);
lean_ctor_set_uint8(v___x_2659_, sizeof(void*)*3, v_diag_2651_);
lean_ctor_set_uint8(v___x_2659_, sizeof(void*)*3 + 1, v_suppressElabErrors_2652_);
v___x_2660_ = l_Lean_Meta_intro1Core(v_mvarId_2640_, v___x_2655_, v_a_2643_, v_a_2644_, v___x_2659_, v_a_2646_);
if (lean_obj_tag(v___x_2660_) == 0)
{
lean_object* v_a_2661_; lean_object* v_fst_2662_; lean_object* v_snd_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; 
v_a_2661_ = lean_ctor_get(v___x_2660_, 0);
lean_inc(v_a_2661_);
lean_dec_ref_known(v___x_2660_, 1);
v_fst_2662_ = lean_ctor_get(v_a_2661_, 0);
lean_inc(v_fst_2662_);
v_snd_2663_ = lean_ctor_get(v_a_2661_, 1);
lean_inc(v_snd_2663_);
lean_dec(v_a_2661_);
v___x_2664_ = ((lean_object*)(l_Lean_Meta_Cases_unifyEqs_x3f___closed__0));
lean_inc(v_caseName_x3f_2642_);
v___x_2665_ = l_Lean_Meta_unifyEq_x3f(v_snd_2663_, v_fst_2662_, v_subst_2641_, v___x_2664_, v_caseName_x3f_2642_, v_a_2643_, v_a_2644_, v___x_2659_, v_a_2646_);
if (lean_obj_tag(v___x_2665_) == 0)
{
lean_object* v_a_2666_; lean_object* v___x_2668_; uint8_t v_isShared_2669_; uint8_t v_isSharedCheck_2681_; 
v_a_2666_ = lean_ctor_get(v___x_2665_, 0);
v_isSharedCheck_2681_ = !lean_is_exclusive(v___x_2665_);
if (v_isSharedCheck_2681_ == 0)
{
v___x_2668_ = v___x_2665_;
v_isShared_2669_ = v_isSharedCheck_2681_;
goto v_resetjp_2667_;
}
else
{
lean_inc(v_a_2666_);
lean_dec(v___x_2665_);
v___x_2668_ = lean_box(0);
v_isShared_2669_ = v_isSharedCheck_2681_;
goto v_resetjp_2667_;
}
v_resetjp_2667_:
{
if (lean_obj_tag(v_a_2666_) == 1)
{
lean_object* v_val_2670_; lean_object* v_mvarId_2671_; lean_object* v_subst_2672_; lean_object* v_numNewEqs_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; 
lean_del_object(v___x_2668_);
v_val_2670_ = lean_ctor_get(v_a_2666_, 0);
lean_inc(v_val_2670_);
lean_dec_ref_known(v_a_2666_, 1);
v_mvarId_2671_ = lean_ctor_get(v_val_2670_, 0);
lean_inc(v_mvarId_2671_);
v_subst_2672_ = lean_ctor_get(v_val_2670_, 1);
lean_inc(v_subst_2672_);
v_numNewEqs_2673_ = lean_ctor_get(v_val_2670_, 2);
lean_inc(v_numNewEqs_2673_);
lean_dec(v_val_2670_);
v___x_2674_ = lean_nat_sub(v_numEqs_2639_, v___x_2657_);
lean_dec(v_numEqs_2639_);
v___x_2675_ = lean_nat_add(v___x_2674_, v_numNewEqs_2673_);
lean_dec(v_numNewEqs_2673_);
lean_dec(v___x_2674_);
v_numEqs_2639_ = v___x_2675_;
v_mvarId_2640_ = v_mvarId_2671_;
v_subst_2641_ = v_subst_2672_;
v_a_2645_ = v___x_2659_;
goto _start;
}
else
{
lean_object* v___x_2677_; lean_object* v___x_2679_; 
lean_dec(v_a_2666_);
lean_dec_ref_known(v___x_2659_, 3);
lean_dec(v_caseName_x3f_2642_);
lean_dec(v_numEqs_2639_);
v___x_2677_ = lean_box(0);
if (v_isShared_2669_ == 0)
{
lean_ctor_set(v___x_2668_, 0, v___x_2677_);
v___x_2679_ = v___x_2668_;
goto v_reusejp_2678_;
}
else
{
lean_object* v_reuseFailAlloc_2680_; 
v_reuseFailAlloc_2680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2680_, 0, v___x_2677_);
v___x_2679_ = v_reuseFailAlloc_2680_;
goto v_reusejp_2678_;
}
v_reusejp_2678_:
{
return v___x_2679_;
}
}
}
}
else
{
lean_object* v_a_2682_; lean_object* v___x_2684_; uint8_t v_isShared_2685_; uint8_t v_isSharedCheck_2689_; 
lean_dec_ref_known(v___x_2659_, 3);
lean_dec(v_caseName_x3f_2642_);
lean_dec(v_numEqs_2639_);
v_a_2682_ = lean_ctor_get(v___x_2665_, 0);
v_isSharedCheck_2689_ = !lean_is_exclusive(v___x_2665_);
if (v_isSharedCheck_2689_ == 0)
{
v___x_2684_ = v___x_2665_;
v_isShared_2685_ = v_isSharedCheck_2689_;
goto v_resetjp_2683_;
}
else
{
lean_inc(v_a_2682_);
lean_dec(v___x_2665_);
v___x_2684_ = lean_box(0);
v_isShared_2685_ = v_isSharedCheck_2689_;
goto v_resetjp_2683_;
}
v_resetjp_2683_:
{
lean_object* v___x_2687_; 
if (v_isShared_2685_ == 0)
{
v___x_2687_ = v___x_2684_;
goto v_reusejp_2686_;
}
else
{
lean_object* v_reuseFailAlloc_2688_; 
v_reuseFailAlloc_2688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2688_, 0, v_a_2682_);
v___x_2687_ = v_reuseFailAlloc_2688_;
goto v_reusejp_2686_;
}
v_reusejp_2686_:
{
return v___x_2687_;
}
}
}
}
else
{
lean_object* v_a_2690_; lean_object* v___x_2692_; uint8_t v_isShared_2693_; uint8_t v_isSharedCheck_2697_; 
lean_dec_ref_known(v___x_2659_, 3);
lean_dec(v_caseName_x3f_2642_);
lean_dec(v_subst_2641_);
lean_dec(v_numEqs_2639_);
v_a_2690_ = lean_ctor_get(v___x_2660_, 0);
v_isSharedCheck_2697_ = !lean_is_exclusive(v___x_2660_);
if (v_isSharedCheck_2697_ == 0)
{
v___x_2692_ = v___x_2660_;
v_isShared_2693_ = v_isSharedCheck_2697_;
goto v_resetjp_2691_;
}
else
{
lean_inc(v_a_2690_);
lean_dec(v___x_2660_);
v___x_2692_ = lean_box(0);
v_isShared_2693_ = v_isSharedCheck_2697_;
goto v_resetjp_2691_;
}
v_resetjp_2691_:
{
lean_object* v___x_2695_; 
if (v_isShared_2693_ == 0)
{
v___x_2695_ = v___x_2692_;
goto v_reusejp_2694_;
}
else
{
lean_object* v_reuseFailAlloc_2696_; 
v_reuseFailAlloc_2696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2696_, 0, v_a_2690_);
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
lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; 
lean_dec(v_ref_2650_);
lean_dec(v_currRecDepth_2649_);
lean_dec_ref(v_toCold_2648_);
lean_dec(v_caseName_x3f_2642_);
lean_dec(v_numEqs_2639_);
v___x_2698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2698_, 0, v_mvarId_2640_);
lean_ctor_set(v___x_2698_, 1, v_subst_2641_);
v___x_2699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2699_, 0, v___x_2698_);
v___x_2700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2700_, 0, v___x_2699_);
return v___x_2700_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_unifyEqs_x3f___boxed(lean_object* v_numEqs_2704_, lean_object* v_mvarId_2705_, lean_object* v_subst_2706_, lean_object* v_caseName_x3f_2707_, lean_object* v_a_2708_, lean_object* v_a_2709_, lean_object* v_a_2710_, lean_object* v_a_2711_, lean_object* v_a_2712_){
_start:
{
lean_object* v_res_2713_; 
v_res_2713_ = l_Lean_Meta_Cases_unifyEqs_x3f(v_numEqs_2704_, v_mvarId_2705_, v_subst_2706_, v_caseName_x3f_2707_, v_a_2708_, v_a_2709_, v_a_2710_, v_a_2711_);
lean_dec(v_a_2711_);
lean_dec(v_a_2709_);
lean_dec_ref(v_a_2708_);
return v_res_2713_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__0(lean_object* v_snd_2714_, size_t v_sz_2715_, size_t v_i_2716_, lean_object* v_bs_2717_){
_start:
{
uint8_t v___x_2718_; 
v___x_2718_ = lean_usize_dec_lt(v_i_2716_, v_sz_2715_);
if (v___x_2718_ == 0)
{
lean_dec(v_snd_2714_);
return v_bs_2717_;
}
else
{
lean_object* v_v_2719_; lean_object* v___x_2720_; lean_object* v_bs_x27_2721_; lean_object* v___x_2722_; size_t v___x_2723_; size_t v___x_2724_; lean_object* v___x_2725_; 
v_v_2719_ = lean_array_uget(v_bs_2717_, v_i_2716_);
v___x_2720_ = lean_unsigned_to_nat(0u);
v_bs_x27_2721_ = lean_array_uset(v_bs_2717_, v_i_2716_, v___x_2720_);
lean_inc(v_snd_2714_);
v___x_2722_ = l_Lean_Meta_FVarSubst_apply(v_snd_2714_, v_v_2719_);
lean_dec(v_v_2719_);
v___x_2723_ = ((size_t)1ULL);
v___x_2724_ = lean_usize_add(v_i_2716_, v___x_2723_);
v___x_2725_ = lean_array_uset(v_bs_x27_2721_, v_i_2716_, v___x_2722_);
v_i_2716_ = v___x_2724_;
v_bs_2717_ = v___x_2725_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__0___boxed(lean_object* v_snd_2727_, lean_object* v_sz_2728_, lean_object* v_i_2729_, lean_object* v_bs_2730_){
_start:
{
size_t v_sz_boxed_2731_; size_t v_i_boxed_2732_; lean_object* v_res_2733_; 
v_sz_boxed_2731_ = lean_unbox_usize(v_sz_2728_);
lean_dec(v_sz_2728_);
v_i_boxed_2732_ = lean_unbox_usize(v_i_2729_);
lean_dec(v_i_2729_);
v_res_2733_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__0(v_snd_2727_, v_sz_boxed_2731_, v_i_boxed_2732_, v_bs_2730_);
return v_res_2733_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1_spec__1(lean_object* v_numEqs_2734_, lean_object* v_as_2735_, size_t v_i_2736_, size_t v_stop_2737_, lean_object* v_b_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_){
_start:
{
lean_object* v_a_2745_; uint8_t v___x_2749_; 
v___x_2749_ = lean_usize_dec_eq(v_i_2736_, v_stop_2737_);
if (v___x_2749_ == 0)
{
lean_object* v___x_2750_; lean_object* v_toInductionSubgoal_2751_; lean_object* v_ctorName_2752_; lean_object* v___x_2754_; uint8_t v_isShared_2755_; uint8_t v_isSharedCheck_2786_; 
v___x_2750_ = lean_array_uget(v_as_2735_, v_i_2736_);
v_toInductionSubgoal_2751_ = lean_ctor_get(v___x_2750_, 0);
v_ctorName_2752_ = lean_ctor_get(v___x_2750_, 1);
v_isSharedCheck_2786_ = !lean_is_exclusive(v___x_2750_);
if (v_isSharedCheck_2786_ == 0)
{
v___x_2754_ = v___x_2750_;
v_isShared_2755_ = v_isSharedCheck_2786_;
goto v_resetjp_2753_;
}
else
{
lean_inc(v_ctorName_2752_);
lean_inc(v_toInductionSubgoal_2751_);
lean_dec(v___x_2750_);
v___x_2754_ = lean_box(0);
v_isShared_2755_ = v_isSharedCheck_2786_;
goto v_resetjp_2753_;
}
v_resetjp_2753_:
{
lean_object* v_mvarId_2756_; lean_object* v_fields_2757_; lean_object* v_subst_2758_; lean_object* v___x_2760_; uint8_t v_isShared_2761_; uint8_t v_isSharedCheck_2785_; 
v_mvarId_2756_ = lean_ctor_get(v_toInductionSubgoal_2751_, 0);
v_fields_2757_ = lean_ctor_get(v_toInductionSubgoal_2751_, 1);
v_subst_2758_ = lean_ctor_get(v_toInductionSubgoal_2751_, 2);
v_isSharedCheck_2785_ = !lean_is_exclusive(v_toInductionSubgoal_2751_);
if (v_isSharedCheck_2785_ == 0)
{
v___x_2760_ = v_toInductionSubgoal_2751_;
v_isShared_2761_ = v_isSharedCheck_2785_;
goto v_resetjp_2759_;
}
else
{
lean_inc(v_subst_2758_);
lean_inc(v_fields_2757_);
lean_inc(v_mvarId_2756_);
lean_dec(v_toInductionSubgoal_2751_);
v___x_2760_ = lean_box(0);
v_isShared_2761_ = v_isSharedCheck_2785_;
goto v_resetjp_2759_;
}
v_resetjp_2759_:
{
lean_object* v___x_2762_; 
lean_inc_ref(v___y_2741_);
lean_inc(v_ctorName_2752_);
lean_inc(v_numEqs_2734_);
v___x_2762_ = l_Lean_Meta_Cases_unifyEqs_x3f(v_numEqs_2734_, v_mvarId_2756_, v_subst_2758_, v_ctorName_2752_, v___y_2739_, v___y_2740_, v___y_2741_, v___y_2742_);
if (lean_obj_tag(v___x_2762_) == 0)
{
lean_object* v_a_2763_; 
v_a_2763_ = lean_ctor_get(v___x_2762_, 0);
lean_inc(v_a_2763_);
lean_dec_ref_known(v___x_2762_, 1);
if (lean_obj_tag(v_a_2763_) == 0)
{
lean_del_object(v___x_2760_);
lean_dec_ref(v_fields_2757_);
lean_del_object(v___x_2754_);
lean_dec(v_ctorName_2752_);
v_a_2745_ = v_b_2738_;
goto v___jp_2744_;
}
else
{
lean_object* v_val_2764_; lean_object* v_fst_2765_; lean_object* v_snd_2766_; size_t v_sz_2767_; size_t v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2771_; 
v_val_2764_ = lean_ctor_get(v_a_2763_, 0);
lean_inc(v_val_2764_);
lean_dec_ref_known(v_a_2763_, 1);
v_fst_2765_ = lean_ctor_get(v_val_2764_, 0);
lean_inc(v_fst_2765_);
v_snd_2766_ = lean_ctor_get(v_val_2764_, 1);
lean_inc_n(v_snd_2766_, 2);
lean_dec(v_val_2764_);
v_sz_2767_ = lean_array_size(v_fields_2757_);
v___x_2768_ = ((size_t)0ULL);
v___x_2769_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__0(v_snd_2766_, v_sz_2767_, v___x_2768_, v_fields_2757_);
if (v_isShared_2761_ == 0)
{
lean_ctor_set(v___x_2760_, 2, v_snd_2766_);
lean_ctor_set(v___x_2760_, 1, v___x_2769_);
lean_ctor_set(v___x_2760_, 0, v_fst_2765_);
v___x_2771_ = v___x_2760_;
goto v_reusejp_2770_;
}
else
{
lean_object* v_reuseFailAlloc_2776_; 
v_reuseFailAlloc_2776_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2776_, 0, v_fst_2765_);
lean_ctor_set(v_reuseFailAlloc_2776_, 1, v___x_2769_);
lean_ctor_set(v_reuseFailAlloc_2776_, 2, v_snd_2766_);
v___x_2771_ = v_reuseFailAlloc_2776_;
goto v_reusejp_2770_;
}
v_reusejp_2770_:
{
lean_object* v___x_2773_; 
if (v_isShared_2755_ == 0)
{
lean_ctor_set(v___x_2754_, 0, v___x_2771_);
v___x_2773_ = v___x_2754_;
goto v_reusejp_2772_;
}
else
{
lean_object* v_reuseFailAlloc_2775_; 
v_reuseFailAlloc_2775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2775_, 0, v___x_2771_);
lean_ctor_set(v_reuseFailAlloc_2775_, 1, v_ctorName_2752_);
v___x_2773_ = v_reuseFailAlloc_2775_;
goto v_reusejp_2772_;
}
v_reusejp_2772_:
{
lean_object* v___x_2774_; 
v___x_2774_ = lean_array_push(v_b_2738_, v___x_2773_);
v_a_2745_ = v___x_2774_;
goto v___jp_2744_;
}
}
}
}
else
{
lean_object* v_a_2777_; lean_object* v___x_2779_; uint8_t v_isShared_2780_; uint8_t v_isSharedCheck_2784_; 
lean_del_object(v___x_2760_);
lean_dec_ref(v_fields_2757_);
lean_del_object(v___x_2754_);
lean_dec(v_ctorName_2752_);
lean_dec_ref(v_b_2738_);
lean_dec(v_numEqs_2734_);
v_a_2777_ = lean_ctor_get(v___x_2762_, 0);
v_isSharedCheck_2784_ = !lean_is_exclusive(v___x_2762_);
if (v_isSharedCheck_2784_ == 0)
{
v___x_2779_ = v___x_2762_;
v_isShared_2780_ = v_isSharedCheck_2784_;
goto v_resetjp_2778_;
}
else
{
lean_inc(v_a_2777_);
lean_dec(v___x_2762_);
v___x_2779_ = lean_box(0);
v_isShared_2780_ = v_isSharedCheck_2784_;
goto v_resetjp_2778_;
}
v_resetjp_2778_:
{
lean_object* v___x_2782_; 
if (v_isShared_2780_ == 0)
{
v___x_2782_ = v___x_2779_;
goto v_reusejp_2781_;
}
else
{
lean_object* v_reuseFailAlloc_2783_; 
v_reuseFailAlloc_2783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2783_, 0, v_a_2777_);
v___x_2782_ = v_reuseFailAlloc_2783_;
goto v_reusejp_2781_;
}
v_reusejp_2781_:
{
return v___x_2782_;
}
}
}
}
}
}
else
{
lean_object* v___x_2787_; 
lean_dec(v_numEqs_2734_);
v___x_2787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2787_, 0, v_b_2738_);
return v___x_2787_;
}
v___jp_2744_:
{
size_t v___x_2746_; size_t v___x_2747_; 
v___x_2746_ = ((size_t)1ULL);
v___x_2747_ = lean_usize_add(v_i_2736_, v___x_2746_);
v_i_2736_ = v___x_2747_;
v_b_2738_ = v_a_2745_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1_spec__1___boxed(lean_object* v_numEqs_2788_, lean_object* v_as_2789_, lean_object* v_i_2790_, lean_object* v_stop_2791_, lean_object* v_b_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_){
_start:
{
size_t v_i_boxed_2798_; size_t v_stop_boxed_2799_; lean_object* v_res_2800_; 
v_i_boxed_2798_ = lean_unbox_usize(v_i_2790_);
lean_dec(v_i_2790_);
v_stop_boxed_2799_ = lean_unbox_usize(v_stop_2791_);
lean_dec(v_stop_2791_);
v_res_2800_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1_spec__1(v_numEqs_2788_, v_as_2789_, v_i_boxed_2798_, v_stop_boxed_2799_, v_b_2792_, v___y_2793_, v___y_2794_, v___y_2795_, v___y_2796_);
lean_dec(v___y_2796_);
lean_dec_ref(v___y_2795_);
lean_dec(v___y_2794_);
lean_dec_ref(v___y_2793_);
lean_dec_ref(v_as_2789_);
return v_res_2800_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1(lean_object* v_numEqs_2803_, lean_object* v_as_2804_, lean_object* v_start_2805_, lean_object* v_stop_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_){
_start:
{
lean_object* v___x_2812_; uint8_t v___x_2813_; 
v___x_2812_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1___closed__0));
v___x_2813_ = lean_nat_dec_lt(v_start_2805_, v_stop_2806_);
if (v___x_2813_ == 0)
{
lean_object* v___x_2814_; 
lean_dec(v_numEqs_2803_);
v___x_2814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2814_, 0, v___x_2812_);
return v___x_2814_;
}
else
{
lean_object* v___x_2815_; uint8_t v___x_2816_; 
v___x_2815_ = lean_array_get_size(v_as_2804_);
v___x_2816_ = lean_nat_dec_le(v_stop_2806_, v___x_2815_);
if (v___x_2816_ == 0)
{
uint8_t v___x_2817_; 
v___x_2817_ = lean_nat_dec_lt(v_start_2805_, v___x_2815_);
if (v___x_2817_ == 0)
{
lean_object* v___x_2818_; 
lean_dec(v_numEqs_2803_);
v___x_2818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2818_, 0, v___x_2812_);
return v___x_2818_;
}
else
{
size_t v___x_2819_; size_t v___x_2820_; lean_object* v___x_2821_; 
v___x_2819_ = lean_usize_of_nat(v_start_2805_);
v___x_2820_ = lean_usize_of_nat(v___x_2815_);
v___x_2821_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1_spec__1(v_numEqs_2803_, v_as_2804_, v___x_2819_, v___x_2820_, v___x_2812_, v___y_2807_, v___y_2808_, v___y_2809_, v___y_2810_);
return v___x_2821_;
}
}
else
{
size_t v___x_2822_; size_t v___x_2823_; lean_object* v___x_2824_; 
v___x_2822_ = lean_usize_of_nat(v_start_2805_);
v___x_2823_ = lean_usize_of_nat(v_stop_2806_);
v___x_2824_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1_spec__1(v_numEqs_2803_, v_as_2804_, v___x_2822_, v___x_2823_, v___x_2812_, v___y_2807_, v___y_2808_, v___y_2809_, v___y_2810_);
return v___x_2824_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1___boxed(lean_object* v_numEqs_2825_, lean_object* v_as_2826_, lean_object* v_start_2827_, lean_object* v_stop_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_){
_start:
{
lean_object* v_res_2834_; 
v_res_2834_ = l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1(v_numEqs_2825_, v_as_2826_, v_start_2827_, v_stop_2828_, v___y_2829_, v___y_2830_, v___y_2831_, v___y_2832_);
lean_dec(v___y_2832_);
lean_dec_ref(v___y_2831_);
lean_dec(v___y_2830_);
lean_dec_ref(v___y_2829_);
lean_dec(v_stop_2828_);
lean_dec(v_start_2827_);
lean_dec_ref(v_as_2826_);
return v_res_2834_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs(lean_object* v_numEqs_2835_, lean_object* v_subgoals_2836_, lean_object* v_a_2837_, lean_object* v_a_2838_, lean_object* v_a_2839_, lean_object* v_a_2840_){
_start:
{
lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; 
v___x_2842_ = lean_unsigned_to_nat(0u);
v___x_2843_ = lean_array_get_size(v_subgoals_2836_);
v___x_2844_ = l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1(v_numEqs_2835_, v_subgoals_2836_, v___x_2842_, v___x_2843_, v_a_2837_, v_a_2838_, v_a_2839_, v_a_2840_);
return v___x_2844_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs___boxed(lean_object* v_numEqs_2845_, lean_object* v_subgoals_2846_, lean_object* v_a_2847_, lean_object* v_a_2848_, lean_object* v_a_2849_, lean_object* v_a_2850_, lean_object* v_a_2851_){
_start:
{
lean_object* v_res_2852_; 
v_res_2852_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs(v_numEqs_2845_, v_subgoals_2846_, v_a_2847_, v_a_2848_, v_a_2849_, v_a_2850_);
lean_dec(v_a_2850_);
lean_dec_ref(v_a_2849_);
lean_dec(v_a_2848_);
lean_dec_ref(v_a_2847_);
lean_dec_ref(v_subgoals_2846_);
return v_res_2852_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0(lean_object* v___x_2864_, lean_object* v_ctx_2865_, lean_object* v_mvarId_2866_, lean_object* v_majorFVarId_2867_, lean_object* v_givenNames_2868_, uint8_t v_useNatCasesAuxOn_2869_, lean_object* v_interestingCtors_x3f_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_){
_start:
{
lean_object* v___x_2876_; 
lean_inc(v___y_2874_);
lean_inc_ref(v___y_2873_);
lean_inc(v___y_2872_);
lean_inc_ref(v___y_2871_);
v___x_2876_ = lean_infer_type(v___x_2864_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_);
if (lean_obj_tag(v___x_2876_) == 0)
{
lean_object* v_a_2877_; lean_object* v___x_2878_; 
v_a_2877_ = lean_ctor_get(v___x_2876_, 0);
lean_inc(v_a_2877_);
lean_dec_ref_known(v___x_2876_, 1);
v___x_2878_ = l_Lean_Meta_getInductiveUniverseAndParams(v_a_2877_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_);
if (lean_obj_tag(v___x_2878_) == 0)
{
lean_object* v_a_2879_; lean_object* v_fst_2880_; lean_object* v_snd_2881_; lean_object* v___y_2883_; lean_object* v___y_2884_; lean_object* v___y_2885_; lean_object* v___y_2886_; lean_object* v___y_2887_; lean_object* v___y_2910_; lean_object* v___y_2911_; lean_object* v___y_2912_; lean_object* v___y_2913_; lean_object* v___y_2919_; lean_object* v___y_2920_; lean_object* v___y_2921_; lean_object* v___y_2922_; 
v_a_2879_ = lean_ctor_get(v___x_2878_, 0);
lean_inc(v_a_2879_);
lean_dec_ref_known(v___x_2878_, 1);
v_fst_2880_ = lean_ctor_get(v_a_2879_, 0);
lean_inc(v_fst_2880_);
v_snd_2881_ = lean_ctor_get(v_a_2879_, 1);
lean_inc(v_snd_2881_);
lean_dec(v_a_2879_);
if (lean_obj_tag(v_interestingCtors_x3f_2870_) == 1)
{
lean_object* v_val_2932_; lean_object* v___x_2933_; lean_object* v_env_2934_; lean_object* v___x_2935_; uint8_t v___x_2936_; uint8_t v___x_2937_; lean_object* v___x_2938_; lean_object* v_inductiveVal_2939_; lean_object* v_toConstantVal_2940_; lean_object* v_ctors_2941_; lean_object* v_name_2942_; uint8_t v___y_2944_; 
v_val_2932_ = lean_ctor_get(v_interestingCtors_x3f_2870_, 0);
lean_inc(v_val_2932_);
lean_dec_ref_known(v_interestingCtors_x3f_2870_, 1);
v___x_2933_ = lean_st_ref_get(v___y_2874_);
v_env_2934_ = lean_ctor_get(v___x_2933_, 0);
lean_inc_ref(v_env_2934_);
lean_dec(v___x_2933_);
v___x_2935_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__5));
v___x_2936_ = 1;
v___x_2937_ = l_Lean_Environment_contains(v_env_2934_, v___x_2935_, v___x_2936_);
v___x_2938_ = lean_st_ref_get(v___y_2874_);
v_inductiveVal_2939_ = lean_ctor_get(v_ctx_2865_, 0);
v_toConstantVal_2940_ = lean_ctor_get(v_inductiveVal_2939_, 0);
v_ctors_2941_ = lean_ctor_get(v_inductiveVal_2939_, 4);
v_name_2942_ = lean_ctor_get(v_toConstantVal_2940_, 0);
if (v___x_2937_ == 0)
{
lean_dec(v___x_2938_);
v___y_2944_ = v___x_2937_;
goto v___jp_2943_;
}
else
{
lean_object* v_env_2978_; lean_object* v___x_2979_; uint8_t v___x_2980_; 
v_env_2978_ = lean_ctor_get(v___x_2938_, 0);
lean_inc_ref(v_env_2978_);
lean_dec(v___x_2938_);
lean_inc(v_name_2942_);
v___x_2979_ = l_Lean_mkCtorIdxName(v_name_2942_);
v___x_2980_ = l_Lean_Environment_contains(v_env_2978_, v___x_2979_, v___x_2936_);
v___y_2944_ = v___x_2980_;
goto v___jp_2943_;
}
v___jp_2943_:
{
if (v___y_2944_ == 0)
{
lean_dec(v_val_2932_);
v___y_2919_ = v___y_2871_;
v___y_2920_ = v___y_2872_;
v___y_2921_ = v___y_2873_;
v___y_2922_ = v___y_2874_;
goto v___jp_2918_;
}
else
{
lean_object* v___x_2945_; lean_object* v___x_2946_; uint8_t v___x_2947_; 
v___x_2945_ = lean_array_get_size(v_val_2932_);
v___x_2946_ = lean_unsigned_to_nat(0u);
v___x_2947_ = lean_nat_dec_eq(v___x_2945_, v___x_2946_);
if (v___x_2947_ == 0)
{
lean_object* v___x_2948_; uint8_t v___x_2949_; 
v___x_2948_ = l_List_lengthTR___redArg(v_ctors_2941_);
v___x_2949_ = lean_nat_dec_lt(v___x_2945_, v___x_2948_);
lean_dec(v___x_2948_);
if (v___x_2949_ == 0)
{
lean_dec(v_val_2932_);
v___y_2919_ = v___y_2871_;
v___y_2920_ = v___y_2872_;
v___y_2921_ = v___y_2873_;
v___y_2922_ = v___y_2874_;
goto v___jp_2918_;
}
else
{
lean_object* v___x_2950_; 
lean_inc(v_name_2942_);
lean_dec_ref(v_ctx_2865_);
lean_inc(v_val_2932_);
v___x_2950_ = l_Lean_Meta_mkSparseCasesOn(v_name_2942_, v_val_2932_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_);
if (lean_obj_tag(v___x_2950_) == 0)
{
lean_object* v_a_2951_; lean_object* v___x_2952_; 
v_a_2951_ = lean_ctor_get(v___x_2950_, 0);
lean_inc(v_a_2951_);
lean_dec_ref_known(v___x_2950_, 1);
lean_inc(v_majorFVarId_2867_);
v___x_2952_ = l_Lean_MVarId_induction(v_mvarId_2866_, v_majorFVarId_2867_, v_a_2951_, v_givenNames_2868_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_);
lean_dec(v___y_2874_);
lean_dec_ref(v___y_2873_);
lean_dec(v___y_2872_);
lean_dec_ref(v___y_2871_);
if (lean_obj_tag(v___x_2952_) == 0)
{
lean_object* v_a_2953_; lean_object* v___x_2955_; uint8_t v_isShared_2956_; uint8_t v_isSharedCheck_2961_; 
v_a_2953_ = lean_ctor_get(v___x_2952_, 0);
v_isSharedCheck_2961_ = !lean_is_exclusive(v___x_2952_);
if (v_isSharedCheck_2961_ == 0)
{
v___x_2955_ = v___x_2952_;
v_isShared_2956_ = v_isSharedCheck_2961_;
goto v_resetjp_2954_;
}
else
{
lean_inc(v_a_2953_);
lean_dec(v___x_2952_);
v___x_2955_ = lean_box(0);
v_isShared_2956_ = v_isSharedCheck_2961_;
goto v_resetjp_2954_;
}
v_resetjp_2954_:
{
lean_object* v___x_2957_; lean_object* v___x_2959_; 
v___x_2957_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals(v_a_2953_, v_val_2932_, v_majorFVarId_2867_, v_fst_2880_, v_snd_2881_);
lean_dec(v_snd_2881_);
lean_dec(v_val_2932_);
if (v_isShared_2956_ == 0)
{
lean_ctor_set(v___x_2955_, 0, v___x_2957_);
v___x_2959_ = v___x_2955_;
goto v_reusejp_2958_;
}
else
{
lean_object* v_reuseFailAlloc_2960_; 
v_reuseFailAlloc_2960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2960_, 0, v___x_2957_);
v___x_2959_ = v_reuseFailAlloc_2960_;
goto v_reusejp_2958_;
}
v_reusejp_2958_:
{
return v___x_2959_;
}
}
}
else
{
lean_object* v_a_2962_; lean_object* v___x_2964_; uint8_t v_isShared_2965_; uint8_t v_isSharedCheck_2969_; 
lean_dec(v_val_2932_);
lean_dec(v_snd_2881_);
lean_dec(v_fst_2880_);
lean_dec(v_majorFVarId_2867_);
v_a_2962_ = lean_ctor_get(v___x_2952_, 0);
v_isSharedCheck_2969_ = !lean_is_exclusive(v___x_2952_);
if (v_isSharedCheck_2969_ == 0)
{
v___x_2964_ = v___x_2952_;
v_isShared_2965_ = v_isSharedCheck_2969_;
goto v_resetjp_2963_;
}
else
{
lean_inc(v_a_2962_);
lean_dec(v___x_2952_);
v___x_2964_ = lean_box(0);
v_isShared_2965_ = v_isSharedCheck_2969_;
goto v_resetjp_2963_;
}
v_resetjp_2963_:
{
lean_object* v___x_2967_; 
if (v_isShared_2965_ == 0)
{
v___x_2967_ = v___x_2964_;
goto v_reusejp_2966_;
}
else
{
lean_object* v_reuseFailAlloc_2968_; 
v_reuseFailAlloc_2968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2968_, 0, v_a_2962_);
v___x_2967_ = v_reuseFailAlloc_2968_;
goto v_reusejp_2966_;
}
v_reusejp_2966_:
{
return v___x_2967_;
}
}
}
}
else
{
lean_object* v_a_2970_; lean_object* v___x_2972_; uint8_t v_isShared_2973_; uint8_t v_isSharedCheck_2977_; 
lean_dec(v_val_2932_);
lean_dec(v_snd_2881_);
lean_dec(v_fst_2880_);
lean_dec(v___y_2874_);
lean_dec_ref(v___y_2873_);
lean_dec(v___y_2872_);
lean_dec_ref(v___y_2871_);
lean_dec_ref(v_givenNames_2868_);
lean_dec(v_majorFVarId_2867_);
lean_dec(v_mvarId_2866_);
v_a_2970_ = lean_ctor_get(v___x_2950_, 0);
v_isSharedCheck_2977_ = !lean_is_exclusive(v___x_2950_);
if (v_isSharedCheck_2977_ == 0)
{
v___x_2972_ = v___x_2950_;
v_isShared_2973_ = v_isSharedCheck_2977_;
goto v_resetjp_2971_;
}
else
{
lean_inc(v_a_2970_);
lean_dec(v___x_2950_);
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
}
else
{
lean_dec(v_val_2932_);
v___y_2919_ = v___y_2871_;
v___y_2920_ = v___y_2872_;
v___y_2921_ = v___y_2873_;
v___y_2922_ = v___y_2874_;
goto v___jp_2918_;
}
}
}
}
else
{
lean_dec(v_interestingCtors_x3f_2870_);
v___y_2919_ = v___y_2871_;
v___y_2920_ = v___y_2872_;
v___y_2921_ = v___y_2873_;
v___y_2922_ = v___y_2874_;
goto v___jp_2918_;
}
v___jp_2882_:
{
lean_object* v_inductiveVal_2888_; lean_object* v_ctors_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; 
v_inductiveVal_2888_ = lean_ctor_get(v_ctx_2865_, 0);
lean_inc_ref(v_inductiveVal_2888_);
lean_dec_ref(v_ctx_2865_);
v_ctors_2889_ = lean_ctor_get(v_inductiveVal_2888_, 4);
lean_inc(v_ctors_2889_);
lean_dec_ref(v_inductiveVal_2888_);
v___x_2890_ = lean_array_mk(v_ctors_2889_);
lean_inc(v_majorFVarId_2867_);
v___x_2891_ = l_Lean_MVarId_induction(v_mvarId_2866_, v_majorFVarId_2867_, v___y_2887_, v_givenNames_2868_, v___y_2886_, v___y_2885_, v___y_2884_, v___y_2883_);
lean_dec(v___y_2883_);
lean_dec_ref(v___y_2884_);
lean_dec(v___y_2885_);
lean_dec_ref(v___y_2886_);
if (lean_obj_tag(v___x_2891_) == 0)
{
lean_object* v_a_2892_; lean_object* v___x_2894_; uint8_t v_isShared_2895_; uint8_t v_isSharedCheck_2900_; 
v_a_2892_ = lean_ctor_get(v___x_2891_, 0);
v_isSharedCheck_2900_ = !lean_is_exclusive(v___x_2891_);
if (v_isSharedCheck_2900_ == 0)
{
v___x_2894_ = v___x_2891_;
v_isShared_2895_ = v_isSharedCheck_2900_;
goto v_resetjp_2893_;
}
else
{
lean_inc(v_a_2892_);
lean_dec(v___x_2891_);
v___x_2894_ = lean_box(0);
v_isShared_2895_ = v_isSharedCheck_2900_;
goto v_resetjp_2893_;
}
v_resetjp_2893_:
{
lean_object* v___x_2896_; lean_object* v___x_2898_; 
v___x_2896_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals(v_a_2892_, v___x_2890_, v_majorFVarId_2867_, v_fst_2880_, v_snd_2881_);
lean_dec(v_snd_2881_);
lean_dec_ref(v___x_2890_);
if (v_isShared_2895_ == 0)
{
lean_ctor_set(v___x_2894_, 0, v___x_2896_);
v___x_2898_ = v___x_2894_;
goto v_reusejp_2897_;
}
else
{
lean_object* v_reuseFailAlloc_2899_; 
v_reuseFailAlloc_2899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2899_, 0, v___x_2896_);
v___x_2898_ = v_reuseFailAlloc_2899_;
goto v_reusejp_2897_;
}
v_reusejp_2897_:
{
return v___x_2898_;
}
}
}
else
{
lean_object* v_a_2901_; lean_object* v___x_2903_; uint8_t v_isShared_2904_; uint8_t v_isSharedCheck_2908_; 
lean_dec_ref(v___x_2890_);
lean_dec(v_snd_2881_);
lean_dec(v_fst_2880_);
lean_dec(v_majorFVarId_2867_);
v_a_2901_ = lean_ctor_get(v___x_2891_, 0);
v_isSharedCheck_2908_ = !lean_is_exclusive(v___x_2891_);
if (v_isSharedCheck_2908_ == 0)
{
v___x_2903_ = v___x_2891_;
v_isShared_2904_ = v_isSharedCheck_2908_;
goto v_resetjp_2902_;
}
else
{
lean_inc(v_a_2901_);
lean_dec(v___x_2891_);
v___x_2903_ = lean_box(0);
v_isShared_2904_ = v_isSharedCheck_2908_;
goto v_resetjp_2902_;
}
v_resetjp_2902_:
{
lean_object* v___x_2906_; 
if (v_isShared_2904_ == 0)
{
v___x_2906_ = v___x_2903_;
goto v_reusejp_2905_;
}
else
{
lean_object* v_reuseFailAlloc_2907_; 
v_reuseFailAlloc_2907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2907_, 0, v_a_2901_);
v___x_2906_ = v_reuseFailAlloc_2907_;
goto v_reusejp_2905_;
}
v_reusejp_2905_:
{
return v___x_2906_;
}
}
}
}
v___jp_2909_:
{
lean_object* v_inductiveVal_2914_; lean_object* v_toConstantVal_2915_; lean_object* v_name_2916_; lean_object* v___x_2917_; 
v_inductiveVal_2914_ = lean_ctor_get(v_ctx_2865_, 0);
v_toConstantVal_2915_ = lean_ctor_get(v_inductiveVal_2914_, 0);
v_name_2916_ = lean_ctor_get(v_toConstantVal_2915_, 0);
lean_inc(v_name_2916_);
v___x_2917_ = l_Lean_mkCasesOnName(v_name_2916_);
v___y_2883_ = v___y_2910_;
v___y_2884_ = v___y_2911_;
v___y_2885_ = v___y_2912_;
v___y_2886_ = v___y_2913_;
v___y_2887_ = v___x_2917_;
goto v___jp_2882_;
}
v___jp_2918_:
{
lean_object* v___x_2923_; 
v___x_2923_ = lean_st_ref_get(v___y_2922_);
if (v_useNatCasesAuxOn_2869_ == 0)
{
lean_dec(v___x_2923_);
v___y_2910_ = v___y_2922_;
v___y_2911_ = v___y_2921_;
v___y_2912_ = v___y_2920_;
v___y_2913_ = v___y_2919_;
goto v___jp_2909_;
}
else
{
lean_object* v_inductiveVal_2924_; lean_object* v_toConstantVal_2925_; lean_object* v_env_2926_; lean_object* v_name_2927_; lean_object* v___x_2928_; uint8_t v___x_2929_; 
v_inductiveVal_2924_ = lean_ctor_get(v_ctx_2865_, 0);
v_toConstantVal_2925_ = lean_ctor_get(v_inductiveVal_2924_, 0);
v_env_2926_ = lean_ctor_get(v___x_2923_, 0);
lean_inc_ref(v_env_2926_);
lean_dec(v___x_2923_);
v_name_2927_ = lean_ctor_get(v_toConstantVal_2925_, 0);
v___x_2928_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__1));
v___x_2929_ = lean_name_eq(v_name_2927_, v___x_2928_);
if (v___x_2929_ == 0)
{
lean_dec_ref(v_env_2926_);
v___y_2910_ = v___y_2922_;
v___y_2911_ = v___y_2921_;
v___y_2912_ = v___y_2920_;
v___y_2913_ = v___y_2919_;
goto v___jp_2909_;
}
else
{
lean_object* v___x_2930_; uint8_t v___x_2931_; 
v___x_2930_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__3));
v___x_2931_ = l_Lean_Environment_contains(v_env_2926_, v___x_2930_, v___x_2929_);
if (v___x_2931_ == 0)
{
v___y_2910_ = v___y_2922_;
v___y_2911_ = v___y_2921_;
v___y_2912_ = v___y_2920_;
v___y_2913_ = v___y_2919_;
goto v___jp_2909_;
}
else
{
v___y_2883_ = v___y_2922_;
v___y_2884_ = v___y_2921_;
v___y_2885_ = v___y_2920_;
v___y_2886_ = v___y_2919_;
v___y_2887_ = v___x_2930_;
goto v___jp_2882_;
}
}
}
}
}
else
{
lean_object* v_a_2981_; lean_object* v___x_2983_; uint8_t v_isShared_2984_; uint8_t v_isSharedCheck_2988_; 
lean_dec(v___y_2874_);
lean_dec_ref(v___y_2873_);
lean_dec(v___y_2872_);
lean_dec_ref(v___y_2871_);
lean_dec(v_interestingCtors_x3f_2870_);
lean_dec_ref(v_givenNames_2868_);
lean_dec(v_majorFVarId_2867_);
lean_dec(v_mvarId_2866_);
lean_dec_ref(v_ctx_2865_);
v_a_2981_ = lean_ctor_get(v___x_2878_, 0);
v_isSharedCheck_2988_ = !lean_is_exclusive(v___x_2878_);
if (v_isSharedCheck_2988_ == 0)
{
v___x_2983_ = v___x_2878_;
v_isShared_2984_ = v_isSharedCheck_2988_;
goto v_resetjp_2982_;
}
else
{
lean_inc(v_a_2981_);
lean_dec(v___x_2878_);
v___x_2983_ = lean_box(0);
v_isShared_2984_ = v_isSharedCheck_2988_;
goto v_resetjp_2982_;
}
v_resetjp_2982_:
{
lean_object* v___x_2986_; 
if (v_isShared_2984_ == 0)
{
v___x_2986_ = v___x_2983_;
goto v_reusejp_2985_;
}
else
{
lean_object* v_reuseFailAlloc_2987_; 
v_reuseFailAlloc_2987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2987_, 0, v_a_2981_);
v___x_2986_ = v_reuseFailAlloc_2987_;
goto v_reusejp_2985_;
}
v_reusejp_2985_:
{
return v___x_2986_;
}
}
}
}
else
{
lean_object* v_a_2989_; lean_object* v___x_2991_; uint8_t v_isShared_2992_; uint8_t v_isSharedCheck_2996_; 
lean_dec(v___y_2874_);
lean_dec_ref(v___y_2873_);
lean_dec(v___y_2872_);
lean_dec_ref(v___y_2871_);
lean_dec(v_interestingCtors_x3f_2870_);
lean_dec_ref(v_givenNames_2868_);
lean_dec(v_majorFVarId_2867_);
lean_dec(v_mvarId_2866_);
lean_dec_ref(v_ctx_2865_);
v_a_2989_ = lean_ctor_get(v___x_2876_, 0);
v_isSharedCheck_2996_ = !lean_is_exclusive(v___x_2876_);
if (v_isSharedCheck_2996_ == 0)
{
v___x_2991_ = v___x_2876_;
v_isShared_2992_ = v_isSharedCheck_2996_;
goto v_resetjp_2990_;
}
else
{
lean_inc(v_a_2989_);
lean_dec(v___x_2876_);
v___x_2991_ = lean_box(0);
v_isShared_2992_ = v_isSharedCheck_2996_;
goto v_resetjp_2990_;
}
v_resetjp_2990_:
{
lean_object* v___x_2994_; 
if (v_isShared_2992_ == 0)
{
v___x_2994_ = v___x_2991_;
goto v_reusejp_2993_;
}
else
{
lean_object* v_reuseFailAlloc_2995_; 
v_reuseFailAlloc_2995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2995_, 0, v_a_2989_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___boxed(lean_object* v___x_2997_, lean_object* v_ctx_2998_, lean_object* v_mvarId_2999_, lean_object* v_majorFVarId_3000_, lean_object* v_givenNames_3001_, lean_object* v_useNatCasesAuxOn_3002_, lean_object* v_interestingCtors_x3f_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_){
_start:
{
uint8_t v_useNatCasesAuxOn_boxed_3009_; lean_object* v_res_3010_; 
v_useNatCasesAuxOn_boxed_3009_ = lean_unbox(v_useNatCasesAuxOn_3002_);
v_res_3010_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0(v___x_2997_, v_ctx_2998_, v_mvarId_2999_, v_majorFVarId_3000_, v_givenNames_3001_, v_useNatCasesAuxOn_boxed_3009_, v_interestingCtors_x3f_3003_, v___y_3004_, v___y_3005_, v___y_3006_, v___y_3007_);
return v_res_3010_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn(lean_object* v_mvarId_3011_, lean_object* v_majorFVarId_3012_, lean_object* v_givenNames_3013_, lean_object* v_ctx_3014_, uint8_t v_useNatCasesAuxOn_3015_, lean_object* v_interestingCtors_x3f_3016_, lean_object* v_a_3017_, lean_object* v_a_3018_, lean_object* v_a_3019_, lean_object* v_a_3020_){
_start:
{
lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___f_3024_; lean_object* v___x_3025_; 
lean_inc(v_majorFVarId_3012_);
v___x_3022_ = l_Lean_mkFVar(v_majorFVarId_3012_);
v___x_3023_ = lean_box(v_useNatCasesAuxOn_3015_);
lean_inc(v_mvarId_3011_);
v___f_3024_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___boxed), 12, 7);
lean_closure_set(v___f_3024_, 0, v___x_3022_);
lean_closure_set(v___f_3024_, 1, v_ctx_3014_);
lean_closure_set(v___f_3024_, 2, v_mvarId_3011_);
lean_closure_set(v___f_3024_, 3, v_majorFVarId_3012_);
lean_closure_set(v___f_3024_, 4, v_givenNames_3013_);
lean_closure_set(v___f_3024_, 5, v___x_3023_);
lean_closure_set(v___f_3024_, 6, v_interestingCtors_x3f_3016_);
v___x_3025_ = l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2___redArg(v_mvarId_3011_, v___f_3024_, v_a_3017_, v_a_3018_, v_a_3019_, v_a_3020_);
return v___x_3025_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___boxed(lean_object* v_mvarId_3026_, lean_object* v_majorFVarId_3027_, lean_object* v_givenNames_3028_, lean_object* v_ctx_3029_, lean_object* v_useNatCasesAuxOn_3030_, lean_object* v_interestingCtors_x3f_3031_, lean_object* v_a_3032_, lean_object* v_a_3033_, lean_object* v_a_3034_, lean_object* v_a_3035_, lean_object* v_a_3036_){
_start:
{
uint8_t v_useNatCasesAuxOn_boxed_3037_; lean_object* v_res_3038_; 
v_useNatCasesAuxOn_boxed_3037_ = lean_unbox(v_useNatCasesAuxOn_3030_);
v_res_3038_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn(v_mvarId_3026_, v_majorFVarId_3027_, v_givenNames_3028_, v_ctx_3029_, v_useNatCasesAuxOn_boxed_3037_, v_interestingCtors_x3f_3031_, v_a_3032_, v_a_3033_, v_a_3034_, v_a_3035_);
lean_dec(v_a_3035_);
lean_dec_ref(v_a_3034_);
lean_dec(v_a_3033_);
lean_dec_ref(v_a_3032_);
return v_res_3038_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0___closed__0(void){
_start:
{
lean_object* v___x_3039_; double v___x_3040_; 
v___x_3039_ = lean_unsigned_to_nat(0u);
v___x_3040_ = lean_float_of_nat(v___x_3039_);
return v___x_3040_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0(lean_object* v_cls_3044_, lean_object* v_msg_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_){
_start:
{
lean_object* v_ref_3051_; lean_object* v___x_3052_; lean_object* v_a_3053_; lean_object* v___x_3055_; uint8_t v_isShared_3056_; uint8_t v_isSharedCheck_3097_; 
v_ref_3051_ = lean_ctor_get(v___y_3048_, 2);
v___x_3052_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected_spec__0_spec__0(v_msg_3045_, v___y_3046_, v___y_3047_, v___y_3048_, v___y_3049_);
v_a_3053_ = lean_ctor_get(v___x_3052_, 0);
v_isSharedCheck_3097_ = !lean_is_exclusive(v___x_3052_);
if (v_isSharedCheck_3097_ == 0)
{
v___x_3055_ = v___x_3052_;
v_isShared_3056_ = v_isSharedCheck_3097_;
goto v_resetjp_3054_;
}
else
{
lean_inc(v_a_3053_);
lean_dec(v___x_3052_);
v___x_3055_ = lean_box(0);
v_isShared_3056_ = v_isSharedCheck_3097_;
goto v_resetjp_3054_;
}
v_resetjp_3054_:
{
lean_object* v___x_3057_; lean_object* v_traceState_3058_; lean_object* v_env_3059_; lean_object* v_nextMacroScope_3060_; lean_object* v_ngen_3061_; lean_object* v_auxDeclNGen_3062_; lean_object* v_cache_3063_; lean_object* v_messages_3064_; lean_object* v_infoState_3065_; lean_object* v_snapshotTasks_3066_; lean_object* v___x_3068_; uint8_t v_isShared_3069_; uint8_t v_isSharedCheck_3096_; 
v___x_3057_ = lean_st_ref_take(v___y_3049_);
v_traceState_3058_ = lean_ctor_get(v___x_3057_, 4);
v_env_3059_ = lean_ctor_get(v___x_3057_, 0);
v_nextMacroScope_3060_ = lean_ctor_get(v___x_3057_, 1);
v_ngen_3061_ = lean_ctor_get(v___x_3057_, 2);
v_auxDeclNGen_3062_ = lean_ctor_get(v___x_3057_, 3);
v_cache_3063_ = lean_ctor_get(v___x_3057_, 5);
v_messages_3064_ = lean_ctor_get(v___x_3057_, 6);
v_infoState_3065_ = lean_ctor_get(v___x_3057_, 7);
v_snapshotTasks_3066_ = lean_ctor_get(v___x_3057_, 8);
v_isSharedCheck_3096_ = !lean_is_exclusive(v___x_3057_);
if (v_isSharedCheck_3096_ == 0)
{
v___x_3068_ = v___x_3057_;
v_isShared_3069_ = v_isSharedCheck_3096_;
goto v_resetjp_3067_;
}
else
{
lean_inc(v_snapshotTasks_3066_);
lean_inc(v_infoState_3065_);
lean_inc(v_messages_3064_);
lean_inc(v_cache_3063_);
lean_inc(v_traceState_3058_);
lean_inc(v_auxDeclNGen_3062_);
lean_inc(v_ngen_3061_);
lean_inc(v_nextMacroScope_3060_);
lean_inc(v_env_3059_);
lean_dec(v___x_3057_);
v___x_3068_ = lean_box(0);
v_isShared_3069_ = v_isSharedCheck_3096_;
goto v_resetjp_3067_;
}
v_resetjp_3067_:
{
uint64_t v_tid_3070_; lean_object* v_traces_3071_; lean_object* v___x_3073_; uint8_t v_isShared_3074_; uint8_t v_isSharedCheck_3095_; 
v_tid_3070_ = lean_ctor_get_uint64(v_traceState_3058_, sizeof(void*)*1);
v_traces_3071_ = lean_ctor_get(v_traceState_3058_, 0);
v_isSharedCheck_3095_ = !lean_is_exclusive(v_traceState_3058_);
if (v_isSharedCheck_3095_ == 0)
{
v___x_3073_ = v_traceState_3058_;
v_isShared_3074_ = v_isSharedCheck_3095_;
goto v_resetjp_3072_;
}
else
{
lean_inc(v_traces_3071_);
lean_dec(v_traceState_3058_);
v___x_3073_ = lean_box(0);
v_isShared_3074_ = v_isSharedCheck_3095_;
goto v_resetjp_3072_;
}
v_resetjp_3072_:
{
lean_object* v___x_3075_; lean_object* v___x_3076_; double v___x_3077_; uint8_t v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3086_; 
v___x_3075_ = lean_box(0);
v___x_3076_ = lean_box(0);
v___x_3077_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0___closed__0);
v___x_3078_ = 0;
v___x_3079_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0___closed__1));
v___x_3080_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3080_, 0, v_cls_3044_);
lean_ctor_set(v___x_3080_, 1, v___x_3076_);
lean_ctor_set(v___x_3080_, 2, v___x_3079_);
lean_ctor_set_float(v___x_3080_, sizeof(void*)*3, v___x_3077_);
lean_ctor_set_float(v___x_3080_, sizeof(void*)*3 + 8, v___x_3077_);
lean_ctor_set_uint8(v___x_3080_, sizeof(void*)*3 + 16, v___x_3078_);
v___x_3081_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0___closed__2));
v___x_3082_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3082_, 0, v___x_3080_);
lean_ctor_set(v___x_3082_, 1, v_a_3053_);
lean_ctor_set(v___x_3082_, 2, v___x_3081_);
lean_inc(v_ref_3051_);
v___x_3083_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3083_, 0, v_ref_3051_);
lean_ctor_set(v___x_3083_, 1, v___x_3082_);
v___x_3084_ = l_Lean_PersistentArray_push___redArg(v_traces_3071_, v___x_3083_);
if (v_isShared_3074_ == 0)
{
lean_ctor_set(v___x_3073_, 0, v___x_3084_);
v___x_3086_ = v___x_3073_;
goto v_reusejp_3085_;
}
else
{
lean_object* v_reuseFailAlloc_3094_; 
v_reuseFailAlloc_3094_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3094_, 0, v___x_3084_);
lean_ctor_set_uint64(v_reuseFailAlloc_3094_, sizeof(void*)*1, v_tid_3070_);
v___x_3086_ = v_reuseFailAlloc_3094_;
goto v_reusejp_3085_;
}
v_reusejp_3085_:
{
lean_object* v___x_3088_; 
if (v_isShared_3069_ == 0)
{
lean_ctor_set(v___x_3068_, 4, v___x_3086_);
v___x_3088_ = v___x_3068_;
goto v_reusejp_3087_;
}
else
{
lean_object* v_reuseFailAlloc_3093_; 
v_reuseFailAlloc_3093_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3093_, 0, v_env_3059_);
lean_ctor_set(v_reuseFailAlloc_3093_, 1, v_nextMacroScope_3060_);
lean_ctor_set(v_reuseFailAlloc_3093_, 2, v_ngen_3061_);
lean_ctor_set(v_reuseFailAlloc_3093_, 3, v_auxDeclNGen_3062_);
lean_ctor_set(v_reuseFailAlloc_3093_, 4, v___x_3086_);
lean_ctor_set(v_reuseFailAlloc_3093_, 5, v_cache_3063_);
lean_ctor_set(v_reuseFailAlloc_3093_, 6, v_messages_3064_);
lean_ctor_set(v_reuseFailAlloc_3093_, 7, v_infoState_3065_);
lean_ctor_set(v_reuseFailAlloc_3093_, 8, v_snapshotTasks_3066_);
v___x_3088_ = v_reuseFailAlloc_3093_;
goto v_reusejp_3087_;
}
v_reusejp_3087_:
{
lean_object* v___x_3089_; lean_object* v___x_3091_; 
v___x_3089_ = lean_st_ref_put(v___y_3049_, v___x_3088_);
if (v_isShared_3056_ == 0)
{
lean_ctor_set(v___x_3055_, 0, v___x_3075_);
v___x_3091_ = v___x_3055_;
goto v_reusejp_3090_;
}
else
{
lean_object* v_reuseFailAlloc_3092_; 
v_reuseFailAlloc_3092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3092_, 0, v___x_3075_);
v___x_3091_ = v_reuseFailAlloc_3092_;
goto v_reusejp_3090_;
}
v_reusejp_3090_:
{
return v___x_3091_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0___boxed(lean_object* v_cls_3098_, lean_object* v_msg_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_){
_start:
{
lean_object* v_res_3105_; 
v_res_3105_ = l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0(v_cls_3098_, v_msg_3099_, v___y_3100_, v___y_3101_, v___y_3102_, v___y_3103_);
lean_dec(v___y_3103_);
lean_dec_ref(v___y_3102_);
lean_dec(v___y_3101_);
lean_dec_ref(v___y_3100_);
return v_res_3105_;
}
}
static lean_object* _init_l_Lean_Meta_Cases_cases___lam__0___closed__2(void){
_start:
{
lean_object* v___x_3109_; lean_object* v___x_3110_; 
v___x_3109_ = ((lean_object*)(l_Lean_Meta_Cases_cases___lam__0___closed__1));
v___x_3110_ = l_Lean_MessageData_ofFormat(v___x_3109_);
return v___x_3110_;
}
}
static lean_object* _init_l_Lean_Meta_Cases_cases___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3111_; lean_object* v___x_3112_; 
v___x_3111_ = lean_obj_once(&l_Lean_Meta_Cases_cases___lam__0___closed__2, &l_Lean_Meta_Cases_cases___lam__0___closed__2_once, _init_l_Lean_Meta_Cases_cases___lam__0___closed__2);
v___x_3112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3112_, 0, v___x_3111_);
return v___x_3112_;
}
}
static lean_object* _init_l_Lean_Meta_Cases_cases___lam__0___closed__9(void){
_start:
{
lean_object* v___x_3119_; lean_object* v___x_3120_; 
v___x_3119_ = ((lean_object*)(l_Lean_Meta_Cases_cases___lam__0___closed__8));
v___x_3120_ = l_Lean_stringToMessageData(v___x_3119_);
return v___x_3120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_cases___lam__0(lean_object* v_mvarId_3121_, lean_object* v___x_3122_, lean_object* v_majorFVarId_3123_, lean_object* v_givenNames_3124_, lean_object* v_interestingCtors_x3f_3125_, lean_object* v___x_3126_, uint8_t v_useNatCasesAuxOn_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_){
_start:
{
lean_object* v___x_3133_; 
lean_inc(v___x_3122_);
lean_inc(v_mvarId_3121_);
v___x_3133_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_3121_, v___x_3122_, v___y_3128_, v___y_3129_, v___y_3130_, v___y_3131_);
if (lean_obj_tag(v___x_3133_) == 0)
{
lean_object* v___x_3134_; 
lean_dec_ref_known(v___x_3133_, 1);
lean_inc(v_majorFVarId_3123_);
v___x_3134_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f(v_majorFVarId_3123_, v___y_3128_, v___y_3129_, v___y_3130_, v___y_3131_);
if (lean_obj_tag(v___x_3134_) == 0)
{
lean_object* v_a_3135_; 
v_a_3135_ = lean_ctor_get(v___x_3134_, 0);
lean_inc(v_a_3135_);
lean_dec_ref_known(v___x_3134_, 1);
if (lean_obj_tag(v_a_3135_) == 0)
{
lean_object* v___x_3136_; lean_object* v___x_3137_; 
lean_dec_ref(v___x_3126_);
lean_dec(v_interestingCtors_x3f_3125_);
lean_dec_ref(v_givenNames_3124_);
lean_dec(v_majorFVarId_3123_);
v___x_3136_ = lean_obj_once(&l_Lean_Meta_Cases_cases___lam__0___closed__3, &l_Lean_Meta_Cases_cases___lam__0___closed__3_once, _init_l_Lean_Meta_Cases_cases___lam__0___closed__3);
v___x_3137_ = l_Lean_Meta_throwTacticEx___redArg(v___x_3122_, v_mvarId_3121_, v___x_3136_, v___y_3128_, v___y_3129_, v___y_3130_, v___y_3131_);
return v___x_3137_;
}
else
{
lean_object* v_val_3138_; lean_object* v___x_3140_; uint8_t v_isShared_3141_; uint8_t v_isSharedCheck_3203_; 
lean_dec(v___x_3122_);
v_val_3138_ = lean_ctor_get(v_a_3135_, 0);
v_isSharedCheck_3203_ = !lean_is_exclusive(v_a_3135_);
if (v_isSharedCheck_3203_ == 0)
{
v___x_3140_ = v_a_3135_;
v_isShared_3141_ = v_isSharedCheck_3203_;
goto v_resetjp_3139_;
}
else
{
lean_inc(v_val_3138_);
lean_dec(v_a_3135_);
v___x_3140_ = lean_box(0);
v_isShared_3141_ = v_isSharedCheck_3203_;
goto v_resetjp_3139_;
}
v_resetjp_3139_:
{
lean_object* v___x_3142_; 
lean_inc(v_val_3138_);
v___x_3142_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices(v_val_3138_, v___y_3128_, v___y_3129_, v___y_3130_, v___y_3131_);
if (lean_obj_tag(v___x_3142_) == 0)
{
lean_object* v_a_3143_; uint8_t v___x_3144_; 
v_a_3143_ = lean_ctor_get(v___x_3142_, 0);
lean_inc(v_a_3143_);
lean_dec_ref_known(v___x_3142_, 1);
v___x_3144_ = lean_unbox(v_a_3143_);
if (v___x_3144_ == 0)
{
lean_object* v___x_3145_; 
v___x_3145_ = l_Lean_Meta_generalizeIndices(v_mvarId_3121_, v_majorFVarId_3123_, v___y_3128_, v___y_3129_, v___y_3130_, v___y_3131_);
if (lean_obj_tag(v___x_3145_) == 0)
{
lean_object* v_a_3146_; lean_object* v___y_3148_; lean_object* v___y_3149_; lean_object* v___y_3150_; lean_object* v___y_3151_; lean_object* v_toCold_3161_; lean_object* v_options_3162_; uint8_t v_hasTrace_3163_; 
v_a_3146_ = lean_ctor_get(v___x_3145_, 0);
lean_inc(v_a_3146_);
lean_dec_ref_known(v___x_3145_, 1);
v_toCold_3161_ = lean_ctor_get(v___y_3130_, 0);
v_options_3162_ = lean_ctor_get(v_toCold_3161_, 2);
v_hasTrace_3163_ = lean_ctor_get_uint8(v_options_3162_, sizeof(void*)*1);
if (v_hasTrace_3163_ == 0)
{
lean_del_object(v___x_3140_);
lean_dec_ref(v___x_3126_);
v___y_3148_ = v___y_3128_;
v___y_3149_ = v___y_3129_;
v___y_3150_ = v___y_3130_;
v___y_3151_ = v___y_3131_;
goto v___jp_3147_;
}
else
{
lean_object* v_inheritedTraceOptions_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; uint8_t v___x_3170_; 
v_inheritedTraceOptions_3164_ = lean_ctor_get(v_toCold_3161_, 11);
v___x_3165_ = ((lean_object*)(l_Lean_Meta_Cases_cases___lam__0___closed__4));
v___x_3166_ = ((lean_object*)(l_Lean_Meta_Cases_cases___lam__0___closed__5));
v___x_3167_ = l_Lean_Name_mkStr3(v___x_3165_, v___x_3166_, v___x_3126_);
v___x_3168_ = ((lean_object*)(l_Lean_Meta_Cases_cases___lam__0___closed__7));
lean_inc(v___x_3167_);
v___x_3169_ = l_Lean_Name_append(v___x_3168_, v___x_3167_);
v___x_3170_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3164_, v_options_3162_, v___x_3169_);
lean_dec(v___x_3169_);
if (v___x_3170_ == 0)
{
lean_dec(v___x_3167_);
lean_del_object(v___x_3140_);
v___y_3148_ = v___y_3128_;
v___y_3149_ = v___y_3129_;
v___y_3150_ = v___y_3130_;
v___y_3151_ = v___y_3131_;
goto v___jp_3147_;
}
else
{
lean_object* v_mvarId_3171_; lean_object* v___x_3172_; lean_object* v___x_3174_; 
v_mvarId_3171_ = lean_ctor_get(v_a_3146_, 0);
v___x_3172_ = lean_obj_once(&l_Lean_Meta_Cases_cases___lam__0___closed__9, &l_Lean_Meta_Cases_cases___lam__0___closed__9_once, _init_l_Lean_Meta_Cases_cases___lam__0___closed__9);
lean_inc(v_mvarId_3171_);
if (v_isShared_3141_ == 0)
{
lean_ctor_set(v___x_3140_, 0, v_mvarId_3171_);
v___x_3174_ = v___x_3140_;
goto v_reusejp_3173_;
}
else
{
lean_object* v_reuseFailAlloc_3185_; 
v_reuseFailAlloc_3185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3185_, 0, v_mvarId_3171_);
v___x_3174_ = v_reuseFailAlloc_3185_;
goto v_reusejp_3173_;
}
v_reusejp_3173_:
{
lean_object* v___x_3175_; lean_object* v___x_3176_; 
v___x_3175_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3175_, 0, v___x_3172_);
lean_ctor_set(v___x_3175_, 1, v___x_3174_);
v___x_3176_ = l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0(v___x_3167_, v___x_3175_, v___y_3128_, v___y_3129_, v___y_3130_, v___y_3131_);
if (lean_obj_tag(v___x_3176_) == 0)
{
lean_dec_ref_known(v___x_3176_, 1);
v___y_3148_ = v___y_3128_;
v___y_3149_ = v___y_3129_;
v___y_3150_ = v___y_3130_;
v___y_3151_ = v___y_3131_;
goto v___jp_3147_;
}
else
{
lean_object* v_a_3177_; lean_object* v___x_3179_; uint8_t v_isShared_3180_; uint8_t v_isSharedCheck_3184_; 
lean_dec(v_a_3146_);
lean_dec(v_a_3143_);
lean_dec(v_val_3138_);
lean_dec(v_interestingCtors_x3f_3125_);
lean_dec_ref(v_givenNames_3124_);
v_a_3177_ = lean_ctor_get(v___x_3176_, 0);
v_isSharedCheck_3184_ = !lean_is_exclusive(v___x_3176_);
if (v_isSharedCheck_3184_ == 0)
{
v___x_3179_ = v___x_3176_;
v_isShared_3180_ = v_isSharedCheck_3184_;
goto v_resetjp_3178_;
}
else
{
lean_inc(v_a_3177_);
lean_dec(v___x_3176_);
v___x_3179_ = lean_box(0);
v_isShared_3180_ = v_isSharedCheck_3184_;
goto v_resetjp_3178_;
}
v_resetjp_3178_:
{
lean_object* v___x_3182_; 
if (v_isShared_3180_ == 0)
{
v___x_3182_ = v___x_3179_;
goto v_reusejp_3181_;
}
else
{
lean_object* v_reuseFailAlloc_3183_; 
v_reuseFailAlloc_3183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3183_, 0, v_a_3177_);
v___x_3182_ = v_reuseFailAlloc_3183_;
goto v_reusejp_3181_;
}
v_reusejp_3181_:
{
return v___x_3182_;
}
}
}
}
}
}
v___jp_3147_:
{
lean_object* v_mvarId_3152_; lean_object* v_fvarId_3153_; lean_object* v_numEqs_3154_; uint8_t v___x_3155_; lean_object* v___x_3156_; 
v_mvarId_3152_ = lean_ctor_get(v_a_3146_, 0);
v_fvarId_3153_ = lean_ctor_get(v_a_3146_, 2);
v_numEqs_3154_ = lean_ctor_get(v_a_3146_, 3);
lean_inc(v_numEqs_3154_);
v___x_3155_ = lean_unbox(v_a_3143_);
lean_dec(v_a_3143_);
lean_inc(v_fvarId_3153_);
lean_inc(v_mvarId_3152_);
v___x_3156_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn(v_mvarId_3152_, v_fvarId_3153_, v_givenNames_3124_, v_val_3138_, v___x_3155_, v_interestingCtors_x3f_3125_, v___y_3148_, v___y_3149_, v___y_3150_, v___y_3151_);
if (lean_obj_tag(v___x_3156_) == 0)
{
lean_object* v_a_3157_; lean_object* v___x_3158_; 
v_a_3157_ = lean_ctor_get(v___x_3156_, 0);
lean_inc(v_a_3157_);
lean_dec_ref_known(v___x_3156_, 1);
v___x_3158_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices(v_a_3146_, v_a_3157_, v___y_3148_, v___y_3149_, v___y_3150_, v___y_3151_);
lean_dec(v_a_3146_);
if (lean_obj_tag(v___x_3158_) == 0)
{
lean_object* v_a_3159_; lean_object* v___x_3160_; 
v_a_3159_ = lean_ctor_get(v___x_3158_, 0);
lean_inc(v_a_3159_);
lean_dec_ref_known(v___x_3158_, 1);
v___x_3160_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs(v_numEqs_3154_, v_a_3159_, v___y_3148_, v___y_3149_, v___y_3150_, v___y_3151_);
lean_dec(v_a_3159_);
return v___x_3160_;
}
else
{
lean_dec(v_numEqs_3154_);
return v___x_3158_;
}
}
else
{
lean_dec(v_numEqs_3154_);
lean_dec(v_a_3146_);
return v___x_3156_;
}
}
}
else
{
lean_object* v_a_3186_; lean_object* v___x_3188_; uint8_t v_isShared_3189_; uint8_t v_isSharedCheck_3193_; 
lean_dec(v_a_3143_);
lean_del_object(v___x_3140_);
lean_dec(v_val_3138_);
lean_dec_ref(v___x_3126_);
lean_dec(v_interestingCtors_x3f_3125_);
lean_dec_ref(v_givenNames_3124_);
v_a_3186_ = lean_ctor_get(v___x_3145_, 0);
v_isSharedCheck_3193_ = !lean_is_exclusive(v___x_3145_);
if (v_isSharedCheck_3193_ == 0)
{
v___x_3188_ = v___x_3145_;
v_isShared_3189_ = v_isSharedCheck_3193_;
goto v_resetjp_3187_;
}
else
{
lean_inc(v_a_3186_);
lean_dec(v___x_3145_);
v___x_3188_ = lean_box(0);
v_isShared_3189_ = v_isSharedCheck_3193_;
goto v_resetjp_3187_;
}
v_resetjp_3187_:
{
lean_object* v___x_3191_; 
if (v_isShared_3189_ == 0)
{
v___x_3191_ = v___x_3188_;
goto v_reusejp_3190_;
}
else
{
lean_object* v_reuseFailAlloc_3192_; 
v_reuseFailAlloc_3192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3192_, 0, v_a_3186_);
v___x_3191_ = v_reuseFailAlloc_3192_;
goto v_reusejp_3190_;
}
v_reusejp_3190_:
{
return v___x_3191_;
}
}
}
}
else
{
lean_object* v___x_3194_; 
lean_dec(v_a_3143_);
lean_del_object(v___x_3140_);
lean_dec_ref(v___x_3126_);
v___x_3194_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn(v_mvarId_3121_, v_majorFVarId_3123_, v_givenNames_3124_, v_val_3138_, v_useNatCasesAuxOn_3127_, v_interestingCtors_x3f_3125_, v___y_3128_, v___y_3129_, v___y_3130_, v___y_3131_);
return v___x_3194_;
}
}
else
{
lean_object* v_a_3195_; lean_object* v___x_3197_; uint8_t v_isShared_3198_; uint8_t v_isSharedCheck_3202_; 
lean_del_object(v___x_3140_);
lean_dec(v_val_3138_);
lean_dec_ref(v___x_3126_);
lean_dec(v_interestingCtors_x3f_3125_);
lean_dec_ref(v_givenNames_3124_);
lean_dec(v_majorFVarId_3123_);
lean_dec(v_mvarId_3121_);
v_a_3195_ = lean_ctor_get(v___x_3142_, 0);
v_isSharedCheck_3202_ = !lean_is_exclusive(v___x_3142_);
if (v_isSharedCheck_3202_ == 0)
{
v___x_3197_ = v___x_3142_;
v_isShared_3198_ = v_isSharedCheck_3202_;
goto v_resetjp_3196_;
}
else
{
lean_inc(v_a_3195_);
lean_dec(v___x_3142_);
v___x_3197_ = lean_box(0);
v_isShared_3198_ = v_isSharedCheck_3202_;
goto v_resetjp_3196_;
}
v_resetjp_3196_:
{
lean_object* v___x_3200_; 
if (v_isShared_3198_ == 0)
{
v___x_3200_ = v___x_3197_;
goto v_reusejp_3199_;
}
else
{
lean_object* v_reuseFailAlloc_3201_; 
v_reuseFailAlloc_3201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3201_, 0, v_a_3195_);
v___x_3200_ = v_reuseFailAlloc_3201_;
goto v_reusejp_3199_;
}
v_reusejp_3199_:
{
return v___x_3200_;
}
}
}
}
}
}
else
{
lean_object* v_a_3204_; lean_object* v___x_3206_; uint8_t v_isShared_3207_; uint8_t v_isSharedCheck_3211_; 
lean_dec_ref(v___x_3126_);
lean_dec(v_interestingCtors_x3f_3125_);
lean_dec_ref(v_givenNames_3124_);
lean_dec(v_majorFVarId_3123_);
lean_dec(v___x_3122_);
lean_dec(v_mvarId_3121_);
v_a_3204_ = lean_ctor_get(v___x_3134_, 0);
v_isSharedCheck_3211_ = !lean_is_exclusive(v___x_3134_);
if (v_isSharedCheck_3211_ == 0)
{
v___x_3206_ = v___x_3134_;
v_isShared_3207_ = v_isSharedCheck_3211_;
goto v_resetjp_3205_;
}
else
{
lean_inc(v_a_3204_);
lean_dec(v___x_3134_);
v___x_3206_ = lean_box(0);
v_isShared_3207_ = v_isSharedCheck_3211_;
goto v_resetjp_3205_;
}
v_resetjp_3205_:
{
lean_object* v___x_3209_; 
if (v_isShared_3207_ == 0)
{
v___x_3209_ = v___x_3206_;
goto v_reusejp_3208_;
}
else
{
lean_object* v_reuseFailAlloc_3210_; 
v_reuseFailAlloc_3210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3210_, 0, v_a_3204_);
v___x_3209_ = v_reuseFailAlloc_3210_;
goto v_reusejp_3208_;
}
v_reusejp_3208_:
{
return v___x_3209_;
}
}
}
}
else
{
lean_object* v_a_3212_; lean_object* v___x_3214_; uint8_t v_isShared_3215_; uint8_t v_isSharedCheck_3219_; 
lean_dec_ref(v___x_3126_);
lean_dec(v_interestingCtors_x3f_3125_);
lean_dec_ref(v_givenNames_3124_);
lean_dec(v_majorFVarId_3123_);
lean_dec(v___x_3122_);
lean_dec(v_mvarId_3121_);
v_a_3212_ = lean_ctor_get(v___x_3133_, 0);
v_isSharedCheck_3219_ = !lean_is_exclusive(v___x_3133_);
if (v_isSharedCheck_3219_ == 0)
{
v___x_3214_ = v___x_3133_;
v_isShared_3215_ = v_isSharedCheck_3219_;
goto v_resetjp_3213_;
}
else
{
lean_inc(v_a_3212_);
lean_dec(v___x_3133_);
v___x_3214_ = lean_box(0);
v_isShared_3215_ = v_isSharedCheck_3219_;
goto v_resetjp_3213_;
}
v_resetjp_3213_:
{
lean_object* v___x_3217_; 
if (v_isShared_3215_ == 0)
{
v___x_3217_ = v___x_3214_;
goto v_reusejp_3216_;
}
else
{
lean_object* v_reuseFailAlloc_3218_; 
v_reuseFailAlloc_3218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3218_, 0, v_a_3212_);
v___x_3217_ = v_reuseFailAlloc_3218_;
goto v_reusejp_3216_;
}
v_reusejp_3216_:
{
return v___x_3217_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_cases___lam__0___boxed(lean_object* v_mvarId_3220_, lean_object* v___x_3221_, lean_object* v_majorFVarId_3222_, lean_object* v_givenNames_3223_, lean_object* v_interestingCtors_x3f_3224_, lean_object* v___x_3225_, lean_object* v_useNatCasesAuxOn_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_){
_start:
{
uint8_t v_useNatCasesAuxOn_boxed_3232_; lean_object* v_res_3233_; 
v_useNatCasesAuxOn_boxed_3232_ = lean_unbox(v_useNatCasesAuxOn_3226_);
v_res_3233_ = l_Lean_Meta_Cases_cases___lam__0(v_mvarId_3220_, v___x_3221_, v_majorFVarId_3222_, v_givenNames_3223_, v_interestingCtors_x3f_3224_, v___x_3225_, v_useNatCasesAuxOn_boxed_3232_, v___y_3227_, v___y_3228_, v___y_3229_, v___y_3230_);
lean_dec(v___y_3230_);
lean_dec_ref(v___y_3229_);
lean_dec(v___y_3228_);
lean_dec_ref(v___y_3227_);
return v_res_3233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_cases(lean_object* v_mvarId_3237_, lean_object* v_majorFVarId_3238_, lean_object* v_givenNames_3239_, uint8_t v_useNatCasesAuxOn_3240_, lean_object* v_interestingCtors_x3f_3241_, lean_object* v_a_3242_, lean_object* v_a_3243_, lean_object* v_a_3244_, lean_object* v_a_3245_){
_start:
{
lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___f_3250_; lean_object* v___x_3251_; 
v___x_3247_ = ((lean_object*)(l_Lean_Meta_Cases_cases___closed__0));
v___x_3248_ = ((lean_object*)(l_Lean_Meta_Cases_cases___closed__1));
v___x_3249_ = lean_box(v_useNatCasesAuxOn_3240_);
lean_inc(v_mvarId_3237_);
v___f_3250_ = lean_alloc_closure((void*)(l_Lean_Meta_Cases_cases___lam__0___boxed), 12, 7);
lean_closure_set(v___f_3250_, 0, v_mvarId_3237_);
lean_closure_set(v___f_3250_, 1, v___x_3248_);
lean_closure_set(v___f_3250_, 2, v_majorFVarId_3238_);
lean_closure_set(v___f_3250_, 3, v_givenNames_3239_);
lean_closure_set(v___f_3250_, 4, v_interestingCtors_x3f_3241_);
lean_closure_set(v___f_3250_, 5, v___x_3247_);
lean_closure_set(v___f_3250_, 6, v___x_3249_);
v___x_3251_ = l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2___redArg(v_mvarId_3237_, v___f_3250_, v_a_3242_, v_a_3243_, v_a_3244_, v_a_3245_);
if (lean_obj_tag(v___x_3251_) == 0)
{
return v___x_3251_;
}
else
{
lean_object* v_a_3252_; uint8_t v___y_3254_; uint8_t v___x_3256_; 
v_a_3252_ = lean_ctor_get(v___x_3251_, 0);
lean_inc(v_a_3252_);
v___x_3256_ = l_Lean_Exception_isInterrupt(v_a_3252_);
if (v___x_3256_ == 0)
{
uint8_t v___x_3257_; 
lean_inc(v_a_3252_);
v___x_3257_ = l_Lean_Exception_isRuntime(v_a_3252_);
v___y_3254_ = v___x_3257_;
goto v___jp_3253_;
}
else
{
v___y_3254_ = v___x_3256_;
goto v___jp_3253_;
}
v___jp_3253_:
{
if (v___y_3254_ == 0)
{
lean_object* v___x_3255_; 
lean_dec_ref_known(v___x_3251_, 1);
v___x_3255_ = l_Lean_Meta_throwNestedTacticEx___redArg(v___x_3248_, v_a_3252_, v_a_3242_, v_a_3243_, v_a_3244_, v_a_3245_);
return v___x_3255_;
}
else
{
lean_dec(v_a_3252_);
return v___x_3251_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_cases___boxed(lean_object* v_mvarId_3258_, lean_object* v_majorFVarId_3259_, lean_object* v_givenNames_3260_, lean_object* v_useNatCasesAuxOn_3261_, lean_object* v_interestingCtors_x3f_3262_, lean_object* v_a_3263_, lean_object* v_a_3264_, lean_object* v_a_3265_, lean_object* v_a_3266_, lean_object* v_a_3267_){
_start:
{
uint8_t v_useNatCasesAuxOn_boxed_3268_; lean_object* v_res_3269_; 
v_useNatCasesAuxOn_boxed_3268_ = lean_unbox(v_useNatCasesAuxOn_3261_);
v_res_3269_ = l_Lean_Meta_Cases_cases(v_mvarId_3258_, v_majorFVarId_3259_, v_givenNames_3260_, v_useNatCasesAuxOn_boxed_3268_, v_interestingCtors_x3f_3262_, v_a_3263_, v_a_3264_, v_a_3265_, v_a_3266_);
lean_dec(v_a_3266_);
lean_dec_ref(v_a_3265_);
lean_dec(v_a_3264_);
lean_dec_ref(v_a_3263_);
return v_res_3269_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_cases(lean_object* v_mvarId_3270_, lean_object* v_majorFVarId_3271_, lean_object* v_givenNames_3272_, uint8_t v_useNatCasesAuxOn_3273_, lean_object* v_interestingCtors_x3f_3274_, lean_object* v_a_3275_, lean_object* v_a_3276_, lean_object* v_a_3277_, lean_object* v_a_3278_){
_start:
{
lean_object* v___x_3280_; 
v___x_3280_ = l_Lean_Meta_Cases_cases(v_mvarId_3270_, v_majorFVarId_3271_, v_givenNames_3272_, v_useNatCasesAuxOn_3273_, v_interestingCtors_x3f_3274_, v_a_3275_, v_a_3276_, v_a_3277_, v_a_3278_);
return v___x_3280_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_cases___boxed(lean_object* v_mvarId_3281_, lean_object* v_majorFVarId_3282_, lean_object* v_givenNames_3283_, lean_object* v_useNatCasesAuxOn_3284_, lean_object* v_interestingCtors_x3f_3285_, lean_object* v_a_3286_, lean_object* v_a_3287_, lean_object* v_a_3288_, lean_object* v_a_3289_, lean_object* v_a_3290_){
_start:
{
uint8_t v_useNatCasesAuxOn_boxed_3291_; lean_object* v_res_3292_; 
v_useNatCasesAuxOn_boxed_3291_ = lean_unbox(v_useNatCasesAuxOn_3284_);
v_res_3292_ = l_Lean_MVarId_cases(v_mvarId_3281_, v_majorFVarId_3282_, v_givenNames_3283_, v_useNatCasesAuxOn_boxed_3291_, v_interestingCtors_x3f_3285_, v_a_3286_, v_a_3287_, v_a_3288_, v_a_3289_);
lean_dec(v_a_3289_);
lean_dec_ref(v_a_3288_);
lean_dec(v_a_3287_);
lean_dec_ref(v_a_3286_);
return v_res_3292_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1___redArg(lean_object* v_x_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_){
_start:
{
lean_object* v___x_3299_; 
v___x_3299_ = l_Lean_Meta_saveState___redArg(v___y_3295_, v___y_3297_);
if (lean_obj_tag(v___x_3299_) == 0)
{
lean_object* v_a_3300_; lean_object* v___x_3301_; 
v_a_3300_ = lean_ctor_get(v___x_3299_, 0);
lean_inc(v_a_3300_);
lean_dec_ref_known(v___x_3299_, 1);
lean_inc(v___y_3297_);
lean_inc_ref(v___y_3296_);
lean_inc(v___y_3295_);
lean_inc_ref(v___y_3294_);
v___x_3301_ = lean_apply_5(v_x_3293_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_, lean_box(0));
if (lean_obj_tag(v___x_3301_) == 0)
{
lean_object* v_a_3302_; lean_object* v___x_3304_; uint8_t v_isShared_3305_; uint8_t v_isSharedCheck_3310_; 
lean_dec(v_a_3300_);
v_a_3302_ = lean_ctor_get(v___x_3301_, 0);
v_isSharedCheck_3310_ = !lean_is_exclusive(v___x_3301_);
if (v_isSharedCheck_3310_ == 0)
{
v___x_3304_ = v___x_3301_;
v_isShared_3305_ = v_isSharedCheck_3310_;
goto v_resetjp_3303_;
}
else
{
lean_inc(v_a_3302_);
lean_dec(v___x_3301_);
v___x_3304_ = lean_box(0);
v_isShared_3305_ = v_isSharedCheck_3310_;
goto v_resetjp_3303_;
}
v_resetjp_3303_:
{
lean_object* v___x_3306_; lean_object* v___x_3308_; 
v___x_3306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3306_, 0, v_a_3302_);
if (v_isShared_3305_ == 0)
{
lean_ctor_set(v___x_3304_, 0, v___x_3306_);
v___x_3308_ = v___x_3304_;
goto v_reusejp_3307_;
}
else
{
lean_object* v_reuseFailAlloc_3309_; 
v_reuseFailAlloc_3309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3309_, 0, v___x_3306_);
v___x_3308_ = v_reuseFailAlloc_3309_;
goto v_reusejp_3307_;
}
v_reusejp_3307_:
{
return v___x_3308_;
}
}
}
else
{
lean_object* v_a_3311_; lean_object* v___x_3313_; uint8_t v_isShared_3314_; uint8_t v_isSharedCheck_3340_; 
v_a_3311_ = lean_ctor_get(v___x_3301_, 0);
v_isSharedCheck_3340_ = !lean_is_exclusive(v___x_3301_);
if (v_isSharedCheck_3340_ == 0)
{
v___x_3313_ = v___x_3301_;
v_isShared_3314_ = v_isSharedCheck_3340_;
goto v_resetjp_3312_;
}
else
{
lean_inc(v_a_3311_);
lean_dec(v___x_3301_);
v___x_3313_ = lean_box(0);
v_isShared_3314_ = v_isSharedCheck_3340_;
goto v_resetjp_3312_;
}
v_resetjp_3312_:
{
uint8_t v___y_3316_; uint8_t v___x_3338_; 
v___x_3338_ = l_Lean_Exception_isInterrupt(v_a_3311_);
if (v___x_3338_ == 0)
{
uint8_t v___x_3339_; 
lean_inc(v_a_3311_);
v___x_3339_ = l_Lean_Exception_isRuntime(v_a_3311_);
v___y_3316_ = v___x_3339_;
goto v___jp_3315_;
}
else
{
v___y_3316_ = v___x_3338_;
goto v___jp_3315_;
}
v___jp_3315_:
{
if (v___y_3316_ == 0)
{
lean_object* v___x_3317_; 
lean_del_object(v___x_3313_);
lean_dec(v_a_3311_);
v___x_3317_ = l_Lean_Meta_SavedState_restore___redArg(v_a_3300_, v___y_3295_, v___y_3297_);
lean_dec(v_a_3300_);
if (lean_obj_tag(v___x_3317_) == 0)
{
lean_object* v___x_3319_; uint8_t v_isShared_3320_; uint8_t v_isSharedCheck_3325_; 
v_isSharedCheck_3325_ = !lean_is_exclusive(v___x_3317_);
if (v_isSharedCheck_3325_ == 0)
{
lean_object* v_unused_3326_; 
v_unused_3326_ = lean_ctor_get(v___x_3317_, 0);
lean_dec(v_unused_3326_);
v___x_3319_ = v___x_3317_;
v_isShared_3320_ = v_isSharedCheck_3325_;
goto v_resetjp_3318_;
}
else
{
lean_dec(v___x_3317_);
v___x_3319_ = lean_box(0);
v_isShared_3320_ = v_isSharedCheck_3325_;
goto v_resetjp_3318_;
}
v_resetjp_3318_:
{
lean_object* v___x_3321_; lean_object* v___x_3323_; 
v___x_3321_ = lean_box(0);
if (v_isShared_3320_ == 0)
{
lean_ctor_set(v___x_3319_, 0, v___x_3321_);
v___x_3323_ = v___x_3319_;
goto v_reusejp_3322_;
}
else
{
lean_object* v_reuseFailAlloc_3324_; 
v_reuseFailAlloc_3324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3324_, 0, v___x_3321_);
v___x_3323_ = v_reuseFailAlloc_3324_;
goto v_reusejp_3322_;
}
v_reusejp_3322_:
{
return v___x_3323_;
}
}
}
else
{
lean_object* v_a_3327_; lean_object* v___x_3329_; uint8_t v_isShared_3330_; uint8_t v_isSharedCheck_3334_; 
v_a_3327_ = lean_ctor_get(v___x_3317_, 0);
v_isSharedCheck_3334_ = !lean_is_exclusive(v___x_3317_);
if (v_isSharedCheck_3334_ == 0)
{
v___x_3329_ = v___x_3317_;
v_isShared_3330_ = v_isSharedCheck_3334_;
goto v_resetjp_3328_;
}
else
{
lean_inc(v_a_3327_);
lean_dec(v___x_3317_);
v___x_3329_ = lean_box(0);
v_isShared_3330_ = v_isSharedCheck_3334_;
goto v_resetjp_3328_;
}
v_resetjp_3328_:
{
lean_object* v___x_3332_; 
if (v_isShared_3330_ == 0)
{
v___x_3332_ = v___x_3329_;
goto v_reusejp_3331_;
}
else
{
lean_object* v_reuseFailAlloc_3333_; 
v_reuseFailAlloc_3333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3333_, 0, v_a_3327_);
v___x_3332_ = v_reuseFailAlloc_3333_;
goto v_reusejp_3331_;
}
v_reusejp_3331_:
{
return v___x_3332_;
}
}
}
}
else
{
lean_object* v___x_3336_; 
lean_dec(v_a_3300_);
if (v_isShared_3314_ == 0)
{
v___x_3336_ = v___x_3313_;
goto v_reusejp_3335_;
}
else
{
lean_object* v_reuseFailAlloc_3337_; 
v_reuseFailAlloc_3337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3337_, 0, v_a_3311_);
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
}
}
else
{
lean_object* v_a_3341_; lean_object* v___x_3343_; uint8_t v_isShared_3344_; uint8_t v_isSharedCheck_3348_; 
lean_dec_ref(v_x_3293_);
v_a_3341_ = lean_ctor_get(v___x_3299_, 0);
v_isSharedCheck_3348_ = !lean_is_exclusive(v___x_3299_);
if (v_isSharedCheck_3348_ == 0)
{
v___x_3343_ = v___x_3299_;
v_isShared_3344_ = v_isSharedCheck_3348_;
goto v_resetjp_3342_;
}
else
{
lean_inc(v_a_3341_);
lean_dec(v___x_3299_);
v___x_3343_ = lean_box(0);
v_isShared_3344_ = v_isSharedCheck_3348_;
goto v_resetjp_3342_;
}
v_resetjp_3342_:
{
lean_object* v___x_3346_; 
if (v_isShared_3344_ == 0)
{
v___x_3346_ = v___x_3343_;
goto v_reusejp_3345_;
}
else
{
lean_object* v_reuseFailAlloc_3347_; 
v_reuseFailAlloc_3347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3347_, 0, v_a_3341_);
v___x_3346_ = v_reuseFailAlloc_3347_;
goto v_reusejp_3345_;
}
v_reusejp_3345_:
{
return v___x_3346_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1___redArg___boxed(lean_object* v_x_3349_, lean_object* v___y_3350_, lean_object* v___y_3351_, lean_object* v___y_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_){
_start:
{
lean_object* v_res_3355_; 
v_res_3355_ = l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1___redArg(v_x_3349_, v___y_3350_, v___y_3351_, v___y_3352_, v___y_3353_);
lean_dec(v___y_3353_);
lean_dec_ref(v___y_3352_);
lean_dec(v___y_3351_);
lean_dec_ref(v___y_3350_);
return v_res_3355_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1(lean_object* v_00_u03b1_3356_, lean_object* v_x_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_, lean_object* v___y_3360_, lean_object* v___y_3361_){
_start:
{
lean_object* v___x_3363_; 
v___x_3363_ = l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1___redArg(v_x_3357_, v___y_3358_, v___y_3359_, v___y_3360_, v___y_3361_);
return v___x_3363_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1___boxed(lean_object* v_00_u03b1_3364_, lean_object* v_x_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_){
_start:
{
lean_object* v_res_3371_; 
v_res_3371_ = l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1(v_00_u03b1_3364_, v_x_3365_, v___y_3366_, v___y_3367_, v___y_3368_, v___y_3369_);
lean_dec(v___y_3369_);
lean_dec_ref(v___y_3368_);
lean_dec(v___y_3367_);
lean_dec_ref(v___y_3366_);
return v_res_3371_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_MVarId_casesRec_spec__0(lean_object* v_a_3372_, lean_object* v_a_3373_){
_start:
{
if (lean_obj_tag(v_a_3372_) == 0)
{
lean_object* v___x_3374_; 
v___x_3374_ = l_List_reverse___redArg(v_a_3373_);
return v___x_3374_;
}
else
{
lean_object* v_head_3375_; lean_object* v_toInductionSubgoal_3376_; lean_object* v_tail_3377_; lean_object* v___x_3379_; uint8_t v_isShared_3380_; uint8_t v_isSharedCheck_3386_; 
v_head_3375_ = lean_ctor_get(v_a_3372_, 0);
v_toInductionSubgoal_3376_ = lean_ctor_get(v_head_3375_, 0);
lean_inc_ref(v_toInductionSubgoal_3376_);
v_tail_3377_ = lean_ctor_get(v_a_3372_, 1);
v_isSharedCheck_3386_ = !lean_is_exclusive(v_a_3372_);
if (v_isSharedCheck_3386_ == 0)
{
lean_object* v_unused_3387_; 
v_unused_3387_ = lean_ctor_get(v_a_3372_, 0);
lean_dec(v_unused_3387_);
v___x_3379_ = v_a_3372_;
v_isShared_3380_ = v_isSharedCheck_3386_;
goto v_resetjp_3378_;
}
else
{
lean_inc(v_tail_3377_);
lean_dec(v_a_3372_);
v___x_3379_ = lean_box(0);
v_isShared_3380_ = v_isSharedCheck_3386_;
goto v_resetjp_3378_;
}
v_resetjp_3378_:
{
lean_object* v_mvarId_3381_; lean_object* v___x_3383_; 
v_mvarId_3381_ = lean_ctor_get(v_toInductionSubgoal_3376_, 0);
lean_inc(v_mvarId_3381_);
lean_dec_ref(v_toInductionSubgoal_3376_);
if (v_isShared_3380_ == 0)
{
lean_ctor_set(v___x_3379_, 1, v_a_3373_);
lean_ctor_set(v___x_3379_, 0, v_mvarId_3381_);
v___x_3383_ = v___x_3379_;
goto v_reusejp_3382_;
}
else
{
lean_object* v_reuseFailAlloc_3385_; 
v_reuseFailAlloc_3385_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3385_, 0, v_mvarId_3381_);
lean_ctor_set(v_reuseFailAlloc_3385_, 1, v_a_3373_);
v___x_3383_ = v_reuseFailAlloc_3385_;
goto v_reusejp_3382_;
}
v_reusejp_3382_:
{
v_a_3372_ = v_tail_3377_;
v_a_3373_ = v___x_3383_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3___lam__0(lean_object* v_mvarId_3388_, lean_object* v___x_3389_, lean_object* v___x_3390_, uint8_t v___x_3391_, lean_object* v___x_3392_, lean_object* v___y_3393_, lean_object* v___y_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_){
_start:
{
lean_object* v___x_3398_; 
v___x_3398_ = l_Lean_Meta_Cases_cases(v_mvarId_3388_, v___x_3389_, v___x_3390_, v___x_3391_, v___x_3392_, v___y_3393_, v___y_3394_, v___y_3395_, v___y_3396_);
if (lean_obj_tag(v___x_3398_) == 0)
{
lean_object* v_a_3399_; lean_object* v___x_3401_; uint8_t v_isShared_3402_; uint8_t v_isSharedCheck_3409_; 
v_a_3399_ = lean_ctor_get(v___x_3398_, 0);
v_isSharedCheck_3409_ = !lean_is_exclusive(v___x_3398_);
if (v_isSharedCheck_3409_ == 0)
{
v___x_3401_ = v___x_3398_;
v_isShared_3402_ = v_isSharedCheck_3409_;
goto v_resetjp_3400_;
}
else
{
lean_inc(v_a_3399_);
lean_dec(v___x_3398_);
v___x_3401_ = lean_box(0);
v_isShared_3402_ = v_isSharedCheck_3409_;
goto v_resetjp_3400_;
}
v_resetjp_3400_:
{
lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3407_; 
v___x_3403_ = lean_array_to_list(v_a_3399_);
v___x_3404_ = lean_box(0);
v___x_3405_ = l_List_mapTR_loop___at___00Lean_MVarId_casesRec_spec__0(v___x_3403_, v___x_3404_);
if (v_isShared_3402_ == 0)
{
lean_ctor_set(v___x_3401_, 0, v___x_3405_);
v___x_3407_ = v___x_3401_;
goto v_reusejp_3406_;
}
else
{
lean_object* v_reuseFailAlloc_3408_; 
v_reuseFailAlloc_3408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3408_, 0, v___x_3405_);
v___x_3407_ = v_reuseFailAlloc_3408_;
goto v_reusejp_3406_;
}
v_reusejp_3406_:
{
return v___x_3407_;
}
}
}
else
{
lean_object* v_a_3410_; lean_object* v___x_3412_; uint8_t v_isShared_3413_; uint8_t v_isSharedCheck_3417_; 
v_a_3410_ = lean_ctor_get(v___x_3398_, 0);
v_isSharedCheck_3417_ = !lean_is_exclusive(v___x_3398_);
if (v_isSharedCheck_3417_ == 0)
{
v___x_3412_ = v___x_3398_;
v_isShared_3413_ = v_isSharedCheck_3417_;
goto v_resetjp_3411_;
}
else
{
lean_inc(v_a_3410_);
lean_dec(v___x_3398_);
v___x_3412_ = lean_box(0);
v_isShared_3413_ = v_isSharedCheck_3417_;
goto v_resetjp_3411_;
}
v_resetjp_3411_:
{
lean_object* v___x_3415_; 
if (v_isShared_3413_ == 0)
{
v___x_3415_ = v___x_3412_;
goto v_reusejp_3414_;
}
else
{
lean_object* v_reuseFailAlloc_3416_; 
v_reuseFailAlloc_3416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3416_, 0, v_a_3410_);
v___x_3415_ = v_reuseFailAlloc_3416_;
goto v_reusejp_3414_;
}
v_reusejp_3414_:
{
return v___x_3415_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3___lam__0___boxed(lean_object* v_mvarId_3418_, lean_object* v___x_3419_, lean_object* v___x_3420_, lean_object* v___x_3421_, lean_object* v___x_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_){
_start:
{
uint8_t v___x_6247__boxed_3428_; lean_object* v_res_3429_; 
v___x_6247__boxed_3428_ = lean_unbox(v___x_3421_);
v_res_3429_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3___lam__0(v_mvarId_3418_, v___x_3419_, v___x_3420_, v___x_6247__boxed_3428_, v___x_3422_, v___y_3423_, v___y_3424_, v___y_3425_, v___y_3426_);
lean_dec(v___y_3426_);
lean_dec_ref(v___y_3425_);
lean_dec(v___y_3424_);
lean_dec_ref(v___y_3423_);
return v_res_3429_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5(lean_object* v_p_3435_, lean_object* v_mvarId_3436_, lean_object* v_as_3437_, size_t v_sz_3438_, size_t v_i_3439_, lean_object* v_b_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_, lean_object* v___y_3444_){
_start:
{
uint8_t v___x_3446_; 
v___x_3446_ = lean_usize_dec_lt(v_i_3439_, v_sz_3438_);
if (v___x_3446_ == 0)
{
lean_object* v___x_3447_; 
lean_dec(v_mvarId_3436_);
lean_dec_ref(v_p_3435_);
v___x_3447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3447_, 0, v_b_3440_);
return v___x_3447_;
}
else
{
lean_object* v_snd_3448_; lean_object* v___x_3450_; uint8_t v_isShared_3451_; uint8_t v_isSharedCheck_3516_; 
v_snd_3448_ = lean_ctor_get(v_b_3440_, 1);
v_isSharedCheck_3516_ = !lean_is_exclusive(v_b_3440_);
if (v_isSharedCheck_3516_ == 0)
{
lean_object* v_unused_3517_; 
v_unused_3517_ = lean_ctor_get(v_b_3440_, 0);
lean_dec(v_unused_3517_);
v___x_3450_ = v_b_3440_;
v_isShared_3451_ = v_isSharedCheck_3516_;
goto v_resetjp_3449_;
}
else
{
lean_inc(v_snd_3448_);
lean_dec(v_b_3440_);
v___x_3450_ = lean_box(0);
v_isShared_3451_ = v_isSharedCheck_3516_;
goto v_resetjp_3449_;
}
v_resetjp_3449_:
{
lean_object* v___x_3452_; lean_object* v_a_3454_; lean_object* v_a_3461_; 
v___x_3452_ = lean_box(0);
v_a_3461_ = lean_array_uget(v_as_3437_, v_i_3439_);
if (lean_obj_tag(v_a_3461_) == 0)
{
v_a_3454_ = v_snd_3448_;
goto v___jp_3453_;
}
else
{
lean_object* v_val_3462_; lean_object* v___x_3464_; uint8_t v_isShared_3465_; uint8_t v_isSharedCheck_3515_; 
v_val_3462_ = lean_ctor_get(v_a_3461_, 0);
v_isSharedCheck_3515_ = !lean_is_exclusive(v_a_3461_);
if (v_isSharedCheck_3515_ == 0)
{
v___x_3464_ = v_a_3461_;
v_isShared_3465_ = v_isSharedCheck_3515_;
goto v_resetjp_3463_;
}
else
{
lean_inc(v_val_3462_);
lean_dec(v_a_3461_);
v___x_3464_ = lean_box(0);
v_isShared_3465_ = v_isSharedCheck_3515_;
goto v_resetjp_3463_;
}
v_resetjp_3463_:
{
lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; 
v___x_3466_ = lean_box(0);
v___x_3467_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5___closed__0));
lean_inc_ref(v_p_3435_);
lean_inc(v___y_3444_);
lean_inc_ref(v___y_3443_);
lean_inc(v___y_3442_);
lean_inc_ref(v___y_3441_);
lean_inc(v_val_3462_);
v___x_3468_ = lean_apply_6(v_p_3435_, v_val_3462_, v___y_3441_, v___y_3442_, v___y_3443_, v___y_3444_, lean_box(0));
if (lean_obj_tag(v___x_3468_) == 0)
{
lean_object* v_a_3469_; uint8_t v___x_3470_; 
v_a_3469_ = lean_ctor_get(v___x_3468_, 0);
lean_inc(v_a_3469_);
lean_dec_ref_known(v___x_3468_, 1);
v___x_3470_ = lean_unbox(v_a_3469_);
lean_dec(v_a_3469_);
if (v___x_3470_ == 0)
{
lean_del_object(v___x_3464_);
lean_dec(v_val_3462_);
lean_dec(v_snd_3448_);
v_a_3454_ = v___x_3467_;
goto v___jp_3453_;
}
else
{
lean_object* v___x_3471_; lean_object* v___x_3472_; uint8_t v___x_3473_; lean_object* v___x_3474_; lean_object* v___f_3475_; lean_object* v___x_3476_; 
v___x_3471_ = l_Lean_LocalDecl_fvarId(v_val_3462_);
lean_dec(v_val_3462_);
v___x_3472_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5___closed__1));
v___x_3473_ = 0;
v___x_3474_ = lean_box(v___x_3473_);
lean_inc(v_mvarId_3436_);
v___f_3475_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3___lam__0___boxed), 10, 5);
lean_closure_set(v___f_3475_, 0, v_mvarId_3436_);
lean_closure_set(v___f_3475_, 1, v___x_3471_);
lean_closure_set(v___f_3475_, 2, v___x_3472_);
lean_closure_set(v___f_3475_, 3, v___x_3474_);
lean_closure_set(v___f_3475_, 4, v___x_3452_);
v___x_3476_ = l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1___redArg(v___f_3475_, v___y_3441_, v___y_3442_, v___y_3443_, v___y_3444_);
if (lean_obj_tag(v___x_3476_) == 0)
{
lean_object* v_a_3477_; lean_object* v___x_3479_; uint8_t v_isShared_3480_; uint8_t v_isSharedCheck_3498_; 
v_a_3477_ = lean_ctor_get(v___x_3476_, 0);
v_isSharedCheck_3498_ = !lean_is_exclusive(v___x_3476_);
if (v_isSharedCheck_3498_ == 0)
{
v___x_3479_ = v___x_3476_;
v_isShared_3480_ = v_isSharedCheck_3498_;
goto v_resetjp_3478_;
}
else
{
lean_inc(v_a_3477_);
lean_dec(v___x_3476_);
v___x_3479_ = lean_box(0);
v_isShared_3480_ = v_isSharedCheck_3498_;
goto v_resetjp_3478_;
}
v_resetjp_3478_:
{
if (lean_obj_tag(v_a_3477_) == 0)
{
lean_del_object(v___x_3479_);
lean_del_object(v___x_3464_);
lean_dec(v_snd_3448_);
v_a_3454_ = v___x_3467_;
goto v___jp_3453_;
}
else
{
lean_object* v___x_3482_; 
lean_del_object(v___x_3450_);
lean_dec(v_mvarId_3436_);
lean_dec_ref(v_p_3435_);
lean_inc_ref(v_a_3477_);
if (v_isShared_3465_ == 0)
{
lean_ctor_set(v___x_3464_, 0, v_a_3477_);
v___x_3482_ = v___x_3464_;
goto v_reusejp_3481_;
}
else
{
lean_object* v_reuseFailAlloc_3497_; 
v_reuseFailAlloc_3497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3497_, 0, v_a_3477_);
v___x_3482_ = v_reuseFailAlloc_3497_;
goto v_reusejp_3481_;
}
v_reusejp_3481_:
{
lean_object* v___x_3484_; uint8_t v_isShared_3485_; uint8_t v_isSharedCheck_3495_; 
v_isSharedCheck_3495_ = !lean_is_exclusive(v_a_3477_);
if (v_isSharedCheck_3495_ == 0)
{
lean_object* v_unused_3496_; 
v_unused_3496_ = lean_ctor_get(v_a_3477_, 0);
lean_dec(v_unused_3496_);
v___x_3484_ = v_a_3477_;
v_isShared_3485_ = v_isSharedCheck_3495_;
goto v_resetjp_3483_;
}
else
{
lean_dec(v_a_3477_);
v___x_3484_ = lean_box(0);
v_isShared_3485_ = v_isSharedCheck_3495_;
goto v_resetjp_3483_;
}
v_resetjp_3483_:
{
lean_object* v___x_3486_; lean_object* v___x_3488_; 
v___x_3486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3486_, 0, v___x_3482_);
lean_ctor_set(v___x_3486_, 1, v___x_3466_);
if (v_isShared_3485_ == 0)
{
lean_ctor_set_tag(v___x_3484_, 0);
lean_ctor_set(v___x_3484_, 0, v___x_3486_);
v___x_3488_ = v___x_3484_;
goto v_reusejp_3487_;
}
else
{
lean_object* v_reuseFailAlloc_3494_; 
v_reuseFailAlloc_3494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3494_, 0, v___x_3486_);
v___x_3488_ = v_reuseFailAlloc_3494_;
goto v_reusejp_3487_;
}
v_reusejp_3487_:
{
lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3492_; 
v___x_3489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3489_, 0, v___x_3488_);
v___x_3490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3490_, 0, v___x_3489_);
lean_ctor_set(v___x_3490_, 1, v_snd_3448_);
if (v_isShared_3480_ == 0)
{
lean_ctor_set(v___x_3479_, 0, v___x_3490_);
v___x_3492_ = v___x_3479_;
goto v_reusejp_3491_;
}
else
{
lean_object* v_reuseFailAlloc_3493_; 
v_reuseFailAlloc_3493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3493_, 0, v___x_3490_);
v___x_3492_ = v_reuseFailAlloc_3493_;
goto v_reusejp_3491_;
}
v_reusejp_3491_:
{
return v___x_3492_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3499_; lean_object* v___x_3501_; uint8_t v_isShared_3502_; uint8_t v_isSharedCheck_3506_; 
lean_del_object(v___x_3464_);
lean_del_object(v___x_3450_);
lean_dec(v_snd_3448_);
lean_dec(v_mvarId_3436_);
lean_dec_ref(v_p_3435_);
v_a_3499_ = lean_ctor_get(v___x_3476_, 0);
v_isSharedCheck_3506_ = !lean_is_exclusive(v___x_3476_);
if (v_isSharedCheck_3506_ == 0)
{
v___x_3501_ = v___x_3476_;
v_isShared_3502_ = v_isSharedCheck_3506_;
goto v_resetjp_3500_;
}
else
{
lean_inc(v_a_3499_);
lean_dec(v___x_3476_);
v___x_3501_ = lean_box(0);
v_isShared_3502_ = v_isSharedCheck_3506_;
goto v_resetjp_3500_;
}
v_resetjp_3500_:
{
lean_object* v___x_3504_; 
if (v_isShared_3502_ == 0)
{
v___x_3504_ = v___x_3501_;
goto v_reusejp_3503_;
}
else
{
lean_object* v_reuseFailAlloc_3505_; 
v_reuseFailAlloc_3505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3505_, 0, v_a_3499_);
v___x_3504_ = v_reuseFailAlloc_3505_;
goto v_reusejp_3503_;
}
v_reusejp_3503_:
{
return v___x_3504_;
}
}
}
}
}
else
{
lean_object* v_a_3507_; lean_object* v___x_3509_; uint8_t v_isShared_3510_; uint8_t v_isSharedCheck_3514_; 
lean_del_object(v___x_3464_);
lean_dec(v_val_3462_);
lean_del_object(v___x_3450_);
lean_dec(v_snd_3448_);
lean_dec(v_mvarId_3436_);
lean_dec_ref(v_p_3435_);
v_a_3507_ = lean_ctor_get(v___x_3468_, 0);
v_isSharedCheck_3514_ = !lean_is_exclusive(v___x_3468_);
if (v_isSharedCheck_3514_ == 0)
{
v___x_3509_ = v___x_3468_;
v_isShared_3510_ = v_isSharedCheck_3514_;
goto v_resetjp_3508_;
}
else
{
lean_inc(v_a_3507_);
lean_dec(v___x_3468_);
v___x_3509_ = lean_box(0);
v_isShared_3510_ = v_isSharedCheck_3514_;
goto v_resetjp_3508_;
}
v_resetjp_3508_:
{
lean_object* v___x_3512_; 
if (v_isShared_3510_ == 0)
{
v___x_3512_ = v___x_3509_;
goto v_reusejp_3511_;
}
else
{
lean_object* v_reuseFailAlloc_3513_; 
v_reuseFailAlloc_3513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3513_, 0, v_a_3507_);
v___x_3512_ = v_reuseFailAlloc_3513_;
goto v_reusejp_3511_;
}
v_reusejp_3511_:
{
return v___x_3512_;
}
}
}
}
}
v___jp_3453_:
{
lean_object* v___x_3456_; 
if (v_isShared_3451_ == 0)
{
lean_ctor_set(v___x_3450_, 1, v_a_3454_);
lean_ctor_set(v___x_3450_, 0, v___x_3452_);
v___x_3456_ = v___x_3450_;
goto v_reusejp_3455_;
}
else
{
lean_object* v_reuseFailAlloc_3460_; 
v_reuseFailAlloc_3460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3460_, 0, v___x_3452_);
lean_ctor_set(v_reuseFailAlloc_3460_, 1, v_a_3454_);
v___x_3456_ = v_reuseFailAlloc_3460_;
goto v_reusejp_3455_;
}
v_reusejp_3455_:
{
size_t v___x_3457_; size_t v___x_3458_; 
v___x_3457_ = ((size_t)1ULL);
v___x_3458_ = lean_usize_add(v_i_3439_, v___x_3457_);
v_i_3439_ = v___x_3458_;
v_b_3440_ = v___x_3456_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5___boxed(lean_object* v_p_3518_, lean_object* v_mvarId_3519_, lean_object* v_as_3520_, lean_object* v_sz_3521_, lean_object* v_i_3522_, lean_object* v_b_3523_, lean_object* v___y_3524_, lean_object* v___y_3525_, lean_object* v___y_3526_, lean_object* v___y_3527_, lean_object* v___y_3528_){
_start:
{
size_t v_sz_boxed_3529_; size_t v_i_boxed_3530_; lean_object* v_res_3531_; 
v_sz_boxed_3529_ = lean_unbox_usize(v_sz_3521_);
lean_dec(v_sz_3521_);
v_i_boxed_3530_ = lean_unbox_usize(v_i_3522_);
lean_dec(v_i_3522_);
v_res_3531_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5(v_p_3518_, v_mvarId_3519_, v_as_3520_, v_sz_boxed_3529_, v_i_boxed_3530_, v_b_3523_, v___y_3524_, v___y_3525_, v___y_3526_, v___y_3527_);
lean_dec(v___y_3527_);
lean_dec_ref(v___y_3526_);
lean_dec(v___y_3525_);
lean_dec_ref(v___y_3524_);
lean_dec_ref(v_as_3520_);
return v_res_3531_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4(lean_object* v_p_3532_, lean_object* v_mvarId_3533_, lean_object* v_as_3534_, size_t v_sz_3535_, size_t v_i_3536_, lean_object* v_b_3537_, lean_object* v___y_3538_, lean_object* v___y_3539_, lean_object* v___y_3540_, lean_object* v___y_3541_){
_start:
{
uint8_t v___x_3543_; 
v___x_3543_ = lean_usize_dec_lt(v_i_3536_, v_sz_3535_);
if (v___x_3543_ == 0)
{
lean_object* v___x_3544_; 
lean_dec(v_mvarId_3533_);
lean_dec_ref(v_p_3532_);
v___x_3544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3544_, 0, v_b_3537_);
return v___x_3544_;
}
else
{
lean_object* v_snd_3545_; lean_object* v___x_3547_; uint8_t v_isShared_3548_; uint8_t v_isSharedCheck_3613_; 
v_snd_3545_ = lean_ctor_get(v_b_3537_, 1);
v_isSharedCheck_3613_ = !lean_is_exclusive(v_b_3537_);
if (v_isSharedCheck_3613_ == 0)
{
lean_object* v_unused_3614_; 
v_unused_3614_ = lean_ctor_get(v_b_3537_, 0);
lean_dec(v_unused_3614_);
v___x_3547_ = v_b_3537_;
v_isShared_3548_ = v_isSharedCheck_3613_;
goto v_resetjp_3546_;
}
else
{
lean_inc(v_snd_3545_);
lean_dec(v_b_3537_);
v___x_3547_ = lean_box(0);
v_isShared_3548_ = v_isSharedCheck_3613_;
goto v_resetjp_3546_;
}
v_resetjp_3546_:
{
lean_object* v___x_3549_; lean_object* v_a_3551_; lean_object* v_a_3558_; 
v___x_3549_ = lean_box(0);
v_a_3558_ = lean_array_uget(v_as_3534_, v_i_3536_);
if (lean_obj_tag(v_a_3558_) == 0)
{
v_a_3551_ = v_snd_3545_;
goto v___jp_3550_;
}
else
{
lean_object* v_val_3559_; lean_object* v___x_3561_; uint8_t v_isShared_3562_; uint8_t v_isSharedCheck_3612_; 
v_val_3559_ = lean_ctor_get(v_a_3558_, 0);
v_isSharedCheck_3612_ = !lean_is_exclusive(v_a_3558_);
if (v_isSharedCheck_3612_ == 0)
{
v___x_3561_ = v_a_3558_;
v_isShared_3562_ = v_isSharedCheck_3612_;
goto v_resetjp_3560_;
}
else
{
lean_inc(v_val_3559_);
lean_dec(v_a_3558_);
v___x_3561_ = lean_box(0);
v_isShared_3562_ = v_isSharedCheck_3612_;
goto v_resetjp_3560_;
}
v_resetjp_3560_:
{
lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; 
v___x_3563_ = lean_box(0);
v___x_3564_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5___closed__0));
lean_inc_ref(v_p_3532_);
lean_inc(v___y_3541_);
lean_inc_ref(v___y_3540_);
lean_inc(v___y_3539_);
lean_inc_ref(v___y_3538_);
lean_inc(v_val_3559_);
v___x_3565_ = lean_apply_6(v_p_3532_, v_val_3559_, v___y_3538_, v___y_3539_, v___y_3540_, v___y_3541_, lean_box(0));
if (lean_obj_tag(v___x_3565_) == 0)
{
lean_object* v_a_3566_; uint8_t v___x_3567_; 
v_a_3566_ = lean_ctor_get(v___x_3565_, 0);
lean_inc(v_a_3566_);
lean_dec_ref_known(v___x_3565_, 1);
v___x_3567_ = lean_unbox(v_a_3566_);
lean_dec(v_a_3566_);
if (v___x_3567_ == 0)
{
lean_del_object(v___x_3561_);
lean_dec(v_val_3559_);
lean_dec(v_snd_3545_);
v_a_3551_ = v___x_3564_;
goto v___jp_3550_;
}
else
{
lean_object* v___x_3568_; lean_object* v___x_3569_; uint8_t v___x_3570_; lean_object* v___x_3571_; lean_object* v___f_3572_; lean_object* v___x_3573_; 
v___x_3568_ = l_Lean_LocalDecl_fvarId(v_val_3559_);
lean_dec(v_val_3559_);
v___x_3569_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5___closed__1));
v___x_3570_ = 0;
v___x_3571_ = lean_box(v___x_3570_);
lean_inc(v_mvarId_3533_);
v___f_3572_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3___lam__0___boxed), 10, 5);
lean_closure_set(v___f_3572_, 0, v_mvarId_3533_);
lean_closure_set(v___f_3572_, 1, v___x_3568_);
lean_closure_set(v___f_3572_, 2, v___x_3569_);
lean_closure_set(v___f_3572_, 3, v___x_3571_);
lean_closure_set(v___f_3572_, 4, v___x_3549_);
v___x_3573_ = l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1___redArg(v___f_3572_, v___y_3538_, v___y_3539_, v___y_3540_, v___y_3541_);
if (lean_obj_tag(v___x_3573_) == 0)
{
lean_object* v_a_3574_; lean_object* v___x_3576_; uint8_t v_isShared_3577_; uint8_t v_isSharedCheck_3595_; 
v_a_3574_ = lean_ctor_get(v___x_3573_, 0);
v_isSharedCheck_3595_ = !lean_is_exclusive(v___x_3573_);
if (v_isSharedCheck_3595_ == 0)
{
v___x_3576_ = v___x_3573_;
v_isShared_3577_ = v_isSharedCheck_3595_;
goto v_resetjp_3575_;
}
else
{
lean_inc(v_a_3574_);
lean_dec(v___x_3573_);
v___x_3576_ = lean_box(0);
v_isShared_3577_ = v_isSharedCheck_3595_;
goto v_resetjp_3575_;
}
v_resetjp_3575_:
{
if (lean_obj_tag(v_a_3574_) == 0)
{
lean_del_object(v___x_3576_);
lean_del_object(v___x_3561_);
lean_dec(v_snd_3545_);
v_a_3551_ = v___x_3564_;
goto v___jp_3550_;
}
else
{
lean_object* v___x_3579_; 
lean_del_object(v___x_3547_);
lean_dec(v_mvarId_3533_);
lean_dec_ref(v_p_3532_);
lean_inc_ref(v_a_3574_);
if (v_isShared_3562_ == 0)
{
lean_ctor_set(v___x_3561_, 0, v_a_3574_);
v___x_3579_ = v___x_3561_;
goto v_reusejp_3578_;
}
else
{
lean_object* v_reuseFailAlloc_3594_; 
v_reuseFailAlloc_3594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3594_, 0, v_a_3574_);
v___x_3579_ = v_reuseFailAlloc_3594_;
goto v_reusejp_3578_;
}
v_reusejp_3578_:
{
lean_object* v___x_3581_; uint8_t v_isShared_3582_; uint8_t v_isSharedCheck_3592_; 
v_isSharedCheck_3592_ = !lean_is_exclusive(v_a_3574_);
if (v_isSharedCheck_3592_ == 0)
{
lean_object* v_unused_3593_; 
v_unused_3593_ = lean_ctor_get(v_a_3574_, 0);
lean_dec(v_unused_3593_);
v___x_3581_ = v_a_3574_;
v_isShared_3582_ = v_isSharedCheck_3592_;
goto v_resetjp_3580_;
}
else
{
lean_dec(v_a_3574_);
v___x_3581_ = lean_box(0);
v_isShared_3582_ = v_isSharedCheck_3592_;
goto v_resetjp_3580_;
}
v_resetjp_3580_:
{
lean_object* v___x_3583_; lean_object* v___x_3585_; 
v___x_3583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3583_, 0, v___x_3579_);
lean_ctor_set(v___x_3583_, 1, v___x_3563_);
if (v_isShared_3582_ == 0)
{
lean_ctor_set_tag(v___x_3581_, 0);
lean_ctor_set(v___x_3581_, 0, v___x_3583_);
v___x_3585_ = v___x_3581_;
goto v_reusejp_3584_;
}
else
{
lean_object* v_reuseFailAlloc_3591_; 
v_reuseFailAlloc_3591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3591_, 0, v___x_3583_);
v___x_3585_ = v_reuseFailAlloc_3591_;
goto v_reusejp_3584_;
}
v_reusejp_3584_:
{
lean_object* v___x_3586_; lean_object* v___x_3587_; lean_object* v___x_3589_; 
v___x_3586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3586_, 0, v___x_3585_);
v___x_3587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3587_, 0, v___x_3586_);
lean_ctor_set(v___x_3587_, 1, v_snd_3545_);
if (v_isShared_3577_ == 0)
{
lean_ctor_set(v___x_3576_, 0, v___x_3587_);
v___x_3589_ = v___x_3576_;
goto v_reusejp_3588_;
}
else
{
lean_object* v_reuseFailAlloc_3590_; 
v_reuseFailAlloc_3590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3590_, 0, v___x_3587_);
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
}
}
else
{
lean_object* v_a_3596_; lean_object* v___x_3598_; uint8_t v_isShared_3599_; uint8_t v_isSharedCheck_3603_; 
lean_del_object(v___x_3561_);
lean_del_object(v___x_3547_);
lean_dec(v_snd_3545_);
lean_dec(v_mvarId_3533_);
lean_dec_ref(v_p_3532_);
v_a_3596_ = lean_ctor_get(v___x_3573_, 0);
v_isSharedCheck_3603_ = !lean_is_exclusive(v___x_3573_);
if (v_isSharedCheck_3603_ == 0)
{
v___x_3598_ = v___x_3573_;
v_isShared_3599_ = v_isSharedCheck_3603_;
goto v_resetjp_3597_;
}
else
{
lean_inc(v_a_3596_);
lean_dec(v___x_3573_);
v___x_3598_ = lean_box(0);
v_isShared_3599_ = v_isSharedCheck_3603_;
goto v_resetjp_3597_;
}
v_resetjp_3597_:
{
lean_object* v___x_3601_; 
if (v_isShared_3599_ == 0)
{
v___x_3601_ = v___x_3598_;
goto v_reusejp_3600_;
}
else
{
lean_object* v_reuseFailAlloc_3602_; 
v_reuseFailAlloc_3602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3602_, 0, v_a_3596_);
v___x_3601_ = v_reuseFailAlloc_3602_;
goto v_reusejp_3600_;
}
v_reusejp_3600_:
{
return v___x_3601_;
}
}
}
}
}
else
{
lean_object* v_a_3604_; lean_object* v___x_3606_; uint8_t v_isShared_3607_; uint8_t v_isSharedCheck_3611_; 
lean_del_object(v___x_3561_);
lean_dec(v_val_3559_);
lean_del_object(v___x_3547_);
lean_dec(v_snd_3545_);
lean_dec(v_mvarId_3533_);
lean_dec_ref(v_p_3532_);
v_a_3604_ = lean_ctor_get(v___x_3565_, 0);
v_isSharedCheck_3611_ = !lean_is_exclusive(v___x_3565_);
if (v_isSharedCheck_3611_ == 0)
{
v___x_3606_ = v___x_3565_;
v_isShared_3607_ = v_isSharedCheck_3611_;
goto v_resetjp_3605_;
}
else
{
lean_inc(v_a_3604_);
lean_dec(v___x_3565_);
v___x_3606_ = lean_box(0);
v_isShared_3607_ = v_isSharedCheck_3611_;
goto v_resetjp_3605_;
}
v_resetjp_3605_:
{
lean_object* v___x_3609_; 
if (v_isShared_3607_ == 0)
{
v___x_3609_ = v___x_3606_;
goto v_reusejp_3608_;
}
else
{
lean_object* v_reuseFailAlloc_3610_; 
v_reuseFailAlloc_3610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3610_, 0, v_a_3604_);
v___x_3609_ = v_reuseFailAlloc_3610_;
goto v_reusejp_3608_;
}
v_reusejp_3608_:
{
return v___x_3609_;
}
}
}
}
}
v___jp_3550_:
{
lean_object* v___x_3553_; 
if (v_isShared_3548_ == 0)
{
lean_ctor_set(v___x_3547_, 1, v_a_3551_);
lean_ctor_set(v___x_3547_, 0, v___x_3549_);
v___x_3553_ = v___x_3547_;
goto v_reusejp_3552_;
}
else
{
lean_object* v_reuseFailAlloc_3557_; 
v_reuseFailAlloc_3557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3557_, 0, v___x_3549_);
lean_ctor_set(v_reuseFailAlloc_3557_, 1, v_a_3551_);
v___x_3553_ = v_reuseFailAlloc_3557_;
goto v_reusejp_3552_;
}
v_reusejp_3552_:
{
size_t v___x_3554_; size_t v___x_3555_; lean_object* v___x_3556_; 
v___x_3554_ = ((size_t)1ULL);
v___x_3555_ = lean_usize_add(v_i_3536_, v___x_3554_);
v___x_3556_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5(v_p_3532_, v_mvarId_3533_, v_as_3534_, v_sz_3535_, v___x_3555_, v___x_3553_, v___y_3538_, v___y_3539_, v___y_3540_, v___y_3541_);
return v___x_3556_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4___boxed(lean_object* v_p_3615_, lean_object* v_mvarId_3616_, lean_object* v_as_3617_, lean_object* v_sz_3618_, lean_object* v_i_3619_, lean_object* v_b_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_, lean_object* v___y_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_){
_start:
{
size_t v_sz_boxed_3626_; size_t v_i_boxed_3627_; lean_object* v_res_3628_; 
v_sz_boxed_3626_ = lean_unbox_usize(v_sz_3618_);
lean_dec(v_sz_3618_);
v_i_boxed_3627_ = lean_unbox_usize(v_i_3619_);
lean_dec(v_i_3619_);
v_res_3628_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4(v_p_3615_, v_mvarId_3616_, v_as_3617_, v_sz_boxed_3626_, v_i_boxed_3627_, v_b_3620_, v___y_3621_, v___y_3622_, v___y_3623_, v___y_3624_);
lean_dec(v___y_3624_);
lean_dec_ref(v___y_3623_);
lean_dec(v___y_3622_);
lean_dec_ref(v___y_3621_);
lean_dec_ref(v_as_3617_);
return v_res_3628_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2(lean_object* v_init_3629_, lean_object* v_p_3630_, lean_object* v_mvarId_3631_, lean_object* v_n_3632_, lean_object* v_b_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_){
_start:
{
if (lean_obj_tag(v_n_3632_) == 0)
{
lean_object* v_cs_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; size_t v_sz_3642_; size_t v___x_3643_; lean_object* v___x_3644_; 
v_cs_3639_ = lean_ctor_get(v_n_3632_, 0);
v___x_3640_ = lean_box(0);
v___x_3641_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3641_, 0, v___x_3640_);
lean_ctor_set(v___x_3641_, 1, v_b_3633_);
v_sz_3642_ = lean_array_size(v_cs_3639_);
v___x_3643_ = ((size_t)0ULL);
v___x_3644_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__3(v_init_3629_, v_p_3630_, v_mvarId_3631_, v_cs_3639_, v_sz_3642_, v___x_3643_, v___x_3641_, v___y_3634_, v___y_3635_, v___y_3636_, v___y_3637_);
if (lean_obj_tag(v___x_3644_) == 0)
{
lean_object* v_a_3645_; lean_object* v___x_3647_; uint8_t v_isShared_3648_; uint8_t v_isSharedCheck_3659_; 
v_a_3645_ = lean_ctor_get(v___x_3644_, 0);
v_isSharedCheck_3659_ = !lean_is_exclusive(v___x_3644_);
if (v_isSharedCheck_3659_ == 0)
{
v___x_3647_ = v___x_3644_;
v_isShared_3648_ = v_isSharedCheck_3659_;
goto v_resetjp_3646_;
}
else
{
lean_inc(v_a_3645_);
lean_dec(v___x_3644_);
v___x_3647_ = lean_box(0);
v_isShared_3648_ = v_isSharedCheck_3659_;
goto v_resetjp_3646_;
}
v_resetjp_3646_:
{
lean_object* v_fst_3649_; 
v_fst_3649_ = lean_ctor_get(v_a_3645_, 0);
if (lean_obj_tag(v_fst_3649_) == 0)
{
lean_object* v_snd_3650_; lean_object* v___x_3651_; lean_object* v___x_3653_; 
v_snd_3650_ = lean_ctor_get(v_a_3645_, 1);
lean_inc(v_snd_3650_);
lean_dec(v_a_3645_);
v___x_3651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3651_, 0, v_snd_3650_);
if (v_isShared_3648_ == 0)
{
lean_ctor_set(v___x_3647_, 0, v___x_3651_);
v___x_3653_ = v___x_3647_;
goto v_reusejp_3652_;
}
else
{
lean_object* v_reuseFailAlloc_3654_; 
v_reuseFailAlloc_3654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3654_, 0, v___x_3651_);
v___x_3653_ = v_reuseFailAlloc_3654_;
goto v_reusejp_3652_;
}
v_reusejp_3652_:
{
return v___x_3653_;
}
}
else
{
lean_object* v_val_3655_; lean_object* v___x_3657_; 
lean_inc_ref(v_fst_3649_);
lean_dec(v_a_3645_);
v_val_3655_ = lean_ctor_get(v_fst_3649_, 0);
lean_inc(v_val_3655_);
lean_dec_ref_known(v_fst_3649_, 1);
if (v_isShared_3648_ == 0)
{
lean_ctor_set(v___x_3647_, 0, v_val_3655_);
v___x_3657_ = v___x_3647_;
goto v_reusejp_3656_;
}
else
{
lean_object* v_reuseFailAlloc_3658_; 
v_reuseFailAlloc_3658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3658_, 0, v_val_3655_);
v___x_3657_ = v_reuseFailAlloc_3658_;
goto v_reusejp_3656_;
}
v_reusejp_3656_:
{
return v___x_3657_;
}
}
}
}
else
{
lean_object* v_a_3660_; lean_object* v___x_3662_; uint8_t v_isShared_3663_; uint8_t v_isSharedCheck_3667_; 
v_a_3660_ = lean_ctor_get(v___x_3644_, 0);
v_isSharedCheck_3667_ = !lean_is_exclusive(v___x_3644_);
if (v_isSharedCheck_3667_ == 0)
{
v___x_3662_ = v___x_3644_;
v_isShared_3663_ = v_isSharedCheck_3667_;
goto v_resetjp_3661_;
}
else
{
lean_inc(v_a_3660_);
lean_dec(v___x_3644_);
v___x_3662_ = lean_box(0);
v_isShared_3663_ = v_isSharedCheck_3667_;
goto v_resetjp_3661_;
}
v_resetjp_3661_:
{
lean_object* v___x_3665_; 
if (v_isShared_3663_ == 0)
{
v___x_3665_ = v___x_3662_;
goto v_reusejp_3664_;
}
else
{
lean_object* v_reuseFailAlloc_3666_; 
v_reuseFailAlloc_3666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3666_, 0, v_a_3660_);
v___x_3665_ = v_reuseFailAlloc_3666_;
goto v_reusejp_3664_;
}
v_reusejp_3664_:
{
return v___x_3665_;
}
}
}
}
else
{
lean_object* v_vs_3668_; lean_object* v___x_3669_; lean_object* v___x_3670_; size_t v_sz_3671_; size_t v___x_3672_; lean_object* v___x_3673_; 
v_vs_3668_ = lean_ctor_get(v_n_3632_, 0);
v___x_3669_ = lean_box(0);
v___x_3670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3670_, 0, v___x_3669_);
lean_ctor_set(v___x_3670_, 1, v_b_3633_);
v_sz_3671_ = lean_array_size(v_vs_3668_);
v___x_3672_ = ((size_t)0ULL);
v___x_3673_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4(v_p_3630_, v_mvarId_3631_, v_vs_3668_, v_sz_3671_, v___x_3672_, v___x_3670_, v___y_3634_, v___y_3635_, v___y_3636_, v___y_3637_);
if (lean_obj_tag(v___x_3673_) == 0)
{
lean_object* v_a_3674_; lean_object* v___x_3676_; uint8_t v_isShared_3677_; uint8_t v_isSharedCheck_3688_; 
v_a_3674_ = lean_ctor_get(v___x_3673_, 0);
v_isSharedCheck_3688_ = !lean_is_exclusive(v___x_3673_);
if (v_isSharedCheck_3688_ == 0)
{
v___x_3676_ = v___x_3673_;
v_isShared_3677_ = v_isSharedCheck_3688_;
goto v_resetjp_3675_;
}
else
{
lean_inc(v_a_3674_);
lean_dec(v___x_3673_);
v___x_3676_ = lean_box(0);
v_isShared_3677_ = v_isSharedCheck_3688_;
goto v_resetjp_3675_;
}
v_resetjp_3675_:
{
lean_object* v_fst_3678_; 
v_fst_3678_ = lean_ctor_get(v_a_3674_, 0);
if (lean_obj_tag(v_fst_3678_) == 0)
{
lean_object* v_snd_3679_; lean_object* v___x_3680_; lean_object* v___x_3682_; 
v_snd_3679_ = lean_ctor_get(v_a_3674_, 1);
lean_inc(v_snd_3679_);
lean_dec(v_a_3674_);
v___x_3680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3680_, 0, v_snd_3679_);
if (v_isShared_3677_ == 0)
{
lean_ctor_set(v___x_3676_, 0, v___x_3680_);
v___x_3682_ = v___x_3676_;
goto v_reusejp_3681_;
}
else
{
lean_object* v_reuseFailAlloc_3683_; 
v_reuseFailAlloc_3683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3683_, 0, v___x_3680_);
v___x_3682_ = v_reuseFailAlloc_3683_;
goto v_reusejp_3681_;
}
v_reusejp_3681_:
{
return v___x_3682_;
}
}
else
{
lean_object* v_val_3684_; lean_object* v___x_3686_; 
lean_inc_ref(v_fst_3678_);
lean_dec(v_a_3674_);
v_val_3684_ = lean_ctor_get(v_fst_3678_, 0);
lean_inc(v_val_3684_);
lean_dec_ref_known(v_fst_3678_, 1);
if (v_isShared_3677_ == 0)
{
lean_ctor_set(v___x_3676_, 0, v_val_3684_);
v___x_3686_ = v___x_3676_;
goto v_reusejp_3685_;
}
else
{
lean_object* v_reuseFailAlloc_3687_; 
v_reuseFailAlloc_3687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3687_, 0, v_val_3684_);
v___x_3686_ = v_reuseFailAlloc_3687_;
goto v_reusejp_3685_;
}
v_reusejp_3685_:
{
return v___x_3686_;
}
}
}
}
else
{
lean_object* v_a_3689_; lean_object* v___x_3691_; uint8_t v_isShared_3692_; uint8_t v_isSharedCheck_3696_; 
v_a_3689_ = lean_ctor_get(v___x_3673_, 0);
v_isSharedCheck_3696_ = !lean_is_exclusive(v___x_3673_);
if (v_isSharedCheck_3696_ == 0)
{
v___x_3691_ = v___x_3673_;
v_isShared_3692_ = v_isSharedCheck_3696_;
goto v_resetjp_3690_;
}
else
{
lean_inc(v_a_3689_);
lean_dec(v___x_3673_);
v___x_3691_ = lean_box(0);
v_isShared_3692_ = v_isSharedCheck_3696_;
goto v_resetjp_3690_;
}
v_resetjp_3690_:
{
lean_object* v___x_3694_; 
if (v_isShared_3692_ == 0)
{
v___x_3694_ = v___x_3691_;
goto v_reusejp_3693_;
}
else
{
lean_object* v_reuseFailAlloc_3695_; 
v_reuseFailAlloc_3695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3695_, 0, v_a_3689_);
v___x_3694_ = v_reuseFailAlloc_3695_;
goto v_reusejp_3693_;
}
v_reusejp_3693_:
{
return v___x_3694_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__3(lean_object* v_init_3697_, lean_object* v_p_3698_, lean_object* v_mvarId_3699_, lean_object* v_as_3700_, size_t v_sz_3701_, size_t v_i_3702_, lean_object* v_b_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_, lean_object* v___y_3707_){
_start:
{
uint8_t v___x_3709_; 
v___x_3709_ = lean_usize_dec_lt(v_i_3702_, v_sz_3701_);
if (v___x_3709_ == 0)
{
lean_object* v___x_3710_; 
lean_dec(v_mvarId_3699_);
lean_dec_ref(v_p_3698_);
v___x_3710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3710_, 0, v_b_3703_);
return v___x_3710_;
}
else
{
lean_object* v_snd_3711_; lean_object* v___x_3713_; uint8_t v_isShared_3714_; uint8_t v_isSharedCheck_3745_; 
v_snd_3711_ = lean_ctor_get(v_b_3703_, 1);
v_isSharedCheck_3745_ = !lean_is_exclusive(v_b_3703_);
if (v_isSharedCheck_3745_ == 0)
{
lean_object* v_unused_3746_; 
v_unused_3746_ = lean_ctor_get(v_b_3703_, 0);
lean_dec(v_unused_3746_);
v___x_3713_ = v_b_3703_;
v_isShared_3714_ = v_isSharedCheck_3745_;
goto v_resetjp_3712_;
}
else
{
lean_inc(v_snd_3711_);
lean_dec(v_b_3703_);
v___x_3713_ = lean_box(0);
v_isShared_3714_ = v_isSharedCheck_3745_;
goto v_resetjp_3712_;
}
v_resetjp_3712_:
{
lean_object* v___x_3715_; lean_object* v_a_3716_; lean_object* v___x_3717_; 
v___x_3715_ = lean_box(0);
v_a_3716_ = lean_array_uget_borrowed(v_as_3700_, v_i_3702_);
lean_inc(v_snd_3711_);
lean_inc(v_mvarId_3699_);
lean_inc_ref(v_p_3698_);
v___x_3717_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2(v_init_3697_, v_p_3698_, v_mvarId_3699_, v_a_3716_, v_snd_3711_, v___y_3704_, v___y_3705_, v___y_3706_, v___y_3707_);
if (lean_obj_tag(v___x_3717_) == 0)
{
lean_object* v_a_3718_; lean_object* v___x_3720_; uint8_t v_isShared_3721_; uint8_t v_isSharedCheck_3736_; 
v_a_3718_ = lean_ctor_get(v___x_3717_, 0);
v_isSharedCheck_3736_ = !lean_is_exclusive(v___x_3717_);
if (v_isSharedCheck_3736_ == 0)
{
v___x_3720_ = v___x_3717_;
v_isShared_3721_ = v_isSharedCheck_3736_;
goto v_resetjp_3719_;
}
else
{
lean_inc(v_a_3718_);
lean_dec(v___x_3717_);
v___x_3720_ = lean_box(0);
v_isShared_3721_ = v_isSharedCheck_3736_;
goto v_resetjp_3719_;
}
v_resetjp_3719_:
{
if (lean_obj_tag(v_a_3718_) == 0)
{
lean_object* v___x_3722_; lean_object* v___x_3724_; 
lean_dec(v_mvarId_3699_);
lean_dec_ref(v_p_3698_);
v___x_3722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3722_, 0, v_a_3718_);
if (v_isShared_3714_ == 0)
{
lean_ctor_set(v___x_3713_, 0, v___x_3722_);
v___x_3724_ = v___x_3713_;
goto v_reusejp_3723_;
}
else
{
lean_object* v_reuseFailAlloc_3728_; 
v_reuseFailAlloc_3728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3728_, 0, v___x_3722_);
lean_ctor_set(v_reuseFailAlloc_3728_, 1, v_snd_3711_);
v___x_3724_ = v_reuseFailAlloc_3728_;
goto v_reusejp_3723_;
}
v_reusejp_3723_:
{
lean_object* v___x_3726_; 
if (v_isShared_3721_ == 0)
{
lean_ctor_set(v___x_3720_, 0, v___x_3724_);
v___x_3726_ = v___x_3720_;
goto v_reusejp_3725_;
}
else
{
lean_object* v_reuseFailAlloc_3727_; 
v_reuseFailAlloc_3727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3727_, 0, v___x_3724_);
v___x_3726_ = v_reuseFailAlloc_3727_;
goto v_reusejp_3725_;
}
v_reusejp_3725_:
{
return v___x_3726_;
}
}
}
else
{
lean_object* v_a_3729_; lean_object* v___x_3731_; 
lean_del_object(v___x_3720_);
lean_dec(v_snd_3711_);
v_a_3729_ = lean_ctor_get(v_a_3718_, 0);
lean_inc(v_a_3729_);
lean_dec_ref_known(v_a_3718_, 1);
if (v_isShared_3714_ == 0)
{
lean_ctor_set(v___x_3713_, 1, v_a_3729_);
lean_ctor_set(v___x_3713_, 0, v___x_3715_);
v___x_3731_ = v___x_3713_;
goto v_reusejp_3730_;
}
else
{
lean_object* v_reuseFailAlloc_3735_; 
v_reuseFailAlloc_3735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3735_, 0, v___x_3715_);
lean_ctor_set(v_reuseFailAlloc_3735_, 1, v_a_3729_);
v___x_3731_ = v_reuseFailAlloc_3735_;
goto v_reusejp_3730_;
}
v_reusejp_3730_:
{
size_t v___x_3732_; size_t v___x_3733_; 
v___x_3732_ = ((size_t)1ULL);
v___x_3733_ = lean_usize_add(v_i_3702_, v___x_3732_);
v_i_3702_ = v___x_3733_;
v_b_3703_ = v___x_3731_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3737_; lean_object* v___x_3739_; uint8_t v_isShared_3740_; uint8_t v_isSharedCheck_3744_; 
lean_del_object(v___x_3713_);
lean_dec(v_snd_3711_);
lean_dec(v_mvarId_3699_);
lean_dec_ref(v_p_3698_);
v_a_3737_ = lean_ctor_get(v___x_3717_, 0);
v_isSharedCheck_3744_ = !lean_is_exclusive(v___x_3717_);
if (v_isSharedCheck_3744_ == 0)
{
v___x_3739_ = v___x_3717_;
v_isShared_3740_ = v_isSharedCheck_3744_;
goto v_resetjp_3738_;
}
else
{
lean_inc(v_a_3737_);
lean_dec(v___x_3717_);
v___x_3739_ = lean_box(0);
v_isShared_3740_ = v_isSharedCheck_3744_;
goto v_resetjp_3738_;
}
v_resetjp_3738_:
{
lean_object* v___x_3742_; 
if (v_isShared_3740_ == 0)
{
v___x_3742_ = v___x_3739_;
goto v_reusejp_3741_;
}
else
{
lean_object* v_reuseFailAlloc_3743_; 
v_reuseFailAlloc_3743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3743_, 0, v_a_3737_);
v___x_3742_ = v_reuseFailAlloc_3743_;
goto v_reusejp_3741_;
}
v_reusejp_3741_:
{
return v___x_3742_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__3___boxed(lean_object* v_init_3747_, lean_object* v_p_3748_, lean_object* v_mvarId_3749_, lean_object* v_as_3750_, lean_object* v_sz_3751_, lean_object* v_i_3752_, lean_object* v_b_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_){
_start:
{
size_t v_sz_boxed_3759_; size_t v_i_boxed_3760_; lean_object* v_res_3761_; 
v_sz_boxed_3759_ = lean_unbox_usize(v_sz_3751_);
lean_dec(v_sz_3751_);
v_i_boxed_3760_ = lean_unbox_usize(v_i_3752_);
lean_dec(v_i_3752_);
v_res_3761_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__3(v_init_3747_, v_p_3748_, v_mvarId_3749_, v_as_3750_, v_sz_boxed_3759_, v_i_boxed_3760_, v_b_3753_, v___y_3754_, v___y_3755_, v___y_3756_, v___y_3757_);
lean_dec(v___y_3757_);
lean_dec_ref(v___y_3756_);
lean_dec(v___y_3755_);
lean_dec_ref(v___y_3754_);
lean_dec_ref(v_as_3750_);
lean_dec_ref(v_init_3747_);
return v_res_3761_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2___boxed(lean_object* v_init_3762_, lean_object* v_p_3763_, lean_object* v_mvarId_3764_, lean_object* v_n_3765_, lean_object* v_b_3766_, lean_object* v___y_3767_, lean_object* v___y_3768_, lean_object* v___y_3769_, lean_object* v___y_3770_, lean_object* v___y_3771_){
_start:
{
lean_object* v_res_3772_; 
v_res_3772_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2(v_init_3762_, v_p_3763_, v_mvarId_3764_, v_n_3765_, v_b_3766_, v___y_3767_, v___y_3768_, v___y_3769_, v___y_3770_);
lean_dec(v___y_3770_);
lean_dec_ref(v___y_3769_);
lean_dec(v___y_3768_);
lean_dec_ref(v___y_3767_);
lean_dec_ref(v_n_3765_);
lean_dec_ref(v_init_3762_);
return v_res_3772_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3_spec__6(lean_object* v_p_3776_, lean_object* v_mvarId_3777_, lean_object* v_as_3778_, size_t v_sz_3779_, size_t v_i_3780_, lean_object* v_b_3781_, lean_object* v___y_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_, lean_object* v___y_3785_){
_start:
{
uint8_t v___x_3787_; 
v___x_3787_ = lean_usize_dec_lt(v_i_3780_, v_sz_3779_);
if (v___x_3787_ == 0)
{
lean_object* v___x_3788_; 
lean_dec(v_mvarId_3777_);
lean_dec_ref(v_p_3776_);
v___x_3788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3788_, 0, v_b_3781_);
return v___x_3788_;
}
else
{
lean_object* v_snd_3789_; lean_object* v___x_3791_; uint8_t v_isShared_3792_; uint8_t v_isSharedCheck_3856_; 
v_snd_3789_ = lean_ctor_get(v_b_3781_, 1);
v_isSharedCheck_3856_ = !lean_is_exclusive(v_b_3781_);
if (v_isSharedCheck_3856_ == 0)
{
lean_object* v_unused_3857_; 
v_unused_3857_ = lean_ctor_get(v_b_3781_, 0);
lean_dec(v_unused_3857_);
v___x_3791_ = v_b_3781_;
v_isShared_3792_ = v_isSharedCheck_3856_;
goto v_resetjp_3790_;
}
else
{
lean_inc(v_snd_3789_);
lean_dec(v_b_3781_);
v___x_3791_ = lean_box(0);
v_isShared_3792_ = v_isSharedCheck_3856_;
goto v_resetjp_3790_;
}
v_resetjp_3790_:
{
lean_object* v___x_3793_; lean_object* v_a_3795_; lean_object* v_a_3802_; 
v___x_3793_ = lean_box(0);
v_a_3802_ = lean_array_uget(v_as_3778_, v_i_3780_);
if (lean_obj_tag(v_a_3802_) == 0)
{
v_a_3795_ = v_snd_3789_;
goto v___jp_3794_;
}
else
{
lean_object* v_val_3803_; lean_object* v___x_3805_; uint8_t v_isShared_3806_; uint8_t v_isSharedCheck_3855_; 
v_val_3803_ = lean_ctor_get(v_a_3802_, 0);
v_isSharedCheck_3855_ = !lean_is_exclusive(v_a_3802_);
if (v_isSharedCheck_3855_ == 0)
{
v___x_3805_ = v_a_3802_;
v_isShared_3806_ = v_isSharedCheck_3855_;
goto v_resetjp_3804_;
}
else
{
lean_inc(v_val_3803_);
lean_dec(v_a_3802_);
v___x_3805_ = lean_box(0);
v_isShared_3806_ = v_isSharedCheck_3855_;
goto v_resetjp_3804_;
}
v_resetjp_3804_:
{
lean_object* v___x_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; 
v___x_3807_ = lean_box(0);
v___x_3808_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3_spec__6___closed__0));
lean_inc_ref(v_p_3776_);
lean_inc(v___y_3785_);
lean_inc_ref(v___y_3784_);
lean_inc(v___y_3783_);
lean_inc_ref(v___y_3782_);
lean_inc(v_val_3803_);
v___x_3809_ = lean_apply_6(v_p_3776_, v_val_3803_, v___y_3782_, v___y_3783_, v___y_3784_, v___y_3785_, lean_box(0));
if (lean_obj_tag(v___x_3809_) == 0)
{
lean_object* v_a_3810_; uint8_t v___x_3811_; 
v_a_3810_ = lean_ctor_get(v___x_3809_, 0);
lean_inc(v_a_3810_);
lean_dec_ref_known(v___x_3809_, 1);
v___x_3811_ = lean_unbox(v_a_3810_);
lean_dec(v_a_3810_);
if (v___x_3811_ == 0)
{
lean_del_object(v___x_3805_);
lean_dec(v_val_3803_);
lean_dec(v_snd_3789_);
v_a_3795_ = v___x_3808_;
goto v___jp_3794_;
}
else
{
lean_object* v___x_3812_; lean_object* v___x_3813_; uint8_t v___x_3814_; lean_object* v___x_3815_; lean_object* v___f_3816_; lean_object* v___x_3817_; 
v___x_3812_ = l_Lean_LocalDecl_fvarId(v_val_3803_);
lean_dec(v_val_3803_);
v___x_3813_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5___closed__1));
v___x_3814_ = 0;
v___x_3815_ = lean_box(v___x_3814_);
lean_inc(v_mvarId_3777_);
v___f_3816_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3___lam__0___boxed), 10, 5);
lean_closure_set(v___f_3816_, 0, v_mvarId_3777_);
lean_closure_set(v___f_3816_, 1, v___x_3812_);
lean_closure_set(v___f_3816_, 2, v___x_3813_);
lean_closure_set(v___f_3816_, 3, v___x_3815_);
lean_closure_set(v___f_3816_, 4, v___x_3793_);
v___x_3817_ = l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1___redArg(v___f_3816_, v___y_3782_, v___y_3783_, v___y_3784_, v___y_3785_);
if (lean_obj_tag(v___x_3817_) == 0)
{
lean_object* v_a_3818_; lean_object* v___x_3820_; uint8_t v_isShared_3821_; uint8_t v_isSharedCheck_3838_; 
v_a_3818_ = lean_ctor_get(v___x_3817_, 0);
v_isSharedCheck_3838_ = !lean_is_exclusive(v___x_3817_);
if (v_isSharedCheck_3838_ == 0)
{
v___x_3820_ = v___x_3817_;
v_isShared_3821_ = v_isSharedCheck_3838_;
goto v_resetjp_3819_;
}
else
{
lean_inc(v_a_3818_);
lean_dec(v___x_3817_);
v___x_3820_ = lean_box(0);
v_isShared_3821_ = v_isSharedCheck_3838_;
goto v_resetjp_3819_;
}
v_resetjp_3819_:
{
if (lean_obj_tag(v_a_3818_) == 0)
{
lean_del_object(v___x_3820_);
lean_del_object(v___x_3805_);
lean_dec(v_snd_3789_);
v_a_3795_ = v___x_3808_;
goto v___jp_3794_;
}
else
{
lean_object* v___x_3823_; 
lean_del_object(v___x_3791_);
lean_dec(v_mvarId_3777_);
lean_dec_ref(v_p_3776_);
lean_inc_ref(v_a_3818_);
if (v_isShared_3806_ == 0)
{
lean_ctor_set(v___x_3805_, 0, v_a_3818_);
v___x_3823_ = v___x_3805_;
goto v_reusejp_3822_;
}
else
{
lean_object* v_reuseFailAlloc_3837_; 
v_reuseFailAlloc_3837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3837_, 0, v_a_3818_);
v___x_3823_ = v_reuseFailAlloc_3837_;
goto v_reusejp_3822_;
}
v_reusejp_3822_:
{
lean_object* v___x_3825_; uint8_t v_isShared_3826_; uint8_t v_isSharedCheck_3835_; 
v_isSharedCheck_3835_ = !lean_is_exclusive(v_a_3818_);
if (v_isSharedCheck_3835_ == 0)
{
lean_object* v_unused_3836_; 
v_unused_3836_ = lean_ctor_get(v_a_3818_, 0);
lean_dec(v_unused_3836_);
v___x_3825_ = v_a_3818_;
v_isShared_3826_ = v_isSharedCheck_3835_;
goto v_resetjp_3824_;
}
else
{
lean_dec(v_a_3818_);
v___x_3825_ = lean_box(0);
v_isShared_3826_ = v_isSharedCheck_3835_;
goto v_resetjp_3824_;
}
v_resetjp_3824_:
{
lean_object* v___x_3827_; lean_object* v___x_3829_; 
v___x_3827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3827_, 0, v___x_3823_);
lean_ctor_set(v___x_3827_, 1, v___x_3807_);
if (v_isShared_3826_ == 0)
{
lean_ctor_set(v___x_3825_, 0, v___x_3827_);
v___x_3829_ = v___x_3825_;
goto v_reusejp_3828_;
}
else
{
lean_object* v_reuseFailAlloc_3834_; 
v_reuseFailAlloc_3834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3834_, 0, v___x_3827_);
v___x_3829_ = v_reuseFailAlloc_3834_;
goto v_reusejp_3828_;
}
v_reusejp_3828_:
{
lean_object* v___x_3830_; lean_object* v___x_3832_; 
v___x_3830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3830_, 0, v___x_3829_);
lean_ctor_set(v___x_3830_, 1, v_snd_3789_);
if (v_isShared_3821_ == 0)
{
lean_ctor_set(v___x_3820_, 0, v___x_3830_);
v___x_3832_ = v___x_3820_;
goto v_reusejp_3831_;
}
else
{
lean_object* v_reuseFailAlloc_3833_; 
v_reuseFailAlloc_3833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3833_, 0, v___x_3830_);
v___x_3832_ = v_reuseFailAlloc_3833_;
goto v_reusejp_3831_;
}
v_reusejp_3831_:
{
return v___x_3832_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3839_; lean_object* v___x_3841_; uint8_t v_isShared_3842_; uint8_t v_isSharedCheck_3846_; 
lean_del_object(v___x_3805_);
lean_del_object(v___x_3791_);
lean_dec(v_snd_3789_);
lean_dec(v_mvarId_3777_);
lean_dec_ref(v_p_3776_);
v_a_3839_ = lean_ctor_get(v___x_3817_, 0);
v_isSharedCheck_3846_ = !lean_is_exclusive(v___x_3817_);
if (v_isSharedCheck_3846_ == 0)
{
v___x_3841_ = v___x_3817_;
v_isShared_3842_ = v_isSharedCheck_3846_;
goto v_resetjp_3840_;
}
else
{
lean_inc(v_a_3839_);
lean_dec(v___x_3817_);
v___x_3841_ = lean_box(0);
v_isShared_3842_ = v_isSharedCheck_3846_;
goto v_resetjp_3840_;
}
v_resetjp_3840_:
{
lean_object* v___x_3844_; 
if (v_isShared_3842_ == 0)
{
v___x_3844_ = v___x_3841_;
goto v_reusejp_3843_;
}
else
{
lean_object* v_reuseFailAlloc_3845_; 
v_reuseFailAlloc_3845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3845_, 0, v_a_3839_);
v___x_3844_ = v_reuseFailAlloc_3845_;
goto v_reusejp_3843_;
}
v_reusejp_3843_:
{
return v___x_3844_;
}
}
}
}
}
else
{
lean_object* v_a_3847_; lean_object* v___x_3849_; uint8_t v_isShared_3850_; uint8_t v_isSharedCheck_3854_; 
lean_del_object(v___x_3805_);
lean_dec(v_val_3803_);
lean_del_object(v___x_3791_);
lean_dec(v_snd_3789_);
lean_dec(v_mvarId_3777_);
lean_dec_ref(v_p_3776_);
v_a_3847_ = lean_ctor_get(v___x_3809_, 0);
v_isSharedCheck_3854_ = !lean_is_exclusive(v___x_3809_);
if (v_isSharedCheck_3854_ == 0)
{
v___x_3849_ = v___x_3809_;
v_isShared_3850_ = v_isSharedCheck_3854_;
goto v_resetjp_3848_;
}
else
{
lean_inc(v_a_3847_);
lean_dec(v___x_3809_);
v___x_3849_ = lean_box(0);
v_isShared_3850_ = v_isSharedCheck_3854_;
goto v_resetjp_3848_;
}
v_resetjp_3848_:
{
lean_object* v___x_3852_; 
if (v_isShared_3850_ == 0)
{
v___x_3852_ = v___x_3849_;
goto v_reusejp_3851_;
}
else
{
lean_object* v_reuseFailAlloc_3853_; 
v_reuseFailAlloc_3853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3853_, 0, v_a_3847_);
v___x_3852_ = v_reuseFailAlloc_3853_;
goto v_reusejp_3851_;
}
v_reusejp_3851_:
{
return v___x_3852_;
}
}
}
}
}
v___jp_3794_:
{
lean_object* v___x_3797_; 
if (v_isShared_3792_ == 0)
{
lean_ctor_set(v___x_3791_, 1, v_a_3795_);
lean_ctor_set(v___x_3791_, 0, v___x_3793_);
v___x_3797_ = v___x_3791_;
goto v_reusejp_3796_;
}
else
{
lean_object* v_reuseFailAlloc_3801_; 
v_reuseFailAlloc_3801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3801_, 0, v___x_3793_);
lean_ctor_set(v_reuseFailAlloc_3801_, 1, v_a_3795_);
v___x_3797_ = v_reuseFailAlloc_3801_;
goto v_reusejp_3796_;
}
v_reusejp_3796_:
{
size_t v___x_3798_; size_t v___x_3799_; 
v___x_3798_ = ((size_t)1ULL);
v___x_3799_ = lean_usize_add(v_i_3780_, v___x_3798_);
v_i_3780_ = v___x_3799_;
v_b_3781_ = v___x_3797_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3_spec__6___boxed(lean_object* v_p_3858_, lean_object* v_mvarId_3859_, lean_object* v_as_3860_, lean_object* v_sz_3861_, lean_object* v_i_3862_, lean_object* v_b_3863_, lean_object* v___y_3864_, lean_object* v___y_3865_, lean_object* v___y_3866_, lean_object* v___y_3867_, lean_object* v___y_3868_){
_start:
{
size_t v_sz_boxed_3869_; size_t v_i_boxed_3870_; lean_object* v_res_3871_; 
v_sz_boxed_3869_ = lean_unbox_usize(v_sz_3861_);
lean_dec(v_sz_3861_);
v_i_boxed_3870_ = lean_unbox_usize(v_i_3862_);
lean_dec(v_i_3862_);
v_res_3871_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3_spec__6(v_p_3858_, v_mvarId_3859_, v_as_3860_, v_sz_boxed_3869_, v_i_boxed_3870_, v_b_3863_, v___y_3864_, v___y_3865_, v___y_3866_, v___y_3867_);
lean_dec(v___y_3867_);
lean_dec_ref(v___y_3866_);
lean_dec(v___y_3865_);
lean_dec_ref(v___y_3864_);
lean_dec_ref(v_as_3860_);
return v_res_3871_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3(lean_object* v_p_3872_, lean_object* v_mvarId_3873_, lean_object* v_as_3874_, size_t v_sz_3875_, size_t v_i_3876_, lean_object* v_b_3877_, lean_object* v___y_3878_, lean_object* v___y_3879_, lean_object* v___y_3880_, lean_object* v___y_3881_){
_start:
{
uint8_t v___x_3883_; 
v___x_3883_ = lean_usize_dec_lt(v_i_3876_, v_sz_3875_);
if (v___x_3883_ == 0)
{
lean_object* v___x_3884_; 
lean_dec(v_mvarId_3873_);
lean_dec_ref(v_p_3872_);
v___x_3884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3884_, 0, v_b_3877_);
return v___x_3884_;
}
else
{
lean_object* v_snd_3885_; lean_object* v___x_3887_; uint8_t v_isShared_3888_; uint8_t v_isSharedCheck_3952_; 
v_snd_3885_ = lean_ctor_get(v_b_3877_, 1);
v_isSharedCheck_3952_ = !lean_is_exclusive(v_b_3877_);
if (v_isSharedCheck_3952_ == 0)
{
lean_object* v_unused_3953_; 
v_unused_3953_ = lean_ctor_get(v_b_3877_, 0);
lean_dec(v_unused_3953_);
v___x_3887_ = v_b_3877_;
v_isShared_3888_ = v_isSharedCheck_3952_;
goto v_resetjp_3886_;
}
else
{
lean_inc(v_snd_3885_);
lean_dec(v_b_3877_);
v___x_3887_ = lean_box(0);
v_isShared_3888_ = v_isSharedCheck_3952_;
goto v_resetjp_3886_;
}
v_resetjp_3886_:
{
lean_object* v___x_3889_; lean_object* v_a_3891_; lean_object* v_a_3898_; 
v___x_3889_ = lean_box(0);
v_a_3898_ = lean_array_uget(v_as_3874_, v_i_3876_);
if (lean_obj_tag(v_a_3898_) == 0)
{
v_a_3891_ = v_snd_3885_;
goto v___jp_3890_;
}
else
{
lean_object* v_val_3899_; lean_object* v___x_3901_; uint8_t v_isShared_3902_; uint8_t v_isSharedCheck_3951_; 
v_val_3899_ = lean_ctor_get(v_a_3898_, 0);
v_isSharedCheck_3951_ = !lean_is_exclusive(v_a_3898_);
if (v_isSharedCheck_3951_ == 0)
{
v___x_3901_ = v_a_3898_;
v_isShared_3902_ = v_isSharedCheck_3951_;
goto v_resetjp_3900_;
}
else
{
lean_inc(v_val_3899_);
lean_dec(v_a_3898_);
v___x_3901_ = lean_box(0);
v_isShared_3902_ = v_isSharedCheck_3951_;
goto v_resetjp_3900_;
}
v_resetjp_3900_:
{
lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; 
v___x_3903_ = lean_box(0);
v___x_3904_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3_spec__6___closed__0));
lean_inc_ref(v_p_3872_);
lean_inc(v___y_3881_);
lean_inc_ref(v___y_3880_);
lean_inc(v___y_3879_);
lean_inc_ref(v___y_3878_);
lean_inc(v_val_3899_);
v___x_3905_ = lean_apply_6(v_p_3872_, v_val_3899_, v___y_3878_, v___y_3879_, v___y_3880_, v___y_3881_, lean_box(0));
if (lean_obj_tag(v___x_3905_) == 0)
{
lean_object* v_a_3906_; uint8_t v___x_3907_; 
v_a_3906_ = lean_ctor_get(v___x_3905_, 0);
lean_inc(v_a_3906_);
lean_dec_ref_known(v___x_3905_, 1);
v___x_3907_ = lean_unbox(v_a_3906_);
lean_dec(v_a_3906_);
if (v___x_3907_ == 0)
{
lean_del_object(v___x_3901_);
lean_dec(v_val_3899_);
lean_dec(v_snd_3885_);
v_a_3891_ = v___x_3904_;
goto v___jp_3890_;
}
else
{
lean_object* v___x_3908_; lean_object* v___x_3909_; uint8_t v___x_3910_; lean_object* v___x_3911_; lean_object* v___f_3912_; lean_object* v___x_3913_; 
v___x_3908_ = l_Lean_LocalDecl_fvarId(v_val_3899_);
lean_dec(v_val_3899_);
v___x_3909_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5___closed__1));
v___x_3910_ = 0;
v___x_3911_ = lean_box(v___x_3910_);
lean_inc(v_mvarId_3873_);
v___f_3912_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3___lam__0___boxed), 10, 5);
lean_closure_set(v___f_3912_, 0, v_mvarId_3873_);
lean_closure_set(v___f_3912_, 1, v___x_3908_);
lean_closure_set(v___f_3912_, 2, v___x_3909_);
lean_closure_set(v___f_3912_, 3, v___x_3911_);
lean_closure_set(v___f_3912_, 4, v___x_3889_);
v___x_3913_ = l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1___redArg(v___f_3912_, v___y_3878_, v___y_3879_, v___y_3880_, v___y_3881_);
if (lean_obj_tag(v___x_3913_) == 0)
{
lean_object* v_a_3914_; lean_object* v___x_3916_; uint8_t v_isShared_3917_; uint8_t v_isSharedCheck_3934_; 
v_a_3914_ = lean_ctor_get(v___x_3913_, 0);
v_isSharedCheck_3934_ = !lean_is_exclusive(v___x_3913_);
if (v_isSharedCheck_3934_ == 0)
{
v___x_3916_ = v___x_3913_;
v_isShared_3917_ = v_isSharedCheck_3934_;
goto v_resetjp_3915_;
}
else
{
lean_inc(v_a_3914_);
lean_dec(v___x_3913_);
v___x_3916_ = lean_box(0);
v_isShared_3917_ = v_isSharedCheck_3934_;
goto v_resetjp_3915_;
}
v_resetjp_3915_:
{
if (lean_obj_tag(v_a_3914_) == 0)
{
lean_del_object(v___x_3916_);
lean_del_object(v___x_3901_);
lean_dec(v_snd_3885_);
v_a_3891_ = v___x_3904_;
goto v___jp_3890_;
}
else
{
lean_object* v___x_3919_; 
lean_del_object(v___x_3887_);
lean_dec(v_mvarId_3873_);
lean_dec_ref(v_p_3872_);
lean_inc_ref(v_a_3914_);
if (v_isShared_3902_ == 0)
{
lean_ctor_set(v___x_3901_, 0, v_a_3914_);
v___x_3919_ = v___x_3901_;
goto v_reusejp_3918_;
}
else
{
lean_object* v_reuseFailAlloc_3933_; 
v_reuseFailAlloc_3933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3933_, 0, v_a_3914_);
v___x_3919_ = v_reuseFailAlloc_3933_;
goto v_reusejp_3918_;
}
v_reusejp_3918_:
{
lean_object* v___x_3921_; uint8_t v_isShared_3922_; uint8_t v_isSharedCheck_3931_; 
v_isSharedCheck_3931_ = !lean_is_exclusive(v_a_3914_);
if (v_isSharedCheck_3931_ == 0)
{
lean_object* v_unused_3932_; 
v_unused_3932_ = lean_ctor_get(v_a_3914_, 0);
lean_dec(v_unused_3932_);
v___x_3921_ = v_a_3914_;
v_isShared_3922_ = v_isSharedCheck_3931_;
goto v_resetjp_3920_;
}
else
{
lean_dec(v_a_3914_);
v___x_3921_ = lean_box(0);
v_isShared_3922_ = v_isSharedCheck_3931_;
goto v_resetjp_3920_;
}
v_resetjp_3920_:
{
lean_object* v___x_3923_; lean_object* v___x_3925_; 
v___x_3923_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3923_, 0, v___x_3919_);
lean_ctor_set(v___x_3923_, 1, v___x_3903_);
if (v_isShared_3922_ == 0)
{
lean_ctor_set(v___x_3921_, 0, v___x_3923_);
v___x_3925_ = v___x_3921_;
goto v_reusejp_3924_;
}
else
{
lean_object* v_reuseFailAlloc_3930_; 
v_reuseFailAlloc_3930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3930_, 0, v___x_3923_);
v___x_3925_ = v_reuseFailAlloc_3930_;
goto v_reusejp_3924_;
}
v_reusejp_3924_:
{
lean_object* v___x_3926_; lean_object* v___x_3928_; 
v___x_3926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3926_, 0, v___x_3925_);
lean_ctor_set(v___x_3926_, 1, v_snd_3885_);
if (v_isShared_3917_ == 0)
{
lean_ctor_set(v___x_3916_, 0, v___x_3926_);
v___x_3928_ = v___x_3916_;
goto v_reusejp_3927_;
}
else
{
lean_object* v_reuseFailAlloc_3929_; 
v_reuseFailAlloc_3929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3929_, 0, v___x_3926_);
v___x_3928_ = v_reuseFailAlloc_3929_;
goto v_reusejp_3927_;
}
v_reusejp_3927_:
{
return v___x_3928_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3935_; lean_object* v___x_3937_; uint8_t v_isShared_3938_; uint8_t v_isSharedCheck_3942_; 
lean_del_object(v___x_3901_);
lean_del_object(v___x_3887_);
lean_dec(v_snd_3885_);
lean_dec(v_mvarId_3873_);
lean_dec_ref(v_p_3872_);
v_a_3935_ = lean_ctor_get(v___x_3913_, 0);
v_isSharedCheck_3942_ = !lean_is_exclusive(v___x_3913_);
if (v_isSharedCheck_3942_ == 0)
{
v___x_3937_ = v___x_3913_;
v_isShared_3938_ = v_isSharedCheck_3942_;
goto v_resetjp_3936_;
}
else
{
lean_inc(v_a_3935_);
lean_dec(v___x_3913_);
v___x_3937_ = lean_box(0);
v_isShared_3938_ = v_isSharedCheck_3942_;
goto v_resetjp_3936_;
}
v_resetjp_3936_:
{
lean_object* v___x_3940_; 
if (v_isShared_3938_ == 0)
{
v___x_3940_ = v___x_3937_;
goto v_reusejp_3939_;
}
else
{
lean_object* v_reuseFailAlloc_3941_; 
v_reuseFailAlloc_3941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3941_, 0, v_a_3935_);
v___x_3940_ = v_reuseFailAlloc_3941_;
goto v_reusejp_3939_;
}
v_reusejp_3939_:
{
return v___x_3940_;
}
}
}
}
}
else
{
lean_object* v_a_3943_; lean_object* v___x_3945_; uint8_t v_isShared_3946_; uint8_t v_isSharedCheck_3950_; 
lean_del_object(v___x_3901_);
lean_dec(v_val_3899_);
lean_del_object(v___x_3887_);
lean_dec(v_snd_3885_);
lean_dec(v_mvarId_3873_);
lean_dec_ref(v_p_3872_);
v_a_3943_ = lean_ctor_get(v___x_3905_, 0);
v_isSharedCheck_3950_ = !lean_is_exclusive(v___x_3905_);
if (v_isSharedCheck_3950_ == 0)
{
v___x_3945_ = v___x_3905_;
v_isShared_3946_ = v_isSharedCheck_3950_;
goto v_resetjp_3944_;
}
else
{
lean_inc(v_a_3943_);
lean_dec(v___x_3905_);
v___x_3945_ = lean_box(0);
v_isShared_3946_ = v_isSharedCheck_3950_;
goto v_resetjp_3944_;
}
v_resetjp_3944_:
{
lean_object* v___x_3948_; 
if (v_isShared_3946_ == 0)
{
v___x_3948_ = v___x_3945_;
goto v_reusejp_3947_;
}
else
{
lean_object* v_reuseFailAlloc_3949_; 
v_reuseFailAlloc_3949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3949_, 0, v_a_3943_);
v___x_3948_ = v_reuseFailAlloc_3949_;
goto v_reusejp_3947_;
}
v_reusejp_3947_:
{
return v___x_3948_;
}
}
}
}
}
v___jp_3890_:
{
lean_object* v___x_3893_; 
if (v_isShared_3888_ == 0)
{
lean_ctor_set(v___x_3887_, 1, v_a_3891_);
lean_ctor_set(v___x_3887_, 0, v___x_3889_);
v___x_3893_ = v___x_3887_;
goto v_reusejp_3892_;
}
else
{
lean_object* v_reuseFailAlloc_3897_; 
v_reuseFailAlloc_3897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3897_, 0, v___x_3889_);
lean_ctor_set(v_reuseFailAlloc_3897_, 1, v_a_3891_);
v___x_3893_ = v_reuseFailAlloc_3897_;
goto v_reusejp_3892_;
}
v_reusejp_3892_:
{
size_t v___x_3894_; size_t v___x_3895_; lean_object* v___x_3896_; 
v___x_3894_ = ((size_t)1ULL);
v___x_3895_ = lean_usize_add(v_i_3876_, v___x_3894_);
v___x_3896_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3_spec__6(v_p_3872_, v_mvarId_3873_, v_as_3874_, v_sz_3875_, v___x_3895_, v___x_3893_, v___y_3878_, v___y_3879_, v___y_3880_, v___y_3881_);
return v___x_3896_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3___boxed(lean_object* v_p_3954_, lean_object* v_mvarId_3955_, lean_object* v_as_3956_, lean_object* v_sz_3957_, lean_object* v_i_3958_, lean_object* v_b_3959_, lean_object* v___y_3960_, lean_object* v___y_3961_, lean_object* v___y_3962_, lean_object* v___y_3963_, lean_object* v___y_3964_){
_start:
{
size_t v_sz_boxed_3965_; size_t v_i_boxed_3966_; lean_object* v_res_3967_; 
v_sz_boxed_3965_ = lean_unbox_usize(v_sz_3957_);
lean_dec(v_sz_3957_);
v_i_boxed_3966_ = lean_unbox_usize(v_i_3958_);
lean_dec(v_i_3958_);
v_res_3967_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3(v_p_3954_, v_mvarId_3955_, v_as_3956_, v_sz_boxed_3965_, v_i_boxed_3966_, v_b_3959_, v___y_3960_, v___y_3961_, v___y_3962_, v___y_3963_);
lean_dec(v___y_3963_);
lean_dec_ref(v___y_3962_);
lean_dec(v___y_3961_);
lean_dec_ref(v___y_3960_);
lean_dec_ref(v_as_3956_);
return v_res_3967_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2(lean_object* v_p_3968_, lean_object* v_mvarId_3969_, lean_object* v_t_3970_, lean_object* v_init_3971_, lean_object* v___y_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_){
_start:
{
lean_object* v_root_3977_; lean_object* v_tail_3978_; lean_object* v___x_3979_; 
v_root_3977_ = lean_ctor_get(v_t_3970_, 0);
v_tail_3978_ = lean_ctor_get(v_t_3970_, 1);
lean_inc(v_mvarId_3969_);
lean_inc_ref(v_p_3968_);
lean_inc_ref(v_init_3971_);
v___x_3979_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2(v_init_3971_, v_p_3968_, v_mvarId_3969_, v_root_3977_, v_init_3971_, v___y_3972_, v___y_3973_, v___y_3974_, v___y_3975_);
lean_dec_ref(v_init_3971_);
if (lean_obj_tag(v___x_3979_) == 0)
{
lean_object* v_a_3980_; lean_object* v___x_3982_; uint8_t v_isShared_3983_; uint8_t v_isSharedCheck_4016_; 
v_a_3980_ = lean_ctor_get(v___x_3979_, 0);
v_isSharedCheck_4016_ = !lean_is_exclusive(v___x_3979_);
if (v_isSharedCheck_4016_ == 0)
{
v___x_3982_ = v___x_3979_;
v_isShared_3983_ = v_isSharedCheck_4016_;
goto v_resetjp_3981_;
}
else
{
lean_inc(v_a_3980_);
lean_dec(v___x_3979_);
v___x_3982_ = lean_box(0);
v_isShared_3983_ = v_isSharedCheck_4016_;
goto v_resetjp_3981_;
}
v_resetjp_3981_:
{
if (lean_obj_tag(v_a_3980_) == 0)
{
lean_object* v_a_3984_; lean_object* v___x_3986_; 
lean_dec(v_mvarId_3969_);
lean_dec_ref(v_p_3968_);
v_a_3984_ = lean_ctor_get(v_a_3980_, 0);
lean_inc(v_a_3984_);
lean_dec_ref_known(v_a_3980_, 1);
if (v_isShared_3983_ == 0)
{
lean_ctor_set(v___x_3982_, 0, v_a_3984_);
v___x_3986_ = v___x_3982_;
goto v_reusejp_3985_;
}
else
{
lean_object* v_reuseFailAlloc_3987_; 
v_reuseFailAlloc_3987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3987_, 0, v_a_3984_);
v___x_3986_ = v_reuseFailAlloc_3987_;
goto v_reusejp_3985_;
}
v_reusejp_3985_:
{
return v___x_3986_;
}
}
else
{
lean_object* v_a_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; size_t v_sz_3991_; size_t v___x_3992_; lean_object* v___x_3993_; 
lean_del_object(v___x_3982_);
v_a_3988_ = lean_ctor_get(v_a_3980_, 0);
lean_inc(v_a_3988_);
lean_dec_ref_known(v_a_3980_, 1);
v___x_3989_ = lean_box(0);
v___x_3990_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3990_, 0, v___x_3989_);
lean_ctor_set(v___x_3990_, 1, v_a_3988_);
v_sz_3991_ = lean_array_size(v_tail_3978_);
v___x_3992_ = ((size_t)0ULL);
v___x_3993_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3(v_p_3968_, v_mvarId_3969_, v_tail_3978_, v_sz_3991_, v___x_3992_, v___x_3990_, v___y_3972_, v___y_3973_, v___y_3974_, v___y_3975_);
if (lean_obj_tag(v___x_3993_) == 0)
{
lean_object* v_a_3994_; lean_object* v___x_3996_; uint8_t v_isShared_3997_; uint8_t v_isSharedCheck_4007_; 
v_a_3994_ = lean_ctor_get(v___x_3993_, 0);
v_isSharedCheck_4007_ = !lean_is_exclusive(v___x_3993_);
if (v_isSharedCheck_4007_ == 0)
{
v___x_3996_ = v___x_3993_;
v_isShared_3997_ = v_isSharedCheck_4007_;
goto v_resetjp_3995_;
}
else
{
lean_inc(v_a_3994_);
lean_dec(v___x_3993_);
v___x_3996_ = lean_box(0);
v_isShared_3997_ = v_isSharedCheck_4007_;
goto v_resetjp_3995_;
}
v_resetjp_3995_:
{
lean_object* v_fst_3998_; 
v_fst_3998_ = lean_ctor_get(v_a_3994_, 0);
if (lean_obj_tag(v_fst_3998_) == 0)
{
lean_object* v_snd_3999_; lean_object* v___x_4001_; 
v_snd_3999_ = lean_ctor_get(v_a_3994_, 1);
lean_inc(v_snd_3999_);
lean_dec(v_a_3994_);
if (v_isShared_3997_ == 0)
{
lean_ctor_set(v___x_3996_, 0, v_snd_3999_);
v___x_4001_ = v___x_3996_;
goto v_reusejp_4000_;
}
else
{
lean_object* v_reuseFailAlloc_4002_; 
v_reuseFailAlloc_4002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4002_, 0, v_snd_3999_);
v___x_4001_ = v_reuseFailAlloc_4002_;
goto v_reusejp_4000_;
}
v_reusejp_4000_:
{
return v___x_4001_;
}
}
else
{
lean_object* v_val_4003_; lean_object* v___x_4005_; 
lean_inc_ref(v_fst_3998_);
lean_dec(v_a_3994_);
v_val_4003_ = lean_ctor_get(v_fst_3998_, 0);
lean_inc(v_val_4003_);
lean_dec_ref_known(v_fst_3998_, 1);
if (v_isShared_3997_ == 0)
{
lean_ctor_set(v___x_3996_, 0, v_val_4003_);
v___x_4005_ = v___x_3996_;
goto v_reusejp_4004_;
}
else
{
lean_object* v_reuseFailAlloc_4006_; 
v_reuseFailAlloc_4006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4006_, 0, v_val_4003_);
v___x_4005_ = v_reuseFailAlloc_4006_;
goto v_reusejp_4004_;
}
v_reusejp_4004_:
{
return v___x_4005_;
}
}
}
}
else
{
lean_object* v_a_4008_; lean_object* v___x_4010_; uint8_t v_isShared_4011_; uint8_t v_isSharedCheck_4015_; 
v_a_4008_ = lean_ctor_get(v___x_3993_, 0);
v_isSharedCheck_4015_ = !lean_is_exclusive(v___x_3993_);
if (v_isSharedCheck_4015_ == 0)
{
v___x_4010_ = v___x_3993_;
v_isShared_4011_ = v_isSharedCheck_4015_;
goto v_resetjp_4009_;
}
else
{
lean_inc(v_a_4008_);
lean_dec(v___x_3993_);
v___x_4010_ = lean_box(0);
v_isShared_4011_ = v_isSharedCheck_4015_;
goto v_resetjp_4009_;
}
v_resetjp_4009_:
{
lean_object* v___x_4013_; 
if (v_isShared_4011_ == 0)
{
v___x_4013_ = v___x_4010_;
goto v_reusejp_4012_;
}
else
{
lean_object* v_reuseFailAlloc_4014_; 
v_reuseFailAlloc_4014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4014_, 0, v_a_4008_);
v___x_4013_ = v_reuseFailAlloc_4014_;
goto v_reusejp_4012_;
}
v_reusejp_4012_:
{
return v___x_4013_;
}
}
}
}
}
}
else
{
lean_object* v_a_4017_; lean_object* v___x_4019_; uint8_t v_isShared_4020_; uint8_t v_isSharedCheck_4024_; 
lean_dec(v_mvarId_3969_);
lean_dec_ref(v_p_3968_);
v_a_4017_ = lean_ctor_get(v___x_3979_, 0);
v_isSharedCheck_4024_ = !lean_is_exclusive(v___x_3979_);
if (v_isSharedCheck_4024_ == 0)
{
v___x_4019_ = v___x_3979_;
v_isShared_4020_ = v_isSharedCheck_4024_;
goto v_resetjp_4018_;
}
else
{
lean_inc(v_a_4017_);
lean_dec(v___x_3979_);
v___x_4019_ = lean_box(0);
v_isShared_4020_ = v_isSharedCheck_4024_;
goto v_resetjp_4018_;
}
v_resetjp_4018_:
{
lean_object* v___x_4022_; 
if (v_isShared_4020_ == 0)
{
v___x_4022_ = v___x_4019_;
goto v_reusejp_4021_;
}
else
{
lean_object* v_reuseFailAlloc_4023_; 
v_reuseFailAlloc_4023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4023_, 0, v_a_4017_);
v___x_4022_ = v_reuseFailAlloc_4023_;
goto v_reusejp_4021_;
}
v_reusejp_4021_:
{
return v___x_4022_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2___boxed(lean_object* v_p_4025_, lean_object* v_mvarId_4026_, lean_object* v_t_4027_, lean_object* v_init_4028_, lean_object* v___y_4029_, lean_object* v___y_4030_, lean_object* v___y_4031_, lean_object* v___y_4032_, lean_object* v___y_4033_){
_start:
{
lean_object* v_res_4034_; 
v_res_4034_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2(v_p_4025_, v_mvarId_4026_, v_t_4027_, v_init_4028_, v___y_4029_, v___y_4030_, v___y_4031_, v___y_4032_);
lean_dec(v___y_4032_);
lean_dec_ref(v___y_4031_);
lean_dec(v___y_4030_);
lean_dec_ref(v___y_4029_);
lean_dec_ref(v_t_4027_);
return v_res_4034_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesRec___lam__0(lean_object* v_p_4038_, lean_object* v_mvarId_4039_, lean_object* v___y_4040_, lean_object* v___y_4041_, lean_object* v___y_4042_, lean_object* v___y_4043_){
_start:
{
lean_object* v_lctx_4045_; lean_object* v_decls_4046_; lean_object* v___x_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; 
v_lctx_4045_ = lean_ctor_get(v___y_4040_, 2);
v_decls_4046_ = lean_ctor_get(v_lctx_4045_, 1);
v___x_4047_ = lean_box(0);
v___x_4048_ = ((lean_object*)(l_Lean_MVarId_casesRec___lam__0___closed__0));
v___x_4049_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2(v_p_4038_, v_mvarId_4039_, v_decls_4046_, v___x_4048_, v___y_4040_, v___y_4041_, v___y_4042_, v___y_4043_);
if (lean_obj_tag(v___x_4049_) == 0)
{
lean_object* v_a_4050_; lean_object* v___x_4052_; uint8_t v_isShared_4053_; uint8_t v_isSharedCheck_4062_; 
v_a_4050_ = lean_ctor_get(v___x_4049_, 0);
v_isSharedCheck_4062_ = !lean_is_exclusive(v___x_4049_);
if (v_isSharedCheck_4062_ == 0)
{
v___x_4052_ = v___x_4049_;
v_isShared_4053_ = v_isSharedCheck_4062_;
goto v_resetjp_4051_;
}
else
{
lean_inc(v_a_4050_);
lean_dec(v___x_4049_);
v___x_4052_ = lean_box(0);
v_isShared_4053_ = v_isSharedCheck_4062_;
goto v_resetjp_4051_;
}
v_resetjp_4051_:
{
lean_object* v_fst_4054_; 
v_fst_4054_ = lean_ctor_get(v_a_4050_, 0);
lean_inc(v_fst_4054_);
lean_dec(v_a_4050_);
if (lean_obj_tag(v_fst_4054_) == 0)
{
lean_object* v___x_4056_; 
if (v_isShared_4053_ == 0)
{
lean_ctor_set(v___x_4052_, 0, v___x_4047_);
v___x_4056_ = v___x_4052_;
goto v_reusejp_4055_;
}
else
{
lean_object* v_reuseFailAlloc_4057_; 
v_reuseFailAlloc_4057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4057_, 0, v___x_4047_);
v___x_4056_ = v_reuseFailAlloc_4057_;
goto v_reusejp_4055_;
}
v_reusejp_4055_:
{
return v___x_4056_;
}
}
else
{
lean_object* v_val_4058_; lean_object* v___x_4060_; 
v_val_4058_ = lean_ctor_get(v_fst_4054_, 0);
lean_inc(v_val_4058_);
lean_dec_ref_known(v_fst_4054_, 1);
if (v_isShared_4053_ == 0)
{
lean_ctor_set(v___x_4052_, 0, v_val_4058_);
v___x_4060_ = v___x_4052_;
goto v_reusejp_4059_;
}
else
{
lean_object* v_reuseFailAlloc_4061_; 
v_reuseFailAlloc_4061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4061_, 0, v_val_4058_);
v___x_4060_ = v_reuseFailAlloc_4061_;
goto v_reusejp_4059_;
}
v_reusejp_4059_:
{
return v___x_4060_;
}
}
}
}
else
{
lean_object* v_a_4063_; lean_object* v___x_4065_; uint8_t v_isShared_4066_; uint8_t v_isSharedCheck_4070_; 
v_a_4063_ = lean_ctor_get(v___x_4049_, 0);
v_isSharedCheck_4070_ = !lean_is_exclusive(v___x_4049_);
if (v_isSharedCheck_4070_ == 0)
{
v___x_4065_ = v___x_4049_;
v_isShared_4066_ = v_isSharedCheck_4070_;
goto v_resetjp_4064_;
}
else
{
lean_inc(v_a_4063_);
lean_dec(v___x_4049_);
v___x_4065_ = lean_box(0);
v_isShared_4066_ = v_isSharedCheck_4070_;
goto v_resetjp_4064_;
}
v_resetjp_4064_:
{
lean_object* v___x_4068_; 
if (v_isShared_4066_ == 0)
{
v___x_4068_ = v___x_4065_;
goto v_reusejp_4067_;
}
else
{
lean_object* v_reuseFailAlloc_4069_; 
v_reuseFailAlloc_4069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4069_, 0, v_a_4063_);
v___x_4068_ = v_reuseFailAlloc_4069_;
goto v_reusejp_4067_;
}
v_reusejp_4067_:
{
return v___x_4068_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesRec___lam__0___boxed(lean_object* v_p_4071_, lean_object* v_mvarId_4072_, lean_object* v___y_4073_, lean_object* v___y_4074_, lean_object* v___y_4075_, lean_object* v___y_4076_, lean_object* v___y_4077_){
_start:
{
lean_object* v_res_4078_; 
v_res_4078_ = l_Lean_MVarId_casesRec___lam__0(v_p_4071_, v_mvarId_4072_, v___y_4073_, v___y_4074_, v___y_4075_, v___y_4076_);
lean_dec(v___y_4076_);
lean_dec_ref(v___y_4075_);
lean_dec(v___y_4074_);
lean_dec_ref(v___y_4073_);
return v_res_4078_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesRec___lam__1(lean_object* v_p_4079_, lean_object* v_mvarId_4080_, lean_object* v___y_4081_, lean_object* v___y_4082_, lean_object* v___y_4083_, lean_object* v___y_4084_){
_start:
{
lean_object* v___f_4086_; lean_object* v___x_4087_; 
lean_inc(v_mvarId_4080_);
v___f_4086_ = lean_alloc_closure((void*)(l_Lean_MVarId_casesRec___lam__0___boxed), 7, 2);
lean_closure_set(v___f_4086_, 0, v_p_4079_);
lean_closure_set(v___f_4086_, 1, v_mvarId_4080_);
v___x_4087_ = l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2___redArg(v_mvarId_4080_, v___f_4086_, v___y_4081_, v___y_4082_, v___y_4083_, v___y_4084_);
return v___x_4087_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesRec___lam__1___boxed(lean_object* v_p_4088_, lean_object* v_mvarId_4089_, lean_object* v___y_4090_, lean_object* v___y_4091_, lean_object* v___y_4092_, lean_object* v___y_4093_, lean_object* v___y_4094_){
_start:
{
lean_object* v_res_4095_; 
v_res_4095_ = l_Lean_MVarId_casesRec___lam__1(v_p_4088_, v_mvarId_4089_, v___y_4090_, v___y_4091_, v___y_4092_, v___y_4093_);
lean_dec(v___y_4093_);
lean_dec_ref(v___y_4092_);
lean_dec(v___y_4091_);
lean_dec_ref(v___y_4090_);
return v_res_4095_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesRec(lean_object* v_mvarId_4096_, lean_object* v_p_4097_, lean_object* v_a_4098_, lean_object* v_a_4099_, lean_object* v_a_4100_, lean_object* v_a_4101_){
_start:
{
lean_object* v___f_4103_; lean_object* v___x_4104_; 
v___f_4103_ = lean_alloc_closure((void*)(l_Lean_MVarId_casesRec___lam__1___boxed), 7, 1);
lean_closure_set(v___f_4103_, 0, v_p_4097_);
v___x_4104_ = l_Lean_Meta_saturate(v_mvarId_4096_, v___f_4103_, v_a_4098_, v_a_4099_, v_a_4100_, v_a_4101_);
return v___x_4104_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesRec___boxed(lean_object* v_mvarId_4105_, lean_object* v_p_4106_, lean_object* v_a_4107_, lean_object* v_a_4108_, lean_object* v_a_4109_, lean_object* v_a_4110_, lean_object* v_a_4111_){
_start:
{
lean_object* v_res_4112_; 
v_res_4112_ = l_Lean_MVarId_casesRec(v_mvarId_4105_, v_p_4106_, v_a_4107_, v_a_4108_, v_a_4109_, v_a_4110_);
lean_dec(v_a_4110_);
lean_dec_ref(v_a_4109_);
lean_dec(v_a_4108_);
lean_dec_ref(v_a_4107_);
return v_res_4112_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0___redArg(lean_object* v_e_4113_, lean_object* v___y_4114_){
_start:
{
uint8_t v___x_4116_; 
v___x_4116_ = l_Lean_Expr_hasMVar(v_e_4113_);
if (v___x_4116_ == 0)
{
lean_object* v___x_4117_; 
v___x_4117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4117_, 0, v_e_4113_);
return v___x_4117_;
}
else
{
lean_object* v___x_4118_; lean_object* v_mctx_4119_; lean_object* v___x_4120_; lean_object* v_fst_4121_; lean_object* v_snd_4122_; lean_object* v___x_4123_; lean_object* v_cache_4124_; lean_object* v_zetaDeltaFVarIds_4125_; lean_object* v_postponed_4126_; lean_object* v_diag_4127_; lean_object* v___x_4129_; uint8_t v_isShared_4130_; uint8_t v_isSharedCheck_4136_; 
v___x_4118_ = lean_st_ref_get(v___y_4114_);
v_mctx_4119_ = lean_ctor_get(v___x_4118_, 0);
lean_inc_ref(v_mctx_4119_);
lean_dec(v___x_4118_);
v___x_4120_ = l_Lean_instantiateMVarsCore(v_mctx_4119_, v_e_4113_);
v_fst_4121_ = lean_ctor_get(v___x_4120_, 0);
lean_inc(v_fst_4121_);
v_snd_4122_ = lean_ctor_get(v___x_4120_, 1);
lean_inc(v_snd_4122_);
lean_dec_ref(v___x_4120_);
v___x_4123_ = lean_st_ref_take(v___y_4114_);
v_cache_4124_ = lean_ctor_get(v___x_4123_, 1);
v_zetaDeltaFVarIds_4125_ = lean_ctor_get(v___x_4123_, 2);
v_postponed_4126_ = lean_ctor_get(v___x_4123_, 3);
v_diag_4127_ = lean_ctor_get(v___x_4123_, 4);
v_isSharedCheck_4136_ = !lean_is_exclusive(v___x_4123_);
if (v_isSharedCheck_4136_ == 0)
{
lean_object* v_unused_4137_; 
v_unused_4137_ = lean_ctor_get(v___x_4123_, 0);
lean_dec(v_unused_4137_);
v___x_4129_ = v___x_4123_;
v_isShared_4130_ = v_isSharedCheck_4136_;
goto v_resetjp_4128_;
}
else
{
lean_inc(v_diag_4127_);
lean_inc(v_postponed_4126_);
lean_inc(v_zetaDeltaFVarIds_4125_);
lean_inc(v_cache_4124_);
lean_dec(v___x_4123_);
v___x_4129_ = lean_box(0);
v_isShared_4130_ = v_isSharedCheck_4136_;
goto v_resetjp_4128_;
}
v_resetjp_4128_:
{
lean_object* v___x_4132_; 
if (v_isShared_4130_ == 0)
{
lean_ctor_set(v___x_4129_, 0, v_snd_4122_);
v___x_4132_ = v___x_4129_;
goto v_reusejp_4131_;
}
else
{
lean_object* v_reuseFailAlloc_4135_; 
v_reuseFailAlloc_4135_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4135_, 0, v_snd_4122_);
lean_ctor_set(v_reuseFailAlloc_4135_, 1, v_cache_4124_);
lean_ctor_set(v_reuseFailAlloc_4135_, 2, v_zetaDeltaFVarIds_4125_);
lean_ctor_set(v_reuseFailAlloc_4135_, 3, v_postponed_4126_);
lean_ctor_set(v_reuseFailAlloc_4135_, 4, v_diag_4127_);
v___x_4132_ = v_reuseFailAlloc_4135_;
goto v_reusejp_4131_;
}
v_reusejp_4131_:
{
lean_object* v___x_4133_; lean_object* v___x_4134_; 
v___x_4133_ = lean_st_ref_put(v___y_4114_, v___x_4132_);
v___x_4134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4134_, 0, v_fst_4121_);
return v___x_4134_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0___redArg___boxed(lean_object* v_e_4138_, lean_object* v___y_4139_, lean_object* v___y_4140_){
_start:
{
lean_object* v_res_4141_; 
v_res_4141_ = l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0___redArg(v_e_4138_, v___y_4139_);
lean_dec(v___y_4139_);
return v_res_4141_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0(lean_object* v_e_4142_, lean_object* v___y_4143_, lean_object* v___y_4144_, lean_object* v___y_4145_, lean_object* v___y_4146_){
_start:
{
lean_object* v___x_4148_; 
v___x_4148_ = l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0___redArg(v_e_4142_, v___y_4144_);
return v___x_4148_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0___boxed(lean_object* v_e_4149_, lean_object* v___y_4150_, lean_object* v___y_4151_, lean_object* v___y_4152_, lean_object* v___y_4153_, lean_object* v___y_4154_){
_start:
{
lean_object* v_res_4155_; 
v_res_4155_ = l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0(v_e_4149_, v___y_4150_, v___y_4151_, v___y_4152_, v___y_4153_);
lean_dec(v___y_4153_);
lean_dec_ref(v___y_4152_);
lean_dec(v___y_4151_);
lean_dec_ref(v___y_4150_);
return v_res_4155_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesAnd___lam__0(lean_object* v_localDecl_4159_, lean_object* v___y_4160_, lean_object* v___y_4161_, lean_object* v___y_4162_, lean_object* v___y_4163_){
_start:
{
lean_object* v___x_4165_; lean_object* v___x_4166_; lean_object* v_a_4167_; lean_object* v___x_4169_; uint8_t v_isShared_4170_; uint8_t v_isSharedCheck_4178_; 
v___x_4165_ = l_Lean_LocalDecl_type(v_localDecl_4159_);
v___x_4166_ = l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0___redArg(v___x_4165_, v___y_4161_);
v_a_4167_ = lean_ctor_get(v___x_4166_, 0);
v_isSharedCheck_4178_ = !lean_is_exclusive(v___x_4166_);
if (v_isSharedCheck_4178_ == 0)
{
v___x_4169_ = v___x_4166_;
v_isShared_4170_ = v_isSharedCheck_4178_;
goto v_resetjp_4168_;
}
else
{
lean_inc(v_a_4167_);
lean_dec(v___x_4166_);
v___x_4169_ = lean_box(0);
v_isShared_4170_ = v_isSharedCheck_4178_;
goto v_resetjp_4168_;
}
v_resetjp_4168_:
{
lean_object* v___x_4171_; lean_object* v___x_4172_; uint8_t v___x_4173_; lean_object* v___x_4174_; lean_object* v___x_4176_; 
v___x_4171_ = ((lean_object*)(l_Lean_MVarId_casesAnd___lam__0___closed__1));
v___x_4172_ = lean_unsigned_to_nat(2u);
v___x_4173_ = l_Lean_Expr_isAppOfArity(v_a_4167_, v___x_4171_, v___x_4172_);
lean_dec(v_a_4167_);
v___x_4174_ = lean_box(v___x_4173_);
if (v_isShared_4170_ == 0)
{
lean_ctor_set(v___x_4169_, 0, v___x_4174_);
v___x_4176_ = v___x_4169_;
goto v_reusejp_4175_;
}
else
{
lean_object* v_reuseFailAlloc_4177_; 
v_reuseFailAlloc_4177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4177_, 0, v___x_4174_);
v___x_4176_ = v_reuseFailAlloc_4177_;
goto v_reusejp_4175_;
}
v_reusejp_4175_:
{
return v___x_4176_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesAnd___lam__0___boxed(lean_object* v_localDecl_4179_, lean_object* v___y_4180_, lean_object* v___y_4181_, lean_object* v___y_4182_, lean_object* v___y_4183_, lean_object* v___y_4184_){
_start:
{
lean_object* v_res_4185_; 
v_res_4185_ = l_Lean_MVarId_casesAnd___lam__0(v_localDecl_4179_, v___y_4180_, v___y_4181_, v___y_4182_, v___y_4183_);
lean_dec(v___y_4183_);
lean_dec_ref(v___y_4182_);
lean_dec(v___y_4181_);
lean_dec_ref(v___y_4180_);
lean_dec_ref(v_localDecl_4179_);
return v_res_4185_;
}
}
static lean_object* _init_l_Lean_MVarId_casesAnd___closed__3(void){
_start:
{
lean_object* v___x_4190_; lean_object* v___x_4191_; 
v___x_4190_ = ((lean_object*)(l_Lean_MVarId_casesAnd___closed__2));
v___x_4191_ = l_Lean_MessageData_ofFormat(v___x_4190_);
return v___x_4191_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesAnd(lean_object* v_mvarId_4192_, lean_object* v_a_4193_, lean_object* v_a_4194_, lean_object* v_a_4195_, lean_object* v_a_4196_){
_start:
{
lean_object* v___f_4198_; lean_object* v___x_4199_; 
v___f_4198_ = ((lean_object*)(l_Lean_MVarId_casesAnd___closed__0));
v___x_4199_ = l_Lean_MVarId_casesRec(v_mvarId_4192_, v___f_4198_, v_a_4193_, v_a_4194_, v_a_4195_, v_a_4196_);
if (lean_obj_tag(v___x_4199_) == 0)
{
lean_object* v_a_4200_; lean_object* v___x_4201_; lean_object* v___x_4202_; 
v_a_4200_ = lean_ctor_get(v___x_4199_, 0);
lean_inc(v_a_4200_);
lean_dec_ref_known(v___x_4199_, 1);
v___x_4201_ = lean_obj_once(&l_Lean_MVarId_casesAnd___closed__3, &l_Lean_MVarId_casesAnd___closed__3_once, _init_l_Lean_MVarId_casesAnd___closed__3);
v___x_4202_ = l_Lean_Meta_exactlyOne(v_a_4200_, v___x_4201_, v_a_4193_, v_a_4194_, v_a_4195_, v_a_4196_);
lean_dec(v_a_4200_);
return v___x_4202_;
}
else
{
lean_object* v_a_4203_; lean_object* v___x_4205_; uint8_t v_isShared_4206_; uint8_t v_isSharedCheck_4210_; 
v_a_4203_ = lean_ctor_get(v___x_4199_, 0);
v_isSharedCheck_4210_ = !lean_is_exclusive(v___x_4199_);
if (v_isSharedCheck_4210_ == 0)
{
v___x_4205_ = v___x_4199_;
v_isShared_4206_ = v_isSharedCheck_4210_;
goto v_resetjp_4204_;
}
else
{
lean_inc(v_a_4203_);
lean_dec(v___x_4199_);
v___x_4205_ = lean_box(0);
v_isShared_4206_ = v_isSharedCheck_4210_;
goto v_resetjp_4204_;
}
v_resetjp_4204_:
{
lean_object* v___x_4208_; 
if (v_isShared_4206_ == 0)
{
v___x_4208_ = v___x_4205_;
goto v_reusejp_4207_;
}
else
{
lean_object* v_reuseFailAlloc_4209_; 
v_reuseFailAlloc_4209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4209_, 0, v_a_4203_);
v___x_4208_ = v_reuseFailAlloc_4209_;
goto v_reusejp_4207_;
}
v_reusejp_4207_:
{
return v___x_4208_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesAnd___boxed(lean_object* v_mvarId_4211_, lean_object* v_a_4212_, lean_object* v_a_4213_, lean_object* v_a_4214_, lean_object* v_a_4215_, lean_object* v_a_4216_){
_start:
{
lean_object* v_res_4217_; 
v_res_4217_ = l_Lean_MVarId_casesAnd(v_mvarId_4211_, v_a_4212_, v_a_4213_, v_a_4214_, v_a_4215_);
lean_dec(v_a_4215_);
lean_dec_ref(v_a_4214_);
lean_dec(v_a_4213_);
lean_dec_ref(v_a_4212_);
return v_res_4217_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_substEqs___lam__0(lean_object* v_localDecl_4218_, lean_object* v___y_4219_, lean_object* v___y_4220_, lean_object* v___y_4221_, lean_object* v___y_4222_){
_start:
{
lean_object* v___x_4224_; lean_object* v___x_4225_; lean_object* v_a_4226_; lean_object* v___x_4228_; uint8_t v_isShared_4229_; uint8_t v_isSharedCheck_4240_; 
v___x_4224_ = l_Lean_LocalDecl_type(v_localDecl_4218_);
v___x_4225_ = l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0___redArg(v___x_4224_, v___y_4220_);
v_a_4226_ = lean_ctor_get(v___x_4225_, 0);
v_isSharedCheck_4240_ = !lean_is_exclusive(v___x_4225_);
if (v_isSharedCheck_4240_ == 0)
{
v___x_4228_ = v___x_4225_;
v_isShared_4229_ = v_isSharedCheck_4240_;
goto v_resetjp_4227_;
}
else
{
lean_inc(v_a_4226_);
lean_dec(v___x_4225_);
v___x_4228_ = lean_box(0);
v_isShared_4229_ = v_isSharedCheck_4240_;
goto v_resetjp_4227_;
}
v_resetjp_4227_:
{
uint8_t v___x_4230_; 
v___x_4230_ = l_Lean_Expr_isEq(v_a_4226_);
if (v___x_4230_ == 0)
{
uint8_t v___x_4231_; lean_object* v___x_4232_; lean_object* v___x_4234_; 
v___x_4231_ = l_Lean_Expr_isHEq(v_a_4226_);
lean_dec(v_a_4226_);
v___x_4232_ = lean_box(v___x_4231_);
if (v_isShared_4229_ == 0)
{
lean_ctor_set(v___x_4228_, 0, v___x_4232_);
v___x_4234_ = v___x_4228_;
goto v_reusejp_4233_;
}
else
{
lean_object* v_reuseFailAlloc_4235_; 
v_reuseFailAlloc_4235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4235_, 0, v___x_4232_);
v___x_4234_ = v_reuseFailAlloc_4235_;
goto v_reusejp_4233_;
}
v_reusejp_4233_:
{
return v___x_4234_;
}
}
else
{
lean_object* v___x_4236_; lean_object* v___x_4238_; 
lean_dec(v_a_4226_);
v___x_4236_ = lean_box(v___x_4230_);
if (v_isShared_4229_ == 0)
{
lean_ctor_set(v___x_4228_, 0, v___x_4236_);
v___x_4238_ = v___x_4228_;
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_substEqs___lam__0___boxed(lean_object* v_localDecl_4241_, lean_object* v___y_4242_, lean_object* v___y_4243_, lean_object* v___y_4244_, lean_object* v___y_4245_, lean_object* v___y_4246_){
_start:
{
lean_object* v_res_4247_; 
v_res_4247_ = l_Lean_MVarId_substEqs___lam__0(v_localDecl_4241_, v___y_4242_, v___y_4243_, v___y_4244_, v___y_4245_);
lean_dec(v___y_4245_);
lean_dec_ref(v___y_4244_);
lean_dec(v___y_4243_);
lean_dec_ref(v___y_4242_);
lean_dec_ref(v_localDecl_4241_);
return v_res_4247_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_substEqs(lean_object* v_mvarId_4249_, lean_object* v_a_4250_, lean_object* v_a_4251_, lean_object* v_a_4252_, lean_object* v_a_4253_){
_start:
{
lean_object* v___f_4255_; lean_object* v___x_4256_; 
v___f_4255_ = ((lean_object*)(l_Lean_MVarId_substEqs___closed__0));
v___x_4256_ = l_Lean_MVarId_casesRec(v_mvarId_4249_, v___f_4255_, v_a_4250_, v_a_4251_, v_a_4252_, v_a_4253_);
if (lean_obj_tag(v___x_4256_) == 0)
{
lean_object* v_a_4257_; lean_object* v___x_4258_; lean_object* v___x_4259_; 
v_a_4257_ = lean_ctor_get(v___x_4256_, 0);
lean_inc(v_a_4257_);
lean_dec_ref_known(v___x_4256_, 1);
v___x_4258_ = lean_obj_once(&l_Lean_MVarId_casesAnd___closed__3, &l_Lean_MVarId_casesAnd___closed__3_once, _init_l_Lean_MVarId_casesAnd___closed__3);
v___x_4259_ = l_Lean_Meta_ensureAtMostOne(v_a_4257_, v___x_4258_, v_a_4250_, v_a_4251_, v_a_4252_, v_a_4253_);
lean_dec(v_a_4257_);
return v___x_4259_;
}
else
{
lean_object* v_a_4260_; lean_object* v___x_4262_; uint8_t v_isShared_4263_; uint8_t v_isSharedCheck_4267_; 
v_a_4260_ = lean_ctor_get(v___x_4256_, 0);
v_isSharedCheck_4267_ = !lean_is_exclusive(v___x_4256_);
if (v_isSharedCheck_4267_ == 0)
{
v___x_4262_ = v___x_4256_;
v_isShared_4263_ = v_isSharedCheck_4267_;
goto v_resetjp_4261_;
}
else
{
lean_inc(v_a_4260_);
lean_dec(v___x_4256_);
v___x_4262_ = lean_box(0);
v_isShared_4263_ = v_isSharedCheck_4267_;
goto v_resetjp_4261_;
}
v_resetjp_4261_:
{
lean_object* v___x_4265_; 
if (v_isShared_4263_ == 0)
{
v___x_4265_ = v___x_4262_;
goto v_reusejp_4264_;
}
else
{
lean_object* v_reuseFailAlloc_4266_; 
v_reuseFailAlloc_4266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4266_, 0, v_a_4260_);
v___x_4265_ = v_reuseFailAlloc_4266_;
goto v_reusejp_4264_;
}
v_reusejp_4264_:
{
return v___x_4265_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_substEqs___boxed(lean_object* v_mvarId_4268_, lean_object* v_a_4269_, lean_object* v_a_4270_, lean_object* v_a_4271_, lean_object* v_a_4272_, lean_object* v_a_4273_){
_start:
{
lean_object* v_res_4274_; 
v_res_4274_ = l_Lean_MVarId_substEqs(v_mvarId_4268_, v_a_4269_, v_a_4270_, v_a_4271_, v_a_4272_);
lean_dec(v_a_4272_);
lean_dec_ref(v_a_4271_);
lean_dec(v_a_4270_);
lean_dec_ref(v_a_4269_);
return v_res_4274_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkByCasesSubgoal___lam__0(lean_object* v_goalType_4275_, lean_object* v_tag_4276_, lean_object* v_hyp_4277_, lean_object* v___y_4278_, lean_object* v___y_4279_, lean_object* v___y_4280_, lean_object* v___y_4281_){
_start:
{
lean_object* v___x_4283_; 
v___x_4283_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_goalType_4275_, v_tag_4276_, v___y_4278_, v___y_4279_, v___y_4280_, v___y_4281_);
if (lean_obj_tag(v___x_4283_) == 0)
{
lean_object* v_a_4284_; lean_object* v___x_4285_; lean_object* v___x_4286_; lean_object* v___x_4287_; uint8_t v___x_4288_; uint8_t v___x_4289_; uint8_t v___x_4290_; lean_object* v___x_4291_; 
v_a_4284_ = lean_ctor_get(v___x_4283_, 0);
lean_inc_n(v_a_4284_, 2);
lean_dec_ref_known(v___x_4283_, 1);
v___x_4285_ = lean_unsigned_to_nat(1u);
v___x_4286_ = lean_mk_empty_array_with_capacity(v___x_4285_);
lean_inc_ref(v_hyp_4277_);
v___x_4287_ = lean_array_push(v___x_4286_, v_hyp_4277_);
v___x_4288_ = 0;
v___x_4289_ = 1;
v___x_4290_ = 1;
v___x_4291_ = l_Lean_Meta_mkLambdaFVars(v___x_4287_, v_a_4284_, v___x_4288_, v___x_4289_, v___x_4288_, v___x_4289_, v___x_4290_, v___y_4278_, v___y_4279_, v___y_4280_, v___y_4281_);
lean_dec_ref(v___x_4287_);
if (lean_obj_tag(v___x_4291_) == 0)
{
lean_object* v_a_4292_; lean_object* v___x_4294_; uint8_t v_isShared_4295_; uint8_t v_isSharedCheck_4303_; 
v_a_4292_ = lean_ctor_get(v___x_4291_, 0);
v_isSharedCheck_4303_ = !lean_is_exclusive(v___x_4291_);
if (v_isSharedCheck_4303_ == 0)
{
v___x_4294_ = v___x_4291_;
v_isShared_4295_ = v_isSharedCheck_4303_;
goto v_resetjp_4293_;
}
else
{
lean_inc(v_a_4292_);
lean_dec(v___x_4291_);
v___x_4294_ = lean_box(0);
v_isShared_4295_ = v_isSharedCheck_4303_;
goto v_resetjp_4293_;
}
v_resetjp_4293_:
{
lean_object* v___x_4296_; lean_object* v___x_4297_; lean_object* v___x_4298_; lean_object* v___x_4299_; lean_object* v___x_4301_; 
v___x_4296_ = l_Lean_Expr_mvarId_x21(v_a_4284_);
lean_dec(v_a_4284_);
v___x_4297_ = l_Lean_Expr_fvarId_x21(v_hyp_4277_);
lean_dec_ref(v_hyp_4277_);
v___x_4298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4298_, 0, v___x_4296_);
lean_ctor_set(v___x_4298_, 1, v___x_4297_);
v___x_4299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4299_, 0, v_a_4292_);
lean_ctor_set(v___x_4299_, 1, v___x_4298_);
if (v_isShared_4295_ == 0)
{
lean_ctor_set(v___x_4294_, 0, v___x_4299_);
v___x_4301_ = v___x_4294_;
goto v_reusejp_4300_;
}
else
{
lean_object* v_reuseFailAlloc_4302_; 
v_reuseFailAlloc_4302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4302_, 0, v___x_4299_);
v___x_4301_ = v_reuseFailAlloc_4302_;
goto v_reusejp_4300_;
}
v_reusejp_4300_:
{
return v___x_4301_;
}
}
}
else
{
lean_object* v_a_4304_; lean_object* v___x_4306_; uint8_t v_isShared_4307_; uint8_t v_isSharedCheck_4311_; 
lean_dec(v_a_4284_);
lean_dec_ref(v_hyp_4277_);
v_a_4304_ = lean_ctor_get(v___x_4291_, 0);
v_isSharedCheck_4311_ = !lean_is_exclusive(v___x_4291_);
if (v_isSharedCheck_4311_ == 0)
{
v___x_4306_ = v___x_4291_;
v_isShared_4307_ = v_isSharedCheck_4311_;
goto v_resetjp_4305_;
}
else
{
lean_inc(v_a_4304_);
lean_dec(v___x_4291_);
v___x_4306_ = lean_box(0);
v_isShared_4307_ = v_isSharedCheck_4311_;
goto v_resetjp_4305_;
}
v_resetjp_4305_:
{
lean_object* v___x_4309_; 
if (v_isShared_4307_ == 0)
{
v___x_4309_ = v___x_4306_;
goto v_reusejp_4308_;
}
else
{
lean_object* v_reuseFailAlloc_4310_; 
v_reuseFailAlloc_4310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4310_, 0, v_a_4304_);
v___x_4309_ = v_reuseFailAlloc_4310_;
goto v_reusejp_4308_;
}
v_reusejp_4308_:
{
return v___x_4309_;
}
}
}
}
else
{
lean_object* v_a_4312_; lean_object* v___x_4314_; uint8_t v_isShared_4315_; uint8_t v_isSharedCheck_4319_; 
lean_dec_ref(v_hyp_4277_);
v_a_4312_ = lean_ctor_get(v___x_4283_, 0);
v_isSharedCheck_4319_ = !lean_is_exclusive(v___x_4283_);
if (v_isSharedCheck_4319_ == 0)
{
v___x_4314_ = v___x_4283_;
v_isShared_4315_ = v_isSharedCheck_4319_;
goto v_resetjp_4313_;
}
else
{
lean_inc(v_a_4312_);
lean_dec(v___x_4283_);
v___x_4314_ = lean_box(0);
v_isShared_4315_ = v_isSharedCheck_4319_;
goto v_resetjp_4313_;
}
v_resetjp_4313_:
{
lean_object* v___x_4317_; 
if (v_isShared_4315_ == 0)
{
v___x_4317_ = v___x_4314_;
goto v_reusejp_4316_;
}
else
{
lean_object* v_reuseFailAlloc_4318_; 
v_reuseFailAlloc_4318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4318_, 0, v_a_4312_);
v___x_4317_ = v_reuseFailAlloc_4318_;
goto v_reusejp_4316_;
}
v_reusejp_4316_:
{
return v___x_4317_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkByCasesSubgoal___lam__0___boxed(lean_object* v_goalType_4320_, lean_object* v_tag_4321_, lean_object* v_hyp_4322_, lean_object* v___y_4323_, lean_object* v___y_4324_, lean_object* v___y_4325_, lean_object* v___y_4326_, lean_object* v___y_4327_){
_start:
{
lean_object* v_res_4328_; 
v_res_4328_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkByCasesSubgoal___lam__0(v_goalType_4320_, v_tag_4321_, v_hyp_4322_, v___y_4323_, v___y_4324_, v___y_4325_, v___y_4326_);
lean_dec(v___y_4326_);
lean_dec_ref(v___y_4325_);
lean_dec(v___y_4324_);
lean_dec_ref(v___y_4323_);
return v_res_4328_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkByCasesSubgoal(lean_object* v_p_4329_, lean_object* v_hName_4330_, lean_object* v_goalType_4331_, lean_object* v_tag_4332_, lean_object* v_a_4333_, lean_object* v_a_4334_, lean_object* v_a_4335_, lean_object* v_a_4336_){
_start:
{
lean_object* v___f_4338_; lean_object* v___x_4339_; 
v___f_4338_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkByCasesSubgoal___lam__0___boxed), 8, 2);
lean_closure_set(v___f_4338_, 0, v_goalType_4331_);
lean_closure_set(v___f_4338_, 1, v_tag_4332_);
v___x_4339_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0___redArg(v_hName_4330_, v_p_4329_, v___f_4338_, v_a_4333_, v_a_4334_, v_a_4335_, v_a_4336_);
return v___x_4339_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkByCasesSubgoal___boxed(lean_object* v_p_4340_, lean_object* v_hName_4341_, lean_object* v_goalType_4342_, lean_object* v_tag_4343_, lean_object* v_a_4344_, lean_object* v_a_4345_, lean_object* v_a_4346_, lean_object* v_a_4347_, lean_object* v_a_4348_){
_start:
{
lean_object* v_res_4349_; 
v_res_4349_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkByCasesSubgoal(v_p_4340_, v_hName_4341_, v_goalType_4342_, v_tag_4343_, v_a_4344_, v_a_4345_, v_a_4346_, v_a_4347_);
lean_dec(v_a_4347_);
lean_dec_ref(v_a_4346_);
lean_dec(v_a_4345_);
lean_dec_ref(v_a_4344_);
return v_res_4349_;
}
}
static lean_object* _init_l_Lean_MVarId_byCases___lam__0___closed__7(void){
_start:
{
lean_object* v___x_4361_; lean_object* v___x_4362_; lean_object* v___x_4363_; 
v___x_4361_ = lean_box(0);
v___x_4362_ = ((lean_object*)(l_Lean_MVarId_byCases___lam__0___closed__6));
v___x_4363_ = l_Lean_Expr_const___override(v___x_4362_, v___x_4361_);
return v___x_4363_;
}
}
static lean_object* _init_l_Lean_MVarId_byCases___lam__0___closed__10(void){
_start:
{
lean_object* v___x_4367_; lean_object* v___x_4368_; 
v___x_4367_ = ((lean_object*)(l_Lean_MVarId_byCases___lam__0___closed__9));
v___x_4368_ = l_Lean_stringToMessageData(v___x_4367_);
return v___x_4368_;
}
}
static lean_object* _init_l_Lean_MVarId_byCases___lam__0___closed__11(void){
_start:
{
lean_object* v___x_4369_; lean_object* v___x_4370_; 
v___x_4369_ = lean_obj_once(&l_Lean_MVarId_byCases___lam__0___closed__10, &l_Lean_MVarId_byCases___lam__0___closed__10_once, _init_l_Lean_MVarId_byCases___lam__0___closed__10);
v___x_4370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4370_, 0, v___x_4369_);
return v___x_4370_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_byCases___lam__0(lean_object* v_mvarId_4371_, lean_object* v_p_4372_, lean_object* v_hName_4373_, lean_object* v___y_4374_, lean_object* v___y_4375_, lean_object* v___y_4376_, lean_object* v___y_4377_){
_start:
{
lean_object* v___x_4379_; 
lean_inc(v_mvarId_4371_);
v___x_4379_ = l_Lean_MVarId_getType(v_mvarId_4371_, v___y_4374_, v___y_4375_, v___y_4376_, v___y_4377_);
if (lean_obj_tag(v___x_4379_) == 0)
{
lean_object* v_a_4380_; lean_object* v___x_4381_; 
v_a_4380_ = lean_ctor_get(v___x_4379_, 0);
lean_inc(v_a_4380_);
lean_dec_ref_known(v___x_4379_, 1);
lean_inc(v_mvarId_4371_);
v___x_4381_ = l_Lean_MVarId_getTag(v_mvarId_4371_, v___y_4374_, v___y_4375_, v___y_4376_, v___y_4377_);
if (lean_obj_tag(v___x_4381_) == 0)
{
lean_object* v_a_4382_; lean_object* v___y_4384_; lean_object* v___y_4385_; lean_object* v___y_4386_; lean_object* v___y_4387_; lean_object* v___x_4435_; 
v_a_4382_ = lean_ctor_get(v___x_4381_, 0);
lean_inc(v_a_4382_);
lean_dec_ref_known(v___x_4381_, 1);
lean_inc(v_a_4380_);
v___x_4435_ = l_Lean_Meta_isProp(v_a_4380_, v___y_4374_, v___y_4375_, v___y_4376_, v___y_4377_);
if (lean_obj_tag(v___x_4435_) == 0)
{
lean_object* v_a_4436_; uint8_t v___x_4437_; 
v_a_4436_ = lean_ctor_get(v___x_4435_, 0);
lean_inc(v_a_4436_);
lean_dec_ref_known(v___x_4435_, 1);
v___x_4437_ = lean_unbox(v_a_4436_);
lean_dec(v_a_4436_);
if (v___x_4437_ == 0)
{
lean_object* v___x_4438_; lean_object* v___x_4439_; lean_object* v___x_4440_; 
v___x_4438_ = ((lean_object*)(l_Lean_MVarId_byCases___lam__0___closed__8));
v___x_4439_ = lean_obj_once(&l_Lean_MVarId_byCases___lam__0___closed__11, &l_Lean_MVarId_byCases___lam__0___closed__11_once, _init_l_Lean_MVarId_byCases___lam__0___closed__11);
lean_inc(v_mvarId_4371_);
v___x_4440_ = l_Lean_Meta_throwTacticEx___redArg(v___x_4438_, v_mvarId_4371_, v___x_4439_, v___y_4374_, v___y_4375_, v___y_4376_, v___y_4377_);
if (lean_obj_tag(v___x_4440_) == 0)
{
lean_dec_ref_known(v___x_4440_, 1);
v___y_4384_ = v___y_4374_;
v___y_4385_ = v___y_4375_;
v___y_4386_ = v___y_4376_;
v___y_4387_ = v___y_4377_;
goto v___jp_4383_;
}
else
{
lean_object* v_a_4441_; lean_object* v___x_4443_; uint8_t v_isShared_4444_; uint8_t v_isSharedCheck_4448_; 
lean_dec(v_a_4382_);
lean_dec(v_a_4380_);
lean_dec(v_hName_4373_);
lean_dec_ref(v_p_4372_);
lean_dec(v_mvarId_4371_);
v_a_4441_ = lean_ctor_get(v___x_4440_, 0);
v_isSharedCheck_4448_ = !lean_is_exclusive(v___x_4440_);
if (v_isSharedCheck_4448_ == 0)
{
v___x_4443_ = v___x_4440_;
v_isShared_4444_ = v_isSharedCheck_4448_;
goto v_resetjp_4442_;
}
else
{
lean_inc(v_a_4441_);
lean_dec(v___x_4440_);
v___x_4443_ = lean_box(0);
v_isShared_4444_ = v_isSharedCheck_4448_;
goto v_resetjp_4442_;
}
v_resetjp_4442_:
{
lean_object* v___x_4446_; 
if (v_isShared_4444_ == 0)
{
v___x_4446_ = v___x_4443_;
goto v_reusejp_4445_;
}
else
{
lean_object* v_reuseFailAlloc_4447_; 
v_reuseFailAlloc_4447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4447_, 0, v_a_4441_);
v___x_4446_ = v_reuseFailAlloc_4447_;
goto v_reusejp_4445_;
}
v_reusejp_4445_:
{
return v___x_4446_;
}
}
}
}
else
{
v___y_4384_ = v___y_4374_;
v___y_4385_ = v___y_4375_;
v___y_4386_ = v___y_4376_;
v___y_4387_ = v___y_4377_;
goto v___jp_4383_;
}
}
else
{
lean_object* v_a_4449_; lean_object* v___x_4451_; uint8_t v_isShared_4452_; uint8_t v_isSharedCheck_4456_; 
lean_dec(v_a_4382_);
lean_dec(v_a_4380_);
lean_dec(v_hName_4373_);
lean_dec_ref(v_p_4372_);
lean_dec(v_mvarId_4371_);
v_a_4449_ = lean_ctor_get(v___x_4435_, 0);
v_isSharedCheck_4456_ = !lean_is_exclusive(v___x_4435_);
if (v_isSharedCheck_4456_ == 0)
{
v___x_4451_ = v___x_4435_;
v_isShared_4452_ = v_isSharedCheck_4456_;
goto v_resetjp_4450_;
}
else
{
lean_inc(v_a_4449_);
lean_dec(v___x_4435_);
v___x_4451_ = lean_box(0);
v_isShared_4452_ = v_isSharedCheck_4456_;
goto v_resetjp_4450_;
}
v_resetjp_4450_:
{
lean_object* v___x_4454_; 
if (v_isShared_4452_ == 0)
{
v___x_4454_ = v___x_4451_;
goto v_reusejp_4453_;
}
else
{
lean_object* v_reuseFailAlloc_4455_; 
v_reuseFailAlloc_4455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4455_, 0, v_a_4449_);
v___x_4454_ = v_reuseFailAlloc_4455_;
goto v_reusejp_4453_;
}
v_reusejp_4453_:
{
return v___x_4454_;
}
}
}
v___jp_4383_:
{
lean_object* v___x_4388_; lean_object* v___x_4389_; lean_object* v___x_4390_; 
v___x_4388_ = ((lean_object*)(l_Lean_MVarId_byCases___lam__0___closed__1));
lean_inc(v_a_4382_);
v___x_4389_ = l_Lean_Name_append(v_a_4382_, v___x_4388_);
lean_inc(v_a_4380_);
lean_inc(v_hName_4373_);
lean_inc_ref(v_p_4372_);
v___x_4390_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkByCasesSubgoal(v_p_4372_, v_hName_4373_, v_a_4380_, v___x_4389_, v___y_4384_, v___y_4385_, v___y_4386_, v___y_4387_);
if (lean_obj_tag(v___x_4390_) == 0)
{
lean_object* v_a_4391_; lean_object* v_fst_4392_; lean_object* v_snd_4393_; lean_object* v___x_4394_; lean_object* v___x_4395_; lean_object* v___x_4396_; lean_object* v___x_4397_; 
v_a_4391_ = lean_ctor_get(v___x_4390_, 0);
lean_inc(v_a_4391_);
lean_dec_ref_known(v___x_4390_, 1);
v_fst_4392_ = lean_ctor_get(v_a_4391_, 0);
lean_inc(v_fst_4392_);
v_snd_4393_ = lean_ctor_get(v_a_4391_, 1);
lean_inc(v_snd_4393_);
lean_dec(v_a_4391_);
lean_inc_ref(v_p_4372_);
v___x_4394_ = l_Lean_mkNot(v_p_4372_);
v___x_4395_ = ((lean_object*)(l_Lean_MVarId_byCases___lam__0___closed__3));
v___x_4396_ = l_Lean_Name_append(v_a_4382_, v___x_4395_);
lean_inc(v_a_4380_);
v___x_4397_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkByCasesSubgoal(v___x_4394_, v_hName_4373_, v_a_4380_, v___x_4396_, v___y_4384_, v___y_4385_, v___y_4386_, v___y_4387_);
if (lean_obj_tag(v___x_4397_) == 0)
{
lean_object* v_a_4398_; lean_object* v_fst_4399_; lean_object* v_snd_4400_; lean_object* v___x_4402_; uint8_t v_isShared_4403_; uint8_t v_isSharedCheck_4418_; 
v_a_4398_ = lean_ctor_get(v___x_4397_, 0);
lean_inc(v_a_4398_);
lean_dec_ref_known(v___x_4397_, 1);
v_fst_4399_ = lean_ctor_get(v_a_4398_, 0);
v_snd_4400_ = lean_ctor_get(v_a_4398_, 1);
v_isSharedCheck_4418_ = !lean_is_exclusive(v_a_4398_);
if (v_isSharedCheck_4418_ == 0)
{
v___x_4402_ = v_a_4398_;
v_isShared_4403_ = v_isSharedCheck_4418_;
goto v_resetjp_4401_;
}
else
{
lean_inc(v_snd_4400_);
lean_inc(v_fst_4399_);
lean_dec(v_a_4398_);
v___x_4402_ = lean_box(0);
v_isShared_4403_ = v_isSharedCheck_4418_;
goto v_resetjp_4401_;
}
v_resetjp_4401_:
{
lean_object* v___x_4404_; lean_object* v___x_4405_; lean_object* v___x_4406_; lean_object* v___x_4408_; uint8_t v_isShared_4409_; uint8_t v_isSharedCheck_4416_; 
v___x_4404_ = lean_obj_once(&l_Lean_MVarId_byCases___lam__0___closed__7, &l_Lean_MVarId_byCases___lam__0___closed__7_once, _init_l_Lean_MVarId_byCases___lam__0___closed__7);
v___x_4405_ = l_Lean_mkApp4(v___x_4404_, v_p_4372_, v_a_4380_, v_fst_4392_, v_fst_4399_);
v___x_4406_ = l_Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1___redArg(v_mvarId_4371_, v___x_4405_, v___y_4385_);
v_isSharedCheck_4416_ = !lean_is_exclusive(v___x_4406_);
if (v_isSharedCheck_4416_ == 0)
{
lean_object* v_unused_4417_; 
v_unused_4417_ = lean_ctor_get(v___x_4406_, 0);
lean_dec(v_unused_4417_);
v___x_4408_ = v___x_4406_;
v_isShared_4409_ = v_isSharedCheck_4416_;
goto v_resetjp_4407_;
}
else
{
lean_dec(v___x_4406_);
v___x_4408_ = lean_box(0);
v_isShared_4409_ = v_isSharedCheck_4416_;
goto v_resetjp_4407_;
}
v_resetjp_4407_:
{
lean_object* v___x_4411_; 
if (v_isShared_4403_ == 0)
{
lean_ctor_set(v___x_4402_, 0, v_snd_4393_);
v___x_4411_ = v___x_4402_;
goto v_reusejp_4410_;
}
else
{
lean_object* v_reuseFailAlloc_4415_; 
v_reuseFailAlloc_4415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4415_, 0, v_snd_4393_);
lean_ctor_set(v_reuseFailAlloc_4415_, 1, v_snd_4400_);
v___x_4411_ = v_reuseFailAlloc_4415_;
goto v_reusejp_4410_;
}
v_reusejp_4410_:
{
lean_object* v___x_4413_; 
if (v_isShared_4409_ == 0)
{
lean_ctor_set(v___x_4408_, 0, v___x_4411_);
v___x_4413_ = v___x_4408_;
goto v_reusejp_4412_;
}
else
{
lean_object* v_reuseFailAlloc_4414_; 
v_reuseFailAlloc_4414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4414_, 0, v___x_4411_);
v___x_4413_ = v_reuseFailAlloc_4414_;
goto v_reusejp_4412_;
}
v_reusejp_4412_:
{
return v___x_4413_;
}
}
}
}
}
else
{
lean_object* v_a_4419_; lean_object* v___x_4421_; uint8_t v_isShared_4422_; uint8_t v_isSharedCheck_4426_; 
lean_dec(v_snd_4393_);
lean_dec(v_fst_4392_);
lean_dec(v_a_4380_);
lean_dec_ref(v_p_4372_);
lean_dec(v_mvarId_4371_);
v_a_4419_ = lean_ctor_get(v___x_4397_, 0);
v_isSharedCheck_4426_ = !lean_is_exclusive(v___x_4397_);
if (v_isSharedCheck_4426_ == 0)
{
v___x_4421_ = v___x_4397_;
v_isShared_4422_ = v_isSharedCheck_4426_;
goto v_resetjp_4420_;
}
else
{
lean_inc(v_a_4419_);
lean_dec(v___x_4397_);
v___x_4421_ = lean_box(0);
v_isShared_4422_ = v_isSharedCheck_4426_;
goto v_resetjp_4420_;
}
v_resetjp_4420_:
{
lean_object* v___x_4424_; 
if (v_isShared_4422_ == 0)
{
v___x_4424_ = v___x_4421_;
goto v_reusejp_4423_;
}
else
{
lean_object* v_reuseFailAlloc_4425_; 
v_reuseFailAlloc_4425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4425_, 0, v_a_4419_);
v___x_4424_ = v_reuseFailAlloc_4425_;
goto v_reusejp_4423_;
}
v_reusejp_4423_:
{
return v___x_4424_;
}
}
}
}
else
{
lean_object* v_a_4427_; lean_object* v___x_4429_; uint8_t v_isShared_4430_; uint8_t v_isSharedCheck_4434_; 
lean_dec(v_a_4382_);
lean_dec(v_a_4380_);
lean_dec(v_hName_4373_);
lean_dec_ref(v_p_4372_);
lean_dec(v_mvarId_4371_);
v_a_4427_ = lean_ctor_get(v___x_4390_, 0);
v_isSharedCheck_4434_ = !lean_is_exclusive(v___x_4390_);
if (v_isSharedCheck_4434_ == 0)
{
v___x_4429_ = v___x_4390_;
v_isShared_4430_ = v_isSharedCheck_4434_;
goto v_resetjp_4428_;
}
else
{
lean_inc(v_a_4427_);
lean_dec(v___x_4390_);
v___x_4429_ = lean_box(0);
v_isShared_4430_ = v_isSharedCheck_4434_;
goto v_resetjp_4428_;
}
v_resetjp_4428_:
{
lean_object* v___x_4432_; 
if (v_isShared_4430_ == 0)
{
v___x_4432_ = v___x_4429_;
goto v_reusejp_4431_;
}
else
{
lean_object* v_reuseFailAlloc_4433_; 
v_reuseFailAlloc_4433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4433_, 0, v_a_4427_);
v___x_4432_ = v_reuseFailAlloc_4433_;
goto v_reusejp_4431_;
}
v_reusejp_4431_:
{
return v___x_4432_;
}
}
}
}
}
else
{
lean_object* v_a_4457_; lean_object* v___x_4459_; uint8_t v_isShared_4460_; uint8_t v_isSharedCheck_4464_; 
lean_dec(v_a_4380_);
lean_dec(v_hName_4373_);
lean_dec_ref(v_p_4372_);
lean_dec(v_mvarId_4371_);
v_a_4457_ = lean_ctor_get(v___x_4381_, 0);
v_isSharedCheck_4464_ = !lean_is_exclusive(v___x_4381_);
if (v_isSharedCheck_4464_ == 0)
{
v___x_4459_ = v___x_4381_;
v_isShared_4460_ = v_isSharedCheck_4464_;
goto v_resetjp_4458_;
}
else
{
lean_inc(v_a_4457_);
lean_dec(v___x_4381_);
v___x_4459_ = lean_box(0);
v_isShared_4460_ = v_isSharedCheck_4464_;
goto v_resetjp_4458_;
}
v_resetjp_4458_:
{
lean_object* v___x_4462_; 
if (v_isShared_4460_ == 0)
{
v___x_4462_ = v___x_4459_;
goto v_reusejp_4461_;
}
else
{
lean_object* v_reuseFailAlloc_4463_; 
v_reuseFailAlloc_4463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4463_, 0, v_a_4457_);
v___x_4462_ = v_reuseFailAlloc_4463_;
goto v_reusejp_4461_;
}
v_reusejp_4461_:
{
return v___x_4462_;
}
}
}
}
else
{
lean_object* v_a_4465_; lean_object* v___x_4467_; uint8_t v_isShared_4468_; uint8_t v_isSharedCheck_4472_; 
lean_dec(v_hName_4373_);
lean_dec_ref(v_p_4372_);
lean_dec(v_mvarId_4371_);
v_a_4465_ = lean_ctor_get(v___x_4379_, 0);
v_isSharedCheck_4472_ = !lean_is_exclusive(v___x_4379_);
if (v_isSharedCheck_4472_ == 0)
{
v___x_4467_ = v___x_4379_;
v_isShared_4468_ = v_isSharedCheck_4472_;
goto v_resetjp_4466_;
}
else
{
lean_inc(v_a_4465_);
lean_dec(v___x_4379_);
v___x_4467_ = lean_box(0);
v_isShared_4468_ = v_isSharedCheck_4472_;
goto v_resetjp_4466_;
}
v_resetjp_4466_:
{
lean_object* v___x_4470_; 
if (v_isShared_4468_ == 0)
{
v___x_4470_ = v___x_4467_;
goto v_reusejp_4469_;
}
else
{
lean_object* v_reuseFailAlloc_4471_; 
v_reuseFailAlloc_4471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4471_, 0, v_a_4465_);
v___x_4470_ = v_reuseFailAlloc_4471_;
goto v_reusejp_4469_;
}
v_reusejp_4469_:
{
return v___x_4470_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_byCases___lam__0___boxed(lean_object* v_mvarId_4473_, lean_object* v_p_4474_, lean_object* v_hName_4475_, lean_object* v___y_4476_, lean_object* v___y_4477_, lean_object* v___y_4478_, lean_object* v___y_4479_, lean_object* v___y_4480_){
_start:
{
lean_object* v_res_4481_; 
v_res_4481_ = l_Lean_MVarId_byCases___lam__0(v_mvarId_4473_, v_p_4474_, v_hName_4475_, v___y_4476_, v___y_4477_, v___y_4478_, v___y_4479_);
lean_dec(v___y_4479_);
lean_dec_ref(v___y_4478_);
lean_dec(v___y_4477_);
lean_dec_ref(v___y_4476_);
return v_res_4481_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_byCases(lean_object* v_mvarId_4482_, lean_object* v_p_4483_, lean_object* v_hName_4484_, lean_object* v_a_4485_, lean_object* v_a_4486_, lean_object* v_a_4487_, lean_object* v_a_4488_){
_start:
{
lean_object* v___f_4490_; lean_object* v___x_4491_; 
lean_inc(v_mvarId_4482_);
v___f_4490_ = lean_alloc_closure((void*)(l_Lean_MVarId_byCases___lam__0___boxed), 8, 3);
lean_closure_set(v___f_4490_, 0, v_mvarId_4482_);
lean_closure_set(v___f_4490_, 1, v_p_4483_);
lean_closure_set(v___f_4490_, 2, v_hName_4484_);
v___x_4491_ = l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2___redArg(v_mvarId_4482_, v___f_4490_, v_a_4485_, v_a_4486_, v_a_4487_, v_a_4488_);
return v___x_4491_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_byCases___boxed(lean_object* v_mvarId_4492_, lean_object* v_p_4493_, lean_object* v_hName_4494_, lean_object* v_a_4495_, lean_object* v_a_4496_, lean_object* v_a_4497_, lean_object* v_a_4498_, lean_object* v_a_4499_){
_start:
{
lean_object* v_res_4500_; 
v_res_4500_ = l_Lean_MVarId_byCases(v_mvarId_4492_, v_p_4493_, v_hName_4494_, v_a_4495_, v_a_4496_, v_a_4497_, v_a_4498_);
lean_dec(v_a_4498_);
lean_dec_ref(v_a_4497_);
lean_dec(v_a_4496_);
lean_dec_ref(v_a_4495_);
return v_res_4500_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_byCasesDec___lam__0(lean_object* v_mvarId_4504_, lean_object* v_p_4505_, lean_object* v_hName_4506_, lean_object* v_dec_4507_, lean_object* v___y_4508_, lean_object* v___y_4509_, lean_object* v___y_4510_, lean_object* v___y_4511_){
_start:
{
lean_object* v___x_4513_; 
lean_inc(v_mvarId_4504_);
v___x_4513_ = l_Lean_MVarId_getType(v_mvarId_4504_, v___y_4508_, v___y_4509_, v___y_4510_, v___y_4511_);
if (lean_obj_tag(v___x_4513_) == 0)
{
lean_object* v_a_4514_; lean_object* v___x_4515_; 
v_a_4514_ = lean_ctor_get(v___x_4513_, 0);
lean_inc(v_a_4514_);
lean_dec_ref_known(v___x_4513_, 1);
lean_inc(v_mvarId_4504_);
v___x_4515_ = l_Lean_MVarId_getTag(v_mvarId_4504_, v___y_4508_, v___y_4509_, v___y_4510_, v___y_4511_);
if (lean_obj_tag(v___x_4515_) == 0)
{
lean_object* v_a_4516_; lean_object* v___x_4517_; 
v_a_4516_ = lean_ctor_get(v___x_4515_, 0);
lean_inc(v_a_4516_);
lean_dec_ref_known(v___x_4515_, 1);
lean_inc(v_a_4514_);
v___x_4517_ = l_Lean_Meta_getLevel(v_a_4514_, v___y_4508_, v___y_4509_, v___y_4510_, v___y_4511_);
if (lean_obj_tag(v___x_4517_) == 0)
{
lean_object* v_a_4518_; lean_object* v___x_4519_; lean_object* v___x_4520_; lean_object* v___x_4521_; 
v_a_4518_ = lean_ctor_get(v___x_4517_, 0);
lean_inc(v_a_4518_);
lean_dec_ref_known(v___x_4517_, 1);
v___x_4519_ = ((lean_object*)(l_Lean_MVarId_byCases___lam__0___closed__1));
lean_inc(v_a_4516_);
v___x_4520_ = l_Lean_Name_append(v_a_4516_, v___x_4519_);
lean_inc(v_a_4514_);
lean_inc(v_hName_4506_);
lean_inc_ref(v_p_4505_);
v___x_4521_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkByCasesSubgoal(v_p_4505_, v_hName_4506_, v_a_4514_, v___x_4520_, v___y_4508_, v___y_4509_, v___y_4510_, v___y_4511_);
if (lean_obj_tag(v___x_4521_) == 0)
{
lean_object* v_a_4522_; lean_object* v_fst_4523_; lean_object* v_snd_4524_; lean_object* v___x_4526_; uint8_t v_isShared_4527_; uint8_t v_isSharedCheck_4566_; 
v_a_4522_ = lean_ctor_get(v___x_4521_, 0);
lean_inc(v_a_4522_);
lean_dec_ref_known(v___x_4521_, 1);
v_fst_4523_ = lean_ctor_get(v_a_4522_, 0);
v_snd_4524_ = lean_ctor_get(v_a_4522_, 1);
v_isSharedCheck_4566_ = !lean_is_exclusive(v_a_4522_);
if (v_isSharedCheck_4566_ == 0)
{
v___x_4526_ = v_a_4522_;
v_isShared_4527_ = v_isSharedCheck_4566_;
goto v_resetjp_4525_;
}
else
{
lean_inc(v_snd_4524_);
lean_inc(v_fst_4523_);
lean_dec(v_a_4522_);
v___x_4526_ = lean_box(0);
v_isShared_4527_ = v_isSharedCheck_4566_;
goto v_resetjp_4525_;
}
v_resetjp_4525_:
{
lean_object* v___x_4528_; lean_object* v___x_4529_; lean_object* v___x_4530_; lean_object* v___x_4531_; 
lean_inc_ref(v_p_4505_);
v___x_4528_ = l_Lean_mkNot(v_p_4505_);
v___x_4529_ = ((lean_object*)(l_Lean_MVarId_byCases___lam__0___closed__3));
v___x_4530_ = l_Lean_Name_append(v_a_4516_, v___x_4529_);
lean_inc(v_a_4514_);
v___x_4531_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkByCasesSubgoal(v___x_4528_, v_hName_4506_, v_a_4514_, v___x_4530_, v___y_4508_, v___y_4509_, v___y_4510_, v___y_4511_);
if (lean_obj_tag(v___x_4531_) == 0)
{
lean_object* v_a_4532_; lean_object* v_fst_4533_; lean_object* v_snd_4534_; lean_object* v___x_4536_; uint8_t v_isShared_4537_; uint8_t v_isSharedCheck_4557_; 
v_a_4532_ = lean_ctor_get(v___x_4531_, 0);
lean_inc(v_a_4532_);
lean_dec_ref_known(v___x_4531_, 1);
v_fst_4533_ = lean_ctor_get(v_a_4532_, 0);
v_snd_4534_ = lean_ctor_get(v_a_4532_, 1);
v_isSharedCheck_4557_ = !lean_is_exclusive(v_a_4532_);
if (v_isSharedCheck_4557_ == 0)
{
v___x_4536_ = v_a_4532_;
v_isShared_4537_ = v_isSharedCheck_4557_;
goto v_resetjp_4535_;
}
else
{
lean_inc(v_snd_4534_);
lean_inc(v_fst_4533_);
lean_dec(v_a_4532_);
v___x_4536_ = lean_box(0);
v_isShared_4537_ = v_isSharedCheck_4557_;
goto v_resetjp_4535_;
}
v_resetjp_4535_:
{
lean_object* v___x_4538_; lean_object* v___x_4539_; lean_object* v___x_4541_; 
v___x_4538_ = ((lean_object*)(l_Lean_MVarId_byCasesDec___lam__0___closed__1));
v___x_4539_ = lean_box(0);
if (v_isShared_4527_ == 0)
{
lean_ctor_set_tag(v___x_4526_, 1);
lean_ctor_set(v___x_4526_, 1, v___x_4539_);
lean_ctor_set(v___x_4526_, 0, v_a_4518_);
v___x_4541_ = v___x_4526_;
goto v_reusejp_4540_;
}
else
{
lean_object* v_reuseFailAlloc_4556_; 
v_reuseFailAlloc_4556_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4556_, 0, v_a_4518_);
lean_ctor_set(v_reuseFailAlloc_4556_, 1, v___x_4539_);
v___x_4541_ = v_reuseFailAlloc_4556_;
goto v_reusejp_4540_;
}
v_reusejp_4540_:
{
lean_object* v___x_4542_; lean_object* v___x_4543_; lean_object* v___x_4544_; lean_object* v___x_4546_; uint8_t v_isShared_4547_; uint8_t v_isSharedCheck_4554_; 
v___x_4542_ = l_Lean_Expr_const___override(v___x_4538_, v___x_4541_);
v___x_4543_ = l_Lean_mkApp5(v___x_4542_, v_a_4514_, v_p_4505_, v_dec_4507_, v_fst_4523_, v_fst_4533_);
v___x_4544_ = l_Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1___redArg(v_mvarId_4504_, v___x_4543_, v___y_4509_);
v_isSharedCheck_4554_ = !lean_is_exclusive(v___x_4544_);
if (v_isSharedCheck_4554_ == 0)
{
lean_object* v_unused_4555_; 
v_unused_4555_ = lean_ctor_get(v___x_4544_, 0);
lean_dec(v_unused_4555_);
v___x_4546_ = v___x_4544_;
v_isShared_4547_ = v_isSharedCheck_4554_;
goto v_resetjp_4545_;
}
else
{
lean_dec(v___x_4544_);
v___x_4546_ = lean_box(0);
v_isShared_4547_ = v_isSharedCheck_4554_;
goto v_resetjp_4545_;
}
v_resetjp_4545_:
{
lean_object* v___x_4549_; 
if (v_isShared_4537_ == 0)
{
lean_ctor_set(v___x_4536_, 0, v_snd_4524_);
v___x_4549_ = v___x_4536_;
goto v_reusejp_4548_;
}
else
{
lean_object* v_reuseFailAlloc_4553_; 
v_reuseFailAlloc_4553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4553_, 0, v_snd_4524_);
lean_ctor_set(v_reuseFailAlloc_4553_, 1, v_snd_4534_);
v___x_4549_ = v_reuseFailAlloc_4553_;
goto v_reusejp_4548_;
}
v_reusejp_4548_:
{
lean_object* v___x_4551_; 
if (v_isShared_4547_ == 0)
{
lean_ctor_set(v___x_4546_, 0, v___x_4549_);
v___x_4551_ = v___x_4546_;
goto v_reusejp_4550_;
}
else
{
lean_object* v_reuseFailAlloc_4552_; 
v_reuseFailAlloc_4552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4552_, 0, v___x_4549_);
v___x_4551_ = v_reuseFailAlloc_4552_;
goto v_reusejp_4550_;
}
v_reusejp_4550_:
{
return v___x_4551_;
}
}
}
}
}
}
else
{
lean_object* v_a_4558_; lean_object* v___x_4560_; uint8_t v_isShared_4561_; uint8_t v_isSharedCheck_4565_; 
lean_del_object(v___x_4526_);
lean_dec(v_snd_4524_);
lean_dec(v_fst_4523_);
lean_dec(v_a_4518_);
lean_dec(v_a_4514_);
lean_dec_ref(v_dec_4507_);
lean_dec_ref(v_p_4505_);
lean_dec(v_mvarId_4504_);
v_a_4558_ = lean_ctor_get(v___x_4531_, 0);
v_isSharedCheck_4565_ = !lean_is_exclusive(v___x_4531_);
if (v_isSharedCheck_4565_ == 0)
{
v___x_4560_ = v___x_4531_;
v_isShared_4561_ = v_isSharedCheck_4565_;
goto v_resetjp_4559_;
}
else
{
lean_inc(v_a_4558_);
lean_dec(v___x_4531_);
v___x_4560_ = lean_box(0);
v_isShared_4561_ = v_isSharedCheck_4565_;
goto v_resetjp_4559_;
}
v_resetjp_4559_:
{
lean_object* v___x_4563_; 
if (v_isShared_4561_ == 0)
{
v___x_4563_ = v___x_4560_;
goto v_reusejp_4562_;
}
else
{
lean_object* v_reuseFailAlloc_4564_; 
v_reuseFailAlloc_4564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4564_, 0, v_a_4558_);
v___x_4563_ = v_reuseFailAlloc_4564_;
goto v_reusejp_4562_;
}
v_reusejp_4562_:
{
return v___x_4563_;
}
}
}
}
}
else
{
lean_object* v_a_4567_; lean_object* v___x_4569_; uint8_t v_isShared_4570_; uint8_t v_isSharedCheck_4574_; 
lean_dec(v_a_4518_);
lean_dec(v_a_4516_);
lean_dec(v_a_4514_);
lean_dec_ref(v_dec_4507_);
lean_dec(v_hName_4506_);
lean_dec_ref(v_p_4505_);
lean_dec(v_mvarId_4504_);
v_a_4567_ = lean_ctor_get(v___x_4521_, 0);
v_isSharedCheck_4574_ = !lean_is_exclusive(v___x_4521_);
if (v_isSharedCheck_4574_ == 0)
{
v___x_4569_ = v___x_4521_;
v_isShared_4570_ = v_isSharedCheck_4574_;
goto v_resetjp_4568_;
}
else
{
lean_inc(v_a_4567_);
lean_dec(v___x_4521_);
v___x_4569_ = lean_box(0);
v_isShared_4570_ = v_isSharedCheck_4574_;
goto v_resetjp_4568_;
}
v_resetjp_4568_:
{
lean_object* v___x_4572_; 
if (v_isShared_4570_ == 0)
{
v___x_4572_ = v___x_4569_;
goto v_reusejp_4571_;
}
else
{
lean_object* v_reuseFailAlloc_4573_; 
v_reuseFailAlloc_4573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4573_, 0, v_a_4567_);
v___x_4572_ = v_reuseFailAlloc_4573_;
goto v_reusejp_4571_;
}
v_reusejp_4571_:
{
return v___x_4572_;
}
}
}
}
else
{
lean_object* v_a_4575_; lean_object* v___x_4577_; uint8_t v_isShared_4578_; uint8_t v_isSharedCheck_4582_; 
lean_dec(v_a_4516_);
lean_dec(v_a_4514_);
lean_dec_ref(v_dec_4507_);
lean_dec(v_hName_4506_);
lean_dec_ref(v_p_4505_);
lean_dec(v_mvarId_4504_);
v_a_4575_ = lean_ctor_get(v___x_4517_, 0);
v_isSharedCheck_4582_ = !lean_is_exclusive(v___x_4517_);
if (v_isSharedCheck_4582_ == 0)
{
v___x_4577_ = v___x_4517_;
v_isShared_4578_ = v_isSharedCheck_4582_;
goto v_resetjp_4576_;
}
else
{
lean_inc(v_a_4575_);
lean_dec(v___x_4517_);
v___x_4577_ = lean_box(0);
v_isShared_4578_ = v_isSharedCheck_4582_;
goto v_resetjp_4576_;
}
v_resetjp_4576_:
{
lean_object* v___x_4580_; 
if (v_isShared_4578_ == 0)
{
v___x_4580_ = v___x_4577_;
goto v_reusejp_4579_;
}
else
{
lean_object* v_reuseFailAlloc_4581_; 
v_reuseFailAlloc_4581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4581_, 0, v_a_4575_);
v___x_4580_ = v_reuseFailAlloc_4581_;
goto v_reusejp_4579_;
}
v_reusejp_4579_:
{
return v___x_4580_;
}
}
}
}
else
{
lean_object* v_a_4583_; lean_object* v___x_4585_; uint8_t v_isShared_4586_; uint8_t v_isSharedCheck_4590_; 
lean_dec(v_a_4514_);
lean_dec_ref(v_dec_4507_);
lean_dec(v_hName_4506_);
lean_dec_ref(v_p_4505_);
lean_dec(v_mvarId_4504_);
v_a_4583_ = lean_ctor_get(v___x_4515_, 0);
v_isSharedCheck_4590_ = !lean_is_exclusive(v___x_4515_);
if (v_isSharedCheck_4590_ == 0)
{
v___x_4585_ = v___x_4515_;
v_isShared_4586_ = v_isSharedCheck_4590_;
goto v_resetjp_4584_;
}
else
{
lean_inc(v_a_4583_);
lean_dec(v___x_4515_);
v___x_4585_ = lean_box(0);
v_isShared_4586_ = v_isSharedCheck_4590_;
goto v_resetjp_4584_;
}
v_resetjp_4584_:
{
lean_object* v___x_4588_; 
if (v_isShared_4586_ == 0)
{
v___x_4588_ = v___x_4585_;
goto v_reusejp_4587_;
}
else
{
lean_object* v_reuseFailAlloc_4589_; 
v_reuseFailAlloc_4589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4589_, 0, v_a_4583_);
v___x_4588_ = v_reuseFailAlloc_4589_;
goto v_reusejp_4587_;
}
v_reusejp_4587_:
{
return v___x_4588_;
}
}
}
}
else
{
lean_object* v_a_4591_; lean_object* v___x_4593_; uint8_t v_isShared_4594_; uint8_t v_isSharedCheck_4598_; 
lean_dec_ref(v_dec_4507_);
lean_dec(v_hName_4506_);
lean_dec_ref(v_p_4505_);
lean_dec(v_mvarId_4504_);
v_a_4591_ = lean_ctor_get(v___x_4513_, 0);
v_isSharedCheck_4598_ = !lean_is_exclusive(v___x_4513_);
if (v_isSharedCheck_4598_ == 0)
{
v___x_4593_ = v___x_4513_;
v_isShared_4594_ = v_isSharedCheck_4598_;
goto v_resetjp_4592_;
}
else
{
lean_inc(v_a_4591_);
lean_dec(v___x_4513_);
v___x_4593_ = lean_box(0);
v_isShared_4594_ = v_isSharedCheck_4598_;
goto v_resetjp_4592_;
}
v_resetjp_4592_:
{
lean_object* v___x_4596_; 
if (v_isShared_4594_ == 0)
{
v___x_4596_ = v___x_4593_;
goto v_reusejp_4595_;
}
else
{
lean_object* v_reuseFailAlloc_4597_; 
v_reuseFailAlloc_4597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4597_, 0, v_a_4591_);
v___x_4596_ = v_reuseFailAlloc_4597_;
goto v_reusejp_4595_;
}
v_reusejp_4595_:
{
return v___x_4596_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_byCasesDec___lam__0___boxed(lean_object* v_mvarId_4599_, lean_object* v_p_4600_, lean_object* v_hName_4601_, lean_object* v_dec_4602_, lean_object* v___y_4603_, lean_object* v___y_4604_, lean_object* v___y_4605_, lean_object* v___y_4606_, lean_object* v___y_4607_){
_start:
{
lean_object* v_res_4608_; 
v_res_4608_ = l_Lean_MVarId_byCasesDec___lam__0(v_mvarId_4599_, v_p_4600_, v_hName_4601_, v_dec_4602_, v___y_4603_, v___y_4604_, v___y_4605_, v___y_4606_);
lean_dec(v___y_4606_);
lean_dec_ref(v___y_4605_);
lean_dec(v___y_4604_);
lean_dec_ref(v___y_4603_);
return v_res_4608_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_byCasesDec(lean_object* v_mvarId_4609_, lean_object* v_p_4610_, lean_object* v_dec_4611_, lean_object* v_hName_4612_, lean_object* v_a_4613_, lean_object* v_a_4614_, lean_object* v_a_4615_, lean_object* v_a_4616_){
_start:
{
lean_object* v___f_4618_; lean_object* v___x_4619_; 
lean_inc(v_mvarId_4609_);
v___f_4618_ = lean_alloc_closure((void*)(l_Lean_MVarId_byCasesDec___lam__0___boxed), 9, 4);
lean_closure_set(v___f_4618_, 0, v_mvarId_4609_);
lean_closure_set(v___f_4618_, 1, v_p_4610_);
lean_closure_set(v___f_4618_, 2, v_hName_4612_);
lean_closure_set(v___f_4618_, 3, v_dec_4611_);
v___x_4619_ = l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2___redArg(v_mvarId_4609_, v___f_4618_, v_a_4613_, v_a_4614_, v_a_4615_, v_a_4616_);
return v___x_4619_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_byCasesDec___boxed(lean_object* v_mvarId_4620_, lean_object* v_p_4621_, lean_object* v_dec_4622_, lean_object* v_hName_4623_, lean_object* v_a_4624_, lean_object* v_a_4625_, lean_object* v_a_4626_, lean_object* v_a_4627_, lean_object* v_a_4628_){
_start:
{
lean_object* v_res_4629_; 
v_res_4629_ = l_Lean_MVarId_byCasesDec(v_mvarId_4620_, v_p_4621_, v_dec_4622_, v_hName_4623_, v_a_4624_, v_a_4625_, v_a_4626_, v_a_4627_);
lean_dec(v_a_4627_);
lean_dec_ref(v_a_4626_);
lean_dec(v_a_4625_);
lean_dec_ref(v_a_4624_);
return v_res_4629_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4681_; lean_object* v___x_4682_; lean_object* v___x_4683_; 
v___x_4681_ = lean_unsigned_to_nat(4241171151u);
v___x_4682_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_));
v___x_4683_ = l_Lean_Name_num___override(v___x_4682_, v___x_4681_);
return v___x_4683_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4685_; lean_object* v___x_4686_; lean_object* v___x_4687_; 
v___x_4685_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_));
v___x_4686_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_);
v___x_4687_ = l_Lean_Name_str___override(v___x_4686_, v___x_4685_);
return v___x_4687_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4689_; lean_object* v___x_4690_; lean_object* v___x_4691_; 
v___x_4689_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_));
v___x_4690_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_);
v___x_4691_ = l_Lean_Name_str___override(v___x_4690_, v___x_4689_);
return v___x_4691_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4692_; lean_object* v___x_4693_; lean_object* v___x_4694_; 
v___x_4692_ = lean_unsigned_to_nat(2u);
v___x_4693_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_);
v___x_4694_ = l_Lean_Name_num___override(v___x_4693_, v___x_4692_);
return v___x_4694_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4696_; uint8_t v___x_4697_; lean_object* v___x_4698_; lean_object* v___x_4699_; 
v___x_4696_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_));
v___x_4697_ = 0;
v___x_4698_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_);
v___x_4699_ = l_Lean_registerTraceClass(v___x_4696_, v___x_4697_, v___x_4698_);
return v___x_4699_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2____boxed(lean_object* v_a_4700_){
_start:
{
lean_object* v_res_4701_; 
v_res_4701_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_();
return v_res_4701_;
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
