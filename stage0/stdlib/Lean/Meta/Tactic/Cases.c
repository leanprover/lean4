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
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
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
v___x_802_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
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
size_t v_x_2547__boxed_906_; size_t v_x_2548__boxed_907_; lean_object* v_res_908_; 
v_x_2547__boxed_906_ = lean_unbox_usize(v_x_902_);
lean_dec(v_x_902_);
v_x_2548__boxed_907_ = lean_unbox_usize(v_x_903_);
lean_dec(v_x_903_);
v_res_908_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg(v_x_901_, v_x_2547__boxed_906_, v_x_2548__boxed_907_, v_x_904_, v_x_905_);
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
lean_object* v___x_943_; lean_object* v___x_945_; 
v___x_943_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1___redArg(v_eAssignment_937_, v_mvarId_916_, v_val_917_);
if (v_isShared_942_ == 0)
{
lean_ctor_set(v___x_941_, 8, v___x_943_);
v___x_945_ = v___x_941_;
goto v_reusejp_944_;
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
lean_ctor_set(v_reuseFailAlloc_952_, 8, v___x_943_);
lean_ctor_set(v_reuseFailAlloc_952_, 9, v_dAssignment_938_);
lean_ctor_set(v_reuseFailAlloc_952_, 10, v_instanceTypedMVars_939_);
v___x_945_ = v_reuseFailAlloc_952_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
lean_object* v___x_947_; 
if (v_isShared_928_ == 0)
{
lean_ctor_set(v___x_927_, 0, v___x_945_);
v___x_947_ = v___x_927_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v___x_945_);
lean_ctor_set(v_reuseFailAlloc_951_, 1, v_cache_922_);
lean_ctor_set(v_reuseFailAlloc_951_, 2, v_zetaDeltaFVarIds_923_);
lean_ctor_set(v_reuseFailAlloc_951_, 3, v_postponed_924_);
lean_ctor_set(v_reuseFailAlloc_951_, 4, v_diag_925_);
v___x_947_ = v_reuseFailAlloc_951_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; 
v___x_948_ = lean_st_ref_put(v___y_918_, v___x_947_);
v___x_949_ = lean_box(0);
v___x_950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_950_, 0, v___x_949_);
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
size_t v_x_2934__boxed_1093_; size_t v_x_2935__boxed_1094_; lean_object* v_res_1095_; 
v_x_2934__boxed_1093_ = lean_unbox_usize(v_x_1089_);
lean_dec(v_x_1089_);
v_x_2935__boxed_1094_ = lean_unbox_usize(v_x_1090_);
lean_dec(v_x_1090_);
v_res_1095_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3(v_00_u03b2_1087_, v_x_1088_, v_x_2934__boxed_1093_, v_x_2935__boxed_1094_, v_x_1091_, v_x_1092_);
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
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__0(lean_object* v_mvarId_1124_, lean_object* v_newEqs_1125_, uint8_t v___x_1126_, lean_object* v_h_x27_1127_, lean_object* v_newIndices_1128_, lean_object* v___x_1129_, lean_object* v___x_1130_, lean_object* v___x_1131_, lean_object* v___x_1132_, lean_object* v_e_1133_, lean_object* v___x_1134_, lean_object* v_newEq_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_){
_start:
{
lean_object* v___x_1141_; 
lean_inc(v_mvarId_1124_);
v___x_1141_ = l_Lean_MVarId_getType(v_mvarId_1124_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_);
if (lean_obj_tag(v___x_1141_) == 0)
{
lean_object* v_a_1142_; lean_object* v___x_1143_; 
v_a_1142_ = lean_ctor_get(v___x_1141_, 0);
lean_inc(v_a_1142_);
lean_dec_ref_known(v___x_1141_, 1);
lean_inc(v_mvarId_1124_);
v___x_1143_ = l_Lean_MVarId_getTag(v_mvarId_1124_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_);
if (lean_obj_tag(v___x_1143_) == 0)
{
lean_object* v_a_1144_; lean_object* v___x_1145_; uint8_t v___x_1146_; uint8_t v___x_1147_; lean_object* v___x_1148_; 
v_a_1144_ = lean_ctor_get(v___x_1143_, 0);
lean_inc(v_a_1144_);
lean_dec_ref_known(v___x_1143_, 1);
v___x_1145_ = lean_array_push(v_newEqs_1125_, v_newEq_1135_);
v___x_1146_ = 1;
v___x_1147_ = 1;
v___x_1148_ = l_Lean_Meta_mkForallFVars(v___x_1145_, v_a_1142_, v___x_1126_, v___x_1146_, v___x_1146_, v___x_1147_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_);
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
v___x_1158_ = l_Lean_Meta_mkFreshExprMVarAt(v___x_1129_, v___x_1130_, v_a_1156_, v___x_1157_, v_a_1144_, v___x_1131_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_);
if (lean_obj_tag(v___x_1158_) == 0)
{
lean_object* v_a_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; 
v_a_1159_ = lean_ctor_get(v___x_1158_, 0);
lean_inc_n(v_a_1159_, 2);
lean_dec_ref_known(v___x_1158_, 1);
v___x_1160_ = l_Lean_mkAppN(v_a_1159_, v___x_1132_);
v___x_1161_ = l_Lean_Expr_app___override(v___x_1160_, v_e_1133_);
v___x_1162_ = l_Lean_mkAppN(v___x_1161_, v___x_1134_);
v___x_1163_ = l_Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1___redArg(v_mvarId_1124_, v___x_1162_, v___y_1137_);
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
v___x_1178_ = lean_array_get_size(v___x_1145_);
lean_dec_ref(v___x_1145_);
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
lean_dec_ref(v___x_1145_);
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
lean_dec_ref(v___x_1145_);
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
lean_dec_ref(v___x_1145_);
lean_dec_ref(v_e_1133_);
lean_dec(v_mvarId_1124_);
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
lean_dec_ref(v___x_1145_);
lean_dec(v_a_1144_);
lean_dec_ref(v_e_1133_);
lean_dec(v___x_1131_);
lean_dec_ref(v___x_1130_);
lean_dec_ref(v___x_1129_);
lean_dec(v_mvarId_1124_);
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
lean_dec_ref(v___x_1145_);
lean_dec(v_a_1144_);
lean_dec_ref(v_e_1133_);
lean_dec(v___x_1131_);
lean_dec_ref(v___x_1130_);
lean_dec_ref(v___x_1129_);
lean_dec(v_mvarId_1124_);
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
lean_dec_ref(v___x_1145_);
lean_dec(v_a_1144_);
lean_dec_ref(v_e_1133_);
lean_dec(v___x_1131_);
lean_dec_ref(v___x_1130_);
lean_dec_ref(v___x_1129_);
lean_dec_ref(v_h_x27_1127_);
lean_dec(v_mvarId_1124_);
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
lean_dec(v_a_1142_);
lean_dec_ref(v_newEq_1135_);
lean_dec_ref(v_e_1133_);
lean_dec(v___x_1131_);
lean_dec_ref(v___x_1130_);
lean_dec_ref(v___x_1129_);
lean_dec_ref(v_h_x27_1127_);
lean_dec_ref(v_newEqs_1125_);
lean_dec(v_mvarId_1124_);
v_a_1232_ = lean_ctor_get(v___x_1143_, 0);
v_isSharedCheck_1239_ = !lean_is_exclusive(v___x_1143_);
if (v_isSharedCheck_1239_ == 0)
{
v___x_1234_ = v___x_1143_;
v_isShared_1235_ = v_isSharedCheck_1239_;
goto v_resetjp_1233_;
}
else
{
lean_inc(v_a_1232_);
lean_dec(v___x_1143_);
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
lean_dec_ref(v_newEq_1135_);
lean_dec_ref(v_e_1133_);
lean_dec(v___x_1131_);
lean_dec_ref(v___x_1130_);
lean_dec_ref(v___x_1129_);
lean_dec_ref(v_h_x27_1127_);
lean_dec_ref(v_newEqs_1125_);
lean_dec(v_mvarId_1124_);
v_a_1240_ = lean_ctor_get(v___x_1141_, 0);
v_isSharedCheck_1247_ = !lean_is_exclusive(v___x_1141_);
if (v_isSharedCheck_1247_ == 0)
{
v___x_1242_ = v___x_1141_;
v_isShared_1243_ = v_isSharedCheck_1247_;
goto v_resetjp_1241_;
}
else
{
lean_inc(v_a_1240_);
lean_dec(v___x_1141_);
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
lean_object* v_mvarId_1248_ = _args[0];
lean_object* v_newEqs_1249_ = _args[1];
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
uint8_t v___x_6145__boxed_1265_; lean_object* v_res_1266_; 
v___x_6145__boxed_1265_ = lean_unbox(v___x_1250_);
v_res_1266_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__0(v_mvarId_1248_, v_newEqs_1249_, v___x_6145__boxed_1265_, v_h_x27_1251_, v_newIndices_1252_, v___x_1253_, v___x_1254_, v___x_1255_, v___x_1256_, v_e_1257_, v___x_1258_, v_newEq_1259_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_);
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
lean_closure_set(v___f_1289_, 0, v_mvarId_1269_);
lean_closure_set(v___f_1289_, 1, v_newEqs_1276_);
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
uint8_t v___x_6397__boxed_1316_; lean_object* v_res_1317_; 
v___x_6397__boxed_1316_ = lean_unbox(v___x_1303_);
v_res_1317_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__1(v_e_1300_, v_h_x27_1301_, v_mvarId_1302_, v___x_6397__boxed_1316_, v_newIndices_1304_, v___x_1305_, v___x_1306_, v___x_1307_, v___x_1308_, v_newEqs_1309_, v_newRefls_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_);
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
uint8_t v___x_6462__boxed_1349_; lean_object* v_res_1350_; 
v___x_6462__boxed_1349_ = lean_unbox(v___x_1337_);
v_res_1350_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__2(v_e_1335_, v_mvarId_1336_, v___x_6462__boxed_1349_, v_newIndices_1338_, v___x_1339_, v___x_1340_, v___x_1341_, v___x_1342_, v_h_x27_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_);
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
uint8_t v___x_6504__boxed_1403_; lean_object* v_res_1404_; 
v___x_6504__boxed_1403_ = lean_unbox(v___x_1389_);
v_res_1404_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__3(v_e_1387_, v_mvarId_1388_, v___x_6504__boxed_1403_, v___x_1390_, v___x_1391_, v___x_1392_, v___x_1393_, v___x_1394_, v_varName_x3f_1395_, v_newIndices_1396_, v_x_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_);
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
lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; 
v___x_1470_ = lean_unsigned_to_nat(0u);
v___x_1471_ = l_Array_extract___redArg(v_x_1435_, v___x_1470_, v_numParams_1463_);
v___x_1472_ = l_Lean_mkAppN(v_x_1434_, v___x_1471_);
lean_dec_ref(v___x_1471_);
lean_inc(v___y_1469_);
lean_inc_ref(v___y_1468_);
lean_inc(v___y_1467_);
lean_inc_ref(v___y_1466_);
lean_inc_ref(v___x_1472_);
v___x_1473_ = lean_infer_type(v___x_1472_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_);
if (lean_obj_tag(v___x_1473_) == 0)
{
lean_object* v_a_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___f_1479_; lean_object* v___x_1480_; 
v_a_1474_ = lean_ctor_get(v___x_1473_, 0);
lean_inc(v_a_1474_);
lean_dec_ref_known(v___x_1473_, 1);
v___x_1475_ = lean_array_get_size(v_x_1435_);
v___x_1476_ = lean_nat_sub(v___x_1475_, v_numIndices_1464_);
lean_dec(v_numIndices_1464_);
v___x_1477_ = l_Array_extract___redArg(v_x_1435_, v___x_1476_, v___x_1475_);
lean_dec_ref(v_x_1435_);
v___x_1478_ = lean_box(v___x_1459_);
v___f_1479_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__3___boxed), 16, 9);
lean_closure_set(v___f_1479_, 0, v_e_1430_);
lean_closure_set(v___f_1479_, 1, v_mvarId_1429_);
lean_closure_set(v___f_1479_, 2, v___x_1478_);
lean_closure_set(v___f_1479_, 3, v___x_1431_);
lean_closure_set(v___f_1479_, 4, v___x_1432_);
lean_closure_set(v___f_1479_, 5, v___x_1470_);
lean_closure_set(v___f_1479_, 6, v___x_1477_);
lean_closure_set(v___f_1479_, 7, v___x_1472_);
lean_closure_set(v___f_1479_, 8, v_varName_x3f_1433_);
v___x_1480_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_generalizeTargetsEq_spec__0___redArg(v_a_1474_, v___f_1479_, v___x_1459_, v___x_1459_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_);
return v___x_1480_;
}
else
{
lean_object* v_a_1481_; lean_object* v___x_1483_; uint8_t v_isShared_1484_; uint8_t v_isSharedCheck_1488_; 
lean_dec_ref(v___x_1472_);
lean_dec(v_numIndices_1464_);
lean_dec_ref(v_x_1435_);
lean_dec(v_varName_x3f_1433_);
lean_dec_ref(v___x_1432_);
lean_dec_ref(v___x_1431_);
lean_dec_ref(v_e_1430_);
lean_dec(v_mvarId_1429_);
v_a_1481_ = lean_ctor_get(v___x_1473_, 0);
v_isSharedCheck_1488_ = !lean_is_exclusive(v___x_1473_);
if (v_isSharedCheck_1488_ == 0)
{
v___x_1483_ = v___x_1473_;
v_isShared_1484_ = v_isSharedCheck_1488_;
goto v_resetjp_1482_;
}
else
{
lean_inc(v_a_1481_);
lean_dec(v___x_1473_);
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
lean_object* v___x_1541_; lean_object* v___x_1542_; 
v___x_1541_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__1));
lean_inc(v_mvarId_1533_);
v___x_1542_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_1533_, v___x_1541_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_);
if (lean_obj_tag(v___x_1542_) == 0)
{
lean_object* v_lctx_1543_; lean_object* v_localInstances_1544_; lean_object* v___x_1545_; 
lean_dec_ref_known(v___x_1542_, 1);
v_lctx_1543_ = lean_ctor_get(v___y_1536_, 2);
lean_inc_ref(v_lctx_1543_);
v_localInstances_1544_ = lean_ctor_get(v___y_1536_, 3);
lean_inc_ref(v_localInstances_1544_);
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
v___x_1554_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0(v_mvarId_1533_, v_e_1534_, v_lctx_1543_, v_localInstances_1544_, v_varName_x3f_1535_, v_a_1548_, v___x_1551_, v___x_1553_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_);
lean_dec(v___y_1539_);
lean_dec_ref(v___y_1538_);
lean_dec(v___y_1537_);
lean_dec_ref(v___y_1536_);
return v___x_1554_;
}
else
{
lean_object* v_a_1555_; lean_object* v___x_1557_; uint8_t v_isShared_1558_; uint8_t v_isSharedCheck_1562_; 
lean_dec_ref(v_localInstances_1544_);
lean_dec_ref(v_lctx_1543_);
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
lean_dec_ref(v_localInstances_1544_);
lean_dec_ref(v_lctx_1543_);
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
lean_dec(v___y_1539_);
lean_dec_ref(v___y_1538_);
lean_dec(v___y_1537_);
lean_dec_ref(v___y_1536_);
lean_dec(v_varName_x3f_1535_);
lean_dec_ref(v_e_1534_);
lean_dec(v_mvarId_1533_);
v_a_1571_ = lean_ctor_get(v___x_1542_, 0);
v_isSharedCheck_1578_ = !lean_is_exclusive(v___x_1542_);
if (v_isSharedCheck_1578_ == 0)
{
v___x_1573_ = v___x_1542_;
v_isShared_1574_ = v_isSharedCheck_1578_;
goto v_resetjp_1572_;
}
else
{
lean_inc(v_a_1571_);
lean_dec(v___x_1542_);
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
lean_object* v_declName_1670_; lean_object* v___x_1671_; lean_object* v_env_1672_; uint8_t v___x_1673_; lean_object* v___x_1674_; 
v_declName_1670_ = lean_ctor_get(v_x_1656_, 0);
v___x_1671_ = lean_st_ref_get(v___y_1659_);
v_env_1672_ = lean_ctor_get(v___x_1671_, 0);
lean_inc_ref(v_env_1672_);
lean_dec(v___x_1671_);
v___x_1673_ = 0;
lean_inc(v_declName_1670_);
v___x_1674_ = l_Lean_Environment_find_x3f(v_env_1672_, v_declName_1670_, v___x_1673_);
if (lean_obj_tag(v___x_1674_) == 0)
{
lean_dec_ref_known(v_x_1656_, 2);
lean_dec_ref(v_x_1657_);
lean_dec_ref(v_a_1655_);
lean_dec_ref(v___x_1654_);
goto v___jp_1661_;
}
else
{
lean_object* v_val_1675_; lean_object* v___x_1677_; uint8_t v_isShared_1678_; uint8_t v_isSharedCheck_1713_; 
v_val_1675_ = lean_ctor_get(v___x_1674_, 0);
v_isSharedCheck_1713_ = !lean_is_exclusive(v___x_1674_);
if (v_isSharedCheck_1713_ == 0)
{
v___x_1677_ = v___x_1674_;
v_isShared_1678_ = v_isSharedCheck_1713_;
goto v_resetjp_1676_;
}
else
{
lean_inc(v_val_1675_);
lean_dec(v___x_1674_);
v___x_1677_ = lean_box(0);
v_isShared_1678_ = v_isSharedCheck_1713_;
goto v_resetjp_1676_;
}
v_resetjp_1676_:
{
if (lean_obj_tag(v_val_1675_) == 5)
{
lean_object* v_val_1679_; lean_object* v___x_1681_; uint8_t v_isShared_1682_; uint8_t v_isSharedCheck_1712_; 
v_val_1679_ = lean_ctor_get(v_val_1675_, 0);
v_isSharedCheck_1712_ = !lean_is_exclusive(v_val_1675_);
if (v_isSharedCheck_1712_ == 0)
{
v___x_1681_ = v_val_1675_;
v_isShared_1682_ = v_isSharedCheck_1712_;
goto v_resetjp_1680_;
}
else
{
lean_inc(v_val_1679_);
lean_dec(v_val_1675_);
v___x_1681_ = lean_box(0);
v_isShared_1682_ = v_isSharedCheck_1712_;
goto v_resetjp_1680_;
}
v_resetjp_1680_:
{
lean_object* v_toConstantVal_1683_; lean_object* v_numParams_1684_; lean_object* v_numIndices_1685_; lean_object* v_ctors_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; uint8_t v___x_1689_; 
v_toConstantVal_1683_ = lean_ctor_get(v_val_1679_, 0);
v_numParams_1684_ = lean_ctor_get(v_val_1679_, 1);
v_numIndices_1685_ = lean_ctor_get(v_val_1679_, 2);
v_ctors_1686_ = lean_ctor_get(v_val_1679_, 4);
v___x_1687_ = lean_array_get_size(v_x_1657_);
v___x_1688_ = lean_nat_add(v_numIndices_1685_, v_numParams_1684_);
v___x_1689_ = lean_nat_dec_eq(v___x_1687_, v___x_1688_);
lean_dec(v___x_1688_);
if (v___x_1689_ == 0)
{
lean_object* v___x_1690_; lean_object* v___x_1692_; 
lean_dec_ref(v_val_1679_);
lean_del_object(v___x_1677_);
lean_dec_ref_known(v_x_1656_, 2);
lean_dec_ref(v_x_1657_);
lean_dec_ref(v_a_1655_);
lean_dec_ref(v___x_1654_);
v___x_1690_ = lean_box(0);
if (v_isShared_1682_ == 0)
{
lean_ctor_set_tag(v___x_1681_, 0);
lean_ctor_set(v___x_1681_, 0, v___x_1690_);
v___x_1692_ = v___x_1681_;
goto v_reusejp_1691_;
}
else
{
lean_object* v_reuseFailAlloc_1693_; 
v_reuseFailAlloc_1693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1693_, 0, v___x_1690_);
v___x_1692_ = v_reuseFailAlloc_1693_;
goto v_reusejp_1691_;
}
v_reusejp_1691_:
{
return v___x_1692_;
}
}
else
{
lean_object* v_name_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; uint8_t v___x_1697_; 
v_name_1694_ = lean_ctor_get(v_toConstantVal_1683_, 0);
v___x_1695_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0___redArg___closed__0));
lean_inc(v_name_1694_);
v___x_1696_ = l_Lean_Name_str___override(v_name_1694_, v___x_1695_);
v___x_1697_ = l_Lean_Environment_contains(v___x_1654_, v___x_1696_, v___x_1689_);
if (v___x_1697_ == 0)
{
lean_object* v___x_1698_; lean_object* v___x_1700_; 
lean_dec_ref(v_val_1679_);
lean_del_object(v___x_1677_);
lean_dec_ref_known(v_x_1656_, 2);
lean_dec_ref(v_x_1657_);
lean_dec_ref(v_a_1655_);
v___x_1698_ = lean_box(0);
if (v_isShared_1682_ == 0)
{
lean_ctor_set_tag(v___x_1681_, 0);
lean_ctor_set(v___x_1681_, 0, v___x_1698_);
v___x_1700_ = v___x_1681_;
goto v_reusejp_1699_;
}
else
{
lean_object* v_reuseFailAlloc_1701_; 
v_reuseFailAlloc_1701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1701_, 0, v___x_1698_);
v___x_1700_ = v_reuseFailAlloc_1701_;
goto v_reusejp_1699_;
}
v_reusejp_1699_:
{
return v___x_1700_;
}
}
else
{
lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1707_; 
v___x_1702_ = l_List_lengthTR___redArg(v_ctors_1686_);
v___x_1703_ = lean_nat_sub(v___x_1687_, v_numIndices_1685_);
v___x_1704_ = l_Array_extract___redArg(v_x_1657_, v___x_1703_, v___x_1687_);
v___x_1705_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1705_, 0, v_val_1679_);
lean_ctor_set(v___x_1705_, 1, v___x_1702_);
lean_ctor_set(v___x_1705_, 2, v_a_1655_);
lean_ctor_set(v___x_1705_, 3, v_x_1656_);
lean_ctor_set(v___x_1705_, 4, v_x_1657_);
lean_ctor_set(v___x_1705_, 5, v___x_1704_);
if (v_isShared_1678_ == 0)
{
lean_ctor_set(v___x_1677_, 0, v___x_1705_);
v___x_1707_ = v___x_1677_;
goto v_reusejp_1706_;
}
else
{
lean_object* v_reuseFailAlloc_1711_; 
v_reuseFailAlloc_1711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1711_, 0, v___x_1705_);
v___x_1707_ = v_reuseFailAlloc_1711_;
goto v_reusejp_1706_;
}
v_reusejp_1706_:
{
lean_object* v___x_1709_; 
if (v_isShared_1682_ == 0)
{
lean_ctor_set_tag(v___x_1681_, 0);
lean_ctor_set(v___x_1681_, 0, v___x_1707_);
v___x_1709_ = v___x_1681_;
goto v_reusejp_1708_;
}
else
{
lean_object* v_reuseFailAlloc_1710_; 
v_reuseFailAlloc_1710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1710_, 0, v___x_1707_);
v___x_1709_ = v_reuseFailAlloc_1710_;
goto v_reusejp_1708_;
}
v_reusejp_1708_:
{
return v___x_1709_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_1677_);
lean_dec(v_val_1675_);
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
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0___redArg___boxed(lean_object* v___x_1714_, lean_object* v_a_1715_, lean_object* v_x_1716_, lean_object* v_x_1717_, lean_object* v_x_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_){
_start:
{
lean_object* v_res_1721_; 
v_res_1721_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0___redArg(v___x_1714_, v_a_1715_, v_x_1716_, v_x_1717_, v_x_1718_, v___y_1719_);
lean_dec(v___y_1719_);
return v_res_1721_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f(lean_object* v_majorFVarId_1722_, lean_object* v_a_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_){
_start:
{
lean_object* v___x_1728_; lean_object* v_env_1732_; lean_object* v___x_1733_; uint8_t v___x_1734_; uint8_t v___x_1735_; 
v___x_1728_ = lean_st_ref_get(v_a_1726_);
v_env_1732_ = lean_ctor_get(v___x_1728_, 0);
lean_inc_ref_n(v_env_1732_, 2);
lean_dec(v___x_1728_);
v___x_1733_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__5));
v___x_1734_ = 1;
v___x_1735_ = l_Lean_Environment_contains(v_env_1732_, v___x_1733_, v___x_1734_);
if (v___x_1735_ == 0)
{
lean_dec_ref(v_env_1732_);
lean_dec(v_majorFVarId_1722_);
goto v___jp_1729_;
}
else
{
lean_object* v___x_1736_; uint8_t v___x_1737_; 
v___x_1736_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__1));
lean_inc_ref(v_env_1732_);
v___x_1737_ = l_Lean_Environment_contains(v_env_1732_, v___x_1736_, v___x_1735_);
if (v___x_1737_ == 0)
{
lean_dec_ref(v_env_1732_);
lean_dec(v_majorFVarId_1722_);
goto v___jp_1729_;
}
else
{
lean_object* v___x_1738_; 
v___x_1738_ = l_Lean_FVarId_getDecl___redArg(v_majorFVarId_1722_, v_a_1723_, v_a_1725_, v_a_1726_);
if (lean_obj_tag(v___x_1738_) == 0)
{
lean_object* v_a_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; 
v_a_1739_ = lean_ctor_get(v___x_1738_, 0);
lean_inc(v_a_1739_);
lean_dec_ref_known(v___x_1738_, 1);
v___x_1740_ = l_Lean_LocalDecl_type(v_a_1739_);
lean_inc(v_a_1726_);
lean_inc_ref(v_a_1725_);
lean_inc(v_a_1724_);
lean_inc_ref(v_a_1723_);
v___x_1741_ = lean_whnf(v___x_1740_, v_a_1723_, v_a_1724_, v_a_1725_, v_a_1726_);
if (lean_obj_tag(v___x_1741_) == 0)
{
lean_object* v_a_1742_; lean_object* v_dummy_1743_; lean_object* v_nargs_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; 
v_a_1742_ = lean_ctor_get(v___x_1741_, 0);
lean_inc(v_a_1742_);
lean_dec_ref_known(v___x_1741_, 1);
v_dummy_1743_ = lean_obj_once(&l_Lean_Meta_getInductiveUniverseAndParams___closed__0, &l_Lean_Meta_getInductiveUniverseAndParams___closed__0_once, _init_l_Lean_Meta_getInductiveUniverseAndParams___closed__0);
v_nargs_1744_ = l_Lean_Expr_getAppNumArgs(v_a_1742_);
lean_inc(v_nargs_1744_);
v___x_1745_ = lean_mk_array(v_nargs_1744_, v_dummy_1743_);
v___x_1746_ = lean_unsigned_to_nat(1u);
v___x_1747_ = lean_nat_sub(v_nargs_1744_, v___x_1746_);
lean_dec(v_nargs_1744_);
v___x_1748_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0___redArg(v_env_1732_, v_a_1739_, v_a_1742_, v___x_1745_, v___x_1747_, v_a_1726_);
return v___x_1748_;
}
else
{
lean_object* v_a_1749_; lean_object* v___x_1751_; uint8_t v_isShared_1752_; uint8_t v_isSharedCheck_1756_; 
lean_dec(v_a_1739_);
lean_dec_ref(v_env_1732_);
v_a_1749_ = lean_ctor_get(v___x_1741_, 0);
v_isSharedCheck_1756_ = !lean_is_exclusive(v___x_1741_);
if (v_isSharedCheck_1756_ == 0)
{
v___x_1751_ = v___x_1741_;
v_isShared_1752_ = v_isSharedCheck_1756_;
goto v_resetjp_1750_;
}
else
{
lean_inc(v_a_1749_);
lean_dec(v___x_1741_);
v___x_1751_ = lean_box(0);
v_isShared_1752_ = v_isSharedCheck_1756_;
goto v_resetjp_1750_;
}
v_resetjp_1750_:
{
lean_object* v___x_1754_; 
if (v_isShared_1752_ == 0)
{
v___x_1754_ = v___x_1751_;
goto v_reusejp_1753_;
}
else
{
lean_object* v_reuseFailAlloc_1755_; 
v_reuseFailAlloc_1755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1755_, 0, v_a_1749_);
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
else
{
lean_object* v_a_1757_; lean_object* v___x_1759_; uint8_t v_isShared_1760_; uint8_t v_isSharedCheck_1764_; 
lean_dec_ref(v_env_1732_);
v_a_1757_ = lean_ctor_get(v___x_1738_, 0);
v_isSharedCheck_1764_ = !lean_is_exclusive(v___x_1738_);
if (v_isSharedCheck_1764_ == 0)
{
v___x_1759_ = v___x_1738_;
v_isShared_1760_ = v_isSharedCheck_1764_;
goto v_resetjp_1758_;
}
else
{
lean_inc(v_a_1757_);
lean_dec(v___x_1738_);
v___x_1759_ = lean_box(0);
v_isShared_1760_ = v_isSharedCheck_1764_;
goto v_resetjp_1758_;
}
v_resetjp_1758_:
{
lean_object* v___x_1762_; 
if (v_isShared_1760_ == 0)
{
v___x_1762_ = v___x_1759_;
goto v_reusejp_1761_;
}
else
{
lean_object* v_reuseFailAlloc_1763_; 
v_reuseFailAlloc_1763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1763_, 0, v_a_1757_);
v___x_1762_ = v_reuseFailAlloc_1763_;
goto v_reusejp_1761_;
}
v_reusejp_1761_:
{
return v___x_1762_;
}
}
}
}
}
v___jp_1729_:
{
lean_object* v___x_1730_; lean_object* v___x_1731_; 
v___x_1730_ = lean_box(0);
v___x_1731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1731_, 0, v___x_1730_);
return v___x_1731_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f___boxed(lean_object* v_majorFVarId_1765_, lean_object* v_a_1766_, lean_object* v_a_1767_, lean_object* v_a_1768_, lean_object* v_a_1769_, lean_object* v_a_1770_){
_start:
{
lean_object* v_res_1771_; 
v_res_1771_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f(v_majorFVarId_1765_, v_a_1766_, v_a_1767_, v_a_1768_, v_a_1769_);
lean_dec(v_a_1769_);
lean_dec_ref(v_a_1768_);
lean_dec(v_a_1767_);
lean_dec_ref(v_a_1766_);
return v_res_1771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0(lean_object* v___x_1772_, lean_object* v_a_1773_, lean_object* v_x_1774_, lean_object* v_x_1775_, lean_object* v_x_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_){
_start:
{
lean_object* v___x_1782_; 
v___x_1782_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0___redArg(v___x_1772_, v_a_1773_, v_x_1774_, v_x_1775_, v_x_1776_, v___y_1780_);
return v___x_1782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0___boxed(lean_object* v___x_1783_, lean_object* v_a_1784_, lean_object* v_x_1785_, lean_object* v_x_1786_, lean_object* v_x_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_){
_start:
{
lean_object* v_res_1793_; 
v_res_1793_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0(v___x_1783_, v_a_1784_, v_x_1785_, v_x_1786_, v_x_1787_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_);
lean_dec(v___y_1791_);
lean_dec_ref(v___y_1790_);
lean_dec(v___y_1789_);
lean_dec_ref(v___y_1788_);
return v_res_1793_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0___redArg(lean_object* v___x_1794_, lean_object* v_i_1795_, lean_object* v_n_1796_, lean_object* v_i_1797_){
_start:
{
lean_object* v_zero_1798_; uint8_t v_isZero_1799_; 
v_zero_1798_ = lean_unsigned_to_nat(0u);
v_isZero_1799_ = lean_nat_dec_eq(v_i_1797_, v_zero_1798_);
if (v_isZero_1799_ == 1)
{
uint8_t v___x_1800_; 
lean_dec(v_i_1797_);
v___x_1800_ = 0;
return v___x_1800_;
}
else
{
lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; uint8_t v___x_1804_; 
v___x_1801_ = lean_nat_sub(v_n_1796_, v_i_1797_);
v___x_1802_ = lean_array_fget_borrowed(v___x_1794_, v_i_1795_);
v___x_1803_ = lean_array_fget_borrowed(v___x_1794_, v___x_1801_);
lean_dec(v___x_1801_);
v___x_1804_ = lean_expr_eqv(v___x_1802_, v___x_1803_);
if (v___x_1804_ == 0)
{
lean_object* v_one_1805_; lean_object* v_n_1806_; 
v_one_1805_ = lean_unsigned_to_nat(1u);
v_n_1806_ = lean_nat_sub(v_i_1797_, v_one_1805_);
lean_dec(v_i_1797_);
v_i_1797_ = v_n_1806_;
goto _start;
}
else
{
lean_dec(v_i_1797_);
return v___x_1804_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0___redArg___boxed(lean_object* v___x_1808_, lean_object* v_i_1809_, lean_object* v_n_1810_, lean_object* v_i_1811_){
_start:
{
uint8_t v_res_1812_; lean_object* v_r_1813_; 
v_res_1812_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0___redArg(v___x_1808_, v_i_1809_, v_n_1810_, v_i_1811_);
lean_dec(v_n_1810_);
lean_dec(v_i_1809_);
lean_dec_ref(v___x_1808_);
v_r_1813_ = lean_box(v_res_1812_);
return v_r_1813_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1___redArg(lean_object* v___x_1814_, lean_object* v_n_1815_, lean_object* v_i_1816_){
_start:
{
lean_object* v_zero_1817_; uint8_t v_isZero_1818_; 
v_zero_1817_ = lean_unsigned_to_nat(0u);
v_isZero_1818_ = lean_nat_dec_eq(v_i_1816_, v_zero_1817_);
if (v_isZero_1818_ == 1)
{
uint8_t v___x_1819_; 
lean_dec(v_i_1816_);
v___x_1819_ = 0;
return v___x_1819_;
}
else
{
lean_object* v___x_1820_; uint8_t v___x_1821_; 
v___x_1820_ = lean_nat_sub(v_n_1815_, v_i_1816_);
lean_inc(v___x_1820_);
v___x_1821_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0___redArg(v___x_1814_, v___x_1820_, v___x_1820_, v___x_1820_);
lean_dec(v___x_1820_);
if (v___x_1821_ == 0)
{
lean_object* v_one_1822_; lean_object* v_n_1823_; 
v_one_1822_ = lean_unsigned_to_nat(1u);
v_n_1823_ = lean_nat_sub(v_i_1816_, v_one_1822_);
lean_dec(v_i_1816_);
v_i_1816_ = v_n_1823_;
goto _start;
}
else
{
lean_dec(v_i_1816_);
return v___x_1821_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1___redArg___boxed(lean_object* v___x_1825_, lean_object* v_n_1826_, lean_object* v_i_1827_){
_start:
{
uint8_t v_res_1828_; lean_object* v_r_1829_; 
v_res_1828_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1___redArg(v___x_1825_, v_n_1826_, v_i_1827_);
lean_dec(v_n_1826_);
lean_dec_ref(v___x_1825_);
v_r_1829_ = lean_box(v_res_1828_);
return v_r_1829_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5(lean_object* v___x_1830_, lean_object* v_as_1831_, size_t v_i_1832_, size_t v_stop_1833_){
_start:
{
uint8_t v___x_1834_; 
v___x_1834_ = lean_usize_dec_eq(v_i_1832_, v_stop_1833_);
if (v___x_1834_ == 0)
{
uint8_t v___x_1835_; lean_object* v___x_1836_; uint8_t v___x_1837_; 
v___x_1835_ = 1;
v___x_1836_ = lean_array_uget_borrowed(v_as_1831_, v_i_1832_);
v___x_1837_ = l_Lean_Expr_isFVar(v___x_1836_);
if (v___x_1837_ == 0)
{
return v___x_1835_;
}
else
{
lean_object* v___x_1838_; uint8_t v___x_1839_; 
v___x_1838_ = lean_unsigned_to_nat(0u);
v___x_1839_ = lean_nat_dec_eq(v___x_1830_, v___x_1838_);
if (v___x_1839_ == 0)
{
size_t v___x_1840_; size_t v___x_1841_; 
v___x_1840_ = ((size_t)1ULL);
v___x_1841_ = lean_usize_add(v_i_1832_, v___x_1840_);
v_i_1832_ = v___x_1841_;
goto _start;
}
else
{
return v___x_1835_;
}
}
}
else
{
uint8_t v___x_1843_; 
v___x_1843_ = 0;
return v___x_1843_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5___boxed(lean_object* v___x_1844_, lean_object* v_as_1845_, lean_object* v_i_1846_, lean_object* v_stop_1847_){
_start:
{
size_t v_i_boxed_1848_; size_t v_stop_boxed_1849_; uint8_t v_res_1850_; lean_object* v_r_1851_; 
v_i_boxed_1848_ = lean_unbox_usize(v_i_1846_);
lean_dec(v_i_1846_);
v_stop_boxed_1849_ = lean_unbox_usize(v_stop_1847_);
lean_dec(v_stop_1847_);
v_res_1850_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5(v___x_1844_, v_as_1845_, v_i_boxed_1848_, v_stop_boxed_1849_);
lean_dec_ref(v_as_1845_);
lean_dec(v___x_1844_);
v_r_1851_ = lean_box(v_res_1850_);
return v_r_1851_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__2(lean_object* v_fvarId_1852_, uint8_t v___x_1853_, lean_object* v_as_1854_, size_t v_i_1855_, size_t v_stop_1856_){
_start:
{
uint8_t v___x_1857_; 
v___x_1857_ = lean_usize_dec_eq(v_i_1855_, v_stop_1856_);
if (v___x_1857_ == 0)
{
uint8_t v___x_1858_; uint8_t v___y_1860_; lean_object* v___x_1864_; lean_object* v___x_1865_; uint8_t v___x_1866_; 
v___x_1858_ = 1;
v___x_1864_ = lean_array_uget_borrowed(v_as_1854_, v_i_1855_);
v___x_1865_ = l_Lean_Expr_fvarId_x21(v___x_1864_);
v___x_1866_ = l_Lean_instBEqFVarId_beq(v___x_1865_, v_fvarId_1852_);
lean_dec(v___x_1865_);
if (v___x_1866_ == 0)
{
v___y_1860_ = v___x_1853_;
goto v___jp_1859_;
}
else
{
if (v___x_1853_ == 0)
{
v___y_1860_ = v___x_1866_;
goto v___jp_1859_;
}
else
{
return v___x_1858_;
}
}
v___jp_1859_:
{
if (v___y_1860_ == 0)
{
size_t v___x_1861_; size_t v___x_1862_; 
v___x_1861_ = ((size_t)1ULL);
v___x_1862_ = lean_usize_add(v_i_1855_, v___x_1861_);
v_i_1855_ = v___x_1862_;
goto _start;
}
else
{
return v___x_1858_;
}
}
}
else
{
uint8_t v___x_1867_; 
v___x_1867_ = 0;
return v___x_1867_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__2___boxed(lean_object* v_fvarId_1868_, lean_object* v___x_1869_, lean_object* v_as_1870_, lean_object* v_i_1871_, lean_object* v_stop_1872_){
_start:
{
uint8_t v___x_7575__boxed_1873_; size_t v_i_boxed_1874_; size_t v_stop_boxed_1875_; uint8_t v_res_1876_; lean_object* v_r_1877_; 
v___x_7575__boxed_1873_ = lean_unbox(v___x_1869_);
v_i_boxed_1874_ = lean_unbox_usize(v_i_1871_);
lean_dec(v_i_1871_);
v_stop_boxed_1875_ = lean_unbox_usize(v_stop_1872_);
lean_dec(v_stop_1872_);
v_res_1876_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__2(v_fvarId_1868_, v___x_7575__boxed_1873_, v_as_1870_, v_i_boxed_1874_, v_stop_boxed_1875_);
lean_dec_ref(v_as_1870_);
lean_dec(v_fvarId_1868_);
v_r_1877_ = lean_box(v_res_1876_);
return v_r_1877_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___lam__1(lean_object* v___x_1878_, lean_object* v___x_1879_, uint8_t v___x_1880_, lean_object* v___x_1881_, lean_object* v_fvarId_1882_){
_start:
{
uint8_t v___x_1883_; lean_object* v___y_1885_; 
v___x_1883_ = lean_nat_dec_lt(v___x_1878_, v___x_1879_);
if (v___x_1883_ == 0)
{
uint8_t v___x_1890_; 
lean_dec(v___x_1879_);
v___x_1890_ = 1;
return v___x_1890_;
}
else
{
lean_object* v___x_1891_; uint8_t v___x_1892_; 
v___x_1891_ = lean_array_get_size(v___x_1881_);
v___x_1892_ = lean_nat_dec_le(v___x_1879_, v___x_1891_);
if (v___x_1892_ == 0)
{
lean_dec(v___x_1879_);
v___y_1885_ = v___x_1891_;
goto v___jp_1884_;
}
else
{
v___y_1885_ = v___x_1879_;
goto v___jp_1884_;
}
}
v___jp_1884_:
{
uint8_t v___x_1886_; 
v___x_1886_ = lean_nat_dec_lt(v___x_1878_, v___y_1885_);
if (v___x_1886_ == 0)
{
lean_dec(v___y_1885_);
return v___x_1883_;
}
else
{
size_t v___x_1887_; size_t v___x_1888_; uint8_t v___x_1889_; 
v___x_1887_ = ((size_t)0ULL);
v___x_1888_ = lean_usize_of_nat(v___y_1885_);
lean_dec(v___y_1885_);
v___x_1889_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__2(v_fvarId_1882_, v___x_1880_, v___x_1881_, v___x_1887_, v___x_1888_);
if (v___x_1889_ == 0)
{
return v___x_1886_;
}
else
{
return v___x_1880_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___lam__1___boxed(lean_object* v___x_1893_, lean_object* v___x_1894_, lean_object* v___x_1895_, lean_object* v___x_1896_, lean_object* v_fvarId_1897_){
_start:
{
uint8_t v___x_7602__boxed_1898_; uint8_t v_res_1899_; lean_object* v_r_1900_; 
v___x_7602__boxed_1898_ = lean_unbox(v___x_1895_);
v_res_1899_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___lam__1(v___x_1893_, v___x_1894_, v___x_7602__boxed_1898_, v___x_1896_, v_fvarId_1897_);
lean_dec(v_fvarId_1897_);
lean_dec_ref(v___x_1896_);
lean_dec(v___x_1893_);
v_r_1900_ = lean_box(v_res_1899_);
return v_r_1900_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__3(lean_object* v___x_1901_, lean_object* v_as_1902_, size_t v_i_1903_, size_t v_stop_1904_){
_start:
{
uint8_t v___x_1905_; 
v___x_1905_ = lean_usize_dec_eq(v_i_1903_, v_stop_1904_);
if (v___x_1905_ == 0)
{
lean_object* v___x_1906_; lean_object* v___x_1907_; uint8_t v___x_1908_; 
v___x_1906_ = lean_array_uget_borrowed(v_as_1902_, v_i_1903_);
v___x_1907_ = l_Lean_Expr_fvarId_x21(v___x_1906_);
v___x_1908_ = l_Lean_instBEqFVarId_beq(v___x_1901_, v___x_1907_);
lean_dec(v___x_1907_);
if (v___x_1908_ == 0)
{
size_t v___x_1909_; size_t v___x_1910_; 
v___x_1909_ = ((size_t)1ULL);
v___x_1910_ = lean_usize_add(v_i_1903_, v___x_1909_);
v_i_1903_ = v___x_1910_;
goto _start;
}
else
{
return v___x_1908_;
}
}
else
{
uint8_t v___x_1912_; 
v___x_1912_ = 0;
return v___x_1912_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__3___boxed(lean_object* v___x_1913_, lean_object* v_as_1914_, lean_object* v_i_1915_, lean_object* v_stop_1916_){
_start:
{
size_t v_i_boxed_1917_; size_t v_stop_boxed_1918_; uint8_t v_res_1919_; lean_object* v_r_1920_; 
v_i_boxed_1917_ = lean_unbox_usize(v_i_1915_);
lean_dec(v_i_1915_);
v_stop_boxed_1918_ = lean_unbox_usize(v_stop_1916_);
lean_dec(v_stop_1916_);
v_res_1919_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__3(v___x_1913_, v_as_1914_, v_i_boxed_1917_, v_stop_boxed_1918_);
lean_dec_ref(v_as_1914_);
lean_dec(v___x_1913_);
v_r_1920_ = lean_box(v_res_1919_);
return v_r_1920_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___lam__0(uint8_t v___x_1921_, lean_object* v_x_1922_){
_start:
{
return v___x_1921_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___lam__0___boxed(lean_object* v___x_1923_, lean_object* v_x_1924_){
_start:
{
uint8_t v___x_7651__boxed_1925_; uint8_t v_res_1926_; lean_object* v_r_1927_; 
v___x_7651__boxed_1925_ = lean_unbox(v___x_1923_);
v_res_1926_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___lam__0(v___x_7651__boxed_1925_, v_x_1924_);
lean_dec(v_x_1924_);
v_r_1927_ = lean_box(v_res_1926_);
return v_r_1927_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; 
v___x_1928_ = lean_box(0);
v___x_1929_ = lean_unsigned_to_nat(16u);
v___x_1930_ = lean_mk_array(v___x_1929_, v___x_1928_);
return v___x_1930_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; 
v___x_1931_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__0);
v___x_1932_ = lean_unsigned_to_nat(0u);
v___x_1933_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1933_, 0, v___x_1932_);
lean_ctor_set(v___x_1933_, 1, v___x_1931_);
return v___x_1933_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg(uint8_t v___x_1934_, lean_object* v___x_1935_, lean_object* v___x_1936_, lean_object* v_ctx_1937_, lean_object* v_as_1938_, size_t v_i_1939_, size_t v_stop_1940_, lean_object* v___y_1941_){
_start:
{
uint8_t v___x_1943_; 
v___x_1943_ = lean_usize_dec_eq(v_i_1939_, v_stop_1940_);
if (v___x_1943_ == 0)
{
uint8_t v___x_1944_; uint8_t v_a_1946_; uint8_t v_a_1953_; uint8_t v_fst_1957_; lean_object* v_mctx_1958_; lean_object* v___y_1974_; uint8_t v_fst_1980_; lean_object* v_snd_1981_; lean_object* v___y_1998_; uint8_t v_fst_2003_; lean_object* v_mctx_2004_; lean_object* v___y_2020_; lean_object* v___x_2025_; 
v___x_1944_ = 1;
v___x_2025_ = lean_array_uget_borrowed(v_as_1938_, v_i_1939_);
if (lean_obj_tag(v___x_2025_) == 0)
{
v_a_1946_ = v___x_1934_;
goto v___jp_1945_;
}
else
{
lean_object* v_val_2026_; lean_object* v_majorDecl_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; uint8_t v___x_2030_; 
v_val_2026_ = lean_ctor_get(v___x_2025_, 0);
v_majorDecl_2027_ = lean_ctor_get(v_ctx_1937_, 2);
v___x_2028_ = l_Lean_LocalDecl_fvarId(v_val_2026_);
v___x_2029_ = l_Lean_LocalDecl_fvarId(v_majorDecl_2027_);
v___x_2030_ = l_Lean_instBEqFVarId_beq(v___x_2028_, v___x_2029_);
lean_dec(v___x_2029_);
if (v___x_2030_ == 0)
{
lean_object* v___x_2031_; lean_object* v___f_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___f_2035_; lean_object* v___y_2037_; uint8_t v_fst_2038_; lean_object* v_snd_2039_; lean_object* v___y_2045_; lean_object* v___y_2046_; lean_object* v___y_2081_; uint8_t v___x_2086_; 
v___x_2031_ = lean_box(v___x_1934_);
v___f_2032_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2032_, 0, v___x_2031_);
v___x_2033_ = lean_unsigned_to_nat(0u);
v___x_2034_ = lean_box(v___x_1934_);
lean_inc_ref(v___x_1935_);
lean_inc(v___x_1936_);
v___f_2035_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_2035_, 0, v___x_2033_);
lean_closure_set(v___f_2035_, 1, v___x_1936_);
lean_closure_set(v___f_2035_, 2, v___x_2034_);
lean_closure_set(v___f_2035_, 3, v___x_1935_);
v___x_2086_ = lean_nat_dec_lt(v___x_2033_, v___x_1936_);
if (v___x_2086_ == 0)
{
lean_dec(v___x_2028_);
goto v___jp_2050_;
}
else
{
lean_object* v___x_2087_; uint8_t v___x_2088_; 
v___x_2087_ = lean_array_get_size(v___x_1935_);
v___x_2088_ = lean_nat_dec_le(v___x_1936_, v___x_2087_);
if (v___x_2088_ == 0)
{
v___y_2081_ = v___x_2087_;
goto v___jp_2080_;
}
else
{
lean_inc(v___x_1936_);
v___y_2081_ = v___x_1936_;
goto v___jp_2080_;
}
}
v___jp_2036_:
{
if (v_fst_2038_ == 0)
{
uint8_t v___x_2040_; 
v___x_2040_ = l_Lean_Expr_hasFVar(v___y_2037_);
if (v___x_2040_ == 0)
{
uint8_t v___x_2041_; 
v___x_2041_ = l_Lean_Expr_hasMVar(v___y_2037_);
if (v___x_2041_ == 0)
{
lean_dec_ref(v___y_2037_);
lean_dec_ref(v___f_2035_);
lean_dec_ref(v___f_2032_);
v_fst_1980_ = v___x_2041_;
v_snd_1981_ = v_snd_2039_;
goto v___jp_1979_;
}
else
{
lean_object* v___x_2042_; 
v___x_2042_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_2035_, v___f_2032_, v___y_2037_, v_snd_2039_);
v___y_1998_ = v___x_2042_;
goto v___jp_1997_;
}
}
else
{
lean_object* v___x_2043_; 
v___x_2043_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_2035_, v___f_2032_, v___y_2037_, v_snd_2039_);
v___y_1998_ = v___x_2043_;
goto v___jp_1997_;
}
}
else
{
lean_dec_ref(v___y_2037_);
lean_dec_ref(v___f_2035_);
lean_dec_ref(v___f_2032_);
v_fst_1980_ = v_fst_2038_;
v_snd_1981_ = v_snd_2039_;
goto v___jp_1979_;
}
}
v___jp_2044_:
{
lean_object* v_fst_2047_; lean_object* v_snd_2048_; uint8_t v___x_2049_; 
v_fst_2047_ = lean_ctor_get(v___y_2046_, 0);
lean_inc(v_fst_2047_);
v_snd_2048_ = lean_ctor_get(v___y_2046_, 1);
lean_inc(v_snd_2048_);
lean_dec_ref(v___y_2046_);
v___x_2049_ = lean_unbox(v_fst_2047_);
lean_dec(v_fst_2047_);
v___y_2037_ = v___y_2045_;
v_fst_2038_ = v___x_2049_;
v_snd_2039_ = v_snd_2048_;
goto v___jp_2036_;
}
v___jp_2050_:
{
if (lean_obj_tag(v_val_2026_) == 0)
{
lean_object* v_type_2051_; lean_object* v___x_2052_; lean_object* v_mctx_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; uint8_t v___x_2056_; 
v_type_2051_ = lean_ctor_get(v_val_2026_, 3);
v___x_2052_ = lean_st_ref_get(v___y_1941_);
v_mctx_2053_ = lean_ctor_get(v___x_2052_, 0);
lean_inc_ref_n(v_mctx_2053_, 2);
lean_dec(v___x_2052_);
v___x_2054_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1);
v___x_2055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2055_, 0, v___x_2054_);
lean_ctor_set(v___x_2055_, 1, v_mctx_2053_);
v___x_2056_ = l_Lean_Expr_hasFVar(v_type_2051_);
if (v___x_2056_ == 0)
{
uint8_t v___x_2057_; 
v___x_2057_ = l_Lean_Expr_hasMVar(v_type_2051_);
if (v___x_2057_ == 0)
{
lean_dec_ref_known(v___x_2055_, 2);
lean_dec_ref(v___f_2035_);
lean_dec_ref(v___f_2032_);
v_fst_2003_ = v___x_2057_;
v_mctx_2004_ = v_mctx_2053_;
goto v___jp_2002_;
}
else
{
lean_object* v___x_2058_; 
lean_dec_ref(v_mctx_2053_);
lean_inc_ref(v_type_2051_);
v___x_2058_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_2035_, v___f_2032_, v_type_2051_, v___x_2055_);
v___y_2020_ = v___x_2058_;
goto v___jp_2019_;
}
}
else
{
lean_object* v___x_2059_; 
lean_dec_ref(v_mctx_2053_);
lean_inc_ref(v_type_2051_);
v___x_2059_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_2035_, v___f_2032_, v_type_2051_, v___x_2055_);
v___y_2020_ = v___x_2059_;
goto v___jp_2019_;
}
}
else
{
uint8_t v_nondep_2060_; 
v_nondep_2060_ = lean_ctor_get_uint8(v_val_2026_, sizeof(void*)*5);
if (v_nondep_2060_ == 0)
{
lean_object* v_type_2061_; lean_object* v_value_2062_; lean_object* v___x_2063_; lean_object* v_mctx_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; uint8_t v___x_2067_; 
v_type_2061_ = lean_ctor_get(v_val_2026_, 3);
v_value_2062_ = lean_ctor_get(v_val_2026_, 4);
v___x_2063_ = lean_st_ref_get(v___y_1941_);
v_mctx_2064_ = lean_ctor_get(v___x_2063_, 0);
lean_inc_ref(v_mctx_2064_);
lean_dec(v___x_2063_);
v___x_2065_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1);
v___x_2066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2066_, 0, v___x_2065_);
lean_ctor_set(v___x_2066_, 1, v_mctx_2064_);
v___x_2067_ = l_Lean_Expr_hasFVar(v_type_2061_);
if (v___x_2067_ == 0)
{
uint8_t v___x_2068_; 
v___x_2068_ = l_Lean_Expr_hasMVar(v_type_2061_);
if (v___x_2068_ == 0)
{
lean_inc_ref(v_value_2062_);
v___y_2037_ = v_value_2062_;
v_fst_2038_ = v___x_2068_;
v_snd_2039_ = v___x_2066_;
goto v___jp_2036_;
}
else
{
lean_object* v___x_2069_; 
lean_inc_ref(v_type_2061_);
lean_inc_ref(v___f_2032_);
lean_inc_ref(v___f_2035_);
v___x_2069_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_2035_, v___f_2032_, v_type_2061_, v___x_2066_);
lean_inc_ref(v_value_2062_);
v___y_2045_ = v_value_2062_;
v___y_2046_ = v___x_2069_;
goto v___jp_2044_;
}
}
else
{
lean_object* v___x_2070_; 
lean_inc_ref(v_type_2061_);
lean_inc_ref(v___f_2032_);
lean_inc_ref(v___f_2035_);
v___x_2070_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_2035_, v___f_2032_, v_type_2061_, v___x_2066_);
lean_inc_ref(v_value_2062_);
v___y_2045_ = v_value_2062_;
v___y_2046_ = v___x_2070_;
goto v___jp_2044_;
}
}
else
{
lean_object* v_type_2071_; lean_object* v___x_2072_; lean_object* v_mctx_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; uint8_t v___x_2076_; 
v_type_2071_ = lean_ctor_get(v_val_2026_, 3);
v___x_2072_ = lean_st_ref_get(v___y_1941_);
v_mctx_2073_ = lean_ctor_get(v___x_2072_, 0);
lean_inc_ref_n(v_mctx_2073_, 2);
lean_dec(v___x_2072_);
v___x_2074_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1);
v___x_2075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2075_, 0, v___x_2074_);
lean_ctor_set(v___x_2075_, 1, v_mctx_2073_);
v___x_2076_ = l_Lean_Expr_hasFVar(v_type_2071_);
if (v___x_2076_ == 0)
{
uint8_t v___x_2077_; 
v___x_2077_ = l_Lean_Expr_hasMVar(v_type_2071_);
if (v___x_2077_ == 0)
{
lean_dec_ref_known(v___x_2075_, 2);
lean_dec_ref(v___f_2035_);
lean_dec_ref(v___f_2032_);
v_fst_1957_ = v___x_2077_;
v_mctx_1958_ = v_mctx_2073_;
goto v___jp_1956_;
}
else
{
lean_object* v___x_2078_; 
lean_dec_ref(v_mctx_2073_);
lean_inc_ref(v_type_2071_);
v___x_2078_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_2035_, v___f_2032_, v_type_2071_, v___x_2075_);
v___y_1974_ = v___x_2078_;
goto v___jp_1973_;
}
}
else
{
lean_object* v___x_2079_; 
lean_dec_ref(v_mctx_2073_);
lean_inc_ref(v_type_2071_);
v___x_2079_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_2035_, v___f_2032_, v_type_2071_, v___x_2075_);
v___y_1974_ = v___x_2079_;
goto v___jp_1973_;
}
}
}
}
v___jp_2080_:
{
uint8_t v___x_2082_; 
v___x_2082_ = lean_nat_dec_lt(v___x_2033_, v___y_2081_);
if (v___x_2082_ == 0)
{
lean_dec(v___y_2081_);
lean_dec(v___x_2028_);
goto v___jp_2050_;
}
else
{
size_t v___x_2083_; size_t v___x_2084_; uint8_t v___x_2085_; 
v___x_2083_ = ((size_t)0ULL);
v___x_2084_ = lean_usize_of_nat(v___y_2081_);
lean_dec(v___y_2081_);
v___x_2085_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__3(v___x_2028_, v___x_1935_, v___x_2083_, v___x_2084_);
lean_dec(v___x_2028_);
if (v___x_2085_ == 0)
{
goto v___jp_2050_;
}
else
{
lean_dec_ref(v___f_2035_);
lean_dec_ref(v___f_2032_);
v_a_1953_ = v___x_2085_;
goto v___jp_1952_;
}
}
}
}
else
{
lean_dec(v___x_2028_);
v_a_1953_ = v___x_2030_;
goto v___jp_1952_;
}
}
v___jp_1945_:
{
if (v_a_1946_ == 0)
{
size_t v___x_1947_; size_t v___x_1948_; 
v___x_1947_ = ((size_t)1ULL);
v___x_1948_ = lean_usize_add(v_i_1939_, v___x_1947_);
v_i_1939_ = v___x_1948_;
goto _start;
}
else
{
lean_object* v___x_1950_; lean_object* v___x_1951_; 
lean_dec(v___x_1936_);
lean_dec_ref(v___x_1935_);
v___x_1950_ = lean_box(v___x_1944_);
v___x_1951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1951_, 0, v___x_1950_);
return v___x_1951_;
}
}
v___jp_1952_:
{
if (v_a_1953_ == 0)
{
lean_object* v___x_1954_; lean_object* v___x_1955_; 
lean_dec(v___x_1936_);
lean_dec_ref(v___x_1935_);
v___x_1954_ = lean_box(v___x_1944_);
v___x_1955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1955_, 0, v___x_1954_);
return v___x_1955_;
}
else
{
v_a_1946_ = v___x_1934_;
goto v___jp_1945_;
}
}
v___jp_1956_:
{
lean_object* v___x_1959_; lean_object* v_cache_1960_; lean_object* v_zetaDeltaFVarIds_1961_; lean_object* v_postponed_1962_; lean_object* v_diag_1963_; lean_object* v___x_1965_; uint8_t v_isShared_1966_; uint8_t v_isSharedCheck_1971_; 
v___x_1959_ = lean_st_ref_take(v___y_1941_);
v_cache_1960_ = lean_ctor_get(v___x_1959_, 1);
v_zetaDeltaFVarIds_1961_ = lean_ctor_get(v___x_1959_, 2);
v_postponed_1962_ = lean_ctor_get(v___x_1959_, 3);
v_diag_1963_ = lean_ctor_get(v___x_1959_, 4);
v_isSharedCheck_1971_ = !lean_is_exclusive(v___x_1959_);
if (v_isSharedCheck_1971_ == 0)
{
lean_object* v_unused_1972_; 
v_unused_1972_ = lean_ctor_get(v___x_1959_, 0);
lean_dec(v_unused_1972_);
v___x_1965_ = v___x_1959_;
v_isShared_1966_ = v_isSharedCheck_1971_;
goto v_resetjp_1964_;
}
else
{
lean_inc(v_diag_1963_);
lean_inc(v_postponed_1962_);
lean_inc(v_zetaDeltaFVarIds_1961_);
lean_inc(v_cache_1960_);
lean_dec(v___x_1959_);
v___x_1965_ = lean_box(0);
v_isShared_1966_ = v_isSharedCheck_1971_;
goto v_resetjp_1964_;
}
v_resetjp_1964_:
{
lean_object* v___x_1968_; 
if (v_isShared_1966_ == 0)
{
lean_ctor_set(v___x_1965_, 0, v_mctx_1958_);
v___x_1968_ = v___x_1965_;
goto v_reusejp_1967_;
}
else
{
lean_object* v_reuseFailAlloc_1970_; 
v_reuseFailAlloc_1970_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1970_, 0, v_mctx_1958_);
lean_ctor_set(v_reuseFailAlloc_1970_, 1, v_cache_1960_);
lean_ctor_set(v_reuseFailAlloc_1970_, 2, v_zetaDeltaFVarIds_1961_);
lean_ctor_set(v_reuseFailAlloc_1970_, 3, v_postponed_1962_);
lean_ctor_set(v_reuseFailAlloc_1970_, 4, v_diag_1963_);
v___x_1968_ = v_reuseFailAlloc_1970_;
goto v_reusejp_1967_;
}
v_reusejp_1967_:
{
lean_object* v___x_1969_; 
v___x_1969_ = lean_st_ref_put(v___y_1941_, v___x_1968_);
v_a_1953_ = v_fst_1957_;
goto v___jp_1952_;
}
}
}
v___jp_1973_:
{
lean_object* v_snd_1975_; lean_object* v_fst_1976_; lean_object* v_mctx_1977_; uint8_t v___x_1978_; 
v_snd_1975_ = lean_ctor_get(v___y_1974_, 1);
lean_inc(v_snd_1975_);
v_fst_1976_ = lean_ctor_get(v___y_1974_, 0);
lean_inc(v_fst_1976_);
lean_dec_ref(v___y_1974_);
v_mctx_1977_ = lean_ctor_get(v_snd_1975_, 1);
lean_inc_ref(v_mctx_1977_);
lean_dec(v_snd_1975_);
v___x_1978_ = lean_unbox(v_fst_1976_);
lean_dec(v_fst_1976_);
v_fst_1957_ = v___x_1978_;
v_mctx_1958_ = v_mctx_1977_;
goto v___jp_1956_;
}
v___jp_1979_:
{
lean_object* v_mctx_1982_; lean_object* v___x_1983_; lean_object* v_cache_1984_; lean_object* v_zetaDeltaFVarIds_1985_; lean_object* v_postponed_1986_; lean_object* v_diag_1987_; lean_object* v___x_1989_; uint8_t v_isShared_1990_; uint8_t v_isSharedCheck_1995_; 
v_mctx_1982_ = lean_ctor_get(v_snd_1981_, 1);
lean_inc_ref(v_mctx_1982_);
lean_dec_ref(v_snd_1981_);
v___x_1983_ = lean_st_ref_take(v___y_1941_);
v_cache_1984_ = lean_ctor_get(v___x_1983_, 1);
v_zetaDeltaFVarIds_1985_ = lean_ctor_get(v___x_1983_, 2);
v_postponed_1986_ = lean_ctor_get(v___x_1983_, 3);
v_diag_1987_ = lean_ctor_get(v___x_1983_, 4);
v_isSharedCheck_1995_ = !lean_is_exclusive(v___x_1983_);
if (v_isSharedCheck_1995_ == 0)
{
lean_object* v_unused_1996_; 
v_unused_1996_ = lean_ctor_get(v___x_1983_, 0);
lean_dec(v_unused_1996_);
v___x_1989_ = v___x_1983_;
v_isShared_1990_ = v_isSharedCheck_1995_;
goto v_resetjp_1988_;
}
else
{
lean_inc(v_diag_1987_);
lean_inc(v_postponed_1986_);
lean_inc(v_zetaDeltaFVarIds_1985_);
lean_inc(v_cache_1984_);
lean_dec(v___x_1983_);
v___x_1989_ = lean_box(0);
v_isShared_1990_ = v_isSharedCheck_1995_;
goto v_resetjp_1988_;
}
v_resetjp_1988_:
{
lean_object* v___x_1992_; 
if (v_isShared_1990_ == 0)
{
lean_ctor_set(v___x_1989_, 0, v_mctx_1982_);
v___x_1992_ = v___x_1989_;
goto v_reusejp_1991_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v_mctx_1982_);
lean_ctor_set(v_reuseFailAlloc_1994_, 1, v_cache_1984_);
lean_ctor_set(v_reuseFailAlloc_1994_, 2, v_zetaDeltaFVarIds_1985_);
lean_ctor_set(v_reuseFailAlloc_1994_, 3, v_postponed_1986_);
lean_ctor_set(v_reuseFailAlloc_1994_, 4, v_diag_1987_);
v___x_1992_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1991_;
}
v_reusejp_1991_:
{
lean_object* v___x_1993_; 
v___x_1993_ = lean_st_ref_put(v___y_1941_, v___x_1992_);
v_a_1953_ = v_fst_1980_;
goto v___jp_1952_;
}
}
}
v___jp_1997_:
{
lean_object* v_fst_1999_; lean_object* v_snd_2000_; uint8_t v___x_2001_; 
v_fst_1999_ = lean_ctor_get(v___y_1998_, 0);
lean_inc(v_fst_1999_);
v_snd_2000_ = lean_ctor_get(v___y_1998_, 1);
lean_inc(v_snd_2000_);
lean_dec_ref(v___y_1998_);
v___x_2001_ = lean_unbox(v_fst_1999_);
lean_dec(v_fst_1999_);
v_fst_1980_ = v___x_2001_;
v_snd_1981_ = v_snd_2000_;
goto v___jp_1979_;
}
v___jp_2002_:
{
lean_object* v___x_2005_; lean_object* v_cache_2006_; lean_object* v_zetaDeltaFVarIds_2007_; lean_object* v_postponed_2008_; lean_object* v_diag_2009_; lean_object* v___x_2011_; uint8_t v_isShared_2012_; uint8_t v_isSharedCheck_2017_; 
v___x_2005_ = lean_st_ref_take(v___y_1941_);
v_cache_2006_ = lean_ctor_get(v___x_2005_, 1);
v_zetaDeltaFVarIds_2007_ = lean_ctor_get(v___x_2005_, 2);
v_postponed_2008_ = lean_ctor_get(v___x_2005_, 3);
v_diag_2009_ = lean_ctor_get(v___x_2005_, 4);
v_isSharedCheck_2017_ = !lean_is_exclusive(v___x_2005_);
if (v_isSharedCheck_2017_ == 0)
{
lean_object* v_unused_2018_; 
v_unused_2018_ = lean_ctor_get(v___x_2005_, 0);
lean_dec(v_unused_2018_);
v___x_2011_ = v___x_2005_;
v_isShared_2012_ = v_isSharedCheck_2017_;
goto v_resetjp_2010_;
}
else
{
lean_inc(v_diag_2009_);
lean_inc(v_postponed_2008_);
lean_inc(v_zetaDeltaFVarIds_2007_);
lean_inc(v_cache_2006_);
lean_dec(v___x_2005_);
v___x_2011_ = lean_box(0);
v_isShared_2012_ = v_isSharedCheck_2017_;
goto v_resetjp_2010_;
}
v_resetjp_2010_:
{
lean_object* v___x_2014_; 
if (v_isShared_2012_ == 0)
{
lean_ctor_set(v___x_2011_, 0, v_mctx_2004_);
v___x_2014_ = v___x_2011_;
goto v_reusejp_2013_;
}
else
{
lean_object* v_reuseFailAlloc_2016_; 
v_reuseFailAlloc_2016_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2016_, 0, v_mctx_2004_);
lean_ctor_set(v_reuseFailAlloc_2016_, 1, v_cache_2006_);
lean_ctor_set(v_reuseFailAlloc_2016_, 2, v_zetaDeltaFVarIds_2007_);
lean_ctor_set(v_reuseFailAlloc_2016_, 3, v_postponed_2008_);
lean_ctor_set(v_reuseFailAlloc_2016_, 4, v_diag_2009_);
v___x_2014_ = v_reuseFailAlloc_2016_;
goto v_reusejp_2013_;
}
v_reusejp_2013_:
{
lean_object* v___x_2015_; 
v___x_2015_ = lean_st_ref_put(v___y_1941_, v___x_2014_);
v_a_1953_ = v_fst_2003_;
goto v___jp_1952_;
}
}
}
v___jp_2019_:
{
lean_object* v_snd_2021_; lean_object* v_fst_2022_; lean_object* v_mctx_2023_; uint8_t v___x_2024_; 
v_snd_2021_ = lean_ctor_get(v___y_2020_, 1);
lean_inc(v_snd_2021_);
v_fst_2022_ = lean_ctor_get(v___y_2020_, 0);
lean_inc(v_fst_2022_);
lean_dec_ref(v___y_2020_);
v_mctx_2023_ = lean_ctor_get(v_snd_2021_, 1);
lean_inc_ref(v_mctx_2023_);
lean_dec(v_snd_2021_);
v___x_2024_ = lean_unbox(v_fst_2022_);
lean_dec(v_fst_2022_);
v_fst_2003_ = v___x_2024_;
v_mctx_2004_ = v_mctx_2023_;
goto v___jp_2002_;
}
}
else
{
uint8_t v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; 
lean_dec(v___x_1936_);
lean_dec_ref(v___x_1935_);
v___x_2089_ = 0;
v___x_2090_ = lean_box(v___x_2089_);
v___x_2091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2091_, 0, v___x_2090_);
return v___x_2091_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___boxed(lean_object* v___x_2092_, lean_object* v___x_2093_, lean_object* v___x_2094_, lean_object* v_ctx_2095_, lean_object* v_as_2096_, lean_object* v_i_2097_, lean_object* v_stop_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_){
_start:
{
uint8_t v___x_7681__boxed_2101_; size_t v_i_boxed_2102_; size_t v_stop_boxed_2103_; lean_object* v_res_2104_; 
v___x_7681__boxed_2101_ = lean_unbox(v___x_2092_);
v_i_boxed_2102_ = lean_unbox_usize(v_i_2097_);
lean_dec(v_i_2097_);
v_stop_boxed_2103_ = lean_unbox_usize(v_stop_2098_);
lean_dec(v_stop_2098_);
v_res_2104_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg(v___x_7681__boxed_2101_, v___x_2093_, v___x_2094_, v_ctx_2095_, v_as_2096_, v_i_boxed_2102_, v_stop_boxed_2103_, v___y_2099_);
lean_dec(v___y_2099_);
lean_dec_ref(v_as_2096_);
lean_dec_ref(v_ctx_2095_);
return v_res_2104_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4(uint8_t v___x_2105_, lean_object* v___x_2106_, lean_object* v___x_2107_, lean_object* v_ctx_2108_, lean_object* v_x_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_){
_start:
{
if (lean_obj_tag(v_x_2109_) == 0)
{
lean_object* v_cs_2115_; lean_object* v___x_2117_; uint8_t v_isShared_2118_; uint8_t v_isSharedCheck_2133_; 
v_cs_2115_ = lean_ctor_get(v_x_2109_, 0);
v_isSharedCheck_2133_ = !lean_is_exclusive(v_x_2109_);
if (v_isSharedCheck_2133_ == 0)
{
v___x_2117_ = v_x_2109_;
v_isShared_2118_ = v_isSharedCheck_2133_;
goto v_resetjp_2116_;
}
else
{
lean_inc(v_cs_2115_);
lean_dec(v_x_2109_);
v___x_2117_ = lean_box(0);
v_isShared_2118_ = v_isSharedCheck_2133_;
goto v_resetjp_2116_;
}
v_resetjp_2116_:
{
lean_object* v___x_2119_; lean_object* v___x_2120_; uint8_t v___x_2121_; 
v___x_2119_ = lean_unsigned_to_nat(0u);
v___x_2120_ = lean_array_get_size(v_cs_2115_);
v___x_2121_ = lean_nat_dec_lt(v___x_2119_, v___x_2120_);
if (v___x_2121_ == 0)
{
lean_object* v___x_2122_; lean_object* v___x_2124_; 
lean_dec_ref(v_cs_2115_);
lean_dec(v___x_2107_);
lean_dec_ref(v___x_2106_);
v___x_2122_ = lean_box(v___x_2121_);
if (v_isShared_2118_ == 0)
{
lean_ctor_set(v___x_2117_, 0, v___x_2122_);
v___x_2124_ = v___x_2117_;
goto v_reusejp_2123_;
}
else
{
lean_object* v_reuseFailAlloc_2125_; 
v_reuseFailAlloc_2125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2125_, 0, v___x_2122_);
v___x_2124_ = v_reuseFailAlloc_2125_;
goto v_reusejp_2123_;
}
v_reusejp_2123_:
{
return v___x_2124_;
}
}
else
{
if (v___x_2121_ == 0)
{
lean_object* v___x_2126_; lean_object* v___x_2128_; 
lean_dec_ref(v_cs_2115_);
lean_dec(v___x_2107_);
lean_dec_ref(v___x_2106_);
v___x_2126_ = lean_box(v___x_2121_);
if (v_isShared_2118_ == 0)
{
lean_ctor_set(v___x_2117_, 0, v___x_2126_);
v___x_2128_ = v___x_2117_;
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
size_t v___x_2130_; size_t v___x_2131_; lean_object* v___x_2132_; 
lean_del_object(v___x_2117_);
v___x_2130_ = ((size_t)0ULL);
v___x_2131_ = lean_usize_of_nat(v___x_2120_);
v___x_2132_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4_spec__5(v___x_2105_, v___x_2106_, v___x_2107_, v_ctx_2108_, v_cs_2115_, v___x_2130_, v___x_2131_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_);
lean_dec_ref(v_cs_2115_);
return v___x_2132_;
}
}
}
}
else
{
lean_object* v_vs_2134_; lean_object* v___x_2136_; uint8_t v_isShared_2137_; uint8_t v_isSharedCheck_2152_; 
v_vs_2134_ = lean_ctor_get(v_x_2109_, 0);
v_isSharedCheck_2152_ = !lean_is_exclusive(v_x_2109_);
if (v_isSharedCheck_2152_ == 0)
{
v___x_2136_ = v_x_2109_;
v_isShared_2137_ = v_isSharedCheck_2152_;
goto v_resetjp_2135_;
}
else
{
lean_inc(v_vs_2134_);
lean_dec(v_x_2109_);
v___x_2136_ = lean_box(0);
v_isShared_2137_ = v_isSharedCheck_2152_;
goto v_resetjp_2135_;
}
v_resetjp_2135_:
{
lean_object* v___x_2138_; lean_object* v___x_2139_; uint8_t v___x_2140_; 
v___x_2138_ = lean_unsigned_to_nat(0u);
v___x_2139_ = lean_array_get_size(v_vs_2134_);
v___x_2140_ = lean_nat_dec_lt(v___x_2138_, v___x_2139_);
if (v___x_2140_ == 0)
{
lean_object* v___x_2141_; lean_object* v___x_2143_; 
lean_dec_ref(v_vs_2134_);
lean_dec(v___x_2107_);
lean_dec_ref(v___x_2106_);
v___x_2141_ = lean_box(v___x_2140_);
if (v_isShared_2137_ == 0)
{
lean_ctor_set_tag(v___x_2136_, 0);
lean_ctor_set(v___x_2136_, 0, v___x_2141_);
v___x_2143_ = v___x_2136_;
goto v_reusejp_2142_;
}
else
{
lean_object* v_reuseFailAlloc_2144_; 
v_reuseFailAlloc_2144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2144_, 0, v___x_2141_);
v___x_2143_ = v_reuseFailAlloc_2144_;
goto v_reusejp_2142_;
}
v_reusejp_2142_:
{
return v___x_2143_;
}
}
else
{
if (v___x_2140_ == 0)
{
lean_object* v___x_2145_; lean_object* v___x_2147_; 
lean_dec_ref(v_vs_2134_);
lean_dec(v___x_2107_);
lean_dec_ref(v___x_2106_);
v___x_2145_ = lean_box(v___x_2140_);
if (v_isShared_2137_ == 0)
{
lean_ctor_set_tag(v___x_2136_, 0);
lean_ctor_set(v___x_2136_, 0, v___x_2145_);
v___x_2147_ = v___x_2136_;
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
size_t v___x_2149_; size_t v___x_2150_; lean_object* v___x_2151_; 
lean_del_object(v___x_2136_);
v___x_2149_ = ((size_t)0ULL);
v___x_2150_ = lean_usize_of_nat(v___x_2139_);
v___x_2151_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg(v___x_2105_, v___x_2106_, v___x_2107_, v_ctx_2108_, v_vs_2134_, v___x_2149_, v___x_2150_, v___y_2111_);
lean_dec_ref(v_vs_2134_);
return v___x_2151_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4_spec__5(uint8_t v___x_2153_, lean_object* v___x_2154_, lean_object* v___x_2155_, lean_object* v_ctx_2156_, lean_object* v_as_2157_, size_t v_i_2158_, size_t v_stop_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_){
_start:
{
uint8_t v___x_2165_; 
v___x_2165_ = lean_usize_dec_eq(v_i_2158_, v_stop_2159_);
if (v___x_2165_ == 0)
{
lean_object* v___x_2166_; lean_object* v___x_2167_; 
v___x_2166_ = lean_array_uget_borrowed(v_as_2157_, v_i_2158_);
lean_inc(v___x_2166_);
lean_inc(v___x_2155_);
lean_inc_ref(v___x_2154_);
v___x_2167_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4(v___x_2153_, v___x_2154_, v___x_2155_, v_ctx_2156_, v___x_2166_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_);
if (lean_obj_tag(v___x_2167_) == 0)
{
lean_object* v_a_2168_; lean_object* v___x_2170_; uint8_t v_isShared_2171_; uint8_t v_isSharedCheck_2179_; 
v_a_2168_ = lean_ctor_get(v___x_2167_, 0);
v_isSharedCheck_2179_ = !lean_is_exclusive(v___x_2167_);
if (v_isSharedCheck_2179_ == 0)
{
v___x_2170_ = v___x_2167_;
v_isShared_2171_ = v_isSharedCheck_2179_;
goto v_resetjp_2169_;
}
else
{
lean_inc(v_a_2168_);
lean_dec(v___x_2167_);
v___x_2170_ = lean_box(0);
v_isShared_2171_ = v_isSharedCheck_2179_;
goto v_resetjp_2169_;
}
v_resetjp_2169_:
{
uint8_t v___x_2172_; 
v___x_2172_ = lean_unbox(v_a_2168_);
if (v___x_2172_ == 0)
{
size_t v___x_2173_; size_t v___x_2174_; 
lean_del_object(v___x_2170_);
lean_dec(v_a_2168_);
v___x_2173_ = ((size_t)1ULL);
v___x_2174_ = lean_usize_add(v_i_2158_, v___x_2173_);
v_i_2158_ = v___x_2174_;
goto _start;
}
else
{
lean_object* v___x_2177_; 
lean_dec(v___x_2155_);
lean_dec_ref(v___x_2154_);
if (v_isShared_2171_ == 0)
{
v___x_2177_ = v___x_2170_;
goto v_reusejp_2176_;
}
else
{
lean_object* v_reuseFailAlloc_2178_; 
v_reuseFailAlloc_2178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2178_, 0, v_a_2168_);
v___x_2177_ = v_reuseFailAlloc_2178_;
goto v_reusejp_2176_;
}
v_reusejp_2176_:
{
return v___x_2177_;
}
}
}
}
else
{
lean_dec(v___x_2155_);
lean_dec_ref(v___x_2154_);
return v___x_2167_;
}
}
else
{
uint8_t v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; 
lean_dec(v___x_2155_);
lean_dec_ref(v___x_2154_);
v___x_2180_ = 0;
v___x_2181_ = lean_box(v___x_2180_);
v___x_2182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2182_, 0, v___x_2181_);
return v___x_2182_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4_spec__5___boxed(lean_object* v___x_2183_, lean_object* v___x_2184_, lean_object* v___x_2185_, lean_object* v_ctx_2186_, lean_object* v_as_2187_, lean_object* v_i_2188_, lean_object* v_stop_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_){
_start:
{
uint8_t v___x_7976__boxed_2195_; size_t v_i_boxed_2196_; size_t v_stop_boxed_2197_; lean_object* v_res_2198_; 
v___x_7976__boxed_2195_ = lean_unbox(v___x_2183_);
v_i_boxed_2196_ = lean_unbox_usize(v_i_2188_);
lean_dec(v_i_2188_);
v_stop_boxed_2197_ = lean_unbox_usize(v_stop_2189_);
lean_dec(v_stop_2189_);
v_res_2198_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4_spec__5(v___x_7976__boxed_2195_, v___x_2184_, v___x_2185_, v_ctx_2186_, v_as_2187_, v_i_boxed_2196_, v_stop_boxed_2197_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_);
lean_dec(v___y_2193_);
lean_dec_ref(v___y_2192_);
lean_dec(v___y_2191_);
lean_dec_ref(v___y_2190_);
lean_dec_ref(v_as_2187_);
lean_dec_ref(v_ctx_2186_);
return v_res_2198_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4___boxed(lean_object* v___x_2199_, lean_object* v___x_2200_, lean_object* v___x_2201_, lean_object* v_ctx_2202_, lean_object* v_x_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_){
_start:
{
uint8_t v___x_7995__boxed_2209_; lean_object* v_res_2210_; 
v___x_7995__boxed_2209_ = lean_unbox(v___x_2199_);
v_res_2210_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4(v___x_7995__boxed_2209_, v___x_2200_, v___x_2201_, v_ctx_2202_, v_x_2203_, v___y_2204_, v___y_2205_, v___y_2206_, v___y_2207_);
lean_dec(v___y_2207_);
lean_dec_ref(v___y_2206_);
lean_dec(v___y_2205_);
lean_dec_ref(v___y_2204_);
lean_dec_ref(v_ctx_2202_);
return v_res_2210_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4(uint8_t v___x_2211_, lean_object* v___x_2212_, lean_object* v___x_2213_, lean_object* v_ctx_2214_, lean_object* v_t_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_){
_start:
{
lean_object* v_root_2221_; lean_object* v_tail_2222_; lean_object* v___x_2223_; 
v_root_2221_ = lean_ctor_get(v_t_2215_, 0);
lean_inc_ref(v_root_2221_);
v_tail_2222_ = lean_ctor_get(v_t_2215_, 1);
lean_inc_ref(v_tail_2222_);
lean_dec_ref(v_t_2215_);
lean_inc(v___x_2213_);
lean_inc_ref(v___x_2212_);
v___x_2223_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4(v___x_2211_, v___x_2212_, v___x_2213_, v_ctx_2214_, v_root_2221_, v___y_2216_, v___y_2217_, v___y_2218_, v___y_2219_);
if (lean_obj_tag(v___x_2223_) == 0)
{
lean_object* v_a_2224_; uint8_t v___x_2225_; 
v_a_2224_ = lean_ctor_get(v___x_2223_, 0);
lean_inc(v_a_2224_);
v___x_2225_ = lean_unbox(v_a_2224_);
lean_dec(v_a_2224_);
if (v___x_2225_ == 0)
{
lean_object* v___x_2227_; uint8_t v_isShared_2228_; uint8_t v_isSharedCheck_2243_; 
v_isSharedCheck_2243_ = !lean_is_exclusive(v___x_2223_);
if (v_isSharedCheck_2243_ == 0)
{
lean_object* v_unused_2244_; 
v_unused_2244_ = lean_ctor_get(v___x_2223_, 0);
lean_dec(v_unused_2244_);
v___x_2227_ = v___x_2223_;
v_isShared_2228_ = v_isSharedCheck_2243_;
goto v_resetjp_2226_;
}
else
{
lean_dec(v___x_2223_);
v___x_2227_ = lean_box(0);
v_isShared_2228_ = v_isSharedCheck_2243_;
goto v_resetjp_2226_;
}
v_resetjp_2226_:
{
lean_object* v___x_2229_; lean_object* v___x_2230_; uint8_t v___x_2231_; 
v___x_2229_ = lean_unsigned_to_nat(0u);
v___x_2230_ = lean_array_get_size(v_tail_2222_);
v___x_2231_ = lean_nat_dec_lt(v___x_2229_, v___x_2230_);
if (v___x_2231_ == 0)
{
lean_object* v___x_2232_; lean_object* v___x_2234_; 
lean_dec_ref(v_tail_2222_);
lean_dec(v___x_2213_);
lean_dec_ref(v___x_2212_);
v___x_2232_ = lean_box(v___x_2231_);
if (v_isShared_2228_ == 0)
{
lean_ctor_set(v___x_2227_, 0, v___x_2232_);
v___x_2234_ = v___x_2227_;
goto v_reusejp_2233_;
}
else
{
lean_object* v_reuseFailAlloc_2235_; 
v_reuseFailAlloc_2235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2235_, 0, v___x_2232_);
v___x_2234_ = v_reuseFailAlloc_2235_;
goto v_reusejp_2233_;
}
v_reusejp_2233_:
{
return v___x_2234_;
}
}
else
{
if (v___x_2231_ == 0)
{
lean_object* v___x_2236_; lean_object* v___x_2238_; 
lean_dec_ref(v_tail_2222_);
lean_dec(v___x_2213_);
lean_dec_ref(v___x_2212_);
v___x_2236_ = lean_box(v___x_2231_);
if (v_isShared_2228_ == 0)
{
lean_ctor_set(v___x_2227_, 0, v___x_2236_);
v___x_2238_ = v___x_2227_;
goto v_reusejp_2237_;
}
else
{
lean_object* v_reuseFailAlloc_2239_; 
v_reuseFailAlloc_2239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2239_, 0, v___x_2236_);
v___x_2238_ = v_reuseFailAlloc_2239_;
goto v_reusejp_2237_;
}
v_reusejp_2237_:
{
return v___x_2238_;
}
}
else
{
size_t v___x_2240_; size_t v___x_2241_; lean_object* v___x_2242_; 
lean_del_object(v___x_2227_);
v___x_2240_ = ((size_t)0ULL);
v___x_2241_ = lean_usize_of_nat(v___x_2230_);
v___x_2242_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg(v___x_2211_, v___x_2212_, v___x_2213_, v_ctx_2214_, v_tail_2222_, v___x_2240_, v___x_2241_, v___y_2217_);
lean_dec_ref(v_tail_2222_);
return v___x_2242_;
}
}
}
}
else
{
lean_dec_ref(v_tail_2222_);
lean_dec(v___x_2213_);
lean_dec_ref(v___x_2212_);
return v___x_2223_;
}
}
else
{
lean_dec_ref(v_tail_2222_);
lean_dec(v___x_2213_);
lean_dec_ref(v___x_2212_);
return v___x_2223_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4___boxed(lean_object* v___x_2245_, lean_object* v___x_2246_, lean_object* v___x_2247_, lean_object* v_ctx_2248_, lean_object* v_t_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_){
_start:
{
uint8_t v___x_8140__boxed_2255_; lean_object* v_res_2256_; 
v___x_8140__boxed_2255_ = lean_unbox(v___x_2245_);
v_res_2256_ = l_Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4(v___x_8140__boxed_2255_, v___x_2246_, v___x_2247_, v_ctx_2248_, v_t_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_);
lean_dec(v___y_2253_);
lean_dec_ref(v___y_2252_);
lean_dec(v___y_2251_);
lean_dec_ref(v___y_2250_);
lean_dec_ref(v_ctx_2248_);
return v_res_2256_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices(lean_object* v_ctx_2257_, lean_object* v_a_2258_, lean_object* v_a_2259_, lean_object* v_a_2260_, lean_object* v_a_2261_){
_start:
{
lean_object* v_majorTypeIndices_2263_; lean_object* v___x_2264_; uint8_t v___y_2266_; lean_object* v___x_2288_; uint8_t v___x_2289_; 
v_majorTypeIndices_2263_ = lean_ctor_get(v_ctx_2257_, 5);
lean_inc_ref(v_majorTypeIndices_2263_);
v___x_2264_ = lean_array_get_size(v_majorTypeIndices_2263_);
v___x_2288_ = lean_unsigned_to_nat(0u);
v___x_2289_ = lean_nat_dec_eq(v___x_2264_, v___x_2288_);
if (v___x_2289_ == 0)
{
uint8_t v___x_2290_; 
v___x_2290_ = lean_nat_dec_lt(v___x_2288_, v___x_2264_);
if (v___x_2290_ == 0)
{
v___y_2266_ = v___x_2290_;
goto v___jp_2265_;
}
else
{
if (v___x_2290_ == 0)
{
v___y_2266_ = v___x_2290_;
goto v___jp_2265_;
}
else
{
size_t v___x_2291_; size_t v___x_2292_; uint8_t v___x_2293_; 
v___x_2291_ = ((size_t)0ULL);
v___x_2292_ = lean_usize_of_nat(v___x_2264_);
v___x_2293_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5(v___x_2264_, v_majorTypeIndices_2263_, v___x_2291_, v___x_2292_);
if (v___x_2293_ == 0)
{
v___y_2266_ = v___x_2293_;
goto v___jp_2265_;
}
else
{
lean_object* v___x_2294_; lean_object* v___x_2295_; 
lean_dec_ref(v_majorTypeIndices_2263_);
lean_dec_ref(v_ctx_2257_);
v___x_2294_ = lean_box(v___x_2289_);
v___x_2295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2295_, 0, v___x_2294_);
return v___x_2295_;
}
}
}
}
else
{
lean_object* v___x_2296_; lean_object* v___x_2297_; 
lean_dec_ref(v_majorTypeIndices_2263_);
lean_dec_ref(v_ctx_2257_);
v___x_2296_ = lean_box(v___x_2289_);
v___x_2297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2297_, 0, v___x_2296_);
return v___x_2297_;
}
v___jp_2265_:
{
uint8_t v___x_2267_; 
v___x_2267_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1___redArg(v_majorTypeIndices_2263_, v___x_2264_, v___x_2264_);
if (v___x_2267_ == 0)
{
lean_object* v_lctx_2268_; lean_object* v_decls_2269_; lean_object* v___x_2270_; 
v_lctx_2268_ = lean_ctor_get(v_a_2258_, 2);
v_decls_2269_ = lean_ctor_get(v_lctx_2268_, 1);
lean_inc_ref(v_decls_2269_);
v___x_2270_ = l_Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4(v___x_2267_, v_majorTypeIndices_2263_, v___x_2264_, v_ctx_2257_, v_decls_2269_, v_a_2258_, v_a_2259_, v_a_2260_, v_a_2261_);
lean_dec_ref(v_ctx_2257_);
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
lean_dec_ref(v_majorTypeIndices_2263_);
lean_dec_ref(v_ctx_2257_);
v___x_2286_ = lean_box(v___y_2266_);
v___x_2287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2287_, 0, v___x_2286_);
return v___x_2287_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___boxed(lean_object* v_ctx_2298_, lean_object* v_a_2299_, lean_object* v_a_2300_, lean_object* v_a_2301_, lean_object* v_a_2302_, lean_object* v_a_2303_){
_start:
{
lean_object* v_res_2304_; 
v_res_2304_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices(v_ctx_2298_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_);
lean_dec(v_a_2302_);
lean_dec_ref(v_a_2301_);
lean_dec(v_a_2300_);
lean_dec_ref(v_a_2299_);
return v_res_2304_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0(lean_object* v___x_2305_, lean_object* v_i_2306_, lean_object* v_n_2307_, lean_object* v_i_2308_, lean_object* v_a_2309_){
_start:
{
uint8_t v___x_2310_; 
v___x_2310_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0___redArg(v___x_2305_, v_i_2306_, v_n_2307_, v_i_2308_);
return v___x_2310_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0___boxed(lean_object* v___x_2311_, lean_object* v_i_2312_, lean_object* v_n_2313_, lean_object* v_i_2314_, lean_object* v_a_2315_){
_start:
{
uint8_t v_res_2316_; lean_object* v_r_2317_; 
v_res_2316_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0(v___x_2311_, v_i_2312_, v_n_2313_, v_i_2314_, v_a_2315_);
lean_dec(v_n_2313_);
lean_dec(v_i_2312_);
lean_dec_ref(v___x_2311_);
v_r_2317_ = lean_box(v_res_2316_);
return v_r_2317_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1(lean_object* v___x_2318_, lean_object* v_n_2319_, lean_object* v_i_2320_, lean_object* v_a_2321_){
_start:
{
uint8_t v___x_2322_; 
v___x_2322_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1___redArg(v___x_2318_, v_n_2319_, v_i_2320_);
return v___x_2322_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1___boxed(lean_object* v___x_2323_, lean_object* v_n_2324_, lean_object* v_i_2325_, lean_object* v_a_2326_){
_start:
{
uint8_t v_res_2327_; lean_object* v_r_2328_; 
v_res_2327_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1(v___x_2323_, v_n_2324_, v_i_2325_, v_a_2326_);
lean_dec(v_n_2324_);
lean_dec_ref(v___x_2323_);
v_r_2328_ = lean_box(v_res_2327_);
return v_r_2328_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5(uint8_t v___x_2329_, lean_object* v___x_2330_, lean_object* v___x_2331_, lean_object* v_ctx_2332_, lean_object* v_as_2333_, size_t v_i_2334_, size_t v_stop_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_){
_start:
{
lean_object* v___x_2341_; 
v___x_2341_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg(v___x_2329_, v___x_2330_, v___x_2331_, v_ctx_2332_, v_as_2333_, v_i_2334_, v_stop_2335_, v___y_2337_);
return v___x_2341_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___boxed(lean_object* v___x_2342_, lean_object* v___x_2343_, lean_object* v___x_2344_, lean_object* v_ctx_2345_, lean_object* v_as_2346_, lean_object* v_i_2347_, lean_object* v_stop_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_){
_start:
{
uint8_t v___x_8293__boxed_2354_; size_t v_i_boxed_2355_; size_t v_stop_boxed_2356_; lean_object* v_res_2357_; 
v___x_8293__boxed_2354_ = lean_unbox(v___x_2342_);
v_i_boxed_2355_ = lean_unbox_usize(v_i_2347_);
lean_dec(v_i_2347_);
v_stop_boxed_2356_ = lean_unbox_usize(v_stop_2348_);
lean_dec(v_stop_2348_);
v_res_2357_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5(v___x_8293__boxed_2354_, v___x_2343_, v___x_2344_, v_ctx_2345_, v_as_2346_, v_i_boxed_2355_, v_stop_boxed_2356_, v___y_2349_, v___y_2350_, v___y_2351_, v___y_2352_);
lean_dec(v___y_2352_);
lean_dec_ref(v___y_2351_);
lean_dec(v___y_2350_);
lean_dec_ref(v___y_2349_);
lean_dec_ref(v_as_2346_);
lean_dec_ref(v_ctx_2345_);
return v_res_2357_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__0(lean_object* v_as_2358_, size_t v_i_2359_, size_t v_stop_2360_, lean_object* v_b_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_){
_start:
{
lean_object* v_a_2368_; uint8_t v___x_2372_; 
v___x_2372_ = lean_usize_dec_eq(v_i_2359_, v_stop_2360_);
if (v___x_2372_ == 0)
{
lean_object* v_toInductionSubgoal_2373_; lean_object* v_ctorName_2374_; lean_object* v_mvarId_2375_; lean_object* v_fields_2376_; lean_object* v_subst_2377_; lean_object* v___x_2379_; uint8_t v_isShared_2380_; uint8_t v_isSharedCheck_2430_; 
v_toInductionSubgoal_2373_ = lean_ctor_get(v_b_2361_, 0);
lean_inc_ref(v_toInductionSubgoal_2373_);
v_ctorName_2374_ = lean_ctor_get(v_b_2361_, 1);
v_mvarId_2375_ = lean_ctor_get(v_toInductionSubgoal_2373_, 0);
v_fields_2376_ = lean_ctor_get(v_toInductionSubgoal_2373_, 1);
v_subst_2377_ = lean_ctor_get(v_toInductionSubgoal_2373_, 2);
v_isSharedCheck_2430_ = !lean_is_exclusive(v_toInductionSubgoal_2373_);
if (v_isSharedCheck_2430_ == 0)
{
v___x_2379_ = v_toInductionSubgoal_2373_;
v_isShared_2380_ = v_isSharedCheck_2430_;
goto v_resetjp_2378_;
}
else
{
lean_inc(v_subst_2377_);
lean_inc(v_fields_2376_);
lean_inc(v_mvarId_2375_);
lean_dec(v_toInductionSubgoal_2373_);
v___x_2379_ = lean_box(0);
v_isShared_2380_ = v_isSharedCheck_2430_;
goto v_resetjp_2378_;
}
v_resetjp_2378_:
{
lean_object* v___x_2381_; lean_object* v___x_2382_; 
v___x_2381_ = lean_array_uget_borrowed(v_as_2358_, v_i_2359_);
lean_inc(v___x_2381_);
v___x_2382_ = l_Lean_Meta_FVarSubst_get(v_subst_2377_, v___x_2381_);
if (lean_obj_tag(v___x_2382_) == 1)
{
lean_object* v_fvarId_2383_; lean_object* v___x_2384_; 
v_fvarId_2383_ = lean_ctor_get(v___x_2382_, 0);
lean_inc(v_fvarId_2383_);
lean_dec_ref_known(v___x_2382_, 1);
v___x_2384_ = l_Lean_Meta_saveState___redArg(v___y_2363_, v___y_2365_);
if (lean_obj_tag(v___x_2384_) == 0)
{
lean_object* v_a_2385_; lean_object* v___x_2386_; 
v_a_2385_ = lean_ctor_get(v___x_2384_, 0);
lean_inc(v_a_2385_);
lean_dec_ref_known(v___x_2384_, 1);
v___x_2386_ = l_Lean_MVarId_clear(v_mvarId_2375_, v_fvarId_2383_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_);
if (lean_obj_tag(v___x_2386_) == 0)
{
lean_object* v___x_2388_; uint8_t v_isShared_2389_; uint8_t v_isSharedCheck_2398_; 
lean_inc(v_ctorName_2374_);
lean_dec(v_a_2385_);
v_isSharedCheck_2398_ = !lean_is_exclusive(v_b_2361_);
if (v_isSharedCheck_2398_ == 0)
{
lean_object* v_unused_2399_; lean_object* v_unused_2400_; 
v_unused_2399_ = lean_ctor_get(v_b_2361_, 1);
lean_dec(v_unused_2399_);
v_unused_2400_ = lean_ctor_get(v_b_2361_, 0);
lean_dec(v_unused_2400_);
v___x_2388_ = v_b_2361_;
v_isShared_2389_ = v_isSharedCheck_2398_;
goto v_resetjp_2387_;
}
else
{
lean_dec(v_b_2361_);
v___x_2388_ = lean_box(0);
v_isShared_2389_ = v_isSharedCheck_2398_;
goto v_resetjp_2387_;
}
v_resetjp_2387_:
{
lean_object* v_a_2390_; lean_object* v___x_2391_; lean_object* v___x_2393_; 
v_a_2390_ = lean_ctor_get(v___x_2386_, 0);
lean_inc(v_a_2390_);
lean_dec_ref_known(v___x_2386_, 1);
v___x_2391_ = l_Lean_Meta_FVarSubst_erase(v_subst_2377_, v___x_2381_);
if (v_isShared_2380_ == 0)
{
lean_ctor_set(v___x_2379_, 2, v___x_2391_);
lean_ctor_set(v___x_2379_, 0, v_a_2390_);
v___x_2393_ = v___x_2379_;
goto v_reusejp_2392_;
}
else
{
lean_object* v_reuseFailAlloc_2397_; 
v_reuseFailAlloc_2397_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2397_, 0, v_a_2390_);
lean_ctor_set(v_reuseFailAlloc_2397_, 1, v_fields_2376_);
lean_ctor_set(v_reuseFailAlloc_2397_, 2, v___x_2391_);
v___x_2393_ = v_reuseFailAlloc_2397_;
goto v_reusejp_2392_;
}
v_reusejp_2392_:
{
lean_object* v___x_2395_; 
if (v_isShared_2389_ == 0)
{
lean_ctor_set(v___x_2388_, 0, v___x_2393_);
v___x_2395_ = v___x_2388_;
goto v_reusejp_2394_;
}
else
{
lean_object* v_reuseFailAlloc_2396_; 
v_reuseFailAlloc_2396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2396_, 0, v___x_2393_);
lean_ctor_set(v_reuseFailAlloc_2396_, 1, v_ctorName_2374_);
v___x_2395_ = v_reuseFailAlloc_2396_;
goto v_reusejp_2394_;
}
v_reusejp_2394_:
{
v_a_2368_ = v___x_2395_;
goto v___jp_2367_;
}
}
}
}
else
{
lean_object* v_a_2401_; lean_object* v___x_2403_; uint8_t v_isShared_2404_; uint8_t v_isSharedCheck_2421_; 
lean_del_object(v___x_2379_);
lean_dec(v_subst_2377_);
lean_dec_ref(v_fields_2376_);
v_a_2401_ = lean_ctor_get(v___x_2386_, 0);
v_isSharedCheck_2421_ = !lean_is_exclusive(v___x_2386_);
if (v_isSharedCheck_2421_ == 0)
{
v___x_2403_ = v___x_2386_;
v_isShared_2404_ = v_isSharedCheck_2421_;
goto v_resetjp_2402_;
}
else
{
lean_inc(v_a_2401_);
lean_dec(v___x_2386_);
v___x_2403_ = lean_box(0);
v_isShared_2404_ = v_isSharedCheck_2421_;
goto v_resetjp_2402_;
}
v_resetjp_2402_:
{
lean_object* v___x_2406_; 
lean_inc(v_a_2401_);
if (v_isShared_2404_ == 0)
{
v___x_2406_ = v___x_2403_;
goto v_reusejp_2405_;
}
else
{
lean_object* v_reuseFailAlloc_2420_; 
v_reuseFailAlloc_2420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2420_, 0, v_a_2401_);
v___x_2406_ = v_reuseFailAlloc_2420_;
goto v_reusejp_2405_;
}
v_reusejp_2405_:
{
uint8_t v___y_2408_; uint8_t v___x_2418_; 
v___x_2418_ = l_Lean_Exception_isInterrupt(v_a_2401_);
if (v___x_2418_ == 0)
{
uint8_t v___x_2419_; 
v___x_2419_ = l_Lean_Exception_isRuntime(v_a_2401_);
v___y_2408_ = v___x_2419_;
goto v___jp_2407_;
}
else
{
lean_dec(v_a_2401_);
v___y_2408_ = v___x_2418_;
goto v___jp_2407_;
}
v___jp_2407_:
{
if (v___y_2408_ == 0)
{
lean_object* v___x_2409_; 
lean_dec_ref(v___x_2406_);
v___x_2409_ = l_Lean_Meta_SavedState_restore___redArg(v_a_2385_, v___y_2363_, v___y_2365_);
lean_dec(v_a_2385_);
if (lean_obj_tag(v___x_2409_) == 0)
{
lean_dec_ref_known(v___x_2409_, 1);
v_a_2368_ = v_b_2361_;
goto v___jp_2367_;
}
else
{
lean_object* v_a_2410_; lean_object* v___x_2412_; uint8_t v_isShared_2413_; uint8_t v_isSharedCheck_2417_; 
lean_dec_ref(v_b_2361_);
v_a_2410_ = lean_ctor_get(v___x_2409_, 0);
v_isSharedCheck_2417_ = !lean_is_exclusive(v___x_2409_);
if (v_isSharedCheck_2417_ == 0)
{
v___x_2412_ = v___x_2409_;
v_isShared_2413_ = v_isSharedCheck_2417_;
goto v_resetjp_2411_;
}
else
{
lean_inc(v_a_2410_);
lean_dec(v___x_2409_);
v___x_2412_ = lean_box(0);
v_isShared_2413_ = v_isSharedCheck_2417_;
goto v_resetjp_2411_;
}
v_resetjp_2411_:
{
lean_object* v___x_2415_; 
if (v_isShared_2413_ == 0)
{
v___x_2415_ = v___x_2412_;
goto v_reusejp_2414_;
}
else
{
lean_object* v_reuseFailAlloc_2416_; 
v_reuseFailAlloc_2416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2416_, 0, v_a_2410_);
v___x_2415_ = v_reuseFailAlloc_2416_;
goto v_reusejp_2414_;
}
v_reusejp_2414_:
{
return v___x_2415_;
}
}
}
}
else
{
lean_dec(v_a_2385_);
lean_dec_ref(v_b_2361_);
return v___x_2406_;
}
}
}
}
}
}
else
{
lean_object* v_a_2422_; lean_object* v___x_2424_; uint8_t v_isShared_2425_; uint8_t v_isSharedCheck_2429_; 
lean_dec(v_fvarId_2383_);
lean_del_object(v___x_2379_);
lean_dec(v_subst_2377_);
lean_dec_ref(v_fields_2376_);
lean_dec(v_mvarId_2375_);
lean_dec_ref(v_b_2361_);
v_a_2422_ = lean_ctor_get(v___x_2384_, 0);
v_isSharedCheck_2429_ = !lean_is_exclusive(v___x_2384_);
if (v_isSharedCheck_2429_ == 0)
{
v___x_2424_ = v___x_2384_;
v_isShared_2425_ = v_isSharedCheck_2429_;
goto v_resetjp_2423_;
}
else
{
lean_inc(v_a_2422_);
lean_dec(v___x_2384_);
v___x_2424_ = lean_box(0);
v_isShared_2425_ = v_isSharedCheck_2429_;
goto v_resetjp_2423_;
}
v_resetjp_2423_:
{
lean_object* v___x_2427_; 
if (v_isShared_2425_ == 0)
{
v___x_2427_ = v___x_2424_;
goto v_reusejp_2426_;
}
else
{
lean_object* v_reuseFailAlloc_2428_; 
v_reuseFailAlloc_2428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2428_, 0, v_a_2422_);
v___x_2427_ = v_reuseFailAlloc_2428_;
goto v_reusejp_2426_;
}
v_reusejp_2426_:
{
return v___x_2427_;
}
}
}
}
else
{
lean_dec_ref(v___x_2382_);
lean_del_object(v___x_2379_);
lean_dec(v_subst_2377_);
lean_dec_ref(v_fields_2376_);
lean_dec(v_mvarId_2375_);
v_a_2368_ = v_b_2361_;
goto v___jp_2367_;
}
}
}
else
{
lean_object* v___x_2431_; 
v___x_2431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2431_, 0, v_b_2361_);
return v___x_2431_;
}
v___jp_2367_:
{
size_t v___x_2369_; size_t v___x_2370_; 
v___x_2369_ = ((size_t)1ULL);
v___x_2370_ = lean_usize_add(v_i_2359_, v___x_2369_);
v_i_2359_ = v___x_2370_;
v_b_2361_ = v_a_2368_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__0___boxed(lean_object* v_as_2432_, lean_object* v_i_2433_, lean_object* v_stop_2434_, lean_object* v_b_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_){
_start:
{
size_t v_i_boxed_2441_; size_t v_stop_boxed_2442_; lean_object* v_res_2443_; 
v_i_boxed_2441_ = lean_unbox_usize(v_i_2433_);
lean_dec(v_i_2433_);
v_stop_boxed_2442_ = lean_unbox_usize(v_stop_2434_);
lean_dec(v_stop_2434_);
v_res_2443_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__0(v_as_2432_, v_i_boxed_2441_, v_stop_boxed_2442_, v_b_2435_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_);
lean_dec(v___y_2439_);
lean_dec_ref(v___y_2438_);
lean_dec(v___y_2437_);
lean_dec_ref(v___y_2436_);
lean_dec_ref(v_as_2432_);
return v_res_2443_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__1(lean_object* v_indicesFVarIds_2444_, size_t v_sz_2445_, size_t v_i_2446_, lean_object* v_bs_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_){
_start:
{
uint8_t v___x_2453_; 
v___x_2453_ = lean_usize_dec_lt(v_i_2446_, v_sz_2445_);
if (v___x_2453_ == 0)
{
lean_object* v___x_2454_; 
v___x_2454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2454_, 0, v_bs_2447_);
return v___x_2454_;
}
else
{
lean_object* v_v_2455_; lean_object* v___x_2456_; lean_object* v_bs_x27_2457_; lean_object* v_a_2459_; lean_object* v___y_2465_; lean_object* v___x_2475_; uint8_t v___x_2476_; 
v_v_2455_ = lean_array_uget(v_bs_2447_, v_i_2446_);
v___x_2456_ = lean_unsigned_to_nat(0u);
v_bs_x27_2457_ = lean_array_uset(v_bs_2447_, v_i_2446_, v___x_2456_);
v___x_2475_ = lean_array_get_size(v_indicesFVarIds_2444_);
v___x_2476_ = lean_nat_dec_lt(v___x_2456_, v___x_2475_);
if (v___x_2476_ == 0)
{
v_a_2459_ = v_v_2455_;
goto v___jp_2458_;
}
else
{
uint8_t v___x_2477_; 
v___x_2477_ = lean_nat_dec_le(v___x_2475_, v___x_2475_);
if (v___x_2477_ == 0)
{
if (v___x_2476_ == 0)
{
v_a_2459_ = v_v_2455_;
goto v___jp_2458_;
}
else
{
size_t v___x_2478_; size_t v___x_2479_; lean_object* v___x_2480_; 
v___x_2478_ = ((size_t)0ULL);
v___x_2479_ = lean_usize_of_nat(v___x_2475_);
v___x_2480_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__0(v_indicesFVarIds_2444_, v___x_2478_, v___x_2479_, v_v_2455_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_);
v___y_2465_ = v___x_2480_;
goto v___jp_2464_;
}
}
else
{
size_t v___x_2481_; size_t v___x_2482_; lean_object* v___x_2483_; 
v___x_2481_ = ((size_t)0ULL);
v___x_2482_ = lean_usize_of_nat(v___x_2475_);
v___x_2483_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__0(v_indicesFVarIds_2444_, v___x_2481_, v___x_2482_, v_v_2455_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_);
v___y_2465_ = v___x_2483_;
goto v___jp_2464_;
}
}
v___jp_2458_:
{
size_t v___x_2460_; size_t v___x_2461_; lean_object* v___x_2462_; 
v___x_2460_ = ((size_t)1ULL);
v___x_2461_ = lean_usize_add(v_i_2446_, v___x_2460_);
v___x_2462_ = lean_array_uset(v_bs_x27_2457_, v_i_2446_, v_a_2459_);
v_i_2446_ = v___x_2461_;
v_bs_2447_ = v___x_2462_;
goto _start;
}
v___jp_2464_:
{
if (lean_obj_tag(v___y_2465_) == 0)
{
lean_object* v_a_2466_; 
v_a_2466_ = lean_ctor_get(v___y_2465_, 0);
lean_inc(v_a_2466_);
lean_dec_ref_known(v___y_2465_, 1);
v_a_2459_ = v_a_2466_;
goto v___jp_2458_;
}
else
{
lean_object* v_a_2467_; lean_object* v___x_2469_; uint8_t v_isShared_2470_; uint8_t v_isSharedCheck_2474_; 
lean_dec_ref(v_bs_x27_2457_);
v_a_2467_ = lean_ctor_get(v___y_2465_, 0);
v_isSharedCheck_2474_ = !lean_is_exclusive(v___y_2465_);
if (v_isSharedCheck_2474_ == 0)
{
v___x_2469_ = v___y_2465_;
v_isShared_2470_ = v_isSharedCheck_2474_;
goto v_resetjp_2468_;
}
else
{
lean_inc(v_a_2467_);
lean_dec(v___y_2465_);
v___x_2469_ = lean_box(0);
v_isShared_2470_ = v_isSharedCheck_2474_;
goto v_resetjp_2468_;
}
v_resetjp_2468_:
{
lean_object* v___x_2472_; 
if (v_isShared_2470_ == 0)
{
v___x_2472_ = v___x_2469_;
goto v_reusejp_2471_;
}
else
{
lean_object* v_reuseFailAlloc_2473_; 
v_reuseFailAlloc_2473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2473_, 0, v_a_2467_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__1___boxed(lean_object* v_indicesFVarIds_2484_, lean_object* v_sz_2485_, lean_object* v_i_2486_, lean_object* v_bs_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_){
_start:
{
size_t v_sz_boxed_2493_; size_t v_i_boxed_2494_; lean_object* v_res_2495_; 
v_sz_boxed_2493_ = lean_unbox_usize(v_sz_2485_);
lean_dec(v_sz_2485_);
v_i_boxed_2494_ = lean_unbox_usize(v_i_2486_);
lean_dec(v_i_2486_);
v_res_2495_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__1(v_indicesFVarIds_2484_, v_sz_boxed_2493_, v_i_boxed_2494_, v_bs_2487_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_);
lean_dec(v___y_2491_);
lean_dec_ref(v___y_2490_);
lean_dec(v___y_2489_);
lean_dec_ref(v___y_2488_);
lean_dec_ref(v_indicesFVarIds_2484_);
return v_res_2495_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices(lean_object* v_s_u2081_2496_, lean_object* v_s_u2082_2497_, lean_object* v_a_2498_, lean_object* v_a_2499_, lean_object* v_a_2500_, lean_object* v_a_2501_){
_start:
{
lean_object* v_indicesFVarIds_2503_; size_t v_sz_2504_; size_t v___x_2505_; lean_object* v___x_2506_; 
v_indicesFVarIds_2503_ = lean_ctor_get(v_s_u2081_2496_, 1);
v_sz_2504_ = lean_array_size(v_s_u2082_2497_);
v___x_2505_ = ((size_t)0ULL);
v___x_2506_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__1(v_indicesFVarIds_2503_, v_sz_2504_, v___x_2505_, v_s_u2082_2497_, v_a_2498_, v_a_2499_, v_a_2500_, v_a_2501_);
return v___x_2506_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices___boxed(lean_object* v_s_u2081_2507_, lean_object* v_s_u2082_2508_, lean_object* v_a_2509_, lean_object* v_a_2510_, lean_object* v_a_2511_, lean_object* v_a_2512_, lean_object* v_a_2513_){
_start:
{
lean_object* v_res_2514_; 
v_res_2514_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices(v_s_u2081_2507_, v_s_u2082_2508_, v_a_2509_, v_a_2510_, v_a_2511_, v_a_2512_);
lean_dec(v_a_2512_);
lean_dec_ref(v_a_2511_);
lean_dec(v_a_2510_);
lean_dec_ref(v_a_2509_);
lean_dec_ref(v_s_u2081_2507_);
return v_res_2514_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0___redArg(lean_object* v_ctorNames_2515_, lean_object* v_us_2516_, lean_object* v_params_2517_, lean_object* v_majorFVarId_2518_, size_t v_sz_2519_, size_t v_i_2520_, lean_object* v_bs_2521_){
_start:
{
uint8_t v___x_2522_; 
v___x_2522_ = lean_usize_dec_lt(v_i_2520_, v_sz_2519_);
if (v___x_2522_ == 0)
{
lean_dec(v_majorFVarId_2518_);
lean_dec(v_us_2516_);
return v_bs_2521_;
}
else
{
lean_object* v_v_2523_; lean_object* v___x_2524_; lean_object* v_bs_x27_2525_; lean_object* v___y_2527_; lean_object* v___x_2532_; lean_object* v___x_2533_; uint8_t v___x_2534_; 
v_v_2523_ = lean_array_uget(v_bs_2521_, v_i_2520_);
v___x_2524_ = lean_unsigned_to_nat(0u);
v_bs_x27_2525_ = lean_array_uset(v_bs_2521_, v_i_2520_, v___x_2524_);
v___x_2532_ = lean_usize_to_nat(v_i_2520_);
v___x_2533_ = lean_array_get_size(v_ctorNames_2515_);
v___x_2534_ = lean_nat_dec_lt(v___x_2532_, v___x_2533_);
if (v___x_2534_ == 0)
{
lean_object* v___x_2535_; lean_object* v___x_2536_; 
lean_dec(v___x_2532_);
v___x_2535_ = lean_box(0);
v___x_2536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2536_, 0, v_v_2523_);
lean_ctor_set(v___x_2536_, 1, v___x_2535_);
v___y_2527_ = v___x_2536_;
goto v___jp_2526_;
}
else
{
lean_object* v_mvarId_2537_; lean_object* v_fields_2538_; lean_object* v_subst_2539_; lean_object* v___x_2541_; uint8_t v_isShared_2542_; uint8_t v_isSharedCheck_2554_; 
v_mvarId_2537_ = lean_ctor_get(v_v_2523_, 0);
v_fields_2538_ = lean_ctor_get(v_v_2523_, 1);
v_subst_2539_ = lean_ctor_get(v_v_2523_, 2);
v_isSharedCheck_2554_ = !lean_is_exclusive(v_v_2523_);
if (v_isSharedCheck_2554_ == 0)
{
v___x_2541_ = v_v_2523_;
v_isShared_2542_ = v_isSharedCheck_2554_;
goto v_resetjp_2540_;
}
else
{
lean_inc(v_subst_2539_);
lean_inc(v_fields_2538_);
lean_inc(v_mvarId_2537_);
lean_dec(v_v_2523_);
v___x_2541_ = lean_box(0);
v_isShared_2542_ = v_isSharedCheck_2554_;
goto v_resetjp_2540_;
}
v_resetjp_2540_:
{
lean_object* v_ctorName_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v_ctorApp_2546_; lean_object* v___x_2547_; lean_object* v_subst_2548_; lean_object* v___x_2550_; 
v_ctorName_2543_ = lean_array_fget_borrowed(v_ctorNames_2515_, v___x_2532_);
lean_dec(v___x_2532_);
lean_inc(v_us_2516_);
lean_inc(v_ctorName_2543_);
v___x_2544_ = l_Lean_mkConst(v_ctorName_2543_, v_us_2516_);
v___x_2545_ = l_Lean_mkAppN(v___x_2544_, v_params_2517_);
v_ctorApp_2546_ = l_Lean_mkAppN(v___x_2545_, v_fields_2538_);
v___x_2547_ = l_Lean_Meta_FVarSubst_erase(v_subst_2539_, v_majorFVarId_2518_);
lean_inc(v_majorFVarId_2518_);
v_subst_2548_ = l_Lean_Meta_FVarSubst_insert(v___x_2547_, v_majorFVarId_2518_, v_ctorApp_2546_);
if (v_isShared_2542_ == 0)
{
lean_ctor_set(v___x_2541_, 2, v_subst_2548_);
v___x_2550_ = v___x_2541_;
goto v_reusejp_2549_;
}
else
{
lean_object* v_reuseFailAlloc_2553_; 
v_reuseFailAlloc_2553_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2553_, 0, v_mvarId_2537_);
lean_ctor_set(v_reuseFailAlloc_2553_, 1, v_fields_2538_);
lean_ctor_set(v_reuseFailAlloc_2553_, 2, v_subst_2548_);
v___x_2550_ = v_reuseFailAlloc_2553_;
goto v_reusejp_2549_;
}
v_reusejp_2549_:
{
lean_object* v___x_2551_; lean_object* v___x_2552_; 
lean_inc(v_ctorName_2543_);
v___x_2551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2551_, 0, v_ctorName_2543_);
v___x_2552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2552_, 0, v___x_2550_);
lean_ctor_set(v___x_2552_, 1, v___x_2551_);
v___y_2527_ = v___x_2552_;
goto v___jp_2526_;
}
}
}
v___jp_2526_:
{
size_t v___x_2528_; size_t v___x_2529_; lean_object* v___x_2530_; 
v___x_2528_ = ((size_t)1ULL);
v___x_2529_ = lean_usize_add(v_i_2520_, v___x_2528_);
v___x_2530_ = lean_array_uset(v_bs_x27_2525_, v_i_2520_, v___y_2527_);
v_i_2520_ = v___x_2529_;
v_bs_2521_ = v___x_2530_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0___redArg___boxed(lean_object* v_ctorNames_2555_, lean_object* v_us_2556_, lean_object* v_params_2557_, lean_object* v_majorFVarId_2558_, lean_object* v_sz_2559_, lean_object* v_i_2560_, lean_object* v_bs_2561_){
_start:
{
size_t v_sz_boxed_2562_; size_t v_i_boxed_2563_; lean_object* v_res_2564_; 
v_sz_boxed_2562_ = lean_unbox_usize(v_sz_2559_);
lean_dec(v_sz_2559_);
v_i_boxed_2563_ = lean_unbox_usize(v_i_2560_);
lean_dec(v_i_2560_);
v_res_2564_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0___redArg(v_ctorNames_2555_, v_us_2556_, v_params_2557_, v_majorFVarId_2558_, v_sz_boxed_2562_, v_i_boxed_2563_, v_bs_2561_);
lean_dec_ref(v_params_2557_);
lean_dec_ref(v_ctorNames_2555_);
return v_res_2564_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals(lean_object* v_s_2565_, lean_object* v_ctorNames_2566_, lean_object* v_majorFVarId_2567_, lean_object* v_us_2568_, lean_object* v_params_2569_){
_start:
{
size_t v_sz_2570_; size_t v___x_2571_; lean_object* v___x_2572_; 
v_sz_2570_ = lean_array_size(v_s_2565_);
v___x_2571_ = ((size_t)0ULL);
v___x_2572_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0___redArg(v_ctorNames_2566_, v_us_2568_, v_params_2569_, v_majorFVarId_2567_, v_sz_2570_, v___x_2571_, v_s_2565_);
return v___x_2572_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals___boxed(lean_object* v_s_2573_, lean_object* v_ctorNames_2574_, lean_object* v_majorFVarId_2575_, lean_object* v_us_2576_, lean_object* v_params_2577_){
_start:
{
lean_object* v_res_2578_; 
v_res_2578_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals(v_s_2573_, v_ctorNames_2574_, v_majorFVarId_2575_, v_us_2576_, v_params_2577_);
lean_dec_ref(v_params_2577_);
lean_dec_ref(v_ctorNames_2574_);
return v_res_2578_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0(lean_object* v_ctorNames_2579_, lean_object* v_us_2580_, lean_object* v_params_2581_, lean_object* v_majorFVarId_2582_, lean_object* v_as_2583_, size_t v_sz_2584_, size_t v_i_2585_, lean_object* v_bs_2586_){
_start:
{
lean_object* v___x_2587_; 
v___x_2587_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0___redArg(v_ctorNames_2579_, v_us_2580_, v_params_2581_, v_majorFVarId_2582_, v_sz_2584_, v_i_2585_, v_bs_2586_);
return v___x_2587_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0___boxed(lean_object* v_ctorNames_2588_, lean_object* v_us_2589_, lean_object* v_params_2590_, lean_object* v_majorFVarId_2591_, lean_object* v_as_2592_, lean_object* v_sz_2593_, lean_object* v_i_2594_, lean_object* v_bs_2595_){
_start:
{
size_t v_sz_boxed_2596_; size_t v_i_boxed_2597_; lean_object* v_res_2598_; 
v_sz_boxed_2596_ = lean_unbox_usize(v_sz_2593_);
lean_dec(v_sz_2593_);
v_i_boxed_2597_ = lean_unbox_usize(v_i_2594_);
lean_dec(v_i_2594_);
v_res_2598_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0(v_ctorNames_2588_, v_us_2589_, v_params_2590_, v_majorFVarId_2591_, v_as_2592_, v_sz_boxed_2596_, v_i_boxed_2597_, v_bs_2595_);
lean_dec_ref(v_as_2592_);
lean_dec_ref(v_params_2590_);
lean_dec_ref(v_ctorNames_2588_);
return v_res_2598_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_2604_; lean_object* v___x_2605_; 
v___x_2604_ = l_Lean_maxRecDepthErrorMessage;
v___x_2605_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2605_, 0, v___x_2604_);
return v___x_2605_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_2606_; lean_object* v___x_2607_; 
v___x_2606_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__3);
v___x_2607_ = l_Lean_MessageData_ofFormat(v___x_2606_);
return v___x_2607_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; 
v___x_2608_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__4);
v___x_2609_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__2));
v___x_2610_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2610_, 0, v___x_2609_);
lean_ctor_set(v___x_2610_, 1, v___x_2608_);
return v___x_2610_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg(lean_object* v_ref_2611_){
_start:
{
lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; 
v___x_2613_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__5);
v___x_2614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2614_, 0, v_ref_2611_);
lean_ctor_set(v___x_2614_, 1, v___x_2613_);
v___x_2615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2615_, 0, v___x_2614_);
return v___x_2615_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___boxed(lean_object* v_ref_2616_, lean_object* v___y_2617_){
_start:
{
lean_object* v_res_2618_; 
v_res_2618_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg(v_ref_2616_);
return v_res_2618_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0(lean_object* v_00_u03b1_2619_, lean_object* v_ref_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_){
_start:
{
lean_object* v___x_2626_; 
v___x_2626_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg(v_ref_2620_);
return v___x_2626_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___boxed(lean_object* v_00_u03b1_2627_, lean_object* v_ref_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_){
_start:
{
lean_object* v_res_2634_; 
v_res_2634_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0(v_00_u03b1_2627_, v_ref_2628_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_);
lean_dec(v___y_2632_);
lean_dec_ref(v___y_2631_);
lean_dec(v___y_2630_);
lean_dec_ref(v___y_2629_);
return v_res_2634_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_unifyEqs_x3f(lean_object* v_numEqs_2636_, lean_object* v_mvarId_2637_, lean_object* v_subst_2638_, lean_object* v_caseName_x3f_2639_, lean_object* v_a_2640_, lean_object* v_a_2641_, lean_object* v_a_2642_, lean_object* v_a_2643_){
_start:
{
lean_object* v_toCold_2645_; lean_object* v_currRecDepth_2646_; lean_object* v_ref_2647_; uint8_t v_diag_2648_; uint8_t v_suppressElabErrors_2649_; lean_object* v_maxRecDepth_2650_; lean_object* v___x_2651_; uint8_t v___x_2652_; uint8_t v___x_2698_; 
v_toCold_2645_ = lean_ctor_get(v_a_2642_, 0);
lean_inc_ref(v_toCold_2645_);
v_currRecDepth_2646_ = lean_ctor_get(v_a_2642_, 1);
lean_inc(v_currRecDepth_2646_);
v_ref_2647_ = lean_ctor_get(v_a_2642_, 2);
lean_inc(v_ref_2647_);
v_diag_2648_ = lean_ctor_get_uint8(v_a_2642_, sizeof(void*)*3);
v_suppressElabErrors_2649_ = lean_ctor_get_uint8(v_a_2642_, sizeof(void*)*3 + 1);
lean_dec_ref(v_a_2642_);
v_maxRecDepth_2650_ = lean_ctor_get(v_toCold_2645_, 3);
v___x_2651_ = lean_unsigned_to_nat(0u);
v___x_2652_ = lean_nat_dec_eq(v_numEqs_2636_, v___x_2651_);
v___x_2698_ = lean_nat_dec_eq(v_maxRecDepth_2650_, v___x_2651_);
if (v___x_2698_ == 0)
{
uint8_t v___x_2699_; 
v___x_2699_ = lean_nat_dec_eq(v_currRecDepth_2646_, v_maxRecDepth_2650_);
if (v___x_2699_ == 0)
{
goto v___jp_2653_;
}
else
{
lean_object* v___x_2700_; 
lean_dec(v_currRecDepth_2646_);
lean_dec_ref(v_toCold_2645_);
lean_dec(v_caseName_x3f_2639_);
lean_dec(v_subst_2638_);
lean_dec(v_mvarId_2637_);
lean_dec(v_numEqs_2636_);
v___x_2700_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg(v_ref_2647_);
return v___x_2700_;
}
}
else
{
goto v___jp_2653_;
}
v___jp_2653_:
{
if (v___x_2652_ == 0)
{
lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; 
v___x_2654_ = lean_unsigned_to_nat(1u);
v___x_2655_ = lean_nat_add(v_currRecDepth_2646_, v___x_2654_);
lean_dec(v_currRecDepth_2646_);
v___x_2656_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2656_, 0, v_toCold_2645_);
lean_ctor_set(v___x_2656_, 1, v___x_2655_);
lean_ctor_set(v___x_2656_, 2, v_ref_2647_);
lean_ctor_set_uint8(v___x_2656_, sizeof(void*)*3, v_diag_2648_);
lean_ctor_set_uint8(v___x_2656_, sizeof(void*)*3 + 1, v_suppressElabErrors_2649_);
v___x_2657_ = l_Lean_Meta_intro1Core(v_mvarId_2637_, v___x_2652_, v_a_2640_, v_a_2641_, v___x_2656_, v_a_2643_);
if (lean_obj_tag(v___x_2657_) == 0)
{
lean_object* v_a_2658_; lean_object* v_fst_2659_; lean_object* v_snd_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; 
v_a_2658_ = lean_ctor_get(v___x_2657_, 0);
lean_inc(v_a_2658_);
lean_dec_ref_known(v___x_2657_, 1);
v_fst_2659_ = lean_ctor_get(v_a_2658_, 0);
lean_inc(v_fst_2659_);
v_snd_2660_ = lean_ctor_get(v_a_2658_, 1);
lean_inc(v_snd_2660_);
lean_dec(v_a_2658_);
v___x_2661_ = ((lean_object*)(l_Lean_Meta_Cases_unifyEqs_x3f___closed__0));
lean_inc(v_caseName_x3f_2639_);
v___x_2662_ = l_Lean_Meta_unifyEq_x3f(v_snd_2660_, v_fst_2659_, v_subst_2638_, v___x_2661_, v_caseName_x3f_2639_, v_a_2640_, v_a_2641_, v___x_2656_, v_a_2643_);
if (lean_obj_tag(v___x_2662_) == 0)
{
lean_object* v_a_2663_; lean_object* v___x_2665_; uint8_t v_isShared_2666_; uint8_t v_isSharedCheck_2678_; 
v_a_2663_ = lean_ctor_get(v___x_2662_, 0);
v_isSharedCheck_2678_ = !lean_is_exclusive(v___x_2662_);
if (v_isSharedCheck_2678_ == 0)
{
v___x_2665_ = v___x_2662_;
v_isShared_2666_ = v_isSharedCheck_2678_;
goto v_resetjp_2664_;
}
else
{
lean_inc(v_a_2663_);
lean_dec(v___x_2662_);
v___x_2665_ = lean_box(0);
v_isShared_2666_ = v_isSharedCheck_2678_;
goto v_resetjp_2664_;
}
v_resetjp_2664_:
{
if (lean_obj_tag(v_a_2663_) == 1)
{
lean_object* v_val_2667_; lean_object* v_mvarId_2668_; lean_object* v_subst_2669_; lean_object* v_numNewEqs_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; 
lean_del_object(v___x_2665_);
v_val_2667_ = lean_ctor_get(v_a_2663_, 0);
lean_inc(v_val_2667_);
lean_dec_ref_known(v_a_2663_, 1);
v_mvarId_2668_ = lean_ctor_get(v_val_2667_, 0);
lean_inc(v_mvarId_2668_);
v_subst_2669_ = lean_ctor_get(v_val_2667_, 1);
lean_inc(v_subst_2669_);
v_numNewEqs_2670_ = lean_ctor_get(v_val_2667_, 2);
lean_inc(v_numNewEqs_2670_);
lean_dec(v_val_2667_);
v___x_2671_ = lean_nat_sub(v_numEqs_2636_, v___x_2654_);
lean_dec(v_numEqs_2636_);
v___x_2672_ = lean_nat_add(v___x_2671_, v_numNewEqs_2670_);
lean_dec(v_numNewEqs_2670_);
lean_dec(v___x_2671_);
v_numEqs_2636_ = v___x_2672_;
v_mvarId_2637_ = v_mvarId_2668_;
v_subst_2638_ = v_subst_2669_;
v_a_2642_ = v___x_2656_;
goto _start;
}
else
{
lean_object* v___x_2674_; lean_object* v___x_2676_; 
lean_dec(v_a_2663_);
lean_dec_ref_known(v___x_2656_, 3);
lean_dec(v_caseName_x3f_2639_);
lean_dec(v_numEqs_2636_);
v___x_2674_ = lean_box(0);
if (v_isShared_2666_ == 0)
{
lean_ctor_set(v___x_2665_, 0, v___x_2674_);
v___x_2676_ = v___x_2665_;
goto v_reusejp_2675_;
}
else
{
lean_object* v_reuseFailAlloc_2677_; 
v_reuseFailAlloc_2677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2677_, 0, v___x_2674_);
v___x_2676_ = v_reuseFailAlloc_2677_;
goto v_reusejp_2675_;
}
v_reusejp_2675_:
{
return v___x_2676_;
}
}
}
}
else
{
lean_object* v_a_2679_; lean_object* v___x_2681_; uint8_t v_isShared_2682_; uint8_t v_isSharedCheck_2686_; 
lean_dec_ref_known(v___x_2656_, 3);
lean_dec(v_caseName_x3f_2639_);
lean_dec(v_numEqs_2636_);
v_a_2679_ = lean_ctor_get(v___x_2662_, 0);
v_isSharedCheck_2686_ = !lean_is_exclusive(v___x_2662_);
if (v_isSharedCheck_2686_ == 0)
{
v___x_2681_ = v___x_2662_;
v_isShared_2682_ = v_isSharedCheck_2686_;
goto v_resetjp_2680_;
}
else
{
lean_inc(v_a_2679_);
lean_dec(v___x_2662_);
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
else
{
lean_object* v_a_2687_; lean_object* v___x_2689_; uint8_t v_isShared_2690_; uint8_t v_isSharedCheck_2694_; 
lean_dec_ref_known(v___x_2656_, 3);
lean_dec(v_caseName_x3f_2639_);
lean_dec(v_subst_2638_);
lean_dec(v_numEqs_2636_);
v_a_2687_ = lean_ctor_get(v___x_2657_, 0);
v_isSharedCheck_2694_ = !lean_is_exclusive(v___x_2657_);
if (v_isSharedCheck_2694_ == 0)
{
v___x_2689_ = v___x_2657_;
v_isShared_2690_ = v_isSharedCheck_2694_;
goto v_resetjp_2688_;
}
else
{
lean_inc(v_a_2687_);
lean_dec(v___x_2657_);
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
lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; 
lean_dec(v_ref_2647_);
lean_dec(v_currRecDepth_2646_);
lean_dec_ref(v_toCold_2645_);
lean_dec(v_caseName_x3f_2639_);
lean_dec(v_numEqs_2636_);
v___x_2695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2695_, 0, v_mvarId_2637_);
lean_ctor_set(v___x_2695_, 1, v_subst_2638_);
v___x_2696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2696_, 0, v___x_2695_);
v___x_2697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2697_, 0, v___x_2696_);
return v___x_2697_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_unifyEqs_x3f___boxed(lean_object* v_numEqs_2701_, lean_object* v_mvarId_2702_, lean_object* v_subst_2703_, lean_object* v_caseName_x3f_2704_, lean_object* v_a_2705_, lean_object* v_a_2706_, lean_object* v_a_2707_, lean_object* v_a_2708_, lean_object* v_a_2709_){
_start:
{
lean_object* v_res_2710_; 
v_res_2710_ = l_Lean_Meta_Cases_unifyEqs_x3f(v_numEqs_2701_, v_mvarId_2702_, v_subst_2703_, v_caseName_x3f_2704_, v_a_2705_, v_a_2706_, v_a_2707_, v_a_2708_);
lean_dec(v_a_2708_);
lean_dec(v_a_2706_);
lean_dec_ref(v_a_2705_);
return v_res_2710_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__0(lean_object* v_snd_2711_, size_t v_sz_2712_, size_t v_i_2713_, lean_object* v_bs_2714_){
_start:
{
uint8_t v___x_2715_; 
v___x_2715_ = lean_usize_dec_lt(v_i_2713_, v_sz_2712_);
if (v___x_2715_ == 0)
{
lean_dec(v_snd_2711_);
return v_bs_2714_;
}
else
{
lean_object* v_v_2716_; lean_object* v___x_2717_; lean_object* v_bs_x27_2718_; lean_object* v___x_2719_; size_t v___x_2720_; size_t v___x_2721_; lean_object* v___x_2722_; 
v_v_2716_ = lean_array_uget(v_bs_2714_, v_i_2713_);
v___x_2717_ = lean_unsigned_to_nat(0u);
v_bs_x27_2718_ = lean_array_uset(v_bs_2714_, v_i_2713_, v___x_2717_);
lean_inc(v_snd_2711_);
v___x_2719_ = l_Lean_Meta_FVarSubst_apply(v_snd_2711_, v_v_2716_);
lean_dec(v_v_2716_);
v___x_2720_ = ((size_t)1ULL);
v___x_2721_ = lean_usize_add(v_i_2713_, v___x_2720_);
v___x_2722_ = lean_array_uset(v_bs_x27_2718_, v_i_2713_, v___x_2719_);
v_i_2713_ = v___x_2721_;
v_bs_2714_ = v___x_2722_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__0___boxed(lean_object* v_snd_2724_, lean_object* v_sz_2725_, lean_object* v_i_2726_, lean_object* v_bs_2727_){
_start:
{
size_t v_sz_boxed_2728_; size_t v_i_boxed_2729_; lean_object* v_res_2730_; 
v_sz_boxed_2728_ = lean_unbox_usize(v_sz_2725_);
lean_dec(v_sz_2725_);
v_i_boxed_2729_ = lean_unbox_usize(v_i_2726_);
lean_dec(v_i_2726_);
v_res_2730_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__0(v_snd_2724_, v_sz_boxed_2728_, v_i_boxed_2729_, v_bs_2727_);
return v_res_2730_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1_spec__1(lean_object* v_numEqs_2731_, lean_object* v_as_2732_, size_t v_i_2733_, size_t v_stop_2734_, lean_object* v_b_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_){
_start:
{
uint8_t v___x_2741_; 
v___x_2741_ = lean_usize_dec_eq(v_i_2733_, v_stop_2734_);
if (v___x_2741_ == 0)
{
lean_object* v___x_2742_; lean_object* v_toInductionSubgoal_2743_; lean_object* v_ctorName_2744_; lean_object* v___x_2746_; uint8_t v_isShared_2747_; uint8_t v_isSharedCheck_2783_; 
v___x_2742_ = lean_array_uget(v_as_2732_, v_i_2733_);
v_toInductionSubgoal_2743_ = lean_ctor_get(v___x_2742_, 0);
v_ctorName_2744_ = lean_ctor_get(v___x_2742_, 1);
v_isSharedCheck_2783_ = !lean_is_exclusive(v___x_2742_);
if (v_isSharedCheck_2783_ == 0)
{
v___x_2746_ = v___x_2742_;
v_isShared_2747_ = v_isSharedCheck_2783_;
goto v_resetjp_2745_;
}
else
{
lean_inc(v_ctorName_2744_);
lean_inc(v_toInductionSubgoal_2743_);
lean_dec(v___x_2742_);
v___x_2746_ = lean_box(0);
v_isShared_2747_ = v_isSharedCheck_2783_;
goto v_resetjp_2745_;
}
v_resetjp_2745_:
{
lean_object* v_mvarId_2748_; lean_object* v_fields_2749_; lean_object* v_subst_2750_; lean_object* v___x_2752_; uint8_t v_isShared_2753_; uint8_t v_isSharedCheck_2782_; 
v_mvarId_2748_ = lean_ctor_get(v_toInductionSubgoal_2743_, 0);
v_fields_2749_ = lean_ctor_get(v_toInductionSubgoal_2743_, 1);
v_subst_2750_ = lean_ctor_get(v_toInductionSubgoal_2743_, 2);
v_isSharedCheck_2782_ = !lean_is_exclusive(v_toInductionSubgoal_2743_);
if (v_isSharedCheck_2782_ == 0)
{
v___x_2752_ = v_toInductionSubgoal_2743_;
v_isShared_2753_ = v_isSharedCheck_2782_;
goto v_resetjp_2751_;
}
else
{
lean_inc(v_subst_2750_);
lean_inc(v_fields_2749_);
lean_inc(v_mvarId_2748_);
lean_dec(v_toInductionSubgoal_2743_);
v___x_2752_ = lean_box(0);
v_isShared_2753_ = v_isSharedCheck_2782_;
goto v_resetjp_2751_;
}
v_resetjp_2751_:
{
lean_object* v___x_2754_; 
lean_inc_ref(v___y_2738_);
lean_inc(v_ctorName_2744_);
lean_inc(v_numEqs_2731_);
v___x_2754_ = l_Lean_Meta_Cases_unifyEqs_x3f(v_numEqs_2731_, v_mvarId_2748_, v_subst_2750_, v_ctorName_2744_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_);
if (lean_obj_tag(v___x_2754_) == 0)
{
lean_object* v_a_2755_; lean_object* v_a_2757_; 
v_a_2755_ = lean_ctor_get(v___x_2754_, 0);
lean_inc(v_a_2755_);
lean_dec_ref_known(v___x_2754_, 1);
if (lean_obj_tag(v_a_2755_) == 0)
{
lean_del_object(v___x_2752_);
lean_dec_ref(v_fields_2749_);
lean_del_object(v___x_2746_);
lean_dec(v_ctorName_2744_);
v_a_2757_ = v_b_2735_;
goto v___jp_2756_;
}
else
{
lean_object* v_val_2761_; lean_object* v_fst_2762_; lean_object* v_snd_2763_; size_t v_sz_2764_; size_t v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2768_; 
v_val_2761_ = lean_ctor_get(v_a_2755_, 0);
lean_inc(v_val_2761_);
lean_dec_ref_known(v_a_2755_, 1);
v_fst_2762_ = lean_ctor_get(v_val_2761_, 0);
lean_inc(v_fst_2762_);
v_snd_2763_ = lean_ctor_get(v_val_2761_, 1);
lean_inc_n(v_snd_2763_, 2);
lean_dec(v_val_2761_);
v_sz_2764_ = lean_array_size(v_fields_2749_);
v___x_2765_ = ((size_t)0ULL);
v___x_2766_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__0(v_snd_2763_, v_sz_2764_, v___x_2765_, v_fields_2749_);
if (v_isShared_2753_ == 0)
{
lean_ctor_set(v___x_2752_, 2, v_snd_2763_);
lean_ctor_set(v___x_2752_, 1, v___x_2766_);
lean_ctor_set(v___x_2752_, 0, v_fst_2762_);
v___x_2768_ = v___x_2752_;
goto v_reusejp_2767_;
}
else
{
lean_object* v_reuseFailAlloc_2773_; 
v_reuseFailAlloc_2773_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2773_, 0, v_fst_2762_);
lean_ctor_set(v_reuseFailAlloc_2773_, 1, v___x_2766_);
lean_ctor_set(v_reuseFailAlloc_2773_, 2, v_snd_2763_);
v___x_2768_ = v_reuseFailAlloc_2773_;
goto v_reusejp_2767_;
}
v_reusejp_2767_:
{
lean_object* v___x_2770_; 
if (v_isShared_2747_ == 0)
{
lean_ctor_set(v___x_2746_, 0, v___x_2768_);
v___x_2770_ = v___x_2746_;
goto v_reusejp_2769_;
}
else
{
lean_object* v_reuseFailAlloc_2772_; 
v_reuseFailAlloc_2772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2772_, 0, v___x_2768_);
lean_ctor_set(v_reuseFailAlloc_2772_, 1, v_ctorName_2744_);
v___x_2770_ = v_reuseFailAlloc_2772_;
goto v_reusejp_2769_;
}
v_reusejp_2769_:
{
lean_object* v___x_2771_; 
v___x_2771_ = lean_array_push(v_b_2735_, v___x_2770_);
v_a_2757_ = v___x_2771_;
goto v___jp_2756_;
}
}
}
v___jp_2756_:
{
size_t v___x_2758_; size_t v___x_2759_; 
v___x_2758_ = ((size_t)1ULL);
v___x_2759_ = lean_usize_add(v_i_2733_, v___x_2758_);
v_i_2733_ = v___x_2759_;
v_b_2735_ = v_a_2757_;
goto _start;
}
}
else
{
lean_object* v_a_2774_; lean_object* v___x_2776_; uint8_t v_isShared_2777_; uint8_t v_isSharedCheck_2781_; 
lean_del_object(v___x_2752_);
lean_dec_ref(v_fields_2749_);
lean_del_object(v___x_2746_);
lean_dec(v_ctorName_2744_);
lean_dec_ref(v_b_2735_);
lean_dec(v_numEqs_2731_);
v_a_2774_ = lean_ctor_get(v___x_2754_, 0);
v_isSharedCheck_2781_ = !lean_is_exclusive(v___x_2754_);
if (v_isSharedCheck_2781_ == 0)
{
v___x_2776_ = v___x_2754_;
v_isShared_2777_ = v_isSharedCheck_2781_;
goto v_resetjp_2775_;
}
else
{
lean_inc(v_a_2774_);
lean_dec(v___x_2754_);
v___x_2776_ = lean_box(0);
v_isShared_2777_ = v_isSharedCheck_2781_;
goto v_resetjp_2775_;
}
v_resetjp_2775_:
{
lean_object* v___x_2779_; 
if (v_isShared_2777_ == 0)
{
v___x_2779_ = v___x_2776_;
goto v_reusejp_2778_;
}
else
{
lean_object* v_reuseFailAlloc_2780_; 
v_reuseFailAlloc_2780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2780_, 0, v_a_2774_);
v___x_2779_ = v_reuseFailAlloc_2780_;
goto v_reusejp_2778_;
}
v_reusejp_2778_:
{
return v___x_2779_;
}
}
}
}
}
}
else
{
lean_object* v___x_2784_; 
lean_dec(v_numEqs_2731_);
v___x_2784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2784_, 0, v_b_2735_);
return v___x_2784_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1_spec__1___boxed(lean_object* v_numEqs_2785_, lean_object* v_as_2786_, lean_object* v_i_2787_, lean_object* v_stop_2788_, lean_object* v_b_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_){
_start:
{
size_t v_i_boxed_2795_; size_t v_stop_boxed_2796_; lean_object* v_res_2797_; 
v_i_boxed_2795_ = lean_unbox_usize(v_i_2787_);
lean_dec(v_i_2787_);
v_stop_boxed_2796_ = lean_unbox_usize(v_stop_2788_);
lean_dec(v_stop_2788_);
v_res_2797_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1_spec__1(v_numEqs_2785_, v_as_2786_, v_i_boxed_2795_, v_stop_boxed_2796_, v_b_2789_, v___y_2790_, v___y_2791_, v___y_2792_, v___y_2793_);
lean_dec(v___y_2793_);
lean_dec_ref(v___y_2792_);
lean_dec(v___y_2791_);
lean_dec_ref(v___y_2790_);
lean_dec_ref(v_as_2786_);
return v_res_2797_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1(lean_object* v_numEqs_2800_, lean_object* v_as_2801_, lean_object* v_start_2802_, lean_object* v_stop_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_){
_start:
{
lean_object* v___x_2809_; uint8_t v___x_2810_; 
v___x_2809_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1___closed__0));
v___x_2810_ = lean_nat_dec_lt(v_start_2802_, v_stop_2803_);
if (v___x_2810_ == 0)
{
lean_object* v___x_2811_; 
lean_dec(v_numEqs_2800_);
v___x_2811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2811_, 0, v___x_2809_);
return v___x_2811_;
}
else
{
lean_object* v___x_2812_; uint8_t v___x_2813_; 
v___x_2812_ = lean_array_get_size(v_as_2801_);
v___x_2813_ = lean_nat_dec_le(v_stop_2803_, v___x_2812_);
if (v___x_2813_ == 0)
{
uint8_t v___x_2814_; 
v___x_2814_ = lean_nat_dec_lt(v_start_2802_, v___x_2812_);
if (v___x_2814_ == 0)
{
lean_object* v___x_2815_; 
lean_dec(v_numEqs_2800_);
v___x_2815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2815_, 0, v___x_2809_);
return v___x_2815_;
}
else
{
size_t v___x_2816_; size_t v___x_2817_; lean_object* v___x_2818_; 
v___x_2816_ = lean_usize_of_nat(v_start_2802_);
v___x_2817_ = lean_usize_of_nat(v___x_2812_);
v___x_2818_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1_spec__1(v_numEqs_2800_, v_as_2801_, v___x_2816_, v___x_2817_, v___x_2809_, v___y_2804_, v___y_2805_, v___y_2806_, v___y_2807_);
return v___x_2818_;
}
}
else
{
size_t v___x_2819_; size_t v___x_2820_; lean_object* v___x_2821_; 
v___x_2819_ = lean_usize_of_nat(v_start_2802_);
v___x_2820_ = lean_usize_of_nat(v_stop_2803_);
v___x_2821_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1_spec__1(v_numEqs_2800_, v_as_2801_, v___x_2819_, v___x_2820_, v___x_2809_, v___y_2804_, v___y_2805_, v___y_2806_, v___y_2807_);
return v___x_2821_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1___boxed(lean_object* v_numEqs_2822_, lean_object* v_as_2823_, lean_object* v_start_2824_, lean_object* v_stop_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_){
_start:
{
lean_object* v_res_2831_; 
v_res_2831_ = l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1(v_numEqs_2822_, v_as_2823_, v_start_2824_, v_stop_2825_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_);
lean_dec(v___y_2829_);
lean_dec_ref(v___y_2828_);
lean_dec(v___y_2827_);
lean_dec_ref(v___y_2826_);
lean_dec(v_stop_2825_);
lean_dec(v_start_2824_);
lean_dec_ref(v_as_2823_);
return v_res_2831_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs(lean_object* v_numEqs_2832_, lean_object* v_subgoals_2833_, lean_object* v_a_2834_, lean_object* v_a_2835_, lean_object* v_a_2836_, lean_object* v_a_2837_){
_start:
{
lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; 
v___x_2839_ = lean_unsigned_to_nat(0u);
v___x_2840_ = lean_array_get_size(v_subgoals_2833_);
v___x_2841_ = l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1(v_numEqs_2832_, v_subgoals_2833_, v___x_2839_, v___x_2840_, v_a_2834_, v_a_2835_, v_a_2836_, v_a_2837_);
return v___x_2841_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs___boxed(lean_object* v_numEqs_2842_, lean_object* v_subgoals_2843_, lean_object* v_a_2844_, lean_object* v_a_2845_, lean_object* v_a_2846_, lean_object* v_a_2847_, lean_object* v_a_2848_){
_start:
{
lean_object* v_res_2849_; 
v_res_2849_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs(v_numEqs_2842_, v_subgoals_2843_, v_a_2844_, v_a_2845_, v_a_2846_, v_a_2847_);
lean_dec(v_a_2847_);
lean_dec_ref(v_a_2846_);
lean_dec(v_a_2845_);
lean_dec_ref(v_a_2844_);
lean_dec_ref(v_subgoals_2843_);
return v_res_2849_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0(lean_object* v___x_2861_, lean_object* v_mvarId_2862_, lean_object* v_majorFVarId_2863_, lean_object* v_givenNames_2864_, lean_object* v_ctx_2865_, uint8_t v_useNatCasesAuxOn_2866_, lean_object* v_interestingCtors_x3f_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_){
_start:
{
lean_object* v___x_2873_; 
lean_inc(v___y_2871_);
lean_inc_ref(v___y_2870_);
lean_inc(v___y_2869_);
lean_inc_ref(v___y_2868_);
v___x_2873_ = lean_infer_type(v___x_2861_, v___y_2868_, v___y_2869_, v___y_2870_, v___y_2871_);
if (lean_obj_tag(v___x_2873_) == 0)
{
lean_object* v_a_2874_; lean_object* v___x_2875_; 
v_a_2874_ = lean_ctor_get(v___x_2873_, 0);
lean_inc(v_a_2874_);
lean_dec_ref_known(v___x_2873_, 1);
v___x_2875_ = l_Lean_Meta_getInductiveUniverseAndParams(v_a_2874_, v___y_2868_, v___y_2869_, v___y_2870_, v___y_2871_);
if (lean_obj_tag(v___x_2875_) == 0)
{
lean_object* v_a_2876_; lean_object* v_fst_2877_; lean_object* v_snd_2878_; lean_object* v___y_2880_; lean_object* v___y_2881_; lean_object* v___y_2882_; lean_object* v___y_2883_; lean_object* v___y_2884_; lean_object* v___y_2907_; lean_object* v___y_2908_; lean_object* v___y_2909_; lean_object* v___y_2910_; lean_object* v___y_2916_; lean_object* v___y_2917_; lean_object* v___y_2918_; lean_object* v___y_2919_; 
v_a_2876_ = lean_ctor_get(v___x_2875_, 0);
lean_inc(v_a_2876_);
lean_dec_ref_known(v___x_2875_, 1);
v_fst_2877_ = lean_ctor_get(v_a_2876_, 0);
lean_inc(v_fst_2877_);
v_snd_2878_ = lean_ctor_get(v_a_2876_, 1);
lean_inc(v_snd_2878_);
lean_dec(v_a_2876_);
if (lean_obj_tag(v_interestingCtors_x3f_2867_) == 1)
{
lean_object* v_val_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v_inductiveVal_2932_; lean_object* v_toConstantVal_2933_; lean_object* v_env_2934_; lean_object* v_ctors_2935_; lean_object* v_name_2936_; uint8_t v___y_2938_; lean_object* v___x_2972_; uint8_t v___x_2973_; uint8_t v___x_2974_; 
v_val_2929_ = lean_ctor_get(v_interestingCtors_x3f_2867_, 0);
lean_inc(v_val_2929_);
lean_dec_ref_known(v_interestingCtors_x3f_2867_, 1);
v___x_2930_ = lean_st_ref_get(v___y_2871_);
v___x_2931_ = lean_st_ref_get(v___y_2871_);
v_inductiveVal_2932_ = lean_ctor_get(v_ctx_2865_, 0);
v_toConstantVal_2933_ = lean_ctor_get(v_inductiveVal_2932_, 0);
v_env_2934_ = lean_ctor_get(v___x_2930_, 0);
lean_inc_ref(v_env_2934_);
lean_dec(v___x_2930_);
v_ctors_2935_ = lean_ctor_get(v_inductiveVal_2932_, 4);
v_name_2936_ = lean_ctor_get(v_toConstantVal_2933_, 0);
v___x_2972_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__5));
v___x_2973_ = 1;
v___x_2974_ = l_Lean_Environment_contains(v_env_2934_, v___x_2972_, v___x_2973_);
if (v___x_2974_ == 0)
{
lean_dec(v___x_2931_);
v___y_2938_ = v___x_2974_;
goto v___jp_2937_;
}
else
{
lean_object* v_env_2975_; lean_object* v___x_2976_; uint8_t v___x_2977_; 
v_env_2975_ = lean_ctor_get(v___x_2931_, 0);
lean_inc_ref(v_env_2975_);
lean_dec(v___x_2931_);
lean_inc(v_name_2936_);
v___x_2976_ = l_Lean_mkCtorIdxName(v_name_2936_);
v___x_2977_ = l_Lean_Environment_contains(v_env_2975_, v___x_2976_, v___x_2973_);
v___y_2938_ = v___x_2977_;
goto v___jp_2937_;
}
v___jp_2937_:
{
if (v___y_2938_ == 0)
{
lean_dec(v_val_2929_);
v___y_2916_ = v___y_2868_;
v___y_2917_ = v___y_2869_;
v___y_2918_ = v___y_2870_;
v___y_2919_ = v___y_2871_;
goto v___jp_2915_;
}
else
{
lean_object* v___x_2939_; lean_object* v___x_2940_; uint8_t v___x_2941_; 
v___x_2939_ = lean_array_get_size(v_val_2929_);
v___x_2940_ = lean_unsigned_to_nat(0u);
v___x_2941_ = lean_nat_dec_eq(v___x_2939_, v___x_2940_);
if (v___x_2941_ == 0)
{
lean_object* v___x_2942_; uint8_t v___x_2943_; 
v___x_2942_ = l_List_lengthTR___redArg(v_ctors_2935_);
v___x_2943_ = lean_nat_dec_lt(v___x_2939_, v___x_2942_);
lean_dec(v___x_2942_);
if (v___x_2943_ == 0)
{
lean_dec(v_val_2929_);
v___y_2916_ = v___y_2868_;
v___y_2917_ = v___y_2869_;
v___y_2918_ = v___y_2870_;
v___y_2919_ = v___y_2871_;
goto v___jp_2915_;
}
else
{
lean_object* v___x_2944_; 
lean_inc(v_name_2936_);
lean_dec_ref(v_ctx_2865_);
lean_inc(v_val_2929_);
v___x_2944_ = l_Lean_Meta_mkSparseCasesOn(v_name_2936_, v_val_2929_, v___y_2868_, v___y_2869_, v___y_2870_, v___y_2871_);
if (lean_obj_tag(v___x_2944_) == 0)
{
lean_object* v_a_2945_; lean_object* v___x_2946_; 
v_a_2945_ = lean_ctor_get(v___x_2944_, 0);
lean_inc(v_a_2945_);
lean_dec_ref_known(v___x_2944_, 1);
lean_inc(v_majorFVarId_2863_);
v___x_2946_ = l_Lean_MVarId_induction(v_mvarId_2862_, v_majorFVarId_2863_, v_a_2945_, v_givenNames_2864_, v___y_2868_, v___y_2869_, v___y_2870_, v___y_2871_);
lean_dec(v___y_2871_);
lean_dec_ref(v___y_2870_);
lean_dec(v___y_2869_);
lean_dec_ref(v___y_2868_);
if (lean_obj_tag(v___x_2946_) == 0)
{
lean_object* v_a_2947_; lean_object* v___x_2949_; uint8_t v_isShared_2950_; uint8_t v_isSharedCheck_2955_; 
v_a_2947_ = lean_ctor_get(v___x_2946_, 0);
v_isSharedCheck_2955_ = !lean_is_exclusive(v___x_2946_);
if (v_isSharedCheck_2955_ == 0)
{
v___x_2949_ = v___x_2946_;
v_isShared_2950_ = v_isSharedCheck_2955_;
goto v_resetjp_2948_;
}
else
{
lean_inc(v_a_2947_);
lean_dec(v___x_2946_);
v___x_2949_ = lean_box(0);
v_isShared_2950_ = v_isSharedCheck_2955_;
goto v_resetjp_2948_;
}
v_resetjp_2948_:
{
lean_object* v___x_2951_; lean_object* v___x_2953_; 
v___x_2951_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals(v_a_2947_, v_val_2929_, v_majorFVarId_2863_, v_fst_2877_, v_snd_2878_);
lean_dec(v_snd_2878_);
lean_dec(v_val_2929_);
if (v_isShared_2950_ == 0)
{
lean_ctor_set(v___x_2949_, 0, v___x_2951_);
v___x_2953_ = v___x_2949_;
goto v_reusejp_2952_;
}
else
{
lean_object* v_reuseFailAlloc_2954_; 
v_reuseFailAlloc_2954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2954_, 0, v___x_2951_);
v___x_2953_ = v_reuseFailAlloc_2954_;
goto v_reusejp_2952_;
}
v_reusejp_2952_:
{
return v___x_2953_;
}
}
}
else
{
lean_object* v_a_2956_; lean_object* v___x_2958_; uint8_t v_isShared_2959_; uint8_t v_isSharedCheck_2963_; 
lean_dec(v_val_2929_);
lean_dec(v_snd_2878_);
lean_dec(v_fst_2877_);
lean_dec(v_majorFVarId_2863_);
v_a_2956_ = lean_ctor_get(v___x_2946_, 0);
v_isSharedCheck_2963_ = !lean_is_exclusive(v___x_2946_);
if (v_isSharedCheck_2963_ == 0)
{
v___x_2958_ = v___x_2946_;
v_isShared_2959_ = v_isSharedCheck_2963_;
goto v_resetjp_2957_;
}
else
{
lean_inc(v_a_2956_);
lean_dec(v___x_2946_);
v___x_2958_ = lean_box(0);
v_isShared_2959_ = v_isSharedCheck_2963_;
goto v_resetjp_2957_;
}
v_resetjp_2957_:
{
lean_object* v___x_2961_; 
if (v_isShared_2959_ == 0)
{
v___x_2961_ = v___x_2958_;
goto v_reusejp_2960_;
}
else
{
lean_object* v_reuseFailAlloc_2962_; 
v_reuseFailAlloc_2962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2962_, 0, v_a_2956_);
v___x_2961_ = v_reuseFailAlloc_2962_;
goto v_reusejp_2960_;
}
v_reusejp_2960_:
{
return v___x_2961_;
}
}
}
}
else
{
lean_object* v_a_2964_; lean_object* v___x_2966_; uint8_t v_isShared_2967_; uint8_t v_isSharedCheck_2971_; 
lean_dec(v_val_2929_);
lean_dec(v_snd_2878_);
lean_dec(v_fst_2877_);
lean_dec(v___y_2871_);
lean_dec_ref(v___y_2870_);
lean_dec(v___y_2869_);
lean_dec_ref(v___y_2868_);
lean_dec_ref(v_givenNames_2864_);
lean_dec(v_majorFVarId_2863_);
lean_dec(v_mvarId_2862_);
v_a_2964_ = lean_ctor_get(v___x_2944_, 0);
v_isSharedCheck_2971_ = !lean_is_exclusive(v___x_2944_);
if (v_isSharedCheck_2971_ == 0)
{
v___x_2966_ = v___x_2944_;
v_isShared_2967_ = v_isSharedCheck_2971_;
goto v_resetjp_2965_;
}
else
{
lean_inc(v_a_2964_);
lean_dec(v___x_2944_);
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
}
else
{
lean_dec(v_val_2929_);
v___y_2916_ = v___y_2868_;
v___y_2917_ = v___y_2869_;
v___y_2918_ = v___y_2870_;
v___y_2919_ = v___y_2871_;
goto v___jp_2915_;
}
}
}
}
else
{
lean_dec(v_interestingCtors_x3f_2867_);
v___y_2916_ = v___y_2868_;
v___y_2917_ = v___y_2869_;
v___y_2918_ = v___y_2870_;
v___y_2919_ = v___y_2871_;
goto v___jp_2915_;
}
v___jp_2879_:
{
lean_object* v___x_2885_; 
lean_inc(v_majorFVarId_2863_);
v___x_2885_ = l_Lean_MVarId_induction(v_mvarId_2862_, v_majorFVarId_2863_, v___y_2884_, v_givenNames_2864_, v___y_2883_, v___y_2882_, v___y_2881_, v___y_2880_);
lean_dec(v___y_2880_);
lean_dec_ref(v___y_2881_);
lean_dec(v___y_2882_);
lean_dec_ref(v___y_2883_);
if (lean_obj_tag(v___x_2885_) == 0)
{
lean_object* v_inductiveVal_2886_; lean_object* v_a_2887_; lean_object* v___x_2889_; uint8_t v_isShared_2890_; uint8_t v_isSharedCheck_2897_; 
v_inductiveVal_2886_ = lean_ctor_get(v_ctx_2865_, 0);
lean_inc_ref(v_inductiveVal_2886_);
lean_dec_ref(v_ctx_2865_);
v_a_2887_ = lean_ctor_get(v___x_2885_, 0);
v_isSharedCheck_2897_ = !lean_is_exclusive(v___x_2885_);
if (v_isSharedCheck_2897_ == 0)
{
v___x_2889_ = v___x_2885_;
v_isShared_2890_ = v_isSharedCheck_2897_;
goto v_resetjp_2888_;
}
else
{
lean_inc(v_a_2887_);
lean_dec(v___x_2885_);
v___x_2889_ = lean_box(0);
v_isShared_2890_ = v_isSharedCheck_2897_;
goto v_resetjp_2888_;
}
v_resetjp_2888_:
{
lean_object* v_ctors_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2895_; 
v_ctors_2891_ = lean_ctor_get(v_inductiveVal_2886_, 4);
lean_inc(v_ctors_2891_);
lean_dec_ref(v_inductiveVal_2886_);
v___x_2892_ = lean_array_mk(v_ctors_2891_);
v___x_2893_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals(v_a_2887_, v___x_2892_, v_majorFVarId_2863_, v_fst_2877_, v_snd_2878_);
lean_dec(v_snd_2878_);
lean_dec_ref(v___x_2892_);
if (v_isShared_2890_ == 0)
{
lean_ctor_set(v___x_2889_, 0, v___x_2893_);
v___x_2895_ = v___x_2889_;
goto v_reusejp_2894_;
}
else
{
lean_object* v_reuseFailAlloc_2896_; 
v_reuseFailAlloc_2896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2896_, 0, v___x_2893_);
v___x_2895_ = v_reuseFailAlloc_2896_;
goto v_reusejp_2894_;
}
v_reusejp_2894_:
{
return v___x_2895_;
}
}
}
else
{
lean_object* v_a_2898_; lean_object* v___x_2900_; uint8_t v_isShared_2901_; uint8_t v_isSharedCheck_2905_; 
lean_dec(v_snd_2878_);
lean_dec(v_fst_2877_);
lean_dec_ref(v_ctx_2865_);
lean_dec(v_majorFVarId_2863_);
v_a_2898_ = lean_ctor_get(v___x_2885_, 0);
v_isSharedCheck_2905_ = !lean_is_exclusive(v___x_2885_);
if (v_isSharedCheck_2905_ == 0)
{
v___x_2900_ = v___x_2885_;
v_isShared_2901_ = v_isSharedCheck_2905_;
goto v_resetjp_2899_;
}
else
{
lean_inc(v_a_2898_);
lean_dec(v___x_2885_);
v___x_2900_ = lean_box(0);
v_isShared_2901_ = v_isSharedCheck_2905_;
goto v_resetjp_2899_;
}
v_resetjp_2899_:
{
lean_object* v___x_2903_; 
if (v_isShared_2901_ == 0)
{
v___x_2903_ = v___x_2900_;
goto v_reusejp_2902_;
}
else
{
lean_object* v_reuseFailAlloc_2904_; 
v_reuseFailAlloc_2904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2904_, 0, v_a_2898_);
v___x_2903_ = v_reuseFailAlloc_2904_;
goto v_reusejp_2902_;
}
v_reusejp_2902_:
{
return v___x_2903_;
}
}
}
}
v___jp_2906_:
{
lean_object* v_inductiveVal_2911_; lean_object* v_toConstantVal_2912_; lean_object* v_name_2913_; lean_object* v___x_2914_; 
v_inductiveVal_2911_ = lean_ctor_get(v_ctx_2865_, 0);
v_toConstantVal_2912_ = lean_ctor_get(v_inductiveVal_2911_, 0);
v_name_2913_ = lean_ctor_get(v_toConstantVal_2912_, 0);
lean_inc(v_name_2913_);
v___x_2914_ = l_Lean_mkCasesOnName(v_name_2913_);
v___y_2880_ = v___y_2907_;
v___y_2881_ = v___y_2908_;
v___y_2882_ = v___y_2909_;
v___y_2883_ = v___y_2910_;
v___y_2884_ = v___x_2914_;
goto v___jp_2879_;
}
v___jp_2915_:
{
lean_object* v___x_2920_; 
v___x_2920_ = lean_st_ref_get(v___y_2919_);
if (v_useNatCasesAuxOn_2866_ == 0)
{
lean_dec(v___x_2920_);
v___y_2907_ = v___y_2919_;
v___y_2908_ = v___y_2918_;
v___y_2909_ = v___y_2917_;
v___y_2910_ = v___y_2916_;
goto v___jp_2906_;
}
else
{
lean_object* v_inductiveVal_2921_; lean_object* v_toConstantVal_2922_; lean_object* v_env_2923_; lean_object* v_name_2924_; lean_object* v___x_2925_; uint8_t v___x_2926_; 
v_inductiveVal_2921_ = lean_ctor_get(v_ctx_2865_, 0);
v_toConstantVal_2922_ = lean_ctor_get(v_inductiveVal_2921_, 0);
v_env_2923_ = lean_ctor_get(v___x_2920_, 0);
lean_inc_ref(v_env_2923_);
lean_dec(v___x_2920_);
v_name_2924_ = lean_ctor_get(v_toConstantVal_2922_, 0);
v___x_2925_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__1));
v___x_2926_ = lean_name_eq(v_name_2924_, v___x_2925_);
if (v___x_2926_ == 0)
{
lean_dec_ref(v_env_2923_);
v___y_2907_ = v___y_2919_;
v___y_2908_ = v___y_2918_;
v___y_2909_ = v___y_2917_;
v___y_2910_ = v___y_2916_;
goto v___jp_2906_;
}
else
{
lean_object* v___x_2927_; uint8_t v___x_2928_; 
v___x_2927_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__3));
v___x_2928_ = l_Lean_Environment_contains(v_env_2923_, v___x_2927_, v___x_2926_);
if (v___x_2928_ == 0)
{
v___y_2907_ = v___y_2919_;
v___y_2908_ = v___y_2918_;
v___y_2909_ = v___y_2917_;
v___y_2910_ = v___y_2916_;
goto v___jp_2906_;
}
else
{
v___y_2880_ = v___y_2919_;
v___y_2881_ = v___y_2918_;
v___y_2882_ = v___y_2917_;
v___y_2883_ = v___y_2916_;
v___y_2884_ = v___x_2927_;
goto v___jp_2879_;
}
}
}
}
}
else
{
lean_object* v_a_2978_; lean_object* v___x_2980_; uint8_t v_isShared_2981_; uint8_t v_isSharedCheck_2985_; 
lean_dec(v___y_2871_);
lean_dec_ref(v___y_2870_);
lean_dec(v___y_2869_);
lean_dec_ref(v___y_2868_);
lean_dec(v_interestingCtors_x3f_2867_);
lean_dec_ref(v_ctx_2865_);
lean_dec_ref(v_givenNames_2864_);
lean_dec(v_majorFVarId_2863_);
lean_dec(v_mvarId_2862_);
v_a_2978_ = lean_ctor_get(v___x_2875_, 0);
v_isSharedCheck_2985_ = !lean_is_exclusive(v___x_2875_);
if (v_isSharedCheck_2985_ == 0)
{
v___x_2980_ = v___x_2875_;
v_isShared_2981_ = v_isSharedCheck_2985_;
goto v_resetjp_2979_;
}
else
{
lean_inc(v_a_2978_);
lean_dec(v___x_2875_);
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
lean_dec(v___y_2871_);
lean_dec_ref(v___y_2870_);
lean_dec(v___y_2869_);
lean_dec_ref(v___y_2868_);
lean_dec(v_interestingCtors_x3f_2867_);
lean_dec_ref(v_ctx_2865_);
lean_dec_ref(v_givenNames_2864_);
lean_dec(v_majorFVarId_2863_);
lean_dec(v_mvarId_2862_);
v_a_2986_ = lean_ctor_get(v___x_2873_, 0);
v_isSharedCheck_2993_ = !lean_is_exclusive(v___x_2873_);
if (v_isSharedCheck_2993_ == 0)
{
v___x_2988_ = v___x_2873_;
v_isShared_2989_ = v_isSharedCheck_2993_;
goto v_resetjp_2987_;
}
else
{
lean_inc(v_a_2986_);
lean_dec(v___x_2873_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___boxed(lean_object* v___x_2994_, lean_object* v_mvarId_2995_, lean_object* v_majorFVarId_2996_, lean_object* v_givenNames_2997_, lean_object* v_ctx_2998_, lean_object* v_useNatCasesAuxOn_2999_, lean_object* v_interestingCtors_x3f_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_){
_start:
{
uint8_t v_useNatCasesAuxOn_boxed_3006_; lean_object* v_res_3007_; 
v_useNatCasesAuxOn_boxed_3006_ = lean_unbox(v_useNatCasesAuxOn_2999_);
v_res_3007_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0(v___x_2994_, v_mvarId_2995_, v_majorFVarId_2996_, v_givenNames_2997_, v_ctx_2998_, v_useNatCasesAuxOn_boxed_3006_, v_interestingCtors_x3f_3000_, v___y_3001_, v___y_3002_, v___y_3003_, v___y_3004_);
return v_res_3007_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn(lean_object* v_mvarId_3008_, lean_object* v_majorFVarId_3009_, lean_object* v_givenNames_3010_, lean_object* v_ctx_3011_, uint8_t v_useNatCasesAuxOn_3012_, lean_object* v_interestingCtors_x3f_3013_, lean_object* v_a_3014_, lean_object* v_a_3015_, lean_object* v_a_3016_, lean_object* v_a_3017_){
_start:
{
lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___f_3021_; lean_object* v___x_3022_; 
lean_inc(v_majorFVarId_3009_);
v___x_3019_ = l_Lean_mkFVar(v_majorFVarId_3009_);
v___x_3020_ = lean_box(v_useNatCasesAuxOn_3012_);
lean_inc(v_mvarId_3008_);
v___f_3021_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___boxed), 12, 7);
lean_closure_set(v___f_3021_, 0, v___x_3019_);
lean_closure_set(v___f_3021_, 1, v_mvarId_3008_);
lean_closure_set(v___f_3021_, 2, v_majorFVarId_3009_);
lean_closure_set(v___f_3021_, 3, v_givenNames_3010_);
lean_closure_set(v___f_3021_, 4, v_ctx_3011_);
lean_closure_set(v___f_3021_, 5, v___x_3020_);
lean_closure_set(v___f_3021_, 6, v_interestingCtors_x3f_3013_);
v___x_3022_ = l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2___redArg(v_mvarId_3008_, v___f_3021_, v_a_3014_, v_a_3015_, v_a_3016_, v_a_3017_);
return v___x_3022_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___boxed(lean_object* v_mvarId_3023_, lean_object* v_majorFVarId_3024_, lean_object* v_givenNames_3025_, lean_object* v_ctx_3026_, lean_object* v_useNatCasesAuxOn_3027_, lean_object* v_interestingCtors_x3f_3028_, lean_object* v_a_3029_, lean_object* v_a_3030_, lean_object* v_a_3031_, lean_object* v_a_3032_, lean_object* v_a_3033_){
_start:
{
uint8_t v_useNatCasesAuxOn_boxed_3034_; lean_object* v_res_3035_; 
v_useNatCasesAuxOn_boxed_3034_ = lean_unbox(v_useNatCasesAuxOn_3027_);
v_res_3035_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn(v_mvarId_3023_, v_majorFVarId_3024_, v_givenNames_3025_, v_ctx_3026_, v_useNatCasesAuxOn_boxed_3034_, v_interestingCtors_x3f_3028_, v_a_3029_, v_a_3030_, v_a_3031_, v_a_3032_);
lean_dec(v_a_3032_);
lean_dec_ref(v_a_3031_);
lean_dec(v_a_3030_);
lean_dec_ref(v_a_3029_);
return v_res_3035_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0___closed__0(void){
_start:
{
lean_object* v___x_3036_; double v___x_3037_; 
v___x_3036_ = lean_unsigned_to_nat(0u);
v___x_3037_ = lean_float_of_nat(v___x_3036_);
return v___x_3037_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0(lean_object* v_cls_3041_, lean_object* v_msg_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_){
_start:
{
lean_object* v_ref_3048_; lean_object* v___x_3049_; lean_object* v_a_3050_; lean_object* v___x_3052_; uint8_t v_isShared_3053_; uint8_t v_isSharedCheck_3094_; 
v_ref_3048_ = lean_ctor_get(v___y_3045_, 2);
v___x_3049_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected_spec__0_spec__0(v_msg_3042_, v___y_3043_, v___y_3044_, v___y_3045_, v___y_3046_);
v_a_3050_ = lean_ctor_get(v___x_3049_, 0);
v_isSharedCheck_3094_ = !lean_is_exclusive(v___x_3049_);
if (v_isSharedCheck_3094_ == 0)
{
v___x_3052_ = v___x_3049_;
v_isShared_3053_ = v_isSharedCheck_3094_;
goto v_resetjp_3051_;
}
else
{
lean_inc(v_a_3050_);
lean_dec(v___x_3049_);
v___x_3052_ = lean_box(0);
v_isShared_3053_ = v_isSharedCheck_3094_;
goto v_resetjp_3051_;
}
v_resetjp_3051_:
{
lean_object* v___x_3054_; lean_object* v_traceState_3055_; lean_object* v_env_3056_; lean_object* v_nextMacroScope_3057_; lean_object* v_ngen_3058_; lean_object* v_auxDeclNGen_3059_; lean_object* v_cache_3060_; lean_object* v_messages_3061_; lean_object* v_infoState_3062_; lean_object* v_snapshotTasks_3063_; lean_object* v___x_3065_; uint8_t v_isShared_3066_; uint8_t v_isSharedCheck_3093_; 
v___x_3054_ = lean_st_ref_take(v___y_3046_);
v_traceState_3055_ = lean_ctor_get(v___x_3054_, 4);
v_env_3056_ = lean_ctor_get(v___x_3054_, 0);
v_nextMacroScope_3057_ = lean_ctor_get(v___x_3054_, 1);
v_ngen_3058_ = lean_ctor_get(v___x_3054_, 2);
v_auxDeclNGen_3059_ = lean_ctor_get(v___x_3054_, 3);
v_cache_3060_ = lean_ctor_get(v___x_3054_, 5);
v_messages_3061_ = lean_ctor_get(v___x_3054_, 6);
v_infoState_3062_ = lean_ctor_get(v___x_3054_, 7);
v_snapshotTasks_3063_ = lean_ctor_get(v___x_3054_, 8);
v_isSharedCheck_3093_ = !lean_is_exclusive(v___x_3054_);
if (v_isSharedCheck_3093_ == 0)
{
v___x_3065_ = v___x_3054_;
v_isShared_3066_ = v_isSharedCheck_3093_;
goto v_resetjp_3064_;
}
else
{
lean_inc(v_snapshotTasks_3063_);
lean_inc(v_infoState_3062_);
lean_inc(v_messages_3061_);
lean_inc(v_cache_3060_);
lean_inc(v_traceState_3055_);
lean_inc(v_auxDeclNGen_3059_);
lean_inc(v_ngen_3058_);
lean_inc(v_nextMacroScope_3057_);
lean_inc(v_env_3056_);
lean_dec(v___x_3054_);
v___x_3065_ = lean_box(0);
v_isShared_3066_ = v_isSharedCheck_3093_;
goto v_resetjp_3064_;
}
v_resetjp_3064_:
{
uint64_t v_tid_3067_; lean_object* v_traces_3068_; lean_object* v___x_3070_; uint8_t v_isShared_3071_; uint8_t v_isSharedCheck_3092_; 
v_tid_3067_ = lean_ctor_get_uint64(v_traceState_3055_, sizeof(void*)*1);
v_traces_3068_ = lean_ctor_get(v_traceState_3055_, 0);
v_isSharedCheck_3092_ = !lean_is_exclusive(v_traceState_3055_);
if (v_isSharedCheck_3092_ == 0)
{
v___x_3070_ = v_traceState_3055_;
v_isShared_3071_ = v_isSharedCheck_3092_;
goto v_resetjp_3069_;
}
else
{
lean_inc(v_traces_3068_);
lean_dec(v_traceState_3055_);
v___x_3070_ = lean_box(0);
v_isShared_3071_ = v_isSharedCheck_3092_;
goto v_resetjp_3069_;
}
v_resetjp_3069_:
{
lean_object* v___x_3072_; double v___x_3073_; uint8_t v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3082_; 
v___x_3072_ = lean_box(0);
v___x_3073_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0___closed__0);
v___x_3074_ = 0;
v___x_3075_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0___closed__1));
v___x_3076_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3076_, 0, v_cls_3041_);
lean_ctor_set(v___x_3076_, 1, v___x_3072_);
lean_ctor_set(v___x_3076_, 2, v___x_3075_);
lean_ctor_set_float(v___x_3076_, sizeof(void*)*3, v___x_3073_);
lean_ctor_set_float(v___x_3076_, sizeof(void*)*3 + 8, v___x_3073_);
lean_ctor_set_uint8(v___x_3076_, sizeof(void*)*3 + 16, v___x_3074_);
v___x_3077_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0___closed__2));
v___x_3078_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3078_, 0, v___x_3076_);
lean_ctor_set(v___x_3078_, 1, v_a_3050_);
lean_ctor_set(v___x_3078_, 2, v___x_3077_);
lean_inc(v_ref_3048_);
v___x_3079_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3079_, 0, v_ref_3048_);
lean_ctor_set(v___x_3079_, 1, v___x_3078_);
v___x_3080_ = l_Lean_PersistentArray_push___redArg(v_traces_3068_, v___x_3079_);
if (v_isShared_3071_ == 0)
{
lean_ctor_set(v___x_3070_, 0, v___x_3080_);
v___x_3082_ = v___x_3070_;
goto v_reusejp_3081_;
}
else
{
lean_object* v_reuseFailAlloc_3091_; 
v_reuseFailAlloc_3091_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3091_, 0, v___x_3080_);
lean_ctor_set_uint64(v_reuseFailAlloc_3091_, sizeof(void*)*1, v_tid_3067_);
v___x_3082_ = v_reuseFailAlloc_3091_;
goto v_reusejp_3081_;
}
v_reusejp_3081_:
{
lean_object* v___x_3084_; 
if (v_isShared_3066_ == 0)
{
lean_ctor_set(v___x_3065_, 4, v___x_3082_);
v___x_3084_ = v___x_3065_;
goto v_reusejp_3083_;
}
else
{
lean_object* v_reuseFailAlloc_3090_; 
v_reuseFailAlloc_3090_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3090_, 0, v_env_3056_);
lean_ctor_set(v_reuseFailAlloc_3090_, 1, v_nextMacroScope_3057_);
lean_ctor_set(v_reuseFailAlloc_3090_, 2, v_ngen_3058_);
lean_ctor_set(v_reuseFailAlloc_3090_, 3, v_auxDeclNGen_3059_);
lean_ctor_set(v_reuseFailAlloc_3090_, 4, v___x_3082_);
lean_ctor_set(v_reuseFailAlloc_3090_, 5, v_cache_3060_);
lean_ctor_set(v_reuseFailAlloc_3090_, 6, v_messages_3061_);
lean_ctor_set(v_reuseFailAlloc_3090_, 7, v_infoState_3062_);
lean_ctor_set(v_reuseFailAlloc_3090_, 8, v_snapshotTasks_3063_);
v___x_3084_ = v_reuseFailAlloc_3090_;
goto v_reusejp_3083_;
}
v_reusejp_3083_:
{
lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3088_; 
v___x_3085_ = lean_st_ref_put(v___y_3046_, v___x_3084_);
v___x_3086_ = lean_box(0);
if (v_isShared_3053_ == 0)
{
lean_ctor_set(v___x_3052_, 0, v___x_3086_);
v___x_3088_ = v___x_3052_;
goto v_reusejp_3087_;
}
else
{
lean_object* v_reuseFailAlloc_3089_; 
v_reuseFailAlloc_3089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3089_, 0, v___x_3086_);
v___x_3088_ = v_reuseFailAlloc_3089_;
goto v_reusejp_3087_;
}
v_reusejp_3087_:
{
return v___x_3088_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0___boxed(lean_object* v_cls_3095_, lean_object* v_msg_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_){
_start:
{
lean_object* v_res_3102_; 
v_res_3102_ = l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0(v_cls_3095_, v_msg_3096_, v___y_3097_, v___y_3098_, v___y_3099_, v___y_3100_);
lean_dec(v___y_3100_);
lean_dec_ref(v___y_3099_);
lean_dec(v___y_3098_);
lean_dec_ref(v___y_3097_);
return v_res_3102_;
}
}
static lean_object* _init_l_Lean_Meta_Cases_cases___lam__0___closed__2(void){
_start:
{
lean_object* v___x_3106_; lean_object* v___x_3107_; 
v___x_3106_ = ((lean_object*)(l_Lean_Meta_Cases_cases___lam__0___closed__1));
v___x_3107_ = l_Lean_MessageData_ofFormat(v___x_3106_);
return v___x_3107_;
}
}
static lean_object* _init_l_Lean_Meta_Cases_cases___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3108_; lean_object* v___x_3109_; 
v___x_3108_ = lean_obj_once(&l_Lean_Meta_Cases_cases___lam__0___closed__2, &l_Lean_Meta_Cases_cases___lam__0___closed__2_once, _init_l_Lean_Meta_Cases_cases___lam__0___closed__2);
v___x_3109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3109_, 0, v___x_3108_);
return v___x_3109_;
}
}
static lean_object* _init_l_Lean_Meta_Cases_cases___lam__0___closed__9(void){
_start:
{
lean_object* v___x_3116_; lean_object* v___x_3117_; 
v___x_3116_ = ((lean_object*)(l_Lean_Meta_Cases_cases___lam__0___closed__8));
v___x_3117_ = l_Lean_stringToMessageData(v___x_3116_);
return v___x_3117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_cases___lam__0(lean_object* v_mvarId_3118_, lean_object* v___x_3119_, lean_object* v_majorFVarId_3120_, lean_object* v_givenNames_3121_, lean_object* v_interestingCtors_x3f_3122_, lean_object* v___x_3123_, uint8_t v_useNatCasesAuxOn_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_){
_start:
{
lean_object* v___x_3130_; 
lean_inc(v___x_3119_);
lean_inc(v_mvarId_3118_);
v___x_3130_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_3118_, v___x_3119_, v___y_3125_, v___y_3126_, v___y_3127_, v___y_3128_);
if (lean_obj_tag(v___x_3130_) == 0)
{
lean_object* v___x_3131_; 
lean_dec_ref_known(v___x_3130_, 1);
lean_inc(v_majorFVarId_3120_);
v___x_3131_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f(v_majorFVarId_3120_, v___y_3125_, v___y_3126_, v___y_3127_, v___y_3128_);
if (lean_obj_tag(v___x_3131_) == 0)
{
lean_object* v_a_3132_; 
v_a_3132_ = lean_ctor_get(v___x_3131_, 0);
lean_inc(v_a_3132_);
lean_dec_ref_known(v___x_3131_, 1);
if (lean_obj_tag(v_a_3132_) == 0)
{
lean_object* v___x_3133_; lean_object* v___x_3134_; 
lean_dec_ref(v___x_3123_);
lean_dec(v_interestingCtors_x3f_3122_);
lean_dec_ref(v_givenNames_3121_);
lean_dec(v_majorFVarId_3120_);
v___x_3133_ = lean_obj_once(&l_Lean_Meta_Cases_cases___lam__0___closed__3, &l_Lean_Meta_Cases_cases___lam__0___closed__3_once, _init_l_Lean_Meta_Cases_cases___lam__0___closed__3);
v___x_3134_ = l_Lean_Meta_throwTacticEx___redArg(v___x_3119_, v_mvarId_3118_, v___x_3133_, v___y_3125_, v___y_3126_, v___y_3127_, v___y_3128_);
return v___x_3134_;
}
else
{
lean_object* v_val_3135_; lean_object* v___x_3137_; uint8_t v_isShared_3138_; uint8_t v_isSharedCheck_3200_; 
lean_dec(v___x_3119_);
v_val_3135_ = lean_ctor_get(v_a_3132_, 0);
v_isSharedCheck_3200_ = !lean_is_exclusive(v_a_3132_);
if (v_isSharedCheck_3200_ == 0)
{
v___x_3137_ = v_a_3132_;
v_isShared_3138_ = v_isSharedCheck_3200_;
goto v_resetjp_3136_;
}
else
{
lean_inc(v_val_3135_);
lean_dec(v_a_3132_);
v___x_3137_ = lean_box(0);
v_isShared_3138_ = v_isSharedCheck_3200_;
goto v_resetjp_3136_;
}
v_resetjp_3136_:
{
lean_object* v___x_3139_; 
lean_inc(v_val_3135_);
v___x_3139_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices(v_val_3135_, v___y_3125_, v___y_3126_, v___y_3127_, v___y_3128_);
if (lean_obj_tag(v___x_3139_) == 0)
{
lean_object* v_a_3140_; uint8_t v___x_3141_; 
v_a_3140_ = lean_ctor_get(v___x_3139_, 0);
lean_inc(v_a_3140_);
lean_dec_ref_known(v___x_3139_, 1);
v___x_3141_ = lean_unbox(v_a_3140_);
if (v___x_3141_ == 0)
{
lean_object* v___x_3142_; 
v___x_3142_ = l_Lean_Meta_generalizeIndices(v_mvarId_3118_, v_majorFVarId_3120_, v___y_3125_, v___y_3126_, v___y_3127_, v___y_3128_);
if (lean_obj_tag(v___x_3142_) == 0)
{
lean_object* v_a_3143_; lean_object* v___y_3145_; lean_object* v___y_3146_; lean_object* v___y_3147_; lean_object* v___y_3148_; lean_object* v_toCold_3158_; lean_object* v_options_3159_; uint8_t v_hasTrace_3160_; 
v_a_3143_ = lean_ctor_get(v___x_3142_, 0);
lean_inc(v_a_3143_);
lean_dec_ref_known(v___x_3142_, 1);
v_toCold_3158_ = lean_ctor_get(v___y_3127_, 0);
v_options_3159_ = lean_ctor_get(v_toCold_3158_, 2);
v_hasTrace_3160_ = lean_ctor_get_uint8(v_options_3159_, sizeof(void*)*1);
if (v_hasTrace_3160_ == 0)
{
lean_del_object(v___x_3137_);
lean_dec_ref(v___x_3123_);
v___y_3145_ = v___y_3125_;
v___y_3146_ = v___y_3126_;
v___y_3147_ = v___y_3127_;
v___y_3148_ = v___y_3128_;
goto v___jp_3144_;
}
else
{
lean_object* v_inheritedTraceOptions_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; uint8_t v___x_3167_; 
v_inheritedTraceOptions_3161_ = lean_ctor_get(v_toCold_3158_, 11);
v___x_3162_ = ((lean_object*)(l_Lean_Meta_Cases_cases___lam__0___closed__4));
v___x_3163_ = ((lean_object*)(l_Lean_Meta_Cases_cases___lam__0___closed__5));
v___x_3164_ = l_Lean_Name_mkStr3(v___x_3162_, v___x_3163_, v___x_3123_);
v___x_3165_ = ((lean_object*)(l_Lean_Meta_Cases_cases___lam__0___closed__7));
lean_inc(v___x_3164_);
v___x_3166_ = l_Lean_Name_append(v___x_3165_, v___x_3164_);
v___x_3167_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3161_, v_options_3159_, v___x_3166_);
lean_dec(v___x_3166_);
if (v___x_3167_ == 0)
{
lean_dec(v___x_3164_);
lean_del_object(v___x_3137_);
v___y_3145_ = v___y_3125_;
v___y_3146_ = v___y_3126_;
v___y_3147_ = v___y_3127_;
v___y_3148_ = v___y_3128_;
goto v___jp_3144_;
}
else
{
lean_object* v_mvarId_3168_; lean_object* v___x_3169_; lean_object* v___x_3171_; 
v_mvarId_3168_ = lean_ctor_get(v_a_3143_, 0);
v___x_3169_ = lean_obj_once(&l_Lean_Meta_Cases_cases___lam__0___closed__9, &l_Lean_Meta_Cases_cases___lam__0___closed__9_once, _init_l_Lean_Meta_Cases_cases___lam__0___closed__9);
lean_inc(v_mvarId_3168_);
if (v_isShared_3138_ == 0)
{
lean_ctor_set(v___x_3137_, 0, v_mvarId_3168_);
v___x_3171_ = v___x_3137_;
goto v_reusejp_3170_;
}
else
{
lean_object* v_reuseFailAlloc_3182_; 
v_reuseFailAlloc_3182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3182_, 0, v_mvarId_3168_);
v___x_3171_ = v_reuseFailAlloc_3182_;
goto v_reusejp_3170_;
}
v_reusejp_3170_:
{
lean_object* v___x_3172_; lean_object* v___x_3173_; 
v___x_3172_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3172_, 0, v___x_3169_);
lean_ctor_set(v___x_3172_, 1, v___x_3171_);
v___x_3173_ = l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0(v___x_3164_, v___x_3172_, v___y_3125_, v___y_3126_, v___y_3127_, v___y_3128_);
if (lean_obj_tag(v___x_3173_) == 0)
{
lean_dec_ref_known(v___x_3173_, 1);
v___y_3145_ = v___y_3125_;
v___y_3146_ = v___y_3126_;
v___y_3147_ = v___y_3127_;
v___y_3148_ = v___y_3128_;
goto v___jp_3144_;
}
else
{
lean_object* v_a_3174_; lean_object* v___x_3176_; uint8_t v_isShared_3177_; uint8_t v_isSharedCheck_3181_; 
lean_dec(v_a_3143_);
lean_dec(v_a_3140_);
lean_dec(v_val_3135_);
lean_dec(v_interestingCtors_x3f_3122_);
lean_dec_ref(v_givenNames_3121_);
v_a_3174_ = lean_ctor_get(v___x_3173_, 0);
v_isSharedCheck_3181_ = !lean_is_exclusive(v___x_3173_);
if (v_isSharedCheck_3181_ == 0)
{
v___x_3176_ = v___x_3173_;
v_isShared_3177_ = v_isSharedCheck_3181_;
goto v_resetjp_3175_;
}
else
{
lean_inc(v_a_3174_);
lean_dec(v___x_3173_);
v___x_3176_ = lean_box(0);
v_isShared_3177_ = v_isSharedCheck_3181_;
goto v_resetjp_3175_;
}
v_resetjp_3175_:
{
lean_object* v___x_3179_; 
if (v_isShared_3177_ == 0)
{
v___x_3179_ = v___x_3176_;
goto v_reusejp_3178_;
}
else
{
lean_object* v_reuseFailAlloc_3180_; 
v_reuseFailAlloc_3180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3180_, 0, v_a_3174_);
v___x_3179_ = v_reuseFailAlloc_3180_;
goto v_reusejp_3178_;
}
v_reusejp_3178_:
{
return v___x_3179_;
}
}
}
}
}
}
v___jp_3144_:
{
lean_object* v_mvarId_3149_; lean_object* v_fvarId_3150_; lean_object* v_numEqs_3151_; uint8_t v___x_3152_; lean_object* v___x_3153_; 
v_mvarId_3149_ = lean_ctor_get(v_a_3143_, 0);
v_fvarId_3150_ = lean_ctor_get(v_a_3143_, 2);
v_numEqs_3151_ = lean_ctor_get(v_a_3143_, 3);
lean_inc(v_numEqs_3151_);
v___x_3152_ = lean_unbox(v_a_3140_);
lean_dec(v_a_3140_);
lean_inc(v_fvarId_3150_);
lean_inc(v_mvarId_3149_);
v___x_3153_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn(v_mvarId_3149_, v_fvarId_3150_, v_givenNames_3121_, v_val_3135_, v___x_3152_, v_interestingCtors_x3f_3122_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_);
if (lean_obj_tag(v___x_3153_) == 0)
{
lean_object* v_a_3154_; lean_object* v___x_3155_; 
v_a_3154_ = lean_ctor_get(v___x_3153_, 0);
lean_inc(v_a_3154_);
lean_dec_ref_known(v___x_3153_, 1);
v___x_3155_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices(v_a_3143_, v_a_3154_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_);
lean_dec(v_a_3143_);
if (lean_obj_tag(v___x_3155_) == 0)
{
lean_object* v_a_3156_; lean_object* v___x_3157_; 
v_a_3156_ = lean_ctor_get(v___x_3155_, 0);
lean_inc(v_a_3156_);
lean_dec_ref_known(v___x_3155_, 1);
v___x_3157_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs(v_numEqs_3151_, v_a_3156_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_);
lean_dec(v_a_3156_);
return v___x_3157_;
}
else
{
lean_dec(v_numEqs_3151_);
return v___x_3155_;
}
}
else
{
lean_dec(v_numEqs_3151_);
lean_dec(v_a_3143_);
return v___x_3153_;
}
}
}
else
{
lean_object* v_a_3183_; lean_object* v___x_3185_; uint8_t v_isShared_3186_; uint8_t v_isSharedCheck_3190_; 
lean_dec(v_a_3140_);
lean_del_object(v___x_3137_);
lean_dec(v_val_3135_);
lean_dec_ref(v___x_3123_);
lean_dec(v_interestingCtors_x3f_3122_);
lean_dec_ref(v_givenNames_3121_);
v_a_3183_ = lean_ctor_get(v___x_3142_, 0);
v_isSharedCheck_3190_ = !lean_is_exclusive(v___x_3142_);
if (v_isSharedCheck_3190_ == 0)
{
v___x_3185_ = v___x_3142_;
v_isShared_3186_ = v_isSharedCheck_3190_;
goto v_resetjp_3184_;
}
else
{
lean_inc(v_a_3183_);
lean_dec(v___x_3142_);
v___x_3185_ = lean_box(0);
v_isShared_3186_ = v_isSharedCheck_3190_;
goto v_resetjp_3184_;
}
v_resetjp_3184_:
{
lean_object* v___x_3188_; 
if (v_isShared_3186_ == 0)
{
v___x_3188_ = v___x_3185_;
goto v_reusejp_3187_;
}
else
{
lean_object* v_reuseFailAlloc_3189_; 
v_reuseFailAlloc_3189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3189_, 0, v_a_3183_);
v___x_3188_ = v_reuseFailAlloc_3189_;
goto v_reusejp_3187_;
}
v_reusejp_3187_:
{
return v___x_3188_;
}
}
}
}
else
{
lean_object* v___x_3191_; 
lean_dec(v_a_3140_);
lean_del_object(v___x_3137_);
lean_dec_ref(v___x_3123_);
v___x_3191_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn(v_mvarId_3118_, v_majorFVarId_3120_, v_givenNames_3121_, v_val_3135_, v_useNatCasesAuxOn_3124_, v_interestingCtors_x3f_3122_, v___y_3125_, v___y_3126_, v___y_3127_, v___y_3128_);
return v___x_3191_;
}
}
else
{
lean_object* v_a_3192_; lean_object* v___x_3194_; uint8_t v_isShared_3195_; uint8_t v_isSharedCheck_3199_; 
lean_del_object(v___x_3137_);
lean_dec(v_val_3135_);
lean_dec_ref(v___x_3123_);
lean_dec(v_interestingCtors_x3f_3122_);
lean_dec_ref(v_givenNames_3121_);
lean_dec(v_majorFVarId_3120_);
lean_dec(v_mvarId_3118_);
v_a_3192_ = lean_ctor_get(v___x_3139_, 0);
v_isSharedCheck_3199_ = !lean_is_exclusive(v___x_3139_);
if (v_isSharedCheck_3199_ == 0)
{
v___x_3194_ = v___x_3139_;
v_isShared_3195_ = v_isSharedCheck_3199_;
goto v_resetjp_3193_;
}
else
{
lean_inc(v_a_3192_);
lean_dec(v___x_3139_);
v___x_3194_ = lean_box(0);
v_isShared_3195_ = v_isSharedCheck_3199_;
goto v_resetjp_3193_;
}
v_resetjp_3193_:
{
lean_object* v___x_3197_; 
if (v_isShared_3195_ == 0)
{
v___x_3197_ = v___x_3194_;
goto v_reusejp_3196_;
}
else
{
lean_object* v_reuseFailAlloc_3198_; 
v_reuseFailAlloc_3198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3198_, 0, v_a_3192_);
v___x_3197_ = v_reuseFailAlloc_3198_;
goto v_reusejp_3196_;
}
v_reusejp_3196_:
{
return v___x_3197_;
}
}
}
}
}
}
else
{
lean_object* v_a_3201_; lean_object* v___x_3203_; uint8_t v_isShared_3204_; uint8_t v_isSharedCheck_3208_; 
lean_dec_ref(v___x_3123_);
lean_dec(v_interestingCtors_x3f_3122_);
lean_dec_ref(v_givenNames_3121_);
lean_dec(v_majorFVarId_3120_);
lean_dec(v___x_3119_);
lean_dec(v_mvarId_3118_);
v_a_3201_ = lean_ctor_get(v___x_3131_, 0);
v_isSharedCheck_3208_ = !lean_is_exclusive(v___x_3131_);
if (v_isSharedCheck_3208_ == 0)
{
v___x_3203_ = v___x_3131_;
v_isShared_3204_ = v_isSharedCheck_3208_;
goto v_resetjp_3202_;
}
else
{
lean_inc(v_a_3201_);
lean_dec(v___x_3131_);
v___x_3203_ = lean_box(0);
v_isShared_3204_ = v_isSharedCheck_3208_;
goto v_resetjp_3202_;
}
v_resetjp_3202_:
{
lean_object* v___x_3206_; 
if (v_isShared_3204_ == 0)
{
v___x_3206_ = v___x_3203_;
goto v_reusejp_3205_;
}
else
{
lean_object* v_reuseFailAlloc_3207_; 
v_reuseFailAlloc_3207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3207_, 0, v_a_3201_);
v___x_3206_ = v_reuseFailAlloc_3207_;
goto v_reusejp_3205_;
}
v_reusejp_3205_:
{
return v___x_3206_;
}
}
}
}
else
{
lean_object* v_a_3209_; lean_object* v___x_3211_; uint8_t v_isShared_3212_; uint8_t v_isSharedCheck_3216_; 
lean_dec_ref(v___x_3123_);
lean_dec(v_interestingCtors_x3f_3122_);
lean_dec_ref(v_givenNames_3121_);
lean_dec(v_majorFVarId_3120_);
lean_dec(v___x_3119_);
lean_dec(v_mvarId_3118_);
v_a_3209_ = lean_ctor_get(v___x_3130_, 0);
v_isSharedCheck_3216_ = !lean_is_exclusive(v___x_3130_);
if (v_isSharedCheck_3216_ == 0)
{
v___x_3211_ = v___x_3130_;
v_isShared_3212_ = v_isSharedCheck_3216_;
goto v_resetjp_3210_;
}
else
{
lean_inc(v_a_3209_);
lean_dec(v___x_3130_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_cases___lam__0___boxed(lean_object* v_mvarId_3217_, lean_object* v___x_3218_, lean_object* v_majorFVarId_3219_, lean_object* v_givenNames_3220_, lean_object* v_interestingCtors_x3f_3221_, lean_object* v___x_3222_, lean_object* v_useNatCasesAuxOn_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_){
_start:
{
uint8_t v_useNatCasesAuxOn_boxed_3229_; lean_object* v_res_3230_; 
v_useNatCasesAuxOn_boxed_3229_ = lean_unbox(v_useNatCasesAuxOn_3223_);
v_res_3230_ = l_Lean_Meta_Cases_cases___lam__0(v_mvarId_3217_, v___x_3218_, v_majorFVarId_3219_, v_givenNames_3220_, v_interestingCtors_x3f_3221_, v___x_3222_, v_useNatCasesAuxOn_boxed_3229_, v___y_3224_, v___y_3225_, v___y_3226_, v___y_3227_);
lean_dec(v___y_3227_);
lean_dec_ref(v___y_3226_);
lean_dec(v___y_3225_);
lean_dec_ref(v___y_3224_);
return v_res_3230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_cases(lean_object* v_mvarId_3234_, lean_object* v_majorFVarId_3235_, lean_object* v_givenNames_3236_, uint8_t v_useNatCasesAuxOn_3237_, lean_object* v_interestingCtors_x3f_3238_, lean_object* v_a_3239_, lean_object* v_a_3240_, lean_object* v_a_3241_, lean_object* v_a_3242_){
_start:
{
lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___f_3247_; lean_object* v___x_3248_; 
v___x_3244_ = ((lean_object*)(l_Lean_Meta_Cases_cases___closed__0));
v___x_3245_ = ((lean_object*)(l_Lean_Meta_Cases_cases___closed__1));
v___x_3246_ = lean_box(v_useNatCasesAuxOn_3237_);
lean_inc(v_mvarId_3234_);
v___f_3247_ = lean_alloc_closure((void*)(l_Lean_Meta_Cases_cases___lam__0___boxed), 12, 7);
lean_closure_set(v___f_3247_, 0, v_mvarId_3234_);
lean_closure_set(v___f_3247_, 1, v___x_3245_);
lean_closure_set(v___f_3247_, 2, v_majorFVarId_3235_);
lean_closure_set(v___f_3247_, 3, v_givenNames_3236_);
lean_closure_set(v___f_3247_, 4, v_interestingCtors_x3f_3238_);
lean_closure_set(v___f_3247_, 5, v___x_3244_);
lean_closure_set(v___f_3247_, 6, v___x_3246_);
v___x_3248_ = l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2___redArg(v_mvarId_3234_, v___f_3247_, v_a_3239_, v_a_3240_, v_a_3241_, v_a_3242_);
if (lean_obj_tag(v___x_3248_) == 0)
{
return v___x_3248_;
}
else
{
lean_object* v_a_3249_; uint8_t v___y_3251_; uint8_t v___x_3253_; 
v_a_3249_ = lean_ctor_get(v___x_3248_, 0);
lean_inc(v_a_3249_);
v___x_3253_ = l_Lean_Exception_isInterrupt(v_a_3249_);
if (v___x_3253_ == 0)
{
uint8_t v___x_3254_; 
lean_inc(v_a_3249_);
v___x_3254_ = l_Lean_Exception_isRuntime(v_a_3249_);
v___y_3251_ = v___x_3254_;
goto v___jp_3250_;
}
else
{
v___y_3251_ = v___x_3253_;
goto v___jp_3250_;
}
v___jp_3250_:
{
if (v___y_3251_ == 0)
{
lean_object* v___x_3252_; 
lean_dec_ref_known(v___x_3248_, 1);
v___x_3252_ = l_Lean_Meta_throwNestedTacticEx___redArg(v___x_3245_, v_a_3249_, v_a_3239_, v_a_3240_, v_a_3241_, v_a_3242_);
return v___x_3252_;
}
else
{
lean_dec(v_a_3249_);
return v___x_3248_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_cases___boxed(lean_object* v_mvarId_3255_, lean_object* v_majorFVarId_3256_, lean_object* v_givenNames_3257_, lean_object* v_useNatCasesAuxOn_3258_, lean_object* v_interestingCtors_x3f_3259_, lean_object* v_a_3260_, lean_object* v_a_3261_, lean_object* v_a_3262_, lean_object* v_a_3263_, lean_object* v_a_3264_){
_start:
{
uint8_t v_useNatCasesAuxOn_boxed_3265_; lean_object* v_res_3266_; 
v_useNatCasesAuxOn_boxed_3265_ = lean_unbox(v_useNatCasesAuxOn_3258_);
v_res_3266_ = l_Lean_Meta_Cases_cases(v_mvarId_3255_, v_majorFVarId_3256_, v_givenNames_3257_, v_useNatCasesAuxOn_boxed_3265_, v_interestingCtors_x3f_3259_, v_a_3260_, v_a_3261_, v_a_3262_, v_a_3263_);
lean_dec(v_a_3263_);
lean_dec_ref(v_a_3262_);
lean_dec(v_a_3261_);
lean_dec_ref(v_a_3260_);
return v_res_3266_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_cases(lean_object* v_mvarId_3267_, lean_object* v_majorFVarId_3268_, lean_object* v_givenNames_3269_, uint8_t v_useNatCasesAuxOn_3270_, lean_object* v_interestingCtors_x3f_3271_, lean_object* v_a_3272_, lean_object* v_a_3273_, lean_object* v_a_3274_, lean_object* v_a_3275_){
_start:
{
lean_object* v___x_3277_; 
v___x_3277_ = l_Lean_Meta_Cases_cases(v_mvarId_3267_, v_majorFVarId_3268_, v_givenNames_3269_, v_useNatCasesAuxOn_3270_, v_interestingCtors_x3f_3271_, v_a_3272_, v_a_3273_, v_a_3274_, v_a_3275_);
return v___x_3277_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_cases___boxed(lean_object* v_mvarId_3278_, lean_object* v_majorFVarId_3279_, lean_object* v_givenNames_3280_, lean_object* v_useNatCasesAuxOn_3281_, lean_object* v_interestingCtors_x3f_3282_, lean_object* v_a_3283_, lean_object* v_a_3284_, lean_object* v_a_3285_, lean_object* v_a_3286_, lean_object* v_a_3287_){
_start:
{
uint8_t v_useNatCasesAuxOn_boxed_3288_; lean_object* v_res_3289_; 
v_useNatCasesAuxOn_boxed_3288_ = lean_unbox(v_useNatCasesAuxOn_3281_);
v_res_3289_ = l_Lean_MVarId_cases(v_mvarId_3278_, v_majorFVarId_3279_, v_givenNames_3280_, v_useNatCasesAuxOn_boxed_3288_, v_interestingCtors_x3f_3282_, v_a_3283_, v_a_3284_, v_a_3285_, v_a_3286_);
lean_dec(v_a_3286_);
lean_dec_ref(v_a_3285_);
lean_dec(v_a_3284_);
lean_dec_ref(v_a_3283_);
return v_res_3289_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1___redArg(lean_object* v_x_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_){
_start:
{
lean_object* v___x_3296_; 
v___x_3296_ = l_Lean_Meta_saveState___redArg(v___y_3292_, v___y_3294_);
if (lean_obj_tag(v___x_3296_) == 0)
{
lean_object* v_a_3297_; lean_object* v___x_3298_; 
v_a_3297_ = lean_ctor_get(v___x_3296_, 0);
lean_inc(v_a_3297_);
lean_dec_ref_known(v___x_3296_, 1);
lean_inc(v___y_3294_);
lean_inc_ref(v___y_3293_);
lean_inc(v___y_3292_);
lean_inc_ref(v___y_3291_);
v___x_3298_ = lean_apply_5(v_x_3290_, v___y_3291_, v___y_3292_, v___y_3293_, v___y_3294_, lean_box(0));
if (lean_obj_tag(v___x_3298_) == 0)
{
lean_object* v_a_3299_; lean_object* v___x_3301_; uint8_t v_isShared_3302_; uint8_t v_isSharedCheck_3307_; 
lean_dec(v_a_3297_);
v_a_3299_ = lean_ctor_get(v___x_3298_, 0);
v_isSharedCheck_3307_ = !lean_is_exclusive(v___x_3298_);
if (v_isSharedCheck_3307_ == 0)
{
v___x_3301_ = v___x_3298_;
v_isShared_3302_ = v_isSharedCheck_3307_;
goto v_resetjp_3300_;
}
else
{
lean_inc(v_a_3299_);
lean_dec(v___x_3298_);
v___x_3301_ = lean_box(0);
v_isShared_3302_ = v_isSharedCheck_3307_;
goto v_resetjp_3300_;
}
v_resetjp_3300_:
{
lean_object* v___x_3303_; lean_object* v___x_3305_; 
v___x_3303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3303_, 0, v_a_3299_);
if (v_isShared_3302_ == 0)
{
lean_ctor_set(v___x_3301_, 0, v___x_3303_);
v___x_3305_ = v___x_3301_;
goto v_reusejp_3304_;
}
else
{
lean_object* v_reuseFailAlloc_3306_; 
v_reuseFailAlloc_3306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3306_, 0, v___x_3303_);
v___x_3305_ = v_reuseFailAlloc_3306_;
goto v_reusejp_3304_;
}
v_reusejp_3304_:
{
return v___x_3305_;
}
}
}
else
{
lean_object* v_a_3308_; lean_object* v___x_3310_; uint8_t v_isShared_3311_; uint8_t v_isSharedCheck_3337_; 
v_a_3308_ = lean_ctor_get(v___x_3298_, 0);
v_isSharedCheck_3337_ = !lean_is_exclusive(v___x_3298_);
if (v_isSharedCheck_3337_ == 0)
{
v___x_3310_ = v___x_3298_;
v_isShared_3311_ = v_isSharedCheck_3337_;
goto v_resetjp_3309_;
}
else
{
lean_inc(v_a_3308_);
lean_dec(v___x_3298_);
v___x_3310_ = lean_box(0);
v_isShared_3311_ = v_isSharedCheck_3337_;
goto v_resetjp_3309_;
}
v_resetjp_3309_:
{
uint8_t v___y_3313_; uint8_t v___x_3335_; 
v___x_3335_ = l_Lean_Exception_isInterrupt(v_a_3308_);
if (v___x_3335_ == 0)
{
uint8_t v___x_3336_; 
lean_inc(v_a_3308_);
v___x_3336_ = l_Lean_Exception_isRuntime(v_a_3308_);
v___y_3313_ = v___x_3336_;
goto v___jp_3312_;
}
else
{
v___y_3313_ = v___x_3335_;
goto v___jp_3312_;
}
v___jp_3312_:
{
if (v___y_3313_ == 0)
{
lean_object* v___x_3314_; 
lean_del_object(v___x_3310_);
lean_dec(v_a_3308_);
v___x_3314_ = l_Lean_Meta_SavedState_restore___redArg(v_a_3297_, v___y_3292_, v___y_3294_);
lean_dec(v_a_3297_);
if (lean_obj_tag(v___x_3314_) == 0)
{
lean_object* v___x_3316_; uint8_t v_isShared_3317_; uint8_t v_isSharedCheck_3322_; 
v_isSharedCheck_3322_ = !lean_is_exclusive(v___x_3314_);
if (v_isSharedCheck_3322_ == 0)
{
lean_object* v_unused_3323_; 
v_unused_3323_ = lean_ctor_get(v___x_3314_, 0);
lean_dec(v_unused_3323_);
v___x_3316_ = v___x_3314_;
v_isShared_3317_ = v_isSharedCheck_3322_;
goto v_resetjp_3315_;
}
else
{
lean_dec(v___x_3314_);
v___x_3316_ = lean_box(0);
v_isShared_3317_ = v_isSharedCheck_3322_;
goto v_resetjp_3315_;
}
v_resetjp_3315_:
{
lean_object* v___x_3318_; lean_object* v___x_3320_; 
v___x_3318_ = lean_box(0);
if (v_isShared_3317_ == 0)
{
lean_ctor_set(v___x_3316_, 0, v___x_3318_);
v___x_3320_ = v___x_3316_;
goto v_reusejp_3319_;
}
else
{
lean_object* v_reuseFailAlloc_3321_; 
v_reuseFailAlloc_3321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3321_, 0, v___x_3318_);
v___x_3320_ = v_reuseFailAlloc_3321_;
goto v_reusejp_3319_;
}
v_reusejp_3319_:
{
return v___x_3320_;
}
}
}
else
{
lean_object* v_a_3324_; lean_object* v___x_3326_; uint8_t v_isShared_3327_; uint8_t v_isSharedCheck_3331_; 
v_a_3324_ = lean_ctor_get(v___x_3314_, 0);
v_isSharedCheck_3331_ = !lean_is_exclusive(v___x_3314_);
if (v_isSharedCheck_3331_ == 0)
{
v___x_3326_ = v___x_3314_;
v_isShared_3327_ = v_isSharedCheck_3331_;
goto v_resetjp_3325_;
}
else
{
lean_inc(v_a_3324_);
lean_dec(v___x_3314_);
v___x_3326_ = lean_box(0);
v_isShared_3327_ = v_isSharedCheck_3331_;
goto v_resetjp_3325_;
}
v_resetjp_3325_:
{
lean_object* v___x_3329_; 
if (v_isShared_3327_ == 0)
{
v___x_3329_ = v___x_3326_;
goto v_reusejp_3328_;
}
else
{
lean_object* v_reuseFailAlloc_3330_; 
v_reuseFailAlloc_3330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3330_, 0, v_a_3324_);
v___x_3329_ = v_reuseFailAlloc_3330_;
goto v_reusejp_3328_;
}
v_reusejp_3328_:
{
return v___x_3329_;
}
}
}
}
else
{
lean_object* v___x_3333_; 
lean_dec(v_a_3297_);
if (v_isShared_3311_ == 0)
{
v___x_3333_ = v___x_3310_;
goto v_reusejp_3332_;
}
else
{
lean_object* v_reuseFailAlloc_3334_; 
v_reuseFailAlloc_3334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3334_, 0, v_a_3308_);
v___x_3333_ = v_reuseFailAlloc_3334_;
goto v_reusejp_3332_;
}
v_reusejp_3332_:
{
return v___x_3333_;
}
}
}
}
}
}
else
{
lean_object* v_a_3338_; lean_object* v___x_3340_; uint8_t v_isShared_3341_; uint8_t v_isSharedCheck_3345_; 
lean_dec_ref(v_x_3290_);
v_a_3338_ = lean_ctor_get(v___x_3296_, 0);
v_isSharedCheck_3345_ = !lean_is_exclusive(v___x_3296_);
if (v_isSharedCheck_3345_ == 0)
{
v___x_3340_ = v___x_3296_;
v_isShared_3341_ = v_isSharedCheck_3345_;
goto v_resetjp_3339_;
}
else
{
lean_inc(v_a_3338_);
lean_dec(v___x_3296_);
v___x_3340_ = lean_box(0);
v_isShared_3341_ = v_isSharedCheck_3345_;
goto v_resetjp_3339_;
}
v_resetjp_3339_:
{
lean_object* v___x_3343_; 
if (v_isShared_3341_ == 0)
{
v___x_3343_ = v___x_3340_;
goto v_reusejp_3342_;
}
else
{
lean_object* v_reuseFailAlloc_3344_; 
v_reuseFailAlloc_3344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3344_, 0, v_a_3338_);
v___x_3343_ = v_reuseFailAlloc_3344_;
goto v_reusejp_3342_;
}
v_reusejp_3342_:
{
return v___x_3343_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1___redArg___boxed(lean_object* v_x_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_, lean_object* v___y_3351_){
_start:
{
lean_object* v_res_3352_; 
v_res_3352_ = l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1___redArg(v_x_3346_, v___y_3347_, v___y_3348_, v___y_3349_, v___y_3350_);
lean_dec(v___y_3350_);
lean_dec_ref(v___y_3349_);
lean_dec(v___y_3348_);
lean_dec_ref(v___y_3347_);
return v_res_3352_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1(lean_object* v_00_u03b1_3353_, lean_object* v_x_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_){
_start:
{
lean_object* v___x_3360_; 
v___x_3360_ = l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1___redArg(v_x_3354_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_);
return v___x_3360_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1___boxed(lean_object* v_00_u03b1_3361_, lean_object* v_x_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_){
_start:
{
lean_object* v_res_3368_; 
v_res_3368_ = l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1(v_00_u03b1_3361_, v_x_3362_, v___y_3363_, v___y_3364_, v___y_3365_, v___y_3366_);
lean_dec(v___y_3366_);
lean_dec_ref(v___y_3365_);
lean_dec(v___y_3364_);
lean_dec_ref(v___y_3363_);
return v_res_3368_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_MVarId_casesRec_spec__0(lean_object* v_a_3369_, lean_object* v_a_3370_){
_start:
{
if (lean_obj_tag(v_a_3369_) == 0)
{
lean_object* v___x_3371_; 
v___x_3371_ = l_List_reverse___redArg(v_a_3370_);
return v___x_3371_;
}
else
{
lean_object* v_head_3372_; lean_object* v_toInductionSubgoal_3373_; lean_object* v_tail_3374_; lean_object* v___x_3376_; uint8_t v_isShared_3377_; uint8_t v_isSharedCheck_3383_; 
v_head_3372_ = lean_ctor_get(v_a_3369_, 0);
v_toInductionSubgoal_3373_ = lean_ctor_get(v_head_3372_, 0);
lean_inc_ref(v_toInductionSubgoal_3373_);
v_tail_3374_ = lean_ctor_get(v_a_3369_, 1);
v_isSharedCheck_3383_ = !lean_is_exclusive(v_a_3369_);
if (v_isSharedCheck_3383_ == 0)
{
lean_object* v_unused_3384_; 
v_unused_3384_ = lean_ctor_get(v_a_3369_, 0);
lean_dec(v_unused_3384_);
v___x_3376_ = v_a_3369_;
v_isShared_3377_ = v_isSharedCheck_3383_;
goto v_resetjp_3375_;
}
else
{
lean_inc(v_tail_3374_);
lean_dec(v_a_3369_);
v___x_3376_ = lean_box(0);
v_isShared_3377_ = v_isSharedCheck_3383_;
goto v_resetjp_3375_;
}
v_resetjp_3375_:
{
lean_object* v_mvarId_3378_; lean_object* v___x_3380_; 
v_mvarId_3378_ = lean_ctor_get(v_toInductionSubgoal_3373_, 0);
lean_inc(v_mvarId_3378_);
lean_dec_ref(v_toInductionSubgoal_3373_);
if (v_isShared_3377_ == 0)
{
lean_ctor_set(v___x_3376_, 1, v_a_3370_);
lean_ctor_set(v___x_3376_, 0, v_mvarId_3378_);
v___x_3380_ = v___x_3376_;
goto v_reusejp_3379_;
}
else
{
lean_object* v_reuseFailAlloc_3382_; 
v_reuseFailAlloc_3382_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3382_, 0, v_mvarId_3378_);
lean_ctor_set(v_reuseFailAlloc_3382_, 1, v_a_3370_);
v___x_3380_ = v_reuseFailAlloc_3382_;
goto v_reusejp_3379_;
}
v_reusejp_3379_:
{
v_a_3369_ = v_tail_3374_;
v_a_3370_ = v___x_3380_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3___lam__0(lean_object* v_mvarId_3385_, lean_object* v___x_3386_, lean_object* v___x_3387_, uint8_t v___x_3388_, lean_object* v___x_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_){
_start:
{
lean_object* v___x_3395_; 
v___x_3395_ = l_Lean_Meta_Cases_cases(v_mvarId_3385_, v___x_3386_, v___x_3387_, v___x_3388_, v___x_3389_, v___y_3390_, v___y_3391_, v___y_3392_, v___y_3393_);
if (lean_obj_tag(v___x_3395_) == 0)
{
lean_object* v_a_3396_; lean_object* v___x_3398_; uint8_t v_isShared_3399_; uint8_t v_isSharedCheck_3406_; 
v_a_3396_ = lean_ctor_get(v___x_3395_, 0);
v_isSharedCheck_3406_ = !lean_is_exclusive(v___x_3395_);
if (v_isSharedCheck_3406_ == 0)
{
v___x_3398_ = v___x_3395_;
v_isShared_3399_ = v_isSharedCheck_3406_;
goto v_resetjp_3397_;
}
else
{
lean_inc(v_a_3396_);
lean_dec(v___x_3395_);
v___x_3398_ = lean_box(0);
v_isShared_3399_ = v_isSharedCheck_3406_;
goto v_resetjp_3397_;
}
v_resetjp_3397_:
{
lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3404_; 
v___x_3400_ = lean_array_to_list(v_a_3396_);
v___x_3401_ = lean_box(0);
v___x_3402_ = l_List_mapTR_loop___at___00Lean_MVarId_casesRec_spec__0(v___x_3400_, v___x_3401_);
if (v_isShared_3399_ == 0)
{
lean_ctor_set(v___x_3398_, 0, v___x_3402_);
v___x_3404_ = v___x_3398_;
goto v_reusejp_3403_;
}
else
{
lean_object* v_reuseFailAlloc_3405_; 
v_reuseFailAlloc_3405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3405_, 0, v___x_3402_);
v___x_3404_ = v_reuseFailAlloc_3405_;
goto v_reusejp_3403_;
}
v_reusejp_3403_:
{
return v___x_3404_;
}
}
}
else
{
lean_object* v_a_3407_; lean_object* v___x_3409_; uint8_t v_isShared_3410_; uint8_t v_isSharedCheck_3414_; 
v_a_3407_ = lean_ctor_get(v___x_3395_, 0);
v_isSharedCheck_3414_ = !lean_is_exclusive(v___x_3395_);
if (v_isSharedCheck_3414_ == 0)
{
v___x_3409_ = v___x_3395_;
v_isShared_3410_ = v_isSharedCheck_3414_;
goto v_resetjp_3408_;
}
else
{
lean_inc(v_a_3407_);
lean_dec(v___x_3395_);
v___x_3409_ = lean_box(0);
v_isShared_3410_ = v_isSharedCheck_3414_;
goto v_resetjp_3408_;
}
v_resetjp_3408_:
{
lean_object* v___x_3412_; 
if (v_isShared_3410_ == 0)
{
v___x_3412_ = v___x_3409_;
goto v_reusejp_3411_;
}
else
{
lean_object* v_reuseFailAlloc_3413_; 
v_reuseFailAlloc_3413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3413_, 0, v_a_3407_);
v___x_3412_ = v_reuseFailAlloc_3413_;
goto v_reusejp_3411_;
}
v_reusejp_3411_:
{
return v___x_3412_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3___lam__0___boxed(lean_object* v_mvarId_3415_, lean_object* v___x_3416_, lean_object* v___x_3417_, lean_object* v___x_3418_, lean_object* v___x_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_){
_start:
{
uint8_t v___x_6243__boxed_3425_; lean_object* v_res_3426_; 
v___x_6243__boxed_3425_ = lean_unbox(v___x_3418_);
v_res_3426_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3___lam__0(v_mvarId_3415_, v___x_3416_, v___x_3417_, v___x_6243__boxed_3425_, v___x_3419_, v___y_3420_, v___y_3421_, v___y_3422_, v___y_3423_);
lean_dec(v___y_3423_);
lean_dec_ref(v___y_3422_);
lean_dec(v___y_3421_);
lean_dec_ref(v___y_3420_);
return v_res_3426_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5(lean_object* v_p_3432_, lean_object* v_mvarId_3433_, lean_object* v_as_3434_, size_t v_sz_3435_, size_t v_i_3436_, lean_object* v_b_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_){
_start:
{
uint8_t v___x_3443_; 
v___x_3443_ = lean_usize_dec_lt(v_i_3436_, v_sz_3435_);
if (v___x_3443_ == 0)
{
lean_object* v___x_3444_; 
lean_dec(v_mvarId_3433_);
lean_dec_ref(v_p_3432_);
v___x_3444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3444_, 0, v_b_3437_);
return v___x_3444_;
}
else
{
lean_object* v_snd_3445_; lean_object* v___x_3447_; uint8_t v_isShared_3448_; uint8_t v_isSharedCheck_3513_; 
v_snd_3445_ = lean_ctor_get(v_b_3437_, 1);
v_isSharedCheck_3513_ = !lean_is_exclusive(v_b_3437_);
if (v_isSharedCheck_3513_ == 0)
{
lean_object* v_unused_3514_; 
v_unused_3514_ = lean_ctor_get(v_b_3437_, 0);
lean_dec(v_unused_3514_);
v___x_3447_ = v_b_3437_;
v_isShared_3448_ = v_isSharedCheck_3513_;
goto v_resetjp_3446_;
}
else
{
lean_inc(v_snd_3445_);
lean_dec(v_b_3437_);
v___x_3447_ = lean_box(0);
v_isShared_3448_ = v_isSharedCheck_3513_;
goto v_resetjp_3446_;
}
v_resetjp_3446_:
{
lean_object* v___x_3449_; lean_object* v_a_3451_; lean_object* v_a_3458_; 
v___x_3449_ = lean_box(0);
v_a_3458_ = lean_array_uget(v_as_3434_, v_i_3436_);
if (lean_obj_tag(v_a_3458_) == 0)
{
v_a_3451_ = v_snd_3445_;
goto v___jp_3450_;
}
else
{
lean_object* v_val_3459_; lean_object* v___x_3461_; uint8_t v_isShared_3462_; uint8_t v_isSharedCheck_3512_; 
v_val_3459_ = lean_ctor_get(v_a_3458_, 0);
v_isSharedCheck_3512_ = !lean_is_exclusive(v_a_3458_);
if (v_isSharedCheck_3512_ == 0)
{
v___x_3461_ = v_a_3458_;
v_isShared_3462_ = v_isSharedCheck_3512_;
goto v_resetjp_3460_;
}
else
{
lean_inc(v_val_3459_);
lean_dec(v_a_3458_);
v___x_3461_ = lean_box(0);
v_isShared_3462_ = v_isSharedCheck_3512_;
goto v_resetjp_3460_;
}
v_resetjp_3460_:
{
lean_object* v___x_3463_; 
lean_inc_ref(v_p_3432_);
lean_inc(v___y_3441_);
lean_inc_ref(v___y_3440_);
lean_inc(v___y_3439_);
lean_inc_ref(v___y_3438_);
lean_inc(v_val_3459_);
v___x_3463_ = lean_apply_6(v_p_3432_, v_val_3459_, v___y_3438_, v___y_3439_, v___y_3440_, v___y_3441_, lean_box(0));
if (lean_obj_tag(v___x_3463_) == 0)
{
lean_object* v_a_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; uint8_t v___x_3467_; 
v_a_3464_ = lean_ctor_get(v___x_3463_, 0);
lean_inc(v_a_3464_);
lean_dec_ref_known(v___x_3463_, 1);
v___x_3465_ = lean_box(0);
v___x_3466_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5___closed__0));
v___x_3467_ = lean_unbox(v_a_3464_);
lean_dec(v_a_3464_);
if (v___x_3467_ == 0)
{
lean_del_object(v___x_3461_);
lean_dec(v_val_3459_);
lean_dec(v_snd_3445_);
v_a_3451_ = v___x_3466_;
goto v___jp_3450_;
}
else
{
lean_object* v___x_3468_; lean_object* v___x_3469_; uint8_t v___x_3470_; lean_object* v___x_3471_; lean_object* v___f_3472_; lean_object* v___x_3473_; 
v___x_3468_ = l_Lean_LocalDecl_fvarId(v_val_3459_);
lean_dec(v_val_3459_);
v___x_3469_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5___closed__1));
v___x_3470_ = 0;
v___x_3471_ = lean_box(v___x_3470_);
lean_inc(v_mvarId_3433_);
v___f_3472_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3___lam__0___boxed), 10, 5);
lean_closure_set(v___f_3472_, 0, v_mvarId_3433_);
lean_closure_set(v___f_3472_, 1, v___x_3468_);
lean_closure_set(v___f_3472_, 2, v___x_3469_);
lean_closure_set(v___f_3472_, 3, v___x_3471_);
lean_closure_set(v___f_3472_, 4, v___x_3449_);
v___x_3473_ = l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1___redArg(v___f_3472_, v___y_3438_, v___y_3439_, v___y_3440_, v___y_3441_);
if (lean_obj_tag(v___x_3473_) == 0)
{
lean_object* v_a_3474_; lean_object* v___x_3476_; uint8_t v_isShared_3477_; uint8_t v_isSharedCheck_3495_; 
v_a_3474_ = lean_ctor_get(v___x_3473_, 0);
v_isSharedCheck_3495_ = !lean_is_exclusive(v___x_3473_);
if (v_isSharedCheck_3495_ == 0)
{
v___x_3476_ = v___x_3473_;
v_isShared_3477_ = v_isSharedCheck_3495_;
goto v_resetjp_3475_;
}
else
{
lean_inc(v_a_3474_);
lean_dec(v___x_3473_);
v___x_3476_ = lean_box(0);
v_isShared_3477_ = v_isSharedCheck_3495_;
goto v_resetjp_3475_;
}
v_resetjp_3475_:
{
if (lean_obj_tag(v_a_3474_) == 0)
{
lean_del_object(v___x_3476_);
lean_del_object(v___x_3461_);
lean_dec(v_snd_3445_);
v_a_3451_ = v___x_3466_;
goto v___jp_3450_;
}
else
{
lean_object* v___x_3479_; 
lean_del_object(v___x_3447_);
lean_dec(v_mvarId_3433_);
lean_dec_ref(v_p_3432_);
lean_inc_ref(v_a_3474_);
if (v_isShared_3462_ == 0)
{
lean_ctor_set(v___x_3461_, 0, v_a_3474_);
v___x_3479_ = v___x_3461_;
goto v_reusejp_3478_;
}
else
{
lean_object* v_reuseFailAlloc_3494_; 
v_reuseFailAlloc_3494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3494_, 0, v_a_3474_);
v___x_3479_ = v_reuseFailAlloc_3494_;
goto v_reusejp_3478_;
}
v_reusejp_3478_:
{
lean_object* v___x_3481_; uint8_t v_isShared_3482_; uint8_t v_isSharedCheck_3492_; 
v_isSharedCheck_3492_ = !lean_is_exclusive(v_a_3474_);
if (v_isSharedCheck_3492_ == 0)
{
lean_object* v_unused_3493_; 
v_unused_3493_ = lean_ctor_get(v_a_3474_, 0);
lean_dec(v_unused_3493_);
v___x_3481_ = v_a_3474_;
v_isShared_3482_ = v_isSharedCheck_3492_;
goto v_resetjp_3480_;
}
else
{
lean_dec(v_a_3474_);
v___x_3481_ = lean_box(0);
v_isShared_3482_ = v_isSharedCheck_3492_;
goto v_resetjp_3480_;
}
v_resetjp_3480_:
{
lean_object* v___x_3483_; lean_object* v___x_3485_; 
v___x_3483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3483_, 0, v___x_3479_);
lean_ctor_set(v___x_3483_, 1, v___x_3465_);
if (v_isShared_3482_ == 0)
{
lean_ctor_set_tag(v___x_3481_, 0);
lean_ctor_set(v___x_3481_, 0, v___x_3483_);
v___x_3485_ = v___x_3481_;
goto v_reusejp_3484_;
}
else
{
lean_object* v_reuseFailAlloc_3491_; 
v_reuseFailAlloc_3491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3491_, 0, v___x_3483_);
v___x_3485_ = v_reuseFailAlloc_3491_;
goto v_reusejp_3484_;
}
v_reusejp_3484_:
{
lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3489_; 
v___x_3486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3486_, 0, v___x_3485_);
v___x_3487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3487_, 0, v___x_3486_);
lean_ctor_set(v___x_3487_, 1, v_snd_3445_);
if (v_isShared_3477_ == 0)
{
lean_ctor_set(v___x_3476_, 0, v___x_3487_);
v___x_3489_ = v___x_3476_;
goto v_reusejp_3488_;
}
else
{
lean_object* v_reuseFailAlloc_3490_; 
v_reuseFailAlloc_3490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3490_, 0, v___x_3487_);
v___x_3489_ = v_reuseFailAlloc_3490_;
goto v_reusejp_3488_;
}
v_reusejp_3488_:
{
return v___x_3489_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3496_; lean_object* v___x_3498_; uint8_t v_isShared_3499_; uint8_t v_isSharedCheck_3503_; 
lean_del_object(v___x_3461_);
lean_del_object(v___x_3447_);
lean_dec(v_snd_3445_);
lean_dec(v_mvarId_3433_);
lean_dec_ref(v_p_3432_);
v_a_3496_ = lean_ctor_get(v___x_3473_, 0);
v_isSharedCheck_3503_ = !lean_is_exclusive(v___x_3473_);
if (v_isSharedCheck_3503_ == 0)
{
v___x_3498_ = v___x_3473_;
v_isShared_3499_ = v_isSharedCheck_3503_;
goto v_resetjp_3497_;
}
else
{
lean_inc(v_a_3496_);
lean_dec(v___x_3473_);
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
else
{
lean_object* v_a_3504_; lean_object* v___x_3506_; uint8_t v_isShared_3507_; uint8_t v_isSharedCheck_3511_; 
lean_del_object(v___x_3461_);
lean_dec(v_val_3459_);
lean_del_object(v___x_3447_);
lean_dec(v_snd_3445_);
lean_dec(v_mvarId_3433_);
lean_dec_ref(v_p_3432_);
v_a_3504_ = lean_ctor_get(v___x_3463_, 0);
v_isSharedCheck_3511_ = !lean_is_exclusive(v___x_3463_);
if (v_isSharedCheck_3511_ == 0)
{
v___x_3506_ = v___x_3463_;
v_isShared_3507_ = v_isSharedCheck_3511_;
goto v_resetjp_3505_;
}
else
{
lean_inc(v_a_3504_);
lean_dec(v___x_3463_);
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
v___jp_3450_:
{
lean_object* v___x_3453_; 
if (v_isShared_3448_ == 0)
{
lean_ctor_set(v___x_3447_, 1, v_a_3451_);
lean_ctor_set(v___x_3447_, 0, v___x_3449_);
v___x_3453_ = v___x_3447_;
goto v_reusejp_3452_;
}
else
{
lean_object* v_reuseFailAlloc_3457_; 
v_reuseFailAlloc_3457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3457_, 0, v___x_3449_);
lean_ctor_set(v_reuseFailAlloc_3457_, 1, v_a_3451_);
v___x_3453_ = v_reuseFailAlloc_3457_;
goto v_reusejp_3452_;
}
v_reusejp_3452_:
{
size_t v___x_3454_; size_t v___x_3455_; 
v___x_3454_ = ((size_t)1ULL);
v___x_3455_ = lean_usize_add(v_i_3436_, v___x_3454_);
v_i_3436_ = v___x_3455_;
v_b_3437_ = v___x_3453_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5___boxed(lean_object* v_p_3515_, lean_object* v_mvarId_3516_, lean_object* v_as_3517_, lean_object* v_sz_3518_, lean_object* v_i_3519_, lean_object* v_b_3520_, lean_object* v___y_3521_, lean_object* v___y_3522_, lean_object* v___y_3523_, lean_object* v___y_3524_, lean_object* v___y_3525_){
_start:
{
size_t v_sz_boxed_3526_; size_t v_i_boxed_3527_; lean_object* v_res_3528_; 
v_sz_boxed_3526_ = lean_unbox_usize(v_sz_3518_);
lean_dec(v_sz_3518_);
v_i_boxed_3527_ = lean_unbox_usize(v_i_3519_);
lean_dec(v_i_3519_);
v_res_3528_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5(v_p_3515_, v_mvarId_3516_, v_as_3517_, v_sz_boxed_3526_, v_i_boxed_3527_, v_b_3520_, v___y_3521_, v___y_3522_, v___y_3523_, v___y_3524_);
lean_dec(v___y_3524_);
lean_dec_ref(v___y_3523_);
lean_dec(v___y_3522_);
lean_dec_ref(v___y_3521_);
lean_dec_ref(v_as_3517_);
return v_res_3528_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4(lean_object* v_p_3529_, lean_object* v_mvarId_3530_, lean_object* v_as_3531_, size_t v_sz_3532_, size_t v_i_3533_, lean_object* v_b_3534_, lean_object* v___y_3535_, lean_object* v___y_3536_, lean_object* v___y_3537_, lean_object* v___y_3538_){
_start:
{
uint8_t v___x_3540_; 
v___x_3540_ = lean_usize_dec_lt(v_i_3533_, v_sz_3532_);
if (v___x_3540_ == 0)
{
lean_object* v___x_3541_; 
lean_dec(v_mvarId_3530_);
lean_dec_ref(v_p_3529_);
v___x_3541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3541_, 0, v_b_3534_);
return v___x_3541_;
}
else
{
lean_object* v_snd_3542_; lean_object* v___x_3544_; uint8_t v_isShared_3545_; uint8_t v_isSharedCheck_3610_; 
v_snd_3542_ = lean_ctor_get(v_b_3534_, 1);
v_isSharedCheck_3610_ = !lean_is_exclusive(v_b_3534_);
if (v_isSharedCheck_3610_ == 0)
{
lean_object* v_unused_3611_; 
v_unused_3611_ = lean_ctor_get(v_b_3534_, 0);
lean_dec(v_unused_3611_);
v___x_3544_ = v_b_3534_;
v_isShared_3545_ = v_isSharedCheck_3610_;
goto v_resetjp_3543_;
}
else
{
lean_inc(v_snd_3542_);
lean_dec(v_b_3534_);
v___x_3544_ = lean_box(0);
v_isShared_3545_ = v_isSharedCheck_3610_;
goto v_resetjp_3543_;
}
v_resetjp_3543_:
{
lean_object* v___x_3546_; lean_object* v_a_3548_; lean_object* v_a_3555_; 
v___x_3546_ = lean_box(0);
v_a_3555_ = lean_array_uget(v_as_3531_, v_i_3533_);
if (lean_obj_tag(v_a_3555_) == 0)
{
v_a_3548_ = v_snd_3542_;
goto v___jp_3547_;
}
else
{
lean_object* v_val_3556_; lean_object* v___x_3558_; uint8_t v_isShared_3559_; uint8_t v_isSharedCheck_3609_; 
v_val_3556_ = lean_ctor_get(v_a_3555_, 0);
v_isSharedCheck_3609_ = !lean_is_exclusive(v_a_3555_);
if (v_isSharedCheck_3609_ == 0)
{
v___x_3558_ = v_a_3555_;
v_isShared_3559_ = v_isSharedCheck_3609_;
goto v_resetjp_3557_;
}
else
{
lean_inc(v_val_3556_);
lean_dec(v_a_3555_);
v___x_3558_ = lean_box(0);
v_isShared_3559_ = v_isSharedCheck_3609_;
goto v_resetjp_3557_;
}
v_resetjp_3557_:
{
lean_object* v___x_3560_; 
lean_inc_ref(v_p_3529_);
lean_inc(v___y_3538_);
lean_inc_ref(v___y_3537_);
lean_inc(v___y_3536_);
lean_inc_ref(v___y_3535_);
lean_inc(v_val_3556_);
v___x_3560_ = lean_apply_6(v_p_3529_, v_val_3556_, v___y_3535_, v___y_3536_, v___y_3537_, v___y_3538_, lean_box(0));
if (lean_obj_tag(v___x_3560_) == 0)
{
lean_object* v_a_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; uint8_t v___x_3564_; 
v_a_3561_ = lean_ctor_get(v___x_3560_, 0);
lean_inc(v_a_3561_);
lean_dec_ref_known(v___x_3560_, 1);
v___x_3562_ = lean_box(0);
v___x_3563_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5___closed__0));
v___x_3564_ = lean_unbox(v_a_3561_);
lean_dec(v_a_3561_);
if (v___x_3564_ == 0)
{
lean_del_object(v___x_3558_);
lean_dec(v_val_3556_);
lean_dec(v_snd_3542_);
v_a_3548_ = v___x_3563_;
goto v___jp_3547_;
}
else
{
lean_object* v___x_3565_; lean_object* v___x_3566_; uint8_t v___x_3567_; lean_object* v___x_3568_; lean_object* v___f_3569_; lean_object* v___x_3570_; 
v___x_3565_ = l_Lean_LocalDecl_fvarId(v_val_3556_);
lean_dec(v_val_3556_);
v___x_3566_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5___closed__1));
v___x_3567_ = 0;
v___x_3568_ = lean_box(v___x_3567_);
lean_inc(v_mvarId_3530_);
v___f_3569_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3___lam__0___boxed), 10, 5);
lean_closure_set(v___f_3569_, 0, v_mvarId_3530_);
lean_closure_set(v___f_3569_, 1, v___x_3565_);
lean_closure_set(v___f_3569_, 2, v___x_3566_);
lean_closure_set(v___f_3569_, 3, v___x_3568_);
lean_closure_set(v___f_3569_, 4, v___x_3546_);
v___x_3570_ = l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1___redArg(v___f_3569_, v___y_3535_, v___y_3536_, v___y_3537_, v___y_3538_);
if (lean_obj_tag(v___x_3570_) == 0)
{
lean_object* v_a_3571_; lean_object* v___x_3573_; uint8_t v_isShared_3574_; uint8_t v_isSharedCheck_3592_; 
v_a_3571_ = lean_ctor_get(v___x_3570_, 0);
v_isSharedCheck_3592_ = !lean_is_exclusive(v___x_3570_);
if (v_isSharedCheck_3592_ == 0)
{
v___x_3573_ = v___x_3570_;
v_isShared_3574_ = v_isSharedCheck_3592_;
goto v_resetjp_3572_;
}
else
{
lean_inc(v_a_3571_);
lean_dec(v___x_3570_);
v___x_3573_ = lean_box(0);
v_isShared_3574_ = v_isSharedCheck_3592_;
goto v_resetjp_3572_;
}
v_resetjp_3572_:
{
if (lean_obj_tag(v_a_3571_) == 0)
{
lean_del_object(v___x_3573_);
lean_del_object(v___x_3558_);
lean_dec(v_snd_3542_);
v_a_3548_ = v___x_3563_;
goto v___jp_3547_;
}
else
{
lean_object* v___x_3576_; 
lean_del_object(v___x_3544_);
lean_dec(v_mvarId_3530_);
lean_dec_ref(v_p_3529_);
lean_inc_ref(v_a_3571_);
if (v_isShared_3559_ == 0)
{
lean_ctor_set(v___x_3558_, 0, v_a_3571_);
v___x_3576_ = v___x_3558_;
goto v_reusejp_3575_;
}
else
{
lean_object* v_reuseFailAlloc_3591_; 
v_reuseFailAlloc_3591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3591_, 0, v_a_3571_);
v___x_3576_ = v_reuseFailAlloc_3591_;
goto v_reusejp_3575_;
}
v_reusejp_3575_:
{
lean_object* v___x_3578_; uint8_t v_isShared_3579_; uint8_t v_isSharedCheck_3589_; 
v_isSharedCheck_3589_ = !lean_is_exclusive(v_a_3571_);
if (v_isSharedCheck_3589_ == 0)
{
lean_object* v_unused_3590_; 
v_unused_3590_ = lean_ctor_get(v_a_3571_, 0);
lean_dec(v_unused_3590_);
v___x_3578_ = v_a_3571_;
v_isShared_3579_ = v_isSharedCheck_3589_;
goto v_resetjp_3577_;
}
else
{
lean_dec(v_a_3571_);
v___x_3578_ = lean_box(0);
v_isShared_3579_ = v_isSharedCheck_3589_;
goto v_resetjp_3577_;
}
v_resetjp_3577_:
{
lean_object* v___x_3580_; lean_object* v___x_3582_; 
v___x_3580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3580_, 0, v___x_3576_);
lean_ctor_set(v___x_3580_, 1, v___x_3562_);
if (v_isShared_3579_ == 0)
{
lean_ctor_set_tag(v___x_3578_, 0);
lean_ctor_set(v___x_3578_, 0, v___x_3580_);
v___x_3582_ = v___x_3578_;
goto v_reusejp_3581_;
}
else
{
lean_object* v_reuseFailAlloc_3588_; 
v_reuseFailAlloc_3588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3588_, 0, v___x_3580_);
v___x_3582_ = v_reuseFailAlloc_3588_;
goto v_reusejp_3581_;
}
v_reusejp_3581_:
{
lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3586_; 
v___x_3583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3583_, 0, v___x_3582_);
v___x_3584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3584_, 0, v___x_3583_);
lean_ctor_set(v___x_3584_, 1, v_snd_3542_);
if (v_isShared_3574_ == 0)
{
lean_ctor_set(v___x_3573_, 0, v___x_3584_);
v___x_3586_ = v___x_3573_;
goto v_reusejp_3585_;
}
else
{
lean_object* v_reuseFailAlloc_3587_; 
v_reuseFailAlloc_3587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3587_, 0, v___x_3584_);
v___x_3586_ = v_reuseFailAlloc_3587_;
goto v_reusejp_3585_;
}
v_reusejp_3585_:
{
return v___x_3586_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3593_; lean_object* v___x_3595_; uint8_t v_isShared_3596_; uint8_t v_isSharedCheck_3600_; 
lean_del_object(v___x_3558_);
lean_del_object(v___x_3544_);
lean_dec(v_snd_3542_);
lean_dec(v_mvarId_3530_);
lean_dec_ref(v_p_3529_);
v_a_3593_ = lean_ctor_get(v___x_3570_, 0);
v_isSharedCheck_3600_ = !lean_is_exclusive(v___x_3570_);
if (v_isSharedCheck_3600_ == 0)
{
v___x_3595_ = v___x_3570_;
v_isShared_3596_ = v_isSharedCheck_3600_;
goto v_resetjp_3594_;
}
else
{
lean_inc(v_a_3593_);
lean_dec(v___x_3570_);
v___x_3595_ = lean_box(0);
v_isShared_3596_ = v_isSharedCheck_3600_;
goto v_resetjp_3594_;
}
v_resetjp_3594_:
{
lean_object* v___x_3598_; 
if (v_isShared_3596_ == 0)
{
v___x_3598_ = v___x_3595_;
goto v_reusejp_3597_;
}
else
{
lean_object* v_reuseFailAlloc_3599_; 
v_reuseFailAlloc_3599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3599_, 0, v_a_3593_);
v___x_3598_ = v_reuseFailAlloc_3599_;
goto v_reusejp_3597_;
}
v_reusejp_3597_:
{
return v___x_3598_;
}
}
}
}
}
else
{
lean_object* v_a_3601_; lean_object* v___x_3603_; uint8_t v_isShared_3604_; uint8_t v_isSharedCheck_3608_; 
lean_del_object(v___x_3558_);
lean_dec(v_val_3556_);
lean_del_object(v___x_3544_);
lean_dec(v_snd_3542_);
lean_dec(v_mvarId_3530_);
lean_dec_ref(v_p_3529_);
v_a_3601_ = lean_ctor_get(v___x_3560_, 0);
v_isSharedCheck_3608_ = !lean_is_exclusive(v___x_3560_);
if (v_isSharedCheck_3608_ == 0)
{
v___x_3603_ = v___x_3560_;
v_isShared_3604_ = v_isSharedCheck_3608_;
goto v_resetjp_3602_;
}
else
{
lean_inc(v_a_3601_);
lean_dec(v___x_3560_);
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
v___jp_3547_:
{
lean_object* v___x_3550_; 
if (v_isShared_3545_ == 0)
{
lean_ctor_set(v___x_3544_, 1, v_a_3548_);
lean_ctor_set(v___x_3544_, 0, v___x_3546_);
v___x_3550_ = v___x_3544_;
goto v_reusejp_3549_;
}
else
{
lean_object* v_reuseFailAlloc_3554_; 
v_reuseFailAlloc_3554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3554_, 0, v___x_3546_);
lean_ctor_set(v_reuseFailAlloc_3554_, 1, v_a_3548_);
v___x_3550_ = v_reuseFailAlloc_3554_;
goto v_reusejp_3549_;
}
v_reusejp_3549_:
{
size_t v___x_3551_; size_t v___x_3552_; lean_object* v___x_3553_; 
v___x_3551_ = ((size_t)1ULL);
v___x_3552_ = lean_usize_add(v_i_3533_, v___x_3551_);
v___x_3553_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5(v_p_3529_, v_mvarId_3530_, v_as_3531_, v_sz_3532_, v___x_3552_, v___x_3550_, v___y_3535_, v___y_3536_, v___y_3537_, v___y_3538_);
return v___x_3553_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4___boxed(lean_object* v_p_3612_, lean_object* v_mvarId_3613_, lean_object* v_as_3614_, lean_object* v_sz_3615_, lean_object* v_i_3616_, lean_object* v_b_3617_, lean_object* v___y_3618_, lean_object* v___y_3619_, lean_object* v___y_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_){
_start:
{
size_t v_sz_boxed_3623_; size_t v_i_boxed_3624_; lean_object* v_res_3625_; 
v_sz_boxed_3623_ = lean_unbox_usize(v_sz_3615_);
lean_dec(v_sz_3615_);
v_i_boxed_3624_ = lean_unbox_usize(v_i_3616_);
lean_dec(v_i_3616_);
v_res_3625_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4(v_p_3612_, v_mvarId_3613_, v_as_3614_, v_sz_boxed_3623_, v_i_boxed_3624_, v_b_3617_, v___y_3618_, v___y_3619_, v___y_3620_, v___y_3621_);
lean_dec(v___y_3621_);
lean_dec_ref(v___y_3620_);
lean_dec(v___y_3619_);
lean_dec_ref(v___y_3618_);
lean_dec_ref(v_as_3614_);
return v_res_3625_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2(lean_object* v_init_3626_, lean_object* v_p_3627_, lean_object* v_mvarId_3628_, lean_object* v_n_3629_, lean_object* v_b_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_){
_start:
{
if (lean_obj_tag(v_n_3629_) == 0)
{
lean_object* v_cs_3636_; lean_object* v___x_3637_; lean_object* v___x_3638_; size_t v_sz_3639_; size_t v___x_3640_; lean_object* v___x_3641_; 
v_cs_3636_ = lean_ctor_get(v_n_3629_, 0);
v___x_3637_ = lean_box(0);
v___x_3638_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3638_, 0, v___x_3637_);
lean_ctor_set(v___x_3638_, 1, v_b_3630_);
v_sz_3639_ = lean_array_size(v_cs_3636_);
v___x_3640_ = ((size_t)0ULL);
v___x_3641_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__3(v_init_3626_, v_p_3627_, v_mvarId_3628_, v_cs_3636_, v_sz_3639_, v___x_3640_, v___x_3638_, v___y_3631_, v___y_3632_, v___y_3633_, v___y_3634_);
if (lean_obj_tag(v___x_3641_) == 0)
{
lean_object* v_a_3642_; lean_object* v___x_3644_; uint8_t v_isShared_3645_; uint8_t v_isSharedCheck_3656_; 
v_a_3642_ = lean_ctor_get(v___x_3641_, 0);
v_isSharedCheck_3656_ = !lean_is_exclusive(v___x_3641_);
if (v_isSharedCheck_3656_ == 0)
{
v___x_3644_ = v___x_3641_;
v_isShared_3645_ = v_isSharedCheck_3656_;
goto v_resetjp_3643_;
}
else
{
lean_inc(v_a_3642_);
lean_dec(v___x_3641_);
v___x_3644_ = lean_box(0);
v_isShared_3645_ = v_isSharedCheck_3656_;
goto v_resetjp_3643_;
}
v_resetjp_3643_:
{
lean_object* v_fst_3646_; 
v_fst_3646_ = lean_ctor_get(v_a_3642_, 0);
if (lean_obj_tag(v_fst_3646_) == 0)
{
lean_object* v_snd_3647_; lean_object* v___x_3648_; lean_object* v___x_3650_; 
v_snd_3647_ = lean_ctor_get(v_a_3642_, 1);
lean_inc(v_snd_3647_);
lean_dec(v_a_3642_);
v___x_3648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3648_, 0, v_snd_3647_);
if (v_isShared_3645_ == 0)
{
lean_ctor_set(v___x_3644_, 0, v___x_3648_);
v___x_3650_ = v___x_3644_;
goto v_reusejp_3649_;
}
else
{
lean_object* v_reuseFailAlloc_3651_; 
v_reuseFailAlloc_3651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3651_, 0, v___x_3648_);
v___x_3650_ = v_reuseFailAlloc_3651_;
goto v_reusejp_3649_;
}
v_reusejp_3649_:
{
return v___x_3650_;
}
}
else
{
lean_object* v_val_3652_; lean_object* v___x_3654_; 
lean_inc_ref(v_fst_3646_);
lean_dec(v_a_3642_);
v_val_3652_ = lean_ctor_get(v_fst_3646_, 0);
lean_inc(v_val_3652_);
lean_dec_ref_known(v_fst_3646_, 1);
if (v_isShared_3645_ == 0)
{
lean_ctor_set(v___x_3644_, 0, v_val_3652_);
v___x_3654_ = v___x_3644_;
goto v_reusejp_3653_;
}
else
{
lean_object* v_reuseFailAlloc_3655_; 
v_reuseFailAlloc_3655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3655_, 0, v_val_3652_);
v___x_3654_ = v_reuseFailAlloc_3655_;
goto v_reusejp_3653_;
}
v_reusejp_3653_:
{
return v___x_3654_;
}
}
}
}
else
{
lean_object* v_a_3657_; lean_object* v___x_3659_; uint8_t v_isShared_3660_; uint8_t v_isSharedCheck_3664_; 
v_a_3657_ = lean_ctor_get(v___x_3641_, 0);
v_isSharedCheck_3664_ = !lean_is_exclusive(v___x_3641_);
if (v_isSharedCheck_3664_ == 0)
{
v___x_3659_ = v___x_3641_;
v_isShared_3660_ = v_isSharedCheck_3664_;
goto v_resetjp_3658_;
}
else
{
lean_inc(v_a_3657_);
lean_dec(v___x_3641_);
v___x_3659_ = lean_box(0);
v_isShared_3660_ = v_isSharedCheck_3664_;
goto v_resetjp_3658_;
}
v_resetjp_3658_:
{
lean_object* v___x_3662_; 
if (v_isShared_3660_ == 0)
{
v___x_3662_ = v___x_3659_;
goto v_reusejp_3661_;
}
else
{
lean_object* v_reuseFailAlloc_3663_; 
v_reuseFailAlloc_3663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3663_, 0, v_a_3657_);
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
lean_object* v_vs_3665_; lean_object* v___x_3666_; lean_object* v___x_3667_; size_t v_sz_3668_; size_t v___x_3669_; lean_object* v___x_3670_; 
v_vs_3665_ = lean_ctor_get(v_n_3629_, 0);
v___x_3666_ = lean_box(0);
v___x_3667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3667_, 0, v___x_3666_);
lean_ctor_set(v___x_3667_, 1, v_b_3630_);
v_sz_3668_ = lean_array_size(v_vs_3665_);
v___x_3669_ = ((size_t)0ULL);
v___x_3670_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4(v_p_3627_, v_mvarId_3628_, v_vs_3665_, v_sz_3668_, v___x_3669_, v___x_3667_, v___y_3631_, v___y_3632_, v___y_3633_, v___y_3634_);
if (lean_obj_tag(v___x_3670_) == 0)
{
lean_object* v_a_3671_; lean_object* v___x_3673_; uint8_t v_isShared_3674_; uint8_t v_isSharedCheck_3685_; 
v_a_3671_ = lean_ctor_get(v___x_3670_, 0);
v_isSharedCheck_3685_ = !lean_is_exclusive(v___x_3670_);
if (v_isSharedCheck_3685_ == 0)
{
v___x_3673_ = v___x_3670_;
v_isShared_3674_ = v_isSharedCheck_3685_;
goto v_resetjp_3672_;
}
else
{
lean_inc(v_a_3671_);
lean_dec(v___x_3670_);
v___x_3673_ = lean_box(0);
v_isShared_3674_ = v_isSharedCheck_3685_;
goto v_resetjp_3672_;
}
v_resetjp_3672_:
{
lean_object* v_fst_3675_; 
v_fst_3675_ = lean_ctor_get(v_a_3671_, 0);
if (lean_obj_tag(v_fst_3675_) == 0)
{
lean_object* v_snd_3676_; lean_object* v___x_3677_; lean_object* v___x_3679_; 
v_snd_3676_ = lean_ctor_get(v_a_3671_, 1);
lean_inc(v_snd_3676_);
lean_dec(v_a_3671_);
v___x_3677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3677_, 0, v_snd_3676_);
if (v_isShared_3674_ == 0)
{
lean_ctor_set(v___x_3673_, 0, v___x_3677_);
v___x_3679_ = v___x_3673_;
goto v_reusejp_3678_;
}
else
{
lean_object* v_reuseFailAlloc_3680_; 
v_reuseFailAlloc_3680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3680_, 0, v___x_3677_);
v___x_3679_ = v_reuseFailAlloc_3680_;
goto v_reusejp_3678_;
}
v_reusejp_3678_:
{
return v___x_3679_;
}
}
else
{
lean_object* v_val_3681_; lean_object* v___x_3683_; 
lean_inc_ref(v_fst_3675_);
lean_dec(v_a_3671_);
v_val_3681_ = lean_ctor_get(v_fst_3675_, 0);
lean_inc(v_val_3681_);
lean_dec_ref_known(v_fst_3675_, 1);
if (v_isShared_3674_ == 0)
{
lean_ctor_set(v___x_3673_, 0, v_val_3681_);
v___x_3683_ = v___x_3673_;
goto v_reusejp_3682_;
}
else
{
lean_object* v_reuseFailAlloc_3684_; 
v_reuseFailAlloc_3684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3684_, 0, v_val_3681_);
v___x_3683_ = v_reuseFailAlloc_3684_;
goto v_reusejp_3682_;
}
v_reusejp_3682_:
{
return v___x_3683_;
}
}
}
}
else
{
lean_object* v_a_3686_; lean_object* v___x_3688_; uint8_t v_isShared_3689_; uint8_t v_isSharedCheck_3693_; 
v_a_3686_ = lean_ctor_get(v___x_3670_, 0);
v_isSharedCheck_3693_ = !lean_is_exclusive(v___x_3670_);
if (v_isSharedCheck_3693_ == 0)
{
v___x_3688_ = v___x_3670_;
v_isShared_3689_ = v_isSharedCheck_3693_;
goto v_resetjp_3687_;
}
else
{
lean_inc(v_a_3686_);
lean_dec(v___x_3670_);
v___x_3688_ = lean_box(0);
v_isShared_3689_ = v_isSharedCheck_3693_;
goto v_resetjp_3687_;
}
v_resetjp_3687_:
{
lean_object* v___x_3691_; 
if (v_isShared_3689_ == 0)
{
v___x_3691_ = v___x_3688_;
goto v_reusejp_3690_;
}
else
{
lean_object* v_reuseFailAlloc_3692_; 
v_reuseFailAlloc_3692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3692_, 0, v_a_3686_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__3(lean_object* v_init_3694_, lean_object* v_p_3695_, lean_object* v_mvarId_3696_, lean_object* v_as_3697_, size_t v_sz_3698_, size_t v_i_3699_, lean_object* v_b_3700_, lean_object* v___y_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_){
_start:
{
uint8_t v___x_3706_; 
v___x_3706_ = lean_usize_dec_lt(v_i_3699_, v_sz_3698_);
if (v___x_3706_ == 0)
{
lean_object* v___x_3707_; 
lean_dec(v_mvarId_3696_);
lean_dec_ref(v_p_3695_);
v___x_3707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3707_, 0, v_b_3700_);
return v___x_3707_;
}
else
{
lean_object* v_snd_3708_; lean_object* v___x_3710_; uint8_t v_isShared_3711_; uint8_t v_isSharedCheck_3742_; 
v_snd_3708_ = lean_ctor_get(v_b_3700_, 1);
v_isSharedCheck_3742_ = !lean_is_exclusive(v_b_3700_);
if (v_isSharedCheck_3742_ == 0)
{
lean_object* v_unused_3743_; 
v_unused_3743_ = lean_ctor_get(v_b_3700_, 0);
lean_dec(v_unused_3743_);
v___x_3710_ = v_b_3700_;
v_isShared_3711_ = v_isSharedCheck_3742_;
goto v_resetjp_3709_;
}
else
{
lean_inc(v_snd_3708_);
lean_dec(v_b_3700_);
v___x_3710_ = lean_box(0);
v_isShared_3711_ = v_isSharedCheck_3742_;
goto v_resetjp_3709_;
}
v_resetjp_3709_:
{
lean_object* v_a_3712_; lean_object* v___x_3713_; 
v_a_3712_ = lean_array_uget_borrowed(v_as_3697_, v_i_3699_);
lean_inc(v_snd_3708_);
lean_inc(v_mvarId_3696_);
lean_inc_ref(v_p_3695_);
v___x_3713_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2(v_init_3694_, v_p_3695_, v_mvarId_3696_, v_a_3712_, v_snd_3708_, v___y_3701_, v___y_3702_, v___y_3703_, v___y_3704_);
if (lean_obj_tag(v___x_3713_) == 0)
{
lean_object* v_a_3714_; lean_object* v___x_3716_; uint8_t v_isShared_3717_; uint8_t v_isSharedCheck_3733_; 
v_a_3714_ = lean_ctor_get(v___x_3713_, 0);
v_isSharedCheck_3733_ = !lean_is_exclusive(v___x_3713_);
if (v_isSharedCheck_3733_ == 0)
{
v___x_3716_ = v___x_3713_;
v_isShared_3717_ = v_isSharedCheck_3733_;
goto v_resetjp_3715_;
}
else
{
lean_inc(v_a_3714_);
lean_dec(v___x_3713_);
v___x_3716_ = lean_box(0);
v_isShared_3717_ = v_isSharedCheck_3733_;
goto v_resetjp_3715_;
}
v_resetjp_3715_:
{
if (lean_obj_tag(v_a_3714_) == 0)
{
lean_object* v___x_3718_; lean_object* v___x_3720_; 
lean_dec(v_mvarId_3696_);
lean_dec_ref(v_p_3695_);
v___x_3718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3718_, 0, v_a_3714_);
if (v_isShared_3711_ == 0)
{
lean_ctor_set(v___x_3710_, 0, v___x_3718_);
v___x_3720_ = v___x_3710_;
goto v_reusejp_3719_;
}
else
{
lean_object* v_reuseFailAlloc_3724_; 
v_reuseFailAlloc_3724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3724_, 0, v___x_3718_);
lean_ctor_set(v_reuseFailAlloc_3724_, 1, v_snd_3708_);
v___x_3720_ = v_reuseFailAlloc_3724_;
goto v_reusejp_3719_;
}
v_reusejp_3719_:
{
lean_object* v___x_3722_; 
if (v_isShared_3717_ == 0)
{
lean_ctor_set(v___x_3716_, 0, v___x_3720_);
v___x_3722_ = v___x_3716_;
goto v_reusejp_3721_;
}
else
{
lean_object* v_reuseFailAlloc_3723_; 
v_reuseFailAlloc_3723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3723_, 0, v___x_3720_);
v___x_3722_ = v_reuseFailAlloc_3723_;
goto v_reusejp_3721_;
}
v_reusejp_3721_:
{
return v___x_3722_;
}
}
}
else
{
lean_object* v_a_3725_; lean_object* v___x_3726_; lean_object* v___x_3728_; 
lean_del_object(v___x_3716_);
lean_dec(v_snd_3708_);
v_a_3725_ = lean_ctor_get(v_a_3714_, 0);
lean_inc(v_a_3725_);
lean_dec_ref_known(v_a_3714_, 1);
v___x_3726_ = lean_box(0);
if (v_isShared_3711_ == 0)
{
lean_ctor_set(v___x_3710_, 1, v_a_3725_);
lean_ctor_set(v___x_3710_, 0, v___x_3726_);
v___x_3728_ = v___x_3710_;
goto v_reusejp_3727_;
}
else
{
lean_object* v_reuseFailAlloc_3732_; 
v_reuseFailAlloc_3732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3732_, 0, v___x_3726_);
lean_ctor_set(v_reuseFailAlloc_3732_, 1, v_a_3725_);
v___x_3728_ = v_reuseFailAlloc_3732_;
goto v_reusejp_3727_;
}
v_reusejp_3727_:
{
size_t v___x_3729_; size_t v___x_3730_; 
v___x_3729_ = ((size_t)1ULL);
v___x_3730_ = lean_usize_add(v_i_3699_, v___x_3729_);
v_i_3699_ = v___x_3730_;
v_b_3700_ = v___x_3728_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3734_; lean_object* v___x_3736_; uint8_t v_isShared_3737_; uint8_t v_isSharedCheck_3741_; 
lean_del_object(v___x_3710_);
lean_dec(v_snd_3708_);
lean_dec(v_mvarId_3696_);
lean_dec_ref(v_p_3695_);
v_a_3734_ = lean_ctor_get(v___x_3713_, 0);
v_isSharedCheck_3741_ = !lean_is_exclusive(v___x_3713_);
if (v_isSharedCheck_3741_ == 0)
{
v___x_3736_ = v___x_3713_;
v_isShared_3737_ = v_isSharedCheck_3741_;
goto v_resetjp_3735_;
}
else
{
lean_inc(v_a_3734_);
lean_dec(v___x_3713_);
v___x_3736_ = lean_box(0);
v_isShared_3737_ = v_isSharedCheck_3741_;
goto v_resetjp_3735_;
}
v_resetjp_3735_:
{
lean_object* v___x_3739_; 
if (v_isShared_3737_ == 0)
{
v___x_3739_ = v___x_3736_;
goto v_reusejp_3738_;
}
else
{
lean_object* v_reuseFailAlloc_3740_; 
v_reuseFailAlloc_3740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3740_, 0, v_a_3734_);
v___x_3739_ = v_reuseFailAlloc_3740_;
goto v_reusejp_3738_;
}
v_reusejp_3738_:
{
return v___x_3739_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__3___boxed(lean_object* v_init_3744_, lean_object* v_p_3745_, lean_object* v_mvarId_3746_, lean_object* v_as_3747_, lean_object* v_sz_3748_, lean_object* v_i_3749_, lean_object* v_b_3750_, lean_object* v___y_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_){
_start:
{
size_t v_sz_boxed_3756_; size_t v_i_boxed_3757_; lean_object* v_res_3758_; 
v_sz_boxed_3756_ = lean_unbox_usize(v_sz_3748_);
lean_dec(v_sz_3748_);
v_i_boxed_3757_ = lean_unbox_usize(v_i_3749_);
lean_dec(v_i_3749_);
v_res_3758_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__3(v_init_3744_, v_p_3745_, v_mvarId_3746_, v_as_3747_, v_sz_boxed_3756_, v_i_boxed_3757_, v_b_3750_, v___y_3751_, v___y_3752_, v___y_3753_, v___y_3754_);
lean_dec(v___y_3754_);
lean_dec_ref(v___y_3753_);
lean_dec(v___y_3752_);
lean_dec_ref(v___y_3751_);
lean_dec_ref(v_as_3747_);
lean_dec_ref(v_init_3744_);
return v_res_3758_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2___boxed(lean_object* v_init_3759_, lean_object* v_p_3760_, lean_object* v_mvarId_3761_, lean_object* v_n_3762_, lean_object* v_b_3763_, lean_object* v___y_3764_, lean_object* v___y_3765_, lean_object* v___y_3766_, lean_object* v___y_3767_, lean_object* v___y_3768_){
_start:
{
lean_object* v_res_3769_; 
v_res_3769_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2(v_init_3759_, v_p_3760_, v_mvarId_3761_, v_n_3762_, v_b_3763_, v___y_3764_, v___y_3765_, v___y_3766_, v___y_3767_);
lean_dec(v___y_3767_);
lean_dec_ref(v___y_3766_);
lean_dec(v___y_3765_);
lean_dec_ref(v___y_3764_);
lean_dec_ref(v_n_3762_);
lean_dec_ref(v_init_3759_);
return v_res_3769_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3_spec__6(lean_object* v_p_3773_, lean_object* v_mvarId_3774_, lean_object* v_as_3775_, size_t v_sz_3776_, size_t v_i_3777_, lean_object* v_b_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_, lean_object* v___y_3782_){
_start:
{
uint8_t v___x_3784_; 
v___x_3784_ = lean_usize_dec_lt(v_i_3777_, v_sz_3776_);
if (v___x_3784_ == 0)
{
lean_object* v___x_3785_; 
lean_dec(v_mvarId_3774_);
lean_dec_ref(v_p_3773_);
v___x_3785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3785_, 0, v_b_3778_);
return v___x_3785_;
}
else
{
lean_object* v_snd_3786_; lean_object* v___x_3788_; uint8_t v_isShared_3789_; uint8_t v_isSharedCheck_3853_; 
v_snd_3786_ = lean_ctor_get(v_b_3778_, 1);
v_isSharedCheck_3853_ = !lean_is_exclusive(v_b_3778_);
if (v_isSharedCheck_3853_ == 0)
{
lean_object* v_unused_3854_; 
v_unused_3854_ = lean_ctor_get(v_b_3778_, 0);
lean_dec(v_unused_3854_);
v___x_3788_ = v_b_3778_;
v_isShared_3789_ = v_isSharedCheck_3853_;
goto v_resetjp_3787_;
}
else
{
lean_inc(v_snd_3786_);
lean_dec(v_b_3778_);
v___x_3788_ = lean_box(0);
v_isShared_3789_ = v_isSharedCheck_3853_;
goto v_resetjp_3787_;
}
v_resetjp_3787_:
{
lean_object* v___x_3790_; lean_object* v_a_3792_; lean_object* v_a_3799_; 
v___x_3790_ = lean_box(0);
v_a_3799_ = lean_array_uget(v_as_3775_, v_i_3777_);
if (lean_obj_tag(v_a_3799_) == 0)
{
v_a_3792_ = v_snd_3786_;
goto v___jp_3791_;
}
else
{
lean_object* v_val_3800_; lean_object* v___x_3802_; uint8_t v_isShared_3803_; uint8_t v_isSharedCheck_3852_; 
v_val_3800_ = lean_ctor_get(v_a_3799_, 0);
v_isSharedCheck_3852_ = !lean_is_exclusive(v_a_3799_);
if (v_isSharedCheck_3852_ == 0)
{
v___x_3802_ = v_a_3799_;
v_isShared_3803_ = v_isSharedCheck_3852_;
goto v_resetjp_3801_;
}
else
{
lean_inc(v_val_3800_);
lean_dec(v_a_3799_);
v___x_3802_ = lean_box(0);
v_isShared_3803_ = v_isSharedCheck_3852_;
goto v_resetjp_3801_;
}
v_resetjp_3801_:
{
lean_object* v___x_3804_; 
lean_inc_ref(v_p_3773_);
lean_inc(v___y_3782_);
lean_inc_ref(v___y_3781_);
lean_inc(v___y_3780_);
lean_inc_ref(v___y_3779_);
lean_inc(v_val_3800_);
v___x_3804_ = lean_apply_6(v_p_3773_, v_val_3800_, v___y_3779_, v___y_3780_, v___y_3781_, v___y_3782_, lean_box(0));
if (lean_obj_tag(v___x_3804_) == 0)
{
lean_object* v_a_3805_; lean_object* v___x_3806_; lean_object* v___x_3807_; uint8_t v___x_3808_; 
v_a_3805_ = lean_ctor_get(v___x_3804_, 0);
lean_inc(v_a_3805_);
lean_dec_ref_known(v___x_3804_, 1);
v___x_3806_ = lean_box(0);
v___x_3807_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3_spec__6___closed__0));
v___x_3808_ = lean_unbox(v_a_3805_);
lean_dec(v_a_3805_);
if (v___x_3808_ == 0)
{
lean_del_object(v___x_3802_);
lean_dec(v_val_3800_);
lean_dec(v_snd_3786_);
v_a_3792_ = v___x_3807_;
goto v___jp_3791_;
}
else
{
lean_object* v___x_3809_; lean_object* v___x_3810_; uint8_t v___x_3811_; lean_object* v___x_3812_; lean_object* v___f_3813_; lean_object* v___x_3814_; 
v___x_3809_ = l_Lean_LocalDecl_fvarId(v_val_3800_);
lean_dec(v_val_3800_);
v___x_3810_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5___closed__1));
v___x_3811_ = 0;
v___x_3812_ = lean_box(v___x_3811_);
lean_inc(v_mvarId_3774_);
v___f_3813_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3___lam__0___boxed), 10, 5);
lean_closure_set(v___f_3813_, 0, v_mvarId_3774_);
lean_closure_set(v___f_3813_, 1, v___x_3809_);
lean_closure_set(v___f_3813_, 2, v___x_3810_);
lean_closure_set(v___f_3813_, 3, v___x_3812_);
lean_closure_set(v___f_3813_, 4, v___x_3790_);
v___x_3814_ = l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1___redArg(v___f_3813_, v___y_3779_, v___y_3780_, v___y_3781_, v___y_3782_);
if (lean_obj_tag(v___x_3814_) == 0)
{
lean_object* v_a_3815_; lean_object* v___x_3817_; uint8_t v_isShared_3818_; uint8_t v_isSharedCheck_3835_; 
v_a_3815_ = lean_ctor_get(v___x_3814_, 0);
v_isSharedCheck_3835_ = !lean_is_exclusive(v___x_3814_);
if (v_isSharedCheck_3835_ == 0)
{
v___x_3817_ = v___x_3814_;
v_isShared_3818_ = v_isSharedCheck_3835_;
goto v_resetjp_3816_;
}
else
{
lean_inc(v_a_3815_);
lean_dec(v___x_3814_);
v___x_3817_ = lean_box(0);
v_isShared_3818_ = v_isSharedCheck_3835_;
goto v_resetjp_3816_;
}
v_resetjp_3816_:
{
if (lean_obj_tag(v_a_3815_) == 0)
{
lean_del_object(v___x_3817_);
lean_del_object(v___x_3802_);
lean_dec(v_snd_3786_);
v_a_3792_ = v___x_3807_;
goto v___jp_3791_;
}
else
{
lean_object* v___x_3820_; 
lean_del_object(v___x_3788_);
lean_dec(v_mvarId_3774_);
lean_dec_ref(v_p_3773_);
lean_inc_ref(v_a_3815_);
if (v_isShared_3803_ == 0)
{
lean_ctor_set(v___x_3802_, 0, v_a_3815_);
v___x_3820_ = v___x_3802_;
goto v_reusejp_3819_;
}
else
{
lean_object* v_reuseFailAlloc_3834_; 
v_reuseFailAlloc_3834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3834_, 0, v_a_3815_);
v___x_3820_ = v_reuseFailAlloc_3834_;
goto v_reusejp_3819_;
}
v_reusejp_3819_:
{
lean_object* v___x_3822_; uint8_t v_isShared_3823_; uint8_t v_isSharedCheck_3832_; 
v_isSharedCheck_3832_ = !lean_is_exclusive(v_a_3815_);
if (v_isSharedCheck_3832_ == 0)
{
lean_object* v_unused_3833_; 
v_unused_3833_ = lean_ctor_get(v_a_3815_, 0);
lean_dec(v_unused_3833_);
v___x_3822_ = v_a_3815_;
v_isShared_3823_ = v_isSharedCheck_3832_;
goto v_resetjp_3821_;
}
else
{
lean_dec(v_a_3815_);
v___x_3822_ = lean_box(0);
v_isShared_3823_ = v_isSharedCheck_3832_;
goto v_resetjp_3821_;
}
v_resetjp_3821_:
{
lean_object* v___x_3824_; lean_object* v___x_3826_; 
v___x_3824_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3824_, 0, v___x_3820_);
lean_ctor_set(v___x_3824_, 1, v___x_3806_);
if (v_isShared_3823_ == 0)
{
lean_ctor_set(v___x_3822_, 0, v___x_3824_);
v___x_3826_ = v___x_3822_;
goto v_reusejp_3825_;
}
else
{
lean_object* v_reuseFailAlloc_3831_; 
v_reuseFailAlloc_3831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3831_, 0, v___x_3824_);
v___x_3826_ = v_reuseFailAlloc_3831_;
goto v_reusejp_3825_;
}
v_reusejp_3825_:
{
lean_object* v___x_3827_; lean_object* v___x_3829_; 
v___x_3827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3827_, 0, v___x_3826_);
lean_ctor_set(v___x_3827_, 1, v_snd_3786_);
if (v_isShared_3818_ == 0)
{
lean_ctor_set(v___x_3817_, 0, v___x_3827_);
v___x_3829_ = v___x_3817_;
goto v_reusejp_3828_;
}
else
{
lean_object* v_reuseFailAlloc_3830_; 
v_reuseFailAlloc_3830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3830_, 0, v___x_3827_);
v___x_3829_ = v_reuseFailAlloc_3830_;
goto v_reusejp_3828_;
}
v_reusejp_3828_:
{
return v___x_3829_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3836_; lean_object* v___x_3838_; uint8_t v_isShared_3839_; uint8_t v_isSharedCheck_3843_; 
lean_del_object(v___x_3802_);
lean_del_object(v___x_3788_);
lean_dec(v_snd_3786_);
lean_dec(v_mvarId_3774_);
lean_dec_ref(v_p_3773_);
v_a_3836_ = lean_ctor_get(v___x_3814_, 0);
v_isSharedCheck_3843_ = !lean_is_exclusive(v___x_3814_);
if (v_isSharedCheck_3843_ == 0)
{
v___x_3838_ = v___x_3814_;
v_isShared_3839_ = v_isSharedCheck_3843_;
goto v_resetjp_3837_;
}
else
{
lean_inc(v_a_3836_);
lean_dec(v___x_3814_);
v___x_3838_ = lean_box(0);
v_isShared_3839_ = v_isSharedCheck_3843_;
goto v_resetjp_3837_;
}
v_resetjp_3837_:
{
lean_object* v___x_3841_; 
if (v_isShared_3839_ == 0)
{
v___x_3841_ = v___x_3838_;
goto v_reusejp_3840_;
}
else
{
lean_object* v_reuseFailAlloc_3842_; 
v_reuseFailAlloc_3842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3842_, 0, v_a_3836_);
v___x_3841_ = v_reuseFailAlloc_3842_;
goto v_reusejp_3840_;
}
v_reusejp_3840_:
{
return v___x_3841_;
}
}
}
}
}
else
{
lean_object* v_a_3844_; lean_object* v___x_3846_; uint8_t v_isShared_3847_; uint8_t v_isSharedCheck_3851_; 
lean_del_object(v___x_3802_);
lean_dec(v_val_3800_);
lean_del_object(v___x_3788_);
lean_dec(v_snd_3786_);
lean_dec(v_mvarId_3774_);
lean_dec_ref(v_p_3773_);
v_a_3844_ = lean_ctor_get(v___x_3804_, 0);
v_isSharedCheck_3851_ = !lean_is_exclusive(v___x_3804_);
if (v_isSharedCheck_3851_ == 0)
{
v___x_3846_ = v___x_3804_;
v_isShared_3847_ = v_isSharedCheck_3851_;
goto v_resetjp_3845_;
}
else
{
lean_inc(v_a_3844_);
lean_dec(v___x_3804_);
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
v___jp_3791_:
{
lean_object* v___x_3794_; 
if (v_isShared_3789_ == 0)
{
lean_ctor_set(v___x_3788_, 1, v_a_3792_);
lean_ctor_set(v___x_3788_, 0, v___x_3790_);
v___x_3794_ = v___x_3788_;
goto v_reusejp_3793_;
}
else
{
lean_object* v_reuseFailAlloc_3798_; 
v_reuseFailAlloc_3798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3798_, 0, v___x_3790_);
lean_ctor_set(v_reuseFailAlloc_3798_, 1, v_a_3792_);
v___x_3794_ = v_reuseFailAlloc_3798_;
goto v_reusejp_3793_;
}
v_reusejp_3793_:
{
size_t v___x_3795_; size_t v___x_3796_; 
v___x_3795_ = ((size_t)1ULL);
v___x_3796_ = lean_usize_add(v_i_3777_, v___x_3795_);
v_i_3777_ = v___x_3796_;
v_b_3778_ = v___x_3794_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3_spec__6___boxed(lean_object* v_p_3855_, lean_object* v_mvarId_3856_, lean_object* v_as_3857_, lean_object* v_sz_3858_, lean_object* v_i_3859_, lean_object* v_b_3860_, lean_object* v___y_3861_, lean_object* v___y_3862_, lean_object* v___y_3863_, lean_object* v___y_3864_, lean_object* v___y_3865_){
_start:
{
size_t v_sz_boxed_3866_; size_t v_i_boxed_3867_; lean_object* v_res_3868_; 
v_sz_boxed_3866_ = lean_unbox_usize(v_sz_3858_);
lean_dec(v_sz_3858_);
v_i_boxed_3867_ = lean_unbox_usize(v_i_3859_);
lean_dec(v_i_3859_);
v_res_3868_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3_spec__6(v_p_3855_, v_mvarId_3856_, v_as_3857_, v_sz_boxed_3866_, v_i_boxed_3867_, v_b_3860_, v___y_3861_, v___y_3862_, v___y_3863_, v___y_3864_);
lean_dec(v___y_3864_);
lean_dec_ref(v___y_3863_);
lean_dec(v___y_3862_);
lean_dec_ref(v___y_3861_);
lean_dec_ref(v_as_3857_);
return v_res_3868_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3(lean_object* v_p_3869_, lean_object* v_mvarId_3870_, lean_object* v_as_3871_, size_t v_sz_3872_, size_t v_i_3873_, lean_object* v_b_3874_, lean_object* v___y_3875_, lean_object* v___y_3876_, lean_object* v___y_3877_, lean_object* v___y_3878_){
_start:
{
uint8_t v___x_3880_; 
v___x_3880_ = lean_usize_dec_lt(v_i_3873_, v_sz_3872_);
if (v___x_3880_ == 0)
{
lean_object* v___x_3881_; 
lean_dec(v_mvarId_3870_);
lean_dec_ref(v_p_3869_);
v___x_3881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3881_, 0, v_b_3874_);
return v___x_3881_;
}
else
{
lean_object* v_snd_3882_; lean_object* v___x_3884_; uint8_t v_isShared_3885_; uint8_t v_isSharedCheck_3949_; 
v_snd_3882_ = lean_ctor_get(v_b_3874_, 1);
v_isSharedCheck_3949_ = !lean_is_exclusive(v_b_3874_);
if (v_isSharedCheck_3949_ == 0)
{
lean_object* v_unused_3950_; 
v_unused_3950_ = lean_ctor_get(v_b_3874_, 0);
lean_dec(v_unused_3950_);
v___x_3884_ = v_b_3874_;
v_isShared_3885_ = v_isSharedCheck_3949_;
goto v_resetjp_3883_;
}
else
{
lean_inc(v_snd_3882_);
lean_dec(v_b_3874_);
v___x_3884_ = lean_box(0);
v_isShared_3885_ = v_isSharedCheck_3949_;
goto v_resetjp_3883_;
}
v_resetjp_3883_:
{
lean_object* v___x_3886_; lean_object* v_a_3888_; lean_object* v_a_3895_; 
v___x_3886_ = lean_box(0);
v_a_3895_ = lean_array_uget(v_as_3871_, v_i_3873_);
if (lean_obj_tag(v_a_3895_) == 0)
{
v_a_3888_ = v_snd_3882_;
goto v___jp_3887_;
}
else
{
lean_object* v_val_3896_; lean_object* v___x_3898_; uint8_t v_isShared_3899_; uint8_t v_isSharedCheck_3948_; 
v_val_3896_ = lean_ctor_get(v_a_3895_, 0);
v_isSharedCheck_3948_ = !lean_is_exclusive(v_a_3895_);
if (v_isSharedCheck_3948_ == 0)
{
v___x_3898_ = v_a_3895_;
v_isShared_3899_ = v_isSharedCheck_3948_;
goto v_resetjp_3897_;
}
else
{
lean_inc(v_val_3896_);
lean_dec(v_a_3895_);
v___x_3898_ = lean_box(0);
v_isShared_3899_ = v_isSharedCheck_3948_;
goto v_resetjp_3897_;
}
v_resetjp_3897_:
{
lean_object* v___x_3900_; 
lean_inc_ref(v_p_3869_);
lean_inc(v___y_3878_);
lean_inc_ref(v___y_3877_);
lean_inc(v___y_3876_);
lean_inc_ref(v___y_3875_);
lean_inc(v_val_3896_);
v___x_3900_ = lean_apply_6(v_p_3869_, v_val_3896_, v___y_3875_, v___y_3876_, v___y_3877_, v___y_3878_, lean_box(0));
if (lean_obj_tag(v___x_3900_) == 0)
{
lean_object* v_a_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; uint8_t v___x_3904_; 
v_a_3901_ = lean_ctor_get(v___x_3900_, 0);
lean_inc(v_a_3901_);
lean_dec_ref_known(v___x_3900_, 1);
v___x_3902_ = lean_box(0);
v___x_3903_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3_spec__6___closed__0));
v___x_3904_ = lean_unbox(v_a_3901_);
lean_dec(v_a_3901_);
if (v___x_3904_ == 0)
{
lean_del_object(v___x_3898_);
lean_dec(v_val_3896_);
lean_dec(v_snd_3882_);
v_a_3888_ = v___x_3903_;
goto v___jp_3887_;
}
else
{
lean_object* v___x_3905_; lean_object* v___x_3906_; uint8_t v___x_3907_; lean_object* v___x_3908_; lean_object* v___f_3909_; lean_object* v___x_3910_; 
v___x_3905_ = l_Lean_LocalDecl_fvarId(v_val_3896_);
lean_dec(v_val_3896_);
v___x_3906_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5___closed__1));
v___x_3907_ = 0;
v___x_3908_ = lean_box(v___x_3907_);
lean_inc(v_mvarId_3870_);
v___f_3909_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3___lam__0___boxed), 10, 5);
lean_closure_set(v___f_3909_, 0, v_mvarId_3870_);
lean_closure_set(v___f_3909_, 1, v___x_3905_);
lean_closure_set(v___f_3909_, 2, v___x_3906_);
lean_closure_set(v___f_3909_, 3, v___x_3908_);
lean_closure_set(v___f_3909_, 4, v___x_3886_);
v___x_3910_ = l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1___redArg(v___f_3909_, v___y_3875_, v___y_3876_, v___y_3877_, v___y_3878_);
if (lean_obj_tag(v___x_3910_) == 0)
{
lean_object* v_a_3911_; lean_object* v___x_3913_; uint8_t v_isShared_3914_; uint8_t v_isSharedCheck_3931_; 
v_a_3911_ = lean_ctor_get(v___x_3910_, 0);
v_isSharedCheck_3931_ = !lean_is_exclusive(v___x_3910_);
if (v_isSharedCheck_3931_ == 0)
{
v___x_3913_ = v___x_3910_;
v_isShared_3914_ = v_isSharedCheck_3931_;
goto v_resetjp_3912_;
}
else
{
lean_inc(v_a_3911_);
lean_dec(v___x_3910_);
v___x_3913_ = lean_box(0);
v_isShared_3914_ = v_isSharedCheck_3931_;
goto v_resetjp_3912_;
}
v_resetjp_3912_:
{
if (lean_obj_tag(v_a_3911_) == 0)
{
lean_del_object(v___x_3913_);
lean_del_object(v___x_3898_);
lean_dec(v_snd_3882_);
v_a_3888_ = v___x_3903_;
goto v___jp_3887_;
}
else
{
lean_object* v___x_3916_; 
lean_del_object(v___x_3884_);
lean_dec(v_mvarId_3870_);
lean_dec_ref(v_p_3869_);
lean_inc_ref(v_a_3911_);
if (v_isShared_3899_ == 0)
{
lean_ctor_set(v___x_3898_, 0, v_a_3911_);
v___x_3916_ = v___x_3898_;
goto v_reusejp_3915_;
}
else
{
lean_object* v_reuseFailAlloc_3930_; 
v_reuseFailAlloc_3930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3930_, 0, v_a_3911_);
v___x_3916_ = v_reuseFailAlloc_3930_;
goto v_reusejp_3915_;
}
v_reusejp_3915_:
{
lean_object* v___x_3918_; uint8_t v_isShared_3919_; uint8_t v_isSharedCheck_3928_; 
v_isSharedCheck_3928_ = !lean_is_exclusive(v_a_3911_);
if (v_isSharedCheck_3928_ == 0)
{
lean_object* v_unused_3929_; 
v_unused_3929_ = lean_ctor_get(v_a_3911_, 0);
lean_dec(v_unused_3929_);
v___x_3918_ = v_a_3911_;
v_isShared_3919_ = v_isSharedCheck_3928_;
goto v_resetjp_3917_;
}
else
{
lean_dec(v_a_3911_);
v___x_3918_ = lean_box(0);
v_isShared_3919_ = v_isSharedCheck_3928_;
goto v_resetjp_3917_;
}
v_resetjp_3917_:
{
lean_object* v___x_3920_; lean_object* v___x_3922_; 
v___x_3920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3920_, 0, v___x_3916_);
lean_ctor_set(v___x_3920_, 1, v___x_3902_);
if (v_isShared_3919_ == 0)
{
lean_ctor_set(v___x_3918_, 0, v___x_3920_);
v___x_3922_ = v___x_3918_;
goto v_reusejp_3921_;
}
else
{
lean_object* v_reuseFailAlloc_3927_; 
v_reuseFailAlloc_3927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3927_, 0, v___x_3920_);
v___x_3922_ = v_reuseFailAlloc_3927_;
goto v_reusejp_3921_;
}
v_reusejp_3921_:
{
lean_object* v___x_3923_; lean_object* v___x_3925_; 
v___x_3923_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3923_, 0, v___x_3922_);
lean_ctor_set(v___x_3923_, 1, v_snd_3882_);
if (v_isShared_3914_ == 0)
{
lean_ctor_set(v___x_3913_, 0, v___x_3923_);
v___x_3925_ = v___x_3913_;
goto v_reusejp_3924_;
}
else
{
lean_object* v_reuseFailAlloc_3926_; 
v_reuseFailAlloc_3926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3926_, 0, v___x_3923_);
v___x_3925_ = v_reuseFailAlloc_3926_;
goto v_reusejp_3924_;
}
v_reusejp_3924_:
{
return v___x_3925_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3932_; lean_object* v___x_3934_; uint8_t v_isShared_3935_; uint8_t v_isSharedCheck_3939_; 
lean_del_object(v___x_3898_);
lean_del_object(v___x_3884_);
lean_dec(v_snd_3882_);
lean_dec(v_mvarId_3870_);
lean_dec_ref(v_p_3869_);
v_a_3932_ = lean_ctor_get(v___x_3910_, 0);
v_isSharedCheck_3939_ = !lean_is_exclusive(v___x_3910_);
if (v_isSharedCheck_3939_ == 0)
{
v___x_3934_ = v___x_3910_;
v_isShared_3935_ = v_isSharedCheck_3939_;
goto v_resetjp_3933_;
}
else
{
lean_inc(v_a_3932_);
lean_dec(v___x_3910_);
v___x_3934_ = lean_box(0);
v_isShared_3935_ = v_isSharedCheck_3939_;
goto v_resetjp_3933_;
}
v_resetjp_3933_:
{
lean_object* v___x_3937_; 
if (v_isShared_3935_ == 0)
{
v___x_3937_ = v___x_3934_;
goto v_reusejp_3936_;
}
else
{
lean_object* v_reuseFailAlloc_3938_; 
v_reuseFailAlloc_3938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3938_, 0, v_a_3932_);
v___x_3937_ = v_reuseFailAlloc_3938_;
goto v_reusejp_3936_;
}
v_reusejp_3936_:
{
return v___x_3937_;
}
}
}
}
}
else
{
lean_object* v_a_3940_; lean_object* v___x_3942_; uint8_t v_isShared_3943_; uint8_t v_isSharedCheck_3947_; 
lean_del_object(v___x_3898_);
lean_dec(v_val_3896_);
lean_del_object(v___x_3884_);
lean_dec(v_snd_3882_);
lean_dec(v_mvarId_3870_);
lean_dec_ref(v_p_3869_);
v_a_3940_ = lean_ctor_get(v___x_3900_, 0);
v_isSharedCheck_3947_ = !lean_is_exclusive(v___x_3900_);
if (v_isSharedCheck_3947_ == 0)
{
v___x_3942_ = v___x_3900_;
v_isShared_3943_ = v_isSharedCheck_3947_;
goto v_resetjp_3941_;
}
else
{
lean_inc(v_a_3940_);
lean_dec(v___x_3900_);
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
v___jp_3887_:
{
lean_object* v___x_3890_; 
if (v_isShared_3885_ == 0)
{
lean_ctor_set(v___x_3884_, 1, v_a_3888_);
lean_ctor_set(v___x_3884_, 0, v___x_3886_);
v___x_3890_ = v___x_3884_;
goto v_reusejp_3889_;
}
else
{
lean_object* v_reuseFailAlloc_3894_; 
v_reuseFailAlloc_3894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3894_, 0, v___x_3886_);
lean_ctor_set(v_reuseFailAlloc_3894_, 1, v_a_3888_);
v___x_3890_ = v_reuseFailAlloc_3894_;
goto v_reusejp_3889_;
}
v_reusejp_3889_:
{
size_t v___x_3891_; size_t v___x_3892_; lean_object* v___x_3893_; 
v___x_3891_ = ((size_t)1ULL);
v___x_3892_ = lean_usize_add(v_i_3873_, v___x_3891_);
v___x_3893_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3_spec__6(v_p_3869_, v_mvarId_3870_, v_as_3871_, v_sz_3872_, v___x_3892_, v___x_3890_, v___y_3875_, v___y_3876_, v___y_3877_, v___y_3878_);
return v___x_3893_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3___boxed(lean_object* v_p_3951_, lean_object* v_mvarId_3952_, lean_object* v_as_3953_, lean_object* v_sz_3954_, lean_object* v_i_3955_, lean_object* v_b_3956_, lean_object* v___y_3957_, lean_object* v___y_3958_, lean_object* v___y_3959_, lean_object* v___y_3960_, lean_object* v___y_3961_){
_start:
{
size_t v_sz_boxed_3962_; size_t v_i_boxed_3963_; lean_object* v_res_3964_; 
v_sz_boxed_3962_ = lean_unbox_usize(v_sz_3954_);
lean_dec(v_sz_3954_);
v_i_boxed_3963_ = lean_unbox_usize(v_i_3955_);
lean_dec(v_i_3955_);
v_res_3964_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3(v_p_3951_, v_mvarId_3952_, v_as_3953_, v_sz_boxed_3962_, v_i_boxed_3963_, v_b_3956_, v___y_3957_, v___y_3958_, v___y_3959_, v___y_3960_);
lean_dec(v___y_3960_);
lean_dec_ref(v___y_3959_);
lean_dec(v___y_3958_);
lean_dec_ref(v___y_3957_);
lean_dec_ref(v_as_3953_);
return v_res_3964_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2(lean_object* v_p_3965_, lean_object* v_mvarId_3966_, lean_object* v_t_3967_, lean_object* v_init_3968_, lean_object* v___y_3969_, lean_object* v___y_3970_, lean_object* v___y_3971_, lean_object* v___y_3972_){
_start:
{
lean_object* v_root_3974_; lean_object* v_tail_3975_; lean_object* v___x_3976_; 
v_root_3974_ = lean_ctor_get(v_t_3967_, 0);
v_tail_3975_ = lean_ctor_get(v_t_3967_, 1);
lean_inc(v_mvarId_3966_);
lean_inc_ref(v_p_3965_);
lean_inc_ref(v_init_3968_);
v___x_3976_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2(v_init_3968_, v_p_3965_, v_mvarId_3966_, v_root_3974_, v_init_3968_, v___y_3969_, v___y_3970_, v___y_3971_, v___y_3972_);
lean_dec_ref(v_init_3968_);
if (lean_obj_tag(v___x_3976_) == 0)
{
lean_object* v_a_3977_; lean_object* v___x_3979_; uint8_t v_isShared_3980_; uint8_t v_isSharedCheck_4013_; 
v_a_3977_ = lean_ctor_get(v___x_3976_, 0);
v_isSharedCheck_4013_ = !lean_is_exclusive(v___x_3976_);
if (v_isSharedCheck_4013_ == 0)
{
v___x_3979_ = v___x_3976_;
v_isShared_3980_ = v_isSharedCheck_4013_;
goto v_resetjp_3978_;
}
else
{
lean_inc(v_a_3977_);
lean_dec(v___x_3976_);
v___x_3979_ = lean_box(0);
v_isShared_3980_ = v_isSharedCheck_4013_;
goto v_resetjp_3978_;
}
v_resetjp_3978_:
{
if (lean_obj_tag(v_a_3977_) == 0)
{
lean_object* v_a_3981_; lean_object* v___x_3983_; 
lean_dec(v_mvarId_3966_);
lean_dec_ref(v_p_3965_);
v_a_3981_ = lean_ctor_get(v_a_3977_, 0);
lean_inc(v_a_3981_);
lean_dec_ref_known(v_a_3977_, 1);
if (v_isShared_3980_ == 0)
{
lean_ctor_set(v___x_3979_, 0, v_a_3981_);
v___x_3983_ = v___x_3979_;
goto v_reusejp_3982_;
}
else
{
lean_object* v_reuseFailAlloc_3984_; 
v_reuseFailAlloc_3984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3984_, 0, v_a_3981_);
v___x_3983_ = v_reuseFailAlloc_3984_;
goto v_reusejp_3982_;
}
v_reusejp_3982_:
{
return v___x_3983_;
}
}
else
{
lean_object* v_a_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; size_t v_sz_3988_; size_t v___x_3989_; lean_object* v___x_3990_; 
lean_del_object(v___x_3979_);
v_a_3985_ = lean_ctor_get(v_a_3977_, 0);
lean_inc(v_a_3985_);
lean_dec_ref_known(v_a_3977_, 1);
v___x_3986_ = lean_box(0);
v___x_3987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3987_, 0, v___x_3986_);
lean_ctor_set(v___x_3987_, 1, v_a_3985_);
v_sz_3988_ = lean_array_size(v_tail_3975_);
v___x_3989_ = ((size_t)0ULL);
v___x_3990_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3(v_p_3965_, v_mvarId_3966_, v_tail_3975_, v_sz_3988_, v___x_3989_, v___x_3987_, v___y_3969_, v___y_3970_, v___y_3971_, v___y_3972_);
if (lean_obj_tag(v___x_3990_) == 0)
{
lean_object* v_a_3991_; lean_object* v___x_3993_; uint8_t v_isShared_3994_; uint8_t v_isSharedCheck_4004_; 
v_a_3991_ = lean_ctor_get(v___x_3990_, 0);
v_isSharedCheck_4004_ = !lean_is_exclusive(v___x_3990_);
if (v_isSharedCheck_4004_ == 0)
{
v___x_3993_ = v___x_3990_;
v_isShared_3994_ = v_isSharedCheck_4004_;
goto v_resetjp_3992_;
}
else
{
lean_inc(v_a_3991_);
lean_dec(v___x_3990_);
v___x_3993_ = lean_box(0);
v_isShared_3994_ = v_isSharedCheck_4004_;
goto v_resetjp_3992_;
}
v_resetjp_3992_:
{
lean_object* v_fst_3995_; 
v_fst_3995_ = lean_ctor_get(v_a_3991_, 0);
if (lean_obj_tag(v_fst_3995_) == 0)
{
lean_object* v_snd_3996_; lean_object* v___x_3998_; 
v_snd_3996_ = lean_ctor_get(v_a_3991_, 1);
lean_inc(v_snd_3996_);
lean_dec(v_a_3991_);
if (v_isShared_3994_ == 0)
{
lean_ctor_set(v___x_3993_, 0, v_snd_3996_);
v___x_3998_ = v___x_3993_;
goto v_reusejp_3997_;
}
else
{
lean_object* v_reuseFailAlloc_3999_; 
v_reuseFailAlloc_3999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3999_, 0, v_snd_3996_);
v___x_3998_ = v_reuseFailAlloc_3999_;
goto v_reusejp_3997_;
}
v_reusejp_3997_:
{
return v___x_3998_;
}
}
else
{
lean_object* v_val_4000_; lean_object* v___x_4002_; 
lean_inc_ref(v_fst_3995_);
lean_dec(v_a_3991_);
v_val_4000_ = lean_ctor_get(v_fst_3995_, 0);
lean_inc(v_val_4000_);
lean_dec_ref_known(v_fst_3995_, 1);
if (v_isShared_3994_ == 0)
{
lean_ctor_set(v___x_3993_, 0, v_val_4000_);
v___x_4002_ = v___x_3993_;
goto v_reusejp_4001_;
}
else
{
lean_object* v_reuseFailAlloc_4003_; 
v_reuseFailAlloc_4003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4003_, 0, v_val_4000_);
v___x_4002_ = v_reuseFailAlloc_4003_;
goto v_reusejp_4001_;
}
v_reusejp_4001_:
{
return v___x_4002_;
}
}
}
}
else
{
lean_object* v_a_4005_; lean_object* v___x_4007_; uint8_t v_isShared_4008_; uint8_t v_isSharedCheck_4012_; 
v_a_4005_ = lean_ctor_get(v___x_3990_, 0);
v_isSharedCheck_4012_ = !lean_is_exclusive(v___x_3990_);
if (v_isSharedCheck_4012_ == 0)
{
v___x_4007_ = v___x_3990_;
v_isShared_4008_ = v_isSharedCheck_4012_;
goto v_resetjp_4006_;
}
else
{
lean_inc(v_a_4005_);
lean_dec(v___x_3990_);
v___x_4007_ = lean_box(0);
v_isShared_4008_ = v_isSharedCheck_4012_;
goto v_resetjp_4006_;
}
v_resetjp_4006_:
{
lean_object* v___x_4010_; 
if (v_isShared_4008_ == 0)
{
v___x_4010_ = v___x_4007_;
goto v_reusejp_4009_;
}
else
{
lean_object* v_reuseFailAlloc_4011_; 
v_reuseFailAlloc_4011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4011_, 0, v_a_4005_);
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
}
}
else
{
lean_object* v_a_4014_; lean_object* v___x_4016_; uint8_t v_isShared_4017_; uint8_t v_isSharedCheck_4021_; 
lean_dec(v_mvarId_3966_);
lean_dec_ref(v_p_3965_);
v_a_4014_ = lean_ctor_get(v___x_3976_, 0);
v_isSharedCheck_4021_ = !lean_is_exclusive(v___x_3976_);
if (v_isSharedCheck_4021_ == 0)
{
v___x_4016_ = v___x_3976_;
v_isShared_4017_ = v_isSharedCheck_4021_;
goto v_resetjp_4015_;
}
else
{
lean_inc(v_a_4014_);
lean_dec(v___x_3976_);
v___x_4016_ = lean_box(0);
v_isShared_4017_ = v_isSharedCheck_4021_;
goto v_resetjp_4015_;
}
v_resetjp_4015_:
{
lean_object* v___x_4019_; 
if (v_isShared_4017_ == 0)
{
v___x_4019_ = v___x_4016_;
goto v_reusejp_4018_;
}
else
{
lean_object* v_reuseFailAlloc_4020_; 
v_reuseFailAlloc_4020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4020_, 0, v_a_4014_);
v___x_4019_ = v_reuseFailAlloc_4020_;
goto v_reusejp_4018_;
}
v_reusejp_4018_:
{
return v___x_4019_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2___boxed(lean_object* v_p_4022_, lean_object* v_mvarId_4023_, lean_object* v_t_4024_, lean_object* v_init_4025_, lean_object* v___y_4026_, lean_object* v___y_4027_, lean_object* v___y_4028_, lean_object* v___y_4029_, lean_object* v___y_4030_){
_start:
{
lean_object* v_res_4031_; 
v_res_4031_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2(v_p_4022_, v_mvarId_4023_, v_t_4024_, v_init_4025_, v___y_4026_, v___y_4027_, v___y_4028_, v___y_4029_);
lean_dec(v___y_4029_);
lean_dec_ref(v___y_4028_);
lean_dec(v___y_4027_);
lean_dec_ref(v___y_4026_);
lean_dec_ref(v_t_4024_);
return v_res_4031_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesRec___lam__0(lean_object* v_p_4035_, lean_object* v_mvarId_4036_, lean_object* v___y_4037_, lean_object* v___y_4038_, lean_object* v___y_4039_, lean_object* v___y_4040_){
_start:
{
lean_object* v_lctx_4042_; lean_object* v_decls_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; 
v_lctx_4042_ = lean_ctor_get(v___y_4037_, 2);
v_decls_4043_ = lean_ctor_get(v_lctx_4042_, 1);
v___x_4044_ = lean_box(0);
v___x_4045_ = ((lean_object*)(l_Lean_MVarId_casesRec___lam__0___closed__0));
v___x_4046_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2(v_p_4035_, v_mvarId_4036_, v_decls_4043_, v___x_4045_, v___y_4037_, v___y_4038_, v___y_4039_, v___y_4040_);
if (lean_obj_tag(v___x_4046_) == 0)
{
lean_object* v_a_4047_; lean_object* v___x_4049_; uint8_t v_isShared_4050_; uint8_t v_isSharedCheck_4059_; 
v_a_4047_ = lean_ctor_get(v___x_4046_, 0);
v_isSharedCheck_4059_ = !lean_is_exclusive(v___x_4046_);
if (v_isSharedCheck_4059_ == 0)
{
v___x_4049_ = v___x_4046_;
v_isShared_4050_ = v_isSharedCheck_4059_;
goto v_resetjp_4048_;
}
else
{
lean_inc(v_a_4047_);
lean_dec(v___x_4046_);
v___x_4049_ = lean_box(0);
v_isShared_4050_ = v_isSharedCheck_4059_;
goto v_resetjp_4048_;
}
v_resetjp_4048_:
{
lean_object* v_fst_4051_; 
v_fst_4051_ = lean_ctor_get(v_a_4047_, 0);
lean_inc(v_fst_4051_);
lean_dec(v_a_4047_);
if (lean_obj_tag(v_fst_4051_) == 0)
{
lean_object* v___x_4053_; 
if (v_isShared_4050_ == 0)
{
lean_ctor_set(v___x_4049_, 0, v___x_4044_);
v___x_4053_ = v___x_4049_;
goto v_reusejp_4052_;
}
else
{
lean_object* v_reuseFailAlloc_4054_; 
v_reuseFailAlloc_4054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4054_, 0, v___x_4044_);
v___x_4053_ = v_reuseFailAlloc_4054_;
goto v_reusejp_4052_;
}
v_reusejp_4052_:
{
return v___x_4053_;
}
}
else
{
lean_object* v_val_4055_; lean_object* v___x_4057_; 
v_val_4055_ = lean_ctor_get(v_fst_4051_, 0);
lean_inc(v_val_4055_);
lean_dec_ref_known(v_fst_4051_, 1);
if (v_isShared_4050_ == 0)
{
lean_ctor_set(v___x_4049_, 0, v_val_4055_);
v___x_4057_ = v___x_4049_;
goto v_reusejp_4056_;
}
else
{
lean_object* v_reuseFailAlloc_4058_; 
v_reuseFailAlloc_4058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4058_, 0, v_val_4055_);
v___x_4057_ = v_reuseFailAlloc_4058_;
goto v_reusejp_4056_;
}
v_reusejp_4056_:
{
return v___x_4057_;
}
}
}
}
else
{
lean_object* v_a_4060_; lean_object* v___x_4062_; uint8_t v_isShared_4063_; uint8_t v_isSharedCheck_4067_; 
v_a_4060_ = lean_ctor_get(v___x_4046_, 0);
v_isSharedCheck_4067_ = !lean_is_exclusive(v___x_4046_);
if (v_isSharedCheck_4067_ == 0)
{
v___x_4062_ = v___x_4046_;
v_isShared_4063_ = v_isSharedCheck_4067_;
goto v_resetjp_4061_;
}
else
{
lean_inc(v_a_4060_);
lean_dec(v___x_4046_);
v___x_4062_ = lean_box(0);
v_isShared_4063_ = v_isSharedCheck_4067_;
goto v_resetjp_4061_;
}
v_resetjp_4061_:
{
lean_object* v___x_4065_; 
if (v_isShared_4063_ == 0)
{
v___x_4065_ = v___x_4062_;
goto v_reusejp_4064_;
}
else
{
lean_object* v_reuseFailAlloc_4066_; 
v_reuseFailAlloc_4066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4066_, 0, v_a_4060_);
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
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesRec___lam__0___boxed(lean_object* v_p_4068_, lean_object* v_mvarId_4069_, lean_object* v___y_4070_, lean_object* v___y_4071_, lean_object* v___y_4072_, lean_object* v___y_4073_, lean_object* v___y_4074_){
_start:
{
lean_object* v_res_4075_; 
v_res_4075_ = l_Lean_MVarId_casesRec___lam__0(v_p_4068_, v_mvarId_4069_, v___y_4070_, v___y_4071_, v___y_4072_, v___y_4073_);
lean_dec(v___y_4073_);
lean_dec_ref(v___y_4072_);
lean_dec(v___y_4071_);
lean_dec_ref(v___y_4070_);
return v_res_4075_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesRec___lam__1(lean_object* v_p_4076_, lean_object* v_mvarId_4077_, lean_object* v___y_4078_, lean_object* v___y_4079_, lean_object* v___y_4080_, lean_object* v___y_4081_){
_start:
{
lean_object* v___f_4083_; lean_object* v___x_4084_; 
lean_inc(v_mvarId_4077_);
v___f_4083_ = lean_alloc_closure((void*)(l_Lean_MVarId_casesRec___lam__0___boxed), 7, 2);
lean_closure_set(v___f_4083_, 0, v_p_4076_);
lean_closure_set(v___f_4083_, 1, v_mvarId_4077_);
v___x_4084_ = l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2___redArg(v_mvarId_4077_, v___f_4083_, v___y_4078_, v___y_4079_, v___y_4080_, v___y_4081_);
return v___x_4084_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesRec___lam__1___boxed(lean_object* v_p_4085_, lean_object* v_mvarId_4086_, lean_object* v___y_4087_, lean_object* v___y_4088_, lean_object* v___y_4089_, lean_object* v___y_4090_, lean_object* v___y_4091_){
_start:
{
lean_object* v_res_4092_; 
v_res_4092_ = l_Lean_MVarId_casesRec___lam__1(v_p_4085_, v_mvarId_4086_, v___y_4087_, v___y_4088_, v___y_4089_, v___y_4090_);
lean_dec(v___y_4090_);
lean_dec_ref(v___y_4089_);
lean_dec(v___y_4088_);
lean_dec_ref(v___y_4087_);
return v_res_4092_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesRec(lean_object* v_mvarId_4093_, lean_object* v_p_4094_, lean_object* v_a_4095_, lean_object* v_a_4096_, lean_object* v_a_4097_, lean_object* v_a_4098_){
_start:
{
lean_object* v___f_4100_; lean_object* v___x_4101_; 
v___f_4100_ = lean_alloc_closure((void*)(l_Lean_MVarId_casesRec___lam__1___boxed), 7, 1);
lean_closure_set(v___f_4100_, 0, v_p_4094_);
v___x_4101_ = l_Lean_Meta_saturate(v_mvarId_4093_, v___f_4100_, v_a_4095_, v_a_4096_, v_a_4097_, v_a_4098_);
return v___x_4101_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesRec___boxed(lean_object* v_mvarId_4102_, lean_object* v_p_4103_, lean_object* v_a_4104_, lean_object* v_a_4105_, lean_object* v_a_4106_, lean_object* v_a_4107_, lean_object* v_a_4108_){
_start:
{
lean_object* v_res_4109_; 
v_res_4109_ = l_Lean_MVarId_casesRec(v_mvarId_4102_, v_p_4103_, v_a_4104_, v_a_4105_, v_a_4106_, v_a_4107_);
lean_dec(v_a_4107_);
lean_dec_ref(v_a_4106_);
lean_dec(v_a_4105_);
lean_dec_ref(v_a_4104_);
return v_res_4109_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0___redArg(lean_object* v_e_4110_, lean_object* v___y_4111_){
_start:
{
uint8_t v___x_4113_; 
v___x_4113_ = l_Lean_Expr_hasMVar(v_e_4110_);
if (v___x_4113_ == 0)
{
lean_object* v___x_4114_; 
v___x_4114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4114_, 0, v_e_4110_);
return v___x_4114_;
}
else
{
lean_object* v___x_4115_; lean_object* v_mctx_4116_; lean_object* v___x_4117_; lean_object* v_fst_4118_; lean_object* v_snd_4119_; lean_object* v___x_4120_; lean_object* v_cache_4121_; lean_object* v_zetaDeltaFVarIds_4122_; lean_object* v_postponed_4123_; lean_object* v_diag_4124_; lean_object* v___x_4126_; uint8_t v_isShared_4127_; uint8_t v_isSharedCheck_4133_; 
v___x_4115_ = lean_st_ref_get(v___y_4111_);
v_mctx_4116_ = lean_ctor_get(v___x_4115_, 0);
lean_inc_ref(v_mctx_4116_);
lean_dec(v___x_4115_);
v___x_4117_ = l_Lean_instantiateMVarsCore(v_mctx_4116_, v_e_4110_);
v_fst_4118_ = lean_ctor_get(v___x_4117_, 0);
lean_inc(v_fst_4118_);
v_snd_4119_ = lean_ctor_get(v___x_4117_, 1);
lean_inc(v_snd_4119_);
lean_dec_ref(v___x_4117_);
v___x_4120_ = lean_st_ref_take(v___y_4111_);
v_cache_4121_ = lean_ctor_get(v___x_4120_, 1);
v_zetaDeltaFVarIds_4122_ = lean_ctor_get(v___x_4120_, 2);
v_postponed_4123_ = lean_ctor_get(v___x_4120_, 3);
v_diag_4124_ = lean_ctor_get(v___x_4120_, 4);
v_isSharedCheck_4133_ = !lean_is_exclusive(v___x_4120_);
if (v_isSharedCheck_4133_ == 0)
{
lean_object* v_unused_4134_; 
v_unused_4134_ = lean_ctor_get(v___x_4120_, 0);
lean_dec(v_unused_4134_);
v___x_4126_ = v___x_4120_;
v_isShared_4127_ = v_isSharedCheck_4133_;
goto v_resetjp_4125_;
}
else
{
lean_inc(v_diag_4124_);
lean_inc(v_postponed_4123_);
lean_inc(v_zetaDeltaFVarIds_4122_);
lean_inc(v_cache_4121_);
lean_dec(v___x_4120_);
v___x_4126_ = lean_box(0);
v_isShared_4127_ = v_isSharedCheck_4133_;
goto v_resetjp_4125_;
}
v_resetjp_4125_:
{
lean_object* v___x_4129_; 
if (v_isShared_4127_ == 0)
{
lean_ctor_set(v___x_4126_, 0, v_snd_4119_);
v___x_4129_ = v___x_4126_;
goto v_reusejp_4128_;
}
else
{
lean_object* v_reuseFailAlloc_4132_; 
v_reuseFailAlloc_4132_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4132_, 0, v_snd_4119_);
lean_ctor_set(v_reuseFailAlloc_4132_, 1, v_cache_4121_);
lean_ctor_set(v_reuseFailAlloc_4132_, 2, v_zetaDeltaFVarIds_4122_);
lean_ctor_set(v_reuseFailAlloc_4132_, 3, v_postponed_4123_);
lean_ctor_set(v_reuseFailAlloc_4132_, 4, v_diag_4124_);
v___x_4129_ = v_reuseFailAlloc_4132_;
goto v_reusejp_4128_;
}
v_reusejp_4128_:
{
lean_object* v___x_4130_; lean_object* v___x_4131_; 
v___x_4130_ = lean_st_ref_put(v___y_4111_, v___x_4129_);
v___x_4131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4131_, 0, v_fst_4118_);
return v___x_4131_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0___redArg___boxed(lean_object* v_e_4135_, lean_object* v___y_4136_, lean_object* v___y_4137_){
_start:
{
lean_object* v_res_4138_; 
v_res_4138_ = l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0___redArg(v_e_4135_, v___y_4136_);
lean_dec(v___y_4136_);
return v_res_4138_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0(lean_object* v_e_4139_, lean_object* v___y_4140_, lean_object* v___y_4141_, lean_object* v___y_4142_, lean_object* v___y_4143_){
_start:
{
lean_object* v___x_4145_; 
v___x_4145_ = l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0___redArg(v_e_4139_, v___y_4141_);
return v___x_4145_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0___boxed(lean_object* v_e_4146_, lean_object* v___y_4147_, lean_object* v___y_4148_, lean_object* v___y_4149_, lean_object* v___y_4150_, lean_object* v___y_4151_){
_start:
{
lean_object* v_res_4152_; 
v_res_4152_ = l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0(v_e_4146_, v___y_4147_, v___y_4148_, v___y_4149_, v___y_4150_);
lean_dec(v___y_4150_);
lean_dec_ref(v___y_4149_);
lean_dec(v___y_4148_);
lean_dec_ref(v___y_4147_);
return v_res_4152_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesAnd___lam__0(lean_object* v_localDecl_4156_, lean_object* v___y_4157_, lean_object* v___y_4158_, lean_object* v___y_4159_, lean_object* v___y_4160_){
_start:
{
lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v_a_4164_; lean_object* v___x_4166_; uint8_t v_isShared_4167_; uint8_t v_isSharedCheck_4175_; 
v___x_4162_ = l_Lean_LocalDecl_type(v_localDecl_4156_);
v___x_4163_ = l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0___redArg(v___x_4162_, v___y_4158_);
v_a_4164_ = lean_ctor_get(v___x_4163_, 0);
v_isSharedCheck_4175_ = !lean_is_exclusive(v___x_4163_);
if (v_isSharedCheck_4175_ == 0)
{
v___x_4166_ = v___x_4163_;
v_isShared_4167_ = v_isSharedCheck_4175_;
goto v_resetjp_4165_;
}
else
{
lean_inc(v_a_4164_);
lean_dec(v___x_4163_);
v___x_4166_ = lean_box(0);
v_isShared_4167_ = v_isSharedCheck_4175_;
goto v_resetjp_4165_;
}
v_resetjp_4165_:
{
lean_object* v___x_4168_; lean_object* v___x_4169_; uint8_t v___x_4170_; lean_object* v___x_4171_; lean_object* v___x_4173_; 
v___x_4168_ = ((lean_object*)(l_Lean_MVarId_casesAnd___lam__0___closed__1));
v___x_4169_ = lean_unsigned_to_nat(2u);
v___x_4170_ = l_Lean_Expr_isAppOfArity(v_a_4164_, v___x_4168_, v___x_4169_);
lean_dec(v_a_4164_);
v___x_4171_ = lean_box(v___x_4170_);
if (v_isShared_4167_ == 0)
{
lean_ctor_set(v___x_4166_, 0, v___x_4171_);
v___x_4173_ = v___x_4166_;
goto v_reusejp_4172_;
}
else
{
lean_object* v_reuseFailAlloc_4174_; 
v_reuseFailAlloc_4174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4174_, 0, v___x_4171_);
v___x_4173_ = v_reuseFailAlloc_4174_;
goto v_reusejp_4172_;
}
v_reusejp_4172_:
{
return v___x_4173_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesAnd___lam__0___boxed(lean_object* v_localDecl_4176_, lean_object* v___y_4177_, lean_object* v___y_4178_, lean_object* v___y_4179_, lean_object* v___y_4180_, lean_object* v___y_4181_){
_start:
{
lean_object* v_res_4182_; 
v_res_4182_ = l_Lean_MVarId_casesAnd___lam__0(v_localDecl_4176_, v___y_4177_, v___y_4178_, v___y_4179_, v___y_4180_);
lean_dec(v___y_4180_);
lean_dec_ref(v___y_4179_);
lean_dec(v___y_4178_);
lean_dec_ref(v___y_4177_);
lean_dec_ref(v_localDecl_4176_);
return v_res_4182_;
}
}
static lean_object* _init_l_Lean_MVarId_casesAnd___closed__3(void){
_start:
{
lean_object* v___x_4187_; lean_object* v___x_4188_; 
v___x_4187_ = ((lean_object*)(l_Lean_MVarId_casesAnd___closed__2));
v___x_4188_ = l_Lean_MessageData_ofFormat(v___x_4187_);
return v___x_4188_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesAnd(lean_object* v_mvarId_4189_, lean_object* v_a_4190_, lean_object* v_a_4191_, lean_object* v_a_4192_, lean_object* v_a_4193_){
_start:
{
lean_object* v___f_4195_; lean_object* v___x_4196_; 
v___f_4195_ = ((lean_object*)(l_Lean_MVarId_casesAnd___closed__0));
v___x_4196_ = l_Lean_MVarId_casesRec(v_mvarId_4189_, v___f_4195_, v_a_4190_, v_a_4191_, v_a_4192_, v_a_4193_);
if (lean_obj_tag(v___x_4196_) == 0)
{
lean_object* v_a_4197_; lean_object* v___x_4198_; lean_object* v___x_4199_; 
v_a_4197_ = lean_ctor_get(v___x_4196_, 0);
lean_inc(v_a_4197_);
lean_dec_ref_known(v___x_4196_, 1);
v___x_4198_ = lean_obj_once(&l_Lean_MVarId_casesAnd___closed__3, &l_Lean_MVarId_casesAnd___closed__3_once, _init_l_Lean_MVarId_casesAnd___closed__3);
v___x_4199_ = l_Lean_Meta_exactlyOne(v_a_4197_, v___x_4198_, v_a_4190_, v_a_4191_, v_a_4192_, v_a_4193_);
lean_dec(v_a_4197_);
return v___x_4199_;
}
else
{
lean_object* v_a_4200_; lean_object* v___x_4202_; uint8_t v_isShared_4203_; uint8_t v_isSharedCheck_4207_; 
v_a_4200_ = lean_ctor_get(v___x_4196_, 0);
v_isSharedCheck_4207_ = !lean_is_exclusive(v___x_4196_);
if (v_isSharedCheck_4207_ == 0)
{
v___x_4202_ = v___x_4196_;
v_isShared_4203_ = v_isSharedCheck_4207_;
goto v_resetjp_4201_;
}
else
{
lean_inc(v_a_4200_);
lean_dec(v___x_4196_);
v___x_4202_ = lean_box(0);
v_isShared_4203_ = v_isSharedCheck_4207_;
goto v_resetjp_4201_;
}
v_resetjp_4201_:
{
lean_object* v___x_4205_; 
if (v_isShared_4203_ == 0)
{
v___x_4205_ = v___x_4202_;
goto v_reusejp_4204_;
}
else
{
lean_object* v_reuseFailAlloc_4206_; 
v_reuseFailAlloc_4206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4206_, 0, v_a_4200_);
v___x_4205_ = v_reuseFailAlloc_4206_;
goto v_reusejp_4204_;
}
v_reusejp_4204_:
{
return v___x_4205_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesAnd___boxed(lean_object* v_mvarId_4208_, lean_object* v_a_4209_, lean_object* v_a_4210_, lean_object* v_a_4211_, lean_object* v_a_4212_, lean_object* v_a_4213_){
_start:
{
lean_object* v_res_4214_; 
v_res_4214_ = l_Lean_MVarId_casesAnd(v_mvarId_4208_, v_a_4209_, v_a_4210_, v_a_4211_, v_a_4212_);
lean_dec(v_a_4212_);
lean_dec_ref(v_a_4211_);
lean_dec(v_a_4210_);
lean_dec_ref(v_a_4209_);
return v_res_4214_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_substEqs___lam__0(lean_object* v_localDecl_4215_, lean_object* v___y_4216_, lean_object* v___y_4217_, lean_object* v___y_4218_, lean_object* v___y_4219_){
_start:
{
lean_object* v___x_4221_; lean_object* v___x_4222_; lean_object* v_a_4223_; lean_object* v___x_4225_; uint8_t v_isShared_4226_; uint8_t v_isSharedCheck_4237_; 
v___x_4221_ = l_Lean_LocalDecl_type(v_localDecl_4215_);
v___x_4222_ = l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0___redArg(v___x_4221_, v___y_4217_);
v_a_4223_ = lean_ctor_get(v___x_4222_, 0);
v_isSharedCheck_4237_ = !lean_is_exclusive(v___x_4222_);
if (v_isSharedCheck_4237_ == 0)
{
v___x_4225_ = v___x_4222_;
v_isShared_4226_ = v_isSharedCheck_4237_;
goto v_resetjp_4224_;
}
else
{
lean_inc(v_a_4223_);
lean_dec(v___x_4222_);
v___x_4225_ = lean_box(0);
v_isShared_4226_ = v_isSharedCheck_4237_;
goto v_resetjp_4224_;
}
v_resetjp_4224_:
{
uint8_t v___x_4227_; 
v___x_4227_ = l_Lean_Expr_isEq(v_a_4223_);
if (v___x_4227_ == 0)
{
uint8_t v___x_4228_; lean_object* v___x_4229_; lean_object* v___x_4231_; 
v___x_4228_ = l_Lean_Expr_isHEq(v_a_4223_);
lean_dec(v_a_4223_);
v___x_4229_ = lean_box(v___x_4228_);
if (v_isShared_4226_ == 0)
{
lean_ctor_set(v___x_4225_, 0, v___x_4229_);
v___x_4231_ = v___x_4225_;
goto v_reusejp_4230_;
}
else
{
lean_object* v_reuseFailAlloc_4232_; 
v_reuseFailAlloc_4232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4232_, 0, v___x_4229_);
v___x_4231_ = v_reuseFailAlloc_4232_;
goto v_reusejp_4230_;
}
v_reusejp_4230_:
{
return v___x_4231_;
}
}
else
{
lean_object* v___x_4233_; lean_object* v___x_4235_; 
lean_dec(v_a_4223_);
v___x_4233_ = lean_box(v___x_4227_);
if (v_isShared_4226_ == 0)
{
lean_ctor_set(v___x_4225_, 0, v___x_4233_);
v___x_4235_ = v___x_4225_;
goto v_reusejp_4234_;
}
else
{
lean_object* v_reuseFailAlloc_4236_; 
v_reuseFailAlloc_4236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4236_, 0, v___x_4233_);
v___x_4235_ = v_reuseFailAlloc_4236_;
goto v_reusejp_4234_;
}
v_reusejp_4234_:
{
return v___x_4235_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_substEqs___lam__0___boxed(lean_object* v_localDecl_4238_, lean_object* v___y_4239_, lean_object* v___y_4240_, lean_object* v___y_4241_, lean_object* v___y_4242_, lean_object* v___y_4243_){
_start:
{
lean_object* v_res_4244_; 
v_res_4244_ = l_Lean_MVarId_substEqs___lam__0(v_localDecl_4238_, v___y_4239_, v___y_4240_, v___y_4241_, v___y_4242_);
lean_dec(v___y_4242_);
lean_dec_ref(v___y_4241_);
lean_dec(v___y_4240_);
lean_dec_ref(v___y_4239_);
lean_dec_ref(v_localDecl_4238_);
return v_res_4244_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_substEqs(lean_object* v_mvarId_4246_, lean_object* v_a_4247_, lean_object* v_a_4248_, lean_object* v_a_4249_, lean_object* v_a_4250_){
_start:
{
lean_object* v___f_4252_; lean_object* v___x_4253_; 
v___f_4252_ = ((lean_object*)(l_Lean_MVarId_substEqs___closed__0));
v___x_4253_ = l_Lean_MVarId_casesRec(v_mvarId_4246_, v___f_4252_, v_a_4247_, v_a_4248_, v_a_4249_, v_a_4250_);
if (lean_obj_tag(v___x_4253_) == 0)
{
lean_object* v_a_4254_; lean_object* v___x_4255_; lean_object* v___x_4256_; 
v_a_4254_ = lean_ctor_get(v___x_4253_, 0);
lean_inc(v_a_4254_);
lean_dec_ref_known(v___x_4253_, 1);
v___x_4255_ = lean_obj_once(&l_Lean_MVarId_casesAnd___closed__3, &l_Lean_MVarId_casesAnd___closed__3_once, _init_l_Lean_MVarId_casesAnd___closed__3);
v___x_4256_ = l_Lean_Meta_ensureAtMostOne(v_a_4254_, v___x_4255_, v_a_4247_, v_a_4248_, v_a_4249_, v_a_4250_);
lean_dec(v_a_4254_);
return v___x_4256_;
}
else
{
lean_object* v_a_4257_; lean_object* v___x_4259_; uint8_t v_isShared_4260_; uint8_t v_isSharedCheck_4264_; 
v_a_4257_ = lean_ctor_get(v___x_4253_, 0);
v_isSharedCheck_4264_ = !lean_is_exclusive(v___x_4253_);
if (v_isSharedCheck_4264_ == 0)
{
v___x_4259_ = v___x_4253_;
v_isShared_4260_ = v_isSharedCheck_4264_;
goto v_resetjp_4258_;
}
else
{
lean_inc(v_a_4257_);
lean_dec(v___x_4253_);
v___x_4259_ = lean_box(0);
v_isShared_4260_ = v_isSharedCheck_4264_;
goto v_resetjp_4258_;
}
v_resetjp_4258_:
{
lean_object* v___x_4262_; 
if (v_isShared_4260_ == 0)
{
v___x_4262_ = v___x_4259_;
goto v_reusejp_4261_;
}
else
{
lean_object* v_reuseFailAlloc_4263_; 
v_reuseFailAlloc_4263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4263_, 0, v_a_4257_);
v___x_4262_ = v_reuseFailAlloc_4263_;
goto v_reusejp_4261_;
}
v_reusejp_4261_:
{
return v___x_4262_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_substEqs___boxed(lean_object* v_mvarId_4265_, lean_object* v_a_4266_, lean_object* v_a_4267_, lean_object* v_a_4268_, lean_object* v_a_4269_, lean_object* v_a_4270_){
_start:
{
lean_object* v_res_4271_; 
v_res_4271_ = l_Lean_MVarId_substEqs(v_mvarId_4265_, v_a_4266_, v_a_4267_, v_a_4268_, v_a_4269_);
lean_dec(v_a_4269_);
lean_dec_ref(v_a_4268_);
lean_dec(v_a_4267_);
lean_dec_ref(v_a_4266_);
return v_res_4271_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkByCasesSubgoal___lam__0(lean_object* v_goalType_4272_, lean_object* v_tag_4273_, lean_object* v_hyp_4274_, lean_object* v___y_4275_, lean_object* v___y_4276_, lean_object* v___y_4277_, lean_object* v___y_4278_){
_start:
{
lean_object* v___x_4280_; 
v___x_4280_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_goalType_4272_, v_tag_4273_, v___y_4275_, v___y_4276_, v___y_4277_, v___y_4278_);
if (lean_obj_tag(v___x_4280_) == 0)
{
lean_object* v_a_4281_; lean_object* v___x_4282_; lean_object* v___x_4283_; lean_object* v___x_4284_; uint8_t v___x_4285_; uint8_t v___x_4286_; uint8_t v___x_4287_; lean_object* v___x_4288_; 
v_a_4281_ = lean_ctor_get(v___x_4280_, 0);
lean_inc_n(v_a_4281_, 2);
lean_dec_ref_known(v___x_4280_, 1);
v___x_4282_ = lean_unsigned_to_nat(1u);
v___x_4283_ = lean_mk_empty_array_with_capacity(v___x_4282_);
lean_inc_ref(v_hyp_4274_);
v___x_4284_ = lean_array_push(v___x_4283_, v_hyp_4274_);
v___x_4285_ = 0;
v___x_4286_ = 1;
v___x_4287_ = 1;
v___x_4288_ = l_Lean_Meta_mkLambdaFVars(v___x_4284_, v_a_4281_, v___x_4285_, v___x_4286_, v___x_4285_, v___x_4286_, v___x_4287_, v___y_4275_, v___y_4276_, v___y_4277_, v___y_4278_);
lean_dec_ref(v___x_4284_);
if (lean_obj_tag(v___x_4288_) == 0)
{
lean_object* v_a_4289_; lean_object* v___x_4291_; uint8_t v_isShared_4292_; uint8_t v_isSharedCheck_4300_; 
v_a_4289_ = lean_ctor_get(v___x_4288_, 0);
v_isSharedCheck_4300_ = !lean_is_exclusive(v___x_4288_);
if (v_isSharedCheck_4300_ == 0)
{
v___x_4291_ = v___x_4288_;
v_isShared_4292_ = v_isSharedCheck_4300_;
goto v_resetjp_4290_;
}
else
{
lean_inc(v_a_4289_);
lean_dec(v___x_4288_);
v___x_4291_ = lean_box(0);
v_isShared_4292_ = v_isSharedCheck_4300_;
goto v_resetjp_4290_;
}
v_resetjp_4290_:
{
lean_object* v___x_4293_; lean_object* v___x_4294_; lean_object* v___x_4295_; lean_object* v___x_4296_; lean_object* v___x_4298_; 
v___x_4293_ = l_Lean_Expr_mvarId_x21(v_a_4281_);
lean_dec(v_a_4281_);
v___x_4294_ = l_Lean_Expr_fvarId_x21(v_hyp_4274_);
lean_dec_ref(v_hyp_4274_);
v___x_4295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4295_, 0, v___x_4293_);
lean_ctor_set(v___x_4295_, 1, v___x_4294_);
v___x_4296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4296_, 0, v_a_4289_);
lean_ctor_set(v___x_4296_, 1, v___x_4295_);
if (v_isShared_4292_ == 0)
{
lean_ctor_set(v___x_4291_, 0, v___x_4296_);
v___x_4298_ = v___x_4291_;
goto v_reusejp_4297_;
}
else
{
lean_object* v_reuseFailAlloc_4299_; 
v_reuseFailAlloc_4299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4299_, 0, v___x_4296_);
v___x_4298_ = v_reuseFailAlloc_4299_;
goto v_reusejp_4297_;
}
v_reusejp_4297_:
{
return v___x_4298_;
}
}
}
else
{
lean_object* v_a_4301_; lean_object* v___x_4303_; uint8_t v_isShared_4304_; uint8_t v_isSharedCheck_4308_; 
lean_dec(v_a_4281_);
lean_dec_ref(v_hyp_4274_);
v_a_4301_ = lean_ctor_get(v___x_4288_, 0);
v_isSharedCheck_4308_ = !lean_is_exclusive(v___x_4288_);
if (v_isSharedCheck_4308_ == 0)
{
v___x_4303_ = v___x_4288_;
v_isShared_4304_ = v_isSharedCheck_4308_;
goto v_resetjp_4302_;
}
else
{
lean_inc(v_a_4301_);
lean_dec(v___x_4288_);
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
else
{
lean_object* v_a_4309_; lean_object* v___x_4311_; uint8_t v_isShared_4312_; uint8_t v_isSharedCheck_4316_; 
lean_dec_ref(v_hyp_4274_);
v_a_4309_ = lean_ctor_get(v___x_4280_, 0);
v_isSharedCheck_4316_ = !lean_is_exclusive(v___x_4280_);
if (v_isSharedCheck_4316_ == 0)
{
v___x_4311_ = v___x_4280_;
v_isShared_4312_ = v_isSharedCheck_4316_;
goto v_resetjp_4310_;
}
else
{
lean_inc(v_a_4309_);
lean_dec(v___x_4280_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkByCasesSubgoal___lam__0___boxed(lean_object* v_goalType_4317_, lean_object* v_tag_4318_, lean_object* v_hyp_4319_, lean_object* v___y_4320_, lean_object* v___y_4321_, lean_object* v___y_4322_, lean_object* v___y_4323_, lean_object* v___y_4324_){
_start:
{
lean_object* v_res_4325_; 
v_res_4325_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkByCasesSubgoal___lam__0(v_goalType_4317_, v_tag_4318_, v_hyp_4319_, v___y_4320_, v___y_4321_, v___y_4322_, v___y_4323_);
lean_dec(v___y_4323_);
lean_dec_ref(v___y_4322_);
lean_dec(v___y_4321_);
lean_dec_ref(v___y_4320_);
return v_res_4325_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkByCasesSubgoal(lean_object* v_p_4326_, lean_object* v_hName_4327_, lean_object* v_goalType_4328_, lean_object* v_tag_4329_, lean_object* v_a_4330_, lean_object* v_a_4331_, lean_object* v_a_4332_, lean_object* v_a_4333_){
_start:
{
lean_object* v___f_4335_; lean_object* v___x_4336_; 
v___f_4335_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkByCasesSubgoal___lam__0___boxed), 8, 2);
lean_closure_set(v___f_4335_, 0, v_goalType_4328_);
lean_closure_set(v___f_4335_, 1, v_tag_4329_);
v___x_4336_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0___redArg(v_hName_4327_, v_p_4326_, v___f_4335_, v_a_4330_, v_a_4331_, v_a_4332_, v_a_4333_);
return v___x_4336_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkByCasesSubgoal___boxed(lean_object* v_p_4337_, lean_object* v_hName_4338_, lean_object* v_goalType_4339_, lean_object* v_tag_4340_, lean_object* v_a_4341_, lean_object* v_a_4342_, lean_object* v_a_4343_, lean_object* v_a_4344_, lean_object* v_a_4345_){
_start:
{
lean_object* v_res_4346_; 
v_res_4346_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkByCasesSubgoal(v_p_4337_, v_hName_4338_, v_goalType_4339_, v_tag_4340_, v_a_4341_, v_a_4342_, v_a_4343_, v_a_4344_);
lean_dec(v_a_4344_);
lean_dec_ref(v_a_4343_);
lean_dec(v_a_4342_);
lean_dec_ref(v_a_4341_);
return v_res_4346_;
}
}
static lean_object* _init_l_Lean_MVarId_byCases___lam__0___closed__7(void){
_start:
{
lean_object* v___x_4358_; lean_object* v___x_4359_; lean_object* v___x_4360_; 
v___x_4358_ = lean_box(0);
v___x_4359_ = ((lean_object*)(l_Lean_MVarId_byCases___lam__0___closed__6));
v___x_4360_ = l_Lean_Expr_const___override(v___x_4359_, v___x_4358_);
return v___x_4360_;
}
}
static lean_object* _init_l_Lean_MVarId_byCases___lam__0___closed__10(void){
_start:
{
lean_object* v___x_4364_; lean_object* v___x_4365_; 
v___x_4364_ = ((lean_object*)(l_Lean_MVarId_byCases___lam__0___closed__9));
v___x_4365_ = l_Lean_stringToMessageData(v___x_4364_);
return v___x_4365_;
}
}
static lean_object* _init_l_Lean_MVarId_byCases___lam__0___closed__11(void){
_start:
{
lean_object* v___x_4366_; lean_object* v___x_4367_; 
v___x_4366_ = lean_obj_once(&l_Lean_MVarId_byCases___lam__0___closed__10, &l_Lean_MVarId_byCases___lam__0___closed__10_once, _init_l_Lean_MVarId_byCases___lam__0___closed__10);
v___x_4367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4367_, 0, v___x_4366_);
return v___x_4367_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_byCases___lam__0(lean_object* v_mvarId_4368_, lean_object* v_p_4369_, lean_object* v_hName_4370_, lean_object* v___y_4371_, lean_object* v___y_4372_, lean_object* v___y_4373_, lean_object* v___y_4374_){
_start:
{
lean_object* v___x_4376_; 
lean_inc(v_mvarId_4368_);
v___x_4376_ = l_Lean_MVarId_getType(v_mvarId_4368_, v___y_4371_, v___y_4372_, v___y_4373_, v___y_4374_);
if (lean_obj_tag(v___x_4376_) == 0)
{
lean_object* v_a_4377_; lean_object* v___x_4378_; 
v_a_4377_ = lean_ctor_get(v___x_4376_, 0);
lean_inc(v_a_4377_);
lean_dec_ref_known(v___x_4376_, 1);
lean_inc(v_mvarId_4368_);
v___x_4378_ = l_Lean_MVarId_getTag(v_mvarId_4368_, v___y_4371_, v___y_4372_, v___y_4373_, v___y_4374_);
if (lean_obj_tag(v___x_4378_) == 0)
{
lean_object* v_a_4379_; lean_object* v___y_4381_; lean_object* v___y_4382_; lean_object* v___y_4383_; lean_object* v___y_4384_; lean_object* v___x_4432_; 
v_a_4379_ = lean_ctor_get(v___x_4378_, 0);
lean_inc(v_a_4379_);
lean_dec_ref_known(v___x_4378_, 1);
lean_inc(v_a_4377_);
v___x_4432_ = l_Lean_Meta_isProp(v_a_4377_, v___y_4371_, v___y_4372_, v___y_4373_, v___y_4374_);
if (lean_obj_tag(v___x_4432_) == 0)
{
lean_object* v_a_4433_; uint8_t v___x_4434_; 
v_a_4433_ = lean_ctor_get(v___x_4432_, 0);
lean_inc(v_a_4433_);
lean_dec_ref_known(v___x_4432_, 1);
v___x_4434_ = lean_unbox(v_a_4433_);
lean_dec(v_a_4433_);
if (v___x_4434_ == 0)
{
lean_object* v___x_4435_; lean_object* v___x_4436_; lean_object* v___x_4437_; 
v___x_4435_ = ((lean_object*)(l_Lean_MVarId_byCases___lam__0___closed__8));
v___x_4436_ = lean_obj_once(&l_Lean_MVarId_byCases___lam__0___closed__11, &l_Lean_MVarId_byCases___lam__0___closed__11_once, _init_l_Lean_MVarId_byCases___lam__0___closed__11);
lean_inc(v_mvarId_4368_);
v___x_4437_ = l_Lean_Meta_throwTacticEx___redArg(v___x_4435_, v_mvarId_4368_, v___x_4436_, v___y_4371_, v___y_4372_, v___y_4373_, v___y_4374_);
if (lean_obj_tag(v___x_4437_) == 0)
{
lean_dec_ref_known(v___x_4437_, 1);
v___y_4381_ = v___y_4371_;
v___y_4382_ = v___y_4372_;
v___y_4383_ = v___y_4373_;
v___y_4384_ = v___y_4374_;
goto v___jp_4380_;
}
else
{
lean_object* v_a_4438_; lean_object* v___x_4440_; uint8_t v_isShared_4441_; uint8_t v_isSharedCheck_4445_; 
lean_dec(v_a_4379_);
lean_dec(v_a_4377_);
lean_dec(v_hName_4370_);
lean_dec_ref(v_p_4369_);
lean_dec(v_mvarId_4368_);
v_a_4438_ = lean_ctor_get(v___x_4437_, 0);
v_isSharedCheck_4445_ = !lean_is_exclusive(v___x_4437_);
if (v_isSharedCheck_4445_ == 0)
{
v___x_4440_ = v___x_4437_;
v_isShared_4441_ = v_isSharedCheck_4445_;
goto v_resetjp_4439_;
}
else
{
lean_inc(v_a_4438_);
lean_dec(v___x_4437_);
v___x_4440_ = lean_box(0);
v_isShared_4441_ = v_isSharedCheck_4445_;
goto v_resetjp_4439_;
}
v_resetjp_4439_:
{
lean_object* v___x_4443_; 
if (v_isShared_4441_ == 0)
{
v___x_4443_ = v___x_4440_;
goto v_reusejp_4442_;
}
else
{
lean_object* v_reuseFailAlloc_4444_; 
v_reuseFailAlloc_4444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4444_, 0, v_a_4438_);
v___x_4443_ = v_reuseFailAlloc_4444_;
goto v_reusejp_4442_;
}
v_reusejp_4442_:
{
return v___x_4443_;
}
}
}
}
else
{
v___y_4381_ = v___y_4371_;
v___y_4382_ = v___y_4372_;
v___y_4383_ = v___y_4373_;
v___y_4384_ = v___y_4374_;
goto v___jp_4380_;
}
}
else
{
lean_object* v_a_4446_; lean_object* v___x_4448_; uint8_t v_isShared_4449_; uint8_t v_isSharedCheck_4453_; 
lean_dec(v_a_4379_);
lean_dec(v_a_4377_);
lean_dec(v_hName_4370_);
lean_dec_ref(v_p_4369_);
lean_dec(v_mvarId_4368_);
v_a_4446_ = lean_ctor_get(v___x_4432_, 0);
v_isSharedCheck_4453_ = !lean_is_exclusive(v___x_4432_);
if (v_isSharedCheck_4453_ == 0)
{
v___x_4448_ = v___x_4432_;
v_isShared_4449_ = v_isSharedCheck_4453_;
goto v_resetjp_4447_;
}
else
{
lean_inc(v_a_4446_);
lean_dec(v___x_4432_);
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
v___jp_4380_:
{
lean_object* v___x_4385_; lean_object* v___x_4386_; lean_object* v___x_4387_; 
v___x_4385_ = ((lean_object*)(l_Lean_MVarId_byCases___lam__0___closed__1));
lean_inc(v_a_4379_);
v___x_4386_ = l_Lean_Name_append(v_a_4379_, v___x_4385_);
lean_inc(v_a_4377_);
lean_inc(v_hName_4370_);
lean_inc_ref(v_p_4369_);
v___x_4387_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkByCasesSubgoal(v_p_4369_, v_hName_4370_, v_a_4377_, v___x_4386_, v___y_4381_, v___y_4382_, v___y_4383_, v___y_4384_);
if (lean_obj_tag(v___x_4387_) == 0)
{
lean_object* v_a_4388_; lean_object* v_fst_4389_; lean_object* v_snd_4390_; lean_object* v___x_4391_; lean_object* v___x_4392_; lean_object* v___x_4393_; lean_object* v___x_4394_; 
v_a_4388_ = lean_ctor_get(v___x_4387_, 0);
lean_inc(v_a_4388_);
lean_dec_ref_known(v___x_4387_, 1);
v_fst_4389_ = lean_ctor_get(v_a_4388_, 0);
lean_inc(v_fst_4389_);
v_snd_4390_ = lean_ctor_get(v_a_4388_, 1);
lean_inc(v_snd_4390_);
lean_dec(v_a_4388_);
lean_inc_ref(v_p_4369_);
v___x_4391_ = l_Lean_mkNot(v_p_4369_);
v___x_4392_ = ((lean_object*)(l_Lean_MVarId_byCases___lam__0___closed__3));
v___x_4393_ = l_Lean_Name_append(v_a_4379_, v___x_4392_);
lean_inc(v_a_4377_);
v___x_4394_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkByCasesSubgoal(v___x_4391_, v_hName_4370_, v_a_4377_, v___x_4393_, v___y_4381_, v___y_4382_, v___y_4383_, v___y_4384_);
if (lean_obj_tag(v___x_4394_) == 0)
{
lean_object* v_a_4395_; lean_object* v_fst_4396_; lean_object* v_snd_4397_; lean_object* v___x_4399_; uint8_t v_isShared_4400_; uint8_t v_isSharedCheck_4415_; 
v_a_4395_ = lean_ctor_get(v___x_4394_, 0);
lean_inc(v_a_4395_);
lean_dec_ref_known(v___x_4394_, 1);
v_fst_4396_ = lean_ctor_get(v_a_4395_, 0);
v_snd_4397_ = lean_ctor_get(v_a_4395_, 1);
v_isSharedCheck_4415_ = !lean_is_exclusive(v_a_4395_);
if (v_isSharedCheck_4415_ == 0)
{
v___x_4399_ = v_a_4395_;
v_isShared_4400_ = v_isSharedCheck_4415_;
goto v_resetjp_4398_;
}
else
{
lean_inc(v_snd_4397_);
lean_inc(v_fst_4396_);
lean_dec(v_a_4395_);
v___x_4399_ = lean_box(0);
v_isShared_4400_ = v_isSharedCheck_4415_;
goto v_resetjp_4398_;
}
v_resetjp_4398_:
{
lean_object* v___x_4401_; lean_object* v___x_4402_; lean_object* v___x_4403_; lean_object* v___x_4405_; uint8_t v_isShared_4406_; uint8_t v_isSharedCheck_4413_; 
v___x_4401_ = lean_obj_once(&l_Lean_MVarId_byCases___lam__0___closed__7, &l_Lean_MVarId_byCases___lam__0___closed__7_once, _init_l_Lean_MVarId_byCases___lam__0___closed__7);
v___x_4402_ = l_Lean_mkApp4(v___x_4401_, v_p_4369_, v_a_4377_, v_fst_4389_, v_fst_4396_);
v___x_4403_ = l_Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1___redArg(v_mvarId_4368_, v___x_4402_, v___y_4382_);
v_isSharedCheck_4413_ = !lean_is_exclusive(v___x_4403_);
if (v_isSharedCheck_4413_ == 0)
{
lean_object* v_unused_4414_; 
v_unused_4414_ = lean_ctor_get(v___x_4403_, 0);
lean_dec(v_unused_4414_);
v___x_4405_ = v___x_4403_;
v_isShared_4406_ = v_isSharedCheck_4413_;
goto v_resetjp_4404_;
}
else
{
lean_dec(v___x_4403_);
v___x_4405_ = lean_box(0);
v_isShared_4406_ = v_isSharedCheck_4413_;
goto v_resetjp_4404_;
}
v_resetjp_4404_:
{
lean_object* v___x_4408_; 
if (v_isShared_4400_ == 0)
{
lean_ctor_set(v___x_4399_, 0, v_snd_4390_);
v___x_4408_ = v___x_4399_;
goto v_reusejp_4407_;
}
else
{
lean_object* v_reuseFailAlloc_4412_; 
v_reuseFailAlloc_4412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4412_, 0, v_snd_4390_);
lean_ctor_set(v_reuseFailAlloc_4412_, 1, v_snd_4397_);
v___x_4408_ = v_reuseFailAlloc_4412_;
goto v_reusejp_4407_;
}
v_reusejp_4407_:
{
lean_object* v___x_4410_; 
if (v_isShared_4406_ == 0)
{
lean_ctor_set(v___x_4405_, 0, v___x_4408_);
v___x_4410_ = v___x_4405_;
goto v_reusejp_4409_;
}
else
{
lean_object* v_reuseFailAlloc_4411_; 
v_reuseFailAlloc_4411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4411_, 0, v___x_4408_);
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
}
else
{
lean_object* v_a_4416_; lean_object* v___x_4418_; uint8_t v_isShared_4419_; uint8_t v_isSharedCheck_4423_; 
lean_dec(v_snd_4390_);
lean_dec(v_fst_4389_);
lean_dec(v_a_4377_);
lean_dec_ref(v_p_4369_);
lean_dec(v_mvarId_4368_);
v_a_4416_ = lean_ctor_get(v___x_4394_, 0);
v_isSharedCheck_4423_ = !lean_is_exclusive(v___x_4394_);
if (v_isSharedCheck_4423_ == 0)
{
v___x_4418_ = v___x_4394_;
v_isShared_4419_ = v_isSharedCheck_4423_;
goto v_resetjp_4417_;
}
else
{
lean_inc(v_a_4416_);
lean_dec(v___x_4394_);
v___x_4418_ = lean_box(0);
v_isShared_4419_ = v_isSharedCheck_4423_;
goto v_resetjp_4417_;
}
v_resetjp_4417_:
{
lean_object* v___x_4421_; 
if (v_isShared_4419_ == 0)
{
v___x_4421_ = v___x_4418_;
goto v_reusejp_4420_;
}
else
{
lean_object* v_reuseFailAlloc_4422_; 
v_reuseFailAlloc_4422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4422_, 0, v_a_4416_);
v___x_4421_ = v_reuseFailAlloc_4422_;
goto v_reusejp_4420_;
}
v_reusejp_4420_:
{
return v___x_4421_;
}
}
}
}
else
{
lean_object* v_a_4424_; lean_object* v___x_4426_; uint8_t v_isShared_4427_; uint8_t v_isSharedCheck_4431_; 
lean_dec(v_a_4379_);
lean_dec(v_a_4377_);
lean_dec(v_hName_4370_);
lean_dec_ref(v_p_4369_);
lean_dec(v_mvarId_4368_);
v_a_4424_ = lean_ctor_get(v___x_4387_, 0);
v_isSharedCheck_4431_ = !lean_is_exclusive(v___x_4387_);
if (v_isSharedCheck_4431_ == 0)
{
v___x_4426_ = v___x_4387_;
v_isShared_4427_ = v_isSharedCheck_4431_;
goto v_resetjp_4425_;
}
else
{
lean_inc(v_a_4424_);
lean_dec(v___x_4387_);
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
}
else
{
lean_object* v_a_4454_; lean_object* v___x_4456_; uint8_t v_isShared_4457_; uint8_t v_isSharedCheck_4461_; 
lean_dec(v_a_4377_);
lean_dec(v_hName_4370_);
lean_dec_ref(v_p_4369_);
lean_dec(v_mvarId_4368_);
v_a_4454_ = lean_ctor_get(v___x_4378_, 0);
v_isSharedCheck_4461_ = !lean_is_exclusive(v___x_4378_);
if (v_isSharedCheck_4461_ == 0)
{
v___x_4456_ = v___x_4378_;
v_isShared_4457_ = v_isSharedCheck_4461_;
goto v_resetjp_4455_;
}
else
{
lean_inc(v_a_4454_);
lean_dec(v___x_4378_);
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
}
else
{
lean_object* v_a_4462_; lean_object* v___x_4464_; uint8_t v_isShared_4465_; uint8_t v_isSharedCheck_4469_; 
lean_dec(v_hName_4370_);
lean_dec_ref(v_p_4369_);
lean_dec(v_mvarId_4368_);
v_a_4462_ = lean_ctor_get(v___x_4376_, 0);
v_isSharedCheck_4469_ = !lean_is_exclusive(v___x_4376_);
if (v_isSharedCheck_4469_ == 0)
{
v___x_4464_ = v___x_4376_;
v_isShared_4465_ = v_isSharedCheck_4469_;
goto v_resetjp_4463_;
}
else
{
lean_inc(v_a_4462_);
lean_dec(v___x_4376_);
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
}
LEAN_EXPORT lean_object* l_Lean_MVarId_byCases___lam__0___boxed(lean_object* v_mvarId_4470_, lean_object* v_p_4471_, lean_object* v_hName_4472_, lean_object* v___y_4473_, lean_object* v___y_4474_, lean_object* v___y_4475_, lean_object* v___y_4476_, lean_object* v___y_4477_){
_start:
{
lean_object* v_res_4478_; 
v_res_4478_ = l_Lean_MVarId_byCases___lam__0(v_mvarId_4470_, v_p_4471_, v_hName_4472_, v___y_4473_, v___y_4474_, v___y_4475_, v___y_4476_);
lean_dec(v___y_4476_);
lean_dec_ref(v___y_4475_);
lean_dec(v___y_4474_);
lean_dec_ref(v___y_4473_);
return v_res_4478_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_byCases(lean_object* v_mvarId_4479_, lean_object* v_p_4480_, lean_object* v_hName_4481_, lean_object* v_a_4482_, lean_object* v_a_4483_, lean_object* v_a_4484_, lean_object* v_a_4485_){
_start:
{
lean_object* v___f_4487_; lean_object* v___x_4488_; 
lean_inc(v_mvarId_4479_);
v___f_4487_ = lean_alloc_closure((void*)(l_Lean_MVarId_byCases___lam__0___boxed), 8, 3);
lean_closure_set(v___f_4487_, 0, v_mvarId_4479_);
lean_closure_set(v___f_4487_, 1, v_p_4480_);
lean_closure_set(v___f_4487_, 2, v_hName_4481_);
v___x_4488_ = l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2___redArg(v_mvarId_4479_, v___f_4487_, v_a_4482_, v_a_4483_, v_a_4484_, v_a_4485_);
return v___x_4488_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_byCases___boxed(lean_object* v_mvarId_4489_, lean_object* v_p_4490_, lean_object* v_hName_4491_, lean_object* v_a_4492_, lean_object* v_a_4493_, lean_object* v_a_4494_, lean_object* v_a_4495_, lean_object* v_a_4496_){
_start:
{
lean_object* v_res_4497_; 
v_res_4497_ = l_Lean_MVarId_byCases(v_mvarId_4489_, v_p_4490_, v_hName_4491_, v_a_4492_, v_a_4493_, v_a_4494_, v_a_4495_);
lean_dec(v_a_4495_);
lean_dec_ref(v_a_4494_);
lean_dec(v_a_4493_);
lean_dec_ref(v_a_4492_);
return v_res_4497_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_byCasesDec___lam__0(lean_object* v_mvarId_4501_, lean_object* v_p_4502_, lean_object* v_hName_4503_, lean_object* v_dec_4504_, lean_object* v___y_4505_, lean_object* v___y_4506_, lean_object* v___y_4507_, lean_object* v___y_4508_){
_start:
{
lean_object* v___x_4510_; 
lean_inc(v_mvarId_4501_);
v___x_4510_ = l_Lean_MVarId_getType(v_mvarId_4501_, v___y_4505_, v___y_4506_, v___y_4507_, v___y_4508_);
if (lean_obj_tag(v___x_4510_) == 0)
{
lean_object* v_a_4511_; lean_object* v___x_4512_; 
v_a_4511_ = lean_ctor_get(v___x_4510_, 0);
lean_inc(v_a_4511_);
lean_dec_ref_known(v___x_4510_, 1);
lean_inc(v_mvarId_4501_);
v___x_4512_ = l_Lean_MVarId_getTag(v_mvarId_4501_, v___y_4505_, v___y_4506_, v___y_4507_, v___y_4508_);
if (lean_obj_tag(v___x_4512_) == 0)
{
lean_object* v_a_4513_; lean_object* v___x_4514_; 
v_a_4513_ = lean_ctor_get(v___x_4512_, 0);
lean_inc(v_a_4513_);
lean_dec_ref_known(v___x_4512_, 1);
lean_inc(v_a_4511_);
v___x_4514_ = l_Lean_Meta_getLevel(v_a_4511_, v___y_4505_, v___y_4506_, v___y_4507_, v___y_4508_);
if (lean_obj_tag(v___x_4514_) == 0)
{
lean_object* v_a_4515_; lean_object* v___x_4516_; lean_object* v___x_4517_; lean_object* v___x_4518_; 
v_a_4515_ = lean_ctor_get(v___x_4514_, 0);
lean_inc(v_a_4515_);
lean_dec_ref_known(v___x_4514_, 1);
v___x_4516_ = ((lean_object*)(l_Lean_MVarId_byCases___lam__0___closed__1));
lean_inc(v_a_4513_);
v___x_4517_ = l_Lean_Name_append(v_a_4513_, v___x_4516_);
lean_inc(v_a_4511_);
lean_inc(v_hName_4503_);
lean_inc_ref(v_p_4502_);
v___x_4518_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkByCasesSubgoal(v_p_4502_, v_hName_4503_, v_a_4511_, v___x_4517_, v___y_4505_, v___y_4506_, v___y_4507_, v___y_4508_);
if (lean_obj_tag(v___x_4518_) == 0)
{
lean_object* v_a_4519_; lean_object* v_fst_4520_; lean_object* v_snd_4521_; lean_object* v___x_4523_; uint8_t v_isShared_4524_; uint8_t v_isSharedCheck_4563_; 
v_a_4519_ = lean_ctor_get(v___x_4518_, 0);
lean_inc(v_a_4519_);
lean_dec_ref_known(v___x_4518_, 1);
v_fst_4520_ = lean_ctor_get(v_a_4519_, 0);
v_snd_4521_ = lean_ctor_get(v_a_4519_, 1);
v_isSharedCheck_4563_ = !lean_is_exclusive(v_a_4519_);
if (v_isSharedCheck_4563_ == 0)
{
v___x_4523_ = v_a_4519_;
v_isShared_4524_ = v_isSharedCheck_4563_;
goto v_resetjp_4522_;
}
else
{
lean_inc(v_snd_4521_);
lean_inc(v_fst_4520_);
lean_dec(v_a_4519_);
v___x_4523_ = lean_box(0);
v_isShared_4524_ = v_isSharedCheck_4563_;
goto v_resetjp_4522_;
}
v_resetjp_4522_:
{
lean_object* v___x_4525_; lean_object* v___x_4526_; lean_object* v___x_4527_; lean_object* v___x_4528_; 
lean_inc_ref(v_p_4502_);
v___x_4525_ = l_Lean_mkNot(v_p_4502_);
v___x_4526_ = ((lean_object*)(l_Lean_MVarId_byCases___lam__0___closed__3));
v___x_4527_ = l_Lean_Name_append(v_a_4513_, v___x_4526_);
lean_inc(v_a_4511_);
v___x_4528_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkByCasesSubgoal(v___x_4525_, v_hName_4503_, v_a_4511_, v___x_4527_, v___y_4505_, v___y_4506_, v___y_4507_, v___y_4508_);
if (lean_obj_tag(v___x_4528_) == 0)
{
lean_object* v_a_4529_; lean_object* v_fst_4530_; lean_object* v_snd_4531_; lean_object* v___x_4533_; uint8_t v_isShared_4534_; uint8_t v_isSharedCheck_4554_; 
v_a_4529_ = lean_ctor_get(v___x_4528_, 0);
lean_inc(v_a_4529_);
lean_dec_ref_known(v___x_4528_, 1);
v_fst_4530_ = lean_ctor_get(v_a_4529_, 0);
v_snd_4531_ = lean_ctor_get(v_a_4529_, 1);
v_isSharedCheck_4554_ = !lean_is_exclusive(v_a_4529_);
if (v_isSharedCheck_4554_ == 0)
{
v___x_4533_ = v_a_4529_;
v_isShared_4534_ = v_isSharedCheck_4554_;
goto v_resetjp_4532_;
}
else
{
lean_inc(v_snd_4531_);
lean_inc(v_fst_4530_);
lean_dec(v_a_4529_);
v___x_4533_ = lean_box(0);
v_isShared_4534_ = v_isSharedCheck_4554_;
goto v_resetjp_4532_;
}
v_resetjp_4532_:
{
lean_object* v___x_4535_; lean_object* v___x_4536_; lean_object* v___x_4538_; 
v___x_4535_ = ((lean_object*)(l_Lean_MVarId_byCasesDec___lam__0___closed__1));
v___x_4536_ = lean_box(0);
if (v_isShared_4524_ == 0)
{
lean_ctor_set_tag(v___x_4523_, 1);
lean_ctor_set(v___x_4523_, 1, v___x_4536_);
lean_ctor_set(v___x_4523_, 0, v_a_4515_);
v___x_4538_ = v___x_4523_;
goto v_reusejp_4537_;
}
else
{
lean_object* v_reuseFailAlloc_4553_; 
v_reuseFailAlloc_4553_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4553_, 0, v_a_4515_);
lean_ctor_set(v_reuseFailAlloc_4553_, 1, v___x_4536_);
v___x_4538_ = v_reuseFailAlloc_4553_;
goto v_reusejp_4537_;
}
v_reusejp_4537_:
{
lean_object* v___x_4539_; lean_object* v___x_4540_; lean_object* v___x_4541_; lean_object* v___x_4543_; uint8_t v_isShared_4544_; uint8_t v_isSharedCheck_4551_; 
v___x_4539_ = l_Lean_Expr_const___override(v___x_4535_, v___x_4538_);
v___x_4540_ = l_Lean_mkApp5(v___x_4539_, v_a_4511_, v_p_4502_, v_dec_4504_, v_fst_4520_, v_fst_4530_);
v___x_4541_ = l_Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1___redArg(v_mvarId_4501_, v___x_4540_, v___y_4506_);
v_isSharedCheck_4551_ = !lean_is_exclusive(v___x_4541_);
if (v_isSharedCheck_4551_ == 0)
{
lean_object* v_unused_4552_; 
v_unused_4552_ = lean_ctor_get(v___x_4541_, 0);
lean_dec(v_unused_4552_);
v___x_4543_ = v___x_4541_;
v_isShared_4544_ = v_isSharedCheck_4551_;
goto v_resetjp_4542_;
}
else
{
lean_dec(v___x_4541_);
v___x_4543_ = lean_box(0);
v_isShared_4544_ = v_isSharedCheck_4551_;
goto v_resetjp_4542_;
}
v_resetjp_4542_:
{
lean_object* v___x_4546_; 
if (v_isShared_4534_ == 0)
{
lean_ctor_set(v___x_4533_, 0, v_snd_4521_);
v___x_4546_ = v___x_4533_;
goto v_reusejp_4545_;
}
else
{
lean_object* v_reuseFailAlloc_4550_; 
v_reuseFailAlloc_4550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4550_, 0, v_snd_4521_);
lean_ctor_set(v_reuseFailAlloc_4550_, 1, v_snd_4531_);
v___x_4546_ = v_reuseFailAlloc_4550_;
goto v_reusejp_4545_;
}
v_reusejp_4545_:
{
lean_object* v___x_4548_; 
if (v_isShared_4544_ == 0)
{
lean_ctor_set(v___x_4543_, 0, v___x_4546_);
v___x_4548_ = v___x_4543_;
goto v_reusejp_4547_;
}
else
{
lean_object* v_reuseFailAlloc_4549_; 
v_reuseFailAlloc_4549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4549_, 0, v___x_4546_);
v___x_4548_ = v_reuseFailAlloc_4549_;
goto v_reusejp_4547_;
}
v_reusejp_4547_:
{
return v___x_4548_;
}
}
}
}
}
}
else
{
lean_object* v_a_4555_; lean_object* v___x_4557_; uint8_t v_isShared_4558_; uint8_t v_isSharedCheck_4562_; 
lean_del_object(v___x_4523_);
lean_dec(v_snd_4521_);
lean_dec(v_fst_4520_);
lean_dec(v_a_4515_);
lean_dec(v_a_4511_);
lean_dec_ref(v_dec_4504_);
lean_dec_ref(v_p_4502_);
lean_dec(v_mvarId_4501_);
v_a_4555_ = lean_ctor_get(v___x_4528_, 0);
v_isSharedCheck_4562_ = !lean_is_exclusive(v___x_4528_);
if (v_isSharedCheck_4562_ == 0)
{
v___x_4557_ = v___x_4528_;
v_isShared_4558_ = v_isSharedCheck_4562_;
goto v_resetjp_4556_;
}
else
{
lean_inc(v_a_4555_);
lean_dec(v___x_4528_);
v___x_4557_ = lean_box(0);
v_isShared_4558_ = v_isSharedCheck_4562_;
goto v_resetjp_4556_;
}
v_resetjp_4556_:
{
lean_object* v___x_4560_; 
if (v_isShared_4558_ == 0)
{
v___x_4560_ = v___x_4557_;
goto v_reusejp_4559_;
}
else
{
lean_object* v_reuseFailAlloc_4561_; 
v_reuseFailAlloc_4561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4561_, 0, v_a_4555_);
v___x_4560_ = v_reuseFailAlloc_4561_;
goto v_reusejp_4559_;
}
v_reusejp_4559_:
{
return v___x_4560_;
}
}
}
}
}
else
{
lean_object* v_a_4564_; lean_object* v___x_4566_; uint8_t v_isShared_4567_; uint8_t v_isSharedCheck_4571_; 
lean_dec(v_a_4515_);
lean_dec(v_a_4513_);
lean_dec(v_a_4511_);
lean_dec_ref(v_dec_4504_);
lean_dec(v_hName_4503_);
lean_dec_ref(v_p_4502_);
lean_dec(v_mvarId_4501_);
v_a_4564_ = lean_ctor_get(v___x_4518_, 0);
v_isSharedCheck_4571_ = !lean_is_exclusive(v___x_4518_);
if (v_isSharedCheck_4571_ == 0)
{
v___x_4566_ = v___x_4518_;
v_isShared_4567_ = v_isSharedCheck_4571_;
goto v_resetjp_4565_;
}
else
{
lean_inc(v_a_4564_);
lean_dec(v___x_4518_);
v___x_4566_ = lean_box(0);
v_isShared_4567_ = v_isSharedCheck_4571_;
goto v_resetjp_4565_;
}
v_resetjp_4565_:
{
lean_object* v___x_4569_; 
if (v_isShared_4567_ == 0)
{
v___x_4569_ = v___x_4566_;
goto v_reusejp_4568_;
}
else
{
lean_object* v_reuseFailAlloc_4570_; 
v_reuseFailAlloc_4570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4570_, 0, v_a_4564_);
v___x_4569_ = v_reuseFailAlloc_4570_;
goto v_reusejp_4568_;
}
v_reusejp_4568_:
{
return v___x_4569_;
}
}
}
}
else
{
lean_object* v_a_4572_; lean_object* v___x_4574_; uint8_t v_isShared_4575_; uint8_t v_isSharedCheck_4579_; 
lean_dec(v_a_4513_);
lean_dec(v_a_4511_);
lean_dec_ref(v_dec_4504_);
lean_dec(v_hName_4503_);
lean_dec_ref(v_p_4502_);
lean_dec(v_mvarId_4501_);
v_a_4572_ = lean_ctor_get(v___x_4514_, 0);
v_isSharedCheck_4579_ = !lean_is_exclusive(v___x_4514_);
if (v_isSharedCheck_4579_ == 0)
{
v___x_4574_ = v___x_4514_;
v_isShared_4575_ = v_isSharedCheck_4579_;
goto v_resetjp_4573_;
}
else
{
lean_inc(v_a_4572_);
lean_dec(v___x_4514_);
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
lean_dec(v_a_4511_);
lean_dec_ref(v_dec_4504_);
lean_dec(v_hName_4503_);
lean_dec_ref(v_p_4502_);
lean_dec(v_mvarId_4501_);
v_a_4580_ = lean_ctor_get(v___x_4512_, 0);
v_isSharedCheck_4587_ = !lean_is_exclusive(v___x_4512_);
if (v_isSharedCheck_4587_ == 0)
{
v___x_4582_ = v___x_4512_;
v_isShared_4583_ = v_isSharedCheck_4587_;
goto v_resetjp_4581_;
}
else
{
lean_inc(v_a_4580_);
lean_dec(v___x_4512_);
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
lean_dec_ref(v_dec_4504_);
lean_dec(v_hName_4503_);
lean_dec_ref(v_p_4502_);
lean_dec(v_mvarId_4501_);
v_a_4588_ = lean_ctor_get(v___x_4510_, 0);
v_isSharedCheck_4595_ = !lean_is_exclusive(v___x_4510_);
if (v_isSharedCheck_4595_ == 0)
{
v___x_4590_ = v___x_4510_;
v_isShared_4591_ = v_isSharedCheck_4595_;
goto v_resetjp_4589_;
}
else
{
lean_inc(v_a_4588_);
lean_dec(v___x_4510_);
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
}
LEAN_EXPORT lean_object* l_Lean_MVarId_byCasesDec___lam__0___boxed(lean_object* v_mvarId_4596_, lean_object* v_p_4597_, lean_object* v_hName_4598_, lean_object* v_dec_4599_, lean_object* v___y_4600_, lean_object* v___y_4601_, lean_object* v___y_4602_, lean_object* v___y_4603_, lean_object* v___y_4604_){
_start:
{
lean_object* v_res_4605_; 
v_res_4605_ = l_Lean_MVarId_byCasesDec___lam__0(v_mvarId_4596_, v_p_4597_, v_hName_4598_, v_dec_4599_, v___y_4600_, v___y_4601_, v___y_4602_, v___y_4603_);
lean_dec(v___y_4603_);
lean_dec_ref(v___y_4602_);
lean_dec(v___y_4601_);
lean_dec_ref(v___y_4600_);
return v_res_4605_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_byCasesDec(lean_object* v_mvarId_4606_, lean_object* v_p_4607_, lean_object* v_dec_4608_, lean_object* v_hName_4609_, lean_object* v_a_4610_, lean_object* v_a_4611_, lean_object* v_a_4612_, lean_object* v_a_4613_){
_start:
{
lean_object* v___f_4615_; lean_object* v___x_4616_; 
lean_inc(v_mvarId_4606_);
v___f_4615_ = lean_alloc_closure((void*)(l_Lean_MVarId_byCasesDec___lam__0___boxed), 9, 4);
lean_closure_set(v___f_4615_, 0, v_mvarId_4606_);
lean_closure_set(v___f_4615_, 1, v_p_4607_);
lean_closure_set(v___f_4615_, 2, v_hName_4609_);
lean_closure_set(v___f_4615_, 3, v_dec_4608_);
v___x_4616_ = l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2___redArg(v_mvarId_4606_, v___f_4615_, v_a_4610_, v_a_4611_, v_a_4612_, v_a_4613_);
return v___x_4616_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_byCasesDec___boxed(lean_object* v_mvarId_4617_, lean_object* v_p_4618_, lean_object* v_dec_4619_, lean_object* v_hName_4620_, lean_object* v_a_4621_, lean_object* v_a_4622_, lean_object* v_a_4623_, lean_object* v_a_4624_, lean_object* v_a_4625_){
_start:
{
lean_object* v_res_4626_; 
v_res_4626_ = l_Lean_MVarId_byCasesDec(v_mvarId_4617_, v_p_4618_, v_dec_4619_, v_hName_4620_, v_a_4621_, v_a_4622_, v_a_4623_, v_a_4624_);
lean_dec(v_a_4624_);
lean_dec_ref(v_a_4623_);
lean_dec(v_a_4622_);
lean_dec_ref(v_a_4621_);
return v_res_4626_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4678_; lean_object* v___x_4679_; lean_object* v___x_4680_; 
v___x_4678_ = lean_unsigned_to_nat(4241171151u);
v___x_4679_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_));
v___x_4680_ = l_Lean_Name_num___override(v___x_4679_, v___x_4678_);
return v___x_4680_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4682_; lean_object* v___x_4683_; lean_object* v___x_4684_; 
v___x_4682_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_));
v___x_4683_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_);
v___x_4684_ = l_Lean_Name_str___override(v___x_4683_, v___x_4682_);
return v___x_4684_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4686_; lean_object* v___x_4687_; lean_object* v___x_4688_; 
v___x_4686_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_));
v___x_4687_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_);
v___x_4688_ = l_Lean_Name_str___override(v___x_4687_, v___x_4686_);
return v___x_4688_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4689_; lean_object* v___x_4690_; lean_object* v___x_4691_; 
v___x_4689_ = lean_unsigned_to_nat(2u);
v___x_4690_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_);
v___x_4691_ = l_Lean_Name_num___override(v___x_4690_, v___x_4689_);
return v___x_4691_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4693_; uint8_t v___x_4694_; lean_object* v___x_4695_; lean_object* v___x_4696_; 
v___x_4693_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_));
v___x_4694_ = 0;
v___x_4695_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_);
v___x_4696_ = l_Lean_registerTraceClass(v___x_4693_, v___x_4694_, v___x_4695_);
return v___x_4696_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2____boxed(lean_object* v_a_4697_){
_start:
{
lean_object* v_res_4698_; 
v_res_4698_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_();
return v_res_4698_;
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
