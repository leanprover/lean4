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
lean_object* v_ks_853_; lean_object* v_vs_854_; lean_object* v___x_856_; uint8_t v_isShared_857_; uint8_t v_isSharedCheck_872_; 
v_ks_853_ = lean_ctor_get(v_x_802_, 0);
v_vs_854_ = lean_ctor_get(v_x_802_, 1);
v_isSharedCheck_872_ = !lean_is_exclusive(v_x_802_);
if (v_isSharedCheck_872_ == 0)
{
v___x_856_ = v_x_802_;
v_isShared_857_ = v_isSharedCheck_872_;
goto v_resetjp_855_;
}
else
{
lean_inc(v_vs_854_);
lean_inc(v_ks_853_);
lean_dec(v_x_802_);
v___x_856_ = lean_box(0);
v_isShared_857_ = v_isSharedCheck_872_;
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
lean_object* v_reuseFailAlloc_871_; 
v_reuseFailAlloc_871_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_871_, 0, v_ks_853_);
lean_ctor_set(v_reuseFailAlloc_871_, 1, v_vs_854_);
v___x_859_ = v_reuseFailAlloc_871_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
lean_object* v_newNode_860_; size_t v___x_861_; uint8_t v___x_862_; 
v_newNode_860_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__4___redArg(v___x_859_, v_x_805_, v_x_806_);
v___x_861_ = ((size_t)7ULL);
v___x_862_ = lean_usize_dec_le(v___x_861_, v_x_804_);
if (v___x_862_ == 0)
{
lean_object* v___x_863_; lean_object* v___x_864_; uint8_t v___x_865_; 
v___x_863_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_860_);
v___x_864_ = lean_unsigned_to_nat(4u);
v___x_865_ = lean_nat_dec_lt(v___x_863_, v___x_864_);
lean_dec(v___x_863_);
if (v___x_865_ == 0)
{
lean_object* v_ks_866_; lean_object* v_vs_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; 
v_ks_866_ = lean_ctor_get(v_newNode_860_, 0);
lean_inc_ref(v_ks_866_);
v_vs_867_ = lean_ctor_get(v_newNode_860_, 1);
lean_inc_ref(v_vs_867_);
lean_dec_ref(v_newNode_860_);
v___x_868_ = lean_unsigned_to_nat(0u);
v___x_869_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg___closed__0);
v___x_870_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__5___redArg(v_x_804_, v_ks_866_, v_vs_867_, v___x_868_, v___x_869_);
lean_dec_ref(v_vs_867_);
lean_dec_ref(v_ks_866_);
return v___x_870_;
}
else
{
return v_newNode_860_;
}
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
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__5___redArg(size_t v_depth_873_, lean_object* v_keys_874_, lean_object* v_vals_875_, lean_object* v_i_876_, lean_object* v_entries_877_){
_start:
{
lean_object* v___x_878_; uint8_t v___x_879_; 
v___x_878_ = lean_array_get_size(v_keys_874_);
v___x_879_ = lean_nat_dec_lt(v_i_876_, v___x_878_);
if (v___x_879_ == 0)
{
lean_dec(v_i_876_);
return v_entries_877_;
}
else
{
lean_object* v_k_880_; lean_object* v_v_881_; uint64_t v___x_882_; size_t v_h_883_; size_t v___x_884_; lean_object* v___x_885_; size_t v___x_886_; size_t v___x_887_; size_t v___x_888_; size_t v_h_889_; lean_object* v___x_890_; lean_object* v___x_891_; 
v_k_880_ = lean_array_fget_borrowed(v_keys_874_, v_i_876_);
v_v_881_ = lean_array_fget_borrowed(v_vals_875_, v_i_876_);
v___x_882_ = l_Lean_instHashableMVarId_hash(v_k_880_);
v_h_883_ = lean_uint64_to_usize(v___x_882_);
v___x_884_ = ((size_t)5ULL);
v___x_885_ = lean_unsigned_to_nat(1u);
v___x_886_ = ((size_t)1ULL);
v___x_887_ = lean_usize_sub(v_depth_873_, v___x_886_);
v___x_888_ = lean_usize_mul(v___x_884_, v___x_887_);
v_h_889_ = lean_usize_shift_right(v_h_883_, v___x_888_);
v___x_890_ = lean_nat_add(v_i_876_, v___x_885_);
lean_dec(v_i_876_);
lean_inc(v_v_881_);
lean_inc(v_k_880_);
v___x_891_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg(v_entries_877_, v_h_889_, v_depth_873_, v_k_880_, v_v_881_);
v_i_876_ = v___x_890_;
v_entries_877_ = v___x_891_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__5___redArg___boxed(lean_object* v_depth_893_, lean_object* v_keys_894_, lean_object* v_vals_895_, lean_object* v_i_896_, lean_object* v_entries_897_){
_start:
{
size_t v_depth_boxed_898_; lean_object* v_res_899_; 
v_depth_boxed_898_ = lean_unbox_usize(v_depth_893_);
lean_dec(v_depth_893_);
v_res_899_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__5___redArg(v_depth_boxed_898_, v_keys_894_, v_vals_895_, v_i_896_, v_entries_897_);
lean_dec_ref(v_vals_895_);
lean_dec_ref(v_keys_894_);
return v_res_899_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_x_900_, lean_object* v_x_901_, lean_object* v_x_902_, lean_object* v_x_903_, lean_object* v_x_904_){
_start:
{
size_t v_x_2547__boxed_905_; size_t v_x_2548__boxed_906_; lean_object* v_res_907_; 
v_x_2547__boxed_905_ = lean_unbox_usize(v_x_901_);
lean_dec(v_x_901_);
v_x_2548__boxed_906_ = lean_unbox_usize(v_x_902_);
lean_dec(v_x_902_);
v_res_907_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg(v_x_900_, v_x_2547__boxed_905_, v_x_2548__boxed_906_, v_x_903_, v_x_904_);
return v_res_907_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1___redArg(lean_object* v_x_908_, lean_object* v_x_909_, lean_object* v_x_910_){
_start:
{
uint64_t v___x_911_; size_t v___x_912_; size_t v___x_913_; lean_object* v___x_914_; 
v___x_911_ = l_Lean_instHashableMVarId_hash(v_x_909_);
v___x_912_ = lean_uint64_to_usize(v___x_911_);
v___x_913_ = ((size_t)1ULL);
v___x_914_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg(v_x_908_, v___x_912_, v___x_913_, v_x_909_, v_x_910_);
return v___x_914_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1___redArg(lean_object* v_mvarId_915_, lean_object* v_val_916_, lean_object* v___y_917_){
_start:
{
lean_object* v___x_919_; lean_object* v_mctx_920_; lean_object* v_cache_921_; lean_object* v_zetaDeltaFVarIds_922_; lean_object* v_postponed_923_; lean_object* v_diag_924_; lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_953_; 
v___x_919_ = lean_st_ref_take(v___y_917_);
v_mctx_920_ = lean_ctor_get(v___x_919_, 0);
v_cache_921_ = lean_ctor_get(v___x_919_, 1);
v_zetaDeltaFVarIds_922_ = lean_ctor_get(v___x_919_, 2);
v_postponed_923_ = lean_ctor_get(v___x_919_, 3);
v_diag_924_ = lean_ctor_get(v___x_919_, 4);
v_isSharedCheck_953_ = !lean_is_exclusive(v___x_919_);
if (v_isSharedCheck_953_ == 0)
{
v___x_926_ = v___x_919_;
v_isShared_927_ = v_isSharedCheck_953_;
goto v_resetjp_925_;
}
else
{
lean_inc(v_diag_924_);
lean_inc(v_postponed_923_);
lean_inc(v_zetaDeltaFVarIds_922_);
lean_inc(v_cache_921_);
lean_inc(v_mctx_920_);
lean_dec(v___x_919_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_953_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
lean_object* v_depth_928_; lean_object* v_levelAssignDepth_929_; lean_object* v_lmvarCounter_930_; lean_object* v_mvarCounter_931_; lean_object* v_lDecls_932_; lean_object* v_decls_933_; lean_object* v_userNames_934_; lean_object* v_lAssignment_935_; lean_object* v_eAssignment_936_; lean_object* v_dAssignment_937_; lean_object* v_instanceTypedMVars_938_; lean_object* v___x_940_; uint8_t v_isShared_941_; uint8_t v_isSharedCheck_952_; 
v_depth_928_ = lean_ctor_get(v_mctx_920_, 0);
v_levelAssignDepth_929_ = lean_ctor_get(v_mctx_920_, 1);
v_lmvarCounter_930_ = lean_ctor_get(v_mctx_920_, 2);
v_mvarCounter_931_ = lean_ctor_get(v_mctx_920_, 3);
v_lDecls_932_ = lean_ctor_get(v_mctx_920_, 4);
v_decls_933_ = lean_ctor_get(v_mctx_920_, 5);
v_userNames_934_ = lean_ctor_get(v_mctx_920_, 6);
v_lAssignment_935_ = lean_ctor_get(v_mctx_920_, 7);
v_eAssignment_936_ = lean_ctor_get(v_mctx_920_, 8);
v_dAssignment_937_ = lean_ctor_get(v_mctx_920_, 9);
v_instanceTypedMVars_938_ = lean_ctor_get(v_mctx_920_, 10);
v_isSharedCheck_952_ = !lean_is_exclusive(v_mctx_920_);
if (v_isSharedCheck_952_ == 0)
{
v___x_940_ = v_mctx_920_;
v_isShared_941_ = v_isSharedCheck_952_;
goto v_resetjp_939_;
}
else
{
lean_inc(v_instanceTypedMVars_938_);
lean_inc(v_dAssignment_937_);
lean_inc(v_eAssignment_936_);
lean_inc(v_lAssignment_935_);
lean_inc(v_userNames_934_);
lean_inc(v_decls_933_);
lean_inc(v_lDecls_932_);
lean_inc(v_mvarCounter_931_);
lean_inc(v_lmvarCounter_930_);
lean_inc(v_levelAssignDepth_929_);
lean_inc(v_depth_928_);
lean_dec(v_mctx_920_);
v___x_940_ = lean_box(0);
v_isShared_941_ = v_isSharedCheck_952_;
goto v_resetjp_939_;
}
v_resetjp_939_:
{
lean_object* v___x_942_; lean_object* v___x_944_; 
v___x_942_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1___redArg(v_eAssignment_936_, v_mvarId_915_, v_val_916_);
if (v_isShared_941_ == 0)
{
lean_ctor_set(v___x_940_, 8, v___x_942_);
v___x_944_ = v___x_940_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v_depth_928_);
lean_ctor_set(v_reuseFailAlloc_951_, 1, v_levelAssignDepth_929_);
lean_ctor_set(v_reuseFailAlloc_951_, 2, v_lmvarCounter_930_);
lean_ctor_set(v_reuseFailAlloc_951_, 3, v_mvarCounter_931_);
lean_ctor_set(v_reuseFailAlloc_951_, 4, v_lDecls_932_);
lean_ctor_set(v_reuseFailAlloc_951_, 5, v_decls_933_);
lean_ctor_set(v_reuseFailAlloc_951_, 6, v_userNames_934_);
lean_ctor_set(v_reuseFailAlloc_951_, 7, v_lAssignment_935_);
lean_ctor_set(v_reuseFailAlloc_951_, 8, v___x_942_);
lean_ctor_set(v_reuseFailAlloc_951_, 9, v_dAssignment_937_);
lean_ctor_set(v_reuseFailAlloc_951_, 10, v_instanceTypedMVars_938_);
v___x_944_ = v_reuseFailAlloc_951_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
lean_object* v___x_946_; 
if (v_isShared_927_ == 0)
{
lean_ctor_set(v___x_926_, 0, v___x_944_);
v___x_946_ = v___x_926_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v___x_944_);
lean_ctor_set(v_reuseFailAlloc_950_, 1, v_cache_921_);
lean_ctor_set(v_reuseFailAlloc_950_, 2, v_zetaDeltaFVarIds_922_);
lean_ctor_set(v_reuseFailAlloc_950_, 3, v_postponed_923_);
lean_ctor_set(v_reuseFailAlloc_950_, 4, v_diag_924_);
v___x_946_ = v_reuseFailAlloc_950_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; 
v___x_947_ = lean_st_ref_put(v___y_917_, v___x_946_);
v___x_948_ = lean_box(0);
v___x_949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_949_, 0, v___x_948_);
return v___x_949_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1___redArg___boxed(lean_object* v_mvarId_954_, lean_object* v_val_955_, lean_object* v___y_956_, lean_object* v___y_957_){
_start:
{
lean_object* v_res_958_; 
v_res_958_ = l_Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1___redArg(v_mvarId_954_, v_val_955_, v___y_956_);
lean_dec(v___y_956_);
return v_res_958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeTargetsEq___lam__2(lean_object* v_mvarId_959_, lean_object* v___x_960_, lean_object* v_motiveType_961_, lean_object* v___f_962_, lean_object* v_targets_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_){
_start:
{
lean_object* v___x_969_; 
lean_inc(v_mvarId_959_);
v___x_969_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_959_, v___x_960_, v___y_964_, v___y_965_, v___y_966_, v___y_967_);
if (lean_obj_tag(v___x_969_) == 0)
{
uint8_t v___x_970_; lean_object* v___x_971_; 
lean_dec_ref_known(v___x_969_, 1);
v___x_970_ = 0;
v___x_971_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_generalizeTargetsEq_spec__0___redArg(v_motiveType_961_, v___f_962_, v___x_970_, v___x_970_, v___y_964_, v___y_965_, v___y_966_, v___y_967_);
if (lean_obj_tag(v___x_971_) == 0)
{
lean_object* v_a_972_; lean_object* v_fst_973_; lean_object* v_snd_974_; lean_object* v___x_975_; 
v_a_972_ = lean_ctor_get(v___x_971_, 0);
lean_inc(v_a_972_);
lean_dec_ref_known(v___x_971_, 1);
v_fst_973_ = lean_ctor_get(v_a_972_, 0);
lean_inc(v_fst_973_);
v_snd_974_ = lean_ctor_get(v_a_972_, 1);
lean_inc(v_snd_974_);
lean_dec(v_a_972_);
lean_inc(v_mvarId_959_);
v___x_975_ = l_Lean_MVarId_getTag(v_mvarId_959_, v___y_964_, v___y_965_, v___y_966_, v___y_967_);
if (lean_obj_tag(v___x_975_) == 0)
{
lean_object* v_a_976_; lean_object* v___x_977_; 
v_a_976_ = lean_ctor_get(v___x_975_, 0);
lean_inc(v_a_976_);
lean_dec_ref_known(v___x_975_, 1);
v___x_977_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_fst_973_, v_a_976_, v___y_964_, v___y_965_, v___y_966_, v___y_967_);
if (lean_obj_tag(v___x_977_) == 0)
{
lean_object* v_a_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_983_; uint8_t v_isShared_984_; uint8_t v_isSharedCheck_989_; 
v_a_978_ = lean_ctor_get(v___x_977_, 0);
lean_inc_n(v_a_978_, 2);
lean_dec_ref_known(v___x_977_, 1);
v___x_979_ = l_Lean_mkAppN(v_a_978_, v_targets_963_);
v___x_980_ = l_Lean_mkAppN(v___x_979_, v_snd_974_);
lean_dec(v_snd_974_);
v___x_981_ = l_Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1___redArg(v_mvarId_959_, v___x_980_, v___y_965_);
v_isSharedCheck_989_ = !lean_is_exclusive(v___x_981_);
if (v_isSharedCheck_989_ == 0)
{
lean_object* v_unused_990_; 
v_unused_990_ = lean_ctor_get(v___x_981_, 0);
lean_dec(v_unused_990_);
v___x_983_ = v___x_981_;
v_isShared_984_ = v_isSharedCheck_989_;
goto v_resetjp_982_;
}
else
{
lean_dec(v___x_981_);
v___x_983_ = lean_box(0);
v_isShared_984_ = v_isSharedCheck_989_;
goto v_resetjp_982_;
}
v_resetjp_982_:
{
lean_object* v___x_985_; lean_object* v___x_987_; 
v___x_985_ = l_Lean_Expr_mvarId_x21(v_a_978_);
lean_dec(v_a_978_);
if (v_isShared_984_ == 0)
{
lean_ctor_set(v___x_983_, 0, v___x_985_);
v___x_987_ = v___x_983_;
goto v_reusejp_986_;
}
else
{
lean_object* v_reuseFailAlloc_988_; 
v_reuseFailAlloc_988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_988_, 0, v___x_985_);
v___x_987_ = v_reuseFailAlloc_988_;
goto v_reusejp_986_;
}
v_reusejp_986_:
{
return v___x_987_;
}
}
}
else
{
lean_object* v_a_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_998_; 
lean_dec(v_snd_974_);
lean_dec(v_mvarId_959_);
v_a_991_ = lean_ctor_get(v___x_977_, 0);
v_isSharedCheck_998_ = !lean_is_exclusive(v___x_977_);
if (v_isSharedCheck_998_ == 0)
{
v___x_993_ = v___x_977_;
v_isShared_994_ = v_isSharedCheck_998_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_a_991_);
lean_dec(v___x_977_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_998_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
lean_object* v___x_996_; 
if (v_isShared_994_ == 0)
{
v___x_996_ = v___x_993_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v_a_991_);
v___x_996_ = v_reuseFailAlloc_997_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
return v___x_996_;
}
}
}
}
else
{
lean_object* v_a_999_; lean_object* v___x_1001_; uint8_t v_isShared_1002_; uint8_t v_isSharedCheck_1006_; 
lean_dec(v_snd_974_);
lean_dec(v_fst_973_);
lean_dec(v_mvarId_959_);
v_a_999_ = lean_ctor_get(v___x_975_, 0);
v_isSharedCheck_1006_ = !lean_is_exclusive(v___x_975_);
if (v_isSharedCheck_1006_ == 0)
{
v___x_1001_ = v___x_975_;
v_isShared_1002_ = v_isSharedCheck_1006_;
goto v_resetjp_1000_;
}
else
{
lean_inc(v_a_999_);
lean_dec(v___x_975_);
v___x_1001_ = lean_box(0);
v_isShared_1002_ = v_isSharedCheck_1006_;
goto v_resetjp_1000_;
}
v_resetjp_1000_:
{
lean_object* v___x_1004_; 
if (v_isShared_1002_ == 0)
{
v___x_1004_ = v___x_1001_;
goto v_reusejp_1003_;
}
else
{
lean_object* v_reuseFailAlloc_1005_; 
v_reuseFailAlloc_1005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1005_, 0, v_a_999_);
v___x_1004_ = v_reuseFailAlloc_1005_;
goto v_reusejp_1003_;
}
v_reusejp_1003_:
{
return v___x_1004_;
}
}
}
}
else
{
lean_object* v_a_1007_; lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1014_; 
lean_dec(v_mvarId_959_);
v_a_1007_ = lean_ctor_get(v___x_971_, 0);
v_isSharedCheck_1014_ = !lean_is_exclusive(v___x_971_);
if (v_isSharedCheck_1014_ == 0)
{
v___x_1009_ = v___x_971_;
v_isShared_1010_ = v_isSharedCheck_1014_;
goto v_resetjp_1008_;
}
else
{
lean_inc(v_a_1007_);
lean_dec(v___x_971_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1014_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
lean_object* v___x_1012_; 
if (v_isShared_1010_ == 0)
{
v___x_1012_ = v___x_1009_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v_a_1007_);
v___x_1012_ = v_reuseFailAlloc_1013_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
return v___x_1012_;
}
}
}
}
else
{
lean_object* v_a_1015_; lean_object* v___x_1017_; uint8_t v_isShared_1018_; uint8_t v_isSharedCheck_1022_; 
lean_dec_ref(v___f_962_);
lean_dec_ref(v_motiveType_961_);
lean_dec(v_mvarId_959_);
v_a_1015_ = lean_ctor_get(v___x_969_, 0);
v_isSharedCheck_1022_ = !lean_is_exclusive(v___x_969_);
if (v_isSharedCheck_1022_ == 0)
{
v___x_1017_ = v___x_969_;
v_isShared_1018_ = v_isSharedCheck_1022_;
goto v_resetjp_1016_;
}
else
{
lean_inc(v_a_1015_);
lean_dec(v___x_969_);
v___x_1017_ = lean_box(0);
v_isShared_1018_ = v_isSharedCheck_1022_;
goto v_resetjp_1016_;
}
v_resetjp_1016_:
{
lean_object* v___x_1020_; 
if (v_isShared_1018_ == 0)
{
v___x_1020_ = v___x_1017_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v_a_1015_);
v___x_1020_ = v_reuseFailAlloc_1021_;
goto v_reusejp_1019_;
}
v_reusejp_1019_:
{
return v___x_1020_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeTargetsEq___lam__2___boxed(lean_object* v_mvarId_1023_, lean_object* v___x_1024_, lean_object* v_motiveType_1025_, lean_object* v___f_1026_, lean_object* v_targets_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_){
_start:
{
lean_object* v_res_1033_; 
v_res_1033_ = l_Lean_Meta_generalizeTargetsEq___lam__2(v_mvarId_1023_, v___x_1024_, v_motiveType_1025_, v___f_1026_, v_targets_1027_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_);
lean_dec(v___y_1031_);
lean_dec_ref(v___y_1030_);
lean_dec(v___y_1029_);
lean_dec_ref(v___y_1028_);
lean_dec_ref(v_targets_1027_);
return v_res_1033_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeTargetsEq(lean_object* v_mvarId_1037_, lean_object* v_motiveType_1038_, lean_object* v_targets_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_){
_start:
{
lean_object* v___f_1045_; lean_object* v___x_1046_; lean_object* v___f_1047_; lean_object* v___x_1048_; 
lean_inc_n(v_mvarId_1037_, 2);
lean_inc_ref(v_targets_1039_);
v___f_1045_ = lean_alloc_closure((void*)(l_Lean_Meta_generalizeTargetsEq___lam__1___boxed), 9, 2);
lean_closure_set(v___f_1045_, 0, v_targets_1039_);
lean_closure_set(v___f_1045_, 1, v_mvarId_1037_);
v___x_1046_ = ((lean_object*)(l_Lean_Meta_generalizeTargetsEq___closed__1));
v___f_1047_ = lean_alloc_closure((void*)(l_Lean_Meta_generalizeTargetsEq___lam__2___boxed), 10, 5);
lean_closure_set(v___f_1047_, 0, v_mvarId_1037_);
lean_closure_set(v___f_1047_, 1, v___x_1046_);
lean_closure_set(v___f_1047_, 2, v_motiveType_1038_);
lean_closure_set(v___f_1047_, 3, v___f_1045_);
lean_closure_set(v___f_1047_, 4, v_targets_1039_);
v___x_1048_ = l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2___redArg(v_mvarId_1037_, v___f_1047_, v_a_1040_, v_a_1041_, v_a_1042_, v_a_1043_);
return v___x_1048_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeTargetsEq___boxed(lean_object* v_mvarId_1049_, lean_object* v_motiveType_1050_, lean_object* v_targets_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_){
_start:
{
lean_object* v_res_1057_; 
v_res_1057_ = l_Lean_Meta_generalizeTargetsEq(v_mvarId_1049_, v_motiveType_1050_, v_targets_1051_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_);
lean_dec(v_a_1055_);
lean_dec_ref(v_a_1054_);
lean_dec(v_a_1053_);
lean_dec_ref(v_a_1052_);
return v_res_1057_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1(lean_object* v_mvarId_1058_, lean_object* v_val_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_){
_start:
{
lean_object* v___x_1065_; 
v___x_1065_ = l_Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1___redArg(v_mvarId_1058_, v_val_1059_, v___y_1061_);
return v___x_1065_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1___boxed(lean_object* v_mvarId_1066_, lean_object* v_val_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_){
_start:
{
lean_object* v_res_1073_; 
v_res_1073_ = l_Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1(v_mvarId_1066_, v_val_1067_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_);
lean_dec(v___y_1071_);
lean_dec_ref(v___y_1070_);
lean_dec(v___y_1069_);
lean_dec_ref(v___y_1068_);
return v_res_1073_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1(lean_object* v_00_u03b2_1074_, lean_object* v_x_1075_, lean_object* v_x_1076_, lean_object* v_x_1077_){
_start:
{
lean_object* v___x_1078_; 
v___x_1078_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1___redArg(v_x_1075_, v_x_1076_, v_x_1077_);
return v___x_1078_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3(lean_object* v_00_u03b2_1079_, lean_object* v_x_1080_, size_t v_x_1081_, size_t v_x_1082_, lean_object* v_x_1083_, lean_object* v_x_1084_){
_start:
{
lean_object* v___x_1085_; 
v___x_1085_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg(v_x_1080_, v_x_1081_, v_x_1082_, v_x_1083_, v_x_1084_);
return v___x_1085_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1086_, lean_object* v_x_1087_, lean_object* v_x_1088_, lean_object* v_x_1089_, lean_object* v_x_1090_, lean_object* v_x_1091_){
_start:
{
size_t v_x_2934__boxed_1092_; size_t v_x_2935__boxed_1093_; lean_object* v_res_1094_; 
v_x_2934__boxed_1092_ = lean_unbox_usize(v_x_1088_);
lean_dec(v_x_1088_);
v_x_2935__boxed_1093_ = lean_unbox_usize(v_x_1089_);
lean_dec(v_x_1089_);
v_res_1094_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3(v_00_u03b2_1086_, v_x_1087_, v_x_2934__boxed_1092_, v_x_2935__boxed_1093_, v_x_1090_, v_x_1091_);
return v_res_1094_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_1095_, lean_object* v_n_1096_, lean_object* v_k_1097_, lean_object* v_v_1098_){
_start:
{
lean_object* v___x_1099_; 
v___x_1099_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__4___redArg(v_n_1096_, v_k_1097_, v_v_1098_);
return v___x_1099_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__5(lean_object* v_00_u03b2_1100_, size_t v_depth_1101_, lean_object* v_keys_1102_, lean_object* v_vals_1103_, lean_object* v_heq_1104_, lean_object* v_i_1105_, lean_object* v_entries_1106_){
_start:
{
lean_object* v___x_1107_; 
v___x_1107_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__5___redArg(v_depth_1101_, v_keys_1102_, v_vals_1103_, v_i_1105_, v_entries_1106_);
return v___x_1107_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__5___boxed(lean_object* v_00_u03b2_1108_, lean_object* v_depth_1109_, lean_object* v_keys_1110_, lean_object* v_vals_1111_, lean_object* v_heq_1112_, lean_object* v_i_1113_, lean_object* v_entries_1114_){
_start:
{
size_t v_depth_boxed_1115_; lean_object* v_res_1116_; 
v_depth_boxed_1115_ = lean_unbox_usize(v_depth_1109_);
lean_dec(v_depth_1109_);
v_res_1116_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__5(v_00_u03b2_1108_, v_depth_boxed_1115_, v_keys_1110_, v_vals_1111_, v_heq_1112_, v_i_1113_, v_entries_1114_);
lean_dec_ref(v_vals_1111_);
lean_dec_ref(v_keys_1110_);
return v_res_1116_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_1117_, lean_object* v_x_1118_, lean_object* v_x_1119_, lean_object* v_x_1120_, lean_object* v_x_1121_){
_start:
{
lean_object* v___x_1122_; 
v___x_1122_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__4_spec__5___redArg(v_x_1118_, v_x_1119_, v_x_1120_, v_x_1121_);
return v___x_1122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__0(lean_object* v_mvarId_1123_, lean_object* v_newEqs_1124_, uint8_t v___x_1125_, lean_object* v_h_x27_1126_, lean_object* v_newIndices_1127_, lean_object* v___x_1128_, lean_object* v___x_1129_, lean_object* v___x_1130_, lean_object* v___x_1131_, lean_object* v_e_1132_, lean_object* v___x_1133_, lean_object* v_newEq_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_){
_start:
{
lean_object* v___x_1140_; 
lean_inc(v_mvarId_1123_);
v___x_1140_ = l_Lean_MVarId_getType(v_mvarId_1123_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_);
if (lean_obj_tag(v___x_1140_) == 0)
{
lean_object* v_a_1141_; lean_object* v___x_1142_; 
v_a_1141_ = lean_ctor_get(v___x_1140_, 0);
lean_inc(v_a_1141_);
lean_dec_ref_known(v___x_1140_, 1);
lean_inc(v_mvarId_1123_);
v___x_1142_ = l_Lean_MVarId_getTag(v_mvarId_1123_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_);
if (lean_obj_tag(v___x_1142_) == 0)
{
lean_object* v_a_1143_; lean_object* v___x_1144_; uint8_t v___x_1145_; uint8_t v___x_1146_; lean_object* v___x_1147_; 
v_a_1143_ = lean_ctor_get(v___x_1142_, 0);
lean_inc(v_a_1143_);
lean_dec_ref_known(v___x_1142_, 1);
v___x_1144_ = lean_array_push(v_newEqs_1124_, v_newEq_1134_);
v___x_1145_ = 1;
v___x_1146_ = 1;
v___x_1147_ = l_Lean_Meta_mkForallFVars(v___x_1144_, v_a_1141_, v___x_1125_, v___x_1145_, v___x_1145_, v___x_1146_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_);
if (lean_obj_tag(v___x_1147_) == 0)
{
lean_object* v_a_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; 
v_a_1148_ = lean_ctor_get(v___x_1147_, 0);
lean_inc(v_a_1148_);
lean_dec_ref_known(v___x_1147_, 1);
v___x_1149_ = lean_unsigned_to_nat(1u);
v___x_1150_ = lean_mk_empty_array_with_capacity(v___x_1149_);
v___x_1151_ = lean_array_push(v___x_1150_, v_h_x27_1126_);
v___x_1152_ = l_Lean_Meta_mkForallFVars(v___x_1151_, v_a_1148_, v___x_1125_, v___x_1145_, v___x_1145_, v___x_1146_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_);
lean_dec_ref(v___x_1151_);
if (lean_obj_tag(v___x_1152_) == 0)
{
lean_object* v_a_1153_; lean_object* v___x_1154_; 
v_a_1153_ = lean_ctor_get(v___x_1152_, 0);
lean_inc(v_a_1153_);
lean_dec_ref_known(v___x_1152_, 1);
v___x_1154_ = l_Lean_Meta_mkForallFVars(v_newIndices_1127_, v_a_1153_, v___x_1125_, v___x_1145_, v___x_1145_, v___x_1146_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_);
if (lean_obj_tag(v___x_1154_) == 0)
{
lean_object* v_a_1155_; uint8_t v___x_1156_; lean_object* v___x_1157_; 
v_a_1155_ = lean_ctor_get(v___x_1154_, 0);
lean_inc(v_a_1155_);
lean_dec_ref_known(v___x_1154_, 1);
v___x_1156_ = 2;
v___x_1157_ = l_Lean_Meta_mkFreshExprMVarAt(v___x_1128_, v___x_1129_, v_a_1155_, v___x_1156_, v_a_1143_, v___x_1130_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_);
if (lean_obj_tag(v___x_1157_) == 0)
{
lean_object* v_a_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; 
v_a_1158_ = lean_ctor_get(v___x_1157_, 0);
lean_inc_n(v_a_1158_, 2);
lean_dec_ref_known(v___x_1157_, 1);
v___x_1159_ = l_Lean_mkAppN(v_a_1158_, v___x_1131_);
v___x_1160_ = l_Lean_Expr_app___override(v___x_1159_, v_e_1132_);
v___x_1161_ = l_Lean_mkAppN(v___x_1160_, v___x_1133_);
v___x_1162_ = l_Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1___redArg(v_mvarId_1123_, v___x_1161_, v___y_1136_);
lean_dec_ref(v___x_1162_);
v___x_1163_ = l_Lean_Expr_mvarId_x21(v_a_1158_);
lean_dec(v_a_1158_);
v___x_1164_ = lean_array_get_size(v_newIndices_1127_);
v___x_1165_ = lean_box(0);
v___x_1166_ = l_Lean_Meta_introNCore(v___x_1163_, v___x_1164_, v___x_1165_, v___x_1125_, v___x_1145_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_);
if (lean_obj_tag(v___x_1166_) == 0)
{
lean_object* v_a_1167_; lean_object* v_fst_1168_; lean_object* v_snd_1169_; lean_object* v___x_1170_; 
v_a_1167_ = lean_ctor_get(v___x_1166_, 0);
lean_inc(v_a_1167_);
lean_dec_ref_known(v___x_1166_, 1);
v_fst_1168_ = lean_ctor_get(v_a_1167_, 0);
lean_inc(v_fst_1168_);
v_snd_1169_ = lean_ctor_get(v_a_1167_, 1);
lean_inc(v_snd_1169_);
lean_dec(v_a_1167_);
v___x_1170_ = l_Lean_Meta_intro1Core(v_snd_1169_, v___x_1145_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_);
if (lean_obj_tag(v___x_1170_) == 0)
{
lean_object* v_a_1171_; lean_object* v___x_1173_; uint8_t v_isShared_1174_; uint8_t v_isSharedCheck_1182_; 
v_a_1171_ = lean_ctor_get(v___x_1170_, 0);
v_isSharedCheck_1182_ = !lean_is_exclusive(v___x_1170_);
if (v_isSharedCheck_1182_ == 0)
{
v___x_1173_ = v___x_1170_;
v_isShared_1174_ = v_isSharedCheck_1182_;
goto v_resetjp_1172_;
}
else
{
lean_inc(v_a_1171_);
lean_dec(v___x_1170_);
v___x_1173_ = lean_box(0);
v_isShared_1174_ = v_isSharedCheck_1182_;
goto v_resetjp_1172_;
}
v_resetjp_1172_:
{
lean_object* v_fst_1175_; lean_object* v_snd_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1180_; 
v_fst_1175_ = lean_ctor_get(v_a_1171_, 0);
lean_inc(v_fst_1175_);
v_snd_1176_ = lean_ctor_get(v_a_1171_, 1);
lean_inc(v_snd_1176_);
lean_dec(v_a_1171_);
v___x_1177_ = lean_array_get_size(v___x_1144_);
lean_dec_ref(v___x_1144_);
v___x_1178_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1178_, 0, v_snd_1176_);
lean_ctor_set(v___x_1178_, 1, v_fst_1168_);
lean_ctor_set(v___x_1178_, 2, v_fst_1175_);
lean_ctor_set(v___x_1178_, 3, v___x_1177_);
if (v_isShared_1174_ == 0)
{
lean_ctor_set(v___x_1173_, 0, v___x_1178_);
v___x_1180_ = v___x_1173_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v___x_1178_);
v___x_1180_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
return v___x_1180_;
}
}
}
else
{
lean_object* v_a_1183_; lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1190_; 
lean_dec(v_fst_1168_);
lean_dec_ref(v___x_1144_);
v_a_1183_ = lean_ctor_get(v___x_1170_, 0);
v_isSharedCheck_1190_ = !lean_is_exclusive(v___x_1170_);
if (v_isSharedCheck_1190_ == 0)
{
v___x_1185_ = v___x_1170_;
v_isShared_1186_ = v_isSharedCheck_1190_;
goto v_resetjp_1184_;
}
else
{
lean_inc(v_a_1183_);
lean_dec(v___x_1170_);
v___x_1185_ = lean_box(0);
v_isShared_1186_ = v_isSharedCheck_1190_;
goto v_resetjp_1184_;
}
v_resetjp_1184_:
{
lean_object* v___x_1188_; 
if (v_isShared_1186_ == 0)
{
v___x_1188_ = v___x_1185_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1189_; 
v_reuseFailAlloc_1189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1189_, 0, v_a_1183_);
v___x_1188_ = v_reuseFailAlloc_1189_;
goto v_reusejp_1187_;
}
v_reusejp_1187_:
{
return v___x_1188_;
}
}
}
}
else
{
lean_object* v_a_1191_; lean_object* v___x_1193_; uint8_t v_isShared_1194_; uint8_t v_isSharedCheck_1198_; 
lean_dec_ref(v___x_1144_);
v_a_1191_ = lean_ctor_get(v___x_1166_, 0);
v_isSharedCheck_1198_ = !lean_is_exclusive(v___x_1166_);
if (v_isSharedCheck_1198_ == 0)
{
v___x_1193_ = v___x_1166_;
v_isShared_1194_ = v_isSharedCheck_1198_;
goto v_resetjp_1192_;
}
else
{
lean_inc(v_a_1191_);
lean_dec(v___x_1166_);
v___x_1193_ = lean_box(0);
v_isShared_1194_ = v_isSharedCheck_1198_;
goto v_resetjp_1192_;
}
v_resetjp_1192_:
{
lean_object* v___x_1196_; 
if (v_isShared_1194_ == 0)
{
v___x_1196_ = v___x_1193_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v_a_1191_);
v___x_1196_ = v_reuseFailAlloc_1197_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
return v___x_1196_;
}
}
}
}
else
{
lean_object* v_a_1199_; lean_object* v___x_1201_; uint8_t v_isShared_1202_; uint8_t v_isSharedCheck_1206_; 
lean_dec_ref(v___x_1144_);
lean_dec_ref(v_e_1132_);
lean_dec(v_mvarId_1123_);
v_a_1199_ = lean_ctor_get(v___x_1157_, 0);
v_isSharedCheck_1206_ = !lean_is_exclusive(v___x_1157_);
if (v_isSharedCheck_1206_ == 0)
{
v___x_1201_ = v___x_1157_;
v_isShared_1202_ = v_isSharedCheck_1206_;
goto v_resetjp_1200_;
}
else
{
lean_inc(v_a_1199_);
lean_dec(v___x_1157_);
v___x_1201_ = lean_box(0);
v_isShared_1202_ = v_isSharedCheck_1206_;
goto v_resetjp_1200_;
}
v_resetjp_1200_:
{
lean_object* v___x_1204_; 
if (v_isShared_1202_ == 0)
{
v___x_1204_ = v___x_1201_;
goto v_reusejp_1203_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v_a_1199_);
v___x_1204_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1203_;
}
v_reusejp_1203_:
{
return v___x_1204_;
}
}
}
}
else
{
lean_object* v_a_1207_; lean_object* v___x_1209_; uint8_t v_isShared_1210_; uint8_t v_isSharedCheck_1214_; 
lean_dec_ref(v___x_1144_);
lean_dec(v_a_1143_);
lean_dec_ref(v_e_1132_);
lean_dec(v___x_1130_);
lean_dec_ref(v___x_1129_);
lean_dec_ref(v___x_1128_);
lean_dec(v_mvarId_1123_);
v_a_1207_ = lean_ctor_get(v___x_1154_, 0);
v_isSharedCheck_1214_ = !lean_is_exclusive(v___x_1154_);
if (v_isSharedCheck_1214_ == 0)
{
v___x_1209_ = v___x_1154_;
v_isShared_1210_ = v_isSharedCheck_1214_;
goto v_resetjp_1208_;
}
else
{
lean_inc(v_a_1207_);
lean_dec(v___x_1154_);
v___x_1209_ = lean_box(0);
v_isShared_1210_ = v_isSharedCheck_1214_;
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
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v_a_1207_);
v___x_1212_ = v_reuseFailAlloc_1213_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
return v___x_1212_;
}
}
}
}
else
{
lean_object* v_a_1215_; lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1222_; 
lean_dec_ref(v___x_1144_);
lean_dec(v_a_1143_);
lean_dec_ref(v_e_1132_);
lean_dec(v___x_1130_);
lean_dec_ref(v___x_1129_);
lean_dec_ref(v___x_1128_);
lean_dec(v_mvarId_1123_);
v_a_1215_ = lean_ctor_get(v___x_1152_, 0);
v_isSharedCheck_1222_ = !lean_is_exclusive(v___x_1152_);
if (v_isSharedCheck_1222_ == 0)
{
v___x_1217_ = v___x_1152_;
v_isShared_1218_ = v_isSharedCheck_1222_;
goto v_resetjp_1216_;
}
else
{
lean_inc(v_a_1215_);
lean_dec(v___x_1152_);
v___x_1217_ = lean_box(0);
v_isShared_1218_ = v_isSharedCheck_1222_;
goto v_resetjp_1216_;
}
v_resetjp_1216_:
{
lean_object* v___x_1220_; 
if (v_isShared_1218_ == 0)
{
v___x_1220_ = v___x_1217_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1221_; 
v_reuseFailAlloc_1221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1221_, 0, v_a_1215_);
v___x_1220_ = v_reuseFailAlloc_1221_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
return v___x_1220_;
}
}
}
}
else
{
lean_object* v_a_1223_; lean_object* v___x_1225_; uint8_t v_isShared_1226_; uint8_t v_isSharedCheck_1230_; 
lean_dec_ref(v___x_1144_);
lean_dec(v_a_1143_);
lean_dec_ref(v_e_1132_);
lean_dec(v___x_1130_);
lean_dec_ref(v___x_1129_);
lean_dec_ref(v___x_1128_);
lean_dec_ref(v_h_x27_1126_);
lean_dec(v_mvarId_1123_);
v_a_1223_ = lean_ctor_get(v___x_1147_, 0);
v_isSharedCheck_1230_ = !lean_is_exclusive(v___x_1147_);
if (v_isSharedCheck_1230_ == 0)
{
v___x_1225_ = v___x_1147_;
v_isShared_1226_ = v_isSharedCheck_1230_;
goto v_resetjp_1224_;
}
else
{
lean_inc(v_a_1223_);
lean_dec(v___x_1147_);
v___x_1225_ = lean_box(0);
v_isShared_1226_ = v_isSharedCheck_1230_;
goto v_resetjp_1224_;
}
v_resetjp_1224_:
{
lean_object* v___x_1228_; 
if (v_isShared_1226_ == 0)
{
v___x_1228_ = v___x_1225_;
goto v_reusejp_1227_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v_a_1223_);
v___x_1228_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1227_;
}
v_reusejp_1227_:
{
return v___x_1228_;
}
}
}
}
else
{
lean_object* v_a_1231_; lean_object* v___x_1233_; uint8_t v_isShared_1234_; uint8_t v_isSharedCheck_1238_; 
lean_dec(v_a_1141_);
lean_dec_ref(v_newEq_1134_);
lean_dec_ref(v_e_1132_);
lean_dec(v___x_1130_);
lean_dec_ref(v___x_1129_);
lean_dec_ref(v___x_1128_);
lean_dec_ref(v_h_x27_1126_);
lean_dec_ref(v_newEqs_1124_);
lean_dec(v_mvarId_1123_);
v_a_1231_ = lean_ctor_get(v___x_1142_, 0);
v_isSharedCheck_1238_ = !lean_is_exclusive(v___x_1142_);
if (v_isSharedCheck_1238_ == 0)
{
v___x_1233_ = v___x_1142_;
v_isShared_1234_ = v_isSharedCheck_1238_;
goto v_resetjp_1232_;
}
else
{
lean_inc(v_a_1231_);
lean_dec(v___x_1142_);
v___x_1233_ = lean_box(0);
v_isShared_1234_ = v_isSharedCheck_1238_;
goto v_resetjp_1232_;
}
v_resetjp_1232_:
{
lean_object* v___x_1236_; 
if (v_isShared_1234_ == 0)
{
v___x_1236_ = v___x_1233_;
goto v_reusejp_1235_;
}
else
{
lean_object* v_reuseFailAlloc_1237_; 
v_reuseFailAlloc_1237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1237_, 0, v_a_1231_);
v___x_1236_ = v_reuseFailAlloc_1237_;
goto v_reusejp_1235_;
}
v_reusejp_1235_:
{
return v___x_1236_;
}
}
}
}
else
{
lean_object* v_a_1239_; lean_object* v___x_1241_; uint8_t v_isShared_1242_; uint8_t v_isSharedCheck_1246_; 
lean_dec_ref(v_newEq_1134_);
lean_dec_ref(v_e_1132_);
lean_dec(v___x_1130_);
lean_dec_ref(v___x_1129_);
lean_dec_ref(v___x_1128_);
lean_dec_ref(v_h_x27_1126_);
lean_dec_ref(v_newEqs_1124_);
lean_dec(v_mvarId_1123_);
v_a_1239_ = lean_ctor_get(v___x_1140_, 0);
v_isSharedCheck_1246_ = !lean_is_exclusive(v___x_1140_);
if (v_isSharedCheck_1246_ == 0)
{
v___x_1241_ = v___x_1140_;
v_isShared_1242_ = v_isSharedCheck_1246_;
goto v_resetjp_1240_;
}
else
{
lean_inc(v_a_1239_);
lean_dec(v___x_1140_);
v___x_1241_ = lean_box(0);
v_isShared_1242_ = v_isSharedCheck_1246_;
goto v_resetjp_1240_;
}
v_resetjp_1240_:
{
lean_object* v___x_1244_; 
if (v_isShared_1242_ == 0)
{
v___x_1244_ = v___x_1241_;
goto v_reusejp_1243_;
}
else
{
lean_object* v_reuseFailAlloc_1245_; 
v_reuseFailAlloc_1245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1245_, 0, v_a_1239_);
v___x_1244_ = v_reuseFailAlloc_1245_;
goto v_reusejp_1243_;
}
v_reusejp_1243_:
{
return v___x_1244_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__0___boxed(lean_object** _args){
lean_object* v_mvarId_1247_ = _args[0];
lean_object* v_newEqs_1248_ = _args[1];
lean_object* v___x_1249_ = _args[2];
lean_object* v_h_x27_1250_ = _args[3];
lean_object* v_newIndices_1251_ = _args[4];
lean_object* v___x_1252_ = _args[5];
lean_object* v___x_1253_ = _args[6];
lean_object* v___x_1254_ = _args[7];
lean_object* v___x_1255_ = _args[8];
lean_object* v_e_1256_ = _args[9];
lean_object* v___x_1257_ = _args[10];
lean_object* v_newEq_1258_ = _args[11];
lean_object* v___y_1259_ = _args[12];
lean_object* v___y_1260_ = _args[13];
lean_object* v___y_1261_ = _args[14];
lean_object* v___y_1262_ = _args[15];
lean_object* v___y_1263_ = _args[16];
_start:
{
uint8_t v___x_6145__boxed_1264_; lean_object* v_res_1265_; 
v___x_6145__boxed_1264_ = lean_unbox(v___x_1249_);
v_res_1265_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__0(v_mvarId_1247_, v_newEqs_1248_, v___x_6145__boxed_1264_, v_h_x27_1250_, v_newIndices_1251_, v___x_1252_, v___x_1253_, v___x_1254_, v___x_1255_, v_e_1256_, v___x_1257_, v_newEq_1258_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_);
lean_dec(v___y_1262_);
lean_dec_ref(v___y_1261_);
lean_dec(v___y_1260_);
lean_dec_ref(v___y_1259_);
lean_dec_ref(v___x_1257_);
lean_dec_ref(v___x_1255_);
lean_dec_ref(v_newIndices_1251_);
return v_res_1265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__1(lean_object* v_e_1266_, lean_object* v_h_x27_1267_, lean_object* v_mvarId_1268_, uint8_t v___x_1269_, lean_object* v_newIndices_1270_, lean_object* v___x_1271_, lean_object* v___x_1272_, lean_object* v___x_1273_, lean_object* v___x_1274_, lean_object* v_newEqs_1275_, lean_object* v_newRefls_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_){
_start:
{
lean_object* v___x_1282_; 
lean_inc_ref(v_h_x27_1267_);
lean_inc_ref(v_e_1266_);
v___x_1282_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof(v_e_1266_, v_h_x27_1267_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_);
if (lean_obj_tag(v___x_1282_) == 0)
{
lean_object* v_a_1283_; lean_object* v_fst_1284_; lean_object* v_snd_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___f_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; 
v_a_1283_ = lean_ctor_get(v___x_1282_, 0);
lean_inc(v_a_1283_);
lean_dec_ref_known(v___x_1282_, 1);
v_fst_1284_ = lean_ctor_get(v_a_1283_, 0);
lean_inc(v_fst_1284_);
v_snd_1285_ = lean_ctor_get(v_a_1283_, 1);
lean_inc(v_snd_1285_);
lean_dec(v_a_1283_);
v___x_1286_ = lean_array_push(v_newRefls_1276_, v_snd_1285_);
v___x_1287_ = lean_box(v___x_1269_);
v___f_1288_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__0___boxed), 17, 11);
lean_closure_set(v___f_1288_, 0, v_mvarId_1268_);
lean_closure_set(v___f_1288_, 1, v_newEqs_1275_);
lean_closure_set(v___f_1288_, 2, v___x_1287_);
lean_closure_set(v___f_1288_, 3, v_h_x27_1267_);
lean_closure_set(v___f_1288_, 4, v_newIndices_1270_);
lean_closure_set(v___f_1288_, 5, v___x_1271_);
lean_closure_set(v___f_1288_, 6, v___x_1272_);
lean_closure_set(v___f_1288_, 7, v___x_1273_);
lean_closure_set(v___f_1288_, 8, v___x_1274_);
lean_closure_set(v___f_1288_, 9, v_e_1266_);
lean_closure_set(v___f_1288_, 10, v___x_1286_);
v___x_1289_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___redArg___closed__1));
v___x_1290_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0___redArg(v___x_1289_, v_fst_1284_, v___f_1288_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_);
return v___x_1290_;
}
else
{
lean_object* v_a_1291_; lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1298_; 
lean_dec_ref(v_newRefls_1276_);
lean_dec_ref(v_newEqs_1275_);
lean_dec_ref(v___x_1274_);
lean_dec(v___x_1273_);
lean_dec_ref(v___x_1272_);
lean_dec_ref(v___x_1271_);
lean_dec_ref(v_newIndices_1270_);
lean_dec(v_mvarId_1268_);
lean_dec_ref(v_h_x27_1267_);
lean_dec_ref(v_e_1266_);
v_a_1291_ = lean_ctor_get(v___x_1282_, 0);
v_isSharedCheck_1298_ = !lean_is_exclusive(v___x_1282_);
if (v_isSharedCheck_1298_ == 0)
{
v___x_1293_ = v___x_1282_;
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
else
{
lean_inc(v_a_1291_);
lean_dec(v___x_1282_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
lean_object* v___x_1296_; 
if (v_isShared_1294_ == 0)
{
v___x_1296_ = v___x_1293_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v_a_1291_);
v___x_1296_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1295_;
}
v_reusejp_1295_:
{
return v___x_1296_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__1___boxed(lean_object* v_e_1299_, lean_object* v_h_x27_1300_, lean_object* v_mvarId_1301_, lean_object* v___x_1302_, lean_object* v_newIndices_1303_, lean_object* v___x_1304_, lean_object* v___x_1305_, lean_object* v___x_1306_, lean_object* v___x_1307_, lean_object* v_newEqs_1308_, lean_object* v_newRefls_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_){
_start:
{
uint8_t v___x_6397__boxed_1315_; lean_object* v_res_1316_; 
v___x_6397__boxed_1315_ = lean_unbox(v___x_1302_);
v_res_1316_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__1(v_e_1299_, v_h_x27_1300_, v_mvarId_1301_, v___x_6397__boxed_1315_, v_newIndices_1303_, v___x_1304_, v___x_1305_, v___x_1306_, v___x_1307_, v_newEqs_1308_, v_newRefls_1309_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_);
lean_dec(v___y_1313_);
lean_dec_ref(v___y_1312_);
lean_dec(v___y_1311_);
lean_dec_ref(v___y_1310_);
return v_res_1316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__2(lean_object* v_e_1317_, lean_object* v_mvarId_1318_, uint8_t v___x_1319_, lean_object* v_newIndices_1320_, lean_object* v___x_1321_, lean_object* v___x_1322_, lean_object* v___x_1323_, lean_object* v___x_1324_, lean_object* v_h_x27_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_){
_start:
{
lean_object* v___x_1331_; lean_object* v___f_1332_; lean_object* v___x_1333_; 
v___x_1331_ = lean_box(v___x_1319_);
lean_inc_ref(v___x_1324_);
lean_inc_ref(v_newIndices_1320_);
v___f_1332_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__1___boxed), 16, 9);
lean_closure_set(v___f_1332_, 0, v_e_1317_);
lean_closure_set(v___f_1332_, 1, v_h_x27_1325_);
lean_closure_set(v___f_1332_, 2, v_mvarId_1318_);
lean_closure_set(v___f_1332_, 3, v___x_1331_);
lean_closure_set(v___f_1332_, 4, v_newIndices_1320_);
lean_closure_set(v___f_1332_, 5, v___x_1321_);
lean_closure_set(v___f_1332_, 6, v___x_1322_);
lean_closure_set(v___f_1332_, 7, v___x_1323_);
lean_closure_set(v___f_1332_, 8, v___x_1324_);
v___x_1333_ = l_Lean_Meta_withNewEqs___redArg(v___x_1324_, v_newIndices_1320_, v___f_1332_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_);
return v___x_1333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__2___boxed(lean_object* v_e_1334_, lean_object* v_mvarId_1335_, lean_object* v___x_1336_, lean_object* v_newIndices_1337_, lean_object* v___x_1338_, lean_object* v___x_1339_, lean_object* v___x_1340_, lean_object* v___x_1341_, lean_object* v_h_x27_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_){
_start:
{
uint8_t v___x_6462__boxed_1348_; lean_object* v_res_1349_; 
v___x_6462__boxed_1348_ = lean_unbox(v___x_1336_);
v_res_1349_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__2(v_e_1334_, v_mvarId_1335_, v___x_6462__boxed_1348_, v_newIndices_1337_, v___x_1338_, v___x_1339_, v___x_1340_, v___x_1341_, v_h_x27_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_);
lean_dec(v___y_1346_);
lean_dec_ref(v___y_1345_);
lean_dec(v___y_1344_);
lean_dec_ref(v___y_1343_);
return v_res_1349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__3(lean_object* v_e_1353_, lean_object* v_mvarId_1354_, uint8_t v___x_1355_, lean_object* v___x_1356_, lean_object* v___x_1357_, lean_object* v___x_1358_, lean_object* v___x_1359_, lean_object* v___x_1360_, lean_object* v_varName_x3f_1361_, lean_object* v_newIndices_1362_, lean_object* v_x_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_){
_start:
{
lean_object* v___x_1369_; lean_object* v___f_1370_; lean_object* v___x_1371_; 
v___x_1369_ = lean_box(v___x_1355_);
lean_inc_ref(v_newIndices_1362_);
v___f_1370_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__2___boxed), 14, 8);
lean_closure_set(v___f_1370_, 0, v_e_1353_);
lean_closure_set(v___f_1370_, 1, v_mvarId_1354_);
lean_closure_set(v___f_1370_, 2, v___x_1369_);
lean_closure_set(v___f_1370_, 3, v_newIndices_1362_);
lean_closure_set(v___f_1370_, 4, v___x_1356_);
lean_closure_set(v___f_1370_, 5, v___x_1357_);
lean_closure_set(v___f_1370_, 6, v___x_1358_);
lean_closure_set(v___f_1370_, 7, v___x_1359_);
v___x_1371_ = l_Lean_mkAppN(v___x_1360_, v_newIndices_1362_);
lean_dec_ref(v_newIndices_1362_);
if (lean_obj_tag(v_varName_x3f_1361_) == 1)
{
lean_object* v_val_1372_; lean_object* v___x_1373_; 
v_val_1372_ = lean_ctor_get(v_varName_x3f_1361_, 0);
lean_inc(v_val_1372_);
lean_dec_ref_known(v_varName_x3f_1361_, 1);
v___x_1373_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0___redArg(v_val_1372_, v___x_1371_, v___f_1370_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_);
return v___x_1373_;
}
else
{
lean_object* v___x_1374_; lean_object* v___x_1375_; 
lean_dec(v_varName_x3f_1361_);
v___x_1374_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__3___closed__1));
v___x_1375_ = l_Lean_Core_mkFreshUserName(v___x_1374_, v___y_1366_, v___y_1367_);
if (lean_obj_tag(v___x_1375_) == 0)
{
lean_object* v_a_1376_; lean_object* v___x_1377_; 
v_a_1376_ = lean_ctor_get(v___x_1375_, 0);
lean_inc(v_a_1376_);
lean_dec_ref_known(v___x_1375_, 1);
v___x_1377_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0___redArg(v_a_1376_, v___x_1371_, v___f_1370_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_);
return v___x_1377_;
}
else
{
lean_object* v_a_1378_; lean_object* v___x_1380_; uint8_t v_isShared_1381_; uint8_t v_isSharedCheck_1385_; 
lean_dec_ref(v___x_1371_);
lean_dec_ref(v___f_1370_);
v_a_1378_ = lean_ctor_get(v___x_1375_, 0);
v_isSharedCheck_1385_ = !lean_is_exclusive(v___x_1375_);
if (v_isSharedCheck_1385_ == 0)
{
v___x_1380_ = v___x_1375_;
v_isShared_1381_ = v_isSharedCheck_1385_;
goto v_resetjp_1379_;
}
else
{
lean_inc(v_a_1378_);
lean_dec(v___x_1375_);
v___x_1380_ = lean_box(0);
v_isShared_1381_ = v_isSharedCheck_1385_;
goto v_resetjp_1379_;
}
v_resetjp_1379_:
{
lean_object* v___x_1383_; 
if (v_isShared_1381_ == 0)
{
v___x_1383_ = v___x_1380_;
goto v_reusejp_1382_;
}
else
{
lean_object* v_reuseFailAlloc_1384_; 
v_reuseFailAlloc_1384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1384_, 0, v_a_1378_);
v___x_1383_ = v_reuseFailAlloc_1384_;
goto v_reusejp_1382_;
}
v_reusejp_1382_:
{
return v___x_1383_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__3___boxed(lean_object* v_e_1386_, lean_object* v_mvarId_1387_, lean_object* v___x_1388_, lean_object* v___x_1389_, lean_object* v___x_1390_, lean_object* v___x_1391_, lean_object* v___x_1392_, lean_object* v___x_1393_, lean_object* v_varName_x3f_1394_, lean_object* v_newIndices_1395_, lean_object* v_x_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_){
_start:
{
uint8_t v___x_6504__boxed_1402_; lean_object* v_res_1403_; 
v___x_6504__boxed_1402_ = lean_unbox(v___x_1388_);
v_res_1403_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__3(v_e_1386_, v_mvarId_1387_, v___x_6504__boxed_1402_, v___x_1389_, v___x_1390_, v___x_1391_, v___x_1392_, v___x_1393_, v_varName_x3f_1394_, v_newIndices_1395_, v_x_1396_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_);
lean_dec(v___y_1400_);
lean_dec_ref(v___y_1399_);
lean_dec(v___y_1398_);
lean_dec_ref(v___y_1397_);
lean_dec_ref(v_x_1396_);
return v_res_1403_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__4(void){
_start:
{
lean_object* v___x_1410_; lean_object* v___x_1411_; 
v___x_1410_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__3));
v___x_1411_ = l_Lean_MessageData_ofFormat(v___x_1410_);
return v___x_1411_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__5(void){
_start:
{
lean_object* v___x_1412_; lean_object* v___x_1413_; 
v___x_1412_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__4, &l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__4_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__4);
v___x_1413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1413_, 0, v___x_1412_);
return v___x_1413_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__8(void){
_start:
{
lean_object* v___x_1417_; lean_object* v___x_1418_; 
v___x_1417_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__7));
v___x_1418_ = l_Lean_MessageData_ofFormat(v___x_1417_);
return v___x_1418_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__9(void){
_start:
{
lean_object* v___x_1419_; lean_object* v___x_1420_; 
v___x_1419_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__8, &l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__8_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__8);
v___x_1420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1420_, 0, v___x_1419_);
return v___x_1420_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__12(void){
_start:
{
lean_object* v___x_1424_; lean_object* v___x_1425_; 
v___x_1424_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__11));
v___x_1425_ = l_Lean_MessageData_ofFormat(v___x_1424_);
return v___x_1425_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__13(void){
_start:
{
lean_object* v___x_1426_; lean_object* v___x_1427_; 
v___x_1426_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__12, &l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__12_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__12);
v___x_1427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1427_, 0, v___x_1426_);
return v___x_1427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0(lean_object* v_mvarId_1428_, lean_object* v_e_1429_, lean_object* v___x_1430_, lean_object* v___x_1431_, lean_object* v_varName_x3f_1432_, lean_object* v_x_1433_, lean_object* v_x_1434_, lean_object* v_x_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_){
_start:
{
if (lean_obj_tag(v_x_1433_) == 5)
{
lean_object* v_fn_1441_; lean_object* v_arg_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; 
v_fn_1441_ = lean_ctor_get(v_x_1433_, 0);
lean_inc_ref(v_fn_1441_);
v_arg_1442_ = lean_ctor_get(v_x_1433_, 1);
lean_inc_ref(v_arg_1442_);
lean_dec_ref_known(v_x_1433_, 2);
v___x_1443_ = lean_array_set(v_x_1434_, v_x_1435_, v_arg_1442_);
v___x_1444_ = lean_unsigned_to_nat(1u);
v___x_1445_ = lean_nat_sub(v_x_1435_, v___x_1444_);
lean_dec(v_x_1435_);
v_x_1433_ = v_fn_1441_;
v_x_1434_ = v___x_1443_;
v_x_1435_ = v___x_1445_;
goto _start;
}
else
{
lean_object* v___x_1447_; lean_object* v___y_1449_; lean_object* v___y_1450_; lean_object* v___y_1451_; lean_object* v___y_1452_; 
lean_dec(v_x_1435_);
v___x_1447_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__1));
if (lean_obj_tag(v_x_1433_) == 4)
{
lean_object* v_declName_1455_; lean_object* v___x_1456_; lean_object* v_env_1457_; uint8_t v___x_1458_; lean_object* v___x_1459_; 
v_declName_1455_ = lean_ctor_get(v_x_1433_, 0);
v___x_1456_ = lean_st_ref_get(v___y_1439_);
v_env_1457_ = lean_ctor_get(v___x_1456_, 0);
lean_inc_ref(v_env_1457_);
lean_dec(v___x_1456_);
v___x_1458_ = 0;
lean_inc(v_declName_1455_);
v___x_1459_ = l_Lean_Environment_find_x3f(v_env_1457_, v_declName_1455_, v___x_1458_);
if (lean_obj_tag(v___x_1459_) == 0)
{
lean_dec_ref_known(v_x_1433_, 2);
lean_dec_ref(v_x_1434_);
lean_dec(v_varName_x3f_1432_);
lean_dec_ref(v___x_1431_);
lean_dec_ref(v___x_1430_);
lean_dec_ref(v_e_1429_);
v___y_1449_ = v___y_1436_;
v___y_1450_ = v___y_1437_;
v___y_1451_ = v___y_1438_;
v___y_1452_ = v___y_1439_;
goto v___jp_1448_;
}
else
{
lean_object* v_val_1460_; 
v_val_1460_ = lean_ctor_get(v___x_1459_, 0);
lean_inc(v_val_1460_);
lean_dec_ref_known(v___x_1459_, 1);
if (lean_obj_tag(v_val_1460_) == 5)
{
lean_object* v_val_1461_; lean_object* v_numParams_1462_; lean_object* v_numIndices_1463_; lean_object* v___y_1465_; lean_object* v___y_1466_; lean_object* v___y_1467_; lean_object* v___y_1468_; lean_object* v___y_1489_; lean_object* v___y_1490_; lean_object* v___y_1491_; lean_object* v___y_1492_; lean_object* v___x_1506_; uint8_t v___x_1507_; 
v_val_1461_ = lean_ctor_get(v_val_1460_, 0);
lean_inc_ref(v_val_1461_);
lean_dec_ref_known(v_val_1460_, 1);
v_numParams_1462_ = lean_ctor_get(v_val_1461_, 1);
lean_inc(v_numParams_1462_);
v_numIndices_1463_ = lean_ctor_get(v_val_1461_, 2);
lean_inc(v_numIndices_1463_);
lean_dec_ref(v_val_1461_);
v___x_1506_ = lean_unsigned_to_nat(0u);
v___x_1507_ = lean_nat_dec_lt(v___x_1506_, v_numIndices_1463_);
if (v___x_1507_ == 0)
{
lean_object* v___x_1508_; lean_object* v___x_1509_; 
v___x_1508_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__13, &l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__13_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__13);
lean_inc(v_mvarId_1428_);
v___x_1509_ = l_Lean_Meta_throwTacticEx___redArg(v___x_1447_, v_mvarId_1428_, v___x_1508_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_);
if (lean_obj_tag(v___x_1509_) == 0)
{
lean_dec_ref_known(v___x_1509_, 1);
v___y_1489_ = v___y_1436_;
v___y_1490_ = v___y_1437_;
v___y_1491_ = v___y_1438_;
v___y_1492_ = v___y_1439_;
goto v___jp_1488_;
}
else
{
lean_object* v_a_1510_; lean_object* v___x_1512_; uint8_t v_isShared_1513_; uint8_t v_isSharedCheck_1517_; 
lean_dec(v_numIndices_1463_);
lean_dec(v_numParams_1462_);
lean_dec_ref_known(v_x_1433_, 2);
lean_dec_ref(v_x_1434_);
lean_dec(v_varName_x3f_1432_);
lean_dec_ref(v___x_1431_);
lean_dec_ref(v___x_1430_);
lean_dec_ref(v_e_1429_);
lean_dec(v_mvarId_1428_);
v_a_1510_ = lean_ctor_get(v___x_1509_, 0);
v_isSharedCheck_1517_ = !lean_is_exclusive(v___x_1509_);
if (v_isSharedCheck_1517_ == 0)
{
v___x_1512_ = v___x_1509_;
v_isShared_1513_ = v_isSharedCheck_1517_;
goto v_resetjp_1511_;
}
else
{
lean_inc(v_a_1510_);
lean_dec(v___x_1509_);
v___x_1512_ = lean_box(0);
v_isShared_1513_ = v_isSharedCheck_1517_;
goto v_resetjp_1511_;
}
v_resetjp_1511_:
{
lean_object* v___x_1515_; 
if (v_isShared_1513_ == 0)
{
v___x_1515_ = v___x_1512_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v_a_1510_);
v___x_1515_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
return v___x_1515_;
}
}
}
}
else
{
v___y_1489_ = v___y_1436_;
v___y_1490_ = v___y_1437_;
v___y_1491_ = v___y_1438_;
v___y_1492_ = v___y_1439_;
goto v___jp_1488_;
}
v___jp_1464_:
{
lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; 
v___x_1469_ = lean_unsigned_to_nat(0u);
v___x_1470_ = l_Array_extract___redArg(v_x_1434_, v___x_1469_, v_numParams_1462_);
v___x_1471_ = l_Lean_mkAppN(v_x_1433_, v___x_1470_);
lean_dec_ref(v___x_1470_);
lean_inc(v___y_1468_);
lean_inc_ref(v___y_1467_);
lean_inc(v___y_1466_);
lean_inc_ref(v___y_1465_);
lean_inc_ref(v___x_1471_);
v___x_1472_ = lean_infer_type(v___x_1471_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_);
if (lean_obj_tag(v___x_1472_) == 0)
{
lean_object* v_a_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___f_1478_; lean_object* v___x_1479_; 
v_a_1473_ = lean_ctor_get(v___x_1472_, 0);
lean_inc(v_a_1473_);
lean_dec_ref_known(v___x_1472_, 1);
v___x_1474_ = lean_array_get_size(v_x_1434_);
v___x_1475_ = lean_nat_sub(v___x_1474_, v_numIndices_1463_);
lean_dec(v_numIndices_1463_);
v___x_1476_ = l_Array_extract___redArg(v_x_1434_, v___x_1475_, v___x_1474_);
lean_dec_ref(v_x_1434_);
v___x_1477_ = lean_box(v___x_1458_);
v___f_1478_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__3___boxed), 16, 9);
lean_closure_set(v___f_1478_, 0, v_e_1429_);
lean_closure_set(v___f_1478_, 1, v_mvarId_1428_);
lean_closure_set(v___f_1478_, 2, v___x_1477_);
lean_closure_set(v___f_1478_, 3, v___x_1430_);
lean_closure_set(v___f_1478_, 4, v___x_1431_);
lean_closure_set(v___f_1478_, 5, v___x_1469_);
lean_closure_set(v___f_1478_, 6, v___x_1476_);
lean_closure_set(v___f_1478_, 7, v___x_1471_);
lean_closure_set(v___f_1478_, 8, v_varName_x3f_1432_);
v___x_1479_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_generalizeTargetsEq_spec__0___redArg(v_a_1473_, v___f_1478_, v___x_1458_, v___x_1458_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_);
return v___x_1479_;
}
else
{
lean_object* v_a_1480_; lean_object* v___x_1482_; uint8_t v_isShared_1483_; uint8_t v_isSharedCheck_1487_; 
lean_dec_ref(v___x_1471_);
lean_dec(v_numIndices_1463_);
lean_dec_ref(v_x_1434_);
lean_dec(v_varName_x3f_1432_);
lean_dec_ref(v___x_1431_);
lean_dec_ref(v___x_1430_);
lean_dec_ref(v_e_1429_);
lean_dec(v_mvarId_1428_);
v_a_1480_ = lean_ctor_get(v___x_1472_, 0);
v_isSharedCheck_1487_ = !lean_is_exclusive(v___x_1472_);
if (v_isSharedCheck_1487_ == 0)
{
v___x_1482_ = v___x_1472_;
v_isShared_1483_ = v_isSharedCheck_1487_;
goto v_resetjp_1481_;
}
else
{
lean_inc(v_a_1480_);
lean_dec(v___x_1472_);
v___x_1482_ = lean_box(0);
v_isShared_1483_ = v_isSharedCheck_1487_;
goto v_resetjp_1481_;
}
v_resetjp_1481_:
{
lean_object* v___x_1485_; 
if (v_isShared_1483_ == 0)
{
v___x_1485_ = v___x_1482_;
goto v_reusejp_1484_;
}
else
{
lean_object* v_reuseFailAlloc_1486_; 
v_reuseFailAlloc_1486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1486_, 0, v_a_1480_);
v___x_1485_ = v_reuseFailAlloc_1486_;
goto v_reusejp_1484_;
}
v_reusejp_1484_:
{
return v___x_1485_;
}
}
}
}
v___jp_1488_:
{
lean_object* v___x_1493_; lean_object* v___x_1494_; uint8_t v___x_1495_; 
v___x_1493_ = lean_array_get_size(v_x_1434_);
v___x_1494_ = lean_nat_add(v_numIndices_1463_, v_numParams_1462_);
v___x_1495_ = lean_nat_dec_eq(v___x_1493_, v___x_1494_);
lean_dec(v___x_1494_);
if (v___x_1495_ == 0)
{
lean_object* v___x_1496_; lean_object* v___x_1497_; 
v___x_1496_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__9, &l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__9_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__9);
lean_inc(v_mvarId_1428_);
v___x_1497_ = l_Lean_Meta_throwTacticEx___redArg(v___x_1447_, v_mvarId_1428_, v___x_1496_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_);
if (lean_obj_tag(v___x_1497_) == 0)
{
lean_dec_ref_known(v___x_1497_, 1);
v___y_1465_ = v___y_1489_;
v___y_1466_ = v___y_1490_;
v___y_1467_ = v___y_1491_;
v___y_1468_ = v___y_1492_;
goto v___jp_1464_;
}
else
{
lean_object* v_a_1498_; lean_object* v___x_1500_; uint8_t v_isShared_1501_; uint8_t v_isSharedCheck_1505_; 
lean_dec(v_numIndices_1463_);
lean_dec(v_numParams_1462_);
lean_dec_ref_known(v_x_1433_, 2);
lean_dec_ref(v_x_1434_);
lean_dec(v_varName_x3f_1432_);
lean_dec_ref(v___x_1431_);
lean_dec_ref(v___x_1430_);
lean_dec_ref(v_e_1429_);
lean_dec(v_mvarId_1428_);
v_a_1498_ = lean_ctor_get(v___x_1497_, 0);
v_isSharedCheck_1505_ = !lean_is_exclusive(v___x_1497_);
if (v_isSharedCheck_1505_ == 0)
{
v___x_1500_ = v___x_1497_;
v_isShared_1501_ = v_isSharedCheck_1505_;
goto v_resetjp_1499_;
}
else
{
lean_inc(v_a_1498_);
lean_dec(v___x_1497_);
v___x_1500_ = lean_box(0);
v_isShared_1501_ = v_isSharedCheck_1505_;
goto v_resetjp_1499_;
}
v_resetjp_1499_:
{
lean_object* v___x_1503_; 
if (v_isShared_1501_ == 0)
{
v___x_1503_ = v___x_1500_;
goto v_reusejp_1502_;
}
else
{
lean_object* v_reuseFailAlloc_1504_; 
v_reuseFailAlloc_1504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1504_, 0, v_a_1498_);
v___x_1503_ = v_reuseFailAlloc_1504_;
goto v_reusejp_1502_;
}
v_reusejp_1502_:
{
return v___x_1503_;
}
}
}
}
else
{
v___y_1465_ = v___y_1489_;
v___y_1466_ = v___y_1490_;
v___y_1467_ = v___y_1491_;
v___y_1468_ = v___y_1492_;
goto v___jp_1464_;
}
}
}
else
{
lean_dec(v_val_1460_);
lean_dec_ref_known(v_x_1433_, 2);
lean_dec_ref(v_x_1434_);
lean_dec(v_varName_x3f_1432_);
lean_dec_ref(v___x_1431_);
lean_dec_ref(v___x_1430_);
lean_dec_ref(v_e_1429_);
v___y_1449_ = v___y_1436_;
v___y_1450_ = v___y_1437_;
v___y_1451_ = v___y_1438_;
v___y_1452_ = v___y_1439_;
goto v___jp_1448_;
}
}
}
else
{
lean_dec_ref(v_x_1434_);
lean_dec_ref(v_x_1433_);
lean_dec(v_varName_x3f_1432_);
lean_dec_ref(v___x_1431_);
lean_dec_ref(v___x_1430_);
lean_dec_ref(v_e_1429_);
v___y_1449_ = v___y_1436_;
v___y_1450_ = v___y_1437_;
v___y_1451_ = v___y_1438_;
v___y_1452_ = v___y_1439_;
goto v___jp_1448_;
}
v___jp_1448_:
{
lean_object* v___x_1453_; lean_object* v___x_1454_; 
v___x_1453_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__5, &l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__5_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__5);
v___x_1454_ = l_Lean_Meta_throwTacticEx___redArg(v___x_1447_, v_mvarId_1428_, v___x_1453_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_);
return v___x_1454_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___boxed(lean_object* v_mvarId_1518_, lean_object* v_e_1519_, lean_object* v___x_1520_, lean_object* v___x_1521_, lean_object* v_varName_x3f_1522_, lean_object* v_x_1523_, lean_object* v_x_1524_, lean_object* v_x_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_){
_start:
{
lean_object* v_res_1531_; 
v_res_1531_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0(v_mvarId_1518_, v_e_1519_, v___x_1520_, v___x_1521_, v_varName_x3f_1522_, v_x_1523_, v_x_1524_, v_x_1525_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_);
lean_dec(v___y_1529_);
lean_dec_ref(v___y_1528_);
lean_dec(v___y_1527_);
lean_dec_ref(v___y_1526_);
return v_res_1531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeIndices_x27___lam__0(lean_object* v_mvarId_1532_, lean_object* v_e_1533_, lean_object* v_varName_x3f_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_){
_start:
{
lean_object* v___x_1540_; lean_object* v___x_1541_; 
v___x_1540_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__1));
lean_inc(v_mvarId_1532_);
v___x_1541_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_1532_, v___x_1540_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_);
if (lean_obj_tag(v___x_1541_) == 0)
{
lean_object* v_lctx_1542_; lean_object* v_localInstances_1543_; lean_object* v___x_1544_; 
lean_dec_ref_known(v___x_1541_, 1);
v_lctx_1542_ = lean_ctor_get(v___y_1535_, 2);
lean_inc_ref(v_lctx_1542_);
v_localInstances_1543_ = lean_ctor_get(v___y_1535_, 3);
lean_inc_ref(v_localInstances_1543_);
lean_inc(v___y_1538_);
lean_inc_ref(v___y_1537_);
lean_inc(v___y_1536_);
lean_inc_ref(v___y_1535_);
lean_inc_ref(v_e_1533_);
v___x_1544_ = lean_infer_type(v_e_1533_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_);
if (lean_obj_tag(v___x_1544_) == 0)
{
lean_object* v_a_1545_; lean_object* v___x_1546_; 
v_a_1545_ = lean_ctor_get(v___x_1544_, 0);
lean_inc(v_a_1545_);
lean_dec_ref_known(v___x_1544_, 1);
v___x_1546_ = l_Lean_Meta_whnfD(v_a_1545_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_);
if (lean_obj_tag(v___x_1546_) == 0)
{
lean_object* v_a_1547_; lean_object* v_dummy_1548_; lean_object* v_nargs_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; 
v_a_1547_ = lean_ctor_get(v___x_1546_, 0);
lean_inc(v_a_1547_);
lean_dec_ref_known(v___x_1546_, 1);
v_dummy_1548_ = lean_obj_once(&l_Lean_Meta_getInductiveUniverseAndParams___closed__0, &l_Lean_Meta_getInductiveUniverseAndParams___closed__0_once, _init_l_Lean_Meta_getInductiveUniverseAndParams___closed__0);
v_nargs_1549_ = l_Lean_Expr_getAppNumArgs(v_a_1547_);
lean_inc(v_nargs_1549_);
v___x_1550_ = lean_mk_array(v_nargs_1549_, v_dummy_1548_);
v___x_1551_ = lean_unsigned_to_nat(1u);
v___x_1552_ = lean_nat_sub(v_nargs_1549_, v___x_1551_);
lean_dec(v_nargs_1549_);
v___x_1553_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0(v_mvarId_1532_, v_e_1533_, v_lctx_1542_, v_localInstances_1543_, v_varName_x3f_1534_, v_a_1547_, v___x_1550_, v___x_1552_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_);
lean_dec(v___y_1538_);
lean_dec_ref(v___y_1537_);
lean_dec(v___y_1536_);
lean_dec_ref(v___y_1535_);
return v___x_1553_;
}
else
{
lean_object* v_a_1554_; lean_object* v___x_1556_; uint8_t v_isShared_1557_; uint8_t v_isSharedCheck_1561_; 
lean_dec_ref(v_localInstances_1543_);
lean_dec_ref(v_lctx_1542_);
lean_dec(v___y_1538_);
lean_dec_ref(v___y_1537_);
lean_dec(v___y_1536_);
lean_dec_ref(v___y_1535_);
lean_dec(v_varName_x3f_1534_);
lean_dec_ref(v_e_1533_);
lean_dec(v_mvarId_1532_);
v_a_1554_ = lean_ctor_get(v___x_1546_, 0);
v_isSharedCheck_1561_ = !lean_is_exclusive(v___x_1546_);
if (v_isSharedCheck_1561_ == 0)
{
v___x_1556_ = v___x_1546_;
v_isShared_1557_ = v_isSharedCheck_1561_;
goto v_resetjp_1555_;
}
else
{
lean_inc(v_a_1554_);
lean_dec(v___x_1546_);
v___x_1556_ = lean_box(0);
v_isShared_1557_ = v_isSharedCheck_1561_;
goto v_resetjp_1555_;
}
v_resetjp_1555_:
{
lean_object* v___x_1559_; 
if (v_isShared_1557_ == 0)
{
v___x_1559_ = v___x_1556_;
goto v_reusejp_1558_;
}
else
{
lean_object* v_reuseFailAlloc_1560_; 
v_reuseFailAlloc_1560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1560_, 0, v_a_1554_);
v___x_1559_ = v_reuseFailAlloc_1560_;
goto v_reusejp_1558_;
}
v_reusejp_1558_:
{
return v___x_1559_;
}
}
}
}
else
{
lean_object* v_a_1562_; lean_object* v___x_1564_; uint8_t v_isShared_1565_; uint8_t v_isSharedCheck_1569_; 
lean_dec_ref(v_localInstances_1543_);
lean_dec_ref(v_lctx_1542_);
lean_dec(v___y_1538_);
lean_dec_ref(v___y_1537_);
lean_dec(v___y_1536_);
lean_dec_ref(v___y_1535_);
lean_dec(v_varName_x3f_1534_);
lean_dec_ref(v_e_1533_);
lean_dec(v_mvarId_1532_);
v_a_1562_ = lean_ctor_get(v___x_1544_, 0);
v_isSharedCheck_1569_ = !lean_is_exclusive(v___x_1544_);
if (v_isSharedCheck_1569_ == 0)
{
v___x_1564_ = v___x_1544_;
v_isShared_1565_ = v_isSharedCheck_1569_;
goto v_resetjp_1563_;
}
else
{
lean_inc(v_a_1562_);
lean_dec(v___x_1544_);
v___x_1564_ = lean_box(0);
v_isShared_1565_ = v_isSharedCheck_1569_;
goto v_resetjp_1563_;
}
v_resetjp_1563_:
{
lean_object* v___x_1567_; 
if (v_isShared_1565_ == 0)
{
v___x_1567_ = v___x_1564_;
goto v_reusejp_1566_;
}
else
{
lean_object* v_reuseFailAlloc_1568_; 
v_reuseFailAlloc_1568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1568_, 0, v_a_1562_);
v___x_1567_ = v_reuseFailAlloc_1568_;
goto v_reusejp_1566_;
}
v_reusejp_1566_:
{
return v___x_1567_;
}
}
}
}
else
{
lean_object* v_a_1570_; lean_object* v___x_1572_; uint8_t v_isShared_1573_; uint8_t v_isSharedCheck_1577_; 
lean_dec(v___y_1538_);
lean_dec_ref(v___y_1537_);
lean_dec(v___y_1536_);
lean_dec_ref(v___y_1535_);
lean_dec(v_varName_x3f_1534_);
lean_dec_ref(v_e_1533_);
lean_dec(v_mvarId_1532_);
v_a_1570_ = lean_ctor_get(v___x_1541_, 0);
v_isSharedCheck_1577_ = !lean_is_exclusive(v___x_1541_);
if (v_isSharedCheck_1577_ == 0)
{
v___x_1572_ = v___x_1541_;
v_isShared_1573_ = v_isSharedCheck_1577_;
goto v_resetjp_1571_;
}
else
{
lean_inc(v_a_1570_);
lean_dec(v___x_1541_);
v___x_1572_ = lean_box(0);
v_isShared_1573_ = v_isSharedCheck_1577_;
goto v_resetjp_1571_;
}
v_resetjp_1571_:
{
lean_object* v___x_1575_; 
if (v_isShared_1573_ == 0)
{
v___x_1575_ = v___x_1572_;
goto v_reusejp_1574_;
}
else
{
lean_object* v_reuseFailAlloc_1576_; 
v_reuseFailAlloc_1576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1576_, 0, v_a_1570_);
v___x_1575_ = v_reuseFailAlloc_1576_;
goto v_reusejp_1574_;
}
v_reusejp_1574_:
{
return v___x_1575_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeIndices_x27___lam__0___boxed(lean_object* v_mvarId_1578_, lean_object* v_e_1579_, lean_object* v_varName_x3f_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_){
_start:
{
lean_object* v_res_1586_; 
v_res_1586_ = l_Lean_Meta_generalizeIndices_x27___lam__0(v_mvarId_1578_, v_e_1579_, v_varName_x3f_1580_, v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_);
return v_res_1586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeIndices_x27(lean_object* v_mvarId_1587_, lean_object* v_e_1588_, lean_object* v_varName_x3f_1589_, lean_object* v_a_1590_, lean_object* v_a_1591_, lean_object* v_a_1592_, lean_object* v_a_1593_){
_start:
{
lean_object* v___f_1595_; lean_object* v___x_1596_; 
lean_inc(v_mvarId_1587_);
v___f_1595_ = lean_alloc_closure((void*)(l_Lean_Meta_generalizeIndices_x27___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1595_, 0, v_mvarId_1587_);
lean_closure_set(v___f_1595_, 1, v_e_1588_);
lean_closure_set(v___f_1595_, 2, v_varName_x3f_1589_);
v___x_1596_ = l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2___redArg(v_mvarId_1587_, v___f_1595_, v_a_1590_, v_a_1591_, v_a_1592_, v_a_1593_);
return v___x_1596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeIndices_x27___boxed(lean_object* v_mvarId_1597_, lean_object* v_e_1598_, lean_object* v_varName_x3f_1599_, lean_object* v_a_1600_, lean_object* v_a_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_){
_start:
{
lean_object* v_res_1605_; 
v_res_1605_ = l_Lean_Meta_generalizeIndices_x27(v_mvarId_1597_, v_e_1598_, v_varName_x3f_1599_, v_a_1600_, v_a_1601_, v_a_1602_, v_a_1603_);
lean_dec(v_a_1603_);
lean_dec_ref(v_a_1602_);
lean_dec(v_a_1601_);
lean_dec_ref(v_a_1600_);
return v_res_1605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeIndices___lam__0(lean_object* v_fvarId_1606_, lean_object* v_mvarId_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_){
_start:
{
lean_object* v___x_1613_; 
v___x_1613_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_1606_, v___y_1608_, v___y_1610_, v___y_1611_);
if (lean_obj_tag(v___x_1613_) == 0)
{
lean_object* v_a_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; 
v_a_1614_ = lean_ctor_get(v___x_1613_, 0);
lean_inc_n(v_a_1614_, 2);
lean_dec_ref_known(v___x_1613_, 1);
v___x_1615_ = l_Lean_LocalDecl_toExpr(v_a_1614_);
v___x_1616_ = l_Lean_LocalDecl_userName(v_a_1614_);
lean_dec(v_a_1614_);
v___x_1617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1617_, 0, v___x_1616_);
v___x_1618_ = l_Lean_Meta_generalizeIndices_x27(v_mvarId_1607_, v___x_1615_, v___x_1617_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_);
return v___x_1618_;
}
else
{
lean_object* v_a_1619_; lean_object* v___x_1621_; uint8_t v_isShared_1622_; uint8_t v_isSharedCheck_1626_; 
lean_dec(v_mvarId_1607_);
v_a_1619_ = lean_ctor_get(v___x_1613_, 0);
v_isSharedCheck_1626_ = !lean_is_exclusive(v___x_1613_);
if (v_isSharedCheck_1626_ == 0)
{
v___x_1621_ = v___x_1613_;
v_isShared_1622_ = v_isSharedCheck_1626_;
goto v_resetjp_1620_;
}
else
{
lean_inc(v_a_1619_);
lean_dec(v___x_1613_);
v___x_1621_ = lean_box(0);
v_isShared_1622_ = v_isSharedCheck_1626_;
goto v_resetjp_1620_;
}
v_resetjp_1620_:
{
lean_object* v___x_1624_; 
if (v_isShared_1622_ == 0)
{
v___x_1624_ = v___x_1621_;
goto v_reusejp_1623_;
}
else
{
lean_object* v_reuseFailAlloc_1625_; 
v_reuseFailAlloc_1625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1625_, 0, v_a_1619_);
v___x_1624_ = v_reuseFailAlloc_1625_;
goto v_reusejp_1623_;
}
v_reusejp_1623_:
{
return v___x_1624_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeIndices___lam__0___boxed(lean_object* v_fvarId_1627_, lean_object* v_mvarId_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_){
_start:
{
lean_object* v_res_1634_; 
v_res_1634_ = l_Lean_Meta_generalizeIndices___lam__0(v_fvarId_1627_, v_mvarId_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_);
lean_dec(v___y_1632_);
lean_dec_ref(v___y_1631_);
lean_dec(v___y_1630_);
lean_dec_ref(v___y_1629_);
return v_res_1634_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeIndices(lean_object* v_mvarId_1635_, lean_object* v_fvarId_1636_, lean_object* v_a_1637_, lean_object* v_a_1638_, lean_object* v_a_1639_, lean_object* v_a_1640_){
_start:
{
lean_object* v___f_1642_; lean_object* v___x_1643_; 
lean_inc(v_mvarId_1635_);
v___f_1642_ = lean_alloc_closure((void*)(l_Lean_Meta_generalizeIndices___lam__0___boxed), 7, 2);
lean_closure_set(v___f_1642_, 0, v_fvarId_1636_);
lean_closure_set(v___f_1642_, 1, v_mvarId_1635_);
v___x_1643_ = l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2___redArg(v_mvarId_1635_, v___f_1642_, v_a_1637_, v_a_1638_, v_a_1639_, v_a_1640_);
return v___x_1643_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeIndices___boxed(lean_object* v_mvarId_1644_, lean_object* v_fvarId_1645_, lean_object* v_a_1646_, lean_object* v_a_1647_, lean_object* v_a_1648_, lean_object* v_a_1649_, lean_object* v_a_1650_){
_start:
{
lean_object* v_res_1651_; 
v_res_1651_ = l_Lean_Meta_generalizeIndices(v_mvarId_1644_, v_fvarId_1645_, v_a_1646_, v_a_1647_, v_a_1648_, v_a_1649_);
lean_dec(v_a_1649_);
lean_dec_ref(v_a_1648_);
lean_dec(v_a_1647_);
lean_dec_ref(v_a_1646_);
return v_res_1651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0___redArg(lean_object* v___x_1653_, lean_object* v_a_1654_, lean_object* v_x_1655_, lean_object* v_x_1656_, lean_object* v_x_1657_, lean_object* v___y_1658_){
_start:
{
if (lean_obj_tag(v_x_1655_) == 5)
{
lean_object* v_fn_1663_; lean_object* v_arg_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; 
v_fn_1663_ = lean_ctor_get(v_x_1655_, 0);
lean_inc_ref(v_fn_1663_);
v_arg_1664_ = lean_ctor_get(v_x_1655_, 1);
lean_inc_ref(v_arg_1664_);
lean_dec_ref_known(v_x_1655_, 2);
v___x_1665_ = lean_array_set(v_x_1656_, v_x_1657_, v_arg_1664_);
v___x_1666_ = lean_unsigned_to_nat(1u);
v___x_1667_ = lean_nat_sub(v_x_1657_, v___x_1666_);
lean_dec(v_x_1657_);
v_x_1655_ = v_fn_1663_;
v_x_1656_ = v___x_1665_;
v_x_1657_ = v___x_1667_;
goto _start;
}
else
{
lean_dec(v_x_1657_);
if (lean_obj_tag(v_x_1655_) == 4)
{
lean_object* v_declName_1669_; lean_object* v___x_1670_; lean_object* v_env_1671_; uint8_t v___x_1672_; lean_object* v___x_1673_; 
v_declName_1669_ = lean_ctor_get(v_x_1655_, 0);
v___x_1670_ = lean_st_ref_get(v___y_1658_);
v_env_1671_ = lean_ctor_get(v___x_1670_, 0);
lean_inc_ref(v_env_1671_);
lean_dec(v___x_1670_);
v___x_1672_ = 0;
lean_inc(v_declName_1669_);
v___x_1673_ = l_Lean_Environment_find_x3f(v_env_1671_, v_declName_1669_, v___x_1672_);
if (lean_obj_tag(v___x_1673_) == 0)
{
lean_dec_ref_known(v_x_1655_, 2);
lean_dec_ref(v_x_1656_);
lean_dec_ref(v_a_1654_);
lean_dec_ref(v___x_1653_);
goto v___jp_1660_;
}
else
{
lean_object* v_val_1674_; lean_object* v___x_1676_; uint8_t v_isShared_1677_; uint8_t v_isSharedCheck_1712_; 
v_val_1674_ = lean_ctor_get(v___x_1673_, 0);
v_isSharedCheck_1712_ = !lean_is_exclusive(v___x_1673_);
if (v_isSharedCheck_1712_ == 0)
{
v___x_1676_ = v___x_1673_;
v_isShared_1677_ = v_isSharedCheck_1712_;
goto v_resetjp_1675_;
}
else
{
lean_inc(v_val_1674_);
lean_dec(v___x_1673_);
v___x_1676_ = lean_box(0);
v_isShared_1677_ = v_isSharedCheck_1712_;
goto v_resetjp_1675_;
}
v_resetjp_1675_:
{
if (lean_obj_tag(v_val_1674_) == 5)
{
lean_object* v_val_1678_; lean_object* v___x_1680_; uint8_t v_isShared_1681_; uint8_t v_isSharedCheck_1711_; 
v_val_1678_ = lean_ctor_get(v_val_1674_, 0);
v_isSharedCheck_1711_ = !lean_is_exclusive(v_val_1674_);
if (v_isSharedCheck_1711_ == 0)
{
v___x_1680_ = v_val_1674_;
v_isShared_1681_ = v_isSharedCheck_1711_;
goto v_resetjp_1679_;
}
else
{
lean_inc(v_val_1678_);
lean_dec(v_val_1674_);
v___x_1680_ = lean_box(0);
v_isShared_1681_ = v_isSharedCheck_1711_;
goto v_resetjp_1679_;
}
v_resetjp_1679_:
{
lean_object* v_toConstantVal_1682_; lean_object* v_numParams_1683_; lean_object* v_numIndices_1684_; lean_object* v_ctors_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; uint8_t v___x_1688_; 
v_toConstantVal_1682_ = lean_ctor_get(v_val_1678_, 0);
v_numParams_1683_ = lean_ctor_get(v_val_1678_, 1);
v_numIndices_1684_ = lean_ctor_get(v_val_1678_, 2);
v_ctors_1685_ = lean_ctor_get(v_val_1678_, 4);
v___x_1686_ = lean_array_get_size(v_x_1656_);
v___x_1687_ = lean_nat_add(v_numIndices_1684_, v_numParams_1683_);
v___x_1688_ = lean_nat_dec_eq(v___x_1686_, v___x_1687_);
lean_dec(v___x_1687_);
if (v___x_1688_ == 0)
{
lean_object* v___x_1689_; lean_object* v___x_1691_; 
lean_dec_ref(v_val_1678_);
lean_del_object(v___x_1676_);
lean_dec_ref_known(v_x_1655_, 2);
lean_dec_ref(v_x_1656_);
lean_dec_ref(v_a_1654_);
lean_dec_ref(v___x_1653_);
v___x_1689_ = lean_box(0);
if (v_isShared_1681_ == 0)
{
lean_ctor_set_tag(v___x_1680_, 0);
lean_ctor_set(v___x_1680_, 0, v___x_1689_);
v___x_1691_ = v___x_1680_;
goto v_reusejp_1690_;
}
else
{
lean_object* v_reuseFailAlloc_1692_; 
v_reuseFailAlloc_1692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1692_, 0, v___x_1689_);
v___x_1691_ = v_reuseFailAlloc_1692_;
goto v_reusejp_1690_;
}
v_reusejp_1690_:
{
return v___x_1691_;
}
}
else
{
lean_object* v_name_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; uint8_t v___x_1696_; 
v_name_1693_ = lean_ctor_get(v_toConstantVal_1682_, 0);
v___x_1694_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0___redArg___closed__0));
lean_inc(v_name_1693_);
v___x_1695_ = l_Lean_Name_str___override(v_name_1693_, v___x_1694_);
v___x_1696_ = l_Lean_Environment_contains(v___x_1653_, v___x_1695_, v___x_1688_);
if (v___x_1696_ == 0)
{
lean_object* v___x_1697_; lean_object* v___x_1699_; 
lean_dec_ref(v_val_1678_);
lean_del_object(v___x_1676_);
lean_dec_ref_known(v_x_1655_, 2);
lean_dec_ref(v_x_1656_);
lean_dec_ref(v_a_1654_);
v___x_1697_ = lean_box(0);
if (v_isShared_1681_ == 0)
{
lean_ctor_set_tag(v___x_1680_, 0);
lean_ctor_set(v___x_1680_, 0, v___x_1697_);
v___x_1699_ = v___x_1680_;
goto v_reusejp_1698_;
}
else
{
lean_object* v_reuseFailAlloc_1700_; 
v_reuseFailAlloc_1700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1700_, 0, v___x_1697_);
v___x_1699_ = v_reuseFailAlloc_1700_;
goto v_reusejp_1698_;
}
v_reusejp_1698_:
{
return v___x_1699_;
}
}
else
{
lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1706_; 
v___x_1701_ = l_List_lengthTR___redArg(v_ctors_1685_);
v___x_1702_ = lean_nat_sub(v___x_1686_, v_numIndices_1684_);
v___x_1703_ = l_Array_extract___redArg(v_x_1656_, v___x_1702_, v___x_1686_);
v___x_1704_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1704_, 0, v_val_1678_);
lean_ctor_set(v___x_1704_, 1, v___x_1701_);
lean_ctor_set(v___x_1704_, 2, v_a_1654_);
lean_ctor_set(v___x_1704_, 3, v_x_1655_);
lean_ctor_set(v___x_1704_, 4, v_x_1656_);
lean_ctor_set(v___x_1704_, 5, v___x_1703_);
if (v_isShared_1677_ == 0)
{
lean_ctor_set(v___x_1676_, 0, v___x_1704_);
v___x_1706_ = v___x_1676_;
goto v_reusejp_1705_;
}
else
{
lean_object* v_reuseFailAlloc_1710_; 
v_reuseFailAlloc_1710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1710_, 0, v___x_1704_);
v___x_1706_ = v_reuseFailAlloc_1710_;
goto v_reusejp_1705_;
}
v_reusejp_1705_:
{
lean_object* v___x_1708_; 
if (v_isShared_1681_ == 0)
{
lean_ctor_set_tag(v___x_1680_, 0);
lean_ctor_set(v___x_1680_, 0, v___x_1706_);
v___x_1708_ = v___x_1680_;
goto v_reusejp_1707_;
}
else
{
lean_object* v_reuseFailAlloc_1709_; 
v_reuseFailAlloc_1709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1709_, 0, v___x_1706_);
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
}
}
else
{
lean_del_object(v___x_1676_);
lean_dec(v_val_1674_);
lean_dec_ref_known(v_x_1655_, 2);
lean_dec_ref(v_x_1656_);
lean_dec_ref(v_a_1654_);
lean_dec_ref(v___x_1653_);
goto v___jp_1660_;
}
}
}
}
else
{
lean_dec_ref(v_x_1656_);
lean_dec_ref(v_x_1655_);
lean_dec_ref(v_a_1654_);
lean_dec_ref(v___x_1653_);
goto v___jp_1660_;
}
}
v___jp_1660_:
{
lean_object* v___x_1661_; lean_object* v___x_1662_; 
v___x_1661_ = lean_box(0);
v___x_1662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1662_, 0, v___x_1661_);
return v___x_1662_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0___redArg___boxed(lean_object* v___x_1713_, lean_object* v_a_1714_, lean_object* v_x_1715_, lean_object* v_x_1716_, lean_object* v_x_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_){
_start:
{
lean_object* v_res_1720_; 
v_res_1720_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0___redArg(v___x_1713_, v_a_1714_, v_x_1715_, v_x_1716_, v_x_1717_, v___y_1718_);
lean_dec(v___y_1718_);
return v_res_1720_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f(lean_object* v_majorFVarId_1721_, lean_object* v_a_1722_, lean_object* v_a_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_){
_start:
{
lean_object* v___x_1727_; lean_object* v_env_1731_; lean_object* v___x_1732_; uint8_t v___x_1733_; uint8_t v___x_1734_; 
v___x_1727_ = lean_st_ref_get(v_a_1725_);
v_env_1731_ = lean_ctor_get(v___x_1727_, 0);
lean_inc_ref_n(v_env_1731_, 2);
lean_dec(v___x_1727_);
v___x_1732_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__5));
v___x_1733_ = 1;
v___x_1734_ = l_Lean_Environment_contains(v_env_1731_, v___x_1732_, v___x_1733_);
if (v___x_1734_ == 0)
{
lean_dec_ref(v_env_1731_);
lean_dec(v_majorFVarId_1721_);
goto v___jp_1728_;
}
else
{
lean_object* v___x_1735_; uint8_t v___x_1736_; 
v___x_1735_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__1));
lean_inc_ref(v_env_1731_);
v___x_1736_ = l_Lean_Environment_contains(v_env_1731_, v___x_1735_, v___x_1734_);
if (v___x_1736_ == 0)
{
lean_dec_ref(v_env_1731_);
lean_dec(v_majorFVarId_1721_);
goto v___jp_1728_;
}
else
{
lean_object* v___x_1737_; 
v___x_1737_ = l_Lean_FVarId_getDecl___redArg(v_majorFVarId_1721_, v_a_1722_, v_a_1724_, v_a_1725_);
if (lean_obj_tag(v___x_1737_) == 0)
{
lean_object* v_a_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; 
v_a_1738_ = lean_ctor_get(v___x_1737_, 0);
lean_inc(v_a_1738_);
lean_dec_ref_known(v___x_1737_, 1);
v___x_1739_ = l_Lean_LocalDecl_type(v_a_1738_);
lean_inc(v_a_1725_);
lean_inc_ref(v_a_1724_);
lean_inc(v_a_1723_);
lean_inc_ref(v_a_1722_);
v___x_1740_ = lean_whnf(v___x_1739_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_);
if (lean_obj_tag(v___x_1740_) == 0)
{
lean_object* v_a_1741_; lean_object* v_dummy_1742_; lean_object* v_nargs_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; 
v_a_1741_ = lean_ctor_get(v___x_1740_, 0);
lean_inc(v_a_1741_);
lean_dec_ref_known(v___x_1740_, 1);
v_dummy_1742_ = lean_obj_once(&l_Lean_Meta_getInductiveUniverseAndParams___closed__0, &l_Lean_Meta_getInductiveUniverseAndParams___closed__0_once, _init_l_Lean_Meta_getInductiveUniverseAndParams___closed__0);
v_nargs_1743_ = l_Lean_Expr_getAppNumArgs(v_a_1741_);
lean_inc(v_nargs_1743_);
v___x_1744_ = lean_mk_array(v_nargs_1743_, v_dummy_1742_);
v___x_1745_ = lean_unsigned_to_nat(1u);
v___x_1746_ = lean_nat_sub(v_nargs_1743_, v___x_1745_);
lean_dec(v_nargs_1743_);
v___x_1747_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0___redArg(v_env_1731_, v_a_1738_, v_a_1741_, v___x_1744_, v___x_1746_, v_a_1725_);
return v___x_1747_;
}
else
{
lean_object* v_a_1748_; lean_object* v___x_1750_; uint8_t v_isShared_1751_; uint8_t v_isSharedCheck_1755_; 
lean_dec(v_a_1738_);
lean_dec_ref(v_env_1731_);
v_a_1748_ = lean_ctor_get(v___x_1740_, 0);
v_isSharedCheck_1755_ = !lean_is_exclusive(v___x_1740_);
if (v_isSharedCheck_1755_ == 0)
{
v___x_1750_ = v___x_1740_;
v_isShared_1751_ = v_isSharedCheck_1755_;
goto v_resetjp_1749_;
}
else
{
lean_inc(v_a_1748_);
lean_dec(v___x_1740_);
v___x_1750_ = lean_box(0);
v_isShared_1751_ = v_isSharedCheck_1755_;
goto v_resetjp_1749_;
}
v_resetjp_1749_:
{
lean_object* v___x_1753_; 
if (v_isShared_1751_ == 0)
{
v___x_1753_ = v___x_1750_;
goto v_reusejp_1752_;
}
else
{
lean_object* v_reuseFailAlloc_1754_; 
v_reuseFailAlloc_1754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1754_, 0, v_a_1748_);
v___x_1753_ = v_reuseFailAlloc_1754_;
goto v_reusejp_1752_;
}
v_reusejp_1752_:
{
return v___x_1753_;
}
}
}
}
else
{
lean_object* v_a_1756_; lean_object* v___x_1758_; uint8_t v_isShared_1759_; uint8_t v_isSharedCheck_1763_; 
lean_dec_ref(v_env_1731_);
v_a_1756_ = lean_ctor_get(v___x_1737_, 0);
v_isSharedCheck_1763_ = !lean_is_exclusive(v___x_1737_);
if (v_isSharedCheck_1763_ == 0)
{
v___x_1758_ = v___x_1737_;
v_isShared_1759_ = v_isSharedCheck_1763_;
goto v_resetjp_1757_;
}
else
{
lean_inc(v_a_1756_);
lean_dec(v___x_1737_);
v___x_1758_ = lean_box(0);
v_isShared_1759_ = v_isSharedCheck_1763_;
goto v_resetjp_1757_;
}
v_resetjp_1757_:
{
lean_object* v___x_1761_; 
if (v_isShared_1759_ == 0)
{
v___x_1761_ = v___x_1758_;
goto v_reusejp_1760_;
}
else
{
lean_object* v_reuseFailAlloc_1762_; 
v_reuseFailAlloc_1762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1762_, 0, v_a_1756_);
v___x_1761_ = v_reuseFailAlloc_1762_;
goto v_reusejp_1760_;
}
v_reusejp_1760_:
{
return v___x_1761_;
}
}
}
}
}
v___jp_1728_:
{
lean_object* v___x_1729_; lean_object* v___x_1730_; 
v___x_1729_ = lean_box(0);
v___x_1730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1730_, 0, v___x_1729_);
return v___x_1730_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f___boxed(lean_object* v_majorFVarId_1764_, lean_object* v_a_1765_, lean_object* v_a_1766_, lean_object* v_a_1767_, lean_object* v_a_1768_, lean_object* v_a_1769_){
_start:
{
lean_object* v_res_1770_; 
v_res_1770_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f(v_majorFVarId_1764_, v_a_1765_, v_a_1766_, v_a_1767_, v_a_1768_);
lean_dec(v_a_1768_);
lean_dec_ref(v_a_1767_);
lean_dec(v_a_1766_);
lean_dec_ref(v_a_1765_);
return v_res_1770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0(lean_object* v___x_1771_, lean_object* v_a_1772_, lean_object* v_x_1773_, lean_object* v_x_1774_, lean_object* v_x_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_){
_start:
{
lean_object* v___x_1781_; 
v___x_1781_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0___redArg(v___x_1771_, v_a_1772_, v_x_1773_, v_x_1774_, v_x_1775_, v___y_1779_);
return v___x_1781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0___boxed(lean_object* v___x_1782_, lean_object* v_a_1783_, lean_object* v_x_1784_, lean_object* v_x_1785_, lean_object* v_x_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_){
_start:
{
lean_object* v_res_1792_; 
v_res_1792_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0(v___x_1782_, v_a_1783_, v_x_1784_, v_x_1785_, v_x_1786_, v___y_1787_, v___y_1788_, v___y_1789_, v___y_1790_);
lean_dec(v___y_1790_);
lean_dec_ref(v___y_1789_);
lean_dec(v___y_1788_);
lean_dec_ref(v___y_1787_);
return v_res_1792_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0___redArg(lean_object* v___x_1793_, lean_object* v_i_1794_, lean_object* v_n_1795_, lean_object* v_i_1796_){
_start:
{
lean_object* v_zero_1797_; uint8_t v_isZero_1798_; 
v_zero_1797_ = lean_unsigned_to_nat(0u);
v_isZero_1798_ = lean_nat_dec_eq(v_i_1796_, v_zero_1797_);
if (v_isZero_1798_ == 1)
{
uint8_t v___x_1799_; 
lean_dec(v_i_1796_);
v___x_1799_ = 0;
return v___x_1799_;
}
else
{
lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; uint8_t v___x_1803_; 
v___x_1800_ = lean_nat_sub(v_n_1795_, v_i_1796_);
v___x_1801_ = lean_array_fget_borrowed(v___x_1793_, v_i_1794_);
v___x_1802_ = lean_array_fget_borrowed(v___x_1793_, v___x_1800_);
lean_dec(v___x_1800_);
v___x_1803_ = lean_expr_eqv(v___x_1801_, v___x_1802_);
if (v___x_1803_ == 0)
{
lean_object* v_one_1804_; lean_object* v_n_1805_; 
v_one_1804_ = lean_unsigned_to_nat(1u);
v_n_1805_ = lean_nat_sub(v_i_1796_, v_one_1804_);
lean_dec(v_i_1796_);
v_i_1796_ = v_n_1805_;
goto _start;
}
else
{
lean_dec(v_i_1796_);
return v___x_1803_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0___redArg___boxed(lean_object* v___x_1807_, lean_object* v_i_1808_, lean_object* v_n_1809_, lean_object* v_i_1810_){
_start:
{
uint8_t v_res_1811_; lean_object* v_r_1812_; 
v_res_1811_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0___redArg(v___x_1807_, v_i_1808_, v_n_1809_, v_i_1810_);
lean_dec(v_n_1809_);
lean_dec(v_i_1808_);
lean_dec_ref(v___x_1807_);
v_r_1812_ = lean_box(v_res_1811_);
return v_r_1812_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1___redArg(lean_object* v___x_1813_, lean_object* v_n_1814_, lean_object* v_i_1815_){
_start:
{
lean_object* v_zero_1816_; uint8_t v_isZero_1817_; 
v_zero_1816_ = lean_unsigned_to_nat(0u);
v_isZero_1817_ = lean_nat_dec_eq(v_i_1815_, v_zero_1816_);
if (v_isZero_1817_ == 1)
{
uint8_t v___x_1818_; 
lean_dec(v_i_1815_);
v___x_1818_ = 0;
return v___x_1818_;
}
else
{
lean_object* v___x_1819_; uint8_t v___x_1820_; 
v___x_1819_ = lean_nat_sub(v_n_1814_, v_i_1815_);
lean_inc(v___x_1819_);
v___x_1820_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0___redArg(v___x_1813_, v___x_1819_, v___x_1819_, v___x_1819_);
lean_dec(v___x_1819_);
if (v___x_1820_ == 0)
{
lean_object* v_one_1821_; lean_object* v_n_1822_; 
v_one_1821_ = lean_unsigned_to_nat(1u);
v_n_1822_ = lean_nat_sub(v_i_1815_, v_one_1821_);
lean_dec(v_i_1815_);
v_i_1815_ = v_n_1822_;
goto _start;
}
else
{
lean_dec(v_i_1815_);
return v___x_1820_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1___redArg___boxed(lean_object* v___x_1824_, lean_object* v_n_1825_, lean_object* v_i_1826_){
_start:
{
uint8_t v_res_1827_; lean_object* v_r_1828_; 
v_res_1827_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1___redArg(v___x_1824_, v_n_1825_, v_i_1826_);
lean_dec(v_n_1825_);
lean_dec_ref(v___x_1824_);
v_r_1828_ = lean_box(v_res_1827_);
return v_r_1828_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5(lean_object* v___x_1829_, lean_object* v_as_1830_, size_t v_i_1831_, size_t v_stop_1832_){
_start:
{
uint8_t v___x_1833_; 
v___x_1833_ = lean_usize_dec_eq(v_i_1831_, v_stop_1832_);
if (v___x_1833_ == 0)
{
uint8_t v___x_1834_; lean_object* v___x_1835_; uint8_t v___x_1836_; 
v___x_1834_ = 1;
v___x_1835_ = lean_array_uget_borrowed(v_as_1830_, v_i_1831_);
v___x_1836_ = l_Lean_Expr_isFVar(v___x_1835_);
if (v___x_1836_ == 0)
{
return v___x_1834_;
}
else
{
lean_object* v___x_1837_; uint8_t v___x_1838_; 
v___x_1837_ = lean_unsigned_to_nat(0u);
v___x_1838_ = lean_nat_dec_eq(v___x_1829_, v___x_1837_);
if (v___x_1838_ == 0)
{
size_t v___x_1839_; size_t v___x_1840_; 
v___x_1839_ = ((size_t)1ULL);
v___x_1840_ = lean_usize_add(v_i_1831_, v___x_1839_);
v_i_1831_ = v___x_1840_;
goto _start;
}
else
{
return v___x_1834_;
}
}
}
else
{
uint8_t v___x_1842_; 
v___x_1842_ = 0;
return v___x_1842_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5___boxed(lean_object* v___x_1843_, lean_object* v_as_1844_, lean_object* v_i_1845_, lean_object* v_stop_1846_){
_start:
{
size_t v_i_boxed_1847_; size_t v_stop_boxed_1848_; uint8_t v_res_1849_; lean_object* v_r_1850_; 
v_i_boxed_1847_ = lean_unbox_usize(v_i_1845_);
lean_dec(v_i_1845_);
v_stop_boxed_1848_ = lean_unbox_usize(v_stop_1846_);
lean_dec(v_stop_1846_);
v_res_1849_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5(v___x_1843_, v_as_1844_, v_i_boxed_1847_, v_stop_boxed_1848_);
lean_dec_ref(v_as_1844_);
lean_dec(v___x_1843_);
v_r_1850_ = lean_box(v_res_1849_);
return v_r_1850_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__2(lean_object* v_fvarId_1851_, uint8_t v___x_1852_, lean_object* v_as_1853_, size_t v_i_1854_, size_t v_stop_1855_){
_start:
{
uint8_t v___x_1856_; 
v___x_1856_ = lean_usize_dec_eq(v_i_1854_, v_stop_1855_);
if (v___x_1856_ == 0)
{
uint8_t v___x_1857_; uint8_t v___y_1859_; lean_object* v___x_1863_; lean_object* v___x_1864_; uint8_t v___x_1865_; 
v___x_1857_ = 1;
v___x_1863_ = lean_array_uget_borrowed(v_as_1853_, v_i_1854_);
v___x_1864_ = l_Lean_Expr_fvarId_x21(v___x_1863_);
v___x_1865_ = l_Lean_instBEqFVarId_beq(v___x_1864_, v_fvarId_1851_);
lean_dec(v___x_1864_);
if (v___x_1865_ == 0)
{
v___y_1859_ = v___x_1852_;
goto v___jp_1858_;
}
else
{
if (v___x_1852_ == 0)
{
v___y_1859_ = v___x_1865_;
goto v___jp_1858_;
}
else
{
return v___x_1857_;
}
}
v___jp_1858_:
{
if (v___y_1859_ == 0)
{
size_t v___x_1860_; size_t v___x_1861_; 
v___x_1860_ = ((size_t)1ULL);
v___x_1861_ = lean_usize_add(v_i_1854_, v___x_1860_);
v_i_1854_ = v___x_1861_;
goto _start;
}
else
{
return v___x_1857_;
}
}
}
else
{
uint8_t v___x_1866_; 
v___x_1866_ = 0;
return v___x_1866_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__2___boxed(lean_object* v_fvarId_1867_, lean_object* v___x_1868_, lean_object* v_as_1869_, lean_object* v_i_1870_, lean_object* v_stop_1871_){
_start:
{
uint8_t v___x_7575__boxed_1872_; size_t v_i_boxed_1873_; size_t v_stop_boxed_1874_; uint8_t v_res_1875_; lean_object* v_r_1876_; 
v___x_7575__boxed_1872_ = lean_unbox(v___x_1868_);
v_i_boxed_1873_ = lean_unbox_usize(v_i_1870_);
lean_dec(v_i_1870_);
v_stop_boxed_1874_ = lean_unbox_usize(v_stop_1871_);
lean_dec(v_stop_1871_);
v_res_1875_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__2(v_fvarId_1867_, v___x_7575__boxed_1872_, v_as_1869_, v_i_boxed_1873_, v_stop_boxed_1874_);
lean_dec_ref(v_as_1869_);
lean_dec(v_fvarId_1867_);
v_r_1876_ = lean_box(v_res_1875_);
return v_r_1876_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___lam__1(lean_object* v___x_1877_, lean_object* v___x_1878_, uint8_t v___x_1879_, lean_object* v___x_1880_, lean_object* v_fvarId_1881_){
_start:
{
uint8_t v___x_1882_; lean_object* v___y_1884_; 
v___x_1882_ = lean_nat_dec_lt(v___x_1877_, v___x_1878_);
if (v___x_1882_ == 0)
{
uint8_t v___x_1889_; 
lean_dec(v___x_1878_);
v___x_1889_ = 1;
return v___x_1889_;
}
else
{
lean_object* v___x_1890_; uint8_t v___x_1891_; 
v___x_1890_ = lean_array_get_size(v___x_1880_);
v___x_1891_ = lean_nat_dec_le(v___x_1878_, v___x_1890_);
if (v___x_1891_ == 0)
{
lean_dec(v___x_1878_);
v___y_1884_ = v___x_1890_;
goto v___jp_1883_;
}
else
{
v___y_1884_ = v___x_1878_;
goto v___jp_1883_;
}
}
v___jp_1883_:
{
uint8_t v___x_1885_; 
v___x_1885_ = lean_nat_dec_lt(v___x_1877_, v___y_1884_);
if (v___x_1885_ == 0)
{
lean_dec(v___y_1884_);
return v___x_1882_;
}
else
{
size_t v___x_1886_; size_t v___x_1887_; uint8_t v___x_1888_; 
v___x_1886_ = ((size_t)0ULL);
v___x_1887_ = lean_usize_of_nat(v___y_1884_);
lean_dec(v___y_1884_);
v___x_1888_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__2(v_fvarId_1881_, v___x_1879_, v___x_1880_, v___x_1886_, v___x_1887_);
if (v___x_1888_ == 0)
{
return v___x_1885_;
}
else
{
return v___x_1879_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___lam__1___boxed(lean_object* v___x_1892_, lean_object* v___x_1893_, lean_object* v___x_1894_, lean_object* v___x_1895_, lean_object* v_fvarId_1896_){
_start:
{
uint8_t v___x_7602__boxed_1897_; uint8_t v_res_1898_; lean_object* v_r_1899_; 
v___x_7602__boxed_1897_ = lean_unbox(v___x_1894_);
v_res_1898_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___lam__1(v___x_1892_, v___x_1893_, v___x_7602__boxed_1897_, v___x_1895_, v_fvarId_1896_);
lean_dec(v_fvarId_1896_);
lean_dec_ref(v___x_1895_);
lean_dec(v___x_1892_);
v_r_1899_ = lean_box(v_res_1898_);
return v_r_1899_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__3(lean_object* v___x_1900_, lean_object* v_as_1901_, size_t v_i_1902_, size_t v_stop_1903_){
_start:
{
uint8_t v___x_1904_; 
v___x_1904_ = lean_usize_dec_eq(v_i_1902_, v_stop_1903_);
if (v___x_1904_ == 0)
{
lean_object* v___x_1905_; lean_object* v___x_1906_; uint8_t v___x_1907_; 
v___x_1905_ = lean_array_uget_borrowed(v_as_1901_, v_i_1902_);
v___x_1906_ = l_Lean_Expr_fvarId_x21(v___x_1905_);
v___x_1907_ = l_Lean_instBEqFVarId_beq(v___x_1900_, v___x_1906_);
lean_dec(v___x_1906_);
if (v___x_1907_ == 0)
{
size_t v___x_1908_; size_t v___x_1909_; 
v___x_1908_ = ((size_t)1ULL);
v___x_1909_ = lean_usize_add(v_i_1902_, v___x_1908_);
v_i_1902_ = v___x_1909_;
goto _start;
}
else
{
return v___x_1907_;
}
}
else
{
uint8_t v___x_1911_; 
v___x_1911_ = 0;
return v___x_1911_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__3___boxed(lean_object* v___x_1912_, lean_object* v_as_1913_, lean_object* v_i_1914_, lean_object* v_stop_1915_){
_start:
{
size_t v_i_boxed_1916_; size_t v_stop_boxed_1917_; uint8_t v_res_1918_; lean_object* v_r_1919_; 
v_i_boxed_1916_ = lean_unbox_usize(v_i_1914_);
lean_dec(v_i_1914_);
v_stop_boxed_1917_ = lean_unbox_usize(v_stop_1915_);
lean_dec(v_stop_1915_);
v_res_1918_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__3(v___x_1912_, v_as_1913_, v_i_boxed_1916_, v_stop_boxed_1917_);
lean_dec_ref(v_as_1913_);
lean_dec(v___x_1912_);
v_r_1919_ = lean_box(v_res_1918_);
return v_r_1919_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___lam__0(uint8_t v___x_1920_, lean_object* v_x_1921_){
_start:
{
return v___x_1920_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___lam__0___boxed(lean_object* v___x_1922_, lean_object* v_x_1923_){
_start:
{
uint8_t v___x_7651__boxed_1924_; uint8_t v_res_1925_; lean_object* v_r_1926_; 
v___x_7651__boxed_1924_ = lean_unbox(v___x_1922_);
v_res_1925_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___lam__0(v___x_7651__boxed_1924_, v_x_1923_);
lean_dec(v_x_1923_);
v_r_1926_ = lean_box(v_res_1925_);
return v_r_1926_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; 
v___x_1927_ = lean_box(0);
v___x_1928_ = lean_unsigned_to_nat(16u);
v___x_1929_ = lean_mk_array(v___x_1928_, v___x_1927_);
return v___x_1929_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; 
v___x_1930_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__0);
v___x_1931_ = lean_unsigned_to_nat(0u);
v___x_1932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1932_, 0, v___x_1931_);
lean_ctor_set(v___x_1932_, 1, v___x_1930_);
return v___x_1932_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg(uint8_t v___x_1933_, lean_object* v___x_1934_, lean_object* v___x_1935_, lean_object* v_ctx_1936_, lean_object* v_as_1937_, size_t v_i_1938_, size_t v_stop_1939_, lean_object* v___y_1940_){
_start:
{
uint8_t v___x_1942_; 
v___x_1942_ = lean_usize_dec_eq(v_i_1938_, v_stop_1939_);
if (v___x_1942_ == 0)
{
uint8_t v___x_1943_; uint8_t v_a_1945_; uint8_t v_a_1952_; uint8_t v_fst_1956_; lean_object* v_mctx_1957_; lean_object* v___y_1973_; uint8_t v_fst_1979_; lean_object* v_snd_1980_; lean_object* v___y_1997_; uint8_t v_fst_2002_; lean_object* v_mctx_2003_; lean_object* v___y_2019_; lean_object* v___x_2024_; 
v___x_1943_ = 1;
v___x_2024_ = lean_array_uget_borrowed(v_as_1937_, v_i_1938_);
if (lean_obj_tag(v___x_2024_) == 0)
{
v_a_1945_ = v___x_1933_;
goto v___jp_1944_;
}
else
{
lean_object* v_val_2025_; lean_object* v_majorDecl_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; uint8_t v___x_2029_; 
v_val_2025_ = lean_ctor_get(v___x_2024_, 0);
v_majorDecl_2026_ = lean_ctor_get(v_ctx_1936_, 2);
v___x_2027_ = l_Lean_LocalDecl_fvarId(v_val_2025_);
v___x_2028_ = l_Lean_LocalDecl_fvarId(v_majorDecl_2026_);
v___x_2029_ = l_Lean_instBEqFVarId_beq(v___x_2027_, v___x_2028_);
lean_dec(v___x_2028_);
if (v___x_2029_ == 0)
{
lean_object* v___x_2030_; lean_object* v___f_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___f_2034_; lean_object* v___y_2036_; uint8_t v_fst_2037_; lean_object* v_snd_2038_; lean_object* v___y_2044_; lean_object* v___y_2045_; lean_object* v___y_2080_; uint8_t v___x_2085_; 
v___x_2030_ = lean_box(v___x_1933_);
v___f_2031_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2031_, 0, v___x_2030_);
v___x_2032_ = lean_unsigned_to_nat(0u);
v___x_2033_ = lean_box(v___x_1933_);
lean_inc_ref(v___x_1934_);
lean_inc(v___x_1935_);
v___f_2034_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_2034_, 0, v___x_2032_);
lean_closure_set(v___f_2034_, 1, v___x_1935_);
lean_closure_set(v___f_2034_, 2, v___x_2033_);
lean_closure_set(v___f_2034_, 3, v___x_1934_);
v___x_2085_ = lean_nat_dec_lt(v___x_2032_, v___x_1935_);
if (v___x_2085_ == 0)
{
lean_dec(v___x_2027_);
goto v___jp_2049_;
}
else
{
lean_object* v___x_2086_; uint8_t v___x_2087_; 
v___x_2086_ = lean_array_get_size(v___x_1934_);
v___x_2087_ = lean_nat_dec_le(v___x_1935_, v___x_2086_);
if (v___x_2087_ == 0)
{
v___y_2080_ = v___x_2086_;
goto v___jp_2079_;
}
else
{
lean_inc(v___x_1935_);
v___y_2080_ = v___x_1935_;
goto v___jp_2079_;
}
}
v___jp_2035_:
{
if (v_fst_2037_ == 0)
{
uint8_t v___x_2039_; 
v___x_2039_ = l_Lean_Expr_hasFVar(v___y_2036_);
if (v___x_2039_ == 0)
{
uint8_t v___x_2040_; 
v___x_2040_ = l_Lean_Expr_hasMVar(v___y_2036_);
if (v___x_2040_ == 0)
{
lean_dec_ref(v___y_2036_);
lean_dec_ref(v___f_2034_);
lean_dec_ref(v___f_2031_);
v_fst_1979_ = v___x_2040_;
v_snd_1980_ = v_snd_2038_;
goto v___jp_1978_;
}
else
{
lean_object* v___x_2041_; 
v___x_2041_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_2034_, v___f_2031_, v___y_2036_, v_snd_2038_);
v___y_1997_ = v___x_2041_;
goto v___jp_1996_;
}
}
else
{
lean_object* v___x_2042_; 
v___x_2042_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_2034_, v___f_2031_, v___y_2036_, v_snd_2038_);
v___y_1997_ = v___x_2042_;
goto v___jp_1996_;
}
}
else
{
lean_dec_ref(v___y_2036_);
lean_dec_ref(v___f_2034_);
lean_dec_ref(v___f_2031_);
v_fst_1979_ = v_fst_2037_;
v_snd_1980_ = v_snd_2038_;
goto v___jp_1978_;
}
}
v___jp_2043_:
{
lean_object* v_fst_2046_; lean_object* v_snd_2047_; uint8_t v___x_2048_; 
v_fst_2046_ = lean_ctor_get(v___y_2045_, 0);
lean_inc(v_fst_2046_);
v_snd_2047_ = lean_ctor_get(v___y_2045_, 1);
lean_inc(v_snd_2047_);
lean_dec_ref(v___y_2045_);
v___x_2048_ = lean_unbox(v_fst_2046_);
lean_dec(v_fst_2046_);
v___y_2036_ = v___y_2044_;
v_fst_2037_ = v___x_2048_;
v_snd_2038_ = v_snd_2047_;
goto v___jp_2035_;
}
v___jp_2049_:
{
if (lean_obj_tag(v_val_2025_) == 0)
{
lean_object* v_type_2050_; lean_object* v___x_2051_; lean_object* v_mctx_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; uint8_t v___x_2055_; 
v_type_2050_ = lean_ctor_get(v_val_2025_, 3);
v___x_2051_ = lean_st_ref_get(v___y_1940_);
v_mctx_2052_ = lean_ctor_get(v___x_2051_, 0);
lean_inc_ref_n(v_mctx_2052_, 2);
lean_dec(v___x_2051_);
v___x_2053_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1);
v___x_2054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2054_, 0, v___x_2053_);
lean_ctor_set(v___x_2054_, 1, v_mctx_2052_);
v___x_2055_ = l_Lean_Expr_hasFVar(v_type_2050_);
if (v___x_2055_ == 0)
{
uint8_t v___x_2056_; 
v___x_2056_ = l_Lean_Expr_hasMVar(v_type_2050_);
if (v___x_2056_ == 0)
{
lean_dec_ref_known(v___x_2054_, 2);
lean_dec_ref(v___f_2034_);
lean_dec_ref(v___f_2031_);
v_fst_2002_ = v___x_2056_;
v_mctx_2003_ = v_mctx_2052_;
goto v___jp_2001_;
}
else
{
lean_object* v___x_2057_; 
lean_dec_ref(v_mctx_2052_);
lean_inc_ref(v_type_2050_);
v___x_2057_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_2034_, v___f_2031_, v_type_2050_, v___x_2054_);
v___y_2019_ = v___x_2057_;
goto v___jp_2018_;
}
}
else
{
lean_object* v___x_2058_; 
lean_dec_ref(v_mctx_2052_);
lean_inc_ref(v_type_2050_);
v___x_2058_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_2034_, v___f_2031_, v_type_2050_, v___x_2054_);
v___y_2019_ = v___x_2058_;
goto v___jp_2018_;
}
}
else
{
uint8_t v_nondep_2059_; 
v_nondep_2059_ = lean_ctor_get_uint8(v_val_2025_, sizeof(void*)*5);
if (v_nondep_2059_ == 0)
{
lean_object* v_type_2060_; lean_object* v_value_2061_; lean_object* v___x_2062_; lean_object* v_mctx_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; uint8_t v___x_2066_; 
v_type_2060_ = lean_ctor_get(v_val_2025_, 3);
v_value_2061_ = lean_ctor_get(v_val_2025_, 4);
v___x_2062_ = lean_st_ref_get(v___y_1940_);
v_mctx_2063_ = lean_ctor_get(v___x_2062_, 0);
lean_inc_ref(v_mctx_2063_);
lean_dec(v___x_2062_);
v___x_2064_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1);
v___x_2065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2065_, 0, v___x_2064_);
lean_ctor_set(v___x_2065_, 1, v_mctx_2063_);
v___x_2066_ = l_Lean_Expr_hasFVar(v_type_2060_);
if (v___x_2066_ == 0)
{
uint8_t v___x_2067_; 
v___x_2067_ = l_Lean_Expr_hasMVar(v_type_2060_);
if (v___x_2067_ == 0)
{
lean_inc_ref(v_value_2061_);
v___y_2036_ = v_value_2061_;
v_fst_2037_ = v___x_2067_;
v_snd_2038_ = v___x_2065_;
goto v___jp_2035_;
}
else
{
lean_object* v___x_2068_; 
lean_inc_ref(v_type_2060_);
lean_inc_ref(v___f_2031_);
lean_inc_ref(v___f_2034_);
v___x_2068_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_2034_, v___f_2031_, v_type_2060_, v___x_2065_);
lean_inc_ref(v_value_2061_);
v___y_2044_ = v_value_2061_;
v___y_2045_ = v___x_2068_;
goto v___jp_2043_;
}
}
else
{
lean_object* v___x_2069_; 
lean_inc_ref(v_type_2060_);
lean_inc_ref(v___f_2031_);
lean_inc_ref(v___f_2034_);
v___x_2069_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_2034_, v___f_2031_, v_type_2060_, v___x_2065_);
lean_inc_ref(v_value_2061_);
v___y_2044_ = v_value_2061_;
v___y_2045_ = v___x_2069_;
goto v___jp_2043_;
}
}
else
{
lean_object* v_type_2070_; lean_object* v___x_2071_; lean_object* v_mctx_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; uint8_t v___x_2075_; 
v_type_2070_ = lean_ctor_get(v_val_2025_, 3);
v___x_2071_ = lean_st_ref_get(v___y_1940_);
v_mctx_2072_ = lean_ctor_get(v___x_2071_, 0);
lean_inc_ref_n(v_mctx_2072_, 2);
lean_dec(v___x_2071_);
v___x_2073_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1);
v___x_2074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2074_, 0, v___x_2073_);
lean_ctor_set(v___x_2074_, 1, v_mctx_2072_);
v___x_2075_ = l_Lean_Expr_hasFVar(v_type_2070_);
if (v___x_2075_ == 0)
{
uint8_t v___x_2076_; 
v___x_2076_ = l_Lean_Expr_hasMVar(v_type_2070_);
if (v___x_2076_ == 0)
{
lean_dec_ref_known(v___x_2074_, 2);
lean_dec_ref(v___f_2034_);
lean_dec_ref(v___f_2031_);
v_fst_1956_ = v___x_2076_;
v_mctx_1957_ = v_mctx_2072_;
goto v___jp_1955_;
}
else
{
lean_object* v___x_2077_; 
lean_dec_ref(v_mctx_2072_);
lean_inc_ref(v_type_2070_);
v___x_2077_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_2034_, v___f_2031_, v_type_2070_, v___x_2074_);
v___y_1973_ = v___x_2077_;
goto v___jp_1972_;
}
}
else
{
lean_object* v___x_2078_; 
lean_dec_ref(v_mctx_2072_);
lean_inc_ref(v_type_2070_);
v___x_2078_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_2034_, v___f_2031_, v_type_2070_, v___x_2074_);
v___y_1973_ = v___x_2078_;
goto v___jp_1972_;
}
}
}
}
v___jp_2079_:
{
uint8_t v___x_2081_; 
v___x_2081_ = lean_nat_dec_lt(v___x_2032_, v___y_2080_);
if (v___x_2081_ == 0)
{
lean_dec(v___y_2080_);
lean_dec(v___x_2027_);
goto v___jp_2049_;
}
else
{
size_t v___x_2082_; size_t v___x_2083_; uint8_t v___x_2084_; 
v___x_2082_ = ((size_t)0ULL);
v___x_2083_ = lean_usize_of_nat(v___y_2080_);
lean_dec(v___y_2080_);
v___x_2084_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__3(v___x_2027_, v___x_1934_, v___x_2082_, v___x_2083_);
lean_dec(v___x_2027_);
if (v___x_2084_ == 0)
{
goto v___jp_2049_;
}
else
{
lean_dec_ref(v___f_2034_);
lean_dec_ref(v___f_2031_);
v_a_1952_ = v___x_2084_;
goto v___jp_1951_;
}
}
}
}
else
{
lean_dec(v___x_2027_);
v_a_1952_ = v___x_2029_;
goto v___jp_1951_;
}
}
v___jp_1944_:
{
if (v_a_1945_ == 0)
{
size_t v___x_1946_; size_t v___x_1947_; 
v___x_1946_ = ((size_t)1ULL);
v___x_1947_ = lean_usize_add(v_i_1938_, v___x_1946_);
v_i_1938_ = v___x_1947_;
goto _start;
}
else
{
lean_object* v___x_1949_; lean_object* v___x_1950_; 
lean_dec(v___x_1935_);
lean_dec_ref(v___x_1934_);
v___x_1949_ = lean_box(v___x_1943_);
v___x_1950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1950_, 0, v___x_1949_);
return v___x_1950_;
}
}
v___jp_1951_:
{
if (v_a_1952_ == 0)
{
lean_object* v___x_1953_; lean_object* v___x_1954_; 
lean_dec(v___x_1935_);
lean_dec_ref(v___x_1934_);
v___x_1953_ = lean_box(v___x_1943_);
v___x_1954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1954_, 0, v___x_1953_);
return v___x_1954_;
}
else
{
v_a_1945_ = v___x_1933_;
goto v___jp_1944_;
}
}
v___jp_1955_:
{
lean_object* v___x_1958_; lean_object* v_cache_1959_; lean_object* v_zetaDeltaFVarIds_1960_; lean_object* v_postponed_1961_; lean_object* v_diag_1962_; lean_object* v___x_1964_; uint8_t v_isShared_1965_; uint8_t v_isSharedCheck_1970_; 
v___x_1958_ = lean_st_ref_take(v___y_1940_);
v_cache_1959_ = lean_ctor_get(v___x_1958_, 1);
v_zetaDeltaFVarIds_1960_ = lean_ctor_get(v___x_1958_, 2);
v_postponed_1961_ = lean_ctor_get(v___x_1958_, 3);
v_diag_1962_ = lean_ctor_get(v___x_1958_, 4);
v_isSharedCheck_1970_ = !lean_is_exclusive(v___x_1958_);
if (v_isSharedCheck_1970_ == 0)
{
lean_object* v_unused_1971_; 
v_unused_1971_ = lean_ctor_get(v___x_1958_, 0);
lean_dec(v_unused_1971_);
v___x_1964_ = v___x_1958_;
v_isShared_1965_ = v_isSharedCheck_1970_;
goto v_resetjp_1963_;
}
else
{
lean_inc(v_diag_1962_);
lean_inc(v_postponed_1961_);
lean_inc(v_zetaDeltaFVarIds_1960_);
lean_inc(v_cache_1959_);
lean_dec(v___x_1958_);
v___x_1964_ = lean_box(0);
v_isShared_1965_ = v_isSharedCheck_1970_;
goto v_resetjp_1963_;
}
v_resetjp_1963_:
{
lean_object* v___x_1967_; 
if (v_isShared_1965_ == 0)
{
lean_ctor_set(v___x_1964_, 0, v_mctx_1957_);
v___x_1967_ = v___x_1964_;
goto v_reusejp_1966_;
}
else
{
lean_object* v_reuseFailAlloc_1969_; 
v_reuseFailAlloc_1969_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1969_, 0, v_mctx_1957_);
lean_ctor_set(v_reuseFailAlloc_1969_, 1, v_cache_1959_);
lean_ctor_set(v_reuseFailAlloc_1969_, 2, v_zetaDeltaFVarIds_1960_);
lean_ctor_set(v_reuseFailAlloc_1969_, 3, v_postponed_1961_);
lean_ctor_set(v_reuseFailAlloc_1969_, 4, v_diag_1962_);
v___x_1967_ = v_reuseFailAlloc_1969_;
goto v_reusejp_1966_;
}
v_reusejp_1966_:
{
lean_object* v___x_1968_; 
v___x_1968_ = lean_st_ref_put(v___y_1940_, v___x_1967_);
v_a_1952_ = v_fst_1956_;
goto v___jp_1951_;
}
}
}
v___jp_1972_:
{
lean_object* v_snd_1974_; lean_object* v_fst_1975_; lean_object* v_mctx_1976_; uint8_t v___x_1977_; 
v_snd_1974_ = lean_ctor_get(v___y_1973_, 1);
lean_inc(v_snd_1974_);
v_fst_1975_ = lean_ctor_get(v___y_1973_, 0);
lean_inc(v_fst_1975_);
lean_dec_ref(v___y_1973_);
v_mctx_1976_ = lean_ctor_get(v_snd_1974_, 1);
lean_inc_ref(v_mctx_1976_);
lean_dec(v_snd_1974_);
v___x_1977_ = lean_unbox(v_fst_1975_);
lean_dec(v_fst_1975_);
v_fst_1956_ = v___x_1977_;
v_mctx_1957_ = v_mctx_1976_;
goto v___jp_1955_;
}
v___jp_1978_:
{
lean_object* v_mctx_1981_; lean_object* v___x_1982_; lean_object* v_cache_1983_; lean_object* v_zetaDeltaFVarIds_1984_; lean_object* v_postponed_1985_; lean_object* v_diag_1986_; lean_object* v___x_1988_; uint8_t v_isShared_1989_; uint8_t v_isSharedCheck_1994_; 
v_mctx_1981_ = lean_ctor_get(v_snd_1980_, 1);
lean_inc_ref(v_mctx_1981_);
lean_dec_ref(v_snd_1980_);
v___x_1982_ = lean_st_ref_take(v___y_1940_);
v_cache_1983_ = lean_ctor_get(v___x_1982_, 1);
v_zetaDeltaFVarIds_1984_ = lean_ctor_get(v___x_1982_, 2);
v_postponed_1985_ = lean_ctor_get(v___x_1982_, 3);
v_diag_1986_ = lean_ctor_get(v___x_1982_, 4);
v_isSharedCheck_1994_ = !lean_is_exclusive(v___x_1982_);
if (v_isSharedCheck_1994_ == 0)
{
lean_object* v_unused_1995_; 
v_unused_1995_ = lean_ctor_get(v___x_1982_, 0);
lean_dec(v_unused_1995_);
v___x_1988_ = v___x_1982_;
v_isShared_1989_ = v_isSharedCheck_1994_;
goto v_resetjp_1987_;
}
else
{
lean_inc(v_diag_1986_);
lean_inc(v_postponed_1985_);
lean_inc(v_zetaDeltaFVarIds_1984_);
lean_inc(v_cache_1983_);
lean_dec(v___x_1982_);
v___x_1988_ = lean_box(0);
v_isShared_1989_ = v_isSharedCheck_1994_;
goto v_resetjp_1987_;
}
v_resetjp_1987_:
{
lean_object* v___x_1991_; 
if (v_isShared_1989_ == 0)
{
lean_ctor_set(v___x_1988_, 0, v_mctx_1981_);
v___x_1991_ = v___x_1988_;
goto v_reusejp_1990_;
}
else
{
lean_object* v_reuseFailAlloc_1993_; 
v_reuseFailAlloc_1993_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1993_, 0, v_mctx_1981_);
lean_ctor_set(v_reuseFailAlloc_1993_, 1, v_cache_1983_);
lean_ctor_set(v_reuseFailAlloc_1993_, 2, v_zetaDeltaFVarIds_1984_);
lean_ctor_set(v_reuseFailAlloc_1993_, 3, v_postponed_1985_);
lean_ctor_set(v_reuseFailAlloc_1993_, 4, v_diag_1986_);
v___x_1991_ = v_reuseFailAlloc_1993_;
goto v_reusejp_1990_;
}
v_reusejp_1990_:
{
lean_object* v___x_1992_; 
v___x_1992_ = lean_st_ref_put(v___y_1940_, v___x_1991_);
v_a_1952_ = v_fst_1979_;
goto v___jp_1951_;
}
}
}
v___jp_1996_:
{
lean_object* v_fst_1998_; lean_object* v_snd_1999_; uint8_t v___x_2000_; 
v_fst_1998_ = lean_ctor_get(v___y_1997_, 0);
lean_inc(v_fst_1998_);
v_snd_1999_ = lean_ctor_get(v___y_1997_, 1);
lean_inc(v_snd_1999_);
lean_dec_ref(v___y_1997_);
v___x_2000_ = lean_unbox(v_fst_1998_);
lean_dec(v_fst_1998_);
v_fst_1979_ = v___x_2000_;
v_snd_1980_ = v_snd_1999_;
goto v___jp_1978_;
}
v___jp_2001_:
{
lean_object* v___x_2004_; lean_object* v_cache_2005_; lean_object* v_zetaDeltaFVarIds_2006_; lean_object* v_postponed_2007_; lean_object* v_diag_2008_; lean_object* v___x_2010_; uint8_t v_isShared_2011_; uint8_t v_isSharedCheck_2016_; 
v___x_2004_ = lean_st_ref_take(v___y_1940_);
v_cache_2005_ = lean_ctor_get(v___x_2004_, 1);
v_zetaDeltaFVarIds_2006_ = lean_ctor_get(v___x_2004_, 2);
v_postponed_2007_ = lean_ctor_get(v___x_2004_, 3);
v_diag_2008_ = lean_ctor_get(v___x_2004_, 4);
v_isSharedCheck_2016_ = !lean_is_exclusive(v___x_2004_);
if (v_isSharedCheck_2016_ == 0)
{
lean_object* v_unused_2017_; 
v_unused_2017_ = lean_ctor_get(v___x_2004_, 0);
lean_dec(v_unused_2017_);
v___x_2010_ = v___x_2004_;
v_isShared_2011_ = v_isSharedCheck_2016_;
goto v_resetjp_2009_;
}
else
{
lean_inc(v_diag_2008_);
lean_inc(v_postponed_2007_);
lean_inc(v_zetaDeltaFVarIds_2006_);
lean_inc(v_cache_2005_);
lean_dec(v___x_2004_);
v___x_2010_ = lean_box(0);
v_isShared_2011_ = v_isSharedCheck_2016_;
goto v_resetjp_2009_;
}
v_resetjp_2009_:
{
lean_object* v___x_2013_; 
if (v_isShared_2011_ == 0)
{
lean_ctor_set(v___x_2010_, 0, v_mctx_2003_);
v___x_2013_ = v___x_2010_;
goto v_reusejp_2012_;
}
else
{
lean_object* v_reuseFailAlloc_2015_; 
v_reuseFailAlloc_2015_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2015_, 0, v_mctx_2003_);
lean_ctor_set(v_reuseFailAlloc_2015_, 1, v_cache_2005_);
lean_ctor_set(v_reuseFailAlloc_2015_, 2, v_zetaDeltaFVarIds_2006_);
lean_ctor_set(v_reuseFailAlloc_2015_, 3, v_postponed_2007_);
lean_ctor_set(v_reuseFailAlloc_2015_, 4, v_diag_2008_);
v___x_2013_ = v_reuseFailAlloc_2015_;
goto v_reusejp_2012_;
}
v_reusejp_2012_:
{
lean_object* v___x_2014_; 
v___x_2014_ = lean_st_ref_put(v___y_1940_, v___x_2013_);
v_a_1952_ = v_fst_2002_;
goto v___jp_1951_;
}
}
}
v___jp_2018_:
{
lean_object* v_snd_2020_; lean_object* v_fst_2021_; lean_object* v_mctx_2022_; uint8_t v___x_2023_; 
v_snd_2020_ = lean_ctor_get(v___y_2019_, 1);
lean_inc(v_snd_2020_);
v_fst_2021_ = lean_ctor_get(v___y_2019_, 0);
lean_inc(v_fst_2021_);
lean_dec_ref(v___y_2019_);
v_mctx_2022_ = lean_ctor_get(v_snd_2020_, 1);
lean_inc_ref(v_mctx_2022_);
lean_dec(v_snd_2020_);
v___x_2023_ = lean_unbox(v_fst_2021_);
lean_dec(v_fst_2021_);
v_fst_2002_ = v___x_2023_;
v_mctx_2003_ = v_mctx_2022_;
goto v___jp_2001_;
}
}
else
{
uint8_t v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; 
lean_dec(v___x_1935_);
lean_dec_ref(v___x_1934_);
v___x_2088_ = 0;
v___x_2089_ = lean_box(v___x_2088_);
v___x_2090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2090_, 0, v___x_2089_);
return v___x_2090_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___boxed(lean_object* v___x_2091_, lean_object* v___x_2092_, lean_object* v___x_2093_, lean_object* v_ctx_2094_, lean_object* v_as_2095_, lean_object* v_i_2096_, lean_object* v_stop_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_){
_start:
{
uint8_t v___x_7681__boxed_2100_; size_t v_i_boxed_2101_; size_t v_stop_boxed_2102_; lean_object* v_res_2103_; 
v___x_7681__boxed_2100_ = lean_unbox(v___x_2091_);
v_i_boxed_2101_ = lean_unbox_usize(v_i_2096_);
lean_dec(v_i_2096_);
v_stop_boxed_2102_ = lean_unbox_usize(v_stop_2097_);
lean_dec(v_stop_2097_);
v_res_2103_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg(v___x_7681__boxed_2100_, v___x_2092_, v___x_2093_, v_ctx_2094_, v_as_2095_, v_i_boxed_2101_, v_stop_boxed_2102_, v___y_2098_);
lean_dec(v___y_2098_);
lean_dec_ref(v_as_2095_);
lean_dec_ref(v_ctx_2094_);
return v_res_2103_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4(uint8_t v___x_2104_, lean_object* v___x_2105_, lean_object* v___x_2106_, lean_object* v_ctx_2107_, lean_object* v_x_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_){
_start:
{
if (lean_obj_tag(v_x_2108_) == 0)
{
lean_object* v_cs_2114_; lean_object* v___x_2116_; uint8_t v_isShared_2117_; uint8_t v_isSharedCheck_2132_; 
v_cs_2114_ = lean_ctor_get(v_x_2108_, 0);
v_isSharedCheck_2132_ = !lean_is_exclusive(v_x_2108_);
if (v_isSharedCheck_2132_ == 0)
{
v___x_2116_ = v_x_2108_;
v_isShared_2117_ = v_isSharedCheck_2132_;
goto v_resetjp_2115_;
}
else
{
lean_inc(v_cs_2114_);
lean_dec(v_x_2108_);
v___x_2116_ = lean_box(0);
v_isShared_2117_ = v_isSharedCheck_2132_;
goto v_resetjp_2115_;
}
v_resetjp_2115_:
{
lean_object* v___x_2118_; lean_object* v___x_2119_; uint8_t v___x_2120_; 
v___x_2118_ = lean_unsigned_to_nat(0u);
v___x_2119_ = lean_array_get_size(v_cs_2114_);
v___x_2120_ = lean_nat_dec_lt(v___x_2118_, v___x_2119_);
if (v___x_2120_ == 0)
{
lean_object* v___x_2121_; lean_object* v___x_2123_; 
lean_dec_ref(v_cs_2114_);
lean_dec(v___x_2106_);
lean_dec_ref(v___x_2105_);
v___x_2121_ = lean_box(v___x_2120_);
if (v_isShared_2117_ == 0)
{
lean_ctor_set(v___x_2116_, 0, v___x_2121_);
v___x_2123_ = v___x_2116_;
goto v_reusejp_2122_;
}
else
{
lean_object* v_reuseFailAlloc_2124_; 
v_reuseFailAlloc_2124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2124_, 0, v___x_2121_);
v___x_2123_ = v_reuseFailAlloc_2124_;
goto v_reusejp_2122_;
}
v_reusejp_2122_:
{
return v___x_2123_;
}
}
else
{
if (v___x_2120_ == 0)
{
lean_object* v___x_2125_; lean_object* v___x_2127_; 
lean_dec_ref(v_cs_2114_);
lean_dec(v___x_2106_);
lean_dec_ref(v___x_2105_);
v___x_2125_ = lean_box(v___x_2120_);
if (v_isShared_2117_ == 0)
{
lean_ctor_set(v___x_2116_, 0, v___x_2125_);
v___x_2127_ = v___x_2116_;
goto v_reusejp_2126_;
}
else
{
lean_object* v_reuseFailAlloc_2128_; 
v_reuseFailAlloc_2128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2128_, 0, v___x_2125_);
v___x_2127_ = v_reuseFailAlloc_2128_;
goto v_reusejp_2126_;
}
v_reusejp_2126_:
{
return v___x_2127_;
}
}
else
{
size_t v___x_2129_; size_t v___x_2130_; lean_object* v___x_2131_; 
lean_del_object(v___x_2116_);
v___x_2129_ = ((size_t)0ULL);
v___x_2130_ = lean_usize_of_nat(v___x_2119_);
v___x_2131_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4_spec__5(v___x_2104_, v___x_2105_, v___x_2106_, v_ctx_2107_, v_cs_2114_, v___x_2129_, v___x_2130_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_);
lean_dec_ref(v_cs_2114_);
return v___x_2131_;
}
}
}
}
else
{
lean_object* v_vs_2133_; lean_object* v___x_2135_; uint8_t v_isShared_2136_; uint8_t v_isSharedCheck_2151_; 
v_vs_2133_ = lean_ctor_get(v_x_2108_, 0);
v_isSharedCheck_2151_ = !lean_is_exclusive(v_x_2108_);
if (v_isSharedCheck_2151_ == 0)
{
v___x_2135_ = v_x_2108_;
v_isShared_2136_ = v_isSharedCheck_2151_;
goto v_resetjp_2134_;
}
else
{
lean_inc(v_vs_2133_);
lean_dec(v_x_2108_);
v___x_2135_ = lean_box(0);
v_isShared_2136_ = v_isSharedCheck_2151_;
goto v_resetjp_2134_;
}
v_resetjp_2134_:
{
lean_object* v___x_2137_; lean_object* v___x_2138_; uint8_t v___x_2139_; 
v___x_2137_ = lean_unsigned_to_nat(0u);
v___x_2138_ = lean_array_get_size(v_vs_2133_);
v___x_2139_ = lean_nat_dec_lt(v___x_2137_, v___x_2138_);
if (v___x_2139_ == 0)
{
lean_object* v___x_2140_; lean_object* v___x_2142_; 
lean_dec_ref(v_vs_2133_);
lean_dec(v___x_2106_);
lean_dec_ref(v___x_2105_);
v___x_2140_ = lean_box(v___x_2139_);
if (v_isShared_2136_ == 0)
{
lean_ctor_set_tag(v___x_2135_, 0);
lean_ctor_set(v___x_2135_, 0, v___x_2140_);
v___x_2142_ = v___x_2135_;
goto v_reusejp_2141_;
}
else
{
lean_object* v_reuseFailAlloc_2143_; 
v_reuseFailAlloc_2143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2143_, 0, v___x_2140_);
v___x_2142_ = v_reuseFailAlloc_2143_;
goto v_reusejp_2141_;
}
v_reusejp_2141_:
{
return v___x_2142_;
}
}
else
{
if (v___x_2139_ == 0)
{
lean_object* v___x_2144_; lean_object* v___x_2146_; 
lean_dec_ref(v_vs_2133_);
lean_dec(v___x_2106_);
lean_dec_ref(v___x_2105_);
v___x_2144_ = lean_box(v___x_2139_);
if (v_isShared_2136_ == 0)
{
lean_ctor_set_tag(v___x_2135_, 0);
lean_ctor_set(v___x_2135_, 0, v___x_2144_);
v___x_2146_ = v___x_2135_;
goto v_reusejp_2145_;
}
else
{
lean_object* v_reuseFailAlloc_2147_; 
v_reuseFailAlloc_2147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2147_, 0, v___x_2144_);
v___x_2146_ = v_reuseFailAlloc_2147_;
goto v_reusejp_2145_;
}
v_reusejp_2145_:
{
return v___x_2146_;
}
}
else
{
size_t v___x_2148_; size_t v___x_2149_; lean_object* v___x_2150_; 
lean_del_object(v___x_2135_);
v___x_2148_ = ((size_t)0ULL);
v___x_2149_ = lean_usize_of_nat(v___x_2138_);
v___x_2150_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg(v___x_2104_, v___x_2105_, v___x_2106_, v_ctx_2107_, v_vs_2133_, v___x_2148_, v___x_2149_, v___y_2110_);
lean_dec_ref(v_vs_2133_);
return v___x_2150_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4_spec__5(uint8_t v___x_2152_, lean_object* v___x_2153_, lean_object* v___x_2154_, lean_object* v_ctx_2155_, lean_object* v_as_2156_, size_t v_i_2157_, size_t v_stop_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_){
_start:
{
uint8_t v___x_2164_; 
v___x_2164_ = lean_usize_dec_eq(v_i_2157_, v_stop_2158_);
if (v___x_2164_ == 0)
{
lean_object* v___x_2165_; lean_object* v___x_2166_; 
v___x_2165_ = lean_array_uget_borrowed(v_as_2156_, v_i_2157_);
lean_inc(v___x_2165_);
lean_inc(v___x_2154_);
lean_inc_ref(v___x_2153_);
v___x_2166_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4(v___x_2152_, v___x_2153_, v___x_2154_, v_ctx_2155_, v___x_2165_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_);
if (lean_obj_tag(v___x_2166_) == 0)
{
lean_object* v_a_2167_; lean_object* v___x_2169_; uint8_t v_isShared_2170_; uint8_t v_isSharedCheck_2178_; 
v_a_2167_ = lean_ctor_get(v___x_2166_, 0);
v_isSharedCheck_2178_ = !lean_is_exclusive(v___x_2166_);
if (v_isSharedCheck_2178_ == 0)
{
v___x_2169_ = v___x_2166_;
v_isShared_2170_ = v_isSharedCheck_2178_;
goto v_resetjp_2168_;
}
else
{
lean_inc(v_a_2167_);
lean_dec(v___x_2166_);
v___x_2169_ = lean_box(0);
v_isShared_2170_ = v_isSharedCheck_2178_;
goto v_resetjp_2168_;
}
v_resetjp_2168_:
{
uint8_t v___x_2171_; 
v___x_2171_ = lean_unbox(v_a_2167_);
if (v___x_2171_ == 0)
{
size_t v___x_2172_; size_t v___x_2173_; 
lean_del_object(v___x_2169_);
lean_dec(v_a_2167_);
v___x_2172_ = ((size_t)1ULL);
v___x_2173_ = lean_usize_add(v_i_2157_, v___x_2172_);
v_i_2157_ = v___x_2173_;
goto _start;
}
else
{
lean_object* v___x_2176_; 
lean_dec(v___x_2154_);
lean_dec_ref(v___x_2153_);
if (v_isShared_2170_ == 0)
{
v___x_2176_ = v___x_2169_;
goto v_reusejp_2175_;
}
else
{
lean_object* v_reuseFailAlloc_2177_; 
v_reuseFailAlloc_2177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2177_, 0, v_a_2167_);
v___x_2176_ = v_reuseFailAlloc_2177_;
goto v_reusejp_2175_;
}
v_reusejp_2175_:
{
return v___x_2176_;
}
}
}
}
else
{
lean_dec(v___x_2154_);
lean_dec_ref(v___x_2153_);
return v___x_2166_;
}
}
else
{
uint8_t v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; 
lean_dec(v___x_2154_);
lean_dec_ref(v___x_2153_);
v___x_2179_ = 0;
v___x_2180_ = lean_box(v___x_2179_);
v___x_2181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2181_, 0, v___x_2180_);
return v___x_2181_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4_spec__5___boxed(lean_object* v___x_2182_, lean_object* v___x_2183_, lean_object* v___x_2184_, lean_object* v_ctx_2185_, lean_object* v_as_2186_, lean_object* v_i_2187_, lean_object* v_stop_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_){
_start:
{
uint8_t v___x_7976__boxed_2194_; size_t v_i_boxed_2195_; size_t v_stop_boxed_2196_; lean_object* v_res_2197_; 
v___x_7976__boxed_2194_ = lean_unbox(v___x_2182_);
v_i_boxed_2195_ = lean_unbox_usize(v_i_2187_);
lean_dec(v_i_2187_);
v_stop_boxed_2196_ = lean_unbox_usize(v_stop_2188_);
lean_dec(v_stop_2188_);
v_res_2197_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4_spec__5(v___x_7976__boxed_2194_, v___x_2183_, v___x_2184_, v_ctx_2185_, v_as_2186_, v_i_boxed_2195_, v_stop_boxed_2196_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_);
lean_dec(v___y_2192_);
lean_dec_ref(v___y_2191_);
lean_dec(v___y_2190_);
lean_dec_ref(v___y_2189_);
lean_dec_ref(v_as_2186_);
lean_dec_ref(v_ctx_2185_);
return v_res_2197_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4___boxed(lean_object* v___x_2198_, lean_object* v___x_2199_, lean_object* v___x_2200_, lean_object* v_ctx_2201_, lean_object* v_x_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_){
_start:
{
uint8_t v___x_7995__boxed_2208_; lean_object* v_res_2209_; 
v___x_7995__boxed_2208_ = lean_unbox(v___x_2198_);
v_res_2209_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4(v___x_7995__boxed_2208_, v___x_2199_, v___x_2200_, v_ctx_2201_, v_x_2202_, v___y_2203_, v___y_2204_, v___y_2205_, v___y_2206_);
lean_dec(v___y_2206_);
lean_dec_ref(v___y_2205_);
lean_dec(v___y_2204_);
lean_dec_ref(v___y_2203_);
lean_dec_ref(v_ctx_2201_);
return v_res_2209_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4(uint8_t v___x_2210_, lean_object* v___x_2211_, lean_object* v___x_2212_, lean_object* v_ctx_2213_, lean_object* v_t_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_){
_start:
{
lean_object* v_root_2220_; lean_object* v_tail_2221_; lean_object* v___x_2222_; 
v_root_2220_ = lean_ctor_get(v_t_2214_, 0);
lean_inc_ref(v_root_2220_);
v_tail_2221_ = lean_ctor_get(v_t_2214_, 1);
lean_inc_ref(v_tail_2221_);
lean_dec_ref(v_t_2214_);
lean_inc(v___x_2212_);
lean_inc_ref(v___x_2211_);
v___x_2222_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4(v___x_2210_, v___x_2211_, v___x_2212_, v_ctx_2213_, v_root_2220_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_);
if (lean_obj_tag(v___x_2222_) == 0)
{
lean_object* v_a_2223_; uint8_t v___x_2224_; 
v_a_2223_ = lean_ctor_get(v___x_2222_, 0);
lean_inc(v_a_2223_);
v___x_2224_ = lean_unbox(v_a_2223_);
lean_dec(v_a_2223_);
if (v___x_2224_ == 0)
{
lean_object* v___x_2226_; uint8_t v_isShared_2227_; uint8_t v_isSharedCheck_2242_; 
v_isSharedCheck_2242_ = !lean_is_exclusive(v___x_2222_);
if (v_isSharedCheck_2242_ == 0)
{
lean_object* v_unused_2243_; 
v_unused_2243_ = lean_ctor_get(v___x_2222_, 0);
lean_dec(v_unused_2243_);
v___x_2226_ = v___x_2222_;
v_isShared_2227_ = v_isSharedCheck_2242_;
goto v_resetjp_2225_;
}
else
{
lean_dec(v___x_2222_);
v___x_2226_ = lean_box(0);
v_isShared_2227_ = v_isSharedCheck_2242_;
goto v_resetjp_2225_;
}
v_resetjp_2225_:
{
lean_object* v___x_2228_; lean_object* v___x_2229_; uint8_t v___x_2230_; 
v___x_2228_ = lean_unsigned_to_nat(0u);
v___x_2229_ = lean_array_get_size(v_tail_2221_);
v___x_2230_ = lean_nat_dec_lt(v___x_2228_, v___x_2229_);
if (v___x_2230_ == 0)
{
lean_object* v___x_2231_; lean_object* v___x_2233_; 
lean_dec_ref(v_tail_2221_);
lean_dec(v___x_2212_);
lean_dec_ref(v___x_2211_);
v___x_2231_ = lean_box(v___x_2230_);
if (v_isShared_2227_ == 0)
{
lean_ctor_set(v___x_2226_, 0, v___x_2231_);
v___x_2233_ = v___x_2226_;
goto v_reusejp_2232_;
}
else
{
lean_object* v_reuseFailAlloc_2234_; 
v_reuseFailAlloc_2234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2234_, 0, v___x_2231_);
v___x_2233_ = v_reuseFailAlloc_2234_;
goto v_reusejp_2232_;
}
v_reusejp_2232_:
{
return v___x_2233_;
}
}
else
{
if (v___x_2230_ == 0)
{
lean_object* v___x_2235_; lean_object* v___x_2237_; 
lean_dec_ref(v_tail_2221_);
lean_dec(v___x_2212_);
lean_dec_ref(v___x_2211_);
v___x_2235_ = lean_box(v___x_2230_);
if (v_isShared_2227_ == 0)
{
lean_ctor_set(v___x_2226_, 0, v___x_2235_);
v___x_2237_ = v___x_2226_;
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
size_t v___x_2239_; size_t v___x_2240_; lean_object* v___x_2241_; 
lean_del_object(v___x_2226_);
v___x_2239_ = ((size_t)0ULL);
v___x_2240_ = lean_usize_of_nat(v___x_2229_);
v___x_2241_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg(v___x_2210_, v___x_2211_, v___x_2212_, v_ctx_2213_, v_tail_2221_, v___x_2239_, v___x_2240_, v___y_2216_);
lean_dec_ref(v_tail_2221_);
return v___x_2241_;
}
}
}
}
else
{
lean_dec_ref(v_tail_2221_);
lean_dec(v___x_2212_);
lean_dec_ref(v___x_2211_);
return v___x_2222_;
}
}
else
{
lean_dec_ref(v_tail_2221_);
lean_dec(v___x_2212_);
lean_dec_ref(v___x_2211_);
return v___x_2222_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4___boxed(lean_object* v___x_2244_, lean_object* v___x_2245_, lean_object* v___x_2246_, lean_object* v_ctx_2247_, lean_object* v_t_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_){
_start:
{
uint8_t v___x_8140__boxed_2254_; lean_object* v_res_2255_; 
v___x_8140__boxed_2254_ = lean_unbox(v___x_2244_);
v_res_2255_ = l_Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4(v___x_8140__boxed_2254_, v___x_2245_, v___x_2246_, v_ctx_2247_, v_t_2248_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_);
lean_dec(v___y_2252_);
lean_dec_ref(v___y_2251_);
lean_dec(v___y_2250_);
lean_dec_ref(v___y_2249_);
lean_dec_ref(v_ctx_2247_);
return v_res_2255_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices(lean_object* v_ctx_2256_, lean_object* v_a_2257_, lean_object* v_a_2258_, lean_object* v_a_2259_, lean_object* v_a_2260_){
_start:
{
lean_object* v_majorTypeIndices_2262_; lean_object* v___x_2263_; uint8_t v___y_2265_; lean_object* v___x_2287_; uint8_t v___x_2288_; 
v_majorTypeIndices_2262_ = lean_ctor_get(v_ctx_2256_, 5);
lean_inc_ref(v_majorTypeIndices_2262_);
v___x_2263_ = lean_array_get_size(v_majorTypeIndices_2262_);
v___x_2287_ = lean_unsigned_to_nat(0u);
v___x_2288_ = lean_nat_dec_eq(v___x_2263_, v___x_2287_);
if (v___x_2288_ == 0)
{
uint8_t v___x_2289_; 
v___x_2289_ = lean_nat_dec_lt(v___x_2287_, v___x_2263_);
if (v___x_2289_ == 0)
{
v___y_2265_ = v___x_2289_;
goto v___jp_2264_;
}
else
{
if (v___x_2289_ == 0)
{
v___y_2265_ = v___x_2289_;
goto v___jp_2264_;
}
else
{
size_t v___x_2290_; size_t v___x_2291_; uint8_t v___x_2292_; 
v___x_2290_ = ((size_t)0ULL);
v___x_2291_ = lean_usize_of_nat(v___x_2263_);
v___x_2292_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5(v___x_2263_, v_majorTypeIndices_2262_, v___x_2290_, v___x_2291_);
if (v___x_2292_ == 0)
{
v___y_2265_ = v___x_2292_;
goto v___jp_2264_;
}
else
{
lean_object* v___x_2293_; lean_object* v___x_2294_; 
lean_dec_ref(v_majorTypeIndices_2262_);
lean_dec_ref(v_ctx_2256_);
v___x_2293_ = lean_box(v___x_2288_);
v___x_2294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2294_, 0, v___x_2293_);
return v___x_2294_;
}
}
}
}
else
{
lean_object* v___x_2295_; lean_object* v___x_2296_; 
lean_dec_ref(v_majorTypeIndices_2262_);
lean_dec_ref(v_ctx_2256_);
v___x_2295_ = lean_box(v___x_2288_);
v___x_2296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2296_, 0, v___x_2295_);
return v___x_2296_;
}
v___jp_2264_:
{
uint8_t v___x_2266_; 
v___x_2266_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1___redArg(v_majorTypeIndices_2262_, v___x_2263_, v___x_2263_);
if (v___x_2266_ == 0)
{
lean_object* v_lctx_2267_; lean_object* v_decls_2268_; lean_object* v___x_2269_; 
v_lctx_2267_ = lean_ctor_get(v_a_2257_, 2);
v_decls_2268_ = lean_ctor_get(v_lctx_2267_, 1);
lean_inc_ref(v_decls_2268_);
v___x_2269_ = l_Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4(v___x_2266_, v_majorTypeIndices_2262_, v___x_2263_, v_ctx_2256_, v_decls_2268_, v_a_2257_, v_a_2258_, v_a_2259_, v_a_2260_);
lean_dec_ref(v_ctx_2256_);
if (lean_obj_tag(v___x_2269_) == 0)
{
lean_object* v_a_2270_; lean_object* v___x_2272_; uint8_t v_isShared_2273_; uint8_t v_isSharedCheck_2284_; 
v_a_2270_ = lean_ctor_get(v___x_2269_, 0);
v_isSharedCheck_2284_ = !lean_is_exclusive(v___x_2269_);
if (v_isSharedCheck_2284_ == 0)
{
v___x_2272_ = v___x_2269_;
v_isShared_2273_ = v_isSharedCheck_2284_;
goto v_resetjp_2271_;
}
else
{
lean_inc(v_a_2270_);
lean_dec(v___x_2269_);
v___x_2272_ = lean_box(0);
v_isShared_2273_ = v_isSharedCheck_2284_;
goto v_resetjp_2271_;
}
v_resetjp_2271_:
{
uint8_t v___x_2274_; 
v___x_2274_ = lean_unbox(v_a_2270_);
lean_dec(v_a_2270_);
if (v___x_2274_ == 0)
{
uint8_t v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2278_; 
v___x_2275_ = 1;
v___x_2276_ = lean_box(v___x_2275_);
if (v_isShared_2273_ == 0)
{
lean_ctor_set(v___x_2272_, 0, v___x_2276_);
v___x_2278_ = v___x_2272_;
goto v_reusejp_2277_;
}
else
{
lean_object* v_reuseFailAlloc_2279_; 
v_reuseFailAlloc_2279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2279_, 0, v___x_2276_);
v___x_2278_ = v_reuseFailAlloc_2279_;
goto v_reusejp_2277_;
}
v_reusejp_2277_:
{
return v___x_2278_;
}
}
else
{
lean_object* v___x_2280_; lean_object* v___x_2282_; 
v___x_2280_ = lean_box(v___x_2266_);
if (v_isShared_2273_ == 0)
{
lean_ctor_set(v___x_2272_, 0, v___x_2280_);
v___x_2282_ = v___x_2272_;
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
}
}
else
{
return v___x_2269_;
}
}
else
{
lean_object* v___x_2285_; lean_object* v___x_2286_; 
lean_dec_ref(v_majorTypeIndices_2262_);
lean_dec_ref(v_ctx_2256_);
v___x_2285_ = lean_box(v___y_2265_);
v___x_2286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2286_, 0, v___x_2285_);
return v___x_2286_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___boxed(lean_object* v_ctx_2297_, lean_object* v_a_2298_, lean_object* v_a_2299_, lean_object* v_a_2300_, lean_object* v_a_2301_, lean_object* v_a_2302_){
_start:
{
lean_object* v_res_2303_; 
v_res_2303_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices(v_ctx_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_);
lean_dec(v_a_2301_);
lean_dec_ref(v_a_2300_);
lean_dec(v_a_2299_);
lean_dec_ref(v_a_2298_);
return v_res_2303_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0(lean_object* v___x_2304_, lean_object* v_i_2305_, lean_object* v_n_2306_, lean_object* v_i_2307_, lean_object* v_a_2308_){
_start:
{
uint8_t v___x_2309_; 
v___x_2309_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0___redArg(v___x_2304_, v_i_2305_, v_n_2306_, v_i_2307_);
return v___x_2309_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0___boxed(lean_object* v___x_2310_, lean_object* v_i_2311_, lean_object* v_n_2312_, lean_object* v_i_2313_, lean_object* v_a_2314_){
_start:
{
uint8_t v_res_2315_; lean_object* v_r_2316_; 
v_res_2315_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0(v___x_2310_, v_i_2311_, v_n_2312_, v_i_2313_, v_a_2314_);
lean_dec(v_n_2312_);
lean_dec(v_i_2311_);
lean_dec_ref(v___x_2310_);
v_r_2316_ = lean_box(v_res_2315_);
return v_r_2316_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1(lean_object* v___x_2317_, lean_object* v_n_2318_, lean_object* v_i_2319_, lean_object* v_a_2320_){
_start:
{
uint8_t v___x_2321_; 
v___x_2321_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1___redArg(v___x_2317_, v_n_2318_, v_i_2319_);
return v___x_2321_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1___boxed(lean_object* v___x_2322_, lean_object* v_n_2323_, lean_object* v_i_2324_, lean_object* v_a_2325_){
_start:
{
uint8_t v_res_2326_; lean_object* v_r_2327_; 
v_res_2326_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1(v___x_2322_, v_n_2323_, v_i_2324_, v_a_2325_);
lean_dec(v_n_2323_);
lean_dec_ref(v___x_2322_);
v_r_2327_ = lean_box(v_res_2326_);
return v_r_2327_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5(uint8_t v___x_2328_, lean_object* v___x_2329_, lean_object* v___x_2330_, lean_object* v_ctx_2331_, lean_object* v_as_2332_, size_t v_i_2333_, size_t v_stop_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_){
_start:
{
lean_object* v___x_2340_; 
v___x_2340_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg(v___x_2328_, v___x_2329_, v___x_2330_, v_ctx_2331_, v_as_2332_, v_i_2333_, v_stop_2334_, v___y_2336_);
return v___x_2340_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___boxed(lean_object* v___x_2341_, lean_object* v___x_2342_, lean_object* v___x_2343_, lean_object* v_ctx_2344_, lean_object* v_as_2345_, lean_object* v_i_2346_, lean_object* v_stop_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_){
_start:
{
uint8_t v___x_8293__boxed_2353_; size_t v_i_boxed_2354_; size_t v_stop_boxed_2355_; lean_object* v_res_2356_; 
v___x_8293__boxed_2353_ = lean_unbox(v___x_2341_);
v_i_boxed_2354_ = lean_unbox_usize(v_i_2346_);
lean_dec(v_i_2346_);
v_stop_boxed_2355_ = lean_unbox_usize(v_stop_2347_);
lean_dec(v_stop_2347_);
v_res_2356_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5(v___x_8293__boxed_2353_, v___x_2342_, v___x_2343_, v_ctx_2344_, v_as_2345_, v_i_boxed_2354_, v_stop_boxed_2355_, v___y_2348_, v___y_2349_, v___y_2350_, v___y_2351_);
lean_dec(v___y_2351_);
lean_dec_ref(v___y_2350_);
lean_dec(v___y_2349_);
lean_dec_ref(v___y_2348_);
lean_dec_ref(v_as_2345_);
lean_dec_ref(v_ctx_2344_);
return v_res_2356_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__0(lean_object* v_as_2357_, size_t v_i_2358_, size_t v_stop_2359_, lean_object* v_b_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_){
_start:
{
lean_object* v_a_2367_; uint8_t v___x_2371_; 
v___x_2371_ = lean_usize_dec_eq(v_i_2358_, v_stop_2359_);
if (v___x_2371_ == 0)
{
lean_object* v_toInductionSubgoal_2372_; lean_object* v_ctorName_2373_; lean_object* v_mvarId_2374_; lean_object* v_fields_2375_; lean_object* v_subst_2376_; lean_object* v___x_2378_; uint8_t v_isShared_2379_; uint8_t v_isSharedCheck_2429_; 
v_toInductionSubgoal_2372_ = lean_ctor_get(v_b_2360_, 0);
lean_inc_ref(v_toInductionSubgoal_2372_);
v_ctorName_2373_ = lean_ctor_get(v_b_2360_, 1);
v_mvarId_2374_ = lean_ctor_get(v_toInductionSubgoal_2372_, 0);
v_fields_2375_ = lean_ctor_get(v_toInductionSubgoal_2372_, 1);
v_subst_2376_ = lean_ctor_get(v_toInductionSubgoal_2372_, 2);
v_isSharedCheck_2429_ = !lean_is_exclusive(v_toInductionSubgoal_2372_);
if (v_isSharedCheck_2429_ == 0)
{
v___x_2378_ = v_toInductionSubgoal_2372_;
v_isShared_2379_ = v_isSharedCheck_2429_;
goto v_resetjp_2377_;
}
else
{
lean_inc(v_subst_2376_);
lean_inc(v_fields_2375_);
lean_inc(v_mvarId_2374_);
lean_dec(v_toInductionSubgoal_2372_);
v___x_2378_ = lean_box(0);
v_isShared_2379_ = v_isSharedCheck_2429_;
goto v_resetjp_2377_;
}
v_resetjp_2377_:
{
lean_object* v___x_2380_; lean_object* v___x_2381_; 
v___x_2380_ = lean_array_uget_borrowed(v_as_2357_, v_i_2358_);
lean_inc(v___x_2380_);
v___x_2381_ = l_Lean_Meta_FVarSubst_get(v_subst_2376_, v___x_2380_);
if (lean_obj_tag(v___x_2381_) == 1)
{
lean_object* v_fvarId_2382_; lean_object* v___x_2383_; 
v_fvarId_2382_ = lean_ctor_get(v___x_2381_, 0);
lean_inc(v_fvarId_2382_);
lean_dec_ref_known(v___x_2381_, 1);
v___x_2383_ = l_Lean_Meta_saveState___redArg(v___y_2362_, v___y_2364_);
if (lean_obj_tag(v___x_2383_) == 0)
{
lean_object* v_a_2384_; lean_object* v___x_2385_; 
v_a_2384_ = lean_ctor_get(v___x_2383_, 0);
lean_inc(v_a_2384_);
lean_dec_ref_known(v___x_2383_, 1);
v___x_2385_ = l_Lean_MVarId_clear(v_mvarId_2374_, v_fvarId_2382_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_);
if (lean_obj_tag(v___x_2385_) == 0)
{
lean_object* v___x_2387_; uint8_t v_isShared_2388_; uint8_t v_isSharedCheck_2397_; 
lean_inc(v_ctorName_2373_);
lean_dec(v_a_2384_);
v_isSharedCheck_2397_ = !lean_is_exclusive(v_b_2360_);
if (v_isSharedCheck_2397_ == 0)
{
lean_object* v_unused_2398_; lean_object* v_unused_2399_; 
v_unused_2398_ = lean_ctor_get(v_b_2360_, 1);
lean_dec(v_unused_2398_);
v_unused_2399_ = lean_ctor_get(v_b_2360_, 0);
lean_dec(v_unused_2399_);
v___x_2387_ = v_b_2360_;
v_isShared_2388_ = v_isSharedCheck_2397_;
goto v_resetjp_2386_;
}
else
{
lean_dec(v_b_2360_);
v___x_2387_ = lean_box(0);
v_isShared_2388_ = v_isSharedCheck_2397_;
goto v_resetjp_2386_;
}
v_resetjp_2386_:
{
lean_object* v_a_2389_; lean_object* v___x_2390_; lean_object* v___x_2392_; 
v_a_2389_ = lean_ctor_get(v___x_2385_, 0);
lean_inc(v_a_2389_);
lean_dec_ref_known(v___x_2385_, 1);
v___x_2390_ = l_Lean_Meta_FVarSubst_erase(v_subst_2376_, v___x_2380_);
if (v_isShared_2379_ == 0)
{
lean_ctor_set(v___x_2378_, 2, v___x_2390_);
lean_ctor_set(v___x_2378_, 0, v_a_2389_);
v___x_2392_ = v___x_2378_;
goto v_reusejp_2391_;
}
else
{
lean_object* v_reuseFailAlloc_2396_; 
v_reuseFailAlloc_2396_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2396_, 0, v_a_2389_);
lean_ctor_set(v_reuseFailAlloc_2396_, 1, v_fields_2375_);
lean_ctor_set(v_reuseFailAlloc_2396_, 2, v___x_2390_);
v___x_2392_ = v_reuseFailAlloc_2396_;
goto v_reusejp_2391_;
}
v_reusejp_2391_:
{
lean_object* v___x_2394_; 
if (v_isShared_2388_ == 0)
{
lean_ctor_set(v___x_2387_, 0, v___x_2392_);
v___x_2394_ = v___x_2387_;
goto v_reusejp_2393_;
}
else
{
lean_object* v_reuseFailAlloc_2395_; 
v_reuseFailAlloc_2395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2395_, 0, v___x_2392_);
lean_ctor_set(v_reuseFailAlloc_2395_, 1, v_ctorName_2373_);
v___x_2394_ = v_reuseFailAlloc_2395_;
goto v_reusejp_2393_;
}
v_reusejp_2393_:
{
v_a_2367_ = v___x_2394_;
goto v___jp_2366_;
}
}
}
}
else
{
lean_object* v_a_2400_; lean_object* v___x_2402_; uint8_t v_isShared_2403_; uint8_t v_isSharedCheck_2420_; 
lean_del_object(v___x_2378_);
lean_dec(v_subst_2376_);
lean_dec_ref(v_fields_2375_);
v_a_2400_ = lean_ctor_get(v___x_2385_, 0);
v_isSharedCheck_2420_ = !lean_is_exclusive(v___x_2385_);
if (v_isSharedCheck_2420_ == 0)
{
v___x_2402_ = v___x_2385_;
v_isShared_2403_ = v_isSharedCheck_2420_;
goto v_resetjp_2401_;
}
else
{
lean_inc(v_a_2400_);
lean_dec(v___x_2385_);
v___x_2402_ = lean_box(0);
v_isShared_2403_ = v_isSharedCheck_2420_;
goto v_resetjp_2401_;
}
v_resetjp_2401_:
{
lean_object* v___x_2405_; 
lean_inc(v_a_2400_);
if (v_isShared_2403_ == 0)
{
v___x_2405_ = v___x_2402_;
goto v_reusejp_2404_;
}
else
{
lean_object* v_reuseFailAlloc_2419_; 
v_reuseFailAlloc_2419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2419_, 0, v_a_2400_);
v___x_2405_ = v_reuseFailAlloc_2419_;
goto v_reusejp_2404_;
}
v_reusejp_2404_:
{
uint8_t v___y_2407_; uint8_t v___x_2417_; 
v___x_2417_ = l_Lean_Exception_isInterrupt(v_a_2400_);
if (v___x_2417_ == 0)
{
uint8_t v___x_2418_; 
v___x_2418_ = l_Lean_Exception_isRuntime(v_a_2400_);
v___y_2407_ = v___x_2418_;
goto v___jp_2406_;
}
else
{
lean_dec(v_a_2400_);
v___y_2407_ = v___x_2417_;
goto v___jp_2406_;
}
v___jp_2406_:
{
if (v___y_2407_ == 0)
{
lean_object* v___x_2408_; 
lean_dec_ref(v___x_2405_);
v___x_2408_ = l_Lean_Meta_SavedState_restore___redArg(v_a_2384_, v___y_2362_, v___y_2364_);
lean_dec(v_a_2384_);
if (lean_obj_tag(v___x_2408_) == 0)
{
lean_dec_ref_known(v___x_2408_, 1);
v_a_2367_ = v_b_2360_;
goto v___jp_2366_;
}
else
{
lean_object* v_a_2409_; lean_object* v___x_2411_; uint8_t v_isShared_2412_; uint8_t v_isSharedCheck_2416_; 
lean_dec_ref(v_b_2360_);
v_a_2409_ = lean_ctor_get(v___x_2408_, 0);
v_isSharedCheck_2416_ = !lean_is_exclusive(v___x_2408_);
if (v_isSharedCheck_2416_ == 0)
{
v___x_2411_ = v___x_2408_;
v_isShared_2412_ = v_isSharedCheck_2416_;
goto v_resetjp_2410_;
}
else
{
lean_inc(v_a_2409_);
lean_dec(v___x_2408_);
v___x_2411_ = lean_box(0);
v_isShared_2412_ = v_isSharedCheck_2416_;
goto v_resetjp_2410_;
}
v_resetjp_2410_:
{
lean_object* v___x_2414_; 
if (v_isShared_2412_ == 0)
{
v___x_2414_ = v___x_2411_;
goto v_reusejp_2413_;
}
else
{
lean_object* v_reuseFailAlloc_2415_; 
v_reuseFailAlloc_2415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2415_, 0, v_a_2409_);
v___x_2414_ = v_reuseFailAlloc_2415_;
goto v_reusejp_2413_;
}
v_reusejp_2413_:
{
return v___x_2414_;
}
}
}
}
else
{
lean_dec(v_a_2384_);
lean_dec_ref(v_b_2360_);
return v___x_2405_;
}
}
}
}
}
}
else
{
lean_object* v_a_2421_; lean_object* v___x_2423_; uint8_t v_isShared_2424_; uint8_t v_isSharedCheck_2428_; 
lean_dec(v_fvarId_2382_);
lean_del_object(v___x_2378_);
lean_dec(v_subst_2376_);
lean_dec_ref(v_fields_2375_);
lean_dec(v_mvarId_2374_);
lean_dec_ref(v_b_2360_);
v_a_2421_ = lean_ctor_get(v___x_2383_, 0);
v_isSharedCheck_2428_ = !lean_is_exclusive(v___x_2383_);
if (v_isSharedCheck_2428_ == 0)
{
v___x_2423_ = v___x_2383_;
v_isShared_2424_ = v_isSharedCheck_2428_;
goto v_resetjp_2422_;
}
else
{
lean_inc(v_a_2421_);
lean_dec(v___x_2383_);
v___x_2423_ = lean_box(0);
v_isShared_2424_ = v_isSharedCheck_2428_;
goto v_resetjp_2422_;
}
v_resetjp_2422_:
{
lean_object* v___x_2426_; 
if (v_isShared_2424_ == 0)
{
v___x_2426_ = v___x_2423_;
goto v_reusejp_2425_;
}
else
{
lean_object* v_reuseFailAlloc_2427_; 
v_reuseFailAlloc_2427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2427_, 0, v_a_2421_);
v___x_2426_ = v_reuseFailAlloc_2427_;
goto v_reusejp_2425_;
}
v_reusejp_2425_:
{
return v___x_2426_;
}
}
}
}
else
{
lean_dec_ref(v___x_2381_);
lean_del_object(v___x_2378_);
lean_dec(v_subst_2376_);
lean_dec_ref(v_fields_2375_);
lean_dec(v_mvarId_2374_);
v_a_2367_ = v_b_2360_;
goto v___jp_2366_;
}
}
}
else
{
lean_object* v___x_2430_; 
v___x_2430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2430_, 0, v_b_2360_);
return v___x_2430_;
}
v___jp_2366_:
{
size_t v___x_2368_; size_t v___x_2369_; 
v___x_2368_ = ((size_t)1ULL);
v___x_2369_ = lean_usize_add(v_i_2358_, v___x_2368_);
v_i_2358_ = v___x_2369_;
v_b_2360_ = v_a_2367_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__0___boxed(lean_object* v_as_2431_, lean_object* v_i_2432_, lean_object* v_stop_2433_, lean_object* v_b_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_){
_start:
{
size_t v_i_boxed_2440_; size_t v_stop_boxed_2441_; lean_object* v_res_2442_; 
v_i_boxed_2440_ = lean_unbox_usize(v_i_2432_);
lean_dec(v_i_2432_);
v_stop_boxed_2441_ = lean_unbox_usize(v_stop_2433_);
lean_dec(v_stop_2433_);
v_res_2442_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__0(v_as_2431_, v_i_boxed_2440_, v_stop_boxed_2441_, v_b_2434_, v___y_2435_, v___y_2436_, v___y_2437_, v___y_2438_);
lean_dec(v___y_2438_);
lean_dec_ref(v___y_2437_);
lean_dec(v___y_2436_);
lean_dec_ref(v___y_2435_);
lean_dec_ref(v_as_2431_);
return v_res_2442_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__1(lean_object* v_indicesFVarIds_2443_, size_t v_sz_2444_, size_t v_i_2445_, lean_object* v_bs_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_){
_start:
{
uint8_t v___x_2452_; 
v___x_2452_ = lean_usize_dec_lt(v_i_2445_, v_sz_2444_);
if (v___x_2452_ == 0)
{
lean_object* v___x_2453_; 
v___x_2453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2453_, 0, v_bs_2446_);
return v___x_2453_;
}
else
{
lean_object* v_v_2454_; lean_object* v___x_2455_; lean_object* v_bs_x27_2456_; lean_object* v_a_2458_; lean_object* v___y_2464_; lean_object* v___x_2474_; uint8_t v___x_2475_; 
v_v_2454_ = lean_array_uget(v_bs_2446_, v_i_2445_);
v___x_2455_ = lean_unsigned_to_nat(0u);
v_bs_x27_2456_ = lean_array_uset(v_bs_2446_, v_i_2445_, v___x_2455_);
v___x_2474_ = lean_array_get_size(v_indicesFVarIds_2443_);
v___x_2475_ = lean_nat_dec_lt(v___x_2455_, v___x_2474_);
if (v___x_2475_ == 0)
{
v_a_2458_ = v_v_2454_;
goto v___jp_2457_;
}
else
{
uint8_t v___x_2476_; 
v___x_2476_ = lean_nat_dec_le(v___x_2474_, v___x_2474_);
if (v___x_2476_ == 0)
{
if (v___x_2475_ == 0)
{
v_a_2458_ = v_v_2454_;
goto v___jp_2457_;
}
else
{
size_t v___x_2477_; size_t v___x_2478_; lean_object* v___x_2479_; 
v___x_2477_ = ((size_t)0ULL);
v___x_2478_ = lean_usize_of_nat(v___x_2474_);
v___x_2479_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__0(v_indicesFVarIds_2443_, v___x_2477_, v___x_2478_, v_v_2454_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_);
v___y_2464_ = v___x_2479_;
goto v___jp_2463_;
}
}
else
{
size_t v___x_2480_; size_t v___x_2481_; lean_object* v___x_2482_; 
v___x_2480_ = ((size_t)0ULL);
v___x_2481_ = lean_usize_of_nat(v___x_2474_);
v___x_2482_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__0(v_indicesFVarIds_2443_, v___x_2480_, v___x_2481_, v_v_2454_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_);
v___y_2464_ = v___x_2482_;
goto v___jp_2463_;
}
}
v___jp_2457_:
{
size_t v___x_2459_; size_t v___x_2460_; lean_object* v___x_2461_; 
v___x_2459_ = ((size_t)1ULL);
v___x_2460_ = lean_usize_add(v_i_2445_, v___x_2459_);
v___x_2461_ = lean_array_uset(v_bs_x27_2456_, v_i_2445_, v_a_2458_);
v_i_2445_ = v___x_2460_;
v_bs_2446_ = v___x_2461_;
goto _start;
}
v___jp_2463_:
{
if (lean_obj_tag(v___y_2464_) == 0)
{
lean_object* v_a_2465_; 
v_a_2465_ = lean_ctor_get(v___y_2464_, 0);
lean_inc(v_a_2465_);
lean_dec_ref_known(v___y_2464_, 1);
v_a_2458_ = v_a_2465_;
goto v___jp_2457_;
}
else
{
lean_object* v_a_2466_; lean_object* v___x_2468_; uint8_t v_isShared_2469_; uint8_t v_isSharedCheck_2473_; 
lean_dec_ref(v_bs_x27_2456_);
v_a_2466_ = lean_ctor_get(v___y_2464_, 0);
v_isSharedCheck_2473_ = !lean_is_exclusive(v___y_2464_);
if (v_isSharedCheck_2473_ == 0)
{
v___x_2468_ = v___y_2464_;
v_isShared_2469_ = v_isSharedCheck_2473_;
goto v_resetjp_2467_;
}
else
{
lean_inc(v_a_2466_);
lean_dec(v___y_2464_);
v___x_2468_ = lean_box(0);
v_isShared_2469_ = v_isSharedCheck_2473_;
goto v_resetjp_2467_;
}
v_resetjp_2467_:
{
lean_object* v___x_2471_; 
if (v_isShared_2469_ == 0)
{
v___x_2471_ = v___x_2468_;
goto v_reusejp_2470_;
}
else
{
lean_object* v_reuseFailAlloc_2472_; 
v_reuseFailAlloc_2472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2472_, 0, v_a_2466_);
v___x_2471_ = v_reuseFailAlloc_2472_;
goto v_reusejp_2470_;
}
v_reusejp_2470_:
{
return v___x_2471_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__1___boxed(lean_object* v_indicesFVarIds_2483_, lean_object* v_sz_2484_, lean_object* v_i_2485_, lean_object* v_bs_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_){
_start:
{
size_t v_sz_boxed_2492_; size_t v_i_boxed_2493_; lean_object* v_res_2494_; 
v_sz_boxed_2492_ = lean_unbox_usize(v_sz_2484_);
lean_dec(v_sz_2484_);
v_i_boxed_2493_ = lean_unbox_usize(v_i_2485_);
lean_dec(v_i_2485_);
v_res_2494_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__1(v_indicesFVarIds_2483_, v_sz_boxed_2492_, v_i_boxed_2493_, v_bs_2486_, v___y_2487_, v___y_2488_, v___y_2489_, v___y_2490_);
lean_dec(v___y_2490_);
lean_dec_ref(v___y_2489_);
lean_dec(v___y_2488_);
lean_dec_ref(v___y_2487_);
lean_dec_ref(v_indicesFVarIds_2483_);
return v_res_2494_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices(lean_object* v_s_u2081_2495_, lean_object* v_s_u2082_2496_, lean_object* v_a_2497_, lean_object* v_a_2498_, lean_object* v_a_2499_, lean_object* v_a_2500_){
_start:
{
lean_object* v_indicesFVarIds_2502_; size_t v_sz_2503_; size_t v___x_2504_; lean_object* v___x_2505_; 
v_indicesFVarIds_2502_ = lean_ctor_get(v_s_u2081_2495_, 1);
v_sz_2503_ = lean_array_size(v_s_u2082_2496_);
v___x_2504_ = ((size_t)0ULL);
v___x_2505_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__1(v_indicesFVarIds_2502_, v_sz_2503_, v___x_2504_, v_s_u2082_2496_, v_a_2497_, v_a_2498_, v_a_2499_, v_a_2500_);
return v___x_2505_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices___boxed(lean_object* v_s_u2081_2506_, lean_object* v_s_u2082_2507_, lean_object* v_a_2508_, lean_object* v_a_2509_, lean_object* v_a_2510_, lean_object* v_a_2511_, lean_object* v_a_2512_){
_start:
{
lean_object* v_res_2513_; 
v_res_2513_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices(v_s_u2081_2506_, v_s_u2082_2507_, v_a_2508_, v_a_2509_, v_a_2510_, v_a_2511_);
lean_dec(v_a_2511_);
lean_dec_ref(v_a_2510_);
lean_dec(v_a_2509_);
lean_dec_ref(v_a_2508_);
lean_dec_ref(v_s_u2081_2506_);
return v_res_2513_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0___redArg(lean_object* v_ctorNames_2514_, lean_object* v_us_2515_, lean_object* v_params_2516_, lean_object* v_majorFVarId_2517_, size_t v_sz_2518_, size_t v_i_2519_, lean_object* v_bs_2520_){
_start:
{
uint8_t v___x_2521_; 
v___x_2521_ = lean_usize_dec_lt(v_i_2519_, v_sz_2518_);
if (v___x_2521_ == 0)
{
lean_dec(v_majorFVarId_2517_);
lean_dec(v_us_2515_);
return v_bs_2520_;
}
else
{
lean_object* v_v_2522_; lean_object* v___x_2523_; lean_object* v_bs_x27_2524_; lean_object* v___y_2526_; lean_object* v___x_2531_; lean_object* v___x_2532_; uint8_t v___x_2533_; 
v_v_2522_ = lean_array_uget(v_bs_2520_, v_i_2519_);
v___x_2523_ = lean_unsigned_to_nat(0u);
v_bs_x27_2524_ = lean_array_uset(v_bs_2520_, v_i_2519_, v___x_2523_);
v___x_2531_ = lean_usize_to_nat(v_i_2519_);
v___x_2532_ = lean_array_get_size(v_ctorNames_2514_);
v___x_2533_ = lean_nat_dec_lt(v___x_2531_, v___x_2532_);
if (v___x_2533_ == 0)
{
lean_object* v___x_2534_; lean_object* v___x_2535_; 
lean_dec(v___x_2531_);
v___x_2534_ = lean_box(0);
v___x_2535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2535_, 0, v_v_2522_);
lean_ctor_set(v___x_2535_, 1, v___x_2534_);
v___y_2526_ = v___x_2535_;
goto v___jp_2525_;
}
else
{
lean_object* v_mvarId_2536_; lean_object* v_fields_2537_; lean_object* v_subst_2538_; lean_object* v___x_2540_; uint8_t v_isShared_2541_; uint8_t v_isSharedCheck_2553_; 
v_mvarId_2536_ = lean_ctor_get(v_v_2522_, 0);
v_fields_2537_ = lean_ctor_get(v_v_2522_, 1);
v_subst_2538_ = lean_ctor_get(v_v_2522_, 2);
v_isSharedCheck_2553_ = !lean_is_exclusive(v_v_2522_);
if (v_isSharedCheck_2553_ == 0)
{
v___x_2540_ = v_v_2522_;
v_isShared_2541_ = v_isSharedCheck_2553_;
goto v_resetjp_2539_;
}
else
{
lean_inc(v_subst_2538_);
lean_inc(v_fields_2537_);
lean_inc(v_mvarId_2536_);
lean_dec(v_v_2522_);
v___x_2540_ = lean_box(0);
v_isShared_2541_ = v_isSharedCheck_2553_;
goto v_resetjp_2539_;
}
v_resetjp_2539_:
{
lean_object* v_ctorName_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v_ctorApp_2545_; lean_object* v___x_2546_; lean_object* v_subst_2547_; lean_object* v___x_2549_; 
v_ctorName_2542_ = lean_array_fget_borrowed(v_ctorNames_2514_, v___x_2531_);
lean_dec(v___x_2531_);
lean_inc(v_us_2515_);
lean_inc(v_ctorName_2542_);
v___x_2543_ = l_Lean_mkConst(v_ctorName_2542_, v_us_2515_);
v___x_2544_ = l_Lean_mkAppN(v___x_2543_, v_params_2516_);
v_ctorApp_2545_ = l_Lean_mkAppN(v___x_2544_, v_fields_2537_);
v___x_2546_ = l_Lean_Meta_FVarSubst_erase(v_subst_2538_, v_majorFVarId_2517_);
lean_inc(v_majorFVarId_2517_);
v_subst_2547_ = l_Lean_Meta_FVarSubst_insert(v___x_2546_, v_majorFVarId_2517_, v_ctorApp_2545_);
if (v_isShared_2541_ == 0)
{
lean_ctor_set(v___x_2540_, 2, v_subst_2547_);
v___x_2549_ = v___x_2540_;
goto v_reusejp_2548_;
}
else
{
lean_object* v_reuseFailAlloc_2552_; 
v_reuseFailAlloc_2552_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2552_, 0, v_mvarId_2536_);
lean_ctor_set(v_reuseFailAlloc_2552_, 1, v_fields_2537_);
lean_ctor_set(v_reuseFailAlloc_2552_, 2, v_subst_2547_);
v___x_2549_ = v_reuseFailAlloc_2552_;
goto v_reusejp_2548_;
}
v_reusejp_2548_:
{
lean_object* v___x_2550_; lean_object* v___x_2551_; 
lean_inc(v_ctorName_2542_);
v___x_2550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2550_, 0, v_ctorName_2542_);
v___x_2551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2551_, 0, v___x_2549_);
lean_ctor_set(v___x_2551_, 1, v___x_2550_);
v___y_2526_ = v___x_2551_;
goto v___jp_2525_;
}
}
}
v___jp_2525_:
{
size_t v___x_2527_; size_t v___x_2528_; lean_object* v___x_2529_; 
v___x_2527_ = ((size_t)1ULL);
v___x_2528_ = lean_usize_add(v_i_2519_, v___x_2527_);
v___x_2529_ = lean_array_uset(v_bs_x27_2524_, v_i_2519_, v___y_2526_);
v_i_2519_ = v___x_2528_;
v_bs_2520_ = v___x_2529_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0___redArg___boxed(lean_object* v_ctorNames_2554_, lean_object* v_us_2555_, lean_object* v_params_2556_, lean_object* v_majorFVarId_2557_, lean_object* v_sz_2558_, lean_object* v_i_2559_, lean_object* v_bs_2560_){
_start:
{
size_t v_sz_boxed_2561_; size_t v_i_boxed_2562_; lean_object* v_res_2563_; 
v_sz_boxed_2561_ = lean_unbox_usize(v_sz_2558_);
lean_dec(v_sz_2558_);
v_i_boxed_2562_ = lean_unbox_usize(v_i_2559_);
lean_dec(v_i_2559_);
v_res_2563_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0___redArg(v_ctorNames_2554_, v_us_2555_, v_params_2556_, v_majorFVarId_2557_, v_sz_boxed_2561_, v_i_boxed_2562_, v_bs_2560_);
lean_dec_ref(v_params_2556_);
lean_dec_ref(v_ctorNames_2554_);
return v_res_2563_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals(lean_object* v_s_2564_, lean_object* v_ctorNames_2565_, lean_object* v_majorFVarId_2566_, lean_object* v_us_2567_, lean_object* v_params_2568_){
_start:
{
size_t v_sz_2569_; size_t v___x_2570_; lean_object* v___x_2571_; 
v_sz_2569_ = lean_array_size(v_s_2564_);
v___x_2570_ = ((size_t)0ULL);
v___x_2571_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0___redArg(v_ctorNames_2565_, v_us_2567_, v_params_2568_, v_majorFVarId_2566_, v_sz_2569_, v___x_2570_, v_s_2564_);
return v___x_2571_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals___boxed(lean_object* v_s_2572_, lean_object* v_ctorNames_2573_, lean_object* v_majorFVarId_2574_, lean_object* v_us_2575_, lean_object* v_params_2576_){
_start:
{
lean_object* v_res_2577_; 
v_res_2577_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals(v_s_2572_, v_ctorNames_2573_, v_majorFVarId_2574_, v_us_2575_, v_params_2576_);
lean_dec_ref(v_params_2576_);
lean_dec_ref(v_ctorNames_2573_);
return v_res_2577_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0(lean_object* v_ctorNames_2578_, lean_object* v_us_2579_, lean_object* v_params_2580_, lean_object* v_majorFVarId_2581_, lean_object* v_as_2582_, size_t v_sz_2583_, size_t v_i_2584_, lean_object* v_bs_2585_){
_start:
{
lean_object* v___x_2586_; 
v___x_2586_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0___redArg(v_ctorNames_2578_, v_us_2579_, v_params_2580_, v_majorFVarId_2581_, v_sz_2583_, v_i_2584_, v_bs_2585_);
return v___x_2586_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0___boxed(lean_object* v_ctorNames_2587_, lean_object* v_us_2588_, lean_object* v_params_2589_, lean_object* v_majorFVarId_2590_, lean_object* v_as_2591_, lean_object* v_sz_2592_, lean_object* v_i_2593_, lean_object* v_bs_2594_){
_start:
{
size_t v_sz_boxed_2595_; size_t v_i_boxed_2596_; lean_object* v_res_2597_; 
v_sz_boxed_2595_ = lean_unbox_usize(v_sz_2592_);
lean_dec(v_sz_2592_);
v_i_boxed_2596_ = lean_unbox_usize(v_i_2593_);
lean_dec(v_i_2593_);
v_res_2597_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0(v_ctorNames_2587_, v_us_2588_, v_params_2589_, v_majorFVarId_2590_, v_as_2591_, v_sz_boxed_2595_, v_i_boxed_2596_, v_bs_2594_);
lean_dec_ref(v_as_2591_);
lean_dec_ref(v_params_2589_);
lean_dec_ref(v_ctorNames_2587_);
return v_res_2597_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_2603_; lean_object* v___x_2604_; 
v___x_2603_ = l_Lean_maxRecDepthErrorMessage;
v___x_2604_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2604_, 0, v___x_2603_);
return v___x_2604_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_2605_; lean_object* v___x_2606_; 
v___x_2605_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__3);
v___x_2606_ = l_Lean_MessageData_ofFormat(v___x_2605_);
return v___x_2606_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; 
v___x_2607_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__4);
v___x_2608_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__2));
v___x_2609_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2609_, 0, v___x_2608_);
lean_ctor_set(v___x_2609_, 1, v___x_2607_);
return v___x_2609_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg(lean_object* v_ref_2610_){
_start:
{
lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; 
v___x_2612_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__5);
v___x_2613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2613_, 0, v_ref_2610_);
lean_ctor_set(v___x_2613_, 1, v___x_2612_);
v___x_2614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2614_, 0, v___x_2613_);
return v___x_2614_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___boxed(lean_object* v_ref_2615_, lean_object* v___y_2616_){
_start:
{
lean_object* v_res_2617_; 
v_res_2617_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg(v_ref_2615_);
return v_res_2617_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0(lean_object* v_00_u03b1_2618_, lean_object* v_ref_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_){
_start:
{
lean_object* v___x_2625_; 
v___x_2625_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg(v_ref_2619_);
return v___x_2625_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___boxed(lean_object* v_00_u03b1_2626_, lean_object* v_ref_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_){
_start:
{
lean_object* v_res_2633_; 
v_res_2633_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0(v_00_u03b1_2626_, v_ref_2627_, v___y_2628_, v___y_2629_, v___y_2630_, v___y_2631_);
lean_dec(v___y_2631_);
lean_dec_ref(v___y_2630_);
lean_dec(v___y_2629_);
lean_dec_ref(v___y_2628_);
return v_res_2633_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_unifyEqs_x3f(lean_object* v_numEqs_2635_, lean_object* v_mvarId_2636_, lean_object* v_subst_2637_, lean_object* v_caseName_x3f_2638_, lean_object* v_a_2639_, lean_object* v_a_2640_, lean_object* v_a_2641_, lean_object* v_a_2642_){
_start:
{
lean_object* v_fileName_2644_; lean_object* v_fileMap_2645_; lean_object* v_options_2646_; lean_object* v_currRecDepth_2647_; lean_object* v_maxRecDepth_2648_; lean_object* v_ref_2649_; lean_object* v_currNamespace_2650_; lean_object* v_openDecls_2651_; lean_object* v_initHeartbeats_2652_; lean_object* v_maxHeartbeats_2653_; lean_object* v_quotContext_2654_; lean_object* v_currMacroScope_2655_; uint8_t v_diag_2656_; lean_object* v_cancelTk_x3f_2657_; uint8_t v_suppressElabErrors_2658_; lean_object* v_inheritedTraceOptions_2659_; lean_object* v___x_2660_; uint8_t v___x_2661_; uint8_t v___x_2707_; 
v_fileName_2644_ = lean_ctor_get(v_a_2641_, 0);
lean_inc_ref(v_fileName_2644_);
v_fileMap_2645_ = lean_ctor_get(v_a_2641_, 1);
lean_inc_ref(v_fileMap_2645_);
v_options_2646_ = lean_ctor_get(v_a_2641_, 2);
lean_inc_ref(v_options_2646_);
v_currRecDepth_2647_ = lean_ctor_get(v_a_2641_, 3);
lean_inc(v_currRecDepth_2647_);
v_maxRecDepth_2648_ = lean_ctor_get(v_a_2641_, 4);
lean_inc(v_maxRecDepth_2648_);
v_ref_2649_ = lean_ctor_get(v_a_2641_, 5);
lean_inc(v_ref_2649_);
v_currNamespace_2650_ = lean_ctor_get(v_a_2641_, 6);
lean_inc(v_currNamespace_2650_);
v_openDecls_2651_ = lean_ctor_get(v_a_2641_, 7);
lean_inc(v_openDecls_2651_);
v_initHeartbeats_2652_ = lean_ctor_get(v_a_2641_, 8);
lean_inc(v_initHeartbeats_2652_);
v_maxHeartbeats_2653_ = lean_ctor_get(v_a_2641_, 9);
lean_inc(v_maxHeartbeats_2653_);
v_quotContext_2654_ = lean_ctor_get(v_a_2641_, 10);
lean_inc(v_quotContext_2654_);
v_currMacroScope_2655_ = lean_ctor_get(v_a_2641_, 11);
lean_inc(v_currMacroScope_2655_);
v_diag_2656_ = lean_ctor_get_uint8(v_a_2641_, sizeof(void*)*14);
v_cancelTk_x3f_2657_ = lean_ctor_get(v_a_2641_, 12);
lean_inc(v_cancelTk_x3f_2657_);
v_suppressElabErrors_2658_ = lean_ctor_get_uint8(v_a_2641_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2659_ = lean_ctor_get(v_a_2641_, 13);
lean_inc_ref(v_inheritedTraceOptions_2659_);
lean_dec_ref(v_a_2641_);
v___x_2660_ = lean_unsigned_to_nat(0u);
v___x_2661_ = lean_nat_dec_eq(v_numEqs_2635_, v___x_2660_);
v___x_2707_ = lean_nat_dec_eq(v_maxRecDepth_2648_, v___x_2660_);
if (v___x_2707_ == 0)
{
uint8_t v___x_2708_; 
v___x_2708_ = lean_nat_dec_eq(v_currRecDepth_2647_, v_maxRecDepth_2648_);
if (v___x_2708_ == 0)
{
goto v___jp_2662_;
}
else
{
lean_object* v___x_2709_; 
lean_dec_ref(v_inheritedTraceOptions_2659_);
lean_dec(v_cancelTk_x3f_2657_);
lean_dec(v_currMacroScope_2655_);
lean_dec(v_quotContext_2654_);
lean_dec(v_maxHeartbeats_2653_);
lean_dec(v_initHeartbeats_2652_);
lean_dec(v_openDecls_2651_);
lean_dec(v_currNamespace_2650_);
lean_dec(v_maxRecDepth_2648_);
lean_dec(v_currRecDepth_2647_);
lean_dec_ref(v_options_2646_);
lean_dec_ref(v_fileMap_2645_);
lean_dec_ref(v_fileName_2644_);
lean_dec(v_caseName_x3f_2638_);
lean_dec(v_subst_2637_);
lean_dec(v_mvarId_2636_);
lean_dec(v_numEqs_2635_);
v___x_2709_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg(v_ref_2649_);
return v___x_2709_;
}
}
else
{
goto v___jp_2662_;
}
v___jp_2662_:
{
if (v___x_2661_ == 0)
{
lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; 
v___x_2663_ = lean_unsigned_to_nat(1u);
v___x_2664_ = lean_nat_add(v_currRecDepth_2647_, v___x_2663_);
lean_dec(v_currRecDepth_2647_);
v___x_2665_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2665_, 0, v_fileName_2644_);
lean_ctor_set(v___x_2665_, 1, v_fileMap_2645_);
lean_ctor_set(v___x_2665_, 2, v_options_2646_);
lean_ctor_set(v___x_2665_, 3, v___x_2664_);
lean_ctor_set(v___x_2665_, 4, v_maxRecDepth_2648_);
lean_ctor_set(v___x_2665_, 5, v_ref_2649_);
lean_ctor_set(v___x_2665_, 6, v_currNamespace_2650_);
lean_ctor_set(v___x_2665_, 7, v_openDecls_2651_);
lean_ctor_set(v___x_2665_, 8, v_initHeartbeats_2652_);
lean_ctor_set(v___x_2665_, 9, v_maxHeartbeats_2653_);
lean_ctor_set(v___x_2665_, 10, v_quotContext_2654_);
lean_ctor_set(v___x_2665_, 11, v_currMacroScope_2655_);
lean_ctor_set(v___x_2665_, 12, v_cancelTk_x3f_2657_);
lean_ctor_set(v___x_2665_, 13, v_inheritedTraceOptions_2659_);
lean_ctor_set_uint8(v___x_2665_, sizeof(void*)*14, v_diag_2656_);
lean_ctor_set_uint8(v___x_2665_, sizeof(void*)*14 + 1, v_suppressElabErrors_2658_);
v___x_2666_ = l_Lean_Meta_intro1Core(v_mvarId_2636_, v___x_2661_, v_a_2639_, v_a_2640_, v___x_2665_, v_a_2642_);
if (lean_obj_tag(v___x_2666_) == 0)
{
lean_object* v_a_2667_; lean_object* v_fst_2668_; lean_object* v_snd_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; 
v_a_2667_ = lean_ctor_get(v___x_2666_, 0);
lean_inc(v_a_2667_);
lean_dec_ref_known(v___x_2666_, 1);
v_fst_2668_ = lean_ctor_get(v_a_2667_, 0);
lean_inc(v_fst_2668_);
v_snd_2669_ = lean_ctor_get(v_a_2667_, 1);
lean_inc(v_snd_2669_);
lean_dec(v_a_2667_);
v___x_2670_ = ((lean_object*)(l_Lean_Meta_Cases_unifyEqs_x3f___closed__0));
lean_inc(v_caseName_x3f_2638_);
v___x_2671_ = l_Lean_Meta_unifyEq_x3f(v_snd_2669_, v_fst_2668_, v_subst_2637_, v___x_2670_, v_caseName_x3f_2638_, v_a_2639_, v_a_2640_, v___x_2665_, v_a_2642_);
if (lean_obj_tag(v___x_2671_) == 0)
{
lean_object* v_a_2672_; lean_object* v___x_2674_; uint8_t v_isShared_2675_; uint8_t v_isSharedCheck_2687_; 
v_a_2672_ = lean_ctor_get(v___x_2671_, 0);
v_isSharedCheck_2687_ = !lean_is_exclusive(v___x_2671_);
if (v_isSharedCheck_2687_ == 0)
{
v___x_2674_ = v___x_2671_;
v_isShared_2675_ = v_isSharedCheck_2687_;
goto v_resetjp_2673_;
}
else
{
lean_inc(v_a_2672_);
lean_dec(v___x_2671_);
v___x_2674_ = lean_box(0);
v_isShared_2675_ = v_isSharedCheck_2687_;
goto v_resetjp_2673_;
}
v_resetjp_2673_:
{
if (lean_obj_tag(v_a_2672_) == 1)
{
lean_object* v_val_2676_; lean_object* v_mvarId_2677_; lean_object* v_subst_2678_; lean_object* v_numNewEqs_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; 
lean_del_object(v___x_2674_);
v_val_2676_ = lean_ctor_get(v_a_2672_, 0);
lean_inc(v_val_2676_);
lean_dec_ref_known(v_a_2672_, 1);
v_mvarId_2677_ = lean_ctor_get(v_val_2676_, 0);
lean_inc(v_mvarId_2677_);
v_subst_2678_ = lean_ctor_get(v_val_2676_, 1);
lean_inc(v_subst_2678_);
v_numNewEqs_2679_ = lean_ctor_get(v_val_2676_, 2);
lean_inc(v_numNewEqs_2679_);
lean_dec(v_val_2676_);
v___x_2680_ = lean_nat_sub(v_numEqs_2635_, v___x_2663_);
lean_dec(v_numEqs_2635_);
v___x_2681_ = lean_nat_add(v___x_2680_, v_numNewEqs_2679_);
lean_dec(v_numNewEqs_2679_);
lean_dec(v___x_2680_);
v_numEqs_2635_ = v___x_2681_;
v_mvarId_2636_ = v_mvarId_2677_;
v_subst_2637_ = v_subst_2678_;
v_a_2641_ = v___x_2665_;
goto _start;
}
else
{
lean_object* v___x_2683_; lean_object* v___x_2685_; 
lean_dec(v_a_2672_);
lean_dec_ref_known(v___x_2665_, 14);
lean_dec(v_caseName_x3f_2638_);
lean_dec(v_numEqs_2635_);
v___x_2683_ = lean_box(0);
if (v_isShared_2675_ == 0)
{
lean_ctor_set(v___x_2674_, 0, v___x_2683_);
v___x_2685_ = v___x_2674_;
goto v_reusejp_2684_;
}
else
{
lean_object* v_reuseFailAlloc_2686_; 
v_reuseFailAlloc_2686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2686_, 0, v___x_2683_);
v___x_2685_ = v_reuseFailAlloc_2686_;
goto v_reusejp_2684_;
}
v_reusejp_2684_:
{
return v___x_2685_;
}
}
}
}
else
{
lean_object* v_a_2688_; lean_object* v___x_2690_; uint8_t v_isShared_2691_; uint8_t v_isSharedCheck_2695_; 
lean_dec_ref_known(v___x_2665_, 14);
lean_dec(v_caseName_x3f_2638_);
lean_dec(v_numEqs_2635_);
v_a_2688_ = lean_ctor_get(v___x_2671_, 0);
v_isSharedCheck_2695_ = !lean_is_exclusive(v___x_2671_);
if (v_isSharedCheck_2695_ == 0)
{
v___x_2690_ = v___x_2671_;
v_isShared_2691_ = v_isSharedCheck_2695_;
goto v_resetjp_2689_;
}
else
{
lean_inc(v_a_2688_);
lean_dec(v___x_2671_);
v___x_2690_ = lean_box(0);
v_isShared_2691_ = v_isSharedCheck_2695_;
goto v_resetjp_2689_;
}
v_resetjp_2689_:
{
lean_object* v___x_2693_; 
if (v_isShared_2691_ == 0)
{
v___x_2693_ = v___x_2690_;
goto v_reusejp_2692_;
}
else
{
lean_object* v_reuseFailAlloc_2694_; 
v_reuseFailAlloc_2694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2694_, 0, v_a_2688_);
v___x_2693_ = v_reuseFailAlloc_2694_;
goto v_reusejp_2692_;
}
v_reusejp_2692_:
{
return v___x_2693_;
}
}
}
}
else
{
lean_object* v_a_2696_; lean_object* v___x_2698_; uint8_t v_isShared_2699_; uint8_t v_isSharedCheck_2703_; 
lean_dec_ref_known(v___x_2665_, 14);
lean_dec(v_caseName_x3f_2638_);
lean_dec(v_subst_2637_);
lean_dec(v_numEqs_2635_);
v_a_2696_ = lean_ctor_get(v___x_2666_, 0);
v_isSharedCheck_2703_ = !lean_is_exclusive(v___x_2666_);
if (v_isSharedCheck_2703_ == 0)
{
v___x_2698_ = v___x_2666_;
v_isShared_2699_ = v_isSharedCheck_2703_;
goto v_resetjp_2697_;
}
else
{
lean_inc(v_a_2696_);
lean_dec(v___x_2666_);
v___x_2698_ = lean_box(0);
v_isShared_2699_ = v_isSharedCheck_2703_;
goto v_resetjp_2697_;
}
v_resetjp_2697_:
{
lean_object* v___x_2701_; 
if (v_isShared_2699_ == 0)
{
v___x_2701_ = v___x_2698_;
goto v_reusejp_2700_;
}
else
{
lean_object* v_reuseFailAlloc_2702_; 
v_reuseFailAlloc_2702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2702_, 0, v_a_2696_);
v___x_2701_ = v_reuseFailAlloc_2702_;
goto v_reusejp_2700_;
}
v_reusejp_2700_:
{
return v___x_2701_;
}
}
}
}
else
{
lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; 
lean_dec_ref(v_inheritedTraceOptions_2659_);
lean_dec(v_cancelTk_x3f_2657_);
lean_dec(v_currMacroScope_2655_);
lean_dec(v_quotContext_2654_);
lean_dec(v_maxHeartbeats_2653_);
lean_dec(v_initHeartbeats_2652_);
lean_dec(v_openDecls_2651_);
lean_dec(v_currNamespace_2650_);
lean_dec(v_ref_2649_);
lean_dec(v_maxRecDepth_2648_);
lean_dec(v_currRecDepth_2647_);
lean_dec_ref(v_options_2646_);
lean_dec_ref(v_fileMap_2645_);
lean_dec_ref(v_fileName_2644_);
lean_dec(v_caseName_x3f_2638_);
lean_dec(v_numEqs_2635_);
v___x_2704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2704_, 0, v_mvarId_2636_);
lean_ctor_set(v___x_2704_, 1, v_subst_2637_);
v___x_2705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2705_, 0, v___x_2704_);
v___x_2706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2706_, 0, v___x_2705_);
return v___x_2706_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_unifyEqs_x3f___boxed(lean_object* v_numEqs_2710_, lean_object* v_mvarId_2711_, lean_object* v_subst_2712_, lean_object* v_caseName_x3f_2713_, lean_object* v_a_2714_, lean_object* v_a_2715_, lean_object* v_a_2716_, lean_object* v_a_2717_, lean_object* v_a_2718_){
_start:
{
lean_object* v_res_2719_; 
v_res_2719_ = l_Lean_Meta_Cases_unifyEqs_x3f(v_numEqs_2710_, v_mvarId_2711_, v_subst_2712_, v_caseName_x3f_2713_, v_a_2714_, v_a_2715_, v_a_2716_, v_a_2717_);
lean_dec(v_a_2717_);
lean_dec(v_a_2715_);
lean_dec_ref(v_a_2714_);
return v_res_2719_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__0(lean_object* v_snd_2720_, size_t v_sz_2721_, size_t v_i_2722_, lean_object* v_bs_2723_){
_start:
{
uint8_t v___x_2724_; 
v___x_2724_ = lean_usize_dec_lt(v_i_2722_, v_sz_2721_);
if (v___x_2724_ == 0)
{
lean_dec(v_snd_2720_);
return v_bs_2723_;
}
else
{
lean_object* v_v_2725_; lean_object* v___x_2726_; lean_object* v_bs_x27_2727_; lean_object* v___x_2728_; size_t v___x_2729_; size_t v___x_2730_; lean_object* v___x_2731_; 
v_v_2725_ = lean_array_uget(v_bs_2723_, v_i_2722_);
v___x_2726_ = lean_unsigned_to_nat(0u);
v_bs_x27_2727_ = lean_array_uset(v_bs_2723_, v_i_2722_, v___x_2726_);
lean_inc(v_snd_2720_);
v___x_2728_ = l_Lean_Meta_FVarSubst_apply(v_snd_2720_, v_v_2725_);
lean_dec(v_v_2725_);
v___x_2729_ = ((size_t)1ULL);
v___x_2730_ = lean_usize_add(v_i_2722_, v___x_2729_);
v___x_2731_ = lean_array_uset(v_bs_x27_2727_, v_i_2722_, v___x_2728_);
v_i_2722_ = v___x_2730_;
v_bs_2723_ = v___x_2731_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__0___boxed(lean_object* v_snd_2733_, lean_object* v_sz_2734_, lean_object* v_i_2735_, lean_object* v_bs_2736_){
_start:
{
size_t v_sz_boxed_2737_; size_t v_i_boxed_2738_; lean_object* v_res_2739_; 
v_sz_boxed_2737_ = lean_unbox_usize(v_sz_2734_);
lean_dec(v_sz_2734_);
v_i_boxed_2738_ = lean_unbox_usize(v_i_2735_);
lean_dec(v_i_2735_);
v_res_2739_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__0(v_snd_2733_, v_sz_boxed_2737_, v_i_boxed_2738_, v_bs_2736_);
return v_res_2739_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1_spec__1(lean_object* v_numEqs_2740_, lean_object* v_as_2741_, size_t v_i_2742_, size_t v_stop_2743_, lean_object* v_b_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_){
_start:
{
uint8_t v___x_2750_; 
v___x_2750_ = lean_usize_dec_eq(v_i_2742_, v_stop_2743_);
if (v___x_2750_ == 0)
{
lean_object* v___x_2751_; lean_object* v_toInductionSubgoal_2752_; lean_object* v_ctorName_2753_; lean_object* v___x_2755_; uint8_t v_isShared_2756_; uint8_t v_isSharedCheck_2792_; 
v___x_2751_ = lean_array_uget(v_as_2741_, v_i_2742_);
v_toInductionSubgoal_2752_ = lean_ctor_get(v___x_2751_, 0);
v_ctorName_2753_ = lean_ctor_get(v___x_2751_, 1);
v_isSharedCheck_2792_ = !lean_is_exclusive(v___x_2751_);
if (v_isSharedCheck_2792_ == 0)
{
v___x_2755_ = v___x_2751_;
v_isShared_2756_ = v_isSharedCheck_2792_;
goto v_resetjp_2754_;
}
else
{
lean_inc(v_ctorName_2753_);
lean_inc(v_toInductionSubgoal_2752_);
lean_dec(v___x_2751_);
v___x_2755_ = lean_box(0);
v_isShared_2756_ = v_isSharedCheck_2792_;
goto v_resetjp_2754_;
}
v_resetjp_2754_:
{
lean_object* v_mvarId_2757_; lean_object* v_fields_2758_; lean_object* v_subst_2759_; lean_object* v___x_2761_; uint8_t v_isShared_2762_; uint8_t v_isSharedCheck_2791_; 
v_mvarId_2757_ = lean_ctor_get(v_toInductionSubgoal_2752_, 0);
v_fields_2758_ = lean_ctor_get(v_toInductionSubgoal_2752_, 1);
v_subst_2759_ = lean_ctor_get(v_toInductionSubgoal_2752_, 2);
v_isSharedCheck_2791_ = !lean_is_exclusive(v_toInductionSubgoal_2752_);
if (v_isSharedCheck_2791_ == 0)
{
v___x_2761_ = v_toInductionSubgoal_2752_;
v_isShared_2762_ = v_isSharedCheck_2791_;
goto v_resetjp_2760_;
}
else
{
lean_inc(v_subst_2759_);
lean_inc(v_fields_2758_);
lean_inc(v_mvarId_2757_);
lean_dec(v_toInductionSubgoal_2752_);
v___x_2761_ = lean_box(0);
v_isShared_2762_ = v_isSharedCheck_2791_;
goto v_resetjp_2760_;
}
v_resetjp_2760_:
{
lean_object* v___x_2763_; 
lean_inc_ref(v___y_2747_);
lean_inc(v_ctorName_2753_);
lean_inc(v_numEqs_2740_);
v___x_2763_ = l_Lean_Meta_Cases_unifyEqs_x3f(v_numEqs_2740_, v_mvarId_2757_, v_subst_2759_, v_ctorName_2753_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_);
if (lean_obj_tag(v___x_2763_) == 0)
{
lean_object* v_a_2764_; lean_object* v_a_2766_; 
v_a_2764_ = lean_ctor_get(v___x_2763_, 0);
lean_inc(v_a_2764_);
lean_dec_ref_known(v___x_2763_, 1);
if (lean_obj_tag(v_a_2764_) == 0)
{
lean_del_object(v___x_2761_);
lean_dec_ref(v_fields_2758_);
lean_del_object(v___x_2755_);
lean_dec(v_ctorName_2753_);
v_a_2766_ = v_b_2744_;
goto v___jp_2765_;
}
else
{
lean_object* v_val_2770_; lean_object* v_fst_2771_; lean_object* v_snd_2772_; size_t v_sz_2773_; size_t v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2777_; 
v_val_2770_ = lean_ctor_get(v_a_2764_, 0);
lean_inc(v_val_2770_);
lean_dec_ref_known(v_a_2764_, 1);
v_fst_2771_ = lean_ctor_get(v_val_2770_, 0);
lean_inc(v_fst_2771_);
v_snd_2772_ = lean_ctor_get(v_val_2770_, 1);
lean_inc_n(v_snd_2772_, 2);
lean_dec(v_val_2770_);
v_sz_2773_ = lean_array_size(v_fields_2758_);
v___x_2774_ = ((size_t)0ULL);
v___x_2775_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__0(v_snd_2772_, v_sz_2773_, v___x_2774_, v_fields_2758_);
if (v_isShared_2762_ == 0)
{
lean_ctor_set(v___x_2761_, 2, v_snd_2772_);
lean_ctor_set(v___x_2761_, 1, v___x_2775_);
lean_ctor_set(v___x_2761_, 0, v_fst_2771_);
v___x_2777_ = v___x_2761_;
goto v_reusejp_2776_;
}
else
{
lean_object* v_reuseFailAlloc_2782_; 
v_reuseFailAlloc_2782_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2782_, 0, v_fst_2771_);
lean_ctor_set(v_reuseFailAlloc_2782_, 1, v___x_2775_);
lean_ctor_set(v_reuseFailAlloc_2782_, 2, v_snd_2772_);
v___x_2777_ = v_reuseFailAlloc_2782_;
goto v_reusejp_2776_;
}
v_reusejp_2776_:
{
lean_object* v___x_2779_; 
if (v_isShared_2756_ == 0)
{
lean_ctor_set(v___x_2755_, 0, v___x_2777_);
v___x_2779_ = v___x_2755_;
goto v_reusejp_2778_;
}
else
{
lean_object* v_reuseFailAlloc_2781_; 
v_reuseFailAlloc_2781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2781_, 0, v___x_2777_);
lean_ctor_set(v_reuseFailAlloc_2781_, 1, v_ctorName_2753_);
v___x_2779_ = v_reuseFailAlloc_2781_;
goto v_reusejp_2778_;
}
v_reusejp_2778_:
{
lean_object* v___x_2780_; 
v___x_2780_ = lean_array_push(v_b_2744_, v___x_2779_);
v_a_2766_ = v___x_2780_;
goto v___jp_2765_;
}
}
}
v___jp_2765_:
{
size_t v___x_2767_; size_t v___x_2768_; 
v___x_2767_ = ((size_t)1ULL);
v___x_2768_ = lean_usize_add(v_i_2742_, v___x_2767_);
v_i_2742_ = v___x_2768_;
v_b_2744_ = v_a_2766_;
goto _start;
}
}
else
{
lean_object* v_a_2783_; lean_object* v___x_2785_; uint8_t v_isShared_2786_; uint8_t v_isSharedCheck_2790_; 
lean_del_object(v___x_2761_);
lean_dec_ref(v_fields_2758_);
lean_del_object(v___x_2755_);
lean_dec(v_ctorName_2753_);
lean_dec_ref(v_b_2744_);
lean_dec(v_numEqs_2740_);
v_a_2783_ = lean_ctor_get(v___x_2763_, 0);
v_isSharedCheck_2790_ = !lean_is_exclusive(v___x_2763_);
if (v_isSharedCheck_2790_ == 0)
{
v___x_2785_ = v___x_2763_;
v_isShared_2786_ = v_isSharedCheck_2790_;
goto v_resetjp_2784_;
}
else
{
lean_inc(v_a_2783_);
lean_dec(v___x_2763_);
v___x_2785_ = lean_box(0);
v_isShared_2786_ = v_isSharedCheck_2790_;
goto v_resetjp_2784_;
}
v_resetjp_2784_:
{
lean_object* v___x_2788_; 
if (v_isShared_2786_ == 0)
{
v___x_2788_ = v___x_2785_;
goto v_reusejp_2787_;
}
else
{
lean_object* v_reuseFailAlloc_2789_; 
v_reuseFailAlloc_2789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2789_, 0, v_a_2783_);
v___x_2788_ = v_reuseFailAlloc_2789_;
goto v_reusejp_2787_;
}
v_reusejp_2787_:
{
return v___x_2788_;
}
}
}
}
}
}
else
{
lean_object* v___x_2793_; 
lean_dec(v_numEqs_2740_);
v___x_2793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2793_, 0, v_b_2744_);
return v___x_2793_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1_spec__1___boxed(lean_object* v_numEqs_2794_, lean_object* v_as_2795_, lean_object* v_i_2796_, lean_object* v_stop_2797_, lean_object* v_b_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_){
_start:
{
size_t v_i_boxed_2804_; size_t v_stop_boxed_2805_; lean_object* v_res_2806_; 
v_i_boxed_2804_ = lean_unbox_usize(v_i_2796_);
lean_dec(v_i_2796_);
v_stop_boxed_2805_ = lean_unbox_usize(v_stop_2797_);
lean_dec(v_stop_2797_);
v_res_2806_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1_spec__1(v_numEqs_2794_, v_as_2795_, v_i_boxed_2804_, v_stop_boxed_2805_, v_b_2798_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_);
lean_dec(v___y_2802_);
lean_dec_ref(v___y_2801_);
lean_dec(v___y_2800_);
lean_dec_ref(v___y_2799_);
lean_dec_ref(v_as_2795_);
return v_res_2806_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1(lean_object* v_numEqs_2809_, lean_object* v_as_2810_, lean_object* v_start_2811_, lean_object* v_stop_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_){
_start:
{
lean_object* v___x_2818_; uint8_t v___x_2819_; 
v___x_2818_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1___closed__0));
v___x_2819_ = lean_nat_dec_lt(v_start_2811_, v_stop_2812_);
if (v___x_2819_ == 0)
{
lean_object* v___x_2820_; 
lean_dec(v_numEqs_2809_);
v___x_2820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2820_, 0, v___x_2818_);
return v___x_2820_;
}
else
{
lean_object* v___x_2821_; uint8_t v___x_2822_; 
v___x_2821_ = lean_array_get_size(v_as_2810_);
v___x_2822_ = lean_nat_dec_le(v_stop_2812_, v___x_2821_);
if (v___x_2822_ == 0)
{
uint8_t v___x_2823_; 
v___x_2823_ = lean_nat_dec_lt(v_start_2811_, v___x_2821_);
if (v___x_2823_ == 0)
{
lean_object* v___x_2824_; 
lean_dec(v_numEqs_2809_);
v___x_2824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2824_, 0, v___x_2818_);
return v___x_2824_;
}
else
{
size_t v___x_2825_; size_t v___x_2826_; lean_object* v___x_2827_; 
v___x_2825_ = lean_usize_of_nat(v_start_2811_);
v___x_2826_ = lean_usize_of_nat(v___x_2821_);
v___x_2827_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1_spec__1(v_numEqs_2809_, v_as_2810_, v___x_2825_, v___x_2826_, v___x_2818_, v___y_2813_, v___y_2814_, v___y_2815_, v___y_2816_);
return v___x_2827_;
}
}
else
{
size_t v___x_2828_; size_t v___x_2829_; lean_object* v___x_2830_; 
v___x_2828_ = lean_usize_of_nat(v_start_2811_);
v___x_2829_ = lean_usize_of_nat(v_stop_2812_);
v___x_2830_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1_spec__1(v_numEqs_2809_, v_as_2810_, v___x_2828_, v___x_2829_, v___x_2818_, v___y_2813_, v___y_2814_, v___y_2815_, v___y_2816_);
return v___x_2830_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1___boxed(lean_object* v_numEqs_2831_, lean_object* v_as_2832_, lean_object* v_start_2833_, lean_object* v_stop_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_){
_start:
{
lean_object* v_res_2840_; 
v_res_2840_ = l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1(v_numEqs_2831_, v_as_2832_, v_start_2833_, v_stop_2834_, v___y_2835_, v___y_2836_, v___y_2837_, v___y_2838_);
lean_dec(v___y_2838_);
lean_dec_ref(v___y_2837_);
lean_dec(v___y_2836_);
lean_dec_ref(v___y_2835_);
lean_dec(v_stop_2834_);
lean_dec(v_start_2833_);
lean_dec_ref(v_as_2832_);
return v_res_2840_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs(lean_object* v_numEqs_2841_, lean_object* v_subgoals_2842_, lean_object* v_a_2843_, lean_object* v_a_2844_, lean_object* v_a_2845_, lean_object* v_a_2846_){
_start:
{
lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; 
v___x_2848_ = lean_unsigned_to_nat(0u);
v___x_2849_ = lean_array_get_size(v_subgoals_2842_);
v___x_2850_ = l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1(v_numEqs_2841_, v_subgoals_2842_, v___x_2848_, v___x_2849_, v_a_2843_, v_a_2844_, v_a_2845_, v_a_2846_);
return v___x_2850_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs___boxed(lean_object* v_numEqs_2851_, lean_object* v_subgoals_2852_, lean_object* v_a_2853_, lean_object* v_a_2854_, lean_object* v_a_2855_, lean_object* v_a_2856_, lean_object* v_a_2857_){
_start:
{
lean_object* v_res_2858_; 
v_res_2858_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs(v_numEqs_2851_, v_subgoals_2852_, v_a_2853_, v_a_2854_, v_a_2855_, v_a_2856_);
lean_dec(v_a_2856_);
lean_dec_ref(v_a_2855_);
lean_dec(v_a_2854_);
lean_dec_ref(v_a_2853_);
lean_dec_ref(v_subgoals_2852_);
return v_res_2858_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0(lean_object* v___x_2870_, lean_object* v_mvarId_2871_, lean_object* v_majorFVarId_2872_, lean_object* v_givenNames_2873_, lean_object* v_ctx_2874_, uint8_t v_useNatCasesAuxOn_2875_, lean_object* v_interestingCtors_x3f_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_){
_start:
{
lean_object* v___x_2882_; 
lean_inc(v___y_2880_);
lean_inc_ref(v___y_2879_);
lean_inc(v___y_2878_);
lean_inc_ref(v___y_2877_);
v___x_2882_ = lean_infer_type(v___x_2870_, v___y_2877_, v___y_2878_, v___y_2879_, v___y_2880_);
if (lean_obj_tag(v___x_2882_) == 0)
{
lean_object* v_a_2883_; lean_object* v___x_2884_; 
v_a_2883_ = lean_ctor_get(v___x_2882_, 0);
lean_inc(v_a_2883_);
lean_dec_ref_known(v___x_2882_, 1);
v___x_2884_ = l_Lean_Meta_getInductiveUniverseAndParams(v_a_2883_, v___y_2877_, v___y_2878_, v___y_2879_, v___y_2880_);
if (lean_obj_tag(v___x_2884_) == 0)
{
lean_object* v_a_2885_; lean_object* v_fst_2886_; lean_object* v_snd_2887_; lean_object* v___y_2889_; lean_object* v___y_2890_; lean_object* v___y_2891_; lean_object* v___y_2892_; lean_object* v___y_2893_; lean_object* v___y_2916_; lean_object* v___y_2917_; lean_object* v___y_2918_; lean_object* v___y_2919_; lean_object* v___y_2925_; lean_object* v___y_2926_; lean_object* v___y_2927_; lean_object* v___y_2928_; 
v_a_2885_ = lean_ctor_get(v___x_2884_, 0);
lean_inc(v_a_2885_);
lean_dec_ref_known(v___x_2884_, 1);
v_fst_2886_ = lean_ctor_get(v_a_2885_, 0);
lean_inc(v_fst_2886_);
v_snd_2887_ = lean_ctor_get(v_a_2885_, 1);
lean_inc(v_snd_2887_);
lean_dec(v_a_2885_);
if (lean_obj_tag(v_interestingCtors_x3f_2876_) == 1)
{
lean_object* v_val_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v_inductiveVal_2941_; lean_object* v_toConstantVal_2942_; lean_object* v_env_2943_; lean_object* v_ctors_2944_; lean_object* v_name_2945_; uint8_t v___y_2947_; lean_object* v___x_2981_; uint8_t v___x_2982_; uint8_t v___x_2983_; 
v_val_2938_ = lean_ctor_get(v_interestingCtors_x3f_2876_, 0);
lean_inc(v_val_2938_);
lean_dec_ref_known(v_interestingCtors_x3f_2876_, 1);
v___x_2939_ = lean_st_ref_get(v___y_2880_);
v___x_2940_ = lean_st_ref_get(v___y_2880_);
v_inductiveVal_2941_ = lean_ctor_get(v_ctx_2874_, 0);
v_toConstantVal_2942_ = lean_ctor_get(v_inductiveVal_2941_, 0);
v_env_2943_ = lean_ctor_get(v___x_2939_, 0);
lean_inc_ref(v_env_2943_);
lean_dec(v___x_2939_);
v_ctors_2944_ = lean_ctor_get(v_inductiveVal_2941_, 4);
v_name_2945_ = lean_ctor_get(v_toConstantVal_2942_, 0);
v___x_2981_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__5));
v___x_2982_ = 1;
v___x_2983_ = l_Lean_Environment_contains(v_env_2943_, v___x_2981_, v___x_2982_);
if (v___x_2983_ == 0)
{
lean_dec(v___x_2940_);
v___y_2947_ = v___x_2983_;
goto v___jp_2946_;
}
else
{
lean_object* v_env_2984_; lean_object* v___x_2985_; uint8_t v___x_2986_; 
v_env_2984_ = lean_ctor_get(v___x_2940_, 0);
lean_inc_ref(v_env_2984_);
lean_dec(v___x_2940_);
lean_inc(v_name_2945_);
v___x_2985_ = l_Lean_mkCtorIdxName(v_name_2945_);
v___x_2986_ = l_Lean_Environment_contains(v_env_2984_, v___x_2985_, v___x_2982_);
v___y_2947_ = v___x_2986_;
goto v___jp_2946_;
}
v___jp_2946_:
{
if (v___y_2947_ == 0)
{
lean_dec(v_val_2938_);
v___y_2925_ = v___y_2877_;
v___y_2926_ = v___y_2878_;
v___y_2927_ = v___y_2879_;
v___y_2928_ = v___y_2880_;
goto v___jp_2924_;
}
else
{
lean_object* v___x_2948_; lean_object* v___x_2949_; uint8_t v___x_2950_; 
v___x_2948_ = lean_array_get_size(v_val_2938_);
v___x_2949_ = lean_unsigned_to_nat(0u);
v___x_2950_ = lean_nat_dec_eq(v___x_2948_, v___x_2949_);
if (v___x_2950_ == 0)
{
lean_object* v___x_2951_; uint8_t v___x_2952_; 
v___x_2951_ = l_List_lengthTR___redArg(v_ctors_2944_);
v___x_2952_ = lean_nat_dec_lt(v___x_2948_, v___x_2951_);
lean_dec(v___x_2951_);
if (v___x_2952_ == 0)
{
lean_dec(v_val_2938_);
v___y_2925_ = v___y_2877_;
v___y_2926_ = v___y_2878_;
v___y_2927_ = v___y_2879_;
v___y_2928_ = v___y_2880_;
goto v___jp_2924_;
}
else
{
lean_object* v___x_2953_; 
lean_inc(v_name_2945_);
lean_dec_ref(v_ctx_2874_);
lean_inc(v_val_2938_);
v___x_2953_ = l_Lean_Meta_mkSparseCasesOn(v_name_2945_, v_val_2938_, v___y_2877_, v___y_2878_, v___y_2879_, v___y_2880_);
if (lean_obj_tag(v___x_2953_) == 0)
{
lean_object* v_a_2954_; lean_object* v___x_2955_; 
v_a_2954_ = lean_ctor_get(v___x_2953_, 0);
lean_inc(v_a_2954_);
lean_dec_ref_known(v___x_2953_, 1);
lean_inc(v_majorFVarId_2872_);
v___x_2955_ = l_Lean_MVarId_induction(v_mvarId_2871_, v_majorFVarId_2872_, v_a_2954_, v_givenNames_2873_, v___y_2877_, v___y_2878_, v___y_2879_, v___y_2880_);
lean_dec(v___y_2880_);
lean_dec_ref(v___y_2879_);
lean_dec(v___y_2878_);
lean_dec_ref(v___y_2877_);
if (lean_obj_tag(v___x_2955_) == 0)
{
lean_object* v_a_2956_; lean_object* v___x_2958_; uint8_t v_isShared_2959_; uint8_t v_isSharedCheck_2964_; 
v_a_2956_ = lean_ctor_get(v___x_2955_, 0);
v_isSharedCheck_2964_ = !lean_is_exclusive(v___x_2955_);
if (v_isSharedCheck_2964_ == 0)
{
v___x_2958_ = v___x_2955_;
v_isShared_2959_ = v_isSharedCheck_2964_;
goto v_resetjp_2957_;
}
else
{
lean_inc(v_a_2956_);
lean_dec(v___x_2955_);
v___x_2958_ = lean_box(0);
v_isShared_2959_ = v_isSharedCheck_2964_;
goto v_resetjp_2957_;
}
v_resetjp_2957_:
{
lean_object* v___x_2960_; lean_object* v___x_2962_; 
v___x_2960_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals(v_a_2956_, v_val_2938_, v_majorFVarId_2872_, v_fst_2886_, v_snd_2887_);
lean_dec(v_snd_2887_);
lean_dec(v_val_2938_);
if (v_isShared_2959_ == 0)
{
lean_ctor_set(v___x_2958_, 0, v___x_2960_);
v___x_2962_ = v___x_2958_;
goto v_reusejp_2961_;
}
else
{
lean_object* v_reuseFailAlloc_2963_; 
v_reuseFailAlloc_2963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2963_, 0, v___x_2960_);
v___x_2962_ = v_reuseFailAlloc_2963_;
goto v_reusejp_2961_;
}
v_reusejp_2961_:
{
return v___x_2962_;
}
}
}
else
{
lean_object* v_a_2965_; lean_object* v___x_2967_; uint8_t v_isShared_2968_; uint8_t v_isSharedCheck_2972_; 
lean_dec(v_val_2938_);
lean_dec(v_snd_2887_);
lean_dec(v_fst_2886_);
lean_dec(v_majorFVarId_2872_);
v_a_2965_ = lean_ctor_get(v___x_2955_, 0);
v_isSharedCheck_2972_ = !lean_is_exclusive(v___x_2955_);
if (v_isSharedCheck_2972_ == 0)
{
v___x_2967_ = v___x_2955_;
v_isShared_2968_ = v_isSharedCheck_2972_;
goto v_resetjp_2966_;
}
else
{
lean_inc(v_a_2965_);
lean_dec(v___x_2955_);
v___x_2967_ = lean_box(0);
v_isShared_2968_ = v_isSharedCheck_2972_;
goto v_resetjp_2966_;
}
v_resetjp_2966_:
{
lean_object* v___x_2970_; 
if (v_isShared_2968_ == 0)
{
v___x_2970_ = v___x_2967_;
goto v_reusejp_2969_;
}
else
{
lean_object* v_reuseFailAlloc_2971_; 
v_reuseFailAlloc_2971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2971_, 0, v_a_2965_);
v___x_2970_ = v_reuseFailAlloc_2971_;
goto v_reusejp_2969_;
}
v_reusejp_2969_:
{
return v___x_2970_;
}
}
}
}
else
{
lean_object* v_a_2973_; lean_object* v___x_2975_; uint8_t v_isShared_2976_; uint8_t v_isSharedCheck_2980_; 
lean_dec(v_val_2938_);
lean_dec(v_snd_2887_);
lean_dec(v_fst_2886_);
lean_dec(v___y_2880_);
lean_dec_ref(v___y_2879_);
lean_dec(v___y_2878_);
lean_dec_ref(v___y_2877_);
lean_dec_ref(v_givenNames_2873_);
lean_dec(v_majorFVarId_2872_);
lean_dec(v_mvarId_2871_);
v_a_2973_ = lean_ctor_get(v___x_2953_, 0);
v_isSharedCheck_2980_ = !lean_is_exclusive(v___x_2953_);
if (v_isSharedCheck_2980_ == 0)
{
v___x_2975_ = v___x_2953_;
v_isShared_2976_ = v_isSharedCheck_2980_;
goto v_resetjp_2974_;
}
else
{
lean_inc(v_a_2973_);
lean_dec(v___x_2953_);
v___x_2975_ = lean_box(0);
v_isShared_2976_ = v_isSharedCheck_2980_;
goto v_resetjp_2974_;
}
v_resetjp_2974_:
{
lean_object* v___x_2978_; 
if (v_isShared_2976_ == 0)
{
v___x_2978_ = v___x_2975_;
goto v_reusejp_2977_;
}
else
{
lean_object* v_reuseFailAlloc_2979_; 
v_reuseFailAlloc_2979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2979_, 0, v_a_2973_);
v___x_2978_ = v_reuseFailAlloc_2979_;
goto v_reusejp_2977_;
}
v_reusejp_2977_:
{
return v___x_2978_;
}
}
}
}
}
else
{
lean_dec(v_val_2938_);
v___y_2925_ = v___y_2877_;
v___y_2926_ = v___y_2878_;
v___y_2927_ = v___y_2879_;
v___y_2928_ = v___y_2880_;
goto v___jp_2924_;
}
}
}
}
else
{
lean_dec(v_interestingCtors_x3f_2876_);
v___y_2925_ = v___y_2877_;
v___y_2926_ = v___y_2878_;
v___y_2927_ = v___y_2879_;
v___y_2928_ = v___y_2880_;
goto v___jp_2924_;
}
v___jp_2888_:
{
lean_object* v___x_2894_; 
lean_inc(v_majorFVarId_2872_);
v___x_2894_ = l_Lean_MVarId_induction(v_mvarId_2871_, v_majorFVarId_2872_, v___y_2893_, v_givenNames_2873_, v___y_2892_, v___y_2891_, v___y_2890_, v___y_2889_);
lean_dec(v___y_2889_);
lean_dec_ref(v___y_2890_);
lean_dec(v___y_2891_);
lean_dec_ref(v___y_2892_);
if (lean_obj_tag(v___x_2894_) == 0)
{
lean_object* v_inductiveVal_2895_; lean_object* v_a_2896_; lean_object* v___x_2898_; uint8_t v_isShared_2899_; uint8_t v_isSharedCheck_2906_; 
v_inductiveVal_2895_ = lean_ctor_get(v_ctx_2874_, 0);
lean_inc_ref(v_inductiveVal_2895_);
lean_dec_ref(v_ctx_2874_);
v_a_2896_ = lean_ctor_get(v___x_2894_, 0);
v_isSharedCheck_2906_ = !lean_is_exclusive(v___x_2894_);
if (v_isSharedCheck_2906_ == 0)
{
v___x_2898_ = v___x_2894_;
v_isShared_2899_ = v_isSharedCheck_2906_;
goto v_resetjp_2897_;
}
else
{
lean_inc(v_a_2896_);
lean_dec(v___x_2894_);
v___x_2898_ = lean_box(0);
v_isShared_2899_ = v_isSharedCheck_2906_;
goto v_resetjp_2897_;
}
v_resetjp_2897_:
{
lean_object* v_ctors_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2904_; 
v_ctors_2900_ = lean_ctor_get(v_inductiveVal_2895_, 4);
lean_inc(v_ctors_2900_);
lean_dec_ref(v_inductiveVal_2895_);
v___x_2901_ = lean_array_mk(v_ctors_2900_);
v___x_2902_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals(v_a_2896_, v___x_2901_, v_majorFVarId_2872_, v_fst_2886_, v_snd_2887_);
lean_dec(v_snd_2887_);
lean_dec_ref(v___x_2901_);
if (v_isShared_2899_ == 0)
{
lean_ctor_set(v___x_2898_, 0, v___x_2902_);
v___x_2904_ = v___x_2898_;
goto v_reusejp_2903_;
}
else
{
lean_object* v_reuseFailAlloc_2905_; 
v_reuseFailAlloc_2905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2905_, 0, v___x_2902_);
v___x_2904_ = v_reuseFailAlloc_2905_;
goto v_reusejp_2903_;
}
v_reusejp_2903_:
{
return v___x_2904_;
}
}
}
else
{
lean_object* v_a_2907_; lean_object* v___x_2909_; uint8_t v_isShared_2910_; uint8_t v_isSharedCheck_2914_; 
lean_dec(v_snd_2887_);
lean_dec(v_fst_2886_);
lean_dec_ref(v_ctx_2874_);
lean_dec(v_majorFVarId_2872_);
v_a_2907_ = lean_ctor_get(v___x_2894_, 0);
v_isSharedCheck_2914_ = !lean_is_exclusive(v___x_2894_);
if (v_isSharedCheck_2914_ == 0)
{
v___x_2909_ = v___x_2894_;
v_isShared_2910_ = v_isSharedCheck_2914_;
goto v_resetjp_2908_;
}
else
{
lean_inc(v_a_2907_);
lean_dec(v___x_2894_);
v___x_2909_ = lean_box(0);
v_isShared_2910_ = v_isSharedCheck_2914_;
goto v_resetjp_2908_;
}
v_resetjp_2908_:
{
lean_object* v___x_2912_; 
if (v_isShared_2910_ == 0)
{
v___x_2912_ = v___x_2909_;
goto v_reusejp_2911_;
}
else
{
lean_object* v_reuseFailAlloc_2913_; 
v_reuseFailAlloc_2913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2913_, 0, v_a_2907_);
v___x_2912_ = v_reuseFailAlloc_2913_;
goto v_reusejp_2911_;
}
v_reusejp_2911_:
{
return v___x_2912_;
}
}
}
}
v___jp_2915_:
{
lean_object* v_inductiveVal_2920_; lean_object* v_toConstantVal_2921_; lean_object* v_name_2922_; lean_object* v___x_2923_; 
v_inductiveVal_2920_ = lean_ctor_get(v_ctx_2874_, 0);
v_toConstantVal_2921_ = lean_ctor_get(v_inductiveVal_2920_, 0);
v_name_2922_ = lean_ctor_get(v_toConstantVal_2921_, 0);
lean_inc(v_name_2922_);
v___x_2923_ = l_Lean_mkCasesOnName(v_name_2922_);
v___y_2889_ = v___y_2916_;
v___y_2890_ = v___y_2917_;
v___y_2891_ = v___y_2918_;
v___y_2892_ = v___y_2919_;
v___y_2893_ = v___x_2923_;
goto v___jp_2888_;
}
v___jp_2924_:
{
lean_object* v___x_2929_; 
v___x_2929_ = lean_st_ref_get(v___y_2928_);
if (v_useNatCasesAuxOn_2875_ == 0)
{
lean_dec(v___x_2929_);
v___y_2916_ = v___y_2928_;
v___y_2917_ = v___y_2927_;
v___y_2918_ = v___y_2926_;
v___y_2919_ = v___y_2925_;
goto v___jp_2915_;
}
else
{
lean_object* v_inductiveVal_2930_; lean_object* v_toConstantVal_2931_; lean_object* v_env_2932_; lean_object* v_name_2933_; lean_object* v___x_2934_; uint8_t v___x_2935_; 
v_inductiveVal_2930_ = lean_ctor_get(v_ctx_2874_, 0);
v_toConstantVal_2931_ = lean_ctor_get(v_inductiveVal_2930_, 0);
v_env_2932_ = lean_ctor_get(v___x_2929_, 0);
lean_inc_ref(v_env_2932_);
lean_dec(v___x_2929_);
v_name_2933_ = lean_ctor_get(v_toConstantVal_2931_, 0);
v___x_2934_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__1));
v___x_2935_ = lean_name_eq(v_name_2933_, v___x_2934_);
if (v___x_2935_ == 0)
{
lean_dec_ref(v_env_2932_);
v___y_2916_ = v___y_2928_;
v___y_2917_ = v___y_2927_;
v___y_2918_ = v___y_2926_;
v___y_2919_ = v___y_2925_;
goto v___jp_2915_;
}
else
{
lean_object* v___x_2936_; uint8_t v___x_2937_; 
v___x_2936_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__3));
v___x_2937_ = l_Lean_Environment_contains(v_env_2932_, v___x_2936_, v___x_2935_);
if (v___x_2937_ == 0)
{
v___y_2916_ = v___y_2928_;
v___y_2917_ = v___y_2927_;
v___y_2918_ = v___y_2926_;
v___y_2919_ = v___y_2925_;
goto v___jp_2915_;
}
else
{
v___y_2889_ = v___y_2928_;
v___y_2890_ = v___y_2927_;
v___y_2891_ = v___y_2926_;
v___y_2892_ = v___y_2925_;
v___y_2893_ = v___x_2936_;
goto v___jp_2888_;
}
}
}
}
}
else
{
lean_object* v_a_2987_; lean_object* v___x_2989_; uint8_t v_isShared_2990_; uint8_t v_isSharedCheck_2994_; 
lean_dec(v___y_2880_);
lean_dec_ref(v___y_2879_);
lean_dec(v___y_2878_);
lean_dec_ref(v___y_2877_);
lean_dec(v_interestingCtors_x3f_2876_);
lean_dec_ref(v_ctx_2874_);
lean_dec_ref(v_givenNames_2873_);
lean_dec(v_majorFVarId_2872_);
lean_dec(v_mvarId_2871_);
v_a_2987_ = lean_ctor_get(v___x_2884_, 0);
v_isSharedCheck_2994_ = !lean_is_exclusive(v___x_2884_);
if (v_isSharedCheck_2994_ == 0)
{
v___x_2989_ = v___x_2884_;
v_isShared_2990_ = v_isSharedCheck_2994_;
goto v_resetjp_2988_;
}
else
{
lean_inc(v_a_2987_);
lean_dec(v___x_2884_);
v___x_2989_ = lean_box(0);
v_isShared_2990_ = v_isSharedCheck_2994_;
goto v_resetjp_2988_;
}
v_resetjp_2988_:
{
lean_object* v___x_2992_; 
if (v_isShared_2990_ == 0)
{
v___x_2992_ = v___x_2989_;
goto v_reusejp_2991_;
}
else
{
lean_object* v_reuseFailAlloc_2993_; 
v_reuseFailAlloc_2993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2993_, 0, v_a_2987_);
v___x_2992_ = v_reuseFailAlloc_2993_;
goto v_reusejp_2991_;
}
v_reusejp_2991_:
{
return v___x_2992_;
}
}
}
}
else
{
lean_object* v_a_2995_; lean_object* v___x_2997_; uint8_t v_isShared_2998_; uint8_t v_isSharedCheck_3002_; 
lean_dec(v___y_2880_);
lean_dec_ref(v___y_2879_);
lean_dec(v___y_2878_);
lean_dec_ref(v___y_2877_);
lean_dec(v_interestingCtors_x3f_2876_);
lean_dec_ref(v_ctx_2874_);
lean_dec_ref(v_givenNames_2873_);
lean_dec(v_majorFVarId_2872_);
lean_dec(v_mvarId_2871_);
v_a_2995_ = lean_ctor_get(v___x_2882_, 0);
v_isSharedCheck_3002_ = !lean_is_exclusive(v___x_2882_);
if (v_isSharedCheck_3002_ == 0)
{
v___x_2997_ = v___x_2882_;
v_isShared_2998_ = v_isSharedCheck_3002_;
goto v_resetjp_2996_;
}
else
{
lean_inc(v_a_2995_);
lean_dec(v___x_2882_);
v___x_2997_ = lean_box(0);
v_isShared_2998_ = v_isSharedCheck_3002_;
goto v_resetjp_2996_;
}
v_resetjp_2996_:
{
lean_object* v___x_3000_; 
if (v_isShared_2998_ == 0)
{
v___x_3000_ = v___x_2997_;
goto v_reusejp_2999_;
}
else
{
lean_object* v_reuseFailAlloc_3001_; 
v_reuseFailAlloc_3001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3001_, 0, v_a_2995_);
v___x_3000_ = v_reuseFailAlloc_3001_;
goto v_reusejp_2999_;
}
v_reusejp_2999_:
{
return v___x_3000_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___boxed(lean_object* v___x_3003_, lean_object* v_mvarId_3004_, lean_object* v_majorFVarId_3005_, lean_object* v_givenNames_3006_, lean_object* v_ctx_3007_, lean_object* v_useNatCasesAuxOn_3008_, lean_object* v_interestingCtors_x3f_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_, lean_object* v___y_3014_){
_start:
{
uint8_t v_useNatCasesAuxOn_boxed_3015_; lean_object* v_res_3016_; 
v_useNatCasesAuxOn_boxed_3015_ = lean_unbox(v_useNatCasesAuxOn_3008_);
v_res_3016_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0(v___x_3003_, v_mvarId_3004_, v_majorFVarId_3005_, v_givenNames_3006_, v_ctx_3007_, v_useNatCasesAuxOn_boxed_3015_, v_interestingCtors_x3f_3009_, v___y_3010_, v___y_3011_, v___y_3012_, v___y_3013_);
return v_res_3016_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn(lean_object* v_mvarId_3017_, lean_object* v_majorFVarId_3018_, lean_object* v_givenNames_3019_, lean_object* v_ctx_3020_, uint8_t v_useNatCasesAuxOn_3021_, lean_object* v_interestingCtors_x3f_3022_, lean_object* v_a_3023_, lean_object* v_a_3024_, lean_object* v_a_3025_, lean_object* v_a_3026_){
_start:
{
lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___f_3030_; lean_object* v___x_3031_; 
lean_inc(v_majorFVarId_3018_);
v___x_3028_ = l_Lean_mkFVar(v_majorFVarId_3018_);
v___x_3029_ = lean_box(v_useNatCasesAuxOn_3021_);
lean_inc(v_mvarId_3017_);
v___f_3030_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___boxed), 12, 7);
lean_closure_set(v___f_3030_, 0, v___x_3028_);
lean_closure_set(v___f_3030_, 1, v_mvarId_3017_);
lean_closure_set(v___f_3030_, 2, v_majorFVarId_3018_);
lean_closure_set(v___f_3030_, 3, v_givenNames_3019_);
lean_closure_set(v___f_3030_, 4, v_ctx_3020_);
lean_closure_set(v___f_3030_, 5, v___x_3029_);
lean_closure_set(v___f_3030_, 6, v_interestingCtors_x3f_3022_);
v___x_3031_ = l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2___redArg(v_mvarId_3017_, v___f_3030_, v_a_3023_, v_a_3024_, v_a_3025_, v_a_3026_);
return v___x_3031_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___boxed(lean_object* v_mvarId_3032_, lean_object* v_majorFVarId_3033_, lean_object* v_givenNames_3034_, lean_object* v_ctx_3035_, lean_object* v_useNatCasesAuxOn_3036_, lean_object* v_interestingCtors_x3f_3037_, lean_object* v_a_3038_, lean_object* v_a_3039_, lean_object* v_a_3040_, lean_object* v_a_3041_, lean_object* v_a_3042_){
_start:
{
uint8_t v_useNatCasesAuxOn_boxed_3043_; lean_object* v_res_3044_; 
v_useNatCasesAuxOn_boxed_3043_ = lean_unbox(v_useNatCasesAuxOn_3036_);
v_res_3044_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn(v_mvarId_3032_, v_majorFVarId_3033_, v_givenNames_3034_, v_ctx_3035_, v_useNatCasesAuxOn_boxed_3043_, v_interestingCtors_x3f_3037_, v_a_3038_, v_a_3039_, v_a_3040_, v_a_3041_);
lean_dec(v_a_3041_);
lean_dec_ref(v_a_3040_);
lean_dec(v_a_3039_);
lean_dec_ref(v_a_3038_);
return v_res_3044_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0___closed__0(void){
_start:
{
lean_object* v___x_3045_; double v___x_3046_; 
v___x_3045_ = lean_unsigned_to_nat(0u);
v___x_3046_ = lean_float_of_nat(v___x_3045_);
return v___x_3046_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0(lean_object* v_cls_3050_, lean_object* v_msg_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_){
_start:
{
lean_object* v_ref_3057_; lean_object* v___x_3058_; lean_object* v_a_3059_; lean_object* v___x_3061_; uint8_t v_isShared_3062_; uint8_t v_isSharedCheck_3103_; 
v_ref_3057_ = lean_ctor_get(v___y_3054_, 5);
v___x_3058_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected_spec__0_spec__0(v_msg_3051_, v___y_3052_, v___y_3053_, v___y_3054_, v___y_3055_);
v_a_3059_ = lean_ctor_get(v___x_3058_, 0);
v_isSharedCheck_3103_ = !lean_is_exclusive(v___x_3058_);
if (v_isSharedCheck_3103_ == 0)
{
v___x_3061_ = v___x_3058_;
v_isShared_3062_ = v_isSharedCheck_3103_;
goto v_resetjp_3060_;
}
else
{
lean_inc(v_a_3059_);
lean_dec(v___x_3058_);
v___x_3061_ = lean_box(0);
v_isShared_3062_ = v_isSharedCheck_3103_;
goto v_resetjp_3060_;
}
v_resetjp_3060_:
{
lean_object* v___x_3063_; lean_object* v_traceState_3064_; lean_object* v_env_3065_; lean_object* v_nextMacroScope_3066_; lean_object* v_ngen_3067_; lean_object* v_auxDeclNGen_3068_; lean_object* v_cache_3069_; lean_object* v_messages_3070_; lean_object* v_infoState_3071_; lean_object* v_snapshotTasks_3072_; lean_object* v___x_3074_; uint8_t v_isShared_3075_; uint8_t v_isSharedCheck_3102_; 
v___x_3063_ = lean_st_ref_take(v___y_3055_);
v_traceState_3064_ = lean_ctor_get(v___x_3063_, 4);
v_env_3065_ = lean_ctor_get(v___x_3063_, 0);
v_nextMacroScope_3066_ = lean_ctor_get(v___x_3063_, 1);
v_ngen_3067_ = lean_ctor_get(v___x_3063_, 2);
v_auxDeclNGen_3068_ = lean_ctor_get(v___x_3063_, 3);
v_cache_3069_ = lean_ctor_get(v___x_3063_, 5);
v_messages_3070_ = lean_ctor_get(v___x_3063_, 6);
v_infoState_3071_ = lean_ctor_get(v___x_3063_, 7);
v_snapshotTasks_3072_ = lean_ctor_get(v___x_3063_, 8);
v_isSharedCheck_3102_ = !lean_is_exclusive(v___x_3063_);
if (v_isSharedCheck_3102_ == 0)
{
v___x_3074_ = v___x_3063_;
v_isShared_3075_ = v_isSharedCheck_3102_;
goto v_resetjp_3073_;
}
else
{
lean_inc(v_snapshotTasks_3072_);
lean_inc(v_infoState_3071_);
lean_inc(v_messages_3070_);
lean_inc(v_cache_3069_);
lean_inc(v_traceState_3064_);
lean_inc(v_auxDeclNGen_3068_);
lean_inc(v_ngen_3067_);
lean_inc(v_nextMacroScope_3066_);
lean_inc(v_env_3065_);
lean_dec(v___x_3063_);
v___x_3074_ = lean_box(0);
v_isShared_3075_ = v_isSharedCheck_3102_;
goto v_resetjp_3073_;
}
v_resetjp_3073_:
{
uint64_t v_tid_3076_; lean_object* v_traces_3077_; lean_object* v___x_3079_; uint8_t v_isShared_3080_; uint8_t v_isSharedCheck_3101_; 
v_tid_3076_ = lean_ctor_get_uint64(v_traceState_3064_, sizeof(void*)*1);
v_traces_3077_ = lean_ctor_get(v_traceState_3064_, 0);
v_isSharedCheck_3101_ = !lean_is_exclusive(v_traceState_3064_);
if (v_isSharedCheck_3101_ == 0)
{
v___x_3079_ = v_traceState_3064_;
v_isShared_3080_ = v_isSharedCheck_3101_;
goto v_resetjp_3078_;
}
else
{
lean_inc(v_traces_3077_);
lean_dec(v_traceState_3064_);
v___x_3079_ = lean_box(0);
v_isShared_3080_ = v_isSharedCheck_3101_;
goto v_resetjp_3078_;
}
v_resetjp_3078_:
{
lean_object* v___x_3081_; double v___x_3082_; uint8_t v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3091_; 
v___x_3081_ = lean_box(0);
v___x_3082_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0___closed__0);
v___x_3083_ = 0;
v___x_3084_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0___closed__1));
v___x_3085_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3085_, 0, v_cls_3050_);
lean_ctor_set(v___x_3085_, 1, v___x_3081_);
lean_ctor_set(v___x_3085_, 2, v___x_3084_);
lean_ctor_set_float(v___x_3085_, sizeof(void*)*3, v___x_3082_);
lean_ctor_set_float(v___x_3085_, sizeof(void*)*3 + 8, v___x_3082_);
lean_ctor_set_uint8(v___x_3085_, sizeof(void*)*3 + 16, v___x_3083_);
v___x_3086_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0___closed__2));
v___x_3087_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3087_, 0, v___x_3085_);
lean_ctor_set(v___x_3087_, 1, v_a_3059_);
lean_ctor_set(v___x_3087_, 2, v___x_3086_);
lean_inc(v_ref_3057_);
v___x_3088_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3088_, 0, v_ref_3057_);
lean_ctor_set(v___x_3088_, 1, v___x_3087_);
v___x_3089_ = l_Lean_PersistentArray_push___redArg(v_traces_3077_, v___x_3088_);
if (v_isShared_3080_ == 0)
{
lean_ctor_set(v___x_3079_, 0, v___x_3089_);
v___x_3091_ = v___x_3079_;
goto v_reusejp_3090_;
}
else
{
lean_object* v_reuseFailAlloc_3100_; 
v_reuseFailAlloc_3100_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3100_, 0, v___x_3089_);
lean_ctor_set_uint64(v_reuseFailAlloc_3100_, sizeof(void*)*1, v_tid_3076_);
v___x_3091_ = v_reuseFailAlloc_3100_;
goto v_reusejp_3090_;
}
v_reusejp_3090_:
{
lean_object* v___x_3093_; 
if (v_isShared_3075_ == 0)
{
lean_ctor_set(v___x_3074_, 4, v___x_3091_);
v___x_3093_ = v___x_3074_;
goto v_reusejp_3092_;
}
else
{
lean_object* v_reuseFailAlloc_3099_; 
v_reuseFailAlloc_3099_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3099_, 0, v_env_3065_);
lean_ctor_set(v_reuseFailAlloc_3099_, 1, v_nextMacroScope_3066_);
lean_ctor_set(v_reuseFailAlloc_3099_, 2, v_ngen_3067_);
lean_ctor_set(v_reuseFailAlloc_3099_, 3, v_auxDeclNGen_3068_);
lean_ctor_set(v_reuseFailAlloc_3099_, 4, v___x_3091_);
lean_ctor_set(v_reuseFailAlloc_3099_, 5, v_cache_3069_);
lean_ctor_set(v_reuseFailAlloc_3099_, 6, v_messages_3070_);
lean_ctor_set(v_reuseFailAlloc_3099_, 7, v_infoState_3071_);
lean_ctor_set(v_reuseFailAlloc_3099_, 8, v_snapshotTasks_3072_);
v___x_3093_ = v_reuseFailAlloc_3099_;
goto v_reusejp_3092_;
}
v_reusejp_3092_:
{
lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3097_; 
v___x_3094_ = lean_st_ref_put(v___y_3055_, v___x_3093_);
v___x_3095_ = lean_box(0);
if (v_isShared_3062_ == 0)
{
lean_ctor_set(v___x_3061_, 0, v___x_3095_);
v___x_3097_ = v___x_3061_;
goto v_reusejp_3096_;
}
else
{
lean_object* v_reuseFailAlloc_3098_; 
v_reuseFailAlloc_3098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3098_, 0, v___x_3095_);
v___x_3097_ = v_reuseFailAlloc_3098_;
goto v_reusejp_3096_;
}
v_reusejp_3096_:
{
return v___x_3097_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0___boxed(lean_object* v_cls_3104_, lean_object* v_msg_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_){
_start:
{
lean_object* v_res_3111_; 
v_res_3111_ = l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0(v_cls_3104_, v_msg_3105_, v___y_3106_, v___y_3107_, v___y_3108_, v___y_3109_);
lean_dec(v___y_3109_);
lean_dec_ref(v___y_3108_);
lean_dec(v___y_3107_);
lean_dec_ref(v___y_3106_);
return v_res_3111_;
}
}
static lean_object* _init_l_Lean_Meta_Cases_cases___lam__0___closed__2(void){
_start:
{
lean_object* v___x_3115_; lean_object* v___x_3116_; 
v___x_3115_ = ((lean_object*)(l_Lean_Meta_Cases_cases___lam__0___closed__1));
v___x_3116_ = l_Lean_MessageData_ofFormat(v___x_3115_);
return v___x_3116_;
}
}
static lean_object* _init_l_Lean_Meta_Cases_cases___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3117_; lean_object* v___x_3118_; 
v___x_3117_ = lean_obj_once(&l_Lean_Meta_Cases_cases___lam__0___closed__2, &l_Lean_Meta_Cases_cases___lam__0___closed__2_once, _init_l_Lean_Meta_Cases_cases___lam__0___closed__2);
v___x_3118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3118_, 0, v___x_3117_);
return v___x_3118_;
}
}
static lean_object* _init_l_Lean_Meta_Cases_cases___lam__0___closed__9(void){
_start:
{
lean_object* v___x_3125_; lean_object* v___x_3126_; 
v___x_3125_ = ((lean_object*)(l_Lean_Meta_Cases_cases___lam__0___closed__8));
v___x_3126_ = l_Lean_stringToMessageData(v___x_3125_);
return v___x_3126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_cases___lam__0(lean_object* v_mvarId_3127_, lean_object* v___x_3128_, lean_object* v_majorFVarId_3129_, lean_object* v_givenNames_3130_, lean_object* v_interestingCtors_x3f_3131_, lean_object* v___x_3132_, uint8_t v_useNatCasesAuxOn_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_){
_start:
{
lean_object* v___x_3139_; 
lean_inc(v___x_3128_);
lean_inc(v_mvarId_3127_);
v___x_3139_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_3127_, v___x_3128_, v___y_3134_, v___y_3135_, v___y_3136_, v___y_3137_);
if (lean_obj_tag(v___x_3139_) == 0)
{
lean_object* v___x_3140_; 
lean_dec_ref_known(v___x_3139_, 1);
lean_inc(v_majorFVarId_3129_);
v___x_3140_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f(v_majorFVarId_3129_, v___y_3134_, v___y_3135_, v___y_3136_, v___y_3137_);
if (lean_obj_tag(v___x_3140_) == 0)
{
lean_object* v_a_3141_; 
v_a_3141_ = lean_ctor_get(v___x_3140_, 0);
lean_inc(v_a_3141_);
lean_dec_ref_known(v___x_3140_, 1);
if (lean_obj_tag(v_a_3141_) == 0)
{
lean_object* v___x_3142_; lean_object* v___x_3143_; 
lean_dec_ref(v___x_3132_);
lean_dec(v_interestingCtors_x3f_3131_);
lean_dec_ref(v_givenNames_3130_);
lean_dec(v_majorFVarId_3129_);
v___x_3142_ = lean_obj_once(&l_Lean_Meta_Cases_cases___lam__0___closed__3, &l_Lean_Meta_Cases_cases___lam__0___closed__3_once, _init_l_Lean_Meta_Cases_cases___lam__0___closed__3);
v___x_3143_ = l_Lean_Meta_throwTacticEx___redArg(v___x_3128_, v_mvarId_3127_, v___x_3142_, v___y_3134_, v___y_3135_, v___y_3136_, v___y_3137_);
return v___x_3143_;
}
else
{
lean_object* v_val_3144_; lean_object* v___x_3146_; uint8_t v_isShared_3147_; uint8_t v_isSharedCheck_3208_; 
lean_dec(v___x_3128_);
v_val_3144_ = lean_ctor_get(v_a_3141_, 0);
v_isSharedCheck_3208_ = !lean_is_exclusive(v_a_3141_);
if (v_isSharedCheck_3208_ == 0)
{
v___x_3146_ = v_a_3141_;
v_isShared_3147_ = v_isSharedCheck_3208_;
goto v_resetjp_3145_;
}
else
{
lean_inc(v_val_3144_);
lean_dec(v_a_3141_);
v___x_3146_ = lean_box(0);
v_isShared_3147_ = v_isSharedCheck_3208_;
goto v_resetjp_3145_;
}
v_resetjp_3145_:
{
lean_object* v___x_3148_; 
lean_inc(v_val_3144_);
v___x_3148_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices(v_val_3144_, v___y_3134_, v___y_3135_, v___y_3136_, v___y_3137_);
if (lean_obj_tag(v___x_3148_) == 0)
{
lean_object* v_a_3149_; uint8_t v___x_3150_; 
v_a_3149_ = lean_ctor_get(v___x_3148_, 0);
lean_inc(v_a_3149_);
lean_dec_ref_known(v___x_3148_, 1);
v___x_3150_ = lean_unbox(v_a_3149_);
if (v___x_3150_ == 0)
{
lean_object* v___x_3151_; 
v___x_3151_ = l_Lean_Meta_generalizeIndices(v_mvarId_3127_, v_majorFVarId_3129_, v___y_3134_, v___y_3135_, v___y_3136_, v___y_3137_);
if (lean_obj_tag(v___x_3151_) == 0)
{
lean_object* v_a_3152_; lean_object* v___y_3154_; lean_object* v___y_3155_; lean_object* v___y_3156_; lean_object* v___y_3157_; lean_object* v_options_3167_; uint8_t v_hasTrace_3168_; 
v_a_3152_ = lean_ctor_get(v___x_3151_, 0);
lean_inc(v_a_3152_);
lean_dec_ref_known(v___x_3151_, 1);
v_options_3167_ = lean_ctor_get(v___y_3136_, 2);
v_hasTrace_3168_ = lean_ctor_get_uint8(v_options_3167_, sizeof(void*)*1);
if (v_hasTrace_3168_ == 0)
{
lean_del_object(v___x_3146_);
lean_dec_ref(v___x_3132_);
v___y_3154_ = v___y_3134_;
v___y_3155_ = v___y_3135_;
v___y_3156_ = v___y_3136_;
v___y_3157_ = v___y_3137_;
goto v___jp_3153_;
}
else
{
lean_object* v_inheritedTraceOptions_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; uint8_t v___x_3175_; 
v_inheritedTraceOptions_3169_ = lean_ctor_get(v___y_3136_, 13);
v___x_3170_ = ((lean_object*)(l_Lean_Meta_Cases_cases___lam__0___closed__4));
v___x_3171_ = ((lean_object*)(l_Lean_Meta_Cases_cases___lam__0___closed__5));
v___x_3172_ = l_Lean_Name_mkStr3(v___x_3170_, v___x_3171_, v___x_3132_);
v___x_3173_ = ((lean_object*)(l_Lean_Meta_Cases_cases___lam__0___closed__7));
lean_inc(v___x_3172_);
v___x_3174_ = l_Lean_Name_append(v___x_3173_, v___x_3172_);
v___x_3175_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3169_, v_options_3167_, v___x_3174_);
lean_dec(v___x_3174_);
if (v___x_3175_ == 0)
{
lean_dec(v___x_3172_);
lean_del_object(v___x_3146_);
v___y_3154_ = v___y_3134_;
v___y_3155_ = v___y_3135_;
v___y_3156_ = v___y_3136_;
v___y_3157_ = v___y_3137_;
goto v___jp_3153_;
}
else
{
lean_object* v_mvarId_3176_; lean_object* v___x_3177_; lean_object* v___x_3179_; 
v_mvarId_3176_ = lean_ctor_get(v_a_3152_, 0);
v___x_3177_ = lean_obj_once(&l_Lean_Meta_Cases_cases___lam__0___closed__9, &l_Lean_Meta_Cases_cases___lam__0___closed__9_once, _init_l_Lean_Meta_Cases_cases___lam__0___closed__9);
lean_inc(v_mvarId_3176_);
if (v_isShared_3147_ == 0)
{
lean_ctor_set(v___x_3146_, 0, v_mvarId_3176_);
v___x_3179_ = v___x_3146_;
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
v___x_3181_ = l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0(v___x_3172_, v___x_3180_, v___y_3134_, v___y_3135_, v___y_3136_, v___y_3137_);
if (lean_obj_tag(v___x_3181_) == 0)
{
lean_dec_ref_known(v___x_3181_, 1);
v___y_3154_ = v___y_3134_;
v___y_3155_ = v___y_3135_;
v___y_3156_ = v___y_3136_;
v___y_3157_ = v___y_3137_;
goto v___jp_3153_;
}
else
{
lean_object* v_a_3182_; lean_object* v___x_3184_; uint8_t v_isShared_3185_; uint8_t v_isSharedCheck_3189_; 
lean_dec(v_a_3152_);
lean_dec(v_a_3149_);
lean_dec(v_val_3144_);
lean_dec(v_interestingCtors_x3f_3131_);
lean_dec_ref(v_givenNames_3130_);
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
v___jp_3153_:
{
lean_object* v_mvarId_3158_; lean_object* v_fvarId_3159_; lean_object* v_numEqs_3160_; uint8_t v___x_3161_; lean_object* v___x_3162_; 
v_mvarId_3158_ = lean_ctor_get(v_a_3152_, 0);
v_fvarId_3159_ = lean_ctor_get(v_a_3152_, 2);
v_numEqs_3160_ = lean_ctor_get(v_a_3152_, 3);
lean_inc(v_numEqs_3160_);
v___x_3161_ = lean_unbox(v_a_3149_);
lean_dec(v_a_3149_);
lean_inc(v_fvarId_3159_);
lean_inc(v_mvarId_3158_);
v___x_3162_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn(v_mvarId_3158_, v_fvarId_3159_, v_givenNames_3130_, v_val_3144_, v___x_3161_, v_interestingCtors_x3f_3131_, v___y_3154_, v___y_3155_, v___y_3156_, v___y_3157_);
if (lean_obj_tag(v___x_3162_) == 0)
{
lean_object* v_a_3163_; lean_object* v___x_3164_; 
v_a_3163_ = lean_ctor_get(v___x_3162_, 0);
lean_inc(v_a_3163_);
lean_dec_ref_known(v___x_3162_, 1);
v___x_3164_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices(v_a_3152_, v_a_3163_, v___y_3154_, v___y_3155_, v___y_3156_, v___y_3157_);
lean_dec(v_a_3152_);
if (lean_obj_tag(v___x_3164_) == 0)
{
lean_object* v_a_3165_; lean_object* v___x_3166_; 
v_a_3165_ = lean_ctor_get(v___x_3164_, 0);
lean_inc(v_a_3165_);
lean_dec_ref_known(v___x_3164_, 1);
v___x_3166_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs(v_numEqs_3160_, v_a_3165_, v___y_3154_, v___y_3155_, v___y_3156_, v___y_3157_);
lean_dec(v_a_3165_);
return v___x_3166_;
}
else
{
lean_dec(v_numEqs_3160_);
return v___x_3164_;
}
}
else
{
lean_dec(v_numEqs_3160_);
lean_dec(v_a_3152_);
return v___x_3162_;
}
}
}
else
{
lean_object* v_a_3191_; lean_object* v___x_3193_; uint8_t v_isShared_3194_; uint8_t v_isSharedCheck_3198_; 
lean_dec(v_a_3149_);
lean_del_object(v___x_3146_);
lean_dec(v_val_3144_);
lean_dec_ref(v___x_3132_);
lean_dec(v_interestingCtors_x3f_3131_);
lean_dec_ref(v_givenNames_3130_);
v_a_3191_ = lean_ctor_get(v___x_3151_, 0);
v_isSharedCheck_3198_ = !lean_is_exclusive(v___x_3151_);
if (v_isSharedCheck_3198_ == 0)
{
v___x_3193_ = v___x_3151_;
v_isShared_3194_ = v_isSharedCheck_3198_;
goto v_resetjp_3192_;
}
else
{
lean_inc(v_a_3191_);
lean_dec(v___x_3151_);
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
lean_dec(v_a_3149_);
lean_del_object(v___x_3146_);
lean_dec_ref(v___x_3132_);
v___x_3199_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn(v_mvarId_3127_, v_majorFVarId_3129_, v_givenNames_3130_, v_val_3144_, v_useNatCasesAuxOn_3133_, v_interestingCtors_x3f_3131_, v___y_3134_, v___y_3135_, v___y_3136_, v___y_3137_);
return v___x_3199_;
}
}
else
{
lean_object* v_a_3200_; lean_object* v___x_3202_; uint8_t v_isShared_3203_; uint8_t v_isSharedCheck_3207_; 
lean_del_object(v___x_3146_);
lean_dec(v_val_3144_);
lean_dec_ref(v___x_3132_);
lean_dec(v_interestingCtors_x3f_3131_);
lean_dec_ref(v_givenNames_3130_);
lean_dec(v_majorFVarId_3129_);
lean_dec(v_mvarId_3127_);
v_a_3200_ = lean_ctor_get(v___x_3148_, 0);
v_isSharedCheck_3207_ = !lean_is_exclusive(v___x_3148_);
if (v_isSharedCheck_3207_ == 0)
{
v___x_3202_ = v___x_3148_;
v_isShared_3203_ = v_isSharedCheck_3207_;
goto v_resetjp_3201_;
}
else
{
lean_inc(v_a_3200_);
lean_dec(v___x_3148_);
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
lean_dec_ref(v___x_3132_);
lean_dec(v_interestingCtors_x3f_3131_);
lean_dec_ref(v_givenNames_3130_);
lean_dec(v_majorFVarId_3129_);
lean_dec(v___x_3128_);
lean_dec(v_mvarId_3127_);
v_a_3209_ = lean_ctor_get(v___x_3140_, 0);
v_isSharedCheck_3216_ = !lean_is_exclusive(v___x_3140_);
if (v_isSharedCheck_3216_ == 0)
{
v___x_3211_ = v___x_3140_;
v_isShared_3212_ = v_isSharedCheck_3216_;
goto v_resetjp_3210_;
}
else
{
lean_inc(v_a_3209_);
lean_dec(v___x_3140_);
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
lean_dec_ref(v___x_3132_);
lean_dec(v_interestingCtors_x3f_3131_);
lean_dec_ref(v_givenNames_3130_);
lean_dec(v_majorFVarId_3129_);
lean_dec(v___x_3128_);
lean_dec(v_mvarId_3127_);
v_a_3217_ = lean_ctor_get(v___x_3139_, 0);
v_isSharedCheck_3224_ = !lean_is_exclusive(v___x_3139_);
if (v_isSharedCheck_3224_ == 0)
{
v___x_3219_ = v___x_3139_;
v_isShared_3220_ = v_isSharedCheck_3224_;
goto v_resetjp_3218_;
}
else
{
lean_inc(v_a_3217_);
lean_dec(v___x_3139_);
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
lean_inc(v_a_3257_);
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
lean_dec_ref_known(v___x_3256_, 1);
v___x_3260_ = l_Lean_Meta_throwNestedTacticEx___redArg(v___x_3253_, v_a_3257_, v_a_3247_, v_a_3248_, v_a_3249_, v_a_3250_);
return v___x_3260_;
}
else
{
lean_dec(v_a_3257_);
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
lean_dec(v_a_3305_);
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
uint8_t v___x_6243__boxed_3433_; lean_object* v_res_3434_; 
v___x_6243__boxed_3433_ = lean_unbox(v___x_3426_);
v_res_3434_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3___lam__0(v_mvarId_3423_, v___x_3424_, v___x_3425_, v___x_6243__boxed_3433_, v___x_3427_, v___y_3428_, v___y_3429_, v___y_3430_, v___y_3431_);
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
lean_object* v___x_3471_; 
lean_inc_ref(v_p_3440_);
lean_inc(v___y_3449_);
lean_inc_ref(v___y_3448_);
lean_inc(v___y_3447_);
lean_inc_ref(v___y_3446_);
lean_inc(v_val_3467_);
v___x_3471_ = lean_apply_6(v_p_3440_, v_val_3467_, v___y_3446_, v___y_3447_, v___y_3448_, v___y_3449_, lean_box(0));
if (lean_obj_tag(v___x_3471_) == 0)
{
lean_object* v_a_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; uint8_t v___x_3475_; 
v_a_3472_ = lean_ctor_get(v___x_3471_, 0);
lean_inc(v_a_3472_);
lean_dec_ref_known(v___x_3471_, 1);
v___x_3473_ = lean_box(0);
v___x_3474_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5___closed__0));
v___x_3475_ = lean_unbox(v_a_3472_);
lean_dec(v_a_3472_);
if (v___x_3475_ == 0)
{
lean_del_object(v___x_3469_);
lean_dec(v_val_3467_);
lean_dec(v_snd_3453_);
v_a_3459_ = v___x_3474_;
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
v_a_3459_ = v___x_3474_;
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
lean_ctor_set(v___x_3491_, 1, v___x_3473_);
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
v_a_3512_ = lean_ctor_get(v___x_3471_, 0);
v_isSharedCheck_3519_ = !lean_is_exclusive(v___x_3471_);
if (v_isSharedCheck_3519_ == 0)
{
v___x_3514_ = v___x_3471_;
v_isShared_3515_ = v_isSharedCheck_3519_;
goto v_resetjp_3513_;
}
else
{
lean_inc(v_a_3512_);
lean_dec(v___x_3471_);
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
lean_object* v___x_3568_; 
lean_inc_ref(v_p_3537_);
lean_inc(v___y_3546_);
lean_inc_ref(v___y_3545_);
lean_inc(v___y_3544_);
lean_inc_ref(v___y_3543_);
lean_inc(v_val_3564_);
v___x_3568_ = lean_apply_6(v_p_3537_, v_val_3564_, v___y_3543_, v___y_3544_, v___y_3545_, v___y_3546_, lean_box(0));
if (lean_obj_tag(v___x_3568_) == 0)
{
lean_object* v_a_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; uint8_t v___x_3572_; 
v_a_3569_ = lean_ctor_get(v___x_3568_, 0);
lean_inc(v_a_3569_);
lean_dec_ref_known(v___x_3568_, 1);
v___x_3570_ = lean_box(0);
v___x_3571_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5___closed__0));
v___x_3572_ = lean_unbox(v_a_3569_);
lean_dec(v_a_3569_);
if (v___x_3572_ == 0)
{
lean_del_object(v___x_3566_);
lean_dec(v_val_3564_);
lean_dec(v_snd_3550_);
v_a_3556_ = v___x_3571_;
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
v_a_3556_ = v___x_3571_;
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
lean_ctor_set(v___x_3588_, 1, v___x_3570_);
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
v_a_3609_ = lean_ctor_get(v___x_3568_, 0);
v_isSharedCheck_3616_ = !lean_is_exclusive(v___x_3568_);
if (v_isSharedCheck_3616_ == 0)
{
v___x_3611_ = v___x_3568_;
v_isShared_3612_ = v_isSharedCheck_3616_;
goto v_resetjp_3610_;
}
else
{
lean_inc(v_a_3609_);
lean_dec(v___x_3568_);
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
lean_object* v_a_3720_; lean_object* v___x_3721_; 
v_a_3720_ = lean_array_uget_borrowed(v_as_3705_, v_i_3707_);
lean_inc(v_snd_3716_);
lean_inc(v_mvarId_3704_);
lean_inc_ref(v_p_3703_);
v___x_3721_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2(v_init_3702_, v_p_3703_, v_mvarId_3704_, v_a_3720_, v_snd_3716_, v___y_3709_, v___y_3710_, v___y_3711_, v___y_3712_);
if (lean_obj_tag(v___x_3721_) == 0)
{
lean_object* v_a_3722_; lean_object* v___x_3724_; uint8_t v_isShared_3725_; uint8_t v_isSharedCheck_3741_; 
v_a_3722_ = lean_ctor_get(v___x_3721_, 0);
v_isSharedCheck_3741_ = !lean_is_exclusive(v___x_3721_);
if (v_isSharedCheck_3741_ == 0)
{
v___x_3724_ = v___x_3721_;
v_isShared_3725_ = v_isSharedCheck_3741_;
goto v_resetjp_3723_;
}
else
{
lean_inc(v_a_3722_);
lean_dec(v___x_3721_);
v___x_3724_ = lean_box(0);
v_isShared_3725_ = v_isSharedCheck_3741_;
goto v_resetjp_3723_;
}
v_resetjp_3723_:
{
if (lean_obj_tag(v_a_3722_) == 0)
{
lean_object* v___x_3726_; lean_object* v___x_3728_; 
lean_dec(v_mvarId_3704_);
lean_dec_ref(v_p_3703_);
v___x_3726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3726_, 0, v_a_3722_);
if (v_isShared_3719_ == 0)
{
lean_ctor_set(v___x_3718_, 0, v___x_3726_);
v___x_3728_ = v___x_3718_;
goto v_reusejp_3727_;
}
else
{
lean_object* v_reuseFailAlloc_3732_; 
v_reuseFailAlloc_3732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3732_, 0, v___x_3726_);
lean_ctor_set(v_reuseFailAlloc_3732_, 1, v_snd_3716_);
v___x_3728_ = v_reuseFailAlloc_3732_;
goto v_reusejp_3727_;
}
v_reusejp_3727_:
{
lean_object* v___x_3730_; 
if (v_isShared_3725_ == 0)
{
lean_ctor_set(v___x_3724_, 0, v___x_3728_);
v___x_3730_ = v___x_3724_;
goto v_reusejp_3729_;
}
else
{
lean_object* v_reuseFailAlloc_3731_; 
v_reuseFailAlloc_3731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3731_, 0, v___x_3728_);
v___x_3730_ = v_reuseFailAlloc_3731_;
goto v_reusejp_3729_;
}
v_reusejp_3729_:
{
return v___x_3730_;
}
}
}
else
{
lean_object* v_a_3733_; lean_object* v___x_3734_; lean_object* v___x_3736_; 
lean_del_object(v___x_3724_);
lean_dec(v_snd_3716_);
v_a_3733_ = lean_ctor_get(v_a_3722_, 0);
lean_inc(v_a_3733_);
lean_dec_ref_known(v_a_3722_, 1);
v___x_3734_ = lean_box(0);
if (v_isShared_3719_ == 0)
{
lean_ctor_set(v___x_3718_, 1, v_a_3733_);
lean_ctor_set(v___x_3718_, 0, v___x_3734_);
v___x_3736_ = v___x_3718_;
goto v_reusejp_3735_;
}
else
{
lean_object* v_reuseFailAlloc_3740_; 
v_reuseFailAlloc_3740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3740_, 0, v___x_3734_);
lean_ctor_set(v_reuseFailAlloc_3740_, 1, v_a_3733_);
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
v_a_3742_ = lean_ctor_get(v___x_3721_, 0);
v_isSharedCheck_3749_ = !lean_is_exclusive(v___x_3721_);
if (v_isSharedCheck_3749_ == 0)
{
v___x_3744_ = v___x_3721_;
v_isShared_3745_ = v_isSharedCheck_3749_;
goto v_resetjp_3743_;
}
else
{
lean_inc(v_a_3742_);
lean_dec(v___x_3721_);
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
lean_object* v___x_3812_; 
lean_inc_ref(v_p_3781_);
lean_inc(v___y_3790_);
lean_inc_ref(v___y_3789_);
lean_inc(v___y_3788_);
lean_inc_ref(v___y_3787_);
lean_inc(v_val_3808_);
v___x_3812_ = lean_apply_6(v_p_3781_, v_val_3808_, v___y_3787_, v___y_3788_, v___y_3789_, v___y_3790_, lean_box(0));
if (lean_obj_tag(v___x_3812_) == 0)
{
lean_object* v_a_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; uint8_t v___x_3816_; 
v_a_3813_ = lean_ctor_get(v___x_3812_, 0);
lean_inc(v_a_3813_);
lean_dec_ref_known(v___x_3812_, 1);
v___x_3814_ = lean_box(0);
v___x_3815_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3_spec__6___closed__0));
v___x_3816_ = lean_unbox(v_a_3813_);
lean_dec(v_a_3813_);
if (v___x_3816_ == 0)
{
lean_del_object(v___x_3810_);
lean_dec(v_val_3808_);
lean_dec(v_snd_3794_);
v_a_3800_ = v___x_3815_;
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
v_a_3800_ = v___x_3815_;
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
lean_ctor_set(v___x_3832_, 1, v___x_3814_);
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
v_a_3852_ = lean_ctor_get(v___x_3812_, 0);
v_isSharedCheck_3859_ = !lean_is_exclusive(v___x_3812_);
if (v_isSharedCheck_3859_ == 0)
{
v___x_3854_ = v___x_3812_;
v_isShared_3855_ = v_isSharedCheck_3859_;
goto v_resetjp_3853_;
}
else
{
lean_inc(v_a_3852_);
lean_dec(v___x_3812_);
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
lean_object* v___x_3908_; 
lean_inc_ref(v_p_3877_);
lean_inc(v___y_3886_);
lean_inc_ref(v___y_3885_);
lean_inc(v___y_3884_);
lean_inc_ref(v___y_3883_);
lean_inc(v_val_3904_);
v___x_3908_ = lean_apply_6(v_p_3877_, v_val_3904_, v___y_3883_, v___y_3884_, v___y_3885_, v___y_3886_, lean_box(0));
if (lean_obj_tag(v___x_3908_) == 0)
{
lean_object* v_a_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; uint8_t v___x_3912_; 
v_a_3909_ = lean_ctor_get(v___x_3908_, 0);
lean_inc(v_a_3909_);
lean_dec_ref_known(v___x_3908_, 1);
v___x_3910_ = lean_box(0);
v___x_3911_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3_spec__6___closed__0));
v___x_3912_ = lean_unbox(v_a_3909_);
lean_dec(v_a_3909_);
if (v___x_3912_ == 0)
{
lean_del_object(v___x_3906_);
lean_dec(v_val_3904_);
lean_dec(v_snd_3890_);
v_a_3896_ = v___x_3911_;
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
v_a_3896_ = v___x_3911_;
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
lean_ctor_set(v___x_3928_, 1, v___x_3910_);
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
v_a_3948_ = lean_ctor_get(v___x_3908_, 0);
v_isSharedCheck_3955_ = !lean_is_exclusive(v___x_3908_);
if (v_isSharedCheck_3955_ == 0)
{
v___x_3950_ = v___x_3908_;
v_isShared_3951_ = v_isSharedCheck_3955_;
goto v_resetjp_3949_;
}
else
{
lean_inc(v_a_3948_);
lean_dec(v___x_3908_);
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
