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
lean_object* l_Lean_Meta_getLocalInstances___redArg(lean_object*);
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
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
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
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_saveState___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_induction(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_FVarSubst_erase(lean_object*, lean_object*);
lean_object* l_Lean_Meta_FVarSubst_insert(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkCasesOnName(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkSparseCasesOn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkCtorIdxName(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Meta_FVarSubst_get(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_clear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_acyclic___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_unifyEq_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_Meta_FVarSubst_apply(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwNestedTacticEx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_Meta_saturate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_exactlyOne(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNot(lean_object*);
lean_object* l_Lean_mkOr(lean_object*, lean_object*);
lean_object* l_Lean_mkEM(lean_object*);
lean_object* l_Lean_MVarId_assert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_inlineExpr(lean_object*, lean_object*);
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
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg___closed__2;
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
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_isTracingEnabledFor___at___00Lean_Meta_Cases_cases_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Cases_cases_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_Cases_cases_spec__0___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00Lean_Meta_Cases_cases_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_Cases_cases_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Cases_cases_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_Cases_cases_spec__0___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Cases_cases_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Cases_cases_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Cases_cases_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Cases_cases_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__1___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__1___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__1___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__1___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__1___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Meta_Cases_cases___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "after generalizeIndices\n"};
static const lean_object* l_Lean_Meta_Cases_cases___lam__0___closed__6 = (const lean_object*)&l_Lean_Meta_Cases_cases___lam__0___closed__6_value;
static lean_once_cell_t l_Lean_Meta_Cases_cases___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Cases_cases___lam__0___closed__7;
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
static const lean_string_object l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 51, .m_capacity = 51, .m_length = 50, .m_data = "Tactic `byCases` failed: Unexpected new hypothesis"};
static const lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MVarId_byCases___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "hByCases"};
static const lean_object* l_Lean_MVarId_byCases___closed__0 = (const lean_object*)&l_Lean_MVarId_byCases___closed__0_value;
static const lean_ctor_object l_Lean_MVarId_byCases___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_byCases___closed__0_value),LEAN_SCALAR_PTR_LITERAL(109, 54, 82, 33, 211, 106, 177, 110)}};
static const lean_object* l_Lean_MVarId_byCases___closed__1 = (const lean_object*)&l_Lean_MVarId_byCases___closed__1_value;
static const lean_string_object l_Lean_MVarId_byCases___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Tactic `byCases` failed: Casing on"};
static const lean_object* l_Lean_MVarId_byCases___closed__2 = (const lean_object*)&l_Lean_MVarId_byCases___closed__2_value;
static lean_once_cell_t l_Lean_MVarId_byCases___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_byCases___closed__3;
static const lean_string_object l_Lean_MVarId_byCases___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "unexpectedly did not yield two subgoals"};
static const lean_object* l_Lean_MVarId_byCases___closed__4 = (const lean_object*)&l_Lean_MVarId_byCases___closed__4_value;
static lean_once_cell_t l_Lean_MVarId_byCases___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_byCases___closed__5;
LEAN_EXPORT lean_object* l_Lean_MVarId_byCases(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_byCases___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MVarId_byCasesDec___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Decidable"};
static const lean_object* l_Lean_MVarId_byCasesDec___closed__0 = (const lean_object*)&l_Lean_MVarId_byCasesDec___closed__0_value;
static const lean_ctor_object l_Lean_MVarId_byCasesDec___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_byCasesDec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(87, 187, 205, 215, 218, 218, 68, 60)}};
static const lean_object* l_Lean_MVarId_byCasesDec___closed__1 = (const lean_object*)&l_Lean_MVarId_byCasesDec___closed__1_value;
static lean_once_cell_t l_Lean_MVarId_byCasesDec___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_byCasesDec___closed__2;
static const lean_string_object l_Lean_MVarId_byCasesDec___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "Tactic `byCasesDec` failed: Casing on"};
static const lean_object* l_Lean_MVarId_byCasesDec___closed__3 = (const lean_object*)&l_Lean_MVarId_byCasesDec___closed__3_value;
static lean_once_cell_t l_Lean_MVarId_byCasesDec___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_byCasesDec___closed__4;
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
lean_inc(v_a_105_);
lean_inc_ref(v_a_104_);
lean_inc(v_a_103_);
lean_inc_ref(v_a_102_);
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
lean_dec_ref(v___x_112_);
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
lean_dec(v_a_105_);
lean_dec_ref(v_a_104_);
lean_dec(v_a_103_);
lean_dec_ref(v_a_102_);
return v___x_119_;
}
else
{
lean_object* v_val_120_; 
v_val_120_ = lean_ctor_get(v___x_118_, 0);
lean_inc(v_val_120_);
lean_dec_ref(v___x_118_);
if (lean_obj_tag(v_val_120_) == 5)
{
lean_object* v_val_121_; lean_object* v_numParams_122_; lean_object* v_nargs_123_; lean_object* v_dummy_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_133_; 
lean_dec(v_a_105_);
lean_dec_ref(v_a_104_);
lean_dec(v_a_103_);
lean_dec_ref(v_a_102_);
v_val_121_ = lean_ctor_get(v_val_120_, 0);
lean_inc_ref(v_val_121_);
lean_dec_ref(v_val_120_);
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
lean_dec(v_a_105_);
lean_dec_ref(v_a_104_);
lean_dec(v_a_103_);
lean_dec_ref(v_a_102_);
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
lean_dec(v_a_105_);
lean_dec_ref(v_a_104_);
lean_dec(v_a_103_);
lean_dec_ref(v_a_102_);
return v___x_136_;
}
}
}
else
{
lean_object* v_a_138_; lean_object* v___x_140_; uint8_t v_isShared_141_; uint8_t v_isSharedCheck_145_; 
lean_dec(v_a_105_);
lean_dec_ref(v_a_104_);
lean_dec(v_a_103_);
lean_dec_ref(v_a_102_);
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
lean_dec_ref(v___x_173_);
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
lean_dec_ref(v___x_175_);
lean_inc(v_a_171_);
lean_inc_ref(v_a_170_);
lean_inc(v_a_169_);
lean_inc_ref(v_a_168_);
lean_inc(v_a_174_);
v___x_177_ = l_Lean_Meta_getLevel(v_a_174_, v_a_168_, v_a_169_, v_a_170_, v_a_171_);
if (lean_obj_tag(v___x_177_) == 0)
{
lean_object* v_a_178_; lean_object* v___x_179_; 
v_a_178_ = lean_ctor_get(v___x_177_, 0);
lean_inc(v_a_178_);
lean_dec_ref(v___x_177_);
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
lean_dec(v_a_171_);
lean_dec_ref(v_a_170_);
lean_dec(v_a_169_);
lean_dec_ref(v_a_168_);
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
lean_dec(v_a_171_);
lean_dec_ref(v_a_170_);
lean_dec(v_a_169_);
lean_dec_ref(v_a_168_);
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
lean_dec(v_a_171_);
lean_dec_ref(v_a_170_);
lean_dec(v_a_169_);
lean_dec_ref(v_a_168_);
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
return v_res_249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0_spec__0___redArg___lam__0(lean_object* v_k_250_, lean_object* v_b_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_){
_start:
{
lean_object* v___x_257_; 
v___x_257_ = lean_apply_6(v_k_250_, v_b_251_, v___y_252_, v___y_253_, v___y_254_, v___y_255_, lean_box(0));
return v___x_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_k_258_, lean_object* v_b_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_){
_start:
{
lean_object* v_res_265_; 
v_res_265_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0_spec__0___redArg___lam__0(v_k_258_, v_b_259_, v___y_260_, v___y_261_, v___y_262_, v___y_263_);
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
return v_res_326_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___redArg___lam__0___boxed(lean_object* v_i_327_, lean_object* v_newEqs_328_, lean_object* v_newRefls_329_, lean_object* v_snd_330_, lean_object* v_targets_331_, lean_object* v_targetsNew_332_, lean_object* v_k_333_, lean_object* v_newEq_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_){
_start:
{
lean_object* v_res_340_; 
v_res_340_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___redArg___lam__0(v_i_327_, v_newEqs_328_, v_newRefls_329_, v_snd_330_, v_targets_331_, v_targetsNew_332_, v_k_333_, v_newEq_334_, v___y_335_, v___y_336_, v___y_337_, v___y_338_);
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
v___x_357_ = lean_apply_7(v_k_346_, v_newEqs_348_, v_newRefls_349_, v_a_350_, v_a_351_, v_a_352_, v_a_353_, lean_box(0));
return v___x_357_;
}
else
{
lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_358_ = l_Lean_instInhabitedExpr;
v___x_359_ = lean_array_get_borrowed(v___x_358_, v_targets_344_, v_i_347_);
v___x_360_ = lean_array_get_borrowed(v___x_358_, v_targetsNew_345_, v_i_347_);
lean_inc(v_a_353_);
lean_inc_ref(v_a_352_);
lean_inc(v_a_351_);
lean_inc_ref(v_a_350_);
lean_inc(v___x_360_);
lean_inc(v___x_359_);
v___x_361_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof(v___x_359_, v___x_360_, v_a_350_, v_a_351_, v_a_352_, v_a_353_);
if (lean_obj_tag(v___x_361_) == 0)
{
lean_object* v_a_362_; lean_object* v_fst_363_; lean_object* v_snd_364_; lean_object* v___f_365_; lean_object* v___x_366_; lean_object* v___x_367_; 
v_a_362_ = lean_ctor_get(v___x_361_, 0);
lean_inc(v_a_362_);
lean_dec_ref(v___x_361_);
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
lean_dec(v_a_353_);
lean_dec_ref(v_a_352_);
lean_dec(v_a_351_);
lean_dec_ref(v_a_350_);
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
return v_res_519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_generalizeTargetsEq_spec__0___redArg___lam__0(lean_object* v_k_520_, lean_object* v_b_521_, lean_object* v_c_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_){
_start:
{
lean_object* v___x_528_; 
v___x_528_ = lean_apply_7(v_k_520_, v_b_521_, v_c_522_, v___y_523_, v___y_524_, v___y_525_, v___y_526_, lean_box(0));
return v___x_528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_generalizeTargetsEq_spec__0___redArg___lam__0___boxed(lean_object* v_k_529_, lean_object* v_b_530_, lean_object* v_c_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_){
_start:
{
lean_object* v_res_537_; 
v_res_537_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_generalizeTargetsEq_spec__0___redArg___lam__0(v_k_529_, v_b_530_, v_c_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_);
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
lean_dec_ref(v___x_660_);
v___x_662_ = 0;
v___x_663_ = 1;
v___x_664_ = 1;
v___x_665_ = l_Lean_Meta_mkForallFVars(v_eqs_653_, v_a_661_, v___x_662_, v___x_663_, v___x_663_, v___x_664_, v___y_655_, v___y_656_, v___y_657_, v___y_658_);
if (lean_obj_tag(v___x_665_) == 0)
{
lean_object* v_a_666_; lean_object* v___x_667_; 
v_a_666_ = lean_ctor_get(v___x_665_, 0);
lean_inc(v_a_666_);
lean_dec_ref(v___x_665_);
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
lean_dec(v___y_724_);
lean_dec_ref(v___y_723_);
lean_dec(v___y_722_);
lean_dec_ref(v___y_721_);
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
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg___closed__0(void){
_start:
{
size_t v___x_801_; size_t v___x_802_; size_t v___x_803_; 
v___x_801_ = ((size_t)5ULL);
v___x_802_ = ((size_t)1ULL);
v___x_803_ = lean_usize_shift_left(v___x_802_, v___x_801_);
return v___x_803_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg___closed__1(void){
_start:
{
size_t v___x_804_; size_t v___x_805_; size_t v___x_806_; 
v___x_804_ = ((size_t)1ULL);
v___x_805_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg___closed__0);
v___x_806_ = lean_usize_sub(v___x_805_, v___x_804_);
return v___x_806_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_807_; 
v___x_807_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_807_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg(lean_object* v_x_808_, size_t v_x_809_, size_t v_x_810_, lean_object* v_x_811_, lean_object* v_x_812_){
_start:
{
if (lean_obj_tag(v_x_808_) == 0)
{
lean_object* v_es_813_; size_t v___x_814_; size_t v___x_815_; size_t v___x_816_; size_t v___x_817_; lean_object* v_j_818_; lean_object* v___x_819_; uint8_t v___x_820_; 
v_es_813_ = lean_ctor_get(v_x_808_, 0);
v___x_814_ = ((size_t)5ULL);
v___x_815_ = ((size_t)1ULL);
v___x_816_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg___closed__1);
v___x_817_ = lean_usize_land(v_x_809_, v___x_816_);
v_j_818_ = lean_usize_to_nat(v___x_817_);
v___x_819_ = lean_array_get_size(v_es_813_);
v___x_820_ = lean_nat_dec_lt(v_j_818_, v___x_819_);
if (v___x_820_ == 0)
{
lean_dec(v_j_818_);
lean_dec(v_x_812_);
lean_dec(v_x_811_);
return v_x_808_;
}
else
{
lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_857_; 
lean_inc_ref(v_es_813_);
v_isSharedCheck_857_ = !lean_is_exclusive(v_x_808_);
if (v_isSharedCheck_857_ == 0)
{
lean_object* v_unused_858_; 
v_unused_858_ = lean_ctor_get(v_x_808_, 0);
lean_dec(v_unused_858_);
v___x_822_ = v_x_808_;
v_isShared_823_ = v_isSharedCheck_857_;
goto v_resetjp_821_;
}
else
{
lean_dec(v_x_808_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_857_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
lean_object* v_v_824_; lean_object* v___x_825_; lean_object* v_xs_x27_826_; lean_object* v___y_828_; 
v_v_824_ = lean_array_fget(v_es_813_, v_j_818_);
v___x_825_ = lean_box(0);
v_xs_x27_826_ = lean_array_fset(v_es_813_, v_j_818_, v___x_825_);
switch(lean_obj_tag(v_v_824_))
{
case 0:
{
lean_object* v_key_833_; lean_object* v_val_834_; lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_844_; 
v_key_833_ = lean_ctor_get(v_v_824_, 0);
v_val_834_ = lean_ctor_get(v_v_824_, 1);
v_isSharedCheck_844_ = !lean_is_exclusive(v_v_824_);
if (v_isSharedCheck_844_ == 0)
{
v___x_836_ = v_v_824_;
v_isShared_837_ = v_isSharedCheck_844_;
goto v_resetjp_835_;
}
else
{
lean_inc(v_val_834_);
lean_inc(v_key_833_);
lean_dec(v_v_824_);
v___x_836_ = lean_box(0);
v_isShared_837_ = v_isSharedCheck_844_;
goto v_resetjp_835_;
}
v_resetjp_835_:
{
uint8_t v___x_838_; 
v___x_838_ = l_Lean_instBEqMVarId_beq(v_x_811_, v_key_833_);
if (v___x_838_ == 0)
{
lean_object* v___x_839_; lean_object* v___x_840_; 
lean_del_object(v___x_836_);
v___x_839_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_833_, v_val_834_, v_x_811_, v_x_812_);
v___x_840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_840_, 0, v___x_839_);
v___y_828_ = v___x_840_;
goto v___jp_827_;
}
else
{
lean_object* v___x_842_; 
lean_dec(v_val_834_);
lean_dec(v_key_833_);
if (v_isShared_837_ == 0)
{
lean_ctor_set(v___x_836_, 1, v_x_812_);
lean_ctor_set(v___x_836_, 0, v_x_811_);
v___x_842_ = v___x_836_;
goto v_reusejp_841_;
}
else
{
lean_object* v_reuseFailAlloc_843_; 
v_reuseFailAlloc_843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_843_, 0, v_x_811_);
lean_ctor_set(v_reuseFailAlloc_843_, 1, v_x_812_);
v___x_842_ = v_reuseFailAlloc_843_;
goto v_reusejp_841_;
}
v_reusejp_841_:
{
v___y_828_ = v___x_842_;
goto v___jp_827_;
}
}
}
}
case 1:
{
lean_object* v_node_845_; lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_855_; 
v_node_845_ = lean_ctor_get(v_v_824_, 0);
v_isSharedCheck_855_ = !lean_is_exclusive(v_v_824_);
if (v_isSharedCheck_855_ == 0)
{
v___x_847_ = v_v_824_;
v_isShared_848_ = v_isSharedCheck_855_;
goto v_resetjp_846_;
}
else
{
lean_inc(v_node_845_);
lean_dec(v_v_824_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_855_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
size_t v___x_849_; size_t v___x_850_; lean_object* v___x_851_; lean_object* v___x_853_; 
v___x_849_ = lean_usize_shift_right(v_x_809_, v___x_814_);
v___x_850_ = lean_usize_add(v_x_810_, v___x_815_);
v___x_851_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg(v_node_845_, v___x_849_, v___x_850_, v_x_811_, v_x_812_);
if (v_isShared_848_ == 0)
{
lean_ctor_set(v___x_847_, 0, v___x_851_);
v___x_853_ = v___x_847_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v___x_851_);
v___x_853_ = v_reuseFailAlloc_854_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
v___y_828_ = v___x_853_;
goto v___jp_827_;
}
}
}
default: 
{
lean_object* v___x_856_; 
v___x_856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_856_, 0, v_x_811_);
lean_ctor_set(v___x_856_, 1, v_x_812_);
v___y_828_ = v___x_856_;
goto v___jp_827_;
}
}
v___jp_827_:
{
lean_object* v___x_829_; lean_object* v___x_831_; 
v___x_829_ = lean_array_fset(v_xs_x27_826_, v_j_818_, v___y_828_);
lean_dec(v_j_818_);
if (v_isShared_823_ == 0)
{
lean_ctor_set(v___x_822_, 0, v___x_829_);
v___x_831_ = v___x_822_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v___x_829_);
v___x_831_ = v_reuseFailAlloc_832_;
goto v_reusejp_830_;
}
v_reusejp_830_:
{
return v___x_831_;
}
}
}
}
}
else
{
lean_object* v_ks_859_; lean_object* v_vs_860_; lean_object* v___x_862_; uint8_t v_isShared_863_; uint8_t v_isSharedCheck_880_; 
v_ks_859_ = lean_ctor_get(v_x_808_, 0);
v_vs_860_ = lean_ctor_get(v_x_808_, 1);
v_isSharedCheck_880_ = !lean_is_exclusive(v_x_808_);
if (v_isSharedCheck_880_ == 0)
{
v___x_862_ = v_x_808_;
v_isShared_863_ = v_isSharedCheck_880_;
goto v_resetjp_861_;
}
else
{
lean_inc(v_vs_860_);
lean_inc(v_ks_859_);
lean_dec(v_x_808_);
v___x_862_ = lean_box(0);
v_isShared_863_ = v_isSharedCheck_880_;
goto v_resetjp_861_;
}
v_resetjp_861_:
{
lean_object* v___x_865_; 
if (v_isShared_863_ == 0)
{
v___x_865_ = v___x_862_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v_ks_859_);
lean_ctor_set(v_reuseFailAlloc_879_, 1, v_vs_860_);
v___x_865_ = v_reuseFailAlloc_879_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
lean_object* v_newNode_866_; uint8_t v___y_868_; size_t v___x_874_; uint8_t v___x_875_; 
v_newNode_866_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__4___redArg(v___x_865_, v_x_811_, v_x_812_);
v___x_874_ = ((size_t)7ULL);
v___x_875_ = lean_usize_dec_le(v___x_874_, v_x_810_);
if (v___x_875_ == 0)
{
lean_object* v___x_876_; lean_object* v___x_877_; uint8_t v___x_878_; 
v___x_876_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_866_);
v___x_877_ = lean_unsigned_to_nat(4u);
v___x_878_ = lean_nat_dec_lt(v___x_876_, v___x_877_);
lean_dec(v___x_876_);
v___y_868_ = v___x_878_;
goto v___jp_867_;
}
else
{
v___y_868_ = v___x_875_;
goto v___jp_867_;
}
v___jp_867_:
{
if (v___y_868_ == 0)
{
lean_object* v_ks_869_; lean_object* v_vs_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; 
v_ks_869_ = lean_ctor_get(v_newNode_866_, 0);
lean_inc_ref(v_ks_869_);
v_vs_870_ = lean_ctor_get(v_newNode_866_, 1);
lean_inc_ref(v_vs_870_);
lean_dec_ref(v_newNode_866_);
v___x_871_ = lean_unsigned_to_nat(0u);
v___x_872_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg___closed__2);
v___x_873_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__5___redArg(v_x_810_, v_ks_869_, v_vs_870_, v___x_871_, v___x_872_);
lean_dec_ref(v_vs_870_);
lean_dec_ref(v_ks_869_);
return v___x_873_;
}
else
{
return v_newNode_866_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__5___redArg(size_t v_depth_881_, lean_object* v_keys_882_, lean_object* v_vals_883_, lean_object* v_i_884_, lean_object* v_entries_885_){
_start:
{
lean_object* v___x_886_; uint8_t v___x_887_; 
v___x_886_ = lean_array_get_size(v_keys_882_);
v___x_887_ = lean_nat_dec_lt(v_i_884_, v___x_886_);
if (v___x_887_ == 0)
{
lean_dec(v_i_884_);
return v_entries_885_;
}
else
{
lean_object* v_k_888_; lean_object* v_v_889_; uint64_t v___x_890_; size_t v_h_891_; size_t v___x_892_; lean_object* v___x_893_; size_t v___x_894_; size_t v___x_895_; size_t v___x_896_; size_t v_h_897_; lean_object* v___x_898_; lean_object* v___x_899_; 
v_k_888_ = lean_array_fget_borrowed(v_keys_882_, v_i_884_);
v_v_889_ = lean_array_fget_borrowed(v_vals_883_, v_i_884_);
v___x_890_ = l_Lean_instHashableMVarId_hash(v_k_888_);
v_h_891_ = lean_uint64_to_usize(v___x_890_);
v___x_892_ = ((size_t)5ULL);
v___x_893_ = lean_unsigned_to_nat(1u);
v___x_894_ = ((size_t)1ULL);
v___x_895_ = lean_usize_sub(v_depth_881_, v___x_894_);
v___x_896_ = lean_usize_mul(v___x_892_, v___x_895_);
v_h_897_ = lean_usize_shift_right(v_h_891_, v___x_896_);
v___x_898_ = lean_nat_add(v_i_884_, v___x_893_);
lean_dec(v_i_884_);
lean_inc(v_v_889_);
lean_inc(v_k_888_);
v___x_899_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg(v_entries_885_, v_h_897_, v_depth_881_, v_k_888_, v_v_889_);
v_i_884_ = v___x_898_;
v_entries_885_ = v___x_899_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__5___redArg___boxed(lean_object* v_depth_901_, lean_object* v_keys_902_, lean_object* v_vals_903_, lean_object* v_i_904_, lean_object* v_entries_905_){
_start:
{
size_t v_depth_boxed_906_; lean_object* v_res_907_; 
v_depth_boxed_906_ = lean_unbox_usize(v_depth_901_);
lean_dec(v_depth_901_);
v_res_907_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__5___redArg(v_depth_boxed_906_, v_keys_902_, v_vals_903_, v_i_904_, v_entries_905_);
lean_dec_ref(v_vals_903_);
lean_dec_ref(v_keys_902_);
return v_res_907_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_x_908_, lean_object* v_x_909_, lean_object* v_x_910_, lean_object* v_x_911_, lean_object* v_x_912_){
_start:
{
size_t v_x_2694__boxed_913_; size_t v_x_2695__boxed_914_; lean_object* v_res_915_; 
v_x_2694__boxed_913_ = lean_unbox_usize(v_x_909_);
lean_dec(v_x_909_);
v_x_2695__boxed_914_ = lean_unbox_usize(v_x_910_);
lean_dec(v_x_910_);
v_res_915_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg(v_x_908_, v_x_2694__boxed_913_, v_x_2695__boxed_914_, v_x_911_, v_x_912_);
return v_res_915_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1___redArg(lean_object* v_x_916_, lean_object* v_x_917_, lean_object* v_x_918_){
_start:
{
uint64_t v___x_919_; size_t v___x_920_; size_t v___x_921_; lean_object* v___x_922_; 
v___x_919_ = l_Lean_instHashableMVarId_hash(v_x_917_);
v___x_920_ = lean_uint64_to_usize(v___x_919_);
v___x_921_ = ((size_t)1ULL);
v___x_922_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg(v_x_916_, v___x_920_, v___x_921_, v_x_917_, v_x_918_);
return v___x_922_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1___redArg(lean_object* v_mvarId_923_, lean_object* v_val_924_, lean_object* v___y_925_){
_start:
{
lean_object* v___x_927_; lean_object* v_mctx_928_; lean_object* v_cache_929_; lean_object* v_zetaDeltaFVarIds_930_; lean_object* v_postponed_931_; lean_object* v_diag_932_; lean_object* v___x_934_; uint8_t v_isShared_935_; uint8_t v_isSharedCheck_959_; 
v___x_927_ = lean_st_ref_take(v___y_925_);
v_mctx_928_ = lean_ctor_get(v___x_927_, 0);
v_cache_929_ = lean_ctor_get(v___x_927_, 1);
v_zetaDeltaFVarIds_930_ = lean_ctor_get(v___x_927_, 2);
v_postponed_931_ = lean_ctor_get(v___x_927_, 3);
v_diag_932_ = lean_ctor_get(v___x_927_, 4);
v_isSharedCheck_959_ = !lean_is_exclusive(v___x_927_);
if (v_isSharedCheck_959_ == 0)
{
v___x_934_ = v___x_927_;
v_isShared_935_ = v_isSharedCheck_959_;
goto v_resetjp_933_;
}
else
{
lean_inc(v_diag_932_);
lean_inc(v_postponed_931_);
lean_inc(v_zetaDeltaFVarIds_930_);
lean_inc(v_cache_929_);
lean_inc(v_mctx_928_);
lean_dec(v___x_927_);
v___x_934_ = lean_box(0);
v_isShared_935_ = v_isSharedCheck_959_;
goto v_resetjp_933_;
}
v_resetjp_933_:
{
lean_object* v_depth_936_; lean_object* v_levelAssignDepth_937_; lean_object* v_mvarCounter_938_; lean_object* v_lDepth_939_; lean_object* v_decls_940_; lean_object* v_userNames_941_; lean_object* v_lAssignment_942_; lean_object* v_eAssignment_943_; lean_object* v_dAssignment_944_; lean_object* v___x_946_; uint8_t v_isShared_947_; uint8_t v_isSharedCheck_958_; 
v_depth_936_ = lean_ctor_get(v_mctx_928_, 0);
v_levelAssignDepth_937_ = lean_ctor_get(v_mctx_928_, 1);
v_mvarCounter_938_ = lean_ctor_get(v_mctx_928_, 2);
v_lDepth_939_ = lean_ctor_get(v_mctx_928_, 3);
v_decls_940_ = lean_ctor_get(v_mctx_928_, 4);
v_userNames_941_ = lean_ctor_get(v_mctx_928_, 5);
v_lAssignment_942_ = lean_ctor_get(v_mctx_928_, 6);
v_eAssignment_943_ = lean_ctor_get(v_mctx_928_, 7);
v_dAssignment_944_ = lean_ctor_get(v_mctx_928_, 8);
v_isSharedCheck_958_ = !lean_is_exclusive(v_mctx_928_);
if (v_isSharedCheck_958_ == 0)
{
v___x_946_ = v_mctx_928_;
v_isShared_947_ = v_isSharedCheck_958_;
goto v_resetjp_945_;
}
else
{
lean_inc(v_dAssignment_944_);
lean_inc(v_eAssignment_943_);
lean_inc(v_lAssignment_942_);
lean_inc(v_userNames_941_);
lean_inc(v_decls_940_);
lean_inc(v_lDepth_939_);
lean_inc(v_mvarCounter_938_);
lean_inc(v_levelAssignDepth_937_);
lean_inc(v_depth_936_);
lean_dec(v_mctx_928_);
v___x_946_ = lean_box(0);
v_isShared_947_ = v_isSharedCheck_958_;
goto v_resetjp_945_;
}
v_resetjp_945_:
{
lean_object* v___x_948_; lean_object* v___x_950_; 
v___x_948_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1___redArg(v_eAssignment_943_, v_mvarId_923_, v_val_924_);
if (v_isShared_947_ == 0)
{
lean_ctor_set(v___x_946_, 7, v___x_948_);
v___x_950_ = v___x_946_;
goto v_reusejp_949_;
}
else
{
lean_object* v_reuseFailAlloc_957_; 
v_reuseFailAlloc_957_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_957_, 0, v_depth_936_);
lean_ctor_set(v_reuseFailAlloc_957_, 1, v_levelAssignDepth_937_);
lean_ctor_set(v_reuseFailAlloc_957_, 2, v_mvarCounter_938_);
lean_ctor_set(v_reuseFailAlloc_957_, 3, v_lDepth_939_);
lean_ctor_set(v_reuseFailAlloc_957_, 4, v_decls_940_);
lean_ctor_set(v_reuseFailAlloc_957_, 5, v_userNames_941_);
lean_ctor_set(v_reuseFailAlloc_957_, 6, v_lAssignment_942_);
lean_ctor_set(v_reuseFailAlloc_957_, 7, v___x_948_);
lean_ctor_set(v_reuseFailAlloc_957_, 8, v_dAssignment_944_);
v___x_950_ = v_reuseFailAlloc_957_;
goto v_reusejp_949_;
}
v_reusejp_949_:
{
lean_object* v___x_952_; 
if (v_isShared_935_ == 0)
{
lean_ctor_set(v___x_934_, 0, v___x_950_);
v___x_952_ = v___x_934_;
goto v_reusejp_951_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v___x_950_);
lean_ctor_set(v_reuseFailAlloc_956_, 1, v_cache_929_);
lean_ctor_set(v_reuseFailAlloc_956_, 2, v_zetaDeltaFVarIds_930_);
lean_ctor_set(v_reuseFailAlloc_956_, 3, v_postponed_931_);
lean_ctor_set(v_reuseFailAlloc_956_, 4, v_diag_932_);
v___x_952_ = v_reuseFailAlloc_956_;
goto v_reusejp_951_;
}
v_reusejp_951_:
{
lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; 
v___x_953_ = lean_st_ref_set(v___y_925_, v___x_952_);
v___x_954_ = lean_box(0);
v___x_955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_955_, 0, v___x_954_);
return v___x_955_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1___redArg___boxed(lean_object* v_mvarId_960_, lean_object* v_val_961_, lean_object* v___y_962_, lean_object* v___y_963_){
_start:
{
lean_object* v_res_964_; 
v_res_964_ = l_Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1___redArg(v_mvarId_960_, v_val_961_, v___y_962_);
lean_dec(v___y_962_);
return v_res_964_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeTargetsEq___lam__2(lean_object* v_mvarId_965_, lean_object* v___x_966_, lean_object* v_motiveType_967_, lean_object* v___f_968_, lean_object* v_targets_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_){
_start:
{
lean_object* v___x_975_; 
lean_inc(v_mvarId_965_);
v___x_975_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_965_, v___x_966_, v___y_970_, v___y_971_, v___y_972_, v___y_973_);
if (lean_obj_tag(v___x_975_) == 0)
{
uint8_t v___x_976_; lean_object* v___x_977_; 
lean_dec_ref(v___x_975_);
v___x_976_ = 0;
lean_inc(v___y_973_);
lean_inc_ref(v___y_972_);
lean_inc(v___y_971_);
lean_inc_ref(v___y_970_);
v___x_977_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_generalizeTargetsEq_spec__0___redArg(v_motiveType_967_, v___f_968_, v___x_976_, v___x_976_, v___y_970_, v___y_971_, v___y_972_, v___y_973_);
if (lean_obj_tag(v___x_977_) == 0)
{
lean_object* v_a_978_; lean_object* v_fst_979_; lean_object* v_snd_980_; lean_object* v___x_981_; 
v_a_978_ = lean_ctor_get(v___x_977_, 0);
lean_inc(v_a_978_);
lean_dec_ref(v___x_977_);
v_fst_979_ = lean_ctor_get(v_a_978_, 0);
lean_inc(v_fst_979_);
v_snd_980_ = lean_ctor_get(v_a_978_, 1);
lean_inc(v_snd_980_);
lean_dec(v_a_978_);
lean_inc(v_mvarId_965_);
v___x_981_ = l_Lean_MVarId_getTag(v_mvarId_965_, v___y_970_, v___y_971_, v___y_972_, v___y_973_);
if (lean_obj_tag(v___x_981_) == 0)
{
lean_object* v_a_982_; lean_object* v___x_983_; 
v_a_982_ = lean_ctor_get(v___x_981_, 0);
lean_inc(v_a_982_);
lean_dec_ref(v___x_981_);
v___x_983_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_fst_979_, v_a_982_, v___y_970_, v___y_971_, v___y_972_, v___y_973_);
lean_dec(v___y_973_);
lean_dec_ref(v___y_972_);
if (lean_obj_tag(v___x_983_) == 0)
{
lean_object* v_a_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_989_; uint8_t v_isShared_990_; uint8_t v_isSharedCheck_995_; 
v_a_984_ = lean_ctor_get(v___x_983_, 0);
lean_inc(v_a_984_);
lean_dec_ref(v___x_983_);
lean_inc(v_a_984_);
v___x_985_ = l_Lean_mkAppN(v_a_984_, v_targets_969_);
v___x_986_ = l_Lean_mkAppN(v___x_985_, v_snd_980_);
lean_dec(v_snd_980_);
v___x_987_ = l_Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1___redArg(v_mvarId_965_, v___x_986_, v___y_971_);
lean_dec(v___y_971_);
v_isSharedCheck_995_ = !lean_is_exclusive(v___x_987_);
if (v_isSharedCheck_995_ == 0)
{
lean_object* v_unused_996_; 
v_unused_996_ = lean_ctor_get(v___x_987_, 0);
lean_dec(v_unused_996_);
v___x_989_ = v___x_987_;
v_isShared_990_ = v_isSharedCheck_995_;
goto v_resetjp_988_;
}
else
{
lean_dec(v___x_987_);
v___x_989_ = lean_box(0);
v_isShared_990_ = v_isSharedCheck_995_;
goto v_resetjp_988_;
}
v_resetjp_988_:
{
lean_object* v___x_991_; lean_object* v___x_993_; 
v___x_991_ = l_Lean_Expr_mvarId_x21(v_a_984_);
lean_dec(v_a_984_);
if (v_isShared_990_ == 0)
{
lean_ctor_set(v___x_989_, 0, v___x_991_);
v___x_993_ = v___x_989_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v___x_991_);
v___x_993_ = v_reuseFailAlloc_994_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
return v___x_993_;
}
}
}
else
{
lean_object* v_a_997_; lean_object* v___x_999_; uint8_t v_isShared_1000_; uint8_t v_isSharedCheck_1004_; 
lean_dec(v_snd_980_);
lean_dec(v___y_971_);
lean_dec(v_mvarId_965_);
v_a_997_ = lean_ctor_get(v___x_983_, 0);
v_isSharedCheck_1004_ = !lean_is_exclusive(v___x_983_);
if (v_isSharedCheck_1004_ == 0)
{
v___x_999_ = v___x_983_;
v_isShared_1000_ = v_isSharedCheck_1004_;
goto v_resetjp_998_;
}
else
{
lean_inc(v_a_997_);
lean_dec(v___x_983_);
v___x_999_ = lean_box(0);
v_isShared_1000_ = v_isSharedCheck_1004_;
goto v_resetjp_998_;
}
v_resetjp_998_:
{
lean_object* v___x_1002_; 
if (v_isShared_1000_ == 0)
{
v___x_1002_ = v___x_999_;
goto v_reusejp_1001_;
}
else
{
lean_object* v_reuseFailAlloc_1003_; 
v_reuseFailAlloc_1003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1003_, 0, v_a_997_);
v___x_1002_ = v_reuseFailAlloc_1003_;
goto v_reusejp_1001_;
}
v_reusejp_1001_:
{
return v___x_1002_;
}
}
}
}
else
{
lean_object* v_a_1005_; lean_object* v___x_1007_; uint8_t v_isShared_1008_; uint8_t v_isSharedCheck_1012_; 
lean_dec(v_snd_980_);
lean_dec(v_fst_979_);
lean_dec(v___y_973_);
lean_dec_ref(v___y_972_);
lean_dec(v___y_971_);
lean_dec_ref(v___y_970_);
lean_dec(v_mvarId_965_);
v_a_1005_ = lean_ctor_get(v___x_981_, 0);
v_isSharedCheck_1012_ = !lean_is_exclusive(v___x_981_);
if (v_isSharedCheck_1012_ == 0)
{
v___x_1007_ = v___x_981_;
v_isShared_1008_ = v_isSharedCheck_1012_;
goto v_resetjp_1006_;
}
else
{
lean_inc(v_a_1005_);
lean_dec(v___x_981_);
v___x_1007_ = lean_box(0);
v_isShared_1008_ = v_isSharedCheck_1012_;
goto v_resetjp_1006_;
}
v_resetjp_1006_:
{
lean_object* v___x_1010_; 
if (v_isShared_1008_ == 0)
{
v___x_1010_ = v___x_1007_;
goto v_reusejp_1009_;
}
else
{
lean_object* v_reuseFailAlloc_1011_; 
v_reuseFailAlloc_1011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1011_, 0, v_a_1005_);
v___x_1010_ = v_reuseFailAlloc_1011_;
goto v_reusejp_1009_;
}
v_reusejp_1009_:
{
return v___x_1010_;
}
}
}
}
else
{
lean_object* v_a_1013_; lean_object* v___x_1015_; uint8_t v_isShared_1016_; uint8_t v_isSharedCheck_1020_; 
lean_dec(v___y_973_);
lean_dec_ref(v___y_972_);
lean_dec(v___y_971_);
lean_dec_ref(v___y_970_);
lean_dec(v_mvarId_965_);
v_a_1013_ = lean_ctor_get(v___x_977_, 0);
v_isSharedCheck_1020_ = !lean_is_exclusive(v___x_977_);
if (v_isSharedCheck_1020_ == 0)
{
v___x_1015_ = v___x_977_;
v_isShared_1016_ = v_isSharedCheck_1020_;
goto v_resetjp_1014_;
}
else
{
lean_inc(v_a_1013_);
lean_dec(v___x_977_);
v___x_1015_ = lean_box(0);
v_isShared_1016_ = v_isSharedCheck_1020_;
goto v_resetjp_1014_;
}
v_resetjp_1014_:
{
lean_object* v___x_1018_; 
if (v_isShared_1016_ == 0)
{
v___x_1018_ = v___x_1015_;
goto v_reusejp_1017_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v_a_1013_);
v___x_1018_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1017_;
}
v_reusejp_1017_:
{
return v___x_1018_;
}
}
}
}
else
{
lean_object* v_a_1021_; lean_object* v___x_1023_; uint8_t v_isShared_1024_; uint8_t v_isSharedCheck_1028_; 
lean_dec(v___y_973_);
lean_dec_ref(v___y_972_);
lean_dec(v___y_971_);
lean_dec_ref(v___y_970_);
lean_dec_ref(v___f_968_);
lean_dec_ref(v_motiveType_967_);
lean_dec(v_mvarId_965_);
v_a_1021_ = lean_ctor_get(v___x_975_, 0);
v_isSharedCheck_1028_ = !lean_is_exclusive(v___x_975_);
if (v_isSharedCheck_1028_ == 0)
{
v___x_1023_ = v___x_975_;
v_isShared_1024_ = v_isSharedCheck_1028_;
goto v_resetjp_1022_;
}
else
{
lean_inc(v_a_1021_);
lean_dec(v___x_975_);
v___x_1023_ = lean_box(0);
v_isShared_1024_ = v_isSharedCheck_1028_;
goto v_resetjp_1022_;
}
v_resetjp_1022_:
{
lean_object* v___x_1026_; 
if (v_isShared_1024_ == 0)
{
v___x_1026_ = v___x_1023_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v_a_1021_);
v___x_1026_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
return v___x_1026_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeTargetsEq___lam__2___boxed(lean_object* v_mvarId_1029_, lean_object* v___x_1030_, lean_object* v_motiveType_1031_, lean_object* v___f_1032_, lean_object* v_targets_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_){
_start:
{
lean_object* v_res_1039_; 
v_res_1039_ = l_Lean_Meta_generalizeTargetsEq___lam__2(v_mvarId_1029_, v___x_1030_, v_motiveType_1031_, v___f_1032_, v_targets_1033_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_);
lean_dec_ref(v_targets_1033_);
return v_res_1039_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeTargetsEq(lean_object* v_mvarId_1043_, lean_object* v_motiveType_1044_, lean_object* v_targets_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_){
_start:
{
lean_object* v___f_1051_; lean_object* v___x_1052_; lean_object* v___f_1053_; lean_object* v___x_1054_; 
lean_inc(v_mvarId_1043_);
lean_inc_ref(v_targets_1045_);
v___f_1051_ = lean_alloc_closure((void*)(l_Lean_Meta_generalizeTargetsEq___lam__1___boxed), 9, 2);
lean_closure_set(v___f_1051_, 0, v_targets_1045_);
lean_closure_set(v___f_1051_, 1, v_mvarId_1043_);
v___x_1052_ = ((lean_object*)(l_Lean_Meta_generalizeTargetsEq___closed__1));
lean_inc(v_mvarId_1043_);
v___f_1053_ = lean_alloc_closure((void*)(l_Lean_Meta_generalizeTargetsEq___lam__2___boxed), 10, 5);
lean_closure_set(v___f_1053_, 0, v_mvarId_1043_);
lean_closure_set(v___f_1053_, 1, v___x_1052_);
lean_closure_set(v___f_1053_, 2, v_motiveType_1044_);
lean_closure_set(v___f_1053_, 3, v___f_1051_);
lean_closure_set(v___f_1053_, 4, v_targets_1045_);
v___x_1054_ = l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2___redArg(v_mvarId_1043_, v___f_1053_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_);
return v___x_1054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeTargetsEq___boxed(lean_object* v_mvarId_1055_, lean_object* v_motiveType_1056_, lean_object* v_targets_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_){
_start:
{
lean_object* v_res_1063_; 
v_res_1063_ = l_Lean_Meta_generalizeTargetsEq(v_mvarId_1055_, v_motiveType_1056_, v_targets_1057_, v_a_1058_, v_a_1059_, v_a_1060_, v_a_1061_);
return v_res_1063_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1(lean_object* v_mvarId_1064_, lean_object* v_val_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_){
_start:
{
lean_object* v___x_1071_; 
v___x_1071_ = l_Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1___redArg(v_mvarId_1064_, v_val_1065_, v___y_1067_);
return v___x_1071_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1___boxed(lean_object* v_mvarId_1072_, lean_object* v_val_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_){
_start:
{
lean_object* v_res_1079_; 
v_res_1079_ = l_Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1(v_mvarId_1072_, v_val_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_);
lean_dec(v___y_1077_);
lean_dec_ref(v___y_1076_);
lean_dec(v___y_1075_);
lean_dec_ref(v___y_1074_);
return v_res_1079_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1(lean_object* v_00_u03b2_1080_, lean_object* v_x_1081_, lean_object* v_x_1082_, lean_object* v_x_1083_){
_start:
{
lean_object* v___x_1084_; 
v___x_1084_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1___redArg(v_x_1081_, v_x_1082_, v_x_1083_);
return v___x_1084_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3(lean_object* v_00_u03b2_1085_, lean_object* v_x_1086_, size_t v_x_1087_, size_t v_x_1088_, lean_object* v_x_1089_, lean_object* v_x_1090_){
_start:
{
lean_object* v___x_1091_; 
v___x_1091_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg(v_x_1086_, v_x_1087_, v_x_1088_, v_x_1089_, v_x_1090_);
return v___x_1091_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1092_, lean_object* v_x_1093_, lean_object* v_x_1094_, lean_object* v_x_1095_, lean_object* v_x_1096_, lean_object* v_x_1097_){
_start:
{
size_t v_x_3103__boxed_1098_; size_t v_x_3104__boxed_1099_; lean_object* v_res_1100_; 
v_x_3103__boxed_1098_ = lean_unbox_usize(v_x_1094_);
lean_dec(v_x_1094_);
v_x_3104__boxed_1099_ = lean_unbox_usize(v_x_1095_);
lean_dec(v_x_1095_);
v_res_1100_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3(v_00_u03b2_1092_, v_x_1093_, v_x_3103__boxed_1098_, v_x_3104__boxed_1099_, v_x_1096_, v_x_1097_);
return v_res_1100_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_1101_, lean_object* v_n_1102_, lean_object* v_k_1103_, lean_object* v_v_1104_){
_start:
{
lean_object* v___x_1105_; 
v___x_1105_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__4___redArg(v_n_1102_, v_k_1103_, v_v_1104_);
return v___x_1105_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__5(lean_object* v_00_u03b2_1106_, size_t v_depth_1107_, lean_object* v_keys_1108_, lean_object* v_vals_1109_, lean_object* v_heq_1110_, lean_object* v_i_1111_, lean_object* v_entries_1112_){
_start:
{
lean_object* v___x_1113_; 
v___x_1113_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__5___redArg(v_depth_1107_, v_keys_1108_, v_vals_1109_, v_i_1111_, v_entries_1112_);
return v___x_1113_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__5___boxed(lean_object* v_00_u03b2_1114_, lean_object* v_depth_1115_, lean_object* v_keys_1116_, lean_object* v_vals_1117_, lean_object* v_heq_1118_, lean_object* v_i_1119_, lean_object* v_entries_1120_){
_start:
{
size_t v_depth_boxed_1121_; lean_object* v_res_1122_; 
v_depth_boxed_1121_ = lean_unbox_usize(v_depth_1115_);
lean_dec(v_depth_1115_);
v_res_1122_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__5(v_00_u03b2_1114_, v_depth_boxed_1121_, v_keys_1116_, v_vals_1117_, v_heq_1118_, v_i_1119_, v_entries_1120_);
lean_dec_ref(v_vals_1117_);
lean_dec_ref(v_keys_1116_);
return v_res_1122_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_1123_, lean_object* v_x_1124_, lean_object* v_x_1125_, lean_object* v_x_1126_, lean_object* v_x_1127_){
_start:
{
lean_object* v___x_1128_; 
v___x_1128_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__4_spec__5___redArg(v_x_1124_, v_x_1125_, v_x_1126_, v_x_1127_);
return v___x_1128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__0(lean_object* v_mvarId_1129_, lean_object* v_newEqs_1130_, uint8_t v___x_1131_, lean_object* v_h_x27_1132_, lean_object* v_newIndices_1133_, lean_object* v___x_1134_, lean_object* v_a_1135_, lean_object* v___x_1136_, lean_object* v___x_1137_, lean_object* v_e_1138_, lean_object* v___x_1139_, lean_object* v_newEq_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_){
_start:
{
lean_object* v___x_1146_; 
lean_inc(v_mvarId_1129_);
v___x_1146_ = l_Lean_MVarId_getType(v_mvarId_1129_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_);
if (lean_obj_tag(v___x_1146_) == 0)
{
lean_object* v_a_1147_; lean_object* v___x_1148_; 
v_a_1147_ = lean_ctor_get(v___x_1146_, 0);
lean_inc(v_a_1147_);
lean_dec_ref(v___x_1146_);
lean_inc(v_mvarId_1129_);
v___x_1148_ = l_Lean_MVarId_getTag(v_mvarId_1129_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_);
if (lean_obj_tag(v___x_1148_) == 0)
{
lean_object* v_a_1149_; lean_object* v___x_1150_; uint8_t v___x_1151_; uint8_t v___x_1152_; lean_object* v___x_1153_; 
v_a_1149_ = lean_ctor_get(v___x_1148_, 0);
lean_inc(v_a_1149_);
lean_dec_ref(v___x_1148_);
v___x_1150_ = lean_array_push(v_newEqs_1130_, v_newEq_1140_);
v___x_1151_ = 1;
v___x_1152_ = 1;
v___x_1153_ = l_Lean_Meta_mkForallFVars(v___x_1150_, v_a_1147_, v___x_1131_, v___x_1151_, v___x_1151_, v___x_1152_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_);
if (lean_obj_tag(v___x_1153_) == 0)
{
lean_object* v_a_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; 
v_a_1154_ = lean_ctor_get(v___x_1153_, 0);
lean_inc(v_a_1154_);
lean_dec_ref(v___x_1153_);
v___x_1155_ = lean_unsigned_to_nat(1u);
v___x_1156_ = lean_mk_empty_array_with_capacity(v___x_1155_);
v___x_1157_ = lean_array_push(v___x_1156_, v_h_x27_1132_);
v___x_1158_ = l_Lean_Meta_mkForallFVars(v___x_1157_, v_a_1154_, v___x_1131_, v___x_1151_, v___x_1151_, v___x_1152_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_);
lean_dec_ref(v___x_1157_);
if (lean_obj_tag(v___x_1158_) == 0)
{
lean_object* v_a_1159_; lean_object* v___x_1160_; 
v_a_1159_ = lean_ctor_get(v___x_1158_, 0);
lean_inc(v_a_1159_);
lean_dec_ref(v___x_1158_);
v___x_1160_ = l_Lean_Meta_mkForallFVars(v_newIndices_1133_, v_a_1159_, v___x_1131_, v___x_1151_, v___x_1151_, v___x_1152_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_);
if (lean_obj_tag(v___x_1160_) == 0)
{
lean_object* v_a_1161_; uint8_t v___x_1162_; lean_object* v___x_1163_; 
v_a_1161_ = lean_ctor_get(v___x_1160_, 0);
lean_inc(v_a_1161_);
lean_dec_ref(v___x_1160_);
v___x_1162_ = 2;
v___x_1163_ = l_Lean_Meta_mkFreshExprMVarAt(v___x_1134_, v_a_1135_, v_a_1161_, v___x_1162_, v_a_1149_, v___x_1136_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_);
if (lean_obj_tag(v___x_1163_) == 0)
{
lean_object* v_a_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; 
v_a_1164_ = lean_ctor_get(v___x_1163_, 0);
lean_inc(v_a_1164_);
lean_dec_ref(v___x_1163_);
lean_inc(v_a_1164_);
v___x_1165_ = l_Lean_mkAppN(v_a_1164_, v___x_1137_);
v___x_1166_ = l_Lean_Expr_app___override(v___x_1165_, v_e_1138_);
v___x_1167_ = l_Lean_mkAppN(v___x_1166_, v___x_1139_);
v___x_1168_ = l_Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1___redArg(v_mvarId_1129_, v___x_1167_, v___y_1142_);
lean_dec_ref(v___x_1168_);
v___x_1169_ = l_Lean_Expr_mvarId_x21(v_a_1164_);
lean_dec(v_a_1164_);
v___x_1170_ = lean_array_get_size(v_newIndices_1133_);
v___x_1171_ = lean_box(0);
lean_inc(v___y_1144_);
lean_inc_ref(v___y_1143_);
lean_inc(v___y_1142_);
lean_inc_ref(v___y_1141_);
v___x_1172_ = l_Lean_Meta_introNCore(v___x_1169_, v___x_1170_, v___x_1171_, v___x_1131_, v___x_1151_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_);
if (lean_obj_tag(v___x_1172_) == 0)
{
lean_object* v_a_1173_; lean_object* v_fst_1174_; lean_object* v_snd_1175_; lean_object* v___x_1176_; 
v_a_1173_ = lean_ctor_get(v___x_1172_, 0);
lean_inc(v_a_1173_);
lean_dec_ref(v___x_1172_);
v_fst_1174_ = lean_ctor_get(v_a_1173_, 0);
lean_inc(v_fst_1174_);
v_snd_1175_ = lean_ctor_get(v_a_1173_, 1);
lean_inc(v_snd_1175_);
lean_dec(v_a_1173_);
v___x_1176_ = l_Lean_Meta_intro1Core(v_snd_1175_, v___x_1151_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_);
if (lean_obj_tag(v___x_1176_) == 0)
{
lean_object* v_a_1177_; lean_object* v___x_1179_; uint8_t v_isShared_1180_; uint8_t v_isSharedCheck_1188_; 
v_a_1177_ = lean_ctor_get(v___x_1176_, 0);
v_isSharedCheck_1188_ = !lean_is_exclusive(v___x_1176_);
if (v_isSharedCheck_1188_ == 0)
{
v___x_1179_ = v___x_1176_;
v_isShared_1180_ = v_isSharedCheck_1188_;
goto v_resetjp_1178_;
}
else
{
lean_inc(v_a_1177_);
lean_dec(v___x_1176_);
v___x_1179_ = lean_box(0);
v_isShared_1180_ = v_isSharedCheck_1188_;
goto v_resetjp_1178_;
}
v_resetjp_1178_:
{
lean_object* v_fst_1181_; lean_object* v_snd_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1186_; 
v_fst_1181_ = lean_ctor_get(v_a_1177_, 0);
lean_inc(v_fst_1181_);
v_snd_1182_ = lean_ctor_get(v_a_1177_, 1);
lean_inc(v_snd_1182_);
lean_dec(v_a_1177_);
v___x_1183_ = lean_array_get_size(v___x_1150_);
lean_dec_ref(v___x_1150_);
v___x_1184_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1184_, 0, v_snd_1182_);
lean_ctor_set(v___x_1184_, 1, v_fst_1174_);
lean_ctor_set(v___x_1184_, 2, v_fst_1181_);
lean_ctor_set(v___x_1184_, 3, v___x_1183_);
if (v_isShared_1180_ == 0)
{
lean_ctor_set(v___x_1179_, 0, v___x_1184_);
v___x_1186_ = v___x_1179_;
goto v_reusejp_1185_;
}
else
{
lean_object* v_reuseFailAlloc_1187_; 
v_reuseFailAlloc_1187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1187_, 0, v___x_1184_);
v___x_1186_ = v_reuseFailAlloc_1187_;
goto v_reusejp_1185_;
}
v_reusejp_1185_:
{
return v___x_1186_;
}
}
}
else
{
lean_object* v_a_1189_; lean_object* v___x_1191_; uint8_t v_isShared_1192_; uint8_t v_isSharedCheck_1196_; 
lean_dec(v_fst_1174_);
lean_dec_ref(v___x_1150_);
v_a_1189_ = lean_ctor_get(v___x_1176_, 0);
v_isSharedCheck_1196_ = !lean_is_exclusive(v___x_1176_);
if (v_isSharedCheck_1196_ == 0)
{
v___x_1191_ = v___x_1176_;
v_isShared_1192_ = v_isSharedCheck_1196_;
goto v_resetjp_1190_;
}
else
{
lean_inc(v_a_1189_);
lean_dec(v___x_1176_);
v___x_1191_ = lean_box(0);
v_isShared_1192_ = v_isSharedCheck_1196_;
goto v_resetjp_1190_;
}
v_resetjp_1190_:
{
lean_object* v___x_1194_; 
if (v_isShared_1192_ == 0)
{
v___x_1194_ = v___x_1191_;
goto v_reusejp_1193_;
}
else
{
lean_object* v_reuseFailAlloc_1195_; 
v_reuseFailAlloc_1195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1195_, 0, v_a_1189_);
v___x_1194_ = v_reuseFailAlloc_1195_;
goto v_reusejp_1193_;
}
v_reusejp_1193_:
{
return v___x_1194_;
}
}
}
}
else
{
lean_object* v_a_1197_; lean_object* v___x_1199_; uint8_t v_isShared_1200_; uint8_t v_isSharedCheck_1204_; 
lean_dec_ref(v___x_1150_);
lean_dec(v___y_1144_);
lean_dec_ref(v___y_1143_);
lean_dec(v___y_1142_);
lean_dec_ref(v___y_1141_);
v_a_1197_ = lean_ctor_get(v___x_1172_, 0);
v_isSharedCheck_1204_ = !lean_is_exclusive(v___x_1172_);
if (v_isSharedCheck_1204_ == 0)
{
v___x_1199_ = v___x_1172_;
v_isShared_1200_ = v_isSharedCheck_1204_;
goto v_resetjp_1198_;
}
else
{
lean_inc(v_a_1197_);
lean_dec(v___x_1172_);
v___x_1199_ = lean_box(0);
v_isShared_1200_ = v_isSharedCheck_1204_;
goto v_resetjp_1198_;
}
v_resetjp_1198_:
{
lean_object* v___x_1202_; 
if (v_isShared_1200_ == 0)
{
v___x_1202_ = v___x_1199_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v_a_1197_);
v___x_1202_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
return v___x_1202_;
}
}
}
}
else
{
lean_object* v_a_1205_; lean_object* v___x_1207_; uint8_t v_isShared_1208_; uint8_t v_isSharedCheck_1212_; 
lean_dec_ref(v___x_1150_);
lean_dec(v___y_1144_);
lean_dec_ref(v___y_1143_);
lean_dec(v___y_1142_);
lean_dec_ref(v___y_1141_);
lean_dec_ref(v_e_1138_);
lean_dec(v_mvarId_1129_);
v_a_1205_ = lean_ctor_get(v___x_1163_, 0);
v_isSharedCheck_1212_ = !lean_is_exclusive(v___x_1163_);
if (v_isSharedCheck_1212_ == 0)
{
v___x_1207_ = v___x_1163_;
v_isShared_1208_ = v_isSharedCheck_1212_;
goto v_resetjp_1206_;
}
else
{
lean_inc(v_a_1205_);
lean_dec(v___x_1163_);
v___x_1207_ = lean_box(0);
v_isShared_1208_ = v_isSharedCheck_1212_;
goto v_resetjp_1206_;
}
v_resetjp_1206_:
{
lean_object* v___x_1210_; 
if (v_isShared_1208_ == 0)
{
v___x_1210_ = v___x_1207_;
goto v_reusejp_1209_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v_a_1205_);
v___x_1210_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1209_;
}
v_reusejp_1209_:
{
return v___x_1210_;
}
}
}
}
else
{
lean_object* v_a_1213_; lean_object* v___x_1215_; uint8_t v_isShared_1216_; uint8_t v_isSharedCheck_1220_; 
lean_dec_ref(v___x_1150_);
lean_dec(v_a_1149_);
lean_dec(v___y_1144_);
lean_dec_ref(v___y_1143_);
lean_dec(v___y_1142_);
lean_dec_ref(v___y_1141_);
lean_dec_ref(v_e_1138_);
lean_dec(v___x_1136_);
lean_dec_ref(v_a_1135_);
lean_dec_ref(v___x_1134_);
lean_dec(v_mvarId_1129_);
v_a_1213_ = lean_ctor_get(v___x_1160_, 0);
v_isSharedCheck_1220_ = !lean_is_exclusive(v___x_1160_);
if (v_isSharedCheck_1220_ == 0)
{
v___x_1215_ = v___x_1160_;
v_isShared_1216_ = v_isSharedCheck_1220_;
goto v_resetjp_1214_;
}
else
{
lean_inc(v_a_1213_);
lean_dec(v___x_1160_);
v___x_1215_ = lean_box(0);
v_isShared_1216_ = v_isSharedCheck_1220_;
goto v_resetjp_1214_;
}
v_resetjp_1214_:
{
lean_object* v___x_1218_; 
if (v_isShared_1216_ == 0)
{
v___x_1218_ = v___x_1215_;
goto v_reusejp_1217_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v_a_1213_);
v___x_1218_ = v_reuseFailAlloc_1219_;
goto v_reusejp_1217_;
}
v_reusejp_1217_:
{
return v___x_1218_;
}
}
}
}
else
{
lean_object* v_a_1221_; lean_object* v___x_1223_; uint8_t v_isShared_1224_; uint8_t v_isSharedCheck_1228_; 
lean_dec_ref(v___x_1150_);
lean_dec(v_a_1149_);
lean_dec(v___y_1144_);
lean_dec_ref(v___y_1143_);
lean_dec(v___y_1142_);
lean_dec_ref(v___y_1141_);
lean_dec_ref(v_e_1138_);
lean_dec(v___x_1136_);
lean_dec_ref(v_a_1135_);
lean_dec_ref(v___x_1134_);
lean_dec(v_mvarId_1129_);
v_a_1221_ = lean_ctor_get(v___x_1158_, 0);
v_isSharedCheck_1228_ = !lean_is_exclusive(v___x_1158_);
if (v_isSharedCheck_1228_ == 0)
{
v___x_1223_ = v___x_1158_;
v_isShared_1224_ = v_isSharedCheck_1228_;
goto v_resetjp_1222_;
}
else
{
lean_inc(v_a_1221_);
lean_dec(v___x_1158_);
v___x_1223_ = lean_box(0);
v_isShared_1224_ = v_isSharedCheck_1228_;
goto v_resetjp_1222_;
}
v_resetjp_1222_:
{
lean_object* v___x_1226_; 
if (v_isShared_1224_ == 0)
{
v___x_1226_ = v___x_1223_;
goto v_reusejp_1225_;
}
else
{
lean_object* v_reuseFailAlloc_1227_; 
v_reuseFailAlloc_1227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1227_, 0, v_a_1221_);
v___x_1226_ = v_reuseFailAlloc_1227_;
goto v_reusejp_1225_;
}
v_reusejp_1225_:
{
return v___x_1226_;
}
}
}
}
else
{
lean_object* v_a_1229_; lean_object* v___x_1231_; uint8_t v_isShared_1232_; uint8_t v_isSharedCheck_1236_; 
lean_dec_ref(v___x_1150_);
lean_dec(v_a_1149_);
lean_dec(v___y_1144_);
lean_dec_ref(v___y_1143_);
lean_dec(v___y_1142_);
lean_dec_ref(v___y_1141_);
lean_dec_ref(v_e_1138_);
lean_dec(v___x_1136_);
lean_dec_ref(v_a_1135_);
lean_dec_ref(v___x_1134_);
lean_dec_ref(v_h_x27_1132_);
lean_dec(v_mvarId_1129_);
v_a_1229_ = lean_ctor_get(v___x_1153_, 0);
v_isSharedCheck_1236_ = !lean_is_exclusive(v___x_1153_);
if (v_isSharedCheck_1236_ == 0)
{
v___x_1231_ = v___x_1153_;
v_isShared_1232_ = v_isSharedCheck_1236_;
goto v_resetjp_1230_;
}
else
{
lean_inc(v_a_1229_);
lean_dec(v___x_1153_);
v___x_1231_ = lean_box(0);
v_isShared_1232_ = v_isSharedCheck_1236_;
goto v_resetjp_1230_;
}
v_resetjp_1230_:
{
lean_object* v___x_1234_; 
if (v_isShared_1232_ == 0)
{
v___x_1234_ = v___x_1231_;
goto v_reusejp_1233_;
}
else
{
lean_object* v_reuseFailAlloc_1235_; 
v_reuseFailAlloc_1235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1235_, 0, v_a_1229_);
v___x_1234_ = v_reuseFailAlloc_1235_;
goto v_reusejp_1233_;
}
v_reusejp_1233_:
{
return v___x_1234_;
}
}
}
}
else
{
lean_object* v_a_1237_; lean_object* v___x_1239_; uint8_t v_isShared_1240_; uint8_t v_isSharedCheck_1244_; 
lean_dec(v_a_1147_);
lean_dec(v___y_1144_);
lean_dec_ref(v___y_1143_);
lean_dec(v___y_1142_);
lean_dec_ref(v___y_1141_);
lean_dec_ref(v_newEq_1140_);
lean_dec_ref(v_e_1138_);
lean_dec(v___x_1136_);
lean_dec_ref(v_a_1135_);
lean_dec_ref(v___x_1134_);
lean_dec_ref(v_h_x27_1132_);
lean_dec_ref(v_newEqs_1130_);
lean_dec(v_mvarId_1129_);
v_a_1237_ = lean_ctor_get(v___x_1148_, 0);
v_isSharedCheck_1244_ = !lean_is_exclusive(v___x_1148_);
if (v_isSharedCheck_1244_ == 0)
{
v___x_1239_ = v___x_1148_;
v_isShared_1240_ = v_isSharedCheck_1244_;
goto v_resetjp_1238_;
}
else
{
lean_inc(v_a_1237_);
lean_dec(v___x_1148_);
v___x_1239_ = lean_box(0);
v_isShared_1240_ = v_isSharedCheck_1244_;
goto v_resetjp_1238_;
}
v_resetjp_1238_:
{
lean_object* v___x_1242_; 
if (v_isShared_1240_ == 0)
{
v___x_1242_ = v___x_1239_;
goto v_reusejp_1241_;
}
else
{
lean_object* v_reuseFailAlloc_1243_; 
v_reuseFailAlloc_1243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1243_, 0, v_a_1237_);
v___x_1242_ = v_reuseFailAlloc_1243_;
goto v_reusejp_1241_;
}
v_reusejp_1241_:
{
return v___x_1242_;
}
}
}
}
else
{
lean_object* v_a_1245_; lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1252_; 
lean_dec(v___y_1144_);
lean_dec_ref(v___y_1143_);
lean_dec(v___y_1142_);
lean_dec_ref(v___y_1141_);
lean_dec_ref(v_newEq_1140_);
lean_dec_ref(v_e_1138_);
lean_dec(v___x_1136_);
lean_dec_ref(v_a_1135_);
lean_dec_ref(v___x_1134_);
lean_dec_ref(v_h_x27_1132_);
lean_dec_ref(v_newEqs_1130_);
lean_dec(v_mvarId_1129_);
v_a_1245_ = lean_ctor_get(v___x_1146_, 0);
v_isSharedCheck_1252_ = !lean_is_exclusive(v___x_1146_);
if (v_isSharedCheck_1252_ == 0)
{
v___x_1247_ = v___x_1146_;
v_isShared_1248_ = v_isSharedCheck_1252_;
goto v_resetjp_1246_;
}
else
{
lean_inc(v_a_1245_);
lean_dec(v___x_1146_);
v___x_1247_ = lean_box(0);
v_isShared_1248_ = v_isSharedCheck_1252_;
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
lean_object* v_reuseFailAlloc_1251_; 
v_reuseFailAlloc_1251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1251_, 0, v_a_1245_);
v___x_1250_ = v_reuseFailAlloc_1251_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
return v___x_1250_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__0___boxed(lean_object** _args){
lean_object* v_mvarId_1253_ = _args[0];
lean_object* v_newEqs_1254_ = _args[1];
lean_object* v___x_1255_ = _args[2];
lean_object* v_h_x27_1256_ = _args[3];
lean_object* v_newIndices_1257_ = _args[4];
lean_object* v___x_1258_ = _args[5];
lean_object* v_a_1259_ = _args[6];
lean_object* v___x_1260_ = _args[7];
lean_object* v___x_1261_ = _args[8];
lean_object* v_e_1262_ = _args[9];
lean_object* v___x_1263_ = _args[10];
lean_object* v_newEq_1264_ = _args[11];
lean_object* v___y_1265_ = _args[12];
lean_object* v___y_1266_ = _args[13];
lean_object* v___y_1267_ = _args[14];
lean_object* v___y_1268_ = _args[15];
lean_object* v___y_1269_ = _args[16];
_start:
{
uint8_t v___x_6336__boxed_1270_; lean_object* v_res_1271_; 
v___x_6336__boxed_1270_ = lean_unbox(v___x_1255_);
v_res_1271_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__0(v_mvarId_1253_, v_newEqs_1254_, v___x_6336__boxed_1270_, v_h_x27_1256_, v_newIndices_1257_, v___x_1258_, v_a_1259_, v___x_1260_, v___x_1261_, v_e_1262_, v___x_1263_, v_newEq_1264_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_);
lean_dec_ref(v___x_1263_);
lean_dec_ref(v___x_1261_);
lean_dec_ref(v_newIndices_1257_);
return v_res_1271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__1(lean_object* v_e_1272_, lean_object* v_h_x27_1273_, lean_object* v_mvarId_1274_, uint8_t v___x_1275_, lean_object* v_newIndices_1276_, lean_object* v___x_1277_, lean_object* v_a_1278_, lean_object* v___x_1279_, lean_object* v___x_1280_, lean_object* v_newEqs_1281_, lean_object* v_newRefls_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_){
_start:
{
lean_object* v___x_1288_; 
lean_inc(v___y_1286_);
lean_inc_ref(v___y_1285_);
lean_inc(v___y_1284_);
lean_inc_ref(v___y_1283_);
lean_inc_ref(v_h_x27_1273_);
lean_inc_ref(v_e_1272_);
v___x_1288_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof(v_e_1272_, v_h_x27_1273_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_);
if (lean_obj_tag(v___x_1288_) == 0)
{
lean_object* v_a_1289_; lean_object* v_fst_1290_; lean_object* v_snd_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___f_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; 
v_a_1289_ = lean_ctor_get(v___x_1288_, 0);
lean_inc(v_a_1289_);
lean_dec_ref(v___x_1288_);
v_fst_1290_ = lean_ctor_get(v_a_1289_, 0);
lean_inc(v_fst_1290_);
v_snd_1291_ = lean_ctor_get(v_a_1289_, 1);
lean_inc(v_snd_1291_);
lean_dec(v_a_1289_);
v___x_1292_ = lean_array_push(v_newRefls_1282_, v_snd_1291_);
v___x_1293_ = lean_box(v___x_1275_);
v___f_1294_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__0___boxed), 17, 11);
lean_closure_set(v___f_1294_, 0, v_mvarId_1274_);
lean_closure_set(v___f_1294_, 1, v_newEqs_1281_);
lean_closure_set(v___f_1294_, 2, v___x_1293_);
lean_closure_set(v___f_1294_, 3, v_h_x27_1273_);
lean_closure_set(v___f_1294_, 4, v_newIndices_1276_);
lean_closure_set(v___f_1294_, 5, v___x_1277_);
lean_closure_set(v___f_1294_, 6, v_a_1278_);
lean_closure_set(v___f_1294_, 7, v___x_1279_);
lean_closure_set(v___f_1294_, 8, v___x_1280_);
lean_closure_set(v___f_1294_, 9, v_e_1272_);
lean_closure_set(v___f_1294_, 10, v___x_1292_);
v___x_1295_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___redArg___closed__1));
v___x_1296_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0___redArg(v___x_1295_, v_fst_1290_, v___f_1294_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_);
return v___x_1296_;
}
else
{
lean_object* v_a_1297_; lean_object* v___x_1299_; uint8_t v_isShared_1300_; uint8_t v_isSharedCheck_1304_; 
lean_dec(v___y_1286_);
lean_dec_ref(v___y_1285_);
lean_dec(v___y_1284_);
lean_dec_ref(v___y_1283_);
lean_dec_ref(v_newRefls_1282_);
lean_dec_ref(v_newEqs_1281_);
lean_dec_ref(v___x_1280_);
lean_dec(v___x_1279_);
lean_dec_ref(v_a_1278_);
lean_dec_ref(v___x_1277_);
lean_dec_ref(v_newIndices_1276_);
lean_dec(v_mvarId_1274_);
lean_dec_ref(v_h_x27_1273_);
lean_dec_ref(v_e_1272_);
v_a_1297_ = lean_ctor_get(v___x_1288_, 0);
v_isSharedCheck_1304_ = !lean_is_exclusive(v___x_1288_);
if (v_isSharedCheck_1304_ == 0)
{
v___x_1299_ = v___x_1288_;
v_isShared_1300_ = v_isSharedCheck_1304_;
goto v_resetjp_1298_;
}
else
{
lean_inc(v_a_1297_);
lean_dec(v___x_1288_);
v___x_1299_ = lean_box(0);
v_isShared_1300_ = v_isSharedCheck_1304_;
goto v_resetjp_1298_;
}
v_resetjp_1298_:
{
lean_object* v___x_1302_; 
if (v_isShared_1300_ == 0)
{
v___x_1302_ = v___x_1299_;
goto v_reusejp_1301_;
}
else
{
lean_object* v_reuseFailAlloc_1303_; 
v_reuseFailAlloc_1303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1303_, 0, v_a_1297_);
v___x_1302_ = v_reuseFailAlloc_1303_;
goto v_reusejp_1301_;
}
v_reusejp_1301_:
{
return v___x_1302_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__1___boxed(lean_object* v_e_1305_, lean_object* v_h_x27_1306_, lean_object* v_mvarId_1307_, lean_object* v___x_1308_, lean_object* v_newIndices_1309_, lean_object* v___x_1310_, lean_object* v_a_1311_, lean_object* v___x_1312_, lean_object* v___x_1313_, lean_object* v_newEqs_1314_, lean_object* v_newRefls_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_){
_start:
{
uint8_t v___x_6588__boxed_1321_; lean_object* v_res_1322_; 
v___x_6588__boxed_1321_ = lean_unbox(v___x_1308_);
v_res_1322_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__1(v_e_1305_, v_h_x27_1306_, v_mvarId_1307_, v___x_6588__boxed_1321_, v_newIndices_1309_, v___x_1310_, v_a_1311_, v___x_1312_, v___x_1313_, v_newEqs_1314_, v_newRefls_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_);
return v_res_1322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__2(lean_object* v_e_1323_, lean_object* v_mvarId_1324_, uint8_t v___x_1325_, lean_object* v_newIndices_1326_, lean_object* v___x_1327_, lean_object* v_a_1328_, lean_object* v___x_1329_, lean_object* v___x_1330_, lean_object* v_h_x27_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_){
_start:
{
lean_object* v___x_1337_; lean_object* v___f_1338_; lean_object* v___x_1339_; 
v___x_1337_ = lean_box(v___x_1325_);
lean_inc_ref(v___x_1330_);
lean_inc_ref(v_newIndices_1326_);
v___f_1338_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__1___boxed), 16, 9);
lean_closure_set(v___f_1338_, 0, v_e_1323_);
lean_closure_set(v___f_1338_, 1, v_h_x27_1331_);
lean_closure_set(v___f_1338_, 2, v_mvarId_1324_);
lean_closure_set(v___f_1338_, 3, v___x_1337_);
lean_closure_set(v___f_1338_, 4, v_newIndices_1326_);
lean_closure_set(v___f_1338_, 5, v___x_1327_);
lean_closure_set(v___f_1338_, 6, v_a_1328_);
lean_closure_set(v___f_1338_, 7, v___x_1329_);
lean_closure_set(v___f_1338_, 8, v___x_1330_);
v___x_1339_ = l_Lean_Meta_withNewEqs___redArg(v___x_1330_, v_newIndices_1326_, v___f_1338_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_);
return v___x_1339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__2___boxed(lean_object* v_e_1340_, lean_object* v_mvarId_1341_, lean_object* v___x_1342_, lean_object* v_newIndices_1343_, lean_object* v___x_1344_, lean_object* v_a_1345_, lean_object* v___x_1346_, lean_object* v___x_1347_, lean_object* v_h_x27_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_){
_start:
{
uint8_t v___x_6653__boxed_1354_; lean_object* v_res_1355_; 
v___x_6653__boxed_1354_ = lean_unbox(v___x_1342_);
v_res_1355_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__2(v_e_1340_, v_mvarId_1341_, v___x_6653__boxed_1354_, v_newIndices_1343_, v___x_1344_, v_a_1345_, v___x_1346_, v___x_1347_, v_h_x27_1348_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_);
return v_res_1355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__3(lean_object* v_e_1359_, lean_object* v_mvarId_1360_, uint8_t v___x_1361_, lean_object* v___x_1362_, lean_object* v_a_1363_, lean_object* v___x_1364_, lean_object* v___x_1365_, lean_object* v___x_1366_, lean_object* v_varName_x3f_1367_, lean_object* v_newIndices_1368_, lean_object* v_x_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_){
_start:
{
lean_object* v___x_1375_; lean_object* v___f_1376_; lean_object* v___x_1377_; 
v___x_1375_ = lean_box(v___x_1361_);
lean_inc_ref(v_newIndices_1368_);
v___f_1376_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__2___boxed), 14, 8);
lean_closure_set(v___f_1376_, 0, v_e_1359_);
lean_closure_set(v___f_1376_, 1, v_mvarId_1360_);
lean_closure_set(v___f_1376_, 2, v___x_1375_);
lean_closure_set(v___f_1376_, 3, v_newIndices_1368_);
lean_closure_set(v___f_1376_, 4, v___x_1362_);
lean_closure_set(v___f_1376_, 5, v_a_1363_);
lean_closure_set(v___f_1376_, 6, v___x_1364_);
lean_closure_set(v___f_1376_, 7, v___x_1365_);
v___x_1377_ = l_Lean_mkAppN(v___x_1366_, v_newIndices_1368_);
lean_dec_ref(v_newIndices_1368_);
if (lean_obj_tag(v_varName_x3f_1367_) == 1)
{
lean_object* v_val_1378_; lean_object* v___x_1379_; 
v_val_1378_ = lean_ctor_get(v_varName_x3f_1367_, 0);
lean_inc(v_val_1378_);
lean_dec_ref(v_varName_x3f_1367_);
v___x_1379_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0___redArg(v_val_1378_, v___x_1377_, v___f_1376_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_);
return v___x_1379_;
}
else
{
lean_object* v___x_1380_; lean_object* v___x_1381_; 
lean_dec(v_varName_x3f_1367_);
v___x_1380_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__3___closed__1));
lean_inc(v___y_1373_);
lean_inc_ref(v___y_1372_);
v___x_1381_ = l_Lean_Core_mkFreshUserName(v___x_1380_, v___y_1372_, v___y_1373_);
if (lean_obj_tag(v___x_1381_) == 0)
{
lean_object* v_a_1382_; lean_object* v___x_1383_; 
v_a_1382_ = lean_ctor_get(v___x_1381_, 0);
lean_inc(v_a_1382_);
lean_dec_ref(v___x_1381_);
v___x_1383_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0___redArg(v_a_1382_, v___x_1377_, v___f_1376_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_);
return v___x_1383_;
}
else
{
lean_object* v_a_1384_; lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1391_; 
lean_dec_ref(v___x_1377_);
lean_dec_ref(v___f_1376_);
lean_dec(v___y_1373_);
lean_dec_ref(v___y_1372_);
lean_dec(v___y_1371_);
lean_dec_ref(v___y_1370_);
v_a_1384_ = lean_ctor_get(v___x_1381_, 0);
v_isSharedCheck_1391_ = !lean_is_exclusive(v___x_1381_);
if (v_isSharedCheck_1391_ == 0)
{
v___x_1386_ = v___x_1381_;
v_isShared_1387_ = v_isSharedCheck_1391_;
goto v_resetjp_1385_;
}
else
{
lean_inc(v_a_1384_);
lean_dec(v___x_1381_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1391_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
lean_object* v___x_1389_; 
if (v_isShared_1387_ == 0)
{
v___x_1389_ = v___x_1386_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v_a_1384_);
v___x_1389_ = v_reuseFailAlloc_1390_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
return v___x_1389_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__3___boxed(lean_object* v_e_1392_, lean_object* v_mvarId_1393_, lean_object* v___x_1394_, lean_object* v___x_1395_, lean_object* v_a_1396_, lean_object* v___x_1397_, lean_object* v___x_1398_, lean_object* v___x_1399_, lean_object* v_varName_x3f_1400_, lean_object* v_newIndices_1401_, lean_object* v_x_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_){
_start:
{
uint8_t v___x_6695__boxed_1408_; lean_object* v_res_1409_; 
v___x_6695__boxed_1408_ = lean_unbox(v___x_1394_);
v_res_1409_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__3(v_e_1392_, v_mvarId_1393_, v___x_6695__boxed_1408_, v___x_1395_, v_a_1396_, v___x_1397_, v___x_1398_, v___x_1399_, v_varName_x3f_1400_, v_newIndices_1401_, v_x_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_);
lean_dec_ref(v_x_1402_);
return v_res_1409_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__4(void){
_start:
{
lean_object* v___x_1416_; lean_object* v___x_1417_; 
v___x_1416_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__3));
v___x_1417_ = l_Lean_MessageData_ofFormat(v___x_1416_);
return v___x_1417_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__5(void){
_start:
{
lean_object* v___x_1418_; lean_object* v___x_1419_; 
v___x_1418_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__4, &l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__4_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__4);
v___x_1419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1419_, 0, v___x_1418_);
return v___x_1419_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__8(void){
_start:
{
lean_object* v___x_1423_; lean_object* v___x_1424_; 
v___x_1423_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__7));
v___x_1424_ = l_Lean_MessageData_ofFormat(v___x_1423_);
return v___x_1424_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__9(void){
_start:
{
lean_object* v___x_1425_; lean_object* v___x_1426_; 
v___x_1425_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__8, &l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__8_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__8);
v___x_1426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1426_, 0, v___x_1425_);
return v___x_1426_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__12(void){
_start:
{
lean_object* v___x_1430_; lean_object* v___x_1431_; 
v___x_1430_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__11));
v___x_1431_ = l_Lean_MessageData_ofFormat(v___x_1430_);
return v___x_1431_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__13(void){
_start:
{
lean_object* v___x_1432_; lean_object* v___x_1433_; 
v___x_1432_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__12, &l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__12_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__12);
v___x_1433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1433_, 0, v___x_1432_);
return v___x_1433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0(lean_object* v_mvarId_1434_, lean_object* v_e_1435_, lean_object* v___x_1436_, lean_object* v_a_1437_, lean_object* v_varName_x3f_1438_, lean_object* v_x_1439_, lean_object* v_x_1440_, lean_object* v_x_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_){
_start:
{
if (lean_obj_tag(v_x_1439_) == 5)
{
lean_object* v_fn_1447_; lean_object* v_arg_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; 
v_fn_1447_ = lean_ctor_get(v_x_1439_, 0);
lean_inc_ref(v_fn_1447_);
v_arg_1448_ = lean_ctor_get(v_x_1439_, 1);
lean_inc_ref(v_arg_1448_);
lean_dec_ref(v_x_1439_);
v___x_1449_ = lean_array_set(v_x_1440_, v_x_1441_, v_arg_1448_);
v___x_1450_ = lean_unsigned_to_nat(1u);
v___x_1451_ = lean_nat_sub(v_x_1441_, v___x_1450_);
lean_dec(v_x_1441_);
v_x_1439_ = v_fn_1447_;
v_x_1440_ = v___x_1449_;
v_x_1441_ = v___x_1451_;
goto _start;
}
else
{
lean_object* v___x_1453_; lean_object* v___y_1455_; lean_object* v___y_1456_; lean_object* v___y_1457_; lean_object* v___y_1458_; 
lean_dec(v_x_1441_);
v___x_1453_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__1));
if (lean_obj_tag(v_x_1439_) == 4)
{
lean_object* v_declName_1461_; lean_object* v___x_1462_; lean_object* v_env_1463_; uint8_t v___x_1464_; lean_object* v___x_1465_; 
v_declName_1461_ = lean_ctor_get(v_x_1439_, 0);
v___x_1462_ = lean_st_ref_get(v___y_1445_);
v_env_1463_ = lean_ctor_get(v___x_1462_, 0);
lean_inc_ref(v_env_1463_);
lean_dec(v___x_1462_);
v___x_1464_ = 0;
lean_inc(v_declName_1461_);
v___x_1465_ = l_Lean_Environment_find_x3f(v_env_1463_, v_declName_1461_, v___x_1464_);
if (lean_obj_tag(v___x_1465_) == 0)
{
lean_dec_ref(v_x_1439_);
lean_dec_ref(v_x_1440_);
lean_dec(v_varName_x3f_1438_);
lean_dec_ref(v_a_1437_);
lean_dec_ref(v___x_1436_);
lean_dec_ref(v_e_1435_);
v___y_1455_ = v___y_1442_;
v___y_1456_ = v___y_1443_;
v___y_1457_ = v___y_1444_;
v___y_1458_ = v___y_1445_;
goto v___jp_1454_;
}
else
{
lean_object* v_val_1466_; 
v_val_1466_ = lean_ctor_get(v___x_1465_, 0);
lean_inc(v_val_1466_);
lean_dec_ref(v___x_1465_);
if (lean_obj_tag(v_val_1466_) == 5)
{
lean_object* v_val_1467_; lean_object* v_numParams_1468_; lean_object* v_numIndices_1469_; lean_object* v___y_1471_; lean_object* v___y_1472_; lean_object* v___y_1473_; lean_object* v___y_1474_; lean_object* v___y_1495_; lean_object* v___y_1496_; lean_object* v___y_1497_; lean_object* v___y_1498_; lean_object* v___x_1512_; uint8_t v___x_1513_; 
v_val_1467_ = lean_ctor_get(v_val_1466_, 0);
lean_inc_ref(v_val_1467_);
lean_dec_ref(v_val_1466_);
v_numParams_1468_ = lean_ctor_get(v_val_1467_, 1);
lean_inc(v_numParams_1468_);
v_numIndices_1469_ = lean_ctor_get(v_val_1467_, 2);
lean_inc(v_numIndices_1469_);
lean_dec_ref(v_val_1467_);
v___x_1512_ = lean_unsigned_to_nat(0u);
v___x_1513_ = lean_nat_dec_lt(v___x_1512_, v_numIndices_1469_);
if (v___x_1513_ == 0)
{
lean_object* v___x_1514_; lean_object* v___x_1515_; 
v___x_1514_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__13, &l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__13_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__13);
lean_inc(v_mvarId_1434_);
v___x_1515_ = l_Lean_Meta_throwTacticEx___redArg(v___x_1453_, v_mvarId_1434_, v___x_1514_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_);
if (lean_obj_tag(v___x_1515_) == 0)
{
lean_dec_ref(v___x_1515_);
v___y_1495_ = v___y_1442_;
v___y_1496_ = v___y_1443_;
v___y_1497_ = v___y_1444_;
v___y_1498_ = v___y_1445_;
goto v___jp_1494_;
}
else
{
lean_object* v_a_1516_; lean_object* v___x_1518_; uint8_t v_isShared_1519_; uint8_t v_isSharedCheck_1523_; 
lean_dec(v_numIndices_1469_);
lean_dec(v_numParams_1468_);
lean_dec_ref(v_x_1439_);
lean_dec(v___y_1445_);
lean_dec_ref(v___y_1444_);
lean_dec(v___y_1443_);
lean_dec_ref(v___y_1442_);
lean_dec_ref(v_x_1440_);
lean_dec(v_varName_x3f_1438_);
lean_dec_ref(v_a_1437_);
lean_dec_ref(v___x_1436_);
lean_dec_ref(v_e_1435_);
lean_dec(v_mvarId_1434_);
v_a_1516_ = lean_ctor_get(v___x_1515_, 0);
v_isSharedCheck_1523_ = !lean_is_exclusive(v___x_1515_);
if (v_isSharedCheck_1523_ == 0)
{
v___x_1518_ = v___x_1515_;
v_isShared_1519_ = v_isSharedCheck_1523_;
goto v_resetjp_1517_;
}
else
{
lean_inc(v_a_1516_);
lean_dec(v___x_1515_);
v___x_1518_ = lean_box(0);
v_isShared_1519_ = v_isSharedCheck_1523_;
goto v_resetjp_1517_;
}
v_resetjp_1517_:
{
lean_object* v___x_1521_; 
if (v_isShared_1519_ == 0)
{
v___x_1521_ = v___x_1518_;
goto v_reusejp_1520_;
}
else
{
lean_object* v_reuseFailAlloc_1522_; 
v_reuseFailAlloc_1522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1522_, 0, v_a_1516_);
v___x_1521_ = v_reuseFailAlloc_1522_;
goto v_reusejp_1520_;
}
v_reusejp_1520_:
{
return v___x_1521_;
}
}
}
}
else
{
v___y_1495_ = v___y_1442_;
v___y_1496_ = v___y_1443_;
v___y_1497_ = v___y_1444_;
v___y_1498_ = v___y_1445_;
goto v___jp_1494_;
}
v___jp_1470_:
{
lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; 
v___x_1475_ = lean_unsigned_to_nat(0u);
v___x_1476_ = l_Array_extract___redArg(v_x_1440_, v___x_1475_, v_numParams_1468_);
v___x_1477_ = l_Lean_mkAppN(v_x_1439_, v___x_1476_);
lean_dec_ref(v___x_1476_);
lean_inc(v___y_1474_);
lean_inc_ref(v___y_1473_);
lean_inc(v___y_1472_);
lean_inc_ref(v___y_1471_);
lean_inc_ref(v___x_1477_);
v___x_1478_ = lean_infer_type(v___x_1477_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_);
if (lean_obj_tag(v___x_1478_) == 0)
{
lean_object* v_a_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___f_1484_; lean_object* v___x_1485_; 
v_a_1479_ = lean_ctor_get(v___x_1478_, 0);
lean_inc(v_a_1479_);
lean_dec_ref(v___x_1478_);
v___x_1480_ = lean_array_get_size(v_x_1440_);
v___x_1481_ = lean_nat_sub(v___x_1480_, v_numIndices_1469_);
lean_dec(v_numIndices_1469_);
v___x_1482_ = l_Array_extract___redArg(v_x_1440_, v___x_1481_, v___x_1480_);
lean_dec_ref(v_x_1440_);
v___x_1483_ = lean_box(v___x_1464_);
v___f_1484_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__3___boxed), 16, 9);
lean_closure_set(v___f_1484_, 0, v_e_1435_);
lean_closure_set(v___f_1484_, 1, v_mvarId_1434_);
lean_closure_set(v___f_1484_, 2, v___x_1483_);
lean_closure_set(v___f_1484_, 3, v___x_1436_);
lean_closure_set(v___f_1484_, 4, v_a_1437_);
lean_closure_set(v___f_1484_, 5, v___x_1475_);
lean_closure_set(v___f_1484_, 6, v___x_1482_);
lean_closure_set(v___f_1484_, 7, v___x_1477_);
lean_closure_set(v___f_1484_, 8, v_varName_x3f_1438_);
v___x_1485_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_generalizeTargetsEq_spec__0___redArg(v_a_1479_, v___f_1484_, v___x_1464_, v___x_1464_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_);
return v___x_1485_;
}
else
{
lean_object* v_a_1486_; lean_object* v___x_1488_; uint8_t v_isShared_1489_; uint8_t v_isSharedCheck_1493_; 
lean_dec_ref(v___x_1477_);
lean_dec(v___y_1474_);
lean_dec_ref(v___y_1473_);
lean_dec(v___y_1472_);
lean_dec_ref(v___y_1471_);
lean_dec(v_numIndices_1469_);
lean_dec_ref(v_x_1440_);
lean_dec(v_varName_x3f_1438_);
lean_dec_ref(v_a_1437_);
lean_dec_ref(v___x_1436_);
lean_dec_ref(v_e_1435_);
lean_dec(v_mvarId_1434_);
v_a_1486_ = lean_ctor_get(v___x_1478_, 0);
v_isSharedCheck_1493_ = !lean_is_exclusive(v___x_1478_);
if (v_isSharedCheck_1493_ == 0)
{
v___x_1488_ = v___x_1478_;
v_isShared_1489_ = v_isSharedCheck_1493_;
goto v_resetjp_1487_;
}
else
{
lean_inc(v_a_1486_);
lean_dec(v___x_1478_);
v___x_1488_ = lean_box(0);
v_isShared_1489_ = v_isSharedCheck_1493_;
goto v_resetjp_1487_;
}
v_resetjp_1487_:
{
lean_object* v___x_1491_; 
if (v_isShared_1489_ == 0)
{
v___x_1491_ = v___x_1488_;
goto v_reusejp_1490_;
}
else
{
lean_object* v_reuseFailAlloc_1492_; 
v_reuseFailAlloc_1492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1492_, 0, v_a_1486_);
v___x_1491_ = v_reuseFailAlloc_1492_;
goto v_reusejp_1490_;
}
v_reusejp_1490_:
{
return v___x_1491_;
}
}
}
}
v___jp_1494_:
{
lean_object* v___x_1499_; lean_object* v___x_1500_; uint8_t v___x_1501_; 
v___x_1499_ = lean_array_get_size(v_x_1440_);
v___x_1500_ = lean_nat_add(v_numIndices_1469_, v_numParams_1468_);
v___x_1501_ = lean_nat_dec_eq(v___x_1499_, v___x_1500_);
lean_dec(v___x_1500_);
if (v___x_1501_ == 0)
{
lean_object* v___x_1502_; lean_object* v___x_1503_; 
v___x_1502_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__9, &l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__9_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__9);
lean_inc(v_mvarId_1434_);
v___x_1503_ = l_Lean_Meta_throwTacticEx___redArg(v___x_1453_, v_mvarId_1434_, v___x_1502_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_);
if (lean_obj_tag(v___x_1503_) == 0)
{
lean_dec_ref(v___x_1503_);
v___y_1471_ = v___y_1495_;
v___y_1472_ = v___y_1496_;
v___y_1473_ = v___y_1497_;
v___y_1474_ = v___y_1498_;
goto v___jp_1470_;
}
else
{
lean_object* v_a_1504_; lean_object* v___x_1506_; uint8_t v_isShared_1507_; uint8_t v_isSharedCheck_1511_; 
lean_dec(v___y_1498_);
lean_dec_ref(v___y_1497_);
lean_dec(v___y_1496_);
lean_dec_ref(v___y_1495_);
lean_dec(v_numIndices_1469_);
lean_dec(v_numParams_1468_);
lean_dec_ref(v_x_1439_);
lean_dec_ref(v_x_1440_);
lean_dec(v_varName_x3f_1438_);
lean_dec_ref(v_a_1437_);
lean_dec_ref(v___x_1436_);
lean_dec_ref(v_e_1435_);
lean_dec(v_mvarId_1434_);
v_a_1504_ = lean_ctor_get(v___x_1503_, 0);
v_isSharedCheck_1511_ = !lean_is_exclusive(v___x_1503_);
if (v_isSharedCheck_1511_ == 0)
{
v___x_1506_ = v___x_1503_;
v_isShared_1507_ = v_isSharedCheck_1511_;
goto v_resetjp_1505_;
}
else
{
lean_inc(v_a_1504_);
lean_dec(v___x_1503_);
v___x_1506_ = lean_box(0);
v_isShared_1507_ = v_isSharedCheck_1511_;
goto v_resetjp_1505_;
}
v_resetjp_1505_:
{
lean_object* v___x_1509_; 
if (v_isShared_1507_ == 0)
{
v___x_1509_ = v___x_1506_;
goto v_reusejp_1508_;
}
else
{
lean_object* v_reuseFailAlloc_1510_; 
v_reuseFailAlloc_1510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1510_, 0, v_a_1504_);
v___x_1509_ = v_reuseFailAlloc_1510_;
goto v_reusejp_1508_;
}
v_reusejp_1508_:
{
return v___x_1509_;
}
}
}
}
else
{
v___y_1471_ = v___y_1495_;
v___y_1472_ = v___y_1496_;
v___y_1473_ = v___y_1497_;
v___y_1474_ = v___y_1498_;
goto v___jp_1470_;
}
}
}
else
{
lean_dec(v_val_1466_);
lean_dec_ref(v_x_1439_);
lean_dec_ref(v_x_1440_);
lean_dec(v_varName_x3f_1438_);
lean_dec_ref(v_a_1437_);
lean_dec_ref(v___x_1436_);
lean_dec_ref(v_e_1435_);
v___y_1455_ = v___y_1442_;
v___y_1456_ = v___y_1443_;
v___y_1457_ = v___y_1444_;
v___y_1458_ = v___y_1445_;
goto v___jp_1454_;
}
}
}
else
{
lean_dec_ref(v_x_1440_);
lean_dec_ref(v_x_1439_);
lean_dec(v_varName_x3f_1438_);
lean_dec_ref(v_a_1437_);
lean_dec_ref(v___x_1436_);
lean_dec_ref(v_e_1435_);
v___y_1455_ = v___y_1442_;
v___y_1456_ = v___y_1443_;
v___y_1457_ = v___y_1444_;
v___y_1458_ = v___y_1445_;
goto v___jp_1454_;
}
v___jp_1454_:
{
lean_object* v___x_1459_; lean_object* v___x_1460_; 
v___x_1459_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__5, &l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__5_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__5);
v___x_1460_ = l_Lean_Meta_throwTacticEx___redArg(v___x_1453_, v_mvarId_1434_, v___x_1459_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_);
lean_dec(v___y_1458_);
lean_dec_ref(v___y_1457_);
lean_dec(v___y_1456_);
lean_dec_ref(v___y_1455_);
return v___x_1460_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___boxed(lean_object* v_mvarId_1524_, lean_object* v_e_1525_, lean_object* v___x_1526_, lean_object* v_a_1527_, lean_object* v_varName_x3f_1528_, lean_object* v_x_1529_, lean_object* v_x_1530_, lean_object* v_x_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_){
_start:
{
lean_object* v_res_1537_; 
v_res_1537_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0(v_mvarId_1524_, v_e_1525_, v___x_1526_, v_a_1527_, v_varName_x3f_1528_, v_x_1529_, v_x_1530_, v_x_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_);
return v_res_1537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeIndices_x27___lam__0(lean_object* v_mvarId_1538_, lean_object* v_e_1539_, lean_object* v_varName_x3f_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_){
_start:
{
lean_object* v___x_1546_; 
v___x_1546_ = l_Lean_Meta_getLocalInstances___redArg(v___y_1541_);
if (lean_obj_tag(v___x_1546_) == 0)
{
lean_object* v_a_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; 
v_a_1547_ = lean_ctor_get(v___x_1546_, 0);
lean_inc(v_a_1547_);
lean_dec_ref(v___x_1546_);
v___x_1548_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__1));
lean_inc(v_mvarId_1538_);
v___x_1549_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_1538_, v___x_1548_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_);
if (lean_obj_tag(v___x_1549_) == 0)
{
lean_object* v_lctx_1550_; lean_object* v___x_1551_; 
lean_dec_ref(v___x_1549_);
v_lctx_1550_ = lean_ctor_get(v___y_1541_, 2);
lean_inc_ref(v_lctx_1550_);
lean_inc(v___y_1544_);
lean_inc_ref(v___y_1543_);
lean_inc(v___y_1542_);
lean_inc_ref(v___y_1541_);
lean_inc_ref(v_e_1539_);
v___x_1551_ = lean_infer_type(v_e_1539_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_);
if (lean_obj_tag(v___x_1551_) == 0)
{
lean_object* v_a_1552_; lean_object* v___x_1553_; 
v_a_1552_ = lean_ctor_get(v___x_1551_, 0);
lean_inc(v_a_1552_);
lean_dec_ref(v___x_1551_);
lean_inc(v___y_1544_);
lean_inc_ref(v___y_1543_);
lean_inc(v___y_1542_);
lean_inc_ref(v___y_1541_);
v___x_1553_ = l_Lean_Meta_whnfD(v_a_1552_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_);
if (lean_obj_tag(v___x_1553_) == 0)
{
lean_object* v_a_1554_; lean_object* v_dummy_1555_; lean_object* v_nargs_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; 
v_a_1554_ = lean_ctor_get(v___x_1553_, 0);
lean_inc(v_a_1554_);
lean_dec_ref(v___x_1553_);
v_dummy_1555_ = lean_obj_once(&l_Lean_Meta_getInductiveUniverseAndParams___closed__0, &l_Lean_Meta_getInductiveUniverseAndParams___closed__0_once, _init_l_Lean_Meta_getInductiveUniverseAndParams___closed__0);
v_nargs_1556_ = l_Lean_Expr_getAppNumArgs(v_a_1554_);
lean_inc(v_nargs_1556_);
v___x_1557_ = lean_mk_array(v_nargs_1556_, v_dummy_1555_);
v___x_1558_ = lean_unsigned_to_nat(1u);
v___x_1559_ = lean_nat_sub(v_nargs_1556_, v___x_1558_);
lean_dec(v_nargs_1556_);
v___x_1560_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0(v_mvarId_1538_, v_e_1539_, v_lctx_1550_, v_a_1547_, v_varName_x3f_1540_, v_a_1554_, v___x_1557_, v___x_1559_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_);
return v___x_1560_;
}
else
{
lean_object* v_a_1561_; lean_object* v___x_1563_; uint8_t v_isShared_1564_; uint8_t v_isSharedCheck_1568_; 
lean_dec_ref(v_lctx_1550_);
lean_dec(v_a_1547_);
lean_dec(v___y_1544_);
lean_dec_ref(v___y_1543_);
lean_dec(v___y_1542_);
lean_dec_ref(v___y_1541_);
lean_dec(v_varName_x3f_1540_);
lean_dec_ref(v_e_1539_);
lean_dec(v_mvarId_1538_);
v_a_1561_ = lean_ctor_get(v___x_1553_, 0);
v_isSharedCheck_1568_ = !lean_is_exclusive(v___x_1553_);
if (v_isSharedCheck_1568_ == 0)
{
v___x_1563_ = v___x_1553_;
v_isShared_1564_ = v_isSharedCheck_1568_;
goto v_resetjp_1562_;
}
else
{
lean_inc(v_a_1561_);
lean_dec(v___x_1553_);
v___x_1563_ = lean_box(0);
v_isShared_1564_ = v_isSharedCheck_1568_;
goto v_resetjp_1562_;
}
v_resetjp_1562_:
{
lean_object* v___x_1566_; 
if (v_isShared_1564_ == 0)
{
v___x_1566_ = v___x_1563_;
goto v_reusejp_1565_;
}
else
{
lean_object* v_reuseFailAlloc_1567_; 
v_reuseFailAlloc_1567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1567_, 0, v_a_1561_);
v___x_1566_ = v_reuseFailAlloc_1567_;
goto v_reusejp_1565_;
}
v_reusejp_1565_:
{
return v___x_1566_;
}
}
}
}
else
{
lean_object* v_a_1569_; lean_object* v___x_1571_; uint8_t v_isShared_1572_; uint8_t v_isSharedCheck_1576_; 
lean_dec_ref(v_lctx_1550_);
lean_dec(v_a_1547_);
lean_dec(v___y_1544_);
lean_dec_ref(v___y_1543_);
lean_dec(v___y_1542_);
lean_dec_ref(v___y_1541_);
lean_dec(v_varName_x3f_1540_);
lean_dec_ref(v_e_1539_);
lean_dec(v_mvarId_1538_);
v_a_1569_ = lean_ctor_get(v___x_1551_, 0);
v_isSharedCheck_1576_ = !lean_is_exclusive(v___x_1551_);
if (v_isSharedCheck_1576_ == 0)
{
v___x_1571_ = v___x_1551_;
v_isShared_1572_ = v_isSharedCheck_1576_;
goto v_resetjp_1570_;
}
else
{
lean_inc(v_a_1569_);
lean_dec(v___x_1551_);
v___x_1571_ = lean_box(0);
v_isShared_1572_ = v_isSharedCheck_1576_;
goto v_resetjp_1570_;
}
v_resetjp_1570_:
{
lean_object* v___x_1574_; 
if (v_isShared_1572_ == 0)
{
v___x_1574_ = v___x_1571_;
goto v_reusejp_1573_;
}
else
{
lean_object* v_reuseFailAlloc_1575_; 
v_reuseFailAlloc_1575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1575_, 0, v_a_1569_);
v___x_1574_ = v_reuseFailAlloc_1575_;
goto v_reusejp_1573_;
}
v_reusejp_1573_:
{
return v___x_1574_;
}
}
}
}
else
{
lean_object* v_a_1577_; lean_object* v___x_1579_; uint8_t v_isShared_1580_; uint8_t v_isSharedCheck_1584_; 
lean_dec(v_a_1547_);
lean_dec(v___y_1544_);
lean_dec_ref(v___y_1543_);
lean_dec(v___y_1542_);
lean_dec_ref(v___y_1541_);
lean_dec(v_varName_x3f_1540_);
lean_dec_ref(v_e_1539_);
lean_dec(v_mvarId_1538_);
v_a_1577_ = lean_ctor_get(v___x_1549_, 0);
v_isSharedCheck_1584_ = !lean_is_exclusive(v___x_1549_);
if (v_isSharedCheck_1584_ == 0)
{
v___x_1579_ = v___x_1549_;
v_isShared_1580_ = v_isSharedCheck_1584_;
goto v_resetjp_1578_;
}
else
{
lean_inc(v_a_1577_);
lean_dec(v___x_1549_);
v___x_1579_ = lean_box(0);
v_isShared_1580_ = v_isSharedCheck_1584_;
goto v_resetjp_1578_;
}
v_resetjp_1578_:
{
lean_object* v___x_1582_; 
if (v_isShared_1580_ == 0)
{
v___x_1582_ = v___x_1579_;
goto v_reusejp_1581_;
}
else
{
lean_object* v_reuseFailAlloc_1583_; 
v_reuseFailAlloc_1583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1583_, 0, v_a_1577_);
v___x_1582_ = v_reuseFailAlloc_1583_;
goto v_reusejp_1581_;
}
v_reusejp_1581_:
{
return v___x_1582_;
}
}
}
}
else
{
lean_object* v_a_1585_; lean_object* v___x_1587_; uint8_t v_isShared_1588_; uint8_t v_isSharedCheck_1592_; 
lean_dec(v___y_1544_);
lean_dec_ref(v___y_1543_);
lean_dec(v___y_1542_);
lean_dec_ref(v___y_1541_);
lean_dec(v_varName_x3f_1540_);
lean_dec_ref(v_e_1539_);
lean_dec(v_mvarId_1538_);
v_a_1585_ = lean_ctor_get(v___x_1546_, 0);
v_isSharedCheck_1592_ = !lean_is_exclusive(v___x_1546_);
if (v_isSharedCheck_1592_ == 0)
{
v___x_1587_ = v___x_1546_;
v_isShared_1588_ = v_isSharedCheck_1592_;
goto v_resetjp_1586_;
}
else
{
lean_inc(v_a_1585_);
lean_dec(v___x_1546_);
v___x_1587_ = lean_box(0);
v_isShared_1588_ = v_isSharedCheck_1592_;
goto v_resetjp_1586_;
}
v_resetjp_1586_:
{
lean_object* v___x_1590_; 
if (v_isShared_1588_ == 0)
{
v___x_1590_ = v___x_1587_;
goto v_reusejp_1589_;
}
else
{
lean_object* v_reuseFailAlloc_1591_; 
v_reuseFailAlloc_1591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1591_, 0, v_a_1585_);
v___x_1590_ = v_reuseFailAlloc_1591_;
goto v_reusejp_1589_;
}
v_reusejp_1589_:
{
return v___x_1590_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeIndices_x27___lam__0___boxed(lean_object* v_mvarId_1593_, lean_object* v_e_1594_, lean_object* v_varName_x3f_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_){
_start:
{
lean_object* v_res_1601_; 
v_res_1601_ = l_Lean_Meta_generalizeIndices_x27___lam__0(v_mvarId_1593_, v_e_1594_, v_varName_x3f_1595_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_);
return v_res_1601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeIndices_x27(lean_object* v_mvarId_1602_, lean_object* v_e_1603_, lean_object* v_varName_x3f_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_, lean_object* v_a_1607_, lean_object* v_a_1608_){
_start:
{
lean_object* v___f_1610_; lean_object* v___x_1611_; 
lean_inc(v_mvarId_1602_);
v___f_1610_ = lean_alloc_closure((void*)(l_Lean_Meta_generalizeIndices_x27___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1610_, 0, v_mvarId_1602_);
lean_closure_set(v___f_1610_, 1, v_e_1603_);
lean_closure_set(v___f_1610_, 2, v_varName_x3f_1604_);
v___x_1611_ = l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2___redArg(v_mvarId_1602_, v___f_1610_, v_a_1605_, v_a_1606_, v_a_1607_, v_a_1608_);
return v___x_1611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeIndices_x27___boxed(lean_object* v_mvarId_1612_, lean_object* v_e_1613_, lean_object* v_varName_x3f_1614_, lean_object* v_a_1615_, lean_object* v_a_1616_, lean_object* v_a_1617_, lean_object* v_a_1618_, lean_object* v_a_1619_){
_start:
{
lean_object* v_res_1620_; 
v_res_1620_ = l_Lean_Meta_generalizeIndices_x27(v_mvarId_1612_, v_e_1613_, v_varName_x3f_1614_, v_a_1615_, v_a_1616_, v_a_1617_, v_a_1618_);
return v_res_1620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeIndices___lam__0(lean_object* v_fvarId_1621_, lean_object* v_mvarId_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_){
_start:
{
lean_object* v___x_1628_; 
lean_inc_ref(v___y_1623_);
v___x_1628_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_1621_, v___y_1623_, v___y_1625_, v___y_1626_);
if (lean_obj_tag(v___x_1628_) == 0)
{
lean_object* v_a_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; 
v_a_1629_ = lean_ctor_get(v___x_1628_, 0);
lean_inc(v_a_1629_);
lean_dec_ref(v___x_1628_);
lean_inc(v_a_1629_);
v___x_1630_ = l_Lean_LocalDecl_toExpr(v_a_1629_);
v___x_1631_ = l_Lean_LocalDecl_userName(v_a_1629_);
lean_dec(v_a_1629_);
v___x_1632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1632_, 0, v___x_1631_);
v___x_1633_ = l_Lean_Meta_generalizeIndices_x27(v_mvarId_1622_, v___x_1630_, v___x_1632_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_);
return v___x_1633_;
}
else
{
lean_object* v_a_1634_; lean_object* v___x_1636_; uint8_t v_isShared_1637_; uint8_t v_isSharedCheck_1641_; 
lean_dec(v___y_1626_);
lean_dec_ref(v___y_1625_);
lean_dec(v___y_1624_);
lean_dec_ref(v___y_1623_);
lean_dec(v_mvarId_1622_);
v_a_1634_ = lean_ctor_get(v___x_1628_, 0);
v_isSharedCheck_1641_ = !lean_is_exclusive(v___x_1628_);
if (v_isSharedCheck_1641_ == 0)
{
v___x_1636_ = v___x_1628_;
v_isShared_1637_ = v_isSharedCheck_1641_;
goto v_resetjp_1635_;
}
else
{
lean_inc(v_a_1634_);
lean_dec(v___x_1628_);
v___x_1636_ = lean_box(0);
v_isShared_1637_ = v_isSharedCheck_1641_;
goto v_resetjp_1635_;
}
v_resetjp_1635_:
{
lean_object* v___x_1639_; 
if (v_isShared_1637_ == 0)
{
v___x_1639_ = v___x_1636_;
goto v_reusejp_1638_;
}
else
{
lean_object* v_reuseFailAlloc_1640_; 
v_reuseFailAlloc_1640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1640_, 0, v_a_1634_);
v___x_1639_ = v_reuseFailAlloc_1640_;
goto v_reusejp_1638_;
}
v_reusejp_1638_:
{
return v___x_1639_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeIndices___lam__0___boxed(lean_object* v_fvarId_1642_, lean_object* v_mvarId_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_){
_start:
{
lean_object* v_res_1649_; 
v_res_1649_ = l_Lean_Meta_generalizeIndices___lam__0(v_fvarId_1642_, v_mvarId_1643_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_);
return v_res_1649_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeIndices(lean_object* v_mvarId_1650_, lean_object* v_fvarId_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_){
_start:
{
lean_object* v___f_1657_; lean_object* v___x_1658_; 
lean_inc(v_mvarId_1650_);
v___f_1657_ = lean_alloc_closure((void*)(l_Lean_Meta_generalizeIndices___lam__0___boxed), 7, 2);
lean_closure_set(v___f_1657_, 0, v_fvarId_1651_);
lean_closure_set(v___f_1657_, 1, v_mvarId_1650_);
v___x_1658_ = l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2___redArg(v_mvarId_1650_, v___f_1657_, v_a_1652_, v_a_1653_, v_a_1654_, v_a_1655_);
return v___x_1658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeIndices___boxed(lean_object* v_mvarId_1659_, lean_object* v_fvarId_1660_, lean_object* v_a_1661_, lean_object* v_a_1662_, lean_object* v_a_1663_, lean_object* v_a_1664_, lean_object* v_a_1665_){
_start:
{
lean_object* v_res_1666_; 
v_res_1666_ = l_Lean_Meta_generalizeIndices(v_mvarId_1659_, v_fvarId_1660_, v_a_1661_, v_a_1662_, v_a_1663_, v_a_1664_);
return v_res_1666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0___redArg(lean_object* v___x_1668_, lean_object* v_a_1669_, lean_object* v_x_1670_, lean_object* v_x_1671_, lean_object* v_x_1672_, lean_object* v___y_1673_){
_start:
{
if (lean_obj_tag(v_x_1670_) == 5)
{
lean_object* v_fn_1678_; lean_object* v_arg_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; 
v_fn_1678_ = lean_ctor_get(v_x_1670_, 0);
lean_inc_ref(v_fn_1678_);
v_arg_1679_ = lean_ctor_get(v_x_1670_, 1);
lean_inc_ref(v_arg_1679_);
lean_dec_ref(v_x_1670_);
v___x_1680_ = lean_array_set(v_x_1671_, v_x_1672_, v_arg_1679_);
v___x_1681_ = lean_unsigned_to_nat(1u);
v___x_1682_ = lean_nat_sub(v_x_1672_, v___x_1681_);
lean_dec(v_x_1672_);
v_x_1670_ = v_fn_1678_;
v_x_1671_ = v___x_1680_;
v_x_1672_ = v___x_1682_;
goto _start;
}
else
{
lean_dec(v_x_1672_);
if (lean_obj_tag(v_x_1670_) == 4)
{
lean_object* v_declName_1684_; lean_object* v___x_1685_; lean_object* v_env_1686_; uint8_t v___x_1687_; lean_object* v___x_1688_; 
v_declName_1684_ = lean_ctor_get(v_x_1670_, 0);
v___x_1685_ = lean_st_ref_get(v___y_1673_);
v_env_1686_ = lean_ctor_get(v___x_1685_, 0);
lean_inc_ref(v_env_1686_);
lean_dec(v___x_1685_);
v___x_1687_ = 0;
lean_inc(v_declName_1684_);
v___x_1688_ = l_Lean_Environment_find_x3f(v_env_1686_, v_declName_1684_, v___x_1687_);
if (lean_obj_tag(v___x_1688_) == 0)
{
lean_dec_ref(v_x_1670_);
lean_dec_ref(v_x_1671_);
lean_dec_ref(v_a_1669_);
lean_dec_ref(v___x_1668_);
goto v___jp_1675_;
}
else
{
lean_object* v_val_1689_; lean_object* v___x_1691_; uint8_t v_isShared_1692_; uint8_t v_isSharedCheck_1727_; 
v_val_1689_ = lean_ctor_get(v___x_1688_, 0);
v_isSharedCheck_1727_ = !lean_is_exclusive(v___x_1688_);
if (v_isSharedCheck_1727_ == 0)
{
v___x_1691_ = v___x_1688_;
v_isShared_1692_ = v_isSharedCheck_1727_;
goto v_resetjp_1690_;
}
else
{
lean_inc(v_val_1689_);
lean_dec(v___x_1688_);
v___x_1691_ = lean_box(0);
v_isShared_1692_ = v_isSharedCheck_1727_;
goto v_resetjp_1690_;
}
v_resetjp_1690_:
{
if (lean_obj_tag(v_val_1689_) == 5)
{
lean_object* v_val_1693_; lean_object* v___x_1695_; uint8_t v_isShared_1696_; uint8_t v_isSharedCheck_1726_; 
v_val_1693_ = lean_ctor_get(v_val_1689_, 0);
v_isSharedCheck_1726_ = !lean_is_exclusive(v_val_1689_);
if (v_isSharedCheck_1726_ == 0)
{
v___x_1695_ = v_val_1689_;
v_isShared_1696_ = v_isSharedCheck_1726_;
goto v_resetjp_1694_;
}
else
{
lean_inc(v_val_1693_);
lean_dec(v_val_1689_);
v___x_1695_ = lean_box(0);
v_isShared_1696_ = v_isSharedCheck_1726_;
goto v_resetjp_1694_;
}
v_resetjp_1694_:
{
lean_object* v_toConstantVal_1697_; lean_object* v_numParams_1698_; lean_object* v_numIndices_1699_; lean_object* v_ctors_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; uint8_t v___x_1703_; 
v_toConstantVal_1697_ = lean_ctor_get(v_val_1693_, 0);
v_numParams_1698_ = lean_ctor_get(v_val_1693_, 1);
v_numIndices_1699_ = lean_ctor_get(v_val_1693_, 2);
v_ctors_1700_ = lean_ctor_get(v_val_1693_, 4);
v___x_1701_ = lean_array_get_size(v_x_1671_);
v___x_1702_ = lean_nat_add(v_numIndices_1699_, v_numParams_1698_);
v___x_1703_ = lean_nat_dec_eq(v___x_1701_, v___x_1702_);
lean_dec(v___x_1702_);
if (v___x_1703_ == 0)
{
lean_object* v___x_1704_; lean_object* v___x_1706_; 
lean_dec_ref(v_val_1693_);
lean_del_object(v___x_1691_);
lean_dec_ref(v_x_1670_);
lean_dec_ref(v_x_1671_);
lean_dec_ref(v_a_1669_);
lean_dec_ref(v___x_1668_);
v___x_1704_ = lean_box(0);
if (v_isShared_1696_ == 0)
{
lean_ctor_set_tag(v___x_1695_, 0);
lean_ctor_set(v___x_1695_, 0, v___x_1704_);
v___x_1706_ = v___x_1695_;
goto v_reusejp_1705_;
}
else
{
lean_object* v_reuseFailAlloc_1707_; 
v_reuseFailAlloc_1707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1707_, 0, v___x_1704_);
v___x_1706_ = v_reuseFailAlloc_1707_;
goto v_reusejp_1705_;
}
v_reusejp_1705_:
{
return v___x_1706_;
}
}
else
{
lean_object* v_name_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; uint8_t v___x_1711_; 
v_name_1708_ = lean_ctor_get(v_toConstantVal_1697_, 0);
v___x_1709_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0___redArg___closed__0));
lean_inc(v_name_1708_);
v___x_1710_ = l_Lean_Name_str___override(v_name_1708_, v___x_1709_);
v___x_1711_ = l_Lean_Environment_contains(v___x_1668_, v___x_1710_, v___x_1703_);
if (v___x_1711_ == 0)
{
lean_object* v___x_1712_; lean_object* v___x_1714_; 
lean_dec_ref(v_val_1693_);
lean_del_object(v___x_1691_);
lean_dec_ref(v_x_1670_);
lean_dec_ref(v_x_1671_);
lean_dec_ref(v_a_1669_);
v___x_1712_ = lean_box(0);
if (v_isShared_1696_ == 0)
{
lean_ctor_set_tag(v___x_1695_, 0);
lean_ctor_set(v___x_1695_, 0, v___x_1712_);
v___x_1714_ = v___x_1695_;
goto v_reusejp_1713_;
}
else
{
lean_object* v_reuseFailAlloc_1715_; 
v_reuseFailAlloc_1715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1715_, 0, v___x_1712_);
v___x_1714_ = v_reuseFailAlloc_1715_;
goto v_reusejp_1713_;
}
v_reusejp_1713_:
{
return v___x_1714_;
}
}
else
{
lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1721_; 
v___x_1716_ = l_List_lengthTR___redArg(v_ctors_1700_);
v___x_1717_ = lean_nat_sub(v___x_1701_, v_numIndices_1699_);
v___x_1718_ = l_Array_extract___redArg(v_x_1671_, v___x_1717_, v___x_1701_);
v___x_1719_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1719_, 0, v_val_1693_);
lean_ctor_set(v___x_1719_, 1, v___x_1716_);
lean_ctor_set(v___x_1719_, 2, v_a_1669_);
lean_ctor_set(v___x_1719_, 3, v_x_1670_);
lean_ctor_set(v___x_1719_, 4, v_x_1671_);
lean_ctor_set(v___x_1719_, 5, v___x_1718_);
if (v_isShared_1692_ == 0)
{
lean_ctor_set(v___x_1691_, 0, v___x_1719_);
v___x_1721_ = v___x_1691_;
goto v_reusejp_1720_;
}
else
{
lean_object* v_reuseFailAlloc_1725_; 
v_reuseFailAlloc_1725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1725_, 0, v___x_1719_);
v___x_1721_ = v_reuseFailAlloc_1725_;
goto v_reusejp_1720_;
}
v_reusejp_1720_:
{
lean_object* v___x_1723_; 
if (v_isShared_1696_ == 0)
{
lean_ctor_set_tag(v___x_1695_, 0);
lean_ctor_set(v___x_1695_, 0, v___x_1721_);
v___x_1723_ = v___x_1695_;
goto v_reusejp_1722_;
}
else
{
lean_object* v_reuseFailAlloc_1724_; 
v_reuseFailAlloc_1724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1724_, 0, v___x_1721_);
v___x_1723_ = v_reuseFailAlloc_1724_;
goto v_reusejp_1722_;
}
v_reusejp_1722_:
{
return v___x_1723_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_1691_);
lean_dec(v_val_1689_);
lean_dec_ref(v_x_1670_);
lean_dec_ref(v_x_1671_);
lean_dec_ref(v_a_1669_);
lean_dec_ref(v___x_1668_);
goto v___jp_1675_;
}
}
}
}
else
{
lean_dec_ref(v_x_1671_);
lean_dec_ref(v_x_1670_);
lean_dec_ref(v_a_1669_);
lean_dec_ref(v___x_1668_);
goto v___jp_1675_;
}
}
v___jp_1675_:
{
lean_object* v___x_1676_; lean_object* v___x_1677_; 
v___x_1676_ = lean_box(0);
v___x_1677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1677_, 0, v___x_1676_);
return v___x_1677_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0___redArg___boxed(lean_object* v___x_1728_, lean_object* v_a_1729_, lean_object* v_x_1730_, lean_object* v_x_1731_, lean_object* v_x_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_){
_start:
{
lean_object* v_res_1735_; 
v_res_1735_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0___redArg(v___x_1728_, v_a_1729_, v_x_1730_, v_x_1731_, v_x_1732_, v___y_1733_);
lean_dec(v___y_1733_);
return v_res_1735_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f(lean_object* v_majorFVarId_1736_, lean_object* v_a_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_){
_start:
{
lean_object* v___x_1742_; lean_object* v_env_1746_; lean_object* v___x_1747_; uint8_t v___x_1748_; uint8_t v___x_1749_; 
v___x_1742_ = lean_st_ref_get(v_a_1740_);
v_env_1746_ = lean_ctor_get(v___x_1742_, 0);
lean_inc_ref(v_env_1746_);
lean_dec(v___x_1742_);
v___x_1747_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__5));
v___x_1748_ = 1;
lean_inc_ref(v_env_1746_);
v___x_1749_ = l_Lean_Environment_contains(v_env_1746_, v___x_1747_, v___x_1748_);
if (v___x_1749_ == 0)
{
lean_dec_ref(v_env_1746_);
lean_dec(v_a_1740_);
lean_dec_ref(v_a_1739_);
lean_dec(v_a_1738_);
lean_dec_ref(v_a_1737_);
lean_dec(v_majorFVarId_1736_);
goto v___jp_1743_;
}
else
{
lean_object* v___x_1750_; uint8_t v___x_1751_; 
v___x_1750_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__1));
lean_inc_ref(v_env_1746_);
v___x_1751_ = l_Lean_Environment_contains(v_env_1746_, v___x_1750_, v___x_1749_);
if (v___x_1751_ == 0)
{
lean_dec_ref(v_env_1746_);
lean_dec(v_a_1740_);
lean_dec_ref(v_a_1739_);
lean_dec(v_a_1738_);
lean_dec_ref(v_a_1737_);
lean_dec(v_majorFVarId_1736_);
goto v___jp_1743_;
}
else
{
lean_object* v___x_1752_; 
lean_inc_ref(v_a_1737_);
v___x_1752_ = l_Lean_FVarId_getDecl___redArg(v_majorFVarId_1736_, v_a_1737_, v_a_1739_, v_a_1740_);
if (lean_obj_tag(v___x_1752_) == 0)
{
lean_object* v_a_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; 
v_a_1753_ = lean_ctor_get(v___x_1752_, 0);
lean_inc(v_a_1753_);
lean_dec_ref(v___x_1752_);
v___x_1754_ = l_Lean_LocalDecl_type(v_a_1753_);
lean_inc(v_a_1740_);
v___x_1755_ = lean_whnf(v___x_1754_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_);
if (lean_obj_tag(v___x_1755_) == 0)
{
lean_object* v_a_1756_; lean_object* v_dummy_1757_; lean_object* v_nargs_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; 
v_a_1756_ = lean_ctor_get(v___x_1755_, 0);
lean_inc(v_a_1756_);
lean_dec_ref(v___x_1755_);
v_dummy_1757_ = lean_obj_once(&l_Lean_Meta_getInductiveUniverseAndParams___closed__0, &l_Lean_Meta_getInductiveUniverseAndParams___closed__0_once, _init_l_Lean_Meta_getInductiveUniverseAndParams___closed__0);
v_nargs_1758_ = l_Lean_Expr_getAppNumArgs(v_a_1756_);
lean_inc(v_nargs_1758_);
v___x_1759_ = lean_mk_array(v_nargs_1758_, v_dummy_1757_);
v___x_1760_ = lean_unsigned_to_nat(1u);
v___x_1761_ = lean_nat_sub(v_nargs_1758_, v___x_1760_);
lean_dec(v_nargs_1758_);
v___x_1762_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0___redArg(v_env_1746_, v_a_1753_, v_a_1756_, v___x_1759_, v___x_1761_, v_a_1740_);
lean_dec(v_a_1740_);
return v___x_1762_;
}
else
{
lean_object* v_a_1763_; lean_object* v___x_1765_; uint8_t v_isShared_1766_; uint8_t v_isSharedCheck_1770_; 
lean_dec(v_a_1753_);
lean_dec_ref(v_env_1746_);
lean_dec(v_a_1740_);
v_a_1763_ = lean_ctor_get(v___x_1755_, 0);
v_isSharedCheck_1770_ = !lean_is_exclusive(v___x_1755_);
if (v_isSharedCheck_1770_ == 0)
{
v___x_1765_ = v___x_1755_;
v_isShared_1766_ = v_isSharedCheck_1770_;
goto v_resetjp_1764_;
}
else
{
lean_inc(v_a_1763_);
lean_dec(v___x_1755_);
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
else
{
lean_object* v_a_1771_; lean_object* v___x_1773_; uint8_t v_isShared_1774_; uint8_t v_isSharedCheck_1778_; 
lean_dec_ref(v_env_1746_);
lean_dec(v_a_1740_);
lean_dec_ref(v_a_1739_);
lean_dec(v_a_1738_);
lean_dec_ref(v_a_1737_);
v_a_1771_ = lean_ctor_get(v___x_1752_, 0);
v_isSharedCheck_1778_ = !lean_is_exclusive(v___x_1752_);
if (v_isSharedCheck_1778_ == 0)
{
v___x_1773_ = v___x_1752_;
v_isShared_1774_ = v_isSharedCheck_1778_;
goto v_resetjp_1772_;
}
else
{
lean_inc(v_a_1771_);
lean_dec(v___x_1752_);
v___x_1773_ = lean_box(0);
v_isShared_1774_ = v_isSharedCheck_1778_;
goto v_resetjp_1772_;
}
v_resetjp_1772_:
{
lean_object* v___x_1776_; 
if (v_isShared_1774_ == 0)
{
v___x_1776_ = v___x_1773_;
goto v_reusejp_1775_;
}
else
{
lean_object* v_reuseFailAlloc_1777_; 
v_reuseFailAlloc_1777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1777_, 0, v_a_1771_);
v___x_1776_ = v_reuseFailAlloc_1777_;
goto v_reusejp_1775_;
}
v_reusejp_1775_:
{
return v___x_1776_;
}
}
}
}
}
v___jp_1743_:
{
lean_object* v___x_1744_; lean_object* v___x_1745_; 
v___x_1744_ = lean_box(0);
v___x_1745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1745_, 0, v___x_1744_);
return v___x_1745_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f___boxed(lean_object* v_majorFVarId_1779_, lean_object* v_a_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_){
_start:
{
lean_object* v_res_1785_; 
v_res_1785_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f(v_majorFVarId_1779_, v_a_1780_, v_a_1781_, v_a_1782_, v_a_1783_);
return v_res_1785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0(lean_object* v___x_1786_, lean_object* v_a_1787_, lean_object* v_x_1788_, lean_object* v_x_1789_, lean_object* v_x_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_){
_start:
{
lean_object* v___x_1796_; 
v___x_1796_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0___redArg(v___x_1786_, v_a_1787_, v_x_1788_, v_x_1789_, v_x_1790_, v___y_1794_);
return v___x_1796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0___boxed(lean_object* v___x_1797_, lean_object* v_a_1798_, lean_object* v_x_1799_, lean_object* v_x_1800_, lean_object* v_x_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_){
_start:
{
lean_object* v_res_1807_; 
v_res_1807_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0(v___x_1797_, v_a_1798_, v_x_1799_, v_x_1800_, v_x_1801_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_);
lean_dec(v___y_1805_);
lean_dec_ref(v___y_1804_);
lean_dec(v___y_1803_);
lean_dec_ref(v___y_1802_);
return v_res_1807_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0___redArg(lean_object* v___x_1808_, lean_object* v_i_1809_, lean_object* v_n_1810_, lean_object* v_i_1811_){
_start:
{
lean_object* v_zero_1812_; uint8_t v_isZero_1813_; 
v_zero_1812_ = lean_unsigned_to_nat(0u);
v_isZero_1813_ = lean_nat_dec_eq(v_i_1811_, v_zero_1812_);
if (v_isZero_1813_ == 1)
{
uint8_t v___x_1814_; 
lean_dec(v_i_1811_);
v___x_1814_ = 0;
return v___x_1814_;
}
else
{
lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; uint8_t v___x_1818_; 
v___x_1815_ = lean_nat_sub(v_n_1810_, v_i_1811_);
v___x_1816_ = lean_array_fget_borrowed(v___x_1808_, v_i_1809_);
v___x_1817_ = lean_array_fget_borrowed(v___x_1808_, v___x_1815_);
lean_dec(v___x_1815_);
v___x_1818_ = lean_expr_eqv(v___x_1816_, v___x_1817_);
if (v___x_1818_ == 0)
{
lean_object* v_one_1819_; lean_object* v_n_1820_; 
v_one_1819_ = lean_unsigned_to_nat(1u);
v_n_1820_ = lean_nat_sub(v_i_1811_, v_one_1819_);
lean_dec(v_i_1811_);
v_i_1811_ = v_n_1820_;
goto _start;
}
else
{
lean_dec(v_i_1811_);
return v___x_1818_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0___redArg___boxed(lean_object* v___x_1822_, lean_object* v_i_1823_, lean_object* v_n_1824_, lean_object* v_i_1825_){
_start:
{
uint8_t v_res_1826_; lean_object* v_r_1827_; 
v_res_1826_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0___redArg(v___x_1822_, v_i_1823_, v_n_1824_, v_i_1825_);
lean_dec(v_n_1824_);
lean_dec(v_i_1823_);
lean_dec_ref(v___x_1822_);
v_r_1827_ = lean_box(v_res_1826_);
return v_r_1827_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1___redArg(lean_object* v___x_1828_, lean_object* v_n_1829_, lean_object* v_i_1830_){
_start:
{
lean_object* v_zero_1831_; uint8_t v_isZero_1832_; 
v_zero_1831_ = lean_unsigned_to_nat(0u);
v_isZero_1832_ = lean_nat_dec_eq(v_i_1830_, v_zero_1831_);
if (v_isZero_1832_ == 1)
{
uint8_t v___x_1833_; 
lean_dec(v_i_1830_);
v___x_1833_ = 0;
return v___x_1833_;
}
else
{
lean_object* v___x_1834_; uint8_t v___x_1835_; 
v___x_1834_ = lean_nat_sub(v_n_1829_, v_i_1830_);
lean_inc(v___x_1834_);
v___x_1835_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0___redArg(v___x_1828_, v___x_1834_, v___x_1834_, v___x_1834_);
lean_dec(v___x_1834_);
if (v___x_1835_ == 0)
{
lean_object* v_one_1836_; lean_object* v_n_1837_; 
v_one_1836_ = lean_unsigned_to_nat(1u);
v_n_1837_ = lean_nat_sub(v_i_1830_, v_one_1836_);
lean_dec(v_i_1830_);
v_i_1830_ = v_n_1837_;
goto _start;
}
else
{
lean_dec(v_i_1830_);
return v___x_1835_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1___redArg___boxed(lean_object* v___x_1839_, lean_object* v_n_1840_, lean_object* v_i_1841_){
_start:
{
uint8_t v_res_1842_; lean_object* v_r_1843_; 
v_res_1842_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1___redArg(v___x_1839_, v_n_1840_, v_i_1841_);
lean_dec(v_n_1840_);
lean_dec_ref(v___x_1839_);
v_r_1843_ = lean_box(v_res_1842_);
return v_r_1843_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5(lean_object* v___x_1844_, lean_object* v_as_1845_, size_t v_i_1846_, size_t v_stop_1847_){
_start:
{
uint8_t v___x_1848_; 
v___x_1848_ = lean_usize_dec_eq(v_i_1846_, v_stop_1847_);
if (v___x_1848_ == 0)
{
uint8_t v___x_1849_; lean_object* v___x_1850_; uint8_t v___x_1851_; 
v___x_1849_ = 1;
v___x_1850_ = lean_array_uget_borrowed(v_as_1845_, v_i_1846_);
v___x_1851_ = l_Lean_Expr_isFVar(v___x_1850_);
if (v___x_1851_ == 0)
{
return v___x_1849_;
}
else
{
lean_object* v___x_1852_; uint8_t v___x_1853_; 
v___x_1852_ = lean_unsigned_to_nat(0u);
v___x_1853_ = lean_nat_dec_eq(v___x_1844_, v___x_1852_);
if (v___x_1853_ == 0)
{
size_t v___x_1854_; size_t v___x_1855_; 
v___x_1854_ = ((size_t)1ULL);
v___x_1855_ = lean_usize_add(v_i_1846_, v___x_1854_);
v_i_1846_ = v___x_1855_;
goto _start;
}
else
{
return v___x_1849_;
}
}
}
else
{
uint8_t v___x_1857_; 
v___x_1857_ = 0;
return v___x_1857_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5___boxed(lean_object* v___x_1858_, lean_object* v_as_1859_, lean_object* v_i_1860_, lean_object* v_stop_1861_){
_start:
{
size_t v_i_boxed_1862_; size_t v_stop_boxed_1863_; uint8_t v_res_1864_; lean_object* v_r_1865_; 
v_i_boxed_1862_ = lean_unbox_usize(v_i_1860_);
lean_dec(v_i_1860_);
v_stop_boxed_1863_ = lean_unbox_usize(v_stop_1861_);
lean_dec(v_stop_1861_);
v_res_1864_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5(v___x_1858_, v_as_1859_, v_i_boxed_1862_, v_stop_boxed_1863_);
lean_dec_ref(v_as_1859_);
lean_dec(v___x_1858_);
v_r_1865_ = lean_box(v_res_1864_);
return v_r_1865_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__2(lean_object* v_fvarId_1866_, uint8_t v___y_1867_, lean_object* v_as_1868_, size_t v_i_1869_, size_t v_stop_1870_){
_start:
{
uint8_t v___x_1871_; 
v___x_1871_ = lean_usize_dec_eq(v_i_1869_, v_stop_1870_);
if (v___x_1871_ == 0)
{
uint8_t v___x_1872_; uint8_t v___y_1874_; lean_object* v___x_1878_; lean_object* v___x_1879_; uint8_t v___x_1880_; 
v___x_1872_ = 1;
v___x_1878_ = lean_array_uget_borrowed(v_as_1868_, v_i_1869_);
v___x_1879_ = l_Lean_Expr_fvarId_x21(v___x_1878_);
v___x_1880_ = l_Lean_instBEqFVarId_beq(v___x_1879_, v_fvarId_1866_);
lean_dec(v___x_1879_);
if (v___x_1880_ == 0)
{
v___y_1874_ = v___y_1867_;
goto v___jp_1873_;
}
else
{
v___y_1874_ = v___x_1880_;
goto v___jp_1873_;
}
v___jp_1873_:
{
if (v___y_1874_ == 0)
{
size_t v___x_1875_; size_t v___x_1876_; 
v___x_1875_ = ((size_t)1ULL);
v___x_1876_ = lean_usize_add(v_i_1869_, v___x_1875_);
v_i_1869_ = v___x_1876_;
goto _start;
}
else
{
return v___x_1872_;
}
}
}
else
{
uint8_t v___x_1881_; 
v___x_1881_ = 0;
return v___x_1881_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__2___boxed(lean_object* v_fvarId_1882_, lean_object* v___y_1883_, lean_object* v_as_1884_, lean_object* v_i_1885_, lean_object* v_stop_1886_){
_start:
{
uint8_t v___y_9276__boxed_1887_; size_t v_i_boxed_1888_; size_t v_stop_boxed_1889_; uint8_t v_res_1890_; lean_object* v_r_1891_; 
v___y_9276__boxed_1887_ = lean_unbox(v___y_1883_);
v_i_boxed_1888_ = lean_unbox_usize(v_i_1885_);
lean_dec(v_i_1885_);
v_stop_boxed_1889_ = lean_unbox_usize(v_stop_1886_);
lean_dec(v_stop_1886_);
v_res_1890_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__2(v_fvarId_1882_, v___y_9276__boxed_1887_, v_as_1884_, v_i_boxed_1888_, v_stop_boxed_1889_);
lean_dec_ref(v_as_1884_);
lean_dec(v_fvarId_1882_);
v_r_1891_ = lean_box(v_res_1890_);
return v_r_1891_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___lam__1(lean_object* v___x_1892_, lean_object* v___x_1893_, uint8_t v___x_1894_, uint8_t v___y_1895_, lean_object* v___x_1896_, lean_object* v_fvarId_1897_){
_start:
{
lean_object* v___y_1899_; uint8_t v___x_1904_; 
v___x_1904_ = lean_nat_dec_lt(v___x_1892_, v___x_1893_);
if (v___x_1904_ == 0)
{
lean_dec(v___x_1893_);
return v___x_1894_;
}
else
{
lean_object* v___x_1905_; uint8_t v___x_1906_; 
v___x_1905_ = lean_array_get_size(v___x_1896_);
v___x_1906_ = lean_nat_dec_le(v___x_1893_, v___x_1905_);
if (v___x_1906_ == 0)
{
lean_dec(v___x_1893_);
v___y_1899_ = v___x_1905_;
goto v___jp_1898_;
}
else
{
v___y_1899_ = v___x_1893_;
goto v___jp_1898_;
}
}
v___jp_1898_:
{
uint8_t v___x_1900_; 
v___x_1900_ = lean_nat_dec_lt(v___x_1892_, v___y_1899_);
if (v___x_1900_ == 0)
{
lean_dec(v___y_1899_);
return v___x_1894_;
}
else
{
size_t v___x_1901_; size_t v___x_1902_; uint8_t v___x_1903_; 
v___x_1901_ = ((size_t)0ULL);
v___x_1902_ = lean_usize_of_nat(v___y_1899_);
lean_dec(v___y_1899_);
v___x_1903_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__2(v_fvarId_1897_, v___y_1895_, v___x_1896_, v___x_1901_, v___x_1902_);
if (v___x_1903_ == 0)
{
return v___x_1894_;
}
else
{
return v___y_1895_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___lam__1___boxed(lean_object* v___x_1907_, lean_object* v___x_1908_, lean_object* v___x_1909_, lean_object* v___y_1910_, lean_object* v___x_1911_, lean_object* v_fvarId_1912_){
_start:
{
uint8_t v___x_9303__boxed_1913_; uint8_t v___y_9304__boxed_1914_; uint8_t v_res_1915_; lean_object* v_r_1916_; 
v___x_9303__boxed_1913_ = lean_unbox(v___x_1909_);
v___y_9304__boxed_1914_ = lean_unbox(v___y_1910_);
v_res_1915_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___lam__1(v___x_1907_, v___x_1908_, v___x_9303__boxed_1913_, v___y_9304__boxed_1914_, v___x_1911_, v_fvarId_1912_);
lean_dec(v_fvarId_1912_);
lean_dec_ref(v___x_1911_);
lean_dec(v___x_1907_);
v_r_1916_ = lean_box(v_res_1915_);
return v_r_1916_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__3(lean_object* v___x_1917_, lean_object* v_as_1918_, size_t v_i_1919_, size_t v_stop_1920_){
_start:
{
uint8_t v___x_1921_; 
v___x_1921_ = lean_usize_dec_eq(v_i_1919_, v_stop_1920_);
if (v___x_1921_ == 0)
{
lean_object* v___x_1922_; lean_object* v___x_1923_; uint8_t v___x_1924_; 
v___x_1922_ = lean_array_uget_borrowed(v_as_1918_, v_i_1919_);
v___x_1923_ = l_Lean_Expr_fvarId_x21(v___x_1922_);
v___x_1924_ = l_Lean_instBEqFVarId_beq(v___x_1917_, v___x_1923_);
lean_dec(v___x_1923_);
if (v___x_1924_ == 0)
{
size_t v___x_1925_; size_t v___x_1926_; 
v___x_1925_ = ((size_t)1ULL);
v___x_1926_ = lean_usize_add(v_i_1919_, v___x_1925_);
v_i_1919_ = v___x_1926_;
goto _start;
}
else
{
return v___x_1924_;
}
}
else
{
uint8_t v___x_1928_; 
v___x_1928_ = 0;
return v___x_1928_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__3___boxed(lean_object* v___x_1929_, lean_object* v_as_1930_, lean_object* v_i_1931_, lean_object* v_stop_1932_){
_start:
{
size_t v_i_boxed_1933_; size_t v_stop_boxed_1934_; uint8_t v_res_1935_; lean_object* v_r_1936_; 
v_i_boxed_1933_ = lean_unbox_usize(v_i_1931_);
lean_dec(v_i_1931_);
v_stop_boxed_1934_ = lean_unbox_usize(v_stop_1932_);
lean_dec(v_stop_1932_);
v_res_1935_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__3(v___x_1929_, v_as_1930_, v_i_boxed_1933_, v_stop_boxed_1934_);
lean_dec_ref(v_as_1930_);
lean_dec(v___x_1929_);
v_r_1936_ = lean_box(v_res_1935_);
return v_r_1936_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___lam__0(uint8_t v___y_1937_, lean_object* v_x_1938_){
_start:
{
return v___y_1937_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___lam__0___boxed(lean_object* v___y_1939_, lean_object* v_x_1940_){
_start:
{
uint8_t v___y_9353__boxed_1941_; uint8_t v_res_1942_; lean_object* v_r_1943_; 
v___y_9353__boxed_1941_ = lean_unbox(v___y_1939_);
v_res_1942_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___lam__0(v___y_9353__boxed_1941_, v_x_1940_);
lean_dec(v_x_1940_);
v_r_1943_ = lean_box(v_res_1942_);
return v_r_1943_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; 
v___x_1944_ = lean_box(0);
v___x_1945_ = lean_unsigned_to_nat(16u);
v___x_1946_ = lean_mk_array(v___x_1945_, v___x_1944_);
return v___x_1946_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; 
v___x_1947_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__0);
v___x_1948_ = lean_unsigned_to_nat(0u);
v___x_1949_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1949_, 0, v___x_1948_);
lean_ctor_set(v___x_1949_, 1, v___x_1947_);
return v___x_1949_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg(uint8_t v___x_1950_, lean_object* v___x_1951_, lean_object* v___x_1952_, lean_object* v_ctx_1953_, lean_object* v_as_1954_, size_t v_i_1955_, size_t v_stop_1956_, lean_object* v___y_1957_){
_start:
{
uint8_t v___x_1959_; 
v___x_1959_ = lean_usize_dec_eq(v_i_1955_, v_stop_1956_);
if (v___x_1959_ == 0)
{
uint8_t v___x_1960_; uint8_t v_a_1962_; uint8_t v_a_1969_; uint8_t v_fst_1973_; lean_object* v_mctx_1974_; lean_object* v___y_1990_; uint8_t v_fst_1996_; lean_object* v_snd_1997_; lean_object* v___y_2014_; lean_object* v___y_2019_; lean_object* v___y_2020_; lean_object* v___y_2021_; uint8_t v_fst_2022_; lean_object* v_snd_2023_; lean_object* v___y_2029_; lean_object* v___y_2030_; lean_object* v___y_2031_; lean_object* v___y_2032_; uint8_t v_fst_2037_; lean_object* v_mctx_2038_; lean_object* v___y_2054_; lean_object* v___x_2059_; 
v___x_1960_ = 1;
v___x_2059_ = lean_array_uget_borrowed(v_as_1954_, v_i_1955_);
if (lean_obj_tag(v___x_2059_) == 0)
{
v_a_1962_ = v___x_1950_;
goto v___jp_1961_;
}
else
{
lean_object* v_val_2060_; lean_object* v_majorDecl_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; uint8_t v___x_2064_; 
v_val_2060_ = lean_ctor_get(v___x_2059_, 0);
v_majorDecl_2061_ = lean_ctor_get(v_ctx_1953_, 2);
v___x_2062_ = l_Lean_LocalDecl_fvarId(v_val_2060_);
v___x_2063_ = l_Lean_LocalDecl_fvarId(v_majorDecl_2061_);
v___x_2064_ = l_Lean_instBEqFVarId_beq(v___x_2062_, v___x_2063_);
lean_dec(v___x_2063_);
if (v___x_2064_ == 0)
{
lean_object* v___x_2065_; uint8_t v___y_2067_; lean_object* v___y_2103_; uint8_t v___x_2108_; 
v___x_2065_ = lean_unsigned_to_nat(0u);
v___x_2108_ = lean_nat_dec_lt(v___x_2065_, v___x_1952_);
if (v___x_2108_ == 0)
{
lean_dec(v___x_2062_);
v___y_2067_ = v___x_2064_;
goto v___jp_2066_;
}
else
{
lean_object* v___x_2109_; uint8_t v___x_2110_; 
v___x_2109_ = lean_array_get_size(v___x_1951_);
v___x_2110_ = lean_nat_dec_le(v___x_1952_, v___x_2109_);
if (v___x_2110_ == 0)
{
v___y_2103_ = v___x_2109_;
goto v___jp_2102_;
}
else
{
lean_inc(v___x_1952_);
v___y_2103_ = v___x_1952_;
goto v___jp_2102_;
}
}
v___jp_2066_:
{
if (v___y_2067_ == 0)
{
lean_object* v___x_2068_; lean_object* v___f_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___f_2072_; 
v___x_2068_ = lean_box(v___y_2067_);
v___f_2069_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2069_, 0, v___x_2068_);
v___x_2070_ = lean_box(v___x_1960_);
v___x_2071_ = lean_box(v___y_2067_);
lean_inc_ref(v___x_1951_);
lean_inc(v___x_1952_);
v___f_2072_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_2072_, 0, v___x_2065_);
lean_closure_set(v___f_2072_, 1, v___x_1952_);
lean_closure_set(v___f_2072_, 2, v___x_2070_);
lean_closure_set(v___f_2072_, 3, v___x_2071_);
lean_closure_set(v___f_2072_, 4, v___x_1951_);
if (lean_obj_tag(v_val_2060_) == 0)
{
lean_object* v_type_2073_; lean_object* v___x_2074_; lean_object* v_mctx_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; uint8_t v___x_2078_; 
v_type_2073_ = lean_ctor_get(v_val_2060_, 3);
v___x_2074_ = lean_st_ref_get(v___y_1957_);
v_mctx_2075_ = lean_ctor_get(v___x_2074_, 0);
lean_inc_ref(v_mctx_2075_);
lean_dec(v___x_2074_);
v___x_2076_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1);
lean_inc_ref(v_mctx_2075_);
v___x_2077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2077_, 0, v___x_2076_);
lean_ctor_set(v___x_2077_, 1, v_mctx_2075_);
v___x_2078_ = l_Lean_Expr_hasFVar(v_type_2073_);
if (v___x_2078_ == 0)
{
uint8_t v___x_2079_; 
v___x_2079_ = l_Lean_Expr_hasMVar(v_type_2073_);
if (v___x_2079_ == 0)
{
lean_dec_ref(v___x_2077_);
lean_dec_ref(v___f_2072_);
lean_dec_ref(v___f_2069_);
v_fst_1973_ = v___x_2079_;
v_mctx_1974_ = v_mctx_2075_;
goto v___jp_1972_;
}
else
{
lean_object* v___x_2080_; 
lean_dec_ref(v_mctx_2075_);
lean_inc_ref(v_type_2073_);
v___x_2080_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_2072_, v___f_2069_, v_type_2073_, v___x_2077_);
v___y_1990_ = v___x_2080_;
goto v___jp_1989_;
}
}
else
{
lean_object* v___x_2081_; 
lean_dec_ref(v_mctx_2075_);
lean_inc_ref(v_type_2073_);
v___x_2081_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_2072_, v___f_2069_, v_type_2073_, v___x_2077_);
v___y_1990_ = v___x_2081_;
goto v___jp_1989_;
}
}
else
{
uint8_t v_nondep_2082_; 
v_nondep_2082_ = lean_ctor_get_uint8(v_val_2060_, sizeof(void*)*5);
if (v_nondep_2082_ == 0)
{
lean_object* v_type_2083_; lean_object* v_value_2084_; lean_object* v___x_2085_; lean_object* v_mctx_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; uint8_t v___x_2089_; 
v_type_2083_ = lean_ctor_get(v_val_2060_, 3);
v_value_2084_ = lean_ctor_get(v_val_2060_, 4);
v___x_2085_ = lean_st_ref_get(v___y_1957_);
v_mctx_2086_ = lean_ctor_get(v___x_2085_, 0);
lean_inc_ref(v_mctx_2086_);
lean_dec(v___x_2085_);
v___x_2087_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1);
v___x_2088_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2088_, 0, v___x_2087_);
lean_ctor_set(v___x_2088_, 1, v_mctx_2086_);
v___x_2089_ = l_Lean_Expr_hasFVar(v_type_2083_);
if (v___x_2089_ == 0)
{
uint8_t v___x_2090_; 
v___x_2090_ = l_Lean_Expr_hasMVar(v_type_2083_);
if (v___x_2090_ == 0)
{
lean_inc_ref(v_value_2084_);
v___y_2019_ = v___f_2072_;
v___y_2020_ = v___f_2069_;
v___y_2021_ = v_value_2084_;
v_fst_2022_ = v___x_2090_;
v_snd_2023_ = v___x_2088_;
goto v___jp_2018_;
}
else
{
lean_object* v___x_2091_; 
lean_inc_ref(v_type_2083_);
lean_inc_ref(v___f_2069_);
lean_inc_ref(v___f_2072_);
v___x_2091_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_2072_, v___f_2069_, v_type_2083_, v___x_2088_);
lean_inc_ref(v_value_2084_);
v___y_2029_ = v___f_2072_;
v___y_2030_ = v___f_2069_;
v___y_2031_ = v_value_2084_;
v___y_2032_ = v___x_2091_;
goto v___jp_2028_;
}
}
else
{
lean_object* v___x_2092_; 
lean_inc_ref(v_type_2083_);
lean_inc_ref(v___f_2069_);
lean_inc_ref(v___f_2072_);
v___x_2092_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_2072_, v___f_2069_, v_type_2083_, v___x_2088_);
lean_inc_ref(v_value_2084_);
v___y_2029_ = v___f_2072_;
v___y_2030_ = v___f_2069_;
v___y_2031_ = v_value_2084_;
v___y_2032_ = v___x_2092_;
goto v___jp_2028_;
}
}
else
{
lean_object* v_type_2093_; lean_object* v___x_2094_; lean_object* v_mctx_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; uint8_t v___x_2098_; 
v_type_2093_ = lean_ctor_get(v_val_2060_, 3);
v___x_2094_ = lean_st_ref_get(v___y_1957_);
v_mctx_2095_ = lean_ctor_get(v___x_2094_, 0);
lean_inc_ref(v_mctx_2095_);
lean_dec(v___x_2094_);
v___x_2096_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1);
lean_inc_ref(v_mctx_2095_);
v___x_2097_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2097_, 0, v___x_2096_);
lean_ctor_set(v___x_2097_, 1, v_mctx_2095_);
v___x_2098_ = l_Lean_Expr_hasFVar(v_type_2093_);
if (v___x_2098_ == 0)
{
uint8_t v___x_2099_; 
v___x_2099_ = l_Lean_Expr_hasMVar(v_type_2093_);
if (v___x_2099_ == 0)
{
lean_dec_ref(v___x_2097_);
lean_dec_ref(v___f_2072_);
lean_dec_ref(v___f_2069_);
v_fst_2037_ = v___x_2099_;
v_mctx_2038_ = v_mctx_2095_;
goto v___jp_2036_;
}
else
{
lean_object* v___x_2100_; 
lean_dec_ref(v_mctx_2095_);
lean_inc_ref(v_type_2093_);
v___x_2100_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_2072_, v___f_2069_, v_type_2093_, v___x_2097_);
v___y_2054_ = v___x_2100_;
goto v___jp_2053_;
}
}
else
{
lean_object* v___x_2101_; 
lean_dec_ref(v_mctx_2095_);
lean_inc_ref(v_type_2093_);
v___x_2101_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_2072_, v___f_2069_, v_type_2093_, v___x_2097_);
v___y_2054_ = v___x_2101_;
goto v___jp_2053_;
}
}
}
}
else
{
v_a_1962_ = v___x_1950_;
goto v___jp_1961_;
}
}
v___jp_2102_:
{
uint8_t v___x_2104_; 
v___x_2104_ = lean_nat_dec_lt(v___x_2065_, v___y_2103_);
if (v___x_2104_ == 0)
{
lean_dec(v___y_2103_);
lean_dec(v___x_2062_);
v___y_2067_ = v___x_2064_;
goto v___jp_2066_;
}
else
{
size_t v___x_2105_; size_t v___x_2106_; uint8_t v___x_2107_; 
v___x_2105_ = ((size_t)0ULL);
v___x_2106_ = lean_usize_of_nat(v___y_2103_);
lean_dec(v___y_2103_);
v___x_2107_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__3(v___x_2062_, v___x_1951_, v___x_2105_, v___x_2106_);
lean_dec(v___x_2062_);
v___y_2067_ = v___x_2107_;
goto v___jp_2066_;
}
}
}
else
{
lean_dec(v___x_2062_);
v_a_1969_ = v___x_2064_;
goto v___jp_1968_;
}
}
v___jp_1961_:
{
if (v_a_1962_ == 0)
{
size_t v___x_1963_; size_t v___x_1964_; 
v___x_1963_ = ((size_t)1ULL);
v___x_1964_ = lean_usize_add(v_i_1955_, v___x_1963_);
v_i_1955_ = v___x_1964_;
goto _start;
}
else
{
lean_object* v___x_1966_; lean_object* v___x_1967_; 
lean_dec(v___x_1952_);
lean_dec_ref(v___x_1951_);
v___x_1966_ = lean_box(v___x_1960_);
v___x_1967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1967_, 0, v___x_1966_);
return v___x_1967_;
}
}
v___jp_1968_:
{
if (v_a_1969_ == 0)
{
lean_object* v___x_1970_; lean_object* v___x_1971_; 
lean_dec(v___x_1952_);
lean_dec_ref(v___x_1951_);
v___x_1970_ = lean_box(v___x_1960_);
v___x_1971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1971_, 0, v___x_1970_);
return v___x_1971_;
}
else
{
v_a_1962_ = v___x_1950_;
goto v___jp_1961_;
}
}
v___jp_1972_:
{
lean_object* v___x_1975_; lean_object* v_cache_1976_; lean_object* v_zetaDeltaFVarIds_1977_; lean_object* v_postponed_1978_; lean_object* v_diag_1979_; lean_object* v___x_1981_; uint8_t v_isShared_1982_; uint8_t v_isSharedCheck_1987_; 
v___x_1975_ = lean_st_ref_take(v___y_1957_);
v_cache_1976_ = lean_ctor_get(v___x_1975_, 1);
v_zetaDeltaFVarIds_1977_ = lean_ctor_get(v___x_1975_, 2);
v_postponed_1978_ = lean_ctor_get(v___x_1975_, 3);
v_diag_1979_ = lean_ctor_get(v___x_1975_, 4);
v_isSharedCheck_1987_ = !lean_is_exclusive(v___x_1975_);
if (v_isSharedCheck_1987_ == 0)
{
lean_object* v_unused_1988_; 
v_unused_1988_ = lean_ctor_get(v___x_1975_, 0);
lean_dec(v_unused_1988_);
v___x_1981_ = v___x_1975_;
v_isShared_1982_ = v_isSharedCheck_1987_;
goto v_resetjp_1980_;
}
else
{
lean_inc(v_diag_1979_);
lean_inc(v_postponed_1978_);
lean_inc(v_zetaDeltaFVarIds_1977_);
lean_inc(v_cache_1976_);
lean_dec(v___x_1975_);
v___x_1981_ = lean_box(0);
v_isShared_1982_ = v_isSharedCheck_1987_;
goto v_resetjp_1980_;
}
v_resetjp_1980_:
{
lean_object* v___x_1984_; 
if (v_isShared_1982_ == 0)
{
lean_ctor_set(v___x_1981_, 0, v_mctx_1974_);
v___x_1984_ = v___x_1981_;
goto v_reusejp_1983_;
}
else
{
lean_object* v_reuseFailAlloc_1986_; 
v_reuseFailAlloc_1986_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1986_, 0, v_mctx_1974_);
lean_ctor_set(v_reuseFailAlloc_1986_, 1, v_cache_1976_);
lean_ctor_set(v_reuseFailAlloc_1986_, 2, v_zetaDeltaFVarIds_1977_);
lean_ctor_set(v_reuseFailAlloc_1986_, 3, v_postponed_1978_);
lean_ctor_set(v_reuseFailAlloc_1986_, 4, v_diag_1979_);
v___x_1984_ = v_reuseFailAlloc_1986_;
goto v_reusejp_1983_;
}
v_reusejp_1983_:
{
lean_object* v___x_1985_; 
v___x_1985_ = lean_st_ref_set(v___y_1957_, v___x_1984_);
v_a_1969_ = v_fst_1973_;
goto v___jp_1968_;
}
}
}
v___jp_1989_:
{
lean_object* v_snd_1991_; lean_object* v_fst_1992_; lean_object* v_mctx_1993_; uint8_t v___x_1994_; 
v_snd_1991_ = lean_ctor_get(v___y_1990_, 1);
lean_inc(v_snd_1991_);
v_fst_1992_ = lean_ctor_get(v___y_1990_, 0);
lean_inc(v_fst_1992_);
lean_dec_ref(v___y_1990_);
v_mctx_1993_ = lean_ctor_get(v_snd_1991_, 1);
lean_inc_ref(v_mctx_1993_);
lean_dec(v_snd_1991_);
v___x_1994_ = lean_unbox(v_fst_1992_);
lean_dec(v_fst_1992_);
v_fst_1973_ = v___x_1994_;
v_mctx_1974_ = v_mctx_1993_;
goto v___jp_1972_;
}
v___jp_1995_:
{
lean_object* v_mctx_1998_; lean_object* v___x_1999_; lean_object* v_cache_2000_; lean_object* v_zetaDeltaFVarIds_2001_; lean_object* v_postponed_2002_; lean_object* v_diag_2003_; lean_object* v___x_2005_; uint8_t v_isShared_2006_; uint8_t v_isSharedCheck_2011_; 
v_mctx_1998_ = lean_ctor_get(v_snd_1997_, 1);
lean_inc_ref(v_mctx_1998_);
lean_dec_ref(v_snd_1997_);
v___x_1999_ = lean_st_ref_take(v___y_1957_);
v_cache_2000_ = lean_ctor_get(v___x_1999_, 1);
v_zetaDeltaFVarIds_2001_ = lean_ctor_get(v___x_1999_, 2);
v_postponed_2002_ = lean_ctor_get(v___x_1999_, 3);
v_diag_2003_ = lean_ctor_get(v___x_1999_, 4);
v_isSharedCheck_2011_ = !lean_is_exclusive(v___x_1999_);
if (v_isSharedCheck_2011_ == 0)
{
lean_object* v_unused_2012_; 
v_unused_2012_ = lean_ctor_get(v___x_1999_, 0);
lean_dec(v_unused_2012_);
v___x_2005_ = v___x_1999_;
v_isShared_2006_ = v_isSharedCheck_2011_;
goto v_resetjp_2004_;
}
else
{
lean_inc(v_diag_2003_);
lean_inc(v_postponed_2002_);
lean_inc(v_zetaDeltaFVarIds_2001_);
lean_inc(v_cache_2000_);
lean_dec(v___x_1999_);
v___x_2005_ = lean_box(0);
v_isShared_2006_ = v_isSharedCheck_2011_;
goto v_resetjp_2004_;
}
v_resetjp_2004_:
{
lean_object* v___x_2008_; 
if (v_isShared_2006_ == 0)
{
lean_ctor_set(v___x_2005_, 0, v_mctx_1998_);
v___x_2008_ = v___x_2005_;
goto v_reusejp_2007_;
}
else
{
lean_object* v_reuseFailAlloc_2010_; 
v_reuseFailAlloc_2010_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2010_, 0, v_mctx_1998_);
lean_ctor_set(v_reuseFailAlloc_2010_, 1, v_cache_2000_);
lean_ctor_set(v_reuseFailAlloc_2010_, 2, v_zetaDeltaFVarIds_2001_);
lean_ctor_set(v_reuseFailAlloc_2010_, 3, v_postponed_2002_);
lean_ctor_set(v_reuseFailAlloc_2010_, 4, v_diag_2003_);
v___x_2008_ = v_reuseFailAlloc_2010_;
goto v_reusejp_2007_;
}
v_reusejp_2007_:
{
lean_object* v___x_2009_; 
v___x_2009_ = lean_st_ref_set(v___y_1957_, v___x_2008_);
v_a_1969_ = v_fst_1996_;
goto v___jp_1968_;
}
}
}
v___jp_2013_:
{
lean_object* v_fst_2015_; lean_object* v_snd_2016_; uint8_t v___x_2017_; 
v_fst_2015_ = lean_ctor_get(v___y_2014_, 0);
lean_inc(v_fst_2015_);
v_snd_2016_ = lean_ctor_get(v___y_2014_, 1);
lean_inc(v_snd_2016_);
lean_dec_ref(v___y_2014_);
v___x_2017_ = lean_unbox(v_fst_2015_);
lean_dec(v_fst_2015_);
v_fst_1996_ = v___x_2017_;
v_snd_1997_ = v_snd_2016_;
goto v___jp_1995_;
}
v___jp_2018_:
{
if (v_fst_2022_ == 0)
{
uint8_t v___x_2024_; 
v___x_2024_ = l_Lean_Expr_hasFVar(v___y_2021_);
if (v___x_2024_ == 0)
{
uint8_t v___x_2025_; 
v___x_2025_ = l_Lean_Expr_hasMVar(v___y_2021_);
if (v___x_2025_ == 0)
{
lean_dec_ref(v___y_2021_);
lean_dec_ref(v___y_2020_);
lean_dec_ref(v___y_2019_);
v_fst_1996_ = v___x_2025_;
v_snd_1997_ = v_snd_2023_;
goto v___jp_1995_;
}
else
{
lean_object* v___x_2026_; 
v___x_2026_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___y_2019_, v___y_2020_, v___y_2021_, v_snd_2023_);
v___y_2014_ = v___x_2026_;
goto v___jp_2013_;
}
}
else
{
lean_object* v___x_2027_; 
v___x_2027_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___y_2019_, v___y_2020_, v___y_2021_, v_snd_2023_);
v___y_2014_ = v___x_2027_;
goto v___jp_2013_;
}
}
else
{
lean_dec_ref(v___y_2021_);
lean_dec_ref(v___y_2020_);
lean_dec_ref(v___y_2019_);
v_fst_1996_ = v_fst_2022_;
v_snd_1997_ = v_snd_2023_;
goto v___jp_1995_;
}
}
v___jp_2028_:
{
lean_object* v_fst_2033_; lean_object* v_snd_2034_; uint8_t v___x_2035_; 
v_fst_2033_ = lean_ctor_get(v___y_2032_, 0);
lean_inc(v_fst_2033_);
v_snd_2034_ = lean_ctor_get(v___y_2032_, 1);
lean_inc(v_snd_2034_);
lean_dec_ref(v___y_2032_);
v___x_2035_ = lean_unbox(v_fst_2033_);
lean_dec(v_fst_2033_);
v___y_2019_ = v___y_2029_;
v___y_2020_ = v___y_2030_;
v___y_2021_ = v___y_2031_;
v_fst_2022_ = v___x_2035_;
v_snd_2023_ = v_snd_2034_;
goto v___jp_2018_;
}
v___jp_2036_:
{
lean_object* v___x_2039_; lean_object* v_cache_2040_; lean_object* v_zetaDeltaFVarIds_2041_; lean_object* v_postponed_2042_; lean_object* v_diag_2043_; lean_object* v___x_2045_; uint8_t v_isShared_2046_; uint8_t v_isSharedCheck_2051_; 
v___x_2039_ = lean_st_ref_take(v___y_1957_);
v_cache_2040_ = lean_ctor_get(v___x_2039_, 1);
v_zetaDeltaFVarIds_2041_ = lean_ctor_get(v___x_2039_, 2);
v_postponed_2042_ = lean_ctor_get(v___x_2039_, 3);
v_diag_2043_ = lean_ctor_get(v___x_2039_, 4);
v_isSharedCheck_2051_ = !lean_is_exclusive(v___x_2039_);
if (v_isSharedCheck_2051_ == 0)
{
lean_object* v_unused_2052_; 
v_unused_2052_ = lean_ctor_get(v___x_2039_, 0);
lean_dec(v_unused_2052_);
v___x_2045_ = v___x_2039_;
v_isShared_2046_ = v_isSharedCheck_2051_;
goto v_resetjp_2044_;
}
else
{
lean_inc(v_diag_2043_);
lean_inc(v_postponed_2042_);
lean_inc(v_zetaDeltaFVarIds_2041_);
lean_inc(v_cache_2040_);
lean_dec(v___x_2039_);
v___x_2045_ = lean_box(0);
v_isShared_2046_ = v_isSharedCheck_2051_;
goto v_resetjp_2044_;
}
v_resetjp_2044_:
{
lean_object* v___x_2048_; 
if (v_isShared_2046_ == 0)
{
lean_ctor_set(v___x_2045_, 0, v_mctx_2038_);
v___x_2048_ = v___x_2045_;
goto v_reusejp_2047_;
}
else
{
lean_object* v_reuseFailAlloc_2050_; 
v_reuseFailAlloc_2050_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2050_, 0, v_mctx_2038_);
lean_ctor_set(v_reuseFailAlloc_2050_, 1, v_cache_2040_);
lean_ctor_set(v_reuseFailAlloc_2050_, 2, v_zetaDeltaFVarIds_2041_);
lean_ctor_set(v_reuseFailAlloc_2050_, 3, v_postponed_2042_);
lean_ctor_set(v_reuseFailAlloc_2050_, 4, v_diag_2043_);
v___x_2048_ = v_reuseFailAlloc_2050_;
goto v_reusejp_2047_;
}
v_reusejp_2047_:
{
lean_object* v___x_2049_; 
v___x_2049_ = lean_st_ref_set(v___y_1957_, v___x_2048_);
v_a_1969_ = v_fst_2037_;
goto v___jp_1968_;
}
}
}
v___jp_2053_:
{
lean_object* v_snd_2055_; lean_object* v_fst_2056_; lean_object* v_mctx_2057_; uint8_t v___x_2058_; 
v_snd_2055_ = lean_ctor_get(v___y_2054_, 1);
lean_inc(v_snd_2055_);
v_fst_2056_ = lean_ctor_get(v___y_2054_, 0);
lean_inc(v_fst_2056_);
lean_dec_ref(v___y_2054_);
v_mctx_2057_ = lean_ctor_get(v_snd_2055_, 1);
lean_inc_ref(v_mctx_2057_);
lean_dec(v_snd_2055_);
v___x_2058_ = lean_unbox(v_fst_2056_);
lean_dec(v_fst_2056_);
v_fst_2037_ = v___x_2058_;
v_mctx_2038_ = v_mctx_2057_;
goto v___jp_2036_;
}
}
else
{
uint8_t v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; 
lean_dec(v___x_1952_);
lean_dec_ref(v___x_1951_);
v___x_2111_ = 0;
v___x_2112_ = lean_box(v___x_2111_);
v___x_2113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2113_, 0, v___x_2112_);
return v___x_2113_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___boxed(lean_object* v___x_2114_, lean_object* v___x_2115_, lean_object* v___x_2116_, lean_object* v_ctx_2117_, lean_object* v_as_2118_, lean_object* v_i_2119_, lean_object* v_stop_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_){
_start:
{
uint8_t v___x_9383__boxed_2123_; size_t v_i_boxed_2124_; size_t v_stop_boxed_2125_; lean_object* v_res_2126_; 
v___x_9383__boxed_2123_ = lean_unbox(v___x_2114_);
v_i_boxed_2124_ = lean_unbox_usize(v_i_2119_);
lean_dec(v_i_2119_);
v_stop_boxed_2125_ = lean_unbox_usize(v_stop_2120_);
lean_dec(v_stop_2120_);
v_res_2126_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg(v___x_9383__boxed_2123_, v___x_2115_, v___x_2116_, v_ctx_2117_, v_as_2118_, v_i_boxed_2124_, v_stop_boxed_2125_, v___y_2121_);
lean_dec(v___y_2121_);
lean_dec_ref(v_as_2118_);
lean_dec_ref(v_ctx_2117_);
return v_res_2126_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4(uint8_t v___x_2127_, lean_object* v___x_2128_, lean_object* v___x_2129_, lean_object* v_ctx_2130_, lean_object* v_x_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_){
_start:
{
if (lean_obj_tag(v_x_2131_) == 0)
{
lean_object* v_cs_2137_; lean_object* v___x_2139_; uint8_t v_isShared_2140_; uint8_t v_isSharedCheck_2155_; 
v_cs_2137_ = lean_ctor_get(v_x_2131_, 0);
v_isSharedCheck_2155_ = !lean_is_exclusive(v_x_2131_);
if (v_isSharedCheck_2155_ == 0)
{
v___x_2139_ = v_x_2131_;
v_isShared_2140_ = v_isSharedCheck_2155_;
goto v_resetjp_2138_;
}
else
{
lean_inc(v_cs_2137_);
lean_dec(v_x_2131_);
v___x_2139_ = lean_box(0);
v_isShared_2140_ = v_isSharedCheck_2155_;
goto v_resetjp_2138_;
}
v_resetjp_2138_:
{
lean_object* v___x_2141_; lean_object* v___x_2142_; uint8_t v___x_2143_; 
v___x_2141_ = lean_unsigned_to_nat(0u);
v___x_2142_ = lean_array_get_size(v_cs_2137_);
v___x_2143_ = lean_nat_dec_lt(v___x_2141_, v___x_2142_);
if (v___x_2143_ == 0)
{
lean_object* v___x_2144_; lean_object* v___x_2146_; 
lean_dec_ref(v_cs_2137_);
lean_dec(v___x_2129_);
lean_dec_ref(v___x_2128_);
v___x_2144_ = lean_box(v___x_2143_);
if (v_isShared_2140_ == 0)
{
lean_ctor_set(v___x_2139_, 0, v___x_2144_);
v___x_2146_ = v___x_2139_;
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
if (v___x_2143_ == 0)
{
lean_object* v___x_2148_; lean_object* v___x_2150_; 
lean_dec_ref(v_cs_2137_);
lean_dec(v___x_2129_);
lean_dec_ref(v___x_2128_);
v___x_2148_ = lean_box(v___x_2143_);
if (v_isShared_2140_ == 0)
{
lean_ctor_set(v___x_2139_, 0, v___x_2148_);
v___x_2150_ = v___x_2139_;
goto v_reusejp_2149_;
}
else
{
lean_object* v_reuseFailAlloc_2151_; 
v_reuseFailAlloc_2151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2151_, 0, v___x_2148_);
v___x_2150_ = v_reuseFailAlloc_2151_;
goto v_reusejp_2149_;
}
v_reusejp_2149_:
{
return v___x_2150_;
}
}
else
{
size_t v___x_2152_; size_t v___x_2153_; lean_object* v___x_2154_; 
lean_del_object(v___x_2139_);
v___x_2152_ = ((size_t)0ULL);
v___x_2153_ = lean_usize_of_nat(v___x_2142_);
v___x_2154_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4_spec__5(v___x_2127_, v___x_2128_, v___x_2129_, v_ctx_2130_, v_cs_2137_, v___x_2152_, v___x_2153_, v___y_2132_, v___y_2133_, v___y_2134_, v___y_2135_);
lean_dec_ref(v_cs_2137_);
return v___x_2154_;
}
}
}
}
else
{
lean_object* v_vs_2156_; lean_object* v___x_2158_; uint8_t v_isShared_2159_; uint8_t v_isSharedCheck_2174_; 
v_vs_2156_ = lean_ctor_get(v_x_2131_, 0);
v_isSharedCheck_2174_ = !lean_is_exclusive(v_x_2131_);
if (v_isSharedCheck_2174_ == 0)
{
v___x_2158_ = v_x_2131_;
v_isShared_2159_ = v_isSharedCheck_2174_;
goto v_resetjp_2157_;
}
else
{
lean_inc(v_vs_2156_);
lean_dec(v_x_2131_);
v___x_2158_ = lean_box(0);
v_isShared_2159_ = v_isSharedCheck_2174_;
goto v_resetjp_2157_;
}
v_resetjp_2157_:
{
lean_object* v___x_2160_; lean_object* v___x_2161_; uint8_t v___x_2162_; 
v___x_2160_ = lean_unsigned_to_nat(0u);
v___x_2161_ = lean_array_get_size(v_vs_2156_);
v___x_2162_ = lean_nat_dec_lt(v___x_2160_, v___x_2161_);
if (v___x_2162_ == 0)
{
lean_object* v___x_2163_; lean_object* v___x_2165_; 
lean_dec_ref(v_vs_2156_);
lean_dec(v___x_2129_);
lean_dec_ref(v___x_2128_);
v___x_2163_ = lean_box(v___x_2162_);
if (v_isShared_2159_ == 0)
{
lean_ctor_set_tag(v___x_2158_, 0);
lean_ctor_set(v___x_2158_, 0, v___x_2163_);
v___x_2165_ = v___x_2158_;
goto v_reusejp_2164_;
}
else
{
lean_object* v_reuseFailAlloc_2166_; 
v_reuseFailAlloc_2166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2166_, 0, v___x_2163_);
v___x_2165_ = v_reuseFailAlloc_2166_;
goto v_reusejp_2164_;
}
v_reusejp_2164_:
{
return v___x_2165_;
}
}
else
{
if (v___x_2162_ == 0)
{
lean_object* v___x_2167_; lean_object* v___x_2169_; 
lean_dec_ref(v_vs_2156_);
lean_dec(v___x_2129_);
lean_dec_ref(v___x_2128_);
v___x_2167_ = lean_box(v___x_2162_);
if (v_isShared_2159_ == 0)
{
lean_ctor_set_tag(v___x_2158_, 0);
lean_ctor_set(v___x_2158_, 0, v___x_2167_);
v___x_2169_ = v___x_2158_;
goto v_reusejp_2168_;
}
else
{
lean_object* v_reuseFailAlloc_2170_; 
v_reuseFailAlloc_2170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2170_, 0, v___x_2167_);
v___x_2169_ = v_reuseFailAlloc_2170_;
goto v_reusejp_2168_;
}
v_reusejp_2168_:
{
return v___x_2169_;
}
}
else
{
size_t v___x_2171_; size_t v___x_2172_; lean_object* v___x_2173_; 
lean_del_object(v___x_2158_);
v___x_2171_ = ((size_t)0ULL);
v___x_2172_ = lean_usize_of_nat(v___x_2161_);
v___x_2173_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg(v___x_2127_, v___x_2128_, v___x_2129_, v_ctx_2130_, v_vs_2156_, v___x_2171_, v___x_2172_, v___y_2133_);
lean_dec_ref(v_vs_2156_);
return v___x_2173_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4_spec__5(uint8_t v___x_2175_, lean_object* v___x_2176_, lean_object* v___x_2177_, lean_object* v_ctx_2178_, lean_object* v_as_2179_, size_t v_i_2180_, size_t v_stop_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_){
_start:
{
uint8_t v___x_2187_; 
v___x_2187_ = lean_usize_dec_eq(v_i_2180_, v_stop_2181_);
if (v___x_2187_ == 0)
{
lean_object* v___x_2188_; lean_object* v___x_2189_; 
v___x_2188_ = lean_array_uget_borrowed(v_as_2179_, v_i_2180_);
lean_inc(v___x_2188_);
lean_inc(v___x_2177_);
lean_inc_ref(v___x_2176_);
v___x_2189_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4(v___x_2175_, v___x_2176_, v___x_2177_, v_ctx_2178_, v___x_2188_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_);
if (lean_obj_tag(v___x_2189_) == 0)
{
lean_object* v_a_2190_; lean_object* v___x_2192_; uint8_t v_isShared_2193_; uint8_t v_isSharedCheck_2201_; 
v_a_2190_ = lean_ctor_get(v___x_2189_, 0);
v_isSharedCheck_2201_ = !lean_is_exclusive(v___x_2189_);
if (v_isSharedCheck_2201_ == 0)
{
v___x_2192_ = v___x_2189_;
v_isShared_2193_ = v_isSharedCheck_2201_;
goto v_resetjp_2191_;
}
else
{
lean_inc(v_a_2190_);
lean_dec(v___x_2189_);
v___x_2192_ = lean_box(0);
v_isShared_2193_ = v_isSharedCheck_2201_;
goto v_resetjp_2191_;
}
v_resetjp_2191_:
{
uint8_t v___x_2194_; 
v___x_2194_ = lean_unbox(v_a_2190_);
if (v___x_2194_ == 0)
{
size_t v___x_2195_; size_t v___x_2196_; 
lean_del_object(v___x_2192_);
lean_dec(v_a_2190_);
v___x_2195_ = ((size_t)1ULL);
v___x_2196_ = lean_usize_add(v_i_2180_, v___x_2195_);
v_i_2180_ = v___x_2196_;
goto _start;
}
else
{
lean_object* v___x_2199_; 
lean_dec(v___x_2177_);
lean_dec_ref(v___x_2176_);
if (v_isShared_2193_ == 0)
{
v___x_2199_ = v___x_2192_;
goto v_reusejp_2198_;
}
else
{
lean_object* v_reuseFailAlloc_2200_; 
v_reuseFailAlloc_2200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2200_, 0, v_a_2190_);
v___x_2199_ = v_reuseFailAlloc_2200_;
goto v_reusejp_2198_;
}
v_reusejp_2198_:
{
return v___x_2199_;
}
}
}
}
else
{
lean_dec(v___x_2177_);
lean_dec_ref(v___x_2176_);
return v___x_2189_;
}
}
else
{
uint8_t v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; 
lean_dec(v___x_2177_);
lean_dec_ref(v___x_2176_);
v___x_2202_ = 0;
v___x_2203_ = lean_box(v___x_2202_);
v___x_2204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2204_, 0, v___x_2203_);
return v___x_2204_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4_spec__5___boxed(lean_object* v___x_2205_, lean_object* v___x_2206_, lean_object* v___x_2207_, lean_object* v_ctx_2208_, lean_object* v_as_2209_, lean_object* v_i_2210_, lean_object* v_stop_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_){
_start:
{
uint8_t v___x_9690__boxed_2217_; size_t v_i_boxed_2218_; size_t v_stop_boxed_2219_; lean_object* v_res_2220_; 
v___x_9690__boxed_2217_ = lean_unbox(v___x_2205_);
v_i_boxed_2218_ = lean_unbox_usize(v_i_2210_);
lean_dec(v_i_2210_);
v_stop_boxed_2219_ = lean_unbox_usize(v_stop_2211_);
lean_dec(v_stop_2211_);
v_res_2220_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4_spec__5(v___x_9690__boxed_2217_, v___x_2206_, v___x_2207_, v_ctx_2208_, v_as_2209_, v_i_boxed_2218_, v_stop_boxed_2219_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_);
lean_dec(v___y_2215_);
lean_dec_ref(v___y_2214_);
lean_dec(v___y_2213_);
lean_dec_ref(v___y_2212_);
lean_dec_ref(v_as_2209_);
lean_dec_ref(v_ctx_2208_);
return v_res_2220_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4___boxed(lean_object* v___x_2221_, lean_object* v___x_2222_, lean_object* v___x_2223_, lean_object* v_ctx_2224_, lean_object* v_x_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_){
_start:
{
uint8_t v___x_9709__boxed_2231_; lean_object* v_res_2232_; 
v___x_9709__boxed_2231_ = lean_unbox(v___x_2221_);
v_res_2232_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4(v___x_9709__boxed_2231_, v___x_2222_, v___x_2223_, v_ctx_2224_, v_x_2225_, v___y_2226_, v___y_2227_, v___y_2228_, v___y_2229_);
lean_dec(v___y_2229_);
lean_dec_ref(v___y_2228_);
lean_dec(v___y_2227_);
lean_dec_ref(v___y_2226_);
lean_dec_ref(v_ctx_2224_);
return v_res_2232_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4(uint8_t v___x_2233_, lean_object* v___x_2234_, lean_object* v___x_2235_, lean_object* v_ctx_2236_, lean_object* v_t_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_){
_start:
{
lean_object* v_root_2243_; lean_object* v_tail_2244_; lean_object* v___x_2245_; 
v_root_2243_ = lean_ctor_get(v_t_2237_, 0);
lean_inc_ref(v_root_2243_);
v_tail_2244_ = lean_ctor_get(v_t_2237_, 1);
lean_inc_ref(v_tail_2244_);
lean_dec_ref(v_t_2237_);
lean_inc(v___x_2235_);
lean_inc_ref(v___x_2234_);
v___x_2245_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4(v___x_2233_, v___x_2234_, v___x_2235_, v_ctx_2236_, v_root_2243_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_);
if (lean_obj_tag(v___x_2245_) == 0)
{
lean_object* v_a_2246_; uint8_t v___x_2247_; 
v_a_2246_ = lean_ctor_get(v___x_2245_, 0);
lean_inc(v_a_2246_);
v___x_2247_ = lean_unbox(v_a_2246_);
lean_dec(v_a_2246_);
if (v___x_2247_ == 0)
{
lean_object* v___x_2248_; lean_object* v___x_2249_; uint8_t v___x_2250_; 
v___x_2248_ = lean_unsigned_to_nat(0u);
v___x_2249_ = lean_array_get_size(v_tail_2244_);
v___x_2250_ = lean_nat_dec_lt(v___x_2248_, v___x_2249_);
if (v___x_2250_ == 0)
{
lean_dec_ref(v_tail_2244_);
lean_dec(v___x_2235_);
lean_dec_ref(v___x_2234_);
return v___x_2245_;
}
else
{
if (v___x_2250_ == 0)
{
lean_dec_ref(v_tail_2244_);
lean_dec(v___x_2235_);
lean_dec_ref(v___x_2234_);
return v___x_2245_;
}
else
{
size_t v___x_2251_; size_t v___x_2252_; lean_object* v___x_2253_; 
lean_dec_ref(v___x_2245_);
v___x_2251_ = ((size_t)0ULL);
v___x_2252_ = lean_usize_of_nat(v___x_2249_);
v___x_2253_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg(v___x_2233_, v___x_2234_, v___x_2235_, v_ctx_2236_, v_tail_2244_, v___x_2251_, v___x_2252_, v___y_2239_);
lean_dec_ref(v_tail_2244_);
return v___x_2253_;
}
}
}
else
{
lean_dec_ref(v_tail_2244_);
lean_dec(v___x_2235_);
lean_dec_ref(v___x_2234_);
return v___x_2245_;
}
}
else
{
lean_dec_ref(v_tail_2244_);
lean_dec(v___x_2235_);
lean_dec_ref(v___x_2234_);
return v___x_2245_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4___boxed(lean_object* v___x_2254_, lean_object* v___x_2255_, lean_object* v___x_2256_, lean_object* v_ctx_2257_, lean_object* v_t_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_){
_start:
{
uint8_t v___x_9854__boxed_2264_; lean_object* v_res_2265_; 
v___x_9854__boxed_2264_ = lean_unbox(v___x_2254_);
v_res_2265_ = l_Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4(v___x_9854__boxed_2264_, v___x_2255_, v___x_2256_, v_ctx_2257_, v_t_2258_, v___y_2259_, v___y_2260_, v___y_2261_, v___y_2262_);
lean_dec(v___y_2262_);
lean_dec_ref(v___y_2261_);
lean_dec(v___y_2260_);
lean_dec_ref(v___y_2259_);
lean_dec_ref(v_ctx_2257_);
return v_res_2265_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices(lean_object* v_ctx_2266_, lean_object* v_a_2267_, lean_object* v_a_2268_, lean_object* v_a_2269_, lean_object* v_a_2270_){
_start:
{
lean_object* v_majorTypeIndices_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; uint8_t v___x_2275_; uint8_t v___y_2277_; 
v_majorTypeIndices_2272_ = lean_ctor_get(v_ctx_2266_, 5);
lean_inc_ref(v_majorTypeIndices_2272_);
v___x_2273_ = lean_array_get_size(v_majorTypeIndices_2272_);
v___x_2274_ = lean_unsigned_to_nat(0u);
v___x_2275_ = lean_nat_dec_eq(v___x_2273_, v___x_2274_);
if (v___x_2275_ == 0)
{
uint8_t v___x_2301_; 
v___x_2301_ = lean_nat_dec_lt(v___x_2274_, v___x_2273_);
if (v___x_2301_ == 0)
{
v___y_2277_ = v___x_2275_;
goto v___jp_2276_;
}
else
{
if (v___x_2301_ == 0)
{
v___y_2277_ = v___x_2275_;
goto v___jp_2276_;
}
else
{
size_t v___x_2302_; size_t v___x_2303_; uint8_t v___x_2304_; 
v___x_2302_ = ((size_t)0ULL);
v___x_2303_ = lean_usize_of_nat(v___x_2273_);
v___x_2304_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5(v___x_2273_, v_majorTypeIndices_2272_, v___x_2302_, v___x_2303_);
v___y_2277_ = v___x_2304_;
goto v___jp_2276_;
}
}
}
else
{
lean_object* v___x_2305_; lean_object* v___x_2306_; 
lean_dec_ref(v_majorTypeIndices_2272_);
lean_dec_ref(v_a_2267_);
lean_dec_ref(v_ctx_2266_);
v___x_2305_ = lean_box(v___x_2275_);
v___x_2306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2306_, 0, v___x_2305_);
return v___x_2306_;
}
v___jp_2276_:
{
if (v___y_2277_ == 0)
{
uint8_t v___x_2278_; 
v___x_2278_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1___redArg(v_majorTypeIndices_2272_, v___x_2273_, v___x_2273_);
if (v___x_2278_ == 0)
{
lean_object* v_lctx_2279_; lean_object* v_decls_2280_; lean_object* v___x_2281_; 
v_lctx_2279_ = lean_ctor_get(v_a_2267_, 2);
v_decls_2280_ = lean_ctor_get(v_lctx_2279_, 1);
lean_inc_ref(v_decls_2280_);
v___x_2281_ = l_Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4(v___x_2278_, v_majorTypeIndices_2272_, v___x_2273_, v_ctx_2266_, v_decls_2280_, v_a_2267_, v_a_2268_, v_a_2269_, v_a_2270_);
lean_dec_ref(v_a_2267_);
lean_dec_ref(v_ctx_2266_);
if (lean_obj_tag(v___x_2281_) == 0)
{
lean_object* v_a_2282_; lean_object* v___x_2284_; uint8_t v_isShared_2285_; uint8_t v_isSharedCheck_2296_; 
v_a_2282_ = lean_ctor_get(v___x_2281_, 0);
v_isSharedCheck_2296_ = !lean_is_exclusive(v___x_2281_);
if (v_isSharedCheck_2296_ == 0)
{
v___x_2284_ = v___x_2281_;
v_isShared_2285_ = v_isSharedCheck_2296_;
goto v_resetjp_2283_;
}
else
{
lean_inc(v_a_2282_);
lean_dec(v___x_2281_);
v___x_2284_ = lean_box(0);
v_isShared_2285_ = v_isSharedCheck_2296_;
goto v_resetjp_2283_;
}
v_resetjp_2283_:
{
uint8_t v___x_2286_; 
v___x_2286_ = lean_unbox(v_a_2282_);
lean_dec(v_a_2282_);
if (v___x_2286_ == 0)
{
uint8_t v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2290_; 
v___x_2287_ = 1;
v___x_2288_ = lean_box(v___x_2287_);
if (v_isShared_2285_ == 0)
{
lean_ctor_set(v___x_2284_, 0, v___x_2288_);
v___x_2290_ = v___x_2284_;
goto v_reusejp_2289_;
}
else
{
lean_object* v_reuseFailAlloc_2291_; 
v_reuseFailAlloc_2291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2291_, 0, v___x_2288_);
v___x_2290_ = v_reuseFailAlloc_2291_;
goto v_reusejp_2289_;
}
v_reusejp_2289_:
{
return v___x_2290_;
}
}
else
{
lean_object* v___x_2292_; lean_object* v___x_2294_; 
v___x_2292_ = lean_box(v___x_2278_);
if (v_isShared_2285_ == 0)
{
lean_ctor_set(v___x_2284_, 0, v___x_2292_);
v___x_2294_ = v___x_2284_;
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
}
}
else
{
return v___x_2281_;
}
}
else
{
lean_object* v___x_2297_; lean_object* v___x_2298_; 
lean_dec_ref(v_majorTypeIndices_2272_);
lean_dec_ref(v_a_2267_);
lean_dec_ref(v_ctx_2266_);
v___x_2297_ = lean_box(v___y_2277_);
v___x_2298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2298_, 0, v___x_2297_);
return v___x_2298_;
}
}
else
{
lean_object* v___x_2299_; lean_object* v___x_2300_; 
lean_dec_ref(v_majorTypeIndices_2272_);
lean_dec_ref(v_a_2267_);
lean_dec_ref(v_ctx_2266_);
v___x_2299_ = lean_box(v___x_2275_);
v___x_2300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2300_, 0, v___x_2299_);
return v___x_2300_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___boxed(lean_object* v_ctx_2307_, lean_object* v_a_2308_, lean_object* v_a_2309_, lean_object* v_a_2310_, lean_object* v_a_2311_, lean_object* v_a_2312_){
_start:
{
lean_object* v_res_2313_; 
v_res_2313_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices(v_ctx_2307_, v_a_2308_, v_a_2309_, v_a_2310_, v_a_2311_);
lean_dec(v_a_2311_);
lean_dec_ref(v_a_2310_);
lean_dec(v_a_2309_);
return v_res_2313_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0(lean_object* v___x_2314_, lean_object* v_i_2315_, lean_object* v_n_2316_, lean_object* v_i_2317_, lean_object* v_a_2318_){
_start:
{
uint8_t v___x_2319_; 
v___x_2319_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0___redArg(v___x_2314_, v_i_2315_, v_n_2316_, v_i_2317_);
return v___x_2319_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0___boxed(lean_object* v___x_2320_, lean_object* v_i_2321_, lean_object* v_n_2322_, lean_object* v_i_2323_, lean_object* v_a_2324_){
_start:
{
uint8_t v_res_2325_; lean_object* v_r_2326_; 
v_res_2325_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0(v___x_2320_, v_i_2321_, v_n_2322_, v_i_2323_, v_a_2324_);
lean_dec(v_n_2322_);
lean_dec(v_i_2321_);
lean_dec_ref(v___x_2320_);
v_r_2326_ = lean_box(v_res_2325_);
return v_r_2326_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1(lean_object* v___x_2327_, lean_object* v_n_2328_, lean_object* v_i_2329_, lean_object* v_a_2330_){
_start:
{
uint8_t v___x_2331_; 
v___x_2331_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1___redArg(v___x_2327_, v_n_2328_, v_i_2329_);
return v___x_2331_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1___boxed(lean_object* v___x_2332_, lean_object* v_n_2333_, lean_object* v_i_2334_, lean_object* v_a_2335_){
_start:
{
uint8_t v_res_2336_; lean_object* v_r_2337_; 
v_res_2336_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1(v___x_2332_, v_n_2333_, v_i_2334_, v_a_2335_);
lean_dec(v_n_2333_);
lean_dec_ref(v___x_2332_);
v_r_2337_ = lean_box(v_res_2336_);
return v_r_2337_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5(uint8_t v___x_2338_, lean_object* v___x_2339_, lean_object* v___x_2340_, lean_object* v_ctx_2341_, lean_object* v_as_2342_, size_t v_i_2343_, size_t v_stop_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_){
_start:
{
lean_object* v___x_2350_; 
v___x_2350_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg(v___x_2338_, v___x_2339_, v___x_2340_, v_ctx_2341_, v_as_2342_, v_i_2343_, v_stop_2344_, v___y_2346_);
return v___x_2350_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___boxed(lean_object* v___x_2351_, lean_object* v___x_2352_, lean_object* v___x_2353_, lean_object* v_ctx_2354_, lean_object* v_as_2355_, lean_object* v_i_2356_, lean_object* v_stop_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_){
_start:
{
uint8_t v___x_9993__boxed_2363_; size_t v_i_boxed_2364_; size_t v_stop_boxed_2365_; lean_object* v_res_2366_; 
v___x_9993__boxed_2363_ = lean_unbox(v___x_2351_);
v_i_boxed_2364_ = lean_unbox_usize(v_i_2356_);
lean_dec(v_i_2356_);
v_stop_boxed_2365_ = lean_unbox_usize(v_stop_2357_);
lean_dec(v_stop_2357_);
v_res_2366_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5(v___x_9993__boxed_2363_, v___x_2352_, v___x_2353_, v_ctx_2354_, v_as_2355_, v_i_boxed_2364_, v_stop_boxed_2365_, v___y_2358_, v___y_2359_, v___y_2360_, v___y_2361_);
lean_dec(v___y_2361_);
lean_dec_ref(v___y_2360_);
lean_dec(v___y_2359_);
lean_dec_ref(v___y_2358_);
lean_dec_ref(v_as_2355_);
lean_dec_ref(v_ctx_2354_);
return v_res_2366_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__0(lean_object* v_as_2367_, size_t v_i_2368_, size_t v_stop_2369_, lean_object* v_b_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_){
_start:
{
lean_object* v_a_2377_; uint8_t v___x_2381_; 
v___x_2381_ = lean_usize_dec_eq(v_i_2368_, v_stop_2369_);
if (v___x_2381_ == 0)
{
lean_object* v_toInductionSubgoal_2382_; lean_object* v_ctorName_2383_; lean_object* v_mvarId_2384_; lean_object* v_fields_2385_; lean_object* v_subst_2386_; lean_object* v___x_2388_; uint8_t v_isShared_2389_; uint8_t v_isSharedCheck_2439_; 
v_toInductionSubgoal_2382_ = lean_ctor_get(v_b_2370_, 0);
lean_inc_ref(v_toInductionSubgoal_2382_);
v_ctorName_2383_ = lean_ctor_get(v_b_2370_, 1);
v_mvarId_2384_ = lean_ctor_get(v_toInductionSubgoal_2382_, 0);
v_fields_2385_ = lean_ctor_get(v_toInductionSubgoal_2382_, 1);
v_subst_2386_ = lean_ctor_get(v_toInductionSubgoal_2382_, 2);
v_isSharedCheck_2439_ = !lean_is_exclusive(v_toInductionSubgoal_2382_);
if (v_isSharedCheck_2439_ == 0)
{
v___x_2388_ = v_toInductionSubgoal_2382_;
v_isShared_2389_ = v_isSharedCheck_2439_;
goto v_resetjp_2387_;
}
else
{
lean_inc(v_subst_2386_);
lean_inc(v_fields_2385_);
lean_inc(v_mvarId_2384_);
lean_dec(v_toInductionSubgoal_2382_);
v___x_2388_ = lean_box(0);
v_isShared_2389_ = v_isSharedCheck_2439_;
goto v_resetjp_2387_;
}
v_resetjp_2387_:
{
lean_object* v___x_2390_; lean_object* v___x_2391_; 
v___x_2390_ = lean_array_uget_borrowed(v_as_2367_, v_i_2368_);
lean_inc(v___x_2390_);
v___x_2391_ = l_Lean_Meta_FVarSubst_get(v_subst_2386_, v___x_2390_);
if (lean_obj_tag(v___x_2391_) == 1)
{
lean_object* v_fvarId_2392_; lean_object* v___x_2393_; 
v_fvarId_2392_ = lean_ctor_get(v___x_2391_, 0);
lean_inc(v_fvarId_2392_);
lean_dec_ref(v___x_2391_);
v___x_2393_ = l_Lean_Meta_saveState___redArg(v___y_2372_, v___y_2374_);
if (lean_obj_tag(v___x_2393_) == 0)
{
lean_object* v_a_2394_; lean_object* v___x_2395_; 
v_a_2394_ = lean_ctor_get(v___x_2393_, 0);
lean_inc(v_a_2394_);
lean_dec_ref(v___x_2393_);
lean_inc(v___y_2374_);
lean_inc_ref(v___y_2373_);
lean_inc(v___y_2372_);
lean_inc_ref(v___y_2371_);
v___x_2395_ = l_Lean_MVarId_clear(v_mvarId_2384_, v_fvarId_2392_, v___y_2371_, v___y_2372_, v___y_2373_, v___y_2374_);
if (lean_obj_tag(v___x_2395_) == 0)
{
lean_object* v___x_2397_; uint8_t v_isShared_2398_; uint8_t v_isSharedCheck_2407_; 
lean_inc(v_ctorName_2383_);
lean_dec(v_a_2394_);
v_isSharedCheck_2407_ = !lean_is_exclusive(v_b_2370_);
if (v_isSharedCheck_2407_ == 0)
{
lean_object* v_unused_2408_; lean_object* v_unused_2409_; 
v_unused_2408_ = lean_ctor_get(v_b_2370_, 1);
lean_dec(v_unused_2408_);
v_unused_2409_ = lean_ctor_get(v_b_2370_, 0);
lean_dec(v_unused_2409_);
v___x_2397_ = v_b_2370_;
v_isShared_2398_ = v_isSharedCheck_2407_;
goto v_resetjp_2396_;
}
else
{
lean_dec(v_b_2370_);
v___x_2397_ = lean_box(0);
v_isShared_2398_ = v_isSharedCheck_2407_;
goto v_resetjp_2396_;
}
v_resetjp_2396_:
{
lean_object* v_a_2399_; lean_object* v___x_2400_; lean_object* v___x_2402_; 
v_a_2399_ = lean_ctor_get(v___x_2395_, 0);
lean_inc(v_a_2399_);
lean_dec_ref(v___x_2395_);
v___x_2400_ = l_Lean_Meta_FVarSubst_erase(v_subst_2386_, v___x_2390_);
if (v_isShared_2389_ == 0)
{
lean_ctor_set(v___x_2388_, 2, v___x_2400_);
lean_ctor_set(v___x_2388_, 0, v_a_2399_);
v___x_2402_ = v___x_2388_;
goto v_reusejp_2401_;
}
else
{
lean_object* v_reuseFailAlloc_2406_; 
v_reuseFailAlloc_2406_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2406_, 0, v_a_2399_);
lean_ctor_set(v_reuseFailAlloc_2406_, 1, v_fields_2385_);
lean_ctor_set(v_reuseFailAlloc_2406_, 2, v___x_2400_);
v___x_2402_ = v_reuseFailAlloc_2406_;
goto v_reusejp_2401_;
}
v_reusejp_2401_:
{
lean_object* v___x_2404_; 
if (v_isShared_2398_ == 0)
{
lean_ctor_set(v___x_2397_, 0, v___x_2402_);
v___x_2404_ = v___x_2397_;
goto v_reusejp_2403_;
}
else
{
lean_object* v_reuseFailAlloc_2405_; 
v_reuseFailAlloc_2405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2405_, 0, v___x_2402_);
lean_ctor_set(v_reuseFailAlloc_2405_, 1, v_ctorName_2383_);
v___x_2404_ = v_reuseFailAlloc_2405_;
goto v_reusejp_2403_;
}
v_reusejp_2403_:
{
v_a_2377_ = v___x_2404_;
goto v___jp_2376_;
}
}
}
}
else
{
lean_object* v_a_2410_; lean_object* v___x_2412_; uint8_t v_isShared_2413_; uint8_t v_isSharedCheck_2430_; 
lean_del_object(v___x_2388_);
lean_dec(v_subst_2386_);
lean_dec_ref(v_fields_2385_);
v_a_2410_ = lean_ctor_get(v___x_2395_, 0);
v_isSharedCheck_2430_ = !lean_is_exclusive(v___x_2395_);
if (v_isSharedCheck_2430_ == 0)
{
v___x_2412_ = v___x_2395_;
v_isShared_2413_ = v_isSharedCheck_2430_;
goto v_resetjp_2411_;
}
else
{
lean_inc(v_a_2410_);
lean_dec(v___x_2395_);
v___x_2412_ = lean_box(0);
v_isShared_2413_ = v_isSharedCheck_2430_;
goto v_resetjp_2411_;
}
v_resetjp_2411_:
{
lean_object* v___x_2415_; 
lean_inc(v_a_2410_);
if (v_isShared_2413_ == 0)
{
v___x_2415_ = v___x_2412_;
goto v_reusejp_2414_;
}
else
{
lean_object* v_reuseFailAlloc_2429_; 
v_reuseFailAlloc_2429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2429_, 0, v_a_2410_);
v___x_2415_ = v_reuseFailAlloc_2429_;
goto v_reusejp_2414_;
}
v_reusejp_2414_:
{
uint8_t v___y_2417_; uint8_t v___x_2427_; 
v___x_2427_ = l_Lean_Exception_isInterrupt(v_a_2410_);
if (v___x_2427_ == 0)
{
uint8_t v___x_2428_; 
v___x_2428_ = l_Lean_Exception_isRuntime(v_a_2410_);
v___y_2417_ = v___x_2428_;
goto v___jp_2416_;
}
else
{
lean_dec(v_a_2410_);
v___y_2417_ = v___x_2427_;
goto v___jp_2416_;
}
v___jp_2416_:
{
if (v___y_2417_ == 0)
{
lean_object* v___x_2418_; 
lean_dec_ref(v___x_2415_);
v___x_2418_ = l_Lean_Meta_SavedState_restore___redArg(v_a_2394_, v___y_2372_, v___y_2374_);
lean_dec(v_a_2394_);
if (lean_obj_tag(v___x_2418_) == 0)
{
lean_dec_ref(v___x_2418_);
v_a_2377_ = v_b_2370_;
goto v___jp_2376_;
}
else
{
lean_object* v_a_2419_; lean_object* v___x_2421_; uint8_t v_isShared_2422_; uint8_t v_isSharedCheck_2426_; 
lean_dec(v___y_2374_);
lean_dec_ref(v___y_2373_);
lean_dec(v___y_2372_);
lean_dec_ref(v___y_2371_);
lean_dec_ref(v_b_2370_);
v_a_2419_ = lean_ctor_get(v___x_2418_, 0);
v_isSharedCheck_2426_ = !lean_is_exclusive(v___x_2418_);
if (v_isSharedCheck_2426_ == 0)
{
v___x_2421_ = v___x_2418_;
v_isShared_2422_ = v_isSharedCheck_2426_;
goto v_resetjp_2420_;
}
else
{
lean_inc(v_a_2419_);
lean_dec(v___x_2418_);
v___x_2421_ = lean_box(0);
v_isShared_2422_ = v_isSharedCheck_2426_;
goto v_resetjp_2420_;
}
v_resetjp_2420_:
{
lean_object* v___x_2424_; 
if (v_isShared_2422_ == 0)
{
v___x_2424_ = v___x_2421_;
goto v_reusejp_2423_;
}
else
{
lean_object* v_reuseFailAlloc_2425_; 
v_reuseFailAlloc_2425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2425_, 0, v_a_2419_);
v___x_2424_ = v_reuseFailAlloc_2425_;
goto v_reusejp_2423_;
}
v_reusejp_2423_:
{
return v___x_2424_;
}
}
}
}
else
{
lean_dec(v_a_2394_);
lean_dec(v___y_2374_);
lean_dec_ref(v___y_2373_);
lean_dec(v___y_2372_);
lean_dec_ref(v___y_2371_);
lean_dec_ref(v_b_2370_);
return v___x_2415_;
}
}
}
}
}
}
else
{
lean_object* v_a_2431_; lean_object* v___x_2433_; uint8_t v_isShared_2434_; uint8_t v_isSharedCheck_2438_; 
lean_dec(v_fvarId_2392_);
lean_del_object(v___x_2388_);
lean_dec(v_subst_2386_);
lean_dec_ref(v_fields_2385_);
lean_dec(v_mvarId_2384_);
lean_dec(v___y_2374_);
lean_dec_ref(v___y_2373_);
lean_dec(v___y_2372_);
lean_dec_ref(v___y_2371_);
lean_dec_ref(v_b_2370_);
v_a_2431_ = lean_ctor_get(v___x_2393_, 0);
v_isSharedCheck_2438_ = !lean_is_exclusive(v___x_2393_);
if (v_isSharedCheck_2438_ == 0)
{
v___x_2433_ = v___x_2393_;
v_isShared_2434_ = v_isSharedCheck_2438_;
goto v_resetjp_2432_;
}
else
{
lean_inc(v_a_2431_);
lean_dec(v___x_2393_);
v___x_2433_ = lean_box(0);
v_isShared_2434_ = v_isSharedCheck_2438_;
goto v_resetjp_2432_;
}
v_resetjp_2432_:
{
lean_object* v___x_2436_; 
if (v_isShared_2434_ == 0)
{
v___x_2436_ = v___x_2433_;
goto v_reusejp_2435_;
}
else
{
lean_object* v_reuseFailAlloc_2437_; 
v_reuseFailAlloc_2437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2437_, 0, v_a_2431_);
v___x_2436_ = v_reuseFailAlloc_2437_;
goto v_reusejp_2435_;
}
v_reusejp_2435_:
{
return v___x_2436_;
}
}
}
}
else
{
lean_dec_ref(v___x_2391_);
lean_del_object(v___x_2388_);
lean_dec(v_subst_2386_);
lean_dec_ref(v_fields_2385_);
lean_dec(v_mvarId_2384_);
v_a_2377_ = v_b_2370_;
goto v___jp_2376_;
}
}
}
else
{
lean_object* v___x_2440_; 
lean_dec(v___y_2374_);
lean_dec_ref(v___y_2373_);
lean_dec(v___y_2372_);
lean_dec_ref(v___y_2371_);
v___x_2440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2440_, 0, v_b_2370_);
return v___x_2440_;
}
v___jp_2376_:
{
size_t v___x_2378_; size_t v___x_2379_; 
v___x_2378_ = ((size_t)1ULL);
v___x_2379_ = lean_usize_add(v_i_2368_, v___x_2378_);
v_i_2368_ = v___x_2379_;
v_b_2370_ = v_a_2377_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__0___boxed(lean_object* v_as_2441_, lean_object* v_i_2442_, lean_object* v_stop_2443_, lean_object* v_b_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_){
_start:
{
size_t v_i_boxed_2450_; size_t v_stop_boxed_2451_; lean_object* v_res_2452_; 
v_i_boxed_2450_ = lean_unbox_usize(v_i_2442_);
lean_dec(v_i_2442_);
v_stop_boxed_2451_ = lean_unbox_usize(v_stop_2443_);
lean_dec(v_stop_2443_);
v_res_2452_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__0(v_as_2441_, v_i_boxed_2450_, v_stop_boxed_2451_, v_b_2444_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_);
lean_dec_ref(v_as_2441_);
return v_res_2452_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__1(lean_object* v_indicesFVarIds_2453_, size_t v_sz_2454_, size_t v_i_2455_, lean_object* v_bs_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_){
_start:
{
uint8_t v___x_2462_; 
v___x_2462_ = lean_usize_dec_lt(v_i_2455_, v_sz_2454_);
if (v___x_2462_ == 0)
{
lean_object* v___x_2463_; 
lean_dec(v___y_2460_);
lean_dec_ref(v___y_2459_);
lean_dec(v___y_2458_);
lean_dec_ref(v___y_2457_);
v___x_2463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2463_, 0, v_bs_2456_);
return v___x_2463_;
}
else
{
lean_object* v_v_2464_; lean_object* v___x_2465_; lean_object* v_bs_x27_2466_; lean_object* v_a_2468_; lean_object* v___y_2474_; lean_object* v___x_2484_; uint8_t v___x_2485_; 
v_v_2464_ = lean_array_uget(v_bs_2456_, v_i_2455_);
v___x_2465_ = lean_unsigned_to_nat(0u);
v_bs_x27_2466_ = lean_array_uset(v_bs_2456_, v_i_2455_, v___x_2465_);
v___x_2484_ = lean_array_get_size(v_indicesFVarIds_2453_);
v___x_2485_ = lean_nat_dec_lt(v___x_2465_, v___x_2484_);
if (v___x_2485_ == 0)
{
v_a_2468_ = v_v_2464_;
goto v___jp_2467_;
}
else
{
uint8_t v___x_2486_; 
v___x_2486_ = lean_nat_dec_le(v___x_2484_, v___x_2484_);
if (v___x_2486_ == 0)
{
if (v___x_2485_ == 0)
{
v_a_2468_ = v_v_2464_;
goto v___jp_2467_;
}
else
{
size_t v___x_2487_; size_t v___x_2488_; lean_object* v___x_2489_; 
v___x_2487_ = ((size_t)0ULL);
v___x_2488_ = lean_usize_of_nat(v___x_2484_);
lean_inc(v___y_2460_);
lean_inc_ref(v___y_2459_);
lean_inc(v___y_2458_);
lean_inc_ref(v___y_2457_);
v___x_2489_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__0(v_indicesFVarIds_2453_, v___x_2487_, v___x_2488_, v_v_2464_, v___y_2457_, v___y_2458_, v___y_2459_, v___y_2460_);
v___y_2474_ = v___x_2489_;
goto v___jp_2473_;
}
}
else
{
size_t v___x_2490_; size_t v___x_2491_; lean_object* v___x_2492_; 
v___x_2490_ = ((size_t)0ULL);
v___x_2491_ = lean_usize_of_nat(v___x_2484_);
lean_inc(v___y_2460_);
lean_inc_ref(v___y_2459_);
lean_inc(v___y_2458_);
lean_inc_ref(v___y_2457_);
v___x_2492_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__0(v_indicesFVarIds_2453_, v___x_2490_, v___x_2491_, v_v_2464_, v___y_2457_, v___y_2458_, v___y_2459_, v___y_2460_);
v___y_2474_ = v___x_2492_;
goto v___jp_2473_;
}
}
v___jp_2467_:
{
size_t v___x_2469_; size_t v___x_2470_; lean_object* v___x_2471_; 
v___x_2469_ = ((size_t)1ULL);
v___x_2470_ = lean_usize_add(v_i_2455_, v___x_2469_);
v___x_2471_ = lean_array_uset(v_bs_x27_2466_, v_i_2455_, v_a_2468_);
v_i_2455_ = v___x_2470_;
v_bs_2456_ = v___x_2471_;
goto _start;
}
v___jp_2473_:
{
if (lean_obj_tag(v___y_2474_) == 0)
{
lean_object* v_a_2475_; 
v_a_2475_ = lean_ctor_get(v___y_2474_, 0);
lean_inc(v_a_2475_);
lean_dec_ref(v___y_2474_);
v_a_2468_ = v_a_2475_;
goto v___jp_2467_;
}
else
{
lean_object* v_a_2476_; lean_object* v___x_2478_; uint8_t v_isShared_2479_; uint8_t v_isSharedCheck_2483_; 
lean_dec_ref(v_bs_x27_2466_);
lean_dec(v___y_2460_);
lean_dec_ref(v___y_2459_);
lean_dec(v___y_2458_);
lean_dec_ref(v___y_2457_);
v_a_2476_ = lean_ctor_get(v___y_2474_, 0);
v_isSharedCheck_2483_ = !lean_is_exclusive(v___y_2474_);
if (v_isSharedCheck_2483_ == 0)
{
v___x_2478_ = v___y_2474_;
v_isShared_2479_ = v_isSharedCheck_2483_;
goto v_resetjp_2477_;
}
else
{
lean_inc(v_a_2476_);
lean_dec(v___y_2474_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__1___boxed(lean_object* v_indicesFVarIds_2493_, lean_object* v_sz_2494_, lean_object* v_i_2495_, lean_object* v_bs_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_){
_start:
{
size_t v_sz_boxed_2502_; size_t v_i_boxed_2503_; lean_object* v_res_2504_; 
v_sz_boxed_2502_ = lean_unbox_usize(v_sz_2494_);
lean_dec(v_sz_2494_);
v_i_boxed_2503_ = lean_unbox_usize(v_i_2495_);
lean_dec(v_i_2495_);
v_res_2504_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__1(v_indicesFVarIds_2493_, v_sz_boxed_2502_, v_i_boxed_2503_, v_bs_2496_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_);
lean_dec_ref(v_indicesFVarIds_2493_);
return v_res_2504_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices(lean_object* v_s_u2081_2505_, lean_object* v_s_u2082_2506_, lean_object* v_a_2507_, lean_object* v_a_2508_, lean_object* v_a_2509_, lean_object* v_a_2510_){
_start:
{
lean_object* v_indicesFVarIds_2512_; size_t v_sz_2513_; size_t v___x_2514_; lean_object* v___x_2515_; 
v_indicesFVarIds_2512_ = lean_ctor_get(v_s_u2081_2505_, 1);
v_sz_2513_ = lean_array_size(v_s_u2082_2506_);
v___x_2514_ = ((size_t)0ULL);
v___x_2515_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__1(v_indicesFVarIds_2512_, v_sz_2513_, v___x_2514_, v_s_u2082_2506_, v_a_2507_, v_a_2508_, v_a_2509_, v_a_2510_);
return v___x_2515_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices___boxed(lean_object* v_s_u2081_2516_, lean_object* v_s_u2082_2517_, lean_object* v_a_2518_, lean_object* v_a_2519_, lean_object* v_a_2520_, lean_object* v_a_2521_, lean_object* v_a_2522_){
_start:
{
lean_object* v_res_2523_; 
v_res_2523_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices(v_s_u2081_2516_, v_s_u2082_2517_, v_a_2518_, v_a_2519_, v_a_2520_, v_a_2521_);
lean_dec_ref(v_s_u2081_2516_);
return v_res_2523_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0___redArg(lean_object* v_ctorNames_2524_, lean_object* v_us_2525_, lean_object* v_params_2526_, lean_object* v_majorFVarId_2527_, lean_object* v_as_2528_, lean_object* v_i_2529_, lean_object* v_j_2530_, lean_object* v_bs_2531_){
_start:
{
lean_object* v_zero_2532_; uint8_t v_isZero_2533_; 
v_zero_2532_ = lean_unsigned_to_nat(0u);
v_isZero_2533_ = lean_nat_dec_eq(v_i_2529_, v_zero_2532_);
if (v_isZero_2533_ == 1)
{
lean_dec(v_j_2530_);
lean_dec(v_i_2529_);
lean_dec(v_majorFVarId_2527_);
lean_dec(v_us_2525_);
return v_bs_2531_;
}
else
{
lean_object* v_one_2534_; lean_object* v_n_2535_; lean_object* v___y_2537_; lean_object* v___x_2541_; lean_object* v___x_2542_; uint8_t v___x_2543_; 
v_one_2534_ = lean_unsigned_to_nat(1u);
v_n_2535_ = lean_nat_sub(v_i_2529_, v_one_2534_);
lean_dec(v_i_2529_);
v___x_2541_ = lean_array_fget(v_as_2528_, v_j_2530_);
v___x_2542_ = lean_array_get_size(v_ctorNames_2524_);
v___x_2543_ = lean_nat_dec_lt(v_j_2530_, v___x_2542_);
if (v___x_2543_ == 0)
{
lean_object* v___x_2544_; lean_object* v___x_2545_; 
v___x_2544_ = lean_box(0);
v___x_2545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2545_, 0, v___x_2541_);
lean_ctor_set(v___x_2545_, 1, v___x_2544_);
v___y_2537_ = v___x_2545_;
goto v___jp_2536_;
}
else
{
lean_object* v_mvarId_2546_; lean_object* v_fields_2547_; lean_object* v_subst_2548_; lean_object* v___x_2550_; uint8_t v_isShared_2551_; uint8_t v_isSharedCheck_2563_; 
v_mvarId_2546_ = lean_ctor_get(v___x_2541_, 0);
v_fields_2547_ = lean_ctor_get(v___x_2541_, 1);
v_subst_2548_ = lean_ctor_get(v___x_2541_, 2);
v_isSharedCheck_2563_ = !lean_is_exclusive(v___x_2541_);
if (v_isSharedCheck_2563_ == 0)
{
v___x_2550_ = v___x_2541_;
v_isShared_2551_ = v_isSharedCheck_2563_;
goto v_resetjp_2549_;
}
else
{
lean_inc(v_subst_2548_);
lean_inc(v_fields_2547_);
lean_inc(v_mvarId_2546_);
lean_dec(v___x_2541_);
v___x_2550_ = lean_box(0);
v_isShared_2551_ = v_isSharedCheck_2563_;
goto v_resetjp_2549_;
}
v_resetjp_2549_:
{
lean_object* v_ctorName_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v_ctorApp_2555_; lean_object* v___x_2556_; lean_object* v_subst_2557_; lean_object* v___x_2559_; 
v_ctorName_2552_ = lean_array_fget_borrowed(v_ctorNames_2524_, v_j_2530_);
lean_inc(v_us_2525_);
lean_inc(v_ctorName_2552_);
v___x_2553_ = l_Lean_mkConst(v_ctorName_2552_, v_us_2525_);
v___x_2554_ = l_Lean_mkAppN(v___x_2553_, v_params_2526_);
v_ctorApp_2555_ = l_Lean_mkAppN(v___x_2554_, v_fields_2547_);
v___x_2556_ = l_Lean_Meta_FVarSubst_erase(v_subst_2548_, v_majorFVarId_2527_);
lean_inc(v_majorFVarId_2527_);
v_subst_2557_ = l_Lean_Meta_FVarSubst_insert(v___x_2556_, v_majorFVarId_2527_, v_ctorApp_2555_);
if (v_isShared_2551_ == 0)
{
lean_ctor_set(v___x_2550_, 2, v_subst_2557_);
v___x_2559_ = v___x_2550_;
goto v_reusejp_2558_;
}
else
{
lean_object* v_reuseFailAlloc_2562_; 
v_reuseFailAlloc_2562_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2562_, 0, v_mvarId_2546_);
lean_ctor_set(v_reuseFailAlloc_2562_, 1, v_fields_2547_);
lean_ctor_set(v_reuseFailAlloc_2562_, 2, v_subst_2557_);
v___x_2559_ = v_reuseFailAlloc_2562_;
goto v_reusejp_2558_;
}
v_reusejp_2558_:
{
lean_object* v___x_2560_; lean_object* v___x_2561_; 
lean_inc(v_ctorName_2552_);
v___x_2560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2560_, 0, v_ctorName_2552_);
v___x_2561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2561_, 0, v___x_2559_);
lean_ctor_set(v___x_2561_, 1, v___x_2560_);
v___y_2537_ = v___x_2561_;
goto v___jp_2536_;
}
}
}
v___jp_2536_:
{
lean_object* v___x_2538_; lean_object* v___x_2539_; 
v___x_2538_ = lean_nat_add(v_j_2530_, v_one_2534_);
lean_dec(v_j_2530_);
v___x_2539_ = lean_array_push(v_bs_2531_, v___y_2537_);
v_i_2529_ = v_n_2535_;
v_j_2530_ = v___x_2538_;
v_bs_2531_ = v___x_2539_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0___redArg___boxed(lean_object* v_ctorNames_2564_, lean_object* v_us_2565_, lean_object* v_params_2566_, lean_object* v_majorFVarId_2567_, lean_object* v_as_2568_, lean_object* v_i_2569_, lean_object* v_j_2570_, lean_object* v_bs_2571_){
_start:
{
lean_object* v_res_2572_; 
v_res_2572_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0___redArg(v_ctorNames_2564_, v_us_2565_, v_params_2566_, v_majorFVarId_2567_, v_as_2568_, v_i_2569_, v_j_2570_, v_bs_2571_);
lean_dec_ref(v_as_2568_);
lean_dec_ref(v_params_2566_);
lean_dec_ref(v_ctorNames_2564_);
return v_res_2572_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals(lean_object* v_s_2573_, lean_object* v_ctorNames_2574_, lean_object* v_majorFVarId_2575_, lean_object* v_us_2576_, lean_object* v_params_2577_){
_start:
{
lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; 
v___x_2578_ = lean_array_get_size(v_s_2573_);
v___x_2579_ = lean_unsigned_to_nat(0u);
v___x_2580_ = lean_mk_empty_array_with_capacity(v___x_2578_);
v___x_2581_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0___redArg(v_ctorNames_2574_, v_us_2576_, v_params_2577_, v_majorFVarId_2575_, v_s_2573_, v___x_2578_, v___x_2579_, v___x_2580_);
return v___x_2581_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals___boxed(lean_object* v_s_2582_, lean_object* v_ctorNames_2583_, lean_object* v_majorFVarId_2584_, lean_object* v_us_2585_, lean_object* v_params_2586_){
_start:
{
lean_object* v_res_2587_; 
v_res_2587_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals(v_s_2582_, v_ctorNames_2583_, v_majorFVarId_2584_, v_us_2585_, v_params_2586_);
lean_dec_ref(v_params_2586_);
lean_dec_ref(v_ctorNames_2583_);
lean_dec_ref(v_s_2582_);
return v_res_2587_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0(lean_object* v_ctorNames_2588_, lean_object* v_us_2589_, lean_object* v_params_2590_, lean_object* v_majorFVarId_2591_, lean_object* v_as_2592_, lean_object* v_i_2593_, lean_object* v_j_2594_, lean_object* v_inv_2595_, lean_object* v_bs_2596_){
_start:
{
lean_object* v___x_2597_; 
v___x_2597_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0___redArg(v_ctorNames_2588_, v_us_2589_, v_params_2590_, v_majorFVarId_2591_, v_as_2592_, v_i_2593_, v_j_2594_, v_bs_2596_);
return v___x_2597_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0___boxed(lean_object* v_ctorNames_2598_, lean_object* v_us_2599_, lean_object* v_params_2600_, lean_object* v_majorFVarId_2601_, lean_object* v_as_2602_, lean_object* v_i_2603_, lean_object* v_j_2604_, lean_object* v_inv_2605_, lean_object* v_bs_2606_){
_start:
{
lean_object* v_res_2607_; 
v_res_2607_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0(v_ctorNames_2598_, v_us_2599_, v_params_2600_, v_majorFVarId_2601_, v_as_2602_, v_i_2603_, v_j_2604_, v_inv_2605_, v_bs_2606_);
lean_dec_ref(v_as_2602_);
lean_dec_ref(v_params_2600_);
lean_dec_ref(v_ctorNames_2598_);
return v_res_2607_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_2613_; lean_object* v___x_2614_; 
v___x_2613_ = l_Lean_maxRecDepthErrorMessage;
v___x_2614_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2614_, 0, v___x_2613_);
return v___x_2614_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_2615_; lean_object* v___x_2616_; 
v___x_2615_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__3);
v___x_2616_ = l_Lean_MessageData_ofFormat(v___x_2615_);
return v___x_2616_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; 
v___x_2617_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__4);
v___x_2618_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__2));
v___x_2619_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2619_, 0, v___x_2618_);
lean_ctor_set(v___x_2619_, 1, v___x_2617_);
return v___x_2619_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg(lean_object* v_ref_2620_){
_start:
{
lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; 
v___x_2622_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__5);
v___x_2623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2623_, 0, v_ref_2620_);
lean_ctor_set(v___x_2623_, 1, v___x_2622_);
v___x_2624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2624_, 0, v___x_2623_);
return v___x_2624_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___boxed(lean_object* v_ref_2625_, lean_object* v___y_2626_){
_start:
{
lean_object* v_res_2627_; 
v_res_2627_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg(v_ref_2625_);
return v_res_2627_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0(lean_object* v_00_u03b1_2628_, lean_object* v_ref_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_){
_start:
{
lean_object* v___x_2635_; 
v___x_2635_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg(v_ref_2629_);
return v___x_2635_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___boxed(lean_object* v_00_u03b1_2636_, lean_object* v_ref_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_){
_start:
{
lean_object* v_res_2643_; 
v_res_2643_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0(v_00_u03b1_2636_, v_ref_2637_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_);
lean_dec(v___y_2641_);
lean_dec_ref(v___y_2640_);
lean_dec(v___y_2639_);
lean_dec_ref(v___y_2638_);
return v_res_2643_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_unifyEqs_x3f(lean_object* v_numEqs_2645_, lean_object* v_mvarId_2646_, lean_object* v_subst_2647_, lean_object* v_caseName_x3f_2648_, lean_object* v_a_2649_, lean_object* v_a_2650_, lean_object* v_a_2651_, lean_object* v_a_2652_){
_start:
{
lean_object* v_fileName_2654_; lean_object* v_fileMap_2655_; lean_object* v_options_2656_; lean_object* v_currRecDepth_2657_; lean_object* v_maxRecDepth_2658_; lean_object* v_ref_2659_; lean_object* v_currNamespace_2660_; lean_object* v_openDecls_2661_; lean_object* v_initHeartbeats_2662_; lean_object* v_maxHeartbeats_2663_; lean_object* v_quotContext_2664_; lean_object* v_currMacroScope_2665_; uint8_t v_diag_2666_; lean_object* v_cancelTk_x3f_2667_; uint8_t v_suppressElabErrors_2668_; lean_object* v_inheritedTraceOptions_2669_; lean_object* v___x_2671_; uint8_t v_isShared_2672_; uint8_t v_isSharedCheck_2723_; 
v_fileName_2654_ = lean_ctor_get(v_a_2651_, 0);
v_fileMap_2655_ = lean_ctor_get(v_a_2651_, 1);
v_options_2656_ = lean_ctor_get(v_a_2651_, 2);
v_currRecDepth_2657_ = lean_ctor_get(v_a_2651_, 3);
v_maxRecDepth_2658_ = lean_ctor_get(v_a_2651_, 4);
v_ref_2659_ = lean_ctor_get(v_a_2651_, 5);
v_currNamespace_2660_ = lean_ctor_get(v_a_2651_, 6);
v_openDecls_2661_ = lean_ctor_get(v_a_2651_, 7);
v_initHeartbeats_2662_ = lean_ctor_get(v_a_2651_, 8);
v_maxHeartbeats_2663_ = lean_ctor_get(v_a_2651_, 9);
v_quotContext_2664_ = lean_ctor_get(v_a_2651_, 10);
v_currMacroScope_2665_ = lean_ctor_get(v_a_2651_, 11);
v_diag_2666_ = lean_ctor_get_uint8(v_a_2651_, sizeof(void*)*14);
v_cancelTk_x3f_2667_ = lean_ctor_get(v_a_2651_, 12);
v_suppressElabErrors_2668_ = lean_ctor_get_uint8(v_a_2651_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2669_ = lean_ctor_get(v_a_2651_, 13);
v_isSharedCheck_2723_ = !lean_is_exclusive(v_a_2651_);
if (v_isSharedCheck_2723_ == 0)
{
v___x_2671_ = v_a_2651_;
v_isShared_2672_ = v_isSharedCheck_2723_;
goto v_resetjp_2670_;
}
else
{
lean_inc(v_inheritedTraceOptions_2669_);
lean_inc(v_cancelTk_x3f_2667_);
lean_inc(v_currMacroScope_2665_);
lean_inc(v_quotContext_2664_);
lean_inc(v_maxHeartbeats_2663_);
lean_inc(v_initHeartbeats_2662_);
lean_inc(v_openDecls_2661_);
lean_inc(v_currNamespace_2660_);
lean_inc(v_ref_2659_);
lean_inc(v_maxRecDepth_2658_);
lean_inc(v_currRecDepth_2657_);
lean_inc(v_options_2656_);
lean_inc(v_fileMap_2655_);
lean_inc(v_fileName_2654_);
lean_dec(v_a_2651_);
v___x_2671_ = lean_box(0);
v_isShared_2672_ = v_isSharedCheck_2723_;
goto v_resetjp_2670_;
}
v_resetjp_2670_:
{
uint8_t v___x_2673_; 
v___x_2673_ = lean_nat_dec_eq(v_currRecDepth_2657_, v_maxRecDepth_2658_);
if (v___x_2673_ == 0)
{
lean_object* v___x_2674_; uint8_t v___x_2675_; 
v___x_2674_ = lean_unsigned_to_nat(0u);
v___x_2675_ = lean_nat_dec_eq(v_numEqs_2645_, v___x_2674_);
if (v___x_2675_ == 0)
{
lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2679_; 
v___x_2676_ = lean_unsigned_to_nat(1u);
v___x_2677_ = lean_nat_add(v_currRecDepth_2657_, v___x_2676_);
lean_dec(v_currRecDepth_2657_);
if (v_isShared_2672_ == 0)
{
lean_ctor_set(v___x_2671_, 3, v___x_2677_);
v___x_2679_ = v___x_2671_;
goto v_reusejp_2678_;
}
else
{
lean_object* v_reuseFailAlloc_2718_; 
v_reuseFailAlloc_2718_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_2718_, 0, v_fileName_2654_);
lean_ctor_set(v_reuseFailAlloc_2718_, 1, v_fileMap_2655_);
lean_ctor_set(v_reuseFailAlloc_2718_, 2, v_options_2656_);
lean_ctor_set(v_reuseFailAlloc_2718_, 3, v___x_2677_);
lean_ctor_set(v_reuseFailAlloc_2718_, 4, v_maxRecDepth_2658_);
lean_ctor_set(v_reuseFailAlloc_2718_, 5, v_ref_2659_);
lean_ctor_set(v_reuseFailAlloc_2718_, 6, v_currNamespace_2660_);
lean_ctor_set(v_reuseFailAlloc_2718_, 7, v_openDecls_2661_);
lean_ctor_set(v_reuseFailAlloc_2718_, 8, v_initHeartbeats_2662_);
lean_ctor_set(v_reuseFailAlloc_2718_, 9, v_maxHeartbeats_2663_);
lean_ctor_set(v_reuseFailAlloc_2718_, 10, v_quotContext_2664_);
lean_ctor_set(v_reuseFailAlloc_2718_, 11, v_currMacroScope_2665_);
lean_ctor_set(v_reuseFailAlloc_2718_, 12, v_cancelTk_x3f_2667_);
lean_ctor_set(v_reuseFailAlloc_2718_, 13, v_inheritedTraceOptions_2669_);
lean_ctor_set_uint8(v_reuseFailAlloc_2718_, sizeof(void*)*14, v_diag_2666_);
lean_ctor_set_uint8(v_reuseFailAlloc_2718_, sizeof(void*)*14 + 1, v_suppressElabErrors_2668_);
v___x_2679_ = v_reuseFailAlloc_2718_;
goto v_reusejp_2678_;
}
v_reusejp_2678_:
{
lean_object* v___x_2680_; 
lean_inc(v_a_2652_);
lean_inc_ref(v___x_2679_);
lean_inc(v_a_2650_);
lean_inc_ref(v_a_2649_);
v___x_2680_ = l_Lean_Meta_intro1Core(v_mvarId_2646_, v___x_2673_, v_a_2649_, v_a_2650_, v___x_2679_, v_a_2652_);
if (lean_obj_tag(v___x_2680_) == 0)
{
lean_object* v_a_2681_; lean_object* v_fst_2682_; lean_object* v_snd_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; 
v_a_2681_ = lean_ctor_get(v___x_2680_, 0);
lean_inc(v_a_2681_);
lean_dec_ref(v___x_2680_);
v_fst_2682_ = lean_ctor_get(v_a_2681_, 0);
lean_inc(v_fst_2682_);
v_snd_2683_ = lean_ctor_get(v_a_2681_, 1);
lean_inc(v_snd_2683_);
lean_dec(v_a_2681_);
v___x_2684_ = ((lean_object*)(l_Lean_Meta_Cases_unifyEqs_x3f___closed__0));
lean_inc(v_a_2652_);
lean_inc_ref(v___x_2679_);
lean_inc(v_a_2650_);
lean_inc_ref(v_a_2649_);
lean_inc(v_caseName_x3f_2648_);
v___x_2685_ = l_Lean_Meta_unifyEq_x3f(v_snd_2683_, v_fst_2682_, v_subst_2647_, v___x_2684_, v_caseName_x3f_2648_, v_a_2649_, v_a_2650_, v___x_2679_, v_a_2652_);
if (lean_obj_tag(v___x_2685_) == 0)
{
lean_object* v_a_2686_; lean_object* v___x_2688_; uint8_t v_isShared_2689_; uint8_t v_isSharedCheck_2701_; 
v_a_2686_ = lean_ctor_get(v___x_2685_, 0);
v_isSharedCheck_2701_ = !lean_is_exclusive(v___x_2685_);
if (v_isSharedCheck_2701_ == 0)
{
v___x_2688_ = v___x_2685_;
v_isShared_2689_ = v_isSharedCheck_2701_;
goto v_resetjp_2687_;
}
else
{
lean_inc(v_a_2686_);
lean_dec(v___x_2685_);
v___x_2688_ = lean_box(0);
v_isShared_2689_ = v_isSharedCheck_2701_;
goto v_resetjp_2687_;
}
v_resetjp_2687_:
{
if (lean_obj_tag(v_a_2686_) == 1)
{
lean_object* v_val_2690_; lean_object* v_mvarId_2691_; lean_object* v_subst_2692_; lean_object* v_numNewEqs_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; 
lean_del_object(v___x_2688_);
v_val_2690_ = lean_ctor_get(v_a_2686_, 0);
lean_inc(v_val_2690_);
lean_dec_ref(v_a_2686_);
v_mvarId_2691_ = lean_ctor_get(v_val_2690_, 0);
lean_inc(v_mvarId_2691_);
v_subst_2692_ = lean_ctor_get(v_val_2690_, 1);
lean_inc(v_subst_2692_);
v_numNewEqs_2693_ = lean_ctor_get(v_val_2690_, 2);
lean_inc(v_numNewEqs_2693_);
lean_dec(v_val_2690_);
v___x_2694_ = lean_nat_sub(v_numEqs_2645_, v___x_2676_);
lean_dec(v_numEqs_2645_);
v___x_2695_ = lean_nat_add(v___x_2694_, v_numNewEqs_2693_);
lean_dec(v_numNewEqs_2693_);
lean_dec(v___x_2694_);
v_numEqs_2645_ = v___x_2695_;
v_mvarId_2646_ = v_mvarId_2691_;
v_subst_2647_ = v_subst_2692_;
v_a_2651_ = v___x_2679_;
goto _start;
}
else
{
lean_object* v___x_2697_; lean_object* v___x_2699_; 
lean_dec(v_a_2686_);
lean_dec_ref(v___x_2679_);
lean_dec(v_a_2652_);
lean_dec(v_a_2650_);
lean_dec_ref(v_a_2649_);
lean_dec(v_caseName_x3f_2648_);
lean_dec(v_numEqs_2645_);
v___x_2697_ = lean_box(0);
if (v_isShared_2689_ == 0)
{
lean_ctor_set(v___x_2688_, 0, v___x_2697_);
v___x_2699_ = v___x_2688_;
goto v_reusejp_2698_;
}
else
{
lean_object* v_reuseFailAlloc_2700_; 
v_reuseFailAlloc_2700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2700_, 0, v___x_2697_);
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
lean_object* v_a_2702_; lean_object* v___x_2704_; uint8_t v_isShared_2705_; uint8_t v_isSharedCheck_2709_; 
lean_dec_ref(v___x_2679_);
lean_dec(v_a_2652_);
lean_dec(v_a_2650_);
lean_dec_ref(v_a_2649_);
lean_dec(v_caseName_x3f_2648_);
lean_dec(v_numEqs_2645_);
v_a_2702_ = lean_ctor_get(v___x_2685_, 0);
v_isSharedCheck_2709_ = !lean_is_exclusive(v___x_2685_);
if (v_isSharedCheck_2709_ == 0)
{
v___x_2704_ = v___x_2685_;
v_isShared_2705_ = v_isSharedCheck_2709_;
goto v_resetjp_2703_;
}
else
{
lean_inc(v_a_2702_);
lean_dec(v___x_2685_);
v___x_2704_ = lean_box(0);
v_isShared_2705_ = v_isSharedCheck_2709_;
goto v_resetjp_2703_;
}
v_resetjp_2703_:
{
lean_object* v___x_2707_; 
if (v_isShared_2705_ == 0)
{
v___x_2707_ = v___x_2704_;
goto v_reusejp_2706_;
}
else
{
lean_object* v_reuseFailAlloc_2708_; 
v_reuseFailAlloc_2708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2708_, 0, v_a_2702_);
v___x_2707_ = v_reuseFailAlloc_2708_;
goto v_reusejp_2706_;
}
v_reusejp_2706_:
{
return v___x_2707_;
}
}
}
}
else
{
lean_object* v_a_2710_; lean_object* v___x_2712_; uint8_t v_isShared_2713_; uint8_t v_isSharedCheck_2717_; 
lean_dec_ref(v___x_2679_);
lean_dec(v_a_2652_);
lean_dec(v_a_2650_);
lean_dec_ref(v_a_2649_);
lean_dec(v_caseName_x3f_2648_);
lean_dec(v_subst_2647_);
lean_dec(v_numEqs_2645_);
v_a_2710_ = lean_ctor_get(v___x_2680_, 0);
v_isSharedCheck_2717_ = !lean_is_exclusive(v___x_2680_);
if (v_isSharedCheck_2717_ == 0)
{
v___x_2712_ = v___x_2680_;
v_isShared_2713_ = v_isSharedCheck_2717_;
goto v_resetjp_2711_;
}
else
{
lean_inc(v_a_2710_);
lean_dec(v___x_2680_);
v___x_2712_ = lean_box(0);
v_isShared_2713_ = v_isSharedCheck_2717_;
goto v_resetjp_2711_;
}
v_resetjp_2711_:
{
lean_object* v___x_2715_; 
if (v_isShared_2713_ == 0)
{
v___x_2715_ = v___x_2712_;
goto v_reusejp_2714_;
}
else
{
lean_object* v_reuseFailAlloc_2716_; 
v_reuseFailAlloc_2716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2716_, 0, v_a_2710_);
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
lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; 
lean_del_object(v___x_2671_);
lean_dec_ref(v_inheritedTraceOptions_2669_);
lean_dec(v_cancelTk_x3f_2667_);
lean_dec(v_currMacroScope_2665_);
lean_dec(v_quotContext_2664_);
lean_dec(v_maxHeartbeats_2663_);
lean_dec(v_initHeartbeats_2662_);
lean_dec(v_openDecls_2661_);
lean_dec(v_currNamespace_2660_);
lean_dec(v_ref_2659_);
lean_dec(v_maxRecDepth_2658_);
lean_dec(v_currRecDepth_2657_);
lean_dec_ref(v_options_2656_);
lean_dec_ref(v_fileMap_2655_);
lean_dec_ref(v_fileName_2654_);
lean_dec(v_a_2652_);
lean_dec(v_a_2650_);
lean_dec_ref(v_a_2649_);
lean_dec(v_caseName_x3f_2648_);
lean_dec(v_numEqs_2645_);
v___x_2719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2719_, 0, v_mvarId_2646_);
lean_ctor_set(v___x_2719_, 1, v_subst_2647_);
v___x_2720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2720_, 0, v___x_2719_);
v___x_2721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2721_, 0, v___x_2720_);
return v___x_2721_;
}
}
else
{
lean_object* v___x_2722_; 
lean_del_object(v___x_2671_);
lean_dec_ref(v_inheritedTraceOptions_2669_);
lean_dec(v_cancelTk_x3f_2667_);
lean_dec(v_currMacroScope_2665_);
lean_dec(v_quotContext_2664_);
lean_dec(v_maxHeartbeats_2663_);
lean_dec(v_initHeartbeats_2662_);
lean_dec(v_openDecls_2661_);
lean_dec(v_currNamespace_2660_);
lean_dec(v_maxRecDepth_2658_);
lean_dec(v_currRecDepth_2657_);
lean_dec_ref(v_options_2656_);
lean_dec_ref(v_fileMap_2655_);
lean_dec_ref(v_fileName_2654_);
lean_dec(v_a_2652_);
lean_dec(v_a_2650_);
lean_dec_ref(v_a_2649_);
lean_dec(v_caseName_x3f_2648_);
lean_dec(v_subst_2647_);
lean_dec(v_mvarId_2646_);
lean_dec(v_numEqs_2645_);
v___x_2722_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg(v_ref_2659_);
return v___x_2722_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_unifyEqs_x3f___boxed(lean_object* v_numEqs_2724_, lean_object* v_mvarId_2725_, lean_object* v_subst_2726_, lean_object* v_caseName_x3f_2727_, lean_object* v_a_2728_, lean_object* v_a_2729_, lean_object* v_a_2730_, lean_object* v_a_2731_, lean_object* v_a_2732_){
_start:
{
lean_object* v_res_2733_; 
v_res_2733_ = l_Lean_Meta_Cases_unifyEqs_x3f(v_numEqs_2724_, v_mvarId_2725_, v_subst_2726_, v_caseName_x3f_2727_, v_a_2728_, v_a_2729_, v_a_2730_, v_a_2731_);
return v_res_2733_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__0(lean_object* v_snd_2734_, size_t v_sz_2735_, size_t v_i_2736_, lean_object* v_bs_2737_){
_start:
{
uint8_t v___x_2738_; 
v___x_2738_ = lean_usize_dec_lt(v_i_2736_, v_sz_2735_);
if (v___x_2738_ == 0)
{
lean_dec(v_snd_2734_);
return v_bs_2737_;
}
else
{
lean_object* v_v_2739_; lean_object* v___x_2740_; lean_object* v_bs_x27_2741_; lean_object* v___x_2742_; size_t v___x_2743_; size_t v___x_2744_; lean_object* v___x_2745_; 
v_v_2739_ = lean_array_uget(v_bs_2737_, v_i_2736_);
v___x_2740_ = lean_unsigned_to_nat(0u);
v_bs_x27_2741_ = lean_array_uset(v_bs_2737_, v_i_2736_, v___x_2740_);
lean_inc(v_snd_2734_);
v___x_2742_ = l_Lean_Meta_FVarSubst_apply(v_snd_2734_, v_v_2739_);
lean_dec(v_v_2739_);
v___x_2743_ = ((size_t)1ULL);
v___x_2744_ = lean_usize_add(v_i_2736_, v___x_2743_);
v___x_2745_ = lean_array_uset(v_bs_x27_2741_, v_i_2736_, v___x_2742_);
v_i_2736_ = v___x_2744_;
v_bs_2737_ = v___x_2745_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__0___boxed(lean_object* v_snd_2747_, lean_object* v_sz_2748_, lean_object* v_i_2749_, lean_object* v_bs_2750_){
_start:
{
size_t v_sz_boxed_2751_; size_t v_i_boxed_2752_; lean_object* v_res_2753_; 
v_sz_boxed_2751_ = lean_unbox_usize(v_sz_2748_);
lean_dec(v_sz_2748_);
v_i_boxed_2752_ = lean_unbox_usize(v_i_2749_);
lean_dec(v_i_2749_);
v_res_2753_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__0(v_snd_2747_, v_sz_boxed_2751_, v_i_boxed_2752_, v_bs_2750_);
return v_res_2753_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1_spec__1(lean_object* v_numEqs_2754_, lean_object* v_as_2755_, size_t v_i_2756_, size_t v_stop_2757_, lean_object* v_b_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_){
_start:
{
uint8_t v___x_2764_; 
v___x_2764_ = lean_usize_dec_eq(v_i_2756_, v_stop_2757_);
if (v___x_2764_ == 0)
{
lean_object* v___x_2765_; lean_object* v_toInductionSubgoal_2766_; lean_object* v_ctorName_2767_; lean_object* v___x_2769_; uint8_t v_isShared_2770_; uint8_t v_isSharedCheck_2806_; 
v___x_2765_ = lean_array_uget(v_as_2755_, v_i_2756_);
v_toInductionSubgoal_2766_ = lean_ctor_get(v___x_2765_, 0);
v_ctorName_2767_ = lean_ctor_get(v___x_2765_, 1);
v_isSharedCheck_2806_ = !lean_is_exclusive(v___x_2765_);
if (v_isSharedCheck_2806_ == 0)
{
v___x_2769_ = v___x_2765_;
v_isShared_2770_ = v_isSharedCheck_2806_;
goto v_resetjp_2768_;
}
else
{
lean_inc(v_ctorName_2767_);
lean_inc(v_toInductionSubgoal_2766_);
lean_dec(v___x_2765_);
v___x_2769_ = lean_box(0);
v_isShared_2770_ = v_isSharedCheck_2806_;
goto v_resetjp_2768_;
}
v_resetjp_2768_:
{
lean_object* v_mvarId_2771_; lean_object* v_fields_2772_; lean_object* v_subst_2773_; lean_object* v___x_2775_; uint8_t v_isShared_2776_; uint8_t v_isSharedCheck_2805_; 
v_mvarId_2771_ = lean_ctor_get(v_toInductionSubgoal_2766_, 0);
v_fields_2772_ = lean_ctor_get(v_toInductionSubgoal_2766_, 1);
v_subst_2773_ = lean_ctor_get(v_toInductionSubgoal_2766_, 2);
v_isSharedCheck_2805_ = !lean_is_exclusive(v_toInductionSubgoal_2766_);
if (v_isSharedCheck_2805_ == 0)
{
v___x_2775_ = v_toInductionSubgoal_2766_;
v_isShared_2776_ = v_isSharedCheck_2805_;
goto v_resetjp_2774_;
}
else
{
lean_inc(v_subst_2773_);
lean_inc(v_fields_2772_);
lean_inc(v_mvarId_2771_);
lean_dec(v_toInductionSubgoal_2766_);
v___x_2775_ = lean_box(0);
v_isShared_2776_ = v_isSharedCheck_2805_;
goto v_resetjp_2774_;
}
v_resetjp_2774_:
{
lean_object* v___x_2777_; 
lean_inc(v___y_2762_);
lean_inc_ref(v___y_2761_);
lean_inc(v___y_2760_);
lean_inc_ref(v___y_2759_);
lean_inc(v_ctorName_2767_);
lean_inc(v_numEqs_2754_);
v___x_2777_ = l_Lean_Meta_Cases_unifyEqs_x3f(v_numEqs_2754_, v_mvarId_2771_, v_subst_2773_, v_ctorName_2767_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_);
if (lean_obj_tag(v___x_2777_) == 0)
{
lean_object* v_a_2778_; lean_object* v_a_2780_; 
v_a_2778_ = lean_ctor_get(v___x_2777_, 0);
lean_inc(v_a_2778_);
lean_dec_ref(v___x_2777_);
if (lean_obj_tag(v_a_2778_) == 0)
{
lean_del_object(v___x_2775_);
lean_dec_ref(v_fields_2772_);
lean_del_object(v___x_2769_);
lean_dec(v_ctorName_2767_);
v_a_2780_ = v_b_2758_;
goto v___jp_2779_;
}
else
{
lean_object* v_val_2784_; lean_object* v_fst_2785_; lean_object* v_snd_2786_; size_t v_sz_2787_; size_t v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2791_; 
v_val_2784_ = lean_ctor_get(v_a_2778_, 0);
lean_inc(v_val_2784_);
lean_dec_ref(v_a_2778_);
v_fst_2785_ = lean_ctor_get(v_val_2784_, 0);
lean_inc(v_fst_2785_);
v_snd_2786_ = lean_ctor_get(v_val_2784_, 1);
lean_inc(v_snd_2786_);
lean_dec(v_val_2784_);
v_sz_2787_ = lean_array_size(v_fields_2772_);
v___x_2788_ = ((size_t)0ULL);
lean_inc(v_snd_2786_);
v___x_2789_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__0(v_snd_2786_, v_sz_2787_, v___x_2788_, v_fields_2772_);
if (v_isShared_2776_ == 0)
{
lean_ctor_set(v___x_2775_, 2, v_snd_2786_);
lean_ctor_set(v___x_2775_, 1, v___x_2789_);
lean_ctor_set(v___x_2775_, 0, v_fst_2785_);
v___x_2791_ = v___x_2775_;
goto v_reusejp_2790_;
}
else
{
lean_object* v_reuseFailAlloc_2796_; 
v_reuseFailAlloc_2796_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2796_, 0, v_fst_2785_);
lean_ctor_set(v_reuseFailAlloc_2796_, 1, v___x_2789_);
lean_ctor_set(v_reuseFailAlloc_2796_, 2, v_snd_2786_);
v___x_2791_ = v_reuseFailAlloc_2796_;
goto v_reusejp_2790_;
}
v_reusejp_2790_:
{
lean_object* v___x_2793_; 
if (v_isShared_2770_ == 0)
{
lean_ctor_set(v___x_2769_, 0, v___x_2791_);
v___x_2793_ = v___x_2769_;
goto v_reusejp_2792_;
}
else
{
lean_object* v_reuseFailAlloc_2795_; 
v_reuseFailAlloc_2795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2795_, 0, v___x_2791_);
lean_ctor_set(v_reuseFailAlloc_2795_, 1, v_ctorName_2767_);
v___x_2793_ = v_reuseFailAlloc_2795_;
goto v_reusejp_2792_;
}
v_reusejp_2792_:
{
lean_object* v___x_2794_; 
v___x_2794_ = lean_array_push(v_b_2758_, v___x_2793_);
v_a_2780_ = v___x_2794_;
goto v___jp_2779_;
}
}
}
v___jp_2779_:
{
size_t v___x_2781_; size_t v___x_2782_; 
v___x_2781_ = ((size_t)1ULL);
v___x_2782_ = lean_usize_add(v_i_2756_, v___x_2781_);
v_i_2756_ = v___x_2782_;
v_b_2758_ = v_a_2780_;
goto _start;
}
}
else
{
lean_object* v_a_2797_; lean_object* v___x_2799_; uint8_t v_isShared_2800_; uint8_t v_isSharedCheck_2804_; 
lean_del_object(v___x_2775_);
lean_dec_ref(v_fields_2772_);
lean_del_object(v___x_2769_);
lean_dec(v_ctorName_2767_);
lean_dec(v___y_2762_);
lean_dec_ref(v___y_2761_);
lean_dec(v___y_2760_);
lean_dec_ref(v___y_2759_);
lean_dec_ref(v_b_2758_);
lean_dec(v_numEqs_2754_);
v_a_2797_ = lean_ctor_get(v___x_2777_, 0);
v_isSharedCheck_2804_ = !lean_is_exclusive(v___x_2777_);
if (v_isSharedCheck_2804_ == 0)
{
v___x_2799_ = v___x_2777_;
v_isShared_2800_ = v_isSharedCheck_2804_;
goto v_resetjp_2798_;
}
else
{
lean_inc(v_a_2797_);
lean_dec(v___x_2777_);
v___x_2799_ = lean_box(0);
v_isShared_2800_ = v_isSharedCheck_2804_;
goto v_resetjp_2798_;
}
v_resetjp_2798_:
{
lean_object* v___x_2802_; 
if (v_isShared_2800_ == 0)
{
v___x_2802_ = v___x_2799_;
goto v_reusejp_2801_;
}
else
{
lean_object* v_reuseFailAlloc_2803_; 
v_reuseFailAlloc_2803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2803_, 0, v_a_2797_);
v___x_2802_ = v_reuseFailAlloc_2803_;
goto v_reusejp_2801_;
}
v_reusejp_2801_:
{
return v___x_2802_;
}
}
}
}
}
}
else
{
lean_object* v___x_2807_; 
lean_dec(v___y_2762_);
lean_dec_ref(v___y_2761_);
lean_dec(v___y_2760_);
lean_dec_ref(v___y_2759_);
lean_dec(v_numEqs_2754_);
v___x_2807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2807_, 0, v_b_2758_);
return v___x_2807_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1_spec__1___boxed(lean_object* v_numEqs_2808_, lean_object* v_as_2809_, lean_object* v_i_2810_, lean_object* v_stop_2811_, lean_object* v_b_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_){
_start:
{
size_t v_i_boxed_2818_; size_t v_stop_boxed_2819_; lean_object* v_res_2820_; 
v_i_boxed_2818_ = lean_unbox_usize(v_i_2810_);
lean_dec(v_i_2810_);
v_stop_boxed_2819_ = lean_unbox_usize(v_stop_2811_);
lean_dec(v_stop_2811_);
v_res_2820_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1_spec__1(v_numEqs_2808_, v_as_2809_, v_i_boxed_2818_, v_stop_boxed_2819_, v_b_2812_, v___y_2813_, v___y_2814_, v___y_2815_, v___y_2816_);
lean_dec_ref(v_as_2809_);
return v_res_2820_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1(lean_object* v_numEqs_2823_, lean_object* v_as_2824_, lean_object* v_start_2825_, lean_object* v_stop_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_){
_start:
{
lean_object* v___x_2832_; uint8_t v___x_2833_; 
v___x_2832_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1___closed__0));
v___x_2833_ = lean_nat_dec_lt(v_start_2825_, v_stop_2826_);
if (v___x_2833_ == 0)
{
lean_object* v___x_2834_; 
lean_dec(v___y_2830_);
lean_dec_ref(v___y_2829_);
lean_dec(v___y_2828_);
lean_dec_ref(v___y_2827_);
lean_dec(v_numEqs_2823_);
v___x_2834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2834_, 0, v___x_2832_);
return v___x_2834_;
}
else
{
lean_object* v___x_2835_; uint8_t v___x_2836_; 
v___x_2835_ = lean_array_get_size(v_as_2824_);
v___x_2836_ = lean_nat_dec_le(v_stop_2826_, v___x_2835_);
if (v___x_2836_ == 0)
{
uint8_t v___x_2837_; 
v___x_2837_ = lean_nat_dec_lt(v_start_2825_, v___x_2835_);
if (v___x_2837_ == 0)
{
lean_object* v___x_2838_; 
lean_dec(v___y_2830_);
lean_dec_ref(v___y_2829_);
lean_dec(v___y_2828_);
lean_dec_ref(v___y_2827_);
lean_dec(v_numEqs_2823_);
v___x_2838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2838_, 0, v___x_2832_);
return v___x_2838_;
}
else
{
size_t v___x_2839_; size_t v___x_2840_; lean_object* v___x_2841_; 
v___x_2839_ = lean_usize_of_nat(v_start_2825_);
v___x_2840_ = lean_usize_of_nat(v___x_2835_);
v___x_2841_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1_spec__1(v_numEqs_2823_, v_as_2824_, v___x_2839_, v___x_2840_, v___x_2832_, v___y_2827_, v___y_2828_, v___y_2829_, v___y_2830_);
return v___x_2841_;
}
}
else
{
size_t v___x_2842_; size_t v___x_2843_; lean_object* v___x_2844_; 
v___x_2842_ = lean_usize_of_nat(v_start_2825_);
v___x_2843_ = lean_usize_of_nat(v_stop_2826_);
v___x_2844_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1_spec__1(v_numEqs_2823_, v_as_2824_, v___x_2842_, v___x_2843_, v___x_2832_, v___y_2827_, v___y_2828_, v___y_2829_, v___y_2830_);
return v___x_2844_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1___boxed(lean_object* v_numEqs_2845_, lean_object* v_as_2846_, lean_object* v_start_2847_, lean_object* v_stop_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_){
_start:
{
lean_object* v_res_2854_; 
v_res_2854_ = l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1(v_numEqs_2845_, v_as_2846_, v_start_2847_, v_stop_2848_, v___y_2849_, v___y_2850_, v___y_2851_, v___y_2852_);
lean_dec(v_stop_2848_);
lean_dec(v_start_2847_);
lean_dec_ref(v_as_2846_);
return v_res_2854_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs(lean_object* v_numEqs_2855_, lean_object* v_subgoals_2856_, lean_object* v_a_2857_, lean_object* v_a_2858_, lean_object* v_a_2859_, lean_object* v_a_2860_){
_start:
{
lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; 
v___x_2862_ = lean_unsigned_to_nat(0u);
v___x_2863_ = lean_array_get_size(v_subgoals_2856_);
v___x_2864_ = l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1(v_numEqs_2855_, v_subgoals_2856_, v___x_2862_, v___x_2863_, v_a_2857_, v_a_2858_, v_a_2859_, v_a_2860_);
return v___x_2864_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs___boxed(lean_object* v_numEqs_2865_, lean_object* v_subgoals_2866_, lean_object* v_a_2867_, lean_object* v_a_2868_, lean_object* v_a_2869_, lean_object* v_a_2870_, lean_object* v_a_2871_){
_start:
{
lean_object* v_res_2872_; 
v_res_2872_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs(v_numEqs_2865_, v_subgoals_2866_, v_a_2867_, v_a_2868_, v_a_2869_, v_a_2870_);
lean_dec_ref(v_subgoals_2866_);
return v_res_2872_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0(lean_object* v___x_2884_, lean_object* v_mvarId_2885_, lean_object* v_majorFVarId_2886_, lean_object* v_givenNames_2887_, lean_object* v_ctx_2888_, uint8_t v_useNatCasesAuxOn_2889_, lean_object* v_interestingCtors_x3f_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_){
_start:
{
lean_object* v___x_2896_; 
lean_inc(v___y_2894_);
lean_inc_ref(v___y_2893_);
lean_inc(v___y_2892_);
lean_inc_ref(v___y_2891_);
v___x_2896_ = lean_infer_type(v___x_2884_, v___y_2891_, v___y_2892_, v___y_2893_, v___y_2894_);
if (lean_obj_tag(v___x_2896_) == 0)
{
lean_object* v_a_2897_; lean_object* v___x_2898_; 
v_a_2897_ = lean_ctor_get(v___x_2896_, 0);
lean_inc(v_a_2897_);
lean_dec_ref(v___x_2896_);
lean_inc(v___y_2894_);
lean_inc_ref(v___y_2893_);
lean_inc(v___y_2892_);
lean_inc_ref(v___y_2891_);
v___x_2898_ = l_Lean_Meta_getInductiveUniverseAndParams(v_a_2897_, v___y_2891_, v___y_2892_, v___y_2893_, v___y_2894_);
if (lean_obj_tag(v___x_2898_) == 0)
{
lean_object* v_a_2899_; lean_object* v_fst_2900_; lean_object* v_snd_2901_; lean_object* v___y_2903_; lean_object* v___y_2904_; lean_object* v___y_2905_; lean_object* v___y_2906_; lean_object* v___y_2907_; lean_object* v___y_2930_; lean_object* v___y_2931_; lean_object* v___y_2932_; lean_object* v___y_2933_; lean_object* v___y_2939_; lean_object* v___y_2940_; lean_object* v___y_2941_; lean_object* v___y_2942_; 
v_a_2899_ = lean_ctor_get(v___x_2898_, 0);
lean_inc(v_a_2899_);
lean_dec_ref(v___x_2898_);
v_fst_2900_ = lean_ctor_get(v_a_2899_, 0);
lean_inc(v_fst_2900_);
v_snd_2901_ = lean_ctor_get(v_a_2899_, 1);
lean_inc(v_snd_2901_);
lean_dec(v_a_2899_);
if (lean_obj_tag(v_interestingCtors_x3f_2890_) == 1)
{
lean_object* v_val_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v_inductiveVal_2955_; lean_object* v_toConstantVal_2956_; lean_object* v_env_2957_; lean_object* v_ctors_2958_; lean_object* v_name_2959_; uint8_t v___y_2961_; lean_object* v___x_2995_; uint8_t v___x_2996_; uint8_t v___x_2997_; 
v_val_2952_ = lean_ctor_get(v_interestingCtors_x3f_2890_, 0);
lean_inc(v_val_2952_);
lean_dec_ref(v_interestingCtors_x3f_2890_);
v___x_2953_ = lean_st_ref_get(v___y_2894_);
v___x_2954_ = lean_st_ref_get(v___y_2894_);
v_inductiveVal_2955_ = lean_ctor_get(v_ctx_2888_, 0);
v_toConstantVal_2956_ = lean_ctor_get(v_inductiveVal_2955_, 0);
v_env_2957_ = lean_ctor_get(v___x_2953_, 0);
lean_inc_ref(v_env_2957_);
lean_dec(v___x_2953_);
v_ctors_2958_ = lean_ctor_get(v_inductiveVal_2955_, 4);
v_name_2959_ = lean_ctor_get(v_toConstantVal_2956_, 0);
v___x_2995_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__5));
v___x_2996_ = 1;
v___x_2997_ = l_Lean_Environment_contains(v_env_2957_, v___x_2995_, v___x_2996_);
if (v___x_2997_ == 0)
{
lean_dec(v___x_2954_);
v___y_2961_ = v___x_2997_;
goto v___jp_2960_;
}
else
{
lean_object* v_env_2998_; lean_object* v___x_2999_; uint8_t v___x_3000_; 
v_env_2998_ = lean_ctor_get(v___x_2954_, 0);
lean_inc_ref(v_env_2998_);
lean_dec(v___x_2954_);
lean_inc(v_name_2959_);
v___x_2999_ = l_mkCtorIdxName(v_name_2959_);
v___x_3000_ = l_Lean_Environment_contains(v_env_2998_, v___x_2999_, v___x_2996_);
v___y_2961_ = v___x_3000_;
goto v___jp_2960_;
}
v___jp_2960_:
{
if (v___y_2961_ == 0)
{
lean_dec(v_val_2952_);
v___y_2939_ = v___y_2891_;
v___y_2940_ = v___y_2892_;
v___y_2941_ = v___y_2893_;
v___y_2942_ = v___y_2894_;
goto v___jp_2938_;
}
else
{
lean_object* v___x_2962_; lean_object* v___x_2963_; uint8_t v___x_2964_; 
v___x_2962_ = lean_array_get_size(v_val_2952_);
v___x_2963_ = lean_unsigned_to_nat(0u);
v___x_2964_ = lean_nat_dec_eq(v___x_2962_, v___x_2963_);
if (v___x_2964_ == 0)
{
lean_object* v___x_2965_; uint8_t v___x_2966_; 
v___x_2965_ = l_List_lengthTR___redArg(v_ctors_2958_);
v___x_2966_ = lean_nat_dec_lt(v___x_2962_, v___x_2965_);
lean_dec(v___x_2965_);
if (v___x_2966_ == 0)
{
lean_dec(v_val_2952_);
v___y_2939_ = v___y_2891_;
v___y_2940_ = v___y_2892_;
v___y_2941_ = v___y_2893_;
v___y_2942_ = v___y_2894_;
goto v___jp_2938_;
}
else
{
lean_object* v___x_2967_; 
lean_inc(v_name_2959_);
lean_dec_ref(v_ctx_2888_);
lean_inc(v___y_2894_);
lean_inc_ref(v___y_2893_);
lean_inc(v___y_2892_);
lean_inc_ref(v___y_2891_);
lean_inc(v_val_2952_);
v___x_2967_ = l_Lean_Meta_mkSparseCasesOn(v_name_2959_, v_val_2952_, v___y_2891_, v___y_2892_, v___y_2893_, v___y_2894_);
if (lean_obj_tag(v___x_2967_) == 0)
{
lean_object* v_a_2968_; lean_object* v___x_2969_; 
v_a_2968_ = lean_ctor_get(v___x_2967_, 0);
lean_inc(v_a_2968_);
lean_dec_ref(v___x_2967_);
lean_inc(v_majorFVarId_2886_);
v___x_2969_ = l_Lean_MVarId_induction(v_mvarId_2885_, v_majorFVarId_2886_, v_a_2968_, v_givenNames_2887_, v___y_2891_, v___y_2892_, v___y_2893_, v___y_2894_);
if (lean_obj_tag(v___x_2969_) == 0)
{
lean_object* v_a_2970_; lean_object* v___x_2972_; uint8_t v_isShared_2973_; uint8_t v_isSharedCheck_2978_; 
v_a_2970_ = lean_ctor_get(v___x_2969_, 0);
v_isSharedCheck_2978_ = !lean_is_exclusive(v___x_2969_);
if (v_isSharedCheck_2978_ == 0)
{
v___x_2972_ = v___x_2969_;
v_isShared_2973_ = v_isSharedCheck_2978_;
goto v_resetjp_2971_;
}
else
{
lean_inc(v_a_2970_);
lean_dec(v___x_2969_);
v___x_2972_ = lean_box(0);
v_isShared_2973_ = v_isSharedCheck_2978_;
goto v_resetjp_2971_;
}
v_resetjp_2971_:
{
lean_object* v___x_2974_; lean_object* v___x_2976_; 
v___x_2974_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals(v_a_2970_, v_val_2952_, v_majorFVarId_2886_, v_fst_2900_, v_snd_2901_);
lean_dec(v_snd_2901_);
lean_dec(v_val_2952_);
lean_dec(v_a_2970_);
if (v_isShared_2973_ == 0)
{
lean_ctor_set(v___x_2972_, 0, v___x_2974_);
v___x_2976_ = v___x_2972_;
goto v_reusejp_2975_;
}
else
{
lean_object* v_reuseFailAlloc_2977_; 
v_reuseFailAlloc_2977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2977_, 0, v___x_2974_);
v___x_2976_ = v_reuseFailAlloc_2977_;
goto v_reusejp_2975_;
}
v_reusejp_2975_:
{
return v___x_2976_;
}
}
}
else
{
lean_object* v_a_2979_; lean_object* v___x_2981_; uint8_t v_isShared_2982_; uint8_t v_isSharedCheck_2986_; 
lean_dec(v_val_2952_);
lean_dec(v_snd_2901_);
lean_dec(v_fst_2900_);
lean_dec(v_majorFVarId_2886_);
v_a_2979_ = lean_ctor_get(v___x_2969_, 0);
v_isSharedCheck_2986_ = !lean_is_exclusive(v___x_2969_);
if (v_isSharedCheck_2986_ == 0)
{
v___x_2981_ = v___x_2969_;
v_isShared_2982_ = v_isSharedCheck_2986_;
goto v_resetjp_2980_;
}
else
{
lean_inc(v_a_2979_);
lean_dec(v___x_2969_);
v___x_2981_ = lean_box(0);
v_isShared_2982_ = v_isSharedCheck_2986_;
goto v_resetjp_2980_;
}
v_resetjp_2980_:
{
lean_object* v___x_2984_; 
if (v_isShared_2982_ == 0)
{
v___x_2984_ = v___x_2981_;
goto v_reusejp_2983_;
}
else
{
lean_object* v_reuseFailAlloc_2985_; 
v_reuseFailAlloc_2985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2985_, 0, v_a_2979_);
v___x_2984_ = v_reuseFailAlloc_2985_;
goto v_reusejp_2983_;
}
v_reusejp_2983_:
{
return v___x_2984_;
}
}
}
}
else
{
lean_object* v_a_2987_; lean_object* v___x_2989_; uint8_t v_isShared_2990_; uint8_t v_isSharedCheck_2994_; 
lean_dec(v_val_2952_);
lean_dec(v_snd_2901_);
lean_dec(v_fst_2900_);
lean_dec(v___y_2894_);
lean_dec_ref(v___y_2893_);
lean_dec(v___y_2892_);
lean_dec_ref(v___y_2891_);
lean_dec_ref(v_givenNames_2887_);
lean_dec(v_majorFVarId_2886_);
lean_dec(v_mvarId_2885_);
v_a_2987_ = lean_ctor_get(v___x_2967_, 0);
v_isSharedCheck_2994_ = !lean_is_exclusive(v___x_2967_);
if (v_isSharedCheck_2994_ == 0)
{
v___x_2989_ = v___x_2967_;
v_isShared_2990_ = v_isSharedCheck_2994_;
goto v_resetjp_2988_;
}
else
{
lean_inc(v_a_2987_);
lean_dec(v___x_2967_);
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
}
else
{
lean_dec(v_val_2952_);
v___y_2939_ = v___y_2891_;
v___y_2940_ = v___y_2892_;
v___y_2941_ = v___y_2893_;
v___y_2942_ = v___y_2894_;
goto v___jp_2938_;
}
}
}
}
else
{
lean_dec(v_interestingCtors_x3f_2890_);
v___y_2939_ = v___y_2891_;
v___y_2940_ = v___y_2892_;
v___y_2941_ = v___y_2893_;
v___y_2942_ = v___y_2894_;
goto v___jp_2938_;
}
v___jp_2902_:
{
lean_object* v___x_2908_; 
lean_inc(v_majorFVarId_2886_);
v___x_2908_ = l_Lean_MVarId_induction(v_mvarId_2885_, v_majorFVarId_2886_, v___y_2907_, v_givenNames_2887_, v___y_2906_, v___y_2904_, v___y_2903_, v___y_2905_);
if (lean_obj_tag(v___x_2908_) == 0)
{
lean_object* v_inductiveVal_2909_; lean_object* v_a_2910_; lean_object* v___x_2912_; uint8_t v_isShared_2913_; uint8_t v_isSharedCheck_2920_; 
v_inductiveVal_2909_ = lean_ctor_get(v_ctx_2888_, 0);
lean_inc_ref(v_inductiveVal_2909_);
lean_dec_ref(v_ctx_2888_);
v_a_2910_ = lean_ctor_get(v___x_2908_, 0);
v_isSharedCheck_2920_ = !lean_is_exclusive(v___x_2908_);
if (v_isSharedCheck_2920_ == 0)
{
v___x_2912_ = v___x_2908_;
v_isShared_2913_ = v_isSharedCheck_2920_;
goto v_resetjp_2911_;
}
else
{
lean_inc(v_a_2910_);
lean_dec(v___x_2908_);
v___x_2912_ = lean_box(0);
v_isShared_2913_ = v_isSharedCheck_2920_;
goto v_resetjp_2911_;
}
v_resetjp_2911_:
{
lean_object* v_ctors_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2918_; 
v_ctors_2914_ = lean_ctor_get(v_inductiveVal_2909_, 4);
lean_inc(v_ctors_2914_);
lean_dec_ref(v_inductiveVal_2909_);
v___x_2915_ = lean_array_mk(v_ctors_2914_);
v___x_2916_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals(v_a_2910_, v___x_2915_, v_majorFVarId_2886_, v_fst_2900_, v_snd_2901_);
lean_dec(v_snd_2901_);
lean_dec_ref(v___x_2915_);
lean_dec(v_a_2910_);
if (v_isShared_2913_ == 0)
{
lean_ctor_set(v___x_2912_, 0, v___x_2916_);
v___x_2918_ = v___x_2912_;
goto v_reusejp_2917_;
}
else
{
lean_object* v_reuseFailAlloc_2919_; 
v_reuseFailAlloc_2919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2919_, 0, v___x_2916_);
v___x_2918_ = v_reuseFailAlloc_2919_;
goto v_reusejp_2917_;
}
v_reusejp_2917_:
{
return v___x_2918_;
}
}
}
else
{
lean_object* v_a_2921_; lean_object* v___x_2923_; uint8_t v_isShared_2924_; uint8_t v_isSharedCheck_2928_; 
lean_dec(v_snd_2901_);
lean_dec(v_fst_2900_);
lean_dec_ref(v_ctx_2888_);
lean_dec(v_majorFVarId_2886_);
v_a_2921_ = lean_ctor_get(v___x_2908_, 0);
v_isSharedCheck_2928_ = !lean_is_exclusive(v___x_2908_);
if (v_isSharedCheck_2928_ == 0)
{
v___x_2923_ = v___x_2908_;
v_isShared_2924_ = v_isSharedCheck_2928_;
goto v_resetjp_2922_;
}
else
{
lean_inc(v_a_2921_);
lean_dec(v___x_2908_);
v___x_2923_ = lean_box(0);
v_isShared_2924_ = v_isSharedCheck_2928_;
goto v_resetjp_2922_;
}
v_resetjp_2922_:
{
lean_object* v___x_2926_; 
if (v_isShared_2924_ == 0)
{
v___x_2926_ = v___x_2923_;
goto v_reusejp_2925_;
}
else
{
lean_object* v_reuseFailAlloc_2927_; 
v_reuseFailAlloc_2927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2927_, 0, v_a_2921_);
v___x_2926_ = v_reuseFailAlloc_2927_;
goto v_reusejp_2925_;
}
v_reusejp_2925_:
{
return v___x_2926_;
}
}
}
}
v___jp_2929_:
{
lean_object* v_inductiveVal_2934_; lean_object* v_toConstantVal_2935_; lean_object* v_name_2936_; lean_object* v___x_2937_; 
v_inductiveVal_2934_ = lean_ctor_get(v_ctx_2888_, 0);
v_toConstantVal_2935_ = lean_ctor_get(v_inductiveVal_2934_, 0);
v_name_2936_ = lean_ctor_get(v_toConstantVal_2935_, 0);
lean_inc(v_name_2936_);
v___x_2937_ = l_Lean_mkCasesOnName(v_name_2936_);
v___y_2903_ = v___y_2930_;
v___y_2904_ = v___y_2931_;
v___y_2905_ = v___y_2932_;
v___y_2906_ = v___y_2933_;
v___y_2907_ = v___x_2937_;
goto v___jp_2902_;
}
v___jp_2938_:
{
lean_object* v___x_2943_; 
v___x_2943_ = lean_st_ref_get(v___y_2942_);
if (v_useNatCasesAuxOn_2889_ == 0)
{
lean_dec(v___x_2943_);
v___y_2930_ = v___y_2941_;
v___y_2931_ = v___y_2940_;
v___y_2932_ = v___y_2942_;
v___y_2933_ = v___y_2939_;
goto v___jp_2929_;
}
else
{
lean_object* v_inductiveVal_2944_; lean_object* v_toConstantVal_2945_; lean_object* v_env_2946_; lean_object* v_name_2947_; lean_object* v___x_2948_; uint8_t v___x_2949_; 
v_inductiveVal_2944_ = lean_ctor_get(v_ctx_2888_, 0);
v_toConstantVal_2945_ = lean_ctor_get(v_inductiveVal_2944_, 0);
v_env_2946_ = lean_ctor_get(v___x_2943_, 0);
lean_inc_ref(v_env_2946_);
lean_dec(v___x_2943_);
v_name_2947_ = lean_ctor_get(v_toConstantVal_2945_, 0);
v___x_2948_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__1));
v___x_2949_ = lean_name_eq(v_name_2947_, v___x_2948_);
if (v___x_2949_ == 0)
{
lean_dec_ref(v_env_2946_);
v___y_2930_ = v___y_2941_;
v___y_2931_ = v___y_2940_;
v___y_2932_ = v___y_2942_;
v___y_2933_ = v___y_2939_;
goto v___jp_2929_;
}
else
{
lean_object* v___x_2950_; uint8_t v___x_2951_; 
v___x_2950_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__3));
v___x_2951_ = l_Lean_Environment_contains(v_env_2946_, v___x_2950_, v___x_2949_);
if (v___x_2951_ == 0)
{
v___y_2930_ = v___y_2941_;
v___y_2931_ = v___y_2940_;
v___y_2932_ = v___y_2942_;
v___y_2933_ = v___y_2939_;
goto v___jp_2929_;
}
else
{
v___y_2903_ = v___y_2941_;
v___y_2904_ = v___y_2940_;
v___y_2905_ = v___y_2942_;
v___y_2906_ = v___y_2939_;
v___y_2907_ = v___x_2950_;
goto v___jp_2902_;
}
}
}
}
}
else
{
lean_object* v_a_3001_; lean_object* v___x_3003_; uint8_t v_isShared_3004_; uint8_t v_isSharedCheck_3008_; 
lean_dec(v___y_2894_);
lean_dec_ref(v___y_2893_);
lean_dec(v___y_2892_);
lean_dec_ref(v___y_2891_);
lean_dec(v_interestingCtors_x3f_2890_);
lean_dec_ref(v_ctx_2888_);
lean_dec_ref(v_givenNames_2887_);
lean_dec(v_majorFVarId_2886_);
lean_dec(v_mvarId_2885_);
v_a_3001_ = lean_ctor_get(v___x_2898_, 0);
v_isSharedCheck_3008_ = !lean_is_exclusive(v___x_2898_);
if (v_isSharedCheck_3008_ == 0)
{
v___x_3003_ = v___x_2898_;
v_isShared_3004_ = v_isSharedCheck_3008_;
goto v_resetjp_3002_;
}
else
{
lean_inc(v_a_3001_);
lean_dec(v___x_2898_);
v___x_3003_ = lean_box(0);
v_isShared_3004_ = v_isSharedCheck_3008_;
goto v_resetjp_3002_;
}
v_resetjp_3002_:
{
lean_object* v___x_3006_; 
if (v_isShared_3004_ == 0)
{
v___x_3006_ = v___x_3003_;
goto v_reusejp_3005_;
}
else
{
lean_object* v_reuseFailAlloc_3007_; 
v_reuseFailAlloc_3007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3007_, 0, v_a_3001_);
v___x_3006_ = v_reuseFailAlloc_3007_;
goto v_reusejp_3005_;
}
v_reusejp_3005_:
{
return v___x_3006_;
}
}
}
}
else
{
lean_object* v_a_3009_; lean_object* v___x_3011_; uint8_t v_isShared_3012_; uint8_t v_isSharedCheck_3016_; 
lean_dec(v___y_2894_);
lean_dec_ref(v___y_2893_);
lean_dec(v___y_2892_);
lean_dec_ref(v___y_2891_);
lean_dec(v_interestingCtors_x3f_2890_);
lean_dec_ref(v_ctx_2888_);
lean_dec_ref(v_givenNames_2887_);
lean_dec(v_majorFVarId_2886_);
lean_dec(v_mvarId_2885_);
v_a_3009_ = lean_ctor_get(v___x_2896_, 0);
v_isSharedCheck_3016_ = !lean_is_exclusive(v___x_2896_);
if (v_isSharedCheck_3016_ == 0)
{
v___x_3011_ = v___x_2896_;
v_isShared_3012_ = v_isSharedCheck_3016_;
goto v_resetjp_3010_;
}
else
{
lean_inc(v_a_3009_);
lean_dec(v___x_2896_);
v___x_3011_ = lean_box(0);
v_isShared_3012_ = v_isSharedCheck_3016_;
goto v_resetjp_3010_;
}
v_resetjp_3010_:
{
lean_object* v___x_3014_; 
if (v_isShared_3012_ == 0)
{
v___x_3014_ = v___x_3011_;
goto v_reusejp_3013_;
}
else
{
lean_object* v_reuseFailAlloc_3015_; 
v_reuseFailAlloc_3015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3015_, 0, v_a_3009_);
v___x_3014_ = v_reuseFailAlloc_3015_;
goto v_reusejp_3013_;
}
v_reusejp_3013_:
{
return v___x_3014_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___boxed(lean_object* v___x_3017_, lean_object* v_mvarId_3018_, lean_object* v_majorFVarId_3019_, lean_object* v_givenNames_3020_, lean_object* v_ctx_3021_, lean_object* v_useNatCasesAuxOn_3022_, lean_object* v_interestingCtors_x3f_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_){
_start:
{
uint8_t v_useNatCasesAuxOn_boxed_3029_; lean_object* v_res_3030_; 
v_useNatCasesAuxOn_boxed_3029_ = lean_unbox(v_useNatCasesAuxOn_3022_);
v_res_3030_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0(v___x_3017_, v_mvarId_3018_, v_majorFVarId_3019_, v_givenNames_3020_, v_ctx_3021_, v_useNatCasesAuxOn_boxed_3029_, v_interestingCtors_x3f_3023_, v___y_3024_, v___y_3025_, v___y_3026_, v___y_3027_);
return v_res_3030_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn(lean_object* v_mvarId_3031_, lean_object* v_majorFVarId_3032_, lean_object* v_givenNames_3033_, lean_object* v_ctx_3034_, uint8_t v_useNatCasesAuxOn_3035_, lean_object* v_interestingCtors_x3f_3036_, lean_object* v_a_3037_, lean_object* v_a_3038_, lean_object* v_a_3039_, lean_object* v_a_3040_){
_start:
{
lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___f_3044_; lean_object* v___x_3045_; 
lean_inc(v_majorFVarId_3032_);
v___x_3042_ = l_Lean_mkFVar(v_majorFVarId_3032_);
v___x_3043_ = lean_box(v_useNatCasesAuxOn_3035_);
lean_inc(v_mvarId_3031_);
v___f_3044_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___boxed), 12, 7);
lean_closure_set(v___f_3044_, 0, v___x_3042_);
lean_closure_set(v___f_3044_, 1, v_mvarId_3031_);
lean_closure_set(v___f_3044_, 2, v_majorFVarId_3032_);
lean_closure_set(v___f_3044_, 3, v_givenNames_3033_);
lean_closure_set(v___f_3044_, 4, v_ctx_3034_);
lean_closure_set(v___f_3044_, 5, v___x_3043_);
lean_closure_set(v___f_3044_, 6, v_interestingCtors_x3f_3036_);
v___x_3045_ = l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2___redArg(v_mvarId_3031_, v___f_3044_, v_a_3037_, v_a_3038_, v_a_3039_, v_a_3040_);
return v___x_3045_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___boxed(lean_object* v_mvarId_3046_, lean_object* v_majorFVarId_3047_, lean_object* v_givenNames_3048_, lean_object* v_ctx_3049_, lean_object* v_useNatCasesAuxOn_3050_, lean_object* v_interestingCtors_x3f_3051_, lean_object* v_a_3052_, lean_object* v_a_3053_, lean_object* v_a_3054_, lean_object* v_a_3055_, lean_object* v_a_3056_){
_start:
{
uint8_t v_useNatCasesAuxOn_boxed_3057_; lean_object* v_res_3058_; 
v_useNatCasesAuxOn_boxed_3057_ = lean_unbox(v_useNatCasesAuxOn_3050_);
v_res_3058_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn(v_mvarId_3046_, v_majorFVarId_3047_, v_givenNames_3048_, v_ctx_3049_, v_useNatCasesAuxOn_boxed_3057_, v_interestingCtors_x3f_3051_, v_a_3052_, v_a_3053_, v_a_3054_, v_a_3055_);
return v_res_3058_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Cases_cases_spec__0___redArg(lean_object* v_cls_3062_, lean_object* v___y_3063_){
_start:
{
lean_object* v_options_3065_; uint8_t v_hasTrace_3066_; 
v_options_3065_ = lean_ctor_get(v___y_3063_, 2);
v_hasTrace_3066_ = lean_ctor_get_uint8(v_options_3065_, sizeof(void*)*1);
if (v_hasTrace_3066_ == 0)
{
lean_object* v___x_3067_; lean_object* v___x_3068_; 
lean_dec(v_cls_3062_);
v___x_3067_ = lean_box(v_hasTrace_3066_);
v___x_3068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3068_, 0, v___x_3067_);
return v___x_3068_;
}
else
{
lean_object* v_inheritedTraceOptions_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; uint8_t v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; 
v_inheritedTraceOptions_3069_ = lean_ctor_get(v___y_3063_, 13);
v___x_3070_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Meta_Cases_cases_spec__0___redArg___closed__1));
v___x_3071_ = l_Lean_Name_append(v___x_3070_, v_cls_3062_);
v___x_3072_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3069_, v_options_3065_, v___x_3071_);
lean_dec(v___x_3071_);
v___x_3073_ = lean_box(v___x_3072_);
v___x_3074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3074_, 0, v___x_3073_);
return v___x_3074_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Cases_cases_spec__0___redArg___boxed(lean_object* v_cls_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_){
_start:
{
lean_object* v_res_3078_; 
v_res_3078_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Cases_cases_spec__0___redArg(v_cls_3075_, v___y_3076_);
lean_dec_ref(v___y_3076_);
return v_res_3078_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Cases_cases_spec__0(lean_object* v_cls_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_){
_start:
{
lean_object* v___x_3085_; 
v___x_3085_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Cases_cases_spec__0___redArg(v_cls_3079_, v___y_3082_);
return v___x_3085_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Cases_cases_spec__0___boxed(lean_object* v_cls_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_){
_start:
{
lean_object* v_res_3092_; 
v_res_3092_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Cases_cases_spec__0(v_cls_3086_, v___y_3087_, v___y_3088_, v___y_3089_, v___y_3090_);
lean_dec(v___y_3090_);
lean_dec_ref(v___y_3089_);
lean_dec(v___y_3088_);
lean_dec_ref(v___y_3087_);
return v_res_3092_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__1___closed__0(void){
_start:
{
lean_object* v___x_3093_; double v___x_3094_; 
v___x_3093_ = lean_unsigned_to_nat(0u);
v___x_3094_ = lean_float_of_nat(v___x_3093_);
return v___x_3094_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__1(lean_object* v_cls_3098_, lean_object* v_msg_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_){
_start:
{
lean_object* v_ref_3105_; lean_object* v___x_3106_; lean_object* v_a_3107_; lean_object* v___x_3109_; uint8_t v_isShared_3110_; uint8_t v_isSharedCheck_3151_; 
v_ref_3105_ = lean_ctor_get(v___y_3102_, 5);
v___x_3106_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected_spec__0_spec__0(v_msg_3099_, v___y_3100_, v___y_3101_, v___y_3102_, v___y_3103_);
v_a_3107_ = lean_ctor_get(v___x_3106_, 0);
v_isSharedCheck_3151_ = !lean_is_exclusive(v___x_3106_);
if (v_isSharedCheck_3151_ == 0)
{
v___x_3109_ = v___x_3106_;
v_isShared_3110_ = v_isSharedCheck_3151_;
goto v_resetjp_3108_;
}
else
{
lean_inc(v_a_3107_);
lean_dec(v___x_3106_);
v___x_3109_ = lean_box(0);
v_isShared_3110_ = v_isSharedCheck_3151_;
goto v_resetjp_3108_;
}
v_resetjp_3108_:
{
lean_object* v___x_3111_; lean_object* v_traceState_3112_; lean_object* v_env_3113_; lean_object* v_nextMacroScope_3114_; lean_object* v_ngen_3115_; lean_object* v_auxDeclNGen_3116_; lean_object* v_cache_3117_; lean_object* v_messages_3118_; lean_object* v_infoState_3119_; lean_object* v_snapshotTasks_3120_; lean_object* v___x_3122_; uint8_t v_isShared_3123_; uint8_t v_isSharedCheck_3150_; 
v___x_3111_ = lean_st_ref_take(v___y_3103_);
v_traceState_3112_ = lean_ctor_get(v___x_3111_, 4);
v_env_3113_ = lean_ctor_get(v___x_3111_, 0);
v_nextMacroScope_3114_ = lean_ctor_get(v___x_3111_, 1);
v_ngen_3115_ = lean_ctor_get(v___x_3111_, 2);
v_auxDeclNGen_3116_ = lean_ctor_get(v___x_3111_, 3);
v_cache_3117_ = lean_ctor_get(v___x_3111_, 5);
v_messages_3118_ = lean_ctor_get(v___x_3111_, 6);
v_infoState_3119_ = lean_ctor_get(v___x_3111_, 7);
v_snapshotTasks_3120_ = lean_ctor_get(v___x_3111_, 8);
v_isSharedCheck_3150_ = !lean_is_exclusive(v___x_3111_);
if (v_isSharedCheck_3150_ == 0)
{
v___x_3122_ = v___x_3111_;
v_isShared_3123_ = v_isSharedCheck_3150_;
goto v_resetjp_3121_;
}
else
{
lean_inc(v_snapshotTasks_3120_);
lean_inc(v_infoState_3119_);
lean_inc(v_messages_3118_);
lean_inc(v_cache_3117_);
lean_inc(v_traceState_3112_);
lean_inc(v_auxDeclNGen_3116_);
lean_inc(v_ngen_3115_);
lean_inc(v_nextMacroScope_3114_);
lean_inc(v_env_3113_);
lean_dec(v___x_3111_);
v___x_3122_ = lean_box(0);
v_isShared_3123_ = v_isSharedCheck_3150_;
goto v_resetjp_3121_;
}
v_resetjp_3121_:
{
uint64_t v_tid_3124_; lean_object* v_traces_3125_; lean_object* v___x_3127_; uint8_t v_isShared_3128_; uint8_t v_isSharedCheck_3149_; 
v_tid_3124_ = lean_ctor_get_uint64(v_traceState_3112_, sizeof(void*)*1);
v_traces_3125_ = lean_ctor_get(v_traceState_3112_, 0);
v_isSharedCheck_3149_ = !lean_is_exclusive(v_traceState_3112_);
if (v_isSharedCheck_3149_ == 0)
{
v___x_3127_ = v_traceState_3112_;
v_isShared_3128_ = v_isSharedCheck_3149_;
goto v_resetjp_3126_;
}
else
{
lean_inc(v_traces_3125_);
lean_dec(v_traceState_3112_);
v___x_3127_ = lean_box(0);
v_isShared_3128_ = v_isSharedCheck_3149_;
goto v_resetjp_3126_;
}
v_resetjp_3126_:
{
lean_object* v___x_3129_; double v___x_3130_; uint8_t v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3139_; 
v___x_3129_ = lean_box(0);
v___x_3130_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__1___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__1___closed__0);
v___x_3131_ = 0;
v___x_3132_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__1___closed__1));
v___x_3133_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3133_, 0, v_cls_3098_);
lean_ctor_set(v___x_3133_, 1, v___x_3129_);
lean_ctor_set(v___x_3133_, 2, v___x_3132_);
lean_ctor_set_float(v___x_3133_, sizeof(void*)*3, v___x_3130_);
lean_ctor_set_float(v___x_3133_, sizeof(void*)*3 + 8, v___x_3130_);
lean_ctor_set_uint8(v___x_3133_, sizeof(void*)*3 + 16, v___x_3131_);
v___x_3134_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__1___closed__2));
v___x_3135_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3135_, 0, v___x_3133_);
lean_ctor_set(v___x_3135_, 1, v_a_3107_);
lean_ctor_set(v___x_3135_, 2, v___x_3134_);
lean_inc(v_ref_3105_);
v___x_3136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3136_, 0, v_ref_3105_);
lean_ctor_set(v___x_3136_, 1, v___x_3135_);
v___x_3137_ = l_Lean_PersistentArray_push___redArg(v_traces_3125_, v___x_3136_);
if (v_isShared_3128_ == 0)
{
lean_ctor_set(v___x_3127_, 0, v___x_3137_);
v___x_3139_ = v___x_3127_;
goto v_reusejp_3138_;
}
else
{
lean_object* v_reuseFailAlloc_3148_; 
v_reuseFailAlloc_3148_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3148_, 0, v___x_3137_);
lean_ctor_set_uint64(v_reuseFailAlloc_3148_, sizeof(void*)*1, v_tid_3124_);
v___x_3139_ = v_reuseFailAlloc_3148_;
goto v_reusejp_3138_;
}
v_reusejp_3138_:
{
lean_object* v___x_3141_; 
if (v_isShared_3123_ == 0)
{
lean_ctor_set(v___x_3122_, 4, v___x_3139_);
v___x_3141_ = v___x_3122_;
goto v_reusejp_3140_;
}
else
{
lean_object* v_reuseFailAlloc_3147_; 
v_reuseFailAlloc_3147_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3147_, 0, v_env_3113_);
lean_ctor_set(v_reuseFailAlloc_3147_, 1, v_nextMacroScope_3114_);
lean_ctor_set(v_reuseFailAlloc_3147_, 2, v_ngen_3115_);
lean_ctor_set(v_reuseFailAlloc_3147_, 3, v_auxDeclNGen_3116_);
lean_ctor_set(v_reuseFailAlloc_3147_, 4, v___x_3139_);
lean_ctor_set(v_reuseFailAlloc_3147_, 5, v_cache_3117_);
lean_ctor_set(v_reuseFailAlloc_3147_, 6, v_messages_3118_);
lean_ctor_set(v_reuseFailAlloc_3147_, 7, v_infoState_3119_);
lean_ctor_set(v_reuseFailAlloc_3147_, 8, v_snapshotTasks_3120_);
v___x_3141_ = v_reuseFailAlloc_3147_;
goto v_reusejp_3140_;
}
v_reusejp_3140_:
{
lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3145_; 
v___x_3142_ = lean_st_ref_set(v___y_3103_, v___x_3141_);
v___x_3143_ = lean_box(0);
if (v_isShared_3110_ == 0)
{
lean_ctor_set(v___x_3109_, 0, v___x_3143_);
v___x_3145_ = v___x_3109_;
goto v_reusejp_3144_;
}
else
{
lean_object* v_reuseFailAlloc_3146_; 
v_reuseFailAlloc_3146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3146_, 0, v___x_3143_);
v___x_3145_ = v_reuseFailAlloc_3146_;
goto v_reusejp_3144_;
}
v_reusejp_3144_:
{
return v___x_3145_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__1___boxed(lean_object* v_cls_3152_, lean_object* v_msg_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_){
_start:
{
lean_object* v_res_3159_; 
v_res_3159_ = l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__1(v_cls_3152_, v_msg_3153_, v___y_3154_, v___y_3155_, v___y_3156_, v___y_3157_);
lean_dec(v___y_3157_);
lean_dec_ref(v___y_3156_);
lean_dec(v___y_3155_);
lean_dec_ref(v___y_3154_);
return v_res_3159_;
}
}
static lean_object* _init_l_Lean_Meta_Cases_cases___lam__0___closed__2(void){
_start:
{
lean_object* v___x_3163_; lean_object* v___x_3164_; 
v___x_3163_ = ((lean_object*)(l_Lean_Meta_Cases_cases___lam__0___closed__1));
v___x_3164_ = l_Lean_MessageData_ofFormat(v___x_3163_);
return v___x_3164_;
}
}
static lean_object* _init_l_Lean_Meta_Cases_cases___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3165_; lean_object* v___x_3166_; 
v___x_3165_ = lean_obj_once(&l_Lean_Meta_Cases_cases___lam__0___closed__2, &l_Lean_Meta_Cases_cases___lam__0___closed__2_once, _init_l_Lean_Meta_Cases_cases___lam__0___closed__2);
v___x_3166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3166_, 0, v___x_3165_);
return v___x_3166_;
}
}
static lean_object* _init_l_Lean_Meta_Cases_cases___lam__0___closed__7(void){
_start:
{
lean_object* v___x_3170_; lean_object* v___x_3171_; 
v___x_3170_ = ((lean_object*)(l_Lean_Meta_Cases_cases___lam__0___closed__6));
v___x_3171_ = l_Lean_stringToMessageData(v___x_3170_);
return v___x_3171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_cases___lam__0(lean_object* v_mvarId_3172_, lean_object* v___x_3173_, lean_object* v_majorFVarId_3174_, lean_object* v___x_3175_, lean_object* v_givenNames_3176_, lean_object* v_interestingCtors_x3f_3177_, uint8_t v_useNatCasesAuxOn_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_){
_start:
{
lean_object* v___x_3184_; 
lean_inc(v___x_3173_);
lean_inc(v_mvarId_3172_);
v___x_3184_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_3172_, v___x_3173_, v___y_3179_, v___y_3180_, v___y_3181_, v___y_3182_);
if (lean_obj_tag(v___x_3184_) == 0)
{
lean_object* v___x_3185_; 
lean_dec_ref(v___x_3184_);
lean_inc(v___y_3182_);
lean_inc_ref(v___y_3181_);
lean_inc(v___y_3180_);
lean_inc_ref(v___y_3179_);
lean_inc(v_majorFVarId_3174_);
v___x_3185_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f(v_majorFVarId_3174_, v___y_3179_, v___y_3180_, v___y_3181_, v___y_3182_);
if (lean_obj_tag(v___x_3185_) == 0)
{
lean_object* v_a_3186_; 
v_a_3186_ = lean_ctor_get(v___x_3185_, 0);
lean_inc(v_a_3186_);
lean_dec_ref(v___x_3185_);
if (lean_obj_tag(v_a_3186_) == 0)
{
lean_object* v___x_3187_; lean_object* v___x_3188_; 
lean_dec(v_interestingCtors_x3f_3177_);
lean_dec_ref(v_givenNames_3176_);
lean_dec_ref(v___x_3175_);
lean_dec(v_majorFVarId_3174_);
v___x_3187_ = lean_obj_once(&l_Lean_Meta_Cases_cases___lam__0___closed__3, &l_Lean_Meta_Cases_cases___lam__0___closed__3_once, _init_l_Lean_Meta_Cases_cases___lam__0___closed__3);
v___x_3188_ = l_Lean_Meta_throwTacticEx___redArg(v___x_3173_, v_mvarId_3172_, v___x_3187_, v___y_3179_, v___y_3180_, v___y_3181_, v___y_3182_);
lean_dec(v___y_3182_);
lean_dec_ref(v___y_3181_);
lean_dec(v___y_3180_);
lean_dec_ref(v___y_3179_);
return v___x_3188_;
}
else
{
lean_object* v_val_3189_; lean_object* v___x_3190_; 
lean_dec(v___x_3173_);
v_val_3189_ = lean_ctor_get(v_a_3186_, 0);
lean_inc(v_val_3189_);
lean_dec_ref(v_a_3186_);
lean_inc_ref(v___y_3179_);
lean_inc(v_val_3189_);
v___x_3190_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices(v_val_3189_, v___y_3179_, v___y_3180_, v___y_3181_, v___y_3182_);
if (lean_obj_tag(v___x_3190_) == 0)
{
lean_object* v_a_3191_; uint8_t v___x_3192_; 
v_a_3191_ = lean_ctor_get(v___x_3190_, 0);
lean_inc(v_a_3191_);
lean_dec_ref(v___x_3190_);
v___x_3192_ = lean_unbox(v_a_3191_);
if (v___x_3192_ == 0)
{
lean_object* v___x_3193_; 
lean_inc(v___y_3182_);
lean_inc_ref(v___y_3181_);
lean_inc(v___y_3180_);
lean_inc_ref(v___y_3179_);
v___x_3193_ = l_Lean_Meta_generalizeIndices(v_mvarId_3172_, v_majorFVarId_3174_, v___y_3179_, v___y_3180_, v___y_3181_, v___y_3182_);
if (lean_obj_tag(v___x_3193_) == 0)
{
lean_object* v_a_3194_; lean_object* v___y_3196_; lean_object* v___y_3197_; lean_object* v___y_3198_; lean_object* v___y_3199_; lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v_a_3213_; lean_object* v___x_3215_; uint8_t v_isShared_3216_; uint8_t v_isSharedCheck_3233_; 
v_a_3194_ = lean_ctor_get(v___x_3193_, 0);
lean_inc(v_a_3194_);
lean_dec_ref(v___x_3193_);
v___x_3209_ = ((lean_object*)(l_Lean_Meta_Cases_cases___lam__0___closed__4));
v___x_3210_ = ((lean_object*)(l_Lean_Meta_Cases_cases___lam__0___closed__5));
v___x_3211_ = l_Lean_Name_mkStr3(v___x_3209_, v___x_3210_, v___x_3175_);
lean_inc(v___x_3211_);
v___x_3212_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Cases_cases_spec__0___redArg(v___x_3211_, v___y_3181_);
v_a_3213_ = lean_ctor_get(v___x_3212_, 0);
v_isSharedCheck_3233_ = !lean_is_exclusive(v___x_3212_);
if (v_isSharedCheck_3233_ == 0)
{
v___x_3215_ = v___x_3212_;
v_isShared_3216_ = v_isSharedCheck_3233_;
goto v_resetjp_3214_;
}
else
{
lean_inc(v_a_3213_);
lean_dec(v___x_3212_);
v___x_3215_ = lean_box(0);
v_isShared_3216_ = v_isSharedCheck_3233_;
goto v_resetjp_3214_;
}
v___jp_3195_:
{
lean_object* v_mvarId_3200_; lean_object* v_fvarId_3201_; lean_object* v_numEqs_3202_; uint8_t v___x_3203_; lean_object* v___x_3204_; 
v_mvarId_3200_ = lean_ctor_get(v_a_3194_, 0);
v_fvarId_3201_ = lean_ctor_get(v_a_3194_, 2);
v_numEqs_3202_ = lean_ctor_get(v_a_3194_, 3);
lean_inc(v_numEqs_3202_);
v___x_3203_ = lean_unbox(v_a_3191_);
lean_dec(v_a_3191_);
lean_inc(v___y_3199_);
lean_inc_ref(v___y_3198_);
lean_inc(v___y_3197_);
lean_inc_ref(v___y_3196_);
lean_inc(v_fvarId_3201_);
lean_inc(v_mvarId_3200_);
v___x_3204_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn(v_mvarId_3200_, v_fvarId_3201_, v_givenNames_3176_, v_val_3189_, v___x_3203_, v_interestingCtors_x3f_3177_, v___y_3196_, v___y_3197_, v___y_3198_, v___y_3199_);
if (lean_obj_tag(v___x_3204_) == 0)
{
lean_object* v_a_3205_; lean_object* v___x_3206_; 
v_a_3205_ = lean_ctor_get(v___x_3204_, 0);
lean_inc(v_a_3205_);
lean_dec_ref(v___x_3204_);
lean_inc(v___y_3199_);
lean_inc_ref(v___y_3198_);
lean_inc(v___y_3197_);
lean_inc_ref(v___y_3196_);
v___x_3206_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices(v_a_3194_, v_a_3205_, v___y_3196_, v___y_3197_, v___y_3198_, v___y_3199_);
lean_dec(v_a_3194_);
if (lean_obj_tag(v___x_3206_) == 0)
{
lean_object* v_a_3207_; lean_object* v___x_3208_; 
v_a_3207_ = lean_ctor_get(v___x_3206_, 0);
lean_inc(v_a_3207_);
lean_dec_ref(v___x_3206_);
v___x_3208_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs(v_numEqs_3202_, v_a_3207_, v___y_3196_, v___y_3197_, v___y_3198_, v___y_3199_);
lean_dec(v_a_3207_);
return v___x_3208_;
}
else
{
lean_dec(v_numEqs_3202_);
lean_dec(v___y_3199_);
lean_dec_ref(v___y_3198_);
lean_dec(v___y_3197_);
lean_dec_ref(v___y_3196_);
return v___x_3206_;
}
}
else
{
lean_dec(v_numEqs_3202_);
lean_dec(v___y_3199_);
lean_dec_ref(v___y_3198_);
lean_dec(v___y_3197_);
lean_dec_ref(v___y_3196_);
lean_dec(v_a_3194_);
return v___x_3204_;
}
}
v_resetjp_3214_:
{
uint8_t v___x_3217_; 
v___x_3217_ = lean_unbox(v_a_3213_);
lean_dec(v_a_3213_);
if (v___x_3217_ == 0)
{
lean_del_object(v___x_3215_);
lean_dec(v___x_3211_);
v___y_3196_ = v___y_3179_;
v___y_3197_ = v___y_3180_;
v___y_3198_ = v___y_3181_;
v___y_3199_ = v___y_3182_;
goto v___jp_3195_;
}
else
{
lean_object* v_mvarId_3218_; lean_object* v___x_3219_; lean_object* v___x_3221_; 
v_mvarId_3218_ = lean_ctor_get(v_a_3194_, 0);
v___x_3219_ = lean_obj_once(&l_Lean_Meta_Cases_cases___lam__0___closed__7, &l_Lean_Meta_Cases_cases___lam__0___closed__7_once, _init_l_Lean_Meta_Cases_cases___lam__0___closed__7);
lean_inc(v_mvarId_3218_);
if (v_isShared_3216_ == 0)
{
lean_ctor_set_tag(v___x_3215_, 1);
lean_ctor_set(v___x_3215_, 0, v_mvarId_3218_);
v___x_3221_ = v___x_3215_;
goto v_reusejp_3220_;
}
else
{
lean_object* v_reuseFailAlloc_3232_; 
v_reuseFailAlloc_3232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3232_, 0, v_mvarId_3218_);
v___x_3221_ = v_reuseFailAlloc_3232_;
goto v_reusejp_3220_;
}
v_reusejp_3220_:
{
lean_object* v___x_3222_; lean_object* v___x_3223_; 
v___x_3222_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3222_, 0, v___x_3219_);
lean_ctor_set(v___x_3222_, 1, v___x_3221_);
v___x_3223_ = l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__1(v___x_3211_, v___x_3222_, v___y_3179_, v___y_3180_, v___y_3181_, v___y_3182_);
if (lean_obj_tag(v___x_3223_) == 0)
{
lean_dec_ref(v___x_3223_);
v___y_3196_ = v___y_3179_;
v___y_3197_ = v___y_3180_;
v___y_3198_ = v___y_3181_;
v___y_3199_ = v___y_3182_;
goto v___jp_3195_;
}
else
{
lean_object* v_a_3224_; lean_object* v___x_3226_; uint8_t v_isShared_3227_; uint8_t v_isSharedCheck_3231_; 
lean_dec(v_a_3194_);
lean_dec(v_a_3191_);
lean_dec(v_val_3189_);
lean_dec(v___y_3182_);
lean_dec_ref(v___y_3181_);
lean_dec(v___y_3180_);
lean_dec_ref(v___y_3179_);
lean_dec(v_interestingCtors_x3f_3177_);
lean_dec_ref(v_givenNames_3176_);
v_a_3224_ = lean_ctor_get(v___x_3223_, 0);
v_isSharedCheck_3231_ = !lean_is_exclusive(v___x_3223_);
if (v_isSharedCheck_3231_ == 0)
{
v___x_3226_ = v___x_3223_;
v_isShared_3227_ = v_isSharedCheck_3231_;
goto v_resetjp_3225_;
}
else
{
lean_inc(v_a_3224_);
lean_dec(v___x_3223_);
v___x_3226_ = lean_box(0);
v_isShared_3227_ = v_isSharedCheck_3231_;
goto v_resetjp_3225_;
}
v_resetjp_3225_:
{
lean_object* v___x_3229_; 
if (v_isShared_3227_ == 0)
{
v___x_3229_ = v___x_3226_;
goto v_reusejp_3228_;
}
else
{
lean_object* v_reuseFailAlloc_3230_; 
v_reuseFailAlloc_3230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3230_, 0, v_a_3224_);
v___x_3229_ = v_reuseFailAlloc_3230_;
goto v_reusejp_3228_;
}
v_reusejp_3228_:
{
return v___x_3229_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3234_; lean_object* v___x_3236_; uint8_t v_isShared_3237_; uint8_t v_isSharedCheck_3241_; 
lean_dec(v_a_3191_);
lean_dec(v_val_3189_);
lean_dec(v___y_3182_);
lean_dec_ref(v___y_3181_);
lean_dec(v___y_3180_);
lean_dec_ref(v___y_3179_);
lean_dec(v_interestingCtors_x3f_3177_);
lean_dec_ref(v_givenNames_3176_);
lean_dec_ref(v___x_3175_);
v_a_3234_ = lean_ctor_get(v___x_3193_, 0);
v_isSharedCheck_3241_ = !lean_is_exclusive(v___x_3193_);
if (v_isSharedCheck_3241_ == 0)
{
v___x_3236_ = v___x_3193_;
v_isShared_3237_ = v_isSharedCheck_3241_;
goto v_resetjp_3235_;
}
else
{
lean_inc(v_a_3234_);
lean_dec(v___x_3193_);
v___x_3236_ = lean_box(0);
v_isShared_3237_ = v_isSharedCheck_3241_;
goto v_resetjp_3235_;
}
v_resetjp_3235_:
{
lean_object* v___x_3239_; 
if (v_isShared_3237_ == 0)
{
v___x_3239_ = v___x_3236_;
goto v_reusejp_3238_;
}
else
{
lean_object* v_reuseFailAlloc_3240_; 
v_reuseFailAlloc_3240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3240_, 0, v_a_3234_);
v___x_3239_ = v_reuseFailAlloc_3240_;
goto v_reusejp_3238_;
}
v_reusejp_3238_:
{
return v___x_3239_;
}
}
}
}
else
{
lean_object* v___x_3242_; 
lean_dec(v_a_3191_);
lean_dec_ref(v___x_3175_);
v___x_3242_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn(v_mvarId_3172_, v_majorFVarId_3174_, v_givenNames_3176_, v_val_3189_, v_useNatCasesAuxOn_3178_, v_interestingCtors_x3f_3177_, v___y_3179_, v___y_3180_, v___y_3181_, v___y_3182_);
return v___x_3242_;
}
}
else
{
lean_object* v_a_3243_; lean_object* v___x_3245_; uint8_t v_isShared_3246_; uint8_t v_isSharedCheck_3250_; 
lean_dec(v_val_3189_);
lean_dec(v___y_3182_);
lean_dec_ref(v___y_3181_);
lean_dec(v___y_3180_);
lean_dec_ref(v___y_3179_);
lean_dec(v_interestingCtors_x3f_3177_);
lean_dec_ref(v_givenNames_3176_);
lean_dec_ref(v___x_3175_);
lean_dec(v_majorFVarId_3174_);
lean_dec(v_mvarId_3172_);
v_a_3243_ = lean_ctor_get(v___x_3190_, 0);
v_isSharedCheck_3250_ = !lean_is_exclusive(v___x_3190_);
if (v_isSharedCheck_3250_ == 0)
{
v___x_3245_ = v___x_3190_;
v_isShared_3246_ = v_isSharedCheck_3250_;
goto v_resetjp_3244_;
}
else
{
lean_inc(v_a_3243_);
lean_dec(v___x_3190_);
v___x_3245_ = lean_box(0);
v_isShared_3246_ = v_isSharedCheck_3250_;
goto v_resetjp_3244_;
}
v_resetjp_3244_:
{
lean_object* v___x_3248_; 
if (v_isShared_3246_ == 0)
{
v___x_3248_ = v___x_3245_;
goto v_reusejp_3247_;
}
else
{
lean_object* v_reuseFailAlloc_3249_; 
v_reuseFailAlloc_3249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3249_, 0, v_a_3243_);
v___x_3248_ = v_reuseFailAlloc_3249_;
goto v_reusejp_3247_;
}
v_reusejp_3247_:
{
return v___x_3248_;
}
}
}
}
}
else
{
lean_object* v_a_3251_; lean_object* v___x_3253_; uint8_t v_isShared_3254_; uint8_t v_isSharedCheck_3258_; 
lean_dec(v___y_3182_);
lean_dec_ref(v___y_3181_);
lean_dec(v___y_3180_);
lean_dec_ref(v___y_3179_);
lean_dec(v_interestingCtors_x3f_3177_);
lean_dec_ref(v_givenNames_3176_);
lean_dec_ref(v___x_3175_);
lean_dec(v_majorFVarId_3174_);
lean_dec(v___x_3173_);
lean_dec(v_mvarId_3172_);
v_a_3251_ = lean_ctor_get(v___x_3185_, 0);
v_isSharedCheck_3258_ = !lean_is_exclusive(v___x_3185_);
if (v_isSharedCheck_3258_ == 0)
{
v___x_3253_ = v___x_3185_;
v_isShared_3254_ = v_isSharedCheck_3258_;
goto v_resetjp_3252_;
}
else
{
lean_inc(v_a_3251_);
lean_dec(v___x_3185_);
v___x_3253_ = lean_box(0);
v_isShared_3254_ = v_isSharedCheck_3258_;
goto v_resetjp_3252_;
}
v_resetjp_3252_:
{
lean_object* v___x_3256_; 
if (v_isShared_3254_ == 0)
{
v___x_3256_ = v___x_3253_;
goto v_reusejp_3255_;
}
else
{
lean_object* v_reuseFailAlloc_3257_; 
v_reuseFailAlloc_3257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3257_, 0, v_a_3251_);
v___x_3256_ = v_reuseFailAlloc_3257_;
goto v_reusejp_3255_;
}
v_reusejp_3255_:
{
return v___x_3256_;
}
}
}
}
else
{
lean_object* v_a_3259_; lean_object* v___x_3261_; uint8_t v_isShared_3262_; uint8_t v_isSharedCheck_3266_; 
lean_dec(v___y_3182_);
lean_dec_ref(v___y_3181_);
lean_dec(v___y_3180_);
lean_dec_ref(v___y_3179_);
lean_dec(v_interestingCtors_x3f_3177_);
lean_dec_ref(v_givenNames_3176_);
lean_dec_ref(v___x_3175_);
lean_dec(v_majorFVarId_3174_);
lean_dec(v___x_3173_);
lean_dec(v_mvarId_3172_);
v_a_3259_ = lean_ctor_get(v___x_3184_, 0);
v_isSharedCheck_3266_ = !lean_is_exclusive(v___x_3184_);
if (v_isSharedCheck_3266_ == 0)
{
v___x_3261_ = v___x_3184_;
v_isShared_3262_ = v_isSharedCheck_3266_;
goto v_resetjp_3260_;
}
else
{
lean_inc(v_a_3259_);
lean_dec(v___x_3184_);
v___x_3261_ = lean_box(0);
v_isShared_3262_ = v_isSharedCheck_3266_;
goto v_resetjp_3260_;
}
v_resetjp_3260_:
{
lean_object* v___x_3264_; 
if (v_isShared_3262_ == 0)
{
v___x_3264_ = v___x_3261_;
goto v_reusejp_3263_;
}
else
{
lean_object* v_reuseFailAlloc_3265_; 
v_reuseFailAlloc_3265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3265_, 0, v_a_3259_);
v___x_3264_ = v_reuseFailAlloc_3265_;
goto v_reusejp_3263_;
}
v_reusejp_3263_:
{
return v___x_3264_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_cases___lam__0___boxed(lean_object* v_mvarId_3267_, lean_object* v___x_3268_, lean_object* v_majorFVarId_3269_, lean_object* v___x_3270_, lean_object* v_givenNames_3271_, lean_object* v_interestingCtors_x3f_3272_, lean_object* v_useNatCasesAuxOn_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_){
_start:
{
uint8_t v_useNatCasesAuxOn_boxed_3279_; lean_object* v_res_3280_; 
v_useNatCasesAuxOn_boxed_3279_ = lean_unbox(v_useNatCasesAuxOn_3273_);
v_res_3280_ = l_Lean_Meta_Cases_cases___lam__0(v_mvarId_3267_, v___x_3268_, v_majorFVarId_3269_, v___x_3270_, v_givenNames_3271_, v_interestingCtors_x3f_3272_, v_useNatCasesAuxOn_boxed_3279_, v___y_3274_, v___y_3275_, v___y_3276_, v___y_3277_);
return v_res_3280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_cases(lean_object* v_mvarId_3284_, lean_object* v_majorFVarId_3285_, lean_object* v_givenNames_3286_, uint8_t v_useNatCasesAuxOn_3287_, lean_object* v_interestingCtors_x3f_3288_, lean_object* v_a_3289_, lean_object* v_a_3290_, lean_object* v_a_3291_, lean_object* v_a_3292_){
_start:
{
lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___f_3297_; lean_object* v___x_3298_; 
v___x_3294_ = ((lean_object*)(l_Lean_Meta_Cases_cases___closed__0));
v___x_3295_ = ((lean_object*)(l_Lean_Meta_Cases_cases___closed__1));
v___x_3296_ = lean_box(v_useNatCasesAuxOn_3287_);
lean_inc(v_mvarId_3284_);
v___f_3297_ = lean_alloc_closure((void*)(l_Lean_Meta_Cases_cases___lam__0___boxed), 12, 7);
lean_closure_set(v___f_3297_, 0, v_mvarId_3284_);
lean_closure_set(v___f_3297_, 1, v___x_3295_);
lean_closure_set(v___f_3297_, 2, v_majorFVarId_3285_);
lean_closure_set(v___f_3297_, 3, v___x_3294_);
lean_closure_set(v___f_3297_, 4, v_givenNames_3286_);
lean_closure_set(v___f_3297_, 5, v_interestingCtors_x3f_3288_);
lean_closure_set(v___f_3297_, 6, v___x_3296_);
lean_inc(v_a_3292_);
lean_inc_ref(v_a_3291_);
lean_inc(v_a_3290_);
lean_inc_ref(v_a_3289_);
v___x_3298_ = l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2___redArg(v_mvarId_3284_, v___f_3297_, v_a_3289_, v_a_3290_, v_a_3291_, v_a_3292_);
if (lean_obj_tag(v___x_3298_) == 0)
{
lean_dec(v_a_3292_);
lean_dec_ref(v_a_3291_);
lean_dec(v_a_3290_);
lean_dec_ref(v_a_3289_);
return v___x_3298_;
}
else
{
lean_object* v_a_3299_; uint8_t v___y_3301_; uint8_t v___x_3303_; 
v_a_3299_ = lean_ctor_get(v___x_3298_, 0);
lean_inc(v_a_3299_);
v___x_3303_ = l_Lean_Exception_isInterrupt(v_a_3299_);
if (v___x_3303_ == 0)
{
uint8_t v___x_3304_; 
lean_inc(v_a_3299_);
v___x_3304_ = l_Lean_Exception_isRuntime(v_a_3299_);
v___y_3301_ = v___x_3304_;
goto v___jp_3300_;
}
else
{
v___y_3301_ = v___x_3303_;
goto v___jp_3300_;
}
v___jp_3300_:
{
if (v___y_3301_ == 0)
{
lean_object* v___x_3302_; 
lean_dec_ref(v___x_3298_);
v___x_3302_ = l_Lean_Meta_throwNestedTacticEx___redArg(v___x_3295_, v_a_3299_, v_a_3289_, v_a_3290_, v_a_3291_, v_a_3292_);
lean_dec(v_a_3292_);
lean_dec_ref(v_a_3291_);
lean_dec(v_a_3290_);
lean_dec_ref(v_a_3289_);
return v___x_3302_;
}
else
{
lean_dec(v_a_3299_);
lean_dec(v_a_3292_);
lean_dec_ref(v_a_3291_);
lean_dec(v_a_3290_);
lean_dec_ref(v_a_3289_);
return v___x_3298_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_cases___boxed(lean_object* v_mvarId_3305_, lean_object* v_majorFVarId_3306_, lean_object* v_givenNames_3307_, lean_object* v_useNatCasesAuxOn_3308_, lean_object* v_interestingCtors_x3f_3309_, lean_object* v_a_3310_, lean_object* v_a_3311_, lean_object* v_a_3312_, lean_object* v_a_3313_, lean_object* v_a_3314_){
_start:
{
uint8_t v_useNatCasesAuxOn_boxed_3315_; lean_object* v_res_3316_; 
v_useNatCasesAuxOn_boxed_3315_ = lean_unbox(v_useNatCasesAuxOn_3308_);
v_res_3316_ = l_Lean_Meta_Cases_cases(v_mvarId_3305_, v_majorFVarId_3306_, v_givenNames_3307_, v_useNatCasesAuxOn_boxed_3315_, v_interestingCtors_x3f_3309_, v_a_3310_, v_a_3311_, v_a_3312_, v_a_3313_);
return v_res_3316_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_cases(lean_object* v_mvarId_3317_, lean_object* v_majorFVarId_3318_, lean_object* v_givenNames_3319_, uint8_t v_useNatCasesAuxOn_3320_, lean_object* v_interestingCtors_x3f_3321_, lean_object* v_a_3322_, lean_object* v_a_3323_, lean_object* v_a_3324_, lean_object* v_a_3325_){
_start:
{
lean_object* v___x_3327_; 
v___x_3327_ = l_Lean_Meta_Cases_cases(v_mvarId_3317_, v_majorFVarId_3318_, v_givenNames_3319_, v_useNatCasesAuxOn_3320_, v_interestingCtors_x3f_3321_, v_a_3322_, v_a_3323_, v_a_3324_, v_a_3325_);
return v___x_3327_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_cases___boxed(lean_object* v_mvarId_3328_, lean_object* v_majorFVarId_3329_, lean_object* v_givenNames_3330_, lean_object* v_useNatCasesAuxOn_3331_, lean_object* v_interestingCtors_x3f_3332_, lean_object* v_a_3333_, lean_object* v_a_3334_, lean_object* v_a_3335_, lean_object* v_a_3336_, lean_object* v_a_3337_){
_start:
{
uint8_t v_useNatCasesAuxOn_boxed_3338_; lean_object* v_res_3339_; 
v_useNatCasesAuxOn_boxed_3338_ = lean_unbox(v_useNatCasesAuxOn_3331_);
v_res_3339_ = l_Lean_MVarId_cases(v_mvarId_3328_, v_majorFVarId_3329_, v_givenNames_3330_, v_useNatCasesAuxOn_boxed_3338_, v_interestingCtors_x3f_3332_, v_a_3333_, v_a_3334_, v_a_3335_, v_a_3336_);
return v_res_3339_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1___redArg(lean_object* v_x_3340_, lean_object* v___y_3341_, lean_object* v___y_3342_, lean_object* v___y_3343_, lean_object* v___y_3344_){
_start:
{
lean_object* v___x_3346_; 
v___x_3346_ = l_Lean_Meta_saveState___redArg(v___y_3342_, v___y_3344_);
if (lean_obj_tag(v___x_3346_) == 0)
{
lean_object* v_a_3347_; lean_object* v___x_3348_; 
v_a_3347_ = lean_ctor_get(v___x_3346_, 0);
lean_inc(v_a_3347_);
lean_dec_ref(v___x_3346_);
lean_inc(v___y_3344_);
lean_inc(v___y_3342_);
v___x_3348_ = lean_apply_5(v_x_3340_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_, lean_box(0));
if (lean_obj_tag(v___x_3348_) == 0)
{
lean_object* v_a_3349_; lean_object* v___x_3351_; uint8_t v_isShared_3352_; uint8_t v_isSharedCheck_3357_; 
lean_dec(v_a_3347_);
lean_dec(v___y_3344_);
lean_dec(v___y_3342_);
v_a_3349_ = lean_ctor_get(v___x_3348_, 0);
v_isSharedCheck_3357_ = !lean_is_exclusive(v___x_3348_);
if (v_isSharedCheck_3357_ == 0)
{
v___x_3351_ = v___x_3348_;
v_isShared_3352_ = v_isSharedCheck_3357_;
goto v_resetjp_3350_;
}
else
{
lean_inc(v_a_3349_);
lean_dec(v___x_3348_);
v___x_3351_ = lean_box(0);
v_isShared_3352_ = v_isSharedCheck_3357_;
goto v_resetjp_3350_;
}
v_resetjp_3350_:
{
lean_object* v___x_3353_; lean_object* v___x_3355_; 
v___x_3353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3353_, 0, v_a_3349_);
if (v_isShared_3352_ == 0)
{
lean_ctor_set(v___x_3351_, 0, v___x_3353_);
v___x_3355_ = v___x_3351_;
goto v_reusejp_3354_;
}
else
{
lean_object* v_reuseFailAlloc_3356_; 
v_reuseFailAlloc_3356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3356_, 0, v___x_3353_);
v___x_3355_ = v_reuseFailAlloc_3356_;
goto v_reusejp_3354_;
}
v_reusejp_3354_:
{
return v___x_3355_;
}
}
}
else
{
lean_object* v_a_3358_; lean_object* v___x_3360_; uint8_t v_isShared_3361_; uint8_t v_isSharedCheck_3387_; 
v_a_3358_ = lean_ctor_get(v___x_3348_, 0);
v_isSharedCheck_3387_ = !lean_is_exclusive(v___x_3348_);
if (v_isSharedCheck_3387_ == 0)
{
v___x_3360_ = v___x_3348_;
v_isShared_3361_ = v_isSharedCheck_3387_;
goto v_resetjp_3359_;
}
else
{
lean_inc(v_a_3358_);
lean_dec(v___x_3348_);
v___x_3360_ = lean_box(0);
v_isShared_3361_ = v_isSharedCheck_3387_;
goto v_resetjp_3359_;
}
v_resetjp_3359_:
{
uint8_t v___y_3363_; uint8_t v___x_3385_; 
v___x_3385_ = l_Lean_Exception_isInterrupt(v_a_3358_);
if (v___x_3385_ == 0)
{
uint8_t v___x_3386_; 
lean_inc(v_a_3358_);
v___x_3386_ = l_Lean_Exception_isRuntime(v_a_3358_);
v___y_3363_ = v___x_3386_;
goto v___jp_3362_;
}
else
{
v___y_3363_ = v___x_3385_;
goto v___jp_3362_;
}
v___jp_3362_:
{
if (v___y_3363_ == 0)
{
lean_object* v___x_3364_; 
lean_del_object(v___x_3360_);
lean_dec(v_a_3358_);
v___x_3364_ = l_Lean_Meta_SavedState_restore___redArg(v_a_3347_, v___y_3342_, v___y_3344_);
lean_dec(v___y_3344_);
lean_dec(v___y_3342_);
lean_dec(v_a_3347_);
if (lean_obj_tag(v___x_3364_) == 0)
{
lean_object* v___x_3366_; uint8_t v_isShared_3367_; uint8_t v_isSharedCheck_3372_; 
v_isSharedCheck_3372_ = !lean_is_exclusive(v___x_3364_);
if (v_isSharedCheck_3372_ == 0)
{
lean_object* v_unused_3373_; 
v_unused_3373_ = lean_ctor_get(v___x_3364_, 0);
lean_dec(v_unused_3373_);
v___x_3366_ = v___x_3364_;
v_isShared_3367_ = v_isSharedCheck_3372_;
goto v_resetjp_3365_;
}
else
{
lean_dec(v___x_3364_);
v___x_3366_ = lean_box(0);
v_isShared_3367_ = v_isSharedCheck_3372_;
goto v_resetjp_3365_;
}
v_resetjp_3365_:
{
lean_object* v___x_3368_; lean_object* v___x_3370_; 
v___x_3368_ = lean_box(0);
if (v_isShared_3367_ == 0)
{
lean_ctor_set(v___x_3366_, 0, v___x_3368_);
v___x_3370_ = v___x_3366_;
goto v_reusejp_3369_;
}
else
{
lean_object* v_reuseFailAlloc_3371_; 
v_reuseFailAlloc_3371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3371_, 0, v___x_3368_);
v___x_3370_ = v_reuseFailAlloc_3371_;
goto v_reusejp_3369_;
}
v_reusejp_3369_:
{
return v___x_3370_;
}
}
}
else
{
lean_object* v_a_3374_; lean_object* v___x_3376_; uint8_t v_isShared_3377_; uint8_t v_isSharedCheck_3381_; 
v_a_3374_ = lean_ctor_get(v___x_3364_, 0);
v_isSharedCheck_3381_ = !lean_is_exclusive(v___x_3364_);
if (v_isSharedCheck_3381_ == 0)
{
v___x_3376_ = v___x_3364_;
v_isShared_3377_ = v_isSharedCheck_3381_;
goto v_resetjp_3375_;
}
else
{
lean_inc(v_a_3374_);
lean_dec(v___x_3364_);
v___x_3376_ = lean_box(0);
v_isShared_3377_ = v_isSharedCheck_3381_;
goto v_resetjp_3375_;
}
v_resetjp_3375_:
{
lean_object* v___x_3379_; 
if (v_isShared_3377_ == 0)
{
v___x_3379_ = v___x_3376_;
goto v_reusejp_3378_;
}
else
{
lean_object* v_reuseFailAlloc_3380_; 
v_reuseFailAlloc_3380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3380_, 0, v_a_3374_);
v___x_3379_ = v_reuseFailAlloc_3380_;
goto v_reusejp_3378_;
}
v_reusejp_3378_:
{
return v___x_3379_;
}
}
}
}
else
{
lean_object* v___x_3383_; 
lean_dec(v_a_3347_);
lean_dec(v___y_3344_);
lean_dec(v___y_3342_);
if (v_isShared_3361_ == 0)
{
v___x_3383_ = v___x_3360_;
goto v_reusejp_3382_;
}
else
{
lean_object* v_reuseFailAlloc_3384_; 
v_reuseFailAlloc_3384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3384_, 0, v_a_3358_);
v___x_3383_ = v_reuseFailAlloc_3384_;
goto v_reusejp_3382_;
}
v_reusejp_3382_:
{
return v___x_3383_;
}
}
}
}
}
}
else
{
lean_object* v_a_3388_; lean_object* v___x_3390_; uint8_t v_isShared_3391_; uint8_t v_isSharedCheck_3395_; 
lean_dec(v___y_3344_);
lean_dec_ref(v___y_3343_);
lean_dec(v___y_3342_);
lean_dec_ref(v___y_3341_);
lean_dec_ref(v_x_3340_);
v_a_3388_ = lean_ctor_get(v___x_3346_, 0);
v_isSharedCheck_3395_ = !lean_is_exclusive(v___x_3346_);
if (v_isSharedCheck_3395_ == 0)
{
v___x_3390_ = v___x_3346_;
v_isShared_3391_ = v_isSharedCheck_3395_;
goto v_resetjp_3389_;
}
else
{
lean_inc(v_a_3388_);
lean_dec(v___x_3346_);
v___x_3390_ = lean_box(0);
v_isShared_3391_ = v_isSharedCheck_3395_;
goto v_resetjp_3389_;
}
v_resetjp_3389_:
{
lean_object* v___x_3393_; 
if (v_isShared_3391_ == 0)
{
v___x_3393_ = v___x_3390_;
goto v_reusejp_3392_;
}
else
{
lean_object* v_reuseFailAlloc_3394_; 
v_reuseFailAlloc_3394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3394_, 0, v_a_3388_);
v___x_3393_ = v_reuseFailAlloc_3394_;
goto v_reusejp_3392_;
}
v_reusejp_3392_:
{
return v___x_3393_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1___redArg___boxed(lean_object* v_x_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_){
_start:
{
lean_object* v_res_3402_; 
v_res_3402_ = l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1___redArg(v_x_3396_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_);
return v_res_3402_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1(lean_object* v_00_u03b1_3403_, lean_object* v_x_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_){
_start:
{
lean_object* v___x_3410_; 
v___x_3410_ = l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1___redArg(v_x_3404_, v___y_3405_, v___y_3406_, v___y_3407_, v___y_3408_);
return v___x_3410_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1___boxed(lean_object* v_00_u03b1_3411_, lean_object* v_x_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_){
_start:
{
lean_object* v_res_3418_; 
v_res_3418_ = l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1(v_00_u03b1_3411_, v_x_3412_, v___y_3413_, v___y_3414_, v___y_3415_, v___y_3416_);
return v_res_3418_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_MVarId_casesRec_spec__0(lean_object* v_a_3419_, lean_object* v_a_3420_){
_start:
{
if (lean_obj_tag(v_a_3419_) == 0)
{
lean_object* v___x_3421_; 
v___x_3421_ = l_List_reverse___redArg(v_a_3420_);
return v___x_3421_;
}
else
{
lean_object* v_head_3422_; lean_object* v_toInductionSubgoal_3423_; lean_object* v_tail_3424_; lean_object* v___x_3426_; uint8_t v_isShared_3427_; uint8_t v_isSharedCheck_3433_; 
v_head_3422_ = lean_ctor_get(v_a_3419_, 0);
v_toInductionSubgoal_3423_ = lean_ctor_get(v_head_3422_, 0);
lean_inc_ref(v_toInductionSubgoal_3423_);
v_tail_3424_ = lean_ctor_get(v_a_3419_, 1);
v_isSharedCheck_3433_ = !lean_is_exclusive(v_a_3419_);
if (v_isSharedCheck_3433_ == 0)
{
lean_object* v_unused_3434_; 
v_unused_3434_ = lean_ctor_get(v_a_3419_, 0);
lean_dec(v_unused_3434_);
v___x_3426_ = v_a_3419_;
v_isShared_3427_ = v_isSharedCheck_3433_;
goto v_resetjp_3425_;
}
else
{
lean_inc(v_tail_3424_);
lean_dec(v_a_3419_);
v___x_3426_ = lean_box(0);
v_isShared_3427_ = v_isSharedCheck_3433_;
goto v_resetjp_3425_;
}
v_resetjp_3425_:
{
lean_object* v_mvarId_3428_; lean_object* v___x_3430_; 
v_mvarId_3428_ = lean_ctor_get(v_toInductionSubgoal_3423_, 0);
lean_inc(v_mvarId_3428_);
lean_dec_ref(v_toInductionSubgoal_3423_);
if (v_isShared_3427_ == 0)
{
lean_ctor_set(v___x_3426_, 1, v_a_3420_);
lean_ctor_set(v___x_3426_, 0, v_mvarId_3428_);
v___x_3430_ = v___x_3426_;
goto v_reusejp_3429_;
}
else
{
lean_object* v_reuseFailAlloc_3432_; 
v_reuseFailAlloc_3432_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3432_, 0, v_mvarId_3428_);
lean_ctor_set(v_reuseFailAlloc_3432_, 1, v_a_3420_);
v___x_3430_ = v_reuseFailAlloc_3432_;
goto v_reusejp_3429_;
}
v_reusejp_3429_:
{
v_a_3419_ = v_tail_3424_;
v_a_3420_ = v___x_3430_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3___lam__0(lean_object* v_mvarId_3435_, lean_object* v___x_3436_, lean_object* v___x_3437_, uint8_t v___x_3438_, lean_object* v___x_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_){
_start:
{
lean_object* v___x_3445_; 
v___x_3445_ = l_Lean_Meta_Cases_cases(v_mvarId_3435_, v___x_3436_, v___x_3437_, v___x_3438_, v___x_3439_, v___y_3440_, v___y_3441_, v___y_3442_, v___y_3443_);
if (lean_obj_tag(v___x_3445_) == 0)
{
lean_object* v_a_3446_; lean_object* v___x_3448_; uint8_t v_isShared_3449_; uint8_t v_isSharedCheck_3456_; 
v_a_3446_ = lean_ctor_get(v___x_3445_, 0);
v_isSharedCheck_3456_ = !lean_is_exclusive(v___x_3445_);
if (v_isSharedCheck_3456_ == 0)
{
v___x_3448_ = v___x_3445_;
v_isShared_3449_ = v_isSharedCheck_3456_;
goto v_resetjp_3447_;
}
else
{
lean_inc(v_a_3446_);
lean_dec(v___x_3445_);
v___x_3448_ = lean_box(0);
v_isShared_3449_ = v_isSharedCheck_3456_;
goto v_resetjp_3447_;
}
v_resetjp_3447_:
{
lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3454_; 
v___x_3450_ = lean_array_to_list(v_a_3446_);
v___x_3451_ = lean_box(0);
v___x_3452_ = l_List_mapTR_loop___at___00Lean_MVarId_casesRec_spec__0(v___x_3450_, v___x_3451_);
if (v_isShared_3449_ == 0)
{
lean_ctor_set(v___x_3448_, 0, v___x_3452_);
v___x_3454_ = v___x_3448_;
goto v_reusejp_3453_;
}
else
{
lean_object* v_reuseFailAlloc_3455_; 
v_reuseFailAlloc_3455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3455_, 0, v___x_3452_);
v___x_3454_ = v_reuseFailAlloc_3455_;
goto v_reusejp_3453_;
}
v_reusejp_3453_:
{
return v___x_3454_;
}
}
}
else
{
lean_object* v_a_3457_; lean_object* v___x_3459_; uint8_t v_isShared_3460_; uint8_t v_isSharedCheck_3464_; 
v_a_3457_ = lean_ctor_get(v___x_3445_, 0);
v_isSharedCheck_3464_ = !lean_is_exclusive(v___x_3445_);
if (v_isSharedCheck_3464_ == 0)
{
v___x_3459_ = v___x_3445_;
v_isShared_3460_ = v_isSharedCheck_3464_;
goto v_resetjp_3458_;
}
else
{
lean_inc(v_a_3457_);
lean_dec(v___x_3445_);
v___x_3459_ = lean_box(0);
v_isShared_3460_ = v_isSharedCheck_3464_;
goto v_resetjp_3458_;
}
v_resetjp_3458_:
{
lean_object* v___x_3462_; 
if (v_isShared_3460_ == 0)
{
v___x_3462_ = v___x_3459_;
goto v_reusejp_3461_;
}
else
{
lean_object* v_reuseFailAlloc_3463_; 
v_reuseFailAlloc_3463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3463_, 0, v_a_3457_);
v___x_3462_ = v_reuseFailAlloc_3463_;
goto v_reusejp_3461_;
}
v_reusejp_3461_:
{
return v___x_3462_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3___lam__0___boxed(lean_object* v_mvarId_3465_, lean_object* v___x_3466_, lean_object* v___x_3467_, lean_object* v___x_3468_, lean_object* v___x_3469_, lean_object* v___y_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_){
_start:
{
uint8_t v___x_6705__boxed_3475_; lean_object* v_res_3476_; 
v___x_6705__boxed_3475_ = lean_unbox(v___x_3468_);
v_res_3476_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3___lam__0(v_mvarId_3465_, v___x_3466_, v___x_3467_, v___x_6705__boxed_3475_, v___x_3469_, v___y_3470_, v___y_3471_, v___y_3472_, v___y_3473_);
return v_res_3476_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5(lean_object* v_p_3482_, lean_object* v_mvarId_3483_, lean_object* v_as_3484_, size_t v_sz_3485_, size_t v_i_3486_, lean_object* v_b_3487_, lean_object* v___y_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_){
_start:
{
uint8_t v___x_3493_; 
v___x_3493_ = lean_usize_dec_lt(v_i_3486_, v_sz_3485_);
if (v___x_3493_ == 0)
{
lean_object* v___x_3494_; 
lean_dec(v___y_3491_);
lean_dec_ref(v___y_3490_);
lean_dec(v___y_3489_);
lean_dec_ref(v___y_3488_);
lean_dec(v_mvarId_3483_);
lean_dec_ref(v_p_3482_);
v___x_3494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3494_, 0, v_b_3487_);
return v___x_3494_;
}
else
{
lean_object* v_snd_3495_; lean_object* v___x_3497_; uint8_t v_isShared_3498_; uint8_t v_isSharedCheck_3563_; 
v_snd_3495_ = lean_ctor_get(v_b_3487_, 1);
v_isSharedCheck_3563_ = !lean_is_exclusive(v_b_3487_);
if (v_isSharedCheck_3563_ == 0)
{
lean_object* v_unused_3564_; 
v_unused_3564_ = lean_ctor_get(v_b_3487_, 0);
lean_dec(v_unused_3564_);
v___x_3497_ = v_b_3487_;
v_isShared_3498_ = v_isSharedCheck_3563_;
goto v_resetjp_3496_;
}
else
{
lean_inc(v_snd_3495_);
lean_dec(v_b_3487_);
v___x_3497_ = lean_box(0);
v_isShared_3498_ = v_isSharedCheck_3563_;
goto v_resetjp_3496_;
}
v_resetjp_3496_:
{
lean_object* v___x_3499_; lean_object* v_a_3501_; lean_object* v_a_3508_; 
v___x_3499_ = lean_box(0);
v_a_3508_ = lean_array_uget(v_as_3484_, v_i_3486_);
if (lean_obj_tag(v_a_3508_) == 0)
{
v_a_3501_ = v_snd_3495_;
goto v___jp_3500_;
}
else
{
lean_object* v_val_3509_; lean_object* v___x_3511_; uint8_t v_isShared_3512_; uint8_t v_isSharedCheck_3562_; 
v_val_3509_ = lean_ctor_get(v_a_3508_, 0);
v_isSharedCheck_3562_ = !lean_is_exclusive(v_a_3508_);
if (v_isSharedCheck_3562_ == 0)
{
v___x_3511_ = v_a_3508_;
v_isShared_3512_ = v_isSharedCheck_3562_;
goto v_resetjp_3510_;
}
else
{
lean_inc(v_val_3509_);
lean_dec(v_a_3508_);
v___x_3511_ = lean_box(0);
v_isShared_3512_ = v_isSharedCheck_3562_;
goto v_resetjp_3510_;
}
v_resetjp_3510_:
{
lean_object* v___x_3513_; 
lean_inc_ref(v_p_3482_);
lean_inc(v___y_3491_);
lean_inc_ref(v___y_3490_);
lean_inc(v___y_3489_);
lean_inc_ref(v___y_3488_);
lean_inc(v_val_3509_);
v___x_3513_ = lean_apply_6(v_p_3482_, v_val_3509_, v___y_3488_, v___y_3489_, v___y_3490_, v___y_3491_, lean_box(0));
if (lean_obj_tag(v___x_3513_) == 0)
{
lean_object* v_a_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; uint8_t v___x_3517_; 
v_a_3514_ = lean_ctor_get(v___x_3513_, 0);
lean_inc(v_a_3514_);
lean_dec_ref(v___x_3513_);
v___x_3515_ = lean_box(0);
v___x_3516_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5___closed__0));
v___x_3517_ = lean_unbox(v_a_3514_);
lean_dec(v_a_3514_);
if (v___x_3517_ == 0)
{
lean_del_object(v___x_3511_);
lean_dec(v_val_3509_);
lean_dec(v_snd_3495_);
v_a_3501_ = v___x_3516_;
goto v___jp_3500_;
}
else
{
lean_object* v___x_3518_; lean_object* v___x_3519_; uint8_t v___x_3520_; lean_object* v___x_3521_; lean_object* v___f_3522_; lean_object* v___x_3523_; 
v___x_3518_ = l_Lean_LocalDecl_fvarId(v_val_3509_);
lean_dec(v_val_3509_);
v___x_3519_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5___closed__1));
v___x_3520_ = 0;
v___x_3521_ = lean_box(v___x_3520_);
lean_inc(v_mvarId_3483_);
v___f_3522_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3___lam__0___boxed), 10, 5);
lean_closure_set(v___f_3522_, 0, v_mvarId_3483_);
lean_closure_set(v___f_3522_, 1, v___x_3518_);
lean_closure_set(v___f_3522_, 2, v___x_3519_);
lean_closure_set(v___f_3522_, 3, v___x_3521_);
lean_closure_set(v___f_3522_, 4, v___x_3499_);
lean_inc(v___y_3491_);
lean_inc_ref(v___y_3490_);
lean_inc(v___y_3489_);
lean_inc_ref(v___y_3488_);
v___x_3523_ = l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1___redArg(v___f_3522_, v___y_3488_, v___y_3489_, v___y_3490_, v___y_3491_);
if (lean_obj_tag(v___x_3523_) == 0)
{
lean_object* v_a_3524_; lean_object* v___x_3526_; uint8_t v_isShared_3527_; uint8_t v_isSharedCheck_3545_; 
v_a_3524_ = lean_ctor_get(v___x_3523_, 0);
v_isSharedCheck_3545_ = !lean_is_exclusive(v___x_3523_);
if (v_isSharedCheck_3545_ == 0)
{
v___x_3526_ = v___x_3523_;
v_isShared_3527_ = v_isSharedCheck_3545_;
goto v_resetjp_3525_;
}
else
{
lean_inc(v_a_3524_);
lean_dec(v___x_3523_);
v___x_3526_ = lean_box(0);
v_isShared_3527_ = v_isSharedCheck_3545_;
goto v_resetjp_3525_;
}
v_resetjp_3525_:
{
if (lean_obj_tag(v_a_3524_) == 0)
{
lean_del_object(v___x_3526_);
lean_del_object(v___x_3511_);
lean_dec(v_snd_3495_);
v_a_3501_ = v___x_3516_;
goto v___jp_3500_;
}
else
{
lean_object* v___x_3529_; 
lean_del_object(v___x_3497_);
lean_dec(v___y_3491_);
lean_dec_ref(v___y_3490_);
lean_dec(v___y_3489_);
lean_dec_ref(v___y_3488_);
lean_dec(v_mvarId_3483_);
lean_dec_ref(v_p_3482_);
lean_inc_ref(v_a_3524_);
if (v_isShared_3512_ == 0)
{
lean_ctor_set(v___x_3511_, 0, v_a_3524_);
v___x_3529_ = v___x_3511_;
goto v_reusejp_3528_;
}
else
{
lean_object* v_reuseFailAlloc_3544_; 
v_reuseFailAlloc_3544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3544_, 0, v_a_3524_);
v___x_3529_ = v_reuseFailAlloc_3544_;
goto v_reusejp_3528_;
}
v_reusejp_3528_:
{
lean_object* v___x_3531_; uint8_t v_isShared_3532_; uint8_t v_isSharedCheck_3542_; 
v_isSharedCheck_3542_ = !lean_is_exclusive(v_a_3524_);
if (v_isSharedCheck_3542_ == 0)
{
lean_object* v_unused_3543_; 
v_unused_3543_ = lean_ctor_get(v_a_3524_, 0);
lean_dec(v_unused_3543_);
v___x_3531_ = v_a_3524_;
v_isShared_3532_ = v_isSharedCheck_3542_;
goto v_resetjp_3530_;
}
else
{
lean_dec(v_a_3524_);
v___x_3531_ = lean_box(0);
v_isShared_3532_ = v_isSharedCheck_3542_;
goto v_resetjp_3530_;
}
v_resetjp_3530_:
{
lean_object* v___x_3533_; lean_object* v___x_3535_; 
v___x_3533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3533_, 0, v___x_3529_);
lean_ctor_set(v___x_3533_, 1, v___x_3515_);
if (v_isShared_3532_ == 0)
{
lean_ctor_set_tag(v___x_3531_, 0);
lean_ctor_set(v___x_3531_, 0, v___x_3533_);
v___x_3535_ = v___x_3531_;
goto v_reusejp_3534_;
}
else
{
lean_object* v_reuseFailAlloc_3541_; 
v_reuseFailAlloc_3541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3541_, 0, v___x_3533_);
v___x_3535_ = v_reuseFailAlloc_3541_;
goto v_reusejp_3534_;
}
v_reusejp_3534_:
{
lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3539_; 
v___x_3536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3536_, 0, v___x_3535_);
v___x_3537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3537_, 0, v___x_3536_);
lean_ctor_set(v___x_3537_, 1, v_snd_3495_);
if (v_isShared_3527_ == 0)
{
lean_ctor_set(v___x_3526_, 0, v___x_3537_);
v___x_3539_ = v___x_3526_;
goto v_reusejp_3538_;
}
else
{
lean_object* v_reuseFailAlloc_3540_; 
v_reuseFailAlloc_3540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3540_, 0, v___x_3537_);
v___x_3539_ = v_reuseFailAlloc_3540_;
goto v_reusejp_3538_;
}
v_reusejp_3538_:
{
return v___x_3539_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3546_; lean_object* v___x_3548_; uint8_t v_isShared_3549_; uint8_t v_isSharedCheck_3553_; 
lean_del_object(v___x_3511_);
lean_del_object(v___x_3497_);
lean_dec(v_snd_3495_);
lean_dec(v___y_3491_);
lean_dec_ref(v___y_3490_);
lean_dec(v___y_3489_);
lean_dec_ref(v___y_3488_);
lean_dec(v_mvarId_3483_);
lean_dec_ref(v_p_3482_);
v_a_3546_ = lean_ctor_get(v___x_3523_, 0);
v_isSharedCheck_3553_ = !lean_is_exclusive(v___x_3523_);
if (v_isSharedCheck_3553_ == 0)
{
v___x_3548_ = v___x_3523_;
v_isShared_3549_ = v_isSharedCheck_3553_;
goto v_resetjp_3547_;
}
else
{
lean_inc(v_a_3546_);
lean_dec(v___x_3523_);
v___x_3548_ = lean_box(0);
v_isShared_3549_ = v_isSharedCheck_3553_;
goto v_resetjp_3547_;
}
v_resetjp_3547_:
{
lean_object* v___x_3551_; 
if (v_isShared_3549_ == 0)
{
v___x_3551_ = v___x_3548_;
goto v_reusejp_3550_;
}
else
{
lean_object* v_reuseFailAlloc_3552_; 
v_reuseFailAlloc_3552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3552_, 0, v_a_3546_);
v___x_3551_ = v_reuseFailAlloc_3552_;
goto v_reusejp_3550_;
}
v_reusejp_3550_:
{
return v___x_3551_;
}
}
}
}
}
else
{
lean_object* v_a_3554_; lean_object* v___x_3556_; uint8_t v_isShared_3557_; uint8_t v_isSharedCheck_3561_; 
lean_del_object(v___x_3511_);
lean_dec(v_val_3509_);
lean_del_object(v___x_3497_);
lean_dec(v_snd_3495_);
lean_dec(v___y_3491_);
lean_dec_ref(v___y_3490_);
lean_dec(v___y_3489_);
lean_dec_ref(v___y_3488_);
lean_dec(v_mvarId_3483_);
lean_dec_ref(v_p_3482_);
v_a_3554_ = lean_ctor_get(v___x_3513_, 0);
v_isSharedCheck_3561_ = !lean_is_exclusive(v___x_3513_);
if (v_isSharedCheck_3561_ == 0)
{
v___x_3556_ = v___x_3513_;
v_isShared_3557_ = v_isSharedCheck_3561_;
goto v_resetjp_3555_;
}
else
{
lean_inc(v_a_3554_);
lean_dec(v___x_3513_);
v___x_3556_ = lean_box(0);
v_isShared_3557_ = v_isSharedCheck_3561_;
goto v_resetjp_3555_;
}
v_resetjp_3555_:
{
lean_object* v___x_3559_; 
if (v_isShared_3557_ == 0)
{
v___x_3559_ = v___x_3556_;
goto v_reusejp_3558_;
}
else
{
lean_object* v_reuseFailAlloc_3560_; 
v_reuseFailAlloc_3560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3560_, 0, v_a_3554_);
v___x_3559_ = v_reuseFailAlloc_3560_;
goto v_reusejp_3558_;
}
v_reusejp_3558_:
{
return v___x_3559_;
}
}
}
}
}
v___jp_3500_:
{
lean_object* v___x_3503_; 
if (v_isShared_3498_ == 0)
{
lean_ctor_set(v___x_3497_, 1, v_a_3501_);
lean_ctor_set(v___x_3497_, 0, v___x_3499_);
v___x_3503_ = v___x_3497_;
goto v_reusejp_3502_;
}
else
{
lean_object* v_reuseFailAlloc_3507_; 
v_reuseFailAlloc_3507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3507_, 0, v___x_3499_);
lean_ctor_set(v_reuseFailAlloc_3507_, 1, v_a_3501_);
v___x_3503_ = v_reuseFailAlloc_3507_;
goto v_reusejp_3502_;
}
v_reusejp_3502_:
{
size_t v___x_3504_; size_t v___x_3505_; 
v___x_3504_ = ((size_t)1ULL);
v___x_3505_ = lean_usize_add(v_i_3486_, v___x_3504_);
v_i_3486_ = v___x_3505_;
v_b_3487_ = v___x_3503_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5___boxed(lean_object* v_p_3565_, lean_object* v_mvarId_3566_, lean_object* v_as_3567_, lean_object* v_sz_3568_, lean_object* v_i_3569_, lean_object* v_b_3570_, lean_object* v___y_3571_, lean_object* v___y_3572_, lean_object* v___y_3573_, lean_object* v___y_3574_, lean_object* v___y_3575_){
_start:
{
size_t v_sz_boxed_3576_; size_t v_i_boxed_3577_; lean_object* v_res_3578_; 
v_sz_boxed_3576_ = lean_unbox_usize(v_sz_3568_);
lean_dec(v_sz_3568_);
v_i_boxed_3577_ = lean_unbox_usize(v_i_3569_);
lean_dec(v_i_3569_);
v_res_3578_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5(v_p_3565_, v_mvarId_3566_, v_as_3567_, v_sz_boxed_3576_, v_i_boxed_3577_, v_b_3570_, v___y_3571_, v___y_3572_, v___y_3573_, v___y_3574_);
lean_dec_ref(v_as_3567_);
return v_res_3578_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4(lean_object* v_p_3579_, lean_object* v_mvarId_3580_, lean_object* v_as_3581_, size_t v_sz_3582_, size_t v_i_3583_, lean_object* v_b_3584_, lean_object* v___y_3585_, lean_object* v___y_3586_, lean_object* v___y_3587_, lean_object* v___y_3588_){
_start:
{
uint8_t v___x_3590_; 
v___x_3590_ = lean_usize_dec_lt(v_i_3583_, v_sz_3582_);
if (v___x_3590_ == 0)
{
lean_object* v___x_3591_; 
lean_dec(v___y_3588_);
lean_dec_ref(v___y_3587_);
lean_dec(v___y_3586_);
lean_dec_ref(v___y_3585_);
lean_dec(v_mvarId_3580_);
lean_dec_ref(v_p_3579_);
v___x_3591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3591_, 0, v_b_3584_);
return v___x_3591_;
}
else
{
lean_object* v_snd_3592_; lean_object* v___x_3594_; uint8_t v_isShared_3595_; uint8_t v_isSharedCheck_3660_; 
v_snd_3592_ = lean_ctor_get(v_b_3584_, 1);
v_isSharedCheck_3660_ = !lean_is_exclusive(v_b_3584_);
if (v_isSharedCheck_3660_ == 0)
{
lean_object* v_unused_3661_; 
v_unused_3661_ = lean_ctor_get(v_b_3584_, 0);
lean_dec(v_unused_3661_);
v___x_3594_ = v_b_3584_;
v_isShared_3595_ = v_isSharedCheck_3660_;
goto v_resetjp_3593_;
}
else
{
lean_inc(v_snd_3592_);
lean_dec(v_b_3584_);
v___x_3594_ = lean_box(0);
v_isShared_3595_ = v_isSharedCheck_3660_;
goto v_resetjp_3593_;
}
v_resetjp_3593_:
{
lean_object* v___x_3596_; lean_object* v_a_3598_; lean_object* v_a_3605_; 
v___x_3596_ = lean_box(0);
v_a_3605_ = lean_array_uget(v_as_3581_, v_i_3583_);
if (lean_obj_tag(v_a_3605_) == 0)
{
v_a_3598_ = v_snd_3592_;
goto v___jp_3597_;
}
else
{
lean_object* v_val_3606_; lean_object* v___x_3608_; uint8_t v_isShared_3609_; uint8_t v_isSharedCheck_3659_; 
v_val_3606_ = lean_ctor_get(v_a_3605_, 0);
v_isSharedCheck_3659_ = !lean_is_exclusive(v_a_3605_);
if (v_isSharedCheck_3659_ == 0)
{
v___x_3608_ = v_a_3605_;
v_isShared_3609_ = v_isSharedCheck_3659_;
goto v_resetjp_3607_;
}
else
{
lean_inc(v_val_3606_);
lean_dec(v_a_3605_);
v___x_3608_ = lean_box(0);
v_isShared_3609_ = v_isSharedCheck_3659_;
goto v_resetjp_3607_;
}
v_resetjp_3607_:
{
lean_object* v___x_3610_; 
lean_inc_ref(v_p_3579_);
lean_inc(v___y_3588_);
lean_inc_ref(v___y_3587_);
lean_inc(v___y_3586_);
lean_inc_ref(v___y_3585_);
lean_inc(v_val_3606_);
v___x_3610_ = lean_apply_6(v_p_3579_, v_val_3606_, v___y_3585_, v___y_3586_, v___y_3587_, v___y_3588_, lean_box(0));
if (lean_obj_tag(v___x_3610_) == 0)
{
lean_object* v_a_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; uint8_t v___x_3614_; 
v_a_3611_ = lean_ctor_get(v___x_3610_, 0);
lean_inc(v_a_3611_);
lean_dec_ref(v___x_3610_);
v___x_3612_ = lean_box(0);
v___x_3613_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5___closed__0));
v___x_3614_ = lean_unbox(v_a_3611_);
lean_dec(v_a_3611_);
if (v___x_3614_ == 0)
{
lean_del_object(v___x_3608_);
lean_dec(v_val_3606_);
lean_dec(v_snd_3592_);
v_a_3598_ = v___x_3613_;
goto v___jp_3597_;
}
else
{
lean_object* v___x_3615_; lean_object* v___x_3616_; uint8_t v___x_3617_; lean_object* v___x_3618_; lean_object* v___f_3619_; lean_object* v___x_3620_; 
v___x_3615_ = l_Lean_LocalDecl_fvarId(v_val_3606_);
lean_dec(v_val_3606_);
v___x_3616_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5___closed__1));
v___x_3617_ = 0;
v___x_3618_ = lean_box(v___x_3617_);
lean_inc(v_mvarId_3580_);
v___f_3619_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3___lam__0___boxed), 10, 5);
lean_closure_set(v___f_3619_, 0, v_mvarId_3580_);
lean_closure_set(v___f_3619_, 1, v___x_3615_);
lean_closure_set(v___f_3619_, 2, v___x_3616_);
lean_closure_set(v___f_3619_, 3, v___x_3618_);
lean_closure_set(v___f_3619_, 4, v___x_3596_);
lean_inc(v___y_3588_);
lean_inc_ref(v___y_3587_);
lean_inc(v___y_3586_);
lean_inc_ref(v___y_3585_);
v___x_3620_ = l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1___redArg(v___f_3619_, v___y_3585_, v___y_3586_, v___y_3587_, v___y_3588_);
if (lean_obj_tag(v___x_3620_) == 0)
{
lean_object* v_a_3621_; lean_object* v___x_3623_; uint8_t v_isShared_3624_; uint8_t v_isSharedCheck_3642_; 
v_a_3621_ = lean_ctor_get(v___x_3620_, 0);
v_isSharedCheck_3642_ = !lean_is_exclusive(v___x_3620_);
if (v_isSharedCheck_3642_ == 0)
{
v___x_3623_ = v___x_3620_;
v_isShared_3624_ = v_isSharedCheck_3642_;
goto v_resetjp_3622_;
}
else
{
lean_inc(v_a_3621_);
lean_dec(v___x_3620_);
v___x_3623_ = lean_box(0);
v_isShared_3624_ = v_isSharedCheck_3642_;
goto v_resetjp_3622_;
}
v_resetjp_3622_:
{
if (lean_obj_tag(v_a_3621_) == 0)
{
lean_del_object(v___x_3623_);
lean_del_object(v___x_3608_);
lean_dec(v_snd_3592_);
v_a_3598_ = v___x_3613_;
goto v___jp_3597_;
}
else
{
lean_object* v___x_3626_; 
lean_del_object(v___x_3594_);
lean_dec(v___y_3588_);
lean_dec_ref(v___y_3587_);
lean_dec(v___y_3586_);
lean_dec_ref(v___y_3585_);
lean_dec(v_mvarId_3580_);
lean_dec_ref(v_p_3579_);
lean_inc_ref(v_a_3621_);
if (v_isShared_3609_ == 0)
{
lean_ctor_set(v___x_3608_, 0, v_a_3621_);
v___x_3626_ = v___x_3608_;
goto v_reusejp_3625_;
}
else
{
lean_object* v_reuseFailAlloc_3641_; 
v_reuseFailAlloc_3641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3641_, 0, v_a_3621_);
v___x_3626_ = v_reuseFailAlloc_3641_;
goto v_reusejp_3625_;
}
v_reusejp_3625_:
{
lean_object* v___x_3628_; uint8_t v_isShared_3629_; uint8_t v_isSharedCheck_3639_; 
v_isSharedCheck_3639_ = !lean_is_exclusive(v_a_3621_);
if (v_isSharedCheck_3639_ == 0)
{
lean_object* v_unused_3640_; 
v_unused_3640_ = lean_ctor_get(v_a_3621_, 0);
lean_dec(v_unused_3640_);
v___x_3628_ = v_a_3621_;
v_isShared_3629_ = v_isSharedCheck_3639_;
goto v_resetjp_3627_;
}
else
{
lean_dec(v_a_3621_);
v___x_3628_ = lean_box(0);
v_isShared_3629_ = v_isSharedCheck_3639_;
goto v_resetjp_3627_;
}
v_resetjp_3627_:
{
lean_object* v___x_3630_; lean_object* v___x_3632_; 
v___x_3630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3630_, 0, v___x_3626_);
lean_ctor_set(v___x_3630_, 1, v___x_3612_);
if (v_isShared_3629_ == 0)
{
lean_ctor_set_tag(v___x_3628_, 0);
lean_ctor_set(v___x_3628_, 0, v___x_3630_);
v___x_3632_ = v___x_3628_;
goto v_reusejp_3631_;
}
else
{
lean_object* v_reuseFailAlloc_3638_; 
v_reuseFailAlloc_3638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3638_, 0, v___x_3630_);
v___x_3632_ = v_reuseFailAlloc_3638_;
goto v_reusejp_3631_;
}
v_reusejp_3631_:
{
lean_object* v___x_3633_; lean_object* v___x_3634_; lean_object* v___x_3636_; 
v___x_3633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3633_, 0, v___x_3632_);
v___x_3634_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3634_, 0, v___x_3633_);
lean_ctor_set(v___x_3634_, 1, v_snd_3592_);
if (v_isShared_3624_ == 0)
{
lean_ctor_set(v___x_3623_, 0, v___x_3634_);
v___x_3636_ = v___x_3623_;
goto v_reusejp_3635_;
}
else
{
lean_object* v_reuseFailAlloc_3637_; 
v_reuseFailAlloc_3637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3637_, 0, v___x_3634_);
v___x_3636_ = v_reuseFailAlloc_3637_;
goto v_reusejp_3635_;
}
v_reusejp_3635_:
{
return v___x_3636_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3643_; lean_object* v___x_3645_; uint8_t v_isShared_3646_; uint8_t v_isSharedCheck_3650_; 
lean_del_object(v___x_3608_);
lean_del_object(v___x_3594_);
lean_dec(v_snd_3592_);
lean_dec(v___y_3588_);
lean_dec_ref(v___y_3587_);
lean_dec(v___y_3586_);
lean_dec_ref(v___y_3585_);
lean_dec(v_mvarId_3580_);
lean_dec_ref(v_p_3579_);
v_a_3643_ = lean_ctor_get(v___x_3620_, 0);
v_isSharedCheck_3650_ = !lean_is_exclusive(v___x_3620_);
if (v_isSharedCheck_3650_ == 0)
{
v___x_3645_ = v___x_3620_;
v_isShared_3646_ = v_isSharedCheck_3650_;
goto v_resetjp_3644_;
}
else
{
lean_inc(v_a_3643_);
lean_dec(v___x_3620_);
v___x_3645_ = lean_box(0);
v_isShared_3646_ = v_isSharedCheck_3650_;
goto v_resetjp_3644_;
}
v_resetjp_3644_:
{
lean_object* v___x_3648_; 
if (v_isShared_3646_ == 0)
{
v___x_3648_ = v___x_3645_;
goto v_reusejp_3647_;
}
else
{
lean_object* v_reuseFailAlloc_3649_; 
v_reuseFailAlloc_3649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3649_, 0, v_a_3643_);
v___x_3648_ = v_reuseFailAlloc_3649_;
goto v_reusejp_3647_;
}
v_reusejp_3647_:
{
return v___x_3648_;
}
}
}
}
}
else
{
lean_object* v_a_3651_; lean_object* v___x_3653_; uint8_t v_isShared_3654_; uint8_t v_isSharedCheck_3658_; 
lean_del_object(v___x_3608_);
lean_dec(v_val_3606_);
lean_del_object(v___x_3594_);
lean_dec(v_snd_3592_);
lean_dec(v___y_3588_);
lean_dec_ref(v___y_3587_);
lean_dec(v___y_3586_);
lean_dec_ref(v___y_3585_);
lean_dec(v_mvarId_3580_);
lean_dec_ref(v_p_3579_);
v_a_3651_ = lean_ctor_get(v___x_3610_, 0);
v_isSharedCheck_3658_ = !lean_is_exclusive(v___x_3610_);
if (v_isSharedCheck_3658_ == 0)
{
v___x_3653_ = v___x_3610_;
v_isShared_3654_ = v_isSharedCheck_3658_;
goto v_resetjp_3652_;
}
else
{
lean_inc(v_a_3651_);
lean_dec(v___x_3610_);
v___x_3653_ = lean_box(0);
v_isShared_3654_ = v_isSharedCheck_3658_;
goto v_resetjp_3652_;
}
v_resetjp_3652_:
{
lean_object* v___x_3656_; 
if (v_isShared_3654_ == 0)
{
v___x_3656_ = v___x_3653_;
goto v_reusejp_3655_;
}
else
{
lean_object* v_reuseFailAlloc_3657_; 
v_reuseFailAlloc_3657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3657_, 0, v_a_3651_);
v___x_3656_ = v_reuseFailAlloc_3657_;
goto v_reusejp_3655_;
}
v_reusejp_3655_:
{
return v___x_3656_;
}
}
}
}
}
v___jp_3597_:
{
lean_object* v___x_3600_; 
if (v_isShared_3595_ == 0)
{
lean_ctor_set(v___x_3594_, 1, v_a_3598_);
lean_ctor_set(v___x_3594_, 0, v___x_3596_);
v___x_3600_ = v___x_3594_;
goto v_reusejp_3599_;
}
else
{
lean_object* v_reuseFailAlloc_3604_; 
v_reuseFailAlloc_3604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3604_, 0, v___x_3596_);
lean_ctor_set(v_reuseFailAlloc_3604_, 1, v_a_3598_);
v___x_3600_ = v_reuseFailAlloc_3604_;
goto v_reusejp_3599_;
}
v_reusejp_3599_:
{
size_t v___x_3601_; size_t v___x_3602_; lean_object* v___x_3603_; 
v___x_3601_ = ((size_t)1ULL);
v___x_3602_ = lean_usize_add(v_i_3583_, v___x_3601_);
v___x_3603_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5(v_p_3579_, v_mvarId_3580_, v_as_3581_, v_sz_3582_, v___x_3602_, v___x_3600_, v___y_3585_, v___y_3586_, v___y_3587_, v___y_3588_);
return v___x_3603_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4___boxed(lean_object* v_p_3662_, lean_object* v_mvarId_3663_, lean_object* v_as_3664_, lean_object* v_sz_3665_, lean_object* v_i_3666_, lean_object* v_b_3667_, lean_object* v___y_3668_, lean_object* v___y_3669_, lean_object* v___y_3670_, lean_object* v___y_3671_, lean_object* v___y_3672_){
_start:
{
size_t v_sz_boxed_3673_; size_t v_i_boxed_3674_; lean_object* v_res_3675_; 
v_sz_boxed_3673_ = lean_unbox_usize(v_sz_3665_);
lean_dec(v_sz_3665_);
v_i_boxed_3674_ = lean_unbox_usize(v_i_3666_);
lean_dec(v_i_3666_);
v_res_3675_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4(v_p_3662_, v_mvarId_3663_, v_as_3664_, v_sz_boxed_3673_, v_i_boxed_3674_, v_b_3667_, v___y_3668_, v___y_3669_, v___y_3670_, v___y_3671_);
lean_dec_ref(v_as_3664_);
return v_res_3675_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2(lean_object* v_p_3676_, lean_object* v_mvarId_3677_, lean_object* v_inh_3678_, lean_object* v_n_3679_, lean_object* v_b_3680_, lean_object* v___y_3681_, lean_object* v___y_3682_, lean_object* v___y_3683_, lean_object* v___y_3684_){
_start:
{
if (lean_obj_tag(v_n_3679_) == 0)
{
lean_object* v_cs_3686_; lean_object* v___x_3688_; uint8_t v_isShared_3689_; uint8_t v_isSharedCheck_3720_; 
v_cs_3686_ = lean_ctor_get(v_n_3679_, 0);
v_isSharedCheck_3720_ = !lean_is_exclusive(v_n_3679_);
if (v_isSharedCheck_3720_ == 0)
{
v___x_3688_ = v_n_3679_;
v_isShared_3689_ = v_isSharedCheck_3720_;
goto v_resetjp_3687_;
}
else
{
lean_inc(v_cs_3686_);
lean_dec(v_n_3679_);
v___x_3688_ = lean_box(0);
v_isShared_3689_ = v_isSharedCheck_3720_;
goto v_resetjp_3687_;
}
v_resetjp_3687_:
{
lean_object* v___x_3690_; lean_object* v___x_3691_; size_t v_sz_3692_; size_t v___x_3693_; lean_object* v___x_3694_; 
v___x_3690_ = lean_box(0);
v___x_3691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3691_, 0, v___x_3690_);
lean_ctor_set(v___x_3691_, 1, v_b_3680_);
v_sz_3692_ = lean_array_size(v_cs_3686_);
v___x_3693_ = ((size_t)0ULL);
v___x_3694_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__3(v_p_3676_, v_mvarId_3677_, v_inh_3678_, v_cs_3686_, v_sz_3692_, v___x_3693_, v___x_3691_, v___y_3681_, v___y_3682_, v___y_3683_, v___y_3684_);
lean_dec_ref(v_cs_3686_);
if (lean_obj_tag(v___x_3694_) == 0)
{
lean_object* v_a_3695_; lean_object* v___x_3697_; uint8_t v_isShared_3698_; uint8_t v_isSharedCheck_3711_; 
v_a_3695_ = lean_ctor_get(v___x_3694_, 0);
v_isSharedCheck_3711_ = !lean_is_exclusive(v___x_3694_);
if (v_isSharedCheck_3711_ == 0)
{
v___x_3697_ = v___x_3694_;
v_isShared_3698_ = v_isSharedCheck_3711_;
goto v_resetjp_3696_;
}
else
{
lean_inc(v_a_3695_);
lean_dec(v___x_3694_);
v___x_3697_ = lean_box(0);
v_isShared_3698_ = v_isSharedCheck_3711_;
goto v_resetjp_3696_;
}
v_resetjp_3696_:
{
lean_object* v_fst_3699_; 
v_fst_3699_ = lean_ctor_get(v_a_3695_, 0);
if (lean_obj_tag(v_fst_3699_) == 0)
{
lean_object* v_snd_3700_; lean_object* v___x_3702_; 
v_snd_3700_ = lean_ctor_get(v_a_3695_, 1);
lean_inc(v_snd_3700_);
lean_dec(v_a_3695_);
if (v_isShared_3689_ == 0)
{
lean_ctor_set_tag(v___x_3688_, 1);
lean_ctor_set(v___x_3688_, 0, v_snd_3700_);
v___x_3702_ = v___x_3688_;
goto v_reusejp_3701_;
}
else
{
lean_object* v_reuseFailAlloc_3706_; 
v_reuseFailAlloc_3706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3706_, 0, v_snd_3700_);
v___x_3702_ = v_reuseFailAlloc_3706_;
goto v_reusejp_3701_;
}
v_reusejp_3701_:
{
lean_object* v___x_3704_; 
if (v_isShared_3698_ == 0)
{
lean_ctor_set(v___x_3697_, 0, v___x_3702_);
v___x_3704_ = v___x_3697_;
goto v_reusejp_3703_;
}
else
{
lean_object* v_reuseFailAlloc_3705_; 
v_reuseFailAlloc_3705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3705_, 0, v___x_3702_);
v___x_3704_ = v_reuseFailAlloc_3705_;
goto v_reusejp_3703_;
}
v_reusejp_3703_:
{
return v___x_3704_;
}
}
}
else
{
lean_object* v_val_3707_; lean_object* v___x_3709_; 
lean_inc_ref(v_fst_3699_);
lean_dec(v_a_3695_);
lean_del_object(v___x_3688_);
v_val_3707_ = lean_ctor_get(v_fst_3699_, 0);
lean_inc(v_val_3707_);
lean_dec_ref(v_fst_3699_);
if (v_isShared_3698_ == 0)
{
lean_ctor_set(v___x_3697_, 0, v_val_3707_);
v___x_3709_ = v___x_3697_;
goto v_reusejp_3708_;
}
else
{
lean_object* v_reuseFailAlloc_3710_; 
v_reuseFailAlloc_3710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3710_, 0, v_val_3707_);
v___x_3709_ = v_reuseFailAlloc_3710_;
goto v_reusejp_3708_;
}
v_reusejp_3708_:
{
return v___x_3709_;
}
}
}
}
else
{
lean_object* v_a_3712_; lean_object* v___x_3714_; uint8_t v_isShared_3715_; uint8_t v_isSharedCheck_3719_; 
lean_del_object(v___x_3688_);
v_a_3712_ = lean_ctor_get(v___x_3694_, 0);
v_isSharedCheck_3719_ = !lean_is_exclusive(v___x_3694_);
if (v_isSharedCheck_3719_ == 0)
{
v___x_3714_ = v___x_3694_;
v_isShared_3715_ = v_isSharedCheck_3719_;
goto v_resetjp_3713_;
}
else
{
lean_inc(v_a_3712_);
lean_dec(v___x_3694_);
v___x_3714_ = lean_box(0);
v_isShared_3715_ = v_isSharedCheck_3719_;
goto v_resetjp_3713_;
}
v_resetjp_3713_:
{
lean_object* v___x_3717_; 
if (v_isShared_3715_ == 0)
{
v___x_3717_ = v___x_3714_;
goto v_reusejp_3716_;
}
else
{
lean_object* v_reuseFailAlloc_3718_; 
v_reuseFailAlloc_3718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3718_, 0, v_a_3712_);
v___x_3717_ = v_reuseFailAlloc_3718_;
goto v_reusejp_3716_;
}
v_reusejp_3716_:
{
return v___x_3717_;
}
}
}
}
}
else
{
lean_object* v_vs_3721_; lean_object* v___x_3723_; uint8_t v_isShared_3724_; uint8_t v_isSharedCheck_3755_; 
v_vs_3721_ = lean_ctor_get(v_n_3679_, 0);
v_isSharedCheck_3755_ = !lean_is_exclusive(v_n_3679_);
if (v_isSharedCheck_3755_ == 0)
{
v___x_3723_ = v_n_3679_;
v_isShared_3724_ = v_isSharedCheck_3755_;
goto v_resetjp_3722_;
}
else
{
lean_inc(v_vs_3721_);
lean_dec(v_n_3679_);
v___x_3723_ = lean_box(0);
v_isShared_3724_ = v_isSharedCheck_3755_;
goto v_resetjp_3722_;
}
v_resetjp_3722_:
{
lean_object* v___x_3725_; lean_object* v___x_3726_; size_t v_sz_3727_; size_t v___x_3728_; lean_object* v___x_3729_; 
v___x_3725_ = lean_box(0);
v___x_3726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3726_, 0, v___x_3725_);
lean_ctor_set(v___x_3726_, 1, v_b_3680_);
v_sz_3727_ = lean_array_size(v_vs_3721_);
v___x_3728_ = ((size_t)0ULL);
v___x_3729_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4(v_p_3676_, v_mvarId_3677_, v_vs_3721_, v_sz_3727_, v___x_3728_, v___x_3726_, v___y_3681_, v___y_3682_, v___y_3683_, v___y_3684_);
lean_dec_ref(v_vs_3721_);
if (lean_obj_tag(v___x_3729_) == 0)
{
lean_object* v_a_3730_; lean_object* v___x_3732_; uint8_t v_isShared_3733_; uint8_t v_isSharedCheck_3746_; 
v_a_3730_ = lean_ctor_get(v___x_3729_, 0);
v_isSharedCheck_3746_ = !lean_is_exclusive(v___x_3729_);
if (v_isSharedCheck_3746_ == 0)
{
v___x_3732_ = v___x_3729_;
v_isShared_3733_ = v_isSharedCheck_3746_;
goto v_resetjp_3731_;
}
else
{
lean_inc(v_a_3730_);
lean_dec(v___x_3729_);
v___x_3732_ = lean_box(0);
v_isShared_3733_ = v_isSharedCheck_3746_;
goto v_resetjp_3731_;
}
v_resetjp_3731_:
{
lean_object* v_fst_3734_; 
v_fst_3734_ = lean_ctor_get(v_a_3730_, 0);
if (lean_obj_tag(v_fst_3734_) == 0)
{
lean_object* v_snd_3735_; lean_object* v___x_3737_; 
v_snd_3735_ = lean_ctor_get(v_a_3730_, 1);
lean_inc(v_snd_3735_);
lean_dec(v_a_3730_);
if (v_isShared_3724_ == 0)
{
lean_ctor_set(v___x_3723_, 0, v_snd_3735_);
v___x_3737_ = v___x_3723_;
goto v_reusejp_3736_;
}
else
{
lean_object* v_reuseFailAlloc_3741_; 
v_reuseFailAlloc_3741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3741_, 0, v_snd_3735_);
v___x_3737_ = v_reuseFailAlloc_3741_;
goto v_reusejp_3736_;
}
v_reusejp_3736_:
{
lean_object* v___x_3739_; 
if (v_isShared_3733_ == 0)
{
lean_ctor_set(v___x_3732_, 0, v___x_3737_);
v___x_3739_ = v___x_3732_;
goto v_reusejp_3738_;
}
else
{
lean_object* v_reuseFailAlloc_3740_; 
v_reuseFailAlloc_3740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3740_, 0, v___x_3737_);
v___x_3739_ = v_reuseFailAlloc_3740_;
goto v_reusejp_3738_;
}
v_reusejp_3738_:
{
return v___x_3739_;
}
}
}
else
{
lean_object* v_val_3742_; lean_object* v___x_3744_; 
lean_inc_ref(v_fst_3734_);
lean_dec(v_a_3730_);
lean_del_object(v___x_3723_);
v_val_3742_ = lean_ctor_get(v_fst_3734_, 0);
lean_inc(v_val_3742_);
lean_dec_ref(v_fst_3734_);
if (v_isShared_3733_ == 0)
{
lean_ctor_set(v___x_3732_, 0, v_val_3742_);
v___x_3744_ = v___x_3732_;
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
lean_del_object(v___x_3723_);
v_a_3747_ = lean_ctor_get(v___x_3729_, 0);
v_isSharedCheck_3754_ = !lean_is_exclusive(v___x_3729_);
if (v_isSharedCheck_3754_ == 0)
{
v___x_3749_ = v___x_3729_;
v_isShared_3750_ = v_isSharedCheck_3754_;
goto v_resetjp_3748_;
}
else
{
lean_inc(v_a_3747_);
lean_dec(v___x_3729_);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__3(lean_object* v_p_3756_, lean_object* v_mvarId_3757_, lean_object* v_inh_3758_, lean_object* v_as_3759_, size_t v_sz_3760_, size_t v_i_3761_, lean_object* v_b_3762_, lean_object* v___y_3763_, lean_object* v___y_3764_, lean_object* v___y_3765_, lean_object* v___y_3766_){
_start:
{
uint8_t v___x_3768_; 
v___x_3768_ = lean_usize_dec_lt(v_i_3761_, v_sz_3760_);
if (v___x_3768_ == 0)
{
lean_object* v___x_3769_; 
lean_dec(v___y_3766_);
lean_dec_ref(v___y_3765_);
lean_dec(v___y_3764_);
lean_dec_ref(v___y_3763_);
lean_dec(v_mvarId_3757_);
lean_dec_ref(v_p_3756_);
v___x_3769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3769_, 0, v_b_3762_);
return v___x_3769_;
}
else
{
lean_object* v_snd_3770_; lean_object* v___x_3772_; uint8_t v_isShared_3773_; uint8_t v_isSharedCheck_3804_; 
v_snd_3770_ = lean_ctor_get(v_b_3762_, 1);
v_isSharedCheck_3804_ = !lean_is_exclusive(v_b_3762_);
if (v_isSharedCheck_3804_ == 0)
{
lean_object* v_unused_3805_; 
v_unused_3805_ = lean_ctor_get(v_b_3762_, 0);
lean_dec(v_unused_3805_);
v___x_3772_ = v_b_3762_;
v_isShared_3773_ = v_isSharedCheck_3804_;
goto v_resetjp_3771_;
}
else
{
lean_inc(v_snd_3770_);
lean_dec(v_b_3762_);
v___x_3772_ = lean_box(0);
v_isShared_3773_ = v_isSharedCheck_3804_;
goto v_resetjp_3771_;
}
v_resetjp_3771_:
{
lean_object* v_a_3774_; lean_object* v___x_3775_; 
v_a_3774_ = lean_array_uget_borrowed(v_as_3759_, v_i_3761_);
lean_inc(v___y_3766_);
lean_inc_ref(v___y_3765_);
lean_inc(v___y_3764_);
lean_inc_ref(v___y_3763_);
lean_inc(v_snd_3770_);
lean_inc(v_a_3774_);
lean_inc(v_mvarId_3757_);
lean_inc_ref(v_p_3756_);
v___x_3775_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2(v_p_3756_, v_mvarId_3757_, v_inh_3758_, v_a_3774_, v_snd_3770_, v___y_3763_, v___y_3764_, v___y_3765_, v___y_3766_);
if (lean_obj_tag(v___x_3775_) == 0)
{
lean_object* v_a_3776_; lean_object* v___x_3778_; uint8_t v_isShared_3779_; uint8_t v_isSharedCheck_3795_; 
v_a_3776_ = lean_ctor_get(v___x_3775_, 0);
v_isSharedCheck_3795_ = !lean_is_exclusive(v___x_3775_);
if (v_isSharedCheck_3795_ == 0)
{
v___x_3778_ = v___x_3775_;
v_isShared_3779_ = v_isSharedCheck_3795_;
goto v_resetjp_3777_;
}
else
{
lean_inc(v_a_3776_);
lean_dec(v___x_3775_);
v___x_3778_ = lean_box(0);
v_isShared_3779_ = v_isSharedCheck_3795_;
goto v_resetjp_3777_;
}
v_resetjp_3777_:
{
if (lean_obj_tag(v_a_3776_) == 0)
{
lean_object* v___x_3780_; lean_object* v___x_3782_; 
lean_dec(v___y_3766_);
lean_dec_ref(v___y_3765_);
lean_dec(v___y_3764_);
lean_dec_ref(v___y_3763_);
lean_dec(v_mvarId_3757_);
lean_dec_ref(v_p_3756_);
v___x_3780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3780_, 0, v_a_3776_);
if (v_isShared_3773_ == 0)
{
lean_ctor_set(v___x_3772_, 0, v___x_3780_);
v___x_3782_ = v___x_3772_;
goto v_reusejp_3781_;
}
else
{
lean_object* v_reuseFailAlloc_3786_; 
v_reuseFailAlloc_3786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3786_, 0, v___x_3780_);
lean_ctor_set(v_reuseFailAlloc_3786_, 1, v_snd_3770_);
v___x_3782_ = v_reuseFailAlloc_3786_;
goto v_reusejp_3781_;
}
v_reusejp_3781_:
{
lean_object* v___x_3784_; 
if (v_isShared_3779_ == 0)
{
lean_ctor_set(v___x_3778_, 0, v___x_3782_);
v___x_3784_ = v___x_3778_;
goto v_reusejp_3783_;
}
else
{
lean_object* v_reuseFailAlloc_3785_; 
v_reuseFailAlloc_3785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3785_, 0, v___x_3782_);
v___x_3784_ = v_reuseFailAlloc_3785_;
goto v_reusejp_3783_;
}
v_reusejp_3783_:
{
return v___x_3784_;
}
}
}
else
{
lean_object* v_a_3787_; lean_object* v___x_3788_; lean_object* v___x_3790_; 
lean_del_object(v___x_3778_);
lean_dec(v_snd_3770_);
v_a_3787_ = lean_ctor_get(v_a_3776_, 0);
lean_inc(v_a_3787_);
lean_dec_ref(v_a_3776_);
v___x_3788_ = lean_box(0);
if (v_isShared_3773_ == 0)
{
lean_ctor_set(v___x_3772_, 1, v_a_3787_);
lean_ctor_set(v___x_3772_, 0, v___x_3788_);
v___x_3790_ = v___x_3772_;
goto v_reusejp_3789_;
}
else
{
lean_object* v_reuseFailAlloc_3794_; 
v_reuseFailAlloc_3794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3794_, 0, v___x_3788_);
lean_ctor_set(v_reuseFailAlloc_3794_, 1, v_a_3787_);
v___x_3790_ = v_reuseFailAlloc_3794_;
goto v_reusejp_3789_;
}
v_reusejp_3789_:
{
size_t v___x_3791_; size_t v___x_3792_; 
v___x_3791_ = ((size_t)1ULL);
v___x_3792_ = lean_usize_add(v_i_3761_, v___x_3791_);
v_i_3761_ = v___x_3792_;
v_b_3762_ = v___x_3790_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3796_; lean_object* v___x_3798_; uint8_t v_isShared_3799_; uint8_t v_isSharedCheck_3803_; 
lean_del_object(v___x_3772_);
lean_dec(v_snd_3770_);
lean_dec(v___y_3766_);
lean_dec_ref(v___y_3765_);
lean_dec(v___y_3764_);
lean_dec_ref(v___y_3763_);
lean_dec(v_mvarId_3757_);
lean_dec_ref(v_p_3756_);
v_a_3796_ = lean_ctor_get(v___x_3775_, 0);
v_isSharedCheck_3803_ = !lean_is_exclusive(v___x_3775_);
if (v_isSharedCheck_3803_ == 0)
{
v___x_3798_ = v___x_3775_;
v_isShared_3799_ = v_isSharedCheck_3803_;
goto v_resetjp_3797_;
}
else
{
lean_inc(v_a_3796_);
lean_dec(v___x_3775_);
v___x_3798_ = lean_box(0);
v_isShared_3799_ = v_isSharedCheck_3803_;
goto v_resetjp_3797_;
}
v_resetjp_3797_:
{
lean_object* v___x_3801_; 
if (v_isShared_3799_ == 0)
{
v___x_3801_ = v___x_3798_;
goto v_reusejp_3800_;
}
else
{
lean_object* v_reuseFailAlloc_3802_; 
v_reuseFailAlloc_3802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3802_, 0, v_a_3796_);
v___x_3801_ = v_reuseFailAlloc_3802_;
goto v_reusejp_3800_;
}
v_reusejp_3800_:
{
return v___x_3801_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__3___boxed(lean_object* v_p_3806_, lean_object* v_mvarId_3807_, lean_object* v_inh_3808_, lean_object* v_as_3809_, lean_object* v_sz_3810_, lean_object* v_i_3811_, lean_object* v_b_3812_, lean_object* v___y_3813_, lean_object* v___y_3814_, lean_object* v___y_3815_, lean_object* v___y_3816_, lean_object* v___y_3817_){
_start:
{
size_t v_sz_boxed_3818_; size_t v_i_boxed_3819_; lean_object* v_res_3820_; 
v_sz_boxed_3818_ = lean_unbox_usize(v_sz_3810_);
lean_dec(v_sz_3810_);
v_i_boxed_3819_ = lean_unbox_usize(v_i_3811_);
lean_dec(v_i_3811_);
v_res_3820_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__3(v_p_3806_, v_mvarId_3807_, v_inh_3808_, v_as_3809_, v_sz_boxed_3818_, v_i_boxed_3819_, v_b_3812_, v___y_3813_, v___y_3814_, v___y_3815_, v___y_3816_);
lean_dec_ref(v_as_3809_);
lean_dec_ref(v_inh_3808_);
return v_res_3820_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2___boxed(lean_object* v_p_3821_, lean_object* v_mvarId_3822_, lean_object* v_inh_3823_, lean_object* v_n_3824_, lean_object* v_b_3825_, lean_object* v___y_3826_, lean_object* v___y_3827_, lean_object* v___y_3828_, lean_object* v___y_3829_, lean_object* v___y_3830_){
_start:
{
lean_object* v_res_3831_; 
v_res_3831_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2(v_p_3821_, v_mvarId_3822_, v_inh_3823_, v_n_3824_, v_b_3825_, v___y_3826_, v___y_3827_, v___y_3828_, v___y_3829_);
lean_dec_ref(v_inh_3823_);
return v_res_3831_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3_spec__6(lean_object* v_p_3835_, lean_object* v_mvarId_3836_, lean_object* v_as_3837_, size_t v_sz_3838_, size_t v_i_3839_, lean_object* v_b_3840_, lean_object* v___y_3841_, lean_object* v___y_3842_, lean_object* v___y_3843_, lean_object* v___y_3844_){
_start:
{
uint8_t v___x_3846_; 
v___x_3846_ = lean_usize_dec_lt(v_i_3839_, v_sz_3838_);
if (v___x_3846_ == 0)
{
lean_object* v___x_3847_; 
lean_dec(v___y_3844_);
lean_dec_ref(v___y_3843_);
lean_dec(v___y_3842_);
lean_dec_ref(v___y_3841_);
lean_dec(v_mvarId_3836_);
lean_dec_ref(v_p_3835_);
v___x_3847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3847_, 0, v_b_3840_);
return v___x_3847_;
}
else
{
lean_object* v_snd_3848_; lean_object* v___x_3850_; uint8_t v_isShared_3851_; uint8_t v_isSharedCheck_3915_; 
v_snd_3848_ = lean_ctor_get(v_b_3840_, 1);
v_isSharedCheck_3915_ = !lean_is_exclusive(v_b_3840_);
if (v_isSharedCheck_3915_ == 0)
{
lean_object* v_unused_3916_; 
v_unused_3916_ = lean_ctor_get(v_b_3840_, 0);
lean_dec(v_unused_3916_);
v___x_3850_ = v_b_3840_;
v_isShared_3851_ = v_isSharedCheck_3915_;
goto v_resetjp_3849_;
}
else
{
lean_inc(v_snd_3848_);
lean_dec(v_b_3840_);
v___x_3850_ = lean_box(0);
v_isShared_3851_ = v_isSharedCheck_3915_;
goto v_resetjp_3849_;
}
v_resetjp_3849_:
{
lean_object* v___x_3852_; lean_object* v_a_3854_; lean_object* v_a_3861_; 
v___x_3852_ = lean_box(0);
v_a_3861_ = lean_array_uget(v_as_3837_, v_i_3839_);
if (lean_obj_tag(v_a_3861_) == 0)
{
v_a_3854_ = v_snd_3848_;
goto v___jp_3853_;
}
else
{
lean_object* v_val_3862_; lean_object* v___x_3864_; uint8_t v_isShared_3865_; uint8_t v_isSharedCheck_3914_; 
v_val_3862_ = lean_ctor_get(v_a_3861_, 0);
v_isSharedCheck_3914_ = !lean_is_exclusive(v_a_3861_);
if (v_isSharedCheck_3914_ == 0)
{
v___x_3864_ = v_a_3861_;
v_isShared_3865_ = v_isSharedCheck_3914_;
goto v_resetjp_3863_;
}
else
{
lean_inc(v_val_3862_);
lean_dec(v_a_3861_);
v___x_3864_ = lean_box(0);
v_isShared_3865_ = v_isSharedCheck_3914_;
goto v_resetjp_3863_;
}
v_resetjp_3863_:
{
lean_object* v___x_3866_; 
lean_inc_ref(v_p_3835_);
lean_inc(v___y_3844_);
lean_inc_ref(v___y_3843_);
lean_inc(v___y_3842_);
lean_inc_ref(v___y_3841_);
lean_inc(v_val_3862_);
v___x_3866_ = lean_apply_6(v_p_3835_, v_val_3862_, v___y_3841_, v___y_3842_, v___y_3843_, v___y_3844_, lean_box(0));
if (lean_obj_tag(v___x_3866_) == 0)
{
lean_object* v_a_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; uint8_t v___x_3870_; 
v_a_3867_ = lean_ctor_get(v___x_3866_, 0);
lean_inc(v_a_3867_);
lean_dec_ref(v___x_3866_);
v___x_3868_ = lean_box(0);
v___x_3869_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3_spec__6___closed__0));
v___x_3870_ = lean_unbox(v_a_3867_);
lean_dec(v_a_3867_);
if (v___x_3870_ == 0)
{
lean_del_object(v___x_3864_);
lean_dec(v_val_3862_);
lean_dec(v_snd_3848_);
v_a_3854_ = v___x_3869_;
goto v___jp_3853_;
}
else
{
lean_object* v___x_3871_; lean_object* v___x_3872_; uint8_t v___x_3873_; lean_object* v___x_3874_; lean_object* v___f_3875_; lean_object* v___x_3876_; 
v___x_3871_ = l_Lean_LocalDecl_fvarId(v_val_3862_);
lean_dec(v_val_3862_);
v___x_3872_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5___closed__1));
v___x_3873_ = 0;
v___x_3874_ = lean_box(v___x_3873_);
lean_inc(v_mvarId_3836_);
v___f_3875_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3___lam__0___boxed), 10, 5);
lean_closure_set(v___f_3875_, 0, v_mvarId_3836_);
lean_closure_set(v___f_3875_, 1, v___x_3871_);
lean_closure_set(v___f_3875_, 2, v___x_3872_);
lean_closure_set(v___f_3875_, 3, v___x_3874_);
lean_closure_set(v___f_3875_, 4, v___x_3852_);
lean_inc(v___y_3844_);
lean_inc_ref(v___y_3843_);
lean_inc(v___y_3842_);
lean_inc_ref(v___y_3841_);
v___x_3876_ = l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1___redArg(v___f_3875_, v___y_3841_, v___y_3842_, v___y_3843_, v___y_3844_);
if (lean_obj_tag(v___x_3876_) == 0)
{
lean_object* v_a_3877_; lean_object* v___x_3879_; uint8_t v_isShared_3880_; uint8_t v_isSharedCheck_3897_; 
v_a_3877_ = lean_ctor_get(v___x_3876_, 0);
v_isSharedCheck_3897_ = !lean_is_exclusive(v___x_3876_);
if (v_isSharedCheck_3897_ == 0)
{
v___x_3879_ = v___x_3876_;
v_isShared_3880_ = v_isSharedCheck_3897_;
goto v_resetjp_3878_;
}
else
{
lean_inc(v_a_3877_);
lean_dec(v___x_3876_);
v___x_3879_ = lean_box(0);
v_isShared_3880_ = v_isSharedCheck_3897_;
goto v_resetjp_3878_;
}
v_resetjp_3878_:
{
if (lean_obj_tag(v_a_3877_) == 0)
{
lean_del_object(v___x_3879_);
lean_del_object(v___x_3864_);
lean_dec(v_snd_3848_);
v_a_3854_ = v___x_3869_;
goto v___jp_3853_;
}
else
{
lean_object* v___x_3882_; 
lean_del_object(v___x_3850_);
lean_dec(v___y_3844_);
lean_dec_ref(v___y_3843_);
lean_dec(v___y_3842_);
lean_dec_ref(v___y_3841_);
lean_dec(v_mvarId_3836_);
lean_dec_ref(v_p_3835_);
lean_inc_ref(v_a_3877_);
if (v_isShared_3865_ == 0)
{
lean_ctor_set(v___x_3864_, 0, v_a_3877_);
v___x_3882_ = v___x_3864_;
goto v_reusejp_3881_;
}
else
{
lean_object* v_reuseFailAlloc_3896_; 
v_reuseFailAlloc_3896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3896_, 0, v_a_3877_);
v___x_3882_ = v_reuseFailAlloc_3896_;
goto v_reusejp_3881_;
}
v_reusejp_3881_:
{
lean_object* v___x_3884_; uint8_t v_isShared_3885_; uint8_t v_isSharedCheck_3894_; 
v_isSharedCheck_3894_ = !lean_is_exclusive(v_a_3877_);
if (v_isSharedCheck_3894_ == 0)
{
lean_object* v_unused_3895_; 
v_unused_3895_ = lean_ctor_get(v_a_3877_, 0);
lean_dec(v_unused_3895_);
v___x_3884_ = v_a_3877_;
v_isShared_3885_ = v_isSharedCheck_3894_;
goto v_resetjp_3883_;
}
else
{
lean_dec(v_a_3877_);
v___x_3884_ = lean_box(0);
v_isShared_3885_ = v_isSharedCheck_3894_;
goto v_resetjp_3883_;
}
v_resetjp_3883_:
{
lean_object* v___x_3886_; lean_object* v___x_3888_; 
v___x_3886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3886_, 0, v___x_3882_);
lean_ctor_set(v___x_3886_, 1, v___x_3868_);
if (v_isShared_3885_ == 0)
{
lean_ctor_set(v___x_3884_, 0, v___x_3886_);
v___x_3888_ = v___x_3884_;
goto v_reusejp_3887_;
}
else
{
lean_object* v_reuseFailAlloc_3893_; 
v_reuseFailAlloc_3893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3893_, 0, v___x_3886_);
v___x_3888_ = v_reuseFailAlloc_3893_;
goto v_reusejp_3887_;
}
v_reusejp_3887_:
{
lean_object* v___x_3889_; lean_object* v___x_3891_; 
v___x_3889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3889_, 0, v___x_3888_);
lean_ctor_set(v___x_3889_, 1, v_snd_3848_);
if (v_isShared_3880_ == 0)
{
lean_ctor_set(v___x_3879_, 0, v___x_3889_);
v___x_3891_ = v___x_3879_;
goto v_reusejp_3890_;
}
else
{
lean_object* v_reuseFailAlloc_3892_; 
v_reuseFailAlloc_3892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3892_, 0, v___x_3889_);
v___x_3891_ = v_reuseFailAlloc_3892_;
goto v_reusejp_3890_;
}
v_reusejp_3890_:
{
return v___x_3891_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3898_; lean_object* v___x_3900_; uint8_t v_isShared_3901_; uint8_t v_isSharedCheck_3905_; 
lean_del_object(v___x_3864_);
lean_del_object(v___x_3850_);
lean_dec(v_snd_3848_);
lean_dec(v___y_3844_);
lean_dec_ref(v___y_3843_);
lean_dec(v___y_3842_);
lean_dec_ref(v___y_3841_);
lean_dec(v_mvarId_3836_);
lean_dec_ref(v_p_3835_);
v_a_3898_ = lean_ctor_get(v___x_3876_, 0);
v_isSharedCheck_3905_ = !lean_is_exclusive(v___x_3876_);
if (v_isSharedCheck_3905_ == 0)
{
v___x_3900_ = v___x_3876_;
v_isShared_3901_ = v_isSharedCheck_3905_;
goto v_resetjp_3899_;
}
else
{
lean_inc(v_a_3898_);
lean_dec(v___x_3876_);
v___x_3900_ = lean_box(0);
v_isShared_3901_ = v_isSharedCheck_3905_;
goto v_resetjp_3899_;
}
v_resetjp_3899_:
{
lean_object* v___x_3903_; 
if (v_isShared_3901_ == 0)
{
v___x_3903_ = v___x_3900_;
goto v_reusejp_3902_;
}
else
{
lean_object* v_reuseFailAlloc_3904_; 
v_reuseFailAlloc_3904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3904_, 0, v_a_3898_);
v___x_3903_ = v_reuseFailAlloc_3904_;
goto v_reusejp_3902_;
}
v_reusejp_3902_:
{
return v___x_3903_;
}
}
}
}
}
else
{
lean_object* v_a_3906_; lean_object* v___x_3908_; uint8_t v_isShared_3909_; uint8_t v_isSharedCheck_3913_; 
lean_del_object(v___x_3864_);
lean_dec(v_val_3862_);
lean_del_object(v___x_3850_);
lean_dec(v_snd_3848_);
lean_dec(v___y_3844_);
lean_dec_ref(v___y_3843_);
lean_dec(v___y_3842_);
lean_dec_ref(v___y_3841_);
lean_dec(v_mvarId_3836_);
lean_dec_ref(v_p_3835_);
v_a_3906_ = lean_ctor_get(v___x_3866_, 0);
v_isSharedCheck_3913_ = !lean_is_exclusive(v___x_3866_);
if (v_isSharedCheck_3913_ == 0)
{
v___x_3908_ = v___x_3866_;
v_isShared_3909_ = v_isSharedCheck_3913_;
goto v_resetjp_3907_;
}
else
{
lean_inc(v_a_3906_);
lean_dec(v___x_3866_);
v___x_3908_ = lean_box(0);
v_isShared_3909_ = v_isSharedCheck_3913_;
goto v_resetjp_3907_;
}
v_resetjp_3907_:
{
lean_object* v___x_3911_; 
if (v_isShared_3909_ == 0)
{
v___x_3911_ = v___x_3908_;
goto v_reusejp_3910_;
}
else
{
lean_object* v_reuseFailAlloc_3912_; 
v_reuseFailAlloc_3912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3912_, 0, v_a_3906_);
v___x_3911_ = v_reuseFailAlloc_3912_;
goto v_reusejp_3910_;
}
v_reusejp_3910_:
{
return v___x_3911_;
}
}
}
}
}
v___jp_3853_:
{
lean_object* v___x_3856_; 
if (v_isShared_3851_ == 0)
{
lean_ctor_set(v___x_3850_, 1, v_a_3854_);
lean_ctor_set(v___x_3850_, 0, v___x_3852_);
v___x_3856_ = v___x_3850_;
goto v_reusejp_3855_;
}
else
{
lean_object* v_reuseFailAlloc_3860_; 
v_reuseFailAlloc_3860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3860_, 0, v___x_3852_);
lean_ctor_set(v_reuseFailAlloc_3860_, 1, v_a_3854_);
v___x_3856_ = v_reuseFailAlloc_3860_;
goto v_reusejp_3855_;
}
v_reusejp_3855_:
{
size_t v___x_3857_; size_t v___x_3858_; 
v___x_3857_ = ((size_t)1ULL);
v___x_3858_ = lean_usize_add(v_i_3839_, v___x_3857_);
v_i_3839_ = v___x_3858_;
v_b_3840_ = v___x_3856_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3_spec__6___boxed(lean_object* v_p_3917_, lean_object* v_mvarId_3918_, lean_object* v_as_3919_, lean_object* v_sz_3920_, lean_object* v_i_3921_, lean_object* v_b_3922_, lean_object* v___y_3923_, lean_object* v___y_3924_, lean_object* v___y_3925_, lean_object* v___y_3926_, lean_object* v___y_3927_){
_start:
{
size_t v_sz_boxed_3928_; size_t v_i_boxed_3929_; lean_object* v_res_3930_; 
v_sz_boxed_3928_ = lean_unbox_usize(v_sz_3920_);
lean_dec(v_sz_3920_);
v_i_boxed_3929_ = lean_unbox_usize(v_i_3921_);
lean_dec(v_i_3921_);
v_res_3930_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3_spec__6(v_p_3917_, v_mvarId_3918_, v_as_3919_, v_sz_boxed_3928_, v_i_boxed_3929_, v_b_3922_, v___y_3923_, v___y_3924_, v___y_3925_, v___y_3926_);
lean_dec_ref(v_as_3919_);
return v_res_3930_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3(lean_object* v_p_3931_, lean_object* v_mvarId_3932_, lean_object* v_as_3933_, size_t v_sz_3934_, size_t v_i_3935_, lean_object* v_b_3936_, lean_object* v___y_3937_, lean_object* v___y_3938_, lean_object* v___y_3939_, lean_object* v___y_3940_){
_start:
{
uint8_t v___x_3942_; 
v___x_3942_ = lean_usize_dec_lt(v_i_3935_, v_sz_3934_);
if (v___x_3942_ == 0)
{
lean_object* v___x_3943_; 
lean_dec(v___y_3940_);
lean_dec_ref(v___y_3939_);
lean_dec(v___y_3938_);
lean_dec_ref(v___y_3937_);
lean_dec(v_mvarId_3932_);
lean_dec_ref(v_p_3931_);
v___x_3943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3943_, 0, v_b_3936_);
return v___x_3943_;
}
else
{
lean_object* v_snd_3944_; lean_object* v___x_3946_; uint8_t v_isShared_3947_; uint8_t v_isSharedCheck_4011_; 
v_snd_3944_ = lean_ctor_get(v_b_3936_, 1);
v_isSharedCheck_4011_ = !lean_is_exclusive(v_b_3936_);
if (v_isSharedCheck_4011_ == 0)
{
lean_object* v_unused_4012_; 
v_unused_4012_ = lean_ctor_get(v_b_3936_, 0);
lean_dec(v_unused_4012_);
v___x_3946_ = v_b_3936_;
v_isShared_3947_ = v_isSharedCheck_4011_;
goto v_resetjp_3945_;
}
else
{
lean_inc(v_snd_3944_);
lean_dec(v_b_3936_);
v___x_3946_ = lean_box(0);
v_isShared_3947_ = v_isSharedCheck_4011_;
goto v_resetjp_3945_;
}
v_resetjp_3945_:
{
lean_object* v___x_3948_; lean_object* v_a_3950_; lean_object* v_a_3957_; 
v___x_3948_ = lean_box(0);
v_a_3957_ = lean_array_uget(v_as_3933_, v_i_3935_);
if (lean_obj_tag(v_a_3957_) == 0)
{
v_a_3950_ = v_snd_3944_;
goto v___jp_3949_;
}
else
{
lean_object* v_val_3958_; lean_object* v___x_3960_; uint8_t v_isShared_3961_; uint8_t v_isSharedCheck_4010_; 
v_val_3958_ = lean_ctor_get(v_a_3957_, 0);
v_isSharedCheck_4010_ = !lean_is_exclusive(v_a_3957_);
if (v_isSharedCheck_4010_ == 0)
{
v___x_3960_ = v_a_3957_;
v_isShared_3961_ = v_isSharedCheck_4010_;
goto v_resetjp_3959_;
}
else
{
lean_inc(v_val_3958_);
lean_dec(v_a_3957_);
v___x_3960_ = lean_box(0);
v_isShared_3961_ = v_isSharedCheck_4010_;
goto v_resetjp_3959_;
}
v_resetjp_3959_:
{
lean_object* v___x_3962_; 
lean_inc_ref(v_p_3931_);
lean_inc(v___y_3940_);
lean_inc_ref(v___y_3939_);
lean_inc(v___y_3938_);
lean_inc_ref(v___y_3937_);
lean_inc(v_val_3958_);
v___x_3962_ = lean_apply_6(v_p_3931_, v_val_3958_, v___y_3937_, v___y_3938_, v___y_3939_, v___y_3940_, lean_box(0));
if (lean_obj_tag(v___x_3962_) == 0)
{
lean_object* v_a_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; uint8_t v___x_3966_; 
v_a_3963_ = lean_ctor_get(v___x_3962_, 0);
lean_inc(v_a_3963_);
lean_dec_ref(v___x_3962_);
v___x_3964_ = lean_box(0);
v___x_3965_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3_spec__6___closed__0));
v___x_3966_ = lean_unbox(v_a_3963_);
lean_dec(v_a_3963_);
if (v___x_3966_ == 0)
{
lean_del_object(v___x_3960_);
lean_dec(v_val_3958_);
lean_dec(v_snd_3944_);
v_a_3950_ = v___x_3965_;
goto v___jp_3949_;
}
else
{
lean_object* v___x_3967_; lean_object* v___x_3968_; uint8_t v___x_3969_; lean_object* v___x_3970_; lean_object* v___f_3971_; lean_object* v___x_3972_; 
v___x_3967_ = l_Lean_LocalDecl_fvarId(v_val_3958_);
lean_dec(v_val_3958_);
v___x_3968_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5___closed__1));
v___x_3969_ = 0;
v___x_3970_ = lean_box(v___x_3969_);
lean_inc(v_mvarId_3932_);
v___f_3971_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3___lam__0___boxed), 10, 5);
lean_closure_set(v___f_3971_, 0, v_mvarId_3932_);
lean_closure_set(v___f_3971_, 1, v___x_3967_);
lean_closure_set(v___f_3971_, 2, v___x_3968_);
lean_closure_set(v___f_3971_, 3, v___x_3970_);
lean_closure_set(v___f_3971_, 4, v___x_3948_);
lean_inc(v___y_3940_);
lean_inc_ref(v___y_3939_);
lean_inc(v___y_3938_);
lean_inc_ref(v___y_3937_);
v___x_3972_ = l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1___redArg(v___f_3971_, v___y_3937_, v___y_3938_, v___y_3939_, v___y_3940_);
if (lean_obj_tag(v___x_3972_) == 0)
{
lean_object* v_a_3973_; lean_object* v___x_3975_; uint8_t v_isShared_3976_; uint8_t v_isSharedCheck_3993_; 
v_a_3973_ = lean_ctor_get(v___x_3972_, 0);
v_isSharedCheck_3993_ = !lean_is_exclusive(v___x_3972_);
if (v_isSharedCheck_3993_ == 0)
{
v___x_3975_ = v___x_3972_;
v_isShared_3976_ = v_isSharedCheck_3993_;
goto v_resetjp_3974_;
}
else
{
lean_inc(v_a_3973_);
lean_dec(v___x_3972_);
v___x_3975_ = lean_box(0);
v_isShared_3976_ = v_isSharedCheck_3993_;
goto v_resetjp_3974_;
}
v_resetjp_3974_:
{
if (lean_obj_tag(v_a_3973_) == 0)
{
lean_del_object(v___x_3975_);
lean_del_object(v___x_3960_);
lean_dec(v_snd_3944_);
v_a_3950_ = v___x_3965_;
goto v___jp_3949_;
}
else
{
lean_object* v___x_3978_; 
lean_del_object(v___x_3946_);
lean_dec(v___y_3940_);
lean_dec_ref(v___y_3939_);
lean_dec(v___y_3938_);
lean_dec_ref(v___y_3937_);
lean_dec(v_mvarId_3932_);
lean_dec_ref(v_p_3931_);
lean_inc_ref(v_a_3973_);
if (v_isShared_3961_ == 0)
{
lean_ctor_set(v___x_3960_, 0, v_a_3973_);
v___x_3978_ = v___x_3960_;
goto v_reusejp_3977_;
}
else
{
lean_object* v_reuseFailAlloc_3992_; 
v_reuseFailAlloc_3992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3992_, 0, v_a_3973_);
v___x_3978_ = v_reuseFailAlloc_3992_;
goto v_reusejp_3977_;
}
v_reusejp_3977_:
{
lean_object* v___x_3980_; uint8_t v_isShared_3981_; uint8_t v_isSharedCheck_3990_; 
v_isSharedCheck_3990_ = !lean_is_exclusive(v_a_3973_);
if (v_isSharedCheck_3990_ == 0)
{
lean_object* v_unused_3991_; 
v_unused_3991_ = lean_ctor_get(v_a_3973_, 0);
lean_dec(v_unused_3991_);
v___x_3980_ = v_a_3973_;
v_isShared_3981_ = v_isSharedCheck_3990_;
goto v_resetjp_3979_;
}
else
{
lean_dec(v_a_3973_);
v___x_3980_ = lean_box(0);
v_isShared_3981_ = v_isSharedCheck_3990_;
goto v_resetjp_3979_;
}
v_resetjp_3979_:
{
lean_object* v___x_3982_; lean_object* v___x_3984_; 
v___x_3982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3982_, 0, v___x_3978_);
lean_ctor_set(v___x_3982_, 1, v___x_3964_);
if (v_isShared_3981_ == 0)
{
lean_ctor_set(v___x_3980_, 0, v___x_3982_);
v___x_3984_ = v___x_3980_;
goto v_reusejp_3983_;
}
else
{
lean_object* v_reuseFailAlloc_3989_; 
v_reuseFailAlloc_3989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3989_, 0, v___x_3982_);
v___x_3984_ = v_reuseFailAlloc_3989_;
goto v_reusejp_3983_;
}
v_reusejp_3983_:
{
lean_object* v___x_3985_; lean_object* v___x_3987_; 
v___x_3985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3985_, 0, v___x_3984_);
lean_ctor_set(v___x_3985_, 1, v_snd_3944_);
if (v_isShared_3976_ == 0)
{
lean_ctor_set(v___x_3975_, 0, v___x_3985_);
v___x_3987_ = v___x_3975_;
goto v_reusejp_3986_;
}
else
{
lean_object* v_reuseFailAlloc_3988_; 
v_reuseFailAlloc_3988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3988_, 0, v___x_3985_);
v___x_3987_ = v_reuseFailAlloc_3988_;
goto v_reusejp_3986_;
}
v_reusejp_3986_:
{
return v___x_3987_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3994_; lean_object* v___x_3996_; uint8_t v_isShared_3997_; uint8_t v_isSharedCheck_4001_; 
lean_del_object(v___x_3960_);
lean_del_object(v___x_3946_);
lean_dec(v_snd_3944_);
lean_dec(v___y_3940_);
lean_dec_ref(v___y_3939_);
lean_dec(v___y_3938_);
lean_dec_ref(v___y_3937_);
lean_dec(v_mvarId_3932_);
lean_dec_ref(v_p_3931_);
v_a_3994_ = lean_ctor_get(v___x_3972_, 0);
v_isSharedCheck_4001_ = !lean_is_exclusive(v___x_3972_);
if (v_isSharedCheck_4001_ == 0)
{
v___x_3996_ = v___x_3972_;
v_isShared_3997_ = v_isSharedCheck_4001_;
goto v_resetjp_3995_;
}
else
{
lean_inc(v_a_3994_);
lean_dec(v___x_3972_);
v___x_3996_ = lean_box(0);
v_isShared_3997_ = v_isSharedCheck_4001_;
goto v_resetjp_3995_;
}
v_resetjp_3995_:
{
lean_object* v___x_3999_; 
if (v_isShared_3997_ == 0)
{
v___x_3999_ = v___x_3996_;
goto v_reusejp_3998_;
}
else
{
lean_object* v_reuseFailAlloc_4000_; 
v_reuseFailAlloc_4000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4000_, 0, v_a_3994_);
v___x_3999_ = v_reuseFailAlloc_4000_;
goto v_reusejp_3998_;
}
v_reusejp_3998_:
{
return v___x_3999_;
}
}
}
}
}
else
{
lean_object* v_a_4002_; lean_object* v___x_4004_; uint8_t v_isShared_4005_; uint8_t v_isSharedCheck_4009_; 
lean_del_object(v___x_3960_);
lean_dec(v_val_3958_);
lean_del_object(v___x_3946_);
lean_dec(v_snd_3944_);
lean_dec(v___y_3940_);
lean_dec_ref(v___y_3939_);
lean_dec(v___y_3938_);
lean_dec_ref(v___y_3937_);
lean_dec(v_mvarId_3932_);
lean_dec_ref(v_p_3931_);
v_a_4002_ = lean_ctor_get(v___x_3962_, 0);
v_isSharedCheck_4009_ = !lean_is_exclusive(v___x_3962_);
if (v_isSharedCheck_4009_ == 0)
{
v___x_4004_ = v___x_3962_;
v_isShared_4005_ = v_isSharedCheck_4009_;
goto v_resetjp_4003_;
}
else
{
lean_inc(v_a_4002_);
lean_dec(v___x_3962_);
v___x_4004_ = lean_box(0);
v_isShared_4005_ = v_isSharedCheck_4009_;
goto v_resetjp_4003_;
}
v_resetjp_4003_:
{
lean_object* v___x_4007_; 
if (v_isShared_4005_ == 0)
{
v___x_4007_ = v___x_4004_;
goto v_reusejp_4006_;
}
else
{
lean_object* v_reuseFailAlloc_4008_; 
v_reuseFailAlloc_4008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4008_, 0, v_a_4002_);
v___x_4007_ = v_reuseFailAlloc_4008_;
goto v_reusejp_4006_;
}
v_reusejp_4006_:
{
return v___x_4007_;
}
}
}
}
}
v___jp_3949_:
{
lean_object* v___x_3952_; 
if (v_isShared_3947_ == 0)
{
lean_ctor_set(v___x_3946_, 1, v_a_3950_);
lean_ctor_set(v___x_3946_, 0, v___x_3948_);
v___x_3952_ = v___x_3946_;
goto v_reusejp_3951_;
}
else
{
lean_object* v_reuseFailAlloc_3956_; 
v_reuseFailAlloc_3956_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3956_, 0, v___x_3948_);
lean_ctor_set(v_reuseFailAlloc_3956_, 1, v_a_3950_);
v___x_3952_ = v_reuseFailAlloc_3956_;
goto v_reusejp_3951_;
}
v_reusejp_3951_:
{
size_t v___x_3953_; size_t v___x_3954_; lean_object* v___x_3955_; 
v___x_3953_ = ((size_t)1ULL);
v___x_3954_ = lean_usize_add(v_i_3935_, v___x_3953_);
v___x_3955_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3_spec__6(v_p_3931_, v_mvarId_3932_, v_as_3933_, v_sz_3934_, v___x_3954_, v___x_3952_, v___y_3937_, v___y_3938_, v___y_3939_, v___y_3940_);
return v___x_3955_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3___boxed(lean_object* v_p_4013_, lean_object* v_mvarId_4014_, lean_object* v_as_4015_, lean_object* v_sz_4016_, lean_object* v_i_4017_, lean_object* v_b_4018_, lean_object* v___y_4019_, lean_object* v___y_4020_, lean_object* v___y_4021_, lean_object* v___y_4022_, lean_object* v___y_4023_){
_start:
{
size_t v_sz_boxed_4024_; size_t v_i_boxed_4025_; lean_object* v_res_4026_; 
v_sz_boxed_4024_ = lean_unbox_usize(v_sz_4016_);
lean_dec(v_sz_4016_);
v_i_boxed_4025_ = lean_unbox_usize(v_i_4017_);
lean_dec(v_i_4017_);
v_res_4026_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3(v_p_4013_, v_mvarId_4014_, v_as_4015_, v_sz_boxed_4024_, v_i_boxed_4025_, v_b_4018_, v___y_4019_, v___y_4020_, v___y_4021_, v___y_4022_);
lean_dec_ref(v_as_4015_);
return v_res_4026_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2(lean_object* v_p_4027_, lean_object* v_mvarId_4028_, lean_object* v_t_4029_, lean_object* v_init_4030_, lean_object* v___y_4031_, lean_object* v___y_4032_, lean_object* v___y_4033_, lean_object* v___y_4034_){
_start:
{
lean_object* v_root_4036_; lean_object* v_tail_4037_; lean_object* v___x_4038_; 
v_root_4036_ = lean_ctor_get(v_t_4029_, 0);
lean_inc_ref(v_root_4036_);
v_tail_4037_ = lean_ctor_get(v_t_4029_, 1);
lean_inc_ref(v_tail_4037_);
lean_dec_ref(v_t_4029_);
lean_inc(v___y_4034_);
lean_inc_ref(v___y_4033_);
lean_inc(v___y_4032_);
lean_inc_ref(v___y_4031_);
lean_inc_ref(v_init_4030_);
lean_inc(v_mvarId_4028_);
lean_inc_ref(v_p_4027_);
v___x_4038_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2(v_p_4027_, v_mvarId_4028_, v_init_4030_, v_root_4036_, v_init_4030_, v___y_4031_, v___y_4032_, v___y_4033_, v___y_4034_);
lean_dec_ref(v_init_4030_);
if (lean_obj_tag(v___x_4038_) == 0)
{
lean_object* v_a_4039_; lean_object* v___x_4041_; uint8_t v_isShared_4042_; uint8_t v_isSharedCheck_4075_; 
v_a_4039_ = lean_ctor_get(v___x_4038_, 0);
v_isSharedCheck_4075_ = !lean_is_exclusive(v___x_4038_);
if (v_isSharedCheck_4075_ == 0)
{
v___x_4041_ = v___x_4038_;
v_isShared_4042_ = v_isSharedCheck_4075_;
goto v_resetjp_4040_;
}
else
{
lean_inc(v_a_4039_);
lean_dec(v___x_4038_);
v___x_4041_ = lean_box(0);
v_isShared_4042_ = v_isSharedCheck_4075_;
goto v_resetjp_4040_;
}
v_resetjp_4040_:
{
if (lean_obj_tag(v_a_4039_) == 0)
{
lean_object* v_a_4043_; lean_object* v___x_4045_; 
lean_dec_ref(v_tail_4037_);
lean_dec(v___y_4034_);
lean_dec_ref(v___y_4033_);
lean_dec(v___y_4032_);
lean_dec_ref(v___y_4031_);
lean_dec(v_mvarId_4028_);
lean_dec_ref(v_p_4027_);
v_a_4043_ = lean_ctor_get(v_a_4039_, 0);
lean_inc(v_a_4043_);
lean_dec_ref(v_a_4039_);
if (v_isShared_4042_ == 0)
{
lean_ctor_set(v___x_4041_, 0, v_a_4043_);
v___x_4045_ = v___x_4041_;
goto v_reusejp_4044_;
}
else
{
lean_object* v_reuseFailAlloc_4046_; 
v_reuseFailAlloc_4046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4046_, 0, v_a_4043_);
v___x_4045_ = v_reuseFailAlloc_4046_;
goto v_reusejp_4044_;
}
v_reusejp_4044_:
{
return v___x_4045_;
}
}
else
{
lean_object* v_a_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; size_t v_sz_4050_; size_t v___x_4051_; lean_object* v___x_4052_; 
lean_del_object(v___x_4041_);
v_a_4047_ = lean_ctor_get(v_a_4039_, 0);
lean_inc(v_a_4047_);
lean_dec_ref(v_a_4039_);
v___x_4048_ = lean_box(0);
v___x_4049_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4049_, 0, v___x_4048_);
lean_ctor_set(v___x_4049_, 1, v_a_4047_);
v_sz_4050_ = lean_array_size(v_tail_4037_);
v___x_4051_ = ((size_t)0ULL);
v___x_4052_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3(v_p_4027_, v_mvarId_4028_, v_tail_4037_, v_sz_4050_, v___x_4051_, v___x_4049_, v___y_4031_, v___y_4032_, v___y_4033_, v___y_4034_);
lean_dec_ref(v_tail_4037_);
if (lean_obj_tag(v___x_4052_) == 0)
{
lean_object* v_a_4053_; lean_object* v___x_4055_; uint8_t v_isShared_4056_; uint8_t v_isSharedCheck_4066_; 
v_a_4053_ = lean_ctor_get(v___x_4052_, 0);
v_isSharedCheck_4066_ = !lean_is_exclusive(v___x_4052_);
if (v_isSharedCheck_4066_ == 0)
{
v___x_4055_ = v___x_4052_;
v_isShared_4056_ = v_isSharedCheck_4066_;
goto v_resetjp_4054_;
}
else
{
lean_inc(v_a_4053_);
lean_dec(v___x_4052_);
v___x_4055_ = lean_box(0);
v_isShared_4056_ = v_isSharedCheck_4066_;
goto v_resetjp_4054_;
}
v_resetjp_4054_:
{
lean_object* v_fst_4057_; 
v_fst_4057_ = lean_ctor_get(v_a_4053_, 0);
if (lean_obj_tag(v_fst_4057_) == 0)
{
lean_object* v_snd_4058_; lean_object* v___x_4060_; 
v_snd_4058_ = lean_ctor_get(v_a_4053_, 1);
lean_inc(v_snd_4058_);
lean_dec(v_a_4053_);
if (v_isShared_4056_ == 0)
{
lean_ctor_set(v___x_4055_, 0, v_snd_4058_);
v___x_4060_ = v___x_4055_;
goto v_reusejp_4059_;
}
else
{
lean_object* v_reuseFailAlloc_4061_; 
v_reuseFailAlloc_4061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4061_, 0, v_snd_4058_);
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
lean_inc_ref(v_fst_4057_);
lean_dec(v_a_4053_);
v_val_4062_ = lean_ctor_get(v_fst_4057_, 0);
lean_inc(v_val_4062_);
lean_dec_ref(v_fst_4057_);
if (v_isShared_4056_ == 0)
{
lean_ctor_set(v___x_4055_, 0, v_val_4062_);
v___x_4064_ = v___x_4055_;
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
v_a_4067_ = lean_ctor_get(v___x_4052_, 0);
v_isSharedCheck_4074_ = !lean_is_exclusive(v___x_4052_);
if (v_isSharedCheck_4074_ == 0)
{
v___x_4069_ = v___x_4052_;
v_isShared_4070_ = v_isSharedCheck_4074_;
goto v_resetjp_4068_;
}
else
{
lean_inc(v_a_4067_);
lean_dec(v___x_4052_);
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
}
else
{
lean_object* v_a_4076_; lean_object* v___x_4078_; uint8_t v_isShared_4079_; uint8_t v_isSharedCheck_4083_; 
lean_dec_ref(v_tail_4037_);
lean_dec(v___y_4034_);
lean_dec_ref(v___y_4033_);
lean_dec(v___y_4032_);
lean_dec_ref(v___y_4031_);
lean_dec(v_mvarId_4028_);
lean_dec_ref(v_p_4027_);
v_a_4076_ = lean_ctor_get(v___x_4038_, 0);
v_isSharedCheck_4083_ = !lean_is_exclusive(v___x_4038_);
if (v_isSharedCheck_4083_ == 0)
{
v___x_4078_ = v___x_4038_;
v_isShared_4079_ = v_isSharedCheck_4083_;
goto v_resetjp_4077_;
}
else
{
lean_inc(v_a_4076_);
lean_dec(v___x_4038_);
v___x_4078_ = lean_box(0);
v_isShared_4079_ = v_isSharedCheck_4083_;
goto v_resetjp_4077_;
}
v_resetjp_4077_:
{
lean_object* v___x_4081_; 
if (v_isShared_4079_ == 0)
{
v___x_4081_ = v___x_4078_;
goto v_reusejp_4080_;
}
else
{
lean_object* v_reuseFailAlloc_4082_; 
v_reuseFailAlloc_4082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4082_, 0, v_a_4076_);
v___x_4081_ = v_reuseFailAlloc_4082_;
goto v_reusejp_4080_;
}
v_reusejp_4080_:
{
return v___x_4081_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2___boxed(lean_object* v_p_4084_, lean_object* v_mvarId_4085_, lean_object* v_t_4086_, lean_object* v_init_4087_, lean_object* v___y_4088_, lean_object* v___y_4089_, lean_object* v___y_4090_, lean_object* v___y_4091_, lean_object* v___y_4092_){
_start:
{
lean_object* v_res_4093_; 
v_res_4093_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2(v_p_4084_, v_mvarId_4085_, v_t_4086_, v_init_4087_, v___y_4088_, v___y_4089_, v___y_4090_, v___y_4091_);
return v_res_4093_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesRec___lam__0(lean_object* v_p_4097_, lean_object* v_mvarId_4098_, lean_object* v___y_4099_, lean_object* v___y_4100_, lean_object* v___y_4101_, lean_object* v___y_4102_){
_start:
{
lean_object* v_lctx_4104_; lean_object* v_decls_4105_; lean_object* v___x_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; 
v_lctx_4104_ = lean_ctor_get(v___y_4099_, 2);
v_decls_4105_ = lean_ctor_get(v_lctx_4104_, 1);
lean_inc_ref(v_decls_4105_);
v___x_4106_ = lean_box(0);
v___x_4107_ = ((lean_object*)(l_Lean_MVarId_casesRec___lam__0___closed__0));
v___x_4108_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2(v_p_4097_, v_mvarId_4098_, v_decls_4105_, v___x_4107_, v___y_4099_, v___y_4100_, v___y_4101_, v___y_4102_);
if (lean_obj_tag(v___x_4108_) == 0)
{
lean_object* v_a_4109_; lean_object* v___x_4111_; uint8_t v_isShared_4112_; uint8_t v_isSharedCheck_4121_; 
v_a_4109_ = lean_ctor_get(v___x_4108_, 0);
v_isSharedCheck_4121_ = !lean_is_exclusive(v___x_4108_);
if (v_isSharedCheck_4121_ == 0)
{
v___x_4111_ = v___x_4108_;
v_isShared_4112_ = v_isSharedCheck_4121_;
goto v_resetjp_4110_;
}
else
{
lean_inc(v_a_4109_);
lean_dec(v___x_4108_);
v___x_4111_ = lean_box(0);
v_isShared_4112_ = v_isSharedCheck_4121_;
goto v_resetjp_4110_;
}
v_resetjp_4110_:
{
lean_object* v_fst_4113_; 
v_fst_4113_ = lean_ctor_get(v_a_4109_, 0);
lean_inc(v_fst_4113_);
lean_dec(v_a_4109_);
if (lean_obj_tag(v_fst_4113_) == 0)
{
lean_object* v___x_4115_; 
if (v_isShared_4112_ == 0)
{
lean_ctor_set(v___x_4111_, 0, v___x_4106_);
v___x_4115_ = v___x_4111_;
goto v_reusejp_4114_;
}
else
{
lean_object* v_reuseFailAlloc_4116_; 
v_reuseFailAlloc_4116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4116_, 0, v___x_4106_);
v___x_4115_ = v_reuseFailAlloc_4116_;
goto v_reusejp_4114_;
}
v_reusejp_4114_:
{
return v___x_4115_;
}
}
else
{
lean_object* v_val_4117_; lean_object* v___x_4119_; 
v_val_4117_ = lean_ctor_get(v_fst_4113_, 0);
lean_inc(v_val_4117_);
lean_dec_ref(v_fst_4113_);
if (v_isShared_4112_ == 0)
{
lean_ctor_set(v___x_4111_, 0, v_val_4117_);
v___x_4119_ = v___x_4111_;
goto v_reusejp_4118_;
}
else
{
lean_object* v_reuseFailAlloc_4120_; 
v_reuseFailAlloc_4120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4120_, 0, v_val_4117_);
v___x_4119_ = v_reuseFailAlloc_4120_;
goto v_reusejp_4118_;
}
v_reusejp_4118_:
{
return v___x_4119_;
}
}
}
}
else
{
lean_object* v_a_4122_; lean_object* v___x_4124_; uint8_t v_isShared_4125_; uint8_t v_isSharedCheck_4129_; 
v_a_4122_ = lean_ctor_get(v___x_4108_, 0);
v_isSharedCheck_4129_ = !lean_is_exclusive(v___x_4108_);
if (v_isSharedCheck_4129_ == 0)
{
v___x_4124_ = v___x_4108_;
v_isShared_4125_ = v_isSharedCheck_4129_;
goto v_resetjp_4123_;
}
else
{
lean_inc(v_a_4122_);
lean_dec(v___x_4108_);
v___x_4124_ = lean_box(0);
v_isShared_4125_ = v_isSharedCheck_4129_;
goto v_resetjp_4123_;
}
v_resetjp_4123_:
{
lean_object* v___x_4127_; 
if (v_isShared_4125_ == 0)
{
v___x_4127_ = v___x_4124_;
goto v_reusejp_4126_;
}
else
{
lean_object* v_reuseFailAlloc_4128_; 
v_reuseFailAlloc_4128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4128_, 0, v_a_4122_);
v___x_4127_ = v_reuseFailAlloc_4128_;
goto v_reusejp_4126_;
}
v_reusejp_4126_:
{
return v___x_4127_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesRec___lam__0___boxed(lean_object* v_p_4130_, lean_object* v_mvarId_4131_, lean_object* v___y_4132_, lean_object* v___y_4133_, lean_object* v___y_4134_, lean_object* v___y_4135_, lean_object* v___y_4136_){
_start:
{
lean_object* v_res_4137_; 
v_res_4137_ = l_Lean_MVarId_casesRec___lam__0(v_p_4130_, v_mvarId_4131_, v___y_4132_, v___y_4133_, v___y_4134_, v___y_4135_);
return v_res_4137_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesRec___lam__1(lean_object* v_p_4138_, lean_object* v_mvarId_4139_, lean_object* v___y_4140_, lean_object* v___y_4141_, lean_object* v___y_4142_, lean_object* v___y_4143_){
_start:
{
lean_object* v___f_4145_; lean_object* v___x_4146_; 
lean_inc(v_mvarId_4139_);
v___f_4145_ = lean_alloc_closure((void*)(l_Lean_MVarId_casesRec___lam__0___boxed), 7, 2);
lean_closure_set(v___f_4145_, 0, v_p_4138_);
lean_closure_set(v___f_4145_, 1, v_mvarId_4139_);
v___x_4146_ = l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2___redArg(v_mvarId_4139_, v___f_4145_, v___y_4140_, v___y_4141_, v___y_4142_, v___y_4143_);
return v___x_4146_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesRec___lam__1___boxed(lean_object* v_p_4147_, lean_object* v_mvarId_4148_, lean_object* v___y_4149_, lean_object* v___y_4150_, lean_object* v___y_4151_, lean_object* v___y_4152_, lean_object* v___y_4153_){
_start:
{
lean_object* v_res_4154_; 
v_res_4154_ = l_Lean_MVarId_casesRec___lam__1(v_p_4147_, v_mvarId_4148_, v___y_4149_, v___y_4150_, v___y_4151_, v___y_4152_);
return v_res_4154_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesRec(lean_object* v_mvarId_4155_, lean_object* v_p_4156_, lean_object* v_a_4157_, lean_object* v_a_4158_, lean_object* v_a_4159_, lean_object* v_a_4160_){
_start:
{
lean_object* v___f_4162_; lean_object* v___x_4163_; 
v___f_4162_ = lean_alloc_closure((void*)(l_Lean_MVarId_casesRec___lam__1___boxed), 7, 1);
lean_closure_set(v___f_4162_, 0, v_p_4156_);
v___x_4163_ = l_Lean_Meta_saturate(v_mvarId_4155_, v___f_4162_, v_a_4157_, v_a_4158_, v_a_4159_, v_a_4160_);
return v___x_4163_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesRec___boxed(lean_object* v_mvarId_4164_, lean_object* v_p_4165_, lean_object* v_a_4166_, lean_object* v_a_4167_, lean_object* v_a_4168_, lean_object* v_a_4169_, lean_object* v_a_4170_){
_start:
{
lean_object* v_res_4171_; 
v_res_4171_ = l_Lean_MVarId_casesRec(v_mvarId_4164_, v_p_4165_, v_a_4166_, v_a_4167_, v_a_4168_, v_a_4169_);
return v_res_4171_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0___redArg(lean_object* v_e_4172_, lean_object* v___y_4173_){
_start:
{
uint8_t v___x_4175_; 
v___x_4175_ = l_Lean_Expr_hasMVar(v_e_4172_);
if (v___x_4175_ == 0)
{
lean_object* v___x_4176_; 
v___x_4176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4176_, 0, v_e_4172_);
return v___x_4176_;
}
else
{
lean_object* v___x_4177_; lean_object* v_mctx_4178_; lean_object* v___x_4179_; lean_object* v_fst_4180_; lean_object* v_snd_4181_; lean_object* v___x_4182_; lean_object* v_cache_4183_; lean_object* v_zetaDeltaFVarIds_4184_; lean_object* v_postponed_4185_; lean_object* v_diag_4186_; lean_object* v___x_4188_; uint8_t v_isShared_4189_; uint8_t v_isSharedCheck_4195_; 
v___x_4177_ = lean_st_ref_get(v___y_4173_);
v_mctx_4178_ = lean_ctor_get(v___x_4177_, 0);
lean_inc_ref(v_mctx_4178_);
lean_dec(v___x_4177_);
v___x_4179_ = l_Lean_instantiateMVarsCore(v_mctx_4178_, v_e_4172_);
v_fst_4180_ = lean_ctor_get(v___x_4179_, 0);
lean_inc(v_fst_4180_);
v_snd_4181_ = lean_ctor_get(v___x_4179_, 1);
lean_inc(v_snd_4181_);
lean_dec_ref(v___x_4179_);
v___x_4182_ = lean_st_ref_take(v___y_4173_);
v_cache_4183_ = lean_ctor_get(v___x_4182_, 1);
v_zetaDeltaFVarIds_4184_ = lean_ctor_get(v___x_4182_, 2);
v_postponed_4185_ = lean_ctor_get(v___x_4182_, 3);
v_diag_4186_ = lean_ctor_get(v___x_4182_, 4);
v_isSharedCheck_4195_ = !lean_is_exclusive(v___x_4182_);
if (v_isSharedCheck_4195_ == 0)
{
lean_object* v_unused_4196_; 
v_unused_4196_ = lean_ctor_get(v___x_4182_, 0);
lean_dec(v_unused_4196_);
v___x_4188_ = v___x_4182_;
v_isShared_4189_ = v_isSharedCheck_4195_;
goto v_resetjp_4187_;
}
else
{
lean_inc(v_diag_4186_);
lean_inc(v_postponed_4185_);
lean_inc(v_zetaDeltaFVarIds_4184_);
lean_inc(v_cache_4183_);
lean_dec(v___x_4182_);
v___x_4188_ = lean_box(0);
v_isShared_4189_ = v_isSharedCheck_4195_;
goto v_resetjp_4187_;
}
v_resetjp_4187_:
{
lean_object* v___x_4191_; 
if (v_isShared_4189_ == 0)
{
lean_ctor_set(v___x_4188_, 0, v_snd_4181_);
v___x_4191_ = v___x_4188_;
goto v_reusejp_4190_;
}
else
{
lean_object* v_reuseFailAlloc_4194_; 
v_reuseFailAlloc_4194_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4194_, 0, v_snd_4181_);
lean_ctor_set(v_reuseFailAlloc_4194_, 1, v_cache_4183_);
lean_ctor_set(v_reuseFailAlloc_4194_, 2, v_zetaDeltaFVarIds_4184_);
lean_ctor_set(v_reuseFailAlloc_4194_, 3, v_postponed_4185_);
lean_ctor_set(v_reuseFailAlloc_4194_, 4, v_diag_4186_);
v___x_4191_ = v_reuseFailAlloc_4194_;
goto v_reusejp_4190_;
}
v_reusejp_4190_:
{
lean_object* v___x_4192_; lean_object* v___x_4193_; 
v___x_4192_ = lean_st_ref_set(v___y_4173_, v___x_4191_);
v___x_4193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4193_, 0, v_fst_4180_);
return v___x_4193_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0___redArg___boxed(lean_object* v_e_4197_, lean_object* v___y_4198_, lean_object* v___y_4199_){
_start:
{
lean_object* v_res_4200_; 
v_res_4200_ = l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0___redArg(v_e_4197_, v___y_4198_);
lean_dec(v___y_4198_);
return v_res_4200_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0(lean_object* v_e_4201_, lean_object* v___y_4202_, lean_object* v___y_4203_, lean_object* v___y_4204_, lean_object* v___y_4205_){
_start:
{
lean_object* v___x_4207_; 
v___x_4207_ = l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0___redArg(v_e_4201_, v___y_4203_);
return v___x_4207_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0___boxed(lean_object* v_e_4208_, lean_object* v___y_4209_, lean_object* v___y_4210_, lean_object* v___y_4211_, lean_object* v___y_4212_, lean_object* v___y_4213_){
_start:
{
lean_object* v_res_4214_; 
v_res_4214_ = l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0(v_e_4208_, v___y_4209_, v___y_4210_, v___y_4211_, v___y_4212_);
lean_dec(v___y_4212_);
lean_dec_ref(v___y_4211_);
lean_dec(v___y_4210_);
lean_dec_ref(v___y_4209_);
return v_res_4214_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesAnd___lam__0(lean_object* v_localDecl_4218_, lean_object* v___y_4219_, lean_object* v___y_4220_, lean_object* v___y_4221_, lean_object* v___y_4222_){
_start:
{
lean_object* v___x_4224_; lean_object* v___x_4225_; lean_object* v_a_4226_; lean_object* v___x_4228_; uint8_t v_isShared_4229_; uint8_t v_isSharedCheck_4237_; 
v___x_4224_ = l_Lean_LocalDecl_type(v_localDecl_4218_);
v___x_4225_ = l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0___redArg(v___x_4224_, v___y_4220_);
v_a_4226_ = lean_ctor_get(v___x_4225_, 0);
v_isSharedCheck_4237_ = !lean_is_exclusive(v___x_4225_);
if (v_isSharedCheck_4237_ == 0)
{
v___x_4228_ = v___x_4225_;
v_isShared_4229_ = v_isSharedCheck_4237_;
goto v_resetjp_4227_;
}
else
{
lean_inc(v_a_4226_);
lean_dec(v___x_4225_);
v___x_4228_ = lean_box(0);
v_isShared_4229_ = v_isSharedCheck_4237_;
goto v_resetjp_4227_;
}
v_resetjp_4227_:
{
lean_object* v___x_4230_; lean_object* v___x_4231_; uint8_t v___x_4232_; lean_object* v___x_4233_; lean_object* v___x_4235_; 
v___x_4230_ = ((lean_object*)(l_Lean_MVarId_casesAnd___lam__0___closed__1));
v___x_4231_ = lean_unsigned_to_nat(2u);
v___x_4232_ = l_Lean_Expr_isAppOfArity(v_a_4226_, v___x_4230_, v___x_4231_);
lean_dec(v_a_4226_);
v___x_4233_ = lean_box(v___x_4232_);
if (v_isShared_4229_ == 0)
{
lean_ctor_set(v___x_4228_, 0, v___x_4233_);
v___x_4235_ = v___x_4228_;
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
LEAN_EXPORT lean_object* l_Lean_MVarId_casesAnd___lam__0___boxed(lean_object* v_localDecl_4238_, lean_object* v___y_4239_, lean_object* v___y_4240_, lean_object* v___y_4241_, lean_object* v___y_4242_, lean_object* v___y_4243_){
_start:
{
lean_object* v_res_4244_; 
v_res_4244_ = l_Lean_MVarId_casesAnd___lam__0(v_localDecl_4238_, v___y_4239_, v___y_4240_, v___y_4241_, v___y_4242_);
lean_dec(v___y_4242_);
lean_dec_ref(v___y_4241_);
lean_dec(v___y_4240_);
lean_dec_ref(v___y_4239_);
lean_dec_ref(v_localDecl_4238_);
return v_res_4244_;
}
}
static lean_object* _init_l_Lean_MVarId_casesAnd___closed__3(void){
_start:
{
lean_object* v___x_4249_; lean_object* v___x_4250_; 
v___x_4249_ = ((lean_object*)(l_Lean_MVarId_casesAnd___closed__2));
v___x_4250_ = l_Lean_MessageData_ofFormat(v___x_4249_);
return v___x_4250_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesAnd(lean_object* v_mvarId_4251_, lean_object* v_a_4252_, lean_object* v_a_4253_, lean_object* v_a_4254_, lean_object* v_a_4255_){
_start:
{
lean_object* v___f_4257_; lean_object* v___x_4258_; 
v___f_4257_ = ((lean_object*)(l_Lean_MVarId_casesAnd___closed__0));
lean_inc(v_a_4255_);
lean_inc_ref(v_a_4254_);
lean_inc(v_a_4253_);
lean_inc_ref(v_a_4252_);
v___x_4258_ = l_Lean_MVarId_casesRec(v_mvarId_4251_, v___f_4257_, v_a_4252_, v_a_4253_, v_a_4254_, v_a_4255_);
if (lean_obj_tag(v___x_4258_) == 0)
{
lean_object* v_a_4259_; lean_object* v___x_4260_; lean_object* v___x_4261_; 
v_a_4259_ = lean_ctor_get(v___x_4258_, 0);
lean_inc(v_a_4259_);
lean_dec_ref(v___x_4258_);
v___x_4260_ = lean_obj_once(&l_Lean_MVarId_casesAnd___closed__3, &l_Lean_MVarId_casesAnd___closed__3_once, _init_l_Lean_MVarId_casesAnd___closed__3);
v___x_4261_ = l_Lean_Meta_exactlyOne(v_a_4259_, v___x_4260_, v_a_4252_, v_a_4253_, v_a_4254_, v_a_4255_);
lean_dec(v_a_4255_);
lean_dec_ref(v_a_4254_);
lean_dec(v_a_4253_);
lean_dec_ref(v_a_4252_);
lean_dec(v_a_4259_);
return v___x_4261_;
}
else
{
lean_object* v_a_4262_; lean_object* v___x_4264_; uint8_t v_isShared_4265_; uint8_t v_isSharedCheck_4269_; 
lean_dec(v_a_4255_);
lean_dec_ref(v_a_4254_);
lean_dec(v_a_4253_);
lean_dec_ref(v_a_4252_);
v_a_4262_ = lean_ctor_get(v___x_4258_, 0);
v_isSharedCheck_4269_ = !lean_is_exclusive(v___x_4258_);
if (v_isSharedCheck_4269_ == 0)
{
v___x_4264_ = v___x_4258_;
v_isShared_4265_ = v_isSharedCheck_4269_;
goto v_resetjp_4263_;
}
else
{
lean_inc(v_a_4262_);
lean_dec(v___x_4258_);
v___x_4264_ = lean_box(0);
v_isShared_4265_ = v_isSharedCheck_4269_;
goto v_resetjp_4263_;
}
v_resetjp_4263_:
{
lean_object* v___x_4267_; 
if (v_isShared_4265_ == 0)
{
v___x_4267_ = v___x_4264_;
goto v_reusejp_4266_;
}
else
{
lean_object* v_reuseFailAlloc_4268_; 
v_reuseFailAlloc_4268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4268_, 0, v_a_4262_);
v___x_4267_ = v_reuseFailAlloc_4268_;
goto v_reusejp_4266_;
}
v_reusejp_4266_:
{
return v___x_4267_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesAnd___boxed(lean_object* v_mvarId_4270_, lean_object* v_a_4271_, lean_object* v_a_4272_, lean_object* v_a_4273_, lean_object* v_a_4274_, lean_object* v_a_4275_){
_start:
{
lean_object* v_res_4276_; 
v_res_4276_ = l_Lean_MVarId_casesAnd(v_mvarId_4270_, v_a_4271_, v_a_4272_, v_a_4273_, v_a_4274_);
return v_res_4276_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_substEqs___lam__0(lean_object* v_localDecl_4277_, lean_object* v___y_4278_, lean_object* v___y_4279_, lean_object* v___y_4280_, lean_object* v___y_4281_){
_start:
{
lean_object* v___x_4283_; lean_object* v___x_4284_; lean_object* v_a_4285_; lean_object* v___x_4287_; uint8_t v_isShared_4288_; uint8_t v_isSharedCheck_4299_; 
v___x_4283_ = l_Lean_LocalDecl_type(v_localDecl_4277_);
v___x_4284_ = l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0___redArg(v___x_4283_, v___y_4279_);
v_a_4285_ = lean_ctor_get(v___x_4284_, 0);
v_isSharedCheck_4299_ = !lean_is_exclusive(v___x_4284_);
if (v_isSharedCheck_4299_ == 0)
{
v___x_4287_ = v___x_4284_;
v_isShared_4288_ = v_isSharedCheck_4299_;
goto v_resetjp_4286_;
}
else
{
lean_inc(v_a_4285_);
lean_dec(v___x_4284_);
v___x_4287_ = lean_box(0);
v_isShared_4288_ = v_isSharedCheck_4299_;
goto v_resetjp_4286_;
}
v_resetjp_4286_:
{
uint8_t v___x_4289_; 
v___x_4289_ = l_Lean_Expr_isEq(v_a_4285_);
if (v___x_4289_ == 0)
{
uint8_t v___x_4290_; lean_object* v___x_4291_; lean_object* v___x_4293_; 
v___x_4290_ = l_Lean_Expr_isHEq(v_a_4285_);
lean_dec(v_a_4285_);
v___x_4291_ = lean_box(v___x_4290_);
if (v_isShared_4288_ == 0)
{
lean_ctor_set(v___x_4287_, 0, v___x_4291_);
v___x_4293_ = v___x_4287_;
goto v_reusejp_4292_;
}
else
{
lean_object* v_reuseFailAlloc_4294_; 
v_reuseFailAlloc_4294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4294_, 0, v___x_4291_);
v___x_4293_ = v_reuseFailAlloc_4294_;
goto v_reusejp_4292_;
}
v_reusejp_4292_:
{
return v___x_4293_;
}
}
else
{
lean_object* v___x_4295_; lean_object* v___x_4297_; 
lean_dec(v_a_4285_);
v___x_4295_ = lean_box(v___x_4289_);
if (v_isShared_4288_ == 0)
{
lean_ctor_set(v___x_4287_, 0, v___x_4295_);
v___x_4297_ = v___x_4287_;
goto v_reusejp_4296_;
}
else
{
lean_object* v_reuseFailAlloc_4298_; 
v_reuseFailAlloc_4298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4298_, 0, v___x_4295_);
v___x_4297_ = v_reuseFailAlloc_4298_;
goto v_reusejp_4296_;
}
v_reusejp_4296_:
{
return v___x_4297_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_substEqs___lam__0___boxed(lean_object* v_localDecl_4300_, lean_object* v___y_4301_, lean_object* v___y_4302_, lean_object* v___y_4303_, lean_object* v___y_4304_, lean_object* v___y_4305_){
_start:
{
lean_object* v_res_4306_; 
v_res_4306_ = l_Lean_MVarId_substEqs___lam__0(v_localDecl_4300_, v___y_4301_, v___y_4302_, v___y_4303_, v___y_4304_);
lean_dec(v___y_4304_);
lean_dec_ref(v___y_4303_);
lean_dec(v___y_4302_);
lean_dec_ref(v___y_4301_);
lean_dec_ref(v_localDecl_4300_);
return v_res_4306_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_substEqs(lean_object* v_mvarId_4308_, lean_object* v_a_4309_, lean_object* v_a_4310_, lean_object* v_a_4311_, lean_object* v_a_4312_){
_start:
{
lean_object* v___f_4314_; lean_object* v___x_4315_; 
v___f_4314_ = ((lean_object*)(l_Lean_MVarId_substEqs___closed__0));
lean_inc(v_a_4312_);
lean_inc_ref(v_a_4311_);
lean_inc(v_a_4310_);
lean_inc_ref(v_a_4309_);
v___x_4315_ = l_Lean_MVarId_casesRec(v_mvarId_4308_, v___f_4314_, v_a_4309_, v_a_4310_, v_a_4311_, v_a_4312_);
if (lean_obj_tag(v___x_4315_) == 0)
{
lean_object* v_a_4316_; lean_object* v___x_4317_; lean_object* v___x_4318_; 
v_a_4316_ = lean_ctor_get(v___x_4315_, 0);
lean_inc(v_a_4316_);
lean_dec_ref(v___x_4315_);
v___x_4317_ = lean_obj_once(&l_Lean_MVarId_casesAnd___closed__3, &l_Lean_MVarId_casesAnd___closed__3_once, _init_l_Lean_MVarId_casesAnd___closed__3);
v___x_4318_ = l_Lean_Meta_ensureAtMostOne(v_a_4316_, v___x_4317_, v_a_4309_, v_a_4310_, v_a_4311_, v_a_4312_);
lean_dec(v_a_4312_);
lean_dec_ref(v_a_4311_);
lean_dec(v_a_4310_);
lean_dec_ref(v_a_4309_);
lean_dec(v_a_4316_);
return v___x_4318_;
}
else
{
lean_object* v_a_4319_; lean_object* v___x_4321_; uint8_t v_isShared_4322_; uint8_t v_isSharedCheck_4326_; 
lean_dec(v_a_4312_);
lean_dec_ref(v_a_4311_);
lean_dec(v_a_4310_);
lean_dec_ref(v_a_4309_);
v_a_4319_ = lean_ctor_get(v___x_4315_, 0);
v_isSharedCheck_4326_ = !lean_is_exclusive(v___x_4315_);
if (v_isSharedCheck_4326_ == 0)
{
v___x_4321_ = v___x_4315_;
v_isShared_4322_ = v_isSharedCheck_4326_;
goto v_resetjp_4320_;
}
else
{
lean_inc(v_a_4319_);
lean_dec(v___x_4315_);
v___x_4321_ = lean_box(0);
v_isShared_4322_ = v_isSharedCheck_4326_;
goto v_resetjp_4320_;
}
v_resetjp_4320_:
{
lean_object* v___x_4324_; 
if (v_isShared_4322_ == 0)
{
v___x_4324_ = v___x_4321_;
goto v_reusejp_4323_;
}
else
{
lean_object* v_reuseFailAlloc_4325_; 
v_reuseFailAlloc_4325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4325_, 0, v_a_4319_);
v___x_4324_ = v_reuseFailAlloc_4325_;
goto v_reusejp_4323_;
}
v_reusejp_4323_:
{
return v___x_4324_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_substEqs___boxed(lean_object* v_mvarId_4327_, lean_object* v_a_4328_, lean_object* v_a_4329_, lean_object* v_a_4330_, lean_object* v_a_4331_, lean_object* v_a_4332_){
_start:
{
lean_object* v_res_4333_; 
v_res_4333_ = l_Lean_MVarId_substEqs(v_mvarId_4327_, v_a_4328_, v_a_4329_, v_a_4330_, v_a_4331_);
return v_res_4333_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal___closed__1(void){
_start:
{
lean_object* v___x_4335_; lean_object* v___x_4336_; 
v___x_4335_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal___closed__0));
v___x_4336_ = l_Lean_stringToMessageData(v___x_4335_);
return v___x_4336_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal(lean_object* v_s_4337_, lean_object* v_a_4338_, lean_object* v_a_4339_, lean_object* v_a_4340_, lean_object* v_a_4341_){
_start:
{
lean_object* v___y_4344_; lean_object* v___y_4345_; lean_object* v___y_4346_; lean_object* v___y_4347_; lean_object* v_toInductionSubgoal_4350_; lean_object* v___x_4352_; uint8_t v_isShared_4353_; uint8_t v_isSharedCheck_4366_; 
v_toInductionSubgoal_4350_ = lean_ctor_get(v_s_4337_, 0);
v_isSharedCheck_4366_ = !lean_is_exclusive(v_s_4337_);
if (v_isSharedCheck_4366_ == 0)
{
lean_object* v_unused_4367_; 
v_unused_4367_ = lean_ctor_get(v_s_4337_, 1);
lean_dec(v_unused_4367_);
v___x_4352_ = v_s_4337_;
v_isShared_4353_ = v_isSharedCheck_4366_;
goto v_resetjp_4351_;
}
else
{
lean_inc(v_toInductionSubgoal_4350_);
lean_dec(v_s_4337_);
v___x_4352_ = lean_box(0);
v_isShared_4353_ = v_isSharedCheck_4366_;
goto v_resetjp_4351_;
}
v___jp_4343_:
{
lean_object* v___x_4348_; lean_object* v___x_4349_; 
v___x_4348_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal___closed__1, &l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal___closed__1_once, _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal___closed__1);
v___x_4349_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected_spec__0___redArg(v___x_4348_, v___y_4344_, v___y_4345_, v___y_4346_, v___y_4347_);
return v___x_4349_;
}
v_resetjp_4351_:
{
lean_object* v_mvarId_4354_; lean_object* v_fields_4355_; lean_object* v___x_4356_; lean_object* v___x_4357_; uint8_t v___x_4358_; 
v_mvarId_4354_ = lean_ctor_get(v_toInductionSubgoal_4350_, 0);
lean_inc(v_mvarId_4354_);
v_fields_4355_ = lean_ctor_get(v_toInductionSubgoal_4350_, 1);
lean_inc_ref(v_fields_4355_);
lean_dec_ref(v_toInductionSubgoal_4350_);
v___x_4356_ = lean_array_get_size(v_fields_4355_);
v___x_4357_ = lean_unsigned_to_nat(1u);
v___x_4358_ = lean_nat_dec_eq(v___x_4356_, v___x_4357_);
if (v___x_4358_ == 0)
{
lean_dec_ref(v_fields_4355_);
lean_dec(v_mvarId_4354_);
lean_del_object(v___x_4352_);
v___y_4344_ = v_a_4338_;
v___y_4345_ = v_a_4339_;
v___y_4346_ = v_a_4340_;
v___y_4347_ = v_a_4341_;
goto v___jp_4343_;
}
else
{
lean_object* v___x_4359_; lean_object* v___x_4360_; 
v___x_4359_ = lean_unsigned_to_nat(0u);
v___x_4360_ = lean_array_fget(v_fields_4355_, v___x_4359_);
lean_dec_ref(v_fields_4355_);
if (lean_obj_tag(v___x_4360_) == 1)
{
lean_object* v_fvarId_4361_; lean_object* v___x_4363_; 
v_fvarId_4361_ = lean_ctor_get(v___x_4360_, 0);
lean_inc(v_fvarId_4361_);
lean_dec_ref(v___x_4360_);
if (v_isShared_4353_ == 0)
{
lean_ctor_set(v___x_4352_, 1, v_fvarId_4361_);
lean_ctor_set(v___x_4352_, 0, v_mvarId_4354_);
v___x_4363_ = v___x_4352_;
goto v_reusejp_4362_;
}
else
{
lean_object* v_reuseFailAlloc_4365_; 
v_reuseFailAlloc_4365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4365_, 0, v_mvarId_4354_);
lean_ctor_set(v_reuseFailAlloc_4365_, 1, v_fvarId_4361_);
v___x_4363_ = v_reuseFailAlloc_4365_;
goto v_reusejp_4362_;
}
v_reusejp_4362_:
{
lean_object* v___x_4364_; 
v___x_4364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4364_, 0, v___x_4363_);
return v___x_4364_;
}
}
else
{
lean_dec(v___x_4360_);
lean_dec(v_mvarId_4354_);
lean_del_object(v___x_4352_);
v___y_4344_ = v_a_4338_;
v___y_4345_ = v_a_4339_;
v___y_4346_ = v_a_4340_;
v___y_4347_ = v_a_4341_;
goto v___jp_4343_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal___boxed(lean_object* v_s_4368_, lean_object* v_a_4369_, lean_object* v_a_4370_, lean_object* v_a_4371_, lean_object* v_a_4372_, lean_object* v_a_4373_){
_start:
{
lean_object* v_res_4374_; 
v_res_4374_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal(v_s_4368_, v_a_4369_, v_a_4370_, v_a_4371_, v_a_4372_);
lean_dec(v_a_4372_);
lean_dec_ref(v_a_4371_);
lean_dec(v_a_4370_);
lean_dec_ref(v_a_4369_);
return v_res_4374_;
}
}
static lean_object* _init_l_Lean_MVarId_byCases___closed__3(void){
_start:
{
lean_object* v___x_4379_; lean_object* v___x_4380_; 
v___x_4379_ = ((lean_object*)(l_Lean_MVarId_byCases___closed__2));
v___x_4380_ = l_Lean_stringToMessageData(v___x_4379_);
return v___x_4380_;
}
}
static lean_object* _init_l_Lean_MVarId_byCases___closed__5(void){
_start:
{
lean_object* v___x_4382_; lean_object* v___x_4383_; 
v___x_4382_ = ((lean_object*)(l_Lean_MVarId_byCases___closed__4));
v___x_4383_ = l_Lean_stringToMessageData(v___x_4382_);
return v___x_4383_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_byCases(lean_object* v_mvarId_4384_, lean_object* v_p_4385_, lean_object* v_hName_4386_, lean_object* v_a_4387_, lean_object* v_a_4388_, lean_object* v_a_4389_, lean_object* v_a_4390_){
_start:
{
lean_object* v___x_4392_; lean_object* v___x_4393_; lean_object* v___x_4394_; lean_object* v___x_4395_; lean_object* v___x_4396_; 
v___x_4392_ = ((lean_object*)(l_Lean_MVarId_byCases___closed__1));
lean_inc_ref(v_p_4385_);
v___x_4393_ = l_Lean_mkNot(v_p_4385_);
lean_inc_ref(v_p_4385_);
v___x_4394_ = l_Lean_mkOr(v_p_4385_, v___x_4393_);
lean_inc_ref(v_p_4385_);
v___x_4395_ = l_Lean_mkEM(v_p_4385_);
lean_inc(v_a_4390_);
lean_inc_ref(v_a_4389_);
lean_inc(v_a_4388_);
lean_inc_ref(v_a_4387_);
v___x_4396_ = l_Lean_MVarId_assert(v_mvarId_4384_, v___x_4392_, v___x_4394_, v___x_4395_, v_a_4387_, v_a_4388_, v_a_4389_, v_a_4390_);
if (lean_obj_tag(v___x_4396_) == 0)
{
lean_object* v_a_4397_; uint8_t v___x_4398_; lean_object* v___x_4399_; 
v_a_4397_ = lean_ctor_get(v___x_4396_, 0);
lean_inc(v_a_4397_);
lean_dec_ref(v___x_4396_);
v___x_4398_ = 0;
lean_inc(v_a_4390_);
lean_inc_ref(v_a_4389_);
lean_inc(v_a_4388_);
lean_inc_ref(v_a_4387_);
v___x_4399_ = l_Lean_Meta_intro1Core(v_a_4397_, v___x_4398_, v_a_4387_, v_a_4388_, v_a_4389_, v_a_4390_);
if (lean_obj_tag(v___x_4399_) == 0)
{
lean_object* v_a_4400_; lean_object* v_fst_4401_; lean_object* v_snd_4402_; lean_object* v___x_4404_; uint8_t v_isShared_4405_; uint8_t v_isSharedCheck_4467_; 
v_a_4400_ = lean_ctor_get(v___x_4399_, 0);
lean_inc(v_a_4400_);
lean_dec_ref(v___x_4399_);
v_fst_4401_ = lean_ctor_get(v_a_4400_, 0);
v_snd_4402_ = lean_ctor_get(v_a_4400_, 1);
v_isSharedCheck_4467_ = !lean_is_exclusive(v_a_4400_);
if (v_isSharedCheck_4467_ == 0)
{
v___x_4404_ = v_a_4400_;
v_isShared_4405_ = v_isSharedCheck_4467_;
goto v_resetjp_4403_;
}
else
{
lean_inc(v_snd_4402_);
lean_inc(v_fst_4401_);
lean_dec(v_a_4400_);
v___x_4404_ = lean_box(0);
v_isShared_4405_ = v_isSharedCheck_4467_;
goto v_resetjp_4403_;
}
v_resetjp_4403_:
{
lean_object* v___x_4406_; lean_object* v___x_4407_; lean_object* v___x_4408_; lean_object* v___x_4409_; lean_object* v___x_4410_; lean_object* v___x_4411_; lean_object* v___x_4412_; lean_object* v___x_4413_; lean_object* v___x_4414_; 
v___x_4406_ = lean_box(0);
v___x_4407_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4407_, 0, v_hName_4386_);
lean_ctor_set(v___x_4407_, 1, v___x_4406_);
v___x_4408_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4408_, 0, v___x_4407_);
lean_ctor_set_uint8(v___x_4408_, sizeof(void*)*1, v___x_4398_);
v___x_4409_ = lean_unsigned_to_nat(2u);
v___x_4410_ = lean_mk_empty_array_with_capacity(v___x_4409_);
lean_inc_ref(v___x_4408_);
v___x_4411_ = lean_array_push(v___x_4410_, v___x_4408_);
v___x_4412_ = lean_array_push(v___x_4411_, v___x_4408_);
v___x_4413_ = lean_box(0);
lean_inc(v_a_4390_);
lean_inc_ref(v_a_4389_);
lean_inc(v_a_4388_);
lean_inc_ref(v_a_4387_);
v___x_4414_ = l_Lean_Meta_Cases_cases(v_snd_4402_, v_fst_4401_, v___x_4412_, v___x_4398_, v___x_4413_, v_a_4387_, v_a_4388_, v_a_4389_, v_a_4390_);
if (lean_obj_tag(v___x_4414_) == 0)
{
lean_object* v_a_4415_; lean_object* v___x_4416_; uint8_t v___x_4417_; 
v_a_4415_ = lean_ctor_get(v___x_4414_, 0);
lean_inc(v_a_4415_);
lean_dec_ref(v___x_4414_);
v___x_4416_ = lean_array_get_size(v_a_4415_);
v___x_4417_ = lean_nat_dec_eq(v___x_4416_, v___x_4409_);
if (v___x_4417_ == 0)
{
lean_object* v___x_4418_; lean_object* v___x_4419_; lean_object* v___x_4420_; lean_object* v___x_4421_; lean_object* v___x_4422_; lean_object* v___x_4423_; lean_object* v___x_4424_; 
lean_dec(v_a_4415_);
lean_del_object(v___x_4404_);
v___x_4418_ = lean_obj_once(&l_Lean_MVarId_byCases___closed__3, &l_Lean_MVarId_byCases___closed__3_once, _init_l_Lean_MVarId_byCases___closed__3);
v___x_4419_ = lean_unsigned_to_nat(30u);
v___x_4420_ = l_Lean_inlineExpr(v_p_4385_, v___x_4419_);
v___x_4421_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4421_, 0, v___x_4418_);
lean_ctor_set(v___x_4421_, 1, v___x_4420_);
v___x_4422_ = lean_obj_once(&l_Lean_MVarId_byCases___closed__5, &l_Lean_MVarId_byCases___closed__5_once, _init_l_Lean_MVarId_byCases___closed__5);
v___x_4423_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4423_, 0, v___x_4421_);
lean_ctor_set(v___x_4423_, 1, v___x_4422_);
v___x_4424_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected_spec__0___redArg(v___x_4423_, v_a_4387_, v_a_4388_, v_a_4389_, v_a_4390_);
lean_dec(v_a_4390_);
lean_dec_ref(v_a_4389_);
lean_dec(v_a_4388_);
lean_dec_ref(v_a_4387_);
return v___x_4424_;
}
else
{
lean_object* v___x_4425_; lean_object* v___x_4426_; lean_object* v___x_4427_; 
lean_dec_ref(v_p_4385_);
v___x_4425_ = lean_unsigned_to_nat(0u);
v___x_4426_ = lean_array_fget_borrowed(v_a_4415_, v___x_4425_);
lean_inc(v___x_4426_);
v___x_4427_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal(v___x_4426_, v_a_4387_, v_a_4388_, v_a_4389_, v_a_4390_);
if (lean_obj_tag(v___x_4427_) == 0)
{
lean_object* v_a_4428_; lean_object* v___x_4429_; lean_object* v___x_4430_; lean_object* v___x_4431_; 
v_a_4428_ = lean_ctor_get(v___x_4427_, 0);
lean_inc(v_a_4428_);
lean_dec_ref(v___x_4427_);
v___x_4429_ = lean_unsigned_to_nat(1u);
v___x_4430_ = lean_array_fget(v_a_4415_, v___x_4429_);
lean_dec(v_a_4415_);
v___x_4431_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal(v___x_4430_, v_a_4387_, v_a_4388_, v_a_4389_, v_a_4390_);
lean_dec(v_a_4390_);
lean_dec_ref(v_a_4389_);
lean_dec(v_a_4388_);
lean_dec_ref(v_a_4387_);
if (lean_obj_tag(v___x_4431_) == 0)
{
lean_object* v_a_4432_; lean_object* v___x_4434_; uint8_t v_isShared_4435_; uint8_t v_isSharedCheck_4442_; 
v_a_4432_ = lean_ctor_get(v___x_4431_, 0);
v_isSharedCheck_4442_ = !lean_is_exclusive(v___x_4431_);
if (v_isSharedCheck_4442_ == 0)
{
v___x_4434_ = v___x_4431_;
v_isShared_4435_ = v_isSharedCheck_4442_;
goto v_resetjp_4433_;
}
else
{
lean_inc(v_a_4432_);
lean_dec(v___x_4431_);
v___x_4434_ = lean_box(0);
v_isShared_4435_ = v_isSharedCheck_4442_;
goto v_resetjp_4433_;
}
v_resetjp_4433_:
{
lean_object* v___x_4437_; 
if (v_isShared_4405_ == 0)
{
lean_ctor_set(v___x_4404_, 1, v_a_4432_);
lean_ctor_set(v___x_4404_, 0, v_a_4428_);
v___x_4437_ = v___x_4404_;
goto v_reusejp_4436_;
}
else
{
lean_object* v_reuseFailAlloc_4441_; 
v_reuseFailAlloc_4441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4441_, 0, v_a_4428_);
lean_ctor_set(v_reuseFailAlloc_4441_, 1, v_a_4432_);
v___x_4437_ = v_reuseFailAlloc_4441_;
goto v_reusejp_4436_;
}
v_reusejp_4436_:
{
lean_object* v___x_4439_; 
if (v_isShared_4435_ == 0)
{
lean_ctor_set(v___x_4434_, 0, v___x_4437_);
v___x_4439_ = v___x_4434_;
goto v_reusejp_4438_;
}
else
{
lean_object* v_reuseFailAlloc_4440_; 
v_reuseFailAlloc_4440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4440_, 0, v___x_4437_);
v___x_4439_ = v_reuseFailAlloc_4440_;
goto v_reusejp_4438_;
}
v_reusejp_4438_:
{
return v___x_4439_;
}
}
}
}
else
{
lean_object* v_a_4443_; lean_object* v___x_4445_; uint8_t v_isShared_4446_; uint8_t v_isSharedCheck_4450_; 
lean_dec(v_a_4428_);
lean_del_object(v___x_4404_);
v_a_4443_ = lean_ctor_get(v___x_4431_, 0);
v_isSharedCheck_4450_ = !lean_is_exclusive(v___x_4431_);
if (v_isSharedCheck_4450_ == 0)
{
v___x_4445_ = v___x_4431_;
v_isShared_4446_ = v_isSharedCheck_4450_;
goto v_resetjp_4444_;
}
else
{
lean_inc(v_a_4443_);
lean_dec(v___x_4431_);
v___x_4445_ = lean_box(0);
v_isShared_4446_ = v_isSharedCheck_4450_;
goto v_resetjp_4444_;
}
v_resetjp_4444_:
{
lean_object* v___x_4448_; 
if (v_isShared_4446_ == 0)
{
v___x_4448_ = v___x_4445_;
goto v_reusejp_4447_;
}
else
{
lean_object* v_reuseFailAlloc_4449_; 
v_reuseFailAlloc_4449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4449_, 0, v_a_4443_);
v___x_4448_ = v_reuseFailAlloc_4449_;
goto v_reusejp_4447_;
}
v_reusejp_4447_:
{
return v___x_4448_;
}
}
}
}
else
{
lean_object* v_a_4451_; lean_object* v___x_4453_; uint8_t v_isShared_4454_; uint8_t v_isSharedCheck_4458_; 
lean_dec(v_a_4415_);
lean_del_object(v___x_4404_);
lean_dec(v_a_4390_);
lean_dec_ref(v_a_4389_);
lean_dec(v_a_4388_);
lean_dec_ref(v_a_4387_);
v_a_4451_ = lean_ctor_get(v___x_4427_, 0);
v_isSharedCheck_4458_ = !lean_is_exclusive(v___x_4427_);
if (v_isSharedCheck_4458_ == 0)
{
v___x_4453_ = v___x_4427_;
v_isShared_4454_ = v_isSharedCheck_4458_;
goto v_resetjp_4452_;
}
else
{
lean_inc(v_a_4451_);
lean_dec(v___x_4427_);
v___x_4453_ = lean_box(0);
v_isShared_4454_ = v_isSharedCheck_4458_;
goto v_resetjp_4452_;
}
v_resetjp_4452_:
{
lean_object* v___x_4456_; 
if (v_isShared_4454_ == 0)
{
v___x_4456_ = v___x_4453_;
goto v_reusejp_4455_;
}
else
{
lean_object* v_reuseFailAlloc_4457_; 
v_reuseFailAlloc_4457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4457_, 0, v_a_4451_);
v___x_4456_ = v_reuseFailAlloc_4457_;
goto v_reusejp_4455_;
}
v_reusejp_4455_:
{
return v___x_4456_;
}
}
}
}
}
else
{
lean_object* v_a_4459_; lean_object* v___x_4461_; uint8_t v_isShared_4462_; uint8_t v_isSharedCheck_4466_; 
lean_del_object(v___x_4404_);
lean_dec(v_a_4390_);
lean_dec_ref(v_a_4389_);
lean_dec(v_a_4388_);
lean_dec_ref(v_a_4387_);
lean_dec_ref(v_p_4385_);
v_a_4459_ = lean_ctor_get(v___x_4414_, 0);
v_isSharedCheck_4466_ = !lean_is_exclusive(v___x_4414_);
if (v_isSharedCheck_4466_ == 0)
{
v___x_4461_ = v___x_4414_;
v_isShared_4462_ = v_isSharedCheck_4466_;
goto v_resetjp_4460_;
}
else
{
lean_inc(v_a_4459_);
lean_dec(v___x_4414_);
v___x_4461_ = lean_box(0);
v_isShared_4462_ = v_isSharedCheck_4466_;
goto v_resetjp_4460_;
}
v_resetjp_4460_:
{
lean_object* v___x_4464_; 
if (v_isShared_4462_ == 0)
{
v___x_4464_ = v___x_4461_;
goto v_reusejp_4463_;
}
else
{
lean_object* v_reuseFailAlloc_4465_; 
v_reuseFailAlloc_4465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4465_, 0, v_a_4459_);
v___x_4464_ = v_reuseFailAlloc_4465_;
goto v_reusejp_4463_;
}
v_reusejp_4463_:
{
return v___x_4464_;
}
}
}
}
}
else
{
lean_object* v_a_4468_; lean_object* v___x_4470_; uint8_t v_isShared_4471_; uint8_t v_isSharedCheck_4475_; 
lean_dec(v_a_4390_);
lean_dec_ref(v_a_4389_);
lean_dec(v_a_4388_);
lean_dec_ref(v_a_4387_);
lean_dec(v_hName_4386_);
lean_dec_ref(v_p_4385_);
v_a_4468_ = lean_ctor_get(v___x_4399_, 0);
v_isSharedCheck_4475_ = !lean_is_exclusive(v___x_4399_);
if (v_isSharedCheck_4475_ == 0)
{
v___x_4470_ = v___x_4399_;
v_isShared_4471_ = v_isSharedCheck_4475_;
goto v_resetjp_4469_;
}
else
{
lean_inc(v_a_4468_);
lean_dec(v___x_4399_);
v___x_4470_ = lean_box(0);
v_isShared_4471_ = v_isSharedCheck_4475_;
goto v_resetjp_4469_;
}
v_resetjp_4469_:
{
lean_object* v___x_4473_; 
if (v_isShared_4471_ == 0)
{
v___x_4473_ = v___x_4470_;
goto v_reusejp_4472_;
}
else
{
lean_object* v_reuseFailAlloc_4474_; 
v_reuseFailAlloc_4474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4474_, 0, v_a_4468_);
v___x_4473_ = v_reuseFailAlloc_4474_;
goto v_reusejp_4472_;
}
v_reusejp_4472_:
{
return v___x_4473_;
}
}
}
}
else
{
lean_object* v_a_4476_; lean_object* v___x_4478_; uint8_t v_isShared_4479_; uint8_t v_isSharedCheck_4483_; 
lean_dec(v_a_4390_);
lean_dec_ref(v_a_4389_);
lean_dec(v_a_4388_);
lean_dec_ref(v_a_4387_);
lean_dec(v_hName_4386_);
lean_dec_ref(v_p_4385_);
v_a_4476_ = lean_ctor_get(v___x_4396_, 0);
v_isSharedCheck_4483_ = !lean_is_exclusive(v___x_4396_);
if (v_isSharedCheck_4483_ == 0)
{
v___x_4478_ = v___x_4396_;
v_isShared_4479_ = v_isSharedCheck_4483_;
goto v_resetjp_4477_;
}
else
{
lean_inc(v_a_4476_);
lean_dec(v___x_4396_);
v___x_4478_ = lean_box(0);
v_isShared_4479_ = v_isSharedCheck_4483_;
goto v_resetjp_4477_;
}
v_resetjp_4477_:
{
lean_object* v___x_4481_; 
if (v_isShared_4479_ == 0)
{
v___x_4481_ = v___x_4478_;
goto v_reusejp_4480_;
}
else
{
lean_object* v_reuseFailAlloc_4482_; 
v_reuseFailAlloc_4482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4482_, 0, v_a_4476_);
v___x_4481_ = v_reuseFailAlloc_4482_;
goto v_reusejp_4480_;
}
v_reusejp_4480_:
{
return v___x_4481_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_byCases___boxed(lean_object* v_mvarId_4484_, lean_object* v_p_4485_, lean_object* v_hName_4486_, lean_object* v_a_4487_, lean_object* v_a_4488_, lean_object* v_a_4489_, lean_object* v_a_4490_, lean_object* v_a_4491_){
_start:
{
lean_object* v_res_4492_; 
v_res_4492_ = l_Lean_MVarId_byCases(v_mvarId_4484_, v_p_4485_, v_hName_4486_, v_a_4487_, v_a_4488_, v_a_4489_, v_a_4490_);
return v_res_4492_;
}
}
static lean_object* _init_l_Lean_MVarId_byCasesDec___closed__2(void){
_start:
{
lean_object* v___x_4496_; lean_object* v___x_4497_; lean_object* v___x_4498_; 
v___x_4496_ = lean_box(0);
v___x_4497_ = ((lean_object*)(l_Lean_MVarId_byCasesDec___closed__1));
v___x_4498_ = l_Lean_mkConst(v___x_4497_, v___x_4496_);
return v___x_4498_;
}
}
static lean_object* _init_l_Lean_MVarId_byCasesDec___closed__4(void){
_start:
{
lean_object* v___x_4500_; lean_object* v___x_4501_; 
v___x_4500_ = ((lean_object*)(l_Lean_MVarId_byCasesDec___closed__3));
v___x_4501_ = l_Lean_stringToMessageData(v___x_4500_);
return v___x_4501_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_byCasesDec(lean_object* v_mvarId_4502_, lean_object* v_p_4503_, lean_object* v_dec_4504_, lean_object* v_hName_4505_, lean_object* v_a_4506_, lean_object* v_a_4507_, lean_object* v_a_4508_, lean_object* v_a_4509_){
_start:
{
lean_object* v___x_4511_; lean_object* v___x_4512_; lean_object* v___x_4513_; lean_object* v___x_4514_; lean_object* v___x_4515_; 
v___x_4511_ = ((lean_object*)(l_Lean_MVarId_byCases___closed__1));
v___x_4512_ = lean_box(0);
v___x_4513_ = lean_obj_once(&l_Lean_MVarId_byCasesDec___closed__2, &l_Lean_MVarId_byCasesDec___closed__2_once, _init_l_Lean_MVarId_byCasesDec___closed__2);
lean_inc_ref(v_p_4503_);
v___x_4514_ = l_Lean_Expr_app___override(v___x_4513_, v_p_4503_);
lean_inc(v_a_4509_);
lean_inc_ref(v_a_4508_);
lean_inc(v_a_4507_);
lean_inc_ref(v_a_4506_);
v___x_4515_ = l_Lean_MVarId_assert(v_mvarId_4502_, v___x_4511_, v___x_4514_, v_dec_4504_, v_a_4506_, v_a_4507_, v_a_4508_, v_a_4509_);
if (lean_obj_tag(v___x_4515_) == 0)
{
lean_object* v_a_4516_; uint8_t v___x_4517_; lean_object* v___x_4518_; 
v_a_4516_ = lean_ctor_get(v___x_4515_, 0);
lean_inc(v_a_4516_);
lean_dec_ref(v___x_4515_);
v___x_4517_ = 0;
lean_inc(v_a_4509_);
lean_inc_ref(v_a_4508_);
lean_inc(v_a_4507_);
lean_inc_ref(v_a_4506_);
v___x_4518_ = l_Lean_Meta_intro1Core(v_a_4516_, v___x_4517_, v_a_4506_, v_a_4507_, v_a_4508_, v_a_4509_);
if (lean_obj_tag(v___x_4518_) == 0)
{
lean_object* v_a_4519_; lean_object* v_fst_4520_; lean_object* v_snd_4521_; lean_object* v___x_4523_; uint8_t v_isShared_4524_; uint8_t v_isSharedCheck_4585_; 
v_a_4519_ = lean_ctor_get(v___x_4518_, 0);
lean_inc(v_a_4519_);
lean_dec_ref(v___x_4518_);
v_fst_4520_ = lean_ctor_get(v_a_4519_, 0);
v_snd_4521_ = lean_ctor_get(v_a_4519_, 1);
v_isSharedCheck_4585_ = !lean_is_exclusive(v_a_4519_);
if (v_isSharedCheck_4585_ == 0)
{
v___x_4523_ = v_a_4519_;
v_isShared_4524_ = v_isSharedCheck_4585_;
goto v_resetjp_4522_;
}
else
{
lean_inc(v_snd_4521_);
lean_inc(v_fst_4520_);
lean_dec(v_a_4519_);
v___x_4523_ = lean_box(0);
v_isShared_4524_ = v_isSharedCheck_4585_;
goto v_resetjp_4522_;
}
v_resetjp_4522_:
{
lean_object* v___x_4525_; lean_object* v___x_4526_; lean_object* v___x_4527_; lean_object* v___x_4528_; lean_object* v___x_4529_; lean_object* v___x_4530_; lean_object* v___x_4531_; lean_object* v___x_4532_; 
v___x_4525_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4525_, 0, v_hName_4505_);
lean_ctor_set(v___x_4525_, 1, v___x_4512_);
v___x_4526_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4526_, 0, v___x_4525_);
lean_ctor_set_uint8(v___x_4526_, sizeof(void*)*1, v___x_4517_);
v___x_4527_ = lean_unsigned_to_nat(2u);
v___x_4528_ = lean_mk_empty_array_with_capacity(v___x_4527_);
lean_inc_ref(v___x_4526_);
v___x_4529_ = lean_array_push(v___x_4528_, v___x_4526_);
v___x_4530_ = lean_array_push(v___x_4529_, v___x_4526_);
v___x_4531_ = lean_box(0);
lean_inc(v_a_4509_);
lean_inc_ref(v_a_4508_);
lean_inc(v_a_4507_);
lean_inc_ref(v_a_4506_);
v___x_4532_ = l_Lean_Meta_Cases_cases(v_snd_4521_, v_fst_4520_, v___x_4530_, v___x_4517_, v___x_4531_, v_a_4506_, v_a_4507_, v_a_4508_, v_a_4509_);
if (lean_obj_tag(v___x_4532_) == 0)
{
lean_object* v_a_4533_; lean_object* v___x_4534_; uint8_t v___x_4535_; 
v_a_4533_ = lean_ctor_get(v___x_4532_, 0);
lean_inc(v_a_4533_);
lean_dec_ref(v___x_4532_);
v___x_4534_ = lean_array_get_size(v_a_4533_);
v___x_4535_ = lean_nat_dec_eq(v___x_4534_, v___x_4527_);
if (v___x_4535_ == 0)
{
lean_object* v___x_4536_; lean_object* v___x_4537_; lean_object* v___x_4538_; lean_object* v___x_4539_; lean_object* v___x_4540_; lean_object* v___x_4541_; lean_object* v___x_4542_; 
lean_dec(v_a_4533_);
lean_del_object(v___x_4523_);
v___x_4536_ = lean_obj_once(&l_Lean_MVarId_byCasesDec___closed__4, &l_Lean_MVarId_byCasesDec___closed__4_once, _init_l_Lean_MVarId_byCasesDec___closed__4);
v___x_4537_ = lean_unsigned_to_nat(30u);
v___x_4538_ = l_Lean_inlineExpr(v_p_4503_, v___x_4537_);
v___x_4539_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4539_, 0, v___x_4536_);
lean_ctor_set(v___x_4539_, 1, v___x_4538_);
v___x_4540_ = lean_obj_once(&l_Lean_MVarId_byCases___closed__5, &l_Lean_MVarId_byCases___closed__5_once, _init_l_Lean_MVarId_byCases___closed__5);
v___x_4541_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4541_, 0, v___x_4539_);
lean_ctor_set(v___x_4541_, 1, v___x_4540_);
v___x_4542_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected_spec__0___redArg(v___x_4541_, v_a_4506_, v_a_4507_, v_a_4508_, v_a_4509_);
lean_dec(v_a_4509_);
lean_dec_ref(v_a_4508_);
lean_dec(v_a_4507_);
lean_dec_ref(v_a_4506_);
return v___x_4542_;
}
else
{
lean_object* v___x_4543_; lean_object* v___x_4544_; lean_object* v___x_4545_; 
lean_dec_ref(v_p_4503_);
v___x_4543_ = lean_unsigned_to_nat(1u);
v___x_4544_ = lean_array_fget_borrowed(v_a_4533_, v___x_4543_);
lean_inc(v___x_4544_);
v___x_4545_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal(v___x_4544_, v_a_4506_, v_a_4507_, v_a_4508_, v_a_4509_);
if (lean_obj_tag(v___x_4545_) == 0)
{
lean_object* v_a_4546_; lean_object* v___x_4547_; lean_object* v___x_4548_; lean_object* v___x_4549_; 
v_a_4546_ = lean_ctor_get(v___x_4545_, 0);
lean_inc(v_a_4546_);
lean_dec_ref(v___x_4545_);
v___x_4547_ = lean_unsigned_to_nat(0u);
v___x_4548_ = lean_array_fget(v_a_4533_, v___x_4547_);
lean_dec(v_a_4533_);
v___x_4549_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal(v___x_4548_, v_a_4506_, v_a_4507_, v_a_4508_, v_a_4509_);
lean_dec(v_a_4509_);
lean_dec_ref(v_a_4508_);
lean_dec(v_a_4507_);
lean_dec_ref(v_a_4506_);
if (lean_obj_tag(v___x_4549_) == 0)
{
lean_object* v_a_4550_; lean_object* v___x_4552_; uint8_t v_isShared_4553_; uint8_t v_isSharedCheck_4560_; 
v_a_4550_ = lean_ctor_get(v___x_4549_, 0);
v_isSharedCheck_4560_ = !lean_is_exclusive(v___x_4549_);
if (v_isSharedCheck_4560_ == 0)
{
v___x_4552_ = v___x_4549_;
v_isShared_4553_ = v_isSharedCheck_4560_;
goto v_resetjp_4551_;
}
else
{
lean_inc(v_a_4550_);
lean_dec(v___x_4549_);
v___x_4552_ = lean_box(0);
v_isShared_4553_ = v_isSharedCheck_4560_;
goto v_resetjp_4551_;
}
v_resetjp_4551_:
{
lean_object* v___x_4555_; 
if (v_isShared_4524_ == 0)
{
lean_ctor_set(v___x_4523_, 1, v_a_4550_);
lean_ctor_set(v___x_4523_, 0, v_a_4546_);
v___x_4555_ = v___x_4523_;
goto v_reusejp_4554_;
}
else
{
lean_object* v_reuseFailAlloc_4559_; 
v_reuseFailAlloc_4559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4559_, 0, v_a_4546_);
lean_ctor_set(v_reuseFailAlloc_4559_, 1, v_a_4550_);
v___x_4555_ = v_reuseFailAlloc_4559_;
goto v_reusejp_4554_;
}
v_reusejp_4554_:
{
lean_object* v___x_4557_; 
if (v_isShared_4553_ == 0)
{
lean_ctor_set(v___x_4552_, 0, v___x_4555_);
v___x_4557_ = v___x_4552_;
goto v_reusejp_4556_;
}
else
{
lean_object* v_reuseFailAlloc_4558_; 
v_reuseFailAlloc_4558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4558_, 0, v___x_4555_);
v___x_4557_ = v_reuseFailAlloc_4558_;
goto v_reusejp_4556_;
}
v_reusejp_4556_:
{
return v___x_4557_;
}
}
}
}
else
{
lean_object* v_a_4561_; lean_object* v___x_4563_; uint8_t v_isShared_4564_; uint8_t v_isSharedCheck_4568_; 
lean_dec(v_a_4546_);
lean_del_object(v___x_4523_);
v_a_4561_ = lean_ctor_get(v___x_4549_, 0);
v_isSharedCheck_4568_ = !lean_is_exclusive(v___x_4549_);
if (v_isSharedCheck_4568_ == 0)
{
v___x_4563_ = v___x_4549_;
v_isShared_4564_ = v_isSharedCheck_4568_;
goto v_resetjp_4562_;
}
else
{
lean_inc(v_a_4561_);
lean_dec(v___x_4549_);
v___x_4563_ = lean_box(0);
v_isShared_4564_ = v_isSharedCheck_4568_;
goto v_resetjp_4562_;
}
v_resetjp_4562_:
{
lean_object* v___x_4566_; 
if (v_isShared_4564_ == 0)
{
v___x_4566_ = v___x_4563_;
goto v_reusejp_4565_;
}
else
{
lean_object* v_reuseFailAlloc_4567_; 
v_reuseFailAlloc_4567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4567_, 0, v_a_4561_);
v___x_4566_ = v_reuseFailAlloc_4567_;
goto v_reusejp_4565_;
}
v_reusejp_4565_:
{
return v___x_4566_;
}
}
}
}
else
{
lean_object* v_a_4569_; lean_object* v___x_4571_; uint8_t v_isShared_4572_; uint8_t v_isSharedCheck_4576_; 
lean_dec(v_a_4533_);
lean_del_object(v___x_4523_);
lean_dec(v_a_4509_);
lean_dec_ref(v_a_4508_);
lean_dec(v_a_4507_);
lean_dec_ref(v_a_4506_);
v_a_4569_ = lean_ctor_get(v___x_4545_, 0);
v_isSharedCheck_4576_ = !lean_is_exclusive(v___x_4545_);
if (v_isSharedCheck_4576_ == 0)
{
v___x_4571_ = v___x_4545_;
v_isShared_4572_ = v_isSharedCheck_4576_;
goto v_resetjp_4570_;
}
else
{
lean_inc(v_a_4569_);
lean_dec(v___x_4545_);
v___x_4571_ = lean_box(0);
v_isShared_4572_ = v_isSharedCheck_4576_;
goto v_resetjp_4570_;
}
v_resetjp_4570_:
{
lean_object* v___x_4574_; 
if (v_isShared_4572_ == 0)
{
v___x_4574_ = v___x_4571_;
goto v_reusejp_4573_;
}
else
{
lean_object* v_reuseFailAlloc_4575_; 
v_reuseFailAlloc_4575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4575_, 0, v_a_4569_);
v___x_4574_ = v_reuseFailAlloc_4575_;
goto v_reusejp_4573_;
}
v_reusejp_4573_:
{
return v___x_4574_;
}
}
}
}
}
else
{
lean_object* v_a_4577_; lean_object* v___x_4579_; uint8_t v_isShared_4580_; uint8_t v_isSharedCheck_4584_; 
lean_del_object(v___x_4523_);
lean_dec(v_a_4509_);
lean_dec_ref(v_a_4508_);
lean_dec(v_a_4507_);
lean_dec_ref(v_a_4506_);
lean_dec_ref(v_p_4503_);
v_a_4577_ = lean_ctor_get(v___x_4532_, 0);
v_isSharedCheck_4584_ = !lean_is_exclusive(v___x_4532_);
if (v_isSharedCheck_4584_ == 0)
{
v___x_4579_ = v___x_4532_;
v_isShared_4580_ = v_isSharedCheck_4584_;
goto v_resetjp_4578_;
}
else
{
lean_inc(v_a_4577_);
lean_dec(v___x_4532_);
v___x_4579_ = lean_box(0);
v_isShared_4580_ = v_isSharedCheck_4584_;
goto v_resetjp_4578_;
}
v_resetjp_4578_:
{
lean_object* v___x_4582_; 
if (v_isShared_4580_ == 0)
{
v___x_4582_ = v___x_4579_;
goto v_reusejp_4581_;
}
else
{
lean_object* v_reuseFailAlloc_4583_; 
v_reuseFailAlloc_4583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4583_, 0, v_a_4577_);
v___x_4582_ = v_reuseFailAlloc_4583_;
goto v_reusejp_4581_;
}
v_reusejp_4581_:
{
return v___x_4582_;
}
}
}
}
}
else
{
lean_object* v_a_4586_; lean_object* v___x_4588_; uint8_t v_isShared_4589_; uint8_t v_isSharedCheck_4593_; 
lean_dec(v_a_4509_);
lean_dec_ref(v_a_4508_);
lean_dec(v_a_4507_);
lean_dec_ref(v_a_4506_);
lean_dec(v_hName_4505_);
lean_dec_ref(v_p_4503_);
v_a_4586_ = lean_ctor_get(v___x_4518_, 0);
v_isSharedCheck_4593_ = !lean_is_exclusive(v___x_4518_);
if (v_isSharedCheck_4593_ == 0)
{
v___x_4588_ = v___x_4518_;
v_isShared_4589_ = v_isSharedCheck_4593_;
goto v_resetjp_4587_;
}
else
{
lean_inc(v_a_4586_);
lean_dec(v___x_4518_);
v___x_4588_ = lean_box(0);
v_isShared_4589_ = v_isSharedCheck_4593_;
goto v_resetjp_4587_;
}
v_resetjp_4587_:
{
lean_object* v___x_4591_; 
if (v_isShared_4589_ == 0)
{
v___x_4591_ = v___x_4588_;
goto v_reusejp_4590_;
}
else
{
lean_object* v_reuseFailAlloc_4592_; 
v_reuseFailAlloc_4592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4592_, 0, v_a_4586_);
v___x_4591_ = v_reuseFailAlloc_4592_;
goto v_reusejp_4590_;
}
v_reusejp_4590_:
{
return v___x_4591_;
}
}
}
}
else
{
lean_object* v_a_4594_; lean_object* v___x_4596_; uint8_t v_isShared_4597_; uint8_t v_isSharedCheck_4601_; 
lean_dec(v_a_4509_);
lean_dec_ref(v_a_4508_);
lean_dec(v_a_4507_);
lean_dec_ref(v_a_4506_);
lean_dec(v_hName_4505_);
lean_dec_ref(v_p_4503_);
v_a_4594_ = lean_ctor_get(v___x_4515_, 0);
v_isSharedCheck_4601_ = !lean_is_exclusive(v___x_4515_);
if (v_isSharedCheck_4601_ == 0)
{
v___x_4596_ = v___x_4515_;
v_isShared_4597_ = v_isSharedCheck_4601_;
goto v_resetjp_4595_;
}
else
{
lean_inc(v_a_4594_);
lean_dec(v___x_4515_);
v___x_4596_ = lean_box(0);
v_isShared_4597_ = v_isSharedCheck_4601_;
goto v_resetjp_4595_;
}
v_resetjp_4595_:
{
lean_object* v___x_4599_; 
if (v_isShared_4597_ == 0)
{
v___x_4599_ = v___x_4596_;
goto v_reusejp_4598_;
}
else
{
lean_object* v_reuseFailAlloc_4600_; 
v_reuseFailAlloc_4600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4600_, 0, v_a_4594_);
v___x_4599_ = v_reuseFailAlloc_4600_;
goto v_reusejp_4598_;
}
v_reusejp_4598_:
{
return v___x_4599_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_byCasesDec___boxed(lean_object* v_mvarId_4602_, lean_object* v_p_4603_, lean_object* v_dec_4604_, lean_object* v_hName_4605_, lean_object* v_a_4606_, lean_object* v_a_4607_, lean_object* v_a_4608_, lean_object* v_a_4609_, lean_object* v_a_4610_){
_start:
{
lean_object* v_res_4611_; 
v_res_4611_ = l_Lean_MVarId_byCasesDec(v_mvarId_4602_, v_p_4603_, v_dec_4604_, v_hName_4605_, v_a_4606_, v_a_4607_, v_a_4608_, v_a_4609_);
return v_res_4611_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4663_; lean_object* v___x_4664_; lean_object* v___x_4665_; 
v___x_4663_ = lean_unsigned_to_nat(4241171151u);
v___x_4664_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_));
v___x_4665_ = l_Lean_Name_num___override(v___x_4664_, v___x_4663_);
return v___x_4665_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4667_; lean_object* v___x_4668_; lean_object* v___x_4669_; 
v___x_4667_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_));
v___x_4668_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_);
v___x_4669_ = l_Lean_Name_str___override(v___x_4668_, v___x_4667_);
return v___x_4669_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4671_; lean_object* v___x_4672_; lean_object* v___x_4673_; 
v___x_4671_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_));
v___x_4672_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_);
v___x_4673_ = l_Lean_Name_str___override(v___x_4672_, v___x_4671_);
return v___x_4673_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4674_; lean_object* v___x_4675_; lean_object* v___x_4676_; 
v___x_4674_ = lean_unsigned_to_nat(2u);
v___x_4675_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_);
v___x_4676_ = l_Lean_Name_num___override(v___x_4675_, v___x_4674_);
return v___x_4676_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4678_; uint8_t v___x_4679_; lean_object* v___x_4680_; lean_object* v___x_4681_; 
v___x_4678_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_));
v___x_4679_ = 0;
v___x_4680_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_);
v___x_4681_ = l_Lean_registerTraceClass(v___x_4678_, v___x_4679_, v___x_4680_);
return v___x_4681_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2____boxed(lean_object* v_a_4682_){
_start:
{
lean_object* v_res_4683_; 
v_res_4683_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_();
return v_res_4683_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Induction(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Acyclic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_UnifyEq(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Constructions_SparseCasesOn(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Constructions_CtorIdx(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Cases(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
