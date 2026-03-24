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
size_t v_x_2566__boxed_913_; size_t v_x_2567__boxed_914_; lean_object* v_res_915_; 
v_x_2566__boxed_913_ = lean_unbox_usize(v_x_909_);
lean_dec(v_x_909_);
v_x_2567__boxed_914_ = lean_unbox_usize(v_x_910_);
lean_dec(v_x_910_);
v_res_915_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg(v_x_908_, v_x_2566__boxed_913_, v_x_2567__boxed_914_, v_x_911_, v_x_912_);
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
lean_dec(v___y_1037_);
lean_dec_ref(v___y_1036_);
lean_dec(v___y_1035_);
lean_dec_ref(v___y_1034_);
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
lean_dec(v_a_1061_);
lean_dec_ref(v_a_1060_);
lean_dec(v_a_1059_);
lean_dec_ref(v_a_1058_);
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
size_t v_x_2963__boxed_1098_; size_t v_x_2964__boxed_1099_; lean_object* v_res_1100_; 
v_x_2963__boxed_1098_ = lean_unbox_usize(v_x_1094_);
lean_dec(v_x_1094_);
v_x_2964__boxed_1099_ = lean_unbox_usize(v_x_1095_);
lean_dec(v_x_1095_);
v_res_1100_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3(v_00_u03b2_1092_, v_x_1093_, v_x_2963__boxed_1098_, v_x_2964__boxed_1099_, v_x_1096_, v_x_1097_);
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
uint8_t v___x_6270__boxed_1270_; lean_object* v_res_1271_; 
v___x_6270__boxed_1270_ = lean_unbox(v___x_1255_);
v_res_1271_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__0(v_mvarId_1253_, v_newEqs_1254_, v___x_6270__boxed_1270_, v_h_x27_1256_, v_newIndices_1257_, v___x_1258_, v_a_1259_, v___x_1260_, v___x_1261_, v_e_1262_, v___x_1263_, v_newEq_1264_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_);
lean_dec(v___y_1268_);
lean_dec_ref(v___y_1267_);
lean_dec(v___y_1266_);
lean_dec_ref(v___y_1265_);
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
uint8_t v___x_6522__boxed_1321_; lean_object* v_res_1322_; 
v___x_6522__boxed_1321_ = lean_unbox(v___x_1308_);
v_res_1322_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__1(v_e_1305_, v_h_x27_1306_, v_mvarId_1307_, v___x_6522__boxed_1321_, v_newIndices_1309_, v___x_1310_, v_a_1311_, v___x_1312_, v___x_1313_, v_newEqs_1314_, v_newRefls_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_);
lean_dec(v___y_1319_);
lean_dec_ref(v___y_1318_);
lean_dec(v___y_1317_);
lean_dec_ref(v___y_1316_);
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
uint8_t v___x_6587__boxed_1354_; lean_object* v_res_1355_; 
v___x_6587__boxed_1354_ = lean_unbox(v___x_1342_);
v_res_1355_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__2(v_e_1340_, v_mvarId_1341_, v___x_6587__boxed_1354_, v_newIndices_1343_, v___x_1344_, v_a_1345_, v___x_1346_, v___x_1347_, v_h_x27_1348_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_);
lean_dec(v___y_1352_);
lean_dec_ref(v___y_1351_);
lean_dec(v___y_1350_);
lean_dec_ref(v___y_1349_);
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
uint8_t v___x_6629__boxed_1408_; lean_object* v_res_1409_; 
v___x_6629__boxed_1408_ = lean_unbox(v___x_1394_);
v_res_1409_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__3(v_e_1392_, v_mvarId_1393_, v___x_6629__boxed_1408_, v___x_1395_, v_a_1396_, v___x_1397_, v___x_1398_, v___x_1399_, v_varName_x3f_1400_, v_newIndices_1401_, v_x_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_);
lean_dec(v___y_1406_);
lean_dec_ref(v___y_1405_);
lean_dec(v___y_1404_);
lean_dec_ref(v___y_1403_);
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
lean_dec(v___y_1535_);
lean_dec_ref(v___y_1534_);
lean_dec(v___y_1533_);
lean_dec_ref(v___y_1532_);
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
lean_dec(v___y_1544_);
lean_dec_ref(v___y_1543_);
lean_dec(v___y_1542_);
lean_dec_ref(v___y_1541_);
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
lean_dec(v_a_1618_);
lean_dec_ref(v_a_1617_);
lean_dec(v_a_1616_);
lean_dec_ref(v_a_1615_);
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
lean_dec_ref(v___y_1623_);
return v___x_1633_;
}
else
{
lean_object* v_a_1634_; lean_object* v___x_1636_; uint8_t v_isShared_1637_; uint8_t v_isSharedCheck_1641_; 
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
lean_dec(v___y_1647_);
lean_dec_ref(v___y_1646_);
lean_dec(v___y_1645_);
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
lean_dec(v_a_1664_);
lean_dec_ref(v_a_1663_);
lean_dec(v_a_1662_);
lean_dec_ref(v_a_1661_);
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
lean_inc_ref(v_a_1739_);
lean_inc(v_a_1738_);
lean_inc_ref(v_a_1737_);
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
return v___x_1762_;
}
else
{
lean_object* v_a_1763_; lean_object* v___x_1765_; uint8_t v_isShared_1766_; uint8_t v_isSharedCheck_1770_; 
lean_dec(v_a_1753_);
lean_dec_ref(v_env_1746_);
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
lean_dec(v_a_1783_);
lean_dec_ref(v_a_1782_);
lean_dec(v_a_1781_);
lean_dec_ref(v_a_1780_);
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
uint8_t v___y_9117__boxed_1887_; size_t v_i_boxed_1888_; size_t v_stop_boxed_1889_; uint8_t v_res_1890_; lean_object* v_r_1891_; 
v___y_9117__boxed_1887_ = lean_unbox(v___y_1883_);
v_i_boxed_1888_ = lean_unbox_usize(v_i_1885_);
lean_dec(v_i_1885_);
v_stop_boxed_1889_ = lean_unbox_usize(v_stop_1886_);
lean_dec(v_stop_1886_);
v_res_1890_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__2(v_fvarId_1882_, v___y_9117__boxed_1887_, v_as_1884_, v_i_boxed_1888_, v_stop_boxed_1889_);
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
uint8_t v___x_9144__boxed_1913_; uint8_t v___y_9145__boxed_1914_; uint8_t v_res_1915_; lean_object* v_r_1916_; 
v___x_9144__boxed_1913_ = lean_unbox(v___x_1909_);
v___y_9145__boxed_1914_ = lean_unbox(v___y_1910_);
v_res_1915_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___lam__1(v___x_1907_, v___x_1908_, v___x_9144__boxed_1913_, v___y_9145__boxed_1914_, v___x_1911_, v_fvarId_1912_);
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
uint8_t v___y_9194__boxed_1941_; uint8_t v_res_1942_; lean_object* v_r_1943_; 
v___y_9194__boxed_1941_ = lean_unbox(v___y_1939_);
v_res_1942_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___lam__0(v___y_9194__boxed_1941_, v_x_1940_);
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
v___y_2019_ = v_value_2084_;
v___y_2020_ = v___f_2072_;
v___y_2021_ = v___f_2069_;
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
v___y_2029_ = v_value_2084_;
v___y_2030_ = v___f_2072_;
v___y_2031_ = v___f_2069_;
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
v___y_2029_ = v_value_2084_;
v___y_2030_ = v___f_2072_;
v___y_2031_ = v___f_2069_;
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
v___x_2024_ = l_Lean_Expr_hasFVar(v___y_2019_);
if (v___x_2024_ == 0)
{
uint8_t v___x_2025_; 
v___x_2025_ = l_Lean_Expr_hasMVar(v___y_2019_);
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
v___x_2026_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___y_2020_, v___y_2021_, v___y_2019_, v_snd_2023_);
v___y_2014_ = v___x_2026_;
goto v___jp_2013_;
}
}
else
{
lean_object* v___x_2027_; 
v___x_2027_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___y_2020_, v___y_2021_, v___y_2019_, v_snd_2023_);
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
uint8_t v___x_9224__boxed_2123_; size_t v_i_boxed_2124_; size_t v_stop_boxed_2125_; lean_object* v_res_2126_; 
v___x_9224__boxed_2123_ = lean_unbox(v___x_2114_);
v_i_boxed_2124_ = lean_unbox_usize(v_i_2119_);
lean_dec(v_i_2119_);
v_stop_boxed_2125_ = lean_unbox_usize(v_stop_2120_);
lean_dec(v_stop_2120_);
v_res_2126_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg(v___x_9224__boxed_2123_, v___x_2115_, v___x_2116_, v_ctx_2117_, v_as_2118_, v_i_boxed_2124_, v_stop_boxed_2125_, v___y_2121_);
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
uint8_t v___x_9531__boxed_2217_; size_t v_i_boxed_2218_; size_t v_stop_boxed_2219_; lean_object* v_res_2220_; 
v___x_9531__boxed_2217_ = lean_unbox(v___x_2205_);
v_i_boxed_2218_ = lean_unbox_usize(v_i_2210_);
lean_dec(v_i_2210_);
v_stop_boxed_2219_ = lean_unbox_usize(v_stop_2211_);
lean_dec(v_stop_2211_);
v_res_2220_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4_spec__5(v___x_9531__boxed_2217_, v___x_2206_, v___x_2207_, v_ctx_2208_, v_as_2209_, v_i_boxed_2218_, v_stop_boxed_2219_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_);
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
uint8_t v___x_9550__boxed_2231_; lean_object* v_res_2232_; 
v___x_9550__boxed_2231_ = lean_unbox(v___x_2221_);
v_res_2232_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4(v___x_9550__boxed_2231_, v___x_2222_, v___x_2223_, v_ctx_2224_, v_x_2225_, v___y_2226_, v___y_2227_, v___y_2228_, v___y_2229_);
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
uint8_t v___x_9695__boxed_2264_; lean_object* v_res_2265_; 
v___x_9695__boxed_2264_ = lean_unbox(v___x_2254_);
v_res_2265_ = l_Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4(v___x_9695__boxed_2264_, v___x_2255_, v___x_2256_, v_ctx_2257_, v_t_2258_, v___y_2259_, v___y_2260_, v___y_2261_, v___y_2262_);
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
uint8_t v___x_9822__boxed_2363_; size_t v_i_boxed_2364_; size_t v_stop_boxed_2365_; lean_object* v_res_2366_; 
v___x_9822__boxed_2363_ = lean_unbox(v___x_2351_);
v_i_boxed_2364_ = lean_unbox_usize(v_i_2356_);
lean_dec(v_i_2356_);
v_stop_boxed_2365_ = lean_unbox_usize(v_stop_2357_);
lean_dec(v_stop_2357_);
v_res_2366_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5(v___x_9822__boxed_2363_, v___x_2352_, v___x_2353_, v_ctx_2354_, v_as_2355_, v_i_boxed_2364_, v_stop_boxed_2365_, v___y_2358_, v___y_2359_, v___y_2360_, v___y_2361_);
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
lean_dec(v___y_2448_);
lean_dec_ref(v___y_2447_);
lean_dec(v___y_2446_);
lean_dec_ref(v___y_2445_);
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
lean_dec(v___y_2500_);
lean_dec_ref(v___y_2499_);
lean_dec(v___y_2498_);
lean_dec_ref(v___y_2497_);
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
lean_dec(v_a_2521_);
lean_dec_ref(v_a_2520_);
lean_dec(v_a_2519_);
lean_dec_ref(v_a_2518_);
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
lean_object* v_fileName_2654_; lean_object* v_fileMap_2655_; lean_object* v_options_2656_; lean_object* v_currRecDepth_2657_; lean_object* v_maxRecDepth_2658_; lean_object* v_ref_2659_; lean_object* v_currNamespace_2660_; lean_object* v_openDecls_2661_; lean_object* v_initHeartbeats_2662_; lean_object* v_maxHeartbeats_2663_; lean_object* v_quotContext_2664_; lean_object* v_currMacroScope_2665_; uint8_t v_diag_2666_; lean_object* v_cancelTk_x3f_2667_; uint8_t v_suppressElabErrors_2668_; lean_object* v_inheritedTraceOptions_2669_; uint8_t v___x_2670_; 
v_fileName_2654_ = lean_ctor_get(v_a_2651_, 0);
lean_inc_ref(v_fileName_2654_);
v_fileMap_2655_ = lean_ctor_get(v_a_2651_, 1);
lean_inc_ref(v_fileMap_2655_);
v_options_2656_ = lean_ctor_get(v_a_2651_, 2);
lean_inc_ref(v_options_2656_);
v_currRecDepth_2657_ = lean_ctor_get(v_a_2651_, 3);
lean_inc(v_currRecDepth_2657_);
v_maxRecDepth_2658_ = lean_ctor_get(v_a_2651_, 4);
lean_inc(v_maxRecDepth_2658_);
v_ref_2659_ = lean_ctor_get(v_a_2651_, 5);
lean_inc(v_ref_2659_);
v_currNamespace_2660_ = lean_ctor_get(v_a_2651_, 6);
lean_inc(v_currNamespace_2660_);
v_openDecls_2661_ = lean_ctor_get(v_a_2651_, 7);
lean_inc(v_openDecls_2661_);
v_initHeartbeats_2662_ = lean_ctor_get(v_a_2651_, 8);
lean_inc(v_initHeartbeats_2662_);
v_maxHeartbeats_2663_ = lean_ctor_get(v_a_2651_, 9);
lean_inc(v_maxHeartbeats_2663_);
v_quotContext_2664_ = lean_ctor_get(v_a_2651_, 10);
lean_inc(v_quotContext_2664_);
v_currMacroScope_2665_ = lean_ctor_get(v_a_2651_, 11);
lean_inc(v_currMacroScope_2665_);
v_diag_2666_ = lean_ctor_get_uint8(v_a_2651_, sizeof(void*)*14);
v_cancelTk_x3f_2667_ = lean_ctor_get(v_a_2651_, 12);
lean_inc(v_cancelTk_x3f_2667_);
v_suppressElabErrors_2668_ = lean_ctor_get_uint8(v_a_2651_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2669_ = lean_ctor_get(v_a_2651_, 13);
lean_inc_ref(v_inheritedTraceOptions_2669_);
lean_dec_ref(v_a_2651_);
v___x_2670_ = lean_nat_dec_eq(v_currRecDepth_2657_, v_maxRecDepth_2658_);
if (v___x_2670_ == 0)
{
lean_object* v___x_2671_; uint8_t v___x_2672_; 
v___x_2671_ = lean_unsigned_to_nat(0u);
v___x_2672_ = lean_nat_dec_eq(v_numEqs_2645_, v___x_2671_);
if (v___x_2672_ == 0)
{
lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; 
v___x_2673_ = lean_unsigned_to_nat(1u);
v___x_2674_ = lean_nat_add(v_currRecDepth_2657_, v___x_2673_);
lean_dec(v_currRecDepth_2657_);
v___x_2675_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2675_, 0, v_fileName_2654_);
lean_ctor_set(v___x_2675_, 1, v_fileMap_2655_);
lean_ctor_set(v___x_2675_, 2, v_options_2656_);
lean_ctor_set(v___x_2675_, 3, v___x_2674_);
lean_ctor_set(v___x_2675_, 4, v_maxRecDepth_2658_);
lean_ctor_set(v___x_2675_, 5, v_ref_2659_);
lean_ctor_set(v___x_2675_, 6, v_currNamespace_2660_);
lean_ctor_set(v___x_2675_, 7, v_openDecls_2661_);
lean_ctor_set(v___x_2675_, 8, v_initHeartbeats_2662_);
lean_ctor_set(v___x_2675_, 9, v_maxHeartbeats_2663_);
lean_ctor_set(v___x_2675_, 10, v_quotContext_2664_);
lean_ctor_set(v___x_2675_, 11, v_currMacroScope_2665_);
lean_ctor_set(v___x_2675_, 12, v_cancelTk_x3f_2667_);
lean_ctor_set(v___x_2675_, 13, v_inheritedTraceOptions_2669_);
lean_ctor_set_uint8(v___x_2675_, sizeof(void*)*14, v_diag_2666_);
lean_ctor_set_uint8(v___x_2675_, sizeof(void*)*14 + 1, v_suppressElabErrors_2668_);
v___x_2676_ = l_Lean_Meta_intro1Core(v_mvarId_2646_, v___x_2670_, v_a_2649_, v_a_2650_, v___x_2675_, v_a_2652_);
if (lean_obj_tag(v___x_2676_) == 0)
{
lean_object* v_a_2677_; lean_object* v_fst_2678_; lean_object* v_snd_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; 
v_a_2677_ = lean_ctor_get(v___x_2676_, 0);
lean_inc(v_a_2677_);
lean_dec_ref(v___x_2676_);
v_fst_2678_ = lean_ctor_get(v_a_2677_, 0);
lean_inc(v_fst_2678_);
v_snd_2679_ = lean_ctor_get(v_a_2677_, 1);
lean_inc(v_snd_2679_);
lean_dec(v_a_2677_);
v___x_2680_ = ((lean_object*)(l_Lean_Meta_Cases_unifyEqs_x3f___closed__0));
lean_inc(v_caseName_x3f_2648_);
v___x_2681_ = l_Lean_Meta_unifyEq_x3f(v_snd_2679_, v_fst_2678_, v_subst_2647_, v___x_2680_, v_caseName_x3f_2648_, v_a_2649_, v_a_2650_, v___x_2675_, v_a_2652_);
if (lean_obj_tag(v___x_2681_) == 0)
{
lean_object* v_a_2682_; lean_object* v___x_2684_; uint8_t v_isShared_2685_; uint8_t v_isSharedCheck_2697_; 
v_a_2682_ = lean_ctor_get(v___x_2681_, 0);
v_isSharedCheck_2697_ = !lean_is_exclusive(v___x_2681_);
if (v_isSharedCheck_2697_ == 0)
{
v___x_2684_ = v___x_2681_;
v_isShared_2685_ = v_isSharedCheck_2697_;
goto v_resetjp_2683_;
}
else
{
lean_inc(v_a_2682_);
lean_dec(v___x_2681_);
v___x_2684_ = lean_box(0);
v_isShared_2685_ = v_isSharedCheck_2697_;
goto v_resetjp_2683_;
}
v_resetjp_2683_:
{
if (lean_obj_tag(v_a_2682_) == 1)
{
lean_object* v_val_2686_; lean_object* v_mvarId_2687_; lean_object* v_subst_2688_; lean_object* v_numNewEqs_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; 
lean_del_object(v___x_2684_);
v_val_2686_ = lean_ctor_get(v_a_2682_, 0);
lean_inc(v_val_2686_);
lean_dec_ref(v_a_2682_);
v_mvarId_2687_ = lean_ctor_get(v_val_2686_, 0);
lean_inc(v_mvarId_2687_);
v_subst_2688_ = lean_ctor_get(v_val_2686_, 1);
lean_inc(v_subst_2688_);
v_numNewEqs_2689_ = lean_ctor_get(v_val_2686_, 2);
lean_inc(v_numNewEqs_2689_);
lean_dec(v_val_2686_);
v___x_2690_ = lean_nat_sub(v_numEqs_2645_, v___x_2673_);
lean_dec(v_numEqs_2645_);
v___x_2691_ = lean_nat_add(v___x_2690_, v_numNewEqs_2689_);
lean_dec(v_numNewEqs_2689_);
lean_dec(v___x_2690_);
v_numEqs_2645_ = v___x_2691_;
v_mvarId_2646_ = v_mvarId_2687_;
v_subst_2647_ = v_subst_2688_;
v_a_2651_ = v___x_2675_;
goto _start;
}
else
{
lean_object* v___x_2693_; lean_object* v___x_2695_; 
lean_dec(v_a_2682_);
lean_dec_ref(v___x_2675_);
lean_dec(v_caseName_x3f_2648_);
lean_dec(v_numEqs_2645_);
v___x_2693_ = lean_box(0);
if (v_isShared_2685_ == 0)
{
lean_ctor_set(v___x_2684_, 0, v___x_2693_);
v___x_2695_ = v___x_2684_;
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
lean_object* v_a_2698_; lean_object* v___x_2700_; uint8_t v_isShared_2701_; uint8_t v_isSharedCheck_2705_; 
lean_dec_ref(v___x_2675_);
lean_dec(v_caseName_x3f_2648_);
lean_dec(v_numEqs_2645_);
v_a_2698_ = lean_ctor_get(v___x_2681_, 0);
v_isSharedCheck_2705_ = !lean_is_exclusive(v___x_2681_);
if (v_isSharedCheck_2705_ == 0)
{
v___x_2700_ = v___x_2681_;
v_isShared_2701_ = v_isSharedCheck_2705_;
goto v_resetjp_2699_;
}
else
{
lean_inc(v_a_2698_);
lean_dec(v___x_2681_);
v___x_2700_ = lean_box(0);
v_isShared_2701_ = v_isSharedCheck_2705_;
goto v_resetjp_2699_;
}
v_resetjp_2699_:
{
lean_object* v___x_2703_; 
if (v_isShared_2701_ == 0)
{
v___x_2703_ = v___x_2700_;
goto v_reusejp_2702_;
}
else
{
lean_object* v_reuseFailAlloc_2704_; 
v_reuseFailAlloc_2704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2704_, 0, v_a_2698_);
v___x_2703_ = v_reuseFailAlloc_2704_;
goto v_reusejp_2702_;
}
v_reusejp_2702_:
{
return v___x_2703_;
}
}
}
}
else
{
lean_object* v_a_2706_; lean_object* v___x_2708_; uint8_t v_isShared_2709_; uint8_t v_isSharedCheck_2713_; 
lean_dec_ref(v___x_2675_);
lean_dec(v_caseName_x3f_2648_);
lean_dec(v_subst_2647_);
lean_dec(v_numEqs_2645_);
v_a_2706_ = lean_ctor_get(v___x_2676_, 0);
v_isSharedCheck_2713_ = !lean_is_exclusive(v___x_2676_);
if (v_isSharedCheck_2713_ == 0)
{
v___x_2708_ = v___x_2676_;
v_isShared_2709_ = v_isSharedCheck_2713_;
goto v_resetjp_2707_;
}
else
{
lean_inc(v_a_2706_);
lean_dec(v___x_2676_);
v___x_2708_ = lean_box(0);
v_isShared_2709_ = v_isSharedCheck_2713_;
goto v_resetjp_2707_;
}
v_resetjp_2707_:
{
lean_object* v___x_2711_; 
if (v_isShared_2709_ == 0)
{
v___x_2711_ = v___x_2708_;
goto v_reusejp_2710_;
}
else
{
lean_object* v_reuseFailAlloc_2712_; 
v_reuseFailAlloc_2712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2712_, 0, v_a_2706_);
v___x_2711_ = v_reuseFailAlloc_2712_;
goto v_reusejp_2710_;
}
v_reusejp_2710_:
{
return v___x_2711_;
}
}
}
}
else
{
lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; 
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
lean_dec(v_caseName_x3f_2648_);
lean_dec(v_numEqs_2645_);
v___x_2714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2714_, 0, v_mvarId_2646_);
lean_ctor_set(v___x_2714_, 1, v_subst_2647_);
v___x_2715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2715_, 0, v___x_2714_);
v___x_2716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2716_, 0, v___x_2715_);
return v___x_2716_;
}
}
else
{
lean_object* v___x_2717_; 
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
lean_dec(v_caseName_x3f_2648_);
lean_dec(v_subst_2647_);
lean_dec(v_mvarId_2646_);
lean_dec(v_numEqs_2645_);
v___x_2717_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg(v_ref_2659_);
return v___x_2717_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_unifyEqs_x3f___boxed(lean_object* v_numEqs_2718_, lean_object* v_mvarId_2719_, lean_object* v_subst_2720_, lean_object* v_caseName_x3f_2721_, lean_object* v_a_2722_, lean_object* v_a_2723_, lean_object* v_a_2724_, lean_object* v_a_2725_, lean_object* v_a_2726_){
_start:
{
lean_object* v_res_2727_; 
v_res_2727_ = l_Lean_Meta_Cases_unifyEqs_x3f(v_numEqs_2718_, v_mvarId_2719_, v_subst_2720_, v_caseName_x3f_2721_, v_a_2722_, v_a_2723_, v_a_2724_, v_a_2725_);
lean_dec(v_a_2725_);
lean_dec(v_a_2723_);
lean_dec_ref(v_a_2722_);
return v_res_2727_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__0(lean_object* v_snd_2728_, size_t v_sz_2729_, size_t v_i_2730_, lean_object* v_bs_2731_){
_start:
{
uint8_t v___x_2732_; 
v___x_2732_ = lean_usize_dec_lt(v_i_2730_, v_sz_2729_);
if (v___x_2732_ == 0)
{
lean_dec(v_snd_2728_);
return v_bs_2731_;
}
else
{
lean_object* v_v_2733_; lean_object* v___x_2734_; lean_object* v_bs_x27_2735_; lean_object* v___x_2736_; size_t v___x_2737_; size_t v___x_2738_; lean_object* v___x_2739_; 
v_v_2733_ = lean_array_uget(v_bs_2731_, v_i_2730_);
v___x_2734_ = lean_unsigned_to_nat(0u);
v_bs_x27_2735_ = lean_array_uset(v_bs_2731_, v_i_2730_, v___x_2734_);
lean_inc(v_snd_2728_);
v___x_2736_ = l_Lean_Meta_FVarSubst_apply(v_snd_2728_, v_v_2733_);
lean_dec(v_v_2733_);
v___x_2737_ = ((size_t)1ULL);
v___x_2738_ = lean_usize_add(v_i_2730_, v___x_2737_);
v___x_2739_ = lean_array_uset(v_bs_x27_2735_, v_i_2730_, v___x_2736_);
v_i_2730_ = v___x_2738_;
v_bs_2731_ = v___x_2739_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__0___boxed(lean_object* v_snd_2741_, lean_object* v_sz_2742_, lean_object* v_i_2743_, lean_object* v_bs_2744_){
_start:
{
size_t v_sz_boxed_2745_; size_t v_i_boxed_2746_; lean_object* v_res_2747_; 
v_sz_boxed_2745_ = lean_unbox_usize(v_sz_2742_);
lean_dec(v_sz_2742_);
v_i_boxed_2746_ = lean_unbox_usize(v_i_2743_);
lean_dec(v_i_2743_);
v_res_2747_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__0(v_snd_2741_, v_sz_boxed_2745_, v_i_boxed_2746_, v_bs_2744_);
return v_res_2747_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1_spec__1(lean_object* v_numEqs_2748_, lean_object* v_as_2749_, size_t v_i_2750_, size_t v_stop_2751_, lean_object* v_b_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_){
_start:
{
uint8_t v___x_2758_; 
v___x_2758_ = lean_usize_dec_eq(v_i_2750_, v_stop_2751_);
if (v___x_2758_ == 0)
{
lean_object* v___x_2759_; lean_object* v_toInductionSubgoal_2760_; lean_object* v_ctorName_2761_; lean_object* v___x_2763_; uint8_t v_isShared_2764_; uint8_t v_isSharedCheck_2800_; 
v___x_2759_ = lean_array_uget(v_as_2749_, v_i_2750_);
v_toInductionSubgoal_2760_ = lean_ctor_get(v___x_2759_, 0);
v_ctorName_2761_ = lean_ctor_get(v___x_2759_, 1);
v_isSharedCheck_2800_ = !lean_is_exclusive(v___x_2759_);
if (v_isSharedCheck_2800_ == 0)
{
v___x_2763_ = v___x_2759_;
v_isShared_2764_ = v_isSharedCheck_2800_;
goto v_resetjp_2762_;
}
else
{
lean_inc(v_ctorName_2761_);
lean_inc(v_toInductionSubgoal_2760_);
lean_dec(v___x_2759_);
v___x_2763_ = lean_box(0);
v_isShared_2764_ = v_isSharedCheck_2800_;
goto v_resetjp_2762_;
}
v_resetjp_2762_:
{
lean_object* v_mvarId_2765_; lean_object* v_fields_2766_; lean_object* v_subst_2767_; lean_object* v___x_2769_; uint8_t v_isShared_2770_; uint8_t v_isSharedCheck_2799_; 
v_mvarId_2765_ = lean_ctor_get(v_toInductionSubgoal_2760_, 0);
v_fields_2766_ = lean_ctor_get(v_toInductionSubgoal_2760_, 1);
v_subst_2767_ = lean_ctor_get(v_toInductionSubgoal_2760_, 2);
v_isSharedCheck_2799_ = !lean_is_exclusive(v_toInductionSubgoal_2760_);
if (v_isSharedCheck_2799_ == 0)
{
v___x_2769_ = v_toInductionSubgoal_2760_;
v_isShared_2770_ = v_isSharedCheck_2799_;
goto v_resetjp_2768_;
}
else
{
lean_inc(v_subst_2767_);
lean_inc(v_fields_2766_);
lean_inc(v_mvarId_2765_);
lean_dec(v_toInductionSubgoal_2760_);
v___x_2769_ = lean_box(0);
v_isShared_2770_ = v_isSharedCheck_2799_;
goto v_resetjp_2768_;
}
v_resetjp_2768_:
{
lean_object* v___x_2771_; 
lean_inc_ref(v___y_2755_);
lean_inc(v_ctorName_2761_);
lean_inc(v_numEqs_2748_);
v___x_2771_ = l_Lean_Meta_Cases_unifyEqs_x3f(v_numEqs_2748_, v_mvarId_2765_, v_subst_2767_, v_ctorName_2761_, v___y_2753_, v___y_2754_, v___y_2755_, v___y_2756_);
if (lean_obj_tag(v___x_2771_) == 0)
{
lean_object* v_a_2772_; lean_object* v_a_2774_; 
v_a_2772_ = lean_ctor_get(v___x_2771_, 0);
lean_inc(v_a_2772_);
lean_dec_ref(v___x_2771_);
if (lean_obj_tag(v_a_2772_) == 0)
{
lean_del_object(v___x_2769_);
lean_dec_ref(v_fields_2766_);
lean_del_object(v___x_2763_);
lean_dec(v_ctorName_2761_);
v_a_2774_ = v_b_2752_;
goto v___jp_2773_;
}
else
{
lean_object* v_val_2778_; lean_object* v_fst_2779_; lean_object* v_snd_2780_; size_t v_sz_2781_; size_t v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2785_; 
v_val_2778_ = lean_ctor_get(v_a_2772_, 0);
lean_inc(v_val_2778_);
lean_dec_ref(v_a_2772_);
v_fst_2779_ = lean_ctor_get(v_val_2778_, 0);
lean_inc(v_fst_2779_);
v_snd_2780_ = lean_ctor_get(v_val_2778_, 1);
lean_inc(v_snd_2780_);
lean_dec(v_val_2778_);
v_sz_2781_ = lean_array_size(v_fields_2766_);
v___x_2782_ = ((size_t)0ULL);
lean_inc(v_snd_2780_);
v___x_2783_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__0(v_snd_2780_, v_sz_2781_, v___x_2782_, v_fields_2766_);
if (v_isShared_2770_ == 0)
{
lean_ctor_set(v___x_2769_, 2, v_snd_2780_);
lean_ctor_set(v___x_2769_, 1, v___x_2783_);
lean_ctor_set(v___x_2769_, 0, v_fst_2779_);
v___x_2785_ = v___x_2769_;
goto v_reusejp_2784_;
}
else
{
lean_object* v_reuseFailAlloc_2790_; 
v_reuseFailAlloc_2790_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2790_, 0, v_fst_2779_);
lean_ctor_set(v_reuseFailAlloc_2790_, 1, v___x_2783_);
lean_ctor_set(v_reuseFailAlloc_2790_, 2, v_snd_2780_);
v___x_2785_ = v_reuseFailAlloc_2790_;
goto v_reusejp_2784_;
}
v_reusejp_2784_:
{
lean_object* v___x_2787_; 
if (v_isShared_2764_ == 0)
{
lean_ctor_set(v___x_2763_, 0, v___x_2785_);
v___x_2787_ = v___x_2763_;
goto v_reusejp_2786_;
}
else
{
lean_object* v_reuseFailAlloc_2789_; 
v_reuseFailAlloc_2789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2789_, 0, v___x_2785_);
lean_ctor_set(v_reuseFailAlloc_2789_, 1, v_ctorName_2761_);
v___x_2787_ = v_reuseFailAlloc_2789_;
goto v_reusejp_2786_;
}
v_reusejp_2786_:
{
lean_object* v___x_2788_; 
v___x_2788_ = lean_array_push(v_b_2752_, v___x_2787_);
v_a_2774_ = v___x_2788_;
goto v___jp_2773_;
}
}
}
v___jp_2773_:
{
size_t v___x_2775_; size_t v___x_2776_; 
v___x_2775_ = ((size_t)1ULL);
v___x_2776_ = lean_usize_add(v_i_2750_, v___x_2775_);
v_i_2750_ = v___x_2776_;
v_b_2752_ = v_a_2774_;
goto _start;
}
}
else
{
lean_object* v_a_2791_; lean_object* v___x_2793_; uint8_t v_isShared_2794_; uint8_t v_isSharedCheck_2798_; 
lean_del_object(v___x_2769_);
lean_dec_ref(v_fields_2766_);
lean_del_object(v___x_2763_);
lean_dec(v_ctorName_2761_);
lean_dec_ref(v_b_2752_);
lean_dec(v_numEqs_2748_);
v_a_2791_ = lean_ctor_get(v___x_2771_, 0);
v_isSharedCheck_2798_ = !lean_is_exclusive(v___x_2771_);
if (v_isSharedCheck_2798_ == 0)
{
v___x_2793_ = v___x_2771_;
v_isShared_2794_ = v_isSharedCheck_2798_;
goto v_resetjp_2792_;
}
else
{
lean_inc(v_a_2791_);
lean_dec(v___x_2771_);
v___x_2793_ = lean_box(0);
v_isShared_2794_ = v_isSharedCheck_2798_;
goto v_resetjp_2792_;
}
v_resetjp_2792_:
{
lean_object* v___x_2796_; 
if (v_isShared_2794_ == 0)
{
v___x_2796_ = v___x_2793_;
goto v_reusejp_2795_;
}
else
{
lean_object* v_reuseFailAlloc_2797_; 
v_reuseFailAlloc_2797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2797_, 0, v_a_2791_);
v___x_2796_ = v_reuseFailAlloc_2797_;
goto v_reusejp_2795_;
}
v_reusejp_2795_:
{
return v___x_2796_;
}
}
}
}
}
}
else
{
lean_object* v___x_2801_; 
lean_dec(v_numEqs_2748_);
v___x_2801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2801_, 0, v_b_2752_);
return v___x_2801_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1_spec__1___boxed(lean_object* v_numEqs_2802_, lean_object* v_as_2803_, lean_object* v_i_2804_, lean_object* v_stop_2805_, lean_object* v_b_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_){
_start:
{
size_t v_i_boxed_2812_; size_t v_stop_boxed_2813_; lean_object* v_res_2814_; 
v_i_boxed_2812_ = lean_unbox_usize(v_i_2804_);
lean_dec(v_i_2804_);
v_stop_boxed_2813_ = lean_unbox_usize(v_stop_2805_);
lean_dec(v_stop_2805_);
v_res_2814_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1_spec__1(v_numEqs_2802_, v_as_2803_, v_i_boxed_2812_, v_stop_boxed_2813_, v_b_2806_, v___y_2807_, v___y_2808_, v___y_2809_, v___y_2810_);
lean_dec(v___y_2810_);
lean_dec_ref(v___y_2809_);
lean_dec(v___y_2808_);
lean_dec_ref(v___y_2807_);
lean_dec_ref(v_as_2803_);
return v_res_2814_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1(lean_object* v_numEqs_2817_, lean_object* v_as_2818_, lean_object* v_start_2819_, lean_object* v_stop_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_){
_start:
{
lean_object* v___x_2826_; uint8_t v___x_2827_; 
v___x_2826_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1___closed__0));
v___x_2827_ = lean_nat_dec_lt(v_start_2819_, v_stop_2820_);
if (v___x_2827_ == 0)
{
lean_object* v___x_2828_; 
lean_dec(v_numEqs_2817_);
v___x_2828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2828_, 0, v___x_2826_);
return v___x_2828_;
}
else
{
lean_object* v___x_2829_; uint8_t v___x_2830_; 
v___x_2829_ = lean_array_get_size(v_as_2818_);
v___x_2830_ = lean_nat_dec_le(v_stop_2820_, v___x_2829_);
if (v___x_2830_ == 0)
{
uint8_t v___x_2831_; 
v___x_2831_ = lean_nat_dec_lt(v_start_2819_, v___x_2829_);
if (v___x_2831_ == 0)
{
lean_object* v___x_2832_; 
lean_dec(v_numEqs_2817_);
v___x_2832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2832_, 0, v___x_2826_);
return v___x_2832_;
}
else
{
size_t v___x_2833_; size_t v___x_2834_; lean_object* v___x_2835_; 
v___x_2833_ = lean_usize_of_nat(v_start_2819_);
v___x_2834_ = lean_usize_of_nat(v___x_2829_);
v___x_2835_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1_spec__1(v_numEqs_2817_, v_as_2818_, v___x_2833_, v___x_2834_, v___x_2826_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_);
return v___x_2835_;
}
}
else
{
size_t v___x_2836_; size_t v___x_2837_; lean_object* v___x_2838_; 
v___x_2836_ = lean_usize_of_nat(v_start_2819_);
v___x_2837_ = lean_usize_of_nat(v_stop_2820_);
v___x_2838_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1_spec__1(v_numEqs_2817_, v_as_2818_, v___x_2836_, v___x_2837_, v___x_2826_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_);
return v___x_2838_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1___boxed(lean_object* v_numEqs_2839_, lean_object* v_as_2840_, lean_object* v_start_2841_, lean_object* v_stop_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_){
_start:
{
lean_object* v_res_2848_; 
v_res_2848_ = l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1(v_numEqs_2839_, v_as_2840_, v_start_2841_, v_stop_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_);
lean_dec(v___y_2846_);
lean_dec_ref(v___y_2845_);
lean_dec(v___y_2844_);
lean_dec_ref(v___y_2843_);
lean_dec(v_stop_2842_);
lean_dec(v_start_2841_);
lean_dec_ref(v_as_2840_);
return v_res_2848_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs(lean_object* v_numEqs_2849_, lean_object* v_subgoals_2850_, lean_object* v_a_2851_, lean_object* v_a_2852_, lean_object* v_a_2853_, lean_object* v_a_2854_){
_start:
{
lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; 
v___x_2856_ = lean_unsigned_to_nat(0u);
v___x_2857_ = lean_array_get_size(v_subgoals_2850_);
v___x_2858_ = l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1(v_numEqs_2849_, v_subgoals_2850_, v___x_2856_, v___x_2857_, v_a_2851_, v_a_2852_, v_a_2853_, v_a_2854_);
return v___x_2858_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs___boxed(lean_object* v_numEqs_2859_, lean_object* v_subgoals_2860_, lean_object* v_a_2861_, lean_object* v_a_2862_, lean_object* v_a_2863_, lean_object* v_a_2864_, lean_object* v_a_2865_){
_start:
{
lean_object* v_res_2866_; 
v_res_2866_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs(v_numEqs_2859_, v_subgoals_2860_, v_a_2861_, v_a_2862_, v_a_2863_, v_a_2864_);
lean_dec(v_a_2864_);
lean_dec_ref(v_a_2863_);
lean_dec(v_a_2862_);
lean_dec_ref(v_a_2861_);
lean_dec_ref(v_subgoals_2860_);
return v_res_2866_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0(lean_object* v___x_2878_, lean_object* v_mvarId_2879_, lean_object* v_majorFVarId_2880_, lean_object* v_givenNames_2881_, lean_object* v_ctx_2882_, uint8_t v_useNatCasesAuxOn_2883_, lean_object* v_interestingCtors_x3f_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_){
_start:
{
lean_object* v___x_2890_; 
lean_inc(v___y_2888_);
lean_inc_ref(v___y_2887_);
lean_inc(v___y_2886_);
lean_inc_ref(v___y_2885_);
v___x_2890_ = lean_infer_type(v___x_2878_, v___y_2885_, v___y_2886_, v___y_2887_, v___y_2888_);
if (lean_obj_tag(v___x_2890_) == 0)
{
lean_object* v_a_2891_; lean_object* v___x_2892_; 
v_a_2891_ = lean_ctor_get(v___x_2890_, 0);
lean_inc(v_a_2891_);
lean_dec_ref(v___x_2890_);
v___x_2892_ = l_Lean_Meta_getInductiveUniverseAndParams(v_a_2891_, v___y_2885_, v___y_2886_, v___y_2887_, v___y_2888_);
if (lean_obj_tag(v___x_2892_) == 0)
{
lean_object* v_a_2893_; lean_object* v_fst_2894_; lean_object* v_snd_2895_; lean_object* v___y_2897_; lean_object* v___y_2898_; lean_object* v___y_2899_; lean_object* v___y_2900_; lean_object* v___y_2901_; lean_object* v___y_2924_; lean_object* v___y_2925_; lean_object* v___y_2926_; lean_object* v___y_2927_; lean_object* v___y_2933_; lean_object* v___y_2934_; lean_object* v___y_2935_; lean_object* v___y_2936_; 
v_a_2893_ = lean_ctor_get(v___x_2892_, 0);
lean_inc(v_a_2893_);
lean_dec_ref(v___x_2892_);
v_fst_2894_ = lean_ctor_get(v_a_2893_, 0);
lean_inc(v_fst_2894_);
v_snd_2895_ = lean_ctor_get(v_a_2893_, 1);
lean_inc(v_snd_2895_);
lean_dec(v_a_2893_);
if (lean_obj_tag(v_interestingCtors_x3f_2884_) == 1)
{
lean_object* v_val_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v_inductiveVal_2949_; lean_object* v_toConstantVal_2950_; lean_object* v_env_2951_; lean_object* v_ctors_2952_; lean_object* v_name_2953_; uint8_t v___y_2955_; lean_object* v___x_2989_; uint8_t v___x_2990_; uint8_t v___x_2991_; 
v_val_2946_ = lean_ctor_get(v_interestingCtors_x3f_2884_, 0);
lean_inc(v_val_2946_);
lean_dec_ref(v_interestingCtors_x3f_2884_);
v___x_2947_ = lean_st_ref_get(v___y_2888_);
v___x_2948_ = lean_st_ref_get(v___y_2888_);
v_inductiveVal_2949_ = lean_ctor_get(v_ctx_2882_, 0);
v_toConstantVal_2950_ = lean_ctor_get(v_inductiveVal_2949_, 0);
v_env_2951_ = lean_ctor_get(v___x_2947_, 0);
lean_inc_ref(v_env_2951_);
lean_dec(v___x_2947_);
v_ctors_2952_ = lean_ctor_get(v_inductiveVal_2949_, 4);
v_name_2953_ = lean_ctor_get(v_toConstantVal_2950_, 0);
v___x_2989_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__5));
v___x_2990_ = 1;
v___x_2991_ = l_Lean_Environment_contains(v_env_2951_, v___x_2989_, v___x_2990_);
if (v___x_2991_ == 0)
{
lean_dec(v___x_2948_);
v___y_2955_ = v___x_2991_;
goto v___jp_2954_;
}
else
{
lean_object* v_env_2992_; lean_object* v___x_2993_; uint8_t v___x_2994_; 
v_env_2992_ = lean_ctor_get(v___x_2948_, 0);
lean_inc_ref(v_env_2992_);
lean_dec(v___x_2948_);
lean_inc(v_name_2953_);
v___x_2993_ = l_mkCtorIdxName(v_name_2953_);
v___x_2994_ = l_Lean_Environment_contains(v_env_2992_, v___x_2993_, v___x_2990_);
v___y_2955_ = v___x_2994_;
goto v___jp_2954_;
}
v___jp_2954_:
{
if (v___y_2955_ == 0)
{
lean_dec(v_val_2946_);
v___y_2933_ = v___y_2885_;
v___y_2934_ = v___y_2886_;
v___y_2935_ = v___y_2887_;
v___y_2936_ = v___y_2888_;
goto v___jp_2932_;
}
else
{
lean_object* v___x_2956_; lean_object* v___x_2957_; uint8_t v___x_2958_; 
v___x_2956_ = lean_array_get_size(v_val_2946_);
v___x_2957_ = lean_unsigned_to_nat(0u);
v___x_2958_ = lean_nat_dec_eq(v___x_2956_, v___x_2957_);
if (v___x_2958_ == 0)
{
lean_object* v___x_2959_; uint8_t v___x_2960_; 
v___x_2959_ = l_List_lengthTR___redArg(v_ctors_2952_);
v___x_2960_ = lean_nat_dec_lt(v___x_2956_, v___x_2959_);
lean_dec(v___x_2959_);
if (v___x_2960_ == 0)
{
lean_dec(v_val_2946_);
v___y_2933_ = v___y_2885_;
v___y_2934_ = v___y_2886_;
v___y_2935_ = v___y_2887_;
v___y_2936_ = v___y_2888_;
goto v___jp_2932_;
}
else
{
lean_object* v___x_2961_; 
lean_inc(v_name_2953_);
lean_dec_ref(v_ctx_2882_);
lean_inc(v_val_2946_);
v___x_2961_ = l_Lean_Meta_mkSparseCasesOn(v_name_2953_, v_val_2946_, v___y_2885_, v___y_2886_, v___y_2887_, v___y_2888_);
if (lean_obj_tag(v___x_2961_) == 0)
{
lean_object* v_a_2962_; lean_object* v___x_2963_; 
v_a_2962_ = lean_ctor_get(v___x_2961_, 0);
lean_inc(v_a_2962_);
lean_dec_ref(v___x_2961_);
lean_inc(v_majorFVarId_2880_);
v___x_2963_ = l_Lean_MVarId_induction(v_mvarId_2879_, v_majorFVarId_2880_, v_a_2962_, v_givenNames_2881_, v___y_2885_, v___y_2886_, v___y_2887_, v___y_2888_);
lean_dec(v___y_2888_);
lean_dec_ref(v___y_2887_);
lean_dec(v___y_2886_);
lean_dec_ref(v___y_2885_);
if (lean_obj_tag(v___x_2963_) == 0)
{
lean_object* v_a_2964_; lean_object* v___x_2966_; uint8_t v_isShared_2967_; uint8_t v_isSharedCheck_2972_; 
v_a_2964_ = lean_ctor_get(v___x_2963_, 0);
v_isSharedCheck_2972_ = !lean_is_exclusive(v___x_2963_);
if (v_isSharedCheck_2972_ == 0)
{
v___x_2966_ = v___x_2963_;
v_isShared_2967_ = v_isSharedCheck_2972_;
goto v_resetjp_2965_;
}
else
{
lean_inc(v_a_2964_);
lean_dec(v___x_2963_);
v___x_2966_ = lean_box(0);
v_isShared_2967_ = v_isSharedCheck_2972_;
goto v_resetjp_2965_;
}
v_resetjp_2965_:
{
lean_object* v___x_2968_; lean_object* v___x_2970_; 
v___x_2968_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals(v_a_2964_, v_val_2946_, v_majorFVarId_2880_, v_fst_2894_, v_snd_2895_);
lean_dec(v_snd_2895_);
lean_dec(v_val_2946_);
lean_dec(v_a_2964_);
if (v_isShared_2967_ == 0)
{
lean_ctor_set(v___x_2966_, 0, v___x_2968_);
v___x_2970_ = v___x_2966_;
goto v_reusejp_2969_;
}
else
{
lean_object* v_reuseFailAlloc_2971_; 
v_reuseFailAlloc_2971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2971_, 0, v___x_2968_);
v___x_2970_ = v_reuseFailAlloc_2971_;
goto v_reusejp_2969_;
}
v_reusejp_2969_:
{
return v___x_2970_;
}
}
}
else
{
lean_object* v_a_2973_; lean_object* v___x_2975_; uint8_t v_isShared_2976_; uint8_t v_isSharedCheck_2980_; 
lean_dec(v_val_2946_);
lean_dec(v_snd_2895_);
lean_dec(v_fst_2894_);
lean_dec(v_majorFVarId_2880_);
v_a_2973_ = lean_ctor_get(v___x_2963_, 0);
v_isSharedCheck_2980_ = !lean_is_exclusive(v___x_2963_);
if (v_isSharedCheck_2980_ == 0)
{
v___x_2975_ = v___x_2963_;
v_isShared_2976_ = v_isSharedCheck_2980_;
goto v_resetjp_2974_;
}
else
{
lean_inc(v_a_2973_);
lean_dec(v___x_2963_);
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
else
{
lean_object* v_a_2981_; lean_object* v___x_2983_; uint8_t v_isShared_2984_; uint8_t v_isSharedCheck_2988_; 
lean_dec(v_val_2946_);
lean_dec(v_snd_2895_);
lean_dec(v_fst_2894_);
lean_dec(v___y_2888_);
lean_dec_ref(v___y_2887_);
lean_dec(v___y_2886_);
lean_dec_ref(v___y_2885_);
lean_dec_ref(v_givenNames_2881_);
lean_dec(v_majorFVarId_2880_);
lean_dec(v_mvarId_2879_);
v_a_2981_ = lean_ctor_get(v___x_2961_, 0);
v_isSharedCheck_2988_ = !lean_is_exclusive(v___x_2961_);
if (v_isSharedCheck_2988_ == 0)
{
v___x_2983_ = v___x_2961_;
v_isShared_2984_ = v_isSharedCheck_2988_;
goto v_resetjp_2982_;
}
else
{
lean_inc(v_a_2981_);
lean_dec(v___x_2961_);
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
}
else
{
lean_dec(v_val_2946_);
v___y_2933_ = v___y_2885_;
v___y_2934_ = v___y_2886_;
v___y_2935_ = v___y_2887_;
v___y_2936_ = v___y_2888_;
goto v___jp_2932_;
}
}
}
}
else
{
lean_dec(v_interestingCtors_x3f_2884_);
v___y_2933_ = v___y_2885_;
v___y_2934_ = v___y_2886_;
v___y_2935_ = v___y_2887_;
v___y_2936_ = v___y_2888_;
goto v___jp_2932_;
}
v___jp_2896_:
{
lean_object* v___x_2902_; 
lean_inc(v_majorFVarId_2880_);
v___x_2902_ = l_Lean_MVarId_induction(v_mvarId_2879_, v_majorFVarId_2880_, v___y_2901_, v_givenNames_2881_, v___y_2897_, v___y_2898_, v___y_2900_, v___y_2899_);
lean_dec(v___y_2899_);
lean_dec_ref(v___y_2900_);
lean_dec(v___y_2898_);
lean_dec_ref(v___y_2897_);
if (lean_obj_tag(v___x_2902_) == 0)
{
lean_object* v_inductiveVal_2903_; lean_object* v_a_2904_; lean_object* v___x_2906_; uint8_t v_isShared_2907_; uint8_t v_isSharedCheck_2914_; 
v_inductiveVal_2903_ = lean_ctor_get(v_ctx_2882_, 0);
lean_inc_ref(v_inductiveVal_2903_);
lean_dec_ref(v_ctx_2882_);
v_a_2904_ = lean_ctor_get(v___x_2902_, 0);
v_isSharedCheck_2914_ = !lean_is_exclusive(v___x_2902_);
if (v_isSharedCheck_2914_ == 0)
{
v___x_2906_ = v___x_2902_;
v_isShared_2907_ = v_isSharedCheck_2914_;
goto v_resetjp_2905_;
}
else
{
lean_inc(v_a_2904_);
lean_dec(v___x_2902_);
v___x_2906_ = lean_box(0);
v_isShared_2907_ = v_isSharedCheck_2914_;
goto v_resetjp_2905_;
}
v_resetjp_2905_:
{
lean_object* v_ctors_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2912_; 
v_ctors_2908_ = lean_ctor_get(v_inductiveVal_2903_, 4);
lean_inc(v_ctors_2908_);
lean_dec_ref(v_inductiveVal_2903_);
v___x_2909_ = lean_array_mk(v_ctors_2908_);
v___x_2910_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals(v_a_2904_, v___x_2909_, v_majorFVarId_2880_, v_fst_2894_, v_snd_2895_);
lean_dec(v_snd_2895_);
lean_dec_ref(v___x_2909_);
lean_dec(v_a_2904_);
if (v_isShared_2907_ == 0)
{
lean_ctor_set(v___x_2906_, 0, v___x_2910_);
v___x_2912_ = v___x_2906_;
goto v_reusejp_2911_;
}
else
{
lean_object* v_reuseFailAlloc_2913_; 
v_reuseFailAlloc_2913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2913_, 0, v___x_2910_);
v___x_2912_ = v_reuseFailAlloc_2913_;
goto v_reusejp_2911_;
}
v_reusejp_2911_:
{
return v___x_2912_;
}
}
}
else
{
lean_object* v_a_2915_; lean_object* v___x_2917_; uint8_t v_isShared_2918_; uint8_t v_isSharedCheck_2922_; 
lean_dec(v_snd_2895_);
lean_dec(v_fst_2894_);
lean_dec_ref(v_ctx_2882_);
lean_dec(v_majorFVarId_2880_);
v_a_2915_ = lean_ctor_get(v___x_2902_, 0);
v_isSharedCheck_2922_ = !lean_is_exclusive(v___x_2902_);
if (v_isSharedCheck_2922_ == 0)
{
v___x_2917_ = v___x_2902_;
v_isShared_2918_ = v_isSharedCheck_2922_;
goto v_resetjp_2916_;
}
else
{
lean_inc(v_a_2915_);
lean_dec(v___x_2902_);
v___x_2917_ = lean_box(0);
v_isShared_2918_ = v_isSharedCheck_2922_;
goto v_resetjp_2916_;
}
v_resetjp_2916_:
{
lean_object* v___x_2920_; 
if (v_isShared_2918_ == 0)
{
v___x_2920_ = v___x_2917_;
goto v_reusejp_2919_;
}
else
{
lean_object* v_reuseFailAlloc_2921_; 
v_reuseFailAlloc_2921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2921_, 0, v_a_2915_);
v___x_2920_ = v_reuseFailAlloc_2921_;
goto v_reusejp_2919_;
}
v_reusejp_2919_:
{
return v___x_2920_;
}
}
}
}
v___jp_2923_:
{
lean_object* v_inductiveVal_2928_; lean_object* v_toConstantVal_2929_; lean_object* v_name_2930_; lean_object* v___x_2931_; 
v_inductiveVal_2928_ = lean_ctor_get(v_ctx_2882_, 0);
v_toConstantVal_2929_ = lean_ctor_get(v_inductiveVal_2928_, 0);
v_name_2930_ = lean_ctor_get(v_toConstantVal_2929_, 0);
lean_inc(v_name_2930_);
v___x_2931_ = l_Lean_mkCasesOnName(v_name_2930_);
v___y_2897_ = v___y_2924_;
v___y_2898_ = v___y_2925_;
v___y_2899_ = v___y_2926_;
v___y_2900_ = v___y_2927_;
v___y_2901_ = v___x_2931_;
goto v___jp_2896_;
}
v___jp_2932_:
{
lean_object* v___x_2937_; 
v___x_2937_ = lean_st_ref_get(v___y_2936_);
if (v_useNatCasesAuxOn_2883_ == 0)
{
lean_dec(v___x_2937_);
v___y_2924_ = v___y_2933_;
v___y_2925_ = v___y_2934_;
v___y_2926_ = v___y_2936_;
v___y_2927_ = v___y_2935_;
goto v___jp_2923_;
}
else
{
lean_object* v_inductiveVal_2938_; lean_object* v_toConstantVal_2939_; lean_object* v_env_2940_; lean_object* v_name_2941_; lean_object* v___x_2942_; uint8_t v___x_2943_; 
v_inductiveVal_2938_ = lean_ctor_get(v_ctx_2882_, 0);
v_toConstantVal_2939_ = lean_ctor_get(v_inductiveVal_2938_, 0);
v_env_2940_ = lean_ctor_get(v___x_2937_, 0);
lean_inc_ref(v_env_2940_);
lean_dec(v___x_2937_);
v_name_2941_ = lean_ctor_get(v_toConstantVal_2939_, 0);
v___x_2942_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__1));
v___x_2943_ = lean_name_eq(v_name_2941_, v___x_2942_);
if (v___x_2943_ == 0)
{
lean_dec_ref(v_env_2940_);
v___y_2924_ = v___y_2933_;
v___y_2925_ = v___y_2934_;
v___y_2926_ = v___y_2936_;
v___y_2927_ = v___y_2935_;
goto v___jp_2923_;
}
else
{
lean_object* v___x_2944_; uint8_t v___x_2945_; 
v___x_2944_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__3));
v___x_2945_ = l_Lean_Environment_contains(v_env_2940_, v___x_2944_, v___x_2943_);
if (v___x_2945_ == 0)
{
v___y_2924_ = v___y_2933_;
v___y_2925_ = v___y_2934_;
v___y_2926_ = v___y_2936_;
v___y_2927_ = v___y_2935_;
goto v___jp_2923_;
}
else
{
v___y_2897_ = v___y_2933_;
v___y_2898_ = v___y_2934_;
v___y_2899_ = v___y_2936_;
v___y_2900_ = v___y_2935_;
v___y_2901_ = v___x_2944_;
goto v___jp_2896_;
}
}
}
}
}
else
{
lean_object* v_a_2995_; lean_object* v___x_2997_; uint8_t v_isShared_2998_; uint8_t v_isSharedCheck_3002_; 
lean_dec(v___y_2888_);
lean_dec_ref(v___y_2887_);
lean_dec(v___y_2886_);
lean_dec_ref(v___y_2885_);
lean_dec(v_interestingCtors_x3f_2884_);
lean_dec_ref(v_ctx_2882_);
lean_dec_ref(v_givenNames_2881_);
lean_dec(v_majorFVarId_2880_);
lean_dec(v_mvarId_2879_);
v_a_2995_ = lean_ctor_get(v___x_2892_, 0);
v_isSharedCheck_3002_ = !lean_is_exclusive(v___x_2892_);
if (v_isSharedCheck_3002_ == 0)
{
v___x_2997_ = v___x_2892_;
v_isShared_2998_ = v_isSharedCheck_3002_;
goto v_resetjp_2996_;
}
else
{
lean_inc(v_a_2995_);
lean_dec(v___x_2892_);
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
else
{
lean_object* v_a_3003_; lean_object* v___x_3005_; uint8_t v_isShared_3006_; uint8_t v_isSharedCheck_3010_; 
lean_dec(v___y_2888_);
lean_dec_ref(v___y_2887_);
lean_dec(v___y_2886_);
lean_dec_ref(v___y_2885_);
lean_dec(v_interestingCtors_x3f_2884_);
lean_dec_ref(v_ctx_2882_);
lean_dec_ref(v_givenNames_2881_);
lean_dec(v_majorFVarId_2880_);
lean_dec(v_mvarId_2879_);
v_a_3003_ = lean_ctor_get(v___x_2890_, 0);
v_isSharedCheck_3010_ = !lean_is_exclusive(v___x_2890_);
if (v_isSharedCheck_3010_ == 0)
{
v___x_3005_ = v___x_2890_;
v_isShared_3006_ = v_isSharedCheck_3010_;
goto v_resetjp_3004_;
}
else
{
lean_inc(v_a_3003_);
lean_dec(v___x_2890_);
v___x_3005_ = lean_box(0);
v_isShared_3006_ = v_isSharedCheck_3010_;
goto v_resetjp_3004_;
}
v_resetjp_3004_:
{
lean_object* v___x_3008_; 
if (v_isShared_3006_ == 0)
{
v___x_3008_ = v___x_3005_;
goto v_reusejp_3007_;
}
else
{
lean_object* v_reuseFailAlloc_3009_; 
v_reuseFailAlloc_3009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3009_, 0, v_a_3003_);
v___x_3008_ = v_reuseFailAlloc_3009_;
goto v_reusejp_3007_;
}
v_reusejp_3007_:
{
return v___x_3008_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___boxed(lean_object* v___x_3011_, lean_object* v_mvarId_3012_, lean_object* v_majorFVarId_3013_, lean_object* v_givenNames_3014_, lean_object* v_ctx_3015_, lean_object* v_useNatCasesAuxOn_3016_, lean_object* v_interestingCtors_x3f_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_){
_start:
{
uint8_t v_useNatCasesAuxOn_boxed_3023_; lean_object* v_res_3024_; 
v_useNatCasesAuxOn_boxed_3023_ = lean_unbox(v_useNatCasesAuxOn_3016_);
v_res_3024_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0(v___x_3011_, v_mvarId_3012_, v_majorFVarId_3013_, v_givenNames_3014_, v_ctx_3015_, v_useNatCasesAuxOn_boxed_3023_, v_interestingCtors_x3f_3017_, v___y_3018_, v___y_3019_, v___y_3020_, v___y_3021_);
return v_res_3024_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn(lean_object* v_mvarId_3025_, lean_object* v_majorFVarId_3026_, lean_object* v_givenNames_3027_, lean_object* v_ctx_3028_, uint8_t v_useNatCasesAuxOn_3029_, lean_object* v_interestingCtors_x3f_3030_, lean_object* v_a_3031_, lean_object* v_a_3032_, lean_object* v_a_3033_, lean_object* v_a_3034_){
_start:
{
lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___f_3038_; lean_object* v___x_3039_; 
lean_inc(v_majorFVarId_3026_);
v___x_3036_ = l_Lean_mkFVar(v_majorFVarId_3026_);
v___x_3037_ = lean_box(v_useNatCasesAuxOn_3029_);
lean_inc(v_mvarId_3025_);
v___f_3038_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___boxed), 12, 7);
lean_closure_set(v___f_3038_, 0, v___x_3036_);
lean_closure_set(v___f_3038_, 1, v_mvarId_3025_);
lean_closure_set(v___f_3038_, 2, v_majorFVarId_3026_);
lean_closure_set(v___f_3038_, 3, v_givenNames_3027_);
lean_closure_set(v___f_3038_, 4, v_ctx_3028_);
lean_closure_set(v___f_3038_, 5, v___x_3037_);
lean_closure_set(v___f_3038_, 6, v_interestingCtors_x3f_3030_);
v___x_3039_ = l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2___redArg(v_mvarId_3025_, v___f_3038_, v_a_3031_, v_a_3032_, v_a_3033_, v_a_3034_);
return v___x_3039_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___boxed(lean_object* v_mvarId_3040_, lean_object* v_majorFVarId_3041_, lean_object* v_givenNames_3042_, lean_object* v_ctx_3043_, lean_object* v_useNatCasesAuxOn_3044_, lean_object* v_interestingCtors_x3f_3045_, lean_object* v_a_3046_, lean_object* v_a_3047_, lean_object* v_a_3048_, lean_object* v_a_3049_, lean_object* v_a_3050_){
_start:
{
uint8_t v_useNatCasesAuxOn_boxed_3051_; lean_object* v_res_3052_; 
v_useNatCasesAuxOn_boxed_3051_ = lean_unbox(v_useNatCasesAuxOn_3044_);
v_res_3052_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn(v_mvarId_3040_, v_majorFVarId_3041_, v_givenNames_3042_, v_ctx_3043_, v_useNatCasesAuxOn_boxed_3051_, v_interestingCtors_x3f_3045_, v_a_3046_, v_a_3047_, v_a_3048_, v_a_3049_);
lean_dec(v_a_3049_);
lean_dec_ref(v_a_3048_);
lean_dec(v_a_3047_);
lean_dec_ref(v_a_3046_);
return v_res_3052_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Cases_cases_spec__0___redArg(lean_object* v_cls_3056_, lean_object* v___y_3057_){
_start:
{
lean_object* v_options_3059_; uint8_t v_hasTrace_3060_; 
v_options_3059_ = lean_ctor_get(v___y_3057_, 2);
v_hasTrace_3060_ = lean_ctor_get_uint8(v_options_3059_, sizeof(void*)*1);
if (v_hasTrace_3060_ == 0)
{
lean_object* v___x_3061_; lean_object* v___x_3062_; 
lean_dec(v_cls_3056_);
v___x_3061_ = lean_box(v_hasTrace_3060_);
v___x_3062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3062_, 0, v___x_3061_);
return v___x_3062_;
}
else
{
lean_object* v_inheritedTraceOptions_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; uint8_t v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; 
v_inheritedTraceOptions_3063_ = lean_ctor_get(v___y_3057_, 13);
v___x_3064_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Meta_Cases_cases_spec__0___redArg___closed__1));
v___x_3065_ = l_Lean_Name_append(v___x_3064_, v_cls_3056_);
v___x_3066_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3063_, v_options_3059_, v___x_3065_);
lean_dec(v___x_3065_);
v___x_3067_ = lean_box(v___x_3066_);
v___x_3068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3068_, 0, v___x_3067_);
return v___x_3068_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Cases_cases_spec__0___redArg___boxed(lean_object* v_cls_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_){
_start:
{
lean_object* v_res_3072_; 
v_res_3072_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Cases_cases_spec__0___redArg(v_cls_3069_, v___y_3070_);
lean_dec_ref(v___y_3070_);
return v_res_3072_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Cases_cases_spec__0(lean_object* v_cls_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_){
_start:
{
lean_object* v___x_3079_; 
v___x_3079_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Cases_cases_spec__0___redArg(v_cls_3073_, v___y_3076_);
return v___x_3079_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Cases_cases_spec__0___boxed(lean_object* v_cls_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_){
_start:
{
lean_object* v_res_3086_; 
v_res_3086_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Cases_cases_spec__0(v_cls_3080_, v___y_3081_, v___y_3082_, v___y_3083_, v___y_3084_);
lean_dec(v___y_3084_);
lean_dec_ref(v___y_3083_);
lean_dec(v___y_3082_);
lean_dec_ref(v___y_3081_);
return v_res_3086_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__1___closed__0(void){
_start:
{
lean_object* v___x_3087_; double v___x_3088_; 
v___x_3087_ = lean_unsigned_to_nat(0u);
v___x_3088_ = lean_float_of_nat(v___x_3087_);
return v___x_3088_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__1(lean_object* v_cls_3092_, lean_object* v_msg_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_){
_start:
{
lean_object* v_ref_3099_; lean_object* v___x_3100_; lean_object* v_a_3101_; lean_object* v___x_3103_; uint8_t v_isShared_3104_; uint8_t v_isSharedCheck_3145_; 
v_ref_3099_ = lean_ctor_get(v___y_3096_, 5);
v___x_3100_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected_spec__0_spec__0(v_msg_3093_, v___y_3094_, v___y_3095_, v___y_3096_, v___y_3097_);
v_a_3101_ = lean_ctor_get(v___x_3100_, 0);
v_isSharedCheck_3145_ = !lean_is_exclusive(v___x_3100_);
if (v_isSharedCheck_3145_ == 0)
{
v___x_3103_ = v___x_3100_;
v_isShared_3104_ = v_isSharedCheck_3145_;
goto v_resetjp_3102_;
}
else
{
lean_inc(v_a_3101_);
lean_dec(v___x_3100_);
v___x_3103_ = lean_box(0);
v_isShared_3104_ = v_isSharedCheck_3145_;
goto v_resetjp_3102_;
}
v_resetjp_3102_:
{
lean_object* v___x_3105_; lean_object* v_traceState_3106_; lean_object* v_env_3107_; lean_object* v_nextMacroScope_3108_; lean_object* v_ngen_3109_; lean_object* v_auxDeclNGen_3110_; lean_object* v_cache_3111_; lean_object* v_messages_3112_; lean_object* v_infoState_3113_; lean_object* v_snapshotTasks_3114_; lean_object* v___x_3116_; uint8_t v_isShared_3117_; uint8_t v_isSharedCheck_3144_; 
v___x_3105_ = lean_st_ref_take(v___y_3097_);
v_traceState_3106_ = lean_ctor_get(v___x_3105_, 4);
v_env_3107_ = lean_ctor_get(v___x_3105_, 0);
v_nextMacroScope_3108_ = lean_ctor_get(v___x_3105_, 1);
v_ngen_3109_ = lean_ctor_get(v___x_3105_, 2);
v_auxDeclNGen_3110_ = lean_ctor_get(v___x_3105_, 3);
v_cache_3111_ = lean_ctor_get(v___x_3105_, 5);
v_messages_3112_ = lean_ctor_get(v___x_3105_, 6);
v_infoState_3113_ = lean_ctor_get(v___x_3105_, 7);
v_snapshotTasks_3114_ = lean_ctor_get(v___x_3105_, 8);
v_isSharedCheck_3144_ = !lean_is_exclusive(v___x_3105_);
if (v_isSharedCheck_3144_ == 0)
{
v___x_3116_ = v___x_3105_;
v_isShared_3117_ = v_isSharedCheck_3144_;
goto v_resetjp_3115_;
}
else
{
lean_inc(v_snapshotTasks_3114_);
lean_inc(v_infoState_3113_);
lean_inc(v_messages_3112_);
lean_inc(v_cache_3111_);
lean_inc(v_traceState_3106_);
lean_inc(v_auxDeclNGen_3110_);
lean_inc(v_ngen_3109_);
lean_inc(v_nextMacroScope_3108_);
lean_inc(v_env_3107_);
lean_dec(v___x_3105_);
v___x_3116_ = lean_box(0);
v_isShared_3117_ = v_isSharedCheck_3144_;
goto v_resetjp_3115_;
}
v_resetjp_3115_:
{
uint64_t v_tid_3118_; lean_object* v_traces_3119_; lean_object* v___x_3121_; uint8_t v_isShared_3122_; uint8_t v_isSharedCheck_3143_; 
v_tid_3118_ = lean_ctor_get_uint64(v_traceState_3106_, sizeof(void*)*1);
v_traces_3119_ = lean_ctor_get(v_traceState_3106_, 0);
v_isSharedCheck_3143_ = !lean_is_exclusive(v_traceState_3106_);
if (v_isSharedCheck_3143_ == 0)
{
v___x_3121_ = v_traceState_3106_;
v_isShared_3122_ = v_isSharedCheck_3143_;
goto v_resetjp_3120_;
}
else
{
lean_inc(v_traces_3119_);
lean_dec(v_traceState_3106_);
v___x_3121_ = lean_box(0);
v_isShared_3122_ = v_isSharedCheck_3143_;
goto v_resetjp_3120_;
}
v_resetjp_3120_:
{
lean_object* v___x_3123_; double v___x_3124_; uint8_t v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3133_; 
v___x_3123_ = lean_box(0);
v___x_3124_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__1___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__1___closed__0);
v___x_3125_ = 0;
v___x_3126_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__1___closed__1));
v___x_3127_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3127_, 0, v_cls_3092_);
lean_ctor_set(v___x_3127_, 1, v___x_3123_);
lean_ctor_set(v___x_3127_, 2, v___x_3126_);
lean_ctor_set_float(v___x_3127_, sizeof(void*)*3, v___x_3124_);
lean_ctor_set_float(v___x_3127_, sizeof(void*)*3 + 8, v___x_3124_);
lean_ctor_set_uint8(v___x_3127_, sizeof(void*)*3 + 16, v___x_3125_);
v___x_3128_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__1___closed__2));
v___x_3129_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3129_, 0, v___x_3127_);
lean_ctor_set(v___x_3129_, 1, v_a_3101_);
lean_ctor_set(v___x_3129_, 2, v___x_3128_);
lean_inc(v_ref_3099_);
v___x_3130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3130_, 0, v_ref_3099_);
lean_ctor_set(v___x_3130_, 1, v___x_3129_);
v___x_3131_ = l_Lean_PersistentArray_push___redArg(v_traces_3119_, v___x_3130_);
if (v_isShared_3122_ == 0)
{
lean_ctor_set(v___x_3121_, 0, v___x_3131_);
v___x_3133_ = v___x_3121_;
goto v_reusejp_3132_;
}
else
{
lean_object* v_reuseFailAlloc_3142_; 
v_reuseFailAlloc_3142_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3142_, 0, v___x_3131_);
lean_ctor_set_uint64(v_reuseFailAlloc_3142_, sizeof(void*)*1, v_tid_3118_);
v___x_3133_ = v_reuseFailAlloc_3142_;
goto v_reusejp_3132_;
}
v_reusejp_3132_:
{
lean_object* v___x_3135_; 
if (v_isShared_3117_ == 0)
{
lean_ctor_set(v___x_3116_, 4, v___x_3133_);
v___x_3135_ = v___x_3116_;
goto v_reusejp_3134_;
}
else
{
lean_object* v_reuseFailAlloc_3141_; 
v_reuseFailAlloc_3141_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3141_, 0, v_env_3107_);
lean_ctor_set(v_reuseFailAlloc_3141_, 1, v_nextMacroScope_3108_);
lean_ctor_set(v_reuseFailAlloc_3141_, 2, v_ngen_3109_);
lean_ctor_set(v_reuseFailAlloc_3141_, 3, v_auxDeclNGen_3110_);
lean_ctor_set(v_reuseFailAlloc_3141_, 4, v___x_3133_);
lean_ctor_set(v_reuseFailAlloc_3141_, 5, v_cache_3111_);
lean_ctor_set(v_reuseFailAlloc_3141_, 6, v_messages_3112_);
lean_ctor_set(v_reuseFailAlloc_3141_, 7, v_infoState_3113_);
lean_ctor_set(v_reuseFailAlloc_3141_, 8, v_snapshotTasks_3114_);
v___x_3135_ = v_reuseFailAlloc_3141_;
goto v_reusejp_3134_;
}
v_reusejp_3134_:
{
lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3139_; 
v___x_3136_ = lean_st_ref_set(v___y_3097_, v___x_3135_);
v___x_3137_ = lean_box(0);
if (v_isShared_3104_ == 0)
{
lean_ctor_set(v___x_3103_, 0, v___x_3137_);
v___x_3139_ = v___x_3103_;
goto v_reusejp_3138_;
}
else
{
lean_object* v_reuseFailAlloc_3140_; 
v_reuseFailAlloc_3140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3140_, 0, v___x_3137_);
v___x_3139_ = v_reuseFailAlloc_3140_;
goto v_reusejp_3138_;
}
v_reusejp_3138_:
{
return v___x_3139_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__1___boxed(lean_object* v_cls_3146_, lean_object* v_msg_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_){
_start:
{
lean_object* v_res_3153_; 
v_res_3153_ = l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__1(v_cls_3146_, v_msg_3147_, v___y_3148_, v___y_3149_, v___y_3150_, v___y_3151_);
lean_dec(v___y_3151_);
lean_dec_ref(v___y_3150_);
lean_dec(v___y_3149_);
lean_dec_ref(v___y_3148_);
return v_res_3153_;
}
}
static lean_object* _init_l_Lean_Meta_Cases_cases___lam__0___closed__2(void){
_start:
{
lean_object* v___x_3157_; lean_object* v___x_3158_; 
v___x_3157_ = ((lean_object*)(l_Lean_Meta_Cases_cases___lam__0___closed__1));
v___x_3158_ = l_Lean_MessageData_ofFormat(v___x_3157_);
return v___x_3158_;
}
}
static lean_object* _init_l_Lean_Meta_Cases_cases___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3159_; lean_object* v___x_3160_; 
v___x_3159_ = lean_obj_once(&l_Lean_Meta_Cases_cases___lam__0___closed__2, &l_Lean_Meta_Cases_cases___lam__0___closed__2_once, _init_l_Lean_Meta_Cases_cases___lam__0___closed__2);
v___x_3160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3160_, 0, v___x_3159_);
return v___x_3160_;
}
}
static lean_object* _init_l_Lean_Meta_Cases_cases___lam__0___closed__7(void){
_start:
{
lean_object* v___x_3164_; lean_object* v___x_3165_; 
v___x_3164_ = ((lean_object*)(l_Lean_Meta_Cases_cases___lam__0___closed__6));
v___x_3165_ = l_Lean_stringToMessageData(v___x_3164_);
return v___x_3165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_cases___lam__0(lean_object* v_mvarId_3166_, lean_object* v___x_3167_, lean_object* v_majorFVarId_3168_, lean_object* v___x_3169_, lean_object* v_givenNames_3170_, lean_object* v_interestingCtors_x3f_3171_, uint8_t v_useNatCasesAuxOn_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_){
_start:
{
lean_object* v___x_3178_; 
lean_inc(v___x_3167_);
lean_inc(v_mvarId_3166_);
v___x_3178_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_3166_, v___x_3167_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_);
if (lean_obj_tag(v___x_3178_) == 0)
{
lean_object* v___x_3179_; 
lean_dec_ref(v___x_3178_);
lean_inc(v_majorFVarId_3168_);
v___x_3179_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f(v_majorFVarId_3168_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_);
if (lean_obj_tag(v___x_3179_) == 0)
{
lean_object* v_a_3180_; 
v_a_3180_ = lean_ctor_get(v___x_3179_, 0);
lean_inc(v_a_3180_);
lean_dec_ref(v___x_3179_);
if (lean_obj_tag(v_a_3180_) == 0)
{
lean_object* v___x_3181_; lean_object* v___x_3182_; 
lean_dec(v_interestingCtors_x3f_3171_);
lean_dec_ref(v_givenNames_3170_);
lean_dec_ref(v___x_3169_);
lean_dec(v_majorFVarId_3168_);
v___x_3181_ = lean_obj_once(&l_Lean_Meta_Cases_cases___lam__0___closed__3, &l_Lean_Meta_Cases_cases___lam__0___closed__3_once, _init_l_Lean_Meta_Cases_cases___lam__0___closed__3);
v___x_3182_ = l_Lean_Meta_throwTacticEx___redArg(v___x_3167_, v_mvarId_3166_, v___x_3181_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_);
lean_dec_ref(v___y_3173_);
return v___x_3182_;
}
else
{
lean_object* v_val_3183_; lean_object* v___x_3184_; 
lean_dec(v___x_3167_);
v_val_3183_ = lean_ctor_get(v_a_3180_, 0);
lean_inc(v_val_3183_);
lean_dec_ref(v_a_3180_);
lean_inc_ref(v___y_3173_);
lean_inc(v_val_3183_);
v___x_3184_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices(v_val_3183_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_);
if (lean_obj_tag(v___x_3184_) == 0)
{
lean_object* v_a_3185_; uint8_t v___x_3186_; 
v_a_3185_ = lean_ctor_get(v___x_3184_, 0);
lean_inc(v_a_3185_);
lean_dec_ref(v___x_3184_);
v___x_3186_ = lean_unbox(v_a_3185_);
if (v___x_3186_ == 0)
{
lean_object* v___x_3187_; 
v___x_3187_ = l_Lean_Meta_generalizeIndices(v_mvarId_3166_, v_majorFVarId_3168_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_);
if (lean_obj_tag(v___x_3187_) == 0)
{
lean_object* v_a_3188_; lean_object* v___y_3190_; lean_object* v___y_3191_; lean_object* v___y_3192_; lean_object* v___y_3193_; lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v_a_3207_; lean_object* v___x_3209_; uint8_t v_isShared_3210_; uint8_t v_isSharedCheck_3227_; 
v_a_3188_ = lean_ctor_get(v___x_3187_, 0);
lean_inc(v_a_3188_);
lean_dec_ref(v___x_3187_);
v___x_3203_ = ((lean_object*)(l_Lean_Meta_Cases_cases___lam__0___closed__4));
v___x_3204_ = ((lean_object*)(l_Lean_Meta_Cases_cases___lam__0___closed__5));
v___x_3205_ = l_Lean_Name_mkStr3(v___x_3203_, v___x_3204_, v___x_3169_);
lean_inc(v___x_3205_);
v___x_3206_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Cases_cases_spec__0___redArg(v___x_3205_, v___y_3175_);
v_a_3207_ = lean_ctor_get(v___x_3206_, 0);
v_isSharedCheck_3227_ = !lean_is_exclusive(v___x_3206_);
if (v_isSharedCheck_3227_ == 0)
{
v___x_3209_ = v___x_3206_;
v_isShared_3210_ = v_isSharedCheck_3227_;
goto v_resetjp_3208_;
}
else
{
lean_inc(v_a_3207_);
lean_dec(v___x_3206_);
v___x_3209_ = lean_box(0);
v_isShared_3210_ = v_isSharedCheck_3227_;
goto v_resetjp_3208_;
}
v___jp_3189_:
{
lean_object* v_mvarId_3194_; lean_object* v_fvarId_3195_; lean_object* v_numEqs_3196_; uint8_t v___x_3197_; lean_object* v___x_3198_; 
v_mvarId_3194_ = lean_ctor_get(v_a_3188_, 0);
v_fvarId_3195_ = lean_ctor_get(v_a_3188_, 2);
v_numEqs_3196_ = lean_ctor_get(v_a_3188_, 3);
lean_inc(v_numEqs_3196_);
v___x_3197_ = lean_unbox(v_a_3185_);
lean_dec(v_a_3185_);
lean_inc(v_fvarId_3195_);
lean_inc(v_mvarId_3194_);
v___x_3198_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn(v_mvarId_3194_, v_fvarId_3195_, v_givenNames_3170_, v_val_3183_, v___x_3197_, v_interestingCtors_x3f_3171_, v___y_3190_, v___y_3191_, v___y_3192_, v___y_3193_);
if (lean_obj_tag(v___x_3198_) == 0)
{
lean_object* v_a_3199_; lean_object* v___x_3200_; 
v_a_3199_ = lean_ctor_get(v___x_3198_, 0);
lean_inc(v_a_3199_);
lean_dec_ref(v___x_3198_);
v___x_3200_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices(v_a_3188_, v_a_3199_, v___y_3190_, v___y_3191_, v___y_3192_, v___y_3193_);
lean_dec(v_a_3188_);
if (lean_obj_tag(v___x_3200_) == 0)
{
lean_object* v_a_3201_; lean_object* v___x_3202_; 
v_a_3201_ = lean_ctor_get(v___x_3200_, 0);
lean_inc(v_a_3201_);
lean_dec_ref(v___x_3200_);
v___x_3202_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs(v_numEqs_3196_, v_a_3201_, v___y_3190_, v___y_3191_, v___y_3192_, v___y_3193_);
lean_dec_ref(v___y_3190_);
lean_dec(v_a_3201_);
return v___x_3202_;
}
else
{
lean_dec(v_numEqs_3196_);
lean_dec_ref(v___y_3190_);
return v___x_3200_;
}
}
else
{
lean_dec(v_numEqs_3196_);
lean_dec_ref(v___y_3190_);
lean_dec(v_a_3188_);
return v___x_3198_;
}
}
v_resetjp_3208_:
{
uint8_t v___x_3211_; 
v___x_3211_ = lean_unbox(v_a_3207_);
lean_dec(v_a_3207_);
if (v___x_3211_ == 0)
{
lean_del_object(v___x_3209_);
lean_dec(v___x_3205_);
v___y_3190_ = v___y_3173_;
v___y_3191_ = v___y_3174_;
v___y_3192_ = v___y_3175_;
v___y_3193_ = v___y_3176_;
goto v___jp_3189_;
}
else
{
lean_object* v_mvarId_3212_; lean_object* v___x_3213_; lean_object* v___x_3215_; 
v_mvarId_3212_ = lean_ctor_get(v_a_3188_, 0);
v___x_3213_ = lean_obj_once(&l_Lean_Meta_Cases_cases___lam__0___closed__7, &l_Lean_Meta_Cases_cases___lam__0___closed__7_once, _init_l_Lean_Meta_Cases_cases___lam__0___closed__7);
lean_inc(v_mvarId_3212_);
if (v_isShared_3210_ == 0)
{
lean_ctor_set_tag(v___x_3209_, 1);
lean_ctor_set(v___x_3209_, 0, v_mvarId_3212_);
v___x_3215_ = v___x_3209_;
goto v_reusejp_3214_;
}
else
{
lean_object* v_reuseFailAlloc_3226_; 
v_reuseFailAlloc_3226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3226_, 0, v_mvarId_3212_);
v___x_3215_ = v_reuseFailAlloc_3226_;
goto v_reusejp_3214_;
}
v_reusejp_3214_:
{
lean_object* v___x_3216_; lean_object* v___x_3217_; 
v___x_3216_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3216_, 0, v___x_3213_);
lean_ctor_set(v___x_3216_, 1, v___x_3215_);
v___x_3217_ = l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__1(v___x_3205_, v___x_3216_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_);
if (lean_obj_tag(v___x_3217_) == 0)
{
lean_dec_ref(v___x_3217_);
v___y_3190_ = v___y_3173_;
v___y_3191_ = v___y_3174_;
v___y_3192_ = v___y_3175_;
v___y_3193_ = v___y_3176_;
goto v___jp_3189_;
}
else
{
lean_object* v_a_3218_; lean_object* v___x_3220_; uint8_t v_isShared_3221_; uint8_t v_isSharedCheck_3225_; 
lean_dec(v_a_3188_);
lean_dec(v_a_3185_);
lean_dec(v_val_3183_);
lean_dec_ref(v___y_3173_);
lean_dec(v_interestingCtors_x3f_3171_);
lean_dec_ref(v_givenNames_3170_);
v_a_3218_ = lean_ctor_get(v___x_3217_, 0);
v_isSharedCheck_3225_ = !lean_is_exclusive(v___x_3217_);
if (v_isSharedCheck_3225_ == 0)
{
v___x_3220_ = v___x_3217_;
v_isShared_3221_ = v_isSharedCheck_3225_;
goto v_resetjp_3219_;
}
else
{
lean_inc(v_a_3218_);
lean_dec(v___x_3217_);
v___x_3220_ = lean_box(0);
v_isShared_3221_ = v_isSharedCheck_3225_;
goto v_resetjp_3219_;
}
v_resetjp_3219_:
{
lean_object* v___x_3223_; 
if (v_isShared_3221_ == 0)
{
v___x_3223_ = v___x_3220_;
goto v_reusejp_3222_;
}
else
{
lean_object* v_reuseFailAlloc_3224_; 
v_reuseFailAlloc_3224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3224_, 0, v_a_3218_);
v___x_3223_ = v_reuseFailAlloc_3224_;
goto v_reusejp_3222_;
}
v_reusejp_3222_:
{
return v___x_3223_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3228_; lean_object* v___x_3230_; uint8_t v_isShared_3231_; uint8_t v_isSharedCheck_3235_; 
lean_dec(v_a_3185_);
lean_dec(v_val_3183_);
lean_dec_ref(v___y_3173_);
lean_dec(v_interestingCtors_x3f_3171_);
lean_dec_ref(v_givenNames_3170_);
lean_dec_ref(v___x_3169_);
v_a_3228_ = lean_ctor_get(v___x_3187_, 0);
v_isSharedCheck_3235_ = !lean_is_exclusive(v___x_3187_);
if (v_isSharedCheck_3235_ == 0)
{
v___x_3230_ = v___x_3187_;
v_isShared_3231_ = v_isSharedCheck_3235_;
goto v_resetjp_3229_;
}
else
{
lean_inc(v_a_3228_);
lean_dec(v___x_3187_);
v___x_3230_ = lean_box(0);
v_isShared_3231_ = v_isSharedCheck_3235_;
goto v_resetjp_3229_;
}
v_resetjp_3229_:
{
lean_object* v___x_3233_; 
if (v_isShared_3231_ == 0)
{
v___x_3233_ = v___x_3230_;
goto v_reusejp_3232_;
}
else
{
lean_object* v_reuseFailAlloc_3234_; 
v_reuseFailAlloc_3234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3234_, 0, v_a_3228_);
v___x_3233_ = v_reuseFailAlloc_3234_;
goto v_reusejp_3232_;
}
v_reusejp_3232_:
{
return v___x_3233_;
}
}
}
}
else
{
lean_object* v___x_3236_; 
lean_dec(v_a_3185_);
lean_dec_ref(v___x_3169_);
v___x_3236_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn(v_mvarId_3166_, v_majorFVarId_3168_, v_givenNames_3170_, v_val_3183_, v_useNatCasesAuxOn_3172_, v_interestingCtors_x3f_3171_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_);
lean_dec_ref(v___y_3173_);
return v___x_3236_;
}
}
else
{
lean_object* v_a_3237_; lean_object* v___x_3239_; uint8_t v_isShared_3240_; uint8_t v_isSharedCheck_3244_; 
lean_dec(v_val_3183_);
lean_dec_ref(v___y_3173_);
lean_dec(v_interestingCtors_x3f_3171_);
lean_dec_ref(v_givenNames_3170_);
lean_dec_ref(v___x_3169_);
lean_dec(v_majorFVarId_3168_);
lean_dec(v_mvarId_3166_);
v_a_3237_ = lean_ctor_get(v___x_3184_, 0);
v_isSharedCheck_3244_ = !lean_is_exclusive(v___x_3184_);
if (v_isSharedCheck_3244_ == 0)
{
v___x_3239_ = v___x_3184_;
v_isShared_3240_ = v_isSharedCheck_3244_;
goto v_resetjp_3238_;
}
else
{
lean_inc(v_a_3237_);
lean_dec(v___x_3184_);
v___x_3239_ = lean_box(0);
v_isShared_3240_ = v_isSharedCheck_3244_;
goto v_resetjp_3238_;
}
v_resetjp_3238_:
{
lean_object* v___x_3242_; 
if (v_isShared_3240_ == 0)
{
v___x_3242_ = v___x_3239_;
goto v_reusejp_3241_;
}
else
{
lean_object* v_reuseFailAlloc_3243_; 
v_reuseFailAlloc_3243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3243_, 0, v_a_3237_);
v___x_3242_ = v_reuseFailAlloc_3243_;
goto v_reusejp_3241_;
}
v_reusejp_3241_:
{
return v___x_3242_;
}
}
}
}
}
else
{
lean_object* v_a_3245_; lean_object* v___x_3247_; uint8_t v_isShared_3248_; uint8_t v_isSharedCheck_3252_; 
lean_dec_ref(v___y_3173_);
lean_dec(v_interestingCtors_x3f_3171_);
lean_dec_ref(v_givenNames_3170_);
lean_dec_ref(v___x_3169_);
lean_dec(v_majorFVarId_3168_);
lean_dec(v___x_3167_);
lean_dec(v_mvarId_3166_);
v_a_3245_ = lean_ctor_get(v___x_3179_, 0);
v_isSharedCheck_3252_ = !lean_is_exclusive(v___x_3179_);
if (v_isSharedCheck_3252_ == 0)
{
v___x_3247_ = v___x_3179_;
v_isShared_3248_ = v_isSharedCheck_3252_;
goto v_resetjp_3246_;
}
else
{
lean_inc(v_a_3245_);
lean_dec(v___x_3179_);
v___x_3247_ = lean_box(0);
v_isShared_3248_ = v_isSharedCheck_3252_;
goto v_resetjp_3246_;
}
v_resetjp_3246_:
{
lean_object* v___x_3250_; 
if (v_isShared_3248_ == 0)
{
v___x_3250_ = v___x_3247_;
goto v_reusejp_3249_;
}
else
{
lean_object* v_reuseFailAlloc_3251_; 
v_reuseFailAlloc_3251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3251_, 0, v_a_3245_);
v___x_3250_ = v_reuseFailAlloc_3251_;
goto v_reusejp_3249_;
}
v_reusejp_3249_:
{
return v___x_3250_;
}
}
}
}
else
{
lean_object* v_a_3253_; lean_object* v___x_3255_; uint8_t v_isShared_3256_; uint8_t v_isSharedCheck_3260_; 
lean_dec_ref(v___y_3173_);
lean_dec(v_interestingCtors_x3f_3171_);
lean_dec_ref(v_givenNames_3170_);
lean_dec_ref(v___x_3169_);
lean_dec(v_majorFVarId_3168_);
lean_dec(v___x_3167_);
lean_dec(v_mvarId_3166_);
v_a_3253_ = lean_ctor_get(v___x_3178_, 0);
v_isSharedCheck_3260_ = !lean_is_exclusive(v___x_3178_);
if (v_isSharedCheck_3260_ == 0)
{
v___x_3255_ = v___x_3178_;
v_isShared_3256_ = v_isSharedCheck_3260_;
goto v_resetjp_3254_;
}
else
{
lean_inc(v_a_3253_);
lean_dec(v___x_3178_);
v___x_3255_ = lean_box(0);
v_isShared_3256_ = v_isSharedCheck_3260_;
goto v_resetjp_3254_;
}
v_resetjp_3254_:
{
lean_object* v___x_3258_; 
if (v_isShared_3256_ == 0)
{
v___x_3258_ = v___x_3255_;
goto v_reusejp_3257_;
}
else
{
lean_object* v_reuseFailAlloc_3259_; 
v_reuseFailAlloc_3259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3259_, 0, v_a_3253_);
v___x_3258_ = v_reuseFailAlloc_3259_;
goto v_reusejp_3257_;
}
v_reusejp_3257_:
{
return v___x_3258_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_cases___lam__0___boxed(lean_object* v_mvarId_3261_, lean_object* v___x_3262_, lean_object* v_majorFVarId_3263_, lean_object* v___x_3264_, lean_object* v_givenNames_3265_, lean_object* v_interestingCtors_x3f_3266_, lean_object* v_useNatCasesAuxOn_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_){
_start:
{
uint8_t v_useNatCasesAuxOn_boxed_3273_; lean_object* v_res_3274_; 
v_useNatCasesAuxOn_boxed_3273_ = lean_unbox(v_useNatCasesAuxOn_3267_);
v_res_3274_ = l_Lean_Meta_Cases_cases___lam__0(v_mvarId_3261_, v___x_3262_, v_majorFVarId_3263_, v___x_3264_, v_givenNames_3265_, v_interestingCtors_x3f_3266_, v_useNatCasesAuxOn_boxed_3273_, v___y_3268_, v___y_3269_, v___y_3270_, v___y_3271_);
lean_dec(v___y_3271_);
lean_dec_ref(v___y_3270_);
lean_dec(v___y_3269_);
return v_res_3274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_cases(lean_object* v_mvarId_3278_, lean_object* v_majorFVarId_3279_, lean_object* v_givenNames_3280_, uint8_t v_useNatCasesAuxOn_3281_, lean_object* v_interestingCtors_x3f_3282_, lean_object* v_a_3283_, lean_object* v_a_3284_, lean_object* v_a_3285_, lean_object* v_a_3286_){
_start:
{
lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___f_3291_; lean_object* v___x_3292_; 
v___x_3288_ = ((lean_object*)(l_Lean_Meta_Cases_cases___closed__0));
v___x_3289_ = ((lean_object*)(l_Lean_Meta_Cases_cases___closed__1));
v___x_3290_ = lean_box(v_useNatCasesAuxOn_3281_);
lean_inc(v_mvarId_3278_);
v___f_3291_ = lean_alloc_closure((void*)(l_Lean_Meta_Cases_cases___lam__0___boxed), 12, 7);
lean_closure_set(v___f_3291_, 0, v_mvarId_3278_);
lean_closure_set(v___f_3291_, 1, v___x_3289_);
lean_closure_set(v___f_3291_, 2, v_majorFVarId_3279_);
lean_closure_set(v___f_3291_, 3, v___x_3288_);
lean_closure_set(v___f_3291_, 4, v_givenNames_3280_);
lean_closure_set(v___f_3291_, 5, v_interestingCtors_x3f_3282_);
lean_closure_set(v___f_3291_, 6, v___x_3290_);
v___x_3292_ = l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2___redArg(v_mvarId_3278_, v___f_3291_, v_a_3283_, v_a_3284_, v_a_3285_, v_a_3286_);
if (lean_obj_tag(v___x_3292_) == 0)
{
return v___x_3292_;
}
else
{
lean_object* v_a_3293_; uint8_t v___y_3295_; uint8_t v___x_3297_; 
v_a_3293_ = lean_ctor_get(v___x_3292_, 0);
lean_inc(v_a_3293_);
v___x_3297_ = l_Lean_Exception_isInterrupt(v_a_3293_);
if (v___x_3297_ == 0)
{
uint8_t v___x_3298_; 
lean_inc(v_a_3293_);
v___x_3298_ = l_Lean_Exception_isRuntime(v_a_3293_);
v___y_3295_ = v___x_3298_;
goto v___jp_3294_;
}
else
{
v___y_3295_ = v___x_3297_;
goto v___jp_3294_;
}
v___jp_3294_:
{
if (v___y_3295_ == 0)
{
lean_object* v___x_3296_; 
lean_dec_ref(v___x_3292_);
v___x_3296_ = l_Lean_Meta_throwNestedTacticEx___redArg(v___x_3289_, v_a_3293_, v_a_3283_, v_a_3284_, v_a_3285_, v_a_3286_);
return v___x_3296_;
}
else
{
lean_dec(v_a_3293_);
return v___x_3292_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_cases___boxed(lean_object* v_mvarId_3299_, lean_object* v_majorFVarId_3300_, lean_object* v_givenNames_3301_, lean_object* v_useNatCasesAuxOn_3302_, lean_object* v_interestingCtors_x3f_3303_, lean_object* v_a_3304_, lean_object* v_a_3305_, lean_object* v_a_3306_, lean_object* v_a_3307_, lean_object* v_a_3308_){
_start:
{
uint8_t v_useNatCasesAuxOn_boxed_3309_; lean_object* v_res_3310_; 
v_useNatCasesAuxOn_boxed_3309_ = lean_unbox(v_useNatCasesAuxOn_3302_);
v_res_3310_ = l_Lean_Meta_Cases_cases(v_mvarId_3299_, v_majorFVarId_3300_, v_givenNames_3301_, v_useNatCasesAuxOn_boxed_3309_, v_interestingCtors_x3f_3303_, v_a_3304_, v_a_3305_, v_a_3306_, v_a_3307_);
lean_dec(v_a_3307_);
lean_dec_ref(v_a_3306_);
lean_dec(v_a_3305_);
lean_dec_ref(v_a_3304_);
return v_res_3310_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_cases(lean_object* v_mvarId_3311_, lean_object* v_majorFVarId_3312_, lean_object* v_givenNames_3313_, uint8_t v_useNatCasesAuxOn_3314_, lean_object* v_interestingCtors_x3f_3315_, lean_object* v_a_3316_, lean_object* v_a_3317_, lean_object* v_a_3318_, lean_object* v_a_3319_){
_start:
{
lean_object* v___x_3321_; 
v___x_3321_ = l_Lean_Meta_Cases_cases(v_mvarId_3311_, v_majorFVarId_3312_, v_givenNames_3313_, v_useNatCasesAuxOn_3314_, v_interestingCtors_x3f_3315_, v_a_3316_, v_a_3317_, v_a_3318_, v_a_3319_);
return v___x_3321_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_cases___boxed(lean_object* v_mvarId_3322_, lean_object* v_majorFVarId_3323_, lean_object* v_givenNames_3324_, lean_object* v_useNatCasesAuxOn_3325_, lean_object* v_interestingCtors_x3f_3326_, lean_object* v_a_3327_, lean_object* v_a_3328_, lean_object* v_a_3329_, lean_object* v_a_3330_, lean_object* v_a_3331_){
_start:
{
uint8_t v_useNatCasesAuxOn_boxed_3332_; lean_object* v_res_3333_; 
v_useNatCasesAuxOn_boxed_3332_ = lean_unbox(v_useNatCasesAuxOn_3325_);
v_res_3333_ = l_Lean_MVarId_cases(v_mvarId_3322_, v_majorFVarId_3323_, v_givenNames_3324_, v_useNatCasesAuxOn_boxed_3332_, v_interestingCtors_x3f_3326_, v_a_3327_, v_a_3328_, v_a_3329_, v_a_3330_);
lean_dec(v_a_3330_);
lean_dec_ref(v_a_3329_);
lean_dec(v_a_3328_);
lean_dec_ref(v_a_3327_);
return v_res_3333_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1___redArg(lean_object* v_x_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_){
_start:
{
lean_object* v___x_3340_; 
v___x_3340_ = l_Lean_Meta_saveState___redArg(v___y_3336_, v___y_3338_);
if (lean_obj_tag(v___x_3340_) == 0)
{
lean_object* v_a_3341_; lean_object* v___x_3342_; 
v_a_3341_ = lean_ctor_get(v___x_3340_, 0);
lean_inc(v_a_3341_);
lean_dec_ref(v___x_3340_);
lean_inc(v___y_3338_);
lean_inc_ref(v___y_3337_);
lean_inc(v___y_3336_);
lean_inc_ref(v___y_3335_);
v___x_3342_ = lean_apply_5(v_x_3334_, v___y_3335_, v___y_3336_, v___y_3337_, v___y_3338_, lean_box(0));
if (lean_obj_tag(v___x_3342_) == 0)
{
lean_object* v_a_3343_; lean_object* v___x_3345_; uint8_t v_isShared_3346_; uint8_t v_isSharedCheck_3351_; 
lean_dec(v_a_3341_);
v_a_3343_ = lean_ctor_get(v___x_3342_, 0);
v_isSharedCheck_3351_ = !lean_is_exclusive(v___x_3342_);
if (v_isSharedCheck_3351_ == 0)
{
v___x_3345_ = v___x_3342_;
v_isShared_3346_ = v_isSharedCheck_3351_;
goto v_resetjp_3344_;
}
else
{
lean_inc(v_a_3343_);
lean_dec(v___x_3342_);
v___x_3345_ = lean_box(0);
v_isShared_3346_ = v_isSharedCheck_3351_;
goto v_resetjp_3344_;
}
v_resetjp_3344_:
{
lean_object* v___x_3347_; lean_object* v___x_3349_; 
v___x_3347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3347_, 0, v_a_3343_);
if (v_isShared_3346_ == 0)
{
lean_ctor_set(v___x_3345_, 0, v___x_3347_);
v___x_3349_ = v___x_3345_;
goto v_reusejp_3348_;
}
else
{
lean_object* v_reuseFailAlloc_3350_; 
v_reuseFailAlloc_3350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3350_, 0, v___x_3347_);
v___x_3349_ = v_reuseFailAlloc_3350_;
goto v_reusejp_3348_;
}
v_reusejp_3348_:
{
return v___x_3349_;
}
}
}
else
{
lean_object* v_a_3352_; lean_object* v___x_3354_; uint8_t v_isShared_3355_; uint8_t v_isSharedCheck_3381_; 
v_a_3352_ = lean_ctor_get(v___x_3342_, 0);
v_isSharedCheck_3381_ = !lean_is_exclusive(v___x_3342_);
if (v_isSharedCheck_3381_ == 0)
{
v___x_3354_ = v___x_3342_;
v_isShared_3355_ = v_isSharedCheck_3381_;
goto v_resetjp_3353_;
}
else
{
lean_inc(v_a_3352_);
lean_dec(v___x_3342_);
v___x_3354_ = lean_box(0);
v_isShared_3355_ = v_isSharedCheck_3381_;
goto v_resetjp_3353_;
}
v_resetjp_3353_:
{
uint8_t v___y_3357_; uint8_t v___x_3379_; 
v___x_3379_ = l_Lean_Exception_isInterrupt(v_a_3352_);
if (v___x_3379_ == 0)
{
uint8_t v___x_3380_; 
lean_inc(v_a_3352_);
v___x_3380_ = l_Lean_Exception_isRuntime(v_a_3352_);
v___y_3357_ = v___x_3380_;
goto v___jp_3356_;
}
else
{
v___y_3357_ = v___x_3379_;
goto v___jp_3356_;
}
v___jp_3356_:
{
if (v___y_3357_ == 0)
{
lean_object* v___x_3358_; 
lean_del_object(v___x_3354_);
lean_dec(v_a_3352_);
v___x_3358_ = l_Lean_Meta_SavedState_restore___redArg(v_a_3341_, v___y_3336_, v___y_3338_);
lean_dec(v_a_3341_);
if (lean_obj_tag(v___x_3358_) == 0)
{
lean_object* v___x_3360_; uint8_t v_isShared_3361_; uint8_t v_isSharedCheck_3366_; 
v_isSharedCheck_3366_ = !lean_is_exclusive(v___x_3358_);
if (v_isSharedCheck_3366_ == 0)
{
lean_object* v_unused_3367_; 
v_unused_3367_ = lean_ctor_get(v___x_3358_, 0);
lean_dec(v_unused_3367_);
v___x_3360_ = v___x_3358_;
v_isShared_3361_ = v_isSharedCheck_3366_;
goto v_resetjp_3359_;
}
else
{
lean_dec(v___x_3358_);
v___x_3360_ = lean_box(0);
v_isShared_3361_ = v_isSharedCheck_3366_;
goto v_resetjp_3359_;
}
v_resetjp_3359_:
{
lean_object* v___x_3362_; lean_object* v___x_3364_; 
v___x_3362_ = lean_box(0);
if (v_isShared_3361_ == 0)
{
lean_ctor_set(v___x_3360_, 0, v___x_3362_);
v___x_3364_ = v___x_3360_;
goto v_reusejp_3363_;
}
else
{
lean_object* v_reuseFailAlloc_3365_; 
v_reuseFailAlloc_3365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3365_, 0, v___x_3362_);
v___x_3364_ = v_reuseFailAlloc_3365_;
goto v_reusejp_3363_;
}
v_reusejp_3363_:
{
return v___x_3364_;
}
}
}
else
{
lean_object* v_a_3368_; lean_object* v___x_3370_; uint8_t v_isShared_3371_; uint8_t v_isSharedCheck_3375_; 
v_a_3368_ = lean_ctor_get(v___x_3358_, 0);
v_isSharedCheck_3375_ = !lean_is_exclusive(v___x_3358_);
if (v_isSharedCheck_3375_ == 0)
{
v___x_3370_ = v___x_3358_;
v_isShared_3371_ = v_isSharedCheck_3375_;
goto v_resetjp_3369_;
}
else
{
lean_inc(v_a_3368_);
lean_dec(v___x_3358_);
v___x_3370_ = lean_box(0);
v_isShared_3371_ = v_isSharedCheck_3375_;
goto v_resetjp_3369_;
}
v_resetjp_3369_:
{
lean_object* v___x_3373_; 
if (v_isShared_3371_ == 0)
{
v___x_3373_ = v___x_3370_;
goto v_reusejp_3372_;
}
else
{
lean_object* v_reuseFailAlloc_3374_; 
v_reuseFailAlloc_3374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3374_, 0, v_a_3368_);
v___x_3373_ = v_reuseFailAlloc_3374_;
goto v_reusejp_3372_;
}
v_reusejp_3372_:
{
return v___x_3373_;
}
}
}
}
else
{
lean_object* v___x_3377_; 
lean_dec(v_a_3341_);
if (v_isShared_3355_ == 0)
{
v___x_3377_ = v___x_3354_;
goto v_reusejp_3376_;
}
else
{
lean_object* v_reuseFailAlloc_3378_; 
v_reuseFailAlloc_3378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3378_, 0, v_a_3352_);
v___x_3377_ = v_reuseFailAlloc_3378_;
goto v_reusejp_3376_;
}
v_reusejp_3376_:
{
return v___x_3377_;
}
}
}
}
}
}
else
{
lean_object* v_a_3382_; lean_object* v___x_3384_; uint8_t v_isShared_3385_; uint8_t v_isSharedCheck_3389_; 
lean_dec_ref(v_x_3334_);
v_a_3382_ = lean_ctor_get(v___x_3340_, 0);
v_isSharedCheck_3389_ = !lean_is_exclusive(v___x_3340_);
if (v_isSharedCheck_3389_ == 0)
{
v___x_3384_ = v___x_3340_;
v_isShared_3385_ = v_isSharedCheck_3389_;
goto v_resetjp_3383_;
}
else
{
lean_inc(v_a_3382_);
lean_dec(v___x_3340_);
v___x_3384_ = lean_box(0);
v_isShared_3385_ = v_isSharedCheck_3389_;
goto v_resetjp_3383_;
}
v_resetjp_3383_:
{
lean_object* v___x_3387_; 
if (v_isShared_3385_ == 0)
{
v___x_3387_ = v___x_3384_;
goto v_reusejp_3386_;
}
else
{
lean_object* v_reuseFailAlloc_3388_; 
v_reuseFailAlloc_3388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3388_, 0, v_a_3382_);
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
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1___redArg___boxed(lean_object* v_x_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_, lean_object* v___y_3394_, lean_object* v___y_3395_){
_start:
{
lean_object* v_res_3396_; 
v_res_3396_ = l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1___redArg(v_x_3390_, v___y_3391_, v___y_3392_, v___y_3393_, v___y_3394_);
lean_dec(v___y_3394_);
lean_dec_ref(v___y_3393_);
lean_dec(v___y_3392_);
lean_dec_ref(v___y_3391_);
return v_res_3396_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1(lean_object* v_00_u03b1_3397_, lean_object* v_x_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_){
_start:
{
lean_object* v___x_3404_; 
v___x_3404_ = l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1___redArg(v_x_3398_, v___y_3399_, v___y_3400_, v___y_3401_, v___y_3402_);
return v___x_3404_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1___boxed(lean_object* v_00_u03b1_3405_, lean_object* v_x_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_){
_start:
{
lean_object* v_res_3412_; 
v_res_3412_ = l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1(v_00_u03b1_3405_, v_x_3406_, v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_);
lean_dec(v___y_3410_);
lean_dec_ref(v___y_3409_);
lean_dec(v___y_3408_);
lean_dec_ref(v___y_3407_);
return v_res_3412_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_MVarId_casesRec_spec__0(lean_object* v_a_3413_, lean_object* v_a_3414_){
_start:
{
if (lean_obj_tag(v_a_3413_) == 0)
{
lean_object* v___x_3415_; 
v___x_3415_ = l_List_reverse___redArg(v_a_3414_);
return v___x_3415_;
}
else
{
lean_object* v_head_3416_; lean_object* v_toInductionSubgoal_3417_; lean_object* v_tail_3418_; lean_object* v___x_3420_; uint8_t v_isShared_3421_; uint8_t v_isSharedCheck_3427_; 
v_head_3416_ = lean_ctor_get(v_a_3413_, 0);
v_toInductionSubgoal_3417_ = lean_ctor_get(v_head_3416_, 0);
lean_inc_ref(v_toInductionSubgoal_3417_);
v_tail_3418_ = lean_ctor_get(v_a_3413_, 1);
v_isSharedCheck_3427_ = !lean_is_exclusive(v_a_3413_);
if (v_isSharedCheck_3427_ == 0)
{
lean_object* v_unused_3428_; 
v_unused_3428_ = lean_ctor_get(v_a_3413_, 0);
lean_dec(v_unused_3428_);
v___x_3420_ = v_a_3413_;
v_isShared_3421_ = v_isSharedCheck_3427_;
goto v_resetjp_3419_;
}
else
{
lean_inc(v_tail_3418_);
lean_dec(v_a_3413_);
v___x_3420_ = lean_box(0);
v_isShared_3421_ = v_isSharedCheck_3427_;
goto v_resetjp_3419_;
}
v_resetjp_3419_:
{
lean_object* v_mvarId_3422_; lean_object* v___x_3424_; 
v_mvarId_3422_ = lean_ctor_get(v_toInductionSubgoal_3417_, 0);
lean_inc(v_mvarId_3422_);
lean_dec_ref(v_toInductionSubgoal_3417_);
if (v_isShared_3421_ == 0)
{
lean_ctor_set(v___x_3420_, 1, v_a_3414_);
lean_ctor_set(v___x_3420_, 0, v_mvarId_3422_);
v___x_3424_ = v___x_3420_;
goto v_reusejp_3423_;
}
else
{
lean_object* v_reuseFailAlloc_3426_; 
v_reuseFailAlloc_3426_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3426_, 0, v_mvarId_3422_);
lean_ctor_set(v_reuseFailAlloc_3426_, 1, v_a_3414_);
v___x_3424_ = v_reuseFailAlloc_3426_;
goto v_reusejp_3423_;
}
v_reusejp_3423_:
{
v_a_3413_ = v_tail_3418_;
v_a_3414_ = v___x_3424_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3___lam__0(lean_object* v_mvarId_3429_, lean_object* v___x_3430_, lean_object* v___x_3431_, uint8_t v___x_3432_, lean_object* v___x_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_){
_start:
{
lean_object* v___x_3439_; 
v___x_3439_ = l_Lean_Meta_Cases_cases(v_mvarId_3429_, v___x_3430_, v___x_3431_, v___x_3432_, v___x_3433_, v___y_3434_, v___y_3435_, v___y_3436_, v___y_3437_);
if (lean_obj_tag(v___x_3439_) == 0)
{
lean_object* v_a_3440_; lean_object* v___x_3442_; uint8_t v_isShared_3443_; uint8_t v_isSharedCheck_3450_; 
v_a_3440_ = lean_ctor_get(v___x_3439_, 0);
v_isSharedCheck_3450_ = !lean_is_exclusive(v___x_3439_);
if (v_isSharedCheck_3450_ == 0)
{
v___x_3442_ = v___x_3439_;
v_isShared_3443_ = v_isSharedCheck_3450_;
goto v_resetjp_3441_;
}
else
{
lean_inc(v_a_3440_);
lean_dec(v___x_3439_);
v___x_3442_ = lean_box(0);
v_isShared_3443_ = v_isSharedCheck_3450_;
goto v_resetjp_3441_;
}
v_resetjp_3441_:
{
lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3448_; 
v___x_3444_ = lean_array_to_list(v_a_3440_);
v___x_3445_ = lean_box(0);
v___x_3446_ = l_List_mapTR_loop___at___00Lean_MVarId_casesRec_spec__0(v___x_3444_, v___x_3445_);
if (v_isShared_3443_ == 0)
{
lean_ctor_set(v___x_3442_, 0, v___x_3446_);
v___x_3448_ = v___x_3442_;
goto v_reusejp_3447_;
}
else
{
lean_object* v_reuseFailAlloc_3449_; 
v_reuseFailAlloc_3449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3449_, 0, v___x_3446_);
v___x_3448_ = v_reuseFailAlloc_3449_;
goto v_reusejp_3447_;
}
v_reusejp_3447_:
{
return v___x_3448_;
}
}
}
else
{
lean_object* v_a_3451_; lean_object* v___x_3453_; uint8_t v_isShared_3454_; uint8_t v_isSharedCheck_3458_; 
v_a_3451_ = lean_ctor_get(v___x_3439_, 0);
v_isSharedCheck_3458_ = !lean_is_exclusive(v___x_3439_);
if (v_isSharedCheck_3458_ == 0)
{
v___x_3453_ = v___x_3439_;
v_isShared_3454_ = v_isSharedCheck_3458_;
goto v_resetjp_3452_;
}
else
{
lean_inc(v_a_3451_);
lean_dec(v___x_3439_);
v___x_3453_ = lean_box(0);
v_isShared_3454_ = v_isSharedCheck_3458_;
goto v_resetjp_3452_;
}
v_resetjp_3452_:
{
lean_object* v___x_3456_; 
if (v_isShared_3454_ == 0)
{
v___x_3456_ = v___x_3453_;
goto v_reusejp_3455_;
}
else
{
lean_object* v_reuseFailAlloc_3457_; 
v_reuseFailAlloc_3457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3457_, 0, v_a_3451_);
v___x_3456_ = v_reuseFailAlloc_3457_;
goto v_reusejp_3455_;
}
v_reusejp_3455_:
{
return v___x_3456_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3___lam__0___boxed(lean_object* v_mvarId_3459_, lean_object* v___x_3460_, lean_object* v___x_3461_, lean_object* v___x_3462_, lean_object* v___x_3463_, lean_object* v___y_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_, lean_object* v___y_3467_, lean_object* v___y_3468_){
_start:
{
uint8_t v___x_6515__boxed_3469_; lean_object* v_res_3470_; 
v___x_6515__boxed_3469_ = lean_unbox(v___x_3462_);
v_res_3470_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3___lam__0(v_mvarId_3459_, v___x_3460_, v___x_3461_, v___x_6515__boxed_3469_, v___x_3463_, v___y_3464_, v___y_3465_, v___y_3466_, v___y_3467_);
lean_dec(v___y_3467_);
lean_dec_ref(v___y_3466_);
lean_dec(v___y_3465_);
lean_dec_ref(v___y_3464_);
return v_res_3470_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5(lean_object* v_p_3476_, lean_object* v_mvarId_3477_, lean_object* v_as_3478_, size_t v_sz_3479_, size_t v_i_3480_, lean_object* v_b_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_){
_start:
{
uint8_t v___x_3487_; 
v___x_3487_ = lean_usize_dec_lt(v_i_3480_, v_sz_3479_);
if (v___x_3487_ == 0)
{
lean_object* v___x_3488_; 
lean_dec(v_mvarId_3477_);
lean_dec_ref(v_p_3476_);
v___x_3488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3488_, 0, v_b_3481_);
return v___x_3488_;
}
else
{
lean_object* v_snd_3489_; lean_object* v___x_3491_; uint8_t v_isShared_3492_; uint8_t v_isSharedCheck_3557_; 
v_snd_3489_ = lean_ctor_get(v_b_3481_, 1);
v_isSharedCheck_3557_ = !lean_is_exclusive(v_b_3481_);
if (v_isSharedCheck_3557_ == 0)
{
lean_object* v_unused_3558_; 
v_unused_3558_ = lean_ctor_get(v_b_3481_, 0);
lean_dec(v_unused_3558_);
v___x_3491_ = v_b_3481_;
v_isShared_3492_ = v_isSharedCheck_3557_;
goto v_resetjp_3490_;
}
else
{
lean_inc(v_snd_3489_);
lean_dec(v_b_3481_);
v___x_3491_ = lean_box(0);
v_isShared_3492_ = v_isSharedCheck_3557_;
goto v_resetjp_3490_;
}
v_resetjp_3490_:
{
lean_object* v___x_3493_; lean_object* v_a_3495_; lean_object* v_a_3502_; 
v___x_3493_ = lean_box(0);
v_a_3502_ = lean_array_uget(v_as_3478_, v_i_3480_);
if (lean_obj_tag(v_a_3502_) == 0)
{
v_a_3495_ = v_snd_3489_;
goto v___jp_3494_;
}
else
{
lean_object* v_val_3503_; lean_object* v___x_3505_; uint8_t v_isShared_3506_; uint8_t v_isSharedCheck_3556_; 
v_val_3503_ = lean_ctor_get(v_a_3502_, 0);
v_isSharedCheck_3556_ = !lean_is_exclusive(v_a_3502_);
if (v_isSharedCheck_3556_ == 0)
{
v___x_3505_ = v_a_3502_;
v_isShared_3506_ = v_isSharedCheck_3556_;
goto v_resetjp_3504_;
}
else
{
lean_inc(v_val_3503_);
lean_dec(v_a_3502_);
v___x_3505_ = lean_box(0);
v_isShared_3506_ = v_isSharedCheck_3556_;
goto v_resetjp_3504_;
}
v_resetjp_3504_:
{
lean_object* v___x_3507_; 
lean_inc_ref(v_p_3476_);
lean_inc(v___y_3485_);
lean_inc_ref(v___y_3484_);
lean_inc(v___y_3483_);
lean_inc_ref(v___y_3482_);
lean_inc(v_val_3503_);
v___x_3507_ = lean_apply_6(v_p_3476_, v_val_3503_, v___y_3482_, v___y_3483_, v___y_3484_, v___y_3485_, lean_box(0));
if (lean_obj_tag(v___x_3507_) == 0)
{
lean_object* v_a_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; uint8_t v___x_3511_; 
v_a_3508_ = lean_ctor_get(v___x_3507_, 0);
lean_inc(v_a_3508_);
lean_dec_ref(v___x_3507_);
v___x_3509_ = lean_box(0);
v___x_3510_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5___closed__0));
v___x_3511_ = lean_unbox(v_a_3508_);
lean_dec(v_a_3508_);
if (v___x_3511_ == 0)
{
lean_del_object(v___x_3505_);
lean_dec(v_val_3503_);
lean_dec(v_snd_3489_);
v_a_3495_ = v___x_3510_;
goto v___jp_3494_;
}
else
{
lean_object* v___x_3512_; lean_object* v___x_3513_; uint8_t v___x_3514_; lean_object* v___x_3515_; lean_object* v___f_3516_; lean_object* v___x_3517_; 
v___x_3512_ = l_Lean_LocalDecl_fvarId(v_val_3503_);
lean_dec(v_val_3503_);
v___x_3513_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5___closed__1));
v___x_3514_ = 0;
v___x_3515_ = lean_box(v___x_3514_);
lean_inc(v_mvarId_3477_);
v___f_3516_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3___lam__0___boxed), 10, 5);
lean_closure_set(v___f_3516_, 0, v_mvarId_3477_);
lean_closure_set(v___f_3516_, 1, v___x_3512_);
lean_closure_set(v___f_3516_, 2, v___x_3513_);
lean_closure_set(v___f_3516_, 3, v___x_3515_);
lean_closure_set(v___f_3516_, 4, v___x_3493_);
v___x_3517_ = l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1___redArg(v___f_3516_, v___y_3482_, v___y_3483_, v___y_3484_, v___y_3485_);
if (lean_obj_tag(v___x_3517_) == 0)
{
lean_object* v_a_3518_; lean_object* v___x_3520_; uint8_t v_isShared_3521_; uint8_t v_isSharedCheck_3539_; 
v_a_3518_ = lean_ctor_get(v___x_3517_, 0);
v_isSharedCheck_3539_ = !lean_is_exclusive(v___x_3517_);
if (v_isSharedCheck_3539_ == 0)
{
v___x_3520_ = v___x_3517_;
v_isShared_3521_ = v_isSharedCheck_3539_;
goto v_resetjp_3519_;
}
else
{
lean_inc(v_a_3518_);
lean_dec(v___x_3517_);
v___x_3520_ = lean_box(0);
v_isShared_3521_ = v_isSharedCheck_3539_;
goto v_resetjp_3519_;
}
v_resetjp_3519_:
{
if (lean_obj_tag(v_a_3518_) == 0)
{
lean_del_object(v___x_3520_);
lean_del_object(v___x_3505_);
lean_dec(v_snd_3489_);
v_a_3495_ = v___x_3510_;
goto v___jp_3494_;
}
else
{
lean_object* v___x_3523_; 
lean_del_object(v___x_3491_);
lean_dec(v_mvarId_3477_);
lean_dec_ref(v_p_3476_);
lean_inc_ref(v_a_3518_);
if (v_isShared_3506_ == 0)
{
lean_ctor_set(v___x_3505_, 0, v_a_3518_);
v___x_3523_ = v___x_3505_;
goto v_reusejp_3522_;
}
else
{
lean_object* v_reuseFailAlloc_3538_; 
v_reuseFailAlloc_3538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3538_, 0, v_a_3518_);
v___x_3523_ = v_reuseFailAlloc_3538_;
goto v_reusejp_3522_;
}
v_reusejp_3522_:
{
lean_object* v___x_3525_; uint8_t v_isShared_3526_; uint8_t v_isSharedCheck_3536_; 
v_isSharedCheck_3536_ = !lean_is_exclusive(v_a_3518_);
if (v_isSharedCheck_3536_ == 0)
{
lean_object* v_unused_3537_; 
v_unused_3537_ = lean_ctor_get(v_a_3518_, 0);
lean_dec(v_unused_3537_);
v___x_3525_ = v_a_3518_;
v_isShared_3526_ = v_isSharedCheck_3536_;
goto v_resetjp_3524_;
}
else
{
lean_dec(v_a_3518_);
v___x_3525_ = lean_box(0);
v_isShared_3526_ = v_isSharedCheck_3536_;
goto v_resetjp_3524_;
}
v_resetjp_3524_:
{
lean_object* v___x_3527_; lean_object* v___x_3529_; 
v___x_3527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3527_, 0, v___x_3523_);
lean_ctor_set(v___x_3527_, 1, v___x_3509_);
if (v_isShared_3526_ == 0)
{
lean_ctor_set_tag(v___x_3525_, 0);
lean_ctor_set(v___x_3525_, 0, v___x_3527_);
v___x_3529_ = v___x_3525_;
goto v_reusejp_3528_;
}
else
{
lean_object* v_reuseFailAlloc_3535_; 
v_reuseFailAlloc_3535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3535_, 0, v___x_3527_);
v___x_3529_ = v_reuseFailAlloc_3535_;
goto v_reusejp_3528_;
}
v_reusejp_3528_:
{
lean_object* v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3533_; 
v___x_3530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3530_, 0, v___x_3529_);
v___x_3531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3531_, 0, v___x_3530_);
lean_ctor_set(v___x_3531_, 1, v_snd_3489_);
if (v_isShared_3521_ == 0)
{
lean_ctor_set(v___x_3520_, 0, v___x_3531_);
v___x_3533_ = v___x_3520_;
goto v_reusejp_3532_;
}
else
{
lean_object* v_reuseFailAlloc_3534_; 
v_reuseFailAlloc_3534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3534_, 0, v___x_3531_);
v___x_3533_ = v_reuseFailAlloc_3534_;
goto v_reusejp_3532_;
}
v_reusejp_3532_:
{
return v___x_3533_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3540_; lean_object* v___x_3542_; uint8_t v_isShared_3543_; uint8_t v_isSharedCheck_3547_; 
lean_del_object(v___x_3505_);
lean_del_object(v___x_3491_);
lean_dec(v_snd_3489_);
lean_dec(v_mvarId_3477_);
lean_dec_ref(v_p_3476_);
v_a_3540_ = lean_ctor_get(v___x_3517_, 0);
v_isSharedCheck_3547_ = !lean_is_exclusive(v___x_3517_);
if (v_isSharedCheck_3547_ == 0)
{
v___x_3542_ = v___x_3517_;
v_isShared_3543_ = v_isSharedCheck_3547_;
goto v_resetjp_3541_;
}
else
{
lean_inc(v_a_3540_);
lean_dec(v___x_3517_);
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
}
else
{
lean_object* v_a_3548_; lean_object* v___x_3550_; uint8_t v_isShared_3551_; uint8_t v_isSharedCheck_3555_; 
lean_del_object(v___x_3505_);
lean_dec(v_val_3503_);
lean_del_object(v___x_3491_);
lean_dec(v_snd_3489_);
lean_dec(v_mvarId_3477_);
lean_dec_ref(v_p_3476_);
v_a_3548_ = lean_ctor_get(v___x_3507_, 0);
v_isSharedCheck_3555_ = !lean_is_exclusive(v___x_3507_);
if (v_isSharedCheck_3555_ == 0)
{
v___x_3550_ = v___x_3507_;
v_isShared_3551_ = v_isSharedCheck_3555_;
goto v_resetjp_3549_;
}
else
{
lean_inc(v_a_3548_);
lean_dec(v___x_3507_);
v___x_3550_ = lean_box(0);
v_isShared_3551_ = v_isSharedCheck_3555_;
goto v_resetjp_3549_;
}
v_resetjp_3549_:
{
lean_object* v___x_3553_; 
if (v_isShared_3551_ == 0)
{
v___x_3553_ = v___x_3550_;
goto v_reusejp_3552_;
}
else
{
lean_object* v_reuseFailAlloc_3554_; 
v_reuseFailAlloc_3554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3554_, 0, v_a_3548_);
v___x_3553_ = v_reuseFailAlloc_3554_;
goto v_reusejp_3552_;
}
v_reusejp_3552_:
{
return v___x_3553_;
}
}
}
}
}
v___jp_3494_:
{
lean_object* v___x_3497_; 
if (v_isShared_3492_ == 0)
{
lean_ctor_set(v___x_3491_, 1, v_a_3495_);
lean_ctor_set(v___x_3491_, 0, v___x_3493_);
v___x_3497_ = v___x_3491_;
goto v_reusejp_3496_;
}
else
{
lean_object* v_reuseFailAlloc_3501_; 
v_reuseFailAlloc_3501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3501_, 0, v___x_3493_);
lean_ctor_set(v_reuseFailAlloc_3501_, 1, v_a_3495_);
v___x_3497_ = v_reuseFailAlloc_3501_;
goto v_reusejp_3496_;
}
v_reusejp_3496_:
{
size_t v___x_3498_; size_t v___x_3499_; 
v___x_3498_ = ((size_t)1ULL);
v___x_3499_ = lean_usize_add(v_i_3480_, v___x_3498_);
v_i_3480_ = v___x_3499_;
v_b_3481_ = v___x_3497_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5___boxed(lean_object* v_p_3559_, lean_object* v_mvarId_3560_, lean_object* v_as_3561_, lean_object* v_sz_3562_, lean_object* v_i_3563_, lean_object* v_b_3564_, lean_object* v___y_3565_, lean_object* v___y_3566_, lean_object* v___y_3567_, lean_object* v___y_3568_, lean_object* v___y_3569_){
_start:
{
size_t v_sz_boxed_3570_; size_t v_i_boxed_3571_; lean_object* v_res_3572_; 
v_sz_boxed_3570_ = lean_unbox_usize(v_sz_3562_);
lean_dec(v_sz_3562_);
v_i_boxed_3571_ = lean_unbox_usize(v_i_3563_);
lean_dec(v_i_3563_);
v_res_3572_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5(v_p_3559_, v_mvarId_3560_, v_as_3561_, v_sz_boxed_3570_, v_i_boxed_3571_, v_b_3564_, v___y_3565_, v___y_3566_, v___y_3567_, v___y_3568_);
lean_dec(v___y_3568_);
lean_dec_ref(v___y_3567_);
lean_dec(v___y_3566_);
lean_dec_ref(v___y_3565_);
lean_dec_ref(v_as_3561_);
return v_res_3572_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4(lean_object* v_p_3573_, lean_object* v_mvarId_3574_, lean_object* v_as_3575_, size_t v_sz_3576_, size_t v_i_3577_, lean_object* v_b_3578_, lean_object* v___y_3579_, lean_object* v___y_3580_, lean_object* v___y_3581_, lean_object* v___y_3582_){
_start:
{
uint8_t v___x_3584_; 
v___x_3584_ = lean_usize_dec_lt(v_i_3577_, v_sz_3576_);
if (v___x_3584_ == 0)
{
lean_object* v___x_3585_; 
lean_dec(v_mvarId_3574_);
lean_dec_ref(v_p_3573_);
v___x_3585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3585_, 0, v_b_3578_);
return v___x_3585_;
}
else
{
lean_object* v_snd_3586_; lean_object* v___x_3588_; uint8_t v_isShared_3589_; uint8_t v_isSharedCheck_3654_; 
v_snd_3586_ = lean_ctor_get(v_b_3578_, 1);
v_isSharedCheck_3654_ = !lean_is_exclusive(v_b_3578_);
if (v_isSharedCheck_3654_ == 0)
{
lean_object* v_unused_3655_; 
v_unused_3655_ = lean_ctor_get(v_b_3578_, 0);
lean_dec(v_unused_3655_);
v___x_3588_ = v_b_3578_;
v_isShared_3589_ = v_isSharedCheck_3654_;
goto v_resetjp_3587_;
}
else
{
lean_inc(v_snd_3586_);
lean_dec(v_b_3578_);
v___x_3588_ = lean_box(0);
v_isShared_3589_ = v_isSharedCheck_3654_;
goto v_resetjp_3587_;
}
v_resetjp_3587_:
{
lean_object* v___x_3590_; lean_object* v_a_3592_; lean_object* v_a_3599_; 
v___x_3590_ = lean_box(0);
v_a_3599_ = lean_array_uget(v_as_3575_, v_i_3577_);
if (lean_obj_tag(v_a_3599_) == 0)
{
v_a_3592_ = v_snd_3586_;
goto v___jp_3591_;
}
else
{
lean_object* v_val_3600_; lean_object* v___x_3602_; uint8_t v_isShared_3603_; uint8_t v_isSharedCheck_3653_; 
v_val_3600_ = lean_ctor_get(v_a_3599_, 0);
v_isSharedCheck_3653_ = !lean_is_exclusive(v_a_3599_);
if (v_isSharedCheck_3653_ == 0)
{
v___x_3602_ = v_a_3599_;
v_isShared_3603_ = v_isSharedCheck_3653_;
goto v_resetjp_3601_;
}
else
{
lean_inc(v_val_3600_);
lean_dec(v_a_3599_);
v___x_3602_ = lean_box(0);
v_isShared_3603_ = v_isSharedCheck_3653_;
goto v_resetjp_3601_;
}
v_resetjp_3601_:
{
lean_object* v___x_3604_; 
lean_inc_ref(v_p_3573_);
lean_inc(v___y_3582_);
lean_inc_ref(v___y_3581_);
lean_inc(v___y_3580_);
lean_inc_ref(v___y_3579_);
lean_inc(v_val_3600_);
v___x_3604_ = lean_apply_6(v_p_3573_, v_val_3600_, v___y_3579_, v___y_3580_, v___y_3581_, v___y_3582_, lean_box(0));
if (lean_obj_tag(v___x_3604_) == 0)
{
lean_object* v_a_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; uint8_t v___x_3608_; 
v_a_3605_ = lean_ctor_get(v___x_3604_, 0);
lean_inc(v_a_3605_);
lean_dec_ref(v___x_3604_);
v___x_3606_ = lean_box(0);
v___x_3607_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5___closed__0));
v___x_3608_ = lean_unbox(v_a_3605_);
lean_dec(v_a_3605_);
if (v___x_3608_ == 0)
{
lean_del_object(v___x_3602_);
lean_dec(v_val_3600_);
lean_dec(v_snd_3586_);
v_a_3592_ = v___x_3607_;
goto v___jp_3591_;
}
else
{
lean_object* v___x_3609_; lean_object* v___x_3610_; uint8_t v___x_3611_; lean_object* v___x_3612_; lean_object* v___f_3613_; lean_object* v___x_3614_; 
v___x_3609_ = l_Lean_LocalDecl_fvarId(v_val_3600_);
lean_dec(v_val_3600_);
v___x_3610_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5___closed__1));
v___x_3611_ = 0;
v___x_3612_ = lean_box(v___x_3611_);
lean_inc(v_mvarId_3574_);
v___f_3613_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3___lam__0___boxed), 10, 5);
lean_closure_set(v___f_3613_, 0, v_mvarId_3574_);
lean_closure_set(v___f_3613_, 1, v___x_3609_);
lean_closure_set(v___f_3613_, 2, v___x_3610_);
lean_closure_set(v___f_3613_, 3, v___x_3612_);
lean_closure_set(v___f_3613_, 4, v___x_3590_);
v___x_3614_ = l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1___redArg(v___f_3613_, v___y_3579_, v___y_3580_, v___y_3581_, v___y_3582_);
if (lean_obj_tag(v___x_3614_) == 0)
{
lean_object* v_a_3615_; lean_object* v___x_3617_; uint8_t v_isShared_3618_; uint8_t v_isSharedCheck_3636_; 
v_a_3615_ = lean_ctor_get(v___x_3614_, 0);
v_isSharedCheck_3636_ = !lean_is_exclusive(v___x_3614_);
if (v_isSharedCheck_3636_ == 0)
{
v___x_3617_ = v___x_3614_;
v_isShared_3618_ = v_isSharedCheck_3636_;
goto v_resetjp_3616_;
}
else
{
lean_inc(v_a_3615_);
lean_dec(v___x_3614_);
v___x_3617_ = lean_box(0);
v_isShared_3618_ = v_isSharedCheck_3636_;
goto v_resetjp_3616_;
}
v_resetjp_3616_:
{
if (lean_obj_tag(v_a_3615_) == 0)
{
lean_del_object(v___x_3617_);
lean_del_object(v___x_3602_);
lean_dec(v_snd_3586_);
v_a_3592_ = v___x_3607_;
goto v___jp_3591_;
}
else
{
lean_object* v___x_3620_; 
lean_del_object(v___x_3588_);
lean_dec(v_mvarId_3574_);
lean_dec_ref(v_p_3573_);
lean_inc_ref(v_a_3615_);
if (v_isShared_3603_ == 0)
{
lean_ctor_set(v___x_3602_, 0, v_a_3615_);
v___x_3620_ = v___x_3602_;
goto v_reusejp_3619_;
}
else
{
lean_object* v_reuseFailAlloc_3635_; 
v_reuseFailAlloc_3635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3635_, 0, v_a_3615_);
v___x_3620_ = v_reuseFailAlloc_3635_;
goto v_reusejp_3619_;
}
v_reusejp_3619_:
{
lean_object* v___x_3622_; uint8_t v_isShared_3623_; uint8_t v_isSharedCheck_3633_; 
v_isSharedCheck_3633_ = !lean_is_exclusive(v_a_3615_);
if (v_isSharedCheck_3633_ == 0)
{
lean_object* v_unused_3634_; 
v_unused_3634_ = lean_ctor_get(v_a_3615_, 0);
lean_dec(v_unused_3634_);
v___x_3622_ = v_a_3615_;
v_isShared_3623_ = v_isSharedCheck_3633_;
goto v_resetjp_3621_;
}
else
{
lean_dec(v_a_3615_);
v___x_3622_ = lean_box(0);
v_isShared_3623_ = v_isSharedCheck_3633_;
goto v_resetjp_3621_;
}
v_resetjp_3621_:
{
lean_object* v___x_3624_; lean_object* v___x_3626_; 
v___x_3624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3624_, 0, v___x_3620_);
lean_ctor_set(v___x_3624_, 1, v___x_3606_);
if (v_isShared_3623_ == 0)
{
lean_ctor_set_tag(v___x_3622_, 0);
lean_ctor_set(v___x_3622_, 0, v___x_3624_);
v___x_3626_ = v___x_3622_;
goto v_reusejp_3625_;
}
else
{
lean_object* v_reuseFailAlloc_3632_; 
v_reuseFailAlloc_3632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3632_, 0, v___x_3624_);
v___x_3626_ = v_reuseFailAlloc_3632_;
goto v_reusejp_3625_;
}
v_reusejp_3625_:
{
lean_object* v___x_3627_; lean_object* v___x_3628_; lean_object* v___x_3630_; 
v___x_3627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3627_, 0, v___x_3626_);
v___x_3628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3628_, 0, v___x_3627_);
lean_ctor_set(v___x_3628_, 1, v_snd_3586_);
if (v_isShared_3618_ == 0)
{
lean_ctor_set(v___x_3617_, 0, v___x_3628_);
v___x_3630_ = v___x_3617_;
goto v_reusejp_3629_;
}
else
{
lean_object* v_reuseFailAlloc_3631_; 
v_reuseFailAlloc_3631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3631_, 0, v___x_3628_);
v___x_3630_ = v_reuseFailAlloc_3631_;
goto v_reusejp_3629_;
}
v_reusejp_3629_:
{
return v___x_3630_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3637_; lean_object* v___x_3639_; uint8_t v_isShared_3640_; uint8_t v_isSharedCheck_3644_; 
lean_del_object(v___x_3602_);
lean_del_object(v___x_3588_);
lean_dec(v_snd_3586_);
lean_dec(v_mvarId_3574_);
lean_dec_ref(v_p_3573_);
v_a_3637_ = lean_ctor_get(v___x_3614_, 0);
v_isSharedCheck_3644_ = !lean_is_exclusive(v___x_3614_);
if (v_isSharedCheck_3644_ == 0)
{
v___x_3639_ = v___x_3614_;
v_isShared_3640_ = v_isSharedCheck_3644_;
goto v_resetjp_3638_;
}
else
{
lean_inc(v_a_3637_);
lean_dec(v___x_3614_);
v___x_3639_ = lean_box(0);
v_isShared_3640_ = v_isSharedCheck_3644_;
goto v_resetjp_3638_;
}
v_resetjp_3638_:
{
lean_object* v___x_3642_; 
if (v_isShared_3640_ == 0)
{
v___x_3642_ = v___x_3639_;
goto v_reusejp_3641_;
}
else
{
lean_object* v_reuseFailAlloc_3643_; 
v_reuseFailAlloc_3643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3643_, 0, v_a_3637_);
v___x_3642_ = v_reuseFailAlloc_3643_;
goto v_reusejp_3641_;
}
v_reusejp_3641_:
{
return v___x_3642_;
}
}
}
}
}
else
{
lean_object* v_a_3645_; lean_object* v___x_3647_; uint8_t v_isShared_3648_; uint8_t v_isSharedCheck_3652_; 
lean_del_object(v___x_3602_);
lean_dec(v_val_3600_);
lean_del_object(v___x_3588_);
lean_dec(v_snd_3586_);
lean_dec(v_mvarId_3574_);
lean_dec_ref(v_p_3573_);
v_a_3645_ = lean_ctor_get(v___x_3604_, 0);
v_isSharedCheck_3652_ = !lean_is_exclusive(v___x_3604_);
if (v_isSharedCheck_3652_ == 0)
{
v___x_3647_ = v___x_3604_;
v_isShared_3648_ = v_isSharedCheck_3652_;
goto v_resetjp_3646_;
}
else
{
lean_inc(v_a_3645_);
lean_dec(v___x_3604_);
v___x_3647_ = lean_box(0);
v_isShared_3648_ = v_isSharedCheck_3652_;
goto v_resetjp_3646_;
}
v_resetjp_3646_:
{
lean_object* v___x_3650_; 
if (v_isShared_3648_ == 0)
{
v___x_3650_ = v___x_3647_;
goto v_reusejp_3649_;
}
else
{
lean_object* v_reuseFailAlloc_3651_; 
v_reuseFailAlloc_3651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3651_, 0, v_a_3645_);
v___x_3650_ = v_reuseFailAlloc_3651_;
goto v_reusejp_3649_;
}
v_reusejp_3649_:
{
return v___x_3650_;
}
}
}
}
}
v___jp_3591_:
{
lean_object* v___x_3594_; 
if (v_isShared_3589_ == 0)
{
lean_ctor_set(v___x_3588_, 1, v_a_3592_);
lean_ctor_set(v___x_3588_, 0, v___x_3590_);
v___x_3594_ = v___x_3588_;
goto v_reusejp_3593_;
}
else
{
lean_object* v_reuseFailAlloc_3598_; 
v_reuseFailAlloc_3598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3598_, 0, v___x_3590_);
lean_ctor_set(v_reuseFailAlloc_3598_, 1, v_a_3592_);
v___x_3594_ = v_reuseFailAlloc_3598_;
goto v_reusejp_3593_;
}
v_reusejp_3593_:
{
size_t v___x_3595_; size_t v___x_3596_; lean_object* v___x_3597_; 
v___x_3595_ = ((size_t)1ULL);
v___x_3596_ = lean_usize_add(v_i_3577_, v___x_3595_);
v___x_3597_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5(v_p_3573_, v_mvarId_3574_, v_as_3575_, v_sz_3576_, v___x_3596_, v___x_3594_, v___y_3579_, v___y_3580_, v___y_3581_, v___y_3582_);
return v___x_3597_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4___boxed(lean_object* v_p_3656_, lean_object* v_mvarId_3657_, lean_object* v_as_3658_, lean_object* v_sz_3659_, lean_object* v_i_3660_, lean_object* v_b_3661_, lean_object* v___y_3662_, lean_object* v___y_3663_, lean_object* v___y_3664_, lean_object* v___y_3665_, lean_object* v___y_3666_){
_start:
{
size_t v_sz_boxed_3667_; size_t v_i_boxed_3668_; lean_object* v_res_3669_; 
v_sz_boxed_3667_ = lean_unbox_usize(v_sz_3659_);
lean_dec(v_sz_3659_);
v_i_boxed_3668_ = lean_unbox_usize(v_i_3660_);
lean_dec(v_i_3660_);
v_res_3669_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4(v_p_3656_, v_mvarId_3657_, v_as_3658_, v_sz_boxed_3667_, v_i_boxed_3668_, v_b_3661_, v___y_3662_, v___y_3663_, v___y_3664_, v___y_3665_);
lean_dec(v___y_3665_);
lean_dec_ref(v___y_3664_);
lean_dec(v___y_3663_);
lean_dec_ref(v___y_3662_);
lean_dec_ref(v_as_3658_);
return v_res_3669_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2(lean_object* v_p_3670_, lean_object* v_mvarId_3671_, lean_object* v_inh_3672_, lean_object* v_n_3673_, lean_object* v_b_3674_, lean_object* v___y_3675_, lean_object* v___y_3676_, lean_object* v___y_3677_, lean_object* v___y_3678_){
_start:
{
if (lean_obj_tag(v_n_3673_) == 0)
{
lean_object* v_cs_3680_; lean_object* v___x_3682_; uint8_t v_isShared_3683_; uint8_t v_isSharedCheck_3714_; 
v_cs_3680_ = lean_ctor_get(v_n_3673_, 0);
v_isSharedCheck_3714_ = !lean_is_exclusive(v_n_3673_);
if (v_isSharedCheck_3714_ == 0)
{
v___x_3682_ = v_n_3673_;
v_isShared_3683_ = v_isSharedCheck_3714_;
goto v_resetjp_3681_;
}
else
{
lean_inc(v_cs_3680_);
lean_dec(v_n_3673_);
v___x_3682_ = lean_box(0);
v_isShared_3683_ = v_isSharedCheck_3714_;
goto v_resetjp_3681_;
}
v_resetjp_3681_:
{
lean_object* v___x_3684_; lean_object* v___x_3685_; size_t v_sz_3686_; size_t v___x_3687_; lean_object* v___x_3688_; 
v___x_3684_ = lean_box(0);
v___x_3685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3685_, 0, v___x_3684_);
lean_ctor_set(v___x_3685_, 1, v_b_3674_);
v_sz_3686_ = lean_array_size(v_cs_3680_);
v___x_3687_ = ((size_t)0ULL);
v___x_3688_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__3(v_p_3670_, v_mvarId_3671_, v_inh_3672_, v_cs_3680_, v_sz_3686_, v___x_3687_, v___x_3685_, v___y_3675_, v___y_3676_, v___y_3677_, v___y_3678_);
lean_dec_ref(v_cs_3680_);
if (lean_obj_tag(v___x_3688_) == 0)
{
lean_object* v_a_3689_; lean_object* v___x_3691_; uint8_t v_isShared_3692_; uint8_t v_isSharedCheck_3705_; 
v_a_3689_ = lean_ctor_get(v___x_3688_, 0);
v_isSharedCheck_3705_ = !lean_is_exclusive(v___x_3688_);
if (v_isSharedCheck_3705_ == 0)
{
v___x_3691_ = v___x_3688_;
v_isShared_3692_ = v_isSharedCheck_3705_;
goto v_resetjp_3690_;
}
else
{
lean_inc(v_a_3689_);
lean_dec(v___x_3688_);
v___x_3691_ = lean_box(0);
v_isShared_3692_ = v_isSharedCheck_3705_;
goto v_resetjp_3690_;
}
v_resetjp_3690_:
{
lean_object* v_fst_3693_; 
v_fst_3693_ = lean_ctor_get(v_a_3689_, 0);
if (lean_obj_tag(v_fst_3693_) == 0)
{
lean_object* v_snd_3694_; lean_object* v___x_3696_; 
v_snd_3694_ = lean_ctor_get(v_a_3689_, 1);
lean_inc(v_snd_3694_);
lean_dec(v_a_3689_);
if (v_isShared_3683_ == 0)
{
lean_ctor_set_tag(v___x_3682_, 1);
lean_ctor_set(v___x_3682_, 0, v_snd_3694_);
v___x_3696_ = v___x_3682_;
goto v_reusejp_3695_;
}
else
{
lean_object* v_reuseFailAlloc_3700_; 
v_reuseFailAlloc_3700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3700_, 0, v_snd_3694_);
v___x_3696_ = v_reuseFailAlloc_3700_;
goto v_reusejp_3695_;
}
v_reusejp_3695_:
{
lean_object* v___x_3698_; 
if (v_isShared_3692_ == 0)
{
lean_ctor_set(v___x_3691_, 0, v___x_3696_);
v___x_3698_ = v___x_3691_;
goto v_reusejp_3697_;
}
else
{
lean_object* v_reuseFailAlloc_3699_; 
v_reuseFailAlloc_3699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3699_, 0, v___x_3696_);
v___x_3698_ = v_reuseFailAlloc_3699_;
goto v_reusejp_3697_;
}
v_reusejp_3697_:
{
return v___x_3698_;
}
}
}
else
{
lean_object* v_val_3701_; lean_object* v___x_3703_; 
lean_inc_ref(v_fst_3693_);
lean_dec(v_a_3689_);
lean_del_object(v___x_3682_);
v_val_3701_ = lean_ctor_get(v_fst_3693_, 0);
lean_inc(v_val_3701_);
lean_dec_ref(v_fst_3693_);
if (v_isShared_3692_ == 0)
{
lean_ctor_set(v___x_3691_, 0, v_val_3701_);
v___x_3703_ = v___x_3691_;
goto v_reusejp_3702_;
}
else
{
lean_object* v_reuseFailAlloc_3704_; 
v_reuseFailAlloc_3704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3704_, 0, v_val_3701_);
v___x_3703_ = v_reuseFailAlloc_3704_;
goto v_reusejp_3702_;
}
v_reusejp_3702_:
{
return v___x_3703_;
}
}
}
}
else
{
lean_object* v_a_3706_; lean_object* v___x_3708_; uint8_t v_isShared_3709_; uint8_t v_isSharedCheck_3713_; 
lean_del_object(v___x_3682_);
v_a_3706_ = lean_ctor_get(v___x_3688_, 0);
v_isSharedCheck_3713_ = !lean_is_exclusive(v___x_3688_);
if (v_isSharedCheck_3713_ == 0)
{
v___x_3708_ = v___x_3688_;
v_isShared_3709_ = v_isSharedCheck_3713_;
goto v_resetjp_3707_;
}
else
{
lean_inc(v_a_3706_);
lean_dec(v___x_3688_);
v___x_3708_ = lean_box(0);
v_isShared_3709_ = v_isSharedCheck_3713_;
goto v_resetjp_3707_;
}
v_resetjp_3707_:
{
lean_object* v___x_3711_; 
if (v_isShared_3709_ == 0)
{
v___x_3711_ = v___x_3708_;
goto v_reusejp_3710_;
}
else
{
lean_object* v_reuseFailAlloc_3712_; 
v_reuseFailAlloc_3712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3712_, 0, v_a_3706_);
v___x_3711_ = v_reuseFailAlloc_3712_;
goto v_reusejp_3710_;
}
v_reusejp_3710_:
{
return v___x_3711_;
}
}
}
}
}
else
{
lean_object* v_vs_3715_; lean_object* v___x_3717_; uint8_t v_isShared_3718_; uint8_t v_isSharedCheck_3749_; 
v_vs_3715_ = lean_ctor_get(v_n_3673_, 0);
v_isSharedCheck_3749_ = !lean_is_exclusive(v_n_3673_);
if (v_isSharedCheck_3749_ == 0)
{
v___x_3717_ = v_n_3673_;
v_isShared_3718_ = v_isSharedCheck_3749_;
goto v_resetjp_3716_;
}
else
{
lean_inc(v_vs_3715_);
lean_dec(v_n_3673_);
v___x_3717_ = lean_box(0);
v_isShared_3718_ = v_isSharedCheck_3749_;
goto v_resetjp_3716_;
}
v_resetjp_3716_:
{
lean_object* v___x_3719_; lean_object* v___x_3720_; size_t v_sz_3721_; size_t v___x_3722_; lean_object* v___x_3723_; 
v___x_3719_ = lean_box(0);
v___x_3720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3720_, 0, v___x_3719_);
lean_ctor_set(v___x_3720_, 1, v_b_3674_);
v_sz_3721_ = lean_array_size(v_vs_3715_);
v___x_3722_ = ((size_t)0ULL);
v___x_3723_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4(v_p_3670_, v_mvarId_3671_, v_vs_3715_, v_sz_3721_, v___x_3722_, v___x_3720_, v___y_3675_, v___y_3676_, v___y_3677_, v___y_3678_);
lean_dec_ref(v_vs_3715_);
if (lean_obj_tag(v___x_3723_) == 0)
{
lean_object* v_a_3724_; lean_object* v___x_3726_; uint8_t v_isShared_3727_; uint8_t v_isSharedCheck_3740_; 
v_a_3724_ = lean_ctor_get(v___x_3723_, 0);
v_isSharedCheck_3740_ = !lean_is_exclusive(v___x_3723_);
if (v_isSharedCheck_3740_ == 0)
{
v___x_3726_ = v___x_3723_;
v_isShared_3727_ = v_isSharedCheck_3740_;
goto v_resetjp_3725_;
}
else
{
lean_inc(v_a_3724_);
lean_dec(v___x_3723_);
v___x_3726_ = lean_box(0);
v_isShared_3727_ = v_isSharedCheck_3740_;
goto v_resetjp_3725_;
}
v_resetjp_3725_:
{
lean_object* v_fst_3728_; 
v_fst_3728_ = lean_ctor_get(v_a_3724_, 0);
if (lean_obj_tag(v_fst_3728_) == 0)
{
lean_object* v_snd_3729_; lean_object* v___x_3731_; 
v_snd_3729_ = lean_ctor_get(v_a_3724_, 1);
lean_inc(v_snd_3729_);
lean_dec(v_a_3724_);
if (v_isShared_3718_ == 0)
{
lean_ctor_set(v___x_3717_, 0, v_snd_3729_);
v___x_3731_ = v___x_3717_;
goto v_reusejp_3730_;
}
else
{
lean_object* v_reuseFailAlloc_3735_; 
v_reuseFailAlloc_3735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3735_, 0, v_snd_3729_);
v___x_3731_ = v_reuseFailAlloc_3735_;
goto v_reusejp_3730_;
}
v_reusejp_3730_:
{
lean_object* v___x_3733_; 
if (v_isShared_3727_ == 0)
{
lean_ctor_set(v___x_3726_, 0, v___x_3731_);
v___x_3733_ = v___x_3726_;
goto v_reusejp_3732_;
}
else
{
lean_object* v_reuseFailAlloc_3734_; 
v_reuseFailAlloc_3734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3734_, 0, v___x_3731_);
v___x_3733_ = v_reuseFailAlloc_3734_;
goto v_reusejp_3732_;
}
v_reusejp_3732_:
{
return v___x_3733_;
}
}
}
else
{
lean_object* v_val_3736_; lean_object* v___x_3738_; 
lean_inc_ref(v_fst_3728_);
lean_dec(v_a_3724_);
lean_del_object(v___x_3717_);
v_val_3736_ = lean_ctor_get(v_fst_3728_, 0);
lean_inc(v_val_3736_);
lean_dec_ref(v_fst_3728_);
if (v_isShared_3727_ == 0)
{
lean_ctor_set(v___x_3726_, 0, v_val_3736_);
v___x_3738_ = v___x_3726_;
goto v_reusejp_3737_;
}
else
{
lean_object* v_reuseFailAlloc_3739_; 
v_reuseFailAlloc_3739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3739_, 0, v_val_3736_);
v___x_3738_ = v_reuseFailAlloc_3739_;
goto v_reusejp_3737_;
}
v_reusejp_3737_:
{
return v___x_3738_;
}
}
}
}
else
{
lean_object* v_a_3741_; lean_object* v___x_3743_; uint8_t v_isShared_3744_; uint8_t v_isSharedCheck_3748_; 
lean_del_object(v___x_3717_);
v_a_3741_ = lean_ctor_get(v___x_3723_, 0);
v_isSharedCheck_3748_ = !lean_is_exclusive(v___x_3723_);
if (v_isSharedCheck_3748_ == 0)
{
v___x_3743_ = v___x_3723_;
v_isShared_3744_ = v_isSharedCheck_3748_;
goto v_resetjp_3742_;
}
else
{
lean_inc(v_a_3741_);
lean_dec(v___x_3723_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__3(lean_object* v_p_3750_, lean_object* v_mvarId_3751_, lean_object* v_inh_3752_, lean_object* v_as_3753_, size_t v_sz_3754_, size_t v_i_3755_, lean_object* v_b_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_){
_start:
{
uint8_t v___x_3762_; 
v___x_3762_ = lean_usize_dec_lt(v_i_3755_, v_sz_3754_);
if (v___x_3762_ == 0)
{
lean_object* v___x_3763_; 
lean_dec(v_mvarId_3751_);
lean_dec_ref(v_p_3750_);
v___x_3763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3763_, 0, v_b_3756_);
return v___x_3763_;
}
else
{
lean_object* v_snd_3764_; lean_object* v___x_3766_; uint8_t v_isShared_3767_; uint8_t v_isSharedCheck_3798_; 
v_snd_3764_ = lean_ctor_get(v_b_3756_, 1);
v_isSharedCheck_3798_ = !lean_is_exclusive(v_b_3756_);
if (v_isSharedCheck_3798_ == 0)
{
lean_object* v_unused_3799_; 
v_unused_3799_ = lean_ctor_get(v_b_3756_, 0);
lean_dec(v_unused_3799_);
v___x_3766_ = v_b_3756_;
v_isShared_3767_ = v_isSharedCheck_3798_;
goto v_resetjp_3765_;
}
else
{
lean_inc(v_snd_3764_);
lean_dec(v_b_3756_);
v___x_3766_ = lean_box(0);
v_isShared_3767_ = v_isSharedCheck_3798_;
goto v_resetjp_3765_;
}
v_resetjp_3765_:
{
lean_object* v_a_3768_; lean_object* v___x_3769_; 
v_a_3768_ = lean_array_uget_borrowed(v_as_3753_, v_i_3755_);
lean_inc(v_snd_3764_);
lean_inc(v_a_3768_);
lean_inc(v_mvarId_3751_);
lean_inc_ref(v_p_3750_);
v___x_3769_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2(v_p_3750_, v_mvarId_3751_, v_inh_3752_, v_a_3768_, v_snd_3764_, v___y_3757_, v___y_3758_, v___y_3759_, v___y_3760_);
if (lean_obj_tag(v___x_3769_) == 0)
{
lean_object* v_a_3770_; lean_object* v___x_3772_; uint8_t v_isShared_3773_; uint8_t v_isSharedCheck_3789_; 
v_a_3770_ = lean_ctor_get(v___x_3769_, 0);
v_isSharedCheck_3789_ = !lean_is_exclusive(v___x_3769_);
if (v_isSharedCheck_3789_ == 0)
{
v___x_3772_ = v___x_3769_;
v_isShared_3773_ = v_isSharedCheck_3789_;
goto v_resetjp_3771_;
}
else
{
lean_inc(v_a_3770_);
lean_dec(v___x_3769_);
v___x_3772_ = lean_box(0);
v_isShared_3773_ = v_isSharedCheck_3789_;
goto v_resetjp_3771_;
}
v_resetjp_3771_:
{
if (lean_obj_tag(v_a_3770_) == 0)
{
lean_object* v___x_3774_; lean_object* v___x_3776_; 
lean_dec(v_mvarId_3751_);
lean_dec_ref(v_p_3750_);
v___x_3774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3774_, 0, v_a_3770_);
if (v_isShared_3767_ == 0)
{
lean_ctor_set(v___x_3766_, 0, v___x_3774_);
v___x_3776_ = v___x_3766_;
goto v_reusejp_3775_;
}
else
{
lean_object* v_reuseFailAlloc_3780_; 
v_reuseFailAlloc_3780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3780_, 0, v___x_3774_);
lean_ctor_set(v_reuseFailAlloc_3780_, 1, v_snd_3764_);
v___x_3776_ = v_reuseFailAlloc_3780_;
goto v_reusejp_3775_;
}
v_reusejp_3775_:
{
lean_object* v___x_3778_; 
if (v_isShared_3773_ == 0)
{
lean_ctor_set(v___x_3772_, 0, v___x_3776_);
v___x_3778_ = v___x_3772_;
goto v_reusejp_3777_;
}
else
{
lean_object* v_reuseFailAlloc_3779_; 
v_reuseFailAlloc_3779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3779_, 0, v___x_3776_);
v___x_3778_ = v_reuseFailAlloc_3779_;
goto v_reusejp_3777_;
}
v_reusejp_3777_:
{
return v___x_3778_;
}
}
}
else
{
lean_object* v_a_3781_; lean_object* v___x_3782_; lean_object* v___x_3784_; 
lean_del_object(v___x_3772_);
lean_dec(v_snd_3764_);
v_a_3781_ = lean_ctor_get(v_a_3770_, 0);
lean_inc(v_a_3781_);
lean_dec_ref(v_a_3770_);
v___x_3782_ = lean_box(0);
if (v_isShared_3767_ == 0)
{
lean_ctor_set(v___x_3766_, 1, v_a_3781_);
lean_ctor_set(v___x_3766_, 0, v___x_3782_);
v___x_3784_ = v___x_3766_;
goto v_reusejp_3783_;
}
else
{
lean_object* v_reuseFailAlloc_3788_; 
v_reuseFailAlloc_3788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3788_, 0, v___x_3782_);
lean_ctor_set(v_reuseFailAlloc_3788_, 1, v_a_3781_);
v___x_3784_ = v_reuseFailAlloc_3788_;
goto v_reusejp_3783_;
}
v_reusejp_3783_:
{
size_t v___x_3785_; size_t v___x_3786_; 
v___x_3785_ = ((size_t)1ULL);
v___x_3786_ = lean_usize_add(v_i_3755_, v___x_3785_);
v_i_3755_ = v___x_3786_;
v_b_3756_ = v___x_3784_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3790_; lean_object* v___x_3792_; uint8_t v_isShared_3793_; uint8_t v_isSharedCheck_3797_; 
lean_del_object(v___x_3766_);
lean_dec(v_snd_3764_);
lean_dec(v_mvarId_3751_);
lean_dec_ref(v_p_3750_);
v_a_3790_ = lean_ctor_get(v___x_3769_, 0);
v_isSharedCheck_3797_ = !lean_is_exclusive(v___x_3769_);
if (v_isSharedCheck_3797_ == 0)
{
v___x_3792_ = v___x_3769_;
v_isShared_3793_ = v_isSharedCheck_3797_;
goto v_resetjp_3791_;
}
else
{
lean_inc(v_a_3790_);
lean_dec(v___x_3769_);
v___x_3792_ = lean_box(0);
v_isShared_3793_ = v_isSharedCheck_3797_;
goto v_resetjp_3791_;
}
v_resetjp_3791_:
{
lean_object* v___x_3795_; 
if (v_isShared_3793_ == 0)
{
v___x_3795_ = v___x_3792_;
goto v_reusejp_3794_;
}
else
{
lean_object* v_reuseFailAlloc_3796_; 
v_reuseFailAlloc_3796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3796_, 0, v_a_3790_);
v___x_3795_ = v_reuseFailAlloc_3796_;
goto v_reusejp_3794_;
}
v_reusejp_3794_:
{
return v___x_3795_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__3___boxed(lean_object* v_p_3800_, lean_object* v_mvarId_3801_, lean_object* v_inh_3802_, lean_object* v_as_3803_, lean_object* v_sz_3804_, lean_object* v_i_3805_, lean_object* v_b_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_, lean_object* v___y_3811_){
_start:
{
size_t v_sz_boxed_3812_; size_t v_i_boxed_3813_; lean_object* v_res_3814_; 
v_sz_boxed_3812_ = lean_unbox_usize(v_sz_3804_);
lean_dec(v_sz_3804_);
v_i_boxed_3813_ = lean_unbox_usize(v_i_3805_);
lean_dec(v_i_3805_);
v_res_3814_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__3(v_p_3800_, v_mvarId_3801_, v_inh_3802_, v_as_3803_, v_sz_boxed_3812_, v_i_boxed_3813_, v_b_3806_, v___y_3807_, v___y_3808_, v___y_3809_, v___y_3810_);
lean_dec(v___y_3810_);
lean_dec_ref(v___y_3809_);
lean_dec(v___y_3808_);
lean_dec_ref(v___y_3807_);
lean_dec_ref(v_as_3803_);
lean_dec_ref(v_inh_3802_);
return v_res_3814_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2___boxed(lean_object* v_p_3815_, lean_object* v_mvarId_3816_, lean_object* v_inh_3817_, lean_object* v_n_3818_, lean_object* v_b_3819_, lean_object* v___y_3820_, lean_object* v___y_3821_, lean_object* v___y_3822_, lean_object* v___y_3823_, lean_object* v___y_3824_){
_start:
{
lean_object* v_res_3825_; 
v_res_3825_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2(v_p_3815_, v_mvarId_3816_, v_inh_3817_, v_n_3818_, v_b_3819_, v___y_3820_, v___y_3821_, v___y_3822_, v___y_3823_);
lean_dec(v___y_3823_);
lean_dec_ref(v___y_3822_);
lean_dec(v___y_3821_);
lean_dec_ref(v___y_3820_);
lean_dec_ref(v_inh_3817_);
return v_res_3825_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3_spec__6(lean_object* v_p_3829_, lean_object* v_mvarId_3830_, lean_object* v_as_3831_, size_t v_sz_3832_, size_t v_i_3833_, lean_object* v_b_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_, lean_object* v___y_3838_){
_start:
{
uint8_t v___x_3840_; 
v___x_3840_ = lean_usize_dec_lt(v_i_3833_, v_sz_3832_);
if (v___x_3840_ == 0)
{
lean_object* v___x_3841_; 
lean_dec(v_mvarId_3830_);
lean_dec_ref(v_p_3829_);
v___x_3841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3841_, 0, v_b_3834_);
return v___x_3841_;
}
else
{
lean_object* v_snd_3842_; lean_object* v___x_3844_; uint8_t v_isShared_3845_; uint8_t v_isSharedCheck_3909_; 
v_snd_3842_ = lean_ctor_get(v_b_3834_, 1);
v_isSharedCheck_3909_ = !lean_is_exclusive(v_b_3834_);
if (v_isSharedCheck_3909_ == 0)
{
lean_object* v_unused_3910_; 
v_unused_3910_ = lean_ctor_get(v_b_3834_, 0);
lean_dec(v_unused_3910_);
v___x_3844_ = v_b_3834_;
v_isShared_3845_ = v_isSharedCheck_3909_;
goto v_resetjp_3843_;
}
else
{
lean_inc(v_snd_3842_);
lean_dec(v_b_3834_);
v___x_3844_ = lean_box(0);
v_isShared_3845_ = v_isSharedCheck_3909_;
goto v_resetjp_3843_;
}
v_resetjp_3843_:
{
lean_object* v___x_3846_; lean_object* v_a_3848_; lean_object* v_a_3855_; 
v___x_3846_ = lean_box(0);
v_a_3855_ = lean_array_uget(v_as_3831_, v_i_3833_);
if (lean_obj_tag(v_a_3855_) == 0)
{
v_a_3848_ = v_snd_3842_;
goto v___jp_3847_;
}
else
{
lean_object* v_val_3856_; lean_object* v___x_3858_; uint8_t v_isShared_3859_; uint8_t v_isSharedCheck_3908_; 
v_val_3856_ = lean_ctor_get(v_a_3855_, 0);
v_isSharedCheck_3908_ = !lean_is_exclusive(v_a_3855_);
if (v_isSharedCheck_3908_ == 0)
{
v___x_3858_ = v_a_3855_;
v_isShared_3859_ = v_isSharedCheck_3908_;
goto v_resetjp_3857_;
}
else
{
lean_inc(v_val_3856_);
lean_dec(v_a_3855_);
v___x_3858_ = lean_box(0);
v_isShared_3859_ = v_isSharedCheck_3908_;
goto v_resetjp_3857_;
}
v_resetjp_3857_:
{
lean_object* v___x_3860_; 
lean_inc_ref(v_p_3829_);
lean_inc(v___y_3838_);
lean_inc_ref(v___y_3837_);
lean_inc(v___y_3836_);
lean_inc_ref(v___y_3835_);
lean_inc(v_val_3856_);
v___x_3860_ = lean_apply_6(v_p_3829_, v_val_3856_, v___y_3835_, v___y_3836_, v___y_3837_, v___y_3838_, lean_box(0));
if (lean_obj_tag(v___x_3860_) == 0)
{
lean_object* v_a_3861_; lean_object* v___x_3862_; lean_object* v___x_3863_; uint8_t v___x_3864_; 
v_a_3861_ = lean_ctor_get(v___x_3860_, 0);
lean_inc(v_a_3861_);
lean_dec_ref(v___x_3860_);
v___x_3862_ = lean_box(0);
v___x_3863_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3_spec__6___closed__0));
v___x_3864_ = lean_unbox(v_a_3861_);
lean_dec(v_a_3861_);
if (v___x_3864_ == 0)
{
lean_del_object(v___x_3858_);
lean_dec(v_val_3856_);
lean_dec(v_snd_3842_);
v_a_3848_ = v___x_3863_;
goto v___jp_3847_;
}
else
{
lean_object* v___x_3865_; lean_object* v___x_3866_; uint8_t v___x_3867_; lean_object* v___x_3868_; lean_object* v___f_3869_; lean_object* v___x_3870_; 
v___x_3865_ = l_Lean_LocalDecl_fvarId(v_val_3856_);
lean_dec(v_val_3856_);
v___x_3866_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5___closed__1));
v___x_3867_ = 0;
v___x_3868_ = lean_box(v___x_3867_);
lean_inc(v_mvarId_3830_);
v___f_3869_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3___lam__0___boxed), 10, 5);
lean_closure_set(v___f_3869_, 0, v_mvarId_3830_);
lean_closure_set(v___f_3869_, 1, v___x_3865_);
lean_closure_set(v___f_3869_, 2, v___x_3866_);
lean_closure_set(v___f_3869_, 3, v___x_3868_);
lean_closure_set(v___f_3869_, 4, v___x_3846_);
v___x_3870_ = l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1___redArg(v___f_3869_, v___y_3835_, v___y_3836_, v___y_3837_, v___y_3838_);
if (lean_obj_tag(v___x_3870_) == 0)
{
lean_object* v_a_3871_; lean_object* v___x_3873_; uint8_t v_isShared_3874_; uint8_t v_isSharedCheck_3891_; 
v_a_3871_ = lean_ctor_get(v___x_3870_, 0);
v_isSharedCheck_3891_ = !lean_is_exclusive(v___x_3870_);
if (v_isSharedCheck_3891_ == 0)
{
v___x_3873_ = v___x_3870_;
v_isShared_3874_ = v_isSharedCheck_3891_;
goto v_resetjp_3872_;
}
else
{
lean_inc(v_a_3871_);
lean_dec(v___x_3870_);
v___x_3873_ = lean_box(0);
v_isShared_3874_ = v_isSharedCheck_3891_;
goto v_resetjp_3872_;
}
v_resetjp_3872_:
{
if (lean_obj_tag(v_a_3871_) == 0)
{
lean_del_object(v___x_3873_);
lean_del_object(v___x_3858_);
lean_dec(v_snd_3842_);
v_a_3848_ = v___x_3863_;
goto v___jp_3847_;
}
else
{
lean_object* v___x_3876_; 
lean_del_object(v___x_3844_);
lean_dec(v_mvarId_3830_);
lean_dec_ref(v_p_3829_);
lean_inc_ref(v_a_3871_);
if (v_isShared_3859_ == 0)
{
lean_ctor_set(v___x_3858_, 0, v_a_3871_);
v___x_3876_ = v___x_3858_;
goto v_reusejp_3875_;
}
else
{
lean_object* v_reuseFailAlloc_3890_; 
v_reuseFailAlloc_3890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3890_, 0, v_a_3871_);
v___x_3876_ = v_reuseFailAlloc_3890_;
goto v_reusejp_3875_;
}
v_reusejp_3875_:
{
lean_object* v___x_3878_; uint8_t v_isShared_3879_; uint8_t v_isSharedCheck_3888_; 
v_isSharedCheck_3888_ = !lean_is_exclusive(v_a_3871_);
if (v_isSharedCheck_3888_ == 0)
{
lean_object* v_unused_3889_; 
v_unused_3889_ = lean_ctor_get(v_a_3871_, 0);
lean_dec(v_unused_3889_);
v___x_3878_ = v_a_3871_;
v_isShared_3879_ = v_isSharedCheck_3888_;
goto v_resetjp_3877_;
}
else
{
lean_dec(v_a_3871_);
v___x_3878_ = lean_box(0);
v_isShared_3879_ = v_isSharedCheck_3888_;
goto v_resetjp_3877_;
}
v_resetjp_3877_:
{
lean_object* v___x_3880_; lean_object* v___x_3882_; 
v___x_3880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3880_, 0, v___x_3876_);
lean_ctor_set(v___x_3880_, 1, v___x_3862_);
if (v_isShared_3879_ == 0)
{
lean_ctor_set(v___x_3878_, 0, v___x_3880_);
v___x_3882_ = v___x_3878_;
goto v_reusejp_3881_;
}
else
{
lean_object* v_reuseFailAlloc_3887_; 
v_reuseFailAlloc_3887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3887_, 0, v___x_3880_);
v___x_3882_ = v_reuseFailAlloc_3887_;
goto v_reusejp_3881_;
}
v_reusejp_3881_:
{
lean_object* v___x_3883_; lean_object* v___x_3885_; 
v___x_3883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3883_, 0, v___x_3882_);
lean_ctor_set(v___x_3883_, 1, v_snd_3842_);
if (v_isShared_3874_ == 0)
{
lean_ctor_set(v___x_3873_, 0, v___x_3883_);
v___x_3885_ = v___x_3873_;
goto v_reusejp_3884_;
}
else
{
lean_object* v_reuseFailAlloc_3886_; 
v_reuseFailAlloc_3886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3886_, 0, v___x_3883_);
v___x_3885_ = v_reuseFailAlloc_3886_;
goto v_reusejp_3884_;
}
v_reusejp_3884_:
{
return v___x_3885_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3892_; lean_object* v___x_3894_; uint8_t v_isShared_3895_; uint8_t v_isSharedCheck_3899_; 
lean_del_object(v___x_3858_);
lean_del_object(v___x_3844_);
lean_dec(v_snd_3842_);
lean_dec(v_mvarId_3830_);
lean_dec_ref(v_p_3829_);
v_a_3892_ = lean_ctor_get(v___x_3870_, 0);
v_isSharedCheck_3899_ = !lean_is_exclusive(v___x_3870_);
if (v_isSharedCheck_3899_ == 0)
{
v___x_3894_ = v___x_3870_;
v_isShared_3895_ = v_isSharedCheck_3899_;
goto v_resetjp_3893_;
}
else
{
lean_inc(v_a_3892_);
lean_dec(v___x_3870_);
v___x_3894_ = lean_box(0);
v_isShared_3895_ = v_isSharedCheck_3899_;
goto v_resetjp_3893_;
}
v_resetjp_3893_:
{
lean_object* v___x_3897_; 
if (v_isShared_3895_ == 0)
{
v___x_3897_ = v___x_3894_;
goto v_reusejp_3896_;
}
else
{
lean_object* v_reuseFailAlloc_3898_; 
v_reuseFailAlloc_3898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3898_, 0, v_a_3892_);
v___x_3897_ = v_reuseFailAlloc_3898_;
goto v_reusejp_3896_;
}
v_reusejp_3896_:
{
return v___x_3897_;
}
}
}
}
}
else
{
lean_object* v_a_3900_; lean_object* v___x_3902_; uint8_t v_isShared_3903_; uint8_t v_isSharedCheck_3907_; 
lean_del_object(v___x_3858_);
lean_dec(v_val_3856_);
lean_del_object(v___x_3844_);
lean_dec(v_snd_3842_);
lean_dec(v_mvarId_3830_);
lean_dec_ref(v_p_3829_);
v_a_3900_ = lean_ctor_get(v___x_3860_, 0);
v_isSharedCheck_3907_ = !lean_is_exclusive(v___x_3860_);
if (v_isSharedCheck_3907_ == 0)
{
v___x_3902_ = v___x_3860_;
v_isShared_3903_ = v_isSharedCheck_3907_;
goto v_resetjp_3901_;
}
else
{
lean_inc(v_a_3900_);
lean_dec(v___x_3860_);
v___x_3902_ = lean_box(0);
v_isShared_3903_ = v_isSharedCheck_3907_;
goto v_resetjp_3901_;
}
v_resetjp_3901_:
{
lean_object* v___x_3905_; 
if (v_isShared_3903_ == 0)
{
v___x_3905_ = v___x_3902_;
goto v_reusejp_3904_;
}
else
{
lean_object* v_reuseFailAlloc_3906_; 
v_reuseFailAlloc_3906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3906_, 0, v_a_3900_);
v___x_3905_ = v_reuseFailAlloc_3906_;
goto v_reusejp_3904_;
}
v_reusejp_3904_:
{
return v___x_3905_;
}
}
}
}
}
v___jp_3847_:
{
lean_object* v___x_3850_; 
if (v_isShared_3845_ == 0)
{
lean_ctor_set(v___x_3844_, 1, v_a_3848_);
lean_ctor_set(v___x_3844_, 0, v___x_3846_);
v___x_3850_ = v___x_3844_;
goto v_reusejp_3849_;
}
else
{
lean_object* v_reuseFailAlloc_3854_; 
v_reuseFailAlloc_3854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3854_, 0, v___x_3846_);
lean_ctor_set(v_reuseFailAlloc_3854_, 1, v_a_3848_);
v___x_3850_ = v_reuseFailAlloc_3854_;
goto v_reusejp_3849_;
}
v_reusejp_3849_:
{
size_t v___x_3851_; size_t v___x_3852_; 
v___x_3851_ = ((size_t)1ULL);
v___x_3852_ = lean_usize_add(v_i_3833_, v___x_3851_);
v_i_3833_ = v___x_3852_;
v_b_3834_ = v___x_3850_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3_spec__6___boxed(lean_object* v_p_3911_, lean_object* v_mvarId_3912_, lean_object* v_as_3913_, lean_object* v_sz_3914_, lean_object* v_i_3915_, lean_object* v_b_3916_, lean_object* v___y_3917_, lean_object* v___y_3918_, lean_object* v___y_3919_, lean_object* v___y_3920_, lean_object* v___y_3921_){
_start:
{
size_t v_sz_boxed_3922_; size_t v_i_boxed_3923_; lean_object* v_res_3924_; 
v_sz_boxed_3922_ = lean_unbox_usize(v_sz_3914_);
lean_dec(v_sz_3914_);
v_i_boxed_3923_ = lean_unbox_usize(v_i_3915_);
lean_dec(v_i_3915_);
v_res_3924_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3_spec__6(v_p_3911_, v_mvarId_3912_, v_as_3913_, v_sz_boxed_3922_, v_i_boxed_3923_, v_b_3916_, v___y_3917_, v___y_3918_, v___y_3919_, v___y_3920_);
lean_dec(v___y_3920_);
lean_dec_ref(v___y_3919_);
lean_dec(v___y_3918_);
lean_dec_ref(v___y_3917_);
lean_dec_ref(v_as_3913_);
return v_res_3924_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3(lean_object* v_p_3925_, lean_object* v_mvarId_3926_, lean_object* v_as_3927_, size_t v_sz_3928_, size_t v_i_3929_, lean_object* v_b_3930_, lean_object* v___y_3931_, lean_object* v___y_3932_, lean_object* v___y_3933_, lean_object* v___y_3934_){
_start:
{
uint8_t v___x_3936_; 
v___x_3936_ = lean_usize_dec_lt(v_i_3929_, v_sz_3928_);
if (v___x_3936_ == 0)
{
lean_object* v___x_3937_; 
lean_dec(v_mvarId_3926_);
lean_dec_ref(v_p_3925_);
v___x_3937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3937_, 0, v_b_3930_);
return v___x_3937_;
}
else
{
lean_object* v_snd_3938_; lean_object* v___x_3940_; uint8_t v_isShared_3941_; uint8_t v_isSharedCheck_4005_; 
v_snd_3938_ = lean_ctor_get(v_b_3930_, 1);
v_isSharedCheck_4005_ = !lean_is_exclusive(v_b_3930_);
if (v_isSharedCheck_4005_ == 0)
{
lean_object* v_unused_4006_; 
v_unused_4006_ = lean_ctor_get(v_b_3930_, 0);
lean_dec(v_unused_4006_);
v___x_3940_ = v_b_3930_;
v_isShared_3941_ = v_isSharedCheck_4005_;
goto v_resetjp_3939_;
}
else
{
lean_inc(v_snd_3938_);
lean_dec(v_b_3930_);
v___x_3940_ = lean_box(0);
v_isShared_3941_ = v_isSharedCheck_4005_;
goto v_resetjp_3939_;
}
v_resetjp_3939_:
{
lean_object* v___x_3942_; lean_object* v_a_3944_; lean_object* v_a_3951_; 
v___x_3942_ = lean_box(0);
v_a_3951_ = lean_array_uget(v_as_3927_, v_i_3929_);
if (lean_obj_tag(v_a_3951_) == 0)
{
v_a_3944_ = v_snd_3938_;
goto v___jp_3943_;
}
else
{
lean_object* v_val_3952_; lean_object* v___x_3954_; uint8_t v_isShared_3955_; uint8_t v_isSharedCheck_4004_; 
v_val_3952_ = lean_ctor_get(v_a_3951_, 0);
v_isSharedCheck_4004_ = !lean_is_exclusive(v_a_3951_);
if (v_isSharedCheck_4004_ == 0)
{
v___x_3954_ = v_a_3951_;
v_isShared_3955_ = v_isSharedCheck_4004_;
goto v_resetjp_3953_;
}
else
{
lean_inc(v_val_3952_);
lean_dec(v_a_3951_);
v___x_3954_ = lean_box(0);
v_isShared_3955_ = v_isSharedCheck_4004_;
goto v_resetjp_3953_;
}
v_resetjp_3953_:
{
lean_object* v___x_3956_; 
lean_inc_ref(v_p_3925_);
lean_inc(v___y_3934_);
lean_inc_ref(v___y_3933_);
lean_inc(v___y_3932_);
lean_inc_ref(v___y_3931_);
lean_inc(v_val_3952_);
v___x_3956_ = lean_apply_6(v_p_3925_, v_val_3952_, v___y_3931_, v___y_3932_, v___y_3933_, v___y_3934_, lean_box(0));
if (lean_obj_tag(v___x_3956_) == 0)
{
lean_object* v_a_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; uint8_t v___x_3960_; 
v_a_3957_ = lean_ctor_get(v___x_3956_, 0);
lean_inc(v_a_3957_);
lean_dec_ref(v___x_3956_);
v___x_3958_ = lean_box(0);
v___x_3959_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3_spec__6___closed__0));
v___x_3960_ = lean_unbox(v_a_3957_);
lean_dec(v_a_3957_);
if (v___x_3960_ == 0)
{
lean_del_object(v___x_3954_);
lean_dec(v_val_3952_);
lean_dec(v_snd_3938_);
v_a_3944_ = v___x_3959_;
goto v___jp_3943_;
}
else
{
lean_object* v___x_3961_; lean_object* v___x_3962_; uint8_t v___x_3963_; lean_object* v___x_3964_; lean_object* v___f_3965_; lean_object* v___x_3966_; 
v___x_3961_ = l_Lean_LocalDecl_fvarId(v_val_3952_);
lean_dec(v_val_3952_);
v___x_3962_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5___closed__1));
v___x_3963_ = 0;
v___x_3964_ = lean_box(v___x_3963_);
lean_inc(v_mvarId_3926_);
v___f_3965_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3___lam__0___boxed), 10, 5);
lean_closure_set(v___f_3965_, 0, v_mvarId_3926_);
lean_closure_set(v___f_3965_, 1, v___x_3961_);
lean_closure_set(v___f_3965_, 2, v___x_3962_);
lean_closure_set(v___f_3965_, 3, v___x_3964_);
lean_closure_set(v___f_3965_, 4, v___x_3942_);
v___x_3966_ = l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1___redArg(v___f_3965_, v___y_3931_, v___y_3932_, v___y_3933_, v___y_3934_);
if (lean_obj_tag(v___x_3966_) == 0)
{
lean_object* v_a_3967_; lean_object* v___x_3969_; uint8_t v_isShared_3970_; uint8_t v_isSharedCheck_3987_; 
v_a_3967_ = lean_ctor_get(v___x_3966_, 0);
v_isSharedCheck_3987_ = !lean_is_exclusive(v___x_3966_);
if (v_isSharedCheck_3987_ == 0)
{
v___x_3969_ = v___x_3966_;
v_isShared_3970_ = v_isSharedCheck_3987_;
goto v_resetjp_3968_;
}
else
{
lean_inc(v_a_3967_);
lean_dec(v___x_3966_);
v___x_3969_ = lean_box(0);
v_isShared_3970_ = v_isSharedCheck_3987_;
goto v_resetjp_3968_;
}
v_resetjp_3968_:
{
if (lean_obj_tag(v_a_3967_) == 0)
{
lean_del_object(v___x_3969_);
lean_del_object(v___x_3954_);
lean_dec(v_snd_3938_);
v_a_3944_ = v___x_3959_;
goto v___jp_3943_;
}
else
{
lean_object* v___x_3972_; 
lean_del_object(v___x_3940_);
lean_dec(v_mvarId_3926_);
lean_dec_ref(v_p_3925_);
lean_inc_ref(v_a_3967_);
if (v_isShared_3955_ == 0)
{
lean_ctor_set(v___x_3954_, 0, v_a_3967_);
v___x_3972_ = v___x_3954_;
goto v_reusejp_3971_;
}
else
{
lean_object* v_reuseFailAlloc_3986_; 
v_reuseFailAlloc_3986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3986_, 0, v_a_3967_);
v___x_3972_ = v_reuseFailAlloc_3986_;
goto v_reusejp_3971_;
}
v_reusejp_3971_:
{
lean_object* v___x_3974_; uint8_t v_isShared_3975_; uint8_t v_isSharedCheck_3984_; 
v_isSharedCheck_3984_ = !lean_is_exclusive(v_a_3967_);
if (v_isSharedCheck_3984_ == 0)
{
lean_object* v_unused_3985_; 
v_unused_3985_ = lean_ctor_get(v_a_3967_, 0);
lean_dec(v_unused_3985_);
v___x_3974_ = v_a_3967_;
v_isShared_3975_ = v_isSharedCheck_3984_;
goto v_resetjp_3973_;
}
else
{
lean_dec(v_a_3967_);
v___x_3974_ = lean_box(0);
v_isShared_3975_ = v_isSharedCheck_3984_;
goto v_resetjp_3973_;
}
v_resetjp_3973_:
{
lean_object* v___x_3976_; lean_object* v___x_3978_; 
v___x_3976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3976_, 0, v___x_3972_);
lean_ctor_set(v___x_3976_, 1, v___x_3958_);
if (v_isShared_3975_ == 0)
{
lean_ctor_set(v___x_3974_, 0, v___x_3976_);
v___x_3978_ = v___x_3974_;
goto v_reusejp_3977_;
}
else
{
lean_object* v_reuseFailAlloc_3983_; 
v_reuseFailAlloc_3983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3983_, 0, v___x_3976_);
v___x_3978_ = v_reuseFailAlloc_3983_;
goto v_reusejp_3977_;
}
v_reusejp_3977_:
{
lean_object* v___x_3979_; lean_object* v___x_3981_; 
v___x_3979_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3979_, 0, v___x_3978_);
lean_ctor_set(v___x_3979_, 1, v_snd_3938_);
if (v_isShared_3970_ == 0)
{
lean_ctor_set(v___x_3969_, 0, v___x_3979_);
v___x_3981_ = v___x_3969_;
goto v_reusejp_3980_;
}
else
{
lean_object* v_reuseFailAlloc_3982_; 
v_reuseFailAlloc_3982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3982_, 0, v___x_3979_);
v___x_3981_ = v_reuseFailAlloc_3982_;
goto v_reusejp_3980_;
}
v_reusejp_3980_:
{
return v___x_3981_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3988_; lean_object* v___x_3990_; uint8_t v_isShared_3991_; uint8_t v_isSharedCheck_3995_; 
lean_del_object(v___x_3954_);
lean_del_object(v___x_3940_);
lean_dec(v_snd_3938_);
lean_dec(v_mvarId_3926_);
lean_dec_ref(v_p_3925_);
v_a_3988_ = lean_ctor_get(v___x_3966_, 0);
v_isSharedCheck_3995_ = !lean_is_exclusive(v___x_3966_);
if (v_isSharedCheck_3995_ == 0)
{
v___x_3990_ = v___x_3966_;
v_isShared_3991_ = v_isSharedCheck_3995_;
goto v_resetjp_3989_;
}
else
{
lean_inc(v_a_3988_);
lean_dec(v___x_3966_);
v___x_3990_ = lean_box(0);
v_isShared_3991_ = v_isSharedCheck_3995_;
goto v_resetjp_3989_;
}
v_resetjp_3989_:
{
lean_object* v___x_3993_; 
if (v_isShared_3991_ == 0)
{
v___x_3993_ = v___x_3990_;
goto v_reusejp_3992_;
}
else
{
lean_object* v_reuseFailAlloc_3994_; 
v_reuseFailAlloc_3994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3994_, 0, v_a_3988_);
v___x_3993_ = v_reuseFailAlloc_3994_;
goto v_reusejp_3992_;
}
v_reusejp_3992_:
{
return v___x_3993_;
}
}
}
}
}
else
{
lean_object* v_a_3996_; lean_object* v___x_3998_; uint8_t v_isShared_3999_; uint8_t v_isSharedCheck_4003_; 
lean_del_object(v___x_3954_);
lean_dec(v_val_3952_);
lean_del_object(v___x_3940_);
lean_dec(v_snd_3938_);
lean_dec(v_mvarId_3926_);
lean_dec_ref(v_p_3925_);
v_a_3996_ = lean_ctor_get(v___x_3956_, 0);
v_isSharedCheck_4003_ = !lean_is_exclusive(v___x_3956_);
if (v_isSharedCheck_4003_ == 0)
{
v___x_3998_ = v___x_3956_;
v_isShared_3999_ = v_isSharedCheck_4003_;
goto v_resetjp_3997_;
}
else
{
lean_inc(v_a_3996_);
lean_dec(v___x_3956_);
v___x_3998_ = lean_box(0);
v_isShared_3999_ = v_isSharedCheck_4003_;
goto v_resetjp_3997_;
}
v_resetjp_3997_:
{
lean_object* v___x_4001_; 
if (v_isShared_3999_ == 0)
{
v___x_4001_ = v___x_3998_;
goto v_reusejp_4000_;
}
else
{
lean_object* v_reuseFailAlloc_4002_; 
v_reuseFailAlloc_4002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4002_, 0, v_a_3996_);
v___x_4001_ = v_reuseFailAlloc_4002_;
goto v_reusejp_4000_;
}
v_reusejp_4000_:
{
return v___x_4001_;
}
}
}
}
}
v___jp_3943_:
{
lean_object* v___x_3946_; 
if (v_isShared_3941_ == 0)
{
lean_ctor_set(v___x_3940_, 1, v_a_3944_);
lean_ctor_set(v___x_3940_, 0, v___x_3942_);
v___x_3946_ = v___x_3940_;
goto v_reusejp_3945_;
}
else
{
lean_object* v_reuseFailAlloc_3950_; 
v_reuseFailAlloc_3950_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3950_, 0, v___x_3942_);
lean_ctor_set(v_reuseFailAlloc_3950_, 1, v_a_3944_);
v___x_3946_ = v_reuseFailAlloc_3950_;
goto v_reusejp_3945_;
}
v_reusejp_3945_:
{
size_t v___x_3947_; size_t v___x_3948_; lean_object* v___x_3949_; 
v___x_3947_ = ((size_t)1ULL);
v___x_3948_ = lean_usize_add(v_i_3929_, v___x_3947_);
v___x_3949_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3_spec__6(v_p_3925_, v_mvarId_3926_, v_as_3927_, v_sz_3928_, v___x_3948_, v___x_3946_, v___y_3931_, v___y_3932_, v___y_3933_, v___y_3934_);
return v___x_3949_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3___boxed(lean_object* v_p_4007_, lean_object* v_mvarId_4008_, lean_object* v_as_4009_, lean_object* v_sz_4010_, lean_object* v_i_4011_, lean_object* v_b_4012_, lean_object* v___y_4013_, lean_object* v___y_4014_, lean_object* v___y_4015_, lean_object* v___y_4016_, lean_object* v___y_4017_){
_start:
{
size_t v_sz_boxed_4018_; size_t v_i_boxed_4019_; lean_object* v_res_4020_; 
v_sz_boxed_4018_ = lean_unbox_usize(v_sz_4010_);
lean_dec(v_sz_4010_);
v_i_boxed_4019_ = lean_unbox_usize(v_i_4011_);
lean_dec(v_i_4011_);
v_res_4020_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3(v_p_4007_, v_mvarId_4008_, v_as_4009_, v_sz_boxed_4018_, v_i_boxed_4019_, v_b_4012_, v___y_4013_, v___y_4014_, v___y_4015_, v___y_4016_);
lean_dec(v___y_4016_);
lean_dec_ref(v___y_4015_);
lean_dec(v___y_4014_);
lean_dec_ref(v___y_4013_);
lean_dec_ref(v_as_4009_);
return v_res_4020_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2(lean_object* v_p_4021_, lean_object* v_mvarId_4022_, lean_object* v_t_4023_, lean_object* v_init_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_, lean_object* v___y_4027_, lean_object* v___y_4028_){
_start:
{
lean_object* v_root_4030_; lean_object* v_tail_4031_; lean_object* v___x_4032_; 
v_root_4030_ = lean_ctor_get(v_t_4023_, 0);
lean_inc_ref(v_root_4030_);
v_tail_4031_ = lean_ctor_get(v_t_4023_, 1);
lean_inc_ref(v_tail_4031_);
lean_dec_ref(v_t_4023_);
lean_inc_ref(v_init_4024_);
lean_inc(v_mvarId_4022_);
lean_inc_ref(v_p_4021_);
v___x_4032_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2(v_p_4021_, v_mvarId_4022_, v_init_4024_, v_root_4030_, v_init_4024_, v___y_4025_, v___y_4026_, v___y_4027_, v___y_4028_);
lean_dec_ref(v_init_4024_);
if (lean_obj_tag(v___x_4032_) == 0)
{
lean_object* v_a_4033_; lean_object* v___x_4035_; uint8_t v_isShared_4036_; uint8_t v_isSharedCheck_4069_; 
v_a_4033_ = lean_ctor_get(v___x_4032_, 0);
v_isSharedCheck_4069_ = !lean_is_exclusive(v___x_4032_);
if (v_isSharedCheck_4069_ == 0)
{
v___x_4035_ = v___x_4032_;
v_isShared_4036_ = v_isSharedCheck_4069_;
goto v_resetjp_4034_;
}
else
{
lean_inc(v_a_4033_);
lean_dec(v___x_4032_);
v___x_4035_ = lean_box(0);
v_isShared_4036_ = v_isSharedCheck_4069_;
goto v_resetjp_4034_;
}
v_resetjp_4034_:
{
if (lean_obj_tag(v_a_4033_) == 0)
{
lean_object* v_a_4037_; lean_object* v___x_4039_; 
lean_dec_ref(v_tail_4031_);
lean_dec(v_mvarId_4022_);
lean_dec_ref(v_p_4021_);
v_a_4037_ = lean_ctor_get(v_a_4033_, 0);
lean_inc(v_a_4037_);
lean_dec_ref(v_a_4033_);
if (v_isShared_4036_ == 0)
{
lean_ctor_set(v___x_4035_, 0, v_a_4037_);
v___x_4039_ = v___x_4035_;
goto v_reusejp_4038_;
}
else
{
lean_object* v_reuseFailAlloc_4040_; 
v_reuseFailAlloc_4040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4040_, 0, v_a_4037_);
v___x_4039_ = v_reuseFailAlloc_4040_;
goto v_reusejp_4038_;
}
v_reusejp_4038_:
{
return v___x_4039_;
}
}
else
{
lean_object* v_a_4041_; lean_object* v___x_4042_; lean_object* v___x_4043_; size_t v_sz_4044_; size_t v___x_4045_; lean_object* v___x_4046_; 
lean_del_object(v___x_4035_);
v_a_4041_ = lean_ctor_get(v_a_4033_, 0);
lean_inc(v_a_4041_);
lean_dec_ref(v_a_4033_);
v___x_4042_ = lean_box(0);
v___x_4043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4043_, 0, v___x_4042_);
lean_ctor_set(v___x_4043_, 1, v_a_4041_);
v_sz_4044_ = lean_array_size(v_tail_4031_);
v___x_4045_ = ((size_t)0ULL);
v___x_4046_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3(v_p_4021_, v_mvarId_4022_, v_tail_4031_, v_sz_4044_, v___x_4045_, v___x_4043_, v___y_4025_, v___y_4026_, v___y_4027_, v___y_4028_);
lean_dec_ref(v_tail_4031_);
if (lean_obj_tag(v___x_4046_) == 0)
{
lean_object* v_a_4047_; lean_object* v___x_4049_; uint8_t v_isShared_4050_; uint8_t v_isSharedCheck_4060_; 
v_a_4047_ = lean_ctor_get(v___x_4046_, 0);
v_isSharedCheck_4060_ = !lean_is_exclusive(v___x_4046_);
if (v_isSharedCheck_4060_ == 0)
{
v___x_4049_ = v___x_4046_;
v_isShared_4050_ = v_isSharedCheck_4060_;
goto v_resetjp_4048_;
}
else
{
lean_inc(v_a_4047_);
lean_dec(v___x_4046_);
v___x_4049_ = lean_box(0);
v_isShared_4050_ = v_isSharedCheck_4060_;
goto v_resetjp_4048_;
}
v_resetjp_4048_:
{
lean_object* v_fst_4051_; 
v_fst_4051_ = lean_ctor_get(v_a_4047_, 0);
if (lean_obj_tag(v_fst_4051_) == 0)
{
lean_object* v_snd_4052_; lean_object* v___x_4054_; 
v_snd_4052_ = lean_ctor_get(v_a_4047_, 1);
lean_inc(v_snd_4052_);
lean_dec(v_a_4047_);
if (v_isShared_4050_ == 0)
{
lean_ctor_set(v___x_4049_, 0, v_snd_4052_);
v___x_4054_ = v___x_4049_;
goto v_reusejp_4053_;
}
else
{
lean_object* v_reuseFailAlloc_4055_; 
v_reuseFailAlloc_4055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4055_, 0, v_snd_4052_);
v___x_4054_ = v_reuseFailAlloc_4055_;
goto v_reusejp_4053_;
}
v_reusejp_4053_:
{
return v___x_4054_;
}
}
else
{
lean_object* v_val_4056_; lean_object* v___x_4058_; 
lean_inc_ref(v_fst_4051_);
lean_dec(v_a_4047_);
v_val_4056_ = lean_ctor_get(v_fst_4051_, 0);
lean_inc(v_val_4056_);
lean_dec_ref(v_fst_4051_);
if (v_isShared_4050_ == 0)
{
lean_ctor_set(v___x_4049_, 0, v_val_4056_);
v___x_4058_ = v___x_4049_;
goto v_reusejp_4057_;
}
else
{
lean_object* v_reuseFailAlloc_4059_; 
v_reuseFailAlloc_4059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4059_, 0, v_val_4056_);
v___x_4058_ = v_reuseFailAlloc_4059_;
goto v_reusejp_4057_;
}
v_reusejp_4057_:
{
return v___x_4058_;
}
}
}
}
else
{
lean_object* v_a_4061_; lean_object* v___x_4063_; uint8_t v_isShared_4064_; uint8_t v_isSharedCheck_4068_; 
v_a_4061_ = lean_ctor_get(v___x_4046_, 0);
v_isSharedCheck_4068_ = !lean_is_exclusive(v___x_4046_);
if (v_isSharedCheck_4068_ == 0)
{
v___x_4063_ = v___x_4046_;
v_isShared_4064_ = v_isSharedCheck_4068_;
goto v_resetjp_4062_;
}
else
{
lean_inc(v_a_4061_);
lean_dec(v___x_4046_);
v___x_4063_ = lean_box(0);
v_isShared_4064_ = v_isSharedCheck_4068_;
goto v_resetjp_4062_;
}
v_resetjp_4062_:
{
lean_object* v___x_4066_; 
if (v_isShared_4064_ == 0)
{
v___x_4066_ = v___x_4063_;
goto v_reusejp_4065_;
}
else
{
lean_object* v_reuseFailAlloc_4067_; 
v_reuseFailAlloc_4067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4067_, 0, v_a_4061_);
v___x_4066_ = v_reuseFailAlloc_4067_;
goto v_reusejp_4065_;
}
v_reusejp_4065_:
{
return v___x_4066_;
}
}
}
}
}
}
else
{
lean_object* v_a_4070_; lean_object* v___x_4072_; uint8_t v_isShared_4073_; uint8_t v_isSharedCheck_4077_; 
lean_dec_ref(v_tail_4031_);
lean_dec(v_mvarId_4022_);
lean_dec_ref(v_p_4021_);
v_a_4070_ = lean_ctor_get(v___x_4032_, 0);
v_isSharedCheck_4077_ = !lean_is_exclusive(v___x_4032_);
if (v_isSharedCheck_4077_ == 0)
{
v___x_4072_ = v___x_4032_;
v_isShared_4073_ = v_isSharedCheck_4077_;
goto v_resetjp_4071_;
}
else
{
lean_inc(v_a_4070_);
lean_dec(v___x_4032_);
v___x_4072_ = lean_box(0);
v_isShared_4073_ = v_isSharedCheck_4077_;
goto v_resetjp_4071_;
}
v_resetjp_4071_:
{
lean_object* v___x_4075_; 
if (v_isShared_4073_ == 0)
{
v___x_4075_ = v___x_4072_;
goto v_reusejp_4074_;
}
else
{
lean_object* v_reuseFailAlloc_4076_; 
v_reuseFailAlloc_4076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4076_, 0, v_a_4070_);
v___x_4075_ = v_reuseFailAlloc_4076_;
goto v_reusejp_4074_;
}
v_reusejp_4074_:
{
return v___x_4075_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2___boxed(lean_object* v_p_4078_, lean_object* v_mvarId_4079_, lean_object* v_t_4080_, lean_object* v_init_4081_, lean_object* v___y_4082_, lean_object* v___y_4083_, lean_object* v___y_4084_, lean_object* v___y_4085_, lean_object* v___y_4086_){
_start:
{
lean_object* v_res_4087_; 
v_res_4087_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2(v_p_4078_, v_mvarId_4079_, v_t_4080_, v_init_4081_, v___y_4082_, v___y_4083_, v___y_4084_, v___y_4085_);
lean_dec(v___y_4085_);
lean_dec_ref(v___y_4084_);
lean_dec(v___y_4083_);
lean_dec_ref(v___y_4082_);
return v_res_4087_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesRec___lam__0(lean_object* v_p_4091_, lean_object* v_mvarId_4092_, lean_object* v___y_4093_, lean_object* v___y_4094_, lean_object* v___y_4095_, lean_object* v___y_4096_){
_start:
{
lean_object* v_lctx_4098_; lean_object* v_decls_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; 
v_lctx_4098_ = lean_ctor_get(v___y_4093_, 2);
v_decls_4099_ = lean_ctor_get(v_lctx_4098_, 1);
lean_inc_ref(v_decls_4099_);
v___x_4100_ = lean_box(0);
v___x_4101_ = ((lean_object*)(l_Lean_MVarId_casesRec___lam__0___closed__0));
v___x_4102_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2(v_p_4091_, v_mvarId_4092_, v_decls_4099_, v___x_4101_, v___y_4093_, v___y_4094_, v___y_4095_, v___y_4096_);
lean_dec_ref(v___y_4093_);
if (lean_obj_tag(v___x_4102_) == 0)
{
lean_object* v_a_4103_; lean_object* v___x_4105_; uint8_t v_isShared_4106_; uint8_t v_isSharedCheck_4115_; 
v_a_4103_ = lean_ctor_get(v___x_4102_, 0);
v_isSharedCheck_4115_ = !lean_is_exclusive(v___x_4102_);
if (v_isSharedCheck_4115_ == 0)
{
v___x_4105_ = v___x_4102_;
v_isShared_4106_ = v_isSharedCheck_4115_;
goto v_resetjp_4104_;
}
else
{
lean_inc(v_a_4103_);
lean_dec(v___x_4102_);
v___x_4105_ = lean_box(0);
v_isShared_4106_ = v_isSharedCheck_4115_;
goto v_resetjp_4104_;
}
v_resetjp_4104_:
{
lean_object* v_fst_4107_; 
v_fst_4107_ = lean_ctor_get(v_a_4103_, 0);
lean_inc(v_fst_4107_);
lean_dec(v_a_4103_);
if (lean_obj_tag(v_fst_4107_) == 0)
{
lean_object* v___x_4109_; 
if (v_isShared_4106_ == 0)
{
lean_ctor_set(v___x_4105_, 0, v___x_4100_);
v___x_4109_ = v___x_4105_;
goto v_reusejp_4108_;
}
else
{
lean_object* v_reuseFailAlloc_4110_; 
v_reuseFailAlloc_4110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4110_, 0, v___x_4100_);
v___x_4109_ = v_reuseFailAlloc_4110_;
goto v_reusejp_4108_;
}
v_reusejp_4108_:
{
return v___x_4109_;
}
}
else
{
lean_object* v_val_4111_; lean_object* v___x_4113_; 
v_val_4111_ = lean_ctor_get(v_fst_4107_, 0);
lean_inc(v_val_4111_);
lean_dec_ref(v_fst_4107_);
if (v_isShared_4106_ == 0)
{
lean_ctor_set(v___x_4105_, 0, v_val_4111_);
v___x_4113_ = v___x_4105_;
goto v_reusejp_4112_;
}
else
{
lean_object* v_reuseFailAlloc_4114_; 
v_reuseFailAlloc_4114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4114_, 0, v_val_4111_);
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
else
{
lean_object* v_a_4116_; lean_object* v___x_4118_; uint8_t v_isShared_4119_; uint8_t v_isSharedCheck_4123_; 
v_a_4116_ = lean_ctor_get(v___x_4102_, 0);
v_isSharedCheck_4123_ = !lean_is_exclusive(v___x_4102_);
if (v_isSharedCheck_4123_ == 0)
{
v___x_4118_ = v___x_4102_;
v_isShared_4119_ = v_isSharedCheck_4123_;
goto v_resetjp_4117_;
}
else
{
lean_inc(v_a_4116_);
lean_dec(v___x_4102_);
v___x_4118_ = lean_box(0);
v_isShared_4119_ = v_isSharedCheck_4123_;
goto v_resetjp_4117_;
}
v_resetjp_4117_:
{
lean_object* v___x_4121_; 
if (v_isShared_4119_ == 0)
{
v___x_4121_ = v___x_4118_;
goto v_reusejp_4120_;
}
else
{
lean_object* v_reuseFailAlloc_4122_; 
v_reuseFailAlloc_4122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4122_, 0, v_a_4116_);
v___x_4121_ = v_reuseFailAlloc_4122_;
goto v_reusejp_4120_;
}
v_reusejp_4120_:
{
return v___x_4121_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesRec___lam__0___boxed(lean_object* v_p_4124_, lean_object* v_mvarId_4125_, lean_object* v___y_4126_, lean_object* v___y_4127_, lean_object* v___y_4128_, lean_object* v___y_4129_, lean_object* v___y_4130_){
_start:
{
lean_object* v_res_4131_; 
v_res_4131_ = l_Lean_MVarId_casesRec___lam__0(v_p_4124_, v_mvarId_4125_, v___y_4126_, v___y_4127_, v___y_4128_, v___y_4129_);
lean_dec(v___y_4129_);
lean_dec_ref(v___y_4128_);
lean_dec(v___y_4127_);
return v_res_4131_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesRec___lam__1(lean_object* v_p_4132_, lean_object* v_mvarId_4133_, lean_object* v___y_4134_, lean_object* v___y_4135_, lean_object* v___y_4136_, lean_object* v___y_4137_){
_start:
{
lean_object* v___f_4139_; lean_object* v___x_4140_; 
lean_inc(v_mvarId_4133_);
v___f_4139_ = lean_alloc_closure((void*)(l_Lean_MVarId_casesRec___lam__0___boxed), 7, 2);
lean_closure_set(v___f_4139_, 0, v_p_4132_);
lean_closure_set(v___f_4139_, 1, v_mvarId_4133_);
v___x_4140_ = l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2___redArg(v_mvarId_4133_, v___f_4139_, v___y_4134_, v___y_4135_, v___y_4136_, v___y_4137_);
return v___x_4140_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesRec___lam__1___boxed(lean_object* v_p_4141_, lean_object* v_mvarId_4142_, lean_object* v___y_4143_, lean_object* v___y_4144_, lean_object* v___y_4145_, lean_object* v___y_4146_, lean_object* v___y_4147_){
_start:
{
lean_object* v_res_4148_; 
v_res_4148_ = l_Lean_MVarId_casesRec___lam__1(v_p_4141_, v_mvarId_4142_, v___y_4143_, v___y_4144_, v___y_4145_, v___y_4146_);
lean_dec(v___y_4146_);
lean_dec_ref(v___y_4145_);
lean_dec(v___y_4144_);
lean_dec_ref(v___y_4143_);
return v_res_4148_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesRec(lean_object* v_mvarId_4149_, lean_object* v_p_4150_, lean_object* v_a_4151_, lean_object* v_a_4152_, lean_object* v_a_4153_, lean_object* v_a_4154_){
_start:
{
lean_object* v___f_4156_; lean_object* v___x_4157_; 
v___f_4156_ = lean_alloc_closure((void*)(l_Lean_MVarId_casesRec___lam__1___boxed), 7, 1);
lean_closure_set(v___f_4156_, 0, v_p_4150_);
v___x_4157_ = l_Lean_Meta_saturate(v_mvarId_4149_, v___f_4156_, v_a_4151_, v_a_4152_, v_a_4153_, v_a_4154_);
return v___x_4157_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesRec___boxed(lean_object* v_mvarId_4158_, lean_object* v_p_4159_, lean_object* v_a_4160_, lean_object* v_a_4161_, lean_object* v_a_4162_, lean_object* v_a_4163_, lean_object* v_a_4164_){
_start:
{
lean_object* v_res_4165_; 
v_res_4165_ = l_Lean_MVarId_casesRec(v_mvarId_4158_, v_p_4159_, v_a_4160_, v_a_4161_, v_a_4162_, v_a_4163_);
lean_dec(v_a_4163_);
lean_dec_ref(v_a_4162_);
lean_dec(v_a_4161_);
lean_dec_ref(v_a_4160_);
return v_res_4165_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0___redArg(lean_object* v_e_4166_, lean_object* v___y_4167_){
_start:
{
uint8_t v___x_4169_; 
v___x_4169_ = l_Lean_Expr_hasMVar(v_e_4166_);
if (v___x_4169_ == 0)
{
lean_object* v___x_4170_; 
v___x_4170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4170_, 0, v_e_4166_);
return v___x_4170_;
}
else
{
lean_object* v___x_4171_; lean_object* v_mctx_4172_; lean_object* v___x_4173_; lean_object* v_fst_4174_; lean_object* v_snd_4175_; lean_object* v___x_4176_; lean_object* v_cache_4177_; lean_object* v_zetaDeltaFVarIds_4178_; lean_object* v_postponed_4179_; lean_object* v_diag_4180_; lean_object* v___x_4182_; uint8_t v_isShared_4183_; uint8_t v_isSharedCheck_4189_; 
v___x_4171_ = lean_st_ref_get(v___y_4167_);
v_mctx_4172_ = lean_ctor_get(v___x_4171_, 0);
lean_inc_ref(v_mctx_4172_);
lean_dec(v___x_4171_);
v___x_4173_ = l_Lean_instantiateMVarsCore(v_mctx_4172_, v_e_4166_);
v_fst_4174_ = lean_ctor_get(v___x_4173_, 0);
lean_inc(v_fst_4174_);
v_snd_4175_ = lean_ctor_get(v___x_4173_, 1);
lean_inc(v_snd_4175_);
lean_dec_ref(v___x_4173_);
v___x_4176_ = lean_st_ref_take(v___y_4167_);
v_cache_4177_ = lean_ctor_get(v___x_4176_, 1);
v_zetaDeltaFVarIds_4178_ = lean_ctor_get(v___x_4176_, 2);
v_postponed_4179_ = lean_ctor_get(v___x_4176_, 3);
v_diag_4180_ = lean_ctor_get(v___x_4176_, 4);
v_isSharedCheck_4189_ = !lean_is_exclusive(v___x_4176_);
if (v_isSharedCheck_4189_ == 0)
{
lean_object* v_unused_4190_; 
v_unused_4190_ = lean_ctor_get(v___x_4176_, 0);
lean_dec(v_unused_4190_);
v___x_4182_ = v___x_4176_;
v_isShared_4183_ = v_isSharedCheck_4189_;
goto v_resetjp_4181_;
}
else
{
lean_inc(v_diag_4180_);
lean_inc(v_postponed_4179_);
lean_inc(v_zetaDeltaFVarIds_4178_);
lean_inc(v_cache_4177_);
lean_dec(v___x_4176_);
v___x_4182_ = lean_box(0);
v_isShared_4183_ = v_isSharedCheck_4189_;
goto v_resetjp_4181_;
}
v_resetjp_4181_:
{
lean_object* v___x_4185_; 
if (v_isShared_4183_ == 0)
{
lean_ctor_set(v___x_4182_, 0, v_snd_4175_);
v___x_4185_ = v___x_4182_;
goto v_reusejp_4184_;
}
else
{
lean_object* v_reuseFailAlloc_4188_; 
v_reuseFailAlloc_4188_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4188_, 0, v_snd_4175_);
lean_ctor_set(v_reuseFailAlloc_4188_, 1, v_cache_4177_);
lean_ctor_set(v_reuseFailAlloc_4188_, 2, v_zetaDeltaFVarIds_4178_);
lean_ctor_set(v_reuseFailAlloc_4188_, 3, v_postponed_4179_);
lean_ctor_set(v_reuseFailAlloc_4188_, 4, v_diag_4180_);
v___x_4185_ = v_reuseFailAlloc_4188_;
goto v_reusejp_4184_;
}
v_reusejp_4184_:
{
lean_object* v___x_4186_; lean_object* v___x_4187_; 
v___x_4186_ = lean_st_ref_set(v___y_4167_, v___x_4185_);
v___x_4187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4187_, 0, v_fst_4174_);
return v___x_4187_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0___redArg___boxed(lean_object* v_e_4191_, lean_object* v___y_4192_, lean_object* v___y_4193_){
_start:
{
lean_object* v_res_4194_; 
v_res_4194_ = l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0___redArg(v_e_4191_, v___y_4192_);
lean_dec(v___y_4192_);
return v_res_4194_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0(lean_object* v_e_4195_, lean_object* v___y_4196_, lean_object* v___y_4197_, lean_object* v___y_4198_, lean_object* v___y_4199_){
_start:
{
lean_object* v___x_4201_; 
v___x_4201_ = l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0___redArg(v_e_4195_, v___y_4197_);
return v___x_4201_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0___boxed(lean_object* v_e_4202_, lean_object* v___y_4203_, lean_object* v___y_4204_, lean_object* v___y_4205_, lean_object* v___y_4206_, lean_object* v___y_4207_){
_start:
{
lean_object* v_res_4208_; 
v_res_4208_ = l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0(v_e_4202_, v___y_4203_, v___y_4204_, v___y_4205_, v___y_4206_);
lean_dec(v___y_4206_);
lean_dec_ref(v___y_4205_);
lean_dec(v___y_4204_);
lean_dec_ref(v___y_4203_);
return v_res_4208_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesAnd___lam__0(lean_object* v_localDecl_4212_, lean_object* v___y_4213_, lean_object* v___y_4214_, lean_object* v___y_4215_, lean_object* v___y_4216_){
_start:
{
lean_object* v___x_4218_; lean_object* v___x_4219_; lean_object* v_a_4220_; lean_object* v___x_4222_; uint8_t v_isShared_4223_; uint8_t v_isSharedCheck_4231_; 
v___x_4218_ = l_Lean_LocalDecl_type(v_localDecl_4212_);
v___x_4219_ = l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0___redArg(v___x_4218_, v___y_4214_);
v_a_4220_ = lean_ctor_get(v___x_4219_, 0);
v_isSharedCheck_4231_ = !lean_is_exclusive(v___x_4219_);
if (v_isSharedCheck_4231_ == 0)
{
v___x_4222_ = v___x_4219_;
v_isShared_4223_ = v_isSharedCheck_4231_;
goto v_resetjp_4221_;
}
else
{
lean_inc(v_a_4220_);
lean_dec(v___x_4219_);
v___x_4222_ = lean_box(0);
v_isShared_4223_ = v_isSharedCheck_4231_;
goto v_resetjp_4221_;
}
v_resetjp_4221_:
{
lean_object* v___x_4224_; lean_object* v___x_4225_; uint8_t v___x_4226_; lean_object* v___x_4227_; lean_object* v___x_4229_; 
v___x_4224_ = ((lean_object*)(l_Lean_MVarId_casesAnd___lam__0___closed__1));
v___x_4225_ = lean_unsigned_to_nat(2u);
v___x_4226_ = l_Lean_Expr_isAppOfArity(v_a_4220_, v___x_4224_, v___x_4225_);
lean_dec(v_a_4220_);
v___x_4227_ = lean_box(v___x_4226_);
if (v_isShared_4223_ == 0)
{
lean_ctor_set(v___x_4222_, 0, v___x_4227_);
v___x_4229_ = v___x_4222_;
goto v_reusejp_4228_;
}
else
{
lean_object* v_reuseFailAlloc_4230_; 
v_reuseFailAlloc_4230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4230_, 0, v___x_4227_);
v___x_4229_ = v_reuseFailAlloc_4230_;
goto v_reusejp_4228_;
}
v_reusejp_4228_:
{
return v___x_4229_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesAnd___lam__0___boxed(lean_object* v_localDecl_4232_, lean_object* v___y_4233_, lean_object* v___y_4234_, lean_object* v___y_4235_, lean_object* v___y_4236_, lean_object* v___y_4237_){
_start:
{
lean_object* v_res_4238_; 
v_res_4238_ = l_Lean_MVarId_casesAnd___lam__0(v_localDecl_4232_, v___y_4233_, v___y_4234_, v___y_4235_, v___y_4236_);
lean_dec(v___y_4236_);
lean_dec_ref(v___y_4235_);
lean_dec(v___y_4234_);
lean_dec_ref(v___y_4233_);
lean_dec_ref(v_localDecl_4232_);
return v_res_4238_;
}
}
static lean_object* _init_l_Lean_MVarId_casesAnd___closed__3(void){
_start:
{
lean_object* v___x_4243_; lean_object* v___x_4244_; 
v___x_4243_ = ((lean_object*)(l_Lean_MVarId_casesAnd___closed__2));
v___x_4244_ = l_Lean_MessageData_ofFormat(v___x_4243_);
return v___x_4244_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesAnd(lean_object* v_mvarId_4245_, lean_object* v_a_4246_, lean_object* v_a_4247_, lean_object* v_a_4248_, lean_object* v_a_4249_){
_start:
{
lean_object* v___f_4251_; lean_object* v___x_4252_; 
v___f_4251_ = ((lean_object*)(l_Lean_MVarId_casesAnd___closed__0));
v___x_4252_ = l_Lean_MVarId_casesRec(v_mvarId_4245_, v___f_4251_, v_a_4246_, v_a_4247_, v_a_4248_, v_a_4249_);
if (lean_obj_tag(v___x_4252_) == 0)
{
lean_object* v_a_4253_; lean_object* v___x_4254_; lean_object* v___x_4255_; 
v_a_4253_ = lean_ctor_get(v___x_4252_, 0);
lean_inc(v_a_4253_);
lean_dec_ref(v___x_4252_);
v___x_4254_ = lean_obj_once(&l_Lean_MVarId_casesAnd___closed__3, &l_Lean_MVarId_casesAnd___closed__3_once, _init_l_Lean_MVarId_casesAnd___closed__3);
v___x_4255_ = l_Lean_Meta_exactlyOne(v_a_4253_, v___x_4254_, v_a_4246_, v_a_4247_, v_a_4248_, v_a_4249_);
lean_dec(v_a_4253_);
return v___x_4255_;
}
else
{
lean_object* v_a_4256_; lean_object* v___x_4258_; uint8_t v_isShared_4259_; uint8_t v_isSharedCheck_4263_; 
v_a_4256_ = lean_ctor_get(v___x_4252_, 0);
v_isSharedCheck_4263_ = !lean_is_exclusive(v___x_4252_);
if (v_isSharedCheck_4263_ == 0)
{
v___x_4258_ = v___x_4252_;
v_isShared_4259_ = v_isSharedCheck_4263_;
goto v_resetjp_4257_;
}
else
{
lean_inc(v_a_4256_);
lean_dec(v___x_4252_);
v___x_4258_ = lean_box(0);
v_isShared_4259_ = v_isSharedCheck_4263_;
goto v_resetjp_4257_;
}
v_resetjp_4257_:
{
lean_object* v___x_4261_; 
if (v_isShared_4259_ == 0)
{
v___x_4261_ = v___x_4258_;
goto v_reusejp_4260_;
}
else
{
lean_object* v_reuseFailAlloc_4262_; 
v_reuseFailAlloc_4262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4262_, 0, v_a_4256_);
v___x_4261_ = v_reuseFailAlloc_4262_;
goto v_reusejp_4260_;
}
v_reusejp_4260_:
{
return v___x_4261_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesAnd___boxed(lean_object* v_mvarId_4264_, lean_object* v_a_4265_, lean_object* v_a_4266_, lean_object* v_a_4267_, lean_object* v_a_4268_, lean_object* v_a_4269_){
_start:
{
lean_object* v_res_4270_; 
v_res_4270_ = l_Lean_MVarId_casesAnd(v_mvarId_4264_, v_a_4265_, v_a_4266_, v_a_4267_, v_a_4268_);
lean_dec(v_a_4268_);
lean_dec_ref(v_a_4267_);
lean_dec(v_a_4266_);
lean_dec_ref(v_a_4265_);
return v_res_4270_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_substEqs___lam__0(lean_object* v_localDecl_4271_, lean_object* v___y_4272_, lean_object* v___y_4273_, lean_object* v___y_4274_, lean_object* v___y_4275_){
_start:
{
lean_object* v___x_4277_; lean_object* v___x_4278_; lean_object* v_a_4279_; lean_object* v___x_4281_; uint8_t v_isShared_4282_; uint8_t v_isSharedCheck_4293_; 
v___x_4277_ = l_Lean_LocalDecl_type(v_localDecl_4271_);
v___x_4278_ = l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0___redArg(v___x_4277_, v___y_4273_);
v_a_4279_ = lean_ctor_get(v___x_4278_, 0);
v_isSharedCheck_4293_ = !lean_is_exclusive(v___x_4278_);
if (v_isSharedCheck_4293_ == 0)
{
v___x_4281_ = v___x_4278_;
v_isShared_4282_ = v_isSharedCheck_4293_;
goto v_resetjp_4280_;
}
else
{
lean_inc(v_a_4279_);
lean_dec(v___x_4278_);
v___x_4281_ = lean_box(0);
v_isShared_4282_ = v_isSharedCheck_4293_;
goto v_resetjp_4280_;
}
v_resetjp_4280_:
{
uint8_t v___x_4283_; 
v___x_4283_ = l_Lean_Expr_isEq(v_a_4279_);
if (v___x_4283_ == 0)
{
uint8_t v___x_4284_; lean_object* v___x_4285_; lean_object* v___x_4287_; 
v___x_4284_ = l_Lean_Expr_isHEq(v_a_4279_);
lean_dec(v_a_4279_);
v___x_4285_ = lean_box(v___x_4284_);
if (v_isShared_4282_ == 0)
{
lean_ctor_set(v___x_4281_, 0, v___x_4285_);
v___x_4287_ = v___x_4281_;
goto v_reusejp_4286_;
}
else
{
lean_object* v_reuseFailAlloc_4288_; 
v_reuseFailAlloc_4288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4288_, 0, v___x_4285_);
v___x_4287_ = v_reuseFailAlloc_4288_;
goto v_reusejp_4286_;
}
v_reusejp_4286_:
{
return v___x_4287_;
}
}
else
{
lean_object* v___x_4289_; lean_object* v___x_4291_; 
lean_dec(v_a_4279_);
v___x_4289_ = lean_box(v___x_4283_);
if (v_isShared_4282_ == 0)
{
lean_ctor_set(v___x_4281_, 0, v___x_4289_);
v___x_4291_ = v___x_4281_;
goto v_reusejp_4290_;
}
else
{
lean_object* v_reuseFailAlloc_4292_; 
v_reuseFailAlloc_4292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4292_, 0, v___x_4289_);
v___x_4291_ = v_reuseFailAlloc_4292_;
goto v_reusejp_4290_;
}
v_reusejp_4290_:
{
return v___x_4291_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_substEqs___lam__0___boxed(lean_object* v_localDecl_4294_, lean_object* v___y_4295_, lean_object* v___y_4296_, lean_object* v___y_4297_, lean_object* v___y_4298_, lean_object* v___y_4299_){
_start:
{
lean_object* v_res_4300_; 
v_res_4300_ = l_Lean_MVarId_substEqs___lam__0(v_localDecl_4294_, v___y_4295_, v___y_4296_, v___y_4297_, v___y_4298_);
lean_dec(v___y_4298_);
lean_dec_ref(v___y_4297_);
lean_dec(v___y_4296_);
lean_dec_ref(v___y_4295_);
lean_dec_ref(v_localDecl_4294_);
return v_res_4300_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_substEqs(lean_object* v_mvarId_4302_, lean_object* v_a_4303_, lean_object* v_a_4304_, lean_object* v_a_4305_, lean_object* v_a_4306_){
_start:
{
lean_object* v___f_4308_; lean_object* v___x_4309_; 
v___f_4308_ = ((lean_object*)(l_Lean_MVarId_substEqs___closed__0));
v___x_4309_ = l_Lean_MVarId_casesRec(v_mvarId_4302_, v___f_4308_, v_a_4303_, v_a_4304_, v_a_4305_, v_a_4306_);
if (lean_obj_tag(v___x_4309_) == 0)
{
lean_object* v_a_4310_; lean_object* v___x_4311_; lean_object* v___x_4312_; 
v_a_4310_ = lean_ctor_get(v___x_4309_, 0);
lean_inc(v_a_4310_);
lean_dec_ref(v___x_4309_);
v___x_4311_ = lean_obj_once(&l_Lean_MVarId_casesAnd___closed__3, &l_Lean_MVarId_casesAnd___closed__3_once, _init_l_Lean_MVarId_casesAnd___closed__3);
v___x_4312_ = l_Lean_Meta_ensureAtMostOne(v_a_4310_, v___x_4311_, v_a_4303_, v_a_4304_, v_a_4305_, v_a_4306_);
lean_dec(v_a_4310_);
return v___x_4312_;
}
else
{
lean_object* v_a_4313_; lean_object* v___x_4315_; uint8_t v_isShared_4316_; uint8_t v_isSharedCheck_4320_; 
v_a_4313_ = lean_ctor_get(v___x_4309_, 0);
v_isSharedCheck_4320_ = !lean_is_exclusive(v___x_4309_);
if (v_isSharedCheck_4320_ == 0)
{
v___x_4315_ = v___x_4309_;
v_isShared_4316_ = v_isSharedCheck_4320_;
goto v_resetjp_4314_;
}
else
{
lean_inc(v_a_4313_);
lean_dec(v___x_4309_);
v___x_4315_ = lean_box(0);
v_isShared_4316_ = v_isSharedCheck_4320_;
goto v_resetjp_4314_;
}
v_resetjp_4314_:
{
lean_object* v___x_4318_; 
if (v_isShared_4316_ == 0)
{
v___x_4318_ = v___x_4315_;
goto v_reusejp_4317_;
}
else
{
lean_object* v_reuseFailAlloc_4319_; 
v_reuseFailAlloc_4319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4319_, 0, v_a_4313_);
v___x_4318_ = v_reuseFailAlloc_4319_;
goto v_reusejp_4317_;
}
v_reusejp_4317_:
{
return v___x_4318_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_substEqs___boxed(lean_object* v_mvarId_4321_, lean_object* v_a_4322_, lean_object* v_a_4323_, lean_object* v_a_4324_, lean_object* v_a_4325_, lean_object* v_a_4326_){
_start:
{
lean_object* v_res_4327_; 
v_res_4327_ = l_Lean_MVarId_substEqs(v_mvarId_4321_, v_a_4322_, v_a_4323_, v_a_4324_, v_a_4325_);
lean_dec(v_a_4325_);
lean_dec_ref(v_a_4324_);
lean_dec(v_a_4323_);
lean_dec_ref(v_a_4322_);
return v_res_4327_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal___closed__1(void){
_start:
{
lean_object* v___x_4329_; lean_object* v___x_4330_; 
v___x_4329_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal___closed__0));
v___x_4330_ = l_Lean_stringToMessageData(v___x_4329_);
return v___x_4330_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal(lean_object* v_s_4331_, lean_object* v_a_4332_, lean_object* v_a_4333_, lean_object* v_a_4334_, lean_object* v_a_4335_){
_start:
{
lean_object* v___y_4338_; lean_object* v___y_4339_; lean_object* v___y_4340_; lean_object* v___y_4341_; lean_object* v_toInductionSubgoal_4344_; lean_object* v___x_4346_; uint8_t v_isShared_4347_; uint8_t v_isSharedCheck_4360_; 
v_toInductionSubgoal_4344_ = lean_ctor_get(v_s_4331_, 0);
v_isSharedCheck_4360_ = !lean_is_exclusive(v_s_4331_);
if (v_isSharedCheck_4360_ == 0)
{
lean_object* v_unused_4361_; 
v_unused_4361_ = lean_ctor_get(v_s_4331_, 1);
lean_dec(v_unused_4361_);
v___x_4346_ = v_s_4331_;
v_isShared_4347_ = v_isSharedCheck_4360_;
goto v_resetjp_4345_;
}
else
{
lean_inc(v_toInductionSubgoal_4344_);
lean_dec(v_s_4331_);
v___x_4346_ = lean_box(0);
v_isShared_4347_ = v_isSharedCheck_4360_;
goto v_resetjp_4345_;
}
v___jp_4337_:
{
lean_object* v___x_4342_; lean_object* v___x_4343_; 
v___x_4342_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal___closed__1, &l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal___closed__1_once, _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal___closed__1);
v___x_4343_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected_spec__0___redArg(v___x_4342_, v___y_4338_, v___y_4339_, v___y_4340_, v___y_4341_);
return v___x_4343_;
}
v_resetjp_4345_:
{
lean_object* v_mvarId_4348_; lean_object* v_fields_4349_; lean_object* v___x_4350_; lean_object* v___x_4351_; uint8_t v___x_4352_; 
v_mvarId_4348_ = lean_ctor_get(v_toInductionSubgoal_4344_, 0);
lean_inc(v_mvarId_4348_);
v_fields_4349_ = lean_ctor_get(v_toInductionSubgoal_4344_, 1);
lean_inc_ref(v_fields_4349_);
lean_dec_ref(v_toInductionSubgoal_4344_);
v___x_4350_ = lean_array_get_size(v_fields_4349_);
v___x_4351_ = lean_unsigned_to_nat(1u);
v___x_4352_ = lean_nat_dec_eq(v___x_4350_, v___x_4351_);
if (v___x_4352_ == 0)
{
lean_dec_ref(v_fields_4349_);
lean_dec(v_mvarId_4348_);
lean_del_object(v___x_4346_);
v___y_4338_ = v_a_4332_;
v___y_4339_ = v_a_4333_;
v___y_4340_ = v_a_4334_;
v___y_4341_ = v_a_4335_;
goto v___jp_4337_;
}
else
{
lean_object* v___x_4353_; lean_object* v___x_4354_; 
v___x_4353_ = lean_unsigned_to_nat(0u);
v___x_4354_ = lean_array_fget(v_fields_4349_, v___x_4353_);
lean_dec_ref(v_fields_4349_);
if (lean_obj_tag(v___x_4354_) == 1)
{
lean_object* v_fvarId_4355_; lean_object* v___x_4357_; 
v_fvarId_4355_ = lean_ctor_get(v___x_4354_, 0);
lean_inc(v_fvarId_4355_);
lean_dec_ref(v___x_4354_);
if (v_isShared_4347_ == 0)
{
lean_ctor_set(v___x_4346_, 1, v_fvarId_4355_);
lean_ctor_set(v___x_4346_, 0, v_mvarId_4348_);
v___x_4357_ = v___x_4346_;
goto v_reusejp_4356_;
}
else
{
lean_object* v_reuseFailAlloc_4359_; 
v_reuseFailAlloc_4359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4359_, 0, v_mvarId_4348_);
lean_ctor_set(v_reuseFailAlloc_4359_, 1, v_fvarId_4355_);
v___x_4357_ = v_reuseFailAlloc_4359_;
goto v_reusejp_4356_;
}
v_reusejp_4356_:
{
lean_object* v___x_4358_; 
v___x_4358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4358_, 0, v___x_4357_);
return v___x_4358_;
}
}
else
{
lean_dec(v___x_4354_);
lean_dec(v_mvarId_4348_);
lean_del_object(v___x_4346_);
v___y_4338_ = v_a_4332_;
v___y_4339_ = v_a_4333_;
v___y_4340_ = v_a_4334_;
v___y_4341_ = v_a_4335_;
goto v___jp_4337_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal___boxed(lean_object* v_s_4362_, lean_object* v_a_4363_, lean_object* v_a_4364_, lean_object* v_a_4365_, lean_object* v_a_4366_, lean_object* v_a_4367_){
_start:
{
lean_object* v_res_4368_; 
v_res_4368_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal(v_s_4362_, v_a_4363_, v_a_4364_, v_a_4365_, v_a_4366_);
lean_dec(v_a_4366_);
lean_dec_ref(v_a_4365_);
lean_dec(v_a_4364_);
lean_dec_ref(v_a_4363_);
return v_res_4368_;
}
}
static lean_object* _init_l_Lean_MVarId_byCases___closed__3(void){
_start:
{
lean_object* v___x_4373_; lean_object* v___x_4374_; 
v___x_4373_ = ((lean_object*)(l_Lean_MVarId_byCases___closed__2));
v___x_4374_ = l_Lean_stringToMessageData(v___x_4373_);
return v___x_4374_;
}
}
static lean_object* _init_l_Lean_MVarId_byCases___closed__5(void){
_start:
{
lean_object* v___x_4376_; lean_object* v___x_4377_; 
v___x_4376_ = ((lean_object*)(l_Lean_MVarId_byCases___closed__4));
v___x_4377_ = l_Lean_stringToMessageData(v___x_4376_);
return v___x_4377_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_byCases(lean_object* v_mvarId_4378_, lean_object* v_p_4379_, lean_object* v_hName_4380_, lean_object* v_a_4381_, lean_object* v_a_4382_, lean_object* v_a_4383_, lean_object* v_a_4384_){
_start:
{
lean_object* v___x_4386_; lean_object* v___x_4387_; lean_object* v___x_4388_; lean_object* v___x_4389_; lean_object* v___x_4390_; 
v___x_4386_ = ((lean_object*)(l_Lean_MVarId_byCases___closed__1));
lean_inc_ref(v_p_4379_);
v___x_4387_ = l_Lean_mkNot(v_p_4379_);
lean_inc_ref(v_p_4379_);
v___x_4388_ = l_Lean_mkOr(v_p_4379_, v___x_4387_);
lean_inc_ref(v_p_4379_);
v___x_4389_ = l_Lean_mkEM(v_p_4379_);
v___x_4390_ = l_Lean_MVarId_assert(v_mvarId_4378_, v___x_4386_, v___x_4388_, v___x_4389_, v_a_4381_, v_a_4382_, v_a_4383_, v_a_4384_);
if (lean_obj_tag(v___x_4390_) == 0)
{
lean_object* v_a_4391_; uint8_t v___x_4392_; lean_object* v___x_4393_; 
v_a_4391_ = lean_ctor_get(v___x_4390_, 0);
lean_inc(v_a_4391_);
lean_dec_ref(v___x_4390_);
v___x_4392_ = 0;
v___x_4393_ = l_Lean_Meta_intro1Core(v_a_4391_, v___x_4392_, v_a_4381_, v_a_4382_, v_a_4383_, v_a_4384_);
if (lean_obj_tag(v___x_4393_) == 0)
{
lean_object* v_a_4394_; lean_object* v_fst_4395_; lean_object* v_snd_4396_; lean_object* v___x_4398_; uint8_t v_isShared_4399_; uint8_t v_isSharedCheck_4461_; 
v_a_4394_ = lean_ctor_get(v___x_4393_, 0);
lean_inc(v_a_4394_);
lean_dec_ref(v___x_4393_);
v_fst_4395_ = lean_ctor_get(v_a_4394_, 0);
v_snd_4396_ = lean_ctor_get(v_a_4394_, 1);
v_isSharedCheck_4461_ = !lean_is_exclusive(v_a_4394_);
if (v_isSharedCheck_4461_ == 0)
{
v___x_4398_ = v_a_4394_;
v_isShared_4399_ = v_isSharedCheck_4461_;
goto v_resetjp_4397_;
}
else
{
lean_inc(v_snd_4396_);
lean_inc(v_fst_4395_);
lean_dec(v_a_4394_);
v___x_4398_ = lean_box(0);
v_isShared_4399_ = v_isSharedCheck_4461_;
goto v_resetjp_4397_;
}
v_resetjp_4397_:
{
lean_object* v___x_4400_; lean_object* v___x_4401_; lean_object* v___x_4402_; lean_object* v___x_4403_; lean_object* v___x_4404_; lean_object* v___x_4405_; lean_object* v___x_4406_; lean_object* v___x_4407_; lean_object* v___x_4408_; 
v___x_4400_ = lean_box(0);
v___x_4401_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4401_, 0, v_hName_4380_);
lean_ctor_set(v___x_4401_, 1, v___x_4400_);
v___x_4402_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4402_, 0, v___x_4401_);
lean_ctor_set_uint8(v___x_4402_, sizeof(void*)*1, v___x_4392_);
v___x_4403_ = lean_unsigned_to_nat(2u);
v___x_4404_ = lean_mk_empty_array_with_capacity(v___x_4403_);
lean_inc_ref(v___x_4402_);
v___x_4405_ = lean_array_push(v___x_4404_, v___x_4402_);
v___x_4406_ = lean_array_push(v___x_4405_, v___x_4402_);
v___x_4407_ = lean_box(0);
v___x_4408_ = l_Lean_Meta_Cases_cases(v_snd_4396_, v_fst_4395_, v___x_4406_, v___x_4392_, v___x_4407_, v_a_4381_, v_a_4382_, v_a_4383_, v_a_4384_);
if (lean_obj_tag(v___x_4408_) == 0)
{
lean_object* v_a_4409_; lean_object* v___x_4410_; uint8_t v___x_4411_; 
v_a_4409_ = lean_ctor_get(v___x_4408_, 0);
lean_inc(v_a_4409_);
lean_dec_ref(v___x_4408_);
v___x_4410_ = lean_array_get_size(v_a_4409_);
v___x_4411_ = lean_nat_dec_eq(v___x_4410_, v___x_4403_);
if (v___x_4411_ == 0)
{
lean_object* v___x_4412_; lean_object* v___x_4413_; lean_object* v___x_4414_; lean_object* v___x_4415_; lean_object* v___x_4416_; lean_object* v___x_4417_; lean_object* v___x_4418_; 
lean_dec(v_a_4409_);
lean_del_object(v___x_4398_);
v___x_4412_ = lean_obj_once(&l_Lean_MVarId_byCases___closed__3, &l_Lean_MVarId_byCases___closed__3_once, _init_l_Lean_MVarId_byCases___closed__3);
v___x_4413_ = lean_unsigned_to_nat(30u);
v___x_4414_ = l_Lean_inlineExpr(v_p_4379_, v___x_4413_);
v___x_4415_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4415_, 0, v___x_4412_);
lean_ctor_set(v___x_4415_, 1, v___x_4414_);
v___x_4416_ = lean_obj_once(&l_Lean_MVarId_byCases___closed__5, &l_Lean_MVarId_byCases___closed__5_once, _init_l_Lean_MVarId_byCases___closed__5);
v___x_4417_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4417_, 0, v___x_4415_);
lean_ctor_set(v___x_4417_, 1, v___x_4416_);
v___x_4418_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected_spec__0___redArg(v___x_4417_, v_a_4381_, v_a_4382_, v_a_4383_, v_a_4384_);
return v___x_4418_;
}
else
{
lean_object* v___x_4419_; lean_object* v___x_4420_; lean_object* v___x_4421_; 
lean_dec_ref(v_p_4379_);
v___x_4419_ = lean_unsigned_to_nat(0u);
v___x_4420_ = lean_array_fget_borrowed(v_a_4409_, v___x_4419_);
lean_inc(v___x_4420_);
v___x_4421_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal(v___x_4420_, v_a_4381_, v_a_4382_, v_a_4383_, v_a_4384_);
if (lean_obj_tag(v___x_4421_) == 0)
{
lean_object* v_a_4422_; lean_object* v___x_4423_; lean_object* v___x_4424_; lean_object* v___x_4425_; 
v_a_4422_ = lean_ctor_get(v___x_4421_, 0);
lean_inc(v_a_4422_);
lean_dec_ref(v___x_4421_);
v___x_4423_ = lean_unsigned_to_nat(1u);
v___x_4424_ = lean_array_fget(v_a_4409_, v___x_4423_);
lean_dec(v_a_4409_);
v___x_4425_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal(v___x_4424_, v_a_4381_, v_a_4382_, v_a_4383_, v_a_4384_);
if (lean_obj_tag(v___x_4425_) == 0)
{
lean_object* v_a_4426_; lean_object* v___x_4428_; uint8_t v_isShared_4429_; uint8_t v_isSharedCheck_4436_; 
v_a_4426_ = lean_ctor_get(v___x_4425_, 0);
v_isSharedCheck_4436_ = !lean_is_exclusive(v___x_4425_);
if (v_isSharedCheck_4436_ == 0)
{
v___x_4428_ = v___x_4425_;
v_isShared_4429_ = v_isSharedCheck_4436_;
goto v_resetjp_4427_;
}
else
{
lean_inc(v_a_4426_);
lean_dec(v___x_4425_);
v___x_4428_ = lean_box(0);
v_isShared_4429_ = v_isSharedCheck_4436_;
goto v_resetjp_4427_;
}
v_resetjp_4427_:
{
lean_object* v___x_4431_; 
if (v_isShared_4399_ == 0)
{
lean_ctor_set(v___x_4398_, 1, v_a_4426_);
lean_ctor_set(v___x_4398_, 0, v_a_4422_);
v___x_4431_ = v___x_4398_;
goto v_reusejp_4430_;
}
else
{
lean_object* v_reuseFailAlloc_4435_; 
v_reuseFailAlloc_4435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4435_, 0, v_a_4422_);
lean_ctor_set(v_reuseFailAlloc_4435_, 1, v_a_4426_);
v___x_4431_ = v_reuseFailAlloc_4435_;
goto v_reusejp_4430_;
}
v_reusejp_4430_:
{
lean_object* v___x_4433_; 
if (v_isShared_4429_ == 0)
{
lean_ctor_set(v___x_4428_, 0, v___x_4431_);
v___x_4433_ = v___x_4428_;
goto v_reusejp_4432_;
}
else
{
lean_object* v_reuseFailAlloc_4434_; 
v_reuseFailAlloc_4434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4434_, 0, v___x_4431_);
v___x_4433_ = v_reuseFailAlloc_4434_;
goto v_reusejp_4432_;
}
v_reusejp_4432_:
{
return v___x_4433_;
}
}
}
}
else
{
lean_object* v_a_4437_; lean_object* v___x_4439_; uint8_t v_isShared_4440_; uint8_t v_isSharedCheck_4444_; 
lean_dec(v_a_4422_);
lean_del_object(v___x_4398_);
v_a_4437_ = lean_ctor_get(v___x_4425_, 0);
v_isSharedCheck_4444_ = !lean_is_exclusive(v___x_4425_);
if (v_isSharedCheck_4444_ == 0)
{
v___x_4439_ = v___x_4425_;
v_isShared_4440_ = v_isSharedCheck_4444_;
goto v_resetjp_4438_;
}
else
{
lean_inc(v_a_4437_);
lean_dec(v___x_4425_);
v___x_4439_ = lean_box(0);
v_isShared_4440_ = v_isSharedCheck_4444_;
goto v_resetjp_4438_;
}
v_resetjp_4438_:
{
lean_object* v___x_4442_; 
if (v_isShared_4440_ == 0)
{
v___x_4442_ = v___x_4439_;
goto v_reusejp_4441_;
}
else
{
lean_object* v_reuseFailAlloc_4443_; 
v_reuseFailAlloc_4443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4443_, 0, v_a_4437_);
v___x_4442_ = v_reuseFailAlloc_4443_;
goto v_reusejp_4441_;
}
v_reusejp_4441_:
{
return v___x_4442_;
}
}
}
}
else
{
lean_object* v_a_4445_; lean_object* v___x_4447_; uint8_t v_isShared_4448_; uint8_t v_isSharedCheck_4452_; 
lean_dec(v_a_4409_);
lean_del_object(v___x_4398_);
v_a_4445_ = lean_ctor_get(v___x_4421_, 0);
v_isSharedCheck_4452_ = !lean_is_exclusive(v___x_4421_);
if (v_isSharedCheck_4452_ == 0)
{
v___x_4447_ = v___x_4421_;
v_isShared_4448_ = v_isSharedCheck_4452_;
goto v_resetjp_4446_;
}
else
{
lean_inc(v_a_4445_);
lean_dec(v___x_4421_);
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
}
else
{
lean_object* v_a_4453_; lean_object* v___x_4455_; uint8_t v_isShared_4456_; uint8_t v_isSharedCheck_4460_; 
lean_del_object(v___x_4398_);
lean_dec_ref(v_p_4379_);
v_a_4453_ = lean_ctor_get(v___x_4408_, 0);
v_isSharedCheck_4460_ = !lean_is_exclusive(v___x_4408_);
if (v_isSharedCheck_4460_ == 0)
{
v___x_4455_ = v___x_4408_;
v_isShared_4456_ = v_isSharedCheck_4460_;
goto v_resetjp_4454_;
}
else
{
lean_inc(v_a_4453_);
lean_dec(v___x_4408_);
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
}
}
else
{
lean_object* v_a_4462_; lean_object* v___x_4464_; uint8_t v_isShared_4465_; uint8_t v_isSharedCheck_4469_; 
lean_dec(v_hName_4380_);
lean_dec_ref(v_p_4379_);
v_a_4462_ = lean_ctor_get(v___x_4393_, 0);
v_isSharedCheck_4469_ = !lean_is_exclusive(v___x_4393_);
if (v_isSharedCheck_4469_ == 0)
{
v___x_4464_ = v___x_4393_;
v_isShared_4465_ = v_isSharedCheck_4469_;
goto v_resetjp_4463_;
}
else
{
lean_inc(v_a_4462_);
lean_dec(v___x_4393_);
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
lean_dec(v_hName_4380_);
lean_dec_ref(v_p_4379_);
v_a_4470_ = lean_ctor_get(v___x_4390_, 0);
v_isSharedCheck_4477_ = !lean_is_exclusive(v___x_4390_);
if (v_isSharedCheck_4477_ == 0)
{
v___x_4472_ = v___x_4390_;
v_isShared_4473_ = v_isSharedCheck_4477_;
goto v_resetjp_4471_;
}
else
{
lean_inc(v_a_4470_);
lean_dec(v___x_4390_);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_byCases___boxed(lean_object* v_mvarId_4478_, lean_object* v_p_4479_, lean_object* v_hName_4480_, lean_object* v_a_4481_, lean_object* v_a_4482_, lean_object* v_a_4483_, lean_object* v_a_4484_, lean_object* v_a_4485_){
_start:
{
lean_object* v_res_4486_; 
v_res_4486_ = l_Lean_MVarId_byCases(v_mvarId_4478_, v_p_4479_, v_hName_4480_, v_a_4481_, v_a_4482_, v_a_4483_, v_a_4484_);
lean_dec(v_a_4484_);
lean_dec_ref(v_a_4483_);
lean_dec(v_a_4482_);
lean_dec_ref(v_a_4481_);
return v_res_4486_;
}
}
static lean_object* _init_l_Lean_MVarId_byCasesDec___closed__2(void){
_start:
{
lean_object* v___x_4490_; lean_object* v___x_4491_; lean_object* v___x_4492_; 
v___x_4490_ = lean_box(0);
v___x_4491_ = ((lean_object*)(l_Lean_MVarId_byCasesDec___closed__1));
v___x_4492_ = l_Lean_mkConst(v___x_4491_, v___x_4490_);
return v___x_4492_;
}
}
static lean_object* _init_l_Lean_MVarId_byCasesDec___closed__4(void){
_start:
{
lean_object* v___x_4494_; lean_object* v___x_4495_; 
v___x_4494_ = ((lean_object*)(l_Lean_MVarId_byCasesDec___closed__3));
v___x_4495_ = l_Lean_stringToMessageData(v___x_4494_);
return v___x_4495_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_byCasesDec(lean_object* v_mvarId_4496_, lean_object* v_p_4497_, lean_object* v_dec_4498_, lean_object* v_hName_4499_, lean_object* v_a_4500_, lean_object* v_a_4501_, lean_object* v_a_4502_, lean_object* v_a_4503_){
_start:
{
lean_object* v___x_4505_; lean_object* v___x_4506_; lean_object* v___x_4507_; lean_object* v___x_4508_; lean_object* v___x_4509_; 
v___x_4505_ = ((lean_object*)(l_Lean_MVarId_byCases___closed__1));
v___x_4506_ = lean_box(0);
v___x_4507_ = lean_obj_once(&l_Lean_MVarId_byCasesDec___closed__2, &l_Lean_MVarId_byCasesDec___closed__2_once, _init_l_Lean_MVarId_byCasesDec___closed__2);
lean_inc_ref(v_p_4497_);
v___x_4508_ = l_Lean_Expr_app___override(v___x_4507_, v_p_4497_);
v___x_4509_ = l_Lean_MVarId_assert(v_mvarId_4496_, v___x_4505_, v___x_4508_, v_dec_4498_, v_a_4500_, v_a_4501_, v_a_4502_, v_a_4503_);
if (lean_obj_tag(v___x_4509_) == 0)
{
lean_object* v_a_4510_; uint8_t v___x_4511_; lean_object* v___x_4512_; 
v_a_4510_ = lean_ctor_get(v___x_4509_, 0);
lean_inc(v_a_4510_);
lean_dec_ref(v___x_4509_);
v___x_4511_ = 0;
v___x_4512_ = l_Lean_Meta_intro1Core(v_a_4510_, v___x_4511_, v_a_4500_, v_a_4501_, v_a_4502_, v_a_4503_);
if (lean_obj_tag(v___x_4512_) == 0)
{
lean_object* v_a_4513_; lean_object* v_fst_4514_; lean_object* v_snd_4515_; lean_object* v___x_4517_; uint8_t v_isShared_4518_; uint8_t v_isSharedCheck_4579_; 
v_a_4513_ = lean_ctor_get(v___x_4512_, 0);
lean_inc(v_a_4513_);
lean_dec_ref(v___x_4512_);
v_fst_4514_ = lean_ctor_get(v_a_4513_, 0);
v_snd_4515_ = lean_ctor_get(v_a_4513_, 1);
v_isSharedCheck_4579_ = !lean_is_exclusive(v_a_4513_);
if (v_isSharedCheck_4579_ == 0)
{
v___x_4517_ = v_a_4513_;
v_isShared_4518_ = v_isSharedCheck_4579_;
goto v_resetjp_4516_;
}
else
{
lean_inc(v_snd_4515_);
lean_inc(v_fst_4514_);
lean_dec(v_a_4513_);
v___x_4517_ = lean_box(0);
v_isShared_4518_ = v_isSharedCheck_4579_;
goto v_resetjp_4516_;
}
v_resetjp_4516_:
{
lean_object* v___x_4519_; lean_object* v___x_4520_; lean_object* v___x_4521_; lean_object* v___x_4522_; lean_object* v___x_4523_; lean_object* v___x_4524_; lean_object* v___x_4525_; lean_object* v___x_4526_; 
v___x_4519_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4519_, 0, v_hName_4499_);
lean_ctor_set(v___x_4519_, 1, v___x_4506_);
v___x_4520_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4520_, 0, v___x_4519_);
lean_ctor_set_uint8(v___x_4520_, sizeof(void*)*1, v___x_4511_);
v___x_4521_ = lean_unsigned_to_nat(2u);
v___x_4522_ = lean_mk_empty_array_with_capacity(v___x_4521_);
lean_inc_ref(v___x_4520_);
v___x_4523_ = lean_array_push(v___x_4522_, v___x_4520_);
v___x_4524_ = lean_array_push(v___x_4523_, v___x_4520_);
v___x_4525_ = lean_box(0);
v___x_4526_ = l_Lean_Meta_Cases_cases(v_snd_4515_, v_fst_4514_, v___x_4524_, v___x_4511_, v___x_4525_, v_a_4500_, v_a_4501_, v_a_4502_, v_a_4503_);
if (lean_obj_tag(v___x_4526_) == 0)
{
lean_object* v_a_4527_; lean_object* v___x_4528_; uint8_t v___x_4529_; 
v_a_4527_ = lean_ctor_get(v___x_4526_, 0);
lean_inc(v_a_4527_);
lean_dec_ref(v___x_4526_);
v___x_4528_ = lean_array_get_size(v_a_4527_);
v___x_4529_ = lean_nat_dec_eq(v___x_4528_, v___x_4521_);
if (v___x_4529_ == 0)
{
lean_object* v___x_4530_; lean_object* v___x_4531_; lean_object* v___x_4532_; lean_object* v___x_4533_; lean_object* v___x_4534_; lean_object* v___x_4535_; lean_object* v___x_4536_; 
lean_dec(v_a_4527_);
lean_del_object(v___x_4517_);
v___x_4530_ = lean_obj_once(&l_Lean_MVarId_byCasesDec___closed__4, &l_Lean_MVarId_byCasesDec___closed__4_once, _init_l_Lean_MVarId_byCasesDec___closed__4);
v___x_4531_ = lean_unsigned_to_nat(30u);
v___x_4532_ = l_Lean_inlineExpr(v_p_4497_, v___x_4531_);
v___x_4533_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4533_, 0, v___x_4530_);
lean_ctor_set(v___x_4533_, 1, v___x_4532_);
v___x_4534_ = lean_obj_once(&l_Lean_MVarId_byCases___closed__5, &l_Lean_MVarId_byCases___closed__5_once, _init_l_Lean_MVarId_byCases___closed__5);
v___x_4535_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4535_, 0, v___x_4533_);
lean_ctor_set(v___x_4535_, 1, v___x_4534_);
v___x_4536_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected_spec__0___redArg(v___x_4535_, v_a_4500_, v_a_4501_, v_a_4502_, v_a_4503_);
return v___x_4536_;
}
else
{
lean_object* v___x_4537_; lean_object* v___x_4538_; lean_object* v___x_4539_; 
lean_dec_ref(v_p_4497_);
v___x_4537_ = lean_unsigned_to_nat(1u);
v___x_4538_ = lean_array_fget_borrowed(v_a_4527_, v___x_4537_);
lean_inc(v___x_4538_);
v___x_4539_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal(v___x_4538_, v_a_4500_, v_a_4501_, v_a_4502_, v_a_4503_);
if (lean_obj_tag(v___x_4539_) == 0)
{
lean_object* v_a_4540_; lean_object* v___x_4541_; lean_object* v___x_4542_; lean_object* v___x_4543_; 
v_a_4540_ = lean_ctor_get(v___x_4539_, 0);
lean_inc(v_a_4540_);
lean_dec_ref(v___x_4539_);
v___x_4541_ = lean_unsigned_to_nat(0u);
v___x_4542_ = lean_array_fget(v_a_4527_, v___x_4541_);
lean_dec(v_a_4527_);
v___x_4543_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal(v___x_4542_, v_a_4500_, v_a_4501_, v_a_4502_, v_a_4503_);
if (lean_obj_tag(v___x_4543_) == 0)
{
lean_object* v_a_4544_; lean_object* v___x_4546_; uint8_t v_isShared_4547_; uint8_t v_isSharedCheck_4554_; 
v_a_4544_ = lean_ctor_get(v___x_4543_, 0);
v_isSharedCheck_4554_ = !lean_is_exclusive(v___x_4543_);
if (v_isSharedCheck_4554_ == 0)
{
v___x_4546_ = v___x_4543_;
v_isShared_4547_ = v_isSharedCheck_4554_;
goto v_resetjp_4545_;
}
else
{
lean_inc(v_a_4544_);
lean_dec(v___x_4543_);
v___x_4546_ = lean_box(0);
v_isShared_4547_ = v_isSharedCheck_4554_;
goto v_resetjp_4545_;
}
v_resetjp_4545_:
{
lean_object* v___x_4549_; 
if (v_isShared_4518_ == 0)
{
lean_ctor_set(v___x_4517_, 1, v_a_4544_);
lean_ctor_set(v___x_4517_, 0, v_a_4540_);
v___x_4549_ = v___x_4517_;
goto v_reusejp_4548_;
}
else
{
lean_object* v_reuseFailAlloc_4553_; 
v_reuseFailAlloc_4553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4553_, 0, v_a_4540_);
lean_ctor_set(v_reuseFailAlloc_4553_, 1, v_a_4544_);
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
else
{
lean_object* v_a_4555_; lean_object* v___x_4557_; uint8_t v_isShared_4558_; uint8_t v_isSharedCheck_4562_; 
lean_dec(v_a_4540_);
lean_del_object(v___x_4517_);
v_a_4555_ = lean_ctor_get(v___x_4543_, 0);
v_isSharedCheck_4562_ = !lean_is_exclusive(v___x_4543_);
if (v_isSharedCheck_4562_ == 0)
{
v___x_4557_ = v___x_4543_;
v_isShared_4558_ = v_isSharedCheck_4562_;
goto v_resetjp_4556_;
}
else
{
lean_inc(v_a_4555_);
lean_dec(v___x_4543_);
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
else
{
lean_object* v_a_4563_; lean_object* v___x_4565_; uint8_t v_isShared_4566_; uint8_t v_isSharedCheck_4570_; 
lean_dec(v_a_4527_);
lean_del_object(v___x_4517_);
v_a_4563_ = lean_ctor_get(v___x_4539_, 0);
v_isSharedCheck_4570_ = !lean_is_exclusive(v___x_4539_);
if (v_isSharedCheck_4570_ == 0)
{
v___x_4565_ = v___x_4539_;
v_isShared_4566_ = v_isSharedCheck_4570_;
goto v_resetjp_4564_;
}
else
{
lean_inc(v_a_4563_);
lean_dec(v___x_4539_);
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
lean_object* v_a_4571_; lean_object* v___x_4573_; uint8_t v_isShared_4574_; uint8_t v_isSharedCheck_4578_; 
lean_del_object(v___x_4517_);
lean_dec_ref(v_p_4497_);
v_a_4571_ = lean_ctor_get(v___x_4526_, 0);
v_isSharedCheck_4578_ = !lean_is_exclusive(v___x_4526_);
if (v_isSharedCheck_4578_ == 0)
{
v___x_4573_ = v___x_4526_;
v_isShared_4574_ = v_isSharedCheck_4578_;
goto v_resetjp_4572_;
}
else
{
lean_inc(v_a_4571_);
lean_dec(v___x_4526_);
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
}
else
{
lean_object* v_a_4580_; lean_object* v___x_4582_; uint8_t v_isShared_4583_; uint8_t v_isSharedCheck_4587_; 
lean_dec(v_hName_4499_);
lean_dec_ref(v_p_4497_);
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
lean_dec(v_hName_4499_);
lean_dec_ref(v_p_4497_);
v_a_4588_ = lean_ctor_get(v___x_4509_, 0);
v_isSharedCheck_4595_ = !lean_is_exclusive(v___x_4509_);
if (v_isSharedCheck_4595_ == 0)
{
v___x_4590_ = v___x_4509_;
v_isShared_4591_ = v_isSharedCheck_4595_;
goto v_resetjp_4589_;
}
else
{
lean_inc(v_a_4588_);
lean_dec(v___x_4509_);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_byCasesDec___boxed(lean_object* v_mvarId_4596_, lean_object* v_p_4597_, lean_object* v_dec_4598_, lean_object* v_hName_4599_, lean_object* v_a_4600_, lean_object* v_a_4601_, lean_object* v_a_4602_, lean_object* v_a_4603_, lean_object* v_a_4604_){
_start:
{
lean_object* v_res_4605_; 
v_res_4605_ = l_Lean_MVarId_byCasesDec(v_mvarId_4596_, v_p_4597_, v_dec_4598_, v_hName_4599_, v_a_4600_, v_a_4601_, v_a_4602_, v_a_4603_);
lean_dec(v_a_4603_);
lean_dec_ref(v_a_4602_);
lean_dec(v_a_4601_);
lean_dec_ref(v_a_4600_);
return v_res_4605_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4657_; lean_object* v___x_4658_; lean_object* v___x_4659_; 
v___x_4657_ = lean_unsigned_to_nat(4241171151u);
v___x_4658_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_));
v___x_4659_ = l_Lean_Name_num___override(v___x_4658_, v___x_4657_);
return v___x_4659_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4661_; lean_object* v___x_4662_; lean_object* v___x_4663_; 
v___x_4661_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_));
v___x_4662_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_);
v___x_4663_ = l_Lean_Name_str___override(v___x_4662_, v___x_4661_);
return v___x_4663_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4665_; lean_object* v___x_4666_; lean_object* v___x_4667_; 
v___x_4665_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_));
v___x_4666_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_);
v___x_4667_ = l_Lean_Name_str___override(v___x_4666_, v___x_4665_);
return v___x_4667_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4668_; lean_object* v___x_4669_; lean_object* v___x_4670_; 
v___x_4668_ = lean_unsigned_to_nat(2u);
v___x_4669_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_);
v___x_4670_ = l_Lean_Name_num___override(v___x_4669_, v___x_4668_);
return v___x_4670_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4672_; uint8_t v___x_4673_; lean_object* v___x_4674_; lean_object* v___x_4675_; 
v___x_4672_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_));
v___x_4673_ = 0;
v___x_4674_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_);
v___x_4675_ = l_Lean_registerTraceClass(v___x_4672_, v___x_4673_, v___x_4674_);
return v___x_4675_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2____boxed(lean_object* v_a_4676_){
_start:
{
lean_object* v_res_4677_; 
v_res_4677_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_();
return v_res_4677_;
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
