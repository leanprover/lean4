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
uint8_t lean_bool_not(uint8_t);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Meta_saveState___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
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
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__2(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__0;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__2;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
size_t v_x_2557__boxed_907_; size_t v_x_2558__boxed_908_; lean_object* v_res_909_; 
v_x_2557__boxed_907_ = lean_unbox_usize(v_x_903_);
lean_dec(v_x_903_);
v_x_2558__boxed_908_ = lean_unbox_usize(v_x_904_);
lean_dec(v_x_904_);
v_res_909_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg(v_x_902_, v_x_2557__boxed_907_, v_x_2558__boxed_908_, v_x_905_, v_x_906_);
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
lean_object* v___x_921_; lean_object* v_mctx_922_; lean_object* v_cache_923_; lean_object* v_zetaDeltaFVarIds_924_; lean_object* v_postponed_925_; lean_object* v_diag_926_; lean_object* v___x_928_; uint8_t v_isShared_929_; uint8_t v_isSharedCheck_954_; 
v___x_921_ = lean_st_ref_take(v___y_919_);
v_mctx_922_ = lean_ctor_get(v___x_921_, 0);
v_cache_923_ = lean_ctor_get(v___x_921_, 1);
v_zetaDeltaFVarIds_924_ = lean_ctor_get(v___x_921_, 2);
v_postponed_925_ = lean_ctor_get(v___x_921_, 3);
v_diag_926_ = lean_ctor_get(v___x_921_, 4);
v_isSharedCheck_954_ = !lean_is_exclusive(v___x_921_);
if (v_isSharedCheck_954_ == 0)
{
v___x_928_ = v___x_921_;
v_isShared_929_ = v_isSharedCheck_954_;
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
v_isShared_929_ = v_isSharedCheck_954_;
goto v_resetjp_927_;
}
v_resetjp_927_:
{
lean_object* v_depth_930_; lean_object* v_levelAssignDepth_931_; lean_object* v_lmvarCounter_932_; lean_object* v_mvarCounter_933_; lean_object* v_lDecls_934_; lean_object* v_decls_935_; lean_object* v_userNames_936_; lean_object* v_lAssignment_937_; lean_object* v_eAssignment_938_; lean_object* v_dAssignment_939_; lean_object* v___x_941_; uint8_t v_isShared_942_; uint8_t v_isSharedCheck_953_; 
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
v_isSharedCheck_953_ = !lean_is_exclusive(v_mctx_922_);
if (v_isSharedCheck_953_ == 0)
{
v___x_941_ = v_mctx_922_;
v_isShared_942_ = v_isSharedCheck_953_;
goto v_resetjp_940_;
}
else
{
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
v___x_941_ = lean_box(0);
v_isShared_942_ = v_isSharedCheck_953_;
goto v_resetjp_940_;
}
v_resetjp_940_:
{
lean_object* v___x_943_; lean_object* v___x_945_; 
v___x_943_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1___redArg(v_eAssignment_938_, v_mvarId_917_, v_val_918_);
if (v_isShared_942_ == 0)
{
lean_ctor_set(v___x_941_, 8, v___x_943_);
v___x_945_ = v___x_941_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v_depth_930_);
lean_ctor_set(v_reuseFailAlloc_952_, 1, v_levelAssignDepth_931_);
lean_ctor_set(v_reuseFailAlloc_952_, 2, v_lmvarCounter_932_);
lean_ctor_set(v_reuseFailAlloc_952_, 3, v_mvarCounter_933_);
lean_ctor_set(v_reuseFailAlloc_952_, 4, v_lDecls_934_);
lean_ctor_set(v_reuseFailAlloc_952_, 5, v_decls_935_);
lean_ctor_set(v_reuseFailAlloc_952_, 6, v_userNames_936_);
lean_ctor_set(v_reuseFailAlloc_952_, 7, v_lAssignment_937_);
lean_ctor_set(v_reuseFailAlloc_952_, 8, v___x_943_);
lean_ctor_set(v_reuseFailAlloc_952_, 9, v_dAssignment_939_);
v___x_945_ = v_reuseFailAlloc_952_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
lean_object* v___x_947_; 
if (v_isShared_929_ == 0)
{
lean_ctor_set(v___x_928_, 0, v___x_945_);
v___x_947_ = v___x_928_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v___x_945_);
lean_ctor_set(v_reuseFailAlloc_951_, 1, v_cache_923_);
lean_ctor_set(v_reuseFailAlloc_951_, 2, v_zetaDeltaFVarIds_924_);
lean_ctor_set(v_reuseFailAlloc_951_, 3, v_postponed_925_);
lean_ctor_set(v_reuseFailAlloc_951_, 4, v_diag_926_);
v___x_947_ = v_reuseFailAlloc_951_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; 
v___x_948_ = lean_st_ref_set(v___y_919_, v___x_947_);
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
size_t v_x_2948__boxed_1093_; size_t v_x_2949__boxed_1094_; lean_object* v_res_1095_; 
v_x_2948__boxed_1093_ = lean_unbox_usize(v_x_1089_);
lean_dec(v_x_1089_);
v_x_2949__boxed_1094_ = lean_unbox_usize(v_x_1090_);
lean_dec(v_x_1090_);
v_res_1095_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3(v_00_u03b2_1087_, v_x_1088_, v_x_2948__boxed_1093_, v_x_2949__boxed_1094_, v_x_1091_, v_x_1092_);
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
uint8_t v___x_6260__boxed_1265_; lean_object* v_res_1266_; 
v___x_6260__boxed_1265_ = lean_unbox(v___x_1250_);
v_res_1266_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__0(v_mvarId_1248_, v_newEqs_1249_, v___x_6260__boxed_1265_, v_h_x27_1251_, v_newIndices_1252_, v___x_1253_, v___x_1254_, v___x_1255_, v___x_1256_, v_e_1257_, v___x_1258_, v_newEq_1259_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_);
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
uint8_t v___x_6512__boxed_1316_; lean_object* v_res_1317_; 
v___x_6512__boxed_1316_ = lean_unbox(v___x_1303_);
v_res_1317_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__1(v_e_1300_, v_h_x27_1301_, v_mvarId_1302_, v___x_6512__boxed_1316_, v_newIndices_1304_, v___x_1305_, v___x_1306_, v___x_1307_, v___x_1308_, v_newEqs_1309_, v_newRefls_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_);
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
uint8_t v___x_6577__boxed_1349_; lean_object* v_res_1350_; 
v___x_6577__boxed_1349_ = lean_unbox(v___x_1337_);
v_res_1350_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__2(v_e_1335_, v_mvarId_1336_, v___x_6577__boxed_1349_, v_newIndices_1338_, v___x_1339_, v___x_1340_, v___x_1341_, v___x_1342_, v_h_x27_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_);
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
uint8_t v___x_6619__boxed_1403_; lean_object* v_res_1404_; 
v___x_6619__boxed_1403_ = lean_unbox(v___x_1389_);
v_res_1404_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__3(v_e_1387_, v_mvarId_1388_, v___x_6619__boxed_1403_, v___x_1390_, v___x_1391_, v___x_1392_, v___x_1393_, v___x_1394_, v_varName_x3f_1395_, v_newIndices_1396_, v_x_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_);
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
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0___redArg(uint8_t v___y_1654_, lean_object* v___x_1655_, lean_object* v_a_1656_, lean_object* v_x_1657_, lean_object* v_x_1658_, lean_object* v_x_1659_, lean_object* v___y_1660_){
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
lean_object* v_declName_1671_; lean_object* v___x_1672_; lean_object* v_env_1673_; lean_object* v___x_1674_; 
v_declName_1671_ = lean_ctor_get(v_x_1657_, 0);
v___x_1672_ = lean_st_ref_get(v___y_1660_);
v_env_1673_ = lean_ctor_get(v___x_1672_, 0);
lean_inc_ref(v_env_1673_);
lean_dec(v___x_1672_);
lean_inc(v_declName_1671_);
v___x_1674_ = l_Lean_Environment_find_x3f(v_env_1673_, v_declName_1671_, v___y_1654_);
if (lean_obj_tag(v___x_1674_) == 0)
{
lean_dec_ref_known(v_x_1657_, 2);
lean_dec_ref(v_x_1658_);
lean_dec_ref(v_a_1656_);
lean_dec_ref(v___x_1655_);
goto v___jp_1662_;
}
else
{
lean_object* v_val_1675_; lean_object* v___x_1677_; uint8_t v_isShared_1678_; uint8_t v_isSharedCheck_1716_; 
v_val_1675_ = lean_ctor_get(v___x_1674_, 0);
v_isSharedCheck_1716_ = !lean_is_exclusive(v___x_1674_);
if (v_isSharedCheck_1716_ == 0)
{
v___x_1677_ = v___x_1674_;
v_isShared_1678_ = v_isSharedCheck_1716_;
goto v_resetjp_1676_;
}
else
{
lean_inc(v_val_1675_);
lean_dec(v___x_1674_);
v___x_1677_ = lean_box(0);
v_isShared_1678_ = v_isSharedCheck_1716_;
goto v_resetjp_1676_;
}
v_resetjp_1676_:
{
if (lean_obj_tag(v_val_1675_) == 5)
{
lean_object* v_val_1679_; lean_object* v___x_1681_; uint8_t v_isShared_1682_; uint8_t v_isSharedCheck_1715_; 
v_val_1679_ = lean_ctor_get(v_val_1675_, 0);
v_isSharedCheck_1715_ = !lean_is_exclusive(v_val_1675_);
if (v_isSharedCheck_1715_ == 0)
{
v___x_1681_ = v_val_1675_;
v_isShared_1682_ = v_isSharedCheck_1715_;
goto v_resetjp_1680_;
}
else
{
lean_inc(v_val_1679_);
lean_dec(v_val_1675_);
v___x_1681_ = lean_box(0);
v_isShared_1682_ = v_isSharedCheck_1715_;
goto v_resetjp_1680_;
}
v_resetjp_1680_:
{
lean_object* v_toConstantVal_1683_; lean_object* v_numParams_1684_; lean_object* v_numIndices_1685_; lean_object* v_ctors_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; uint8_t v___x_1689_; uint8_t v___x_1690_; 
v_toConstantVal_1683_ = lean_ctor_get(v_val_1679_, 0);
v_numParams_1684_ = lean_ctor_get(v_val_1679_, 1);
v_numIndices_1685_ = lean_ctor_get(v_val_1679_, 2);
v_ctors_1686_ = lean_ctor_get(v_val_1679_, 4);
v___x_1687_ = lean_array_get_size(v_x_1658_);
v___x_1688_ = lean_nat_add(v_numIndices_1685_, v_numParams_1684_);
v___x_1689_ = lean_nat_dec_eq(v___x_1687_, v___x_1688_);
lean_dec(v___x_1688_);
v___x_1690_ = lean_bool_not(v___x_1689_);
if (v___x_1690_ == 0)
{
lean_object* v_name_1691_; uint8_t v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; uint8_t v___x_1695_; uint8_t v___x_1696_; 
v_name_1691_ = lean_ctor_get(v_toConstantVal_1683_, 0);
v___x_1692_ = 1;
v___x_1693_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0___redArg___closed__0));
lean_inc(v_name_1691_);
v___x_1694_ = l_Lean_Name_str___override(v_name_1691_, v___x_1693_);
v___x_1695_ = l_Lean_Environment_contains(v___x_1655_, v___x_1694_, v___x_1692_);
v___x_1696_ = lean_bool_not(v___x_1695_);
if (v___x_1696_ == 0)
{
lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1702_; 
v___x_1697_ = l_List_lengthTR___redArg(v_ctors_1686_);
v___x_1698_ = lean_nat_sub(v___x_1687_, v_numIndices_1685_);
v___x_1699_ = l_Array_extract___redArg(v_x_1658_, v___x_1698_, v___x_1687_);
v___x_1700_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1700_, 0, v_val_1679_);
lean_ctor_set(v___x_1700_, 1, v___x_1697_);
lean_ctor_set(v___x_1700_, 2, v_a_1656_);
lean_ctor_set(v___x_1700_, 3, v_x_1657_);
lean_ctor_set(v___x_1700_, 4, v_x_1658_);
lean_ctor_set(v___x_1700_, 5, v___x_1699_);
if (v_isShared_1678_ == 0)
{
lean_ctor_set(v___x_1677_, 0, v___x_1700_);
v___x_1702_ = v___x_1677_;
goto v_reusejp_1701_;
}
else
{
lean_object* v_reuseFailAlloc_1706_; 
v_reuseFailAlloc_1706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1706_, 0, v___x_1700_);
v___x_1702_ = v_reuseFailAlloc_1706_;
goto v_reusejp_1701_;
}
v_reusejp_1701_:
{
lean_object* v___x_1704_; 
if (v_isShared_1682_ == 0)
{
lean_ctor_set_tag(v___x_1681_, 0);
lean_ctor_set(v___x_1681_, 0, v___x_1702_);
v___x_1704_ = v___x_1681_;
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
}
else
{
lean_object* v___x_1707_; lean_object* v___x_1709_; 
lean_dec_ref(v_val_1679_);
lean_del_object(v___x_1677_);
lean_dec_ref_known(v_x_1657_, 2);
lean_dec_ref(v_x_1658_);
lean_dec_ref(v_a_1656_);
v___x_1707_ = lean_box(0);
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
else
{
lean_object* v___x_1711_; lean_object* v___x_1713_; 
lean_dec_ref(v_val_1679_);
lean_del_object(v___x_1677_);
lean_dec_ref_known(v_x_1657_, 2);
lean_dec_ref(v_x_1658_);
lean_dec_ref(v_a_1656_);
lean_dec_ref(v___x_1655_);
v___x_1711_ = lean_box(0);
if (v_isShared_1682_ == 0)
{
lean_ctor_set_tag(v___x_1681_, 0);
lean_ctor_set(v___x_1681_, 0, v___x_1711_);
v___x_1713_ = v___x_1681_;
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
else
{
lean_del_object(v___x_1677_);
lean_dec(v_val_1675_);
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
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0___redArg___boxed(lean_object* v___y_1717_, lean_object* v___x_1718_, lean_object* v_a_1719_, lean_object* v_x_1720_, lean_object* v_x_1721_, lean_object* v_x_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_){
_start:
{
uint8_t v___y_2098__boxed_1725_; lean_object* v_res_1726_; 
v___y_2098__boxed_1725_ = lean_unbox(v___y_1717_);
v_res_1726_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0___redArg(v___y_2098__boxed_1725_, v___x_1718_, v_a_1719_, v_x_1720_, v_x_1721_, v_x_1722_, v___y_1723_);
lean_dec(v___y_1723_);
return v_res_1726_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f(lean_object* v_majorFVarId_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_){
_start:
{
lean_object* v___x_1733_; lean_object* v_env_1734_; uint8_t v___y_1736_; lean_object* v___x_1766_; uint8_t v___x_1767_; uint8_t v___x_1768_; uint8_t v___x_1769_; 
v___x_1733_ = lean_st_ref_get(v_a_1731_);
v_env_1734_ = lean_ctor_get(v___x_1733_, 0);
lean_inc_ref_n(v_env_1734_, 2);
lean_dec(v___x_1733_);
v___x_1766_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__5));
v___x_1767_ = 1;
v___x_1768_ = l_Lean_Environment_contains(v_env_1734_, v___x_1766_, v___x_1767_);
v___x_1769_ = lean_bool_not(v___x_1768_);
if (v___x_1769_ == 0)
{
lean_object* v___x_1770_; uint8_t v___x_1771_; uint8_t v___x_1772_; 
v___x_1770_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__1));
lean_inc_ref(v_env_1734_);
v___x_1771_ = l_Lean_Environment_contains(v_env_1734_, v___x_1770_, v___x_1767_);
v___x_1772_ = lean_bool_not(v___x_1771_);
v___y_1736_ = v___x_1772_;
goto v___jp_1735_;
}
else
{
v___y_1736_ = v___x_1769_;
goto v___jp_1735_;
}
v___jp_1735_:
{
if (v___y_1736_ == 0)
{
lean_object* v___x_1737_; 
v___x_1737_ = l_Lean_FVarId_getDecl___redArg(v_majorFVarId_1727_, v_a_1728_, v_a_1730_, v_a_1731_);
if (lean_obj_tag(v___x_1737_) == 0)
{
lean_object* v_a_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; 
v_a_1738_ = lean_ctor_get(v___x_1737_, 0);
lean_inc(v_a_1738_);
lean_dec_ref_known(v___x_1737_, 1);
v___x_1739_ = l_Lean_LocalDecl_type(v_a_1738_);
lean_inc(v_a_1731_);
lean_inc_ref(v_a_1730_);
lean_inc(v_a_1729_);
lean_inc_ref(v_a_1728_);
v___x_1740_ = lean_whnf(v___x_1739_, v_a_1728_, v_a_1729_, v_a_1730_, v_a_1731_);
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
v___x_1747_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0___redArg(v___y_1736_, v_env_1734_, v_a_1738_, v_a_1741_, v___x_1744_, v___x_1746_, v_a_1731_);
return v___x_1747_;
}
else
{
lean_object* v_a_1748_; lean_object* v___x_1750_; uint8_t v_isShared_1751_; uint8_t v_isSharedCheck_1755_; 
lean_dec(v_a_1738_);
lean_dec_ref(v_env_1734_);
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
lean_dec_ref(v_env_1734_);
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
else
{
lean_object* v___x_1764_; lean_object* v___x_1765_; 
lean_dec_ref(v_env_1734_);
lean_dec(v_majorFVarId_1727_);
v___x_1764_ = lean_box(0);
v___x_1765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1765_, 0, v___x_1764_);
return v___x_1765_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f___boxed(lean_object* v_majorFVarId_1773_, lean_object* v_a_1774_, lean_object* v_a_1775_, lean_object* v_a_1776_, lean_object* v_a_1777_, lean_object* v_a_1778_){
_start:
{
lean_object* v_res_1779_; 
v_res_1779_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f(v_majorFVarId_1773_, v_a_1774_, v_a_1775_, v_a_1776_, v_a_1777_);
lean_dec(v_a_1777_);
lean_dec_ref(v_a_1776_);
lean_dec(v_a_1775_);
lean_dec_ref(v_a_1774_);
return v_res_1779_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0(uint8_t v___y_1780_, lean_object* v___x_1781_, lean_object* v_a_1782_, lean_object* v_x_1783_, lean_object* v_x_1784_, lean_object* v_x_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_){
_start:
{
lean_object* v___x_1791_; 
v___x_1791_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0___redArg(v___y_1780_, v___x_1781_, v_a_1782_, v_x_1783_, v_x_1784_, v_x_1785_, v___y_1789_);
return v___x_1791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0___boxed(lean_object* v___y_1792_, lean_object* v___x_1793_, lean_object* v_a_1794_, lean_object* v_x_1795_, lean_object* v_x_1796_, lean_object* v_x_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_){
_start:
{
uint8_t v___y_2309__boxed_1803_; lean_object* v_res_1804_; 
v___y_2309__boxed_1803_ = lean_unbox(v___y_1792_);
v_res_1804_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0(v___y_2309__boxed_1803_, v___x_1793_, v_a_1794_, v_x_1795_, v_x_1796_, v_x_1797_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_);
lean_dec(v___y_1801_);
lean_dec_ref(v___y_1800_);
lean_dec(v___y_1799_);
lean_dec_ref(v___y_1798_);
return v_res_1804_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0___redArg(lean_object* v___x_1805_, lean_object* v_i_1806_, lean_object* v_n_1807_, lean_object* v_i_1808_){
_start:
{
lean_object* v_zero_1809_; uint8_t v_isZero_1810_; 
v_zero_1809_ = lean_unsigned_to_nat(0u);
v_isZero_1810_ = lean_nat_dec_eq(v_i_1808_, v_zero_1809_);
if (v_isZero_1810_ == 1)
{
uint8_t v___x_1811_; 
lean_dec(v_i_1808_);
v___x_1811_ = 0;
return v___x_1811_;
}
else
{
lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; uint8_t v___x_1815_; 
v___x_1812_ = lean_nat_sub(v_n_1807_, v_i_1808_);
v___x_1813_ = lean_array_fget_borrowed(v___x_1805_, v_i_1806_);
v___x_1814_ = lean_array_fget_borrowed(v___x_1805_, v___x_1812_);
lean_dec(v___x_1812_);
v___x_1815_ = lean_expr_eqv(v___x_1813_, v___x_1814_);
if (v___x_1815_ == 0)
{
lean_object* v_one_1816_; lean_object* v_n_1817_; 
v_one_1816_ = lean_unsigned_to_nat(1u);
v_n_1817_ = lean_nat_sub(v_i_1808_, v_one_1816_);
lean_dec(v_i_1808_);
v_i_1808_ = v_n_1817_;
goto _start;
}
else
{
lean_dec(v_i_1808_);
return v___x_1815_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0___redArg___boxed(lean_object* v___x_1819_, lean_object* v_i_1820_, lean_object* v_n_1821_, lean_object* v_i_1822_){
_start:
{
uint8_t v_res_1823_; lean_object* v_r_1824_; 
v_res_1823_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0___redArg(v___x_1819_, v_i_1820_, v_n_1821_, v_i_1822_);
lean_dec(v_n_1821_);
lean_dec(v_i_1820_);
lean_dec_ref(v___x_1819_);
v_r_1824_ = lean_box(v_res_1823_);
return v_r_1824_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__3___redArg(lean_object* v___x_1825_, lean_object* v_n_1826_, lean_object* v_i_1827_){
_start:
{
lean_object* v_zero_1828_; uint8_t v_isZero_1829_; 
v_zero_1828_ = lean_unsigned_to_nat(0u);
v_isZero_1829_ = lean_nat_dec_eq(v_i_1827_, v_zero_1828_);
if (v_isZero_1829_ == 1)
{
uint8_t v___x_1830_; 
lean_dec(v_i_1827_);
v___x_1830_ = 0;
return v___x_1830_;
}
else
{
lean_object* v___x_1831_; uint8_t v___x_1832_; 
v___x_1831_ = lean_nat_sub(v_n_1826_, v_i_1827_);
lean_inc(v___x_1831_);
v___x_1832_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0___redArg(v___x_1825_, v___x_1831_, v___x_1831_, v___x_1831_);
lean_dec(v___x_1831_);
if (v___x_1832_ == 0)
{
lean_object* v_one_1833_; lean_object* v_n_1834_; 
v_one_1833_ = lean_unsigned_to_nat(1u);
v_n_1834_ = lean_nat_sub(v_i_1827_, v_one_1833_);
lean_dec(v_i_1827_);
v_i_1827_ = v_n_1834_;
goto _start;
}
else
{
lean_dec(v_i_1827_);
return v___x_1832_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__3___redArg___boxed(lean_object* v___x_1836_, lean_object* v_n_1837_, lean_object* v_i_1838_){
_start:
{
uint8_t v_res_1839_; lean_object* v_r_1840_; 
v_res_1839_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__3___redArg(v___x_1836_, v_n_1837_, v_i_1838_);
lean_dec(v_n_1837_);
lean_dec_ref(v___x_1836_);
v_r_1840_ = lean_box(v_res_1839_);
return v_r_1840_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5(lean_object* v_as_1841_, size_t v_i_1842_, size_t v_stop_1843_){
_start:
{
uint8_t v___x_1844_; 
v___x_1844_ = lean_usize_dec_eq(v_i_1842_, v_stop_1843_);
if (v___x_1844_ == 0)
{
lean_object* v___x_1845_; uint8_t v___x_1846_; uint8_t v___x_1847_; 
v___x_1845_ = lean_array_uget_borrowed(v_as_1841_, v_i_1842_);
v___x_1846_ = l_Lean_Expr_isFVar(v___x_1845_);
v___x_1847_ = lean_bool_not(v___x_1846_);
if (v___x_1847_ == 0)
{
size_t v___x_1848_; size_t v___x_1849_; 
v___x_1848_ = ((size_t)1ULL);
v___x_1849_ = lean_usize_add(v_i_1842_, v___x_1848_);
v_i_1842_ = v___x_1849_;
goto _start;
}
else
{
return v___x_1847_;
}
}
else
{
uint8_t v___x_1851_; 
v___x_1851_ = 0;
return v___x_1851_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5___boxed(lean_object* v_as_1852_, lean_object* v_i_1853_, lean_object* v_stop_1854_){
_start:
{
size_t v_i_boxed_1855_; size_t v_stop_boxed_1856_; uint8_t v_res_1857_; lean_object* v_r_1858_; 
v_i_boxed_1855_ = lean_unbox_usize(v_i_1853_);
lean_dec(v_i_1853_);
v_stop_boxed_1856_ = lean_unbox_usize(v_stop_1854_);
lean_dec(v_stop_1854_);
v_res_1857_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5(v_as_1852_, v_i_boxed_1855_, v_stop_boxed_1856_);
lean_dec_ref(v_as_1852_);
v_r_1858_ = lean_box(v_res_1857_);
return v_r_1858_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1(lean_object* v_fvarId_1859_, lean_object* v_as_1860_, size_t v_i_1861_, size_t v_stop_1862_){
_start:
{
uint8_t v___x_1863_; 
v___x_1863_ = lean_usize_dec_eq(v_i_1861_, v_stop_1862_);
if (v___x_1863_ == 0)
{
lean_object* v___x_1864_; lean_object* v___x_1865_; uint8_t v___x_1866_; uint8_t v___x_1867_; uint8_t v___x_1868_; 
v___x_1864_ = lean_array_uget_borrowed(v_as_1860_, v_i_1861_);
v___x_1865_ = l_Lean_Expr_fvarId_x21(v___x_1864_);
v___x_1866_ = l_Lean_instBEqFVarId_beq(v___x_1865_, v_fvarId_1859_);
lean_dec(v___x_1865_);
v___x_1867_ = lean_bool_not(v___x_1866_);
v___x_1868_ = lean_bool_not(v___x_1867_);
if (v___x_1868_ == 0)
{
size_t v___x_1869_; size_t v___x_1870_; 
v___x_1869_ = ((size_t)1ULL);
v___x_1870_ = lean_usize_add(v_i_1861_, v___x_1869_);
v_i_1861_ = v___x_1870_;
goto _start;
}
else
{
return v___x_1868_;
}
}
else
{
uint8_t v___x_1872_; 
v___x_1872_ = 0;
return v___x_1872_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1___boxed(lean_object* v_fvarId_1873_, lean_object* v_as_1874_, lean_object* v_i_1875_, lean_object* v_stop_1876_){
_start:
{
size_t v_i_boxed_1877_; size_t v_stop_boxed_1878_; uint8_t v_res_1879_; lean_object* v_r_1880_; 
v_i_boxed_1877_ = lean_unbox_usize(v_i_1875_);
lean_dec(v_i_1875_);
v_stop_boxed_1878_ = lean_unbox_usize(v_stop_1876_);
lean_dec(v_stop_1876_);
v_res_1879_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1(v_fvarId_1873_, v_as_1874_, v_i_boxed_1877_, v_stop_boxed_1878_);
lean_dec_ref(v_as_1874_);
lean_dec(v_fvarId_1873_);
v_r_1880_ = lean_box(v_res_1879_);
return v_r_1880_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___lam__1(lean_object* v___x_1881_, lean_object* v___x_1882_, uint8_t v___y_1883_, lean_object* v___x_1884_, lean_object* v_fvarId_1885_){
_start:
{
lean_object* v___y_1887_; uint8_t v___x_1894_; 
v___x_1894_ = lean_nat_dec_lt(v___x_1881_, v___x_1882_);
if (v___x_1894_ == 0)
{
uint8_t v___x_1895_; 
lean_dec(v___x_1882_);
v___x_1895_ = lean_bool_not(v___y_1883_);
return v___x_1895_;
}
else
{
lean_object* v___x_1896_; uint8_t v___x_1897_; 
v___x_1896_ = lean_array_get_size(v___x_1884_);
v___x_1897_ = lean_nat_dec_le(v___x_1882_, v___x_1896_);
if (v___x_1897_ == 0)
{
lean_dec(v___x_1882_);
v___y_1887_ = v___x_1896_;
goto v___jp_1886_;
}
else
{
v___y_1887_ = v___x_1882_;
goto v___jp_1886_;
}
}
v___jp_1886_:
{
uint8_t v___x_1888_; 
v___x_1888_ = lean_nat_dec_lt(v___x_1881_, v___y_1887_);
if (v___x_1888_ == 0)
{
uint8_t v___x_1889_; 
lean_dec(v___y_1887_);
v___x_1889_ = lean_bool_not(v___y_1883_);
return v___x_1889_;
}
else
{
size_t v___x_1890_; size_t v___x_1891_; uint8_t v___x_1892_; uint8_t v___x_1893_; 
v___x_1890_ = ((size_t)0ULL);
v___x_1891_ = lean_usize_of_nat(v___y_1887_);
lean_dec(v___y_1887_);
v___x_1892_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1(v_fvarId_1885_, v___x_1884_, v___x_1890_, v___x_1891_);
v___x_1893_ = lean_bool_not(v___x_1892_);
return v___x_1893_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___lam__1___boxed(lean_object* v___x_1898_, lean_object* v___x_1899_, lean_object* v___y_1900_, lean_object* v___x_1901_, lean_object* v_fvarId_1902_){
_start:
{
uint8_t v___y_9142__boxed_1903_; uint8_t v_res_1904_; lean_object* v_r_1905_; 
v___y_9142__boxed_1903_ = lean_unbox(v___y_1900_);
v_res_1904_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___lam__1(v___x_1898_, v___x_1899_, v___y_9142__boxed_1903_, v___x_1901_, v_fvarId_1902_);
lean_dec(v_fvarId_1902_);
lean_dec_ref(v___x_1901_);
lean_dec(v___x_1898_);
v_r_1905_ = lean_box(v_res_1904_);
return v_r_1905_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___lam__0(uint8_t v___y_1906_, lean_object* v_x_1907_){
_start:
{
return v___y_1906_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___lam__0___boxed(lean_object* v___y_1908_, lean_object* v_x_1909_){
_start:
{
uint8_t v___y_9176__boxed_1910_; uint8_t v_res_1911_; lean_object* v_r_1912_; 
v___y_9176__boxed_1910_ = lean_unbox(v___y_1908_);
v_res_1911_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___lam__0(v___y_9176__boxed_1910_, v_x_1909_);
lean_dec(v_x_1909_);
v_r_1912_ = lean_box(v_res_1911_);
return v_r_1912_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__2(lean_object* v___x_1913_, lean_object* v_as_1914_, size_t v_i_1915_, size_t v_stop_1916_){
_start:
{
uint8_t v___x_1917_; 
v___x_1917_ = lean_usize_dec_eq(v_i_1915_, v_stop_1916_);
if (v___x_1917_ == 0)
{
lean_object* v___x_1918_; lean_object* v___x_1919_; uint8_t v___x_1920_; 
v___x_1918_ = lean_array_uget_borrowed(v_as_1914_, v_i_1915_);
v___x_1919_ = l_Lean_Expr_fvarId_x21(v___x_1918_);
v___x_1920_ = l_Lean_instBEqFVarId_beq(v___x_1913_, v___x_1919_);
lean_dec(v___x_1919_);
if (v___x_1920_ == 0)
{
size_t v___x_1921_; size_t v___x_1922_; 
v___x_1921_ = ((size_t)1ULL);
v___x_1922_ = lean_usize_add(v_i_1915_, v___x_1921_);
v_i_1915_ = v___x_1922_;
goto _start;
}
else
{
return v___x_1920_;
}
}
else
{
uint8_t v___x_1924_; 
v___x_1924_ = 0;
return v___x_1924_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__2___boxed(lean_object* v___x_1925_, lean_object* v_as_1926_, lean_object* v_i_1927_, lean_object* v_stop_1928_){
_start:
{
size_t v_i_boxed_1929_; size_t v_stop_boxed_1930_; uint8_t v_res_1931_; lean_object* v_r_1932_; 
v_i_boxed_1929_ = lean_unbox_usize(v_i_1927_);
lean_dec(v_i_1927_);
v_stop_boxed_1930_ = lean_unbox_usize(v_stop_1928_);
lean_dec(v_stop_1928_);
v_res_1931_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__2(v___x_1925_, v_as_1926_, v_i_boxed_1929_, v_stop_boxed_1930_);
lean_dec_ref(v_as_1926_);
lean_dec(v___x_1925_);
v_r_1932_ = lean_box(v_res_1931_);
return v_r_1932_;
}
}
static uint8_t _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__0(void){
_start:
{
uint8_t v___x_1933_; uint8_t v___x_1934_; 
v___x_1933_ = 1;
v___x_1934_ = lean_bool_not(v___x_1933_);
return v___x_1934_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; 
v___x_1935_ = lean_box(0);
v___x_1936_ = lean_unsigned_to_nat(16u);
v___x_1937_ = lean_mk_array(v___x_1936_, v___x_1935_);
return v___x_1937_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; 
v___x_1938_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1);
v___x_1939_ = lean_unsigned_to_nat(0u);
v___x_1940_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1940_, 0, v___x_1939_);
lean_ctor_set(v___x_1940_, 1, v___x_1938_);
return v___x_1940_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg(lean_object* v___x_1941_, lean_object* v___x_1942_, lean_object* v_ctx_1943_, lean_object* v_as_1944_, size_t v_i_1945_, size_t v_stop_1946_, lean_object* v___y_1947_){
_start:
{
uint8_t v___x_1949_; 
v___x_1949_ = lean_usize_dec_eq(v_i_1945_, v_stop_1946_);
if (v___x_1949_ == 0)
{
uint8_t v___x_1950_; uint8_t v_a_1952_; uint8_t v_a_1959_; uint8_t v_fst_1962_; lean_object* v_mctx_1963_; lean_object* v___y_1979_; lean_object* v___y_1980_; lean_object* v___y_1981_; uint8_t v___y_1982_; lean_object* v___y_1983_; lean_object* v___y_1984_; uint8_t v___y_1985_; uint8_t v_fst_1992_; lean_object* v_snd_1993_; lean_object* v___y_2010_; lean_object* v___y_2011_; lean_object* v___y_2012_; lean_object* v___y_2013_; uint8_t v___y_2014_; uint8_t v___y_2015_; lean_object* v___y_2021_; lean_object* v___y_2022_; lean_object* v___y_2023_; uint8_t v_fst_2024_; lean_object* v_snd_2025_; uint8_t v___y_2031_; lean_object* v___y_2032_; lean_object* v___y_2033_; lean_object* v___y_2034_; lean_object* v___y_2035_; lean_object* v___y_2036_; uint8_t v___y_2037_; uint8_t v_fst_2046_; lean_object* v_mctx_2047_; lean_object* v___y_2063_; lean_object* v___y_2064_; uint8_t v___y_2065_; lean_object* v___y_2066_; lean_object* v___y_2067_; lean_object* v___y_2068_; uint8_t v___y_2069_; lean_object* v___x_2075_; 
v___x_1950_ = 1;
v___x_2075_ = lean_array_uget_borrowed(v_as_1944_, v_i_1945_);
if (lean_obj_tag(v___x_2075_) == 0)
{
uint8_t v___x_2076_; 
v___x_2076_ = lean_uint8_once(&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__0);
v_a_1952_ = v___x_2076_;
goto v___jp_1951_;
}
else
{
lean_object* v_val_2077_; lean_object* v_majorDecl_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; uint8_t v___x_2081_; 
v_val_2077_ = lean_ctor_get(v___x_2075_, 0);
v_majorDecl_2078_ = lean_ctor_get(v_ctx_1943_, 2);
v___x_2079_ = l_Lean_LocalDecl_fvarId(v_val_2077_);
v___x_2080_ = l_Lean_LocalDecl_fvarId(v_majorDecl_2078_);
v___x_2081_ = l_Lean_instBEqFVarId_beq(v___x_2079_, v___x_2080_);
lean_dec(v___x_2080_);
if (v___x_2081_ == 0)
{
lean_object* v___x_2082_; uint8_t v___y_2084_; lean_object* v___y_2119_; uint8_t v___x_2124_; 
v___x_2082_ = lean_unsigned_to_nat(0u);
v___x_2124_ = lean_nat_dec_lt(v___x_2082_, v___x_1942_);
if (v___x_2124_ == 0)
{
lean_dec(v___x_2079_);
v___y_2084_ = v___x_2081_;
goto v___jp_2083_;
}
else
{
lean_object* v___x_2125_; uint8_t v___x_2126_; 
v___x_2125_ = lean_array_get_size(v___x_1941_);
v___x_2126_ = lean_nat_dec_le(v___x_1942_, v___x_2125_);
if (v___x_2126_ == 0)
{
v___y_2119_ = v___x_2125_;
goto v___jp_2118_;
}
else
{
lean_inc(v___x_1942_);
v___y_2119_ = v___x_1942_;
goto v___jp_2118_;
}
}
v___jp_2083_:
{
if (v___y_2084_ == 0)
{
lean_object* v___x_2085_; lean_object* v___f_2086_; lean_object* v___x_2087_; lean_object* v___f_2088_; 
v___x_2085_ = lean_box(v___y_2084_);
v___f_2086_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2086_, 0, v___x_2085_);
v___x_2087_ = lean_box(v___y_2084_);
lean_inc_ref(v___x_1941_);
lean_inc(v___x_1942_);
v___f_2088_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_2088_, 0, v___x_2082_);
lean_closure_set(v___f_2088_, 1, v___x_1942_);
lean_closure_set(v___f_2088_, 2, v___x_2087_);
lean_closure_set(v___f_2088_, 3, v___x_1941_);
if (lean_obj_tag(v_val_2077_) == 0)
{
lean_object* v_type_2089_; lean_object* v___x_2090_; lean_object* v_mctx_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; uint8_t v___x_2094_; uint8_t v___x_2095_; 
v_type_2089_ = lean_ctor_get(v_val_2077_, 3);
v___x_2090_ = lean_st_ref_get(v___y_1947_);
v_mctx_2091_ = lean_ctor_get(v___x_2090_, 0);
lean_inc_ref_n(v_mctx_2091_, 2);
lean_dec(v___x_2090_);
v___x_2092_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__2);
v___x_2093_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2093_, 0, v___x_2092_);
lean_ctor_set(v___x_2093_, 1, v_mctx_2091_);
v___x_2094_ = l_Lean_Expr_hasFVar(v_type_2089_);
v___x_2095_ = lean_bool_not(v___x_2094_);
if (v___x_2095_ == 0)
{
lean_inc_ref(v_type_2089_);
v___y_1979_ = v_mctx_2091_;
v___y_1980_ = v___x_2093_;
v___y_1981_ = v___f_2088_;
v___y_1982_ = v___y_2084_;
v___y_1983_ = v___f_2086_;
v___y_1984_ = v_type_2089_;
v___y_1985_ = v___x_2095_;
goto v___jp_1978_;
}
else
{
uint8_t v___x_2096_; uint8_t v___x_2097_; 
v___x_2096_ = l_Lean_Expr_hasMVar(v_type_2089_);
v___x_2097_ = lean_bool_not(v___x_2096_);
lean_inc_ref(v_type_2089_);
v___y_1979_ = v_mctx_2091_;
v___y_1980_ = v___x_2093_;
v___y_1981_ = v___f_2088_;
v___y_1982_ = v___y_2084_;
v___y_1983_ = v___f_2086_;
v___y_1984_ = v_type_2089_;
v___y_1985_ = v___x_2097_;
goto v___jp_1978_;
}
}
else
{
uint8_t v_nondep_2098_; 
v_nondep_2098_ = lean_ctor_get_uint8(v_val_2077_, sizeof(void*)*5);
if (v_nondep_2098_ == 0)
{
lean_object* v_type_2099_; lean_object* v_value_2100_; lean_object* v___x_2101_; lean_object* v_mctx_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; uint8_t v___x_2105_; uint8_t v___x_2106_; 
v_type_2099_ = lean_ctor_get(v_val_2077_, 3);
v_value_2100_ = lean_ctor_get(v_val_2077_, 4);
v___x_2101_ = lean_st_ref_get(v___y_1947_);
v_mctx_2102_ = lean_ctor_get(v___x_2101_, 0);
lean_inc_ref(v_mctx_2102_);
lean_dec(v___x_2101_);
v___x_2103_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__2);
v___x_2104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2104_, 0, v___x_2103_);
lean_ctor_set(v___x_2104_, 1, v_mctx_2102_);
v___x_2105_ = l_Lean_Expr_hasFVar(v_type_2099_);
v___x_2106_ = lean_bool_not(v___x_2105_);
if (v___x_2106_ == 0)
{
lean_inc_ref(v_value_2100_);
lean_inc_ref(v_type_2099_);
v___y_2031_ = v_nondep_2098_;
v___y_2032_ = v_type_2099_;
v___y_2033_ = v_value_2100_;
v___y_2034_ = v___f_2088_;
v___y_2035_ = v___f_2086_;
v___y_2036_ = v___x_2104_;
v___y_2037_ = v___x_2106_;
goto v___jp_2030_;
}
else
{
uint8_t v___x_2107_; uint8_t v___x_2108_; 
v___x_2107_ = l_Lean_Expr_hasMVar(v_type_2099_);
v___x_2108_ = lean_bool_not(v___x_2107_);
lean_inc_ref(v_value_2100_);
lean_inc_ref(v_type_2099_);
v___y_2031_ = v_nondep_2098_;
v___y_2032_ = v_type_2099_;
v___y_2033_ = v_value_2100_;
v___y_2034_ = v___f_2088_;
v___y_2035_ = v___f_2086_;
v___y_2036_ = v___x_2104_;
v___y_2037_ = v___x_2108_;
goto v___jp_2030_;
}
}
else
{
lean_object* v_type_2109_; lean_object* v___x_2110_; lean_object* v_mctx_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; uint8_t v___x_2114_; uint8_t v___x_2115_; 
v_type_2109_ = lean_ctor_get(v_val_2077_, 3);
v___x_2110_ = lean_st_ref_get(v___y_1947_);
v_mctx_2111_ = lean_ctor_get(v___x_2110_, 0);
lean_inc_ref_n(v_mctx_2111_, 2);
lean_dec(v___x_2110_);
v___x_2112_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__2);
v___x_2113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2113_, 0, v___x_2112_);
lean_ctor_set(v___x_2113_, 1, v_mctx_2111_);
v___x_2114_ = l_Lean_Expr_hasFVar(v_type_2109_);
v___x_2115_ = lean_bool_not(v___x_2114_);
if (v___x_2115_ == 0)
{
lean_inc_ref(v_type_2109_);
v___y_2063_ = v_type_2109_;
v___y_2064_ = v___f_2088_;
v___y_2065_ = v___y_2084_;
v___y_2066_ = v___f_2086_;
v___y_2067_ = v_mctx_2111_;
v___y_2068_ = v___x_2113_;
v___y_2069_ = v___x_2115_;
goto v___jp_2062_;
}
else
{
uint8_t v___x_2116_; uint8_t v___x_2117_; 
v___x_2116_ = l_Lean_Expr_hasMVar(v_type_2109_);
v___x_2117_ = lean_bool_not(v___x_2116_);
lean_inc_ref(v_type_2109_);
v___y_2063_ = v_type_2109_;
v___y_2064_ = v___f_2088_;
v___y_2065_ = v___y_2084_;
v___y_2066_ = v___f_2086_;
v___y_2067_ = v_mctx_2111_;
v___y_2068_ = v___x_2113_;
v___y_2069_ = v___x_2117_;
goto v___jp_2062_;
}
}
}
}
else
{
v_a_1959_ = v___y_2084_;
goto v___jp_1958_;
}
}
v___jp_2118_:
{
uint8_t v___x_2120_; 
v___x_2120_ = lean_nat_dec_lt(v___x_2082_, v___y_2119_);
if (v___x_2120_ == 0)
{
lean_dec(v___y_2119_);
lean_dec(v___x_2079_);
v___y_2084_ = v___x_2081_;
goto v___jp_2083_;
}
else
{
size_t v___x_2121_; size_t v___x_2122_; uint8_t v___x_2123_; 
v___x_2121_ = ((size_t)0ULL);
v___x_2122_ = lean_usize_of_nat(v___y_2119_);
lean_dec(v___y_2119_);
v___x_2123_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__2(v___x_2079_, v___x_1941_, v___x_2121_, v___x_2122_);
lean_dec(v___x_2079_);
v___y_2084_ = v___x_2123_;
goto v___jp_2083_;
}
}
}
else
{
lean_dec(v___x_2079_);
v_a_1959_ = v___x_2081_;
goto v___jp_1958_;
}
}
v___jp_1951_:
{
if (v_a_1952_ == 0)
{
size_t v___x_1953_; size_t v___x_1954_; 
v___x_1953_ = ((size_t)1ULL);
v___x_1954_ = lean_usize_add(v_i_1945_, v___x_1953_);
v_i_1945_ = v___x_1954_;
goto _start;
}
else
{
lean_object* v___x_1956_; lean_object* v___x_1957_; 
lean_dec(v___x_1942_);
lean_dec_ref(v___x_1941_);
v___x_1956_ = lean_box(v___x_1950_);
v___x_1957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1957_, 0, v___x_1956_);
return v___x_1957_;
}
}
v___jp_1958_:
{
uint8_t v___x_1960_; 
v___x_1960_ = lean_bool_not(v_a_1959_);
v_a_1952_ = v___x_1960_;
goto v___jp_1951_;
}
v___jp_1961_:
{
lean_object* v___x_1964_; lean_object* v_cache_1965_; lean_object* v_zetaDeltaFVarIds_1966_; lean_object* v_postponed_1967_; lean_object* v_diag_1968_; lean_object* v___x_1970_; uint8_t v_isShared_1971_; uint8_t v_isSharedCheck_1976_; 
v___x_1964_ = lean_st_ref_take(v___y_1947_);
v_cache_1965_ = lean_ctor_get(v___x_1964_, 1);
v_zetaDeltaFVarIds_1966_ = lean_ctor_get(v___x_1964_, 2);
v_postponed_1967_ = lean_ctor_get(v___x_1964_, 3);
v_diag_1968_ = lean_ctor_get(v___x_1964_, 4);
v_isSharedCheck_1976_ = !lean_is_exclusive(v___x_1964_);
if (v_isSharedCheck_1976_ == 0)
{
lean_object* v_unused_1977_; 
v_unused_1977_ = lean_ctor_get(v___x_1964_, 0);
lean_dec(v_unused_1977_);
v___x_1970_ = v___x_1964_;
v_isShared_1971_ = v_isSharedCheck_1976_;
goto v_resetjp_1969_;
}
else
{
lean_inc(v_diag_1968_);
lean_inc(v_postponed_1967_);
lean_inc(v_zetaDeltaFVarIds_1966_);
lean_inc(v_cache_1965_);
lean_dec(v___x_1964_);
v___x_1970_ = lean_box(0);
v_isShared_1971_ = v_isSharedCheck_1976_;
goto v_resetjp_1969_;
}
v_resetjp_1969_:
{
lean_object* v___x_1973_; 
if (v_isShared_1971_ == 0)
{
lean_ctor_set(v___x_1970_, 0, v_mctx_1963_);
v___x_1973_ = v___x_1970_;
goto v_reusejp_1972_;
}
else
{
lean_object* v_reuseFailAlloc_1975_; 
v_reuseFailAlloc_1975_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1975_, 0, v_mctx_1963_);
lean_ctor_set(v_reuseFailAlloc_1975_, 1, v_cache_1965_);
lean_ctor_set(v_reuseFailAlloc_1975_, 2, v_zetaDeltaFVarIds_1966_);
lean_ctor_set(v_reuseFailAlloc_1975_, 3, v_postponed_1967_);
lean_ctor_set(v_reuseFailAlloc_1975_, 4, v_diag_1968_);
v___x_1973_ = v_reuseFailAlloc_1975_;
goto v_reusejp_1972_;
}
v_reusejp_1972_:
{
lean_object* v___x_1974_; 
v___x_1974_ = lean_st_ref_set(v___y_1947_, v___x_1973_);
v_a_1959_ = v_fst_1962_;
goto v___jp_1958_;
}
}
}
v___jp_1978_:
{
if (v___y_1985_ == 0)
{
lean_object* v___x_1986_; lean_object* v_snd_1987_; lean_object* v_fst_1988_; lean_object* v_mctx_1989_; uint8_t v___x_1990_; 
lean_dec_ref(v___y_1979_);
v___x_1986_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___y_1981_, v___y_1983_, v___y_1984_, v___y_1980_);
v_snd_1987_ = lean_ctor_get(v___x_1986_, 1);
lean_inc(v_snd_1987_);
v_fst_1988_ = lean_ctor_get(v___x_1986_, 0);
lean_inc(v_fst_1988_);
lean_dec_ref(v___x_1986_);
v_mctx_1989_ = lean_ctor_get(v_snd_1987_, 1);
lean_inc_ref(v_mctx_1989_);
lean_dec(v_snd_1987_);
v___x_1990_ = lean_unbox(v_fst_1988_);
lean_dec(v_fst_1988_);
v_fst_1962_ = v___x_1990_;
v_mctx_1963_ = v_mctx_1989_;
goto v___jp_1961_;
}
else
{
lean_dec_ref(v___y_1984_);
lean_dec_ref(v___y_1983_);
lean_dec_ref(v___y_1981_);
lean_dec_ref(v___y_1980_);
v_fst_1962_ = v___y_1982_;
v_mctx_1963_ = v___y_1979_;
goto v___jp_1961_;
}
}
v___jp_1991_:
{
lean_object* v_mctx_1994_; lean_object* v___x_1995_; lean_object* v_cache_1996_; lean_object* v_zetaDeltaFVarIds_1997_; lean_object* v_postponed_1998_; lean_object* v_diag_1999_; lean_object* v___x_2001_; uint8_t v_isShared_2002_; uint8_t v_isSharedCheck_2007_; 
v_mctx_1994_ = lean_ctor_get(v_snd_1993_, 1);
lean_inc_ref(v_mctx_1994_);
lean_dec_ref(v_snd_1993_);
v___x_1995_ = lean_st_ref_take(v___y_1947_);
v_cache_1996_ = lean_ctor_get(v___x_1995_, 1);
v_zetaDeltaFVarIds_1997_ = lean_ctor_get(v___x_1995_, 2);
v_postponed_1998_ = lean_ctor_get(v___x_1995_, 3);
v_diag_1999_ = lean_ctor_get(v___x_1995_, 4);
v_isSharedCheck_2007_ = !lean_is_exclusive(v___x_1995_);
if (v_isSharedCheck_2007_ == 0)
{
lean_object* v_unused_2008_; 
v_unused_2008_ = lean_ctor_get(v___x_1995_, 0);
lean_dec(v_unused_2008_);
v___x_2001_ = v___x_1995_;
v_isShared_2002_ = v_isSharedCheck_2007_;
goto v_resetjp_2000_;
}
else
{
lean_inc(v_diag_1999_);
lean_inc(v_postponed_1998_);
lean_inc(v_zetaDeltaFVarIds_1997_);
lean_inc(v_cache_1996_);
lean_dec(v___x_1995_);
v___x_2001_ = lean_box(0);
v_isShared_2002_ = v_isSharedCheck_2007_;
goto v_resetjp_2000_;
}
v_resetjp_2000_:
{
lean_object* v___x_2004_; 
if (v_isShared_2002_ == 0)
{
lean_ctor_set(v___x_2001_, 0, v_mctx_1994_);
v___x_2004_ = v___x_2001_;
goto v_reusejp_2003_;
}
else
{
lean_object* v_reuseFailAlloc_2006_; 
v_reuseFailAlloc_2006_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2006_, 0, v_mctx_1994_);
lean_ctor_set(v_reuseFailAlloc_2006_, 1, v_cache_1996_);
lean_ctor_set(v_reuseFailAlloc_2006_, 2, v_zetaDeltaFVarIds_1997_);
lean_ctor_set(v_reuseFailAlloc_2006_, 3, v_postponed_1998_);
lean_ctor_set(v_reuseFailAlloc_2006_, 4, v_diag_1999_);
v___x_2004_ = v_reuseFailAlloc_2006_;
goto v_reusejp_2003_;
}
v_reusejp_2003_:
{
lean_object* v___x_2005_; 
v___x_2005_ = lean_st_ref_set(v___y_1947_, v___x_2004_);
v_a_1959_ = v_fst_1992_;
goto v___jp_1958_;
}
}
}
v___jp_2009_:
{
if (v___y_2015_ == 0)
{
lean_object* v___x_2016_; lean_object* v_fst_2017_; lean_object* v_snd_2018_; uint8_t v___x_2019_; 
v___x_2016_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___y_2011_, v___y_2012_, v___y_2010_, v___y_2013_);
v_fst_2017_ = lean_ctor_get(v___x_2016_, 0);
lean_inc(v_fst_2017_);
v_snd_2018_ = lean_ctor_get(v___x_2016_, 1);
lean_inc(v_snd_2018_);
lean_dec_ref(v___x_2016_);
v___x_2019_ = lean_unbox(v_fst_2017_);
lean_dec(v_fst_2017_);
v_fst_1992_ = v___x_2019_;
v_snd_1993_ = v_snd_2018_;
goto v___jp_1991_;
}
else
{
lean_dec_ref(v___y_2012_);
lean_dec_ref(v___y_2011_);
lean_dec_ref(v___y_2010_);
v_fst_1992_ = v___y_2014_;
v_snd_1993_ = v___y_2013_;
goto v___jp_1991_;
}
}
v___jp_2020_:
{
uint8_t v___x_2026_; uint8_t v___x_2027_; 
v___x_2026_ = l_Lean_Expr_hasFVar(v___y_2022_);
v___x_2027_ = lean_bool_not(v___x_2026_);
if (v___x_2027_ == 0)
{
v___y_2010_ = v___y_2022_;
v___y_2011_ = v___y_2021_;
v___y_2012_ = v___y_2023_;
v___y_2013_ = v_snd_2025_;
v___y_2014_ = v_fst_2024_;
v___y_2015_ = v___x_2027_;
goto v___jp_2009_;
}
else
{
uint8_t v___x_2028_; uint8_t v___x_2029_; 
v___x_2028_ = l_Lean_Expr_hasMVar(v___y_2022_);
v___x_2029_ = lean_bool_not(v___x_2028_);
v___y_2010_ = v___y_2022_;
v___y_2011_ = v___y_2021_;
v___y_2012_ = v___y_2023_;
v___y_2013_ = v_snd_2025_;
v___y_2014_ = v_fst_2024_;
v___y_2015_ = v___x_2029_;
goto v___jp_2009_;
}
}
v___jp_2030_:
{
if (v___y_2037_ == 0)
{
lean_object* v___x_2038_; lean_object* v_fst_2039_; uint8_t v___x_2040_; 
lean_inc_ref(v___y_2035_);
lean_inc_ref(v___y_2034_);
v___x_2038_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___y_2034_, v___y_2035_, v___y_2032_, v___y_2036_);
v_fst_2039_ = lean_ctor_get(v___x_2038_, 0);
lean_inc(v_fst_2039_);
v___x_2040_ = lean_unbox(v_fst_2039_);
if (v___x_2040_ == 0)
{
lean_object* v_snd_2041_; uint8_t v___x_2042_; 
v_snd_2041_ = lean_ctor_get(v___x_2038_, 1);
lean_inc(v_snd_2041_);
lean_dec_ref(v___x_2038_);
v___x_2042_ = lean_unbox(v_fst_2039_);
lean_dec(v_fst_2039_);
v___y_2021_ = v___y_2034_;
v___y_2022_ = v___y_2033_;
v___y_2023_ = v___y_2035_;
v_fst_2024_ = v___x_2042_;
v_snd_2025_ = v_snd_2041_;
goto v___jp_2020_;
}
else
{
lean_object* v_snd_2043_; uint8_t v___x_2044_; 
lean_dec_ref(v___y_2035_);
lean_dec_ref(v___y_2034_);
lean_dec_ref(v___y_2033_);
v_snd_2043_ = lean_ctor_get(v___x_2038_, 1);
lean_inc(v_snd_2043_);
lean_dec_ref(v___x_2038_);
v___x_2044_ = lean_unbox(v_fst_2039_);
lean_dec(v_fst_2039_);
v_fst_1992_ = v___x_2044_;
v_snd_1993_ = v_snd_2043_;
goto v___jp_1991_;
}
}
else
{
lean_dec_ref(v___y_2032_);
v___y_2021_ = v___y_2034_;
v___y_2022_ = v___y_2033_;
v___y_2023_ = v___y_2035_;
v_fst_2024_ = v___y_2031_;
v_snd_2025_ = v___y_2036_;
goto v___jp_2020_;
}
}
v___jp_2045_:
{
lean_object* v___x_2048_; lean_object* v_cache_2049_; lean_object* v_zetaDeltaFVarIds_2050_; lean_object* v_postponed_2051_; lean_object* v_diag_2052_; lean_object* v___x_2054_; uint8_t v_isShared_2055_; uint8_t v_isSharedCheck_2060_; 
v___x_2048_ = lean_st_ref_take(v___y_1947_);
v_cache_2049_ = lean_ctor_get(v___x_2048_, 1);
v_zetaDeltaFVarIds_2050_ = lean_ctor_get(v___x_2048_, 2);
v_postponed_2051_ = lean_ctor_get(v___x_2048_, 3);
v_diag_2052_ = lean_ctor_get(v___x_2048_, 4);
v_isSharedCheck_2060_ = !lean_is_exclusive(v___x_2048_);
if (v_isSharedCheck_2060_ == 0)
{
lean_object* v_unused_2061_; 
v_unused_2061_ = lean_ctor_get(v___x_2048_, 0);
lean_dec(v_unused_2061_);
v___x_2054_ = v___x_2048_;
v_isShared_2055_ = v_isSharedCheck_2060_;
goto v_resetjp_2053_;
}
else
{
lean_inc(v_diag_2052_);
lean_inc(v_postponed_2051_);
lean_inc(v_zetaDeltaFVarIds_2050_);
lean_inc(v_cache_2049_);
lean_dec(v___x_2048_);
v___x_2054_ = lean_box(0);
v_isShared_2055_ = v_isSharedCheck_2060_;
goto v_resetjp_2053_;
}
v_resetjp_2053_:
{
lean_object* v___x_2057_; 
if (v_isShared_2055_ == 0)
{
lean_ctor_set(v___x_2054_, 0, v_mctx_2047_);
v___x_2057_ = v___x_2054_;
goto v_reusejp_2056_;
}
else
{
lean_object* v_reuseFailAlloc_2059_; 
v_reuseFailAlloc_2059_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2059_, 0, v_mctx_2047_);
lean_ctor_set(v_reuseFailAlloc_2059_, 1, v_cache_2049_);
lean_ctor_set(v_reuseFailAlloc_2059_, 2, v_zetaDeltaFVarIds_2050_);
lean_ctor_set(v_reuseFailAlloc_2059_, 3, v_postponed_2051_);
lean_ctor_set(v_reuseFailAlloc_2059_, 4, v_diag_2052_);
v___x_2057_ = v_reuseFailAlloc_2059_;
goto v_reusejp_2056_;
}
v_reusejp_2056_:
{
lean_object* v___x_2058_; 
v___x_2058_ = lean_st_ref_set(v___y_1947_, v___x_2057_);
v_a_1959_ = v_fst_2046_;
goto v___jp_1958_;
}
}
}
v___jp_2062_:
{
if (v___y_2069_ == 0)
{
lean_object* v___x_2070_; lean_object* v_snd_2071_; lean_object* v_fst_2072_; lean_object* v_mctx_2073_; uint8_t v___x_2074_; 
lean_dec_ref(v___y_2067_);
v___x_2070_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___y_2064_, v___y_2066_, v___y_2063_, v___y_2068_);
v_snd_2071_ = lean_ctor_get(v___x_2070_, 1);
lean_inc(v_snd_2071_);
v_fst_2072_ = lean_ctor_get(v___x_2070_, 0);
lean_inc(v_fst_2072_);
lean_dec_ref(v___x_2070_);
v_mctx_2073_ = lean_ctor_get(v_snd_2071_, 1);
lean_inc_ref(v_mctx_2073_);
lean_dec(v_snd_2071_);
v___x_2074_ = lean_unbox(v_fst_2072_);
lean_dec(v_fst_2072_);
v_fst_2046_ = v___x_2074_;
v_mctx_2047_ = v_mctx_2073_;
goto v___jp_2045_;
}
else
{
lean_dec_ref(v___y_2068_);
lean_dec_ref(v___y_2066_);
lean_dec_ref(v___y_2064_);
lean_dec_ref(v___y_2063_);
v_fst_2046_ = v___y_2065_;
v_mctx_2047_ = v___y_2067_;
goto v___jp_2045_;
}
}
}
else
{
uint8_t v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; 
lean_dec(v___x_1942_);
lean_dec_ref(v___x_1941_);
v___x_2127_ = 0;
v___x_2128_ = lean_box(v___x_2127_);
v___x_2129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2129_, 0, v___x_2128_);
return v___x_2129_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___boxed(lean_object* v___x_2130_, lean_object* v___x_2131_, lean_object* v_ctx_2132_, lean_object* v_as_2133_, lean_object* v_i_2134_, lean_object* v_stop_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_){
_start:
{
size_t v_i_boxed_2138_; size_t v_stop_boxed_2139_; lean_object* v_res_2140_; 
v_i_boxed_2138_ = lean_unbox_usize(v_i_2134_);
lean_dec(v_i_2134_);
v_stop_boxed_2139_ = lean_unbox_usize(v_stop_2135_);
lean_dec(v_stop_2135_);
v_res_2140_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg(v___x_2130_, v___x_2131_, v_ctx_2132_, v_as_2133_, v_i_boxed_2138_, v_stop_boxed_2139_, v___y_2136_);
lean_dec(v___y_2136_);
lean_dec_ref(v_as_2133_);
lean_dec_ref(v_ctx_2132_);
return v_res_2140_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4(lean_object* v___x_2141_, lean_object* v___x_2142_, lean_object* v_ctx_2143_, lean_object* v_x_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_){
_start:
{
if (lean_obj_tag(v_x_2144_) == 0)
{
lean_object* v_cs_2150_; lean_object* v___x_2152_; uint8_t v_isShared_2153_; uint8_t v_isSharedCheck_2168_; 
v_cs_2150_ = lean_ctor_get(v_x_2144_, 0);
v_isSharedCheck_2168_ = !lean_is_exclusive(v_x_2144_);
if (v_isSharedCheck_2168_ == 0)
{
v___x_2152_ = v_x_2144_;
v_isShared_2153_ = v_isSharedCheck_2168_;
goto v_resetjp_2151_;
}
else
{
lean_inc(v_cs_2150_);
lean_dec(v_x_2144_);
v___x_2152_ = lean_box(0);
v_isShared_2153_ = v_isSharedCheck_2168_;
goto v_resetjp_2151_;
}
v_resetjp_2151_:
{
lean_object* v___x_2154_; lean_object* v___x_2155_; uint8_t v___x_2156_; 
v___x_2154_ = lean_unsigned_to_nat(0u);
v___x_2155_ = lean_array_get_size(v_cs_2150_);
v___x_2156_ = lean_nat_dec_lt(v___x_2154_, v___x_2155_);
if (v___x_2156_ == 0)
{
lean_object* v___x_2157_; lean_object* v___x_2159_; 
lean_dec_ref(v_cs_2150_);
lean_dec(v___x_2142_);
lean_dec_ref(v___x_2141_);
v___x_2157_ = lean_box(v___x_2156_);
if (v_isShared_2153_ == 0)
{
lean_ctor_set(v___x_2152_, 0, v___x_2157_);
v___x_2159_ = v___x_2152_;
goto v_reusejp_2158_;
}
else
{
lean_object* v_reuseFailAlloc_2160_; 
v_reuseFailAlloc_2160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2160_, 0, v___x_2157_);
v___x_2159_ = v_reuseFailAlloc_2160_;
goto v_reusejp_2158_;
}
v_reusejp_2158_:
{
return v___x_2159_;
}
}
else
{
if (v___x_2156_ == 0)
{
lean_object* v___x_2161_; lean_object* v___x_2163_; 
lean_dec_ref(v_cs_2150_);
lean_dec(v___x_2142_);
lean_dec_ref(v___x_2141_);
v___x_2161_ = lean_box(v___x_2156_);
if (v_isShared_2153_ == 0)
{
lean_ctor_set(v___x_2152_, 0, v___x_2161_);
v___x_2163_ = v___x_2152_;
goto v_reusejp_2162_;
}
else
{
lean_object* v_reuseFailAlloc_2164_; 
v_reuseFailAlloc_2164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2164_, 0, v___x_2161_);
v___x_2163_ = v_reuseFailAlloc_2164_;
goto v_reusejp_2162_;
}
v_reusejp_2162_:
{
return v___x_2163_;
}
}
else
{
size_t v___x_2165_; size_t v___x_2166_; lean_object* v___x_2167_; 
lean_del_object(v___x_2152_);
v___x_2165_ = ((size_t)0ULL);
v___x_2166_ = lean_usize_of_nat(v___x_2155_);
v___x_2167_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4_spec__5(v___x_2141_, v___x_2142_, v_ctx_2143_, v_cs_2150_, v___x_2165_, v___x_2166_, v___y_2145_, v___y_2146_, v___y_2147_, v___y_2148_);
lean_dec_ref(v_cs_2150_);
return v___x_2167_;
}
}
}
}
else
{
lean_object* v_vs_2169_; lean_object* v___x_2171_; uint8_t v_isShared_2172_; uint8_t v_isSharedCheck_2187_; 
v_vs_2169_ = lean_ctor_get(v_x_2144_, 0);
v_isSharedCheck_2187_ = !lean_is_exclusive(v_x_2144_);
if (v_isSharedCheck_2187_ == 0)
{
v___x_2171_ = v_x_2144_;
v_isShared_2172_ = v_isSharedCheck_2187_;
goto v_resetjp_2170_;
}
else
{
lean_inc(v_vs_2169_);
lean_dec(v_x_2144_);
v___x_2171_ = lean_box(0);
v_isShared_2172_ = v_isSharedCheck_2187_;
goto v_resetjp_2170_;
}
v_resetjp_2170_:
{
lean_object* v___x_2173_; lean_object* v___x_2174_; uint8_t v___x_2175_; 
v___x_2173_ = lean_unsigned_to_nat(0u);
v___x_2174_ = lean_array_get_size(v_vs_2169_);
v___x_2175_ = lean_nat_dec_lt(v___x_2173_, v___x_2174_);
if (v___x_2175_ == 0)
{
lean_object* v___x_2176_; lean_object* v___x_2178_; 
lean_dec_ref(v_vs_2169_);
lean_dec(v___x_2142_);
lean_dec_ref(v___x_2141_);
v___x_2176_ = lean_box(v___x_2175_);
if (v_isShared_2172_ == 0)
{
lean_ctor_set_tag(v___x_2171_, 0);
lean_ctor_set(v___x_2171_, 0, v___x_2176_);
v___x_2178_ = v___x_2171_;
goto v_reusejp_2177_;
}
else
{
lean_object* v_reuseFailAlloc_2179_; 
v_reuseFailAlloc_2179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2179_, 0, v___x_2176_);
v___x_2178_ = v_reuseFailAlloc_2179_;
goto v_reusejp_2177_;
}
v_reusejp_2177_:
{
return v___x_2178_;
}
}
else
{
if (v___x_2175_ == 0)
{
lean_object* v___x_2180_; lean_object* v___x_2182_; 
lean_dec_ref(v_vs_2169_);
lean_dec(v___x_2142_);
lean_dec_ref(v___x_2141_);
v___x_2180_ = lean_box(v___x_2175_);
if (v_isShared_2172_ == 0)
{
lean_ctor_set_tag(v___x_2171_, 0);
lean_ctor_set(v___x_2171_, 0, v___x_2180_);
v___x_2182_ = v___x_2171_;
goto v_reusejp_2181_;
}
else
{
lean_object* v_reuseFailAlloc_2183_; 
v_reuseFailAlloc_2183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2183_, 0, v___x_2180_);
v___x_2182_ = v_reuseFailAlloc_2183_;
goto v_reusejp_2181_;
}
v_reusejp_2181_:
{
return v___x_2182_;
}
}
else
{
size_t v___x_2184_; size_t v___x_2185_; lean_object* v___x_2186_; 
lean_del_object(v___x_2171_);
v___x_2184_ = ((size_t)0ULL);
v___x_2185_ = lean_usize_of_nat(v___x_2174_);
v___x_2186_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg(v___x_2141_, v___x_2142_, v_ctx_2143_, v_vs_2169_, v___x_2184_, v___x_2185_, v___y_2146_);
lean_dec_ref(v_vs_2169_);
return v___x_2186_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4_spec__5(lean_object* v___x_2188_, lean_object* v___x_2189_, lean_object* v_ctx_2190_, lean_object* v_as_2191_, size_t v_i_2192_, size_t v_stop_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_){
_start:
{
uint8_t v___x_2199_; 
v___x_2199_ = lean_usize_dec_eq(v_i_2192_, v_stop_2193_);
if (v___x_2199_ == 0)
{
lean_object* v___x_2200_; lean_object* v___x_2201_; 
v___x_2200_ = lean_array_uget_borrowed(v_as_2191_, v_i_2192_);
lean_inc(v___x_2200_);
lean_inc(v___x_2189_);
lean_inc_ref(v___x_2188_);
v___x_2201_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4(v___x_2188_, v___x_2189_, v_ctx_2190_, v___x_2200_, v___y_2194_, v___y_2195_, v___y_2196_, v___y_2197_);
if (lean_obj_tag(v___x_2201_) == 0)
{
lean_object* v_a_2202_; lean_object* v___x_2204_; uint8_t v_isShared_2205_; uint8_t v_isSharedCheck_2213_; 
v_a_2202_ = lean_ctor_get(v___x_2201_, 0);
v_isSharedCheck_2213_ = !lean_is_exclusive(v___x_2201_);
if (v_isSharedCheck_2213_ == 0)
{
v___x_2204_ = v___x_2201_;
v_isShared_2205_ = v_isSharedCheck_2213_;
goto v_resetjp_2203_;
}
else
{
lean_inc(v_a_2202_);
lean_dec(v___x_2201_);
v___x_2204_ = lean_box(0);
v_isShared_2205_ = v_isSharedCheck_2213_;
goto v_resetjp_2203_;
}
v_resetjp_2203_:
{
uint8_t v___x_2206_; 
v___x_2206_ = lean_unbox(v_a_2202_);
if (v___x_2206_ == 0)
{
size_t v___x_2207_; size_t v___x_2208_; 
lean_del_object(v___x_2204_);
lean_dec(v_a_2202_);
v___x_2207_ = ((size_t)1ULL);
v___x_2208_ = lean_usize_add(v_i_2192_, v___x_2207_);
v_i_2192_ = v___x_2208_;
goto _start;
}
else
{
lean_object* v___x_2211_; 
lean_dec(v___x_2189_);
lean_dec_ref(v___x_2188_);
if (v_isShared_2205_ == 0)
{
v___x_2211_ = v___x_2204_;
goto v_reusejp_2210_;
}
else
{
lean_object* v_reuseFailAlloc_2212_; 
v_reuseFailAlloc_2212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2212_, 0, v_a_2202_);
v___x_2211_ = v_reuseFailAlloc_2212_;
goto v_reusejp_2210_;
}
v_reusejp_2210_:
{
return v___x_2211_;
}
}
}
}
else
{
lean_dec(v___x_2189_);
lean_dec_ref(v___x_2188_);
return v___x_2201_;
}
}
else
{
uint8_t v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; 
lean_dec(v___x_2189_);
lean_dec_ref(v___x_2188_);
v___x_2214_ = 0;
v___x_2215_ = lean_box(v___x_2214_);
v___x_2216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2216_, 0, v___x_2215_);
return v___x_2216_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4_spec__5___boxed(lean_object* v___x_2217_, lean_object* v___x_2218_, lean_object* v_ctx_2219_, lean_object* v_as_2220_, lean_object* v_i_2221_, lean_object* v_stop_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_){
_start:
{
size_t v_i_boxed_2228_; size_t v_stop_boxed_2229_; lean_object* v_res_2230_; 
v_i_boxed_2228_ = lean_unbox_usize(v_i_2221_);
lean_dec(v_i_2221_);
v_stop_boxed_2229_ = lean_unbox_usize(v_stop_2222_);
lean_dec(v_stop_2222_);
v_res_2230_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4_spec__5(v___x_2217_, v___x_2218_, v_ctx_2219_, v_as_2220_, v_i_boxed_2228_, v_stop_boxed_2229_, v___y_2223_, v___y_2224_, v___y_2225_, v___y_2226_);
lean_dec(v___y_2226_);
lean_dec_ref(v___y_2225_);
lean_dec(v___y_2224_);
lean_dec_ref(v___y_2223_);
lean_dec_ref(v_as_2220_);
lean_dec_ref(v_ctx_2219_);
return v_res_2230_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4___boxed(lean_object* v___x_2231_, lean_object* v___x_2232_, lean_object* v_ctx_2233_, lean_object* v_x_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_){
_start:
{
lean_object* v_res_2240_; 
v_res_2240_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4(v___x_2231_, v___x_2232_, v_ctx_2233_, v_x_2234_, v___y_2235_, v___y_2236_, v___y_2237_, v___y_2238_);
lean_dec(v___y_2238_);
lean_dec_ref(v___y_2237_);
lean_dec(v___y_2236_);
lean_dec_ref(v___y_2235_);
lean_dec_ref(v_ctx_2233_);
return v_res_2240_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4(lean_object* v___x_2241_, lean_object* v___x_2242_, lean_object* v_ctx_2243_, lean_object* v_t_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_){
_start:
{
lean_object* v_root_2250_; lean_object* v_tail_2251_; lean_object* v___x_2252_; 
v_root_2250_ = lean_ctor_get(v_t_2244_, 0);
lean_inc_ref(v_root_2250_);
v_tail_2251_ = lean_ctor_get(v_t_2244_, 1);
lean_inc_ref(v_tail_2251_);
lean_dec_ref(v_t_2244_);
lean_inc(v___x_2242_);
lean_inc_ref(v___x_2241_);
v___x_2252_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4(v___x_2241_, v___x_2242_, v_ctx_2243_, v_root_2250_, v___y_2245_, v___y_2246_, v___y_2247_, v___y_2248_);
if (lean_obj_tag(v___x_2252_) == 0)
{
lean_object* v_a_2253_; uint8_t v___x_2254_; 
v_a_2253_ = lean_ctor_get(v___x_2252_, 0);
lean_inc(v_a_2253_);
v___x_2254_ = lean_unbox(v_a_2253_);
lean_dec(v_a_2253_);
if (v___x_2254_ == 0)
{
lean_object* v___x_2255_; lean_object* v___x_2256_; uint8_t v___x_2257_; 
v___x_2255_ = lean_unsigned_to_nat(0u);
v___x_2256_ = lean_array_get_size(v_tail_2251_);
v___x_2257_ = lean_nat_dec_lt(v___x_2255_, v___x_2256_);
if (v___x_2257_ == 0)
{
lean_dec_ref(v_tail_2251_);
lean_dec(v___x_2242_);
lean_dec_ref(v___x_2241_);
return v___x_2252_;
}
else
{
if (v___x_2257_ == 0)
{
lean_dec_ref(v_tail_2251_);
lean_dec(v___x_2242_);
lean_dec_ref(v___x_2241_);
return v___x_2252_;
}
else
{
size_t v___x_2258_; size_t v___x_2259_; lean_object* v___x_2260_; 
lean_dec_ref_known(v___x_2252_, 1);
v___x_2258_ = ((size_t)0ULL);
v___x_2259_ = lean_usize_of_nat(v___x_2256_);
v___x_2260_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg(v___x_2241_, v___x_2242_, v_ctx_2243_, v_tail_2251_, v___x_2258_, v___x_2259_, v___y_2246_);
lean_dec_ref(v_tail_2251_);
return v___x_2260_;
}
}
}
else
{
lean_dec_ref(v_tail_2251_);
lean_dec(v___x_2242_);
lean_dec_ref(v___x_2241_);
return v___x_2252_;
}
}
else
{
lean_dec_ref(v_tail_2251_);
lean_dec(v___x_2242_);
lean_dec_ref(v___x_2241_);
return v___x_2252_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4___boxed(lean_object* v___x_2261_, lean_object* v___x_2262_, lean_object* v_ctx_2263_, lean_object* v_t_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_){
_start:
{
lean_object* v_res_2270_; 
v_res_2270_ = l_Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4(v___x_2261_, v___x_2262_, v_ctx_2263_, v_t_2264_, v___y_2265_, v___y_2266_, v___y_2267_, v___y_2268_);
lean_dec(v___y_2268_);
lean_dec_ref(v___y_2267_);
lean_dec(v___y_2266_);
lean_dec_ref(v___y_2265_);
lean_dec_ref(v_ctx_2263_);
return v_res_2270_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices(lean_object* v_ctx_2271_, lean_object* v_a_2272_, lean_object* v_a_2273_, lean_object* v_a_2274_, lean_object* v_a_2275_){
_start:
{
lean_object* v_majorTypeIndices_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; uint8_t v___x_2280_; uint8_t v___y_2282_; 
v_majorTypeIndices_2277_ = lean_ctor_get(v_ctx_2271_, 5);
lean_inc_ref(v_majorTypeIndices_2277_);
v___x_2278_ = lean_array_get_size(v_majorTypeIndices_2277_);
v___x_2279_ = lean_unsigned_to_nat(0u);
v___x_2280_ = lean_nat_dec_eq(v___x_2278_, v___x_2279_);
if (v___x_2280_ == 0)
{
uint8_t v___x_2302_; 
v___x_2302_ = lean_nat_dec_lt(v___x_2279_, v___x_2278_);
if (v___x_2302_ == 0)
{
v___y_2282_ = v___x_2280_;
goto v___jp_2281_;
}
else
{
if (v___x_2302_ == 0)
{
v___y_2282_ = v___x_2280_;
goto v___jp_2281_;
}
else
{
size_t v___x_2303_; size_t v___x_2304_; uint8_t v___x_2305_; 
v___x_2303_ = ((size_t)0ULL);
v___x_2304_ = lean_usize_of_nat(v___x_2278_);
v___x_2305_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5(v_majorTypeIndices_2277_, v___x_2303_, v___x_2304_);
v___y_2282_ = v___x_2305_;
goto v___jp_2281_;
}
}
}
else
{
lean_object* v___x_2306_; lean_object* v___x_2307_; 
lean_dec_ref(v_majorTypeIndices_2277_);
lean_dec_ref(v_ctx_2271_);
v___x_2306_ = lean_box(v___x_2280_);
v___x_2307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2307_, 0, v___x_2306_);
return v___x_2307_;
}
v___jp_2281_:
{
if (v___y_2282_ == 0)
{
uint8_t v___x_2283_; 
v___x_2283_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__3___redArg(v_majorTypeIndices_2277_, v___x_2278_, v___x_2278_);
if (v___x_2283_ == 0)
{
lean_object* v_lctx_2284_; lean_object* v_decls_2285_; lean_object* v___x_2286_; 
v_lctx_2284_ = lean_ctor_get(v_a_2272_, 2);
v_decls_2285_ = lean_ctor_get(v_lctx_2284_, 1);
lean_inc_ref(v_decls_2285_);
v___x_2286_ = l_Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4(v_majorTypeIndices_2277_, v___x_2278_, v_ctx_2271_, v_decls_2285_, v_a_2272_, v_a_2273_, v_a_2274_, v_a_2275_);
lean_dec_ref(v_ctx_2271_);
if (lean_obj_tag(v___x_2286_) == 0)
{
lean_object* v_a_2287_; lean_object* v___x_2289_; uint8_t v_isShared_2290_; uint8_t v_isSharedCheck_2297_; 
v_a_2287_ = lean_ctor_get(v___x_2286_, 0);
v_isSharedCheck_2297_ = !lean_is_exclusive(v___x_2286_);
if (v_isSharedCheck_2297_ == 0)
{
v___x_2289_ = v___x_2286_;
v_isShared_2290_ = v_isSharedCheck_2297_;
goto v_resetjp_2288_;
}
else
{
lean_inc(v_a_2287_);
lean_dec(v___x_2286_);
v___x_2289_ = lean_box(0);
v_isShared_2290_ = v_isSharedCheck_2297_;
goto v_resetjp_2288_;
}
v_resetjp_2288_:
{
uint8_t v___x_2291_; uint8_t v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2295_; 
v___x_2291_ = lean_unbox(v_a_2287_);
lean_dec(v_a_2287_);
v___x_2292_ = lean_bool_not(v___x_2291_);
v___x_2293_ = lean_box(v___x_2292_);
if (v_isShared_2290_ == 0)
{
lean_ctor_set(v___x_2289_, 0, v___x_2293_);
v___x_2295_ = v___x_2289_;
goto v_reusejp_2294_;
}
else
{
lean_object* v_reuseFailAlloc_2296_; 
v_reuseFailAlloc_2296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2296_, 0, v___x_2293_);
v___x_2295_ = v_reuseFailAlloc_2296_;
goto v_reusejp_2294_;
}
v_reusejp_2294_:
{
return v___x_2295_;
}
}
}
else
{
return v___x_2286_;
}
}
else
{
lean_object* v___x_2298_; lean_object* v___x_2299_; 
lean_dec_ref(v_majorTypeIndices_2277_);
lean_dec_ref(v_ctx_2271_);
v___x_2298_ = lean_box(v___y_2282_);
v___x_2299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2299_, 0, v___x_2298_);
return v___x_2299_;
}
}
else
{
lean_object* v___x_2300_; lean_object* v___x_2301_; 
lean_dec_ref(v_majorTypeIndices_2277_);
lean_dec_ref(v_ctx_2271_);
v___x_2300_ = lean_box(v___x_2280_);
v___x_2301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2301_, 0, v___x_2300_);
return v___x_2301_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___boxed(lean_object* v_ctx_2308_, lean_object* v_a_2309_, lean_object* v_a_2310_, lean_object* v_a_2311_, lean_object* v_a_2312_, lean_object* v_a_2313_){
_start:
{
lean_object* v_res_2314_; 
v_res_2314_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices(v_ctx_2308_, v_a_2309_, v_a_2310_, v_a_2311_, v_a_2312_);
lean_dec(v_a_2312_);
lean_dec_ref(v_a_2311_);
lean_dec(v_a_2310_);
lean_dec_ref(v_a_2309_);
return v_res_2314_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0(lean_object* v___x_2315_, lean_object* v_i_2316_, lean_object* v_n_2317_, lean_object* v_i_2318_, lean_object* v_a_2319_){
_start:
{
uint8_t v___x_2320_; 
v___x_2320_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0___redArg(v___x_2315_, v_i_2316_, v_n_2317_, v_i_2318_);
return v___x_2320_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0___boxed(lean_object* v___x_2321_, lean_object* v_i_2322_, lean_object* v_n_2323_, lean_object* v_i_2324_, lean_object* v_a_2325_){
_start:
{
uint8_t v_res_2326_; lean_object* v_r_2327_; 
v_res_2326_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0(v___x_2321_, v_i_2322_, v_n_2323_, v_i_2324_, v_a_2325_);
lean_dec(v_n_2323_);
lean_dec(v_i_2322_);
lean_dec_ref(v___x_2321_);
v_r_2327_ = lean_box(v_res_2326_);
return v_r_2327_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__3(lean_object* v___x_2328_, lean_object* v_n_2329_, lean_object* v_i_2330_, lean_object* v_a_2331_){
_start:
{
uint8_t v___x_2332_; 
v___x_2332_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__3___redArg(v___x_2328_, v_n_2329_, v_i_2330_);
return v___x_2332_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__3___boxed(lean_object* v___x_2333_, lean_object* v_n_2334_, lean_object* v_i_2335_, lean_object* v_a_2336_){
_start:
{
uint8_t v_res_2337_; lean_object* v_r_2338_; 
v_res_2337_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__3(v___x_2333_, v_n_2334_, v_i_2335_, v_a_2336_);
lean_dec(v_n_2334_);
lean_dec_ref(v___x_2333_);
v_r_2338_ = lean_box(v_res_2337_);
return v_r_2338_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5(lean_object* v___x_2339_, lean_object* v___x_2340_, lean_object* v_ctx_2341_, lean_object* v_as_2342_, size_t v_i_2343_, size_t v_stop_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_){
_start:
{
lean_object* v___x_2350_; 
v___x_2350_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg(v___x_2339_, v___x_2340_, v_ctx_2341_, v_as_2342_, v_i_2343_, v_stop_2344_, v___y_2346_);
return v___x_2350_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___boxed(lean_object* v___x_2351_, lean_object* v___x_2352_, lean_object* v_ctx_2353_, lean_object* v_as_2354_, lean_object* v_i_2355_, lean_object* v_stop_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_){
_start:
{
size_t v_i_boxed_2362_; size_t v_stop_boxed_2363_; lean_object* v_res_2364_; 
v_i_boxed_2362_ = lean_unbox_usize(v_i_2355_);
lean_dec(v_i_2355_);
v_stop_boxed_2363_ = lean_unbox_usize(v_stop_2356_);
lean_dec(v_stop_2356_);
v_res_2364_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5(v___x_2351_, v___x_2352_, v_ctx_2353_, v_as_2354_, v_i_boxed_2362_, v_stop_boxed_2363_, v___y_2357_, v___y_2358_, v___y_2359_, v___y_2360_);
lean_dec(v___y_2360_);
lean_dec_ref(v___y_2359_);
lean_dec(v___y_2358_);
lean_dec_ref(v___y_2357_);
lean_dec_ref(v_as_2354_);
lean_dec_ref(v_ctx_2353_);
return v_res_2364_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__0(lean_object* v_as_2365_, size_t v_i_2366_, size_t v_stop_2367_, lean_object* v_b_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_){
_start:
{
lean_object* v_a_2375_; uint8_t v___x_2379_; 
v___x_2379_ = lean_usize_dec_eq(v_i_2366_, v_stop_2367_);
if (v___x_2379_ == 0)
{
lean_object* v_toInductionSubgoal_2380_; lean_object* v_ctorName_2381_; lean_object* v_mvarId_2382_; lean_object* v_fields_2383_; lean_object* v_subst_2384_; lean_object* v___x_2386_; uint8_t v_isShared_2387_; uint8_t v_isSharedCheck_2437_; 
v_toInductionSubgoal_2380_ = lean_ctor_get(v_b_2368_, 0);
lean_inc_ref(v_toInductionSubgoal_2380_);
v_ctorName_2381_ = lean_ctor_get(v_b_2368_, 1);
v_mvarId_2382_ = lean_ctor_get(v_toInductionSubgoal_2380_, 0);
v_fields_2383_ = lean_ctor_get(v_toInductionSubgoal_2380_, 1);
v_subst_2384_ = lean_ctor_get(v_toInductionSubgoal_2380_, 2);
v_isSharedCheck_2437_ = !lean_is_exclusive(v_toInductionSubgoal_2380_);
if (v_isSharedCheck_2437_ == 0)
{
v___x_2386_ = v_toInductionSubgoal_2380_;
v_isShared_2387_ = v_isSharedCheck_2437_;
goto v_resetjp_2385_;
}
else
{
lean_inc(v_subst_2384_);
lean_inc(v_fields_2383_);
lean_inc(v_mvarId_2382_);
lean_dec(v_toInductionSubgoal_2380_);
v___x_2386_ = lean_box(0);
v_isShared_2387_ = v_isSharedCheck_2437_;
goto v_resetjp_2385_;
}
v_resetjp_2385_:
{
lean_object* v___x_2388_; lean_object* v___x_2389_; 
v___x_2388_ = lean_array_uget_borrowed(v_as_2365_, v_i_2366_);
lean_inc(v___x_2388_);
v___x_2389_ = l_Lean_Meta_FVarSubst_get(v_subst_2384_, v___x_2388_);
if (lean_obj_tag(v___x_2389_) == 1)
{
lean_object* v_fvarId_2390_; lean_object* v___x_2391_; 
v_fvarId_2390_ = lean_ctor_get(v___x_2389_, 0);
lean_inc(v_fvarId_2390_);
lean_dec_ref_known(v___x_2389_, 1);
v___x_2391_ = l_Lean_Meta_saveState___redArg(v___y_2370_, v___y_2372_);
if (lean_obj_tag(v___x_2391_) == 0)
{
lean_object* v_a_2392_; lean_object* v___x_2393_; 
v_a_2392_ = lean_ctor_get(v___x_2391_, 0);
lean_inc(v_a_2392_);
lean_dec_ref_known(v___x_2391_, 1);
v___x_2393_ = l_Lean_MVarId_clear(v_mvarId_2382_, v_fvarId_2390_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_);
if (lean_obj_tag(v___x_2393_) == 0)
{
lean_object* v___x_2395_; uint8_t v_isShared_2396_; uint8_t v_isSharedCheck_2405_; 
lean_inc(v_ctorName_2381_);
lean_dec(v_a_2392_);
v_isSharedCheck_2405_ = !lean_is_exclusive(v_b_2368_);
if (v_isSharedCheck_2405_ == 0)
{
lean_object* v_unused_2406_; lean_object* v_unused_2407_; 
v_unused_2406_ = lean_ctor_get(v_b_2368_, 1);
lean_dec(v_unused_2406_);
v_unused_2407_ = lean_ctor_get(v_b_2368_, 0);
lean_dec(v_unused_2407_);
v___x_2395_ = v_b_2368_;
v_isShared_2396_ = v_isSharedCheck_2405_;
goto v_resetjp_2394_;
}
else
{
lean_dec(v_b_2368_);
v___x_2395_ = lean_box(0);
v_isShared_2396_ = v_isSharedCheck_2405_;
goto v_resetjp_2394_;
}
v_resetjp_2394_:
{
lean_object* v_a_2397_; lean_object* v___x_2398_; lean_object* v___x_2400_; 
v_a_2397_ = lean_ctor_get(v___x_2393_, 0);
lean_inc(v_a_2397_);
lean_dec_ref_known(v___x_2393_, 1);
v___x_2398_ = l_Lean_Meta_FVarSubst_erase(v_subst_2384_, v___x_2388_);
if (v_isShared_2387_ == 0)
{
lean_ctor_set(v___x_2386_, 2, v___x_2398_);
lean_ctor_set(v___x_2386_, 0, v_a_2397_);
v___x_2400_ = v___x_2386_;
goto v_reusejp_2399_;
}
else
{
lean_object* v_reuseFailAlloc_2404_; 
v_reuseFailAlloc_2404_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2404_, 0, v_a_2397_);
lean_ctor_set(v_reuseFailAlloc_2404_, 1, v_fields_2383_);
lean_ctor_set(v_reuseFailAlloc_2404_, 2, v___x_2398_);
v___x_2400_ = v_reuseFailAlloc_2404_;
goto v_reusejp_2399_;
}
v_reusejp_2399_:
{
lean_object* v___x_2402_; 
if (v_isShared_2396_ == 0)
{
lean_ctor_set(v___x_2395_, 0, v___x_2400_);
v___x_2402_ = v___x_2395_;
goto v_reusejp_2401_;
}
else
{
lean_object* v_reuseFailAlloc_2403_; 
v_reuseFailAlloc_2403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2403_, 0, v___x_2400_);
lean_ctor_set(v_reuseFailAlloc_2403_, 1, v_ctorName_2381_);
v___x_2402_ = v_reuseFailAlloc_2403_;
goto v_reusejp_2401_;
}
v_reusejp_2401_:
{
v_a_2375_ = v___x_2402_;
goto v___jp_2374_;
}
}
}
}
else
{
lean_object* v_a_2408_; lean_object* v___x_2410_; uint8_t v_isShared_2411_; uint8_t v_isSharedCheck_2428_; 
lean_del_object(v___x_2386_);
lean_dec(v_subst_2384_);
lean_dec_ref(v_fields_2383_);
v_a_2408_ = lean_ctor_get(v___x_2393_, 0);
v_isSharedCheck_2428_ = !lean_is_exclusive(v___x_2393_);
if (v_isSharedCheck_2428_ == 0)
{
v___x_2410_ = v___x_2393_;
v_isShared_2411_ = v_isSharedCheck_2428_;
goto v_resetjp_2409_;
}
else
{
lean_inc(v_a_2408_);
lean_dec(v___x_2393_);
v___x_2410_ = lean_box(0);
v_isShared_2411_ = v_isSharedCheck_2428_;
goto v_resetjp_2409_;
}
v_resetjp_2409_:
{
lean_object* v___x_2413_; 
lean_inc(v_a_2408_);
if (v_isShared_2411_ == 0)
{
v___x_2413_ = v___x_2410_;
goto v_reusejp_2412_;
}
else
{
lean_object* v_reuseFailAlloc_2427_; 
v_reuseFailAlloc_2427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2427_, 0, v_a_2408_);
v___x_2413_ = v_reuseFailAlloc_2427_;
goto v_reusejp_2412_;
}
v_reusejp_2412_:
{
uint8_t v___y_2415_; uint8_t v___x_2425_; 
v___x_2425_ = l_Lean_Exception_isInterrupt(v_a_2408_);
if (v___x_2425_ == 0)
{
uint8_t v___x_2426_; 
v___x_2426_ = l_Lean_Exception_isRuntime(v_a_2408_);
v___y_2415_ = v___x_2426_;
goto v___jp_2414_;
}
else
{
lean_dec(v_a_2408_);
v___y_2415_ = v___x_2425_;
goto v___jp_2414_;
}
v___jp_2414_:
{
if (v___y_2415_ == 0)
{
lean_object* v___x_2416_; 
lean_dec_ref(v___x_2413_);
v___x_2416_ = l_Lean_Meta_SavedState_restore___redArg(v_a_2392_, v___y_2370_, v___y_2372_);
lean_dec(v_a_2392_);
if (lean_obj_tag(v___x_2416_) == 0)
{
lean_dec_ref_known(v___x_2416_, 1);
v_a_2375_ = v_b_2368_;
goto v___jp_2374_;
}
else
{
lean_object* v_a_2417_; lean_object* v___x_2419_; uint8_t v_isShared_2420_; uint8_t v_isSharedCheck_2424_; 
lean_dec_ref(v_b_2368_);
v_a_2417_ = lean_ctor_get(v___x_2416_, 0);
v_isSharedCheck_2424_ = !lean_is_exclusive(v___x_2416_);
if (v_isSharedCheck_2424_ == 0)
{
v___x_2419_ = v___x_2416_;
v_isShared_2420_ = v_isSharedCheck_2424_;
goto v_resetjp_2418_;
}
else
{
lean_inc(v_a_2417_);
lean_dec(v___x_2416_);
v___x_2419_ = lean_box(0);
v_isShared_2420_ = v_isSharedCheck_2424_;
goto v_resetjp_2418_;
}
v_resetjp_2418_:
{
lean_object* v___x_2422_; 
if (v_isShared_2420_ == 0)
{
v___x_2422_ = v___x_2419_;
goto v_reusejp_2421_;
}
else
{
lean_object* v_reuseFailAlloc_2423_; 
v_reuseFailAlloc_2423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2423_, 0, v_a_2417_);
v___x_2422_ = v_reuseFailAlloc_2423_;
goto v_reusejp_2421_;
}
v_reusejp_2421_:
{
return v___x_2422_;
}
}
}
}
else
{
lean_dec(v_a_2392_);
lean_dec_ref(v_b_2368_);
return v___x_2413_;
}
}
}
}
}
}
else
{
lean_object* v_a_2429_; lean_object* v___x_2431_; uint8_t v_isShared_2432_; uint8_t v_isSharedCheck_2436_; 
lean_dec(v_fvarId_2390_);
lean_del_object(v___x_2386_);
lean_dec(v_subst_2384_);
lean_dec_ref(v_fields_2383_);
lean_dec(v_mvarId_2382_);
lean_dec_ref(v_b_2368_);
v_a_2429_ = lean_ctor_get(v___x_2391_, 0);
v_isSharedCheck_2436_ = !lean_is_exclusive(v___x_2391_);
if (v_isSharedCheck_2436_ == 0)
{
v___x_2431_ = v___x_2391_;
v_isShared_2432_ = v_isSharedCheck_2436_;
goto v_resetjp_2430_;
}
else
{
lean_inc(v_a_2429_);
lean_dec(v___x_2391_);
v___x_2431_ = lean_box(0);
v_isShared_2432_ = v_isSharedCheck_2436_;
goto v_resetjp_2430_;
}
v_resetjp_2430_:
{
lean_object* v___x_2434_; 
if (v_isShared_2432_ == 0)
{
v___x_2434_ = v___x_2431_;
goto v_reusejp_2433_;
}
else
{
lean_object* v_reuseFailAlloc_2435_; 
v_reuseFailAlloc_2435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2435_, 0, v_a_2429_);
v___x_2434_ = v_reuseFailAlloc_2435_;
goto v_reusejp_2433_;
}
v_reusejp_2433_:
{
return v___x_2434_;
}
}
}
}
else
{
lean_dec_ref(v___x_2389_);
lean_del_object(v___x_2386_);
lean_dec(v_subst_2384_);
lean_dec_ref(v_fields_2383_);
lean_dec(v_mvarId_2382_);
v_a_2375_ = v_b_2368_;
goto v___jp_2374_;
}
}
}
else
{
lean_object* v___x_2438_; 
v___x_2438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2438_, 0, v_b_2368_);
return v___x_2438_;
}
v___jp_2374_:
{
size_t v___x_2376_; size_t v___x_2377_; 
v___x_2376_ = ((size_t)1ULL);
v___x_2377_ = lean_usize_add(v_i_2366_, v___x_2376_);
v_i_2366_ = v___x_2377_;
v_b_2368_ = v_a_2375_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__0___boxed(lean_object* v_as_2439_, lean_object* v_i_2440_, lean_object* v_stop_2441_, lean_object* v_b_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_){
_start:
{
size_t v_i_boxed_2448_; size_t v_stop_boxed_2449_; lean_object* v_res_2450_; 
v_i_boxed_2448_ = lean_unbox_usize(v_i_2440_);
lean_dec(v_i_2440_);
v_stop_boxed_2449_ = lean_unbox_usize(v_stop_2441_);
lean_dec(v_stop_2441_);
v_res_2450_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__0(v_as_2439_, v_i_boxed_2448_, v_stop_boxed_2449_, v_b_2442_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_);
lean_dec(v___y_2446_);
lean_dec_ref(v___y_2445_);
lean_dec(v___y_2444_);
lean_dec_ref(v___y_2443_);
lean_dec_ref(v_as_2439_);
return v_res_2450_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__1(lean_object* v_indicesFVarIds_2451_, size_t v_sz_2452_, size_t v_i_2453_, lean_object* v_bs_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_){
_start:
{
uint8_t v___x_2460_; 
v___x_2460_ = lean_usize_dec_lt(v_i_2453_, v_sz_2452_);
if (v___x_2460_ == 0)
{
lean_object* v___x_2461_; 
v___x_2461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2461_, 0, v_bs_2454_);
return v___x_2461_;
}
else
{
lean_object* v_v_2462_; lean_object* v___x_2463_; lean_object* v_bs_x27_2464_; lean_object* v_a_2466_; lean_object* v___y_2472_; lean_object* v___x_2482_; uint8_t v___x_2483_; 
v_v_2462_ = lean_array_uget(v_bs_2454_, v_i_2453_);
v___x_2463_ = lean_unsigned_to_nat(0u);
v_bs_x27_2464_ = lean_array_uset(v_bs_2454_, v_i_2453_, v___x_2463_);
v___x_2482_ = lean_array_get_size(v_indicesFVarIds_2451_);
v___x_2483_ = lean_nat_dec_lt(v___x_2463_, v___x_2482_);
if (v___x_2483_ == 0)
{
v_a_2466_ = v_v_2462_;
goto v___jp_2465_;
}
else
{
uint8_t v___x_2484_; 
v___x_2484_ = lean_nat_dec_le(v___x_2482_, v___x_2482_);
if (v___x_2484_ == 0)
{
if (v___x_2483_ == 0)
{
v_a_2466_ = v_v_2462_;
goto v___jp_2465_;
}
else
{
size_t v___x_2485_; size_t v___x_2486_; lean_object* v___x_2487_; 
v___x_2485_ = ((size_t)0ULL);
v___x_2486_ = lean_usize_of_nat(v___x_2482_);
v___x_2487_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__0(v_indicesFVarIds_2451_, v___x_2485_, v___x_2486_, v_v_2462_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_);
v___y_2472_ = v___x_2487_;
goto v___jp_2471_;
}
}
else
{
size_t v___x_2488_; size_t v___x_2489_; lean_object* v___x_2490_; 
v___x_2488_ = ((size_t)0ULL);
v___x_2489_ = lean_usize_of_nat(v___x_2482_);
v___x_2490_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__0(v_indicesFVarIds_2451_, v___x_2488_, v___x_2489_, v_v_2462_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_);
v___y_2472_ = v___x_2490_;
goto v___jp_2471_;
}
}
v___jp_2465_:
{
size_t v___x_2467_; size_t v___x_2468_; lean_object* v___x_2469_; 
v___x_2467_ = ((size_t)1ULL);
v___x_2468_ = lean_usize_add(v_i_2453_, v___x_2467_);
v___x_2469_ = lean_array_uset(v_bs_x27_2464_, v_i_2453_, v_a_2466_);
v_i_2453_ = v___x_2468_;
v_bs_2454_ = v___x_2469_;
goto _start;
}
v___jp_2471_:
{
if (lean_obj_tag(v___y_2472_) == 0)
{
lean_object* v_a_2473_; 
v_a_2473_ = lean_ctor_get(v___y_2472_, 0);
lean_inc(v_a_2473_);
lean_dec_ref_known(v___y_2472_, 1);
v_a_2466_ = v_a_2473_;
goto v___jp_2465_;
}
else
{
lean_object* v_a_2474_; lean_object* v___x_2476_; uint8_t v_isShared_2477_; uint8_t v_isSharedCheck_2481_; 
lean_dec_ref(v_bs_x27_2464_);
v_a_2474_ = lean_ctor_get(v___y_2472_, 0);
v_isSharedCheck_2481_ = !lean_is_exclusive(v___y_2472_);
if (v_isSharedCheck_2481_ == 0)
{
v___x_2476_ = v___y_2472_;
v_isShared_2477_ = v_isSharedCheck_2481_;
goto v_resetjp_2475_;
}
else
{
lean_inc(v_a_2474_);
lean_dec(v___y_2472_);
v___x_2476_ = lean_box(0);
v_isShared_2477_ = v_isSharedCheck_2481_;
goto v_resetjp_2475_;
}
v_resetjp_2475_:
{
lean_object* v___x_2479_; 
if (v_isShared_2477_ == 0)
{
v___x_2479_ = v___x_2476_;
goto v_reusejp_2478_;
}
else
{
lean_object* v_reuseFailAlloc_2480_; 
v_reuseFailAlloc_2480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2480_, 0, v_a_2474_);
v___x_2479_ = v_reuseFailAlloc_2480_;
goto v_reusejp_2478_;
}
v_reusejp_2478_:
{
return v___x_2479_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__1___boxed(lean_object* v_indicesFVarIds_2491_, lean_object* v_sz_2492_, lean_object* v_i_2493_, lean_object* v_bs_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_){
_start:
{
size_t v_sz_boxed_2500_; size_t v_i_boxed_2501_; lean_object* v_res_2502_; 
v_sz_boxed_2500_ = lean_unbox_usize(v_sz_2492_);
lean_dec(v_sz_2492_);
v_i_boxed_2501_ = lean_unbox_usize(v_i_2493_);
lean_dec(v_i_2493_);
v_res_2502_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__1(v_indicesFVarIds_2491_, v_sz_boxed_2500_, v_i_boxed_2501_, v_bs_2494_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_);
lean_dec(v___y_2498_);
lean_dec_ref(v___y_2497_);
lean_dec(v___y_2496_);
lean_dec_ref(v___y_2495_);
lean_dec_ref(v_indicesFVarIds_2491_);
return v_res_2502_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices(lean_object* v_s_u2081_2503_, lean_object* v_s_u2082_2504_, lean_object* v_a_2505_, lean_object* v_a_2506_, lean_object* v_a_2507_, lean_object* v_a_2508_){
_start:
{
lean_object* v_indicesFVarIds_2510_; size_t v_sz_2511_; size_t v___x_2512_; lean_object* v___x_2513_; 
v_indicesFVarIds_2510_ = lean_ctor_get(v_s_u2081_2503_, 1);
v_sz_2511_ = lean_array_size(v_s_u2082_2504_);
v___x_2512_ = ((size_t)0ULL);
v___x_2513_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__1(v_indicesFVarIds_2510_, v_sz_2511_, v___x_2512_, v_s_u2082_2504_, v_a_2505_, v_a_2506_, v_a_2507_, v_a_2508_);
return v___x_2513_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices___boxed(lean_object* v_s_u2081_2514_, lean_object* v_s_u2082_2515_, lean_object* v_a_2516_, lean_object* v_a_2517_, lean_object* v_a_2518_, lean_object* v_a_2519_, lean_object* v_a_2520_){
_start:
{
lean_object* v_res_2521_; 
v_res_2521_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices(v_s_u2081_2514_, v_s_u2082_2515_, v_a_2516_, v_a_2517_, v_a_2518_, v_a_2519_);
lean_dec(v_a_2519_);
lean_dec_ref(v_a_2518_);
lean_dec(v_a_2517_);
lean_dec_ref(v_a_2516_);
lean_dec_ref(v_s_u2081_2514_);
return v_res_2521_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0___redArg(lean_object* v_ctorNames_2522_, lean_object* v_us_2523_, lean_object* v_params_2524_, lean_object* v_majorFVarId_2525_, size_t v_sz_2526_, size_t v_i_2527_, lean_object* v_bs_2528_){
_start:
{
uint8_t v___x_2529_; 
v___x_2529_ = lean_usize_dec_lt(v_i_2527_, v_sz_2526_);
if (v___x_2529_ == 0)
{
lean_dec(v_majorFVarId_2525_);
lean_dec(v_us_2523_);
return v_bs_2528_;
}
else
{
lean_object* v_v_2530_; lean_object* v___x_2531_; lean_object* v_bs_x27_2532_; lean_object* v___y_2534_; lean_object* v___x_2539_; lean_object* v___x_2540_; uint8_t v___x_2541_; 
v_v_2530_ = lean_array_uget(v_bs_2528_, v_i_2527_);
v___x_2531_ = lean_unsigned_to_nat(0u);
v_bs_x27_2532_ = lean_array_uset(v_bs_2528_, v_i_2527_, v___x_2531_);
v___x_2539_ = lean_usize_to_nat(v_i_2527_);
v___x_2540_ = lean_array_get_size(v_ctorNames_2522_);
v___x_2541_ = lean_nat_dec_lt(v___x_2539_, v___x_2540_);
if (v___x_2541_ == 0)
{
lean_object* v___x_2542_; lean_object* v___x_2543_; 
lean_dec(v___x_2539_);
v___x_2542_ = lean_box(0);
v___x_2543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2543_, 0, v_v_2530_);
lean_ctor_set(v___x_2543_, 1, v___x_2542_);
v___y_2534_ = v___x_2543_;
goto v___jp_2533_;
}
else
{
lean_object* v_mvarId_2544_; lean_object* v_fields_2545_; lean_object* v_subst_2546_; lean_object* v___x_2548_; uint8_t v_isShared_2549_; uint8_t v_isSharedCheck_2561_; 
v_mvarId_2544_ = lean_ctor_get(v_v_2530_, 0);
v_fields_2545_ = lean_ctor_get(v_v_2530_, 1);
v_subst_2546_ = lean_ctor_get(v_v_2530_, 2);
v_isSharedCheck_2561_ = !lean_is_exclusive(v_v_2530_);
if (v_isSharedCheck_2561_ == 0)
{
v___x_2548_ = v_v_2530_;
v_isShared_2549_ = v_isSharedCheck_2561_;
goto v_resetjp_2547_;
}
else
{
lean_inc(v_subst_2546_);
lean_inc(v_fields_2545_);
lean_inc(v_mvarId_2544_);
lean_dec(v_v_2530_);
v___x_2548_ = lean_box(0);
v_isShared_2549_ = v_isSharedCheck_2561_;
goto v_resetjp_2547_;
}
v_resetjp_2547_:
{
lean_object* v_ctorName_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v_ctorApp_2553_; lean_object* v___x_2554_; lean_object* v_subst_2555_; lean_object* v___x_2557_; 
v_ctorName_2550_ = lean_array_fget_borrowed(v_ctorNames_2522_, v___x_2539_);
lean_dec(v___x_2539_);
lean_inc(v_us_2523_);
lean_inc(v_ctorName_2550_);
v___x_2551_ = l_Lean_mkConst(v_ctorName_2550_, v_us_2523_);
v___x_2552_ = l_Lean_mkAppN(v___x_2551_, v_params_2524_);
v_ctorApp_2553_ = l_Lean_mkAppN(v___x_2552_, v_fields_2545_);
v___x_2554_ = l_Lean_Meta_FVarSubst_erase(v_subst_2546_, v_majorFVarId_2525_);
lean_inc(v_majorFVarId_2525_);
v_subst_2555_ = l_Lean_Meta_FVarSubst_insert(v___x_2554_, v_majorFVarId_2525_, v_ctorApp_2553_);
if (v_isShared_2549_ == 0)
{
lean_ctor_set(v___x_2548_, 2, v_subst_2555_);
v___x_2557_ = v___x_2548_;
goto v_reusejp_2556_;
}
else
{
lean_object* v_reuseFailAlloc_2560_; 
v_reuseFailAlloc_2560_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2560_, 0, v_mvarId_2544_);
lean_ctor_set(v_reuseFailAlloc_2560_, 1, v_fields_2545_);
lean_ctor_set(v_reuseFailAlloc_2560_, 2, v_subst_2555_);
v___x_2557_ = v_reuseFailAlloc_2560_;
goto v_reusejp_2556_;
}
v_reusejp_2556_:
{
lean_object* v___x_2558_; lean_object* v___x_2559_; 
lean_inc(v_ctorName_2550_);
v___x_2558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2558_, 0, v_ctorName_2550_);
v___x_2559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2559_, 0, v___x_2557_);
lean_ctor_set(v___x_2559_, 1, v___x_2558_);
v___y_2534_ = v___x_2559_;
goto v___jp_2533_;
}
}
}
v___jp_2533_:
{
size_t v___x_2535_; size_t v___x_2536_; lean_object* v___x_2537_; 
v___x_2535_ = ((size_t)1ULL);
v___x_2536_ = lean_usize_add(v_i_2527_, v___x_2535_);
v___x_2537_ = lean_array_uset(v_bs_x27_2532_, v_i_2527_, v___y_2534_);
v_i_2527_ = v___x_2536_;
v_bs_2528_ = v___x_2537_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0___redArg___boxed(lean_object* v_ctorNames_2562_, lean_object* v_us_2563_, lean_object* v_params_2564_, lean_object* v_majorFVarId_2565_, lean_object* v_sz_2566_, lean_object* v_i_2567_, lean_object* v_bs_2568_){
_start:
{
size_t v_sz_boxed_2569_; size_t v_i_boxed_2570_; lean_object* v_res_2571_; 
v_sz_boxed_2569_ = lean_unbox_usize(v_sz_2566_);
lean_dec(v_sz_2566_);
v_i_boxed_2570_ = lean_unbox_usize(v_i_2567_);
lean_dec(v_i_2567_);
v_res_2571_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0___redArg(v_ctorNames_2562_, v_us_2563_, v_params_2564_, v_majorFVarId_2565_, v_sz_boxed_2569_, v_i_boxed_2570_, v_bs_2568_);
lean_dec_ref(v_params_2564_);
lean_dec_ref(v_ctorNames_2562_);
return v_res_2571_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals(lean_object* v_s_2572_, lean_object* v_ctorNames_2573_, lean_object* v_majorFVarId_2574_, lean_object* v_us_2575_, lean_object* v_params_2576_){
_start:
{
size_t v_sz_2577_; size_t v___x_2578_; lean_object* v___x_2579_; 
v_sz_2577_ = lean_array_size(v_s_2572_);
v___x_2578_ = ((size_t)0ULL);
v___x_2579_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0___redArg(v_ctorNames_2573_, v_us_2575_, v_params_2576_, v_majorFVarId_2574_, v_sz_2577_, v___x_2578_, v_s_2572_);
return v___x_2579_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals___boxed(lean_object* v_s_2580_, lean_object* v_ctorNames_2581_, lean_object* v_majorFVarId_2582_, lean_object* v_us_2583_, lean_object* v_params_2584_){
_start:
{
lean_object* v_res_2585_; 
v_res_2585_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals(v_s_2580_, v_ctorNames_2581_, v_majorFVarId_2582_, v_us_2583_, v_params_2584_);
lean_dec_ref(v_params_2584_);
lean_dec_ref(v_ctorNames_2581_);
return v_res_2585_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0(lean_object* v_ctorNames_2586_, lean_object* v_us_2587_, lean_object* v_params_2588_, lean_object* v_majorFVarId_2589_, lean_object* v_as_2590_, size_t v_sz_2591_, size_t v_i_2592_, lean_object* v_bs_2593_){
_start:
{
lean_object* v___x_2594_; 
v___x_2594_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0___redArg(v_ctorNames_2586_, v_us_2587_, v_params_2588_, v_majorFVarId_2589_, v_sz_2591_, v_i_2592_, v_bs_2593_);
return v___x_2594_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0___boxed(lean_object* v_ctorNames_2595_, lean_object* v_us_2596_, lean_object* v_params_2597_, lean_object* v_majorFVarId_2598_, lean_object* v_as_2599_, lean_object* v_sz_2600_, lean_object* v_i_2601_, lean_object* v_bs_2602_){
_start:
{
size_t v_sz_boxed_2603_; size_t v_i_boxed_2604_; lean_object* v_res_2605_; 
v_sz_boxed_2603_ = lean_unbox_usize(v_sz_2600_);
lean_dec(v_sz_2600_);
v_i_boxed_2604_ = lean_unbox_usize(v_i_2601_);
lean_dec(v_i_2601_);
v_res_2605_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0(v_ctorNames_2595_, v_us_2596_, v_params_2597_, v_majorFVarId_2598_, v_as_2599_, v_sz_boxed_2603_, v_i_boxed_2604_, v_bs_2602_);
lean_dec_ref(v_as_2599_);
lean_dec_ref(v_params_2597_);
lean_dec_ref(v_ctorNames_2595_);
return v_res_2605_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_2611_; lean_object* v___x_2612_; 
v___x_2611_ = l_Lean_maxRecDepthErrorMessage;
v___x_2612_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2612_, 0, v___x_2611_);
return v___x_2612_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_2613_; lean_object* v___x_2614_; 
v___x_2613_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__3);
v___x_2614_ = l_Lean_MessageData_ofFormat(v___x_2613_);
return v___x_2614_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; 
v___x_2615_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__4);
v___x_2616_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__2));
v___x_2617_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2617_, 0, v___x_2616_);
lean_ctor_set(v___x_2617_, 1, v___x_2615_);
return v___x_2617_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg(lean_object* v_ref_2618_){
_start:
{
lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; 
v___x_2620_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__5);
v___x_2621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2621_, 0, v_ref_2618_);
lean_ctor_set(v___x_2621_, 1, v___x_2620_);
v___x_2622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2622_, 0, v___x_2621_);
return v___x_2622_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___boxed(lean_object* v_ref_2623_, lean_object* v___y_2624_){
_start:
{
lean_object* v_res_2625_; 
v_res_2625_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg(v_ref_2623_);
return v_res_2625_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0(lean_object* v_00_u03b1_2626_, lean_object* v_ref_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_){
_start:
{
lean_object* v___x_2633_; 
v___x_2633_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg(v_ref_2627_);
return v___x_2633_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___boxed(lean_object* v_00_u03b1_2634_, lean_object* v_ref_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_){
_start:
{
lean_object* v_res_2641_; 
v_res_2641_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0(v_00_u03b1_2634_, v_ref_2635_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_);
lean_dec(v___y_2639_);
lean_dec_ref(v___y_2638_);
lean_dec(v___y_2637_);
lean_dec_ref(v___y_2636_);
return v_res_2641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_unifyEqs_x3f(lean_object* v_numEqs_2643_, lean_object* v_mvarId_2644_, lean_object* v_subst_2645_, lean_object* v_caseName_x3f_2646_, lean_object* v_a_2647_, lean_object* v_a_2648_, lean_object* v_a_2649_, lean_object* v_a_2650_){
_start:
{
lean_object* v_fileName_2652_; lean_object* v_fileMap_2653_; lean_object* v_options_2654_; lean_object* v_currRecDepth_2655_; lean_object* v_maxRecDepth_2656_; lean_object* v_ref_2657_; lean_object* v_currNamespace_2658_; lean_object* v_openDecls_2659_; lean_object* v_initHeartbeats_2660_; lean_object* v_maxHeartbeats_2661_; lean_object* v_quotContext_2662_; lean_object* v_currMacroScope_2663_; uint8_t v_diag_2664_; lean_object* v_cancelTk_x3f_2665_; uint8_t v_suppressElabErrors_2666_; lean_object* v_inheritedTraceOptions_2667_; lean_object* v___x_2668_; uint8_t v___x_2669_; uint8_t v___y_2671_; uint8_t v___x_2717_; uint8_t v___x_2718_; 
v_fileName_2652_ = lean_ctor_get(v_a_2649_, 0);
lean_inc_ref(v_fileName_2652_);
v_fileMap_2653_ = lean_ctor_get(v_a_2649_, 1);
lean_inc_ref(v_fileMap_2653_);
v_options_2654_ = lean_ctor_get(v_a_2649_, 2);
lean_inc_ref(v_options_2654_);
v_currRecDepth_2655_ = lean_ctor_get(v_a_2649_, 3);
lean_inc(v_currRecDepth_2655_);
v_maxRecDepth_2656_ = lean_ctor_get(v_a_2649_, 4);
lean_inc(v_maxRecDepth_2656_);
v_ref_2657_ = lean_ctor_get(v_a_2649_, 5);
lean_inc(v_ref_2657_);
v_currNamespace_2658_ = lean_ctor_get(v_a_2649_, 6);
lean_inc(v_currNamespace_2658_);
v_openDecls_2659_ = lean_ctor_get(v_a_2649_, 7);
lean_inc(v_openDecls_2659_);
v_initHeartbeats_2660_ = lean_ctor_get(v_a_2649_, 8);
lean_inc(v_initHeartbeats_2660_);
v_maxHeartbeats_2661_ = lean_ctor_get(v_a_2649_, 9);
lean_inc(v_maxHeartbeats_2661_);
v_quotContext_2662_ = lean_ctor_get(v_a_2649_, 10);
lean_inc(v_quotContext_2662_);
v_currMacroScope_2663_ = lean_ctor_get(v_a_2649_, 11);
lean_inc(v_currMacroScope_2663_);
v_diag_2664_ = lean_ctor_get_uint8(v_a_2649_, sizeof(void*)*14);
v_cancelTk_x3f_2665_ = lean_ctor_get(v_a_2649_, 12);
lean_inc(v_cancelTk_x3f_2665_);
v_suppressElabErrors_2666_ = lean_ctor_get_uint8(v_a_2649_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2667_ = lean_ctor_get(v_a_2649_, 13);
lean_inc_ref(v_inheritedTraceOptions_2667_);
lean_dec_ref(v_a_2649_);
v___x_2668_ = lean_unsigned_to_nat(0u);
v___x_2669_ = lean_nat_dec_eq(v_numEqs_2643_, v___x_2668_);
v___x_2717_ = lean_nat_dec_eq(v_maxRecDepth_2656_, v___x_2668_);
v___x_2718_ = lean_bool_not(v___x_2717_);
if (v___x_2718_ == 0)
{
v___y_2671_ = v___x_2718_;
goto v___jp_2670_;
}
else
{
uint8_t v___x_2719_; 
v___x_2719_ = lean_nat_dec_eq(v_currRecDepth_2655_, v_maxRecDepth_2656_);
v___y_2671_ = v___x_2719_;
goto v___jp_2670_;
}
v___jp_2670_:
{
if (v___y_2671_ == 0)
{
if (v___x_2669_ == 0)
{
lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; 
v___x_2672_ = lean_unsigned_to_nat(1u);
v___x_2673_ = lean_nat_add(v_currRecDepth_2655_, v___x_2672_);
lean_dec(v_currRecDepth_2655_);
v___x_2674_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2674_, 0, v_fileName_2652_);
lean_ctor_set(v___x_2674_, 1, v_fileMap_2653_);
lean_ctor_set(v___x_2674_, 2, v_options_2654_);
lean_ctor_set(v___x_2674_, 3, v___x_2673_);
lean_ctor_set(v___x_2674_, 4, v_maxRecDepth_2656_);
lean_ctor_set(v___x_2674_, 5, v_ref_2657_);
lean_ctor_set(v___x_2674_, 6, v_currNamespace_2658_);
lean_ctor_set(v___x_2674_, 7, v_openDecls_2659_);
lean_ctor_set(v___x_2674_, 8, v_initHeartbeats_2660_);
lean_ctor_set(v___x_2674_, 9, v_maxHeartbeats_2661_);
lean_ctor_set(v___x_2674_, 10, v_quotContext_2662_);
lean_ctor_set(v___x_2674_, 11, v_currMacroScope_2663_);
lean_ctor_set(v___x_2674_, 12, v_cancelTk_x3f_2665_);
lean_ctor_set(v___x_2674_, 13, v_inheritedTraceOptions_2667_);
lean_ctor_set_uint8(v___x_2674_, sizeof(void*)*14, v_diag_2664_);
lean_ctor_set_uint8(v___x_2674_, sizeof(void*)*14 + 1, v_suppressElabErrors_2666_);
v___x_2675_ = l_Lean_Meta_intro1Core(v_mvarId_2644_, v___y_2671_, v_a_2647_, v_a_2648_, v___x_2674_, v_a_2650_);
if (lean_obj_tag(v___x_2675_) == 0)
{
lean_object* v_a_2676_; lean_object* v_fst_2677_; lean_object* v_snd_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; 
v_a_2676_ = lean_ctor_get(v___x_2675_, 0);
lean_inc(v_a_2676_);
lean_dec_ref_known(v___x_2675_, 1);
v_fst_2677_ = lean_ctor_get(v_a_2676_, 0);
lean_inc(v_fst_2677_);
v_snd_2678_ = lean_ctor_get(v_a_2676_, 1);
lean_inc(v_snd_2678_);
lean_dec(v_a_2676_);
v___x_2679_ = ((lean_object*)(l_Lean_Meta_Cases_unifyEqs_x3f___closed__0));
lean_inc(v_caseName_x3f_2646_);
v___x_2680_ = l_Lean_Meta_unifyEq_x3f(v_snd_2678_, v_fst_2677_, v_subst_2645_, v___x_2679_, v_caseName_x3f_2646_, v_a_2647_, v_a_2648_, v___x_2674_, v_a_2650_);
if (lean_obj_tag(v___x_2680_) == 0)
{
lean_object* v_a_2681_; lean_object* v___x_2683_; uint8_t v_isShared_2684_; uint8_t v_isSharedCheck_2696_; 
v_a_2681_ = lean_ctor_get(v___x_2680_, 0);
v_isSharedCheck_2696_ = !lean_is_exclusive(v___x_2680_);
if (v_isSharedCheck_2696_ == 0)
{
v___x_2683_ = v___x_2680_;
v_isShared_2684_ = v_isSharedCheck_2696_;
goto v_resetjp_2682_;
}
else
{
lean_inc(v_a_2681_);
lean_dec(v___x_2680_);
v___x_2683_ = lean_box(0);
v_isShared_2684_ = v_isSharedCheck_2696_;
goto v_resetjp_2682_;
}
v_resetjp_2682_:
{
if (lean_obj_tag(v_a_2681_) == 1)
{
lean_object* v_val_2685_; lean_object* v_mvarId_2686_; lean_object* v_subst_2687_; lean_object* v_numNewEqs_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; 
lean_del_object(v___x_2683_);
v_val_2685_ = lean_ctor_get(v_a_2681_, 0);
lean_inc(v_val_2685_);
lean_dec_ref_known(v_a_2681_, 1);
v_mvarId_2686_ = lean_ctor_get(v_val_2685_, 0);
lean_inc(v_mvarId_2686_);
v_subst_2687_ = lean_ctor_get(v_val_2685_, 1);
lean_inc(v_subst_2687_);
v_numNewEqs_2688_ = lean_ctor_get(v_val_2685_, 2);
lean_inc(v_numNewEqs_2688_);
lean_dec(v_val_2685_);
v___x_2689_ = lean_nat_sub(v_numEqs_2643_, v___x_2672_);
lean_dec(v_numEqs_2643_);
v___x_2690_ = lean_nat_add(v___x_2689_, v_numNewEqs_2688_);
lean_dec(v_numNewEqs_2688_);
lean_dec(v___x_2689_);
v_numEqs_2643_ = v___x_2690_;
v_mvarId_2644_ = v_mvarId_2686_;
v_subst_2645_ = v_subst_2687_;
v_a_2649_ = v___x_2674_;
goto _start;
}
else
{
lean_object* v___x_2692_; lean_object* v___x_2694_; 
lean_dec(v_a_2681_);
lean_dec_ref_known(v___x_2674_, 14);
lean_dec(v_caseName_x3f_2646_);
lean_dec(v_numEqs_2643_);
v___x_2692_ = lean_box(0);
if (v_isShared_2684_ == 0)
{
lean_ctor_set(v___x_2683_, 0, v___x_2692_);
v___x_2694_ = v___x_2683_;
goto v_reusejp_2693_;
}
else
{
lean_object* v_reuseFailAlloc_2695_; 
v_reuseFailAlloc_2695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2695_, 0, v___x_2692_);
v___x_2694_ = v_reuseFailAlloc_2695_;
goto v_reusejp_2693_;
}
v_reusejp_2693_:
{
return v___x_2694_;
}
}
}
}
else
{
lean_object* v_a_2697_; lean_object* v___x_2699_; uint8_t v_isShared_2700_; uint8_t v_isSharedCheck_2704_; 
lean_dec_ref_known(v___x_2674_, 14);
lean_dec(v_caseName_x3f_2646_);
lean_dec(v_numEqs_2643_);
v_a_2697_ = lean_ctor_get(v___x_2680_, 0);
v_isSharedCheck_2704_ = !lean_is_exclusive(v___x_2680_);
if (v_isSharedCheck_2704_ == 0)
{
v___x_2699_ = v___x_2680_;
v_isShared_2700_ = v_isSharedCheck_2704_;
goto v_resetjp_2698_;
}
else
{
lean_inc(v_a_2697_);
lean_dec(v___x_2680_);
v___x_2699_ = lean_box(0);
v_isShared_2700_ = v_isSharedCheck_2704_;
goto v_resetjp_2698_;
}
v_resetjp_2698_:
{
lean_object* v___x_2702_; 
if (v_isShared_2700_ == 0)
{
v___x_2702_ = v___x_2699_;
goto v_reusejp_2701_;
}
else
{
lean_object* v_reuseFailAlloc_2703_; 
v_reuseFailAlloc_2703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2703_, 0, v_a_2697_);
v___x_2702_ = v_reuseFailAlloc_2703_;
goto v_reusejp_2701_;
}
v_reusejp_2701_:
{
return v___x_2702_;
}
}
}
}
else
{
lean_object* v_a_2705_; lean_object* v___x_2707_; uint8_t v_isShared_2708_; uint8_t v_isSharedCheck_2712_; 
lean_dec_ref_known(v___x_2674_, 14);
lean_dec(v_caseName_x3f_2646_);
lean_dec(v_subst_2645_);
lean_dec(v_numEqs_2643_);
v_a_2705_ = lean_ctor_get(v___x_2675_, 0);
v_isSharedCheck_2712_ = !lean_is_exclusive(v___x_2675_);
if (v_isSharedCheck_2712_ == 0)
{
v___x_2707_ = v___x_2675_;
v_isShared_2708_ = v_isSharedCheck_2712_;
goto v_resetjp_2706_;
}
else
{
lean_inc(v_a_2705_);
lean_dec(v___x_2675_);
v___x_2707_ = lean_box(0);
v_isShared_2708_ = v_isSharedCheck_2712_;
goto v_resetjp_2706_;
}
v_resetjp_2706_:
{
lean_object* v___x_2710_; 
if (v_isShared_2708_ == 0)
{
v___x_2710_ = v___x_2707_;
goto v_reusejp_2709_;
}
else
{
lean_object* v_reuseFailAlloc_2711_; 
v_reuseFailAlloc_2711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2711_, 0, v_a_2705_);
v___x_2710_ = v_reuseFailAlloc_2711_;
goto v_reusejp_2709_;
}
v_reusejp_2709_:
{
return v___x_2710_;
}
}
}
}
else
{
lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; 
lean_dec_ref(v_inheritedTraceOptions_2667_);
lean_dec(v_cancelTk_x3f_2665_);
lean_dec(v_currMacroScope_2663_);
lean_dec(v_quotContext_2662_);
lean_dec(v_maxHeartbeats_2661_);
lean_dec(v_initHeartbeats_2660_);
lean_dec(v_openDecls_2659_);
lean_dec(v_currNamespace_2658_);
lean_dec(v_ref_2657_);
lean_dec(v_maxRecDepth_2656_);
lean_dec(v_currRecDepth_2655_);
lean_dec_ref(v_options_2654_);
lean_dec_ref(v_fileMap_2653_);
lean_dec_ref(v_fileName_2652_);
lean_dec(v_caseName_x3f_2646_);
lean_dec(v_numEqs_2643_);
v___x_2713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2713_, 0, v_mvarId_2644_);
lean_ctor_set(v___x_2713_, 1, v_subst_2645_);
v___x_2714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2714_, 0, v___x_2713_);
v___x_2715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2715_, 0, v___x_2714_);
return v___x_2715_;
}
}
else
{
lean_object* v___x_2716_; 
lean_dec_ref(v_inheritedTraceOptions_2667_);
lean_dec(v_cancelTk_x3f_2665_);
lean_dec(v_currMacroScope_2663_);
lean_dec(v_quotContext_2662_);
lean_dec(v_maxHeartbeats_2661_);
lean_dec(v_initHeartbeats_2660_);
lean_dec(v_openDecls_2659_);
lean_dec(v_currNamespace_2658_);
lean_dec(v_maxRecDepth_2656_);
lean_dec(v_currRecDepth_2655_);
lean_dec_ref(v_options_2654_);
lean_dec_ref(v_fileMap_2653_);
lean_dec_ref(v_fileName_2652_);
lean_dec(v_caseName_x3f_2646_);
lean_dec(v_subst_2645_);
lean_dec(v_mvarId_2644_);
lean_dec(v_numEqs_2643_);
v___x_2716_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg(v_ref_2657_);
return v___x_2716_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_unifyEqs_x3f___boxed(lean_object* v_numEqs_2720_, lean_object* v_mvarId_2721_, lean_object* v_subst_2722_, lean_object* v_caseName_x3f_2723_, lean_object* v_a_2724_, lean_object* v_a_2725_, lean_object* v_a_2726_, lean_object* v_a_2727_, lean_object* v_a_2728_){
_start:
{
lean_object* v_res_2729_; 
v_res_2729_ = l_Lean_Meta_Cases_unifyEqs_x3f(v_numEqs_2720_, v_mvarId_2721_, v_subst_2722_, v_caseName_x3f_2723_, v_a_2724_, v_a_2725_, v_a_2726_, v_a_2727_);
lean_dec(v_a_2727_);
lean_dec(v_a_2725_);
lean_dec_ref(v_a_2724_);
return v_res_2729_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__0(lean_object* v_snd_2730_, size_t v_sz_2731_, size_t v_i_2732_, lean_object* v_bs_2733_){
_start:
{
uint8_t v___x_2734_; 
v___x_2734_ = lean_usize_dec_lt(v_i_2732_, v_sz_2731_);
if (v___x_2734_ == 0)
{
lean_dec(v_snd_2730_);
return v_bs_2733_;
}
else
{
lean_object* v_v_2735_; lean_object* v___x_2736_; lean_object* v_bs_x27_2737_; lean_object* v___x_2738_; size_t v___x_2739_; size_t v___x_2740_; lean_object* v___x_2741_; 
v_v_2735_ = lean_array_uget(v_bs_2733_, v_i_2732_);
v___x_2736_ = lean_unsigned_to_nat(0u);
v_bs_x27_2737_ = lean_array_uset(v_bs_2733_, v_i_2732_, v___x_2736_);
lean_inc(v_snd_2730_);
v___x_2738_ = l_Lean_Meta_FVarSubst_apply(v_snd_2730_, v_v_2735_);
lean_dec(v_v_2735_);
v___x_2739_ = ((size_t)1ULL);
v___x_2740_ = lean_usize_add(v_i_2732_, v___x_2739_);
v___x_2741_ = lean_array_uset(v_bs_x27_2737_, v_i_2732_, v___x_2738_);
v_i_2732_ = v___x_2740_;
v_bs_2733_ = v___x_2741_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__0___boxed(lean_object* v_snd_2743_, lean_object* v_sz_2744_, lean_object* v_i_2745_, lean_object* v_bs_2746_){
_start:
{
size_t v_sz_boxed_2747_; size_t v_i_boxed_2748_; lean_object* v_res_2749_; 
v_sz_boxed_2747_ = lean_unbox_usize(v_sz_2744_);
lean_dec(v_sz_2744_);
v_i_boxed_2748_ = lean_unbox_usize(v_i_2745_);
lean_dec(v_i_2745_);
v_res_2749_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__0(v_snd_2743_, v_sz_boxed_2747_, v_i_boxed_2748_, v_bs_2746_);
return v_res_2749_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1_spec__1(lean_object* v_numEqs_2750_, lean_object* v_as_2751_, size_t v_i_2752_, size_t v_stop_2753_, lean_object* v_b_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_){
_start:
{
uint8_t v___x_2760_; 
v___x_2760_ = lean_usize_dec_eq(v_i_2752_, v_stop_2753_);
if (v___x_2760_ == 0)
{
lean_object* v___x_2761_; lean_object* v_toInductionSubgoal_2762_; lean_object* v_ctorName_2763_; lean_object* v___x_2765_; uint8_t v_isShared_2766_; uint8_t v_isSharedCheck_2802_; 
v___x_2761_ = lean_array_uget(v_as_2751_, v_i_2752_);
v_toInductionSubgoal_2762_ = lean_ctor_get(v___x_2761_, 0);
v_ctorName_2763_ = lean_ctor_get(v___x_2761_, 1);
v_isSharedCheck_2802_ = !lean_is_exclusive(v___x_2761_);
if (v_isSharedCheck_2802_ == 0)
{
v___x_2765_ = v___x_2761_;
v_isShared_2766_ = v_isSharedCheck_2802_;
goto v_resetjp_2764_;
}
else
{
lean_inc(v_ctorName_2763_);
lean_inc(v_toInductionSubgoal_2762_);
lean_dec(v___x_2761_);
v___x_2765_ = lean_box(0);
v_isShared_2766_ = v_isSharedCheck_2802_;
goto v_resetjp_2764_;
}
v_resetjp_2764_:
{
lean_object* v_mvarId_2767_; lean_object* v_fields_2768_; lean_object* v_subst_2769_; lean_object* v___x_2771_; uint8_t v_isShared_2772_; uint8_t v_isSharedCheck_2801_; 
v_mvarId_2767_ = lean_ctor_get(v_toInductionSubgoal_2762_, 0);
v_fields_2768_ = lean_ctor_get(v_toInductionSubgoal_2762_, 1);
v_subst_2769_ = lean_ctor_get(v_toInductionSubgoal_2762_, 2);
v_isSharedCheck_2801_ = !lean_is_exclusive(v_toInductionSubgoal_2762_);
if (v_isSharedCheck_2801_ == 0)
{
v___x_2771_ = v_toInductionSubgoal_2762_;
v_isShared_2772_ = v_isSharedCheck_2801_;
goto v_resetjp_2770_;
}
else
{
lean_inc(v_subst_2769_);
lean_inc(v_fields_2768_);
lean_inc(v_mvarId_2767_);
lean_dec(v_toInductionSubgoal_2762_);
v___x_2771_ = lean_box(0);
v_isShared_2772_ = v_isSharedCheck_2801_;
goto v_resetjp_2770_;
}
v_resetjp_2770_:
{
lean_object* v___x_2773_; 
lean_inc_ref(v___y_2757_);
lean_inc(v_ctorName_2763_);
lean_inc(v_numEqs_2750_);
v___x_2773_ = l_Lean_Meta_Cases_unifyEqs_x3f(v_numEqs_2750_, v_mvarId_2767_, v_subst_2769_, v_ctorName_2763_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_);
if (lean_obj_tag(v___x_2773_) == 0)
{
lean_object* v_a_2774_; lean_object* v_a_2776_; 
v_a_2774_ = lean_ctor_get(v___x_2773_, 0);
lean_inc(v_a_2774_);
lean_dec_ref_known(v___x_2773_, 1);
if (lean_obj_tag(v_a_2774_) == 0)
{
lean_del_object(v___x_2771_);
lean_dec_ref(v_fields_2768_);
lean_del_object(v___x_2765_);
lean_dec(v_ctorName_2763_);
v_a_2776_ = v_b_2754_;
goto v___jp_2775_;
}
else
{
lean_object* v_val_2780_; lean_object* v_fst_2781_; lean_object* v_snd_2782_; size_t v_sz_2783_; size_t v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2787_; 
v_val_2780_ = lean_ctor_get(v_a_2774_, 0);
lean_inc(v_val_2780_);
lean_dec_ref_known(v_a_2774_, 1);
v_fst_2781_ = lean_ctor_get(v_val_2780_, 0);
lean_inc(v_fst_2781_);
v_snd_2782_ = lean_ctor_get(v_val_2780_, 1);
lean_inc_n(v_snd_2782_, 2);
lean_dec(v_val_2780_);
v_sz_2783_ = lean_array_size(v_fields_2768_);
v___x_2784_ = ((size_t)0ULL);
v___x_2785_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__0(v_snd_2782_, v_sz_2783_, v___x_2784_, v_fields_2768_);
if (v_isShared_2772_ == 0)
{
lean_ctor_set(v___x_2771_, 2, v_snd_2782_);
lean_ctor_set(v___x_2771_, 1, v___x_2785_);
lean_ctor_set(v___x_2771_, 0, v_fst_2781_);
v___x_2787_ = v___x_2771_;
goto v_reusejp_2786_;
}
else
{
lean_object* v_reuseFailAlloc_2792_; 
v_reuseFailAlloc_2792_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2792_, 0, v_fst_2781_);
lean_ctor_set(v_reuseFailAlloc_2792_, 1, v___x_2785_);
lean_ctor_set(v_reuseFailAlloc_2792_, 2, v_snd_2782_);
v___x_2787_ = v_reuseFailAlloc_2792_;
goto v_reusejp_2786_;
}
v_reusejp_2786_:
{
lean_object* v___x_2789_; 
if (v_isShared_2766_ == 0)
{
lean_ctor_set(v___x_2765_, 0, v___x_2787_);
v___x_2789_ = v___x_2765_;
goto v_reusejp_2788_;
}
else
{
lean_object* v_reuseFailAlloc_2791_; 
v_reuseFailAlloc_2791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2791_, 0, v___x_2787_);
lean_ctor_set(v_reuseFailAlloc_2791_, 1, v_ctorName_2763_);
v___x_2789_ = v_reuseFailAlloc_2791_;
goto v_reusejp_2788_;
}
v_reusejp_2788_:
{
lean_object* v___x_2790_; 
v___x_2790_ = lean_array_push(v_b_2754_, v___x_2789_);
v_a_2776_ = v___x_2790_;
goto v___jp_2775_;
}
}
}
v___jp_2775_:
{
size_t v___x_2777_; size_t v___x_2778_; 
v___x_2777_ = ((size_t)1ULL);
v___x_2778_ = lean_usize_add(v_i_2752_, v___x_2777_);
v_i_2752_ = v___x_2778_;
v_b_2754_ = v_a_2776_;
goto _start;
}
}
else
{
lean_object* v_a_2793_; lean_object* v___x_2795_; uint8_t v_isShared_2796_; uint8_t v_isSharedCheck_2800_; 
lean_del_object(v___x_2771_);
lean_dec_ref(v_fields_2768_);
lean_del_object(v___x_2765_);
lean_dec(v_ctorName_2763_);
lean_dec_ref(v_b_2754_);
lean_dec(v_numEqs_2750_);
v_a_2793_ = lean_ctor_get(v___x_2773_, 0);
v_isSharedCheck_2800_ = !lean_is_exclusive(v___x_2773_);
if (v_isSharedCheck_2800_ == 0)
{
v___x_2795_ = v___x_2773_;
v_isShared_2796_ = v_isSharedCheck_2800_;
goto v_resetjp_2794_;
}
else
{
lean_inc(v_a_2793_);
lean_dec(v___x_2773_);
v___x_2795_ = lean_box(0);
v_isShared_2796_ = v_isSharedCheck_2800_;
goto v_resetjp_2794_;
}
v_resetjp_2794_:
{
lean_object* v___x_2798_; 
if (v_isShared_2796_ == 0)
{
v___x_2798_ = v___x_2795_;
goto v_reusejp_2797_;
}
else
{
lean_object* v_reuseFailAlloc_2799_; 
v_reuseFailAlloc_2799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2799_, 0, v_a_2793_);
v___x_2798_ = v_reuseFailAlloc_2799_;
goto v_reusejp_2797_;
}
v_reusejp_2797_:
{
return v___x_2798_;
}
}
}
}
}
}
else
{
lean_object* v___x_2803_; 
lean_dec(v_numEqs_2750_);
v___x_2803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2803_, 0, v_b_2754_);
return v___x_2803_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1_spec__1___boxed(lean_object* v_numEqs_2804_, lean_object* v_as_2805_, lean_object* v_i_2806_, lean_object* v_stop_2807_, lean_object* v_b_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_){
_start:
{
size_t v_i_boxed_2814_; size_t v_stop_boxed_2815_; lean_object* v_res_2816_; 
v_i_boxed_2814_ = lean_unbox_usize(v_i_2806_);
lean_dec(v_i_2806_);
v_stop_boxed_2815_ = lean_unbox_usize(v_stop_2807_);
lean_dec(v_stop_2807_);
v_res_2816_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1_spec__1(v_numEqs_2804_, v_as_2805_, v_i_boxed_2814_, v_stop_boxed_2815_, v_b_2808_, v___y_2809_, v___y_2810_, v___y_2811_, v___y_2812_);
lean_dec(v___y_2812_);
lean_dec_ref(v___y_2811_);
lean_dec(v___y_2810_);
lean_dec_ref(v___y_2809_);
lean_dec_ref(v_as_2805_);
return v_res_2816_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1(lean_object* v_numEqs_2819_, lean_object* v_as_2820_, lean_object* v_start_2821_, lean_object* v_stop_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_){
_start:
{
lean_object* v___x_2828_; uint8_t v___x_2829_; 
v___x_2828_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1___closed__0));
v___x_2829_ = lean_nat_dec_lt(v_start_2821_, v_stop_2822_);
if (v___x_2829_ == 0)
{
lean_object* v___x_2830_; 
lean_dec(v_numEqs_2819_);
v___x_2830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2830_, 0, v___x_2828_);
return v___x_2830_;
}
else
{
lean_object* v___x_2831_; uint8_t v___x_2832_; 
v___x_2831_ = lean_array_get_size(v_as_2820_);
v___x_2832_ = lean_nat_dec_le(v_stop_2822_, v___x_2831_);
if (v___x_2832_ == 0)
{
uint8_t v___x_2833_; 
v___x_2833_ = lean_nat_dec_lt(v_start_2821_, v___x_2831_);
if (v___x_2833_ == 0)
{
lean_object* v___x_2834_; 
lean_dec(v_numEqs_2819_);
v___x_2834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2834_, 0, v___x_2828_);
return v___x_2834_;
}
else
{
size_t v___x_2835_; size_t v___x_2836_; lean_object* v___x_2837_; 
v___x_2835_ = lean_usize_of_nat(v_start_2821_);
v___x_2836_ = lean_usize_of_nat(v___x_2831_);
v___x_2837_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1_spec__1(v_numEqs_2819_, v_as_2820_, v___x_2835_, v___x_2836_, v___x_2828_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_);
return v___x_2837_;
}
}
else
{
size_t v___x_2838_; size_t v___x_2839_; lean_object* v___x_2840_; 
v___x_2838_ = lean_usize_of_nat(v_start_2821_);
v___x_2839_ = lean_usize_of_nat(v_stop_2822_);
v___x_2840_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1_spec__1(v_numEqs_2819_, v_as_2820_, v___x_2838_, v___x_2839_, v___x_2828_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_);
return v___x_2840_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1___boxed(lean_object* v_numEqs_2841_, lean_object* v_as_2842_, lean_object* v_start_2843_, lean_object* v_stop_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_){
_start:
{
lean_object* v_res_2850_; 
v_res_2850_ = l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1(v_numEqs_2841_, v_as_2842_, v_start_2843_, v_stop_2844_, v___y_2845_, v___y_2846_, v___y_2847_, v___y_2848_);
lean_dec(v___y_2848_);
lean_dec_ref(v___y_2847_);
lean_dec(v___y_2846_);
lean_dec_ref(v___y_2845_);
lean_dec(v_stop_2844_);
lean_dec(v_start_2843_);
lean_dec_ref(v_as_2842_);
return v_res_2850_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs(lean_object* v_numEqs_2851_, lean_object* v_subgoals_2852_, lean_object* v_a_2853_, lean_object* v_a_2854_, lean_object* v_a_2855_, lean_object* v_a_2856_){
_start:
{
lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; 
v___x_2858_ = lean_unsigned_to_nat(0u);
v___x_2859_ = lean_array_get_size(v_subgoals_2852_);
v___x_2860_ = l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1(v_numEqs_2851_, v_subgoals_2852_, v___x_2858_, v___x_2859_, v_a_2853_, v_a_2854_, v_a_2855_, v_a_2856_);
return v___x_2860_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs___boxed(lean_object* v_numEqs_2861_, lean_object* v_subgoals_2862_, lean_object* v_a_2863_, lean_object* v_a_2864_, lean_object* v_a_2865_, lean_object* v_a_2866_, lean_object* v_a_2867_){
_start:
{
lean_object* v_res_2868_; 
v_res_2868_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs(v_numEqs_2861_, v_subgoals_2862_, v_a_2863_, v_a_2864_, v_a_2865_, v_a_2866_);
lean_dec(v_a_2866_);
lean_dec_ref(v_a_2865_);
lean_dec(v_a_2864_);
lean_dec_ref(v_a_2863_);
lean_dec_ref(v_subgoals_2862_);
return v_res_2868_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0(lean_object* v___x_2880_, lean_object* v_mvarId_2881_, lean_object* v_majorFVarId_2882_, lean_object* v_givenNames_2883_, lean_object* v_ctx_2884_, uint8_t v_useNatCasesAuxOn_2885_, lean_object* v_interestingCtors_x3f_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_){
_start:
{
lean_object* v___x_2892_; 
lean_inc(v___y_2890_);
lean_inc_ref(v___y_2889_);
lean_inc(v___y_2888_);
lean_inc_ref(v___y_2887_);
v___x_2892_ = lean_infer_type(v___x_2880_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_);
if (lean_obj_tag(v___x_2892_) == 0)
{
lean_object* v_a_2893_; lean_object* v___x_2894_; 
v_a_2893_ = lean_ctor_get(v___x_2892_, 0);
lean_inc(v_a_2893_);
lean_dec_ref_known(v___x_2892_, 1);
v___x_2894_ = l_Lean_Meta_getInductiveUniverseAndParams(v_a_2893_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_);
if (lean_obj_tag(v___x_2894_) == 0)
{
lean_object* v_a_2895_; lean_object* v_fst_2896_; lean_object* v_snd_2897_; lean_object* v___y_2899_; lean_object* v___y_2900_; lean_object* v___y_2901_; lean_object* v___y_2902_; lean_object* v___y_2903_; lean_object* v___y_2926_; lean_object* v___y_2927_; lean_object* v___y_2928_; lean_object* v___y_2929_; lean_object* v___y_2935_; lean_object* v___y_2936_; lean_object* v___y_2937_; lean_object* v___y_2938_; 
v_a_2895_ = lean_ctor_get(v___x_2894_, 0);
lean_inc(v_a_2895_);
lean_dec_ref_known(v___x_2894_, 1);
v_fst_2896_ = lean_ctor_get(v_a_2895_, 0);
lean_inc(v_fst_2896_);
v_snd_2897_ = lean_ctor_get(v_a_2895_, 1);
lean_inc(v_snd_2897_);
lean_dec(v_a_2895_);
if (lean_obj_tag(v_interestingCtors_x3f_2886_) == 1)
{
lean_object* v_val_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v_inductiveVal_2951_; lean_object* v_toConstantVal_2952_; lean_object* v_env_2953_; lean_object* v_ctors_2954_; lean_object* v_name_2955_; uint8_t v___y_2957_; lean_object* v___x_2992_; uint8_t v___x_2993_; uint8_t v___x_2994_; 
v_val_2948_ = lean_ctor_get(v_interestingCtors_x3f_2886_, 0);
lean_inc(v_val_2948_);
lean_dec_ref_known(v_interestingCtors_x3f_2886_, 1);
v___x_2949_ = lean_st_ref_get(v___y_2890_);
v___x_2950_ = lean_st_ref_get(v___y_2890_);
v_inductiveVal_2951_ = lean_ctor_get(v_ctx_2884_, 0);
v_toConstantVal_2952_ = lean_ctor_get(v_inductiveVal_2951_, 0);
v_env_2953_ = lean_ctor_get(v___x_2949_, 0);
lean_inc_ref(v_env_2953_);
lean_dec(v___x_2949_);
v_ctors_2954_ = lean_ctor_get(v_inductiveVal_2951_, 4);
v_name_2955_ = lean_ctor_get(v_toConstantVal_2952_, 0);
v___x_2992_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__5));
v___x_2993_ = 1;
v___x_2994_ = l_Lean_Environment_contains(v_env_2953_, v___x_2992_, v___x_2993_);
if (v___x_2994_ == 0)
{
lean_dec(v___x_2950_);
v___y_2957_ = v___x_2994_;
goto v___jp_2956_;
}
else
{
lean_object* v_env_2995_; lean_object* v___x_2996_; uint8_t v___x_2997_; 
v_env_2995_ = lean_ctor_get(v___x_2950_, 0);
lean_inc_ref(v_env_2995_);
lean_dec(v___x_2950_);
lean_inc(v_name_2955_);
v___x_2996_ = l_Lean_mkCtorIdxName(v_name_2955_);
v___x_2997_ = l_Lean_Environment_contains(v_env_2995_, v___x_2996_, v___x_2993_);
v___y_2957_ = v___x_2997_;
goto v___jp_2956_;
}
v___jp_2956_:
{
if (v___y_2957_ == 0)
{
lean_dec(v_val_2948_);
v___y_2935_ = v___y_2887_;
v___y_2936_ = v___y_2888_;
v___y_2937_ = v___y_2889_;
v___y_2938_ = v___y_2890_;
goto v___jp_2934_;
}
else
{
lean_object* v___x_2958_; lean_object* v___x_2959_; uint8_t v___x_2960_; uint8_t v___x_2961_; 
v___x_2958_ = lean_array_get_size(v_val_2948_);
v___x_2959_ = lean_unsigned_to_nat(0u);
v___x_2960_ = lean_nat_dec_eq(v___x_2958_, v___x_2959_);
v___x_2961_ = lean_bool_not(v___x_2960_);
if (v___x_2961_ == 0)
{
lean_dec(v_val_2948_);
v___y_2935_ = v___y_2887_;
v___y_2936_ = v___y_2888_;
v___y_2937_ = v___y_2889_;
v___y_2938_ = v___y_2890_;
goto v___jp_2934_;
}
else
{
lean_object* v___x_2962_; uint8_t v___x_2963_; 
v___x_2962_ = l_List_lengthTR___redArg(v_ctors_2954_);
v___x_2963_ = lean_nat_dec_lt(v___x_2958_, v___x_2962_);
lean_dec(v___x_2962_);
if (v___x_2963_ == 0)
{
lean_dec(v_val_2948_);
v___y_2935_ = v___y_2887_;
v___y_2936_ = v___y_2888_;
v___y_2937_ = v___y_2889_;
v___y_2938_ = v___y_2890_;
goto v___jp_2934_;
}
else
{
lean_object* v___x_2964_; 
lean_inc(v_name_2955_);
lean_dec_ref(v_ctx_2884_);
lean_inc(v_val_2948_);
v___x_2964_ = l_Lean_Meta_mkSparseCasesOn(v_name_2955_, v_val_2948_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_);
if (lean_obj_tag(v___x_2964_) == 0)
{
lean_object* v_a_2965_; lean_object* v___x_2966_; 
v_a_2965_ = lean_ctor_get(v___x_2964_, 0);
lean_inc(v_a_2965_);
lean_dec_ref_known(v___x_2964_, 1);
lean_inc(v_majorFVarId_2882_);
v___x_2966_ = l_Lean_MVarId_induction(v_mvarId_2881_, v_majorFVarId_2882_, v_a_2965_, v_givenNames_2883_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_);
lean_dec(v___y_2890_);
lean_dec_ref(v___y_2889_);
lean_dec(v___y_2888_);
lean_dec_ref(v___y_2887_);
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
v___x_2971_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals(v_a_2967_, v_val_2948_, v_majorFVarId_2882_, v_fst_2896_, v_snd_2897_);
lean_dec(v_snd_2897_);
lean_dec(v_val_2948_);
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
lean_dec(v_val_2948_);
lean_dec(v_snd_2897_);
lean_dec(v_fst_2896_);
lean_dec(v_majorFVarId_2882_);
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
else
{
lean_object* v_a_2984_; lean_object* v___x_2986_; uint8_t v_isShared_2987_; uint8_t v_isSharedCheck_2991_; 
lean_dec(v_val_2948_);
lean_dec(v_snd_2897_);
lean_dec(v_fst_2896_);
lean_dec(v___y_2890_);
lean_dec_ref(v___y_2889_);
lean_dec(v___y_2888_);
lean_dec_ref(v___y_2887_);
lean_dec_ref(v_givenNames_2883_);
lean_dec(v_majorFVarId_2882_);
lean_dec(v_mvarId_2881_);
v_a_2984_ = lean_ctor_get(v___x_2964_, 0);
v_isSharedCheck_2991_ = !lean_is_exclusive(v___x_2964_);
if (v_isSharedCheck_2991_ == 0)
{
v___x_2986_ = v___x_2964_;
v_isShared_2987_ = v_isSharedCheck_2991_;
goto v_resetjp_2985_;
}
else
{
lean_inc(v_a_2984_);
lean_dec(v___x_2964_);
v___x_2986_ = lean_box(0);
v_isShared_2987_ = v_isSharedCheck_2991_;
goto v_resetjp_2985_;
}
v_resetjp_2985_:
{
lean_object* v___x_2989_; 
if (v_isShared_2987_ == 0)
{
v___x_2989_ = v___x_2986_;
goto v_reusejp_2988_;
}
else
{
lean_object* v_reuseFailAlloc_2990_; 
v_reuseFailAlloc_2990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2990_, 0, v_a_2984_);
v___x_2989_ = v_reuseFailAlloc_2990_;
goto v_reusejp_2988_;
}
v_reusejp_2988_:
{
return v___x_2989_;
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
lean_dec(v_interestingCtors_x3f_2886_);
v___y_2935_ = v___y_2887_;
v___y_2936_ = v___y_2888_;
v___y_2937_ = v___y_2889_;
v___y_2938_ = v___y_2890_;
goto v___jp_2934_;
}
v___jp_2898_:
{
lean_object* v___x_2904_; 
lean_inc(v_majorFVarId_2882_);
v___x_2904_ = l_Lean_MVarId_induction(v_mvarId_2881_, v_majorFVarId_2882_, v___y_2903_, v_givenNames_2883_, v___y_2900_, v___y_2899_, v___y_2901_, v___y_2902_);
lean_dec(v___y_2902_);
lean_dec_ref(v___y_2901_);
lean_dec(v___y_2899_);
lean_dec_ref(v___y_2900_);
if (lean_obj_tag(v___x_2904_) == 0)
{
lean_object* v_inductiveVal_2905_; lean_object* v_a_2906_; lean_object* v___x_2908_; uint8_t v_isShared_2909_; uint8_t v_isSharedCheck_2916_; 
v_inductiveVal_2905_ = lean_ctor_get(v_ctx_2884_, 0);
lean_inc_ref(v_inductiveVal_2905_);
lean_dec_ref(v_ctx_2884_);
v_a_2906_ = lean_ctor_get(v___x_2904_, 0);
v_isSharedCheck_2916_ = !lean_is_exclusive(v___x_2904_);
if (v_isSharedCheck_2916_ == 0)
{
v___x_2908_ = v___x_2904_;
v_isShared_2909_ = v_isSharedCheck_2916_;
goto v_resetjp_2907_;
}
else
{
lean_inc(v_a_2906_);
lean_dec(v___x_2904_);
v___x_2908_ = lean_box(0);
v_isShared_2909_ = v_isSharedCheck_2916_;
goto v_resetjp_2907_;
}
v_resetjp_2907_:
{
lean_object* v_ctors_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2914_; 
v_ctors_2910_ = lean_ctor_get(v_inductiveVal_2905_, 4);
lean_inc(v_ctors_2910_);
lean_dec_ref(v_inductiveVal_2905_);
v___x_2911_ = lean_array_mk(v_ctors_2910_);
v___x_2912_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals(v_a_2906_, v___x_2911_, v_majorFVarId_2882_, v_fst_2896_, v_snd_2897_);
lean_dec(v_snd_2897_);
lean_dec_ref(v___x_2911_);
if (v_isShared_2909_ == 0)
{
lean_ctor_set(v___x_2908_, 0, v___x_2912_);
v___x_2914_ = v___x_2908_;
goto v_reusejp_2913_;
}
else
{
lean_object* v_reuseFailAlloc_2915_; 
v_reuseFailAlloc_2915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2915_, 0, v___x_2912_);
v___x_2914_ = v_reuseFailAlloc_2915_;
goto v_reusejp_2913_;
}
v_reusejp_2913_:
{
return v___x_2914_;
}
}
}
else
{
lean_object* v_a_2917_; lean_object* v___x_2919_; uint8_t v_isShared_2920_; uint8_t v_isSharedCheck_2924_; 
lean_dec(v_snd_2897_);
lean_dec(v_fst_2896_);
lean_dec_ref(v_ctx_2884_);
lean_dec(v_majorFVarId_2882_);
v_a_2917_ = lean_ctor_get(v___x_2904_, 0);
v_isSharedCheck_2924_ = !lean_is_exclusive(v___x_2904_);
if (v_isSharedCheck_2924_ == 0)
{
v___x_2919_ = v___x_2904_;
v_isShared_2920_ = v_isSharedCheck_2924_;
goto v_resetjp_2918_;
}
else
{
lean_inc(v_a_2917_);
lean_dec(v___x_2904_);
v___x_2919_ = lean_box(0);
v_isShared_2920_ = v_isSharedCheck_2924_;
goto v_resetjp_2918_;
}
v_resetjp_2918_:
{
lean_object* v___x_2922_; 
if (v_isShared_2920_ == 0)
{
v___x_2922_ = v___x_2919_;
goto v_reusejp_2921_;
}
else
{
lean_object* v_reuseFailAlloc_2923_; 
v_reuseFailAlloc_2923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2923_, 0, v_a_2917_);
v___x_2922_ = v_reuseFailAlloc_2923_;
goto v_reusejp_2921_;
}
v_reusejp_2921_:
{
return v___x_2922_;
}
}
}
}
v___jp_2925_:
{
lean_object* v_inductiveVal_2930_; lean_object* v_toConstantVal_2931_; lean_object* v_name_2932_; lean_object* v___x_2933_; 
v_inductiveVal_2930_ = lean_ctor_get(v_ctx_2884_, 0);
v_toConstantVal_2931_ = lean_ctor_get(v_inductiveVal_2930_, 0);
v_name_2932_ = lean_ctor_get(v_toConstantVal_2931_, 0);
lean_inc(v_name_2932_);
v___x_2933_ = l_Lean_mkCasesOnName(v_name_2932_);
v___y_2899_ = v___y_2926_;
v___y_2900_ = v___y_2927_;
v___y_2901_ = v___y_2928_;
v___y_2902_ = v___y_2929_;
v___y_2903_ = v___x_2933_;
goto v___jp_2898_;
}
v___jp_2934_:
{
lean_object* v___x_2939_; 
v___x_2939_ = lean_st_ref_get(v___y_2938_);
if (v_useNatCasesAuxOn_2885_ == 0)
{
lean_dec(v___x_2939_);
v___y_2926_ = v___y_2936_;
v___y_2927_ = v___y_2935_;
v___y_2928_ = v___y_2937_;
v___y_2929_ = v___y_2938_;
goto v___jp_2925_;
}
else
{
lean_object* v_inductiveVal_2940_; lean_object* v_toConstantVal_2941_; lean_object* v_env_2942_; lean_object* v_name_2943_; lean_object* v___x_2944_; uint8_t v___x_2945_; 
v_inductiveVal_2940_ = lean_ctor_get(v_ctx_2884_, 0);
v_toConstantVal_2941_ = lean_ctor_get(v_inductiveVal_2940_, 0);
v_env_2942_ = lean_ctor_get(v___x_2939_, 0);
lean_inc_ref(v_env_2942_);
lean_dec(v___x_2939_);
v_name_2943_ = lean_ctor_get(v_toConstantVal_2941_, 0);
v___x_2944_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__1));
v___x_2945_ = lean_name_eq(v_name_2943_, v___x_2944_);
if (v___x_2945_ == 0)
{
lean_dec_ref(v_env_2942_);
v___y_2926_ = v___y_2936_;
v___y_2927_ = v___y_2935_;
v___y_2928_ = v___y_2937_;
v___y_2929_ = v___y_2938_;
goto v___jp_2925_;
}
else
{
lean_object* v___x_2946_; uint8_t v___x_2947_; 
v___x_2946_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__3));
v___x_2947_ = l_Lean_Environment_contains(v_env_2942_, v___x_2946_, v___x_2945_);
if (v___x_2947_ == 0)
{
v___y_2926_ = v___y_2936_;
v___y_2927_ = v___y_2935_;
v___y_2928_ = v___y_2937_;
v___y_2929_ = v___y_2938_;
goto v___jp_2925_;
}
else
{
v___y_2899_ = v___y_2936_;
v___y_2900_ = v___y_2935_;
v___y_2901_ = v___y_2937_;
v___y_2902_ = v___y_2938_;
v___y_2903_ = v___x_2946_;
goto v___jp_2898_;
}
}
}
}
}
else
{
lean_object* v_a_2998_; lean_object* v___x_3000_; uint8_t v_isShared_3001_; uint8_t v_isSharedCheck_3005_; 
lean_dec(v___y_2890_);
lean_dec_ref(v___y_2889_);
lean_dec(v___y_2888_);
lean_dec_ref(v___y_2887_);
lean_dec(v_interestingCtors_x3f_2886_);
lean_dec_ref(v_ctx_2884_);
lean_dec_ref(v_givenNames_2883_);
lean_dec(v_majorFVarId_2882_);
lean_dec(v_mvarId_2881_);
v_a_2998_ = lean_ctor_get(v___x_2894_, 0);
v_isSharedCheck_3005_ = !lean_is_exclusive(v___x_2894_);
if (v_isSharedCheck_3005_ == 0)
{
v___x_3000_ = v___x_2894_;
v_isShared_3001_ = v_isSharedCheck_3005_;
goto v_resetjp_2999_;
}
else
{
lean_inc(v_a_2998_);
lean_dec(v___x_2894_);
v___x_3000_ = lean_box(0);
v_isShared_3001_ = v_isSharedCheck_3005_;
goto v_resetjp_2999_;
}
v_resetjp_2999_:
{
lean_object* v___x_3003_; 
if (v_isShared_3001_ == 0)
{
v___x_3003_ = v___x_3000_;
goto v_reusejp_3002_;
}
else
{
lean_object* v_reuseFailAlloc_3004_; 
v_reuseFailAlloc_3004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3004_, 0, v_a_2998_);
v___x_3003_ = v_reuseFailAlloc_3004_;
goto v_reusejp_3002_;
}
v_reusejp_3002_:
{
return v___x_3003_;
}
}
}
}
else
{
lean_object* v_a_3006_; lean_object* v___x_3008_; uint8_t v_isShared_3009_; uint8_t v_isSharedCheck_3013_; 
lean_dec(v___y_2890_);
lean_dec_ref(v___y_2889_);
lean_dec(v___y_2888_);
lean_dec_ref(v___y_2887_);
lean_dec(v_interestingCtors_x3f_2886_);
lean_dec_ref(v_ctx_2884_);
lean_dec_ref(v_givenNames_2883_);
lean_dec(v_majorFVarId_2882_);
lean_dec(v_mvarId_2881_);
v_a_3006_ = lean_ctor_get(v___x_2892_, 0);
v_isSharedCheck_3013_ = !lean_is_exclusive(v___x_2892_);
if (v_isSharedCheck_3013_ == 0)
{
v___x_3008_ = v___x_2892_;
v_isShared_3009_ = v_isSharedCheck_3013_;
goto v_resetjp_3007_;
}
else
{
lean_inc(v_a_3006_);
lean_dec(v___x_2892_);
v___x_3008_ = lean_box(0);
v_isShared_3009_ = v_isSharedCheck_3013_;
goto v_resetjp_3007_;
}
v_resetjp_3007_:
{
lean_object* v___x_3011_; 
if (v_isShared_3009_ == 0)
{
v___x_3011_ = v___x_3008_;
goto v_reusejp_3010_;
}
else
{
lean_object* v_reuseFailAlloc_3012_; 
v_reuseFailAlloc_3012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3012_, 0, v_a_3006_);
v___x_3011_ = v_reuseFailAlloc_3012_;
goto v_reusejp_3010_;
}
v_reusejp_3010_:
{
return v___x_3011_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___boxed(lean_object* v___x_3014_, lean_object* v_mvarId_3015_, lean_object* v_majorFVarId_3016_, lean_object* v_givenNames_3017_, lean_object* v_ctx_3018_, lean_object* v_useNatCasesAuxOn_3019_, lean_object* v_interestingCtors_x3f_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_){
_start:
{
uint8_t v_useNatCasesAuxOn_boxed_3026_; lean_object* v_res_3027_; 
v_useNatCasesAuxOn_boxed_3026_ = lean_unbox(v_useNatCasesAuxOn_3019_);
v_res_3027_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0(v___x_3014_, v_mvarId_3015_, v_majorFVarId_3016_, v_givenNames_3017_, v_ctx_3018_, v_useNatCasesAuxOn_boxed_3026_, v_interestingCtors_x3f_3020_, v___y_3021_, v___y_3022_, v___y_3023_, v___y_3024_);
return v_res_3027_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn(lean_object* v_mvarId_3028_, lean_object* v_majorFVarId_3029_, lean_object* v_givenNames_3030_, lean_object* v_ctx_3031_, uint8_t v_useNatCasesAuxOn_3032_, lean_object* v_interestingCtors_x3f_3033_, lean_object* v_a_3034_, lean_object* v_a_3035_, lean_object* v_a_3036_, lean_object* v_a_3037_){
_start:
{
lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___f_3041_; lean_object* v___x_3042_; 
lean_inc(v_majorFVarId_3029_);
v___x_3039_ = l_Lean_mkFVar(v_majorFVarId_3029_);
v___x_3040_ = lean_box(v_useNatCasesAuxOn_3032_);
lean_inc(v_mvarId_3028_);
v___f_3041_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___boxed), 12, 7);
lean_closure_set(v___f_3041_, 0, v___x_3039_);
lean_closure_set(v___f_3041_, 1, v_mvarId_3028_);
lean_closure_set(v___f_3041_, 2, v_majorFVarId_3029_);
lean_closure_set(v___f_3041_, 3, v_givenNames_3030_);
lean_closure_set(v___f_3041_, 4, v_ctx_3031_);
lean_closure_set(v___f_3041_, 5, v___x_3040_);
lean_closure_set(v___f_3041_, 6, v_interestingCtors_x3f_3033_);
v___x_3042_ = l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2___redArg(v_mvarId_3028_, v___f_3041_, v_a_3034_, v_a_3035_, v_a_3036_, v_a_3037_);
return v___x_3042_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___boxed(lean_object* v_mvarId_3043_, lean_object* v_majorFVarId_3044_, lean_object* v_givenNames_3045_, lean_object* v_ctx_3046_, lean_object* v_useNatCasesAuxOn_3047_, lean_object* v_interestingCtors_x3f_3048_, lean_object* v_a_3049_, lean_object* v_a_3050_, lean_object* v_a_3051_, lean_object* v_a_3052_, lean_object* v_a_3053_){
_start:
{
uint8_t v_useNatCasesAuxOn_boxed_3054_; lean_object* v_res_3055_; 
v_useNatCasesAuxOn_boxed_3054_ = lean_unbox(v_useNatCasesAuxOn_3047_);
v_res_3055_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn(v_mvarId_3043_, v_majorFVarId_3044_, v_givenNames_3045_, v_ctx_3046_, v_useNatCasesAuxOn_boxed_3054_, v_interestingCtors_x3f_3048_, v_a_3049_, v_a_3050_, v_a_3051_, v_a_3052_);
lean_dec(v_a_3052_);
lean_dec_ref(v_a_3051_);
lean_dec(v_a_3050_);
lean_dec_ref(v_a_3049_);
return v_res_3055_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0___closed__0(void){
_start:
{
lean_object* v___x_3056_; double v___x_3057_; 
v___x_3056_ = lean_unsigned_to_nat(0u);
v___x_3057_ = lean_float_of_nat(v___x_3056_);
return v___x_3057_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0(lean_object* v_cls_3061_, lean_object* v_msg_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_){
_start:
{
lean_object* v_ref_3068_; lean_object* v___x_3069_; lean_object* v_a_3070_; lean_object* v___x_3072_; uint8_t v_isShared_3073_; uint8_t v_isSharedCheck_3114_; 
v_ref_3068_ = lean_ctor_get(v___y_3065_, 5);
v___x_3069_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected_spec__0_spec__0(v_msg_3062_, v___y_3063_, v___y_3064_, v___y_3065_, v___y_3066_);
v_a_3070_ = lean_ctor_get(v___x_3069_, 0);
v_isSharedCheck_3114_ = !lean_is_exclusive(v___x_3069_);
if (v_isSharedCheck_3114_ == 0)
{
v___x_3072_ = v___x_3069_;
v_isShared_3073_ = v_isSharedCheck_3114_;
goto v_resetjp_3071_;
}
else
{
lean_inc(v_a_3070_);
lean_dec(v___x_3069_);
v___x_3072_ = lean_box(0);
v_isShared_3073_ = v_isSharedCheck_3114_;
goto v_resetjp_3071_;
}
v_resetjp_3071_:
{
lean_object* v___x_3074_; lean_object* v_traceState_3075_; lean_object* v_env_3076_; lean_object* v_nextMacroScope_3077_; lean_object* v_ngen_3078_; lean_object* v_auxDeclNGen_3079_; lean_object* v_cache_3080_; lean_object* v_messages_3081_; lean_object* v_infoState_3082_; lean_object* v_snapshotTasks_3083_; lean_object* v___x_3085_; uint8_t v_isShared_3086_; uint8_t v_isSharedCheck_3113_; 
v___x_3074_ = lean_st_ref_take(v___y_3066_);
v_traceState_3075_ = lean_ctor_get(v___x_3074_, 4);
v_env_3076_ = lean_ctor_get(v___x_3074_, 0);
v_nextMacroScope_3077_ = lean_ctor_get(v___x_3074_, 1);
v_ngen_3078_ = lean_ctor_get(v___x_3074_, 2);
v_auxDeclNGen_3079_ = lean_ctor_get(v___x_3074_, 3);
v_cache_3080_ = lean_ctor_get(v___x_3074_, 5);
v_messages_3081_ = lean_ctor_get(v___x_3074_, 6);
v_infoState_3082_ = lean_ctor_get(v___x_3074_, 7);
v_snapshotTasks_3083_ = lean_ctor_get(v___x_3074_, 8);
v_isSharedCheck_3113_ = !lean_is_exclusive(v___x_3074_);
if (v_isSharedCheck_3113_ == 0)
{
v___x_3085_ = v___x_3074_;
v_isShared_3086_ = v_isSharedCheck_3113_;
goto v_resetjp_3084_;
}
else
{
lean_inc(v_snapshotTasks_3083_);
lean_inc(v_infoState_3082_);
lean_inc(v_messages_3081_);
lean_inc(v_cache_3080_);
lean_inc(v_traceState_3075_);
lean_inc(v_auxDeclNGen_3079_);
lean_inc(v_ngen_3078_);
lean_inc(v_nextMacroScope_3077_);
lean_inc(v_env_3076_);
lean_dec(v___x_3074_);
v___x_3085_ = lean_box(0);
v_isShared_3086_ = v_isSharedCheck_3113_;
goto v_resetjp_3084_;
}
v_resetjp_3084_:
{
uint64_t v_tid_3087_; lean_object* v_traces_3088_; lean_object* v___x_3090_; uint8_t v_isShared_3091_; uint8_t v_isSharedCheck_3112_; 
v_tid_3087_ = lean_ctor_get_uint64(v_traceState_3075_, sizeof(void*)*1);
v_traces_3088_ = lean_ctor_get(v_traceState_3075_, 0);
v_isSharedCheck_3112_ = !lean_is_exclusive(v_traceState_3075_);
if (v_isSharedCheck_3112_ == 0)
{
v___x_3090_ = v_traceState_3075_;
v_isShared_3091_ = v_isSharedCheck_3112_;
goto v_resetjp_3089_;
}
else
{
lean_inc(v_traces_3088_);
lean_dec(v_traceState_3075_);
v___x_3090_ = lean_box(0);
v_isShared_3091_ = v_isSharedCheck_3112_;
goto v_resetjp_3089_;
}
v_resetjp_3089_:
{
lean_object* v___x_3092_; double v___x_3093_; uint8_t v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3102_; 
v___x_3092_ = lean_box(0);
v___x_3093_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0___closed__0);
v___x_3094_ = 0;
v___x_3095_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0___closed__1));
v___x_3096_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3096_, 0, v_cls_3061_);
lean_ctor_set(v___x_3096_, 1, v___x_3092_);
lean_ctor_set(v___x_3096_, 2, v___x_3095_);
lean_ctor_set_float(v___x_3096_, sizeof(void*)*3, v___x_3093_);
lean_ctor_set_float(v___x_3096_, sizeof(void*)*3 + 8, v___x_3093_);
lean_ctor_set_uint8(v___x_3096_, sizeof(void*)*3 + 16, v___x_3094_);
v___x_3097_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0___closed__2));
v___x_3098_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3098_, 0, v___x_3096_);
lean_ctor_set(v___x_3098_, 1, v_a_3070_);
lean_ctor_set(v___x_3098_, 2, v___x_3097_);
lean_inc(v_ref_3068_);
v___x_3099_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3099_, 0, v_ref_3068_);
lean_ctor_set(v___x_3099_, 1, v___x_3098_);
v___x_3100_ = l_Lean_PersistentArray_push___redArg(v_traces_3088_, v___x_3099_);
if (v_isShared_3091_ == 0)
{
lean_ctor_set(v___x_3090_, 0, v___x_3100_);
v___x_3102_ = v___x_3090_;
goto v_reusejp_3101_;
}
else
{
lean_object* v_reuseFailAlloc_3111_; 
v_reuseFailAlloc_3111_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3111_, 0, v___x_3100_);
lean_ctor_set_uint64(v_reuseFailAlloc_3111_, sizeof(void*)*1, v_tid_3087_);
v___x_3102_ = v_reuseFailAlloc_3111_;
goto v_reusejp_3101_;
}
v_reusejp_3101_:
{
lean_object* v___x_3104_; 
if (v_isShared_3086_ == 0)
{
lean_ctor_set(v___x_3085_, 4, v___x_3102_);
v___x_3104_ = v___x_3085_;
goto v_reusejp_3103_;
}
else
{
lean_object* v_reuseFailAlloc_3110_; 
v_reuseFailAlloc_3110_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3110_, 0, v_env_3076_);
lean_ctor_set(v_reuseFailAlloc_3110_, 1, v_nextMacroScope_3077_);
lean_ctor_set(v_reuseFailAlloc_3110_, 2, v_ngen_3078_);
lean_ctor_set(v_reuseFailAlloc_3110_, 3, v_auxDeclNGen_3079_);
lean_ctor_set(v_reuseFailAlloc_3110_, 4, v___x_3102_);
lean_ctor_set(v_reuseFailAlloc_3110_, 5, v_cache_3080_);
lean_ctor_set(v_reuseFailAlloc_3110_, 6, v_messages_3081_);
lean_ctor_set(v_reuseFailAlloc_3110_, 7, v_infoState_3082_);
lean_ctor_set(v_reuseFailAlloc_3110_, 8, v_snapshotTasks_3083_);
v___x_3104_ = v_reuseFailAlloc_3110_;
goto v_reusejp_3103_;
}
v_reusejp_3103_:
{
lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3108_; 
v___x_3105_ = lean_st_ref_set(v___y_3066_, v___x_3104_);
v___x_3106_ = lean_box(0);
if (v_isShared_3073_ == 0)
{
lean_ctor_set(v___x_3072_, 0, v___x_3106_);
v___x_3108_ = v___x_3072_;
goto v_reusejp_3107_;
}
else
{
lean_object* v_reuseFailAlloc_3109_; 
v_reuseFailAlloc_3109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3109_, 0, v___x_3106_);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0___boxed(lean_object* v_cls_3115_, lean_object* v_msg_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_){
_start:
{
lean_object* v_res_3122_; 
v_res_3122_ = l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0(v_cls_3115_, v_msg_3116_, v___y_3117_, v___y_3118_, v___y_3119_, v___y_3120_);
lean_dec(v___y_3120_);
lean_dec_ref(v___y_3119_);
lean_dec(v___y_3118_);
lean_dec_ref(v___y_3117_);
return v_res_3122_;
}
}
static lean_object* _init_l_Lean_Meta_Cases_cases___lam__0___closed__2(void){
_start:
{
lean_object* v___x_3126_; lean_object* v___x_3127_; 
v___x_3126_ = ((lean_object*)(l_Lean_Meta_Cases_cases___lam__0___closed__1));
v___x_3127_ = l_Lean_MessageData_ofFormat(v___x_3126_);
return v___x_3127_;
}
}
static lean_object* _init_l_Lean_Meta_Cases_cases___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3128_; lean_object* v___x_3129_; 
v___x_3128_ = lean_obj_once(&l_Lean_Meta_Cases_cases___lam__0___closed__2, &l_Lean_Meta_Cases_cases___lam__0___closed__2_once, _init_l_Lean_Meta_Cases_cases___lam__0___closed__2);
v___x_3129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3129_, 0, v___x_3128_);
return v___x_3129_;
}
}
static lean_object* _init_l_Lean_Meta_Cases_cases___lam__0___closed__9(void){
_start:
{
lean_object* v___x_3136_; lean_object* v___x_3137_; 
v___x_3136_ = ((lean_object*)(l_Lean_Meta_Cases_cases___lam__0___closed__8));
v___x_3137_ = l_Lean_stringToMessageData(v___x_3136_);
return v___x_3137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_cases___lam__0(lean_object* v_mvarId_3138_, lean_object* v___x_3139_, lean_object* v_majorFVarId_3140_, lean_object* v_givenNames_3141_, lean_object* v_interestingCtors_x3f_3142_, lean_object* v___x_3143_, uint8_t v_useNatCasesAuxOn_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_){
_start:
{
lean_object* v___x_3150_; 
lean_inc(v___x_3139_);
lean_inc(v_mvarId_3138_);
v___x_3150_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_3138_, v___x_3139_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_);
if (lean_obj_tag(v___x_3150_) == 0)
{
lean_object* v___x_3151_; 
lean_dec_ref_known(v___x_3150_, 1);
lean_inc(v_majorFVarId_3140_);
v___x_3151_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f(v_majorFVarId_3140_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_);
if (lean_obj_tag(v___x_3151_) == 0)
{
lean_object* v_a_3152_; 
v_a_3152_ = lean_ctor_get(v___x_3151_, 0);
lean_inc(v_a_3152_);
lean_dec_ref_known(v___x_3151_, 1);
if (lean_obj_tag(v_a_3152_) == 0)
{
lean_object* v___x_3153_; lean_object* v___x_3154_; 
lean_dec_ref(v___x_3143_);
lean_dec(v_interestingCtors_x3f_3142_);
lean_dec_ref(v_givenNames_3141_);
lean_dec(v_majorFVarId_3140_);
v___x_3153_ = lean_obj_once(&l_Lean_Meta_Cases_cases___lam__0___closed__3, &l_Lean_Meta_Cases_cases___lam__0___closed__3_once, _init_l_Lean_Meta_Cases_cases___lam__0___closed__3);
v___x_3154_ = l_Lean_Meta_throwTacticEx___redArg(v___x_3139_, v_mvarId_3138_, v___x_3153_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_);
return v___x_3154_;
}
else
{
lean_object* v_val_3155_; lean_object* v___x_3157_; uint8_t v_isShared_3158_; uint8_t v_isSharedCheck_3219_; 
lean_dec(v___x_3139_);
v_val_3155_ = lean_ctor_get(v_a_3152_, 0);
v_isSharedCheck_3219_ = !lean_is_exclusive(v_a_3152_);
if (v_isSharedCheck_3219_ == 0)
{
v___x_3157_ = v_a_3152_;
v_isShared_3158_ = v_isSharedCheck_3219_;
goto v_resetjp_3156_;
}
else
{
lean_inc(v_val_3155_);
lean_dec(v_a_3152_);
v___x_3157_ = lean_box(0);
v_isShared_3158_ = v_isSharedCheck_3219_;
goto v_resetjp_3156_;
}
v_resetjp_3156_:
{
lean_object* v___x_3159_; 
lean_inc(v_val_3155_);
v___x_3159_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices(v_val_3155_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_);
if (lean_obj_tag(v___x_3159_) == 0)
{
lean_object* v_a_3160_; uint8_t v___x_3161_; 
v_a_3160_ = lean_ctor_get(v___x_3159_, 0);
lean_inc(v_a_3160_);
lean_dec_ref_known(v___x_3159_, 1);
v___x_3161_ = lean_unbox(v_a_3160_);
if (v___x_3161_ == 0)
{
lean_object* v___x_3162_; 
v___x_3162_ = l_Lean_Meta_generalizeIndices(v_mvarId_3138_, v_majorFVarId_3140_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_);
if (lean_obj_tag(v___x_3162_) == 0)
{
lean_object* v_a_3163_; lean_object* v___y_3165_; lean_object* v___y_3166_; lean_object* v___y_3167_; lean_object* v___y_3168_; lean_object* v_options_3178_; uint8_t v_hasTrace_3179_; 
v_a_3163_ = lean_ctor_get(v___x_3162_, 0);
lean_inc(v_a_3163_);
lean_dec_ref_known(v___x_3162_, 1);
v_options_3178_ = lean_ctor_get(v___y_3147_, 2);
v_hasTrace_3179_ = lean_ctor_get_uint8(v_options_3178_, sizeof(void*)*1);
if (v_hasTrace_3179_ == 0)
{
lean_del_object(v___x_3157_);
lean_dec_ref(v___x_3143_);
v___y_3165_ = v___y_3145_;
v___y_3166_ = v___y_3146_;
v___y_3167_ = v___y_3147_;
v___y_3168_ = v___y_3148_;
goto v___jp_3164_;
}
else
{
lean_object* v_inheritedTraceOptions_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; uint8_t v___x_3186_; 
v_inheritedTraceOptions_3180_ = lean_ctor_get(v___y_3147_, 13);
v___x_3181_ = ((lean_object*)(l_Lean_Meta_Cases_cases___lam__0___closed__4));
v___x_3182_ = ((lean_object*)(l_Lean_Meta_Cases_cases___lam__0___closed__5));
v___x_3183_ = l_Lean_Name_mkStr3(v___x_3181_, v___x_3182_, v___x_3143_);
v___x_3184_ = ((lean_object*)(l_Lean_Meta_Cases_cases___lam__0___closed__7));
lean_inc(v___x_3183_);
v___x_3185_ = l_Lean_Name_append(v___x_3184_, v___x_3183_);
v___x_3186_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3180_, v_options_3178_, v___x_3185_);
lean_dec(v___x_3185_);
if (v___x_3186_ == 0)
{
lean_dec(v___x_3183_);
lean_del_object(v___x_3157_);
v___y_3165_ = v___y_3145_;
v___y_3166_ = v___y_3146_;
v___y_3167_ = v___y_3147_;
v___y_3168_ = v___y_3148_;
goto v___jp_3164_;
}
else
{
lean_object* v_mvarId_3187_; lean_object* v___x_3188_; lean_object* v___x_3190_; 
v_mvarId_3187_ = lean_ctor_get(v_a_3163_, 0);
v___x_3188_ = lean_obj_once(&l_Lean_Meta_Cases_cases___lam__0___closed__9, &l_Lean_Meta_Cases_cases___lam__0___closed__9_once, _init_l_Lean_Meta_Cases_cases___lam__0___closed__9);
lean_inc(v_mvarId_3187_);
if (v_isShared_3158_ == 0)
{
lean_ctor_set(v___x_3157_, 0, v_mvarId_3187_);
v___x_3190_ = v___x_3157_;
goto v_reusejp_3189_;
}
else
{
lean_object* v_reuseFailAlloc_3201_; 
v_reuseFailAlloc_3201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3201_, 0, v_mvarId_3187_);
v___x_3190_ = v_reuseFailAlloc_3201_;
goto v_reusejp_3189_;
}
v_reusejp_3189_:
{
lean_object* v___x_3191_; lean_object* v___x_3192_; 
v___x_3191_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3191_, 0, v___x_3188_);
lean_ctor_set(v___x_3191_, 1, v___x_3190_);
v___x_3192_ = l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0(v___x_3183_, v___x_3191_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_);
if (lean_obj_tag(v___x_3192_) == 0)
{
lean_dec_ref_known(v___x_3192_, 1);
v___y_3165_ = v___y_3145_;
v___y_3166_ = v___y_3146_;
v___y_3167_ = v___y_3147_;
v___y_3168_ = v___y_3148_;
goto v___jp_3164_;
}
else
{
lean_object* v_a_3193_; lean_object* v___x_3195_; uint8_t v_isShared_3196_; uint8_t v_isSharedCheck_3200_; 
lean_dec(v_a_3163_);
lean_dec(v_a_3160_);
lean_dec(v_val_3155_);
lean_dec(v_interestingCtors_x3f_3142_);
lean_dec_ref(v_givenNames_3141_);
v_a_3193_ = lean_ctor_get(v___x_3192_, 0);
v_isSharedCheck_3200_ = !lean_is_exclusive(v___x_3192_);
if (v_isSharedCheck_3200_ == 0)
{
v___x_3195_ = v___x_3192_;
v_isShared_3196_ = v_isSharedCheck_3200_;
goto v_resetjp_3194_;
}
else
{
lean_inc(v_a_3193_);
lean_dec(v___x_3192_);
v___x_3195_ = lean_box(0);
v_isShared_3196_ = v_isSharedCheck_3200_;
goto v_resetjp_3194_;
}
v_resetjp_3194_:
{
lean_object* v___x_3198_; 
if (v_isShared_3196_ == 0)
{
v___x_3198_ = v___x_3195_;
goto v_reusejp_3197_;
}
else
{
lean_object* v_reuseFailAlloc_3199_; 
v_reuseFailAlloc_3199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3199_, 0, v_a_3193_);
v___x_3198_ = v_reuseFailAlloc_3199_;
goto v_reusejp_3197_;
}
v_reusejp_3197_:
{
return v___x_3198_;
}
}
}
}
}
}
v___jp_3164_:
{
lean_object* v_mvarId_3169_; lean_object* v_fvarId_3170_; lean_object* v_numEqs_3171_; uint8_t v___x_3172_; lean_object* v___x_3173_; 
v_mvarId_3169_ = lean_ctor_get(v_a_3163_, 0);
v_fvarId_3170_ = lean_ctor_get(v_a_3163_, 2);
v_numEqs_3171_ = lean_ctor_get(v_a_3163_, 3);
lean_inc(v_numEqs_3171_);
v___x_3172_ = lean_unbox(v_a_3160_);
lean_dec(v_a_3160_);
lean_inc(v_fvarId_3170_);
lean_inc(v_mvarId_3169_);
v___x_3173_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn(v_mvarId_3169_, v_fvarId_3170_, v_givenNames_3141_, v_val_3155_, v___x_3172_, v_interestingCtors_x3f_3142_, v___y_3165_, v___y_3166_, v___y_3167_, v___y_3168_);
if (lean_obj_tag(v___x_3173_) == 0)
{
lean_object* v_a_3174_; lean_object* v___x_3175_; 
v_a_3174_ = lean_ctor_get(v___x_3173_, 0);
lean_inc(v_a_3174_);
lean_dec_ref_known(v___x_3173_, 1);
v___x_3175_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices(v_a_3163_, v_a_3174_, v___y_3165_, v___y_3166_, v___y_3167_, v___y_3168_);
lean_dec(v_a_3163_);
if (lean_obj_tag(v___x_3175_) == 0)
{
lean_object* v_a_3176_; lean_object* v___x_3177_; 
v_a_3176_ = lean_ctor_get(v___x_3175_, 0);
lean_inc(v_a_3176_);
lean_dec_ref_known(v___x_3175_, 1);
v___x_3177_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs(v_numEqs_3171_, v_a_3176_, v___y_3165_, v___y_3166_, v___y_3167_, v___y_3168_);
lean_dec(v_a_3176_);
return v___x_3177_;
}
else
{
lean_dec(v_numEqs_3171_);
return v___x_3175_;
}
}
else
{
lean_dec(v_numEqs_3171_);
lean_dec(v_a_3163_);
return v___x_3173_;
}
}
}
else
{
lean_object* v_a_3202_; lean_object* v___x_3204_; uint8_t v_isShared_3205_; uint8_t v_isSharedCheck_3209_; 
lean_dec(v_a_3160_);
lean_del_object(v___x_3157_);
lean_dec(v_val_3155_);
lean_dec_ref(v___x_3143_);
lean_dec(v_interestingCtors_x3f_3142_);
lean_dec_ref(v_givenNames_3141_);
v_a_3202_ = lean_ctor_get(v___x_3162_, 0);
v_isSharedCheck_3209_ = !lean_is_exclusive(v___x_3162_);
if (v_isSharedCheck_3209_ == 0)
{
v___x_3204_ = v___x_3162_;
v_isShared_3205_ = v_isSharedCheck_3209_;
goto v_resetjp_3203_;
}
else
{
lean_inc(v_a_3202_);
lean_dec(v___x_3162_);
v___x_3204_ = lean_box(0);
v_isShared_3205_ = v_isSharedCheck_3209_;
goto v_resetjp_3203_;
}
v_resetjp_3203_:
{
lean_object* v___x_3207_; 
if (v_isShared_3205_ == 0)
{
v___x_3207_ = v___x_3204_;
goto v_reusejp_3206_;
}
else
{
lean_object* v_reuseFailAlloc_3208_; 
v_reuseFailAlloc_3208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3208_, 0, v_a_3202_);
v___x_3207_ = v_reuseFailAlloc_3208_;
goto v_reusejp_3206_;
}
v_reusejp_3206_:
{
return v___x_3207_;
}
}
}
}
else
{
lean_object* v___x_3210_; 
lean_dec(v_a_3160_);
lean_del_object(v___x_3157_);
lean_dec_ref(v___x_3143_);
v___x_3210_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn(v_mvarId_3138_, v_majorFVarId_3140_, v_givenNames_3141_, v_val_3155_, v_useNatCasesAuxOn_3144_, v_interestingCtors_x3f_3142_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_);
return v___x_3210_;
}
}
else
{
lean_object* v_a_3211_; lean_object* v___x_3213_; uint8_t v_isShared_3214_; uint8_t v_isSharedCheck_3218_; 
lean_del_object(v___x_3157_);
lean_dec(v_val_3155_);
lean_dec_ref(v___x_3143_);
lean_dec(v_interestingCtors_x3f_3142_);
lean_dec_ref(v_givenNames_3141_);
lean_dec(v_majorFVarId_3140_);
lean_dec(v_mvarId_3138_);
v_a_3211_ = lean_ctor_get(v___x_3159_, 0);
v_isSharedCheck_3218_ = !lean_is_exclusive(v___x_3159_);
if (v_isSharedCheck_3218_ == 0)
{
v___x_3213_ = v___x_3159_;
v_isShared_3214_ = v_isSharedCheck_3218_;
goto v_resetjp_3212_;
}
else
{
lean_inc(v_a_3211_);
lean_dec(v___x_3159_);
v___x_3213_ = lean_box(0);
v_isShared_3214_ = v_isSharedCheck_3218_;
goto v_resetjp_3212_;
}
v_resetjp_3212_:
{
lean_object* v___x_3216_; 
if (v_isShared_3214_ == 0)
{
v___x_3216_ = v___x_3213_;
goto v_reusejp_3215_;
}
else
{
lean_object* v_reuseFailAlloc_3217_; 
v_reuseFailAlloc_3217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3217_, 0, v_a_3211_);
v___x_3216_ = v_reuseFailAlloc_3217_;
goto v_reusejp_3215_;
}
v_reusejp_3215_:
{
return v___x_3216_;
}
}
}
}
}
}
else
{
lean_object* v_a_3220_; lean_object* v___x_3222_; uint8_t v_isShared_3223_; uint8_t v_isSharedCheck_3227_; 
lean_dec_ref(v___x_3143_);
lean_dec(v_interestingCtors_x3f_3142_);
lean_dec_ref(v_givenNames_3141_);
lean_dec(v_majorFVarId_3140_);
lean_dec(v___x_3139_);
lean_dec(v_mvarId_3138_);
v_a_3220_ = lean_ctor_get(v___x_3151_, 0);
v_isSharedCheck_3227_ = !lean_is_exclusive(v___x_3151_);
if (v_isSharedCheck_3227_ == 0)
{
v___x_3222_ = v___x_3151_;
v_isShared_3223_ = v_isSharedCheck_3227_;
goto v_resetjp_3221_;
}
else
{
lean_inc(v_a_3220_);
lean_dec(v___x_3151_);
v___x_3222_ = lean_box(0);
v_isShared_3223_ = v_isSharedCheck_3227_;
goto v_resetjp_3221_;
}
v_resetjp_3221_:
{
lean_object* v___x_3225_; 
if (v_isShared_3223_ == 0)
{
v___x_3225_ = v___x_3222_;
goto v_reusejp_3224_;
}
else
{
lean_object* v_reuseFailAlloc_3226_; 
v_reuseFailAlloc_3226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3226_, 0, v_a_3220_);
v___x_3225_ = v_reuseFailAlloc_3226_;
goto v_reusejp_3224_;
}
v_reusejp_3224_:
{
return v___x_3225_;
}
}
}
}
else
{
lean_object* v_a_3228_; lean_object* v___x_3230_; uint8_t v_isShared_3231_; uint8_t v_isSharedCheck_3235_; 
lean_dec_ref(v___x_3143_);
lean_dec(v_interestingCtors_x3f_3142_);
lean_dec_ref(v_givenNames_3141_);
lean_dec(v_majorFVarId_3140_);
lean_dec(v___x_3139_);
lean_dec(v_mvarId_3138_);
v_a_3228_ = lean_ctor_get(v___x_3150_, 0);
v_isSharedCheck_3235_ = !lean_is_exclusive(v___x_3150_);
if (v_isSharedCheck_3235_ == 0)
{
v___x_3230_ = v___x_3150_;
v_isShared_3231_ = v_isSharedCheck_3235_;
goto v_resetjp_3229_;
}
else
{
lean_inc(v_a_3228_);
lean_dec(v___x_3150_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_cases___lam__0___boxed(lean_object* v_mvarId_3236_, lean_object* v___x_3237_, lean_object* v_majorFVarId_3238_, lean_object* v_givenNames_3239_, lean_object* v_interestingCtors_x3f_3240_, lean_object* v___x_3241_, lean_object* v_useNatCasesAuxOn_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_){
_start:
{
uint8_t v_useNatCasesAuxOn_boxed_3248_; lean_object* v_res_3249_; 
v_useNatCasesAuxOn_boxed_3248_ = lean_unbox(v_useNatCasesAuxOn_3242_);
v_res_3249_ = l_Lean_Meta_Cases_cases___lam__0(v_mvarId_3236_, v___x_3237_, v_majorFVarId_3238_, v_givenNames_3239_, v_interestingCtors_x3f_3240_, v___x_3241_, v_useNatCasesAuxOn_boxed_3248_, v___y_3243_, v___y_3244_, v___y_3245_, v___y_3246_);
lean_dec(v___y_3246_);
lean_dec_ref(v___y_3245_);
lean_dec(v___y_3244_);
lean_dec_ref(v___y_3243_);
return v_res_3249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_cases(lean_object* v_mvarId_3253_, lean_object* v_majorFVarId_3254_, lean_object* v_givenNames_3255_, uint8_t v_useNatCasesAuxOn_3256_, lean_object* v_interestingCtors_x3f_3257_, lean_object* v_a_3258_, lean_object* v_a_3259_, lean_object* v_a_3260_, lean_object* v_a_3261_){
_start:
{
lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___f_3266_; lean_object* v___x_3267_; 
v___x_3263_ = ((lean_object*)(l_Lean_Meta_Cases_cases___closed__0));
v___x_3264_ = ((lean_object*)(l_Lean_Meta_Cases_cases___closed__1));
v___x_3265_ = lean_box(v_useNatCasesAuxOn_3256_);
lean_inc(v_mvarId_3253_);
v___f_3266_ = lean_alloc_closure((void*)(l_Lean_Meta_Cases_cases___lam__0___boxed), 12, 7);
lean_closure_set(v___f_3266_, 0, v_mvarId_3253_);
lean_closure_set(v___f_3266_, 1, v___x_3264_);
lean_closure_set(v___f_3266_, 2, v_majorFVarId_3254_);
lean_closure_set(v___f_3266_, 3, v_givenNames_3255_);
lean_closure_set(v___f_3266_, 4, v_interestingCtors_x3f_3257_);
lean_closure_set(v___f_3266_, 5, v___x_3263_);
lean_closure_set(v___f_3266_, 6, v___x_3265_);
v___x_3267_ = l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2___redArg(v_mvarId_3253_, v___f_3266_, v_a_3258_, v_a_3259_, v_a_3260_, v_a_3261_);
if (lean_obj_tag(v___x_3267_) == 0)
{
return v___x_3267_;
}
else
{
lean_object* v_a_3268_; uint8_t v___y_3270_; uint8_t v___x_3272_; 
v_a_3268_ = lean_ctor_get(v___x_3267_, 0);
lean_inc(v_a_3268_);
v___x_3272_ = l_Lean_Exception_isInterrupt(v_a_3268_);
if (v___x_3272_ == 0)
{
uint8_t v___x_3273_; 
lean_inc(v_a_3268_);
v___x_3273_ = l_Lean_Exception_isRuntime(v_a_3268_);
v___y_3270_ = v___x_3273_;
goto v___jp_3269_;
}
else
{
v___y_3270_ = v___x_3272_;
goto v___jp_3269_;
}
v___jp_3269_:
{
if (v___y_3270_ == 0)
{
lean_object* v___x_3271_; 
lean_dec_ref_known(v___x_3267_, 1);
v___x_3271_ = l_Lean_Meta_throwNestedTacticEx___redArg(v___x_3264_, v_a_3268_, v_a_3258_, v_a_3259_, v_a_3260_, v_a_3261_);
return v___x_3271_;
}
else
{
lean_dec(v_a_3268_);
return v___x_3267_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_cases___boxed(lean_object* v_mvarId_3274_, lean_object* v_majorFVarId_3275_, lean_object* v_givenNames_3276_, lean_object* v_useNatCasesAuxOn_3277_, lean_object* v_interestingCtors_x3f_3278_, lean_object* v_a_3279_, lean_object* v_a_3280_, lean_object* v_a_3281_, lean_object* v_a_3282_, lean_object* v_a_3283_){
_start:
{
uint8_t v_useNatCasesAuxOn_boxed_3284_; lean_object* v_res_3285_; 
v_useNatCasesAuxOn_boxed_3284_ = lean_unbox(v_useNatCasesAuxOn_3277_);
v_res_3285_ = l_Lean_Meta_Cases_cases(v_mvarId_3274_, v_majorFVarId_3275_, v_givenNames_3276_, v_useNatCasesAuxOn_boxed_3284_, v_interestingCtors_x3f_3278_, v_a_3279_, v_a_3280_, v_a_3281_, v_a_3282_);
lean_dec(v_a_3282_);
lean_dec_ref(v_a_3281_);
lean_dec(v_a_3280_);
lean_dec_ref(v_a_3279_);
return v_res_3285_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_cases(lean_object* v_mvarId_3286_, lean_object* v_majorFVarId_3287_, lean_object* v_givenNames_3288_, uint8_t v_useNatCasesAuxOn_3289_, lean_object* v_interestingCtors_x3f_3290_, lean_object* v_a_3291_, lean_object* v_a_3292_, lean_object* v_a_3293_, lean_object* v_a_3294_){
_start:
{
lean_object* v___x_3296_; 
v___x_3296_ = l_Lean_Meta_Cases_cases(v_mvarId_3286_, v_majorFVarId_3287_, v_givenNames_3288_, v_useNatCasesAuxOn_3289_, v_interestingCtors_x3f_3290_, v_a_3291_, v_a_3292_, v_a_3293_, v_a_3294_);
return v___x_3296_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_cases___boxed(lean_object* v_mvarId_3297_, lean_object* v_majorFVarId_3298_, lean_object* v_givenNames_3299_, lean_object* v_useNatCasesAuxOn_3300_, lean_object* v_interestingCtors_x3f_3301_, lean_object* v_a_3302_, lean_object* v_a_3303_, lean_object* v_a_3304_, lean_object* v_a_3305_, lean_object* v_a_3306_){
_start:
{
uint8_t v_useNatCasesAuxOn_boxed_3307_; lean_object* v_res_3308_; 
v_useNatCasesAuxOn_boxed_3307_ = lean_unbox(v_useNatCasesAuxOn_3300_);
v_res_3308_ = l_Lean_MVarId_cases(v_mvarId_3297_, v_majorFVarId_3298_, v_givenNames_3299_, v_useNatCasesAuxOn_boxed_3307_, v_interestingCtors_x3f_3301_, v_a_3302_, v_a_3303_, v_a_3304_, v_a_3305_);
lean_dec(v_a_3305_);
lean_dec_ref(v_a_3304_);
lean_dec(v_a_3303_);
lean_dec_ref(v_a_3302_);
return v_res_3308_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1___redArg(lean_object* v_x_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_){
_start:
{
lean_object* v___x_3315_; 
v___x_3315_ = l_Lean_Meta_saveState___redArg(v___y_3311_, v___y_3313_);
if (lean_obj_tag(v___x_3315_) == 0)
{
lean_object* v_a_3316_; lean_object* v___x_3317_; 
v_a_3316_ = lean_ctor_get(v___x_3315_, 0);
lean_inc(v_a_3316_);
lean_dec_ref_known(v___x_3315_, 1);
lean_inc(v___y_3313_);
lean_inc_ref(v___y_3312_);
lean_inc(v___y_3311_);
lean_inc_ref(v___y_3310_);
v___x_3317_ = lean_apply_5(v_x_3309_, v___y_3310_, v___y_3311_, v___y_3312_, v___y_3313_, lean_box(0));
if (lean_obj_tag(v___x_3317_) == 0)
{
lean_object* v_a_3318_; lean_object* v___x_3320_; uint8_t v_isShared_3321_; uint8_t v_isSharedCheck_3326_; 
lean_dec(v_a_3316_);
v_a_3318_ = lean_ctor_get(v___x_3317_, 0);
v_isSharedCheck_3326_ = !lean_is_exclusive(v___x_3317_);
if (v_isSharedCheck_3326_ == 0)
{
v___x_3320_ = v___x_3317_;
v_isShared_3321_ = v_isSharedCheck_3326_;
goto v_resetjp_3319_;
}
else
{
lean_inc(v_a_3318_);
lean_dec(v___x_3317_);
v___x_3320_ = lean_box(0);
v_isShared_3321_ = v_isSharedCheck_3326_;
goto v_resetjp_3319_;
}
v_resetjp_3319_:
{
lean_object* v___x_3322_; lean_object* v___x_3324_; 
v___x_3322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3322_, 0, v_a_3318_);
if (v_isShared_3321_ == 0)
{
lean_ctor_set(v___x_3320_, 0, v___x_3322_);
v___x_3324_ = v___x_3320_;
goto v_reusejp_3323_;
}
else
{
lean_object* v_reuseFailAlloc_3325_; 
v_reuseFailAlloc_3325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3325_, 0, v___x_3322_);
v___x_3324_ = v_reuseFailAlloc_3325_;
goto v_reusejp_3323_;
}
v_reusejp_3323_:
{
return v___x_3324_;
}
}
}
else
{
lean_object* v_a_3327_; lean_object* v___x_3329_; uint8_t v_isShared_3330_; uint8_t v_isSharedCheck_3356_; 
v_a_3327_ = lean_ctor_get(v___x_3317_, 0);
v_isSharedCheck_3356_ = !lean_is_exclusive(v___x_3317_);
if (v_isSharedCheck_3356_ == 0)
{
v___x_3329_ = v___x_3317_;
v_isShared_3330_ = v_isSharedCheck_3356_;
goto v_resetjp_3328_;
}
else
{
lean_inc(v_a_3327_);
lean_dec(v___x_3317_);
v___x_3329_ = lean_box(0);
v_isShared_3330_ = v_isSharedCheck_3356_;
goto v_resetjp_3328_;
}
v_resetjp_3328_:
{
uint8_t v___y_3332_; uint8_t v___x_3354_; 
v___x_3354_ = l_Lean_Exception_isInterrupt(v_a_3327_);
if (v___x_3354_ == 0)
{
uint8_t v___x_3355_; 
lean_inc(v_a_3327_);
v___x_3355_ = l_Lean_Exception_isRuntime(v_a_3327_);
v___y_3332_ = v___x_3355_;
goto v___jp_3331_;
}
else
{
v___y_3332_ = v___x_3354_;
goto v___jp_3331_;
}
v___jp_3331_:
{
if (v___y_3332_ == 0)
{
lean_object* v___x_3333_; 
lean_del_object(v___x_3329_);
lean_dec(v_a_3327_);
v___x_3333_ = l_Lean_Meta_SavedState_restore___redArg(v_a_3316_, v___y_3311_, v___y_3313_);
lean_dec(v_a_3316_);
if (lean_obj_tag(v___x_3333_) == 0)
{
lean_object* v___x_3335_; uint8_t v_isShared_3336_; uint8_t v_isSharedCheck_3341_; 
v_isSharedCheck_3341_ = !lean_is_exclusive(v___x_3333_);
if (v_isSharedCheck_3341_ == 0)
{
lean_object* v_unused_3342_; 
v_unused_3342_ = lean_ctor_get(v___x_3333_, 0);
lean_dec(v_unused_3342_);
v___x_3335_ = v___x_3333_;
v_isShared_3336_ = v_isSharedCheck_3341_;
goto v_resetjp_3334_;
}
else
{
lean_dec(v___x_3333_);
v___x_3335_ = lean_box(0);
v_isShared_3336_ = v_isSharedCheck_3341_;
goto v_resetjp_3334_;
}
v_resetjp_3334_:
{
lean_object* v___x_3337_; lean_object* v___x_3339_; 
v___x_3337_ = lean_box(0);
if (v_isShared_3336_ == 0)
{
lean_ctor_set(v___x_3335_, 0, v___x_3337_);
v___x_3339_ = v___x_3335_;
goto v_reusejp_3338_;
}
else
{
lean_object* v_reuseFailAlloc_3340_; 
v_reuseFailAlloc_3340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3340_, 0, v___x_3337_);
v___x_3339_ = v_reuseFailAlloc_3340_;
goto v_reusejp_3338_;
}
v_reusejp_3338_:
{
return v___x_3339_;
}
}
}
else
{
lean_object* v_a_3343_; lean_object* v___x_3345_; uint8_t v_isShared_3346_; uint8_t v_isSharedCheck_3350_; 
v_a_3343_ = lean_ctor_get(v___x_3333_, 0);
v_isSharedCheck_3350_ = !lean_is_exclusive(v___x_3333_);
if (v_isSharedCheck_3350_ == 0)
{
v___x_3345_ = v___x_3333_;
v_isShared_3346_ = v_isSharedCheck_3350_;
goto v_resetjp_3344_;
}
else
{
lean_inc(v_a_3343_);
lean_dec(v___x_3333_);
v___x_3345_ = lean_box(0);
v_isShared_3346_ = v_isSharedCheck_3350_;
goto v_resetjp_3344_;
}
v_resetjp_3344_:
{
lean_object* v___x_3348_; 
if (v_isShared_3346_ == 0)
{
v___x_3348_ = v___x_3345_;
goto v_reusejp_3347_;
}
else
{
lean_object* v_reuseFailAlloc_3349_; 
v_reuseFailAlloc_3349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3349_, 0, v_a_3343_);
v___x_3348_ = v_reuseFailAlloc_3349_;
goto v_reusejp_3347_;
}
v_reusejp_3347_:
{
return v___x_3348_;
}
}
}
}
else
{
lean_object* v___x_3352_; 
lean_dec(v_a_3316_);
if (v_isShared_3330_ == 0)
{
v___x_3352_ = v___x_3329_;
goto v_reusejp_3351_;
}
else
{
lean_object* v_reuseFailAlloc_3353_; 
v_reuseFailAlloc_3353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3353_, 0, v_a_3327_);
v___x_3352_ = v_reuseFailAlloc_3353_;
goto v_reusejp_3351_;
}
v_reusejp_3351_:
{
return v___x_3352_;
}
}
}
}
}
}
else
{
lean_object* v_a_3357_; lean_object* v___x_3359_; uint8_t v_isShared_3360_; uint8_t v_isSharedCheck_3364_; 
lean_dec_ref(v_x_3309_);
v_a_3357_ = lean_ctor_get(v___x_3315_, 0);
v_isSharedCheck_3364_ = !lean_is_exclusive(v___x_3315_);
if (v_isSharedCheck_3364_ == 0)
{
v___x_3359_ = v___x_3315_;
v_isShared_3360_ = v_isSharedCheck_3364_;
goto v_resetjp_3358_;
}
else
{
lean_inc(v_a_3357_);
lean_dec(v___x_3315_);
v___x_3359_ = lean_box(0);
v_isShared_3360_ = v_isSharedCheck_3364_;
goto v_resetjp_3358_;
}
v_resetjp_3358_:
{
lean_object* v___x_3362_; 
if (v_isShared_3360_ == 0)
{
v___x_3362_ = v___x_3359_;
goto v_reusejp_3361_;
}
else
{
lean_object* v_reuseFailAlloc_3363_; 
v_reuseFailAlloc_3363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3363_, 0, v_a_3357_);
v___x_3362_ = v_reuseFailAlloc_3363_;
goto v_reusejp_3361_;
}
v_reusejp_3361_:
{
return v___x_3362_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1___redArg___boxed(lean_object* v_x_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_){
_start:
{
lean_object* v_res_3371_; 
v_res_3371_ = l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1___redArg(v_x_3365_, v___y_3366_, v___y_3367_, v___y_3368_, v___y_3369_);
lean_dec(v___y_3369_);
lean_dec_ref(v___y_3368_);
lean_dec(v___y_3367_);
lean_dec_ref(v___y_3366_);
return v_res_3371_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1(lean_object* v_00_u03b1_3372_, lean_object* v_x_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_){
_start:
{
lean_object* v___x_3379_; 
v___x_3379_ = l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1___redArg(v_x_3373_, v___y_3374_, v___y_3375_, v___y_3376_, v___y_3377_);
return v___x_3379_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1___boxed(lean_object* v_00_u03b1_3380_, lean_object* v_x_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_){
_start:
{
lean_object* v_res_3387_; 
v_res_3387_ = l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1(v_00_u03b1_3380_, v_x_3381_, v___y_3382_, v___y_3383_, v___y_3384_, v___y_3385_);
lean_dec(v___y_3385_);
lean_dec_ref(v___y_3384_);
lean_dec(v___y_3383_);
lean_dec_ref(v___y_3382_);
return v_res_3387_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_MVarId_casesRec_spec__0(lean_object* v_a_3388_, lean_object* v_a_3389_){
_start:
{
if (lean_obj_tag(v_a_3388_) == 0)
{
lean_object* v___x_3390_; 
v___x_3390_ = l_List_reverse___redArg(v_a_3389_);
return v___x_3390_;
}
else
{
lean_object* v_head_3391_; lean_object* v_toInductionSubgoal_3392_; lean_object* v_tail_3393_; lean_object* v___x_3395_; uint8_t v_isShared_3396_; uint8_t v_isSharedCheck_3402_; 
v_head_3391_ = lean_ctor_get(v_a_3388_, 0);
v_toInductionSubgoal_3392_ = lean_ctor_get(v_head_3391_, 0);
lean_inc_ref(v_toInductionSubgoal_3392_);
v_tail_3393_ = lean_ctor_get(v_a_3388_, 1);
v_isSharedCheck_3402_ = !lean_is_exclusive(v_a_3388_);
if (v_isSharedCheck_3402_ == 0)
{
lean_object* v_unused_3403_; 
v_unused_3403_ = lean_ctor_get(v_a_3388_, 0);
lean_dec(v_unused_3403_);
v___x_3395_ = v_a_3388_;
v_isShared_3396_ = v_isSharedCheck_3402_;
goto v_resetjp_3394_;
}
else
{
lean_inc(v_tail_3393_);
lean_dec(v_a_3388_);
v___x_3395_ = lean_box(0);
v_isShared_3396_ = v_isSharedCheck_3402_;
goto v_resetjp_3394_;
}
v_resetjp_3394_:
{
lean_object* v_mvarId_3397_; lean_object* v___x_3399_; 
v_mvarId_3397_ = lean_ctor_get(v_toInductionSubgoal_3392_, 0);
lean_inc(v_mvarId_3397_);
lean_dec_ref(v_toInductionSubgoal_3392_);
if (v_isShared_3396_ == 0)
{
lean_ctor_set(v___x_3395_, 1, v_a_3389_);
lean_ctor_set(v___x_3395_, 0, v_mvarId_3397_);
v___x_3399_ = v___x_3395_;
goto v_reusejp_3398_;
}
else
{
lean_object* v_reuseFailAlloc_3401_; 
v_reuseFailAlloc_3401_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3401_, 0, v_mvarId_3397_);
lean_ctor_set(v_reuseFailAlloc_3401_, 1, v_a_3389_);
v___x_3399_ = v_reuseFailAlloc_3401_;
goto v_reusejp_3398_;
}
v_reusejp_3398_:
{
v_a_3388_ = v_tail_3393_;
v_a_3389_ = v___x_3399_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3___lam__0(lean_object* v_mvarId_3404_, lean_object* v___x_3405_, lean_object* v___x_3406_, uint8_t v___x_3407_, lean_object* v___x_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_){
_start:
{
lean_object* v___x_3414_; 
v___x_3414_ = l_Lean_Meta_Cases_cases(v_mvarId_3404_, v___x_3405_, v___x_3406_, v___x_3407_, v___x_3408_, v___y_3409_, v___y_3410_, v___y_3411_, v___y_3412_);
if (lean_obj_tag(v___x_3414_) == 0)
{
lean_object* v_a_3415_; lean_object* v___x_3417_; uint8_t v_isShared_3418_; uint8_t v_isSharedCheck_3425_; 
v_a_3415_ = lean_ctor_get(v___x_3414_, 0);
v_isSharedCheck_3425_ = !lean_is_exclusive(v___x_3414_);
if (v_isSharedCheck_3425_ == 0)
{
v___x_3417_ = v___x_3414_;
v_isShared_3418_ = v_isSharedCheck_3425_;
goto v_resetjp_3416_;
}
else
{
lean_inc(v_a_3415_);
lean_dec(v___x_3414_);
v___x_3417_ = lean_box(0);
v_isShared_3418_ = v_isSharedCheck_3425_;
goto v_resetjp_3416_;
}
v_resetjp_3416_:
{
lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3423_; 
v___x_3419_ = lean_array_to_list(v_a_3415_);
v___x_3420_ = lean_box(0);
v___x_3421_ = l_List_mapTR_loop___at___00Lean_MVarId_casesRec_spec__0(v___x_3419_, v___x_3420_);
if (v_isShared_3418_ == 0)
{
lean_ctor_set(v___x_3417_, 0, v___x_3421_);
v___x_3423_ = v___x_3417_;
goto v_reusejp_3422_;
}
else
{
lean_object* v_reuseFailAlloc_3424_; 
v_reuseFailAlloc_3424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3424_, 0, v___x_3421_);
v___x_3423_ = v_reuseFailAlloc_3424_;
goto v_reusejp_3422_;
}
v_reusejp_3422_:
{
return v___x_3423_;
}
}
}
else
{
lean_object* v_a_3426_; lean_object* v___x_3428_; uint8_t v_isShared_3429_; uint8_t v_isSharedCheck_3433_; 
v_a_3426_ = lean_ctor_get(v___x_3414_, 0);
v_isSharedCheck_3433_ = !lean_is_exclusive(v___x_3414_);
if (v_isSharedCheck_3433_ == 0)
{
v___x_3428_ = v___x_3414_;
v_isShared_3429_ = v_isSharedCheck_3433_;
goto v_resetjp_3427_;
}
else
{
lean_inc(v_a_3426_);
lean_dec(v___x_3414_);
v___x_3428_ = lean_box(0);
v_isShared_3429_ = v_isSharedCheck_3433_;
goto v_resetjp_3427_;
}
v_resetjp_3427_:
{
lean_object* v___x_3431_; 
if (v_isShared_3429_ == 0)
{
v___x_3431_ = v___x_3428_;
goto v_reusejp_3430_;
}
else
{
lean_object* v_reuseFailAlloc_3432_; 
v_reuseFailAlloc_3432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3432_, 0, v_a_3426_);
v___x_3431_ = v_reuseFailAlloc_3432_;
goto v_reusejp_3430_;
}
v_reusejp_3430_:
{
return v___x_3431_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3___lam__0___boxed(lean_object* v_mvarId_3434_, lean_object* v___x_3435_, lean_object* v___x_3436_, lean_object* v___x_3437_, lean_object* v___x_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_){
_start:
{
uint8_t v___x_6516__boxed_3444_; lean_object* v_res_3445_; 
v___x_6516__boxed_3444_ = lean_unbox(v___x_3437_);
v_res_3445_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3___lam__0(v_mvarId_3434_, v___x_3435_, v___x_3436_, v___x_6516__boxed_3444_, v___x_3438_, v___y_3439_, v___y_3440_, v___y_3441_, v___y_3442_);
lean_dec(v___y_3442_);
lean_dec_ref(v___y_3441_);
lean_dec(v___y_3440_);
lean_dec_ref(v___y_3439_);
return v_res_3445_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5(lean_object* v_p_3451_, lean_object* v_mvarId_3452_, lean_object* v_as_3453_, size_t v_sz_3454_, size_t v_i_3455_, lean_object* v_b_3456_, lean_object* v___y_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_, lean_object* v___y_3460_){
_start:
{
uint8_t v___x_3462_; 
v___x_3462_ = lean_usize_dec_lt(v_i_3455_, v_sz_3454_);
if (v___x_3462_ == 0)
{
lean_object* v___x_3463_; 
lean_dec(v_mvarId_3452_);
lean_dec_ref(v_p_3451_);
v___x_3463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3463_, 0, v_b_3456_);
return v___x_3463_;
}
else
{
lean_object* v_snd_3464_; lean_object* v___x_3466_; uint8_t v_isShared_3467_; uint8_t v_isSharedCheck_3532_; 
v_snd_3464_ = lean_ctor_get(v_b_3456_, 1);
v_isSharedCheck_3532_ = !lean_is_exclusive(v_b_3456_);
if (v_isSharedCheck_3532_ == 0)
{
lean_object* v_unused_3533_; 
v_unused_3533_ = lean_ctor_get(v_b_3456_, 0);
lean_dec(v_unused_3533_);
v___x_3466_ = v_b_3456_;
v_isShared_3467_ = v_isSharedCheck_3532_;
goto v_resetjp_3465_;
}
else
{
lean_inc(v_snd_3464_);
lean_dec(v_b_3456_);
v___x_3466_ = lean_box(0);
v_isShared_3467_ = v_isSharedCheck_3532_;
goto v_resetjp_3465_;
}
v_resetjp_3465_:
{
lean_object* v___x_3468_; lean_object* v_a_3470_; lean_object* v_a_3477_; 
v___x_3468_ = lean_box(0);
v_a_3477_ = lean_array_uget(v_as_3453_, v_i_3455_);
if (lean_obj_tag(v_a_3477_) == 0)
{
v_a_3470_ = v_snd_3464_;
goto v___jp_3469_;
}
else
{
lean_object* v_val_3478_; lean_object* v___x_3480_; uint8_t v_isShared_3481_; uint8_t v_isSharedCheck_3531_; 
v_val_3478_ = lean_ctor_get(v_a_3477_, 0);
v_isSharedCheck_3531_ = !lean_is_exclusive(v_a_3477_);
if (v_isSharedCheck_3531_ == 0)
{
v___x_3480_ = v_a_3477_;
v_isShared_3481_ = v_isSharedCheck_3531_;
goto v_resetjp_3479_;
}
else
{
lean_inc(v_val_3478_);
lean_dec(v_a_3477_);
v___x_3480_ = lean_box(0);
v_isShared_3481_ = v_isSharedCheck_3531_;
goto v_resetjp_3479_;
}
v_resetjp_3479_:
{
lean_object* v___x_3482_; 
lean_inc_ref(v_p_3451_);
lean_inc(v___y_3460_);
lean_inc_ref(v___y_3459_);
lean_inc(v___y_3458_);
lean_inc_ref(v___y_3457_);
lean_inc(v_val_3478_);
v___x_3482_ = lean_apply_6(v_p_3451_, v_val_3478_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_, lean_box(0));
if (lean_obj_tag(v___x_3482_) == 0)
{
lean_object* v_a_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; uint8_t v___x_3486_; 
v_a_3483_ = lean_ctor_get(v___x_3482_, 0);
lean_inc(v_a_3483_);
lean_dec_ref_known(v___x_3482_, 1);
v___x_3484_ = lean_box(0);
v___x_3485_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5___closed__0));
v___x_3486_ = lean_unbox(v_a_3483_);
lean_dec(v_a_3483_);
if (v___x_3486_ == 0)
{
lean_del_object(v___x_3480_);
lean_dec(v_val_3478_);
lean_dec(v_snd_3464_);
v_a_3470_ = v___x_3485_;
goto v___jp_3469_;
}
else
{
lean_object* v___x_3487_; lean_object* v___x_3488_; uint8_t v___x_3489_; lean_object* v___x_3490_; lean_object* v___f_3491_; lean_object* v___x_3492_; 
v___x_3487_ = l_Lean_LocalDecl_fvarId(v_val_3478_);
lean_dec(v_val_3478_);
v___x_3488_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5___closed__1));
v___x_3489_ = 0;
v___x_3490_ = lean_box(v___x_3489_);
lean_inc(v_mvarId_3452_);
v___f_3491_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3___lam__0___boxed), 10, 5);
lean_closure_set(v___f_3491_, 0, v_mvarId_3452_);
lean_closure_set(v___f_3491_, 1, v___x_3487_);
lean_closure_set(v___f_3491_, 2, v___x_3488_);
lean_closure_set(v___f_3491_, 3, v___x_3490_);
lean_closure_set(v___f_3491_, 4, v___x_3468_);
v___x_3492_ = l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1___redArg(v___f_3491_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_);
if (lean_obj_tag(v___x_3492_) == 0)
{
lean_object* v_a_3493_; lean_object* v___x_3495_; uint8_t v_isShared_3496_; uint8_t v_isSharedCheck_3514_; 
v_a_3493_ = lean_ctor_get(v___x_3492_, 0);
v_isSharedCheck_3514_ = !lean_is_exclusive(v___x_3492_);
if (v_isSharedCheck_3514_ == 0)
{
v___x_3495_ = v___x_3492_;
v_isShared_3496_ = v_isSharedCheck_3514_;
goto v_resetjp_3494_;
}
else
{
lean_inc(v_a_3493_);
lean_dec(v___x_3492_);
v___x_3495_ = lean_box(0);
v_isShared_3496_ = v_isSharedCheck_3514_;
goto v_resetjp_3494_;
}
v_resetjp_3494_:
{
if (lean_obj_tag(v_a_3493_) == 0)
{
lean_del_object(v___x_3495_);
lean_del_object(v___x_3480_);
lean_dec(v_snd_3464_);
v_a_3470_ = v___x_3485_;
goto v___jp_3469_;
}
else
{
lean_object* v___x_3498_; 
lean_del_object(v___x_3466_);
lean_dec(v_mvarId_3452_);
lean_dec_ref(v_p_3451_);
lean_inc_ref(v_a_3493_);
if (v_isShared_3481_ == 0)
{
lean_ctor_set(v___x_3480_, 0, v_a_3493_);
v___x_3498_ = v___x_3480_;
goto v_reusejp_3497_;
}
else
{
lean_object* v_reuseFailAlloc_3513_; 
v_reuseFailAlloc_3513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3513_, 0, v_a_3493_);
v___x_3498_ = v_reuseFailAlloc_3513_;
goto v_reusejp_3497_;
}
v_reusejp_3497_:
{
lean_object* v___x_3500_; uint8_t v_isShared_3501_; uint8_t v_isSharedCheck_3511_; 
v_isSharedCheck_3511_ = !lean_is_exclusive(v_a_3493_);
if (v_isSharedCheck_3511_ == 0)
{
lean_object* v_unused_3512_; 
v_unused_3512_ = lean_ctor_get(v_a_3493_, 0);
lean_dec(v_unused_3512_);
v___x_3500_ = v_a_3493_;
v_isShared_3501_ = v_isSharedCheck_3511_;
goto v_resetjp_3499_;
}
else
{
lean_dec(v_a_3493_);
v___x_3500_ = lean_box(0);
v_isShared_3501_ = v_isSharedCheck_3511_;
goto v_resetjp_3499_;
}
v_resetjp_3499_:
{
lean_object* v___x_3502_; lean_object* v___x_3504_; 
v___x_3502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3502_, 0, v___x_3498_);
lean_ctor_set(v___x_3502_, 1, v___x_3484_);
if (v_isShared_3501_ == 0)
{
lean_ctor_set_tag(v___x_3500_, 0);
lean_ctor_set(v___x_3500_, 0, v___x_3502_);
v___x_3504_ = v___x_3500_;
goto v_reusejp_3503_;
}
else
{
lean_object* v_reuseFailAlloc_3510_; 
v_reuseFailAlloc_3510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3510_, 0, v___x_3502_);
v___x_3504_ = v_reuseFailAlloc_3510_;
goto v_reusejp_3503_;
}
v_reusejp_3503_:
{
lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3508_; 
v___x_3505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3505_, 0, v___x_3504_);
v___x_3506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3506_, 0, v___x_3505_);
lean_ctor_set(v___x_3506_, 1, v_snd_3464_);
if (v_isShared_3496_ == 0)
{
lean_ctor_set(v___x_3495_, 0, v___x_3506_);
v___x_3508_ = v___x_3495_;
goto v_reusejp_3507_;
}
else
{
lean_object* v_reuseFailAlloc_3509_; 
v_reuseFailAlloc_3509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3509_, 0, v___x_3506_);
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
}
else
{
lean_object* v_a_3515_; lean_object* v___x_3517_; uint8_t v_isShared_3518_; uint8_t v_isSharedCheck_3522_; 
lean_del_object(v___x_3480_);
lean_del_object(v___x_3466_);
lean_dec(v_snd_3464_);
lean_dec(v_mvarId_3452_);
lean_dec_ref(v_p_3451_);
v_a_3515_ = lean_ctor_get(v___x_3492_, 0);
v_isSharedCheck_3522_ = !lean_is_exclusive(v___x_3492_);
if (v_isSharedCheck_3522_ == 0)
{
v___x_3517_ = v___x_3492_;
v_isShared_3518_ = v_isSharedCheck_3522_;
goto v_resetjp_3516_;
}
else
{
lean_inc(v_a_3515_);
lean_dec(v___x_3492_);
v___x_3517_ = lean_box(0);
v_isShared_3518_ = v_isSharedCheck_3522_;
goto v_resetjp_3516_;
}
v_resetjp_3516_:
{
lean_object* v___x_3520_; 
if (v_isShared_3518_ == 0)
{
v___x_3520_ = v___x_3517_;
goto v_reusejp_3519_;
}
else
{
lean_object* v_reuseFailAlloc_3521_; 
v_reuseFailAlloc_3521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3521_, 0, v_a_3515_);
v___x_3520_ = v_reuseFailAlloc_3521_;
goto v_reusejp_3519_;
}
v_reusejp_3519_:
{
return v___x_3520_;
}
}
}
}
}
else
{
lean_object* v_a_3523_; lean_object* v___x_3525_; uint8_t v_isShared_3526_; uint8_t v_isSharedCheck_3530_; 
lean_del_object(v___x_3480_);
lean_dec(v_val_3478_);
lean_del_object(v___x_3466_);
lean_dec(v_snd_3464_);
lean_dec(v_mvarId_3452_);
lean_dec_ref(v_p_3451_);
v_a_3523_ = lean_ctor_get(v___x_3482_, 0);
v_isSharedCheck_3530_ = !lean_is_exclusive(v___x_3482_);
if (v_isSharedCheck_3530_ == 0)
{
v___x_3525_ = v___x_3482_;
v_isShared_3526_ = v_isSharedCheck_3530_;
goto v_resetjp_3524_;
}
else
{
lean_inc(v_a_3523_);
lean_dec(v___x_3482_);
v___x_3525_ = lean_box(0);
v_isShared_3526_ = v_isSharedCheck_3530_;
goto v_resetjp_3524_;
}
v_resetjp_3524_:
{
lean_object* v___x_3528_; 
if (v_isShared_3526_ == 0)
{
v___x_3528_ = v___x_3525_;
goto v_reusejp_3527_;
}
else
{
lean_object* v_reuseFailAlloc_3529_; 
v_reuseFailAlloc_3529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3529_, 0, v_a_3523_);
v___x_3528_ = v_reuseFailAlloc_3529_;
goto v_reusejp_3527_;
}
v_reusejp_3527_:
{
return v___x_3528_;
}
}
}
}
}
v___jp_3469_:
{
lean_object* v___x_3472_; 
if (v_isShared_3467_ == 0)
{
lean_ctor_set(v___x_3466_, 1, v_a_3470_);
lean_ctor_set(v___x_3466_, 0, v___x_3468_);
v___x_3472_ = v___x_3466_;
goto v_reusejp_3471_;
}
else
{
lean_object* v_reuseFailAlloc_3476_; 
v_reuseFailAlloc_3476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3476_, 0, v___x_3468_);
lean_ctor_set(v_reuseFailAlloc_3476_, 1, v_a_3470_);
v___x_3472_ = v_reuseFailAlloc_3476_;
goto v_reusejp_3471_;
}
v_reusejp_3471_:
{
size_t v___x_3473_; size_t v___x_3474_; 
v___x_3473_ = ((size_t)1ULL);
v___x_3474_ = lean_usize_add(v_i_3455_, v___x_3473_);
v_i_3455_ = v___x_3474_;
v_b_3456_ = v___x_3472_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5___boxed(lean_object* v_p_3534_, lean_object* v_mvarId_3535_, lean_object* v_as_3536_, lean_object* v_sz_3537_, lean_object* v_i_3538_, lean_object* v_b_3539_, lean_object* v___y_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_){
_start:
{
size_t v_sz_boxed_3545_; size_t v_i_boxed_3546_; lean_object* v_res_3547_; 
v_sz_boxed_3545_ = lean_unbox_usize(v_sz_3537_);
lean_dec(v_sz_3537_);
v_i_boxed_3546_ = lean_unbox_usize(v_i_3538_);
lean_dec(v_i_3538_);
v_res_3547_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5(v_p_3534_, v_mvarId_3535_, v_as_3536_, v_sz_boxed_3545_, v_i_boxed_3546_, v_b_3539_, v___y_3540_, v___y_3541_, v___y_3542_, v___y_3543_);
lean_dec(v___y_3543_);
lean_dec_ref(v___y_3542_);
lean_dec(v___y_3541_);
lean_dec_ref(v___y_3540_);
lean_dec_ref(v_as_3536_);
return v_res_3547_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4(lean_object* v_p_3548_, lean_object* v_mvarId_3549_, lean_object* v_as_3550_, size_t v_sz_3551_, size_t v_i_3552_, lean_object* v_b_3553_, lean_object* v___y_3554_, lean_object* v___y_3555_, lean_object* v___y_3556_, lean_object* v___y_3557_){
_start:
{
uint8_t v___x_3559_; 
v___x_3559_ = lean_usize_dec_lt(v_i_3552_, v_sz_3551_);
if (v___x_3559_ == 0)
{
lean_object* v___x_3560_; 
lean_dec(v_mvarId_3549_);
lean_dec_ref(v_p_3548_);
v___x_3560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3560_, 0, v_b_3553_);
return v___x_3560_;
}
else
{
lean_object* v_snd_3561_; lean_object* v___x_3563_; uint8_t v_isShared_3564_; uint8_t v_isSharedCheck_3629_; 
v_snd_3561_ = lean_ctor_get(v_b_3553_, 1);
v_isSharedCheck_3629_ = !lean_is_exclusive(v_b_3553_);
if (v_isSharedCheck_3629_ == 0)
{
lean_object* v_unused_3630_; 
v_unused_3630_ = lean_ctor_get(v_b_3553_, 0);
lean_dec(v_unused_3630_);
v___x_3563_ = v_b_3553_;
v_isShared_3564_ = v_isSharedCheck_3629_;
goto v_resetjp_3562_;
}
else
{
lean_inc(v_snd_3561_);
lean_dec(v_b_3553_);
v___x_3563_ = lean_box(0);
v_isShared_3564_ = v_isSharedCheck_3629_;
goto v_resetjp_3562_;
}
v_resetjp_3562_:
{
lean_object* v___x_3565_; lean_object* v_a_3567_; lean_object* v_a_3574_; 
v___x_3565_ = lean_box(0);
v_a_3574_ = lean_array_uget(v_as_3550_, v_i_3552_);
if (lean_obj_tag(v_a_3574_) == 0)
{
v_a_3567_ = v_snd_3561_;
goto v___jp_3566_;
}
else
{
lean_object* v_val_3575_; lean_object* v___x_3577_; uint8_t v_isShared_3578_; uint8_t v_isSharedCheck_3628_; 
v_val_3575_ = lean_ctor_get(v_a_3574_, 0);
v_isSharedCheck_3628_ = !lean_is_exclusive(v_a_3574_);
if (v_isSharedCheck_3628_ == 0)
{
v___x_3577_ = v_a_3574_;
v_isShared_3578_ = v_isSharedCheck_3628_;
goto v_resetjp_3576_;
}
else
{
lean_inc(v_val_3575_);
lean_dec(v_a_3574_);
v___x_3577_ = lean_box(0);
v_isShared_3578_ = v_isSharedCheck_3628_;
goto v_resetjp_3576_;
}
v_resetjp_3576_:
{
lean_object* v___x_3579_; 
lean_inc_ref(v_p_3548_);
lean_inc(v___y_3557_);
lean_inc_ref(v___y_3556_);
lean_inc(v___y_3555_);
lean_inc_ref(v___y_3554_);
lean_inc(v_val_3575_);
v___x_3579_ = lean_apply_6(v_p_3548_, v_val_3575_, v___y_3554_, v___y_3555_, v___y_3556_, v___y_3557_, lean_box(0));
if (lean_obj_tag(v___x_3579_) == 0)
{
lean_object* v_a_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; uint8_t v___x_3583_; 
v_a_3580_ = lean_ctor_get(v___x_3579_, 0);
lean_inc(v_a_3580_);
lean_dec_ref_known(v___x_3579_, 1);
v___x_3581_ = lean_box(0);
v___x_3582_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5___closed__0));
v___x_3583_ = lean_unbox(v_a_3580_);
lean_dec(v_a_3580_);
if (v___x_3583_ == 0)
{
lean_del_object(v___x_3577_);
lean_dec(v_val_3575_);
lean_dec(v_snd_3561_);
v_a_3567_ = v___x_3582_;
goto v___jp_3566_;
}
else
{
lean_object* v___x_3584_; lean_object* v___x_3585_; uint8_t v___x_3586_; lean_object* v___x_3587_; lean_object* v___f_3588_; lean_object* v___x_3589_; 
v___x_3584_ = l_Lean_LocalDecl_fvarId(v_val_3575_);
lean_dec(v_val_3575_);
v___x_3585_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5___closed__1));
v___x_3586_ = 0;
v___x_3587_ = lean_box(v___x_3586_);
lean_inc(v_mvarId_3549_);
v___f_3588_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3___lam__0___boxed), 10, 5);
lean_closure_set(v___f_3588_, 0, v_mvarId_3549_);
lean_closure_set(v___f_3588_, 1, v___x_3584_);
lean_closure_set(v___f_3588_, 2, v___x_3585_);
lean_closure_set(v___f_3588_, 3, v___x_3587_);
lean_closure_set(v___f_3588_, 4, v___x_3565_);
v___x_3589_ = l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1___redArg(v___f_3588_, v___y_3554_, v___y_3555_, v___y_3556_, v___y_3557_);
if (lean_obj_tag(v___x_3589_) == 0)
{
lean_object* v_a_3590_; lean_object* v___x_3592_; uint8_t v_isShared_3593_; uint8_t v_isSharedCheck_3611_; 
v_a_3590_ = lean_ctor_get(v___x_3589_, 0);
v_isSharedCheck_3611_ = !lean_is_exclusive(v___x_3589_);
if (v_isSharedCheck_3611_ == 0)
{
v___x_3592_ = v___x_3589_;
v_isShared_3593_ = v_isSharedCheck_3611_;
goto v_resetjp_3591_;
}
else
{
lean_inc(v_a_3590_);
lean_dec(v___x_3589_);
v___x_3592_ = lean_box(0);
v_isShared_3593_ = v_isSharedCheck_3611_;
goto v_resetjp_3591_;
}
v_resetjp_3591_:
{
if (lean_obj_tag(v_a_3590_) == 0)
{
lean_del_object(v___x_3592_);
lean_del_object(v___x_3577_);
lean_dec(v_snd_3561_);
v_a_3567_ = v___x_3582_;
goto v___jp_3566_;
}
else
{
lean_object* v___x_3595_; 
lean_del_object(v___x_3563_);
lean_dec(v_mvarId_3549_);
lean_dec_ref(v_p_3548_);
lean_inc_ref(v_a_3590_);
if (v_isShared_3578_ == 0)
{
lean_ctor_set(v___x_3577_, 0, v_a_3590_);
v___x_3595_ = v___x_3577_;
goto v_reusejp_3594_;
}
else
{
lean_object* v_reuseFailAlloc_3610_; 
v_reuseFailAlloc_3610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3610_, 0, v_a_3590_);
v___x_3595_ = v_reuseFailAlloc_3610_;
goto v_reusejp_3594_;
}
v_reusejp_3594_:
{
lean_object* v___x_3597_; uint8_t v_isShared_3598_; uint8_t v_isSharedCheck_3608_; 
v_isSharedCheck_3608_ = !lean_is_exclusive(v_a_3590_);
if (v_isSharedCheck_3608_ == 0)
{
lean_object* v_unused_3609_; 
v_unused_3609_ = lean_ctor_get(v_a_3590_, 0);
lean_dec(v_unused_3609_);
v___x_3597_ = v_a_3590_;
v_isShared_3598_ = v_isSharedCheck_3608_;
goto v_resetjp_3596_;
}
else
{
lean_dec(v_a_3590_);
v___x_3597_ = lean_box(0);
v_isShared_3598_ = v_isSharedCheck_3608_;
goto v_resetjp_3596_;
}
v_resetjp_3596_:
{
lean_object* v___x_3599_; lean_object* v___x_3601_; 
v___x_3599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3599_, 0, v___x_3595_);
lean_ctor_set(v___x_3599_, 1, v___x_3581_);
if (v_isShared_3598_ == 0)
{
lean_ctor_set_tag(v___x_3597_, 0);
lean_ctor_set(v___x_3597_, 0, v___x_3599_);
v___x_3601_ = v___x_3597_;
goto v_reusejp_3600_;
}
else
{
lean_object* v_reuseFailAlloc_3607_; 
v_reuseFailAlloc_3607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3607_, 0, v___x_3599_);
v___x_3601_ = v_reuseFailAlloc_3607_;
goto v_reusejp_3600_;
}
v_reusejp_3600_:
{
lean_object* v___x_3602_; lean_object* v___x_3603_; lean_object* v___x_3605_; 
v___x_3602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3602_, 0, v___x_3601_);
v___x_3603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3603_, 0, v___x_3602_);
lean_ctor_set(v___x_3603_, 1, v_snd_3561_);
if (v_isShared_3593_ == 0)
{
lean_ctor_set(v___x_3592_, 0, v___x_3603_);
v___x_3605_ = v___x_3592_;
goto v_reusejp_3604_;
}
else
{
lean_object* v_reuseFailAlloc_3606_; 
v_reuseFailAlloc_3606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3606_, 0, v___x_3603_);
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
}
}
else
{
lean_object* v_a_3612_; lean_object* v___x_3614_; uint8_t v_isShared_3615_; uint8_t v_isSharedCheck_3619_; 
lean_del_object(v___x_3577_);
lean_del_object(v___x_3563_);
lean_dec(v_snd_3561_);
lean_dec(v_mvarId_3549_);
lean_dec_ref(v_p_3548_);
v_a_3612_ = lean_ctor_get(v___x_3589_, 0);
v_isSharedCheck_3619_ = !lean_is_exclusive(v___x_3589_);
if (v_isSharedCheck_3619_ == 0)
{
v___x_3614_ = v___x_3589_;
v_isShared_3615_ = v_isSharedCheck_3619_;
goto v_resetjp_3613_;
}
else
{
lean_inc(v_a_3612_);
lean_dec(v___x_3589_);
v___x_3614_ = lean_box(0);
v_isShared_3615_ = v_isSharedCheck_3619_;
goto v_resetjp_3613_;
}
v_resetjp_3613_:
{
lean_object* v___x_3617_; 
if (v_isShared_3615_ == 0)
{
v___x_3617_ = v___x_3614_;
goto v_reusejp_3616_;
}
else
{
lean_object* v_reuseFailAlloc_3618_; 
v_reuseFailAlloc_3618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3618_, 0, v_a_3612_);
v___x_3617_ = v_reuseFailAlloc_3618_;
goto v_reusejp_3616_;
}
v_reusejp_3616_:
{
return v___x_3617_;
}
}
}
}
}
else
{
lean_object* v_a_3620_; lean_object* v___x_3622_; uint8_t v_isShared_3623_; uint8_t v_isSharedCheck_3627_; 
lean_del_object(v___x_3577_);
lean_dec(v_val_3575_);
lean_del_object(v___x_3563_);
lean_dec(v_snd_3561_);
lean_dec(v_mvarId_3549_);
lean_dec_ref(v_p_3548_);
v_a_3620_ = lean_ctor_get(v___x_3579_, 0);
v_isSharedCheck_3627_ = !lean_is_exclusive(v___x_3579_);
if (v_isSharedCheck_3627_ == 0)
{
v___x_3622_ = v___x_3579_;
v_isShared_3623_ = v_isSharedCheck_3627_;
goto v_resetjp_3621_;
}
else
{
lean_inc(v_a_3620_);
lean_dec(v___x_3579_);
v___x_3622_ = lean_box(0);
v_isShared_3623_ = v_isSharedCheck_3627_;
goto v_resetjp_3621_;
}
v_resetjp_3621_:
{
lean_object* v___x_3625_; 
if (v_isShared_3623_ == 0)
{
v___x_3625_ = v___x_3622_;
goto v_reusejp_3624_;
}
else
{
lean_object* v_reuseFailAlloc_3626_; 
v_reuseFailAlloc_3626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3626_, 0, v_a_3620_);
v___x_3625_ = v_reuseFailAlloc_3626_;
goto v_reusejp_3624_;
}
v_reusejp_3624_:
{
return v___x_3625_;
}
}
}
}
}
v___jp_3566_:
{
lean_object* v___x_3569_; 
if (v_isShared_3564_ == 0)
{
lean_ctor_set(v___x_3563_, 1, v_a_3567_);
lean_ctor_set(v___x_3563_, 0, v___x_3565_);
v___x_3569_ = v___x_3563_;
goto v_reusejp_3568_;
}
else
{
lean_object* v_reuseFailAlloc_3573_; 
v_reuseFailAlloc_3573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3573_, 0, v___x_3565_);
lean_ctor_set(v_reuseFailAlloc_3573_, 1, v_a_3567_);
v___x_3569_ = v_reuseFailAlloc_3573_;
goto v_reusejp_3568_;
}
v_reusejp_3568_:
{
size_t v___x_3570_; size_t v___x_3571_; lean_object* v___x_3572_; 
v___x_3570_ = ((size_t)1ULL);
v___x_3571_ = lean_usize_add(v_i_3552_, v___x_3570_);
v___x_3572_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5(v_p_3548_, v_mvarId_3549_, v_as_3550_, v_sz_3551_, v___x_3571_, v___x_3569_, v___y_3554_, v___y_3555_, v___y_3556_, v___y_3557_);
return v___x_3572_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4___boxed(lean_object* v_p_3631_, lean_object* v_mvarId_3632_, lean_object* v_as_3633_, lean_object* v_sz_3634_, lean_object* v_i_3635_, lean_object* v_b_3636_, lean_object* v___y_3637_, lean_object* v___y_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_, lean_object* v___y_3641_){
_start:
{
size_t v_sz_boxed_3642_; size_t v_i_boxed_3643_; lean_object* v_res_3644_; 
v_sz_boxed_3642_ = lean_unbox_usize(v_sz_3634_);
lean_dec(v_sz_3634_);
v_i_boxed_3643_ = lean_unbox_usize(v_i_3635_);
lean_dec(v_i_3635_);
v_res_3644_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4(v_p_3631_, v_mvarId_3632_, v_as_3633_, v_sz_boxed_3642_, v_i_boxed_3643_, v_b_3636_, v___y_3637_, v___y_3638_, v___y_3639_, v___y_3640_);
lean_dec(v___y_3640_);
lean_dec_ref(v___y_3639_);
lean_dec(v___y_3638_);
lean_dec_ref(v___y_3637_);
lean_dec_ref(v_as_3633_);
return v_res_3644_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2(lean_object* v_init_3645_, lean_object* v_p_3646_, lean_object* v_mvarId_3647_, lean_object* v_n_3648_, lean_object* v_b_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_){
_start:
{
if (lean_obj_tag(v_n_3648_) == 0)
{
lean_object* v_cs_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; size_t v_sz_3658_; size_t v___x_3659_; lean_object* v___x_3660_; 
v_cs_3655_ = lean_ctor_get(v_n_3648_, 0);
v___x_3656_ = lean_box(0);
v___x_3657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3657_, 0, v___x_3656_);
lean_ctor_set(v___x_3657_, 1, v_b_3649_);
v_sz_3658_ = lean_array_size(v_cs_3655_);
v___x_3659_ = ((size_t)0ULL);
v___x_3660_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__3(v_init_3645_, v_p_3646_, v_mvarId_3647_, v_cs_3655_, v_sz_3658_, v___x_3659_, v___x_3657_, v___y_3650_, v___y_3651_, v___y_3652_, v___y_3653_);
if (lean_obj_tag(v___x_3660_) == 0)
{
lean_object* v_a_3661_; lean_object* v___x_3663_; uint8_t v_isShared_3664_; uint8_t v_isSharedCheck_3675_; 
v_a_3661_ = lean_ctor_get(v___x_3660_, 0);
v_isSharedCheck_3675_ = !lean_is_exclusive(v___x_3660_);
if (v_isSharedCheck_3675_ == 0)
{
v___x_3663_ = v___x_3660_;
v_isShared_3664_ = v_isSharedCheck_3675_;
goto v_resetjp_3662_;
}
else
{
lean_inc(v_a_3661_);
lean_dec(v___x_3660_);
v___x_3663_ = lean_box(0);
v_isShared_3664_ = v_isSharedCheck_3675_;
goto v_resetjp_3662_;
}
v_resetjp_3662_:
{
lean_object* v_fst_3665_; 
v_fst_3665_ = lean_ctor_get(v_a_3661_, 0);
if (lean_obj_tag(v_fst_3665_) == 0)
{
lean_object* v_snd_3666_; lean_object* v___x_3667_; lean_object* v___x_3669_; 
v_snd_3666_ = lean_ctor_get(v_a_3661_, 1);
lean_inc(v_snd_3666_);
lean_dec(v_a_3661_);
v___x_3667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3667_, 0, v_snd_3666_);
if (v_isShared_3664_ == 0)
{
lean_ctor_set(v___x_3663_, 0, v___x_3667_);
v___x_3669_ = v___x_3663_;
goto v_reusejp_3668_;
}
else
{
lean_object* v_reuseFailAlloc_3670_; 
v_reuseFailAlloc_3670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3670_, 0, v___x_3667_);
v___x_3669_ = v_reuseFailAlloc_3670_;
goto v_reusejp_3668_;
}
v_reusejp_3668_:
{
return v___x_3669_;
}
}
else
{
lean_object* v_val_3671_; lean_object* v___x_3673_; 
lean_inc_ref(v_fst_3665_);
lean_dec(v_a_3661_);
v_val_3671_ = lean_ctor_get(v_fst_3665_, 0);
lean_inc(v_val_3671_);
lean_dec_ref_known(v_fst_3665_, 1);
if (v_isShared_3664_ == 0)
{
lean_ctor_set(v___x_3663_, 0, v_val_3671_);
v___x_3673_ = v___x_3663_;
goto v_reusejp_3672_;
}
else
{
lean_object* v_reuseFailAlloc_3674_; 
v_reuseFailAlloc_3674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3674_, 0, v_val_3671_);
v___x_3673_ = v_reuseFailAlloc_3674_;
goto v_reusejp_3672_;
}
v_reusejp_3672_:
{
return v___x_3673_;
}
}
}
}
else
{
lean_object* v_a_3676_; lean_object* v___x_3678_; uint8_t v_isShared_3679_; uint8_t v_isSharedCheck_3683_; 
v_a_3676_ = lean_ctor_get(v___x_3660_, 0);
v_isSharedCheck_3683_ = !lean_is_exclusive(v___x_3660_);
if (v_isSharedCheck_3683_ == 0)
{
v___x_3678_ = v___x_3660_;
v_isShared_3679_ = v_isSharedCheck_3683_;
goto v_resetjp_3677_;
}
else
{
lean_inc(v_a_3676_);
lean_dec(v___x_3660_);
v___x_3678_ = lean_box(0);
v_isShared_3679_ = v_isSharedCheck_3683_;
goto v_resetjp_3677_;
}
v_resetjp_3677_:
{
lean_object* v___x_3681_; 
if (v_isShared_3679_ == 0)
{
v___x_3681_ = v___x_3678_;
goto v_reusejp_3680_;
}
else
{
lean_object* v_reuseFailAlloc_3682_; 
v_reuseFailAlloc_3682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3682_, 0, v_a_3676_);
v___x_3681_ = v_reuseFailAlloc_3682_;
goto v_reusejp_3680_;
}
v_reusejp_3680_:
{
return v___x_3681_;
}
}
}
}
else
{
lean_object* v_vs_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; size_t v_sz_3687_; size_t v___x_3688_; lean_object* v___x_3689_; 
v_vs_3684_ = lean_ctor_get(v_n_3648_, 0);
v___x_3685_ = lean_box(0);
v___x_3686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3686_, 0, v___x_3685_);
lean_ctor_set(v___x_3686_, 1, v_b_3649_);
v_sz_3687_ = lean_array_size(v_vs_3684_);
v___x_3688_ = ((size_t)0ULL);
v___x_3689_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4(v_p_3646_, v_mvarId_3647_, v_vs_3684_, v_sz_3687_, v___x_3688_, v___x_3686_, v___y_3650_, v___y_3651_, v___y_3652_, v___y_3653_);
if (lean_obj_tag(v___x_3689_) == 0)
{
lean_object* v_a_3690_; lean_object* v___x_3692_; uint8_t v_isShared_3693_; uint8_t v_isSharedCheck_3704_; 
v_a_3690_ = lean_ctor_get(v___x_3689_, 0);
v_isSharedCheck_3704_ = !lean_is_exclusive(v___x_3689_);
if (v_isSharedCheck_3704_ == 0)
{
v___x_3692_ = v___x_3689_;
v_isShared_3693_ = v_isSharedCheck_3704_;
goto v_resetjp_3691_;
}
else
{
lean_inc(v_a_3690_);
lean_dec(v___x_3689_);
v___x_3692_ = lean_box(0);
v_isShared_3693_ = v_isSharedCheck_3704_;
goto v_resetjp_3691_;
}
v_resetjp_3691_:
{
lean_object* v_fst_3694_; 
v_fst_3694_ = lean_ctor_get(v_a_3690_, 0);
if (lean_obj_tag(v_fst_3694_) == 0)
{
lean_object* v_snd_3695_; lean_object* v___x_3696_; lean_object* v___x_3698_; 
v_snd_3695_ = lean_ctor_get(v_a_3690_, 1);
lean_inc(v_snd_3695_);
lean_dec(v_a_3690_);
v___x_3696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3696_, 0, v_snd_3695_);
if (v_isShared_3693_ == 0)
{
lean_ctor_set(v___x_3692_, 0, v___x_3696_);
v___x_3698_ = v___x_3692_;
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
else
{
lean_object* v_val_3700_; lean_object* v___x_3702_; 
lean_inc_ref(v_fst_3694_);
lean_dec(v_a_3690_);
v_val_3700_ = lean_ctor_get(v_fst_3694_, 0);
lean_inc(v_val_3700_);
lean_dec_ref_known(v_fst_3694_, 1);
if (v_isShared_3693_ == 0)
{
lean_ctor_set(v___x_3692_, 0, v_val_3700_);
v___x_3702_ = v___x_3692_;
goto v_reusejp_3701_;
}
else
{
lean_object* v_reuseFailAlloc_3703_; 
v_reuseFailAlloc_3703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3703_, 0, v_val_3700_);
v___x_3702_ = v_reuseFailAlloc_3703_;
goto v_reusejp_3701_;
}
v_reusejp_3701_:
{
return v___x_3702_;
}
}
}
}
else
{
lean_object* v_a_3705_; lean_object* v___x_3707_; uint8_t v_isShared_3708_; uint8_t v_isSharedCheck_3712_; 
v_a_3705_ = lean_ctor_get(v___x_3689_, 0);
v_isSharedCheck_3712_ = !lean_is_exclusive(v___x_3689_);
if (v_isSharedCheck_3712_ == 0)
{
v___x_3707_ = v___x_3689_;
v_isShared_3708_ = v_isSharedCheck_3712_;
goto v_resetjp_3706_;
}
else
{
lean_inc(v_a_3705_);
lean_dec(v___x_3689_);
v___x_3707_ = lean_box(0);
v_isShared_3708_ = v_isSharedCheck_3712_;
goto v_resetjp_3706_;
}
v_resetjp_3706_:
{
lean_object* v___x_3710_; 
if (v_isShared_3708_ == 0)
{
v___x_3710_ = v___x_3707_;
goto v_reusejp_3709_;
}
else
{
lean_object* v_reuseFailAlloc_3711_; 
v_reuseFailAlloc_3711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3711_, 0, v_a_3705_);
v___x_3710_ = v_reuseFailAlloc_3711_;
goto v_reusejp_3709_;
}
v_reusejp_3709_:
{
return v___x_3710_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__3(lean_object* v_init_3713_, lean_object* v_p_3714_, lean_object* v_mvarId_3715_, lean_object* v_as_3716_, size_t v_sz_3717_, size_t v_i_3718_, lean_object* v_b_3719_, lean_object* v___y_3720_, lean_object* v___y_3721_, lean_object* v___y_3722_, lean_object* v___y_3723_){
_start:
{
uint8_t v___x_3725_; 
v___x_3725_ = lean_usize_dec_lt(v_i_3718_, v_sz_3717_);
if (v___x_3725_ == 0)
{
lean_object* v___x_3726_; 
lean_dec(v_mvarId_3715_);
lean_dec_ref(v_p_3714_);
v___x_3726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3726_, 0, v_b_3719_);
return v___x_3726_;
}
else
{
lean_object* v_snd_3727_; lean_object* v___x_3729_; uint8_t v_isShared_3730_; uint8_t v_isSharedCheck_3761_; 
v_snd_3727_ = lean_ctor_get(v_b_3719_, 1);
v_isSharedCheck_3761_ = !lean_is_exclusive(v_b_3719_);
if (v_isSharedCheck_3761_ == 0)
{
lean_object* v_unused_3762_; 
v_unused_3762_ = lean_ctor_get(v_b_3719_, 0);
lean_dec(v_unused_3762_);
v___x_3729_ = v_b_3719_;
v_isShared_3730_ = v_isSharedCheck_3761_;
goto v_resetjp_3728_;
}
else
{
lean_inc(v_snd_3727_);
lean_dec(v_b_3719_);
v___x_3729_ = lean_box(0);
v_isShared_3730_ = v_isSharedCheck_3761_;
goto v_resetjp_3728_;
}
v_resetjp_3728_:
{
lean_object* v_a_3731_; lean_object* v___x_3732_; 
v_a_3731_ = lean_array_uget_borrowed(v_as_3716_, v_i_3718_);
lean_inc(v_snd_3727_);
lean_inc(v_mvarId_3715_);
lean_inc_ref(v_p_3714_);
v___x_3732_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2(v_init_3713_, v_p_3714_, v_mvarId_3715_, v_a_3731_, v_snd_3727_, v___y_3720_, v___y_3721_, v___y_3722_, v___y_3723_);
if (lean_obj_tag(v___x_3732_) == 0)
{
lean_object* v_a_3733_; lean_object* v___x_3735_; uint8_t v_isShared_3736_; uint8_t v_isSharedCheck_3752_; 
v_a_3733_ = lean_ctor_get(v___x_3732_, 0);
v_isSharedCheck_3752_ = !lean_is_exclusive(v___x_3732_);
if (v_isSharedCheck_3752_ == 0)
{
v___x_3735_ = v___x_3732_;
v_isShared_3736_ = v_isSharedCheck_3752_;
goto v_resetjp_3734_;
}
else
{
lean_inc(v_a_3733_);
lean_dec(v___x_3732_);
v___x_3735_ = lean_box(0);
v_isShared_3736_ = v_isSharedCheck_3752_;
goto v_resetjp_3734_;
}
v_resetjp_3734_:
{
if (lean_obj_tag(v_a_3733_) == 0)
{
lean_object* v___x_3737_; lean_object* v___x_3739_; 
lean_dec(v_mvarId_3715_);
lean_dec_ref(v_p_3714_);
v___x_3737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3737_, 0, v_a_3733_);
if (v_isShared_3730_ == 0)
{
lean_ctor_set(v___x_3729_, 0, v___x_3737_);
v___x_3739_ = v___x_3729_;
goto v_reusejp_3738_;
}
else
{
lean_object* v_reuseFailAlloc_3743_; 
v_reuseFailAlloc_3743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3743_, 0, v___x_3737_);
lean_ctor_set(v_reuseFailAlloc_3743_, 1, v_snd_3727_);
v___x_3739_ = v_reuseFailAlloc_3743_;
goto v_reusejp_3738_;
}
v_reusejp_3738_:
{
lean_object* v___x_3741_; 
if (v_isShared_3736_ == 0)
{
lean_ctor_set(v___x_3735_, 0, v___x_3739_);
v___x_3741_ = v___x_3735_;
goto v_reusejp_3740_;
}
else
{
lean_object* v_reuseFailAlloc_3742_; 
v_reuseFailAlloc_3742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3742_, 0, v___x_3739_);
v___x_3741_ = v_reuseFailAlloc_3742_;
goto v_reusejp_3740_;
}
v_reusejp_3740_:
{
return v___x_3741_;
}
}
}
else
{
lean_object* v_a_3744_; lean_object* v___x_3745_; lean_object* v___x_3747_; 
lean_del_object(v___x_3735_);
lean_dec(v_snd_3727_);
v_a_3744_ = lean_ctor_get(v_a_3733_, 0);
lean_inc(v_a_3744_);
lean_dec_ref_known(v_a_3733_, 1);
v___x_3745_ = lean_box(0);
if (v_isShared_3730_ == 0)
{
lean_ctor_set(v___x_3729_, 1, v_a_3744_);
lean_ctor_set(v___x_3729_, 0, v___x_3745_);
v___x_3747_ = v___x_3729_;
goto v_reusejp_3746_;
}
else
{
lean_object* v_reuseFailAlloc_3751_; 
v_reuseFailAlloc_3751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3751_, 0, v___x_3745_);
lean_ctor_set(v_reuseFailAlloc_3751_, 1, v_a_3744_);
v___x_3747_ = v_reuseFailAlloc_3751_;
goto v_reusejp_3746_;
}
v_reusejp_3746_:
{
size_t v___x_3748_; size_t v___x_3749_; 
v___x_3748_ = ((size_t)1ULL);
v___x_3749_ = lean_usize_add(v_i_3718_, v___x_3748_);
v_i_3718_ = v___x_3749_;
v_b_3719_ = v___x_3747_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3753_; lean_object* v___x_3755_; uint8_t v_isShared_3756_; uint8_t v_isSharedCheck_3760_; 
lean_del_object(v___x_3729_);
lean_dec(v_snd_3727_);
lean_dec(v_mvarId_3715_);
lean_dec_ref(v_p_3714_);
v_a_3753_ = lean_ctor_get(v___x_3732_, 0);
v_isSharedCheck_3760_ = !lean_is_exclusive(v___x_3732_);
if (v_isSharedCheck_3760_ == 0)
{
v___x_3755_ = v___x_3732_;
v_isShared_3756_ = v_isSharedCheck_3760_;
goto v_resetjp_3754_;
}
else
{
lean_inc(v_a_3753_);
lean_dec(v___x_3732_);
v___x_3755_ = lean_box(0);
v_isShared_3756_ = v_isSharedCheck_3760_;
goto v_resetjp_3754_;
}
v_resetjp_3754_:
{
lean_object* v___x_3758_; 
if (v_isShared_3756_ == 0)
{
v___x_3758_ = v___x_3755_;
goto v_reusejp_3757_;
}
else
{
lean_object* v_reuseFailAlloc_3759_; 
v_reuseFailAlloc_3759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3759_, 0, v_a_3753_);
v___x_3758_ = v_reuseFailAlloc_3759_;
goto v_reusejp_3757_;
}
v_reusejp_3757_:
{
return v___x_3758_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__3___boxed(lean_object* v_init_3763_, lean_object* v_p_3764_, lean_object* v_mvarId_3765_, lean_object* v_as_3766_, lean_object* v_sz_3767_, lean_object* v_i_3768_, lean_object* v_b_3769_, lean_object* v___y_3770_, lean_object* v___y_3771_, lean_object* v___y_3772_, lean_object* v___y_3773_, lean_object* v___y_3774_){
_start:
{
size_t v_sz_boxed_3775_; size_t v_i_boxed_3776_; lean_object* v_res_3777_; 
v_sz_boxed_3775_ = lean_unbox_usize(v_sz_3767_);
lean_dec(v_sz_3767_);
v_i_boxed_3776_ = lean_unbox_usize(v_i_3768_);
lean_dec(v_i_3768_);
v_res_3777_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__3(v_init_3763_, v_p_3764_, v_mvarId_3765_, v_as_3766_, v_sz_boxed_3775_, v_i_boxed_3776_, v_b_3769_, v___y_3770_, v___y_3771_, v___y_3772_, v___y_3773_);
lean_dec(v___y_3773_);
lean_dec_ref(v___y_3772_);
lean_dec(v___y_3771_);
lean_dec_ref(v___y_3770_);
lean_dec_ref(v_as_3766_);
lean_dec_ref(v_init_3763_);
return v_res_3777_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2___boxed(lean_object* v_init_3778_, lean_object* v_p_3779_, lean_object* v_mvarId_3780_, lean_object* v_n_3781_, lean_object* v_b_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_, lean_object* v___y_3785_, lean_object* v___y_3786_, lean_object* v___y_3787_){
_start:
{
lean_object* v_res_3788_; 
v_res_3788_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2(v_init_3778_, v_p_3779_, v_mvarId_3780_, v_n_3781_, v_b_3782_, v___y_3783_, v___y_3784_, v___y_3785_, v___y_3786_);
lean_dec(v___y_3786_);
lean_dec_ref(v___y_3785_);
lean_dec(v___y_3784_);
lean_dec_ref(v___y_3783_);
lean_dec_ref(v_n_3781_);
lean_dec_ref(v_init_3778_);
return v_res_3788_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3_spec__6(lean_object* v_p_3792_, lean_object* v_mvarId_3793_, lean_object* v_as_3794_, size_t v_sz_3795_, size_t v_i_3796_, lean_object* v_b_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_, lean_object* v___y_3800_, lean_object* v___y_3801_){
_start:
{
uint8_t v___x_3803_; 
v___x_3803_ = lean_usize_dec_lt(v_i_3796_, v_sz_3795_);
if (v___x_3803_ == 0)
{
lean_object* v___x_3804_; 
lean_dec(v_mvarId_3793_);
lean_dec_ref(v_p_3792_);
v___x_3804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3804_, 0, v_b_3797_);
return v___x_3804_;
}
else
{
lean_object* v_snd_3805_; lean_object* v___x_3807_; uint8_t v_isShared_3808_; uint8_t v_isSharedCheck_3872_; 
v_snd_3805_ = lean_ctor_get(v_b_3797_, 1);
v_isSharedCheck_3872_ = !lean_is_exclusive(v_b_3797_);
if (v_isSharedCheck_3872_ == 0)
{
lean_object* v_unused_3873_; 
v_unused_3873_ = lean_ctor_get(v_b_3797_, 0);
lean_dec(v_unused_3873_);
v___x_3807_ = v_b_3797_;
v_isShared_3808_ = v_isSharedCheck_3872_;
goto v_resetjp_3806_;
}
else
{
lean_inc(v_snd_3805_);
lean_dec(v_b_3797_);
v___x_3807_ = lean_box(0);
v_isShared_3808_ = v_isSharedCheck_3872_;
goto v_resetjp_3806_;
}
v_resetjp_3806_:
{
lean_object* v___x_3809_; lean_object* v_a_3811_; lean_object* v_a_3818_; 
v___x_3809_ = lean_box(0);
v_a_3818_ = lean_array_uget(v_as_3794_, v_i_3796_);
if (lean_obj_tag(v_a_3818_) == 0)
{
v_a_3811_ = v_snd_3805_;
goto v___jp_3810_;
}
else
{
lean_object* v_val_3819_; lean_object* v___x_3821_; uint8_t v_isShared_3822_; uint8_t v_isSharedCheck_3871_; 
v_val_3819_ = lean_ctor_get(v_a_3818_, 0);
v_isSharedCheck_3871_ = !lean_is_exclusive(v_a_3818_);
if (v_isSharedCheck_3871_ == 0)
{
v___x_3821_ = v_a_3818_;
v_isShared_3822_ = v_isSharedCheck_3871_;
goto v_resetjp_3820_;
}
else
{
lean_inc(v_val_3819_);
lean_dec(v_a_3818_);
v___x_3821_ = lean_box(0);
v_isShared_3822_ = v_isSharedCheck_3871_;
goto v_resetjp_3820_;
}
v_resetjp_3820_:
{
lean_object* v___x_3823_; 
lean_inc_ref(v_p_3792_);
lean_inc(v___y_3801_);
lean_inc_ref(v___y_3800_);
lean_inc(v___y_3799_);
lean_inc_ref(v___y_3798_);
lean_inc(v_val_3819_);
v___x_3823_ = lean_apply_6(v_p_3792_, v_val_3819_, v___y_3798_, v___y_3799_, v___y_3800_, v___y_3801_, lean_box(0));
if (lean_obj_tag(v___x_3823_) == 0)
{
lean_object* v_a_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; uint8_t v___x_3827_; 
v_a_3824_ = lean_ctor_get(v___x_3823_, 0);
lean_inc(v_a_3824_);
lean_dec_ref_known(v___x_3823_, 1);
v___x_3825_ = lean_box(0);
v___x_3826_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3_spec__6___closed__0));
v___x_3827_ = lean_unbox(v_a_3824_);
lean_dec(v_a_3824_);
if (v___x_3827_ == 0)
{
lean_del_object(v___x_3821_);
lean_dec(v_val_3819_);
lean_dec(v_snd_3805_);
v_a_3811_ = v___x_3826_;
goto v___jp_3810_;
}
else
{
lean_object* v___x_3828_; lean_object* v___x_3829_; uint8_t v___x_3830_; lean_object* v___x_3831_; lean_object* v___f_3832_; lean_object* v___x_3833_; 
v___x_3828_ = l_Lean_LocalDecl_fvarId(v_val_3819_);
lean_dec(v_val_3819_);
v___x_3829_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5___closed__1));
v___x_3830_ = 0;
v___x_3831_ = lean_box(v___x_3830_);
lean_inc(v_mvarId_3793_);
v___f_3832_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3___lam__0___boxed), 10, 5);
lean_closure_set(v___f_3832_, 0, v_mvarId_3793_);
lean_closure_set(v___f_3832_, 1, v___x_3828_);
lean_closure_set(v___f_3832_, 2, v___x_3829_);
lean_closure_set(v___f_3832_, 3, v___x_3831_);
lean_closure_set(v___f_3832_, 4, v___x_3809_);
v___x_3833_ = l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1___redArg(v___f_3832_, v___y_3798_, v___y_3799_, v___y_3800_, v___y_3801_);
if (lean_obj_tag(v___x_3833_) == 0)
{
lean_object* v_a_3834_; lean_object* v___x_3836_; uint8_t v_isShared_3837_; uint8_t v_isSharedCheck_3854_; 
v_a_3834_ = lean_ctor_get(v___x_3833_, 0);
v_isSharedCheck_3854_ = !lean_is_exclusive(v___x_3833_);
if (v_isSharedCheck_3854_ == 0)
{
v___x_3836_ = v___x_3833_;
v_isShared_3837_ = v_isSharedCheck_3854_;
goto v_resetjp_3835_;
}
else
{
lean_inc(v_a_3834_);
lean_dec(v___x_3833_);
v___x_3836_ = lean_box(0);
v_isShared_3837_ = v_isSharedCheck_3854_;
goto v_resetjp_3835_;
}
v_resetjp_3835_:
{
if (lean_obj_tag(v_a_3834_) == 0)
{
lean_del_object(v___x_3836_);
lean_del_object(v___x_3821_);
lean_dec(v_snd_3805_);
v_a_3811_ = v___x_3826_;
goto v___jp_3810_;
}
else
{
lean_object* v___x_3839_; 
lean_del_object(v___x_3807_);
lean_dec(v_mvarId_3793_);
lean_dec_ref(v_p_3792_);
lean_inc_ref(v_a_3834_);
if (v_isShared_3822_ == 0)
{
lean_ctor_set(v___x_3821_, 0, v_a_3834_);
v___x_3839_ = v___x_3821_;
goto v_reusejp_3838_;
}
else
{
lean_object* v_reuseFailAlloc_3853_; 
v_reuseFailAlloc_3853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3853_, 0, v_a_3834_);
v___x_3839_ = v_reuseFailAlloc_3853_;
goto v_reusejp_3838_;
}
v_reusejp_3838_:
{
lean_object* v___x_3841_; uint8_t v_isShared_3842_; uint8_t v_isSharedCheck_3851_; 
v_isSharedCheck_3851_ = !lean_is_exclusive(v_a_3834_);
if (v_isSharedCheck_3851_ == 0)
{
lean_object* v_unused_3852_; 
v_unused_3852_ = lean_ctor_get(v_a_3834_, 0);
lean_dec(v_unused_3852_);
v___x_3841_ = v_a_3834_;
v_isShared_3842_ = v_isSharedCheck_3851_;
goto v_resetjp_3840_;
}
else
{
lean_dec(v_a_3834_);
v___x_3841_ = lean_box(0);
v_isShared_3842_ = v_isSharedCheck_3851_;
goto v_resetjp_3840_;
}
v_resetjp_3840_:
{
lean_object* v___x_3843_; lean_object* v___x_3845_; 
v___x_3843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3843_, 0, v___x_3839_);
lean_ctor_set(v___x_3843_, 1, v___x_3825_);
if (v_isShared_3842_ == 0)
{
lean_ctor_set(v___x_3841_, 0, v___x_3843_);
v___x_3845_ = v___x_3841_;
goto v_reusejp_3844_;
}
else
{
lean_object* v_reuseFailAlloc_3850_; 
v_reuseFailAlloc_3850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3850_, 0, v___x_3843_);
v___x_3845_ = v_reuseFailAlloc_3850_;
goto v_reusejp_3844_;
}
v_reusejp_3844_:
{
lean_object* v___x_3846_; lean_object* v___x_3848_; 
v___x_3846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3846_, 0, v___x_3845_);
lean_ctor_set(v___x_3846_, 1, v_snd_3805_);
if (v_isShared_3837_ == 0)
{
lean_ctor_set(v___x_3836_, 0, v___x_3846_);
v___x_3848_ = v___x_3836_;
goto v_reusejp_3847_;
}
else
{
lean_object* v_reuseFailAlloc_3849_; 
v_reuseFailAlloc_3849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3849_, 0, v___x_3846_);
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
}
}
else
{
lean_object* v_a_3855_; lean_object* v___x_3857_; uint8_t v_isShared_3858_; uint8_t v_isSharedCheck_3862_; 
lean_del_object(v___x_3821_);
lean_del_object(v___x_3807_);
lean_dec(v_snd_3805_);
lean_dec(v_mvarId_3793_);
lean_dec_ref(v_p_3792_);
v_a_3855_ = lean_ctor_get(v___x_3833_, 0);
v_isSharedCheck_3862_ = !lean_is_exclusive(v___x_3833_);
if (v_isSharedCheck_3862_ == 0)
{
v___x_3857_ = v___x_3833_;
v_isShared_3858_ = v_isSharedCheck_3862_;
goto v_resetjp_3856_;
}
else
{
lean_inc(v_a_3855_);
lean_dec(v___x_3833_);
v___x_3857_ = lean_box(0);
v_isShared_3858_ = v_isSharedCheck_3862_;
goto v_resetjp_3856_;
}
v_resetjp_3856_:
{
lean_object* v___x_3860_; 
if (v_isShared_3858_ == 0)
{
v___x_3860_ = v___x_3857_;
goto v_reusejp_3859_;
}
else
{
lean_object* v_reuseFailAlloc_3861_; 
v_reuseFailAlloc_3861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3861_, 0, v_a_3855_);
v___x_3860_ = v_reuseFailAlloc_3861_;
goto v_reusejp_3859_;
}
v_reusejp_3859_:
{
return v___x_3860_;
}
}
}
}
}
else
{
lean_object* v_a_3863_; lean_object* v___x_3865_; uint8_t v_isShared_3866_; uint8_t v_isSharedCheck_3870_; 
lean_del_object(v___x_3821_);
lean_dec(v_val_3819_);
lean_del_object(v___x_3807_);
lean_dec(v_snd_3805_);
lean_dec(v_mvarId_3793_);
lean_dec_ref(v_p_3792_);
v_a_3863_ = lean_ctor_get(v___x_3823_, 0);
v_isSharedCheck_3870_ = !lean_is_exclusive(v___x_3823_);
if (v_isSharedCheck_3870_ == 0)
{
v___x_3865_ = v___x_3823_;
v_isShared_3866_ = v_isSharedCheck_3870_;
goto v_resetjp_3864_;
}
else
{
lean_inc(v_a_3863_);
lean_dec(v___x_3823_);
v___x_3865_ = lean_box(0);
v_isShared_3866_ = v_isSharedCheck_3870_;
goto v_resetjp_3864_;
}
v_resetjp_3864_:
{
lean_object* v___x_3868_; 
if (v_isShared_3866_ == 0)
{
v___x_3868_ = v___x_3865_;
goto v_reusejp_3867_;
}
else
{
lean_object* v_reuseFailAlloc_3869_; 
v_reuseFailAlloc_3869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3869_, 0, v_a_3863_);
v___x_3868_ = v_reuseFailAlloc_3869_;
goto v_reusejp_3867_;
}
v_reusejp_3867_:
{
return v___x_3868_;
}
}
}
}
}
v___jp_3810_:
{
lean_object* v___x_3813_; 
if (v_isShared_3808_ == 0)
{
lean_ctor_set(v___x_3807_, 1, v_a_3811_);
lean_ctor_set(v___x_3807_, 0, v___x_3809_);
v___x_3813_ = v___x_3807_;
goto v_reusejp_3812_;
}
else
{
lean_object* v_reuseFailAlloc_3817_; 
v_reuseFailAlloc_3817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3817_, 0, v___x_3809_);
lean_ctor_set(v_reuseFailAlloc_3817_, 1, v_a_3811_);
v___x_3813_ = v_reuseFailAlloc_3817_;
goto v_reusejp_3812_;
}
v_reusejp_3812_:
{
size_t v___x_3814_; size_t v___x_3815_; 
v___x_3814_ = ((size_t)1ULL);
v___x_3815_ = lean_usize_add(v_i_3796_, v___x_3814_);
v_i_3796_ = v___x_3815_;
v_b_3797_ = v___x_3813_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3_spec__6___boxed(lean_object* v_p_3874_, lean_object* v_mvarId_3875_, lean_object* v_as_3876_, lean_object* v_sz_3877_, lean_object* v_i_3878_, lean_object* v_b_3879_, lean_object* v___y_3880_, lean_object* v___y_3881_, lean_object* v___y_3882_, lean_object* v___y_3883_, lean_object* v___y_3884_){
_start:
{
size_t v_sz_boxed_3885_; size_t v_i_boxed_3886_; lean_object* v_res_3887_; 
v_sz_boxed_3885_ = lean_unbox_usize(v_sz_3877_);
lean_dec(v_sz_3877_);
v_i_boxed_3886_ = lean_unbox_usize(v_i_3878_);
lean_dec(v_i_3878_);
v_res_3887_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3_spec__6(v_p_3874_, v_mvarId_3875_, v_as_3876_, v_sz_boxed_3885_, v_i_boxed_3886_, v_b_3879_, v___y_3880_, v___y_3881_, v___y_3882_, v___y_3883_);
lean_dec(v___y_3883_);
lean_dec_ref(v___y_3882_);
lean_dec(v___y_3881_);
lean_dec_ref(v___y_3880_);
lean_dec_ref(v_as_3876_);
return v_res_3887_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3(lean_object* v_p_3888_, lean_object* v_mvarId_3889_, lean_object* v_as_3890_, size_t v_sz_3891_, size_t v_i_3892_, lean_object* v_b_3893_, lean_object* v___y_3894_, lean_object* v___y_3895_, lean_object* v___y_3896_, lean_object* v___y_3897_){
_start:
{
uint8_t v___x_3899_; 
v___x_3899_ = lean_usize_dec_lt(v_i_3892_, v_sz_3891_);
if (v___x_3899_ == 0)
{
lean_object* v___x_3900_; 
lean_dec(v_mvarId_3889_);
lean_dec_ref(v_p_3888_);
v___x_3900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3900_, 0, v_b_3893_);
return v___x_3900_;
}
else
{
lean_object* v_snd_3901_; lean_object* v___x_3903_; uint8_t v_isShared_3904_; uint8_t v_isSharedCheck_3968_; 
v_snd_3901_ = lean_ctor_get(v_b_3893_, 1);
v_isSharedCheck_3968_ = !lean_is_exclusive(v_b_3893_);
if (v_isSharedCheck_3968_ == 0)
{
lean_object* v_unused_3969_; 
v_unused_3969_ = lean_ctor_get(v_b_3893_, 0);
lean_dec(v_unused_3969_);
v___x_3903_ = v_b_3893_;
v_isShared_3904_ = v_isSharedCheck_3968_;
goto v_resetjp_3902_;
}
else
{
lean_inc(v_snd_3901_);
lean_dec(v_b_3893_);
v___x_3903_ = lean_box(0);
v_isShared_3904_ = v_isSharedCheck_3968_;
goto v_resetjp_3902_;
}
v_resetjp_3902_:
{
lean_object* v___x_3905_; lean_object* v_a_3907_; lean_object* v_a_3914_; 
v___x_3905_ = lean_box(0);
v_a_3914_ = lean_array_uget(v_as_3890_, v_i_3892_);
if (lean_obj_tag(v_a_3914_) == 0)
{
v_a_3907_ = v_snd_3901_;
goto v___jp_3906_;
}
else
{
lean_object* v_val_3915_; lean_object* v___x_3917_; uint8_t v_isShared_3918_; uint8_t v_isSharedCheck_3967_; 
v_val_3915_ = lean_ctor_get(v_a_3914_, 0);
v_isSharedCheck_3967_ = !lean_is_exclusive(v_a_3914_);
if (v_isSharedCheck_3967_ == 0)
{
v___x_3917_ = v_a_3914_;
v_isShared_3918_ = v_isSharedCheck_3967_;
goto v_resetjp_3916_;
}
else
{
lean_inc(v_val_3915_);
lean_dec(v_a_3914_);
v___x_3917_ = lean_box(0);
v_isShared_3918_ = v_isSharedCheck_3967_;
goto v_resetjp_3916_;
}
v_resetjp_3916_:
{
lean_object* v___x_3919_; 
lean_inc_ref(v_p_3888_);
lean_inc(v___y_3897_);
lean_inc_ref(v___y_3896_);
lean_inc(v___y_3895_);
lean_inc_ref(v___y_3894_);
lean_inc(v_val_3915_);
v___x_3919_ = lean_apply_6(v_p_3888_, v_val_3915_, v___y_3894_, v___y_3895_, v___y_3896_, v___y_3897_, lean_box(0));
if (lean_obj_tag(v___x_3919_) == 0)
{
lean_object* v_a_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; uint8_t v___x_3923_; 
v_a_3920_ = lean_ctor_get(v___x_3919_, 0);
lean_inc(v_a_3920_);
lean_dec_ref_known(v___x_3919_, 1);
v___x_3921_ = lean_box(0);
v___x_3922_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3_spec__6___closed__0));
v___x_3923_ = lean_unbox(v_a_3920_);
lean_dec(v_a_3920_);
if (v___x_3923_ == 0)
{
lean_del_object(v___x_3917_);
lean_dec(v_val_3915_);
lean_dec(v_snd_3901_);
v_a_3907_ = v___x_3922_;
goto v___jp_3906_;
}
else
{
lean_object* v___x_3924_; lean_object* v___x_3925_; uint8_t v___x_3926_; lean_object* v___x_3927_; lean_object* v___f_3928_; lean_object* v___x_3929_; 
v___x_3924_ = l_Lean_LocalDecl_fvarId(v_val_3915_);
lean_dec(v_val_3915_);
v___x_3925_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5___closed__1));
v___x_3926_ = 0;
v___x_3927_ = lean_box(v___x_3926_);
lean_inc(v_mvarId_3889_);
v___f_3928_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3___lam__0___boxed), 10, 5);
lean_closure_set(v___f_3928_, 0, v_mvarId_3889_);
lean_closure_set(v___f_3928_, 1, v___x_3924_);
lean_closure_set(v___f_3928_, 2, v___x_3925_);
lean_closure_set(v___f_3928_, 3, v___x_3927_);
lean_closure_set(v___f_3928_, 4, v___x_3905_);
v___x_3929_ = l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1___redArg(v___f_3928_, v___y_3894_, v___y_3895_, v___y_3896_, v___y_3897_);
if (lean_obj_tag(v___x_3929_) == 0)
{
lean_object* v_a_3930_; lean_object* v___x_3932_; uint8_t v_isShared_3933_; uint8_t v_isSharedCheck_3950_; 
v_a_3930_ = lean_ctor_get(v___x_3929_, 0);
v_isSharedCheck_3950_ = !lean_is_exclusive(v___x_3929_);
if (v_isSharedCheck_3950_ == 0)
{
v___x_3932_ = v___x_3929_;
v_isShared_3933_ = v_isSharedCheck_3950_;
goto v_resetjp_3931_;
}
else
{
lean_inc(v_a_3930_);
lean_dec(v___x_3929_);
v___x_3932_ = lean_box(0);
v_isShared_3933_ = v_isSharedCheck_3950_;
goto v_resetjp_3931_;
}
v_resetjp_3931_:
{
if (lean_obj_tag(v_a_3930_) == 0)
{
lean_del_object(v___x_3932_);
lean_del_object(v___x_3917_);
lean_dec(v_snd_3901_);
v_a_3907_ = v___x_3922_;
goto v___jp_3906_;
}
else
{
lean_object* v___x_3935_; 
lean_del_object(v___x_3903_);
lean_dec(v_mvarId_3889_);
lean_dec_ref(v_p_3888_);
lean_inc_ref(v_a_3930_);
if (v_isShared_3918_ == 0)
{
lean_ctor_set(v___x_3917_, 0, v_a_3930_);
v___x_3935_ = v___x_3917_;
goto v_reusejp_3934_;
}
else
{
lean_object* v_reuseFailAlloc_3949_; 
v_reuseFailAlloc_3949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3949_, 0, v_a_3930_);
v___x_3935_ = v_reuseFailAlloc_3949_;
goto v_reusejp_3934_;
}
v_reusejp_3934_:
{
lean_object* v___x_3937_; uint8_t v_isShared_3938_; uint8_t v_isSharedCheck_3947_; 
v_isSharedCheck_3947_ = !lean_is_exclusive(v_a_3930_);
if (v_isSharedCheck_3947_ == 0)
{
lean_object* v_unused_3948_; 
v_unused_3948_ = lean_ctor_get(v_a_3930_, 0);
lean_dec(v_unused_3948_);
v___x_3937_ = v_a_3930_;
v_isShared_3938_ = v_isSharedCheck_3947_;
goto v_resetjp_3936_;
}
else
{
lean_dec(v_a_3930_);
v___x_3937_ = lean_box(0);
v_isShared_3938_ = v_isSharedCheck_3947_;
goto v_resetjp_3936_;
}
v_resetjp_3936_:
{
lean_object* v___x_3939_; lean_object* v___x_3941_; 
v___x_3939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3939_, 0, v___x_3935_);
lean_ctor_set(v___x_3939_, 1, v___x_3921_);
if (v_isShared_3938_ == 0)
{
lean_ctor_set(v___x_3937_, 0, v___x_3939_);
v___x_3941_ = v___x_3937_;
goto v_reusejp_3940_;
}
else
{
lean_object* v_reuseFailAlloc_3946_; 
v_reuseFailAlloc_3946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3946_, 0, v___x_3939_);
v___x_3941_ = v_reuseFailAlloc_3946_;
goto v_reusejp_3940_;
}
v_reusejp_3940_:
{
lean_object* v___x_3942_; lean_object* v___x_3944_; 
v___x_3942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3942_, 0, v___x_3941_);
lean_ctor_set(v___x_3942_, 1, v_snd_3901_);
if (v_isShared_3933_ == 0)
{
lean_ctor_set(v___x_3932_, 0, v___x_3942_);
v___x_3944_ = v___x_3932_;
goto v_reusejp_3943_;
}
else
{
lean_object* v_reuseFailAlloc_3945_; 
v_reuseFailAlloc_3945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3945_, 0, v___x_3942_);
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
}
}
else
{
lean_object* v_a_3951_; lean_object* v___x_3953_; uint8_t v_isShared_3954_; uint8_t v_isSharedCheck_3958_; 
lean_del_object(v___x_3917_);
lean_del_object(v___x_3903_);
lean_dec(v_snd_3901_);
lean_dec(v_mvarId_3889_);
lean_dec_ref(v_p_3888_);
v_a_3951_ = lean_ctor_get(v___x_3929_, 0);
v_isSharedCheck_3958_ = !lean_is_exclusive(v___x_3929_);
if (v_isSharedCheck_3958_ == 0)
{
v___x_3953_ = v___x_3929_;
v_isShared_3954_ = v_isSharedCheck_3958_;
goto v_resetjp_3952_;
}
else
{
lean_inc(v_a_3951_);
lean_dec(v___x_3929_);
v___x_3953_ = lean_box(0);
v_isShared_3954_ = v_isSharedCheck_3958_;
goto v_resetjp_3952_;
}
v_resetjp_3952_:
{
lean_object* v___x_3956_; 
if (v_isShared_3954_ == 0)
{
v___x_3956_ = v___x_3953_;
goto v_reusejp_3955_;
}
else
{
lean_object* v_reuseFailAlloc_3957_; 
v_reuseFailAlloc_3957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3957_, 0, v_a_3951_);
v___x_3956_ = v_reuseFailAlloc_3957_;
goto v_reusejp_3955_;
}
v_reusejp_3955_:
{
return v___x_3956_;
}
}
}
}
}
else
{
lean_object* v_a_3959_; lean_object* v___x_3961_; uint8_t v_isShared_3962_; uint8_t v_isSharedCheck_3966_; 
lean_del_object(v___x_3917_);
lean_dec(v_val_3915_);
lean_del_object(v___x_3903_);
lean_dec(v_snd_3901_);
lean_dec(v_mvarId_3889_);
lean_dec_ref(v_p_3888_);
v_a_3959_ = lean_ctor_get(v___x_3919_, 0);
v_isSharedCheck_3966_ = !lean_is_exclusive(v___x_3919_);
if (v_isSharedCheck_3966_ == 0)
{
v___x_3961_ = v___x_3919_;
v_isShared_3962_ = v_isSharedCheck_3966_;
goto v_resetjp_3960_;
}
else
{
lean_inc(v_a_3959_);
lean_dec(v___x_3919_);
v___x_3961_ = lean_box(0);
v_isShared_3962_ = v_isSharedCheck_3966_;
goto v_resetjp_3960_;
}
v_resetjp_3960_:
{
lean_object* v___x_3964_; 
if (v_isShared_3962_ == 0)
{
v___x_3964_ = v___x_3961_;
goto v_reusejp_3963_;
}
else
{
lean_object* v_reuseFailAlloc_3965_; 
v_reuseFailAlloc_3965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3965_, 0, v_a_3959_);
v___x_3964_ = v_reuseFailAlloc_3965_;
goto v_reusejp_3963_;
}
v_reusejp_3963_:
{
return v___x_3964_;
}
}
}
}
}
v___jp_3906_:
{
lean_object* v___x_3909_; 
if (v_isShared_3904_ == 0)
{
lean_ctor_set(v___x_3903_, 1, v_a_3907_);
lean_ctor_set(v___x_3903_, 0, v___x_3905_);
v___x_3909_ = v___x_3903_;
goto v_reusejp_3908_;
}
else
{
lean_object* v_reuseFailAlloc_3913_; 
v_reuseFailAlloc_3913_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3913_, 0, v___x_3905_);
lean_ctor_set(v_reuseFailAlloc_3913_, 1, v_a_3907_);
v___x_3909_ = v_reuseFailAlloc_3913_;
goto v_reusejp_3908_;
}
v_reusejp_3908_:
{
size_t v___x_3910_; size_t v___x_3911_; lean_object* v___x_3912_; 
v___x_3910_ = ((size_t)1ULL);
v___x_3911_ = lean_usize_add(v_i_3892_, v___x_3910_);
v___x_3912_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3_spec__6(v_p_3888_, v_mvarId_3889_, v_as_3890_, v_sz_3891_, v___x_3911_, v___x_3909_, v___y_3894_, v___y_3895_, v___y_3896_, v___y_3897_);
return v___x_3912_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3___boxed(lean_object* v_p_3970_, lean_object* v_mvarId_3971_, lean_object* v_as_3972_, lean_object* v_sz_3973_, lean_object* v_i_3974_, lean_object* v_b_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_, lean_object* v___y_3978_, lean_object* v___y_3979_, lean_object* v___y_3980_){
_start:
{
size_t v_sz_boxed_3981_; size_t v_i_boxed_3982_; lean_object* v_res_3983_; 
v_sz_boxed_3981_ = lean_unbox_usize(v_sz_3973_);
lean_dec(v_sz_3973_);
v_i_boxed_3982_ = lean_unbox_usize(v_i_3974_);
lean_dec(v_i_3974_);
v_res_3983_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3(v_p_3970_, v_mvarId_3971_, v_as_3972_, v_sz_boxed_3981_, v_i_boxed_3982_, v_b_3975_, v___y_3976_, v___y_3977_, v___y_3978_, v___y_3979_);
lean_dec(v___y_3979_);
lean_dec_ref(v___y_3978_);
lean_dec(v___y_3977_);
lean_dec_ref(v___y_3976_);
lean_dec_ref(v_as_3972_);
return v_res_3983_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2(lean_object* v_p_3984_, lean_object* v_mvarId_3985_, lean_object* v_t_3986_, lean_object* v_init_3987_, lean_object* v___y_3988_, lean_object* v___y_3989_, lean_object* v___y_3990_, lean_object* v___y_3991_){
_start:
{
lean_object* v_root_3993_; lean_object* v_tail_3994_; lean_object* v___x_3995_; 
v_root_3993_ = lean_ctor_get(v_t_3986_, 0);
v_tail_3994_ = lean_ctor_get(v_t_3986_, 1);
lean_inc(v_mvarId_3985_);
lean_inc_ref(v_p_3984_);
lean_inc_ref(v_init_3987_);
v___x_3995_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2(v_init_3987_, v_p_3984_, v_mvarId_3985_, v_root_3993_, v_init_3987_, v___y_3988_, v___y_3989_, v___y_3990_, v___y_3991_);
lean_dec_ref(v_init_3987_);
if (lean_obj_tag(v___x_3995_) == 0)
{
lean_object* v_a_3996_; lean_object* v___x_3998_; uint8_t v_isShared_3999_; uint8_t v_isSharedCheck_4032_; 
v_a_3996_ = lean_ctor_get(v___x_3995_, 0);
v_isSharedCheck_4032_ = !lean_is_exclusive(v___x_3995_);
if (v_isSharedCheck_4032_ == 0)
{
v___x_3998_ = v___x_3995_;
v_isShared_3999_ = v_isSharedCheck_4032_;
goto v_resetjp_3997_;
}
else
{
lean_inc(v_a_3996_);
lean_dec(v___x_3995_);
v___x_3998_ = lean_box(0);
v_isShared_3999_ = v_isSharedCheck_4032_;
goto v_resetjp_3997_;
}
v_resetjp_3997_:
{
if (lean_obj_tag(v_a_3996_) == 0)
{
lean_object* v_a_4000_; lean_object* v___x_4002_; 
lean_dec(v_mvarId_3985_);
lean_dec_ref(v_p_3984_);
v_a_4000_ = lean_ctor_get(v_a_3996_, 0);
lean_inc(v_a_4000_);
lean_dec_ref_known(v_a_3996_, 1);
if (v_isShared_3999_ == 0)
{
lean_ctor_set(v___x_3998_, 0, v_a_4000_);
v___x_4002_ = v___x_3998_;
goto v_reusejp_4001_;
}
else
{
lean_object* v_reuseFailAlloc_4003_; 
v_reuseFailAlloc_4003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4003_, 0, v_a_4000_);
v___x_4002_ = v_reuseFailAlloc_4003_;
goto v_reusejp_4001_;
}
v_reusejp_4001_:
{
return v___x_4002_;
}
}
else
{
lean_object* v_a_4004_; lean_object* v___x_4005_; lean_object* v___x_4006_; size_t v_sz_4007_; size_t v___x_4008_; lean_object* v___x_4009_; 
lean_del_object(v___x_3998_);
v_a_4004_ = lean_ctor_get(v_a_3996_, 0);
lean_inc(v_a_4004_);
lean_dec_ref_known(v_a_3996_, 1);
v___x_4005_ = lean_box(0);
v___x_4006_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4006_, 0, v___x_4005_);
lean_ctor_set(v___x_4006_, 1, v_a_4004_);
v_sz_4007_ = lean_array_size(v_tail_3994_);
v___x_4008_ = ((size_t)0ULL);
v___x_4009_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3(v_p_3984_, v_mvarId_3985_, v_tail_3994_, v_sz_4007_, v___x_4008_, v___x_4006_, v___y_3988_, v___y_3989_, v___y_3990_, v___y_3991_);
if (lean_obj_tag(v___x_4009_) == 0)
{
lean_object* v_a_4010_; lean_object* v___x_4012_; uint8_t v_isShared_4013_; uint8_t v_isSharedCheck_4023_; 
v_a_4010_ = lean_ctor_get(v___x_4009_, 0);
v_isSharedCheck_4023_ = !lean_is_exclusive(v___x_4009_);
if (v_isSharedCheck_4023_ == 0)
{
v___x_4012_ = v___x_4009_;
v_isShared_4013_ = v_isSharedCheck_4023_;
goto v_resetjp_4011_;
}
else
{
lean_inc(v_a_4010_);
lean_dec(v___x_4009_);
v___x_4012_ = lean_box(0);
v_isShared_4013_ = v_isSharedCheck_4023_;
goto v_resetjp_4011_;
}
v_resetjp_4011_:
{
lean_object* v_fst_4014_; 
v_fst_4014_ = lean_ctor_get(v_a_4010_, 0);
if (lean_obj_tag(v_fst_4014_) == 0)
{
lean_object* v_snd_4015_; lean_object* v___x_4017_; 
v_snd_4015_ = lean_ctor_get(v_a_4010_, 1);
lean_inc(v_snd_4015_);
lean_dec(v_a_4010_);
if (v_isShared_4013_ == 0)
{
lean_ctor_set(v___x_4012_, 0, v_snd_4015_);
v___x_4017_ = v___x_4012_;
goto v_reusejp_4016_;
}
else
{
lean_object* v_reuseFailAlloc_4018_; 
v_reuseFailAlloc_4018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4018_, 0, v_snd_4015_);
v___x_4017_ = v_reuseFailAlloc_4018_;
goto v_reusejp_4016_;
}
v_reusejp_4016_:
{
return v___x_4017_;
}
}
else
{
lean_object* v_val_4019_; lean_object* v___x_4021_; 
lean_inc_ref(v_fst_4014_);
lean_dec(v_a_4010_);
v_val_4019_ = lean_ctor_get(v_fst_4014_, 0);
lean_inc(v_val_4019_);
lean_dec_ref_known(v_fst_4014_, 1);
if (v_isShared_4013_ == 0)
{
lean_ctor_set(v___x_4012_, 0, v_val_4019_);
v___x_4021_ = v___x_4012_;
goto v_reusejp_4020_;
}
else
{
lean_object* v_reuseFailAlloc_4022_; 
v_reuseFailAlloc_4022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4022_, 0, v_val_4019_);
v___x_4021_ = v_reuseFailAlloc_4022_;
goto v_reusejp_4020_;
}
v_reusejp_4020_:
{
return v___x_4021_;
}
}
}
}
else
{
lean_object* v_a_4024_; lean_object* v___x_4026_; uint8_t v_isShared_4027_; uint8_t v_isSharedCheck_4031_; 
v_a_4024_ = lean_ctor_get(v___x_4009_, 0);
v_isSharedCheck_4031_ = !lean_is_exclusive(v___x_4009_);
if (v_isSharedCheck_4031_ == 0)
{
v___x_4026_ = v___x_4009_;
v_isShared_4027_ = v_isSharedCheck_4031_;
goto v_resetjp_4025_;
}
else
{
lean_inc(v_a_4024_);
lean_dec(v___x_4009_);
v___x_4026_ = lean_box(0);
v_isShared_4027_ = v_isSharedCheck_4031_;
goto v_resetjp_4025_;
}
v_resetjp_4025_:
{
lean_object* v___x_4029_; 
if (v_isShared_4027_ == 0)
{
v___x_4029_ = v___x_4026_;
goto v_reusejp_4028_;
}
else
{
lean_object* v_reuseFailAlloc_4030_; 
v_reuseFailAlloc_4030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4030_, 0, v_a_4024_);
v___x_4029_ = v_reuseFailAlloc_4030_;
goto v_reusejp_4028_;
}
v_reusejp_4028_:
{
return v___x_4029_;
}
}
}
}
}
}
else
{
lean_object* v_a_4033_; lean_object* v___x_4035_; uint8_t v_isShared_4036_; uint8_t v_isSharedCheck_4040_; 
lean_dec(v_mvarId_3985_);
lean_dec_ref(v_p_3984_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2___boxed(lean_object* v_p_4041_, lean_object* v_mvarId_4042_, lean_object* v_t_4043_, lean_object* v_init_4044_, lean_object* v___y_4045_, lean_object* v___y_4046_, lean_object* v___y_4047_, lean_object* v___y_4048_, lean_object* v___y_4049_){
_start:
{
lean_object* v_res_4050_; 
v_res_4050_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2(v_p_4041_, v_mvarId_4042_, v_t_4043_, v_init_4044_, v___y_4045_, v___y_4046_, v___y_4047_, v___y_4048_);
lean_dec(v___y_4048_);
lean_dec_ref(v___y_4047_);
lean_dec(v___y_4046_);
lean_dec_ref(v___y_4045_);
lean_dec_ref(v_t_4043_);
return v_res_4050_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesRec___lam__0(lean_object* v_p_4054_, lean_object* v_mvarId_4055_, lean_object* v___y_4056_, lean_object* v___y_4057_, lean_object* v___y_4058_, lean_object* v___y_4059_){
_start:
{
lean_object* v_lctx_4061_; lean_object* v_decls_4062_; lean_object* v___x_4063_; lean_object* v___x_4064_; lean_object* v___x_4065_; 
v_lctx_4061_ = lean_ctor_get(v___y_4056_, 2);
v_decls_4062_ = lean_ctor_get(v_lctx_4061_, 1);
v___x_4063_ = lean_box(0);
v___x_4064_ = ((lean_object*)(l_Lean_MVarId_casesRec___lam__0___closed__0));
v___x_4065_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2(v_p_4054_, v_mvarId_4055_, v_decls_4062_, v___x_4064_, v___y_4056_, v___y_4057_, v___y_4058_, v___y_4059_);
if (lean_obj_tag(v___x_4065_) == 0)
{
lean_object* v_a_4066_; lean_object* v___x_4068_; uint8_t v_isShared_4069_; uint8_t v_isSharedCheck_4078_; 
v_a_4066_ = lean_ctor_get(v___x_4065_, 0);
v_isSharedCheck_4078_ = !lean_is_exclusive(v___x_4065_);
if (v_isSharedCheck_4078_ == 0)
{
v___x_4068_ = v___x_4065_;
v_isShared_4069_ = v_isSharedCheck_4078_;
goto v_resetjp_4067_;
}
else
{
lean_inc(v_a_4066_);
lean_dec(v___x_4065_);
v___x_4068_ = lean_box(0);
v_isShared_4069_ = v_isSharedCheck_4078_;
goto v_resetjp_4067_;
}
v_resetjp_4067_:
{
lean_object* v_fst_4070_; 
v_fst_4070_ = lean_ctor_get(v_a_4066_, 0);
lean_inc(v_fst_4070_);
lean_dec(v_a_4066_);
if (lean_obj_tag(v_fst_4070_) == 0)
{
lean_object* v___x_4072_; 
if (v_isShared_4069_ == 0)
{
lean_ctor_set(v___x_4068_, 0, v___x_4063_);
v___x_4072_ = v___x_4068_;
goto v_reusejp_4071_;
}
else
{
lean_object* v_reuseFailAlloc_4073_; 
v_reuseFailAlloc_4073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4073_, 0, v___x_4063_);
v___x_4072_ = v_reuseFailAlloc_4073_;
goto v_reusejp_4071_;
}
v_reusejp_4071_:
{
return v___x_4072_;
}
}
else
{
lean_object* v_val_4074_; lean_object* v___x_4076_; 
v_val_4074_ = lean_ctor_get(v_fst_4070_, 0);
lean_inc(v_val_4074_);
lean_dec_ref_known(v_fst_4070_, 1);
if (v_isShared_4069_ == 0)
{
lean_ctor_set(v___x_4068_, 0, v_val_4074_);
v___x_4076_ = v___x_4068_;
goto v_reusejp_4075_;
}
else
{
lean_object* v_reuseFailAlloc_4077_; 
v_reuseFailAlloc_4077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4077_, 0, v_val_4074_);
v___x_4076_ = v_reuseFailAlloc_4077_;
goto v_reusejp_4075_;
}
v_reusejp_4075_:
{
return v___x_4076_;
}
}
}
}
else
{
lean_object* v_a_4079_; lean_object* v___x_4081_; uint8_t v_isShared_4082_; uint8_t v_isSharedCheck_4086_; 
v_a_4079_ = lean_ctor_get(v___x_4065_, 0);
v_isSharedCheck_4086_ = !lean_is_exclusive(v___x_4065_);
if (v_isSharedCheck_4086_ == 0)
{
v___x_4081_ = v___x_4065_;
v_isShared_4082_ = v_isSharedCheck_4086_;
goto v_resetjp_4080_;
}
else
{
lean_inc(v_a_4079_);
lean_dec(v___x_4065_);
v___x_4081_ = lean_box(0);
v_isShared_4082_ = v_isSharedCheck_4086_;
goto v_resetjp_4080_;
}
v_resetjp_4080_:
{
lean_object* v___x_4084_; 
if (v_isShared_4082_ == 0)
{
v___x_4084_ = v___x_4081_;
goto v_reusejp_4083_;
}
else
{
lean_object* v_reuseFailAlloc_4085_; 
v_reuseFailAlloc_4085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4085_, 0, v_a_4079_);
v___x_4084_ = v_reuseFailAlloc_4085_;
goto v_reusejp_4083_;
}
v_reusejp_4083_:
{
return v___x_4084_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesRec___lam__0___boxed(lean_object* v_p_4087_, lean_object* v_mvarId_4088_, lean_object* v___y_4089_, lean_object* v___y_4090_, lean_object* v___y_4091_, lean_object* v___y_4092_, lean_object* v___y_4093_){
_start:
{
lean_object* v_res_4094_; 
v_res_4094_ = l_Lean_MVarId_casesRec___lam__0(v_p_4087_, v_mvarId_4088_, v___y_4089_, v___y_4090_, v___y_4091_, v___y_4092_);
lean_dec(v___y_4092_);
lean_dec_ref(v___y_4091_);
lean_dec(v___y_4090_);
lean_dec_ref(v___y_4089_);
return v_res_4094_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesRec___lam__1(lean_object* v_p_4095_, lean_object* v_mvarId_4096_, lean_object* v___y_4097_, lean_object* v___y_4098_, lean_object* v___y_4099_, lean_object* v___y_4100_){
_start:
{
lean_object* v___f_4102_; lean_object* v___x_4103_; 
lean_inc(v_mvarId_4096_);
v___f_4102_ = lean_alloc_closure((void*)(l_Lean_MVarId_casesRec___lam__0___boxed), 7, 2);
lean_closure_set(v___f_4102_, 0, v_p_4095_);
lean_closure_set(v___f_4102_, 1, v_mvarId_4096_);
v___x_4103_ = l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2___redArg(v_mvarId_4096_, v___f_4102_, v___y_4097_, v___y_4098_, v___y_4099_, v___y_4100_);
return v___x_4103_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesRec___lam__1___boxed(lean_object* v_p_4104_, lean_object* v_mvarId_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_, lean_object* v___y_4110_){
_start:
{
lean_object* v_res_4111_; 
v_res_4111_ = l_Lean_MVarId_casesRec___lam__1(v_p_4104_, v_mvarId_4105_, v___y_4106_, v___y_4107_, v___y_4108_, v___y_4109_);
lean_dec(v___y_4109_);
lean_dec_ref(v___y_4108_);
lean_dec(v___y_4107_);
lean_dec_ref(v___y_4106_);
return v_res_4111_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesRec(lean_object* v_mvarId_4112_, lean_object* v_p_4113_, lean_object* v_a_4114_, lean_object* v_a_4115_, lean_object* v_a_4116_, lean_object* v_a_4117_){
_start:
{
lean_object* v___f_4119_; lean_object* v___x_4120_; 
v___f_4119_ = lean_alloc_closure((void*)(l_Lean_MVarId_casesRec___lam__1___boxed), 7, 1);
lean_closure_set(v___f_4119_, 0, v_p_4113_);
v___x_4120_ = l_Lean_Meta_saturate(v_mvarId_4112_, v___f_4119_, v_a_4114_, v_a_4115_, v_a_4116_, v_a_4117_);
return v___x_4120_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesRec___boxed(lean_object* v_mvarId_4121_, lean_object* v_p_4122_, lean_object* v_a_4123_, lean_object* v_a_4124_, lean_object* v_a_4125_, lean_object* v_a_4126_, lean_object* v_a_4127_){
_start:
{
lean_object* v_res_4128_; 
v_res_4128_ = l_Lean_MVarId_casesRec(v_mvarId_4121_, v_p_4122_, v_a_4123_, v_a_4124_, v_a_4125_, v_a_4126_);
lean_dec(v_a_4126_);
lean_dec_ref(v_a_4125_);
lean_dec(v_a_4124_);
lean_dec_ref(v_a_4123_);
return v_res_4128_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0___redArg(lean_object* v_e_4129_, lean_object* v___y_4130_){
_start:
{
uint8_t v___x_4132_; uint8_t v___x_4133_; 
v___x_4132_ = l_Lean_Expr_hasMVar(v_e_4129_);
v___x_4133_ = lean_bool_not(v___x_4132_);
if (v___x_4133_ == 0)
{
lean_object* v___x_4134_; lean_object* v_mctx_4135_; lean_object* v___x_4136_; lean_object* v_fst_4137_; lean_object* v_snd_4138_; lean_object* v___x_4139_; lean_object* v_cache_4140_; lean_object* v_zetaDeltaFVarIds_4141_; lean_object* v_postponed_4142_; lean_object* v_diag_4143_; lean_object* v___x_4145_; uint8_t v_isShared_4146_; uint8_t v_isSharedCheck_4152_; 
v___x_4134_ = lean_st_ref_get(v___y_4130_);
v_mctx_4135_ = lean_ctor_get(v___x_4134_, 0);
lean_inc_ref(v_mctx_4135_);
lean_dec(v___x_4134_);
v___x_4136_ = l_Lean_instantiateMVarsCore(v_mctx_4135_, v_e_4129_);
v_fst_4137_ = lean_ctor_get(v___x_4136_, 0);
lean_inc(v_fst_4137_);
v_snd_4138_ = lean_ctor_get(v___x_4136_, 1);
lean_inc(v_snd_4138_);
lean_dec_ref(v___x_4136_);
v___x_4139_ = lean_st_ref_take(v___y_4130_);
v_cache_4140_ = lean_ctor_get(v___x_4139_, 1);
v_zetaDeltaFVarIds_4141_ = lean_ctor_get(v___x_4139_, 2);
v_postponed_4142_ = lean_ctor_get(v___x_4139_, 3);
v_diag_4143_ = lean_ctor_get(v___x_4139_, 4);
v_isSharedCheck_4152_ = !lean_is_exclusive(v___x_4139_);
if (v_isSharedCheck_4152_ == 0)
{
lean_object* v_unused_4153_; 
v_unused_4153_ = lean_ctor_get(v___x_4139_, 0);
lean_dec(v_unused_4153_);
v___x_4145_ = v___x_4139_;
v_isShared_4146_ = v_isSharedCheck_4152_;
goto v_resetjp_4144_;
}
else
{
lean_inc(v_diag_4143_);
lean_inc(v_postponed_4142_);
lean_inc(v_zetaDeltaFVarIds_4141_);
lean_inc(v_cache_4140_);
lean_dec(v___x_4139_);
v___x_4145_ = lean_box(0);
v_isShared_4146_ = v_isSharedCheck_4152_;
goto v_resetjp_4144_;
}
v_resetjp_4144_:
{
lean_object* v___x_4148_; 
if (v_isShared_4146_ == 0)
{
lean_ctor_set(v___x_4145_, 0, v_snd_4138_);
v___x_4148_ = v___x_4145_;
goto v_reusejp_4147_;
}
else
{
lean_object* v_reuseFailAlloc_4151_; 
v_reuseFailAlloc_4151_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4151_, 0, v_snd_4138_);
lean_ctor_set(v_reuseFailAlloc_4151_, 1, v_cache_4140_);
lean_ctor_set(v_reuseFailAlloc_4151_, 2, v_zetaDeltaFVarIds_4141_);
lean_ctor_set(v_reuseFailAlloc_4151_, 3, v_postponed_4142_);
lean_ctor_set(v_reuseFailAlloc_4151_, 4, v_diag_4143_);
v___x_4148_ = v_reuseFailAlloc_4151_;
goto v_reusejp_4147_;
}
v_reusejp_4147_:
{
lean_object* v___x_4149_; lean_object* v___x_4150_; 
v___x_4149_ = lean_st_ref_set(v___y_4130_, v___x_4148_);
v___x_4150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4150_, 0, v_fst_4137_);
return v___x_4150_;
}
}
}
else
{
lean_object* v___x_4154_; 
v___x_4154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4154_, 0, v_e_4129_);
return v___x_4154_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0___redArg___boxed(lean_object* v_e_4155_, lean_object* v___y_4156_, lean_object* v___y_4157_){
_start:
{
lean_object* v_res_4158_; 
v_res_4158_ = l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0___redArg(v_e_4155_, v___y_4156_);
lean_dec(v___y_4156_);
return v_res_4158_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0(lean_object* v_e_4159_, lean_object* v___y_4160_, lean_object* v___y_4161_, lean_object* v___y_4162_, lean_object* v___y_4163_){
_start:
{
lean_object* v___x_4165_; 
v___x_4165_ = l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0___redArg(v_e_4159_, v___y_4161_);
return v___x_4165_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0___boxed(lean_object* v_e_4166_, lean_object* v___y_4167_, lean_object* v___y_4168_, lean_object* v___y_4169_, lean_object* v___y_4170_, lean_object* v___y_4171_){
_start:
{
lean_object* v_res_4172_; 
v_res_4172_ = l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0(v_e_4166_, v___y_4167_, v___y_4168_, v___y_4169_, v___y_4170_);
lean_dec(v___y_4170_);
lean_dec_ref(v___y_4169_);
lean_dec(v___y_4168_);
lean_dec_ref(v___y_4167_);
return v_res_4172_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesAnd___lam__0(lean_object* v_localDecl_4176_, lean_object* v___y_4177_, lean_object* v___y_4178_, lean_object* v___y_4179_, lean_object* v___y_4180_){
_start:
{
lean_object* v___x_4182_; lean_object* v___x_4183_; lean_object* v_a_4184_; lean_object* v___x_4186_; uint8_t v_isShared_4187_; uint8_t v_isSharedCheck_4195_; 
v___x_4182_ = l_Lean_LocalDecl_type(v_localDecl_4176_);
v___x_4183_ = l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0___redArg(v___x_4182_, v___y_4178_);
v_a_4184_ = lean_ctor_get(v___x_4183_, 0);
v_isSharedCheck_4195_ = !lean_is_exclusive(v___x_4183_);
if (v_isSharedCheck_4195_ == 0)
{
v___x_4186_ = v___x_4183_;
v_isShared_4187_ = v_isSharedCheck_4195_;
goto v_resetjp_4185_;
}
else
{
lean_inc(v_a_4184_);
lean_dec(v___x_4183_);
v___x_4186_ = lean_box(0);
v_isShared_4187_ = v_isSharedCheck_4195_;
goto v_resetjp_4185_;
}
v_resetjp_4185_:
{
lean_object* v___x_4188_; lean_object* v___x_4189_; uint8_t v___x_4190_; lean_object* v___x_4191_; lean_object* v___x_4193_; 
v___x_4188_ = ((lean_object*)(l_Lean_MVarId_casesAnd___lam__0___closed__1));
v___x_4189_ = lean_unsigned_to_nat(2u);
v___x_4190_ = l_Lean_Expr_isAppOfArity(v_a_4184_, v___x_4188_, v___x_4189_);
lean_dec(v_a_4184_);
v___x_4191_ = lean_box(v___x_4190_);
if (v_isShared_4187_ == 0)
{
lean_ctor_set(v___x_4186_, 0, v___x_4191_);
v___x_4193_ = v___x_4186_;
goto v_reusejp_4192_;
}
else
{
lean_object* v_reuseFailAlloc_4194_; 
v_reuseFailAlloc_4194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4194_, 0, v___x_4191_);
v___x_4193_ = v_reuseFailAlloc_4194_;
goto v_reusejp_4192_;
}
v_reusejp_4192_:
{
return v___x_4193_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesAnd___lam__0___boxed(lean_object* v_localDecl_4196_, lean_object* v___y_4197_, lean_object* v___y_4198_, lean_object* v___y_4199_, lean_object* v___y_4200_, lean_object* v___y_4201_){
_start:
{
lean_object* v_res_4202_; 
v_res_4202_ = l_Lean_MVarId_casesAnd___lam__0(v_localDecl_4196_, v___y_4197_, v___y_4198_, v___y_4199_, v___y_4200_);
lean_dec(v___y_4200_);
lean_dec_ref(v___y_4199_);
lean_dec(v___y_4198_);
lean_dec_ref(v___y_4197_);
lean_dec_ref(v_localDecl_4196_);
return v_res_4202_;
}
}
static lean_object* _init_l_Lean_MVarId_casesAnd___closed__3(void){
_start:
{
lean_object* v___x_4207_; lean_object* v___x_4208_; 
v___x_4207_ = ((lean_object*)(l_Lean_MVarId_casesAnd___closed__2));
v___x_4208_ = l_Lean_MessageData_ofFormat(v___x_4207_);
return v___x_4208_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesAnd(lean_object* v_mvarId_4209_, lean_object* v_a_4210_, lean_object* v_a_4211_, lean_object* v_a_4212_, lean_object* v_a_4213_){
_start:
{
lean_object* v___f_4215_; lean_object* v___x_4216_; 
v___f_4215_ = ((lean_object*)(l_Lean_MVarId_casesAnd___closed__0));
v___x_4216_ = l_Lean_MVarId_casesRec(v_mvarId_4209_, v___f_4215_, v_a_4210_, v_a_4211_, v_a_4212_, v_a_4213_);
if (lean_obj_tag(v___x_4216_) == 0)
{
lean_object* v_a_4217_; lean_object* v___x_4218_; lean_object* v___x_4219_; 
v_a_4217_ = lean_ctor_get(v___x_4216_, 0);
lean_inc(v_a_4217_);
lean_dec_ref_known(v___x_4216_, 1);
v___x_4218_ = lean_obj_once(&l_Lean_MVarId_casesAnd___closed__3, &l_Lean_MVarId_casesAnd___closed__3_once, _init_l_Lean_MVarId_casesAnd___closed__3);
v___x_4219_ = l_Lean_Meta_exactlyOne(v_a_4217_, v___x_4218_, v_a_4210_, v_a_4211_, v_a_4212_, v_a_4213_);
lean_dec(v_a_4217_);
return v___x_4219_;
}
else
{
lean_object* v_a_4220_; lean_object* v___x_4222_; uint8_t v_isShared_4223_; uint8_t v_isSharedCheck_4227_; 
v_a_4220_ = lean_ctor_get(v___x_4216_, 0);
v_isSharedCheck_4227_ = !lean_is_exclusive(v___x_4216_);
if (v_isSharedCheck_4227_ == 0)
{
v___x_4222_ = v___x_4216_;
v_isShared_4223_ = v_isSharedCheck_4227_;
goto v_resetjp_4221_;
}
else
{
lean_inc(v_a_4220_);
lean_dec(v___x_4216_);
v___x_4222_ = lean_box(0);
v_isShared_4223_ = v_isSharedCheck_4227_;
goto v_resetjp_4221_;
}
v_resetjp_4221_:
{
lean_object* v___x_4225_; 
if (v_isShared_4223_ == 0)
{
v___x_4225_ = v___x_4222_;
goto v_reusejp_4224_;
}
else
{
lean_object* v_reuseFailAlloc_4226_; 
v_reuseFailAlloc_4226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4226_, 0, v_a_4220_);
v___x_4225_ = v_reuseFailAlloc_4226_;
goto v_reusejp_4224_;
}
v_reusejp_4224_:
{
return v___x_4225_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesAnd___boxed(lean_object* v_mvarId_4228_, lean_object* v_a_4229_, lean_object* v_a_4230_, lean_object* v_a_4231_, lean_object* v_a_4232_, lean_object* v_a_4233_){
_start:
{
lean_object* v_res_4234_; 
v_res_4234_ = l_Lean_MVarId_casesAnd(v_mvarId_4228_, v_a_4229_, v_a_4230_, v_a_4231_, v_a_4232_);
lean_dec(v_a_4232_);
lean_dec_ref(v_a_4231_);
lean_dec(v_a_4230_);
lean_dec_ref(v_a_4229_);
return v_res_4234_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_substEqs___lam__0(lean_object* v_localDecl_4235_, lean_object* v___y_4236_, lean_object* v___y_4237_, lean_object* v___y_4238_, lean_object* v___y_4239_){
_start:
{
lean_object* v___x_4241_; lean_object* v___x_4242_; lean_object* v_a_4243_; lean_object* v___x_4245_; uint8_t v_isShared_4246_; uint8_t v_isSharedCheck_4257_; 
v___x_4241_ = l_Lean_LocalDecl_type(v_localDecl_4235_);
v___x_4242_ = l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0___redArg(v___x_4241_, v___y_4237_);
v_a_4243_ = lean_ctor_get(v___x_4242_, 0);
v_isSharedCheck_4257_ = !lean_is_exclusive(v___x_4242_);
if (v_isSharedCheck_4257_ == 0)
{
v___x_4245_ = v___x_4242_;
v_isShared_4246_ = v_isSharedCheck_4257_;
goto v_resetjp_4244_;
}
else
{
lean_inc(v_a_4243_);
lean_dec(v___x_4242_);
v___x_4245_ = lean_box(0);
v_isShared_4246_ = v_isSharedCheck_4257_;
goto v_resetjp_4244_;
}
v_resetjp_4244_:
{
uint8_t v___x_4247_; 
v___x_4247_ = l_Lean_Expr_isEq(v_a_4243_);
if (v___x_4247_ == 0)
{
uint8_t v___x_4248_; lean_object* v___x_4249_; lean_object* v___x_4251_; 
v___x_4248_ = l_Lean_Expr_isHEq(v_a_4243_);
lean_dec(v_a_4243_);
v___x_4249_ = lean_box(v___x_4248_);
if (v_isShared_4246_ == 0)
{
lean_ctor_set(v___x_4245_, 0, v___x_4249_);
v___x_4251_ = v___x_4245_;
goto v_reusejp_4250_;
}
else
{
lean_object* v_reuseFailAlloc_4252_; 
v_reuseFailAlloc_4252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4252_, 0, v___x_4249_);
v___x_4251_ = v_reuseFailAlloc_4252_;
goto v_reusejp_4250_;
}
v_reusejp_4250_:
{
return v___x_4251_;
}
}
else
{
lean_object* v___x_4253_; lean_object* v___x_4255_; 
lean_dec(v_a_4243_);
v___x_4253_ = lean_box(v___x_4247_);
if (v_isShared_4246_ == 0)
{
lean_ctor_set(v___x_4245_, 0, v___x_4253_);
v___x_4255_ = v___x_4245_;
goto v_reusejp_4254_;
}
else
{
lean_object* v_reuseFailAlloc_4256_; 
v_reuseFailAlloc_4256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4256_, 0, v___x_4253_);
v___x_4255_ = v_reuseFailAlloc_4256_;
goto v_reusejp_4254_;
}
v_reusejp_4254_:
{
return v___x_4255_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_substEqs___lam__0___boxed(lean_object* v_localDecl_4258_, lean_object* v___y_4259_, lean_object* v___y_4260_, lean_object* v___y_4261_, lean_object* v___y_4262_, lean_object* v___y_4263_){
_start:
{
lean_object* v_res_4264_; 
v_res_4264_ = l_Lean_MVarId_substEqs___lam__0(v_localDecl_4258_, v___y_4259_, v___y_4260_, v___y_4261_, v___y_4262_);
lean_dec(v___y_4262_);
lean_dec_ref(v___y_4261_);
lean_dec(v___y_4260_);
lean_dec_ref(v___y_4259_);
lean_dec_ref(v_localDecl_4258_);
return v_res_4264_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_substEqs(lean_object* v_mvarId_4266_, lean_object* v_a_4267_, lean_object* v_a_4268_, lean_object* v_a_4269_, lean_object* v_a_4270_){
_start:
{
lean_object* v___f_4272_; lean_object* v___x_4273_; 
v___f_4272_ = ((lean_object*)(l_Lean_MVarId_substEqs___closed__0));
v___x_4273_ = l_Lean_MVarId_casesRec(v_mvarId_4266_, v___f_4272_, v_a_4267_, v_a_4268_, v_a_4269_, v_a_4270_);
if (lean_obj_tag(v___x_4273_) == 0)
{
lean_object* v_a_4274_; lean_object* v___x_4275_; lean_object* v___x_4276_; 
v_a_4274_ = lean_ctor_get(v___x_4273_, 0);
lean_inc(v_a_4274_);
lean_dec_ref_known(v___x_4273_, 1);
v___x_4275_ = lean_obj_once(&l_Lean_MVarId_casesAnd___closed__3, &l_Lean_MVarId_casesAnd___closed__3_once, _init_l_Lean_MVarId_casesAnd___closed__3);
v___x_4276_ = l_Lean_Meta_ensureAtMostOne(v_a_4274_, v___x_4275_, v_a_4267_, v_a_4268_, v_a_4269_, v_a_4270_);
lean_dec(v_a_4274_);
return v___x_4276_;
}
else
{
lean_object* v_a_4277_; lean_object* v___x_4279_; uint8_t v_isShared_4280_; uint8_t v_isSharedCheck_4284_; 
v_a_4277_ = lean_ctor_get(v___x_4273_, 0);
v_isSharedCheck_4284_ = !lean_is_exclusive(v___x_4273_);
if (v_isSharedCheck_4284_ == 0)
{
v___x_4279_ = v___x_4273_;
v_isShared_4280_ = v_isSharedCheck_4284_;
goto v_resetjp_4278_;
}
else
{
lean_inc(v_a_4277_);
lean_dec(v___x_4273_);
v___x_4279_ = lean_box(0);
v_isShared_4280_ = v_isSharedCheck_4284_;
goto v_resetjp_4278_;
}
v_resetjp_4278_:
{
lean_object* v___x_4282_; 
if (v_isShared_4280_ == 0)
{
v___x_4282_ = v___x_4279_;
goto v_reusejp_4281_;
}
else
{
lean_object* v_reuseFailAlloc_4283_; 
v_reuseFailAlloc_4283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4283_, 0, v_a_4277_);
v___x_4282_ = v_reuseFailAlloc_4283_;
goto v_reusejp_4281_;
}
v_reusejp_4281_:
{
return v___x_4282_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_substEqs___boxed(lean_object* v_mvarId_4285_, lean_object* v_a_4286_, lean_object* v_a_4287_, lean_object* v_a_4288_, lean_object* v_a_4289_, lean_object* v_a_4290_){
_start:
{
lean_object* v_res_4291_; 
v_res_4291_ = l_Lean_MVarId_substEqs(v_mvarId_4285_, v_a_4286_, v_a_4287_, v_a_4288_, v_a_4289_);
lean_dec(v_a_4289_);
lean_dec_ref(v_a_4288_);
lean_dec(v_a_4287_);
lean_dec_ref(v_a_4286_);
return v_res_4291_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal___closed__1(void){
_start:
{
lean_object* v___x_4293_; lean_object* v___x_4294_; 
v___x_4293_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal___closed__0));
v___x_4294_ = l_Lean_stringToMessageData(v___x_4293_);
return v___x_4294_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal(lean_object* v_s_4295_, lean_object* v_a_4296_, lean_object* v_a_4297_, lean_object* v_a_4298_, lean_object* v_a_4299_){
_start:
{
lean_object* v___y_4302_; lean_object* v___y_4303_; lean_object* v___y_4304_; lean_object* v___y_4305_; lean_object* v_toInductionSubgoal_4308_; lean_object* v___x_4310_; uint8_t v_isShared_4311_; uint8_t v_isSharedCheck_4324_; 
v_toInductionSubgoal_4308_ = lean_ctor_get(v_s_4295_, 0);
v_isSharedCheck_4324_ = !lean_is_exclusive(v_s_4295_);
if (v_isSharedCheck_4324_ == 0)
{
lean_object* v_unused_4325_; 
v_unused_4325_ = lean_ctor_get(v_s_4295_, 1);
lean_dec(v_unused_4325_);
v___x_4310_ = v_s_4295_;
v_isShared_4311_ = v_isSharedCheck_4324_;
goto v_resetjp_4309_;
}
else
{
lean_inc(v_toInductionSubgoal_4308_);
lean_dec(v_s_4295_);
v___x_4310_ = lean_box(0);
v_isShared_4311_ = v_isSharedCheck_4324_;
goto v_resetjp_4309_;
}
v___jp_4301_:
{
lean_object* v___x_4306_; lean_object* v___x_4307_; 
v___x_4306_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal___closed__1, &l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal___closed__1_once, _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal___closed__1);
v___x_4307_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected_spec__0___redArg(v___x_4306_, v___y_4302_, v___y_4303_, v___y_4304_, v___y_4305_);
return v___x_4307_;
}
v_resetjp_4309_:
{
lean_object* v_mvarId_4312_; lean_object* v_fields_4313_; lean_object* v___x_4314_; lean_object* v___x_4315_; uint8_t v___x_4316_; 
v_mvarId_4312_ = lean_ctor_get(v_toInductionSubgoal_4308_, 0);
lean_inc(v_mvarId_4312_);
v_fields_4313_ = lean_ctor_get(v_toInductionSubgoal_4308_, 1);
lean_inc_ref(v_fields_4313_);
lean_dec_ref(v_toInductionSubgoal_4308_);
v___x_4314_ = lean_array_get_size(v_fields_4313_);
v___x_4315_ = lean_unsigned_to_nat(1u);
v___x_4316_ = lean_nat_dec_eq(v___x_4314_, v___x_4315_);
if (v___x_4316_ == 0)
{
lean_dec_ref(v_fields_4313_);
lean_dec(v_mvarId_4312_);
lean_del_object(v___x_4310_);
v___y_4302_ = v_a_4296_;
v___y_4303_ = v_a_4297_;
v___y_4304_ = v_a_4298_;
v___y_4305_ = v_a_4299_;
goto v___jp_4301_;
}
else
{
lean_object* v___x_4317_; lean_object* v___x_4318_; 
v___x_4317_ = lean_unsigned_to_nat(0u);
v___x_4318_ = lean_array_fget(v_fields_4313_, v___x_4317_);
lean_dec_ref(v_fields_4313_);
if (lean_obj_tag(v___x_4318_) == 1)
{
lean_object* v_fvarId_4319_; lean_object* v___x_4321_; 
v_fvarId_4319_ = lean_ctor_get(v___x_4318_, 0);
lean_inc(v_fvarId_4319_);
lean_dec_ref_known(v___x_4318_, 1);
if (v_isShared_4311_ == 0)
{
lean_ctor_set(v___x_4310_, 1, v_fvarId_4319_);
lean_ctor_set(v___x_4310_, 0, v_mvarId_4312_);
v___x_4321_ = v___x_4310_;
goto v_reusejp_4320_;
}
else
{
lean_object* v_reuseFailAlloc_4323_; 
v_reuseFailAlloc_4323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4323_, 0, v_mvarId_4312_);
lean_ctor_set(v_reuseFailAlloc_4323_, 1, v_fvarId_4319_);
v___x_4321_ = v_reuseFailAlloc_4323_;
goto v_reusejp_4320_;
}
v_reusejp_4320_:
{
lean_object* v___x_4322_; 
v___x_4322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4322_, 0, v___x_4321_);
return v___x_4322_;
}
}
else
{
lean_dec(v___x_4318_);
lean_dec(v_mvarId_4312_);
lean_del_object(v___x_4310_);
v___y_4302_ = v_a_4296_;
v___y_4303_ = v_a_4297_;
v___y_4304_ = v_a_4298_;
v___y_4305_ = v_a_4299_;
goto v___jp_4301_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal___boxed(lean_object* v_s_4326_, lean_object* v_a_4327_, lean_object* v_a_4328_, lean_object* v_a_4329_, lean_object* v_a_4330_, lean_object* v_a_4331_){
_start:
{
lean_object* v_res_4332_; 
v_res_4332_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal(v_s_4326_, v_a_4327_, v_a_4328_, v_a_4329_, v_a_4330_);
lean_dec(v_a_4330_);
lean_dec_ref(v_a_4329_);
lean_dec(v_a_4328_);
lean_dec_ref(v_a_4327_);
return v_res_4332_;
}
}
static lean_object* _init_l_Lean_MVarId_byCases___closed__3(void){
_start:
{
lean_object* v___x_4337_; lean_object* v___x_4338_; 
v___x_4337_ = ((lean_object*)(l_Lean_MVarId_byCases___closed__2));
v___x_4338_ = l_Lean_stringToMessageData(v___x_4337_);
return v___x_4338_;
}
}
static lean_object* _init_l_Lean_MVarId_byCases___closed__5(void){
_start:
{
lean_object* v___x_4340_; lean_object* v___x_4341_; 
v___x_4340_ = ((lean_object*)(l_Lean_MVarId_byCases___closed__4));
v___x_4341_ = l_Lean_stringToMessageData(v___x_4340_);
return v___x_4341_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_byCases(lean_object* v_mvarId_4342_, lean_object* v_p_4343_, lean_object* v_hName_4344_, lean_object* v_a_4345_, lean_object* v_a_4346_, lean_object* v_a_4347_, lean_object* v_a_4348_){
_start:
{
lean_object* v___x_4350_; lean_object* v___x_4351_; lean_object* v___x_4352_; lean_object* v___x_4353_; lean_object* v___x_4354_; 
v___x_4350_ = ((lean_object*)(l_Lean_MVarId_byCases___closed__1));
lean_inc_ref_n(v_p_4343_, 3);
v___x_4351_ = l_Lean_mkNot(v_p_4343_);
v___x_4352_ = l_Lean_mkOr(v_p_4343_, v___x_4351_);
v___x_4353_ = l_Lean_mkEM(v_p_4343_);
v___x_4354_ = l_Lean_MVarId_assert(v_mvarId_4342_, v___x_4350_, v___x_4352_, v___x_4353_, v_a_4345_, v_a_4346_, v_a_4347_, v_a_4348_);
if (lean_obj_tag(v___x_4354_) == 0)
{
lean_object* v_a_4355_; uint8_t v___x_4356_; lean_object* v___x_4357_; 
v_a_4355_ = lean_ctor_get(v___x_4354_, 0);
lean_inc(v_a_4355_);
lean_dec_ref_known(v___x_4354_, 1);
v___x_4356_ = 0;
v___x_4357_ = l_Lean_Meta_intro1Core(v_a_4355_, v___x_4356_, v_a_4345_, v_a_4346_, v_a_4347_, v_a_4348_);
if (lean_obj_tag(v___x_4357_) == 0)
{
lean_object* v_a_4358_; lean_object* v_fst_4359_; lean_object* v_snd_4360_; lean_object* v___x_4362_; uint8_t v_isShared_4363_; uint8_t v_isSharedCheck_4425_; 
v_a_4358_ = lean_ctor_get(v___x_4357_, 0);
lean_inc(v_a_4358_);
lean_dec_ref_known(v___x_4357_, 1);
v_fst_4359_ = lean_ctor_get(v_a_4358_, 0);
v_snd_4360_ = lean_ctor_get(v_a_4358_, 1);
v_isSharedCheck_4425_ = !lean_is_exclusive(v_a_4358_);
if (v_isSharedCheck_4425_ == 0)
{
v___x_4362_ = v_a_4358_;
v_isShared_4363_ = v_isSharedCheck_4425_;
goto v_resetjp_4361_;
}
else
{
lean_inc(v_snd_4360_);
lean_inc(v_fst_4359_);
lean_dec(v_a_4358_);
v___x_4362_ = lean_box(0);
v_isShared_4363_ = v_isSharedCheck_4425_;
goto v_resetjp_4361_;
}
v_resetjp_4361_:
{
lean_object* v___x_4364_; lean_object* v___x_4365_; lean_object* v___x_4366_; lean_object* v___x_4367_; lean_object* v___x_4368_; lean_object* v___x_4369_; lean_object* v___x_4370_; lean_object* v___x_4371_; lean_object* v___x_4372_; 
v___x_4364_ = lean_box(0);
v___x_4365_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4365_, 0, v_hName_4344_);
lean_ctor_set(v___x_4365_, 1, v___x_4364_);
v___x_4366_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4366_, 0, v___x_4365_);
lean_ctor_set_uint8(v___x_4366_, sizeof(void*)*1, v___x_4356_);
v___x_4367_ = lean_unsigned_to_nat(2u);
v___x_4368_ = lean_mk_empty_array_with_capacity(v___x_4367_);
lean_inc_ref(v___x_4366_);
v___x_4369_ = lean_array_push(v___x_4368_, v___x_4366_);
v___x_4370_ = lean_array_push(v___x_4369_, v___x_4366_);
v___x_4371_ = lean_box(0);
v___x_4372_ = l_Lean_Meta_Cases_cases(v_snd_4360_, v_fst_4359_, v___x_4370_, v___x_4356_, v___x_4371_, v_a_4345_, v_a_4346_, v_a_4347_, v_a_4348_);
if (lean_obj_tag(v___x_4372_) == 0)
{
lean_object* v_a_4373_; lean_object* v___x_4374_; uint8_t v___x_4375_; 
v_a_4373_ = lean_ctor_get(v___x_4372_, 0);
lean_inc(v_a_4373_);
lean_dec_ref_known(v___x_4372_, 1);
v___x_4374_ = lean_array_get_size(v_a_4373_);
v___x_4375_ = lean_nat_dec_eq(v___x_4374_, v___x_4367_);
if (v___x_4375_ == 0)
{
lean_object* v___x_4376_; lean_object* v___x_4377_; lean_object* v___x_4378_; lean_object* v___x_4379_; lean_object* v___x_4380_; lean_object* v___x_4381_; lean_object* v___x_4382_; 
lean_dec(v_a_4373_);
lean_del_object(v___x_4362_);
v___x_4376_ = lean_obj_once(&l_Lean_MVarId_byCases___closed__3, &l_Lean_MVarId_byCases___closed__3_once, _init_l_Lean_MVarId_byCases___closed__3);
v___x_4377_ = lean_unsigned_to_nat(30u);
v___x_4378_ = l_Lean_inlineExpr(v_p_4343_, v___x_4377_);
v___x_4379_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4379_, 0, v___x_4376_);
lean_ctor_set(v___x_4379_, 1, v___x_4378_);
v___x_4380_ = lean_obj_once(&l_Lean_MVarId_byCases___closed__5, &l_Lean_MVarId_byCases___closed__5_once, _init_l_Lean_MVarId_byCases___closed__5);
v___x_4381_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4381_, 0, v___x_4379_);
lean_ctor_set(v___x_4381_, 1, v___x_4380_);
v___x_4382_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected_spec__0___redArg(v___x_4381_, v_a_4345_, v_a_4346_, v_a_4347_, v_a_4348_);
return v___x_4382_;
}
else
{
lean_object* v___x_4383_; lean_object* v___x_4384_; lean_object* v___x_4385_; 
lean_dec_ref(v_p_4343_);
v___x_4383_ = lean_unsigned_to_nat(0u);
v___x_4384_ = lean_array_fget_borrowed(v_a_4373_, v___x_4383_);
lean_inc(v___x_4384_);
v___x_4385_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal(v___x_4384_, v_a_4345_, v_a_4346_, v_a_4347_, v_a_4348_);
if (lean_obj_tag(v___x_4385_) == 0)
{
lean_object* v_a_4386_; lean_object* v___x_4387_; lean_object* v___x_4388_; lean_object* v___x_4389_; 
v_a_4386_ = lean_ctor_get(v___x_4385_, 0);
lean_inc(v_a_4386_);
lean_dec_ref_known(v___x_4385_, 1);
v___x_4387_ = lean_unsigned_to_nat(1u);
v___x_4388_ = lean_array_fget(v_a_4373_, v___x_4387_);
lean_dec(v_a_4373_);
v___x_4389_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal(v___x_4388_, v_a_4345_, v_a_4346_, v_a_4347_, v_a_4348_);
if (lean_obj_tag(v___x_4389_) == 0)
{
lean_object* v_a_4390_; lean_object* v___x_4392_; uint8_t v_isShared_4393_; uint8_t v_isSharedCheck_4400_; 
v_a_4390_ = lean_ctor_get(v___x_4389_, 0);
v_isSharedCheck_4400_ = !lean_is_exclusive(v___x_4389_);
if (v_isSharedCheck_4400_ == 0)
{
v___x_4392_ = v___x_4389_;
v_isShared_4393_ = v_isSharedCheck_4400_;
goto v_resetjp_4391_;
}
else
{
lean_inc(v_a_4390_);
lean_dec(v___x_4389_);
v___x_4392_ = lean_box(0);
v_isShared_4393_ = v_isSharedCheck_4400_;
goto v_resetjp_4391_;
}
v_resetjp_4391_:
{
lean_object* v___x_4395_; 
if (v_isShared_4363_ == 0)
{
lean_ctor_set(v___x_4362_, 1, v_a_4390_);
lean_ctor_set(v___x_4362_, 0, v_a_4386_);
v___x_4395_ = v___x_4362_;
goto v_reusejp_4394_;
}
else
{
lean_object* v_reuseFailAlloc_4399_; 
v_reuseFailAlloc_4399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4399_, 0, v_a_4386_);
lean_ctor_set(v_reuseFailAlloc_4399_, 1, v_a_4390_);
v___x_4395_ = v_reuseFailAlloc_4399_;
goto v_reusejp_4394_;
}
v_reusejp_4394_:
{
lean_object* v___x_4397_; 
if (v_isShared_4393_ == 0)
{
lean_ctor_set(v___x_4392_, 0, v___x_4395_);
v___x_4397_ = v___x_4392_;
goto v_reusejp_4396_;
}
else
{
lean_object* v_reuseFailAlloc_4398_; 
v_reuseFailAlloc_4398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4398_, 0, v___x_4395_);
v___x_4397_ = v_reuseFailAlloc_4398_;
goto v_reusejp_4396_;
}
v_reusejp_4396_:
{
return v___x_4397_;
}
}
}
}
else
{
lean_object* v_a_4401_; lean_object* v___x_4403_; uint8_t v_isShared_4404_; uint8_t v_isSharedCheck_4408_; 
lean_dec(v_a_4386_);
lean_del_object(v___x_4362_);
v_a_4401_ = lean_ctor_get(v___x_4389_, 0);
v_isSharedCheck_4408_ = !lean_is_exclusive(v___x_4389_);
if (v_isSharedCheck_4408_ == 0)
{
v___x_4403_ = v___x_4389_;
v_isShared_4404_ = v_isSharedCheck_4408_;
goto v_resetjp_4402_;
}
else
{
lean_inc(v_a_4401_);
lean_dec(v___x_4389_);
v___x_4403_ = lean_box(0);
v_isShared_4404_ = v_isSharedCheck_4408_;
goto v_resetjp_4402_;
}
v_resetjp_4402_:
{
lean_object* v___x_4406_; 
if (v_isShared_4404_ == 0)
{
v___x_4406_ = v___x_4403_;
goto v_reusejp_4405_;
}
else
{
lean_object* v_reuseFailAlloc_4407_; 
v_reuseFailAlloc_4407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4407_, 0, v_a_4401_);
v___x_4406_ = v_reuseFailAlloc_4407_;
goto v_reusejp_4405_;
}
v_reusejp_4405_:
{
return v___x_4406_;
}
}
}
}
else
{
lean_object* v_a_4409_; lean_object* v___x_4411_; uint8_t v_isShared_4412_; uint8_t v_isSharedCheck_4416_; 
lean_dec(v_a_4373_);
lean_del_object(v___x_4362_);
v_a_4409_ = lean_ctor_get(v___x_4385_, 0);
v_isSharedCheck_4416_ = !lean_is_exclusive(v___x_4385_);
if (v_isSharedCheck_4416_ == 0)
{
v___x_4411_ = v___x_4385_;
v_isShared_4412_ = v_isSharedCheck_4416_;
goto v_resetjp_4410_;
}
else
{
lean_inc(v_a_4409_);
lean_dec(v___x_4385_);
v___x_4411_ = lean_box(0);
v_isShared_4412_ = v_isSharedCheck_4416_;
goto v_resetjp_4410_;
}
v_resetjp_4410_:
{
lean_object* v___x_4414_; 
if (v_isShared_4412_ == 0)
{
v___x_4414_ = v___x_4411_;
goto v_reusejp_4413_;
}
else
{
lean_object* v_reuseFailAlloc_4415_; 
v_reuseFailAlloc_4415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4415_, 0, v_a_4409_);
v___x_4414_ = v_reuseFailAlloc_4415_;
goto v_reusejp_4413_;
}
v_reusejp_4413_:
{
return v___x_4414_;
}
}
}
}
}
else
{
lean_object* v_a_4417_; lean_object* v___x_4419_; uint8_t v_isShared_4420_; uint8_t v_isSharedCheck_4424_; 
lean_del_object(v___x_4362_);
lean_dec_ref(v_p_4343_);
v_a_4417_ = lean_ctor_get(v___x_4372_, 0);
v_isSharedCheck_4424_ = !lean_is_exclusive(v___x_4372_);
if (v_isSharedCheck_4424_ == 0)
{
v___x_4419_ = v___x_4372_;
v_isShared_4420_ = v_isSharedCheck_4424_;
goto v_resetjp_4418_;
}
else
{
lean_inc(v_a_4417_);
lean_dec(v___x_4372_);
v___x_4419_ = lean_box(0);
v_isShared_4420_ = v_isSharedCheck_4424_;
goto v_resetjp_4418_;
}
v_resetjp_4418_:
{
lean_object* v___x_4422_; 
if (v_isShared_4420_ == 0)
{
v___x_4422_ = v___x_4419_;
goto v_reusejp_4421_;
}
else
{
lean_object* v_reuseFailAlloc_4423_; 
v_reuseFailAlloc_4423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4423_, 0, v_a_4417_);
v___x_4422_ = v_reuseFailAlloc_4423_;
goto v_reusejp_4421_;
}
v_reusejp_4421_:
{
return v___x_4422_;
}
}
}
}
}
else
{
lean_object* v_a_4426_; lean_object* v___x_4428_; uint8_t v_isShared_4429_; uint8_t v_isSharedCheck_4433_; 
lean_dec(v_hName_4344_);
lean_dec_ref(v_p_4343_);
v_a_4426_ = lean_ctor_get(v___x_4357_, 0);
v_isSharedCheck_4433_ = !lean_is_exclusive(v___x_4357_);
if (v_isSharedCheck_4433_ == 0)
{
v___x_4428_ = v___x_4357_;
v_isShared_4429_ = v_isSharedCheck_4433_;
goto v_resetjp_4427_;
}
else
{
lean_inc(v_a_4426_);
lean_dec(v___x_4357_);
v___x_4428_ = lean_box(0);
v_isShared_4429_ = v_isSharedCheck_4433_;
goto v_resetjp_4427_;
}
v_resetjp_4427_:
{
lean_object* v___x_4431_; 
if (v_isShared_4429_ == 0)
{
v___x_4431_ = v___x_4428_;
goto v_reusejp_4430_;
}
else
{
lean_object* v_reuseFailAlloc_4432_; 
v_reuseFailAlloc_4432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4432_, 0, v_a_4426_);
v___x_4431_ = v_reuseFailAlloc_4432_;
goto v_reusejp_4430_;
}
v_reusejp_4430_:
{
return v___x_4431_;
}
}
}
}
else
{
lean_object* v_a_4434_; lean_object* v___x_4436_; uint8_t v_isShared_4437_; uint8_t v_isSharedCheck_4441_; 
lean_dec(v_hName_4344_);
lean_dec_ref(v_p_4343_);
v_a_4434_ = lean_ctor_get(v___x_4354_, 0);
v_isSharedCheck_4441_ = !lean_is_exclusive(v___x_4354_);
if (v_isSharedCheck_4441_ == 0)
{
v___x_4436_ = v___x_4354_;
v_isShared_4437_ = v_isSharedCheck_4441_;
goto v_resetjp_4435_;
}
else
{
lean_inc(v_a_4434_);
lean_dec(v___x_4354_);
v___x_4436_ = lean_box(0);
v_isShared_4437_ = v_isSharedCheck_4441_;
goto v_resetjp_4435_;
}
v_resetjp_4435_:
{
lean_object* v___x_4439_; 
if (v_isShared_4437_ == 0)
{
v___x_4439_ = v___x_4436_;
goto v_reusejp_4438_;
}
else
{
lean_object* v_reuseFailAlloc_4440_; 
v_reuseFailAlloc_4440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4440_, 0, v_a_4434_);
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
}
LEAN_EXPORT lean_object* l_Lean_MVarId_byCases___boxed(lean_object* v_mvarId_4442_, lean_object* v_p_4443_, lean_object* v_hName_4444_, lean_object* v_a_4445_, lean_object* v_a_4446_, lean_object* v_a_4447_, lean_object* v_a_4448_, lean_object* v_a_4449_){
_start:
{
lean_object* v_res_4450_; 
v_res_4450_ = l_Lean_MVarId_byCases(v_mvarId_4442_, v_p_4443_, v_hName_4444_, v_a_4445_, v_a_4446_, v_a_4447_, v_a_4448_);
lean_dec(v_a_4448_);
lean_dec_ref(v_a_4447_);
lean_dec(v_a_4446_);
lean_dec_ref(v_a_4445_);
return v_res_4450_;
}
}
static lean_object* _init_l_Lean_MVarId_byCasesDec___closed__2(void){
_start:
{
lean_object* v___x_4454_; lean_object* v___x_4455_; lean_object* v___x_4456_; 
v___x_4454_ = lean_box(0);
v___x_4455_ = ((lean_object*)(l_Lean_MVarId_byCasesDec___closed__1));
v___x_4456_ = l_Lean_mkConst(v___x_4455_, v___x_4454_);
return v___x_4456_;
}
}
static lean_object* _init_l_Lean_MVarId_byCasesDec___closed__4(void){
_start:
{
lean_object* v___x_4458_; lean_object* v___x_4459_; 
v___x_4458_ = ((lean_object*)(l_Lean_MVarId_byCasesDec___closed__3));
v___x_4459_ = l_Lean_stringToMessageData(v___x_4458_);
return v___x_4459_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_byCasesDec(lean_object* v_mvarId_4460_, lean_object* v_p_4461_, lean_object* v_dec_4462_, lean_object* v_hName_4463_, lean_object* v_a_4464_, lean_object* v_a_4465_, lean_object* v_a_4466_, lean_object* v_a_4467_){
_start:
{
lean_object* v___x_4469_; lean_object* v___x_4470_; lean_object* v___x_4471_; lean_object* v___x_4472_; lean_object* v___x_4473_; 
v___x_4469_ = ((lean_object*)(l_Lean_MVarId_byCases___closed__1));
v___x_4470_ = lean_box(0);
v___x_4471_ = lean_obj_once(&l_Lean_MVarId_byCasesDec___closed__2, &l_Lean_MVarId_byCasesDec___closed__2_once, _init_l_Lean_MVarId_byCasesDec___closed__2);
lean_inc_ref(v_p_4461_);
v___x_4472_ = l_Lean_Expr_app___override(v___x_4471_, v_p_4461_);
v___x_4473_ = l_Lean_MVarId_assert(v_mvarId_4460_, v___x_4469_, v___x_4472_, v_dec_4462_, v_a_4464_, v_a_4465_, v_a_4466_, v_a_4467_);
if (lean_obj_tag(v___x_4473_) == 0)
{
lean_object* v_a_4474_; uint8_t v___x_4475_; lean_object* v___x_4476_; 
v_a_4474_ = lean_ctor_get(v___x_4473_, 0);
lean_inc(v_a_4474_);
lean_dec_ref_known(v___x_4473_, 1);
v___x_4475_ = 0;
v___x_4476_ = l_Lean_Meta_intro1Core(v_a_4474_, v___x_4475_, v_a_4464_, v_a_4465_, v_a_4466_, v_a_4467_);
if (lean_obj_tag(v___x_4476_) == 0)
{
lean_object* v_a_4477_; lean_object* v_fst_4478_; lean_object* v_snd_4479_; lean_object* v___x_4481_; uint8_t v_isShared_4482_; uint8_t v_isSharedCheck_4543_; 
v_a_4477_ = lean_ctor_get(v___x_4476_, 0);
lean_inc(v_a_4477_);
lean_dec_ref_known(v___x_4476_, 1);
v_fst_4478_ = lean_ctor_get(v_a_4477_, 0);
v_snd_4479_ = lean_ctor_get(v_a_4477_, 1);
v_isSharedCheck_4543_ = !lean_is_exclusive(v_a_4477_);
if (v_isSharedCheck_4543_ == 0)
{
v___x_4481_ = v_a_4477_;
v_isShared_4482_ = v_isSharedCheck_4543_;
goto v_resetjp_4480_;
}
else
{
lean_inc(v_snd_4479_);
lean_inc(v_fst_4478_);
lean_dec(v_a_4477_);
v___x_4481_ = lean_box(0);
v_isShared_4482_ = v_isSharedCheck_4543_;
goto v_resetjp_4480_;
}
v_resetjp_4480_:
{
lean_object* v___x_4483_; lean_object* v___x_4484_; lean_object* v___x_4485_; lean_object* v___x_4486_; lean_object* v___x_4487_; lean_object* v___x_4488_; lean_object* v___x_4489_; lean_object* v___x_4490_; 
v___x_4483_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4483_, 0, v_hName_4463_);
lean_ctor_set(v___x_4483_, 1, v___x_4470_);
v___x_4484_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4484_, 0, v___x_4483_);
lean_ctor_set_uint8(v___x_4484_, sizeof(void*)*1, v___x_4475_);
v___x_4485_ = lean_unsigned_to_nat(2u);
v___x_4486_ = lean_mk_empty_array_with_capacity(v___x_4485_);
lean_inc_ref(v___x_4484_);
v___x_4487_ = lean_array_push(v___x_4486_, v___x_4484_);
v___x_4488_ = lean_array_push(v___x_4487_, v___x_4484_);
v___x_4489_ = lean_box(0);
v___x_4490_ = l_Lean_Meta_Cases_cases(v_snd_4479_, v_fst_4478_, v___x_4488_, v___x_4475_, v___x_4489_, v_a_4464_, v_a_4465_, v_a_4466_, v_a_4467_);
if (lean_obj_tag(v___x_4490_) == 0)
{
lean_object* v_a_4491_; lean_object* v___x_4492_; uint8_t v___x_4493_; 
v_a_4491_ = lean_ctor_get(v___x_4490_, 0);
lean_inc(v_a_4491_);
lean_dec_ref_known(v___x_4490_, 1);
v___x_4492_ = lean_array_get_size(v_a_4491_);
v___x_4493_ = lean_nat_dec_eq(v___x_4492_, v___x_4485_);
if (v___x_4493_ == 0)
{
lean_object* v___x_4494_; lean_object* v___x_4495_; lean_object* v___x_4496_; lean_object* v___x_4497_; lean_object* v___x_4498_; lean_object* v___x_4499_; lean_object* v___x_4500_; 
lean_dec(v_a_4491_);
lean_del_object(v___x_4481_);
v___x_4494_ = lean_obj_once(&l_Lean_MVarId_byCasesDec___closed__4, &l_Lean_MVarId_byCasesDec___closed__4_once, _init_l_Lean_MVarId_byCasesDec___closed__4);
v___x_4495_ = lean_unsigned_to_nat(30u);
v___x_4496_ = l_Lean_inlineExpr(v_p_4461_, v___x_4495_);
v___x_4497_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4497_, 0, v___x_4494_);
lean_ctor_set(v___x_4497_, 1, v___x_4496_);
v___x_4498_ = lean_obj_once(&l_Lean_MVarId_byCases___closed__5, &l_Lean_MVarId_byCases___closed__5_once, _init_l_Lean_MVarId_byCases___closed__5);
v___x_4499_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4499_, 0, v___x_4497_);
lean_ctor_set(v___x_4499_, 1, v___x_4498_);
v___x_4500_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected_spec__0___redArg(v___x_4499_, v_a_4464_, v_a_4465_, v_a_4466_, v_a_4467_);
return v___x_4500_;
}
else
{
lean_object* v___x_4501_; lean_object* v___x_4502_; lean_object* v___x_4503_; 
lean_dec_ref(v_p_4461_);
v___x_4501_ = lean_unsigned_to_nat(1u);
v___x_4502_ = lean_array_fget_borrowed(v_a_4491_, v___x_4501_);
lean_inc(v___x_4502_);
v___x_4503_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal(v___x_4502_, v_a_4464_, v_a_4465_, v_a_4466_, v_a_4467_);
if (lean_obj_tag(v___x_4503_) == 0)
{
lean_object* v_a_4504_; lean_object* v___x_4505_; lean_object* v___x_4506_; lean_object* v___x_4507_; 
v_a_4504_ = lean_ctor_get(v___x_4503_, 0);
lean_inc(v_a_4504_);
lean_dec_ref_known(v___x_4503_, 1);
v___x_4505_ = lean_unsigned_to_nat(0u);
v___x_4506_ = lean_array_fget(v_a_4491_, v___x_4505_);
lean_dec(v_a_4491_);
v___x_4507_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal(v___x_4506_, v_a_4464_, v_a_4465_, v_a_4466_, v_a_4467_);
if (lean_obj_tag(v___x_4507_) == 0)
{
lean_object* v_a_4508_; lean_object* v___x_4510_; uint8_t v_isShared_4511_; uint8_t v_isSharedCheck_4518_; 
v_a_4508_ = lean_ctor_get(v___x_4507_, 0);
v_isSharedCheck_4518_ = !lean_is_exclusive(v___x_4507_);
if (v_isSharedCheck_4518_ == 0)
{
v___x_4510_ = v___x_4507_;
v_isShared_4511_ = v_isSharedCheck_4518_;
goto v_resetjp_4509_;
}
else
{
lean_inc(v_a_4508_);
lean_dec(v___x_4507_);
v___x_4510_ = lean_box(0);
v_isShared_4511_ = v_isSharedCheck_4518_;
goto v_resetjp_4509_;
}
v_resetjp_4509_:
{
lean_object* v___x_4513_; 
if (v_isShared_4482_ == 0)
{
lean_ctor_set(v___x_4481_, 1, v_a_4508_);
lean_ctor_set(v___x_4481_, 0, v_a_4504_);
v___x_4513_ = v___x_4481_;
goto v_reusejp_4512_;
}
else
{
lean_object* v_reuseFailAlloc_4517_; 
v_reuseFailAlloc_4517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4517_, 0, v_a_4504_);
lean_ctor_set(v_reuseFailAlloc_4517_, 1, v_a_4508_);
v___x_4513_ = v_reuseFailAlloc_4517_;
goto v_reusejp_4512_;
}
v_reusejp_4512_:
{
lean_object* v___x_4515_; 
if (v_isShared_4511_ == 0)
{
lean_ctor_set(v___x_4510_, 0, v___x_4513_);
v___x_4515_ = v___x_4510_;
goto v_reusejp_4514_;
}
else
{
lean_object* v_reuseFailAlloc_4516_; 
v_reuseFailAlloc_4516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4516_, 0, v___x_4513_);
v___x_4515_ = v_reuseFailAlloc_4516_;
goto v_reusejp_4514_;
}
v_reusejp_4514_:
{
return v___x_4515_;
}
}
}
}
else
{
lean_object* v_a_4519_; lean_object* v___x_4521_; uint8_t v_isShared_4522_; uint8_t v_isSharedCheck_4526_; 
lean_dec(v_a_4504_);
lean_del_object(v___x_4481_);
v_a_4519_ = lean_ctor_get(v___x_4507_, 0);
v_isSharedCheck_4526_ = !lean_is_exclusive(v___x_4507_);
if (v_isSharedCheck_4526_ == 0)
{
v___x_4521_ = v___x_4507_;
v_isShared_4522_ = v_isSharedCheck_4526_;
goto v_resetjp_4520_;
}
else
{
lean_inc(v_a_4519_);
lean_dec(v___x_4507_);
v___x_4521_ = lean_box(0);
v_isShared_4522_ = v_isSharedCheck_4526_;
goto v_resetjp_4520_;
}
v_resetjp_4520_:
{
lean_object* v___x_4524_; 
if (v_isShared_4522_ == 0)
{
v___x_4524_ = v___x_4521_;
goto v_reusejp_4523_;
}
else
{
lean_object* v_reuseFailAlloc_4525_; 
v_reuseFailAlloc_4525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4525_, 0, v_a_4519_);
v___x_4524_ = v_reuseFailAlloc_4525_;
goto v_reusejp_4523_;
}
v_reusejp_4523_:
{
return v___x_4524_;
}
}
}
}
else
{
lean_object* v_a_4527_; lean_object* v___x_4529_; uint8_t v_isShared_4530_; uint8_t v_isSharedCheck_4534_; 
lean_dec(v_a_4491_);
lean_del_object(v___x_4481_);
v_a_4527_ = lean_ctor_get(v___x_4503_, 0);
v_isSharedCheck_4534_ = !lean_is_exclusive(v___x_4503_);
if (v_isSharedCheck_4534_ == 0)
{
v___x_4529_ = v___x_4503_;
v_isShared_4530_ = v_isSharedCheck_4534_;
goto v_resetjp_4528_;
}
else
{
lean_inc(v_a_4527_);
lean_dec(v___x_4503_);
v___x_4529_ = lean_box(0);
v_isShared_4530_ = v_isSharedCheck_4534_;
goto v_resetjp_4528_;
}
v_resetjp_4528_:
{
lean_object* v___x_4532_; 
if (v_isShared_4530_ == 0)
{
v___x_4532_ = v___x_4529_;
goto v_reusejp_4531_;
}
else
{
lean_object* v_reuseFailAlloc_4533_; 
v_reuseFailAlloc_4533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4533_, 0, v_a_4527_);
v___x_4532_ = v_reuseFailAlloc_4533_;
goto v_reusejp_4531_;
}
v_reusejp_4531_:
{
return v___x_4532_;
}
}
}
}
}
else
{
lean_object* v_a_4535_; lean_object* v___x_4537_; uint8_t v_isShared_4538_; uint8_t v_isSharedCheck_4542_; 
lean_del_object(v___x_4481_);
lean_dec_ref(v_p_4461_);
v_a_4535_ = lean_ctor_get(v___x_4490_, 0);
v_isSharedCheck_4542_ = !lean_is_exclusive(v___x_4490_);
if (v_isSharedCheck_4542_ == 0)
{
v___x_4537_ = v___x_4490_;
v_isShared_4538_ = v_isSharedCheck_4542_;
goto v_resetjp_4536_;
}
else
{
lean_inc(v_a_4535_);
lean_dec(v___x_4490_);
v___x_4537_ = lean_box(0);
v_isShared_4538_ = v_isSharedCheck_4542_;
goto v_resetjp_4536_;
}
v_resetjp_4536_:
{
lean_object* v___x_4540_; 
if (v_isShared_4538_ == 0)
{
v___x_4540_ = v___x_4537_;
goto v_reusejp_4539_;
}
else
{
lean_object* v_reuseFailAlloc_4541_; 
v_reuseFailAlloc_4541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4541_, 0, v_a_4535_);
v___x_4540_ = v_reuseFailAlloc_4541_;
goto v_reusejp_4539_;
}
v_reusejp_4539_:
{
return v___x_4540_;
}
}
}
}
}
else
{
lean_object* v_a_4544_; lean_object* v___x_4546_; uint8_t v_isShared_4547_; uint8_t v_isSharedCheck_4551_; 
lean_dec(v_hName_4463_);
lean_dec_ref(v_p_4461_);
v_a_4544_ = lean_ctor_get(v___x_4476_, 0);
v_isSharedCheck_4551_ = !lean_is_exclusive(v___x_4476_);
if (v_isSharedCheck_4551_ == 0)
{
v___x_4546_ = v___x_4476_;
v_isShared_4547_ = v_isSharedCheck_4551_;
goto v_resetjp_4545_;
}
else
{
lean_inc(v_a_4544_);
lean_dec(v___x_4476_);
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
lean_object* v_a_4552_; lean_object* v___x_4554_; uint8_t v_isShared_4555_; uint8_t v_isSharedCheck_4559_; 
lean_dec(v_hName_4463_);
lean_dec_ref(v_p_4461_);
v_a_4552_ = lean_ctor_get(v___x_4473_, 0);
v_isSharedCheck_4559_ = !lean_is_exclusive(v___x_4473_);
if (v_isSharedCheck_4559_ == 0)
{
v___x_4554_ = v___x_4473_;
v_isShared_4555_ = v_isSharedCheck_4559_;
goto v_resetjp_4553_;
}
else
{
lean_inc(v_a_4552_);
lean_dec(v___x_4473_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_byCasesDec___boxed(lean_object* v_mvarId_4560_, lean_object* v_p_4561_, lean_object* v_dec_4562_, lean_object* v_hName_4563_, lean_object* v_a_4564_, lean_object* v_a_4565_, lean_object* v_a_4566_, lean_object* v_a_4567_, lean_object* v_a_4568_){
_start:
{
lean_object* v_res_4569_; 
v_res_4569_ = l_Lean_MVarId_byCasesDec(v_mvarId_4560_, v_p_4561_, v_dec_4562_, v_hName_4563_, v_a_4564_, v_a_4565_, v_a_4566_, v_a_4567_);
lean_dec(v_a_4567_);
lean_dec_ref(v_a_4566_);
lean_dec(v_a_4565_);
lean_dec_ref(v_a_4564_);
return v_res_4569_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4621_; lean_object* v___x_4622_; lean_object* v___x_4623_; 
v___x_4621_ = lean_unsigned_to_nat(4241171151u);
v___x_4622_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_));
v___x_4623_ = l_Lean_Name_num___override(v___x_4622_, v___x_4621_);
return v___x_4623_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4625_; lean_object* v___x_4626_; lean_object* v___x_4627_; 
v___x_4625_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_));
v___x_4626_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_);
v___x_4627_ = l_Lean_Name_str___override(v___x_4626_, v___x_4625_);
return v___x_4627_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4629_; lean_object* v___x_4630_; lean_object* v___x_4631_; 
v___x_4629_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_));
v___x_4630_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_);
v___x_4631_ = l_Lean_Name_str___override(v___x_4630_, v___x_4629_);
return v___x_4631_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4632_; lean_object* v___x_4633_; lean_object* v___x_4634_; 
v___x_4632_ = lean_unsigned_to_nat(2u);
v___x_4633_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_);
v___x_4634_ = l_Lean_Name_num___override(v___x_4633_, v___x_4632_);
return v___x_4634_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4636_; uint8_t v___x_4637_; lean_object* v___x_4638_; lean_object* v___x_4639_; 
v___x_4636_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_));
v___x_4637_ = 0;
v___x_4638_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_);
v___x_4639_ = l_Lean_registerTraceClass(v___x_4636_, v___x_4637_, v___x_4638_);
return v___x_4639_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2____boxed(lean_object* v_a_4640_){
_start:
{
lean_object* v_res_4641_; 
v_res_4641_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_();
return v_res_4641_;
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
