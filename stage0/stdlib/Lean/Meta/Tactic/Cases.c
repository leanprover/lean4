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
lean_inc_n(v_a_984_, 2);
lean_dec_ref(v___x_983_);
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
lean_inc_n(v_mvarId_1043_, 2);
lean_inc_ref(v_targets_1045_);
v___f_1051_ = lean_alloc_closure((void*)(l_Lean_Meta_generalizeTargetsEq___lam__1___boxed), 9, 2);
lean_closure_set(v___f_1051_, 0, v_targets_1045_);
lean_closure_set(v___f_1051_, 1, v_mvarId_1043_);
v___x_1052_ = ((lean_object*)(l_Lean_Meta_generalizeTargetsEq___closed__1));
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
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__0(lean_object* v_mvarId_1129_, lean_object* v_newEqs_1130_, uint8_t v___x_1131_, lean_object* v_h_x27_1132_, lean_object* v_newIndices_1133_, lean_object* v___x_1134_, lean_object* v___x_1135_, lean_object* v___x_1136_, lean_object* v___x_1137_, lean_object* v_e_1138_, lean_object* v___x_1139_, lean_object* v_newEq_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_){
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
v___x_1163_ = l_Lean_Meta_mkFreshExprMVarAt(v___x_1134_, v___x_1135_, v_a_1161_, v___x_1162_, v_a_1149_, v___x_1136_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_);
if (lean_obj_tag(v___x_1163_) == 0)
{
lean_object* v_a_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; 
v_a_1164_ = lean_ctor_get(v___x_1163_, 0);
lean_inc_n(v_a_1164_, 2);
lean_dec_ref(v___x_1163_);
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
lean_dec_ref(v___x_1135_);
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
lean_dec_ref(v___x_1135_);
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
lean_dec_ref(v___x_1135_);
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
lean_dec_ref(v___x_1135_);
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
lean_dec_ref(v___x_1135_);
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
lean_object* v___x_1259_ = _args[6];
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
uint8_t v___x_6258__boxed_1270_; lean_object* v_res_1271_; 
v___x_6258__boxed_1270_ = lean_unbox(v___x_1255_);
v_res_1271_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__0(v_mvarId_1253_, v_newEqs_1254_, v___x_6258__boxed_1270_, v_h_x27_1256_, v_newIndices_1257_, v___x_1258_, v___x_1259_, v___x_1260_, v___x_1261_, v_e_1262_, v___x_1263_, v_newEq_1264_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_);
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
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__1(lean_object* v_e_1272_, lean_object* v_h_x27_1273_, lean_object* v_mvarId_1274_, uint8_t v___x_1275_, lean_object* v_newIndices_1276_, lean_object* v___x_1277_, lean_object* v___x_1278_, lean_object* v___x_1279_, lean_object* v___x_1280_, lean_object* v_newEqs_1281_, lean_object* v_newRefls_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_){
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
lean_closure_set(v___f_1294_, 6, v___x_1278_);
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
lean_dec_ref(v___x_1278_);
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
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__1___boxed(lean_object* v_e_1305_, lean_object* v_h_x27_1306_, lean_object* v_mvarId_1307_, lean_object* v___x_1308_, lean_object* v_newIndices_1309_, lean_object* v___x_1310_, lean_object* v___x_1311_, lean_object* v___x_1312_, lean_object* v___x_1313_, lean_object* v_newEqs_1314_, lean_object* v_newRefls_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_){
_start:
{
uint8_t v___x_6510__boxed_1321_; lean_object* v_res_1322_; 
v___x_6510__boxed_1321_ = lean_unbox(v___x_1308_);
v_res_1322_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__1(v_e_1305_, v_h_x27_1306_, v_mvarId_1307_, v___x_6510__boxed_1321_, v_newIndices_1309_, v___x_1310_, v___x_1311_, v___x_1312_, v___x_1313_, v_newEqs_1314_, v_newRefls_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_);
lean_dec(v___y_1319_);
lean_dec_ref(v___y_1318_);
lean_dec(v___y_1317_);
lean_dec_ref(v___y_1316_);
return v_res_1322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__2(lean_object* v_e_1323_, lean_object* v_mvarId_1324_, uint8_t v___x_1325_, lean_object* v_newIndices_1326_, lean_object* v___x_1327_, lean_object* v___x_1328_, lean_object* v___x_1329_, lean_object* v___x_1330_, lean_object* v_h_x27_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_){
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
lean_closure_set(v___f_1338_, 6, v___x_1328_);
lean_closure_set(v___f_1338_, 7, v___x_1329_);
lean_closure_set(v___f_1338_, 8, v___x_1330_);
v___x_1339_ = l_Lean_Meta_withNewEqs___redArg(v___x_1330_, v_newIndices_1326_, v___f_1338_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_);
return v___x_1339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__2___boxed(lean_object* v_e_1340_, lean_object* v_mvarId_1341_, lean_object* v___x_1342_, lean_object* v_newIndices_1343_, lean_object* v___x_1344_, lean_object* v___x_1345_, lean_object* v___x_1346_, lean_object* v___x_1347_, lean_object* v_h_x27_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_){
_start:
{
uint8_t v___x_6575__boxed_1354_; lean_object* v_res_1355_; 
v___x_6575__boxed_1354_ = lean_unbox(v___x_1342_);
v_res_1355_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__2(v_e_1340_, v_mvarId_1341_, v___x_6575__boxed_1354_, v_newIndices_1343_, v___x_1344_, v___x_1345_, v___x_1346_, v___x_1347_, v_h_x27_1348_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_);
lean_dec(v___y_1352_);
lean_dec_ref(v___y_1351_);
lean_dec(v___y_1350_);
lean_dec_ref(v___y_1349_);
return v_res_1355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__3(lean_object* v_e_1359_, lean_object* v_mvarId_1360_, uint8_t v___x_1361_, lean_object* v___x_1362_, lean_object* v___x_1363_, lean_object* v___x_1364_, lean_object* v___x_1365_, lean_object* v___x_1366_, lean_object* v_varName_x3f_1367_, lean_object* v_newIndices_1368_, lean_object* v_x_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_){
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
lean_closure_set(v___f_1376_, 5, v___x_1363_);
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
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__3___boxed(lean_object* v_e_1392_, lean_object* v_mvarId_1393_, lean_object* v___x_1394_, lean_object* v___x_1395_, lean_object* v___x_1396_, lean_object* v___x_1397_, lean_object* v___x_1398_, lean_object* v___x_1399_, lean_object* v_varName_x3f_1400_, lean_object* v_newIndices_1401_, lean_object* v_x_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_){
_start:
{
uint8_t v___x_6617__boxed_1408_; lean_object* v_res_1409_; 
v___x_6617__boxed_1408_ = lean_unbox(v___x_1394_);
v_res_1409_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__3(v_e_1392_, v_mvarId_1393_, v___x_6617__boxed_1408_, v___x_1395_, v___x_1396_, v___x_1397_, v___x_1398_, v___x_1399_, v_varName_x3f_1400_, v_newIndices_1401_, v_x_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_);
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
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0(lean_object* v_mvarId_1434_, lean_object* v_e_1435_, lean_object* v___x_1436_, lean_object* v___x_1437_, lean_object* v_varName_x3f_1438_, lean_object* v_x_1439_, lean_object* v_x_1440_, lean_object* v_x_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_){
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
lean_dec_ref(v___x_1437_);
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
lean_dec_ref(v___x_1437_);
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
lean_closure_set(v___f_1484_, 4, v___x_1437_);
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
lean_dec_ref(v___x_1437_);
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
lean_dec_ref(v___x_1437_);
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
lean_dec_ref(v___x_1437_);
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
lean_dec_ref(v___x_1437_);
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
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___boxed(lean_object* v_mvarId_1524_, lean_object* v_e_1525_, lean_object* v___x_1526_, lean_object* v___x_1527_, lean_object* v_varName_x3f_1528_, lean_object* v_x_1529_, lean_object* v_x_1530_, lean_object* v_x_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_){
_start:
{
lean_object* v_res_1537_; 
v_res_1537_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0(v_mvarId_1524_, v_e_1525_, v___x_1526_, v___x_1527_, v_varName_x3f_1528_, v_x_1529_, v_x_1530_, v_x_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_);
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
lean_object* v___x_1546_; lean_object* v___x_1547_; 
v___x_1546_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__1));
lean_inc(v_mvarId_1538_);
v___x_1547_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_1538_, v___x_1546_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_);
if (lean_obj_tag(v___x_1547_) == 0)
{
lean_object* v_lctx_1548_; lean_object* v_localInstances_1549_; lean_object* v___x_1550_; 
lean_dec_ref(v___x_1547_);
v_lctx_1548_ = lean_ctor_get(v___y_1541_, 2);
lean_inc_ref(v_lctx_1548_);
v_localInstances_1549_ = lean_ctor_get(v___y_1541_, 3);
lean_inc_ref(v_localInstances_1549_);
lean_inc(v___y_1544_);
lean_inc_ref(v___y_1543_);
lean_inc(v___y_1542_);
lean_inc_ref(v___y_1541_);
lean_inc_ref(v_e_1539_);
v___x_1550_ = lean_infer_type(v_e_1539_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_);
if (lean_obj_tag(v___x_1550_) == 0)
{
lean_object* v_a_1551_; lean_object* v___x_1552_; 
v_a_1551_ = lean_ctor_get(v___x_1550_, 0);
lean_inc(v_a_1551_);
lean_dec_ref(v___x_1550_);
v___x_1552_ = l_Lean_Meta_whnfD(v_a_1551_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_);
if (lean_obj_tag(v___x_1552_) == 0)
{
lean_object* v_a_1553_; lean_object* v_dummy_1554_; lean_object* v_nargs_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; 
v_a_1553_ = lean_ctor_get(v___x_1552_, 0);
lean_inc(v_a_1553_);
lean_dec_ref(v___x_1552_);
v_dummy_1554_ = lean_obj_once(&l_Lean_Meta_getInductiveUniverseAndParams___closed__0, &l_Lean_Meta_getInductiveUniverseAndParams___closed__0_once, _init_l_Lean_Meta_getInductiveUniverseAndParams___closed__0);
v_nargs_1555_ = l_Lean_Expr_getAppNumArgs(v_a_1553_);
lean_inc(v_nargs_1555_);
v___x_1556_ = lean_mk_array(v_nargs_1555_, v_dummy_1554_);
v___x_1557_ = lean_unsigned_to_nat(1u);
v___x_1558_ = lean_nat_sub(v_nargs_1555_, v___x_1557_);
lean_dec(v_nargs_1555_);
v___x_1559_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0(v_mvarId_1538_, v_e_1539_, v_lctx_1548_, v_localInstances_1549_, v_varName_x3f_1540_, v_a_1553_, v___x_1556_, v___x_1558_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_);
lean_dec(v___y_1544_);
lean_dec_ref(v___y_1543_);
lean_dec(v___y_1542_);
lean_dec_ref(v___y_1541_);
return v___x_1559_;
}
else
{
lean_object* v_a_1560_; lean_object* v___x_1562_; uint8_t v_isShared_1563_; uint8_t v_isSharedCheck_1567_; 
lean_dec_ref(v_localInstances_1549_);
lean_dec_ref(v_lctx_1548_);
lean_dec(v___y_1544_);
lean_dec_ref(v___y_1543_);
lean_dec(v___y_1542_);
lean_dec_ref(v___y_1541_);
lean_dec(v_varName_x3f_1540_);
lean_dec_ref(v_e_1539_);
lean_dec(v_mvarId_1538_);
v_a_1560_ = lean_ctor_get(v___x_1552_, 0);
v_isSharedCheck_1567_ = !lean_is_exclusive(v___x_1552_);
if (v_isSharedCheck_1567_ == 0)
{
v___x_1562_ = v___x_1552_;
v_isShared_1563_ = v_isSharedCheck_1567_;
goto v_resetjp_1561_;
}
else
{
lean_inc(v_a_1560_);
lean_dec(v___x_1552_);
v___x_1562_ = lean_box(0);
v_isShared_1563_ = v_isSharedCheck_1567_;
goto v_resetjp_1561_;
}
v_resetjp_1561_:
{
lean_object* v___x_1565_; 
if (v_isShared_1563_ == 0)
{
v___x_1565_ = v___x_1562_;
goto v_reusejp_1564_;
}
else
{
lean_object* v_reuseFailAlloc_1566_; 
v_reuseFailAlloc_1566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1566_, 0, v_a_1560_);
v___x_1565_ = v_reuseFailAlloc_1566_;
goto v_reusejp_1564_;
}
v_reusejp_1564_:
{
return v___x_1565_;
}
}
}
}
else
{
lean_object* v_a_1568_; lean_object* v___x_1570_; uint8_t v_isShared_1571_; uint8_t v_isSharedCheck_1575_; 
lean_dec_ref(v_localInstances_1549_);
lean_dec_ref(v_lctx_1548_);
lean_dec(v___y_1544_);
lean_dec_ref(v___y_1543_);
lean_dec(v___y_1542_);
lean_dec_ref(v___y_1541_);
lean_dec(v_varName_x3f_1540_);
lean_dec_ref(v_e_1539_);
lean_dec(v_mvarId_1538_);
v_a_1568_ = lean_ctor_get(v___x_1550_, 0);
v_isSharedCheck_1575_ = !lean_is_exclusive(v___x_1550_);
if (v_isSharedCheck_1575_ == 0)
{
v___x_1570_ = v___x_1550_;
v_isShared_1571_ = v_isSharedCheck_1575_;
goto v_resetjp_1569_;
}
else
{
lean_inc(v_a_1568_);
lean_dec(v___x_1550_);
v___x_1570_ = lean_box(0);
v_isShared_1571_ = v_isSharedCheck_1575_;
goto v_resetjp_1569_;
}
v_resetjp_1569_:
{
lean_object* v___x_1573_; 
if (v_isShared_1571_ == 0)
{
v___x_1573_ = v___x_1570_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1574_; 
v_reuseFailAlloc_1574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1574_, 0, v_a_1568_);
v___x_1573_ = v_reuseFailAlloc_1574_;
goto v_reusejp_1572_;
}
v_reusejp_1572_:
{
return v___x_1573_;
}
}
}
}
else
{
lean_object* v_a_1576_; lean_object* v___x_1578_; uint8_t v_isShared_1579_; uint8_t v_isSharedCheck_1583_; 
lean_dec(v___y_1544_);
lean_dec_ref(v___y_1543_);
lean_dec(v___y_1542_);
lean_dec_ref(v___y_1541_);
lean_dec(v_varName_x3f_1540_);
lean_dec_ref(v_e_1539_);
lean_dec(v_mvarId_1538_);
v_a_1576_ = lean_ctor_get(v___x_1547_, 0);
v_isSharedCheck_1583_ = !lean_is_exclusive(v___x_1547_);
if (v_isSharedCheck_1583_ == 0)
{
v___x_1578_ = v___x_1547_;
v_isShared_1579_ = v_isSharedCheck_1583_;
goto v_resetjp_1577_;
}
else
{
lean_inc(v_a_1576_);
lean_dec(v___x_1547_);
v___x_1578_ = lean_box(0);
v_isShared_1579_ = v_isSharedCheck_1583_;
goto v_resetjp_1577_;
}
v_resetjp_1577_:
{
lean_object* v___x_1581_; 
if (v_isShared_1579_ == 0)
{
v___x_1581_ = v___x_1578_;
goto v_reusejp_1580_;
}
else
{
lean_object* v_reuseFailAlloc_1582_; 
v_reuseFailAlloc_1582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1582_, 0, v_a_1576_);
v___x_1581_ = v_reuseFailAlloc_1582_;
goto v_reusejp_1580_;
}
v_reusejp_1580_:
{
return v___x_1581_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeIndices_x27___lam__0___boxed(lean_object* v_mvarId_1584_, lean_object* v_e_1585_, lean_object* v_varName_x3f_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_){
_start:
{
lean_object* v_res_1592_; 
v_res_1592_ = l_Lean_Meta_generalizeIndices_x27___lam__0(v_mvarId_1584_, v_e_1585_, v_varName_x3f_1586_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_);
return v_res_1592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeIndices_x27(lean_object* v_mvarId_1593_, lean_object* v_e_1594_, lean_object* v_varName_x3f_1595_, lean_object* v_a_1596_, lean_object* v_a_1597_, lean_object* v_a_1598_, lean_object* v_a_1599_){
_start:
{
lean_object* v___f_1601_; lean_object* v___x_1602_; 
lean_inc(v_mvarId_1593_);
v___f_1601_ = lean_alloc_closure((void*)(l_Lean_Meta_generalizeIndices_x27___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1601_, 0, v_mvarId_1593_);
lean_closure_set(v___f_1601_, 1, v_e_1594_);
lean_closure_set(v___f_1601_, 2, v_varName_x3f_1595_);
v___x_1602_ = l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2___redArg(v_mvarId_1593_, v___f_1601_, v_a_1596_, v_a_1597_, v_a_1598_, v_a_1599_);
return v___x_1602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeIndices_x27___boxed(lean_object* v_mvarId_1603_, lean_object* v_e_1604_, lean_object* v_varName_x3f_1605_, lean_object* v_a_1606_, lean_object* v_a_1607_, lean_object* v_a_1608_, lean_object* v_a_1609_, lean_object* v_a_1610_){
_start:
{
lean_object* v_res_1611_; 
v_res_1611_ = l_Lean_Meta_generalizeIndices_x27(v_mvarId_1603_, v_e_1604_, v_varName_x3f_1605_, v_a_1606_, v_a_1607_, v_a_1608_, v_a_1609_);
lean_dec(v_a_1609_);
lean_dec_ref(v_a_1608_);
lean_dec(v_a_1607_);
lean_dec_ref(v_a_1606_);
return v_res_1611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeIndices___lam__0(lean_object* v_fvarId_1612_, lean_object* v_mvarId_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_){
_start:
{
lean_object* v___x_1619_; 
v___x_1619_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_1612_, v___y_1614_, v___y_1616_, v___y_1617_);
if (lean_obj_tag(v___x_1619_) == 0)
{
lean_object* v_a_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; 
v_a_1620_ = lean_ctor_get(v___x_1619_, 0);
lean_inc_n(v_a_1620_, 2);
lean_dec_ref(v___x_1619_);
v___x_1621_ = l_Lean_LocalDecl_toExpr(v_a_1620_);
v___x_1622_ = l_Lean_LocalDecl_userName(v_a_1620_);
lean_dec(v_a_1620_);
v___x_1623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1623_, 0, v___x_1622_);
v___x_1624_ = l_Lean_Meta_generalizeIndices_x27(v_mvarId_1613_, v___x_1621_, v___x_1623_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_);
return v___x_1624_;
}
else
{
lean_object* v_a_1625_; lean_object* v___x_1627_; uint8_t v_isShared_1628_; uint8_t v_isSharedCheck_1632_; 
lean_dec(v_mvarId_1613_);
v_a_1625_ = lean_ctor_get(v___x_1619_, 0);
v_isSharedCheck_1632_ = !lean_is_exclusive(v___x_1619_);
if (v_isSharedCheck_1632_ == 0)
{
v___x_1627_ = v___x_1619_;
v_isShared_1628_ = v_isSharedCheck_1632_;
goto v_resetjp_1626_;
}
else
{
lean_inc(v_a_1625_);
lean_dec(v___x_1619_);
v___x_1627_ = lean_box(0);
v_isShared_1628_ = v_isSharedCheck_1632_;
goto v_resetjp_1626_;
}
v_resetjp_1626_:
{
lean_object* v___x_1630_; 
if (v_isShared_1628_ == 0)
{
v___x_1630_ = v___x_1627_;
goto v_reusejp_1629_;
}
else
{
lean_object* v_reuseFailAlloc_1631_; 
v_reuseFailAlloc_1631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1631_, 0, v_a_1625_);
v___x_1630_ = v_reuseFailAlloc_1631_;
goto v_reusejp_1629_;
}
v_reusejp_1629_:
{
return v___x_1630_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeIndices___lam__0___boxed(lean_object* v_fvarId_1633_, lean_object* v_mvarId_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_){
_start:
{
lean_object* v_res_1640_; 
v_res_1640_ = l_Lean_Meta_generalizeIndices___lam__0(v_fvarId_1633_, v_mvarId_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_);
lean_dec(v___y_1638_);
lean_dec_ref(v___y_1637_);
lean_dec(v___y_1636_);
lean_dec_ref(v___y_1635_);
return v_res_1640_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeIndices(lean_object* v_mvarId_1641_, lean_object* v_fvarId_1642_, lean_object* v_a_1643_, lean_object* v_a_1644_, lean_object* v_a_1645_, lean_object* v_a_1646_){
_start:
{
lean_object* v___f_1648_; lean_object* v___x_1649_; 
lean_inc(v_mvarId_1641_);
v___f_1648_ = lean_alloc_closure((void*)(l_Lean_Meta_generalizeIndices___lam__0___boxed), 7, 2);
lean_closure_set(v___f_1648_, 0, v_fvarId_1642_);
lean_closure_set(v___f_1648_, 1, v_mvarId_1641_);
v___x_1649_ = l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2___redArg(v_mvarId_1641_, v___f_1648_, v_a_1643_, v_a_1644_, v_a_1645_, v_a_1646_);
return v___x_1649_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeIndices___boxed(lean_object* v_mvarId_1650_, lean_object* v_fvarId_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_, lean_object* v_a_1656_){
_start:
{
lean_object* v_res_1657_; 
v_res_1657_ = l_Lean_Meta_generalizeIndices(v_mvarId_1650_, v_fvarId_1651_, v_a_1652_, v_a_1653_, v_a_1654_, v_a_1655_);
lean_dec(v_a_1655_);
lean_dec_ref(v_a_1654_);
lean_dec(v_a_1653_);
lean_dec_ref(v_a_1652_);
return v_res_1657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0___redArg(lean_object* v___x_1659_, lean_object* v_a_1660_, lean_object* v_x_1661_, lean_object* v_x_1662_, lean_object* v_x_1663_, lean_object* v___y_1664_){
_start:
{
if (lean_obj_tag(v_x_1661_) == 5)
{
lean_object* v_fn_1669_; lean_object* v_arg_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; 
v_fn_1669_ = lean_ctor_get(v_x_1661_, 0);
lean_inc_ref(v_fn_1669_);
v_arg_1670_ = lean_ctor_get(v_x_1661_, 1);
lean_inc_ref(v_arg_1670_);
lean_dec_ref(v_x_1661_);
v___x_1671_ = lean_array_set(v_x_1662_, v_x_1663_, v_arg_1670_);
v___x_1672_ = lean_unsigned_to_nat(1u);
v___x_1673_ = lean_nat_sub(v_x_1663_, v___x_1672_);
lean_dec(v_x_1663_);
v_x_1661_ = v_fn_1669_;
v_x_1662_ = v___x_1671_;
v_x_1663_ = v___x_1673_;
goto _start;
}
else
{
lean_dec(v_x_1663_);
if (lean_obj_tag(v_x_1661_) == 4)
{
lean_object* v_declName_1675_; lean_object* v___x_1676_; lean_object* v_env_1677_; uint8_t v___x_1678_; lean_object* v___x_1679_; 
v_declName_1675_ = lean_ctor_get(v_x_1661_, 0);
v___x_1676_ = lean_st_ref_get(v___y_1664_);
v_env_1677_ = lean_ctor_get(v___x_1676_, 0);
lean_inc_ref(v_env_1677_);
lean_dec(v___x_1676_);
v___x_1678_ = 0;
lean_inc(v_declName_1675_);
v___x_1679_ = l_Lean_Environment_find_x3f(v_env_1677_, v_declName_1675_, v___x_1678_);
if (lean_obj_tag(v___x_1679_) == 0)
{
lean_dec_ref(v_x_1661_);
lean_dec_ref(v_x_1662_);
lean_dec_ref(v_a_1660_);
lean_dec_ref(v___x_1659_);
goto v___jp_1666_;
}
else
{
lean_object* v_val_1680_; lean_object* v___x_1682_; uint8_t v_isShared_1683_; uint8_t v_isSharedCheck_1718_; 
v_val_1680_ = lean_ctor_get(v___x_1679_, 0);
v_isSharedCheck_1718_ = !lean_is_exclusive(v___x_1679_);
if (v_isSharedCheck_1718_ == 0)
{
v___x_1682_ = v___x_1679_;
v_isShared_1683_ = v_isSharedCheck_1718_;
goto v_resetjp_1681_;
}
else
{
lean_inc(v_val_1680_);
lean_dec(v___x_1679_);
v___x_1682_ = lean_box(0);
v_isShared_1683_ = v_isSharedCheck_1718_;
goto v_resetjp_1681_;
}
v_resetjp_1681_:
{
if (lean_obj_tag(v_val_1680_) == 5)
{
lean_object* v_val_1684_; lean_object* v___x_1686_; uint8_t v_isShared_1687_; uint8_t v_isSharedCheck_1717_; 
v_val_1684_ = lean_ctor_get(v_val_1680_, 0);
v_isSharedCheck_1717_ = !lean_is_exclusive(v_val_1680_);
if (v_isSharedCheck_1717_ == 0)
{
v___x_1686_ = v_val_1680_;
v_isShared_1687_ = v_isSharedCheck_1717_;
goto v_resetjp_1685_;
}
else
{
lean_inc(v_val_1684_);
lean_dec(v_val_1680_);
v___x_1686_ = lean_box(0);
v_isShared_1687_ = v_isSharedCheck_1717_;
goto v_resetjp_1685_;
}
v_resetjp_1685_:
{
lean_object* v_toConstantVal_1688_; lean_object* v_numParams_1689_; lean_object* v_numIndices_1690_; lean_object* v_ctors_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; uint8_t v___x_1694_; 
v_toConstantVal_1688_ = lean_ctor_get(v_val_1684_, 0);
v_numParams_1689_ = lean_ctor_get(v_val_1684_, 1);
v_numIndices_1690_ = lean_ctor_get(v_val_1684_, 2);
v_ctors_1691_ = lean_ctor_get(v_val_1684_, 4);
v___x_1692_ = lean_array_get_size(v_x_1662_);
v___x_1693_ = lean_nat_add(v_numIndices_1690_, v_numParams_1689_);
v___x_1694_ = lean_nat_dec_eq(v___x_1692_, v___x_1693_);
lean_dec(v___x_1693_);
if (v___x_1694_ == 0)
{
lean_object* v___x_1695_; lean_object* v___x_1697_; 
lean_dec_ref(v_val_1684_);
lean_del_object(v___x_1682_);
lean_dec_ref(v_x_1661_);
lean_dec_ref(v_x_1662_);
lean_dec_ref(v_a_1660_);
lean_dec_ref(v___x_1659_);
v___x_1695_ = lean_box(0);
if (v_isShared_1687_ == 0)
{
lean_ctor_set_tag(v___x_1686_, 0);
lean_ctor_set(v___x_1686_, 0, v___x_1695_);
v___x_1697_ = v___x_1686_;
goto v_reusejp_1696_;
}
else
{
lean_object* v_reuseFailAlloc_1698_; 
v_reuseFailAlloc_1698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1698_, 0, v___x_1695_);
v___x_1697_ = v_reuseFailAlloc_1698_;
goto v_reusejp_1696_;
}
v_reusejp_1696_:
{
return v___x_1697_;
}
}
else
{
lean_object* v_name_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; uint8_t v___x_1702_; 
v_name_1699_ = lean_ctor_get(v_toConstantVal_1688_, 0);
v___x_1700_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0___redArg___closed__0));
lean_inc(v_name_1699_);
v___x_1701_ = l_Lean_Name_str___override(v_name_1699_, v___x_1700_);
v___x_1702_ = l_Lean_Environment_contains(v___x_1659_, v___x_1701_, v___x_1694_);
if (v___x_1702_ == 0)
{
lean_object* v___x_1703_; lean_object* v___x_1705_; 
lean_dec_ref(v_val_1684_);
lean_del_object(v___x_1682_);
lean_dec_ref(v_x_1661_);
lean_dec_ref(v_x_1662_);
lean_dec_ref(v_a_1660_);
v___x_1703_ = lean_box(0);
if (v_isShared_1687_ == 0)
{
lean_ctor_set_tag(v___x_1686_, 0);
lean_ctor_set(v___x_1686_, 0, v___x_1703_);
v___x_1705_ = v___x_1686_;
goto v_reusejp_1704_;
}
else
{
lean_object* v_reuseFailAlloc_1706_; 
v_reuseFailAlloc_1706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1706_, 0, v___x_1703_);
v___x_1705_ = v_reuseFailAlloc_1706_;
goto v_reusejp_1704_;
}
v_reusejp_1704_:
{
return v___x_1705_;
}
}
else
{
lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1712_; 
v___x_1707_ = l_List_lengthTR___redArg(v_ctors_1691_);
v___x_1708_ = lean_nat_sub(v___x_1692_, v_numIndices_1690_);
v___x_1709_ = l_Array_extract___redArg(v_x_1662_, v___x_1708_, v___x_1692_);
v___x_1710_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1710_, 0, v_val_1684_);
lean_ctor_set(v___x_1710_, 1, v___x_1707_);
lean_ctor_set(v___x_1710_, 2, v_a_1660_);
lean_ctor_set(v___x_1710_, 3, v_x_1661_);
lean_ctor_set(v___x_1710_, 4, v_x_1662_);
lean_ctor_set(v___x_1710_, 5, v___x_1709_);
if (v_isShared_1683_ == 0)
{
lean_ctor_set(v___x_1682_, 0, v___x_1710_);
v___x_1712_ = v___x_1682_;
goto v_reusejp_1711_;
}
else
{
lean_object* v_reuseFailAlloc_1716_; 
v_reuseFailAlloc_1716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1716_, 0, v___x_1710_);
v___x_1712_ = v_reuseFailAlloc_1716_;
goto v_reusejp_1711_;
}
v_reusejp_1711_:
{
lean_object* v___x_1714_; 
if (v_isShared_1687_ == 0)
{
lean_ctor_set_tag(v___x_1686_, 0);
lean_ctor_set(v___x_1686_, 0, v___x_1712_);
v___x_1714_ = v___x_1686_;
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
}
}
}
}
else
{
lean_del_object(v___x_1682_);
lean_dec(v_val_1680_);
lean_dec_ref(v_x_1661_);
lean_dec_ref(v_x_1662_);
lean_dec_ref(v_a_1660_);
lean_dec_ref(v___x_1659_);
goto v___jp_1666_;
}
}
}
}
else
{
lean_dec_ref(v_x_1662_);
lean_dec_ref(v_x_1661_);
lean_dec_ref(v_a_1660_);
lean_dec_ref(v___x_1659_);
goto v___jp_1666_;
}
}
v___jp_1666_:
{
lean_object* v___x_1667_; lean_object* v___x_1668_; 
v___x_1667_ = lean_box(0);
v___x_1668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1668_, 0, v___x_1667_);
return v___x_1668_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0___redArg___boxed(lean_object* v___x_1719_, lean_object* v_a_1720_, lean_object* v_x_1721_, lean_object* v_x_1722_, lean_object* v_x_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_){
_start:
{
lean_object* v_res_1726_; 
v_res_1726_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0___redArg(v___x_1719_, v_a_1720_, v_x_1721_, v_x_1722_, v_x_1723_, v___y_1724_);
lean_dec(v___y_1724_);
return v_res_1726_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f(lean_object* v_majorFVarId_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_){
_start:
{
lean_object* v___x_1733_; lean_object* v_env_1737_; lean_object* v___x_1738_; uint8_t v___x_1739_; uint8_t v___x_1740_; 
v___x_1733_ = lean_st_ref_get(v_a_1731_);
v_env_1737_ = lean_ctor_get(v___x_1733_, 0);
lean_inc_ref_n(v_env_1737_, 2);
lean_dec(v___x_1733_);
v___x_1738_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__5));
v___x_1739_ = 1;
v___x_1740_ = l_Lean_Environment_contains(v_env_1737_, v___x_1738_, v___x_1739_);
if (v___x_1740_ == 0)
{
lean_dec_ref(v_env_1737_);
lean_dec(v_majorFVarId_1727_);
goto v___jp_1734_;
}
else
{
lean_object* v___x_1741_; uint8_t v___x_1742_; 
v___x_1741_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__1));
lean_inc_ref(v_env_1737_);
v___x_1742_ = l_Lean_Environment_contains(v_env_1737_, v___x_1741_, v___x_1740_);
if (v___x_1742_ == 0)
{
lean_dec_ref(v_env_1737_);
lean_dec(v_majorFVarId_1727_);
goto v___jp_1734_;
}
else
{
lean_object* v___x_1743_; 
v___x_1743_ = l_Lean_FVarId_getDecl___redArg(v_majorFVarId_1727_, v_a_1728_, v_a_1730_, v_a_1731_);
if (lean_obj_tag(v___x_1743_) == 0)
{
lean_object* v_a_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; 
v_a_1744_ = lean_ctor_get(v___x_1743_, 0);
lean_inc(v_a_1744_);
lean_dec_ref(v___x_1743_);
v___x_1745_ = l_Lean_LocalDecl_type(v_a_1744_);
lean_inc(v_a_1731_);
lean_inc_ref(v_a_1730_);
lean_inc(v_a_1729_);
lean_inc_ref(v_a_1728_);
v___x_1746_ = lean_whnf(v___x_1745_, v_a_1728_, v_a_1729_, v_a_1730_, v_a_1731_);
if (lean_obj_tag(v___x_1746_) == 0)
{
lean_object* v_a_1747_; lean_object* v_dummy_1748_; lean_object* v_nargs_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; 
v_a_1747_ = lean_ctor_get(v___x_1746_, 0);
lean_inc(v_a_1747_);
lean_dec_ref(v___x_1746_);
v_dummy_1748_ = lean_obj_once(&l_Lean_Meta_getInductiveUniverseAndParams___closed__0, &l_Lean_Meta_getInductiveUniverseAndParams___closed__0_once, _init_l_Lean_Meta_getInductiveUniverseAndParams___closed__0);
v_nargs_1749_ = l_Lean_Expr_getAppNumArgs(v_a_1747_);
lean_inc(v_nargs_1749_);
v___x_1750_ = lean_mk_array(v_nargs_1749_, v_dummy_1748_);
v___x_1751_ = lean_unsigned_to_nat(1u);
v___x_1752_ = lean_nat_sub(v_nargs_1749_, v___x_1751_);
lean_dec(v_nargs_1749_);
v___x_1753_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0___redArg(v_env_1737_, v_a_1744_, v_a_1747_, v___x_1750_, v___x_1752_, v_a_1731_);
return v___x_1753_;
}
else
{
lean_object* v_a_1754_; lean_object* v___x_1756_; uint8_t v_isShared_1757_; uint8_t v_isSharedCheck_1761_; 
lean_dec(v_a_1744_);
lean_dec_ref(v_env_1737_);
v_a_1754_ = lean_ctor_get(v___x_1746_, 0);
v_isSharedCheck_1761_ = !lean_is_exclusive(v___x_1746_);
if (v_isSharedCheck_1761_ == 0)
{
v___x_1756_ = v___x_1746_;
v_isShared_1757_ = v_isSharedCheck_1761_;
goto v_resetjp_1755_;
}
else
{
lean_inc(v_a_1754_);
lean_dec(v___x_1746_);
v___x_1756_ = lean_box(0);
v_isShared_1757_ = v_isSharedCheck_1761_;
goto v_resetjp_1755_;
}
v_resetjp_1755_:
{
lean_object* v___x_1759_; 
if (v_isShared_1757_ == 0)
{
v___x_1759_ = v___x_1756_;
goto v_reusejp_1758_;
}
else
{
lean_object* v_reuseFailAlloc_1760_; 
v_reuseFailAlloc_1760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1760_, 0, v_a_1754_);
v___x_1759_ = v_reuseFailAlloc_1760_;
goto v_reusejp_1758_;
}
v_reusejp_1758_:
{
return v___x_1759_;
}
}
}
}
else
{
lean_object* v_a_1762_; lean_object* v___x_1764_; uint8_t v_isShared_1765_; uint8_t v_isSharedCheck_1769_; 
lean_dec_ref(v_env_1737_);
v_a_1762_ = lean_ctor_get(v___x_1743_, 0);
v_isSharedCheck_1769_ = !lean_is_exclusive(v___x_1743_);
if (v_isSharedCheck_1769_ == 0)
{
v___x_1764_ = v___x_1743_;
v_isShared_1765_ = v_isSharedCheck_1769_;
goto v_resetjp_1763_;
}
else
{
lean_inc(v_a_1762_);
lean_dec(v___x_1743_);
v___x_1764_ = lean_box(0);
v_isShared_1765_ = v_isSharedCheck_1769_;
goto v_resetjp_1763_;
}
v_resetjp_1763_:
{
lean_object* v___x_1767_; 
if (v_isShared_1765_ == 0)
{
v___x_1767_ = v___x_1764_;
goto v_reusejp_1766_;
}
else
{
lean_object* v_reuseFailAlloc_1768_; 
v_reuseFailAlloc_1768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1768_, 0, v_a_1762_);
v___x_1767_ = v_reuseFailAlloc_1768_;
goto v_reusejp_1766_;
}
v_reusejp_1766_:
{
return v___x_1767_;
}
}
}
}
}
v___jp_1734_:
{
lean_object* v___x_1735_; lean_object* v___x_1736_; 
v___x_1735_ = lean_box(0);
v___x_1736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1736_, 0, v___x_1735_);
return v___x_1736_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f___boxed(lean_object* v_majorFVarId_1770_, lean_object* v_a_1771_, lean_object* v_a_1772_, lean_object* v_a_1773_, lean_object* v_a_1774_, lean_object* v_a_1775_){
_start:
{
lean_object* v_res_1776_; 
v_res_1776_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f(v_majorFVarId_1770_, v_a_1771_, v_a_1772_, v_a_1773_, v_a_1774_);
lean_dec(v_a_1774_);
lean_dec_ref(v_a_1773_);
lean_dec(v_a_1772_);
lean_dec_ref(v_a_1771_);
return v_res_1776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0(lean_object* v___x_1777_, lean_object* v_a_1778_, lean_object* v_x_1779_, lean_object* v_x_1780_, lean_object* v_x_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_){
_start:
{
lean_object* v___x_1787_; 
v___x_1787_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0___redArg(v___x_1777_, v_a_1778_, v_x_1779_, v_x_1780_, v_x_1781_, v___y_1785_);
return v___x_1787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0___boxed(lean_object* v___x_1788_, lean_object* v_a_1789_, lean_object* v_x_1790_, lean_object* v_x_1791_, lean_object* v_x_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_){
_start:
{
lean_object* v_res_1798_; 
v_res_1798_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0(v___x_1788_, v_a_1789_, v_x_1790_, v_x_1791_, v_x_1792_, v___y_1793_, v___y_1794_, v___y_1795_, v___y_1796_);
lean_dec(v___y_1796_);
lean_dec_ref(v___y_1795_);
lean_dec(v___y_1794_);
lean_dec_ref(v___y_1793_);
return v_res_1798_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0___redArg(lean_object* v___x_1799_, lean_object* v_i_1800_, lean_object* v_n_1801_, lean_object* v_i_1802_){
_start:
{
lean_object* v_zero_1803_; uint8_t v_isZero_1804_; 
v_zero_1803_ = lean_unsigned_to_nat(0u);
v_isZero_1804_ = lean_nat_dec_eq(v_i_1802_, v_zero_1803_);
if (v_isZero_1804_ == 1)
{
uint8_t v___x_1805_; 
lean_dec(v_i_1802_);
v___x_1805_ = 0;
return v___x_1805_;
}
else
{
lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; uint8_t v___x_1809_; 
v___x_1806_ = lean_nat_sub(v_n_1801_, v_i_1802_);
v___x_1807_ = lean_array_fget_borrowed(v___x_1799_, v_i_1800_);
v___x_1808_ = lean_array_fget_borrowed(v___x_1799_, v___x_1806_);
lean_dec(v___x_1806_);
v___x_1809_ = lean_expr_eqv(v___x_1807_, v___x_1808_);
if (v___x_1809_ == 0)
{
lean_object* v_one_1810_; lean_object* v_n_1811_; 
v_one_1810_ = lean_unsigned_to_nat(1u);
v_n_1811_ = lean_nat_sub(v_i_1802_, v_one_1810_);
lean_dec(v_i_1802_);
v_i_1802_ = v_n_1811_;
goto _start;
}
else
{
lean_dec(v_i_1802_);
return v___x_1809_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0___redArg___boxed(lean_object* v___x_1813_, lean_object* v_i_1814_, lean_object* v_n_1815_, lean_object* v_i_1816_){
_start:
{
uint8_t v_res_1817_; lean_object* v_r_1818_; 
v_res_1817_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0___redArg(v___x_1813_, v_i_1814_, v_n_1815_, v_i_1816_);
lean_dec(v_n_1815_);
lean_dec(v_i_1814_);
lean_dec_ref(v___x_1813_);
v_r_1818_ = lean_box(v_res_1817_);
return v_r_1818_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1___redArg(lean_object* v___x_1819_, lean_object* v_n_1820_, lean_object* v_i_1821_){
_start:
{
lean_object* v_zero_1822_; uint8_t v_isZero_1823_; 
v_zero_1822_ = lean_unsigned_to_nat(0u);
v_isZero_1823_ = lean_nat_dec_eq(v_i_1821_, v_zero_1822_);
if (v_isZero_1823_ == 1)
{
uint8_t v___x_1824_; 
lean_dec(v_i_1821_);
v___x_1824_ = 0;
return v___x_1824_;
}
else
{
lean_object* v___x_1825_; uint8_t v___x_1826_; 
v___x_1825_ = lean_nat_sub(v_n_1820_, v_i_1821_);
lean_inc(v___x_1825_);
v___x_1826_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0___redArg(v___x_1819_, v___x_1825_, v___x_1825_, v___x_1825_);
lean_dec(v___x_1825_);
if (v___x_1826_ == 0)
{
lean_object* v_one_1827_; lean_object* v_n_1828_; 
v_one_1827_ = lean_unsigned_to_nat(1u);
v_n_1828_ = lean_nat_sub(v_i_1821_, v_one_1827_);
lean_dec(v_i_1821_);
v_i_1821_ = v_n_1828_;
goto _start;
}
else
{
lean_dec(v_i_1821_);
return v___x_1826_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1___redArg___boxed(lean_object* v___x_1830_, lean_object* v_n_1831_, lean_object* v_i_1832_){
_start:
{
uint8_t v_res_1833_; lean_object* v_r_1834_; 
v_res_1833_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1___redArg(v___x_1830_, v_n_1831_, v_i_1832_);
lean_dec(v_n_1831_);
lean_dec_ref(v___x_1830_);
v_r_1834_ = lean_box(v_res_1833_);
return v_r_1834_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5(lean_object* v___x_1835_, lean_object* v_as_1836_, size_t v_i_1837_, size_t v_stop_1838_){
_start:
{
uint8_t v___x_1839_; 
v___x_1839_ = lean_usize_dec_eq(v_i_1837_, v_stop_1838_);
if (v___x_1839_ == 0)
{
uint8_t v___x_1840_; lean_object* v___x_1841_; uint8_t v___x_1842_; 
v___x_1840_ = 1;
v___x_1841_ = lean_array_uget_borrowed(v_as_1836_, v_i_1837_);
v___x_1842_ = l_Lean_Expr_isFVar(v___x_1841_);
if (v___x_1842_ == 0)
{
return v___x_1840_;
}
else
{
lean_object* v___x_1843_; uint8_t v___x_1844_; 
v___x_1843_ = lean_unsigned_to_nat(0u);
v___x_1844_ = lean_nat_dec_eq(v___x_1835_, v___x_1843_);
if (v___x_1844_ == 0)
{
size_t v___x_1845_; size_t v___x_1846_; 
v___x_1845_ = ((size_t)1ULL);
v___x_1846_ = lean_usize_add(v_i_1837_, v___x_1845_);
v_i_1837_ = v___x_1846_;
goto _start;
}
else
{
return v___x_1840_;
}
}
}
else
{
uint8_t v___x_1848_; 
v___x_1848_ = 0;
return v___x_1848_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5___boxed(lean_object* v___x_1849_, lean_object* v_as_1850_, lean_object* v_i_1851_, lean_object* v_stop_1852_){
_start:
{
size_t v_i_boxed_1853_; size_t v_stop_boxed_1854_; uint8_t v_res_1855_; lean_object* v_r_1856_; 
v_i_boxed_1853_ = lean_unbox_usize(v_i_1851_);
lean_dec(v_i_1851_);
v_stop_boxed_1854_ = lean_unbox_usize(v_stop_1852_);
lean_dec(v_stop_1852_);
v_res_1855_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5(v___x_1849_, v_as_1850_, v_i_boxed_1853_, v_stop_boxed_1854_);
lean_dec_ref(v_as_1850_);
lean_dec(v___x_1849_);
v_r_1856_ = lean_box(v_res_1855_);
return v_r_1856_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__2(lean_object* v_fvarId_1857_, uint8_t v___y_1858_, lean_object* v_as_1859_, size_t v_i_1860_, size_t v_stop_1861_){
_start:
{
uint8_t v___x_1862_; 
v___x_1862_ = lean_usize_dec_eq(v_i_1860_, v_stop_1861_);
if (v___x_1862_ == 0)
{
uint8_t v___x_1863_; uint8_t v___y_1865_; lean_object* v___x_1869_; lean_object* v___x_1870_; uint8_t v___x_1871_; 
v___x_1863_ = 1;
v___x_1869_ = lean_array_uget_borrowed(v_as_1859_, v_i_1860_);
v___x_1870_ = l_Lean_Expr_fvarId_x21(v___x_1869_);
v___x_1871_ = l_Lean_instBEqFVarId_beq(v___x_1870_, v_fvarId_1857_);
lean_dec(v___x_1870_);
if (v___x_1871_ == 0)
{
v___y_1865_ = v___y_1858_;
goto v___jp_1864_;
}
else
{
v___y_1865_ = v___x_1871_;
goto v___jp_1864_;
}
v___jp_1864_:
{
if (v___y_1865_ == 0)
{
size_t v___x_1866_; size_t v___x_1867_; 
v___x_1866_ = ((size_t)1ULL);
v___x_1867_ = lean_usize_add(v_i_1860_, v___x_1866_);
v_i_1860_ = v___x_1867_;
goto _start;
}
else
{
return v___x_1863_;
}
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__2___boxed(lean_object* v_fvarId_1873_, lean_object* v___y_1874_, lean_object* v_as_1875_, lean_object* v_i_1876_, lean_object* v_stop_1877_){
_start:
{
uint8_t v___y_9117__boxed_1878_; size_t v_i_boxed_1879_; size_t v_stop_boxed_1880_; uint8_t v_res_1881_; lean_object* v_r_1882_; 
v___y_9117__boxed_1878_ = lean_unbox(v___y_1874_);
v_i_boxed_1879_ = lean_unbox_usize(v_i_1876_);
lean_dec(v_i_1876_);
v_stop_boxed_1880_ = lean_unbox_usize(v_stop_1877_);
lean_dec(v_stop_1877_);
v_res_1881_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__2(v_fvarId_1873_, v___y_9117__boxed_1878_, v_as_1875_, v_i_boxed_1879_, v_stop_boxed_1880_);
lean_dec_ref(v_as_1875_);
lean_dec(v_fvarId_1873_);
v_r_1882_ = lean_box(v_res_1881_);
return v_r_1882_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___lam__1(lean_object* v___x_1883_, lean_object* v___x_1884_, uint8_t v___x_1885_, uint8_t v___y_1886_, lean_object* v___x_1887_, lean_object* v_fvarId_1888_){
_start:
{
lean_object* v___y_1890_; uint8_t v___x_1895_; 
v___x_1895_ = lean_nat_dec_lt(v___x_1883_, v___x_1884_);
if (v___x_1895_ == 0)
{
lean_dec(v___x_1884_);
return v___x_1885_;
}
else
{
lean_object* v___x_1896_; uint8_t v___x_1897_; 
v___x_1896_ = lean_array_get_size(v___x_1887_);
v___x_1897_ = lean_nat_dec_le(v___x_1884_, v___x_1896_);
if (v___x_1897_ == 0)
{
lean_dec(v___x_1884_);
v___y_1890_ = v___x_1896_;
goto v___jp_1889_;
}
else
{
v___y_1890_ = v___x_1884_;
goto v___jp_1889_;
}
}
v___jp_1889_:
{
uint8_t v___x_1891_; 
v___x_1891_ = lean_nat_dec_lt(v___x_1883_, v___y_1890_);
if (v___x_1891_ == 0)
{
lean_dec(v___y_1890_);
return v___x_1885_;
}
else
{
size_t v___x_1892_; size_t v___x_1893_; uint8_t v___x_1894_; 
v___x_1892_ = ((size_t)0ULL);
v___x_1893_ = lean_usize_of_nat(v___y_1890_);
lean_dec(v___y_1890_);
v___x_1894_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__2(v_fvarId_1888_, v___y_1886_, v___x_1887_, v___x_1892_, v___x_1893_);
if (v___x_1894_ == 0)
{
return v___x_1885_;
}
else
{
return v___y_1886_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___lam__1___boxed(lean_object* v___x_1898_, lean_object* v___x_1899_, lean_object* v___x_1900_, lean_object* v___y_1901_, lean_object* v___x_1902_, lean_object* v_fvarId_1903_){
_start:
{
uint8_t v___x_9144__boxed_1904_; uint8_t v___y_9145__boxed_1905_; uint8_t v_res_1906_; lean_object* v_r_1907_; 
v___x_9144__boxed_1904_ = lean_unbox(v___x_1900_);
v___y_9145__boxed_1905_ = lean_unbox(v___y_1901_);
v_res_1906_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___lam__1(v___x_1898_, v___x_1899_, v___x_9144__boxed_1904_, v___y_9145__boxed_1905_, v___x_1902_, v_fvarId_1903_);
lean_dec(v_fvarId_1903_);
lean_dec_ref(v___x_1902_);
lean_dec(v___x_1898_);
v_r_1907_ = lean_box(v_res_1906_);
return v_r_1907_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__3(lean_object* v___x_1908_, lean_object* v_as_1909_, size_t v_i_1910_, size_t v_stop_1911_){
_start:
{
uint8_t v___x_1912_; 
v___x_1912_ = lean_usize_dec_eq(v_i_1910_, v_stop_1911_);
if (v___x_1912_ == 0)
{
lean_object* v___x_1913_; lean_object* v___x_1914_; uint8_t v___x_1915_; 
v___x_1913_ = lean_array_uget_borrowed(v_as_1909_, v_i_1910_);
v___x_1914_ = l_Lean_Expr_fvarId_x21(v___x_1913_);
v___x_1915_ = l_Lean_instBEqFVarId_beq(v___x_1908_, v___x_1914_);
lean_dec(v___x_1914_);
if (v___x_1915_ == 0)
{
size_t v___x_1916_; size_t v___x_1917_; 
v___x_1916_ = ((size_t)1ULL);
v___x_1917_ = lean_usize_add(v_i_1910_, v___x_1916_);
v_i_1910_ = v___x_1917_;
goto _start;
}
else
{
return v___x_1915_;
}
}
else
{
uint8_t v___x_1919_; 
v___x_1919_ = 0;
return v___x_1919_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__3___boxed(lean_object* v___x_1920_, lean_object* v_as_1921_, lean_object* v_i_1922_, lean_object* v_stop_1923_){
_start:
{
size_t v_i_boxed_1924_; size_t v_stop_boxed_1925_; uint8_t v_res_1926_; lean_object* v_r_1927_; 
v_i_boxed_1924_ = lean_unbox_usize(v_i_1922_);
lean_dec(v_i_1922_);
v_stop_boxed_1925_ = lean_unbox_usize(v_stop_1923_);
lean_dec(v_stop_1923_);
v_res_1926_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__3(v___x_1920_, v_as_1921_, v_i_boxed_1924_, v_stop_boxed_1925_);
lean_dec_ref(v_as_1921_);
lean_dec(v___x_1920_);
v_r_1927_ = lean_box(v_res_1926_);
return v_r_1927_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___lam__0(uint8_t v___y_1928_, lean_object* v_x_1929_){
_start:
{
return v___y_1928_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___lam__0___boxed(lean_object* v___y_1930_, lean_object* v_x_1931_){
_start:
{
uint8_t v___y_9194__boxed_1932_; uint8_t v_res_1933_; lean_object* v_r_1934_; 
v___y_9194__boxed_1932_ = lean_unbox(v___y_1930_);
v_res_1933_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___lam__0(v___y_9194__boxed_1932_, v_x_1931_);
lean_dec(v_x_1931_);
v_r_1934_ = lean_box(v_res_1933_);
return v_r_1934_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; 
v___x_1935_ = lean_box(0);
v___x_1936_ = lean_unsigned_to_nat(16u);
v___x_1937_ = lean_mk_array(v___x_1936_, v___x_1935_);
return v___x_1937_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; 
v___x_1938_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__0);
v___x_1939_ = lean_unsigned_to_nat(0u);
v___x_1940_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1940_, 0, v___x_1939_);
lean_ctor_set(v___x_1940_, 1, v___x_1938_);
return v___x_1940_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg(uint8_t v___x_1941_, lean_object* v___x_1942_, lean_object* v___x_1943_, lean_object* v_ctx_1944_, lean_object* v_as_1945_, size_t v_i_1946_, size_t v_stop_1947_, lean_object* v___y_1948_){
_start:
{
uint8_t v___x_1950_; 
v___x_1950_ = lean_usize_dec_eq(v_i_1946_, v_stop_1947_);
if (v___x_1950_ == 0)
{
uint8_t v___x_1951_; uint8_t v_a_1953_; uint8_t v_a_1960_; uint8_t v_fst_1964_; lean_object* v_mctx_1965_; lean_object* v___y_1981_; uint8_t v_fst_1987_; lean_object* v_snd_1988_; lean_object* v___y_2005_; lean_object* v___y_2010_; lean_object* v___y_2011_; lean_object* v___y_2012_; uint8_t v_fst_2013_; lean_object* v_snd_2014_; lean_object* v___y_2020_; lean_object* v___y_2021_; lean_object* v___y_2022_; lean_object* v___y_2023_; uint8_t v_fst_2028_; lean_object* v_mctx_2029_; lean_object* v___y_2045_; lean_object* v___x_2050_; 
v___x_1951_ = 1;
v___x_2050_ = lean_array_uget_borrowed(v_as_1945_, v_i_1946_);
if (lean_obj_tag(v___x_2050_) == 0)
{
v_a_1953_ = v___x_1941_;
goto v___jp_1952_;
}
else
{
lean_object* v_val_2051_; lean_object* v_majorDecl_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; uint8_t v___x_2055_; 
v_val_2051_ = lean_ctor_get(v___x_2050_, 0);
v_majorDecl_2052_ = lean_ctor_get(v_ctx_1944_, 2);
v___x_2053_ = l_Lean_LocalDecl_fvarId(v_val_2051_);
v___x_2054_ = l_Lean_LocalDecl_fvarId(v_majorDecl_2052_);
v___x_2055_ = l_Lean_instBEqFVarId_beq(v___x_2053_, v___x_2054_);
lean_dec(v___x_2054_);
if (v___x_2055_ == 0)
{
lean_object* v___x_2056_; uint8_t v___y_2058_; lean_object* v___y_2094_; uint8_t v___x_2099_; 
v___x_2056_ = lean_unsigned_to_nat(0u);
v___x_2099_ = lean_nat_dec_lt(v___x_2056_, v___x_1943_);
if (v___x_2099_ == 0)
{
lean_dec(v___x_2053_);
v___y_2058_ = v___x_2055_;
goto v___jp_2057_;
}
else
{
lean_object* v___x_2100_; uint8_t v___x_2101_; 
v___x_2100_ = lean_array_get_size(v___x_1942_);
v___x_2101_ = lean_nat_dec_le(v___x_1943_, v___x_2100_);
if (v___x_2101_ == 0)
{
v___y_2094_ = v___x_2100_;
goto v___jp_2093_;
}
else
{
lean_inc(v___x_1943_);
v___y_2094_ = v___x_1943_;
goto v___jp_2093_;
}
}
v___jp_2057_:
{
if (v___y_2058_ == 0)
{
lean_object* v___x_2059_; lean_object* v___f_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___f_2063_; 
v___x_2059_ = lean_box(v___y_2058_);
v___f_2060_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2060_, 0, v___x_2059_);
v___x_2061_ = lean_box(v___x_1951_);
v___x_2062_ = lean_box(v___y_2058_);
lean_inc_ref(v___x_1942_);
lean_inc(v___x_1943_);
v___f_2063_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_2063_, 0, v___x_2056_);
lean_closure_set(v___f_2063_, 1, v___x_1943_);
lean_closure_set(v___f_2063_, 2, v___x_2061_);
lean_closure_set(v___f_2063_, 3, v___x_2062_);
lean_closure_set(v___f_2063_, 4, v___x_1942_);
if (lean_obj_tag(v_val_2051_) == 0)
{
lean_object* v_type_2064_; lean_object* v___x_2065_; lean_object* v_mctx_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; uint8_t v___x_2069_; 
v_type_2064_ = lean_ctor_get(v_val_2051_, 3);
v___x_2065_ = lean_st_ref_get(v___y_1948_);
v_mctx_2066_ = lean_ctor_get(v___x_2065_, 0);
lean_inc_ref_n(v_mctx_2066_, 2);
lean_dec(v___x_2065_);
v___x_2067_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1);
v___x_2068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2068_, 0, v___x_2067_);
lean_ctor_set(v___x_2068_, 1, v_mctx_2066_);
v___x_2069_ = l_Lean_Expr_hasFVar(v_type_2064_);
if (v___x_2069_ == 0)
{
uint8_t v___x_2070_; 
v___x_2070_ = l_Lean_Expr_hasMVar(v_type_2064_);
if (v___x_2070_ == 0)
{
lean_dec_ref(v___x_2068_);
lean_dec_ref(v___f_2063_);
lean_dec_ref(v___f_2060_);
v_fst_1964_ = v___x_2070_;
v_mctx_1965_ = v_mctx_2066_;
goto v___jp_1963_;
}
else
{
lean_object* v___x_2071_; 
lean_dec_ref(v_mctx_2066_);
lean_inc_ref(v_type_2064_);
v___x_2071_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_2063_, v___f_2060_, v_type_2064_, v___x_2068_);
v___y_1981_ = v___x_2071_;
goto v___jp_1980_;
}
}
else
{
lean_object* v___x_2072_; 
lean_dec_ref(v_mctx_2066_);
lean_inc_ref(v_type_2064_);
v___x_2072_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_2063_, v___f_2060_, v_type_2064_, v___x_2068_);
v___y_1981_ = v___x_2072_;
goto v___jp_1980_;
}
}
else
{
uint8_t v_nondep_2073_; 
v_nondep_2073_ = lean_ctor_get_uint8(v_val_2051_, sizeof(void*)*5);
if (v_nondep_2073_ == 0)
{
lean_object* v_type_2074_; lean_object* v_value_2075_; lean_object* v___x_2076_; lean_object* v_mctx_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; uint8_t v___x_2080_; 
v_type_2074_ = lean_ctor_get(v_val_2051_, 3);
v_value_2075_ = lean_ctor_get(v_val_2051_, 4);
v___x_2076_ = lean_st_ref_get(v___y_1948_);
v_mctx_2077_ = lean_ctor_get(v___x_2076_, 0);
lean_inc_ref(v_mctx_2077_);
lean_dec(v___x_2076_);
v___x_2078_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1);
v___x_2079_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2079_, 0, v___x_2078_);
lean_ctor_set(v___x_2079_, 1, v_mctx_2077_);
v___x_2080_ = l_Lean_Expr_hasFVar(v_type_2074_);
if (v___x_2080_ == 0)
{
uint8_t v___x_2081_; 
v___x_2081_ = l_Lean_Expr_hasMVar(v_type_2074_);
if (v___x_2081_ == 0)
{
lean_inc_ref(v_value_2075_);
v___y_2010_ = v_value_2075_;
v___y_2011_ = v___f_2063_;
v___y_2012_ = v___f_2060_;
v_fst_2013_ = v___x_2081_;
v_snd_2014_ = v___x_2079_;
goto v___jp_2009_;
}
else
{
lean_object* v___x_2082_; 
lean_inc_ref(v_type_2074_);
lean_inc_ref(v___f_2060_);
lean_inc_ref(v___f_2063_);
v___x_2082_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_2063_, v___f_2060_, v_type_2074_, v___x_2079_);
lean_inc_ref(v_value_2075_);
v___y_2020_ = v_value_2075_;
v___y_2021_ = v___f_2063_;
v___y_2022_ = v___f_2060_;
v___y_2023_ = v___x_2082_;
goto v___jp_2019_;
}
}
else
{
lean_object* v___x_2083_; 
lean_inc_ref(v_type_2074_);
lean_inc_ref(v___f_2060_);
lean_inc_ref(v___f_2063_);
v___x_2083_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_2063_, v___f_2060_, v_type_2074_, v___x_2079_);
lean_inc_ref(v_value_2075_);
v___y_2020_ = v_value_2075_;
v___y_2021_ = v___f_2063_;
v___y_2022_ = v___f_2060_;
v___y_2023_ = v___x_2083_;
goto v___jp_2019_;
}
}
else
{
lean_object* v_type_2084_; lean_object* v___x_2085_; lean_object* v_mctx_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; uint8_t v___x_2089_; 
v_type_2084_ = lean_ctor_get(v_val_2051_, 3);
v___x_2085_ = lean_st_ref_get(v___y_1948_);
v_mctx_2086_ = lean_ctor_get(v___x_2085_, 0);
lean_inc_ref_n(v_mctx_2086_, 2);
lean_dec(v___x_2085_);
v___x_2087_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1);
v___x_2088_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2088_, 0, v___x_2087_);
lean_ctor_set(v___x_2088_, 1, v_mctx_2086_);
v___x_2089_ = l_Lean_Expr_hasFVar(v_type_2084_);
if (v___x_2089_ == 0)
{
uint8_t v___x_2090_; 
v___x_2090_ = l_Lean_Expr_hasMVar(v_type_2084_);
if (v___x_2090_ == 0)
{
lean_dec_ref(v___x_2088_);
lean_dec_ref(v___f_2063_);
lean_dec_ref(v___f_2060_);
v_fst_2028_ = v___x_2090_;
v_mctx_2029_ = v_mctx_2086_;
goto v___jp_2027_;
}
else
{
lean_object* v___x_2091_; 
lean_dec_ref(v_mctx_2086_);
lean_inc_ref(v_type_2084_);
v___x_2091_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_2063_, v___f_2060_, v_type_2084_, v___x_2088_);
v___y_2045_ = v___x_2091_;
goto v___jp_2044_;
}
}
else
{
lean_object* v___x_2092_; 
lean_dec_ref(v_mctx_2086_);
lean_inc_ref(v_type_2084_);
v___x_2092_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_2063_, v___f_2060_, v_type_2084_, v___x_2088_);
v___y_2045_ = v___x_2092_;
goto v___jp_2044_;
}
}
}
}
else
{
v_a_1953_ = v___x_1941_;
goto v___jp_1952_;
}
}
v___jp_2093_:
{
uint8_t v___x_2095_; 
v___x_2095_ = lean_nat_dec_lt(v___x_2056_, v___y_2094_);
if (v___x_2095_ == 0)
{
lean_dec(v___y_2094_);
lean_dec(v___x_2053_);
v___y_2058_ = v___x_2055_;
goto v___jp_2057_;
}
else
{
size_t v___x_2096_; size_t v___x_2097_; uint8_t v___x_2098_; 
v___x_2096_ = ((size_t)0ULL);
v___x_2097_ = lean_usize_of_nat(v___y_2094_);
lean_dec(v___y_2094_);
v___x_2098_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__3(v___x_2053_, v___x_1942_, v___x_2096_, v___x_2097_);
lean_dec(v___x_2053_);
v___y_2058_ = v___x_2098_;
goto v___jp_2057_;
}
}
}
else
{
lean_dec(v___x_2053_);
v_a_1960_ = v___x_2055_;
goto v___jp_1959_;
}
}
v___jp_1952_:
{
if (v_a_1953_ == 0)
{
size_t v___x_1954_; size_t v___x_1955_; 
v___x_1954_ = ((size_t)1ULL);
v___x_1955_ = lean_usize_add(v_i_1946_, v___x_1954_);
v_i_1946_ = v___x_1955_;
goto _start;
}
else
{
lean_object* v___x_1957_; lean_object* v___x_1958_; 
lean_dec(v___x_1943_);
lean_dec_ref(v___x_1942_);
v___x_1957_ = lean_box(v___x_1951_);
v___x_1958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1958_, 0, v___x_1957_);
return v___x_1958_;
}
}
v___jp_1959_:
{
if (v_a_1960_ == 0)
{
lean_object* v___x_1961_; lean_object* v___x_1962_; 
lean_dec(v___x_1943_);
lean_dec_ref(v___x_1942_);
v___x_1961_ = lean_box(v___x_1951_);
v___x_1962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1962_, 0, v___x_1961_);
return v___x_1962_;
}
else
{
v_a_1953_ = v___x_1941_;
goto v___jp_1952_;
}
}
v___jp_1963_:
{
lean_object* v___x_1966_; lean_object* v_cache_1967_; lean_object* v_zetaDeltaFVarIds_1968_; lean_object* v_postponed_1969_; lean_object* v_diag_1970_; lean_object* v___x_1972_; uint8_t v_isShared_1973_; uint8_t v_isSharedCheck_1978_; 
v___x_1966_ = lean_st_ref_take(v___y_1948_);
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
v___x_1976_ = lean_st_ref_set(v___y_1948_, v___x_1975_);
v_a_1960_ = v_fst_1964_;
goto v___jp_1959_;
}
}
}
v___jp_1980_:
{
lean_object* v_snd_1982_; lean_object* v_fst_1983_; lean_object* v_mctx_1984_; uint8_t v___x_1985_; 
v_snd_1982_ = lean_ctor_get(v___y_1981_, 1);
lean_inc(v_snd_1982_);
v_fst_1983_ = lean_ctor_get(v___y_1981_, 0);
lean_inc(v_fst_1983_);
lean_dec_ref(v___y_1981_);
v_mctx_1984_ = lean_ctor_get(v_snd_1982_, 1);
lean_inc_ref(v_mctx_1984_);
lean_dec(v_snd_1982_);
v___x_1985_ = lean_unbox(v_fst_1983_);
lean_dec(v_fst_1983_);
v_fst_1964_ = v___x_1985_;
v_mctx_1965_ = v_mctx_1984_;
goto v___jp_1963_;
}
v___jp_1986_:
{
lean_object* v_mctx_1989_; lean_object* v___x_1990_; lean_object* v_cache_1991_; lean_object* v_zetaDeltaFVarIds_1992_; lean_object* v_postponed_1993_; lean_object* v_diag_1994_; lean_object* v___x_1996_; uint8_t v_isShared_1997_; uint8_t v_isSharedCheck_2002_; 
v_mctx_1989_ = lean_ctor_get(v_snd_1988_, 1);
lean_inc_ref(v_mctx_1989_);
lean_dec_ref(v_snd_1988_);
v___x_1990_ = lean_st_ref_take(v___y_1948_);
v_cache_1991_ = lean_ctor_get(v___x_1990_, 1);
v_zetaDeltaFVarIds_1992_ = lean_ctor_get(v___x_1990_, 2);
v_postponed_1993_ = lean_ctor_get(v___x_1990_, 3);
v_diag_1994_ = lean_ctor_get(v___x_1990_, 4);
v_isSharedCheck_2002_ = !lean_is_exclusive(v___x_1990_);
if (v_isSharedCheck_2002_ == 0)
{
lean_object* v_unused_2003_; 
v_unused_2003_ = lean_ctor_get(v___x_1990_, 0);
lean_dec(v_unused_2003_);
v___x_1996_ = v___x_1990_;
v_isShared_1997_ = v_isSharedCheck_2002_;
goto v_resetjp_1995_;
}
else
{
lean_inc(v_diag_1994_);
lean_inc(v_postponed_1993_);
lean_inc(v_zetaDeltaFVarIds_1992_);
lean_inc(v_cache_1991_);
lean_dec(v___x_1990_);
v___x_1996_ = lean_box(0);
v_isShared_1997_ = v_isSharedCheck_2002_;
goto v_resetjp_1995_;
}
v_resetjp_1995_:
{
lean_object* v___x_1999_; 
if (v_isShared_1997_ == 0)
{
lean_ctor_set(v___x_1996_, 0, v_mctx_1989_);
v___x_1999_ = v___x_1996_;
goto v_reusejp_1998_;
}
else
{
lean_object* v_reuseFailAlloc_2001_; 
v_reuseFailAlloc_2001_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2001_, 0, v_mctx_1989_);
lean_ctor_set(v_reuseFailAlloc_2001_, 1, v_cache_1991_);
lean_ctor_set(v_reuseFailAlloc_2001_, 2, v_zetaDeltaFVarIds_1992_);
lean_ctor_set(v_reuseFailAlloc_2001_, 3, v_postponed_1993_);
lean_ctor_set(v_reuseFailAlloc_2001_, 4, v_diag_1994_);
v___x_1999_ = v_reuseFailAlloc_2001_;
goto v_reusejp_1998_;
}
v_reusejp_1998_:
{
lean_object* v___x_2000_; 
v___x_2000_ = lean_st_ref_set(v___y_1948_, v___x_1999_);
v_a_1960_ = v_fst_1987_;
goto v___jp_1959_;
}
}
}
v___jp_2004_:
{
lean_object* v_fst_2006_; lean_object* v_snd_2007_; uint8_t v___x_2008_; 
v_fst_2006_ = lean_ctor_get(v___y_2005_, 0);
lean_inc(v_fst_2006_);
v_snd_2007_ = lean_ctor_get(v___y_2005_, 1);
lean_inc(v_snd_2007_);
lean_dec_ref(v___y_2005_);
v___x_2008_ = lean_unbox(v_fst_2006_);
lean_dec(v_fst_2006_);
v_fst_1987_ = v___x_2008_;
v_snd_1988_ = v_snd_2007_;
goto v___jp_1986_;
}
v___jp_2009_:
{
if (v_fst_2013_ == 0)
{
uint8_t v___x_2015_; 
v___x_2015_ = l_Lean_Expr_hasFVar(v___y_2010_);
if (v___x_2015_ == 0)
{
uint8_t v___x_2016_; 
v___x_2016_ = l_Lean_Expr_hasMVar(v___y_2010_);
if (v___x_2016_ == 0)
{
lean_dec_ref(v___y_2012_);
lean_dec_ref(v___y_2011_);
lean_dec_ref(v___y_2010_);
v_fst_1987_ = v___x_2016_;
v_snd_1988_ = v_snd_2014_;
goto v___jp_1986_;
}
else
{
lean_object* v___x_2017_; 
v___x_2017_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___y_2011_, v___y_2012_, v___y_2010_, v_snd_2014_);
v___y_2005_ = v___x_2017_;
goto v___jp_2004_;
}
}
else
{
lean_object* v___x_2018_; 
v___x_2018_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___y_2011_, v___y_2012_, v___y_2010_, v_snd_2014_);
v___y_2005_ = v___x_2018_;
goto v___jp_2004_;
}
}
else
{
lean_dec_ref(v___y_2012_);
lean_dec_ref(v___y_2011_);
lean_dec_ref(v___y_2010_);
v_fst_1987_ = v_fst_2013_;
v_snd_1988_ = v_snd_2014_;
goto v___jp_1986_;
}
}
v___jp_2019_:
{
lean_object* v_fst_2024_; lean_object* v_snd_2025_; uint8_t v___x_2026_; 
v_fst_2024_ = lean_ctor_get(v___y_2023_, 0);
lean_inc(v_fst_2024_);
v_snd_2025_ = lean_ctor_get(v___y_2023_, 1);
lean_inc(v_snd_2025_);
lean_dec_ref(v___y_2023_);
v___x_2026_ = lean_unbox(v_fst_2024_);
lean_dec(v_fst_2024_);
v___y_2010_ = v___y_2020_;
v___y_2011_ = v___y_2021_;
v___y_2012_ = v___y_2022_;
v_fst_2013_ = v___x_2026_;
v_snd_2014_ = v_snd_2025_;
goto v___jp_2009_;
}
v___jp_2027_:
{
lean_object* v___x_2030_; lean_object* v_cache_2031_; lean_object* v_zetaDeltaFVarIds_2032_; lean_object* v_postponed_2033_; lean_object* v_diag_2034_; lean_object* v___x_2036_; uint8_t v_isShared_2037_; uint8_t v_isSharedCheck_2042_; 
v___x_2030_ = lean_st_ref_take(v___y_1948_);
v_cache_2031_ = lean_ctor_get(v___x_2030_, 1);
v_zetaDeltaFVarIds_2032_ = lean_ctor_get(v___x_2030_, 2);
v_postponed_2033_ = lean_ctor_get(v___x_2030_, 3);
v_diag_2034_ = lean_ctor_get(v___x_2030_, 4);
v_isSharedCheck_2042_ = !lean_is_exclusive(v___x_2030_);
if (v_isSharedCheck_2042_ == 0)
{
lean_object* v_unused_2043_; 
v_unused_2043_ = lean_ctor_get(v___x_2030_, 0);
lean_dec(v_unused_2043_);
v___x_2036_ = v___x_2030_;
v_isShared_2037_ = v_isSharedCheck_2042_;
goto v_resetjp_2035_;
}
else
{
lean_inc(v_diag_2034_);
lean_inc(v_postponed_2033_);
lean_inc(v_zetaDeltaFVarIds_2032_);
lean_inc(v_cache_2031_);
lean_dec(v___x_2030_);
v___x_2036_ = lean_box(0);
v_isShared_2037_ = v_isSharedCheck_2042_;
goto v_resetjp_2035_;
}
v_resetjp_2035_:
{
lean_object* v___x_2039_; 
if (v_isShared_2037_ == 0)
{
lean_ctor_set(v___x_2036_, 0, v_mctx_2029_);
v___x_2039_ = v___x_2036_;
goto v_reusejp_2038_;
}
else
{
lean_object* v_reuseFailAlloc_2041_; 
v_reuseFailAlloc_2041_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2041_, 0, v_mctx_2029_);
lean_ctor_set(v_reuseFailAlloc_2041_, 1, v_cache_2031_);
lean_ctor_set(v_reuseFailAlloc_2041_, 2, v_zetaDeltaFVarIds_2032_);
lean_ctor_set(v_reuseFailAlloc_2041_, 3, v_postponed_2033_);
lean_ctor_set(v_reuseFailAlloc_2041_, 4, v_diag_2034_);
v___x_2039_ = v_reuseFailAlloc_2041_;
goto v_reusejp_2038_;
}
v_reusejp_2038_:
{
lean_object* v___x_2040_; 
v___x_2040_ = lean_st_ref_set(v___y_1948_, v___x_2039_);
v_a_1960_ = v_fst_2028_;
goto v___jp_1959_;
}
}
}
v___jp_2044_:
{
lean_object* v_snd_2046_; lean_object* v_fst_2047_; lean_object* v_mctx_2048_; uint8_t v___x_2049_; 
v_snd_2046_ = lean_ctor_get(v___y_2045_, 1);
lean_inc(v_snd_2046_);
v_fst_2047_ = lean_ctor_get(v___y_2045_, 0);
lean_inc(v_fst_2047_);
lean_dec_ref(v___y_2045_);
v_mctx_2048_ = lean_ctor_get(v_snd_2046_, 1);
lean_inc_ref(v_mctx_2048_);
lean_dec(v_snd_2046_);
v___x_2049_ = lean_unbox(v_fst_2047_);
lean_dec(v_fst_2047_);
v_fst_2028_ = v___x_2049_;
v_mctx_2029_ = v_mctx_2048_;
goto v___jp_2027_;
}
}
else
{
uint8_t v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; 
lean_dec(v___x_1943_);
lean_dec_ref(v___x_1942_);
v___x_2102_ = 0;
v___x_2103_ = lean_box(v___x_2102_);
v___x_2104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2104_, 0, v___x_2103_);
return v___x_2104_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___boxed(lean_object* v___x_2105_, lean_object* v___x_2106_, lean_object* v___x_2107_, lean_object* v_ctx_2108_, lean_object* v_as_2109_, lean_object* v_i_2110_, lean_object* v_stop_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_){
_start:
{
uint8_t v___x_9224__boxed_2114_; size_t v_i_boxed_2115_; size_t v_stop_boxed_2116_; lean_object* v_res_2117_; 
v___x_9224__boxed_2114_ = lean_unbox(v___x_2105_);
v_i_boxed_2115_ = lean_unbox_usize(v_i_2110_);
lean_dec(v_i_2110_);
v_stop_boxed_2116_ = lean_unbox_usize(v_stop_2111_);
lean_dec(v_stop_2111_);
v_res_2117_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg(v___x_9224__boxed_2114_, v___x_2106_, v___x_2107_, v_ctx_2108_, v_as_2109_, v_i_boxed_2115_, v_stop_boxed_2116_, v___y_2112_);
lean_dec(v___y_2112_);
lean_dec_ref(v_as_2109_);
lean_dec_ref(v_ctx_2108_);
return v_res_2117_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4(uint8_t v___x_2118_, lean_object* v___x_2119_, lean_object* v___x_2120_, lean_object* v_ctx_2121_, lean_object* v_x_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_){
_start:
{
if (lean_obj_tag(v_x_2122_) == 0)
{
lean_object* v_cs_2128_; lean_object* v___x_2130_; uint8_t v_isShared_2131_; uint8_t v_isSharedCheck_2146_; 
v_cs_2128_ = lean_ctor_get(v_x_2122_, 0);
v_isSharedCheck_2146_ = !lean_is_exclusive(v_x_2122_);
if (v_isSharedCheck_2146_ == 0)
{
v___x_2130_ = v_x_2122_;
v_isShared_2131_ = v_isSharedCheck_2146_;
goto v_resetjp_2129_;
}
else
{
lean_inc(v_cs_2128_);
lean_dec(v_x_2122_);
v___x_2130_ = lean_box(0);
v_isShared_2131_ = v_isSharedCheck_2146_;
goto v_resetjp_2129_;
}
v_resetjp_2129_:
{
lean_object* v___x_2132_; lean_object* v___x_2133_; uint8_t v___x_2134_; 
v___x_2132_ = lean_unsigned_to_nat(0u);
v___x_2133_ = lean_array_get_size(v_cs_2128_);
v___x_2134_ = lean_nat_dec_lt(v___x_2132_, v___x_2133_);
if (v___x_2134_ == 0)
{
lean_object* v___x_2135_; lean_object* v___x_2137_; 
lean_dec_ref(v_cs_2128_);
lean_dec(v___x_2120_);
lean_dec_ref(v___x_2119_);
v___x_2135_ = lean_box(v___x_2134_);
if (v_isShared_2131_ == 0)
{
lean_ctor_set(v___x_2130_, 0, v___x_2135_);
v___x_2137_ = v___x_2130_;
goto v_reusejp_2136_;
}
else
{
lean_object* v_reuseFailAlloc_2138_; 
v_reuseFailAlloc_2138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2138_, 0, v___x_2135_);
v___x_2137_ = v_reuseFailAlloc_2138_;
goto v_reusejp_2136_;
}
v_reusejp_2136_:
{
return v___x_2137_;
}
}
else
{
if (v___x_2134_ == 0)
{
lean_object* v___x_2139_; lean_object* v___x_2141_; 
lean_dec_ref(v_cs_2128_);
lean_dec(v___x_2120_);
lean_dec_ref(v___x_2119_);
v___x_2139_ = lean_box(v___x_2134_);
if (v_isShared_2131_ == 0)
{
lean_ctor_set(v___x_2130_, 0, v___x_2139_);
v___x_2141_ = v___x_2130_;
goto v_reusejp_2140_;
}
else
{
lean_object* v_reuseFailAlloc_2142_; 
v_reuseFailAlloc_2142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2142_, 0, v___x_2139_);
v___x_2141_ = v_reuseFailAlloc_2142_;
goto v_reusejp_2140_;
}
v_reusejp_2140_:
{
return v___x_2141_;
}
}
else
{
size_t v___x_2143_; size_t v___x_2144_; lean_object* v___x_2145_; 
lean_del_object(v___x_2130_);
v___x_2143_ = ((size_t)0ULL);
v___x_2144_ = lean_usize_of_nat(v___x_2133_);
v___x_2145_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4_spec__5(v___x_2118_, v___x_2119_, v___x_2120_, v_ctx_2121_, v_cs_2128_, v___x_2143_, v___x_2144_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_);
lean_dec_ref(v_cs_2128_);
return v___x_2145_;
}
}
}
}
else
{
lean_object* v_vs_2147_; lean_object* v___x_2149_; uint8_t v_isShared_2150_; uint8_t v_isSharedCheck_2165_; 
v_vs_2147_ = lean_ctor_get(v_x_2122_, 0);
v_isSharedCheck_2165_ = !lean_is_exclusive(v_x_2122_);
if (v_isSharedCheck_2165_ == 0)
{
v___x_2149_ = v_x_2122_;
v_isShared_2150_ = v_isSharedCheck_2165_;
goto v_resetjp_2148_;
}
else
{
lean_inc(v_vs_2147_);
lean_dec(v_x_2122_);
v___x_2149_ = lean_box(0);
v_isShared_2150_ = v_isSharedCheck_2165_;
goto v_resetjp_2148_;
}
v_resetjp_2148_:
{
lean_object* v___x_2151_; lean_object* v___x_2152_; uint8_t v___x_2153_; 
v___x_2151_ = lean_unsigned_to_nat(0u);
v___x_2152_ = lean_array_get_size(v_vs_2147_);
v___x_2153_ = lean_nat_dec_lt(v___x_2151_, v___x_2152_);
if (v___x_2153_ == 0)
{
lean_object* v___x_2154_; lean_object* v___x_2156_; 
lean_dec_ref(v_vs_2147_);
lean_dec(v___x_2120_);
lean_dec_ref(v___x_2119_);
v___x_2154_ = lean_box(v___x_2153_);
if (v_isShared_2150_ == 0)
{
lean_ctor_set_tag(v___x_2149_, 0);
lean_ctor_set(v___x_2149_, 0, v___x_2154_);
v___x_2156_ = v___x_2149_;
goto v_reusejp_2155_;
}
else
{
lean_object* v_reuseFailAlloc_2157_; 
v_reuseFailAlloc_2157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2157_, 0, v___x_2154_);
v___x_2156_ = v_reuseFailAlloc_2157_;
goto v_reusejp_2155_;
}
v_reusejp_2155_:
{
return v___x_2156_;
}
}
else
{
if (v___x_2153_ == 0)
{
lean_object* v___x_2158_; lean_object* v___x_2160_; 
lean_dec_ref(v_vs_2147_);
lean_dec(v___x_2120_);
lean_dec_ref(v___x_2119_);
v___x_2158_ = lean_box(v___x_2153_);
if (v_isShared_2150_ == 0)
{
lean_ctor_set_tag(v___x_2149_, 0);
lean_ctor_set(v___x_2149_, 0, v___x_2158_);
v___x_2160_ = v___x_2149_;
goto v_reusejp_2159_;
}
else
{
lean_object* v_reuseFailAlloc_2161_; 
v_reuseFailAlloc_2161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2161_, 0, v___x_2158_);
v___x_2160_ = v_reuseFailAlloc_2161_;
goto v_reusejp_2159_;
}
v_reusejp_2159_:
{
return v___x_2160_;
}
}
else
{
size_t v___x_2162_; size_t v___x_2163_; lean_object* v___x_2164_; 
lean_del_object(v___x_2149_);
v___x_2162_ = ((size_t)0ULL);
v___x_2163_ = lean_usize_of_nat(v___x_2152_);
v___x_2164_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg(v___x_2118_, v___x_2119_, v___x_2120_, v_ctx_2121_, v_vs_2147_, v___x_2162_, v___x_2163_, v___y_2124_);
lean_dec_ref(v_vs_2147_);
return v___x_2164_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4_spec__5(uint8_t v___x_2166_, lean_object* v___x_2167_, lean_object* v___x_2168_, lean_object* v_ctx_2169_, lean_object* v_as_2170_, size_t v_i_2171_, size_t v_stop_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_){
_start:
{
uint8_t v___x_2178_; 
v___x_2178_ = lean_usize_dec_eq(v_i_2171_, v_stop_2172_);
if (v___x_2178_ == 0)
{
lean_object* v___x_2179_; lean_object* v___x_2180_; 
v___x_2179_ = lean_array_uget_borrowed(v_as_2170_, v_i_2171_);
lean_inc(v___x_2179_);
lean_inc(v___x_2168_);
lean_inc_ref(v___x_2167_);
v___x_2180_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4(v___x_2166_, v___x_2167_, v___x_2168_, v_ctx_2169_, v___x_2179_, v___y_2173_, v___y_2174_, v___y_2175_, v___y_2176_);
if (lean_obj_tag(v___x_2180_) == 0)
{
lean_object* v_a_2181_; lean_object* v___x_2183_; uint8_t v_isShared_2184_; uint8_t v_isSharedCheck_2192_; 
v_a_2181_ = lean_ctor_get(v___x_2180_, 0);
v_isSharedCheck_2192_ = !lean_is_exclusive(v___x_2180_);
if (v_isSharedCheck_2192_ == 0)
{
v___x_2183_ = v___x_2180_;
v_isShared_2184_ = v_isSharedCheck_2192_;
goto v_resetjp_2182_;
}
else
{
lean_inc(v_a_2181_);
lean_dec(v___x_2180_);
v___x_2183_ = lean_box(0);
v_isShared_2184_ = v_isSharedCheck_2192_;
goto v_resetjp_2182_;
}
v_resetjp_2182_:
{
uint8_t v___x_2185_; 
v___x_2185_ = lean_unbox(v_a_2181_);
if (v___x_2185_ == 0)
{
size_t v___x_2186_; size_t v___x_2187_; 
lean_del_object(v___x_2183_);
lean_dec(v_a_2181_);
v___x_2186_ = ((size_t)1ULL);
v___x_2187_ = lean_usize_add(v_i_2171_, v___x_2186_);
v_i_2171_ = v___x_2187_;
goto _start;
}
else
{
lean_object* v___x_2190_; 
lean_dec(v___x_2168_);
lean_dec_ref(v___x_2167_);
if (v_isShared_2184_ == 0)
{
v___x_2190_ = v___x_2183_;
goto v_reusejp_2189_;
}
else
{
lean_object* v_reuseFailAlloc_2191_; 
v_reuseFailAlloc_2191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2191_, 0, v_a_2181_);
v___x_2190_ = v_reuseFailAlloc_2191_;
goto v_reusejp_2189_;
}
v_reusejp_2189_:
{
return v___x_2190_;
}
}
}
}
else
{
lean_dec(v___x_2168_);
lean_dec_ref(v___x_2167_);
return v___x_2180_;
}
}
else
{
uint8_t v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; 
lean_dec(v___x_2168_);
lean_dec_ref(v___x_2167_);
v___x_2193_ = 0;
v___x_2194_ = lean_box(v___x_2193_);
v___x_2195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2195_, 0, v___x_2194_);
return v___x_2195_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4_spec__5___boxed(lean_object* v___x_2196_, lean_object* v___x_2197_, lean_object* v___x_2198_, lean_object* v_ctx_2199_, lean_object* v_as_2200_, lean_object* v_i_2201_, lean_object* v_stop_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_){
_start:
{
uint8_t v___x_9531__boxed_2208_; size_t v_i_boxed_2209_; size_t v_stop_boxed_2210_; lean_object* v_res_2211_; 
v___x_9531__boxed_2208_ = lean_unbox(v___x_2196_);
v_i_boxed_2209_ = lean_unbox_usize(v_i_2201_);
lean_dec(v_i_2201_);
v_stop_boxed_2210_ = lean_unbox_usize(v_stop_2202_);
lean_dec(v_stop_2202_);
v_res_2211_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4_spec__5(v___x_9531__boxed_2208_, v___x_2197_, v___x_2198_, v_ctx_2199_, v_as_2200_, v_i_boxed_2209_, v_stop_boxed_2210_, v___y_2203_, v___y_2204_, v___y_2205_, v___y_2206_);
lean_dec(v___y_2206_);
lean_dec_ref(v___y_2205_);
lean_dec(v___y_2204_);
lean_dec_ref(v___y_2203_);
lean_dec_ref(v_as_2200_);
lean_dec_ref(v_ctx_2199_);
return v_res_2211_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4___boxed(lean_object* v___x_2212_, lean_object* v___x_2213_, lean_object* v___x_2214_, lean_object* v_ctx_2215_, lean_object* v_x_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_){
_start:
{
uint8_t v___x_9550__boxed_2222_; lean_object* v_res_2223_; 
v___x_9550__boxed_2222_ = lean_unbox(v___x_2212_);
v_res_2223_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4(v___x_9550__boxed_2222_, v___x_2213_, v___x_2214_, v_ctx_2215_, v_x_2216_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_);
lean_dec(v___y_2220_);
lean_dec_ref(v___y_2219_);
lean_dec(v___y_2218_);
lean_dec_ref(v___y_2217_);
lean_dec_ref(v_ctx_2215_);
return v_res_2223_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4(uint8_t v___x_2224_, lean_object* v___x_2225_, lean_object* v___x_2226_, lean_object* v_ctx_2227_, lean_object* v_t_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_){
_start:
{
lean_object* v_root_2234_; lean_object* v_tail_2235_; lean_object* v___x_2236_; 
v_root_2234_ = lean_ctor_get(v_t_2228_, 0);
lean_inc_ref(v_root_2234_);
v_tail_2235_ = lean_ctor_get(v_t_2228_, 1);
lean_inc_ref(v_tail_2235_);
lean_dec_ref(v_t_2228_);
lean_inc(v___x_2226_);
lean_inc_ref(v___x_2225_);
v___x_2236_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4(v___x_2224_, v___x_2225_, v___x_2226_, v_ctx_2227_, v_root_2234_, v___y_2229_, v___y_2230_, v___y_2231_, v___y_2232_);
if (lean_obj_tag(v___x_2236_) == 0)
{
lean_object* v_a_2237_; uint8_t v___x_2238_; 
v_a_2237_ = lean_ctor_get(v___x_2236_, 0);
lean_inc(v_a_2237_);
v___x_2238_ = lean_unbox(v_a_2237_);
lean_dec(v_a_2237_);
if (v___x_2238_ == 0)
{
lean_object* v___x_2239_; lean_object* v___x_2240_; uint8_t v___x_2241_; 
v___x_2239_ = lean_unsigned_to_nat(0u);
v___x_2240_ = lean_array_get_size(v_tail_2235_);
v___x_2241_ = lean_nat_dec_lt(v___x_2239_, v___x_2240_);
if (v___x_2241_ == 0)
{
lean_dec_ref(v_tail_2235_);
lean_dec(v___x_2226_);
lean_dec_ref(v___x_2225_);
return v___x_2236_;
}
else
{
if (v___x_2241_ == 0)
{
lean_dec_ref(v_tail_2235_);
lean_dec(v___x_2226_);
lean_dec_ref(v___x_2225_);
return v___x_2236_;
}
else
{
size_t v___x_2242_; size_t v___x_2243_; lean_object* v___x_2244_; 
lean_dec_ref(v___x_2236_);
v___x_2242_ = ((size_t)0ULL);
v___x_2243_ = lean_usize_of_nat(v___x_2240_);
v___x_2244_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg(v___x_2224_, v___x_2225_, v___x_2226_, v_ctx_2227_, v_tail_2235_, v___x_2242_, v___x_2243_, v___y_2230_);
lean_dec_ref(v_tail_2235_);
return v___x_2244_;
}
}
}
else
{
lean_dec_ref(v_tail_2235_);
lean_dec(v___x_2226_);
lean_dec_ref(v___x_2225_);
return v___x_2236_;
}
}
else
{
lean_dec_ref(v_tail_2235_);
lean_dec(v___x_2226_);
lean_dec_ref(v___x_2225_);
return v___x_2236_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4___boxed(lean_object* v___x_2245_, lean_object* v___x_2246_, lean_object* v___x_2247_, lean_object* v_ctx_2248_, lean_object* v_t_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_){
_start:
{
uint8_t v___x_9695__boxed_2255_; lean_object* v_res_2256_; 
v___x_9695__boxed_2255_ = lean_unbox(v___x_2245_);
v_res_2256_ = l_Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4(v___x_9695__boxed_2255_, v___x_2246_, v___x_2247_, v_ctx_2248_, v_t_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_);
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
lean_object* v_majorTypeIndices_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; uint8_t v___x_2266_; uint8_t v___y_2268_; 
v_majorTypeIndices_2263_ = lean_ctor_get(v_ctx_2257_, 5);
lean_inc_ref(v_majorTypeIndices_2263_);
v___x_2264_ = lean_array_get_size(v_majorTypeIndices_2263_);
v___x_2265_ = lean_unsigned_to_nat(0u);
v___x_2266_ = lean_nat_dec_eq(v___x_2264_, v___x_2265_);
if (v___x_2266_ == 0)
{
uint8_t v___x_2292_; 
v___x_2292_ = lean_nat_dec_lt(v___x_2265_, v___x_2264_);
if (v___x_2292_ == 0)
{
v___y_2268_ = v___x_2266_;
goto v___jp_2267_;
}
else
{
if (v___x_2292_ == 0)
{
v___y_2268_ = v___x_2266_;
goto v___jp_2267_;
}
else
{
size_t v___x_2293_; size_t v___x_2294_; uint8_t v___x_2295_; 
v___x_2293_ = ((size_t)0ULL);
v___x_2294_ = lean_usize_of_nat(v___x_2264_);
v___x_2295_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5(v___x_2264_, v_majorTypeIndices_2263_, v___x_2293_, v___x_2294_);
v___y_2268_ = v___x_2295_;
goto v___jp_2267_;
}
}
}
else
{
lean_object* v___x_2296_; lean_object* v___x_2297_; 
lean_dec_ref(v_majorTypeIndices_2263_);
lean_dec_ref(v_ctx_2257_);
v___x_2296_ = lean_box(v___x_2266_);
v___x_2297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2297_, 0, v___x_2296_);
return v___x_2297_;
}
v___jp_2267_:
{
if (v___y_2268_ == 0)
{
uint8_t v___x_2269_; 
v___x_2269_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1___redArg(v_majorTypeIndices_2263_, v___x_2264_, v___x_2264_);
if (v___x_2269_ == 0)
{
lean_object* v_lctx_2270_; lean_object* v_decls_2271_; lean_object* v___x_2272_; 
v_lctx_2270_ = lean_ctor_get(v_a_2258_, 2);
v_decls_2271_ = lean_ctor_get(v_lctx_2270_, 1);
lean_inc_ref(v_decls_2271_);
v___x_2272_ = l_Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4(v___x_2269_, v_majorTypeIndices_2263_, v___x_2264_, v_ctx_2257_, v_decls_2271_, v_a_2258_, v_a_2259_, v_a_2260_, v_a_2261_);
lean_dec_ref(v_ctx_2257_);
if (lean_obj_tag(v___x_2272_) == 0)
{
lean_object* v_a_2273_; lean_object* v___x_2275_; uint8_t v_isShared_2276_; uint8_t v_isSharedCheck_2287_; 
v_a_2273_ = lean_ctor_get(v___x_2272_, 0);
v_isSharedCheck_2287_ = !lean_is_exclusive(v___x_2272_);
if (v_isSharedCheck_2287_ == 0)
{
v___x_2275_ = v___x_2272_;
v_isShared_2276_ = v_isSharedCheck_2287_;
goto v_resetjp_2274_;
}
else
{
lean_inc(v_a_2273_);
lean_dec(v___x_2272_);
v___x_2275_ = lean_box(0);
v_isShared_2276_ = v_isSharedCheck_2287_;
goto v_resetjp_2274_;
}
v_resetjp_2274_:
{
uint8_t v___x_2277_; 
v___x_2277_ = lean_unbox(v_a_2273_);
lean_dec(v_a_2273_);
if (v___x_2277_ == 0)
{
uint8_t v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2281_; 
v___x_2278_ = 1;
v___x_2279_ = lean_box(v___x_2278_);
if (v_isShared_2276_ == 0)
{
lean_ctor_set(v___x_2275_, 0, v___x_2279_);
v___x_2281_ = v___x_2275_;
goto v_reusejp_2280_;
}
else
{
lean_object* v_reuseFailAlloc_2282_; 
v_reuseFailAlloc_2282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2282_, 0, v___x_2279_);
v___x_2281_ = v_reuseFailAlloc_2282_;
goto v_reusejp_2280_;
}
v_reusejp_2280_:
{
return v___x_2281_;
}
}
else
{
lean_object* v___x_2283_; lean_object* v___x_2285_; 
v___x_2283_ = lean_box(v___x_2269_);
if (v_isShared_2276_ == 0)
{
lean_ctor_set(v___x_2275_, 0, v___x_2283_);
v___x_2285_ = v___x_2275_;
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
}
}
else
{
return v___x_2272_;
}
}
else
{
lean_object* v___x_2288_; lean_object* v___x_2289_; 
lean_dec_ref(v_majorTypeIndices_2263_);
lean_dec_ref(v_ctx_2257_);
v___x_2288_ = lean_box(v___y_2268_);
v___x_2289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2289_, 0, v___x_2288_);
return v___x_2289_;
}
}
else
{
lean_object* v___x_2290_; lean_object* v___x_2291_; 
lean_dec_ref(v_majorTypeIndices_2263_);
lean_dec_ref(v_ctx_2257_);
v___x_2290_ = lean_box(v___x_2266_);
v___x_2291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2291_, 0, v___x_2290_);
return v___x_2291_;
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
uint8_t v___x_9822__boxed_2354_; size_t v_i_boxed_2355_; size_t v_stop_boxed_2356_; lean_object* v_res_2357_; 
v___x_9822__boxed_2354_ = lean_unbox(v___x_2342_);
v_i_boxed_2355_ = lean_unbox_usize(v_i_2347_);
lean_dec(v_i_2347_);
v_stop_boxed_2356_ = lean_unbox_usize(v_stop_2348_);
lean_dec(v_stop_2348_);
v_res_2357_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5(v___x_9822__boxed_2354_, v___x_2343_, v___x_2344_, v_ctx_2345_, v_as_2346_, v_i_boxed_2355_, v_stop_boxed_2356_, v___y_2349_, v___y_2350_, v___y_2351_, v___y_2352_);
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
lean_dec_ref(v___x_2382_);
v___x_2384_ = l_Lean_Meta_saveState___redArg(v___y_2363_, v___y_2365_);
if (lean_obj_tag(v___x_2384_) == 0)
{
lean_object* v_a_2385_; lean_object* v___x_2386_; 
v_a_2385_ = lean_ctor_get(v___x_2384_, 0);
lean_inc(v_a_2385_);
lean_dec_ref(v___x_2384_);
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
lean_dec_ref(v___x_2386_);
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
lean_dec_ref(v___x_2409_);
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
lean_dec_ref(v___y_2465_);
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
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0___redArg(lean_object* v_ctorNames_2515_, lean_object* v_us_2516_, lean_object* v_params_2517_, lean_object* v_majorFVarId_2518_, lean_object* v_as_2519_, lean_object* v_i_2520_, lean_object* v_j_2521_, lean_object* v_bs_2522_){
_start:
{
lean_object* v_zero_2523_; uint8_t v_isZero_2524_; 
v_zero_2523_ = lean_unsigned_to_nat(0u);
v_isZero_2524_ = lean_nat_dec_eq(v_i_2520_, v_zero_2523_);
if (v_isZero_2524_ == 1)
{
lean_dec(v_j_2521_);
lean_dec(v_i_2520_);
lean_dec(v_majorFVarId_2518_);
lean_dec(v_us_2516_);
return v_bs_2522_;
}
else
{
lean_object* v_one_2525_; lean_object* v_n_2526_; lean_object* v___y_2528_; lean_object* v___x_2532_; lean_object* v___x_2533_; uint8_t v___x_2534_; 
v_one_2525_ = lean_unsigned_to_nat(1u);
v_n_2526_ = lean_nat_sub(v_i_2520_, v_one_2525_);
lean_dec(v_i_2520_);
v___x_2532_ = lean_array_fget(v_as_2519_, v_j_2521_);
v___x_2533_ = lean_array_get_size(v_ctorNames_2515_);
v___x_2534_ = lean_nat_dec_lt(v_j_2521_, v___x_2533_);
if (v___x_2534_ == 0)
{
lean_object* v___x_2535_; lean_object* v___x_2536_; 
v___x_2535_ = lean_box(0);
v___x_2536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2536_, 0, v___x_2532_);
lean_ctor_set(v___x_2536_, 1, v___x_2535_);
v___y_2528_ = v___x_2536_;
goto v___jp_2527_;
}
else
{
lean_object* v_mvarId_2537_; lean_object* v_fields_2538_; lean_object* v_subst_2539_; lean_object* v___x_2541_; uint8_t v_isShared_2542_; uint8_t v_isSharedCheck_2554_; 
v_mvarId_2537_ = lean_ctor_get(v___x_2532_, 0);
v_fields_2538_ = lean_ctor_get(v___x_2532_, 1);
v_subst_2539_ = lean_ctor_get(v___x_2532_, 2);
v_isSharedCheck_2554_ = !lean_is_exclusive(v___x_2532_);
if (v_isSharedCheck_2554_ == 0)
{
v___x_2541_ = v___x_2532_;
v_isShared_2542_ = v_isSharedCheck_2554_;
goto v_resetjp_2540_;
}
else
{
lean_inc(v_subst_2539_);
lean_inc(v_fields_2538_);
lean_inc(v_mvarId_2537_);
lean_dec(v___x_2532_);
v___x_2541_ = lean_box(0);
v_isShared_2542_ = v_isSharedCheck_2554_;
goto v_resetjp_2540_;
}
v_resetjp_2540_:
{
lean_object* v_ctorName_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v_ctorApp_2546_; lean_object* v___x_2547_; lean_object* v_subst_2548_; lean_object* v___x_2550_; 
v_ctorName_2543_ = lean_array_fget_borrowed(v_ctorNames_2515_, v_j_2521_);
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
v___y_2528_ = v___x_2552_;
goto v___jp_2527_;
}
}
}
v___jp_2527_:
{
lean_object* v___x_2529_; lean_object* v___x_2530_; 
v___x_2529_ = lean_nat_add(v_j_2521_, v_one_2525_);
lean_dec(v_j_2521_);
v___x_2530_ = lean_array_push(v_bs_2522_, v___y_2528_);
v_i_2520_ = v_n_2526_;
v_j_2521_ = v___x_2529_;
v_bs_2522_ = v___x_2530_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0___redArg___boxed(lean_object* v_ctorNames_2555_, lean_object* v_us_2556_, lean_object* v_params_2557_, lean_object* v_majorFVarId_2558_, lean_object* v_as_2559_, lean_object* v_i_2560_, lean_object* v_j_2561_, lean_object* v_bs_2562_){
_start:
{
lean_object* v_res_2563_; 
v_res_2563_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0___redArg(v_ctorNames_2555_, v_us_2556_, v_params_2557_, v_majorFVarId_2558_, v_as_2559_, v_i_2560_, v_j_2561_, v_bs_2562_);
lean_dec_ref(v_as_2559_);
lean_dec_ref(v_params_2557_);
lean_dec_ref(v_ctorNames_2555_);
return v_res_2563_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals(lean_object* v_s_2564_, lean_object* v_ctorNames_2565_, lean_object* v_majorFVarId_2566_, lean_object* v_us_2567_, lean_object* v_params_2568_){
_start:
{
lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; 
v___x_2569_ = lean_array_get_size(v_s_2564_);
v___x_2570_ = lean_unsigned_to_nat(0u);
v___x_2571_ = lean_mk_empty_array_with_capacity(v___x_2569_);
v___x_2572_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0___redArg(v_ctorNames_2565_, v_us_2567_, v_params_2568_, v_majorFVarId_2566_, v_s_2564_, v___x_2569_, v___x_2570_, v___x_2571_);
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
lean_dec_ref(v_s_2573_);
return v_res_2578_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0(lean_object* v_ctorNames_2579_, lean_object* v_us_2580_, lean_object* v_params_2581_, lean_object* v_majorFVarId_2582_, lean_object* v_as_2583_, lean_object* v_i_2584_, lean_object* v_j_2585_, lean_object* v_inv_2586_, lean_object* v_bs_2587_){
_start:
{
lean_object* v___x_2588_; 
v___x_2588_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0___redArg(v_ctorNames_2579_, v_us_2580_, v_params_2581_, v_majorFVarId_2582_, v_as_2583_, v_i_2584_, v_j_2585_, v_bs_2587_);
return v___x_2588_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0___boxed(lean_object* v_ctorNames_2589_, lean_object* v_us_2590_, lean_object* v_params_2591_, lean_object* v_majorFVarId_2592_, lean_object* v_as_2593_, lean_object* v_i_2594_, lean_object* v_j_2595_, lean_object* v_inv_2596_, lean_object* v_bs_2597_){
_start:
{
lean_object* v_res_2598_; 
v_res_2598_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0(v_ctorNames_2589_, v_us_2590_, v_params_2591_, v_majorFVarId_2592_, v_as_2593_, v_i_2594_, v_j_2595_, v_inv_2596_, v_bs_2597_);
lean_dec_ref(v_as_2593_);
lean_dec_ref(v_params_2591_);
lean_dec_ref(v_ctorNames_2589_);
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
lean_object* v_fileName_2645_; lean_object* v_fileMap_2646_; lean_object* v_options_2647_; lean_object* v_currRecDepth_2648_; lean_object* v_maxRecDepth_2649_; lean_object* v_ref_2650_; lean_object* v_currNamespace_2651_; lean_object* v_openDecls_2652_; lean_object* v_initHeartbeats_2653_; lean_object* v_maxHeartbeats_2654_; lean_object* v_quotContext_2655_; lean_object* v_currMacroScope_2656_; uint8_t v_diag_2657_; lean_object* v_cancelTk_x3f_2658_; uint8_t v_suppressElabErrors_2659_; lean_object* v_inheritedTraceOptions_2660_; uint8_t v___x_2661_; 
v_fileName_2645_ = lean_ctor_get(v_a_2642_, 0);
lean_inc_ref(v_fileName_2645_);
v_fileMap_2646_ = lean_ctor_get(v_a_2642_, 1);
lean_inc_ref(v_fileMap_2646_);
v_options_2647_ = lean_ctor_get(v_a_2642_, 2);
lean_inc_ref(v_options_2647_);
v_currRecDepth_2648_ = lean_ctor_get(v_a_2642_, 3);
lean_inc(v_currRecDepth_2648_);
v_maxRecDepth_2649_ = lean_ctor_get(v_a_2642_, 4);
lean_inc(v_maxRecDepth_2649_);
v_ref_2650_ = lean_ctor_get(v_a_2642_, 5);
lean_inc(v_ref_2650_);
v_currNamespace_2651_ = lean_ctor_get(v_a_2642_, 6);
lean_inc(v_currNamespace_2651_);
v_openDecls_2652_ = lean_ctor_get(v_a_2642_, 7);
lean_inc(v_openDecls_2652_);
v_initHeartbeats_2653_ = lean_ctor_get(v_a_2642_, 8);
lean_inc(v_initHeartbeats_2653_);
v_maxHeartbeats_2654_ = lean_ctor_get(v_a_2642_, 9);
lean_inc(v_maxHeartbeats_2654_);
v_quotContext_2655_ = lean_ctor_get(v_a_2642_, 10);
lean_inc(v_quotContext_2655_);
v_currMacroScope_2656_ = lean_ctor_get(v_a_2642_, 11);
lean_inc(v_currMacroScope_2656_);
v_diag_2657_ = lean_ctor_get_uint8(v_a_2642_, sizeof(void*)*14);
v_cancelTk_x3f_2658_ = lean_ctor_get(v_a_2642_, 12);
lean_inc(v_cancelTk_x3f_2658_);
v_suppressElabErrors_2659_ = lean_ctor_get_uint8(v_a_2642_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2660_ = lean_ctor_get(v_a_2642_, 13);
lean_inc_ref(v_inheritedTraceOptions_2660_);
lean_dec_ref(v_a_2642_);
v___x_2661_ = lean_nat_dec_eq(v_currRecDepth_2648_, v_maxRecDepth_2649_);
if (v___x_2661_ == 0)
{
lean_object* v___x_2662_; uint8_t v___x_2663_; 
v___x_2662_ = lean_unsigned_to_nat(0u);
v___x_2663_ = lean_nat_dec_eq(v_numEqs_2636_, v___x_2662_);
if (v___x_2663_ == 0)
{
lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; 
v___x_2664_ = lean_unsigned_to_nat(1u);
v___x_2665_ = lean_nat_add(v_currRecDepth_2648_, v___x_2664_);
lean_dec(v_currRecDepth_2648_);
v___x_2666_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2666_, 0, v_fileName_2645_);
lean_ctor_set(v___x_2666_, 1, v_fileMap_2646_);
lean_ctor_set(v___x_2666_, 2, v_options_2647_);
lean_ctor_set(v___x_2666_, 3, v___x_2665_);
lean_ctor_set(v___x_2666_, 4, v_maxRecDepth_2649_);
lean_ctor_set(v___x_2666_, 5, v_ref_2650_);
lean_ctor_set(v___x_2666_, 6, v_currNamespace_2651_);
lean_ctor_set(v___x_2666_, 7, v_openDecls_2652_);
lean_ctor_set(v___x_2666_, 8, v_initHeartbeats_2653_);
lean_ctor_set(v___x_2666_, 9, v_maxHeartbeats_2654_);
lean_ctor_set(v___x_2666_, 10, v_quotContext_2655_);
lean_ctor_set(v___x_2666_, 11, v_currMacroScope_2656_);
lean_ctor_set(v___x_2666_, 12, v_cancelTk_x3f_2658_);
lean_ctor_set(v___x_2666_, 13, v_inheritedTraceOptions_2660_);
lean_ctor_set_uint8(v___x_2666_, sizeof(void*)*14, v_diag_2657_);
lean_ctor_set_uint8(v___x_2666_, sizeof(void*)*14 + 1, v_suppressElabErrors_2659_);
v___x_2667_ = l_Lean_Meta_intro1Core(v_mvarId_2637_, v___x_2661_, v_a_2640_, v_a_2641_, v___x_2666_, v_a_2643_);
if (lean_obj_tag(v___x_2667_) == 0)
{
lean_object* v_a_2668_; lean_object* v_fst_2669_; lean_object* v_snd_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; 
v_a_2668_ = lean_ctor_get(v___x_2667_, 0);
lean_inc(v_a_2668_);
lean_dec_ref(v___x_2667_);
v_fst_2669_ = lean_ctor_get(v_a_2668_, 0);
lean_inc(v_fst_2669_);
v_snd_2670_ = lean_ctor_get(v_a_2668_, 1);
lean_inc(v_snd_2670_);
lean_dec(v_a_2668_);
v___x_2671_ = ((lean_object*)(l_Lean_Meta_Cases_unifyEqs_x3f___closed__0));
lean_inc(v_caseName_x3f_2639_);
v___x_2672_ = l_Lean_Meta_unifyEq_x3f(v_snd_2670_, v_fst_2669_, v_subst_2638_, v___x_2671_, v_caseName_x3f_2639_, v_a_2640_, v_a_2641_, v___x_2666_, v_a_2643_);
if (lean_obj_tag(v___x_2672_) == 0)
{
lean_object* v_a_2673_; lean_object* v___x_2675_; uint8_t v_isShared_2676_; uint8_t v_isSharedCheck_2688_; 
v_a_2673_ = lean_ctor_get(v___x_2672_, 0);
v_isSharedCheck_2688_ = !lean_is_exclusive(v___x_2672_);
if (v_isSharedCheck_2688_ == 0)
{
v___x_2675_ = v___x_2672_;
v_isShared_2676_ = v_isSharedCheck_2688_;
goto v_resetjp_2674_;
}
else
{
lean_inc(v_a_2673_);
lean_dec(v___x_2672_);
v___x_2675_ = lean_box(0);
v_isShared_2676_ = v_isSharedCheck_2688_;
goto v_resetjp_2674_;
}
v_resetjp_2674_:
{
if (lean_obj_tag(v_a_2673_) == 1)
{
lean_object* v_val_2677_; lean_object* v_mvarId_2678_; lean_object* v_subst_2679_; lean_object* v_numNewEqs_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; 
lean_del_object(v___x_2675_);
v_val_2677_ = lean_ctor_get(v_a_2673_, 0);
lean_inc(v_val_2677_);
lean_dec_ref(v_a_2673_);
v_mvarId_2678_ = lean_ctor_get(v_val_2677_, 0);
lean_inc(v_mvarId_2678_);
v_subst_2679_ = lean_ctor_get(v_val_2677_, 1);
lean_inc(v_subst_2679_);
v_numNewEqs_2680_ = lean_ctor_get(v_val_2677_, 2);
lean_inc(v_numNewEqs_2680_);
lean_dec(v_val_2677_);
v___x_2681_ = lean_nat_sub(v_numEqs_2636_, v___x_2664_);
lean_dec(v_numEqs_2636_);
v___x_2682_ = lean_nat_add(v___x_2681_, v_numNewEqs_2680_);
lean_dec(v_numNewEqs_2680_);
lean_dec(v___x_2681_);
v_numEqs_2636_ = v___x_2682_;
v_mvarId_2637_ = v_mvarId_2678_;
v_subst_2638_ = v_subst_2679_;
v_a_2642_ = v___x_2666_;
goto _start;
}
else
{
lean_object* v___x_2684_; lean_object* v___x_2686_; 
lean_dec(v_a_2673_);
lean_dec_ref(v___x_2666_);
lean_dec(v_caseName_x3f_2639_);
lean_dec(v_numEqs_2636_);
v___x_2684_ = lean_box(0);
if (v_isShared_2676_ == 0)
{
lean_ctor_set(v___x_2675_, 0, v___x_2684_);
v___x_2686_ = v___x_2675_;
goto v_reusejp_2685_;
}
else
{
lean_object* v_reuseFailAlloc_2687_; 
v_reuseFailAlloc_2687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2687_, 0, v___x_2684_);
v___x_2686_ = v_reuseFailAlloc_2687_;
goto v_reusejp_2685_;
}
v_reusejp_2685_:
{
return v___x_2686_;
}
}
}
}
else
{
lean_object* v_a_2689_; lean_object* v___x_2691_; uint8_t v_isShared_2692_; uint8_t v_isSharedCheck_2696_; 
lean_dec_ref(v___x_2666_);
lean_dec(v_caseName_x3f_2639_);
lean_dec(v_numEqs_2636_);
v_a_2689_ = lean_ctor_get(v___x_2672_, 0);
v_isSharedCheck_2696_ = !lean_is_exclusive(v___x_2672_);
if (v_isSharedCheck_2696_ == 0)
{
v___x_2691_ = v___x_2672_;
v_isShared_2692_ = v_isSharedCheck_2696_;
goto v_resetjp_2690_;
}
else
{
lean_inc(v_a_2689_);
lean_dec(v___x_2672_);
v___x_2691_ = lean_box(0);
v_isShared_2692_ = v_isSharedCheck_2696_;
goto v_resetjp_2690_;
}
v_resetjp_2690_:
{
lean_object* v___x_2694_; 
if (v_isShared_2692_ == 0)
{
v___x_2694_ = v___x_2691_;
goto v_reusejp_2693_;
}
else
{
lean_object* v_reuseFailAlloc_2695_; 
v_reuseFailAlloc_2695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2695_, 0, v_a_2689_);
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
lean_dec_ref(v___x_2666_);
lean_dec(v_caseName_x3f_2639_);
lean_dec(v_subst_2638_);
lean_dec(v_numEqs_2636_);
v_a_2697_ = lean_ctor_get(v___x_2667_, 0);
v_isSharedCheck_2704_ = !lean_is_exclusive(v___x_2667_);
if (v_isSharedCheck_2704_ == 0)
{
v___x_2699_ = v___x_2667_;
v_isShared_2700_ = v_isSharedCheck_2704_;
goto v_resetjp_2698_;
}
else
{
lean_inc(v_a_2697_);
lean_dec(v___x_2667_);
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
lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; 
lean_dec_ref(v_inheritedTraceOptions_2660_);
lean_dec(v_cancelTk_x3f_2658_);
lean_dec(v_currMacroScope_2656_);
lean_dec(v_quotContext_2655_);
lean_dec(v_maxHeartbeats_2654_);
lean_dec(v_initHeartbeats_2653_);
lean_dec(v_openDecls_2652_);
lean_dec(v_currNamespace_2651_);
lean_dec(v_ref_2650_);
lean_dec(v_maxRecDepth_2649_);
lean_dec(v_currRecDepth_2648_);
lean_dec_ref(v_options_2647_);
lean_dec_ref(v_fileMap_2646_);
lean_dec_ref(v_fileName_2645_);
lean_dec(v_caseName_x3f_2639_);
lean_dec(v_numEqs_2636_);
v___x_2705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2705_, 0, v_mvarId_2637_);
lean_ctor_set(v___x_2705_, 1, v_subst_2638_);
v___x_2706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2706_, 0, v___x_2705_);
v___x_2707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2707_, 0, v___x_2706_);
return v___x_2707_;
}
}
else
{
lean_object* v___x_2708_; 
lean_dec_ref(v_inheritedTraceOptions_2660_);
lean_dec(v_cancelTk_x3f_2658_);
lean_dec(v_currMacroScope_2656_);
lean_dec(v_quotContext_2655_);
lean_dec(v_maxHeartbeats_2654_);
lean_dec(v_initHeartbeats_2653_);
lean_dec(v_openDecls_2652_);
lean_dec(v_currNamespace_2651_);
lean_dec(v_maxRecDepth_2649_);
lean_dec(v_currRecDepth_2648_);
lean_dec_ref(v_options_2647_);
lean_dec_ref(v_fileMap_2646_);
lean_dec_ref(v_fileName_2645_);
lean_dec(v_caseName_x3f_2639_);
lean_dec(v_subst_2638_);
lean_dec(v_mvarId_2637_);
lean_dec(v_numEqs_2636_);
v___x_2708_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg(v_ref_2650_);
return v___x_2708_;
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
lean_dec_ref(v___x_2762_);
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
lean_dec_ref(v_a_2763_);
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
lean_dec_ref(v___x_2881_);
v___x_2883_ = l_Lean_Meta_getInductiveUniverseAndParams(v_a_2882_, v___y_2876_, v___y_2877_, v___y_2878_, v___y_2879_);
if (lean_obj_tag(v___x_2883_) == 0)
{
lean_object* v_a_2884_; lean_object* v_fst_2885_; lean_object* v_snd_2886_; lean_object* v___y_2888_; lean_object* v___y_2889_; lean_object* v___y_2890_; lean_object* v___y_2891_; lean_object* v___y_2892_; lean_object* v___y_2915_; lean_object* v___y_2916_; lean_object* v___y_2917_; lean_object* v___y_2918_; lean_object* v___y_2924_; lean_object* v___y_2925_; lean_object* v___y_2926_; lean_object* v___y_2927_; 
v_a_2884_ = lean_ctor_get(v___x_2883_, 0);
lean_inc(v_a_2884_);
lean_dec_ref(v___x_2883_);
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
lean_dec_ref(v_interestingCtors_x3f_2875_);
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
v___x_2984_ = l_mkCtorIdxName(v_name_2944_);
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
lean_dec_ref(v___x_2952_);
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
lean_dec(v_a_2955_);
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
v___x_2893_ = l_Lean_MVarId_induction(v_mvarId_2870_, v_majorFVarId_2871_, v___y_2892_, v_givenNames_2872_, v___y_2888_, v___y_2889_, v___y_2891_, v___y_2890_);
lean_dec(v___y_2890_);
lean_dec_ref(v___y_2891_);
lean_dec(v___y_2889_);
lean_dec_ref(v___y_2888_);
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
lean_dec(v_a_2895_);
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
v___y_2915_ = v___y_2924_;
v___y_2916_ = v___y_2925_;
v___y_2917_ = v___y_2927_;
v___y_2918_ = v___y_2926_;
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
v___y_2915_ = v___y_2924_;
v___y_2916_ = v___y_2925_;
v___y_2917_ = v___y_2927_;
v___y_2918_ = v___y_2926_;
goto v___jp_2914_;
}
else
{
lean_object* v___x_2935_; uint8_t v___x_2936_; 
v___x_2935_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__3));
v___x_2936_ = l_Lean_Environment_contains(v_env_2931_, v___x_2935_, v___x_2934_);
if (v___x_2936_ == 0)
{
v___y_2915_ = v___y_2924_;
v___y_2916_ = v___y_2925_;
v___y_2917_ = v___y_2927_;
v___y_2918_ = v___y_2926_;
goto v___jp_2914_;
}
else
{
v___y_2888_ = v___y_2924_;
v___y_2889_ = v___y_2925_;
v___y_2890_ = v___y_2927_;
v___y_2891_ = v___y_2926_;
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
v___x_3093_ = lean_st_ref_set(v___y_3054_, v___x_3092_);
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
lean_dec_ref(v___x_3138_);
lean_inc(v_majorFVarId_3128_);
v___x_3139_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f(v_majorFVarId_3128_, v___y_3133_, v___y_3134_, v___y_3135_, v___y_3136_);
if (lean_obj_tag(v___x_3139_) == 0)
{
lean_object* v_a_3140_; 
v_a_3140_ = lean_ctor_get(v___x_3139_, 0);
lean_inc(v_a_3140_);
lean_dec_ref(v___x_3139_);
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
lean_dec_ref(v___x_3147_);
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
lean_dec_ref(v___x_3150_);
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
lean_dec_ref(v___x_3180_);
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
lean_dec_ref(v___x_3161_);
v___x_3163_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices(v_a_3151_, v_a_3162_, v___y_3153_, v___y_3154_, v___y_3155_, v___y_3156_);
lean_dec(v_a_3151_);
if (lean_obj_tag(v___x_3163_) == 0)
{
lean_object* v_a_3164_; lean_object* v___x_3165_; 
v_a_3164_ = lean_ctor_get(v___x_3163_, 0);
lean_inc(v_a_3164_);
lean_dec_ref(v___x_3163_);
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
lean_dec_ref(v___x_3255_);
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
lean_dec_ref(v___x_3303_);
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
lean_dec_ref(v___x_3470_);
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
lean_dec_ref(v___x_3567_);
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
lean_object* v_cs_3643_; lean_object* v___x_3645_; uint8_t v_isShared_3646_; uint8_t v_isSharedCheck_3677_; 
v_cs_3643_ = lean_ctor_get(v_n_3636_, 0);
v_isSharedCheck_3677_ = !lean_is_exclusive(v_n_3636_);
if (v_isSharedCheck_3677_ == 0)
{
v___x_3645_ = v_n_3636_;
v_isShared_3646_ = v_isSharedCheck_3677_;
goto v_resetjp_3644_;
}
else
{
lean_inc(v_cs_3643_);
lean_dec(v_n_3636_);
v___x_3645_ = lean_box(0);
v_isShared_3646_ = v_isSharedCheck_3677_;
goto v_resetjp_3644_;
}
v_resetjp_3644_:
{
lean_object* v___x_3647_; lean_object* v___x_3648_; size_t v_sz_3649_; size_t v___x_3650_; lean_object* v___x_3651_; 
v___x_3647_ = lean_box(0);
v___x_3648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3648_, 0, v___x_3647_);
lean_ctor_set(v___x_3648_, 1, v_b_3637_);
v_sz_3649_ = lean_array_size(v_cs_3643_);
v___x_3650_ = ((size_t)0ULL);
v___x_3651_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__3(v_init_3633_, v_p_3634_, v_mvarId_3635_, v_cs_3643_, v_sz_3649_, v___x_3650_, v___x_3648_, v___y_3638_, v___y_3639_, v___y_3640_, v___y_3641_);
lean_dec_ref(v_cs_3643_);
if (lean_obj_tag(v___x_3651_) == 0)
{
lean_object* v_a_3652_; lean_object* v___x_3654_; uint8_t v_isShared_3655_; uint8_t v_isSharedCheck_3668_; 
v_a_3652_ = lean_ctor_get(v___x_3651_, 0);
v_isSharedCheck_3668_ = !lean_is_exclusive(v___x_3651_);
if (v_isSharedCheck_3668_ == 0)
{
v___x_3654_ = v___x_3651_;
v_isShared_3655_ = v_isSharedCheck_3668_;
goto v_resetjp_3653_;
}
else
{
lean_inc(v_a_3652_);
lean_dec(v___x_3651_);
v___x_3654_ = lean_box(0);
v_isShared_3655_ = v_isSharedCheck_3668_;
goto v_resetjp_3653_;
}
v_resetjp_3653_:
{
lean_object* v_fst_3656_; 
v_fst_3656_ = lean_ctor_get(v_a_3652_, 0);
if (lean_obj_tag(v_fst_3656_) == 0)
{
lean_object* v_snd_3657_; lean_object* v___x_3659_; 
v_snd_3657_ = lean_ctor_get(v_a_3652_, 1);
lean_inc(v_snd_3657_);
lean_dec(v_a_3652_);
if (v_isShared_3646_ == 0)
{
lean_ctor_set_tag(v___x_3645_, 1);
lean_ctor_set(v___x_3645_, 0, v_snd_3657_);
v___x_3659_ = v___x_3645_;
goto v_reusejp_3658_;
}
else
{
lean_object* v_reuseFailAlloc_3663_; 
v_reuseFailAlloc_3663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3663_, 0, v_snd_3657_);
v___x_3659_ = v_reuseFailAlloc_3663_;
goto v_reusejp_3658_;
}
v_reusejp_3658_:
{
lean_object* v___x_3661_; 
if (v_isShared_3655_ == 0)
{
lean_ctor_set(v___x_3654_, 0, v___x_3659_);
v___x_3661_ = v___x_3654_;
goto v_reusejp_3660_;
}
else
{
lean_object* v_reuseFailAlloc_3662_; 
v_reuseFailAlloc_3662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3662_, 0, v___x_3659_);
v___x_3661_ = v_reuseFailAlloc_3662_;
goto v_reusejp_3660_;
}
v_reusejp_3660_:
{
return v___x_3661_;
}
}
}
else
{
lean_object* v_val_3664_; lean_object* v___x_3666_; 
lean_inc_ref(v_fst_3656_);
lean_dec(v_a_3652_);
lean_del_object(v___x_3645_);
v_val_3664_ = lean_ctor_get(v_fst_3656_, 0);
lean_inc(v_val_3664_);
lean_dec_ref(v_fst_3656_);
if (v_isShared_3655_ == 0)
{
lean_ctor_set(v___x_3654_, 0, v_val_3664_);
v___x_3666_ = v___x_3654_;
goto v_reusejp_3665_;
}
else
{
lean_object* v_reuseFailAlloc_3667_; 
v_reuseFailAlloc_3667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3667_, 0, v_val_3664_);
v___x_3666_ = v_reuseFailAlloc_3667_;
goto v_reusejp_3665_;
}
v_reusejp_3665_:
{
return v___x_3666_;
}
}
}
}
else
{
lean_object* v_a_3669_; lean_object* v___x_3671_; uint8_t v_isShared_3672_; uint8_t v_isSharedCheck_3676_; 
lean_del_object(v___x_3645_);
v_a_3669_ = lean_ctor_get(v___x_3651_, 0);
v_isSharedCheck_3676_ = !lean_is_exclusive(v___x_3651_);
if (v_isSharedCheck_3676_ == 0)
{
v___x_3671_ = v___x_3651_;
v_isShared_3672_ = v_isSharedCheck_3676_;
goto v_resetjp_3670_;
}
else
{
lean_inc(v_a_3669_);
lean_dec(v___x_3651_);
v___x_3671_ = lean_box(0);
v_isShared_3672_ = v_isSharedCheck_3676_;
goto v_resetjp_3670_;
}
v_resetjp_3670_:
{
lean_object* v___x_3674_; 
if (v_isShared_3672_ == 0)
{
v___x_3674_ = v___x_3671_;
goto v_reusejp_3673_;
}
else
{
lean_object* v_reuseFailAlloc_3675_; 
v_reuseFailAlloc_3675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3675_, 0, v_a_3669_);
v___x_3674_ = v_reuseFailAlloc_3675_;
goto v_reusejp_3673_;
}
v_reusejp_3673_:
{
return v___x_3674_;
}
}
}
}
}
else
{
lean_object* v_vs_3678_; lean_object* v___x_3680_; uint8_t v_isShared_3681_; uint8_t v_isSharedCheck_3712_; 
v_vs_3678_ = lean_ctor_get(v_n_3636_, 0);
v_isSharedCheck_3712_ = !lean_is_exclusive(v_n_3636_);
if (v_isSharedCheck_3712_ == 0)
{
v___x_3680_ = v_n_3636_;
v_isShared_3681_ = v_isSharedCheck_3712_;
goto v_resetjp_3679_;
}
else
{
lean_inc(v_vs_3678_);
lean_dec(v_n_3636_);
v___x_3680_ = lean_box(0);
v_isShared_3681_ = v_isSharedCheck_3712_;
goto v_resetjp_3679_;
}
v_resetjp_3679_:
{
lean_object* v___x_3682_; lean_object* v___x_3683_; size_t v_sz_3684_; size_t v___x_3685_; lean_object* v___x_3686_; 
v___x_3682_ = lean_box(0);
v___x_3683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3683_, 0, v___x_3682_);
lean_ctor_set(v___x_3683_, 1, v_b_3637_);
v_sz_3684_ = lean_array_size(v_vs_3678_);
v___x_3685_ = ((size_t)0ULL);
v___x_3686_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4(v_p_3634_, v_mvarId_3635_, v_vs_3678_, v_sz_3684_, v___x_3685_, v___x_3683_, v___y_3638_, v___y_3639_, v___y_3640_, v___y_3641_);
lean_dec_ref(v_vs_3678_);
if (lean_obj_tag(v___x_3686_) == 0)
{
lean_object* v_a_3687_; lean_object* v___x_3689_; uint8_t v_isShared_3690_; uint8_t v_isSharedCheck_3703_; 
v_a_3687_ = lean_ctor_get(v___x_3686_, 0);
v_isSharedCheck_3703_ = !lean_is_exclusive(v___x_3686_);
if (v_isSharedCheck_3703_ == 0)
{
v___x_3689_ = v___x_3686_;
v_isShared_3690_ = v_isSharedCheck_3703_;
goto v_resetjp_3688_;
}
else
{
lean_inc(v_a_3687_);
lean_dec(v___x_3686_);
v___x_3689_ = lean_box(0);
v_isShared_3690_ = v_isSharedCheck_3703_;
goto v_resetjp_3688_;
}
v_resetjp_3688_:
{
lean_object* v_fst_3691_; 
v_fst_3691_ = lean_ctor_get(v_a_3687_, 0);
if (lean_obj_tag(v_fst_3691_) == 0)
{
lean_object* v_snd_3692_; lean_object* v___x_3694_; 
v_snd_3692_ = lean_ctor_get(v_a_3687_, 1);
lean_inc(v_snd_3692_);
lean_dec(v_a_3687_);
if (v_isShared_3681_ == 0)
{
lean_ctor_set(v___x_3680_, 0, v_snd_3692_);
v___x_3694_ = v___x_3680_;
goto v_reusejp_3693_;
}
else
{
lean_object* v_reuseFailAlloc_3698_; 
v_reuseFailAlloc_3698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3698_, 0, v_snd_3692_);
v___x_3694_ = v_reuseFailAlloc_3698_;
goto v_reusejp_3693_;
}
v_reusejp_3693_:
{
lean_object* v___x_3696_; 
if (v_isShared_3690_ == 0)
{
lean_ctor_set(v___x_3689_, 0, v___x_3694_);
v___x_3696_ = v___x_3689_;
goto v_reusejp_3695_;
}
else
{
lean_object* v_reuseFailAlloc_3697_; 
v_reuseFailAlloc_3697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3697_, 0, v___x_3694_);
v___x_3696_ = v_reuseFailAlloc_3697_;
goto v_reusejp_3695_;
}
v_reusejp_3695_:
{
return v___x_3696_;
}
}
}
else
{
lean_object* v_val_3699_; lean_object* v___x_3701_; 
lean_inc_ref(v_fst_3691_);
lean_dec(v_a_3687_);
lean_del_object(v___x_3680_);
v_val_3699_ = lean_ctor_get(v_fst_3691_, 0);
lean_inc(v_val_3699_);
lean_dec_ref(v_fst_3691_);
if (v_isShared_3690_ == 0)
{
lean_ctor_set(v___x_3689_, 0, v_val_3699_);
v___x_3701_ = v___x_3689_;
goto v_reusejp_3700_;
}
else
{
lean_object* v_reuseFailAlloc_3702_; 
v_reuseFailAlloc_3702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3702_, 0, v_val_3699_);
v___x_3701_ = v_reuseFailAlloc_3702_;
goto v_reusejp_3700_;
}
v_reusejp_3700_:
{
return v___x_3701_;
}
}
}
}
else
{
lean_object* v_a_3704_; lean_object* v___x_3706_; uint8_t v_isShared_3707_; uint8_t v_isSharedCheck_3711_; 
lean_del_object(v___x_3680_);
v_a_3704_ = lean_ctor_get(v___x_3686_, 0);
v_isSharedCheck_3711_ = !lean_is_exclusive(v___x_3686_);
if (v_isSharedCheck_3711_ == 0)
{
v___x_3706_ = v___x_3686_;
v_isShared_3707_ = v_isSharedCheck_3711_;
goto v_resetjp_3705_;
}
else
{
lean_inc(v_a_3704_);
lean_dec(v___x_3686_);
v___x_3706_ = lean_box(0);
v_isShared_3707_ = v_isSharedCheck_3711_;
goto v_resetjp_3705_;
}
v_resetjp_3705_:
{
lean_object* v___x_3709_; 
if (v_isShared_3707_ == 0)
{
v___x_3709_ = v___x_3706_;
goto v_reusejp_3708_;
}
else
{
lean_object* v_reuseFailAlloc_3710_; 
v_reuseFailAlloc_3710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3710_, 0, v_a_3704_);
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
lean_inc(v_a_3731_);
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
lean_dec_ref(v_a_3733_);
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
lean_dec_ref(v___x_3823_);
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
lean_dec_ref(v___x_3919_);
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
lean_inc_ref(v_root_3993_);
v_tail_3994_ = lean_ctor_get(v_t_3986_, 1);
lean_inc_ref(v_tail_3994_);
lean_dec_ref(v_t_3986_);
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
lean_dec_ref(v_tail_3994_);
lean_dec(v_mvarId_3985_);
lean_dec_ref(v_p_3984_);
v_a_4000_ = lean_ctor_get(v_a_3996_, 0);
lean_inc(v_a_4000_);
lean_dec_ref(v_a_3996_);
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
lean_dec_ref(v_a_3996_);
v___x_4005_ = lean_box(0);
v___x_4006_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4006_, 0, v___x_4005_);
lean_ctor_set(v___x_4006_, 1, v_a_4004_);
v_sz_4007_ = lean_array_size(v_tail_3994_);
v___x_4008_ = ((size_t)0ULL);
v___x_4009_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3(v_p_3984_, v_mvarId_3985_, v_tail_3994_, v_sz_4007_, v___x_4008_, v___x_4006_, v___y_3988_, v___y_3989_, v___y_3990_, v___y_3991_);
lean_dec_ref(v_tail_3994_);
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
lean_dec_ref(v_fst_4014_);
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
lean_dec_ref(v_tail_3994_);
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
return v_res_4050_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesRec___lam__0(lean_object* v_p_4054_, lean_object* v_mvarId_4055_, lean_object* v___y_4056_, lean_object* v___y_4057_, lean_object* v___y_4058_, lean_object* v___y_4059_){
_start:
{
lean_object* v_lctx_4061_; lean_object* v_decls_4062_; lean_object* v___x_4063_; lean_object* v___x_4064_; lean_object* v___x_4065_; 
v_lctx_4061_ = lean_ctor_get(v___y_4056_, 2);
v_decls_4062_ = lean_ctor_get(v_lctx_4061_, 1);
lean_inc_ref(v_decls_4062_);
v___x_4063_ = lean_box(0);
v___x_4064_ = ((lean_object*)(l_Lean_MVarId_casesRec___lam__0___closed__0));
v___x_4065_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2(v_p_4054_, v_mvarId_4055_, v_decls_4062_, v___x_4064_, v___y_4056_, v___y_4057_, v___y_4058_, v___y_4059_);
lean_dec_ref(v___y_4056_);
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
lean_dec_ref(v_fst_4070_);
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
uint8_t v___x_4132_; 
v___x_4132_ = l_Lean_Expr_hasMVar(v_e_4129_);
if (v___x_4132_ == 0)
{
lean_object* v___x_4133_; 
v___x_4133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4133_, 0, v_e_4129_);
return v___x_4133_;
}
else
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
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0___redArg___boxed(lean_object* v_e_4154_, lean_object* v___y_4155_, lean_object* v___y_4156_){
_start:
{
lean_object* v_res_4157_; 
v_res_4157_ = l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0___redArg(v_e_4154_, v___y_4155_);
lean_dec(v___y_4155_);
return v_res_4157_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0(lean_object* v_e_4158_, lean_object* v___y_4159_, lean_object* v___y_4160_, lean_object* v___y_4161_, lean_object* v___y_4162_){
_start:
{
lean_object* v___x_4164_; 
v___x_4164_ = l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0___redArg(v_e_4158_, v___y_4160_);
return v___x_4164_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0___boxed(lean_object* v_e_4165_, lean_object* v___y_4166_, lean_object* v___y_4167_, lean_object* v___y_4168_, lean_object* v___y_4169_, lean_object* v___y_4170_){
_start:
{
lean_object* v_res_4171_; 
v_res_4171_ = l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0(v_e_4165_, v___y_4166_, v___y_4167_, v___y_4168_, v___y_4169_);
lean_dec(v___y_4169_);
lean_dec_ref(v___y_4168_);
lean_dec(v___y_4167_);
lean_dec_ref(v___y_4166_);
return v_res_4171_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesAnd___lam__0(lean_object* v_localDecl_4175_, lean_object* v___y_4176_, lean_object* v___y_4177_, lean_object* v___y_4178_, lean_object* v___y_4179_){
_start:
{
lean_object* v___x_4181_; lean_object* v___x_4182_; lean_object* v_a_4183_; lean_object* v___x_4185_; uint8_t v_isShared_4186_; uint8_t v_isSharedCheck_4194_; 
v___x_4181_ = l_Lean_LocalDecl_type(v_localDecl_4175_);
v___x_4182_ = l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0___redArg(v___x_4181_, v___y_4177_);
v_a_4183_ = lean_ctor_get(v___x_4182_, 0);
v_isSharedCheck_4194_ = !lean_is_exclusive(v___x_4182_);
if (v_isSharedCheck_4194_ == 0)
{
v___x_4185_ = v___x_4182_;
v_isShared_4186_ = v_isSharedCheck_4194_;
goto v_resetjp_4184_;
}
else
{
lean_inc(v_a_4183_);
lean_dec(v___x_4182_);
v___x_4185_ = lean_box(0);
v_isShared_4186_ = v_isSharedCheck_4194_;
goto v_resetjp_4184_;
}
v_resetjp_4184_:
{
lean_object* v___x_4187_; lean_object* v___x_4188_; uint8_t v___x_4189_; lean_object* v___x_4190_; lean_object* v___x_4192_; 
v___x_4187_ = ((lean_object*)(l_Lean_MVarId_casesAnd___lam__0___closed__1));
v___x_4188_ = lean_unsigned_to_nat(2u);
v___x_4189_ = l_Lean_Expr_isAppOfArity(v_a_4183_, v___x_4187_, v___x_4188_);
lean_dec(v_a_4183_);
v___x_4190_ = lean_box(v___x_4189_);
if (v_isShared_4186_ == 0)
{
lean_ctor_set(v___x_4185_, 0, v___x_4190_);
v___x_4192_ = v___x_4185_;
goto v_reusejp_4191_;
}
else
{
lean_object* v_reuseFailAlloc_4193_; 
v_reuseFailAlloc_4193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4193_, 0, v___x_4190_);
v___x_4192_ = v_reuseFailAlloc_4193_;
goto v_reusejp_4191_;
}
v_reusejp_4191_:
{
return v___x_4192_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesAnd___lam__0___boxed(lean_object* v_localDecl_4195_, lean_object* v___y_4196_, lean_object* v___y_4197_, lean_object* v___y_4198_, lean_object* v___y_4199_, lean_object* v___y_4200_){
_start:
{
lean_object* v_res_4201_; 
v_res_4201_ = l_Lean_MVarId_casesAnd___lam__0(v_localDecl_4195_, v___y_4196_, v___y_4197_, v___y_4198_, v___y_4199_);
lean_dec(v___y_4199_);
lean_dec_ref(v___y_4198_);
lean_dec(v___y_4197_);
lean_dec_ref(v___y_4196_);
lean_dec_ref(v_localDecl_4195_);
return v_res_4201_;
}
}
static lean_object* _init_l_Lean_MVarId_casesAnd___closed__3(void){
_start:
{
lean_object* v___x_4206_; lean_object* v___x_4207_; 
v___x_4206_ = ((lean_object*)(l_Lean_MVarId_casesAnd___closed__2));
v___x_4207_ = l_Lean_MessageData_ofFormat(v___x_4206_);
return v___x_4207_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesAnd(lean_object* v_mvarId_4208_, lean_object* v_a_4209_, lean_object* v_a_4210_, lean_object* v_a_4211_, lean_object* v_a_4212_){
_start:
{
lean_object* v___f_4214_; lean_object* v___x_4215_; 
v___f_4214_ = ((lean_object*)(l_Lean_MVarId_casesAnd___closed__0));
v___x_4215_ = l_Lean_MVarId_casesRec(v_mvarId_4208_, v___f_4214_, v_a_4209_, v_a_4210_, v_a_4211_, v_a_4212_);
if (lean_obj_tag(v___x_4215_) == 0)
{
lean_object* v_a_4216_; lean_object* v___x_4217_; lean_object* v___x_4218_; 
v_a_4216_ = lean_ctor_get(v___x_4215_, 0);
lean_inc(v_a_4216_);
lean_dec_ref(v___x_4215_);
v___x_4217_ = lean_obj_once(&l_Lean_MVarId_casesAnd___closed__3, &l_Lean_MVarId_casesAnd___closed__3_once, _init_l_Lean_MVarId_casesAnd___closed__3);
v___x_4218_ = l_Lean_Meta_exactlyOne(v_a_4216_, v___x_4217_, v_a_4209_, v_a_4210_, v_a_4211_, v_a_4212_);
lean_dec(v_a_4216_);
return v___x_4218_;
}
else
{
lean_object* v_a_4219_; lean_object* v___x_4221_; uint8_t v_isShared_4222_; uint8_t v_isSharedCheck_4226_; 
v_a_4219_ = lean_ctor_get(v___x_4215_, 0);
v_isSharedCheck_4226_ = !lean_is_exclusive(v___x_4215_);
if (v_isSharedCheck_4226_ == 0)
{
v___x_4221_ = v___x_4215_;
v_isShared_4222_ = v_isSharedCheck_4226_;
goto v_resetjp_4220_;
}
else
{
lean_inc(v_a_4219_);
lean_dec(v___x_4215_);
v___x_4221_ = lean_box(0);
v_isShared_4222_ = v_isSharedCheck_4226_;
goto v_resetjp_4220_;
}
v_resetjp_4220_:
{
lean_object* v___x_4224_; 
if (v_isShared_4222_ == 0)
{
v___x_4224_ = v___x_4221_;
goto v_reusejp_4223_;
}
else
{
lean_object* v_reuseFailAlloc_4225_; 
v_reuseFailAlloc_4225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4225_, 0, v_a_4219_);
v___x_4224_ = v_reuseFailAlloc_4225_;
goto v_reusejp_4223_;
}
v_reusejp_4223_:
{
return v___x_4224_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesAnd___boxed(lean_object* v_mvarId_4227_, lean_object* v_a_4228_, lean_object* v_a_4229_, lean_object* v_a_4230_, lean_object* v_a_4231_, lean_object* v_a_4232_){
_start:
{
lean_object* v_res_4233_; 
v_res_4233_ = l_Lean_MVarId_casesAnd(v_mvarId_4227_, v_a_4228_, v_a_4229_, v_a_4230_, v_a_4231_);
lean_dec(v_a_4231_);
lean_dec_ref(v_a_4230_);
lean_dec(v_a_4229_);
lean_dec_ref(v_a_4228_);
return v_res_4233_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_substEqs___lam__0(lean_object* v_localDecl_4234_, lean_object* v___y_4235_, lean_object* v___y_4236_, lean_object* v___y_4237_, lean_object* v___y_4238_){
_start:
{
lean_object* v___x_4240_; lean_object* v___x_4241_; lean_object* v_a_4242_; lean_object* v___x_4244_; uint8_t v_isShared_4245_; uint8_t v_isSharedCheck_4256_; 
v___x_4240_ = l_Lean_LocalDecl_type(v_localDecl_4234_);
v___x_4241_ = l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0___redArg(v___x_4240_, v___y_4236_);
v_a_4242_ = lean_ctor_get(v___x_4241_, 0);
v_isSharedCheck_4256_ = !lean_is_exclusive(v___x_4241_);
if (v_isSharedCheck_4256_ == 0)
{
v___x_4244_ = v___x_4241_;
v_isShared_4245_ = v_isSharedCheck_4256_;
goto v_resetjp_4243_;
}
else
{
lean_inc(v_a_4242_);
lean_dec(v___x_4241_);
v___x_4244_ = lean_box(0);
v_isShared_4245_ = v_isSharedCheck_4256_;
goto v_resetjp_4243_;
}
v_resetjp_4243_:
{
uint8_t v___x_4246_; 
v___x_4246_ = l_Lean_Expr_isEq(v_a_4242_);
if (v___x_4246_ == 0)
{
uint8_t v___x_4247_; lean_object* v___x_4248_; lean_object* v___x_4250_; 
v___x_4247_ = l_Lean_Expr_isHEq(v_a_4242_);
lean_dec(v_a_4242_);
v___x_4248_ = lean_box(v___x_4247_);
if (v_isShared_4245_ == 0)
{
lean_ctor_set(v___x_4244_, 0, v___x_4248_);
v___x_4250_ = v___x_4244_;
goto v_reusejp_4249_;
}
else
{
lean_object* v_reuseFailAlloc_4251_; 
v_reuseFailAlloc_4251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4251_, 0, v___x_4248_);
v___x_4250_ = v_reuseFailAlloc_4251_;
goto v_reusejp_4249_;
}
v_reusejp_4249_:
{
return v___x_4250_;
}
}
else
{
lean_object* v___x_4252_; lean_object* v___x_4254_; 
lean_dec(v_a_4242_);
v___x_4252_ = lean_box(v___x_4246_);
if (v_isShared_4245_ == 0)
{
lean_ctor_set(v___x_4244_, 0, v___x_4252_);
v___x_4254_ = v___x_4244_;
goto v_reusejp_4253_;
}
else
{
lean_object* v_reuseFailAlloc_4255_; 
v_reuseFailAlloc_4255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4255_, 0, v___x_4252_);
v___x_4254_ = v_reuseFailAlloc_4255_;
goto v_reusejp_4253_;
}
v_reusejp_4253_:
{
return v___x_4254_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_substEqs___lam__0___boxed(lean_object* v_localDecl_4257_, lean_object* v___y_4258_, lean_object* v___y_4259_, lean_object* v___y_4260_, lean_object* v___y_4261_, lean_object* v___y_4262_){
_start:
{
lean_object* v_res_4263_; 
v_res_4263_ = l_Lean_MVarId_substEqs___lam__0(v_localDecl_4257_, v___y_4258_, v___y_4259_, v___y_4260_, v___y_4261_);
lean_dec(v___y_4261_);
lean_dec_ref(v___y_4260_);
lean_dec(v___y_4259_);
lean_dec_ref(v___y_4258_);
lean_dec_ref(v_localDecl_4257_);
return v_res_4263_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_substEqs(lean_object* v_mvarId_4265_, lean_object* v_a_4266_, lean_object* v_a_4267_, lean_object* v_a_4268_, lean_object* v_a_4269_){
_start:
{
lean_object* v___f_4271_; lean_object* v___x_4272_; 
v___f_4271_ = ((lean_object*)(l_Lean_MVarId_substEqs___closed__0));
v___x_4272_ = l_Lean_MVarId_casesRec(v_mvarId_4265_, v___f_4271_, v_a_4266_, v_a_4267_, v_a_4268_, v_a_4269_);
if (lean_obj_tag(v___x_4272_) == 0)
{
lean_object* v_a_4273_; lean_object* v___x_4274_; lean_object* v___x_4275_; 
v_a_4273_ = lean_ctor_get(v___x_4272_, 0);
lean_inc(v_a_4273_);
lean_dec_ref(v___x_4272_);
v___x_4274_ = lean_obj_once(&l_Lean_MVarId_casesAnd___closed__3, &l_Lean_MVarId_casesAnd___closed__3_once, _init_l_Lean_MVarId_casesAnd___closed__3);
v___x_4275_ = l_Lean_Meta_ensureAtMostOne(v_a_4273_, v___x_4274_, v_a_4266_, v_a_4267_, v_a_4268_, v_a_4269_);
lean_dec(v_a_4273_);
return v___x_4275_;
}
else
{
lean_object* v_a_4276_; lean_object* v___x_4278_; uint8_t v_isShared_4279_; uint8_t v_isSharedCheck_4283_; 
v_a_4276_ = lean_ctor_get(v___x_4272_, 0);
v_isSharedCheck_4283_ = !lean_is_exclusive(v___x_4272_);
if (v_isSharedCheck_4283_ == 0)
{
v___x_4278_ = v___x_4272_;
v_isShared_4279_ = v_isSharedCheck_4283_;
goto v_resetjp_4277_;
}
else
{
lean_inc(v_a_4276_);
lean_dec(v___x_4272_);
v___x_4278_ = lean_box(0);
v_isShared_4279_ = v_isSharedCheck_4283_;
goto v_resetjp_4277_;
}
v_resetjp_4277_:
{
lean_object* v___x_4281_; 
if (v_isShared_4279_ == 0)
{
v___x_4281_ = v___x_4278_;
goto v_reusejp_4280_;
}
else
{
lean_object* v_reuseFailAlloc_4282_; 
v_reuseFailAlloc_4282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4282_, 0, v_a_4276_);
v___x_4281_ = v_reuseFailAlloc_4282_;
goto v_reusejp_4280_;
}
v_reusejp_4280_:
{
return v___x_4281_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_substEqs___boxed(lean_object* v_mvarId_4284_, lean_object* v_a_4285_, lean_object* v_a_4286_, lean_object* v_a_4287_, lean_object* v_a_4288_, lean_object* v_a_4289_){
_start:
{
lean_object* v_res_4290_; 
v_res_4290_ = l_Lean_MVarId_substEqs(v_mvarId_4284_, v_a_4285_, v_a_4286_, v_a_4287_, v_a_4288_);
lean_dec(v_a_4288_);
lean_dec_ref(v_a_4287_);
lean_dec(v_a_4286_);
lean_dec_ref(v_a_4285_);
return v_res_4290_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal___closed__1(void){
_start:
{
lean_object* v___x_4292_; lean_object* v___x_4293_; 
v___x_4292_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal___closed__0));
v___x_4293_ = l_Lean_stringToMessageData(v___x_4292_);
return v___x_4293_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal(lean_object* v_s_4294_, lean_object* v_a_4295_, lean_object* v_a_4296_, lean_object* v_a_4297_, lean_object* v_a_4298_){
_start:
{
lean_object* v___y_4301_; lean_object* v___y_4302_; lean_object* v___y_4303_; lean_object* v___y_4304_; lean_object* v_toInductionSubgoal_4307_; lean_object* v___x_4309_; uint8_t v_isShared_4310_; uint8_t v_isSharedCheck_4323_; 
v_toInductionSubgoal_4307_ = lean_ctor_get(v_s_4294_, 0);
v_isSharedCheck_4323_ = !lean_is_exclusive(v_s_4294_);
if (v_isSharedCheck_4323_ == 0)
{
lean_object* v_unused_4324_; 
v_unused_4324_ = lean_ctor_get(v_s_4294_, 1);
lean_dec(v_unused_4324_);
v___x_4309_ = v_s_4294_;
v_isShared_4310_ = v_isSharedCheck_4323_;
goto v_resetjp_4308_;
}
else
{
lean_inc(v_toInductionSubgoal_4307_);
lean_dec(v_s_4294_);
v___x_4309_ = lean_box(0);
v_isShared_4310_ = v_isSharedCheck_4323_;
goto v_resetjp_4308_;
}
v___jp_4300_:
{
lean_object* v___x_4305_; lean_object* v___x_4306_; 
v___x_4305_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal___closed__1, &l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal___closed__1_once, _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal___closed__1);
v___x_4306_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected_spec__0___redArg(v___x_4305_, v___y_4301_, v___y_4302_, v___y_4303_, v___y_4304_);
return v___x_4306_;
}
v_resetjp_4308_:
{
lean_object* v_mvarId_4311_; lean_object* v_fields_4312_; lean_object* v___x_4313_; lean_object* v___x_4314_; uint8_t v___x_4315_; 
v_mvarId_4311_ = lean_ctor_get(v_toInductionSubgoal_4307_, 0);
lean_inc(v_mvarId_4311_);
v_fields_4312_ = lean_ctor_get(v_toInductionSubgoal_4307_, 1);
lean_inc_ref(v_fields_4312_);
lean_dec_ref(v_toInductionSubgoal_4307_);
v___x_4313_ = lean_array_get_size(v_fields_4312_);
v___x_4314_ = lean_unsigned_to_nat(1u);
v___x_4315_ = lean_nat_dec_eq(v___x_4313_, v___x_4314_);
if (v___x_4315_ == 0)
{
lean_dec_ref(v_fields_4312_);
lean_dec(v_mvarId_4311_);
lean_del_object(v___x_4309_);
v___y_4301_ = v_a_4295_;
v___y_4302_ = v_a_4296_;
v___y_4303_ = v_a_4297_;
v___y_4304_ = v_a_4298_;
goto v___jp_4300_;
}
else
{
lean_object* v___x_4316_; lean_object* v___x_4317_; 
v___x_4316_ = lean_unsigned_to_nat(0u);
v___x_4317_ = lean_array_fget(v_fields_4312_, v___x_4316_);
lean_dec_ref(v_fields_4312_);
if (lean_obj_tag(v___x_4317_) == 1)
{
lean_object* v_fvarId_4318_; lean_object* v___x_4320_; 
v_fvarId_4318_ = lean_ctor_get(v___x_4317_, 0);
lean_inc(v_fvarId_4318_);
lean_dec_ref(v___x_4317_);
if (v_isShared_4310_ == 0)
{
lean_ctor_set(v___x_4309_, 1, v_fvarId_4318_);
lean_ctor_set(v___x_4309_, 0, v_mvarId_4311_);
v___x_4320_ = v___x_4309_;
goto v_reusejp_4319_;
}
else
{
lean_object* v_reuseFailAlloc_4322_; 
v_reuseFailAlloc_4322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4322_, 0, v_mvarId_4311_);
lean_ctor_set(v_reuseFailAlloc_4322_, 1, v_fvarId_4318_);
v___x_4320_ = v_reuseFailAlloc_4322_;
goto v_reusejp_4319_;
}
v_reusejp_4319_:
{
lean_object* v___x_4321_; 
v___x_4321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4321_, 0, v___x_4320_);
return v___x_4321_;
}
}
else
{
lean_dec(v___x_4317_);
lean_dec(v_mvarId_4311_);
lean_del_object(v___x_4309_);
v___y_4301_ = v_a_4295_;
v___y_4302_ = v_a_4296_;
v___y_4303_ = v_a_4297_;
v___y_4304_ = v_a_4298_;
goto v___jp_4300_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal___boxed(lean_object* v_s_4325_, lean_object* v_a_4326_, lean_object* v_a_4327_, lean_object* v_a_4328_, lean_object* v_a_4329_, lean_object* v_a_4330_){
_start:
{
lean_object* v_res_4331_; 
v_res_4331_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal(v_s_4325_, v_a_4326_, v_a_4327_, v_a_4328_, v_a_4329_);
lean_dec(v_a_4329_);
lean_dec_ref(v_a_4328_);
lean_dec(v_a_4327_);
lean_dec_ref(v_a_4326_);
return v_res_4331_;
}
}
static lean_object* _init_l_Lean_MVarId_byCases___closed__3(void){
_start:
{
lean_object* v___x_4336_; lean_object* v___x_4337_; 
v___x_4336_ = ((lean_object*)(l_Lean_MVarId_byCases___closed__2));
v___x_4337_ = l_Lean_stringToMessageData(v___x_4336_);
return v___x_4337_;
}
}
static lean_object* _init_l_Lean_MVarId_byCases___closed__5(void){
_start:
{
lean_object* v___x_4339_; lean_object* v___x_4340_; 
v___x_4339_ = ((lean_object*)(l_Lean_MVarId_byCases___closed__4));
v___x_4340_ = l_Lean_stringToMessageData(v___x_4339_);
return v___x_4340_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_byCases(lean_object* v_mvarId_4341_, lean_object* v_p_4342_, lean_object* v_hName_4343_, lean_object* v_a_4344_, lean_object* v_a_4345_, lean_object* v_a_4346_, lean_object* v_a_4347_){
_start:
{
lean_object* v___x_4349_; lean_object* v___x_4350_; lean_object* v___x_4351_; lean_object* v___x_4352_; lean_object* v___x_4353_; 
v___x_4349_ = ((lean_object*)(l_Lean_MVarId_byCases___closed__1));
lean_inc_ref_n(v_p_4342_, 3);
v___x_4350_ = l_Lean_mkNot(v_p_4342_);
v___x_4351_ = l_Lean_mkOr(v_p_4342_, v___x_4350_);
v___x_4352_ = l_Lean_mkEM(v_p_4342_);
v___x_4353_ = l_Lean_MVarId_assert(v_mvarId_4341_, v___x_4349_, v___x_4351_, v___x_4352_, v_a_4344_, v_a_4345_, v_a_4346_, v_a_4347_);
if (lean_obj_tag(v___x_4353_) == 0)
{
lean_object* v_a_4354_; uint8_t v___x_4355_; lean_object* v___x_4356_; 
v_a_4354_ = lean_ctor_get(v___x_4353_, 0);
lean_inc(v_a_4354_);
lean_dec_ref(v___x_4353_);
v___x_4355_ = 0;
v___x_4356_ = l_Lean_Meta_intro1Core(v_a_4354_, v___x_4355_, v_a_4344_, v_a_4345_, v_a_4346_, v_a_4347_);
if (lean_obj_tag(v___x_4356_) == 0)
{
lean_object* v_a_4357_; lean_object* v_fst_4358_; lean_object* v_snd_4359_; lean_object* v___x_4361_; uint8_t v_isShared_4362_; uint8_t v_isSharedCheck_4424_; 
v_a_4357_ = lean_ctor_get(v___x_4356_, 0);
lean_inc(v_a_4357_);
lean_dec_ref(v___x_4356_);
v_fst_4358_ = lean_ctor_get(v_a_4357_, 0);
v_snd_4359_ = lean_ctor_get(v_a_4357_, 1);
v_isSharedCheck_4424_ = !lean_is_exclusive(v_a_4357_);
if (v_isSharedCheck_4424_ == 0)
{
v___x_4361_ = v_a_4357_;
v_isShared_4362_ = v_isSharedCheck_4424_;
goto v_resetjp_4360_;
}
else
{
lean_inc(v_snd_4359_);
lean_inc(v_fst_4358_);
lean_dec(v_a_4357_);
v___x_4361_ = lean_box(0);
v_isShared_4362_ = v_isSharedCheck_4424_;
goto v_resetjp_4360_;
}
v_resetjp_4360_:
{
lean_object* v___x_4363_; lean_object* v___x_4364_; lean_object* v___x_4365_; lean_object* v___x_4366_; lean_object* v___x_4367_; lean_object* v___x_4368_; lean_object* v___x_4369_; lean_object* v___x_4370_; lean_object* v___x_4371_; 
v___x_4363_ = lean_box(0);
v___x_4364_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4364_, 0, v_hName_4343_);
lean_ctor_set(v___x_4364_, 1, v___x_4363_);
v___x_4365_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4365_, 0, v___x_4364_);
lean_ctor_set_uint8(v___x_4365_, sizeof(void*)*1, v___x_4355_);
v___x_4366_ = lean_unsigned_to_nat(2u);
v___x_4367_ = lean_mk_empty_array_with_capacity(v___x_4366_);
lean_inc_ref(v___x_4365_);
v___x_4368_ = lean_array_push(v___x_4367_, v___x_4365_);
v___x_4369_ = lean_array_push(v___x_4368_, v___x_4365_);
v___x_4370_ = lean_box(0);
v___x_4371_ = l_Lean_Meta_Cases_cases(v_snd_4359_, v_fst_4358_, v___x_4369_, v___x_4355_, v___x_4370_, v_a_4344_, v_a_4345_, v_a_4346_, v_a_4347_);
if (lean_obj_tag(v___x_4371_) == 0)
{
lean_object* v_a_4372_; lean_object* v___x_4373_; uint8_t v___x_4374_; 
v_a_4372_ = lean_ctor_get(v___x_4371_, 0);
lean_inc(v_a_4372_);
lean_dec_ref(v___x_4371_);
v___x_4373_ = lean_array_get_size(v_a_4372_);
v___x_4374_ = lean_nat_dec_eq(v___x_4373_, v___x_4366_);
if (v___x_4374_ == 0)
{
lean_object* v___x_4375_; lean_object* v___x_4376_; lean_object* v___x_4377_; lean_object* v___x_4378_; lean_object* v___x_4379_; lean_object* v___x_4380_; lean_object* v___x_4381_; 
lean_dec(v_a_4372_);
lean_del_object(v___x_4361_);
v___x_4375_ = lean_obj_once(&l_Lean_MVarId_byCases___closed__3, &l_Lean_MVarId_byCases___closed__3_once, _init_l_Lean_MVarId_byCases___closed__3);
v___x_4376_ = lean_unsigned_to_nat(30u);
v___x_4377_ = l_Lean_inlineExpr(v_p_4342_, v___x_4376_);
v___x_4378_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4378_, 0, v___x_4375_);
lean_ctor_set(v___x_4378_, 1, v___x_4377_);
v___x_4379_ = lean_obj_once(&l_Lean_MVarId_byCases___closed__5, &l_Lean_MVarId_byCases___closed__5_once, _init_l_Lean_MVarId_byCases___closed__5);
v___x_4380_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4380_, 0, v___x_4378_);
lean_ctor_set(v___x_4380_, 1, v___x_4379_);
v___x_4381_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected_spec__0___redArg(v___x_4380_, v_a_4344_, v_a_4345_, v_a_4346_, v_a_4347_);
return v___x_4381_;
}
else
{
lean_object* v___x_4382_; lean_object* v___x_4383_; lean_object* v___x_4384_; 
lean_dec_ref(v_p_4342_);
v___x_4382_ = lean_unsigned_to_nat(0u);
v___x_4383_ = lean_array_fget_borrowed(v_a_4372_, v___x_4382_);
lean_inc(v___x_4383_);
v___x_4384_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal(v___x_4383_, v_a_4344_, v_a_4345_, v_a_4346_, v_a_4347_);
if (lean_obj_tag(v___x_4384_) == 0)
{
lean_object* v_a_4385_; lean_object* v___x_4386_; lean_object* v___x_4387_; lean_object* v___x_4388_; 
v_a_4385_ = lean_ctor_get(v___x_4384_, 0);
lean_inc(v_a_4385_);
lean_dec_ref(v___x_4384_);
v___x_4386_ = lean_unsigned_to_nat(1u);
v___x_4387_ = lean_array_fget(v_a_4372_, v___x_4386_);
lean_dec(v_a_4372_);
v___x_4388_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal(v___x_4387_, v_a_4344_, v_a_4345_, v_a_4346_, v_a_4347_);
if (lean_obj_tag(v___x_4388_) == 0)
{
lean_object* v_a_4389_; lean_object* v___x_4391_; uint8_t v_isShared_4392_; uint8_t v_isSharedCheck_4399_; 
v_a_4389_ = lean_ctor_get(v___x_4388_, 0);
v_isSharedCheck_4399_ = !lean_is_exclusive(v___x_4388_);
if (v_isSharedCheck_4399_ == 0)
{
v___x_4391_ = v___x_4388_;
v_isShared_4392_ = v_isSharedCheck_4399_;
goto v_resetjp_4390_;
}
else
{
lean_inc(v_a_4389_);
lean_dec(v___x_4388_);
v___x_4391_ = lean_box(0);
v_isShared_4392_ = v_isSharedCheck_4399_;
goto v_resetjp_4390_;
}
v_resetjp_4390_:
{
lean_object* v___x_4394_; 
if (v_isShared_4362_ == 0)
{
lean_ctor_set(v___x_4361_, 1, v_a_4389_);
lean_ctor_set(v___x_4361_, 0, v_a_4385_);
v___x_4394_ = v___x_4361_;
goto v_reusejp_4393_;
}
else
{
lean_object* v_reuseFailAlloc_4398_; 
v_reuseFailAlloc_4398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4398_, 0, v_a_4385_);
lean_ctor_set(v_reuseFailAlloc_4398_, 1, v_a_4389_);
v___x_4394_ = v_reuseFailAlloc_4398_;
goto v_reusejp_4393_;
}
v_reusejp_4393_:
{
lean_object* v___x_4396_; 
if (v_isShared_4392_ == 0)
{
lean_ctor_set(v___x_4391_, 0, v___x_4394_);
v___x_4396_ = v___x_4391_;
goto v_reusejp_4395_;
}
else
{
lean_object* v_reuseFailAlloc_4397_; 
v_reuseFailAlloc_4397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4397_, 0, v___x_4394_);
v___x_4396_ = v_reuseFailAlloc_4397_;
goto v_reusejp_4395_;
}
v_reusejp_4395_:
{
return v___x_4396_;
}
}
}
}
else
{
lean_object* v_a_4400_; lean_object* v___x_4402_; uint8_t v_isShared_4403_; uint8_t v_isSharedCheck_4407_; 
lean_dec(v_a_4385_);
lean_del_object(v___x_4361_);
v_a_4400_ = lean_ctor_get(v___x_4388_, 0);
v_isSharedCheck_4407_ = !lean_is_exclusive(v___x_4388_);
if (v_isSharedCheck_4407_ == 0)
{
v___x_4402_ = v___x_4388_;
v_isShared_4403_ = v_isSharedCheck_4407_;
goto v_resetjp_4401_;
}
else
{
lean_inc(v_a_4400_);
lean_dec(v___x_4388_);
v___x_4402_ = lean_box(0);
v_isShared_4403_ = v_isSharedCheck_4407_;
goto v_resetjp_4401_;
}
v_resetjp_4401_:
{
lean_object* v___x_4405_; 
if (v_isShared_4403_ == 0)
{
v___x_4405_ = v___x_4402_;
goto v_reusejp_4404_;
}
else
{
lean_object* v_reuseFailAlloc_4406_; 
v_reuseFailAlloc_4406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4406_, 0, v_a_4400_);
v___x_4405_ = v_reuseFailAlloc_4406_;
goto v_reusejp_4404_;
}
v_reusejp_4404_:
{
return v___x_4405_;
}
}
}
}
else
{
lean_object* v_a_4408_; lean_object* v___x_4410_; uint8_t v_isShared_4411_; uint8_t v_isSharedCheck_4415_; 
lean_dec(v_a_4372_);
lean_del_object(v___x_4361_);
v_a_4408_ = lean_ctor_get(v___x_4384_, 0);
v_isSharedCheck_4415_ = !lean_is_exclusive(v___x_4384_);
if (v_isSharedCheck_4415_ == 0)
{
v___x_4410_ = v___x_4384_;
v_isShared_4411_ = v_isSharedCheck_4415_;
goto v_resetjp_4409_;
}
else
{
lean_inc(v_a_4408_);
lean_dec(v___x_4384_);
v___x_4410_ = lean_box(0);
v_isShared_4411_ = v_isSharedCheck_4415_;
goto v_resetjp_4409_;
}
v_resetjp_4409_:
{
lean_object* v___x_4413_; 
if (v_isShared_4411_ == 0)
{
v___x_4413_ = v___x_4410_;
goto v_reusejp_4412_;
}
else
{
lean_object* v_reuseFailAlloc_4414_; 
v_reuseFailAlloc_4414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4414_, 0, v_a_4408_);
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
lean_object* v_a_4416_; lean_object* v___x_4418_; uint8_t v_isShared_4419_; uint8_t v_isSharedCheck_4423_; 
lean_del_object(v___x_4361_);
lean_dec_ref(v_p_4342_);
v_a_4416_ = lean_ctor_get(v___x_4371_, 0);
v_isSharedCheck_4423_ = !lean_is_exclusive(v___x_4371_);
if (v_isSharedCheck_4423_ == 0)
{
v___x_4418_ = v___x_4371_;
v_isShared_4419_ = v_isSharedCheck_4423_;
goto v_resetjp_4417_;
}
else
{
lean_inc(v_a_4416_);
lean_dec(v___x_4371_);
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
}
else
{
lean_object* v_a_4425_; lean_object* v___x_4427_; uint8_t v_isShared_4428_; uint8_t v_isSharedCheck_4432_; 
lean_dec(v_hName_4343_);
lean_dec_ref(v_p_4342_);
v_a_4425_ = lean_ctor_get(v___x_4356_, 0);
v_isSharedCheck_4432_ = !lean_is_exclusive(v___x_4356_);
if (v_isSharedCheck_4432_ == 0)
{
v___x_4427_ = v___x_4356_;
v_isShared_4428_ = v_isSharedCheck_4432_;
goto v_resetjp_4426_;
}
else
{
lean_inc(v_a_4425_);
lean_dec(v___x_4356_);
v___x_4427_ = lean_box(0);
v_isShared_4428_ = v_isSharedCheck_4432_;
goto v_resetjp_4426_;
}
v_resetjp_4426_:
{
lean_object* v___x_4430_; 
if (v_isShared_4428_ == 0)
{
v___x_4430_ = v___x_4427_;
goto v_reusejp_4429_;
}
else
{
lean_object* v_reuseFailAlloc_4431_; 
v_reuseFailAlloc_4431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4431_, 0, v_a_4425_);
v___x_4430_ = v_reuseFailAlloc_4431_;
goto v_reusejp_4429_;
}
v_reusejp_4429_:
{
return v___x_4430_;
}
}
}
}
else
{
lean_object* v_a_4433_; lean_object* v___x_4435_; uint8_t v_isShared_4436_; uint8_t v_isSharedCheck_4440_; 
lean_dec(v_hName_4343_);
lean_dec_ref(v_p_4342_);
v_a_4433_ = lean_ctor_get(v___x_4353_, 0);
v_isSharedCheck_4440_ = !lean_is_exclusive(v___x_4353_);
if (v_isSharedCheck_4440_ == 0)
{
v___x_4435_ = v___x_4353_;
v_isShared_4436_ = v_isSharedCheck_4440_;
goto v_resetjp_4434_;
}
else
{
lean_inc(v_a_4433_);
lean_dec(v___x_4353_);
v___x_4435_ = lean_box(0);
v_isShared_4436_ = v_isSharedCheck_4440_;
goto v_resetjp_4434_;
}
v_resetjp_4434_:
{
lean_object* v___x_4438_; 
if (v_isShared_4436_ == 0)
{
v___x_4438_ = v___x_4435_;
goto v_reusejp_4437_;
}
else
{
lean_object* v_reuseFailAlloc_4439_; 
v_reuseFailAlloc_4439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4439_, 0, v_a_4433_);
v___x_4438_ = v_reuseFailAlloc_4439_;
goto v_reusejp_4437_;
}
v_reusejp_4437_:
{
return v___x_4438_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_byCases___boxed(lean_object* v_mvarId_4441_, lean_object* v_p_4442_, lean_object* v_hName_4443_, lean_object* v_a_4444_, lean_object* v_a_4445_, lean_object* v_a_4446_, lean_object* v_a_4447_, lean_object* v_a_4448_){
_start:
{
lean_object* v_res_4449_; 
v_res_4449_ = l_Lean_MVarId_byCases(v_mvarId_4441_, v_p_4442_, v_hName_4443_, v_a_4444_, v_a_4445_, v_a_4446_, v_a_4447_);
lean_dec(v_a_4447_);
lean_dec_ref(v_a_4446_);
lean_dec(v_a_4445_);
lean_dec_ref(v_a_4444_);
return v_res_4449_;
}
}
static lean_object* _init_l_Lean_MVarId_byCasesDec___closed__2(void){
_start:
{
lean_object* v___x_4453_; lean_object* v___x_4454_; lean_object* v___x_4455_; 
v___x_4453_ = lean_box(0);
v___x_4454_ = ((lean_object*)(l_Lean_MVarId_byCasesDec___closed__1));
v___x_4455_ = l_Lean_mkConst(v___x_4454_, v___x_4453_);
return v___x_4455_;
}
}
static lean_object* _init_l_Lean_MVarId_byCasesDec___closed__4(void){
_start:
{
lean_object* v___x_4457_; lean_object* v___x_4458_; 
v___x_4457_ = ((lean_object*)(l_Lean_MVarId_byCasesDec___closed__3));
v___x_4458_ = l_Lean_stringToMessageData(v___x_4457_);
return v___x_4458_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_byCasesDec(lean_object* v_mvarId_4459_, lean_object* v_p_4460_, lean_object* v_dec_4461_, lean_object* v_hName_4462_, lean_object* v_a_4463_, lean_object* v_a_4464_, lean_object* v_a_4465_, lean_object* v_a_4466_){
_start:
{
lean_object* v___x_4468_; lean_object* v___x_4469_; lean_object* v___x_4470_; lean_object* v___x_4471_; lean_object* v___x_4472_; 
v___x_4468_ = ((lean_object*)(l_Lean_MVarId_byCases___closed__1));
v___x_4469_ = lean_box(0);
v___x_4470_ = lean_obj_once(&l_Lean_MVarId_byCasesDec___closed__2, &l_Lean_MVarId_byCasesDec___closed__2_once, _init_l_Lean_MVarId_byCasesDec___closed__2);
lean_inc_ref(v_p_4460_);
v___x_4471_ = l_Lean_Expr_app___override(v___x_4470_, v_p_4460_);
v___x_4472_ = l_Lean_MVarId_assert(v_mvarId_4459_, v___x_4468_, v___x_4471_, v_dec_4461_, v_a_4463_, v_a_4464_, v_a_4465_, v_a_4466_);
if (lean_obj_tag(v___x_4472_) == 0)
{
lean_object* v_a_4473_; uint8_t v___x_4474_; lean_object* v___x_4475_; 
v_a_4473_ = lean_ctor_get(v___x_4472_, 0);
lean_inc(v_a_4473_);
lean_dec_ref(v___x_4472_);
v___x_4474_ = 0;
v___x_4475_ = l_Lean_Meta_intro1Core(v_a_4473_, v___x_4474_, v_a_4463_, v_a_4464_, v_a_4465_, v_a_4466_);
if (lean_obj_tag(v___x_4475_) == 0)
{
lean_object* v_a_4476_; lean_object* v_fst_4477_; lean_object* v_snd_4478_; lean_object* v___x_4480_; uint8_t v_isShared_4481_; uint8_t v_isSharedCheck_4542_; 
v_a_4476_ = lean_ctor_get(v___x_4475_, 0);
lean_inc(v_a_4476_);
lean_dec_ref(v___x_4475_);
v_fst_4477_ = lean_ctor_get(v_a_4476_, 0);
v_snd_4478_ = lean_ctor_get(v_a_4476_, 1);
v_isSharedCheck_4542_ = !lean_is_exclusive(v_a_4476_);
if (v_isSharedCheck_4542_ == 0)
{
v___x_4480_ = v_a_4476_;
v_isShared_4481_ = v_isSharedCheck_4542_;
goto v_resetjp_4479_;
}
else
{
lean_inc(v_snd_4478_);
lean_inc(v_fst_4477_);
lean_dec(v_a_4476_);
v___x_4480_ = lean_box(0);
v_isShared_4481_ = v_isSharedCheck_4542_;
goto v_resetjp_4479_;
}
v_resetjp_4479_:
{
lean_object* v___x_4482_; lean_object* v___x_4483_; lean_object* v___x_4484_; lean_object* v___x_4485_; lean_object* v___x_4486_; lean_object* v___x_4487_; lean_object* v___x_4488_; lean_object* v___x_4489_; 
v___x_4482_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4482_, 0, v_hName_4462_);
lean_ctor_set(v___x_4482_, 1, v___x_4469_);
v___x_4483_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4483_, 0, v___x_4482_);
lean_ctor_set_uint8(v___x_4483_, sizeof(void*)*1, v___x_4474_);
v___x_4484_ = lean_unsigned_to_nat(2u);
v___x_4485_ = lean_mk_empty_array_with_capacity(v___x_4484_);
lean_inc_ref(v___x_4483_);
v___x_4486_ = lean_array_push(v___x_4485_, v___x_4483_);
v___x_4487_ = lean_array_push(v___x_4486_, v___x_4483_);
v___x_4488_ = lean_box(0);
v___x_4489_ = l_Lean_Meta_Cases_cases(v_snd_4478_, v_fst_4477_, v___x_4487_, v___x_4474_, v___x_4488_, v_a_4463_, v_a_4464_, v_a_4465_, v_a_4466_);
if (lean_obj_tag(v___x_4489_) == 0)
{
lean_object* v_a_4490_; lean_object* v___x_4491_; uint8_t v___x_4492_; 
v_a_4490_ = lean_ctor_get(v___x_4489_, 0);
lean_inc(v_a_4490_);
lean_dec_ref(v___x_4489_);
v___x_4491_ = lean_array_get_size(v_a_4490_);
v___x_4492_ = lean_nat_dec_eq(v___x_4491_, v___x_4484_);
if (v___x_4492_ == 0)
{
lean_object* v___x_4493_; lean_object* v___x_4494_; lean_object* v___x_4495_; lean_object* v___x_4496_; lean_object* v___x_4497_; lean_object* v___x_4498_; lean_object* v___x_4499_; 
lean_dec(v_a_4490_);
lean_del_object(v___x_4480_);
v___x_4493_ = lean_obj_once(&l_Lean_MVarId_byCasesDec___closed__4, &l_Lean_MVarId_byCasesDec___closed__4_once, _init_l_Lean_MVarId_byCasesDec___closed__4);
v___x_4494_ = lean_unsigned_to_nat(30u);
v___x_4495_ = l_Lean_inlineExpr(v_p_4460_, v___x_4494_);
v___x_4496_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4496_, 0, v___x_4493_);
lean_ctor_set(v___x_4496_, 1, v___x_4495_);
v___x_4497_ = lean_obj_once(&l_Lean_MVarId_byCases___closed__5, &l_Lean_MVarId_byCases___closed__5_once, _init_l_Lean_MVarId_byCases___closed__5);
v___x_4498_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4498_, 0, v___x_4496_);
lean_ctor_set(v___x_4498_, 1, v___x_4497_);
v___x_4499_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected_spec__0___redArg(v___x_4498_, v_a_4463_, v_a_4464_, v_a_4465_, v_a_4466_);
return v___x_4499_;
}
else
{
lean_object* v___x_4500_; lean_object* v___x_4501_; lean_object* v___x_4502_; 
lean_dec_ref(v_p_4460_);
v___x_4500_ = lean_unsigned_to_nat(1u);
v___x_4501_ = lean_array_fget_borrowed(v_a_4490_, v___x_4500_);
lean_inc(v___x_4501_);
v___x_4502_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal(v___x_4501_, v_a_4463_, v_a_4464_, v_a_4465_, v_a_4466_);
if (lean_obj_tag(v___x_4502_) == 0)
{
lean_object* v_a_4503_; lean_object* v___x_4504_; lean_object* v___x_4505_; lean_object* v___x_4506_; 
v_a_4503_ = lean_ctor_get(v___x_4502_, 0);
lean_inc(v_a_4503_);
lean_dec_ref(v___x_4502_);
v___x_4504_ = lean_unsigned_to_nat(0u);
v___x_4505_ = lean_array_fget(v_a_4490_, v___x_4504_);
lean_dec(v_a_4490_);
v___x_4506_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal(v___x_4505_, v_a_4463_, v_a_4464_, v_a_4465_, v_a_4466_);
if (lean_obj_tag(v___x_4506_) == 0)
{
lean_object* v_a_4507_; lean_object* v___x_4509_; uint8_t v_isShared_4510_; uint8_t v_isSharedCheck_4517_; 
v_a_4507_ = lean_ctor_get(v___x_4506_, 0);
v_isSharedCheck_4517_ = !lean_is_exclusive(v___x_4506_);
if (v_isSharedCheck_4517_ == 0)
{
v___x_4509_ = v___x_4506_;
v_isShared_4510_ = v_isSharedCheck_4517_;
goto v_resetjp_4508_;
}
else
{
lean_inc(v_a_4507_);
lean_dec(v___x_4506_);
v___x_4509_ = lean_box(0);
v_isShared_4510_ = v_isSharedCheck_4517_;
goto v_resetjp_4508_;
}
v_resetjp_4508_:
{
lean_object* v___x_4512_; 
if (v_isShared_4481_ == 0)
{
lean_ctor_set(v___x_4480_, 1, v_a_4507_);
lean_ctor_set(v___x_4480_, 0, v_a_4503_);
v___x_4512_ = v___x_4480_;
goto v_reusejp_4511_;
}
else
{
lean_object* v_reuseFailAlloc_4516_; 
v_reuseFailAlloc_4516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4516_, 0, v_a_4503_);
lean_ctor_set(v_reuseFailAlloc_4516_, 1, v_a_4507_);
v___x_4512_ = v_reuseFailAlloc_4516_;
goto v_reusejp_4511_;
}
v_reusejp_4511_:
{
lean_object* v___x_4514_; 
if (v_isShared_4510_ == 0)
{
lean_ctor_set(v___x_4509_, 0, v___x_4512_);
v___x_4514_ = v___x_4509_;
goto v_reusejp_4513_;
}
else
{
lean_object* v_reuseFailAlloc_4515_; 
v_reuseFailAlloc_4515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4515_, 0, v___x_4512_);
v___x_4514_ = v_reuseFailAlloc_4515_;
goto v_reusejp_4513_;
}
v_reusejp_4513_:
{
return v___x_4514_;
}
}
}
}
else
{
lean_object* v_a_4518_; lean_object* v___x_4520_; uint8_t v_isShared_4521_; uint8_t v_isSharedCheck_4525_; 
lean_dec(v_a_4503_);
lean_del_object(v___x_4480_);
v_a_4518_ = lean_ctor_get(v___x_4506_, 0);
v_isSharedCheck_4525_ = !lean_is_exclusive(v___x_4506_);
if (v_isSharedCheck_4525_ == 0)
{
v___x_4520_ = v___x_4506_;
v_isShared_4521_ = v_isSharedCheck_4525_;
goto v_resetjp_4519_;
}
else
{
lean_inc(v_a_4518_);
lean_dec(v___x_4506_);
v___x_4520_ = lean_box(0);
v_isShared_4521_ = v_isSharedCheck_4525_;
goto v_resetjp_4519_;
}
v_resetjp_4519_:
{
lean_object* v___x_4523_; 
if (v_isShared_4521_ == 0)
{
v___x_4523_ = v___x_4520_;
goto v_reusejp_4522_;
}
else
{
lean_object* v_reuseFailAlloc_4524_; 
v_reuseFailAlloc_4524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4524_, 0, v_a_4518_);
v___x_4523_ = v_reuseFailAlloc_4524_;
goto v_reusejp_4522_;
}
v_reusejp_4522_:
{
return v___x_4523_;
}
}
}
}
else
{
lean_object* v_a_4526_; lean_object* v___x_4528_; uint8_t v_isShared_4529_; uint8_t v_isSharedCheck_4533_; 
lean_dec(v_a_4490_);
lean_del_object(v___x_4480_);
v_a_4526_ = lean_ctor_get(v___x_4502_, 0);
v_isSharedCheck_4533_ = !lean_is_exclusive(v___x_4502_);
if (v_isSharedCheck_4533_ == 0)
{
v___x_4528_ = v___x_4502_;
v_isShared_4529_ = v_isSharedCheck_4533_;
goto v_resetjp_4527_;
}
else
{
lean_inc(v_a_4526_);
lean_dec(v___x_4502_);
v___x_4528_ = lean_box(0);
v_isShared_4529_ = v_isSharedCheck_4533_;
goto v_resetjp_4527_;
}
v_resetjp_4527_:
{
lean_object* v___x_4531_; 
if (v_isShared_4529_ == 0)
{
v___x_4531_ = v___x_4528_;
goto v_reusejp_4530_;
}
else
{
lean_object* v_reuseFailAlloc_4532_; 
v_reuseFailAlloc_4532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4532_, 0, v_a_4526_);
v___x_4531_ = v_reuseFailAlloc_4532_;
goto v_reusejp_4530_;
}
v_reusejp_4530_:
{
return v___x_4531_;
}
}
}
}
}
else
{
lean_object* v_a_4534_; lean_object* v___x_4536_; uint8_t v_isShared_4537_; uint8_t v_isSharedCheck_4541_; 
lean_del_object(v___x_4480_);
lean_dec_ref(v_p_4460_);
v_a_4534_ = lean_ctor_get(v___x_4489_, 0);
v_isSharedCheck_4541_ = !lean_is_exclusive(v___x_4489_);
if (v_isSharedCheck_4541_ == 0)
{
v___x_4536_ = v___x_4489_;
v_isShared_4537_ = v_isSharedCheck_4541_;
goto v_resetjp_4535_;
}
else
{
lean_inc(v_a_4534_);
lean_dec(v___x_4489_);
v___x_4536_ = lean_box(0);
v_isShared_4537_ = v_isSharedCheck_4541_;
goto v_resetjp_4535_;
}
v_resetjp_4535_:
{
lean_object* v___x_4539_; 
if (v_isShared_4537_ == 0)
{
v___x_4539_ = v___x_4536_;
goto v_reusejp_4538_;
}
else
{
lean_object* v_reuseFailAlloc_4540_; 
v_reuseFailAlloc_4540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4540_, 0, v_a_4534_);
v___x_4539_ = v_reuseFailAlloc_4540_;
goto v_reusejp_4538_;
}
v_reusejp_4538_:
{
return v___x_4539_;
}
}
}
}
}
else
{
lean_object* v_a_4543_; lean_object* v___x_4545_; uint8_t v_isShared_4546_; uint8_t v_isSharedCheck_4550_; 
lean_dec(v_hName_4462_);
lean_dec_ref(v_p_4460_);
v_a_4543_ = lean_ctor_get(v___x_4475_, 0);
v_isSharedCheck_4550_ = !lean_is_exclusive(v___x_4475_);
if (v_isSharedCheck_4550_ == 0)
{
v___x_4545_ = v___x_4475_;
v_isShared_4546_ = v_isSharedCheck_4550_;
goto v_resetjp_4544_;
}
else
{
lean_inc(v_a_4543_);
lean_dec(v___x_4475_);
v___x_4545_ = lean_box(0);
v_isShared_4546_ = v_isSharedCheck_4550_;
goto v_resetjp_4544_;
}
v_resetjp_4544_:
{
lean_object* v___x_4548_; 
if (v_isShared_4546_ == 0)
{
v___x_4548_ = v___x_4545_;
goto v_reusejp_4547_;
}
else
{
lean_object* v_reuseFailAlloc_4549_; 
v_reuseFailAlloc_4549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4549_, 0, v_a_4543_);
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
else
{
lean_object* v_a_4551_; lean_object* v___x_4553_; uint8_t v_isShared_4554_; uint8_t v_isSharedCheck_4558_; 
lean_dec(v_hName_4462_);
lean_dec_ref(v_p_4460_);
v_a_4551_ = lean_ctor_get(v___x_4472_, 0);
v_isSharedCheck_4558_ = !lean_is_exclusive(v___x_4472_);
if (v_isSharedCheck_4558_ == 0)
{
v___x_4553_ = v___x_4472_;
v_isShared_4554_ = v_isSharedCheck_4558_;
goto v_resetjp_4552_;
}
else
{
lean_inc(v_a_4551_);
lean_dec(v___x_4472_);
v___x_4553_ = lean_box(0);
v_isShared_4554_ = v_isSharedCheck_4558_;
goto v_resetjp_4552_;
}
v_resetjp_4552_:
{
lean_object* v___x_4556_; 
if (v_isShared_4554_ == 0)
{
v___x_4556_ = v___x_4553_;
goto v_reusejp_4555_;
}
else
{
lean_object* v_reuseFailAlloc_4557_; 
v_reuseFailAlloc_4557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4557_, 0, v_a_4551_);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_byCasesDec___boxed(lean_object* v_mvarId_4559_, lean_object* v_p_4560_, lean_object* v_dec_4561_, lean_object* v_hName_4562_, lean_object* v_a_4563_, lean_object* v_a_4564_, lean_object* v_a_4565_, lean_object* v_a_4566_, lean_object* v_a_4567_){
_start:
{
lean_object* v_res_4568_; 
v_res_4568_ = l_Lean_MVarId_byCasesDec(v_mvarId_4559_, v_p_4560_, v_dec_4561_, v_hName_4562_, v_a_4563_, v_a_4564_, v_a_4565_, v_a_4566_);
lean_dec(v_a_4566_);
lean_dec_ref(v_a_4565_);
lean_dec(v_a_4564_);
lean_dec_ref(v_a_4563_);
return v_res_4568_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4620_; lean_object* v___x_4621_; lean_object* v___x_4622_; 
v___x_4620_ = lean_unsigned_to_nat(4241171151u);
v___x_4621_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_));
v___x_4622_ = l_Lean_Name_num___override(v___x_4621_, v___x_4620_);
return v___x_4622_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4624_; lean_object* v___x_4625_; lean_object* v___x_4626_; 
v___x_4624_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_));
v___x_4625_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_);
v___x_4626_ = l_Lean_Name_str___override(v___x_4625_, v___x_4624_);
return v___x_4626_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4628_; lean_object* v___x_4629_; lean_object* v___x_4630_; 
v___x_4628_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_));
v___x_4629_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_);
v___x_4630_ = l_Lean_Name_str___override(v___x_4629_, v___x_4628_);
return v___x_4630_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4631_; lean_object* v___x_4632_; lean_object* v___x_4633_; 
v___x_4631_ = lean_unsigned_to_nat(2u);
v___x_4632_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_);
v___x_4633_ = l_Lean_Name_num___override(v___x_4632_, v___x_4631_);
return v___x_4633_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4635_; uint8_t v___x_4636_; lean_object* v___x_4637_; lean_object* v___x_4638_; 
v___x_4635_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_));
v___x_4636_ = 0;
v___x_4637_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_);
v___x_4638_ = l_Lean_registerTraceClass(v___x_4635_, v___x_4636_, v___x_4637_);
return v___x_4638_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2____boxed(lean_object* v_a_4639_){
_start:
{
lean_object* v_res_4640_; 
v_res_4640_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_();
return v_res_4640_;
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
