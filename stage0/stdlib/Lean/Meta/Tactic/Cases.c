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
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Meta_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_mkCtorIdxName(lean_object*);
lean_object* l_Lean_Meta_mkSparseCasesOn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
size_t v_x_2554__boxed_908_; size_t v_x_2555__boxed_909_; lean_object* v_res_910_; 
v_x_2554__boxed_908_ = lean_unbox_usize(v_x_904_);
lean_dec(v_x_904_);
v_x_2555__boxed_909_ = lean_unbox_usize(v_x_905_);
lean_dec(v_x_905_);
v_res_910_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg(v_x_903_, v_x_2554__boxed_908_, v_x_2555__boxed_909_, v_x_906_, v_x_907_);
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
lean_object* v___x_922_; lean_object* v_mctx_923_; lean_object* v_cache_924_; lean_object* v_zetaDeltaFVarIds_925_; lean_object* v_postponed_926_; lean_object* v_diag_927_; lean_object* v___x_929_; uint8_t v_isShared_930_; uint8_t v_isSharedCheck_956_; 
v___x_922_ = lean_st_ref_take(v___y_920_);
v_mctx_923_ = lean_ctor_get(v___x_922_, 0);
v_cache_924_ = lean_ctor_get(v___x_922_, 1);
v_zetaDeltaFVarIds_925_ = lean_ctor_get(v___x_922_, 2);
v_postponed_926_ = lean_ctor_get(v___x_922_, 3);
v_diag_927_ = lean_ctor_get(v___x_922_, 4);
v_isSharedCheck_956_ = !lean_is_exclusive(v___x_922_);
if (v_isSharedCheck_956_ == 0)
{
v___x_929_ = v___x_922_;
v_isShared_930_ = v_isSharedCheck_956_;
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
v_isShared_930_ = v_isSharedCheck_956_;
goto v_resetjp_928_;
}
v_resetjp_928_:
{
lean_object* v_depth_931_; lean_object* v_levelAssignDepth_932_; lean_object* v_lmvarCounter_933_; lean_object* v_mvarCounter_934_; lean_object* v_lDecls_935_; lean_object* v_decls_936_; lean_object* v_userNames_937_; lean_object* v_lAssignment_938_; lean_object* v_eAssignment_939_; lean_object* v_dAssignment_940_; lean_object* v_synthNormMemo_941_; lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_955_; 
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
v_synthNormMemo_941_ = lean_ctor_get(v_mctx_923_, 10);
v_isSharedCheck_955_ = !lean_is_exclusive(v_mctx_923_);
if (v_isSharedCheck_955_ == 0)
{
v___x_943_ = v_mctx_923_;
v_isShared_944_ = v_isSharedCheck_955_;
goto v_resetjp_942_;
}
else
{
lean_inc(v_synthNormMemo_941_);
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
v___x_943_ = lean_box(0);
v_isShared_944_ = v_isSharedCheck_955_;
goto v_resetjp_942_;
}
v_resetjp_942_:
{
lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_948_; 
v___x_945_ = lean_box(0);
v___x_946_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1___redArg(v_eAssignment_939_, v_mvarId_918_, v_val_919_);
if (v_isShared_944_ == 0)
{
lean_ctor_set(v___x_943_, 8, v___x_946_);
v___x_948_ = v___x_943_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v_depth_931_);
lean_ctor_set(v_reuseFailAlloc_954_, 1, v_levelAssignDepth_932_);
lean_ctor_set(v_reuseFailAlloc_954_, 2, v_lmvarCounter_933_);
lean_ctor_set(v_reuseFailAlloc_954_, 3, v_mvarCounter_934_);
lean_ctor_set(v_reuseFailAlloc_954_, 4, v_lDecls_935_);
lean_ctor_set(v_reuseFailAlloc_954_, 5, v_decls_936_);
lean_ctor_set(v_reuseFailAlloc_954_, 6, v_userNames_937_);
lean_ctor_set(v_reuseFailAlloc_954_, 7, v_lAssignment_938_);
lean_ctor_set(v_reuseFailAlloc_954_, 8, v___x_946_);
lean_ctor_set(v_reuseFailAlloc_954_, 9, v_dAssignment_940_);
lean_ctor_set(v_reuseFailAlloc_954_, 10, v_synthNormMemo_941_);
v___x_948_ = v_reuseFailAlloc_954_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
lean_object* v___x_950_; 
if (v_isShared_930_ == 0)
{
lean_ctor_set(v___x_929_, 0, v___x_948_);
v___x_950_ = v___x_929_;
goto v_reusejp_949_;
}
else
{
lean_object* v_reuseFailAlloc_953_; 
v_reuseFailAlloc_953_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_953_, 0, v___x_948_);
lean_ctor_set(v_reuseFailAlloc_953_, 1, v_cache_924_);
lean_ctor_set(v_reuseFailAlloc_953_, 2, v_zetaDeltaFVarIds_925_);
lean_ctor_set(v_reuseFailAlloc_953_, 3, v_postponed_926_);
lean_ctor_set(v_reuseFailAlloc_953_, 4, v_diag_927_);
v___x_950_ = v_reuseFailAlloc_953_;
goto v_reusejp_949_;
}
v_reusejp_949_:
{
lean_object* v___x_951_; lean_object* v___x_952_; 
v___x_951_ = lean_st_ref_put(v___y_920_, v___x_950_);
v___x_952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_952_, 0, v___x_945_);
return v___x_952_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1___redArg___boxed(lean_object* v_mvarId_957_, lean_object* v_val_958_, lean_object* v___y_959_, lean_object* v___y_960_){
_start:
{
lean_object* v_res_961_; 
v_res_961_ = l_Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1___redArg(v_mvarId_957_, v_val_958_, v___y_959_);
lean_dec(v___y_959_);
return v_res_961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeTargetsEq___lam__2(lean_object* v_mvarId_962_, lean_object* v___x_963_, lean_object* v_motiveType_964_, lean_object* v___f_965_, lean_object* v_targets_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_){
_start:
{
lean_object* v___x_972_; 
lean_inc(v_mvarId_962_);
v___x_972_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_962_, v___x_963_, v___y_967_, v___y_968_, v___y_969_, v___y_970_);
if (lean_obj_tag(v___x_972_) == 0)
{
uint8_t v___x_973_; lean_object* v___x_974_; 
lean_dec_ref_known(v___x_972_, 1);
v___x_973_ = 0;
v___x_974_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_generalizeTargetsEq_spec__0___redArg(v_motiveType_964_, v___f_965_, v___x_973_, v___x_973_, v___y_967_, v___y_968_, v___y_969_, v___y_970_);
if (lean_obj_tag(v___x_974_) == 0)
{
lean_object* v_a_975_; lean_object* v_fst_976_; lean_object* v_snd_977_; lean_object* v___x_978_; 
v_a_975_ = lean_ctor_get(v___x_974_, 0);
lean_inc(v_a_975_);
lean_dec_ref_known(v___x_974_, 1);
v_fst_976_ = lean_ctor_get(v_a_975_, 0);
lean_inc(v_fst_976_);
v_snd_977_ = lean_ctor_get(v_a_975_, 1);
lean_inc(v_snd_977_);
lean_dec(v_a_975_);
lean_inc(v_mvarId_962_);
v___x_978_ = l_Lean_MVarId_getTag(v_mvarId_962_, v___y_967_, v___y_968_, v___y_969_, v___y_970_);
if (lean_obj_tag(v___x_978_) == 0)
{
lean_object* v_a_979_; lean_object* v___x_980_; 
v_a_979_ = lean_ctor_get(v___x_978_, 0);
lean_inc(v_a_979_);
lean_dec_ref_known(v___x_978_, 1);
v___x_980_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_fst_976_, v_a_979_, v___y_967_, v___y_968_, v___y_969_, v___y_970_);
if (lean_obj_tag(v___x_980_) == 0)
{
lean_object* v_a_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_986_; uint8_t v_isShared_987_; uint8_t v_isSharedCheck_992_; 
v_a_981_ = lean_ctor_get(v___x_980_, 0);
lean_inc_n(v_a_981_, 2);
lean_dec_ref_known(v___x_980_, 1);
v___x_982_ = l_Lean_mkAppN(v_a_981_, v_targets_966_);
v___x_983_ = l_Lean_mkAppN(v___x_982_, v_snd_977_);
lean_dec(v_snd_977_);
v___x_984_ = l_Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1___redArg(v_mvarId_962_, v___x_983_, v___y_968_);
v_isSharedCheck_992_ = !lean_is_exclusive(v___x_984_);
if (v_isSharedCheck_992_ == 0)
{
lean_object* v_unused_993_; 
v_unused_993_ = lean_ctor_get(v___x_984_, 0);
lean_dec(v_unused_993_);
v___x_986_ = v___x_984_;
v_isShared_987_ = v_isSharedCheck_992_;
goto v_resetjp_985_;
}
else
{
lean_dec(v___x_984_);
v___x_986_ = lean_box(0);
v_isShared_987_ = v_isSharedCheck_992_;
goto v_resetjp_985_;
}
v_resetjp_985_:
{
lean_object* v___x_988_; lean_object* v___x_990_; 
v___x_988_ = l_Lean_Expr_mvarId_x21(v_a_981_);
lean_dec(v_a_981_);
if (v_isShared_987_ == 0)
{
lean_ctor_set(v___x_986_, 0, v___x_988_);
v___x_990_ = v___x_986_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v___x_988_);
v___x_990_ = v_reuseFailAlloc_991_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
return v___x_990_;
}
}
}
else
{
lean_object* v_a_994_; lean_object* v___x_996_; uint8_t v_isShared_997_; uint8_t v_isSharedCheck_1001_; 
lean_dec(v_snd_977_);
lean_dec(v_mvarId_962_);
v_a_994_ = lean_ctor_get(v___x_980_, 0);
v_isSharedCheck_1001_ = !lean_is_exclusive(v___x_980_);
if (v_isSharedCheck_1001_ == 0)
{
v___x_996_ = v___x_980_;
v_isShared_997_ = v_isSharedCheck_1001_;
goto v_resetjp_995_;
}
else
{
lean_inc(v_a_994_);
lean_dec(v___x_980_);
v___x_996_ = lean_box(0);
v_isShared_997_ = v_isSharedCheck_1001_;
goto v_resetjp_995_;
}
v_resetjp_995_:
{
lean_object* v___x_999_; 
if (v_isShared_997_ == 0)
{
v___x_999_ = v___x_996_;
goto v_reusejp_998_;
}
else
{
lean_object* v_reuseFailAlloc_1000_; 
v_reuseFailAlloc_1000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1000_, 0, v_a_994_);
v___x_999_ = v_reuseFailAlloc_1000_;
goto v_reusejp_998_;
}
v_reusejp_998_:
{
return v___x_999_;
}
}
}
}
else
{
lean_object* v_a_1002_; lean_object* v___x_1004_; uint8_t v_isShared_1005_; uint8_t v_isSharedCheck_1009_; 
lean_dec(v_snd_977_);
lean_dec(v_fst_976_);
lean_dec(v_mvarId_962_);
v_a_1002_ = lean_ctor_get(v___x_978_, 0);
v_isSharedCheck_1009_ = !lean_is_exclusive(v___x_978_);
if (v_isSharedCheck_1009_ == 0)
{
v___x_1004_ = v___x_978_;
v_isShared_1005_ = v_isSharedCheck_1009_;
goto v_resetjp_1003_;
}
else
{
lean_inc(v_a_1002_);
lean_dec(v___x_978_);
v___x_1004_ = lean_box(0);
v_isShared_1005_ = v_isSharedCheck_1009_;
goto v_resetjp_1003_;
}
v_resetjp_1003_:
{
lean_object* v___x_1007_; 
if (v_isShared_1005_ == 0)
{
v___x_1007_ = v___x_1004_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1008_; 
v_reuseFailAlloc_1008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1008_, 0, v_a_1002_);
v___x_1007_ = v_reuseFailAlloc_1008_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
return v___x_1007_;
}
}
}
}
else
{
lean_object* v_a_1010_; lean_object* v___x_1012_; uint8_t v_isShared_1013_; uint8_t v_isSharedCheck_1017_; 
lean_dec(v_mvarId_962_);
v_a_1010_ = lean_ctor_get(v___x_974_, 0);
v_isSharedCheck_1017_ = !lean_is_exclusive(v___x_974_);
if (v_isSharedCheck_1017_ == 0)
{
v___x_1012_ = v___x_974_;
v_isShared_1013_ = v_isSharedCheck_1017_;
goto v_resetjp_1011_;
}
else
{
lean_inc(v_a_1010_);
lean_dec(v___x_974_);
v___x_1012_ = lean_box(0);
v_isShared_1013_ = v_isSharedCheck_1017_;
goto v_resetjp_1011_;
}
v_resetjp_1011_:
{
lean_object* v___x_1015_; 
if (v_isShared_1013_ == 0)
{
v___x_1015_ = v___x_1012_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v_a_1010_);
v___x_1015_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
return v___x_1015_;
}
}
}
}
else
{
lean_object* v_a_1018_; lean_object* v___x_1020_; uint8_t v_isShared_1021_; uint8_t v_isSharedCheck_1025_; 
lean_dec_ref(v___f_965_);
lean_dec_ref(v_motiveType_964_);
lean_dec(v_mvarId_962_);
v_a_1018_ = lean_ctor_get(v___x_972_, 0);
v_isSharedCheck_1025_ = !lean_is_exclusive(v___x_972_);
if (v_isSharedCheck_1025_ == 0)
{
v___x_1020_ = v___x_972_;
v_isShared_1021_ = v_isSharedCheck_1025_;
goto v_resetjp_1019_;
}
else
{
lean_inc(v_a_1018_);
lean_dec(v___x_972_);
v___x_1020_ = lean_box(0);
v_isShared_1021_ = v_isSharedCheck_1025_;
goto v_resetjp_1019_;
}
v_resetjp_1019_:
{
lean_object* v___x_1023_; 
if (v_isShared_1021_ == 0)
{
v___x_1023_ = v___x_1020_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v_a_1018_);
v___x_1023_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
return v___x_1023_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeTargetsEq___lam__2___boxed(lean_object* v_mvarId_1026_, lean_object* v___x_1027_, lean_object* v_motiveType_1028_, lean_object* v___f_1029_, lean_object* v_targets_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_){
_start:
{
lean_object* v_res_1036_; 
v_res_1036_ = l_Lean_Meta_generalizeTargetsEq___lam__2(v_mvarId_1026_, v___x_1027_, v_motiveType_1028_, v___f_1029_, v_targets_1030_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_);
lean_dec(v___y_1034_);
lean_dec_ref(v___y_1033_);
lean_dec(v___y_1032_);
lean_dec_ref(v___y_1031_);
lean_dec_ref(v_targets_1030_);
return v_res_1036_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeTargetsEq(lean_object* v_mvarId_1040_, lean_object* v_motiveType_1041_, lean_object* v_targets_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_){
_start:
{
lean_object* v___f_1048_; lean_object* v___x_1049_; lean_object* v___f_1050_; lean_object* v___x_1051_; 
lean_inc_n(v_mvarId_1040_, 2);
lean_inc_ref(v_targets_1042_);
v___f_1048_ = lean_alloc_closure((void*)(l_Lean_Meta_generalizeTargetsEq___lam__1___boxed), 9, 2);
lean_closure_set(v___f_1048_, 0, v_targets_1042_);
lean_closure_set(v___f_1048_, 1, v_mvarId_1040_);
v___x_1049_ = ((lean_object*)(l_Lean_Meta_generalizeTargetsEq___closed__1));
v___f_1050_ = lean_alloc_closure((void*)(l_Lean_Meta_generalizeTargetsEq___lam__2___boxed), 10, 5);
lean_closure_set(v___f_1050_, 0, v_mvarId_1040_);
lean_closure_set(v___f_1050_, 1, v___x_1049_);
lean_closure_set(v___f_1050_, 2, v_motiveType_1041_);
lean_closure_set(v___f_1050_, 3, v___f_1048_);
lean_closure_set(v___f_1050_, 4, v_targets_1042_);
v___x_1051_ = l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2___redArg(v_mvarId_1040_, v___f_1050_, v_a_1043_, v_a_1044_, v_a_1045_, v_a_1046_);
return v___x_1051_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeTargetsEq___boxed(lean_object* v_mvarId_1052_, lean_object* v_motiveType_1053_, lean_object* v_targets_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_){
_start:
{
lean_object* v_res_1060_; 
v_res_1060_ = l_Lean_Meta_generalizeTargetsEq(v_mvarId_1052_, v_motiveType_1053_, v_targets_1054_, v_a_1055_, v_a_1056_, v_a_1057_, v_a_1058_);
lean_dec(v_a_1058_);
lean_dec_ref(v_a_1057_);
lean_dec(v_a_1056_);
lean_dec_ref(v_a_1055_);
return v_res_1060_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1(lean_object* v_mvarId_1061_, lean_object* v_val_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_){
_start:
{
lean_object* v___x_1068_; 
v___x_1068_ = l_Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1___redArg(v_mvarId_1061_, v_val_1062_, v___y_1064_);
return v___x_1068_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1___boxed(lean_object* v_mvarId_1069_, lean_object* v_val_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_){
_start:
{
lean_object* v_res_1076_; 
v_res_1076_ = l_Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1(v_mvarId_1069_, v_val_1070_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_);
lean_dec(v___y_1074_);
lean_dec_ref(v___y_1073_);
lean_dec(v___y_1072_);
lean_dec_ref(v___y_1071_);
return v_res_1076_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1(lean_object* v_00_u03b2_1077_, lean_object* v_x_1078_, lean_object* v_x_1079_, lean_object* v_x_1080_){
_start:
{
lean_object* v___x_1081_; 
v___x_1081_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1___redArg(v_x_1078_, v_x_1079_, v_x_1080_);
return v___x_1081_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3(lean_object* v_00_u03b2_1082_, lean_object* v_x_1083_, size_t v_x_1084_, size_t v_x_1085_, lean_object* v_x_1086_, lean_object* v_x_1087_){
_start:
{
lean_object* v___x_1088_; 
v___x_1088_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___redArg(v_x_1083_, v_x_1084_, v_x_1085_, v_x_1086_, v_x_1087_);
return v___x_1088_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1089_, lean_object* v_x_1090_, lean_object* v_x_1091_, lean_object* v_x_1092_, lean_object* v_x_1093_, lean_object* v_x_1094_){
_start:
{
size_t v_x_2941__boxed_1095_; size_t v_x_2942__boxed_1096_; lean_object* v_res_1097_; 
v_x_2941__boxed_1095_ = lean_unbox_usize(v_x_1091_);
lean_dec(v_x_1091_);
v_x_2942__boxed_1096_ = lean_unbox_usize(v_x_1092_);
lean_dec(v_x_1092_);
v_res_1097_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3(v_00_u03b2_1089_, v_x_1090_, v_x_2941__boxed_1095_, v_x_2942__boxed_1096_, v_x_1093_, v_x_1094_);
return v_res_1097_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_1098_, lean_object* v_n_1099_, lean_object* v_k_1100_, lean_object* v_v_1101_){
_start:
{
lean_object* v___x_1102_; 
v___x_1102_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__4___redArg(v_n_1099_, v_k_1100_, v_v_1101_);
return v___x_1102_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__5(lean_object* v_00_u03b2_1103_, size_t v_depth_1104_, lean_object* v_keys_1105_, lean_object* v_vals_1106_, lean_object* v_heq_1107_, lean_object* v_i_1108_, lean_object* v_entries_1109_){
_start:
{
lean_object* v___x_1110_; 
v___x_1110_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__5___redArg(v_depth_1104_, v_keys_1105_, v_vals_1106_, v_i_1108_, v_entries_1109_);
return v___x_1110_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__5___boxed(lean_object* v_00_u03b2_1111_, lean_object* v_depth_1112_, lean_object* v_keys_1113_, lean_object* v_vals_1114_, lean_object* v_heq_1115_, lean_object* v_i_1116_, lean_object* v_entries_1117_){
_start:
{
size_t v_depth_boxed_1118_; lean_object* v_res_1119_; 
v_depth_boxed_1118_ = lean_unbox_usize(v_depth_1112_);
lean_dec(v_depth_1112_);
v_res_1119_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__5(v_00_u03b2_1111_, v_depth_boxed_1118_, v_keys_1113_, v_vals_1114_, v_heq_1115_, v_i_1116_, v_entries_1117_);
lean_dec_ref(v_vals_1114_);
lean_dec_ref(v_keys_1113_);
return v_res_1119_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_1120_, lean_object* v_x_1121_, lean_object* v_x_1122_, lean_object* v_x_1123_, lean_object* v_x_1124_){
_start:
{
lean_object* v___x_1125_; 
v___x_1125_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1_spec__1_spec__3_spec__4_spec__5___redArg(v_x_1121_, v_x_1122_, v_x_1123_, v_x_1124_);
return v___x_1125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__0(lean_object* v_newEqs_1126_, lean_object* v_mvarId_1127_, uint8_t v___x_1128_, lean_object* v_h_x27_1129_, lean_object* v_newIndices_1130_, lean_object* v___x_1131_, lean_object* v___x_1132_, lean_object* v___x_1133_, lean_object* v___x_1134_, lean_object* v_e_1135_, lean_object* v___x_1136_, lean_object* v_newEq_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_){
_start:
{
lean_object* v___x_1143_; lean_object* v___x_1144_; 
v___x_1143_ = lean_array_push(v_newEqs_1126_, v_newEq_1137_);
lean_inc(v_mvarId_1127_);
v___x_1144_ = l_Lean_MVarId_getType(v_mvarId_1127_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_);
if (lean_obj_tag(v___x_1144_) == 0)
{
lean_object* v_a_1145_; lean_object* v___x_1146_; 
v_a_1145_ = lean_ctor_get(v___x_1144_, 0);
lean_inc(v_a_1145_);
lean_dec_ref_known(v___x_1144_, 1);
lean_inc(v_mvarId_1127_);
v___x_1146_ = l_Lean_MVarId_getTag(v_mvarId_1127_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_);
if (lean_obj_tag(v___x_1146_) == 0)
{
lean_object* v_a_1147_; uint8_t v___x_1148_; uint8_t v___x_1149_; lean_object* v___x_1150_; 
v_a_1147_ = lean_ctor_get(v___x_1146_, 0);
lean_inc(v_a_1147_);
lean_dec_ref_known(v___x_1146_, 1);
v___x_1148_ = 1;
v___x_1149_ = 1;
v___x_1150_ = l_Lean_Meta_mkForallFVars(v___x_1143_, v_a_1145_, v___x_1128_, v___x_1148_, v___x_1148_, v___x_1149_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_);
if (lean_obj_tag(v___x_1150_) == 0)
{
lean_object* v_a_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; 
v_a_1151_ = lean_ctor_get(v___x_1150_, 0);
lean_inc(v_a_1151_);
lean_dec_ref_known(v___x_1150_, 1);
v___x_1152_ = lean_unsigned_to_nat(1u);
v___x_1153_ = lean_mk_empty_array_with_capacity(v___x_1152_);
v___x_1154_ = lean_array_push(v___x_1153_, v_h_x27_1129_);
v___x_1155_ = l_Lean_Meta_mkForallFVars(v___x_1154_, v_a_1151_, v___x_1128_, v___x_1148_, v___x_1148_, v___x_1149_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_);
lean_dec_ref(v___x_1154_);
if (lean_obj_tag(v___x_1155_) == 0)
{
lean_object* v_a_1156_; lean_object* v___x_1157_; 
v_a_1156_ = lean_ctor_get(v___x_1155_, 0);
lean_inc(v_a_1156_);
lean_dec_ref_known(v___x_1155_, 1);
v___x_1157_ = l_Lean_Meta_mkForallFVars(v_newIndices_1130_, v_a_1156_, v___x_1128_, v___x_1148_, v___x_1148_, v___x_1149_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_);
if (lean_obj_tag(v___x_1157_) == 0)
{
lean_object* v_a_1158_; uint8_t v___x_1159_; lean_object* v___x_1160_; 
v_a_1158_ = lean_ctor_get(v___x_1157_, 0);
lean_inc(v_a_1158_);
lean_dec_ref_known(v___x_1157_, 1);
v___x_1159_ = 2;
v___x_1160_ = l_Lean_Meta_mkFreshExprMVarAt(v___x_1131_, v___x_1132_, v_a_1158_, v___x_1159_, v_a_1147_, v___x_1133_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_);
if (lean_obj_tag(v___x_1160_) == 0)
{
lean_object* v_a_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; 
v_a_1161_ = lean_ctor_get(v___x_1160_, 0);
lean_inc_n(v_a_1161_, 2);
lean_dec_ref_known(v___x_1160_, 1);
v___x_1162_ = l_Lean_mkAppN(v_a_1161_, v___x_1134_);
v___x_1163_ = l_Lean_Expr_app___override(v___x_1162_, v_e_1135_);
v___x_1164_ = l_Lean_mkAppN(v___x_1163_, v___x_1136_);
v___x_1165_ = l_Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1___redArg(v_mvarId_1127_, v___x_1164_, v___y_1139_);
lean_dec_ref(v___x_1165_);
v___x_1166_ = l_Lean_Expr_mvarId_x21(v_a_1161_);
lean_dec(v_a_1161_);
v___x_1167_ = lean_array_get_size(v_newIndices_1130_);
v___x_1168_ = lean_box(0);
v___x_1169_ = l_Lean_Meta_introNCore(v___x_1166_, v___x_1167_, v___x_1168_, v___x_1128_, v___x_1148_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_);
if (lean_obj_tag(v___x_1169_) == 0)
{
lean_object* v_a_1170_; lean_object* v_fst_1171_; lean_object* v_snd_1172_; lean_object* v___x_1173_; 
v_a_1170_ = lean_ctor_get(v___x_1169_, 0);
lean_inc(v_a_1170_);
lean_dec_ref_known(v___x_1169_, 1);
v_fst_1171_ = lean_ctor_get(v_a_1170_, 0);
lean_inc(v_fst_1171_);
v_snd_1172_ = lean_ctor_get(v_a_1170_, 1);
lean_inc(v_snd_1172_);
lean_dec(v_a_1170_);
v___x_1173_ = l_Lean_Meta_intro1Core(v_snd_1172_, v___x_1148_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_);
if (lean_obj_tag(v___x_1173_) == 0)
{
lean_object* v_a_1174_; lean_object* v___x_1176_; uint8_t v_isShared_1177_; uint8_t v_isSharedCheck_1185_; 
v_a_1174_ = lean_ctor_get(v___x_1173_, 0);
v_isSharedCheck_1185_ = !lean_is_exclusive(v___x_1173_);
if (v_isSharedCheck_1185_ == 0)
{
v___x_1176_ = v___x_1173_;
v_isShared_1177_ = v_isSharedCheck_1185_;
goto v_resetjp_1175_;
}
else
{
lean_inc(v_a_1174_);
lean_dec(v___x_1173_);
v___x_1176_ = lean_box(0);
v_isShared_1177_ = v_isSharedCheck_1185_;
goto v_resetjp_1175_;
}
v_resetjp_1175_:
{
lean_object* v_fst_1178_; lean_object* v_snd_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1183_; 
v_fst_1178_ = lean_ctor_get(v_a_1174_, 0);
lean_inc(v_fst_1178_);
v_snd_1179_ = lean_ctor_get(v_a_1174_, 1);
lean_inc(v_snd_1179_);
lean_dec(v_a_1174_);
v___x_1180_ = lean_array_get_size(v___x_1143_);
lean_dec_ref(v___x_1143_);
v___x_1181_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1181_, 0, v_snd_1179_);
lean_ctor_set(v___x_1181_, 1, v_fst_1171_);
lean_ctor_set(v___x_1181_, 2, v_fst_1178_);
lean_ctor_set(v___x_1181_, 3, v___x_1180_);
if (v_isShared_1177_ == 0)
{
lean_ctor_set(v___x_1176_, 0, v___x_1181_);
v___x_1183_ = v___x_1176_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v___x_1181_);
v___x_1183_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
return v___x_1183_;
}
}
}
else
{
lean_object* v_a_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1193_; 
lean_dec(v_fst_1171_);
lean_dec_ref(v___x_1143_);
v_a_1186_ = lean_ctor_get(v___x_1173_, 0);
v_isSharedCheck_1193_ = !lean_is_exclusive(v___x_1173_);
if (v_isSharedCheck_1193_ == 0)
{
v___x_1188_ = v___x_1173_;
v_isShared_1189_ = v_isSharedCheck_1193_;
goto v_resetjp_1187_;
}
else
{
lean_inc(v_a_1186_);
lean_dec(v___x_1173_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1193_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
lean_object* v___x_1191_; 
if (v_isShared_1189_ == 0)
{
v___x_1191_ = v___x_1188_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v_a_1186_);
v___x_1191_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
return v___x_1191_;
}
}
}
}
else
{
lean_object* v_a_1194_; lean_object* v___x_1196_; uint8_t v_isShared_1197_; uint8_t v_isSharedCheck_1201_; 
lean_dec_ref(v___x_1143_);
v_a_1194_ = lean_ctor_get(v___x_1169_, 0);
v_isSharedCheck_1201_ = !lean_is_exclusive(v___x_1169_);
if (v_isSharedCheck_1201_ == 0)
{
v___x_1196_ = v___x_1169_;
v_isShared_1197_ = v_isSharedCheck_1201_;
goto v_resetjp_1195_;
}
else
{
lean_inc(v_a_1194_);
lean_dec(v___x_1169_);
v___x_1196_ = lean_box(0);
v_isShared_1197_ = v_isSharedCheck_1201_;
goto v_resetjp_1195_;
}
v_resetjp_1195_:
{
lean_object* v___x_1199_; 
if (v_isShared_1197_ == 0)
{
v___x_1199_ = v___x_1196_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v_a_1194_);
v___x_1199_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
return v___x_1199_;
}
}
}
}
else
{
lean_object* v_a_1202_; lean_object* v___x_1204_; uint8_t v_isShared_1205_; uint8_t v_isSharedCheck_1209_; 
lean_dec_ref(v___x_1143_);
lean_dec_ref(v_e_1135_);
lean_dec(v_mvarId_1127_);
v_a_1202_ = lean_ctor_get(v___x_1160_, 0);
v_isSharedCheck_1209_ = !lean_is_exclusive(v___x_1160_);
if (v_isSharedCheck_1209_ == 0)
{
v___x_1204_ = v___x_1160_;
v_isShared_1205_ = v_isSharedCheck_1209_;
goto v_resetjp_1203_;
}
else
{
lean_inc(v_a_1202_);
lean_dec(v___x_1160_);
v___x_1204_ = lean_box(0);
v_isShared_1205_ = v_isSharedCheck_1209_;
goto v_resetjp_1203_;
}
v_resetjp_1203_:
{
lean_object* v___x_1207_; 
if (v_isShared_1205_ == 0)
{
v___x_1207_ = v___x_1204_;
goto v_reusejp_1206_;
}
else
{
lean_object* v_reuseFailAlloc_1208_; 
v_reuseFailAlloc_1208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1208_, 0, v_a_1202_);
v___x_1207_ = v_reuseFailAlloc_1208_;
goto v_reusejp_1206_;
}
v_reusejp_1206_:
{
return v___x_1207_;
}
}
}
}
else
{
lean_object* v_a_1210_; lean_object* v___x_1212_; uint8_t v_isShared_1213_; uint8_t v_isSharedCheck_1217_; 
lean_dec(v_a_1147_);
lean_dec_ref(v___x_1143_);
lean_dec_ref(v_e_1135_);
lean_dec(v___x_1133_);
lean_dec_ref(v___x_1132_);
lean_dec_ref(v___x_1131_);
lean_dec(v_mvarId_1127_);
v_a_1210_ = lean_ctor_get(v___x_1157_, 0);
v_isSharedCheck_1217_ = !lean_is_exclusive(v___x_1157_);
if (v_isSharedCheck_1217_ == 0)
{
v___x_1212_ = v___x_1157_;
v_isShared_1213_ = v_isSharedCheck_1217_;
goto v_resetjp_1211_;
}
else
{
lean_inc(v_a_1210_);
lean_dec(v___x_1157_);
v___x_1212_ = lean_box(0);
v_isShared_1213_ = v_isSharedCheck_1217_;
goto v_resetjp_1211_;
}
v_resetjp_1211_:
{
lean_object* v___x_1215_; 
if (v_isShared_1213_ == 0)
{
v___x_1215_ = v___x_1212_;
goto v_reusejp_1214_;
}
else
{
lean_object* v_reuseFailAlloc_1216_; 
v_reuseFailAlloc_1216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1216_, 0, v_a_1210_);
v___x_1215_ = v_reuseFailAlloc_1216_;
goto v_reusejp_1214_;
}
v_reusejp_1214_:
{
return v___x_1215_;
}
}
}
}
else
{
lean_object* v_a_1218_; lean_object* v___x_1220_; uint8_t v_isShared_1221_; uint8_t v_isSharedCheck_1225_; 
lean_dec(v_a_1147_);
lean_dec_ref(v___x_1143_);
lean_dec_ref(v_e_1135_);
lean_dec(v___x_1133_);
lean_dec_ref(v___x_1132_);
lean_dec_ref(v___x_1131_);
lean_dec(v_mvarId_1127_);
v_a_1218_ = lean_ctor_get(v___x_1155_, 0);
v_isSharedCheck_1225_ = !lean_is_exclusive(v___x_1155_);
if (v_isSharedCheck_1225_ == 0)
{
v___x_1220_ = v___x_1155_;
v_isShared_1221_ = v_isSharedCheck_1225_;
goto v_resetjp_1219_;
}
else
{
lean_inc(v_a_1218_);
lean_dec(v___x_1155_);
v___x_1220_ = lean_box(0);
v_isShared_1221_ = v_isSharedCheck_1225_;
goto v_resetjp_1219_;
}
v_resetjp_1219_:
{
lean_object* v___x_1223_; 
if (v_isShared_1221_ == 0)
{
v___x_1223_ = v___x_1220_;
goto v_reusejp_1222_;
}
else
{
lean_object* v_reuseFailAlloc_1224_; 
v_reuseFailAlloc_1224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1224_, 0, v_a_1218_);
v___x_1223_ = v_reuseFailAlloc_1224_;
goto v_reusejp_1222_;
}
v_reusejp_1222_:
{
return v___x_1223_;
}
}
}
}
else
{
lean_object* v_a_1226_; lean_object* v___x_1228_; uint8_t v_isShared_1229_; uint8_t v_isSharedCheck_1233_; 
lean_dec(v_a_1147_);
lean_dec_ref(v___x_1143_);
lean_dec_ref(v_e_1135_);
lean_dec(v___x_1133_);
lean_dec_ref(v___x_1132_);
lean_dec_ref(v___x_1131_);
lean_dec_ref(v_h_x27_1129_);
lean_dec(v_mvarId_1127_);
v_a_1226_ = lean_ctor_get(v___x_1150_, 0);
v_isSharedCheck_1233_ = !lean_is_exclusive(v___x_1150_);
if (v_isSharedCheck_1233_ == 0)
{
v___x_1228_ = v___x_1150_;
v_isShared_1229_ = v_isSharedCheck_1233_;
goto v_resetjp_1227_;
}
else
{
lean_inc(v_a_1226_);
lean_dec(v___x_1150_);
v___x_1228_ = lean_box(0);
v_isShared_1229_ = v_isSharedCheck_1233_;
goto v_resetjp_1227_;
}
v_resetjp_1227_:
{
lean_object* v___x_1231_; 
if (v_isShared_1229_ == 0)
{
v___x_1231_ = v___x_1228_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v_a_1226_);
v___x_1231_ = v_reuseFailAlloc_1232_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
return v___x_1231_;
}
}
}
}
else
{
lean_object* v_a_1234_; lean_object* v___x_1236_; uint8_t v_isShared_1237_; uint8_t v_isSharedCheck_1241_; 
lean_dec(v_a_1145_);
lean_dec_ref(v___x_1143_);
lean_dec_ref(v_e_1135_);
lean_dec(v___x_1133_);
lean_dec_ref(v___x_1132_);
lean_dec_ref(v___x_1131_);
lean_dec_ref(v_h_x27_1129_);
lean_dec(v_mvarId_1127_);
v_a_1234_ = lean_ctor_get(v___x_1146_, 0);
v_isSharedCheck_1241_ = !lean_is_exclusive(v___x_1146_);
if (v_isSharedCheck_1241_ == 0)
{
v___x_1236_ = v___x_1146_;
v_isShared_1237_ = v_isSharedCheck_1241_;
goto v_resetjp_1235_;
}
else
{
lean_inc(v_a_1234_);
lean_dec(v___x_1146_);
v___x_1236_ = lean_box(0);
v_isShared_1237_ = v_isSharedCheck_1241_;
goto v_resetjp_1235_;
}
v_resetjp_1235_:
{
lean_object* v___x_1239_; 
if (v_isShared_1237_ == 0)
{
v___x_1239_ = v___x_1236_;
goto v_reusejp_1238_;
}
else
{
lean_object* v_reuseFailAlloc_1240_; 
v_reuseFailAlloc_1240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1240_, 0, v_a_1234_);
v___x_1239_ = v_reuseFailAlloc_1240_;
goto v_reusejp_1238_;
}
v_reusejp_1238_:
{
return v___x_1239_;
}
}
}
}
else
{
lean_object* v_a_1242_; lean_object* v___x_1244_; uint8_t v_isShared_1245_; uint8_t v_isSharedCheck_1249_; 
lean_dec_ref(v___x_1143_);
lean_dec_ref(v_e_1135_);
lean_dec(v___x_1133_);
lean_dec_ref(v___x_1132_);
lean_dec_ref(v___x_1131_);
lean_dec_ref(v_h_x27_1129_);
lean_dec(v_mvarId_1127_);
v_a_1242_ = lean_ctor_get(v___x_1144_, 0);
v_isSharedCheck_1249_ = !lean_is_exclusive(v___x_1144_);
if (v_isSharedCheck_1249_ == 0)
{
v___x_1244_ = v___x_1144_;
v_isShared_1245_ = v_isSharedCheck_1249_;
goto v_resetjp_1243_;
}
else
{
lean_inc(v_a_1242_);
lean_dec(v___x_1144_);
v___x_1244_ = lean_box(0);
v_isShared_1245_ = v_isSharedCheck_1249_;
goto v_resetjp_1243_;
}
v_resetjp_1243_:
{
lean_object* v___x_1247_; 
if (v_isShared_1245_ == 0)
{
v___x_1247_ = v___x_1244_;
goto v_reusejp_1246_;
}
else
{
lean_object* v_reuseFailAlloc_1248_; 
v_reuseFailAlloc_1248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1248_, 0, v_a_1242_);
v___x_1247_ = v_reuseFailAlloc_1248_;
goto v_reusejp_1246_;
}
v_reusejp_1246_:
{
return v___x_1247_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__0___boxed(lean_object** _args){
lean_object* v_newEqs_1250_ = _args[0];
lean_object* v_mvarId_1251_ = _args[1];
lean_object* v___x_1252_ = _args[2];
lean_object* v_h_x27_1253_ = _args[3];
lean_object* v_newIndices_1254_ = _args[4];
lean_object* v___x_1255_ = _args[5];
lean_object* v___x_1256_ = _args[6];
lean_object* v___x_1257_ = _args[7];
lean_object* v___x_1258_ = _args[8];
lean_object* v_e_1259_ = _args[9];
lean_object* v___x_1260_ = _args[10];
lean_object* v_newEq_1261_ = _args[11];
lean_object* v___y_1262_ = _args[12];
lean_object* v___y_1263_ = _args[13];
lean_object* v___y_1264_ = _args[14];
lean_object* v___y_1265_ = _args[15];
lean_object* v___y_1266_ = _args[16];
_start:
{
uint8_t v___x_6158__boxed_1267_; lean_object* v_res_1268_; 
v___x_6158__boxed_1267_ = lean_unbox(v___x_1252_);
v_res_1268_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__0(v_newEqs_1250_, v_mvarId_1251_, v___x_6158__boxed_1267_, v_h_x27_1253_, v_newIndices_1254_, v___x_1255_, v___x_1256_, v___x_1257_, v___x_1258_, v_e_1259_, v___x_1260_, v_newEq_1261_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_);
lean_dec(v___y_1265_);
lean_dec_ref(v___y_1264_);
lean_dec(v___y_1263_);
lean_dec_ref(v___y_1262_);
lean_dec_ref(v___x_1260_);
lean_dec_ref(v___x_1258_);
lean_dec_ref(v_newIndices_1254_);
return v_res_1268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__1(lean_object* v_e_1269_, lean_object* v_h_x27_1270_, lean_object* v_mvarId_1271_, uint8_t v___x_1272_, lean_object* v_newIndices_1273_, lean_object* v___x_1274_, lean_object* v___x_1275_, lean_object* v___x_1276_, lean_object* v___x_1277_, lean_object* v_newEqs_1278_, lean_object* v_newRefls_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_){
_start:
{
lean_object* v___x_1285_; 
lean_inc_ref(v_h_x27_1270_);
lean_inc_ref(v_e_1269_);
v___x_1285_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof(v_e_1269_, v_h_x27_1270_, v___y_1280_, v___y_1281_, v___y_1282_, v___y_1283_);
if (lean_obj_tag(v___x_1285_) == 0)
{
lean_object* v_a_1286_; lean_object* v_fst_1287_; lean_object* v_snd_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___f_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; 
v_a_1286_ = lean_ctor_get(v___x_1285_, 0);
lean_inc(v_a_1286_);
lean_dec_ref_known(v___x_1285_, 1);
v_fst_1287_ = lean_ctor_get(v_a_1286_, 0);
lean_inc(v_fst_1287_);
v_snd_1288_ = lean_ctor_get(v_a_1286_, 1);
lean_inc(v_snd_1288_);
lean_dec(v_a_1286_);
v___x_1289_ = lean_array_push(v_newRefls_1279_, v_snd_1288_);
v___x_1290_ = lean_box(v___x_1272_);
v___f_1291_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__0___boxed), 17, 11);
lean_closure_set(v___f_1291_, 0, v_newEqs_1278_);
lean_closure_set(v___f_1291_, 1, v_mvarId_1271_);
lean_closure_set(v___f_1291_, 2, v___x_1290_);
lean_closure_set(v___f_1291_, 3, v_h_x27_1270_);
lean_closure_set(v___f_1291_, 4, v_newIndices_1273_);
lean_closure_set(v___f_1291_, 5, v___x_1274_);
lean_closure_set(v___f_1291_, 6, v___x_1275_);
lean_closure_set(v___f_1291_, 7, v___x_1276_);
lean_closure_set(v___f_1291_, 8, v___x_1277_);
lean_closure_set(v___f_1291_, 9, v_e_1269_);
lean_closure_set(v___f_1291_, 10, v___x_1289_);
v___x_1292_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___redArg___closed__1));
v___x_1293_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0___redArg(v___x_1292_, v_fst_1287_, v___f_1291_, v___y_1280_, v___y_1281_, v___y_1282_, v___y_1283_);
return v___x_1293_;
}
else
{
lean_object* v_a_1294_; lean_object* v___x_1296_; uint8_t v_isShared_1297_; uint8_t v_isSharedCheck_1301_; 
lean_dec_ref(v_newRefls_1279_);
lean_dec_ref(v_newEqs_1278_);
lean_dec_ref(v___x_1277_);
lean_dec(v___x_1276_);
lean_dec_ref(v___x_1275_);
lean_dec_ref(v___x_1274_);
lean_dec_ref(v_newIndices_1273_);
lean_dec(v_mvarId_1271_);
lean_dec_ref(v_h_x27_1270_);
lean_dec_ref(v_e_1269_);
v_a_1294_ = lean_ctor_get(v___x_1285_, 0);
v_isSharedCheck_1301_ = !lean_is_exclusive(v___x_1285_);
if (v_isSharedCheck_1301_ == 0)
{
v___x_1296_ = v___x_1285_;
v_isShared_1297_ = v_isSharedCheck_1301_;
goto v_resetjp_1295_;
}
else
{
lean_inc(v_a_1294_);
lean_dec(v___x_1285_);
v___x_1296_ = lean_box(0);
v_isShared_1297_ = v_isSharedCheck_1301_;
goto v_resetjp_1295_;
}
v_resetjp_1295_:
{
lean_object* v___x_1299_; 
if (v_isShared_1297_ == 0)
{
v___x_1299_ = v___x_1296_;
goto v_reusejp_1298_;
}
else
{
lean_object* v_reuseFailAlloc_1300_; 
v_reuseFailAlloc_1300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1300_, 0, v_a_1294_);
v___x_1299_ = v_reuseFailAlloc_1300_;
goto v_reusejp_1298_;
}
v_reusejp_1298_:
{
return v___x_1299_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__1___boxed(lean_object* v_e_1302_, lean_object* v_h_x27_1303_, lean_object* v_mvarId_1304_, lean_object* v___x_1305_, lean_object* v_newIndices_1306_, lean_object* v___x_1307_, lean_object* v___x_1308_, lean_object* v___x_1309_, lean_object* v___x_1310_, lean_object* v_newEqs_1311_, lean_object* v_newRefls_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_){
_start:
{
uint8_t v___x_6410__boxed_1318_; lean_object* v_res_1319_; 
v___x_6410__boxed_1318_ = lean_unbox(v___x_1305_);
v_res_1319_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__1(v_e_1302_, v_h_x27_1303_, v_mvarId_1304_, v___x_6410__boxed_1318_, v_newIndices_1306_, v___x_1307_, v___x_1308_, v___x_1309_, v___x_1310_, v_newEqs_1311_, v_newRefls_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_);
lean_dec(v___y_1316_);
lean_dec_ref(v___y_1315_);
lean_dec(v___y_1314_);
lean_dec_ref(v___y_1313_);
return v_res_1319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__2(lean_object* v_e_1320_, lean_object* v_mvarId_1321_, uint8_t v___x_1322_, lean_object* v_newIndices_1323_, lean_object* v___x_1324_, lean_object* v___x_1325_, lean_object* v___x_1326_, lean_object* v___x_1327_, lean_object* v_h_x27_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_){
_start:
{
lean_object* v___x_1334_; lean_object* v___f_1335_; lean_object* v___x_1336_; 
v___x_1334_ = lean_box(v___x_1322_);
lean_inc_ref(v___x_1327_);
lean_inc_ref(v_newIndices_1323_);
v___f_1335_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__1___boxed), 16, 9);
lean_closure_set(v___f_1335_, 0, v_e_1320_);
lean_closure_set(v___f_1335_, 1, v_h_x27_1328_);
lean_closure_set(v___f_1335_, 2, v_mvarId_1321_);
lean_closure_set(v___f_1335_, 3, v___x_1334_);
lean_closure_set(v___f_1335_, 4, v_newIndices_1323_);
lean_closure_set(v___f_1335_, 5, v___x_1324_);
lean_closure_set(v___f_1335_, 6, v___x_1325_);
lean_closure_set(v___f_1335_, 7, v___x_1326_);
lean_closure_set(v___f_1335_, 8, v___x_1327_);
v___x_1336_ = l_Lean_Meta_withNewEqs___redArg(v___x_1327_, v_newIndices_1323_, v___f_1335_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_);
return v___x_1336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__2___boxed(lean_object* v_e_1337_, lean_object* v_mvarId_1338_, lean_object* v___x_1339_, lean_object* v_newIndices_1340_, lean_object* v___x_1341_, lean_object* v___x_1342_, lean_object* v___x_1343_, lean_object* v___x_1344_, lean_object* v_h_x27_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_){
_start:
{
uint8_t v___x_6475__boxed_1351_; lean_object* v_res_1352_; 
v___x_6475__boxed_1351_ = lean_unbox(v___x_1339_);
v_res_1352_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__2(v_e_1337_, v_mvarId_1338_, v___x_6475__boxed_1351_, v_newIndices_1340_, v___x_1341_, v___x_1342_, v___x_1343_, v___x_1344_, v_h_x27_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_);
lean_dec(v___y_1349_);
lean_dec_ref(v___y_1348_);
lean_dec(v___y_1347_);
lean_dec_ref(v___y_1346_);
return v_res_1352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__3(lean_object* v_e_1356_, lean_object* v_mvarId_1357_, uint8_t v___x_1358_, lean_object* v___x_1359_, lean_object* v___x_1360_, lean_object* v___x_1361_, lean_object* v___x_1362_, lean_object* v___x_1363_, lean_object* v_varName_x3f_1364_, lean_object* v_newIndices_1365_, lean_object* v_x_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_){
_start:
{
lean_object* v___x_1372_; lean_object* v___f_1373_; lean_object* v___x_1374_; 
v___x_1372_ = lean_box(v___x_1358_);
lean_inc_ref(v_newIndices_1365_);
v___f_1373_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__2___boxed), 14, 8);
lean_closure_set(v___f_1373_, 0, v_e_1356_);
lean_closure_set(v___f_1373_, 1, v_mvarId_1357_);
lean_closure_set(v___f_1373_, 2, v___x_1372_);
lean_closure_set(v___f_1373_, 3, v_newIndices_1365_);
lean_closure_set(v___f_1373_, 4, v___x_1359_);
lean_closure_set(v___f_1373_, 5, v___x_1360_);
lean_closure_set(v___f_1373_, 6, v___x_1361_);
lean_closure_set(v___f_1373_, 7, v___x_1362_);
v___x_1374_ = l_Lean_mkAppN(v___x_1363_, v_newIndices_1365_);
lean_dec_ref(v_newIndices_1365_);
if (lean_obj_tag(v_varName_x3f_1364_) == 1)
{
lean_object* v_val_1375_; lean_object* v___x_1376_; 
v_val_1375_ = lean_ctor_get(v_varName_x3f_1364_, 0);
lean_inc(v_val_1375_);
lean_dec_ref_known(v_varName_x3f_1364_, 1);
v___x_1376_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0___redArg(v_val_1375_, v___x_1374_, v___f_1373_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_);
return v___x_1376_;
}
else
{
lean_object* v___x_1377_; lean_object* v___x_1378_; 
lean_dec(v_varName_x3f_1364_);
v___x_1377_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__3___closed__1));
v___x_1378_ = l_Lean_Core_mkFreshUserName(v___x_1377_, v___y_1369_, v___y_1370_);
if (lean_obj_tag(v___x_1378_) == 0)
{
lean_object* v_a_1379_; lean_object* v___x_1380_; 
v_a_1379_ = lean_ctor_get(v___x_1378_, 0);
lean_inc(v_a_1379_);
lean_dec_ref_known(v___x_1378_, 1);
v___x_1380_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0___redArg(v_a_1379_, v___x_1374_, v___f_1373_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_);
return v___x_1380_;
}
else
{
lean_object* v_a_1381_; lean_object* v___x_1383_; uint8_t v_isShared_1384_; uint8_t v_isSharedCheck_1388_; 
lean_dec_ref(v___x_1374_);
lean_dec_ref(v___f_1373_);
v_a_1381_ = lean_ctor_get(v___x_1378_, 0);
v_isSharedCheck_1388_ = !lean_is_exclusive(v___x_1378_);
if (v_isSharedCheck_1388_ == 0)
{
v___x_1383_ = v___x_1378_;
v_isShared_1384_ = v_isSharedCheck_1388_;
goto v_resetjp_1382_;
}
else
{
lean_inc(v_a_1381_);
lean_dec(v___x_1378_);
v___x_1383_ = lean_box(0);
v_isShared_1384_ = v_isSharedCheck_1388_;
goto v_resetjp_1382_;
}
v_resetjp_1382_:
{
lean_object* v___x_1386_; 
if (v_isShared_1384_ == 0)
{
v___x_1386_ = v___x_1383_;
goto v_reusejp_1385_;
}
else
{
lean_object* v_reuseFailAlloc_1387_; 
v_reuseFailAlloc_1387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1387_, 0, v_a_1381_);
v___x_1386_ = v_reuseFailAlloc_1387_;
goto v_reusejp_1385_;
}
v_reusejp_1385_:
{
return v___x_1386_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__3___boxed(lean_object* v_e_1389_, lean_object* v_mvarId_1390_, lean_object* v___x_1391_, lean_object* v___x_1392_, lean_object* v___x_1393_, lean_object* v___x_1394_, lean_object* v___x_1395_, lean_object* v___x_1396_, lean_object* v_varName_x3f_1397_, lean_object* v_newIndices_1398_, lean_object* v_x_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_){
_start:
{
uint8_t v___x_6517__boxed_1405_; lean_object* v_res_1406_; 
v___x_6517__boxed_1405_ = lean_unbox(v___x_1391_);
v_res_1406_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__3(v_e_1389_, v_mvarId_1390_, v___x_6517__boxed_1405_, v___x_1392_, v___x_1393_, v___x_1394_, v___x_1395_, v___x_1396_, v_varName_x3f_1397_, v_newIndices_1398_, v_x_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_);
lean_dec(v___y_1403_);
lean_dec_ref(v___y_1402_);
lean_dec(v___y_1401_);
lean_dec_ref(v___y_1400_);
lean_dec_ref(v_x_1399_);
return v_res_1406_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__4(void){
_start:
{
lean_object* v___x_1413_; lean_object* v___x_1414_; 
v___x_1413_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__3));
v___x_1414_ = l_Lean_MessageData_ofFormat(v___x_1413_);
return v___x_1414_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__5(void){
_start:
{
lean_object* v___x_1415_; lean_object* v___x_1416_; 
v___x_1415_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__4, &l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__4_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__4);
v___x_1416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1416_, 0, v___x_1415_);
return v___x_1416_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__8(void){
_start:
{
lean_object* v___x_1420_; lean_object* v___x_1421_; 
v___x_1420_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__7));
v___x_1421_ = l_Lean_MessageData_ofFormat(v___x_1420_);
return v___x_1421_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__9(void){
_start:
{
lean_object* v___x_1422_; lean_object* v___x_1423_; 
v___x_1422_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__8, &l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__8_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__8);
v___x_1423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1423_, 0, v___x_1422_);
return v___x_1423_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__12(void){
_start:
{
lean_object* v___x_1427_; lean_object* v___x_1428_; 
v___x_1427_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__11));
v___x_1428_ = l_Lean_MessageData_ofFormat(v___x_1427_);
return v___x_1428_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__13(void){
_start:
{
lean_object* v___x_1429_; lean_object* v___x_1430_; 
v___x_1429_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__12, &l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__12_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__12);
v___x_1430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1430_, 0, v___x_1429_);
return v___x_1430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0(lean_object* v_mvarId_1431_, lean_object* v_e_1432_, lean_object* v___x_1433_, lean_object* v___x_1434_, lean_object* v_varName_x3f_1435_, lean_object* v_x_1436_, lean_object* v_x_1437_, lean_object* v_x_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_){
_start:
{
if (lean_obj_tag(v_x_1436_) == 5)
{
lean_object* v_fn_1444_; lean_object* v_arg_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; 
v_fn_1444_ = lean_ctor_get(v_x_1436_, 0);
lean_inc_ref(v_fn_1444_);
v_arg_1445_ = lean_ctor_get(v_x_1436_, 1);
lean_inc_ref(v_arg_1445_);
lean_dec_ref_known(v_x_1436_, 2);
v___x_1446_ = lean_array_set(v_x_1437_, v_x_1438_, v_arg_1445_);
v___x_1447_ = lean_unsigned_to_nat(1u);
v___x_1448_ = lean_nat_sub(v_x_1438_, v___x_1447_);
lean_dec(v_x_1438_);
v_x_1436_ = v_fn_1444_;
v_x_1437_ = v___x_1446_;
v_x_1438_ = v___x_1448_;
goto _start;
}
else
{
lean_object* v___x_1450_; lean_object* v___y_1452_; lean_object* v___y_1453_; lean_object* v___y_1454_; lean_object* v___y_1455_; 
lean_dec(v_x_1438_);
v___x_1450_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__1));
if (lean_obj_tag(v_x_1436_) == 4)
{
lean_object* v_declName_1458_; lean_object* v___x_1459_; lean_object* v_env_1460_; uint8_t v___x_1461_; lean_object* v___x_1462_; 
v_declName_1458_ = lean_ctor_get(v_x_1436_, 0);
v___x_1459_ = lean_st_ref_get(v___y_1442_);
v_env_1460_ = lean_ctor_get(v___x_1459_, 0);
lean_inc_ref(v_env_1460_);
lean_dec(v___x_1459_);
v___x_1461_ = 0;
lean_inc(v_declName_1458_);
v___x_1462_ = l_Lean_Environment_find_x3f(v_env_1460_, v_declName_1458_, v___x_1461_);
if (lean_obj_tag(v___x_1462_) == 0)
{
lean_dec_ref_known(v_x_1436_, 2);
lean_dec_ref(v_x_1437_);
lean_dec(v_varName_x3f_1435_);
lean_dec_ref(v___x_1434_);
lean_dec_ref(v___x_1433_);
lean_dec_ref(v_e_1432_);
v___y_1452_ = v___y_1439_;
v___y_1453_ = v___y_1440_;
v___y_1454_ = v___y_1441_;
v___y_1455_ = v___y_1442_;
goto v___jp_1451_;
}
else
{
lean_object* v_val_1463_; 
v_val_1463_ = lean_ctor_get(v___x_1462_, 0);
lean_inc(v_val_1463_);
lean_dec_ref_known(v___x_1462_, 1);
if (lean_obj_tag(v_val_1463_) == 5)
{
lean_object* v_val_1464_; lean_object* v_numParams_1465_; lean_object* v_numIndices_1466_; lean_object* v___y_1468_; lean_object* v___y_1469_; lean_object* v___y_1470_; lean_object* v___y_1471_; lean_object* v___y_1492_; lean_object* v___y_1493_; lean_object* v___y_1494_; lean_object* v___y_1495_; lean_object* v___x_1509_; uint8_t v___x_1510_; 
v_val_1464_ = lean_ctor_get(v_val_1463_, 0);
lean_inc_ref(v_val_1464_);
lean_dec_ref_known(v_val_1463_, 1);
v_numParams_1465_ = lean_ctor_get(v_val_1464_, 1);
lean_inc(v_numParams_1465_);
v_numIndices_1466_ = lean_ctor_get(v_val_1464_, 2);
lean_inc(v_numIndices_1466_);
lean_dec_ref(v_val_1464_);
v___x_1509_ = lean_unsigned_to_nat(0u);
v___x_1510_ = lean_nat_dec_lt(v___x_1509_, v_numIndices_1466_);
if (v___x_1510_ == 0)
{
lean_object* v___x_1511_; lean_object* v___x_1512_; 
v___x_1511_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__13, &l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__13_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__13);
lean_inc(v_mvarId_1431_);
v___x_1512_ = l_Lean_Meta_throwTacticEx___redArg(v___x_1450_, v_mvarId_1431_, v___x_1511_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_);
if (lean_obj_tag(v___x_1512_) == 0)
{
lean_dec_ref_known(v___x_1512_, 1);
v___y_1492_ = v___y_1439_;
v___y_1493_ = v___y_1440_;
v___y_1494_ = v___y_1441_;
v___y_1495_ = v___y_1442_;
goto v___jp_1491_;
}
else
{
lean_object* v_a_1513_; lean_object* v___x_1515_; uint8_t v_isShared_1516_; uint8_t v_isSharedCheck_1520_; 
lean_dec(v_numIndices_1466_);
lean_dec(v_numParams_1465_);
lean_dec_ref_known(v_x_1436_, 2);
lean_dec_ref(v_x_1437_);
lean_dec(v_varName_x3f_1435_);
lean_dec_ref(v___x_1434_);
lean_dec_ref(v___x_1433_);
lean_dec_ref(v_e_1432_);
lean_dec(v_mvarId_1431_);
v_a_1513_ = lean_ctor_get(v___x_1512_, 0);
v_isSharedCheck_1520_ = !lean_is_exclusive(v___x_1512_);
if (v_isSharedCheck_1520_ == 0)
{
v___x_1515_ = v___x_1512_;
v_isShared_1516_ = v_isSharedCheck_1520_;
goto v_resetjp_1514_;
}
else
{
lean_inc(v_a_1513_);
lean_dec(v___x_1512_);
v___x_1515_ = lean_box(0);
v_isShared_1516_ = v_isSharedCheck_1520_;
goto v_resetjp_1514_;
}
v_resetjp_1514_:
{
lean_object* v___x_1518_; 
if (v_isShared_1516_ == 0)
{
v___x_1518_ = v___x_1515_;
goto v_reusejp_1517_;
}
else
{
lean_object* v_reuseFailAlloc_1519_; 
v_reuseFailAlloc_1519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1519_, 0, v_a_1513_);
v___x_1518_ = v_reuseFailAlloc_1519_;
goto v_reusejp_1517_;
}
v_reusejp_1517_:
{
return v___x_1518_;
}
}
}
}
else
{
v___y_1492_ = v___y_1439_;
v___y_1493_ = v___y_1440_;
v___y_1494_ = v___y_1441_;
v___y_1495_ = v___y_1442_;
goto v___jp_1491_;
}
v___jp_1467_:
{
lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___f_1479_; lean_object* v___x_1480_; 
v___x_1472_ = lean_array_get_size(v_x_1437_);
v___x_1473_ = lean_nat_sub(v___x_1472_, v_numIndices_1466_);
lean_dec(v_numIndices_1466_);
v___x_1474_ = l_Array_extract___redArg(v_x_1437_, v___x_1473_, v___x_1472_);
v___x_1475_ = lean_unsigned_to_nat(0u);
v___x_1476_ = l_Array_extract___redArg(v_x_1437_, v___x_1475_, v_numParams_1465_);
lean_dec_ref(v_x_1437_);
v___x_1477_ = l_Lean_mkAppN(v_x_1436_, v___x_1476_);
lean_dec_ref(v___x_1476_);
v___x_1478_ = lean_box(v___x_1461_);
lean_inc_ref(v___x_1477_);
v___f_1479_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___lam__3___boxed), 16, 9);
lean_closure_set(v___f_1479_, 0, v_e_1432_);
lean_closure_set(v___f_1479_, 1, v_mvarId_1431_);
lean_closure_set(v___f_1479_, 2, v___x_1478_);
lean_closure_set(v___f_1479_, 3, v___x_1433_);
lean_closure_set(v___f_1479_, 4, v___x_1434_);
lean_closure_set(v___f_1479_, 5, v___x_1475_);
lean_closure_set(v___f_1479_, 6, v___x_1474_);
lean_closure_set(v___f_1479_, 7, v___x_1477_);
lean_closure_set(v___f_1479_, 8, v_varName_x3f_1435_);
lean_inc(v___y_1471_);
lean_inc_ref(v___y_1470_);
lean_inc(v___y_1469_);
lean_inc_ref(v___y_1468_);
v___x_1480_ = lean_infer_type(v___x_1477_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_);
if (lean_obj_tag(v___x_1480_) == 0)
{
lean_object* v_a_1481_; lean_object* v___x_1482_; 
v_a_1481_ = lean_ctor_get(v___x_1480_, 0);
lean_inc(v_a_1481_);
lean_dec_ref_known(v___x_1480_, 1);
v___x_1482_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_generalizeTargetsEq_spec__0___redArg(v_a_1481_, v___f_1479_, v___x_1461_, v___x_1461_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_);
return v___x_1482_;
}
else
{
lean_object* v_a_1483_; lean_object* v___x_1485_; uint8_t v_isShared_1486_; uint8_t v_isSharedCheck_1490_; 
lean_dec_ref(v___f_1479_);
v_a_1483_ = lean_ctor_get(v___x_1480_, 0);
v_isSharedCheck_1490_ = !lean_is_exclusive(v___x_1480_);
if (v_isSharedCheck_1490_ == 0)
{
v___x_1485_ = v___x_1480_;
v_isShared_1486_ = v_isSharedCheck_1490_;
goto v_resetjp_1484_;
}
else
{
lean_inc(v_a_1483_);
lean_dec(v___x_1480_);
v___x_1485_ = lean_box(0);
v_isShared_1486_ = v_isSharedCheck_1490_;
goto v_resetjp_1484_;
}
v_resetjp_1484_:
{
lean_object* v___x_1488_; 
if (v_isShared_1486_ == 0)
{
v___x_1488_ = v___x_1485_;
goto v_reusejp_1487_;
}
else
{
lean_object* v_reuseFailAlloc_1489_; 
v_reuseFailAlloc_1489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1489_, 0, v_a_1483_);
v___x_1488_ = v_reuseFailAlloc_1489_;
goto v_reusejp_1487_;
}
v_reusejp_1487_:
{
return v___x_1488_;
}
}
}
}
v___jp_1491_:
{
lean_object* v___x_1496_; lean_object* v___x_1497_; uint8_t v___x_1498_; 
v___x_1496_ = lean_array_get_size(v_x_1437_);
v___x_1497_ = lean_nat_add(v_numIndices_1466_, v_numParams_1465_);
v___x_1498_ = lean_nat_dec_eq(v___x_1496_, v___x_1497_);
lean_dec(v___x_1497_);
if (v___x_1498_ == 0)
{
lean_object* v___x_1499_; lean_object* v___x_1500_; 
v___x_1499_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__9, &l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__9_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__9);
lean_inc(v_mvarId_1431_);
v___x_1500_ = l_Lean_Meta_throwTacticEx___redArg(v___x_1450_, v_mvarId_1431_, v___x_1499_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_);
if (lean_obj_tag(v___x_1500_) == 0)
{
lean_dec_ref_known(v___x_1500_, 1);
v___y_1468_ = v___y_1492_;
v___y_1469_ = v___y_1493_;
v___y_1470_ = v___y_1494_;
v___y_1471_ = v___y_1495_;
goto v___jp_1467_;
}
else
{
lean_object* v_a_1501_; lean_object* v___x_1503_; uint8_t v_isShared_1504_; uint8_t v_isSharedCheck_1508_; 
lean_dec(v_numIndices_1466_);
lean_dec(v_numParams_1465_);
lean_dec_ref_known(v_x_1436_, 2);
lean_dec_ref(v_x_1437_);
lean_dec(v_varName_x3f_1435_);
lean_dec_ref(v___x_1434_);
lean_dec_ref(v___x_1433_);
lean_dec_ref(v_e_1432_);
lean_dec(v_mvarId_1431_);
v_a_1501_ = lean_ctor_get(v___x_1500_, 0);
v_isSharedCheck_1508_ = !lean_is_exclusive(v___x_1500_);
if (v_isSharedCheck_1508_ == 0)
{
v___x_1503_ = v___x_1500_;
v_isShared_1504_ = v_isSharedCheck_1508_;
goto v_resetjp_1502_;
}
else
{
lean_inc(v_a_1501_);
lean_dec(v___x_1500_);
v___x_1503_ = lean_box(0);
v_isShared_1504_ = v_isSharedCheck_1508_;
goto v_resetjp_1502_;
}
v_resetjp_1502_:
{
lean_object* v___x_1506_; 
if (v_isShared_1504_ == 0)
{
v___x_1506_ = v___x_1503_;
goto v_reusejp_1505_;
}
else
{
lean_object* v_reuseFailAlloc_1507_; 
v_reuseFailAlloc_1507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1507_, 0, v_a_1501_);
v___x_1506_ = v_reuseFailAlloc_1507_;
goto v_reusejp_1505_;
}
v_reusejp_1505_:
{
return v___x_1506_;
}
}
}
}
else
{
v___y_1468_ = v___y_1492_;
v___y_1469_ = v___y_1493_;
v___y_1470_ = v___y_1494_;
v___y_1471_ = v___y_1495_;
goto v___jp_1467_;
}
}
}
else
{
lean_dec(v_val_1463_);
lean_dec_ref_known(v_x_1436_, 2);
lean_dec_ref(v_x_1437_);
lean_dec(v_varName_x3f_1435_);
lean_dec_ref(v___x_1434_);
lean_dec_ref(v___x_1433_);
lean_dec_ref(v_e_1432_);
v___y_1452_ = v___y_1439_;
v___y_1453_ = v___y_1440_;
v___y_1454_ = v___y_1441_;
v___y_1455_ = v___y_1442_;
goto v___jp_1451_;
}
}
}
else
{
lean_dec_ref(v_x_1437_);
lean_dec_ref(v_x_1436_);
lean_dec(v_varName_x3f_1435_);
lean_dec_ref(v___x_1434_);
lean_dec_ref(v___x_1433_);
lean_dec_ref(v_e_1432_);
v___y_1452_ = v___y_1439_;
v___y_1453_ = v___y_1440_;
v___y_1454_ = v___y_1441_;
v___y_1455_ = v___y_1442_;
goto v___jp_1451_;
}
v___jp_1451_:
{
lean_object* v___x_1456_; lean_object* v___x_1457_; 
v___x_1456_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__5, &l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__5_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__5);
v___x_1457_ = l_Lean_Meta_throwTacticEx___redArg(v___x_1450_, v_mvarId_1431_, v___x_1456_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_);
return v___x_1457_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___boxed(lean_object* v_mvarId_1521_, lean_object* v_e_1522_, lean_object* v___x_1523_, lean_object* v___x_1524_, lean_object* v_varName_x3f_1525_, lean_object* v_x_1526_, lean_object* v_x_1527_, lean_object* v_x_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_){
_start:
{
lean_object* v_res_1534_; 
v_res_1534_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0(v_mvarId_1521_, v_e_1522_, v___x_1523_, v___x_1524_, v_varName_x3f_1525_, v_x_1526_, v_x_1527_, v_x_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_);
lean_dec(v___y_1532_);
lean_dec_ref(v___y_1531_);
lean_dec(v___y_1530_);
lean_dec_ref(v___y_1529_);
return v_res_1534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeIndices_x27___lam__0(lean_object* v_mvarId_1535_, lean_object* v_e_1536_, lean_object* v_varName_x3f_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_){
_start:
{
lean_object* v_lctx_1543_; lean_object* v_localInstances_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; 
v_lctx_1543_ = lean_ctor_get(v___y_1538_, 2);
lean_inc_ref(v_lctx_1543_);
v_localInstances_1544_ = lean_ctor_get(v___y_1538_, 3);
lean_inc_ref(v_localInstances_1544_);
v___x_1545_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0___closed__1));
lean_inc(v_mvarId_1535_);
v___x_1546_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_1535_, v___x_1545_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_);
if (lean_obj_tag(v___x_1546_) == 0)
{
lean_object* v___x_1547_; 
lean_dec_ref_known(v___x_1546_, 1);
lean_inc(v___y_1541_);
lean_inc_ref(v___y_1540_);
lean_inc(v___y_1539_);
lean_inc_ref(v___y_1538_);
lean_inc_ref(v_e_1536_);
v___x_1547_ = lean_infer_type(v_e_1536_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_);
if (lean_obj_tag(v___x_1547_) == 0)
{
lean_object* v_a_1548_; lean_object* v___x_1549_; 
v_a_1548_ = lean_ctor_get(v___x_1547_, 0);
lean_inc(v_a_1548_);
lean_dec_ref_known(v___x_1547_, 1);
v___x_1549_ = l_Lean_Meta_whnfD(v_a_1548_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_);
if (lean_obj_tag(v___x_1549_) == 0)
{
lean_object* v_a_1550_; lean_object* v_dummy_1551_; lean_object* v_nargs_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; 
v_a_1550_ = lean_ctor_get(v___x_1549_, 0);
lean_inc(v_a_1550_);
lean_dec_ref_known(v___x_1549_, 1);
v_dummy_1551_ = lean_obj_once(&l_Lean_Meta_getInductiveUniverseAndParams___closed__0, &l_Lean_Meta_getInductiveUniverseAndParams___closed__0_once, _init_l_Lean_Meta_getInductiveUniverseAndParams___closed__0);
v_nargs_1552_ = l_Lean_Expr_getAppNumArgs(v_a_1550_);
lean_inc(v_nargs_1552_);
v___x_1553_ = lean_mk_array(v_nargs_1552_, v_dummy_1551_);
v___x_1554_ = lean_unsigned_to_nat(1u);
v___x_1555_ = lean_nat_sub(v_nargs_1552_, v___x_1554_);
lean_dec(v_nargs_1552_);
v___x_1556_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_generalizeIndices_x27_spec__0(v_mvarId_1535_, v_e_1536_, v_lctx_1543_, v_localInstances_1544_, v_varName_x3f_1537_, v_a_1550_, v___x_1553_, v___x_1555_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_);
lean_dec(v___y_1541_);
lean_dec_ref(v___y_1540_);
lean_dec(v___y_1539_);
lean_dec_ref(v___y_1538_);
return v___x_1556_;
}
else
{
lean_object* v_a_1557_; lean_object* v___x_1559_; uint8_t v_isShared_1560_; uint8_t v_isSharedCheck_1564_; 
lean_dec_ref(v_localInstances_1544_);
lean_dec_ref(v_lctx_1543_);
lean_dec(v___y_1541_);
lean_dec_ref(v___y_1540_);
lean_dec(v___y_1539_);
lean_dec_ref(v___y_1538_);
lean_dec(v_varName_x3f_1537_);
lean_dec_ref(v_e_1536_);
lean_dec(v_mvarId_1535_);
v_a_1557_ = lean_ctor_get(v___x_1549_, 0);
v_isSharedCheck_1564_ = !lean_is_exclusive(v___x_1549_);
if (v_isSharedCheck_1564_ == 0)
{
v___x_1559_ = v___x_1549_;
v_isShared_1560_ = v_isSharedCheck_1564_;
goto v_resetjp_1558_;
}
else
{
lean_inc(v_a_1557_);
lean_dec(v___x_1549_);
v___x_1559_ = lean_box(0);
v_isShared_1560_ = v_isSharedCheck_1564_;
goto v_resetjp_1558_;
}
v_resetjp_1558_:
{
lean_object* v___x_1562_; 
if (v_isShared_1560_ == 0)
{
v___x_1562_ = v___x_1559_;
goto v_reusejp_1561_;
}
else
{
lean_object* v_reuseFailAlloc_1563_; 
v_reuseFailAlloc_1563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1563_, 0, v_a_1557_);
v___x_1562_ = v_reuseFailAlloc_1563_;
goto v_reusejp_1561_;
}
v_reusejp_1561_:
{
return v___x_1562_;
}
}
}
}
else
{
lean_object* v_a_1565_; lean_object* v___x_1567_; uint8_t v_isShared_1568_; uint8_t v_isSharedCheck_1572_; 
lean_dec_ref(v_localInstances_1544_);
lean_dec_ref(v_lctx_1543_);
lean_dec(v___y_1541_);
lean_dec_ref(v___y_1540_);
lean_dec(v___y_1539_);
lean_dec_ref(v___y_1538_);
lean_dec(v_varName_x3f_1537_);
lean_dec_ref(v_e_1536_);
lean_dec(v_mvarId_1535_);
v_a_1565_ = lean_ctor_get(v___x_1547_, 0);
v_isSharedCheck_1572_ = !lean_is_exclusive(v___x_1547_);
if (v_isSharedCheck_1572_ == 0)
{
v___x_1567_ = v___x_1547_;
v_isShared_1568_ = v_isSharedCheck_1572_;
goto v_resetjp_1566_;
}
else
{
lean_inc(v_a_1565_);
lean_dec(v___x_1547_);
v___x_1567_ = lean_box(0);
v_isShared_1568_ = v_isSharedCheck_1572_;
goto v_resetjp_1566_;
}
v_resetjp_1566_:
{
lean_object* v___x_1570_; 
if (v_isShared_1568_ == 0)
{
v___x_1570_ = v___x_1567_;
goto v_reusejp_1569_;
}
else
{
lean_object* v_reuseFailAlloc_1571_; 
v_reuseFailAlloc_1571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1571_, 0, v_a_1565_);
v___x_1570_ = v_reuseFailAlloc_1571_;
goto v_reusejp_1569_;
}
v_reusejp_1569_:
{
return v___x_1570_;
}
}
}
}
else
{
lean_object* v_a_1573_; lean_object* v___x_1575_; uint8_t v_isShared_1576_; uint8_t v_isSharedCheck_1580_; 
lean_dec_ref(v_localInstances_1544_);
lean_dec_ref(v_lctx_1543_);
lean_dec(v___y_1541_);
lean_dec_ref(v___y_1540_);
lean_dec(v___y_1539_);
lean_dec_ref(v___y_1538_);
lean_dec(v_varName_x3f_1537_);
lean_dec_ref(v_e_1536_);
lean_dec(v_mvarId_1535_);
v_a_1573_ = lean_ctor_get(v___x_1546_, 0);
v_isSharedCheck_1580_ = !lean_is_exclusive(v___x_1546_);
if (v_isSharedCheck_1580_ == 0)
{
v___x_1575_ = v___x_1546_;
v_isShared_1576_ = v_isSharedCheck_1580_;
goto v_resetjp_1574_;
}
else
{
lean_inc(v_a_1573_);
lean_dec(v___x_1546_);
v___x_1575_ = lean_box(0);
v_isShared_1576_ = v_isSharedCheck_1580_;
goto v_resetjp_1574_;
}
v_resetjp_1574_:
{
lean_object* v___x_1578_; 
if (v_isShared_1576_ == 0)
{
v___x_1578_ = v___x_1575_;
goto v_reusejp_1577_;
}
else
{
lean_object* v_reuseFailAlloc_1579_; 
v_reuseFailAlloc_1579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1579_, 0, v_a_1573_);
v___x_1578_ = v_reuseFailAlloc_1579_;
goto v_reusejp_1577_;
}
v_reusejp_1577_:
{
return v___x_1578_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeIndices_x27___lam__0___boxed(lean_object* v_mvarId_1581_, lean_object* v_e_1582_, lean_object* v_varName_x3f_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_){
_start:
{
lean_object* v_res_1589_; 
v_res_1589_ = l_Lean_Meta_generalizeIndices_x27___lam__0(v_mvarId_1581_, v_e_1582_, v_varName_x3f_1583_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_);
return v_res_1589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeIndices_x27(lean_object* v_mvarId_1590_, lean_object* v_e_1591_, lean_object* v_varName_x3f_1592_, lean_object* v_a_1593_, lean_object* v_a_1594_, lean_object* v_a_1595_, lean_object* v_a_1596_){
_start:
{
lean_object* v___f_1598_; lean_object* v___x_1599_; 
lean_inc(v_mvarId_1590_);
v___f_1598_ = lean_alloc_closure((void*)(l_Lean_Meta_generalizeIndices_x27___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1598_, 0, v_mvarId_1590_);
lean_closure_set(v___f_1598_, 1, v_e_1591_);
lean_closure_set(v___f_1598_, 2, v_varName_x3f_1592_);
v___x_1599_ = l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2___redArg(v_mvarId_1590_, v___f_1598_, v_a_1593_, v_a_1594_, v_a_1595_, v_a_1596_);
return v___x_1599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeIndices_x27___boxed(lean_object* v_mvarId_1600_, lean_object* v_e_1601_, lean_object* v_varName_x3f_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_, lean_object* v_a_1607_){
_start:
{
lean_object* v_res_1608_; 
v_res_1608_ = l_Lean_Meta_generalizeIndices_x27(v_mvarId_1600_, v_e_1601_, v_varName_x3f_1602_, v_a_1603_, v_a_1604_, v_a_1605_, v_a_1606_);
lean_dec(v_a_1606_);
lean_dec_ref(v_a_1605_);
lean_dec(v_a_1604_);
lean_dec_ref(v_a_1603_);
return v_res_1608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeIndices___lam__0(lean_object* v_fvarId_1609_, lean_object* v_mvarId_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_){
_start:
{
lean_object* v___x_1616_; 
v___x_1616_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_1609_, v___y_1611_, v___y_1613_, v___y_1614_);
if (lean_obj_tag(v___x_1616_) == 0)
{
lean_object* v_a_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; 
v_a_1617_ = lean_ctor_get(v___x_1616_, 0);
lean_inc_n(v_a_1617_, 2);
lean_dec_ref_known(v___x_1616_, 1);
v___x_1618_ = l_Lean_LocalDecl_toExpr(v_a_1617_);
v___x_1619_ = l_Lean_LocalDecl_userName(v_a_1617_);
lean_dec(v_a_1617_);
v___x_1620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1620_, 0, v___x_1619_);
v___x_1621_ = l_Lean_Meta_generalizeIndices_x27(v_mvarId_1610_, v___x_1618_, v___x_1620_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_);
return v___x_1621_;
}
else
{
lean_object* v_a_1622_; lean_object* v___x_1624_; uint8_t v_isShared_1625_; uint8_t v_isSharedCheck_1629_; 
lean_dec(v_mvarId_1610_);
v_a_1622_ = lean_ctor_get(v___x_1616_, 0);
v_isSharedCheck_1629_ = !lean_is_exclusive(v___x_1616_);
if (v_isSharedCheck_1629_ == 0)
{
v___x_1624_ = v___x_1616_;
v_isShared_1625_ = v_isSharedCheck_1629_;
goto v_resetjp_1623_;
}
else
{
lean_inc(v_a_1622_);
lean_dec(v___x_1616_);
v___x_1624_ = lean_box(0);
v_isShared_1625_ = v_isSharedCheck_1629_;
goto v_resetjp_1623_;
}
v_resetjp_1623_:
{
lean_object* v___x_1627_; 
if (v_isShared_1625_ == 0)
{
v___x_1627_ = v___x_1624_;
goto v_reusejp_1626_;
}
else
{
lean_object* v_reuseFailAlloc_1628_; 
v_reuseFailAlloc_1628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1628_, 0, v_a_1622_);
v___x_1627_ = v_reuseFailAlloc_1628_;
goto v_reusejp_1626_;
}
v_reusejp_1626_:
{
return v___x_1627_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeIndices___lam__0___boxed(lean_object* v_fvarId_1630_, lean_object* v_mvarId_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_){
_start:
{
lean_object* v_res_1637_; 
v_res_1637_ = l_Lean_Meta_generalizeIndices___lam__0(v_fvarId_1630_, v_mvarId_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_);
lean_dec(v___y_1635_);
lean_dec_ref(v___y_1634_);
lean_dec(v___y_1633_);
lean_dec_ref(v___y_1632_);
return v_res_1637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeIndices(lean_object* v_mvarId_1638_, lean_object* v_fvarId_1639_, lean_object* v_a_1640_, lean_object* v_a_1641_, lean_object* v_a_1642_, lean_object* v_a_1643_){
_start:
{
lean_object* v___f_1645_; lean_object* v___x_1646_; 
lean_inc(v_mvarId_1638_);
v___f_1645_ = lean_alloc_closure((void*)(l_Lean_Meta_generalizeIndices___lam__0___boxed), 7, 2);
lean_closure_set(v___f_1645_, 0, v_fvarId_1639_);
lean_closure_set(v___f_1645_, 1, v_mvarId_1638_);
v___x_1646_ = l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2___redArg(v_mvarId_1638_, v___f_1645_, v_a_1640_, v_a_1641_, v_a_1642_, v_a_1643_);
return v___x_1646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeIndices___boxed(lean_object* v_mvarId_1647_, lean_object* v_fvarId_1648_, lean_object* v_a_1649_, lean_object* v_a_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_){
_start:
{
lean_object* v_res_1654_; 
v_res_1654_ = l_Lean_Meta_generalizeIndices(v_mvarId_1647_, v_fvarId_1648_, v_a_1649_, v_a_1650_, v_a_1651_, v_a_1652_);
lean_dec(v_a_1652_);
lean_dec_ref(v_a_1651_);
lean_dec(v_a_1650_);
lean_dec_ref(v_a_1649_);
return v_res_1654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0___redArg(lean_object* v___x_1656_, lean_object* v_a_1657_, lean_object* v_x_1658_, lean_object* v_x_1659_, lean_object* v_x_1660_, lean_object* v___y_1661_){
_start:
{
if (lean_obj_tag(v_x_1658_) == 5)
{
lean_object* v_fn_1666_; lean_object* v_arg_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; 
v_fn_1666_ = lean_ctor_get(v_x_1658_, 0);
lean_inc_ref(v_fn_1666_);
v_arg_1667_ = lean_ctor_get(v_x_1658_, 1);
lean_inc_ref(v_arg_1667_);
lean_dec_ref_known(v_x_1658_, 2);
v___x_1668_ = lean_array_set(v_x_1659_, v_x_1660_, v_arg_1667_);
v___x_1669_ = lean_unsigned_to_nat(1u);
v___x_1670_ = lean_nat_sub(v_x_1660_, v___x_1669_);
lean_dec(v_x_1660_);
v_x_1658_ = v_fn_1666_;
v_x_1659_ = v___x_1668_;
v_x_1660_ = v___x_1670_;
goto _start;
}
else
{
lean_dec(v_x_1660_);
if (lean_obj_tag(v_x_1658_) == 4)
{
lean_object* v_declName_1672_; uint8_t v___x_1673_; uint8_t v___x_1674_; lean_object* v___x_1675_; lean_object* v_env_1676_; lean_object* v___x_1677_; 
v_declName_1672_ = lean_ctor_get(v_x_1658_, 0);
v___x_1673_ = 0;
v___x_1674_ = 1;
v___x_1675_ = lean_st_ref_get(v___y_1661_);
v_env_1676_ = lean_ctor_get(v___x_1675_, 0);
lean_inc_ref(v_env_1676_);
lean_dec(v___x_1675_);
lean_inc(v_declName_1672_);
v___x_1677_ = l_Lean_Environment_find_x3f(v_env_1676_, v_declName_1672_, v___x_1673_);
if (lean_obj_tag(v___x_1677_) == 0)
{
lean_dec_ref_known(v_x_1658_, 2);
lean_dec_ref(v_x_1659_);
lean_dec_ref(v_a_1657_);
lean_dec_ref(v___x_1656_);
goto v___jp_1663_;
}
else
{
lean_object* v_val_1678_; lean_object* v___x_1680_; uint8_t v_isShared_1681_; uint8_t v_isSharedCheck_1716_; 
v_val_1678_ = lean_ctor_get(v___x_1677_, 0);
v_isSharedCheck_1716_ = !lean_is_exclusive(v___x_1677_);
if (v_isSharedCheck_1716_ == 0)
{
v___x_1680_ = v___x_1677_;
v_isShared_1681_ = v_isSharedCheck_1716_;
goto v_resetjp_1679_;
}
else
{
lean_inc(v_val_1678_);
lean_dec(v___x_1677_);
v___x_1680_ = lean_box(0);
v_isShared_1681_ = v_isSharedCheck_1716_;
goto v_resetjp_1679_;
}
v_resetjp_1679_:
{
if (lean_obj_tag(v_val_1678_) == 5)
{
lean_object* v_val_1682_; lean_object* v___x_1684_; uint8_t v_isShared_1685_; uint8_t v_isSharedCheck_1715_; 
v_val_1682_ = lean_ctor_get(v_val_1678_, 0);
v_isSharedCheck_1715_ = !lean_is_exclusive(v_val_1678_);
if (v_isSharedCheck_1715_ == 0)
{
v___x_1684_ = v_val_1678_;
v_isShared_1685_ = v_isSharedCheck_1715_;
goto v_resetjp_1683_;
}
else
{
lean_inc(v_val_1682_);
lean_dec(v_val_1678_);
v___x_1684_ = lean_box(0);
v_isShared_1685_ = v_isSharedCheck_1715_;
goto v_resetjp_1683_;
}
v_resetjp_1683_:
{
lean_object* v_toConstantVal_1686_; lean_object* v_numParams_1687_; lean_object* v_numIndices_1688_; lean_object* v_ctors_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; uint8_t v___x_1692_; 
v_toConstantVal_1686_ = lean_ctor_get(v_val_1682_, 0);
v_numParams_1687_ = lean_ctor_get(v_val_1682_, 1);
v_numIndices_1688_ = lean_ctor_get(v_val_1682_, 2);
v_ctors_1689_ = lean_ctor_get(v_val_1682_, 4);
v___x_1690_ = lean_array_get_size(v_x_1659_);
v___x_1691_ = lean_nat_add(v_numIndices_1688_, v_numParams_1687_);
v___x_1692_ = lean_nat_dec_eq(v___x_1690_, v___x_1691_);
lean_dec(v___x_1691_);
if (v___x_1692_ == 0)
{
lean_object* v___x_1693_; lean_object* v___x_1695_; 
lean_dec_ref(v_val_1682_);
lean_del_object(v___x_1680_);
lean_dec_ref_known(v_x_1658_, 2);
lean_dec_ref(v_x_1659_);
lean_dec_ref(v_a_1657_);
lean_dec_ref(v___x_1656_);
v___x_1693_ = lean_box(0);
if (v_isShared_1685_ == 0)
{
lean_ctor_set_tag(v___x_1684_, 0);
lean_ctor_set(v___x_1684_, 0, v___x_1693_);
v___x_1695_ = v___x_1684_;
goto v_reusejp_1694_;
}
else
{
lean_object* v_reuseFailAlloc_1696_; 
v_reuseFailAlloc_1696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1696_, 0, v___x_1693_);
v___x_1695_ = v_reuseFailAlloc_1696_;
goto v_reusejp_1694_;
}
v_reusejp_1694_:
{
return v___x_1695_;
}
}
else
{
lean_object* v_name_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; uint8_t v___x_1700_; 
v_name_1697_ = lean_ctor_get(v_toConstantVal_1686_, 0);
v___x_1698_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0___redArg___closed__0));
lean_inc(v_name_1697_);
v___x_1699_ = l_Lean_Name_str___override(v_name_1697_, v___x_1698_);
v___x_1700_ = l_Lean_Environment_contains(v___x_1656_, v___x_1699_, v___x_1674_);
if (v___x_1700_ == 0)
{
lean_object* v___x_1701_; lean_object* v___x_1703_; 
lean_dec_ref(v_val_1682_);
lean_del_object(v___x_1680_);
lean_dec_ref_known(v_x_1658_, 2);
lean_dec_ref(v_x_1659_);
lean_dec_ref(v_a_1657_);
v___x_1701_ = lean_box(0);
if (v_isShared_1685_ == 0)
{
lean_ctor_set_tag(v___x_1684_, 0);
lean_ctor_set(v___x_1684_, 0, v___x_1701_);
v___x_1703_ = v___x_1684_;
goto v_reusejp_1702_;
}
else
{
lean_object* v_reuseFailAlloc_1704_; 
v_reuseFailAlloc_1704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1704_, 0, v___x_1701_);
v___x_1703_ = v_reuseFailAlloc_1704_;
goto v_reusejp_1702_;
}
v_reusejp_1702_:
{
return v___x_1703_;
}
}
else
{
lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1710_; 
v___x_1705_ = l_List_lengthTR___redArg(v_ctors_1689_);
v___x_1706_ = lean_nat_sub(v___x_1690_, v_numIndices_1688_);
v___x_1707_ = l_Array_extract___redArg(v_x_1659_, v___x_1706_, v___x_1690_);
v___x_1708_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1708_, 0, v_val_1682_);
lean_ctor_set(v___x_1708_, 1, v___x_1705_);
lean_ctor_set(v___x_1708_, 2, v_a_1657_);
lean_ctor_set(v___x_1708_, 3, v_x_1658_);
lean_ctor_set(v___x_1708_, 4, v_x_1659_);
lean_ctor_set(v___x_1708_, 5, v___x_1707_);
if (v_isShared_1681_ == 0)
{
lean_ctor_set(v___x_1680_, 0, v___x_1708_);
v___x_1710_ = v___x_1680_;
goto v_reusejp_1709_;
}
else
{
lean_object* v_reuseFailAlloc_1714_; 
v_reuseFailAlloc_1714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1714_, 0, v___x_1708_);
v___x_1710_ = v_reuseFailAlloc_1714_;
goto v_reusejp_1709_;
}
v_reusejp_1709_:
{
lean_object* v___x_1712_; 
if (v_isShared_1685_ == 0)
{
lean_ctor_set_tag(v___x_1684_, 0);
lean_ctor_set(v___x_1684_, 0, v___x_1710_);
v___x_1712_ = v___x_1684_;
goto v_reusejp_1711_;
}
else
{
lean_object* v_reuseFailAlloc_1713_; 
v_reuseFailAlloc_1713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1713_, 0, v___x_1710_);
v___x_1712_ = v_reuseFailAlloc_1713_;
goto v_reusejp_1711_;
}
v_reusejp_1711_:
{
return v___x_1712_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_1680_);
lean_dec(v_val_1678_);
lean_dec_ref_known(v_x_1658_, 2);
lean_dec_ref(v_x_1659_);
lean_dec_ref(v_a_1657_);
lean_dec_ref(v___x_1656_);
goto v___jp_1663_;
}
}
}
}
else
{
lean_dec_ref(v_x_1659_);
lean_dec_ref(v_x_1658_);
lean_dec_ref(v_a_1657_);
lean_dec_ref(v___x_1656_);
goto v___jp_1663_;
}
}
v___jp_1663_:
{
lean_object* v___x_1664_; lean_object* v___x_1665_; 
v___x_1664_ = lean_box(0);
v___x_1665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1665_, 0, v___x_1664_);
return v___x_1665_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0___redArg___boxed(lean_object* v___x_1717_, lean_object* v_a_1718_, lean_object* v_x_1719_, lean_object* v_x_1720_, lean_object* v_x_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_){
_start:
{
lean_object* v_res_1724_; 
v_res_1724_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0___redArg(v___x_1717_, v_a_1718_, v_x_1719_, v_x_1720_, v_x_1721_, v___y_1722_);
lean_dec(v___y_1722_);
return v_res_1724_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f(lean_object* v_majorFVarId_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_){
_start:
{
lean_object* v___x_1731_; lean_object* v_env_1735_; lean_object* v___x_1736_; uint8_t v___x_1737_; uint8_t v___x_1738_; 
v___x_1731_ = lean_st_ref_get(v_a_1729_);
v_env_1735_ = lean_ctor_get(v___x_1731_, 0);
lean_inc_ref_n(v_env_1735_, 2);
lean_dec(v___x_1731_);
v___x_1736_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__5));
v___x_1737_ = 1;
v___x_1738_ = l_Lean_Environment_contains(v_env_1735_, v___x_1736_, v___x_1737_);
if (v___x_1738_ == 0)
{
lean_dec_ref(v_env_1735_);
lean_dec(v_majorFVarId_1725_);
goto v___jp_1732_;
}
else
{
lean_object* v___x_1739_; uint8_t v___x_1740_; 
v___x_1739_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__1));
lean_inc_ref(v_env_1735_);
v___x_1740_ = l_Lean_Environment_contains(v_env_1735_, v___x_1739_, v___x_1738_);
if (v___x_1740_ == 0)
{
lean_dec_ref(v_env_1735_);
lean_dec(v_majorFVarId_1725_);
goto v___jp_1732_;
}
else
{
lean_object* v___x_1741_; 
v___x_1741_ = l_Lean_FVarId_getDecl___redArg(v_majorFVarId_1725_, v_a_1726_, v_a_1728_, v_a_1729_);
if (lean_obj_tag(v___x_1741_) == 0)
{
lean_object* v_a_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; 
v_a_1742_ = lean_ctor_get(v___x_1741_, 0);
lean_inc(v_a_1742_);
lean_dec_ref_known(v___x_1741_, 1);
v___x_1743_ = l_Lean_LocalDecl_type(v_a_1742_);
lean_inc(v_a_1729_);
lean_inc_ref(v_a_1728_);
lean_inc(v_a_1727_);
lean_inc_ref(v_a_1726_);
v___x_1744_ = lean_whnf(v___x_1743_, v_a_1726_, v_a_1727_, v_a_1728_, v_a_1729_);
if (lean_obj_tag(v___x_1744_) == 0)
{
lean_object* v_a_1745_; lean_object* v_dummy_1746_; lean_object* v_nargs_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; 
v_a_1745_ = lean_ctor_get(v___x_1744_, 0);
lean_inc(v_a_1745_);
lean_dec_ref_known(v___x_1744_, 1);
v_dummy_1746_ = lean_obj_once(&l_Lean_Meta_getInductiveUniverseAndParams___closed__0, &l_Lean_Meta_getInductiveUniverseAndParams___closed__0_once, _init_l_Lean_Meta_getInductiveUniverseAndParams___closed__0);
v_nargs_1747_ = l_Lean_Expr_getAppNumArgs(v_a_1745_);
lean_inc(v_nargs_1747_);
v___x_1748_ = lean_mk_array(v_nargs_1747_, v_dummy_1746_);
v___x_1749_ = lean_unsigned_to_nat(1u);
v___x_1750_ = lean_nat_sub(v_nargs_1747_, v___x_1749_);
lean_dec(v_nargs_1747_);
v___x_1751_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0___redArg(v_env_1735_, v_a_1742_, v_a_1745_, v___x_1748_, v___x_1750_, v_a_1729_);
return v___x_1751_;
}
else
{
lean_object* v_a_1752_; lean_object* v___x_1754_; uint8_t v_isShared_1755_; uint8_t v_isSharedCheck_1759_; 
lean_dec(v_a_1742_);
lean_dec_ref(v_env_1735_);
v_a_1752_ = lean_ctor_get(v___x_1744_, 0);
v_isSharedCheck_1759_ = !lean_is_exclusive(v___x_1744_);
if (v_isSharedCheck_1759_ == 0)
{
v___x_1754_ = v___x_1744_;
v_isShared_1755_ = v_isSharedCheck_1759_;
goto v_resetjp_1753_;
}
else
{
lean_inc(v_a_1752_);
lean_dec(v___x_1744_);
v___x_1754_ = lean_box(0);
v_isShared_1755_ = v_isSharedCheck_1759_;
goto v_resetjp_1753_;
}
v_resetjp_1753_:
{
lean_object* v___x_1757_; 
if (v_isShared_1755_ == 0)
{
v___x_1757_ = v___x_1754_;
goto v_reusejp_1756_;
}
else
{
lean_object* v_reuseFailAlloc_1758_; 
v_reuseFailAlloc_1758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1758_, 0, v_a_1752_);
v___x_1757_ = v_reuseFailAlloc_1758_;
goto v_reusejp_1756_;
}
v_reusejp_1756_:
{
return v___x_1757_;
}
}
}
}
else
{
lean_object* v_a_1760_; lean_object* v___x_1762_; uint8_t v_isShared_1763_; uint8_t v_isSharedCheck_1767_; 
lean_dec_ref(v_env_1735_);
v_a_1760_ = lean_ctor_get(v___x_1741_, 0);
v_isSharedCheck_1767_ = !lean_is_exclusive(v___x_1741_);
if (v_isSharedCheck_1767_ == 0)
{
v___x_1762_ = v___x_1741_;
v_isShared_1763_ = v_isSharedCheck_1767_;
goto v_resetjp_1761_;
}
else
{
lean_inc(v_a_1760_);
lean_dec(v___x_1741_);
v___x_1762_ = lean_box(0);
v_isShared_1763_ = v_isSharedCheck_1767_;
goto v_resetjp_1761_;
}
v_resetjp_1761_:
{
lean_object* v___x_1765_; 
if (v_isShared_1763_ == 0)
{
v___x_1765_ = v___x_1762_;
goto v_reusejp_1764_;
}
else
{
lean_object* v_reuseFailAlloc_1766_; 
v_reuseFailAlloc_1766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1766_, 0, v_a_1760_);
v___x_1765_ = v_reuseFailAlloc_1766_;
goto v_reusejp_1764_;
}
v_reusejp_1764_:
{
return v___x_1765_;
}
}
}
}
}
v___jp_1732_:
{
lean_object* v___x_1733_; lean_object* v___x_1734_; 
v___x_1733_ = lean_box(0);
v___x_1734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1734_, 0, v___x_1733_);
return v___x_1734_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f___boxed(lean_object* v_majorFVarId_1768_, lean_object* v_a_1769_, lean_object* v_a_1770_, lean_object* v_a_1771_, lean_object* v_a_1772_, lean_object* v_a_1773_){
_start:
{
lean_object* v_res_1774_; 
v_res_1774_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f(v_majorFVarId_1768_, v_a_1769_, v_a_1770_, v_a_1771_, v_a_1772_);
lean_dec(v_a_1772_);
lean_dec_ref(v_a_1771_);
lean_dec(v_a_1770_);
lean_dec_ref(v_a_1769_);
return v_res_1774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0(lean_object* v___x_1775_, lean_object* v_a_1776_, lean_object* v_x_1777_, lean_object* v_x_1778_, lean_object* v_x_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_){
_start:
{
lean_object* v___x_1785_; 
v___x_1785_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0___redArg(v___x_1775_, v_a_1776_, v_x_1777_, v_x_1778_, v_x_1779_, v___y_1783_);
return v___x_1785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0___boxed(lean_object* v___x_1786_, lean_object* v_a_1787_, lean_object* v_x_1788_, lean_object* v_x_1789_, lean_object* v_x_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_){
_start:
{
lean_object* v_res_1796_; 
v_res_1796_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_spec__0(v___x_1786_, v_a_1787_, v_x_1788_, v_x_1789_, v_x_1790_, v___y_1791_, v___y_1792_, v___y_1793_, v___y_1794_);
lean_dec(v___y_1794_);
lean_dec_ref(v___y_1793_);
lean_dec(v___y_1792_);
lean_dec_ref(v___y_1791_);
return v_res_1796_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0___redArg(lean_object* v___x_1797_, lean_object* v_i_1798_, lean_object* v_n_1799_, lean_object* v_i_1800_){
_start:
{
lean_object* v_zero_1801_; uint8_t v_isZero_1802_; 
v_zero_1801_ = lean_unsigned_to_nat(0u);
v_isZero_1802_ = lean_nat_dec_eq(v_i_1800_, v_zero_1801_);
if (v_isZero_1802_ == 1)
{
uint8_t v___x_1803_; 
lean_dec(v_i_1800_);
v___x_1803_ = 0;
return v___x_1803_;
}
else
{
lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; uint8_t v___x_1807_; 
v___x_1804_ = lean_nat_sub(v_n_1799_, v_i_1800_);
v___x_1805_ = lean_array_fget_borrowed(v___x_1797_, v_i_1798_);
v___x_1806_ = lean_array_fget_borrowed(v___x_1797_, v___x_1804_);
lean_dec(v___x_1804_);
v___x_1807_ = lean_expr_eqv(v___x_1805_, v___x_1806_);
if (v___x_1807_ == 0)
{
lean_object* v_one_1808_; lean_object* v_n_1809_; 
v_one_1808_ = lean_unsigned_to_nat(1u);
v_n_1809_ = lean_nat_sub(v_i_1800_, v_one_1808_);
lean_dec(v_i_1800_);
v_i_1800_ = v_n_1809_;
goto _start;
}
else
{
lean_dec(v_i_1800_);
return v___x_1807_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0___redArg___boxed(lean_object* v___x_1811_, lean_object* v_i_1812_, lean_object* v_n_1813_, lean_object* v_i_1814_){
_start:
{
uint8_t v_res_1815_; lean_object* v_r_1816_; 
v_res_1815_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0___redArg(v___x_1811_, v_i_1812_, v_n_1813_, v_i_1814_);
lean_dec(v_n_1813_);
lean_dec(v_i_1812_);
lean_dec_ref(v___x_1811_);
v_r_1816_ = lean_box(v_res_1815_);
return v_r_1816_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1___redArg(lean_object* v___x_1817_, lean_object* v_n_1818_, lean_object* v_i_1819_){
_start:
{
lean_object* v_zero_1820_; uint8_t v_isZero_1821_; 
v_zero_1820_ = lean_unsigned_to_nat(0u);
v_isZero_1821_ = lean_nat_dec_eq(v_i_1819_, v_zero_1820_);
if (v_isZero_1821_ == 1)
{
uint8_t v___x_1822_; 
lean_dec(v_i_1819_);
v___x_1822_ = 0;
return v___x_1822_;
}
else
{
lean_object* v___x_1823_; uint8_t v___x_1824_; 
v___x_1823_ = lean_nat_sub(v_n_1818_, v_i_1819_);
lean_inc(v___x_1823_);
v___x_1824_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0___redArg(v___x_1817_, v___x_1823_, v___x_1823_, v___x_1823_);
lean_dec(v___x_1823_);
if (v___x_1824_ == 0)
{
lean_object* v_one_1825_; lean_object* v_n_1826_; 
v_one_1825_ = lean_unsigned_to_nat(1u);
v_n_1826_ = lean_nat_sub(v_i_1819_, v_one_1825_);
lean_dec(v_i_1819_);
v_i_1819_ = v_n_1826_;
goto _start;
}
else
{
lean_dec(v_i_1819_);
return v___x_1824_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1___redArg___boxed(lean_object* v___x_1828_, lean_object* v_n_1829_, lean_object* v_i_1830_){
_start:
{
uint8_t v_res_1831_; lean_object* v_r_1832_; 
v_res_1831_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1___redArg(v___x_1828_, v_n_1829_, v_i_1830_);
lean_dec(v_n_1829_);
lean_dec_ref(v___x_1828_);
v_r_1832_ = lean_box(v_res_1831_);
return v_r_1832_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5(lean_object* v___x_1833_, lean_object* v_as_1834_, size_t v_i_1835_, size_t v_stop_1836_){
_start:
{
uint8_t v___x_1837_; 
v___x_1837_ = lean_usize_dec_eq(v_i_1835_, v_stop_1836_);
if (v___x_1837_ == 0)
{
uint8_t v___x_1838_; lean_object* v___x_1839_; uint8_t v___x_1840_; 
v___x_1838_ = 1;
v___x_1839_ = lean_array_uget_borrowed(v_as_1834_, v_i_1835_);
v___x_1840_ = l_Lean_Expr_isFVar(v___x_1839_);
if (v___x_1840_ == 0)
{
return v___x_1838_;
}
else
{
lean_object* v___x_1841_; uint8_t v___x_1842_; 
v___x_1841_ = lean_unsigned_to_nat(0u);
v___x_1842_ = lean_nat_dec_eq(v___x_1833_, v___x_1841_);
if (v___x_1842_ == 0)
{
size_t v___x_1843_; size_t v___x_1844_; 
v___x_1843_ = ((size_t)1ULL);
v___x_1844_ = lean_usize_add(v_i_1835_, v___x_1843_);
v_i_1835_ = v___x_1844_;
goto _start;
}
else
{
return v___x_1838_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5___boxed(lean_object* v___x_1847_, lean_object* v_as_1848_, lean_object* v_i_1849_, lean_object* v_stop_1850_){
_start:
{
size_t v_i_boxed_1851_; size_t v_stop_boxed_1852_; uint8_t v_res_1853_; lean_object* v_r_1854_; 
v_i_boxed_1851_ = lean_unbox_usize(v_i_1849_);
lean_dec(v_i_1849_);
v_stop_boxed_1852_ = lean_unbox_usize(v_stop_1850_);
lean_dec(v_stop_1850_);
v_res_1853_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5(v___x_1847_, v_as_1848_, v_i_boxed_1851_, v_stop_boxed_1852_);
lean_dec_ref(v_as_1848_);
lean_dec(v___x_1847_);
v_r_1854_ = lean_box(v_res_1853_);
return v_r_1854_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__2(lean_object* v_fvarId_1855_, uint8_t v___x_1856_, lean_object* v_as_1857_, size_t v_i_1858_, size_t v_stop_1859_){
_start:
{
uint8_t v___x_1860_; 
v___x_1860_ = lean_usize_dec_eq(v_i_1858_, v_stop_1859_);
if (v___x_1860_ == 0)
{
uint8_t v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; uint8_t v___x_1864_; 
v___x_1861_ = 1;
v___x_1862_ = lean_array_uget_borrowed(v_as_1857_, v_i_1858_);
v___x_1863_ = l_Lean_Expr_fvarId_x21(v___x_1862_);
v___x_1864_ = l_Lean_instBEqFVarId_beq(v___x_1863_, v_fvarId_1855_);
lean_dec(v___x_1863_);
if (v___x_1864_ == 0)
{
if (v___x_1856_ == 0)
{
size_t v___x_1865_; size_t v___x_1866_; 
v___x_1865_ = ((size_t)1ULL);
v___x_1866_ = lean_usize_add(v_i_1858_, v___x_1865_);
v_i_1858_ = v___x_1866_;
goto _start;
}
else
{
return v___x_1861_;
}
}
else
{
return v___x_1861_;
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
uint8_t v___x_7581__boxed_1874_; size_t v_i_boxed_1875_; size_t v_stop_boxed_1876_; uint8_t v_res_1877_; lean_object* v_r_1878_; 
v___x_7581__boxed_1874_ = lean_unbox(v___x_1870_);
v_i_boxed_1875_ = lean_unbox_usize(v_i_1872_);
lean_dec(v_i_1872_);
v_stop_boxed_1876_ = lean_unbox_usize(v_stop_1873_);
lean_dec(v_stop_1873_);
v_res_1877_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__2(v_fvarId_1869_, v___x_7581__boxed_1874_, v_as_1871_, v_i_boxed_1875_, v_stop_boxed_1876_);
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
uint8_t v___x_7604__boxed_1899_; uint8_t v_res_1900_; lean_object* v_r_1901_; 
v___x_7604__boxed_1899_ = lean_unbox(v___x_1896_);
v_res_1900_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___lam__1(v___x_1894_, v___x_1895_, v___x_7604__boxed_1899_, v___x_1897_, v_fvarId_1898_);
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
uint8_t v___x_7653__boxed_1926_; uint8_t v_res_1927_; lean_object* v_r_1928_; 
v___x_7653__boxed_1926_ = lean_unbox(v___x_1924_);
v_res_1927_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___lam__0(v___x_7653__boxed_1926_, v_x_1925_);
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
lean_object* v___x_2032_; lean_object* v___f_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___f_2036_; lean_object* v___y_2038_; lean_object* v_snd_2039_; lean_object* v___y_2045_; lean_object* v___y_2046_; lean_object* v___y_2083_; uint8_t v___x_2088_; 
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
v___x_2088_ = lean_nat_dec_lt(v___x_2034_, v___x_1937_);
if (v___x_2088_ == 0)
{
lean_dec(v___x_2029_);
goto v___jp_2052_;
}
else
{
lean_object* v___x_2089_; uint8_t v___x_2090_; 
v___x_2089_ = lean_array_get_size(v___x_1936_);
v___x_2090_ = lean_nat_dec_le(v___x_1937_, v___x_2089_);
if (v___x_2090_ == 0)
{
v___y_2083_ = v___x_2089_;
goto v___jp_2082_;
}
else
{
lean_inc(v___x_1937_);
v___y_2083_ = v___x_1937_;
goto v___jp_2082_;
}
}
v___jp_2037_:
{
uint8_t v___x_2040_; 
v___x_2040_ = l_Lean_Expr_hasFVar(v___y_2038_);
if (v___x_2040_ == 0)
{
uint8_t v___x_2041_; 
v___x_2041_ = l_Lean_Expr_hasMVar(v___y_2038_);
if (v___x_2041_ == 0)
{
lean_dec_ref(v___y_2038_);
lean_dec_ref(v___f_2036_);
lean_dec_ref(v___f_2033_);
v_fst_1981_ = v___x_2041_;
v_snd_1982_ = v_snd_2039_;
goto v___jp_1980_;
}
else
{
lean_object* v___x_2042_; 
v___x_2042_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_2036_, v___f_2033_, v___y_2038_, v_snd_2039_);
v___y_1999_ = v___x_2042_;
goto v___jp_1998_;
}
}
else
{
lean_object* v___x_2043_; 
v___x_2043_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_2036_, v___f_2033_, v___y_2038_, v_snd_2039_);
v___y_1999_ = v___x_2043_;
goto v___jp_1998_;
}
}
v___jp_2044_:
{
lean_object* v_fst_2047_; uint8_t v___x_2048_; 
v_fst_2047_ = lean_ctor_get(v___y_2046_, 0);
v___x_2048_ = lean_unbox(v_fst_2047_);
if (v___x_2048_ == 0)
{
lean_object* v_snd_2049_; 
v_snd_2049_ = lean_ctor_get(v___y_2046_, 1);
lean_inc(v_snd_2049_);
lean_dec_ref(v___y_2046_);
v___y_2038_ = v___y_2045_;
v_snd_2039_ = v_snd_2049_;
goto v___jp_2037_;
}
else
{
lean_object* v_snd_2050_; uint8_t v___x_2051_; 
lean_inc(v_fst_2047_);
lean_dec_ref(v___y_2045_);
lean_dec_ref(v___f_2036_);
lean_dec_ref(v___f_2033_);
v_snd_2050_ = lean_ctor_get(v___y_2046_, 1);
lean_inc(v_snd_2050_);
lean_dec_ref(v___y_2046_);
v___x_2051_ = lean_unbox(v_fst_2047_);
lean_dec(v_fst_2047_);
v_fst_1981_ = v___x_2051_;
v_snd_1982_ = v_snd_2050_;
goto v___jp_1980_;
}
}
v___jp_2052_:
{
if (lean_obj_tag(v_val_2027_) == 0)
{
lean_object* v_type_2053_; lean_object* v___x_2054_; lean_object* v_mctx_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; uint8_t v___x_2058_; 
v_type_2053_ = lean_ctor_get(v_val_2027_, 3);
v___x_2054_ = lean_st_ref_get(v___y_1942_);
v_mctx_2055_ = lean_ctor_get(v___x_2054_, 0);
lean_inc_ref_n(v_mctx_2055_, 2);
lean_dec(v___x_2054_);
v___x_2056_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1);
v___x_2057_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2057_, 0, v___x_2056_);
lean_ctor_set(v___x_2057_, 1, v_mctx_2055_);
v___x_2058_ = l_Lean_Expr_hasFVar(v_type_2053_);
if (v___x_2058_ == 0)
{
uint8_t v___x_2059_; 
v___x_2059_ = l_Lean_Expr_hasMVar(v_type_2053_);
if (v___x_2059_ == 0)
{
lean_dec_ref_known(v___x_2057_, 2);
lean_dec_ref(v___f_2036_);
lean_dec_ref(v___f_2033_);
v_fst_2004_ = v___x_2059_;
v_mctx_2005_ = v_mctx_2055_;
goto v___jp_2003_;
}
else
{
lean_object* v___x_2060_; 
lean_dec_ref(v_mctx_2055_);
lean_inc_ref(v_type_2053_);
v___x_2060_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_2036_, v___f_2033_, v_type_2053_, v___x_2057_);
v___y_2021_ = v___x_2060_;
goto v___jp_2020_;
}
}
else
{
lean_object* v___x_2061_; 
lean_dec_ref(v_mctx_2055_);
lean_inc_ref(v_type_2053_);
v___x_2061_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_2036_, v___f_2033_, v_type_2053_, v___x_2057_);
v___y_2021_ = v___x_2061_;
goto v___jp_2020_;
}
}
else
{
uint8_t v_nondep_2062_; 
v_nondep_2062_ = lean_ctor_get_uint8(v_val_2027_, sizeof(void*)*5);
if (v_nondep_2062_ == 0)
{
lean_object* v_type_2063_; lean_object* v_value_2064_; lean_object* v___x_2065_; lean_object* v_mctx_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; uint8_t v___x_2069_; 
v_type_2063_ = lean_ctor_get(v_val_2027_, 3);
v_value_2064_ = lean_ctor_get(v_val_2027_, 4);
v___x_2065_ = lean_st_ref_get(v___y_1942_);
v_mctx_2066_ = lean_ctor_get(v___x_2065_, 0);
lean_inc_ref(v_mctx_2066_);
lean_dec(v___x_2065_);
v___x_2067_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1);
v___x_2068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2068_, 0, v___x_2067_);
lean_ctor_set(v___x_2068_, 1, v_mctx_2066_);
v___x_2069_ = l_Lean_Expr_hasFVar(v_type_2063_);
if (v___x_2069_ == 0)
{
uint8_t v___x_2070_; 
v___x_2070_ = l_Lean_Expr_hasMVar(v_type_2063_);
if (v___x_2070_ == 0)
{
lean_inc_ref(v_value_2064_);
v___y_2038_ = v_value_2064_;
v_snd_2039_ = v___x_2068_;
goto v___jp_2037_;
}
else
{
lean_object* v___x_2071_; 
lean_inc_ref(v_type_2063_);
lean_inc_ref(v___f_2033_);
lean_inc_ref(v___f_2036_);
v___x_2071_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_2036_, v___f_2033_, v_type_2063_, v___x_2068_);
lean_inc_ref(v_value_2064_);
v___y_2045_ = v_value_2064_;
v___y_2046_ = v___x_2071_;
goto v___jp_2044_;
}
}
else
{
lean_object* v___x_2072_; 
lean_inc_ref(v_type_2063_);
lean_inc_ref(v___f_2033_);
lean_inc_ref(v___f_2036_);
v___x_2072_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_2036_, v___f_2033_, v_type_2063_, v___x_2068_);
lean_inc_ref(v_value_2064_);
v___y_2045_ = v_value_2064_;
v___y_2046_ = v___x_2072_;
goto v___jp_2044_;
}
}
else
{
lean_object* v_type_2073_; lean_object* v___x_2074_; lean_object* v_mctx_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; uint8_t v___x_2078_; 
v_type_2073_ = lean_ctor_get(v_val_2027_, 3);
v___x_2074_ = lean_st_ref_get(v___y_1942_);
v_mctx_2075_ = lean_ctor_get(v___x_2074_, 0);
lean_inc_ref_n(v_mctx_2075_, 2);
lean_dec(v___x_2074_);
v___x_2076_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___closed__1);
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
lean_dec_ref_known(v___x_2077_, 2);
lean_dec_ref(v___f_2036_);
lean_dec_ref(v___f_2033_);
v_fst_1958_ = v___x_2079_;
v_mctx_1959_ = v_mctx_2075_;
goto v___jp_1957_;
}
else
{
lean_object* v___x_2080_; 
lean_dec_ref(v_mctx_2075_);
lean_inc_ref(v_type_2073_);
v___x_2080_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_2036_, v___f_2033_, v_type_2073_, v___x_2077_);
v___y_1975_ = v___x_2080_;
goto v___jp_1974_;
}
}
else
{
lean_object* v___x_2081_; 
lean_dec_ref(v_mctx_2075_);
lean_inc_ref(v_type_2073_);
v___x_2081_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_2036_, v___f_2033_, v_type_2073_, v___x_2077_);
v___y_1975_ = v___x_2081_;
goto v___jp_1974_;
}
}
}
}
v___jp_2082_:
{
uint8_t v___x_2084_; 
v___x_2084_ = lean_nat_dec_lt(v___x_2034_, v___y_2083_);
if (v___x_2084_ == 0)
{
lean_dec(v___y_2083_);
lean_dec(v___x_2029_);
goto v___jp_2052_;
}
else
{
size_t v___x_2085_; size_t v___x_2086_; uint8_t v___x_2087_; 
v___x_2085_ = ((size_t)0ULL);
v___x_2086_ = lean_usize_of_nat(v___y_2083_);
lean_dec(v___y_2083_);
v___x_2087_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__3(v___x_2029_, v___x_1936_, v___x_2085_, v___x_2086_);
lean_dec(v___x_2029_);
if (v___x_2087_ == 0)
{
goto v___jp_2052_;
}
else
{
lean_dec_ref(v___f_2036_);
lean_dec_ref(v___f_2033_);
v_a_1947_ = v___x_1935_;
goto v___jp_1946_;
}
}
}
}
else
{
lean_dec(v___x_2029_);
v_a_1947_ = v___x_1935_;
goto v___jp_1946_;
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
uint8_t v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; 
lean_dec(v___x_1937_);
lean_dec_ref(v___x_1936_);
v___x_2091_ = 0;
v___x_2092_ = lean_box(v___x_2091_);
v___x_2093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2093_, 0, v___x_2092_);
return v___x_2093_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg___boxed(lean_object* v___x_2094_, lean_object* v___x_2095_, lean_object* v___x_2096_, lean_object* v_ctx_2097_, lean_object* v_as_2098_, lean_object* v_i_2099_, lean_object* v_stop_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_){
_start:
{
uint8_t v___x_7683__boxed_2103_; size_t v_i_boxed_2104_; size_t v_stop_boxed_2105_; lean_object* v_res_2106_; 
v___x_7683__boxed_2103_ = lean_unbox(v___x_2094_);
v_i_boxed_2104_ = lean_unbox_usize(v_i_2099_);
lean_dec(v_i_2099_);
v_stop_boxed_2105_ = lean_unbox_usize(v_stop_2100_);
lean_dec(v_stop_2100_);
v_res_2106_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg(v___x_7683__boxed_2103_, v___x_2095_, v___x_2096_, v_ctx_2097_, v_as_2098_, v_i_boxed_2104_, v_stop_boxed_2105_, v___y_2101_);
lean_dec(v___y_2101_);
lean_dec_ref(v_as_2098_);
lean_dec_ref(v_ctx_2097_);
return v_res_2106_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4(uint8_t v___x_2107_, lean_object* v___x_2108_, lean_object* v___x_2109_, lean_object* v_ctx_2110_, lean_object* v_x_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_){
_start:
{
if (lean_obj_tag(v_x_2111_) == 0)
{
lean_object* v_cs_2117_; lean_object* v___x_2119_; uint8_t v_isShared_2120_; uint8_t v_isSharedCheck_2131_; 
v_cs_2117_ = lean_ctor_get(v_x_2111_, 0);
v_isSharedCheck_2131_ = !lean_is_exclusive(v_x_2111_);
if (v_isSharedCheck_2131_ == 0)
{
v___x_2119_ = v_x_2111_;
v_isShared_2120_ = v_isSharedCheck_2131_;
goto v_resetjp_2118_;
}
else
{
lean_inc(v_cs_2117_);
lean_dec(v_x_2111_);
v___x_2119_ = lean_box(0);
v_isShared_2120_ = v_isSharedCheck_2131_;
goto v_resetjp_2118_;
}
v_resetjp_2118_:
{
lean_object* v___x_2121_; lean_object* v___x_2122_; uint8_t v___x_2123_; 
v___x_2121_ = lean_unsigned_to_nat(0u);
v___x_2122_ = lean_array_get_size(v_cs_2117_);
v___x_2123_ = lean_nat_dec_lt(v___x_2121_, v___x_2122_);
if (v___x_2123_ == 0)
{
lean_object* v___x_2124_; lean_object* v___x_2126_; 
lean_dec_ref(v_cs_2117_);
lean_dec(v___x_2109_);
lean_dec_ref(v___x_2108_);
v___x_2124_ = lean_box(v___x_2123_);
if (v_isShared_2120_ == 0)
{
lean_ctor_set(v___x_2119_, 0, v___x_2124_);
v___x_2126_ = v___x_2119_;
goto v_reusejp_2125_;
}
else
{
lean_object* v_reuseFailAlloc_2127_; 
v_reuseFailAlloc_2127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2127_, 0, v___x_2124_);
v___x_2126_ = v_reuseFailAlloc_2127_;
goto v_reusejp_2125_;
}
v_reusejp_2125_:
{
return v___x_2126_;
}
}
else
{
size_t v___x_2128_; size_t v___x_2129_; lean_object* v___x_2130_; 
lean_del_object(v___x_2119_);
v___x_2128_ = ((size_t)0ULL);
v___x_2129_ = lean_usize_of_nat(v___x_2122_);
v___x_2130_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4_spec__5(v___x_2107_, v___x_2108_, v___x_2109_, v_ctx_2110_, v_cs_2117_, v___x_2128_, v___x_2129_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_);
lean_dec_ref(v_cs_2117_);
return v___x_2130_;
}
}
}
else
{
lean_object* v_vs_2132_; lean_object* v___x_2134_; uint8_t v_isShared_2135_; uint8_t v_isSharedCheck_2146_; 
v_vs_2132_ = lean_ctor_get(v_x_2111_, 0);
v_isSharedCheck_2146_ = !lean_is_exclusive(v_x_2111_);
if (v_isSharedCheck_2146_ == 0)
{
v___x_2134_ = v_x_2111_;
v_isShared_2135_ = v_isSharedCheck_2146_;
goto v_resetjp_2133_;
}
else
{
lean_inc(v_vs_2132_);
lean_dec(v_x_2111_);
v___x_2134_ = lean_box(0);
v_isShared_2135_ = v_isSharedCheck_2146_;
goto v_resetjp_2133_;
}
v_resetjp_2133_:
{
lean_object* v___x_2136_; lean_object* v___x_2137_; uint8_t v___x_2138_; 
v___x_2136_ = lean_unsigned_to_nat(0u);
v___x_2137_ = lean_array_get_size(v_vs_2132_);
v___x_2138_ = lean_nat_dec_lt(v___x_2136_, v___x_2137_);
if (v___x_2138_ == 0)
{
lean_object* v___x_2139_; lean_object* v___x_2141_; 
lean_dec_ref(v_vs_2132_);
lean_dec(v___x_2109_);
lean_dec_ref(v___x_2108_);
v___x_2139_ = lean_box(v___x_2138_);
if (v_isShared_2135_ == 0)
{
lean_ctor_set_tag(v___x_2134_, 0);
lean_ctor_set(v___x_2134_, 0, v___x_2139_);
v___x_2141_ = v___x_2134_;
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
lean_del_object(v___x_2134_);
v___x_2143_ = ((size_t)0ULL);
v___x_2144_ = lean_usize_of_nat(v___x_2137_);
v___x_2145_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg(v___x_2107_, v___x_2108_, v___x_2109_, v_ctx_2110_, v_vs_2132_, v___x_2143_, v___x_2144_, v___y_2113_);
lean_dec_ref(v_vs_2132_);
return v___x_2145_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4_spec__5(uint8_t v___x_2147_, lean_object* v___x_2148_, lean_object* v___x_2149_, lean_object* v_ctx_2150_, lean_object* v_as_2151_, size_t v_i_2152_, size_t v_stop_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_){
_start:
{
uint8_t v___x_2159_; 
v___x_2159_ = lean_usize_dec_eq(v_i_2152_, v_stop_2153_);
if (v___x_2159_ == 0)
{
uint8_t v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; 
v___x_2160_ = 1;
v___x_2161_ = lean_array_uget_borrowed(v_as_2151_, v_i_2152_);
lean_inc(v___x_2161_);
lean_inc(v___x_2149_);
lean_inc_ref(v___x_2148_);
v___x_2162_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4(v___x_2147_, v___x_2148_, v___x_2149_, v_ctx_2150_, v___x_2161_, v___y_2154_, v___y_2155_, v___y_2156_, v___y_2157_);
if (lean_obj_tag(v___x_2162_) == 0)
{
lean_object* v_a_2163_; lean_object* v___x_2165_; uint8_t v_isShared_2166_; uint8_t v_isSharedCheck_2175_; 
v_a_2163_ = lean_ctor_get(v___x_2162_, 0);
v_isSharedCheck_2175_ = !lean_is_exclusive(v___x_2162_);
if (v_isSharedCheck_2175_ == 0)
{
v___x_2165_ = v___x_2162_;
v_isShared_2166_ = v_isSharedCheck_2175_;
goto v_resetjp_2164_;
}
else
{
lean_inc(v_a_2163_);
lean_dec(v___x_2162_);
v___x_2165_ = lean_box(0);
v_isShared_2166_ = v_isSharedCheck_2175_;
goto v_resetjp_2164_;
}
v_resetjp_2164_:
{
uint8_t v___x_2167_; 
v___x_2167_ = lean_unbox(v_a_2163_);
lean_dec(v_a_2163_);
if (v___x_2167_ == 0)
{
size_t v___x_2168_; size_t v___x_2169_; 
lean_del_object(v___x_2165_);
v___x_2168_ = ((size_t)1ULL);
v___x_2169_ = lean_usize_add(v_i_2152_, v___x_2168_);
v_i_2152_ = v___x_2169_;
goto _start;
}
else
{
lean_object* v___x_2171_; lean_object* v___x_2173_; 
lean_dec(v___x_2149_);
lean_dec_ref(v___x_2148_);
v___x_2171_ = lean_box(v___x_2160_);
if (v_isShared_2166_ == 0)
{
lean_ctor_set(v___x_2165_, 0, v___x_2171_);
v___x_2173_ = v___x_2165_;
goto v_reusejp_2172_;
}
else
{
lean_object* v_reuseFailAlloc_2174_; 
v_reuseFailAlloc_2174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2174_, 0, v___x_2171_);
v___x_2173_ = v_reuseFailAlloc_2174_;
goto v_reusejp_2172_;
}
v_reusejp_2172_:
{
return v___x_2173_;
}
}
}
}
else
{
lean_dec(v___x_2149_);
lean_dec_ref(v___x_2148_);
return v___x_2162_;
}
}
else
{
uint8_t v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; 
lean_dec(v___x_2149_);
lean_dec_ref(v___x_2148_);
v___x_2176_ = 0;
v___x_2177_ = lean_box(v___x_2176_);
v___x_2178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2178_, 0, v___x_2177_);
return v___x_2178_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4_spec__5___boxed(lean_object* v___x_2179_, lean_object* v___x_2180_, lean_object* v___x_2181_, lean_object* v_ctx_2182_, lean_object* v_as_2183_, lean_object* v_i_2184_, lean_object* v_stop_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_){
_start:
{
uint8_t v___x_7980__boxed_2191_; size_t v_i_boxed_2192_; size_t v_stop_boxed_2193_; lean_object* v_res_2194_; 
v___x_7980__boxed_2191_ = lean_unbox(v___x_2179_);
v_i_boxed_2192_ = lean_unbox_usize(v_i_2184_);
lean_dec(v_i_2184_);
v_stop_boxed_2193_ = lean_unbox_usize(v_stop_2185_);
lean_dec(v_stop_2185_);
v_res_2194_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4_spec__5(v___x_7980__boxed_2191_, v___x_2180_, v___x_2181_, v_ctx_2182_, v_as_2183_, v_i_boxed_2192_, v_stop_boxed_2193_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_);
lean_dec(v___y_2189_);
lean_dec_ref(v___y_2188_);
lean_dec(v___y_2187_);
lean_dec_ref(v___y_2186_);
lean_dec_ref(v_as_2183_);
lean_dec_ref(v_ctx_2182_);
return v_res_2194_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4___boxed(lean_object* v___x_2195_, lean_object* v___x_2196_, lean_object* v___x_2197_, lean_object* v_ctx_2198_, lean_object* v_x_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_){
_start:
{
uint8_t v___x_8000__boxed_2205_; lean_object* v_res_2206_; 
v___x_8000__boxed_2205_ = lean_unbox(v___x_2195_);
v_res_2206_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4(v___x_8000__boxed_2205_, v___x_2196_, v___x_2197_, v_ctx_2198_, v_x_2199_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_);
lean_dec(v___y_2203_);
lean_dec_ref(v___y_2202_);
lean_dec(v___y_2201_);
lean_dec_ref(v___y_2200_);
lean_dec_ref(v_ctx_2198_);
return v_res_2206_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4(uint8_t v___x_2207_, lean_object* v___x_2208_, lean_object* v___x_2209_, lean_object* v_ctx_2210_, lean_object* v_t_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_){
_start:
{
lean_object* v_root_2217_; lean_object* v_tail_2218_; lean_object* v___x_2219_; 
v_root_2217_ = lean_ctor_get(v_t_2211_, 0);
lean_inc_ref(v_root_2217_);
v_tail_2218_ = lean_ctor_get(v_t_2211_, 1);
lean_inc_ref(v_tail_2218_);
lean_dec_ref(v_t_2211_);
lean_inc(v___x_2209_);
lean_inc_ref(v___x_2208_);
v___x_2219_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__4(v___x_2207_, v___x_2208_, v___x_2209_, v_ctx_2210_, v_root_2217_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_);
if (lean_obj_tag(v___x_2219_) == 0)
{
lean_object* v_a_2220_; uint8_t v___x_2221_; 
v_a_2220_ = lean_ctor_get(v___x_2219_, 0);
v___x_2221_ = lean_unbox(v_a_2220_);
if (v___x_2221_ == 0)
{
lean_object* v___x_2223_; uint8_t v_isShared_2224_; uint8_t v_isSharedCheck_2235_; 
v_isSharedCheck_2235_ = !lean_is_exclusive(v___x_2219_);
if (v_isSharedCheck_2235_ == 0)
{
lean_object* v_unused_2236_; 
v_unused_2236_ = lean_ctor_get(v___x_2219_, 0);
lean_dec(v_unused_2236_);
v___x_2223_ = v___x_2219_;
v_isShared_2224_ = v_isSharedCheck_2235_;
goto v_resetjp_2222_;
}
else
{
lean_dec(v___x_2219_);
v___x_2223_ = lean_box(0);
v_isShared_2224_ = v_isSharedCheck_2235_;
goto v_resetjp_2222_;
}
v_resetjp_2222_:
{
lean_object* v___x_2225_; lean_object* v___x_2226_; uint8_t v___x_2227_; 
v___x_2225_ = lean_unsigned_to_nat(0u);
v___x_2226_ = lean_array_get_size(v_tail_2218_);
v___x_2227_ = lean_nat_dec_lt(v___x_2225_, v___x_2226_);
if (v___x_2227_ == 0)
{
lean_object* v___x_2228_; lean_object* v___x_2230_; 
lean_dec_ref(v_tail_2218_);
lean_dec(v___x_2209_);
lean_dec_ref(v___x_2208_);
v___x_2228_ = lean_box(v___x_2227_);
if (v_isShared_2224_ == 0)
{
lean_ctor_set(v___x_2223_, 0, v___x_2228_);
v___x_2230_ = v___x_2223_;
goto v_reusejp_2229_;
}
else
{
lean_object* v_reuseFailAlloc_2231_; 
v_reuseFailAlloc_2231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2231_, 0, v___x_2228_);
v___x_2230_ = v_reuseFailAlloc_2231_;
goto v_reusejp_2229_;
}
v_reusejp_2229_:
{
return v___x_2230_;
}
}
else
{
size_t v___x_2232_; size_t v___x_2233_; lean_object* v___x_2234_; 
lean_del_object(v___x_2223_);
v___x_2232_ = ((size_t)0ULL);
v___x_2233_ = lean_usize_of_nat(v___x_2226_);
v___x_2234_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg(v___x_2207_, v___x_2208_, v___x_2209_, v_ctx_2210_, v_tail_2218_, v___x_2232_, v___x_2233_, v___y_2213_);
lean_dec_ref(v_tail_2218_);
return v___x_2234_;
}
}
}
else
{
lean_dec_ref(v_tail_2218_);
lean_dec(v___x_2209_);
lean_dec_ref(v___x_2208_);
return v___x_2219_;
}
}
else
{
lean_dec_ref(v_tail_2218_);
lean_dec(v___x_2209_);
lean_dec_ref(v___x_2208_);
return v___x_2219_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4___boxed(lean_object* v___x_2237_, lean_object* v___x_2238_, lean_object* v___x_2239_, lean_object* v_ctx_2240_, lean_object* v_t_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_){
_start:
{
uint8_t v___x_8132__boxed_2247_; lean_object* v_res_2248_; 
v___x_8132__boxed_2247_ = lean_unbox(v___x_2237_);
v_res_2248_ = l_Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4(v___x_8132__boxed_2247_, v___x_2238_, v___x_2239_, v_ctx_2240_, v_t_2241_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_);
lean_dec(v___y_2245_);
lean_dec_ref(v___y_2244_);
lean_dec(v___y_2243_);
lean_dec_ref(v___y_2242_);
lean_dec_ref(v_ctx_2240_);
return v_res_2248_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices(lean_object* v_ctx_2249_, lean_object* v_a_2250_, lean_object* v_a_2251_, lean_object* v_a_2252_, lean_object* v_a_2253_){
_start:
{
lean_object* v_majorTypeIndices_2255_; lean_object* v___x_2256_; uint8_t v___y_2258_; lean_object* v___x_2280_; uint8_t v___x_2281_; 
v_majorTypeIndices_2255_ = lean_ctor_get(v_ctx_2249_, 5);
lean_inc_ref(v_majorTypeIndices_2255_);
v___x_2256_ = lean_array_get_size(v_majorTypeIndices_2255_);
v___x_2280_ = lean_unsigned_to_nat(0u);
v___x_2281_ = lean_nat_dec_eq(v___x_2256_, v___x_2280_);
if (v___x_2281_ == 0)
{
uint8_t v___x_2282_; 
v___x_2282_ = lean_nat_dec_lt(v___x_2280_, v___x_2256_);
if (v___x_2282_ == 0)
{
v___y_2258_ = v___x_2282_;
goto v___jp_2257_;
}
else
{
if (v___x_2282_ == 0)
{
v___y_2258_ = v___x_2282_;
goto v___jp_2257_;
}
else
{
size_t v___x_2283_; size_t v___x_2284_; uint8_t v___x_2285_; 
v___x_2283_ = ((size_t)0ULL);
v___x_2284_ = lean_usize_of_nat(v___x_2256_);
v___x_2285_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__5(v___x_2256_, v_majorTypeIndices_2255_, v___x_2283_, v___x_2284_);
if (v___x_2285_ == 0)
{
v___y_2258_ = v___x_2285_;
goto v___jp_2257_;
}
else
{
lean_object* v___x_2286_; lean_object* v___x_2287_; 
lean_dec_ref(v_majorTypeIndices_2255_);
lean_dec_ref(v_ctx_2249_);
v___x_2286_ = lean_box(v___x_2281_);
v___x_2287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2287_, 0, v___x_2286_);
return v___x_2287_;
}
}
}
}
else
{
lean_object* v___x_2288_; lean_object* v___x_2289_; 
lean_dec_ref(v_majorTypeIndices_2255_);
lean_dec_ref(v_ctx_2249_);
v___x_2288_ = lean_box(v___x_2281_);
v___x_2289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2289_, 0, v___x_2288_);
return v___x_2289_;
}
v___jp_2257_:
{
uint8_t v___x_2259_; 
v___x_2259_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1___redArg(v_majorTypeIndices_2255_, v___x_2256_, v___x_2256_);
if (v___x_2259_ == 0)
{
lean_object* v_lctx_2260_; lean_object* v_decls_2261_; lean_object* v___x_2262_; 
v_lctx_2260_ = lean_ctor_get(v_a_2250_, 2);
v_decls_2261_ = lean_ctor_get(v_lctx_2260_, 1);
lean_inc_ref(v_decls_2261_);
v___x_2262_ = l_Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4(v___x_2259_, v_majorTypeIndices_2255_, v___x_2256_, v_ctx_2249_, v_decls_2261_, v_a_2250_, v_a_2251_, v_a_2252_, v_a_2253_);
lean_dec_ref(v_ctx_2249_);
if (lean_obj_tag(v___x_2262_) == 0)
{
lean_object* v_a_2263_; lean_object* v___x_2265_; uint8_t v_isShared_2266_; uint8_t v_isSharedCheck_2277_; 
v_a_2263_ = lean_ctor_get(v___x_2262_, 0);
v_isSharedCheck_2277_ = !lean_is_exclusive(v___x_2262_);
if (v_isSharedCheck_2277_ == 0)
{
v___x_2265_ = v___x_2262_;
v_isShared_2266_ = v_isSharedCheck_2277_;
goto v_resetjp_2264_;
}
else
{
lean_inc(v_a_2263_);
lean_dec(v___x_2262_);
v___x_2265_ = lean_box(0);
v_isShared_2266_ = v_isSharedCheck_2277_;
goto v_resetjp_2264_;
}
v_resetjp_2264_:
{
uint8_t v___x_2267_; 
v___x_2267_ = lean_unbox(v_a_2263_);
lean_dec(v_a_2263_);
if (v___x_2267_ == 0)
{
uint8_t v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2271_; 
v___x_2268_ = 1;
v___x_2269_ = lean_box(v___x_2268_);
if (v_isShared_2266_ == 0)
{
lean_ctor_set(v___x_2265_, 0, v___x_2269_);
v___x_2271_ = v___x_2265_;
goto v_reusejp_2270_;
}
else
{
lean_object* v_reuseFailAlloc_2272_; 
v_reuseFailAlloc_2272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2272_, 0, v___x_2269_);
v___x_2271_ = v_reuseFailAlloc_2272_;
goto v_reusejp_2270_;
}
v_reusejp_2270_:
{
return v___x_2271_;
}
}
else
{
lean_object* v___x_2273_; lean_object* v___x_2275_; 
v___x_2273_ = lean_box(v___x_2259_);
if (v_isShared_2266_ == 0)
{
lean_ctor_set(v___x_2265_, 0, v___x_2273_);
v___x_2275_ = v___x_2265_;
goto v_reusejp_2274_;
}
else
{
lean_object* v_reuseFailAlloc_2276_; 
v_reuseFailAlloc_2276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2276_, 0, v___x_2273_);
v___x_2275_ = v_reuseFailAlloc_2276_;
goto v_reusejp_2274_;
}
v_reusejp_2274_:
{
return v___x_2275_;
}
}
}
}
else
{
return v___x_2262_;
}
}
else
{
lean_object* v___x_2278_; lean_object* v___x_2279_; 
lean_dec_ref(v_majorTypeIndices_2255_);
lean_dec_ref(v_ctx_2249_);
v___x_2278_ = lean_box(v___y_2258_);
v___x_2279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2279_, 0, v___x_2278_);
return v___x_2279_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___boxed(lean_object* v_ctx_2290_, lean_object* v_a_2291_, lean_object* v_a_2292_, lean_object* v_a_2293_, lean_object* v_a_2294_, lean_object* v_a_2295_){
_start:
{
lean_object* v_res_2296_; 
v_res_2296_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices(v_ctx_2290_, v_a_2291_, v_a_2292_, v_a_2293_, v_a_2294_);
lean_dec(v_a_2294_);
lean_dec_ref(v_a_2293_);
lean_dec(v_a_2292_);
lean_dec_ref(v_a_2291_);
return v_res_2296_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0(lean_object* v___x_2297_, lean_object* v_i_2298_, lean_object* v_n_2299_, lean_object* v_i_2300_, lean_object* v_a_2301_){
_start:
{
uint8_t v___x_2302_; 
v___x_2302_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0___redArg(v___x_2297_, v_i_2298_, v_n_2299_, v_i_2300_);
return v___x_2302_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0___boxed(lean_object* v___x_2303_, lean_object* v_i_2304_, lean_object* v_n_2305_, lean_object* v_i_2306_, lean_object* v_a_2307_){
_start:
{
uint8_t v_res_2308_; lean_object* v_r_2309_; 
v_res_2308_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__0(v___x_2303_, v_i_2304_, v_n_2305_, v_i_2306_, v_a_2307_);
lean_dec(v_n_2305_);
lean_dec(v_i_2304_);
lean_dec_ref(v___x_2303_);
v_r_2309_ = lean_box(v_res_2308_);
return v_r_2309_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1(lean_object* v___x_2310_, lean_object* v_n_2311_, lean_object* v_i_2312_, lean_object* v_a_2313_){
_start:
{
uint8_t v___x_2314_; 
v___x_2314_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1___redArg(v___x_2310_, v_n_2311_, v_i_2312_);
return v___x_2314_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1___boxed(lean_object* v___x_2315_, lean_object* v_n_2316_, lean_object* v_i_2317_, lean_object* v_a_2318_){
_start:
{
uint8_t v_res_2319_; lean_object* v_r_2320_; 
v_res_2319_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__1(v___x_2315_, v_n_2316_, v_i_2317_, v_a_2318_);
lean_dec(v_n_2316_);
lean_dec_ref(v___x_2315_);
v_r_2320_ = lean_box(v_res_2319_);
return v_r_2320_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5(uint8_t v___x_2321_, lean_object* v___x_2322_, lean_object* v___x_2323_, lean_object* v_ctx_2324_, lean_object* v_as_2325_, size_t v_i_2326_, size_t v_stop_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_){
_start:
{
lean_object* v___x_2333_; 
v___x_2333_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___redArg(v___x_2321_, v___x_2322_, v___x_2323_, v_ctx_2324_, v_as_2325_, v_i_2326_, v_stop_2327_, v___y_2329_);
return v___x_2333_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5___boxed(lean_object* v___x_2334_, lean_object* v___x_2335_, lean_object* v___x_2336_, lean_object* v_ctx_2337_, lean_object* v_as_2338_, lean_object* v_i_2339_, lean_object* v_stop_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_){
_start:
{
uint8_t v___x_8277__boxed_2346_; size_t v_i_boxed_2347_; size_t v_stop_boxed_2348_; lean_object* v_res_2349_; 
v___x_8277__boxed_2346_ = lean_unbox(v___x_2334_);
v_i_boxed_2347_ = lean_unbox_usize(v_i_2339_);
lean_dec(v_i_2339_);
v_stop_boxed_2348_ = lean_unbox_usize(v_stop_2340_);
lean_dec(v_stop_2340_);
v_res_2349_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices_spec__4_spec__5(v___x_8277__boxed_2346_, v___x_2335_, v___x_2336_, v_ctx_2337_, v_as_2338_, v_i_boxed_2347_, v_stop_boxed_2348_, v___y_2341_, v___y_2342_, v___y_2343_, v___y_2344_);
lean_dec(v___y_2344_);
lean_dec_ref(v___y_2343_);
lean_dec(v___y_2342_);
lean_dec_ref(v___y_2341_);
lean_dec_ref(v_as_2338_);
lean_dec_ref(v_ctx_2337_);
return v_res_2349_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__0(lean_object* v_as_2350_, size_t v_i_2351_, size_t v_stop_2352_, lean_object* v_b_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_){
_start:
{
lean_object* v_a_2360_; uint8_t v___x_2364_; 
v___x_2364_ = lean_usize_dec_eq(v_i_2351_, v_stop_2352_);
if (v___x_2364_ == 0)
{
lean_object* v_toInductionSubgoal_2365_; lean_object* v_ctorName_2366_; lean_object* v_mvarId_2367_; lean_object* v_fields_2368_; lean_object* v_subst_2369_; lean_object* v___x_2371_; uint8_t v_isShared_2372_; uint8_t v_isSharedCheck_2420_; 
v_toInductionSubgoal_2365_ = lean_ctor_get(v_b_2353_, 0);
lean_inc_ref(v_toInductionSubgoal_2365_);
v_ctorName_2366_ = lean_ctor_get(v_b_2353_, 1);
v_mvarId_2367_ = lean_ctor_get(v_toInductionSubgoal_2365_, 0);
v_fields_2368_ = lean_ctor_get(v_toInductionSubgoal_2365_, 1);
v_subst_2369_ = lean_ctor_get(v_toInductionSubgoal_2365_, 2);
v_isSharedCheck_2420_ = !lean_is_exclusive(v_toInductionSubgoal_2365_);
if (v_isSharedCheck_2420_ == 0)
{
v___x_2371_ = v_toInductionSubgoal_2365_;
v_isShared_2372_ = v_isSharedCheck_2420_;
goto v_resetjp_2370_;
}
else
{
lean_inc(v_subst_2369_);
lean_inc(v_fields_2368_);
lean_inc(v_mvarId_2367_);
lean_dec(v_toInductionSubgoal_2365_);
v___x_2371_ = lean_box(0);
v_isShared_2372_ = v_isSharedCheck_2420_;
goto v_resetjp_2370_;
}
v_resetjp_2370_:
{
lean_object* v___x_2373_; lean_object* v___x_2374_; 
v___x_2373_ = lean_array_uget_borrowed(v_as_2350_, v_i_2351_);
lean_inc(v___x_2373_);
v___x_2374_ = l_Lean_Meta_FVarSubst_get(v_subst_2369_, v___x_2373_);
if (lean_obj_tag(v___x_2374_) == 1)
{
lean_object* v_fvarId_2375_; lean_object* v___x_2376_; 
v_fvarId_2375_ = lean_ctor_get(v___x_2374_, 0);
lean_inc(v_fvarId_2375_);
lean_dec_ref_known(v___x_2374_, 1);
v___x_2376_ = l_Lean_Meta_saveState___redArg(v___y_2355_, v___y_2357_);
if (lean_obj_tag(v___x_2376_) == 0)
{
lean_object* v_a_2377_; lean_object* v___x_2378_; 
v_a_2377_ = lean_ctor_get(v___x_2376_, 0);
lean_inc(v_a_2377_);
lean_dec_ref_known(v___x_2376_, 1);
v___x_2378_ = l_Lean_MVarId_clear(v_mvarId_2367_, v_fvarId_2375_, v___y_2354_, v___y_2355_, v___y_2356_, v___y_2357_);
if (lean_obj_tag(v___x_2378_) == 0)
{
lean_object* v___x_2380_; uint8_t v_isShared_2381_; uint8_t v_isSharedCheck_2390_; 
lean_inc(v_ctorName_2366_);
lean_dec(v_a_2377_);
v_isSharedCheck_2390_ = !lean_is_exclusive(v_b_2353_);
if (v_isSharedCheck_2390_ == 0)
{
lean_object* v_unused_2391_; lean_object* v_unused_2392_; 
v_unused_2391_ = lean_ctor_get(v_b_2353_, 1);
lean_dec(v_unused_2391_);
v_unused_2392_ = lean_ctor_get(v_b_2353_, 0);
lean_dec(v_unused_2392_);
v___x_2380_ = v_b_2353_;
v_isShared_2381_ = v_isSharedCheck_2390_;
goto v_resetjp_2379_;
}
else
{
lean_dec(v_b_2353_);
v___x_2380_ = lean_box(0);
v_isShared_2381_ = v_isSharedCheck_2390_;
goto v_resetjp_2379_;
}
v_resetjp_2379_:
{
lean_object* v_a_2382_; lean_object* v___x_2383_; lean_object* v___x_2385_; 
v_a_2382_ = lean_ctor_get(v___x_2378_, 0);
lean_inc(v_a_2382_);
lean_dec_ref_known(v___x_2378_, 1);
v___x_2383_ = l_Lean_Meta_FVarSubst_erase(v_subst_2369_, v___x_2373_);
if (v_isShared_2372_ == 0)
{
lean_ctor_set(v___x_2371_, 2, v___x_2383_);
lean_ctor_set(v___x_2371_, 0, v_a_2382_);
v___x_2385_ = v___x_2371_;
goto v_reusejp_2384_;
}
else
{
lean_object* v_reuseFailAlloc_2389_; 
v_reuseFailAlloc_2389_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2389_, 0, v_a_2382_);
lean_ctor_set(v_reuseFailAlloc_2389_, 1, v_fields_2368_);
lean_ctor_set(v_reuseFailAlloc_2389_, 2, v___x_2383_);
v___x_2385_ = v_reuseFailAlloc_2389_;
goto v_reusejp_2384_;
}
v_reusejp_2384_:
{
lean_object* v___x_2387_; 
if (v_isShared_2381_ == 0)
{
lean_ctor_set(v___x_2380_, 0, v___x_2385_);
v___x_2387_ = v___x_2380_;
goto v_reusejp_2386_;
}
else
{
lean_object* v_reuseFailAlloc_2388_; 
v_reuseFailAlloc_2388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2388_, 0, v___x_2385_);
lean_ctor_set(v_reuseFailAlloc_2388_, 1, v_ctorName_2366_);
v___x_2387_ = v_reuseFailAlloc_2388_;
goto v_reusejp_2386_;
}
v_reusejp_2386_:
{
v_a_2360_ = v___x_2387_;
goto v___jp_2359_;
}
}
}
}
else
{
lean_object* v_a_2393_; lean_object* v___x_2395_; uint8_t v_isShared_2396_; uint8_t v_isSharedCheck_2411_; 
lean_del_object(v___x_2371_);
lean_dec(v_subst_2369_);
lean_dec_ref(v_fields_2368_);
v_a_2393_ = lean_ctor_get(v___x_2378_, 0);
v_isSharedCheck_2411_ = !lean_is_exclusive(v___x_2378_);
if (v_isSharedCheck_2411_ == 0)
{
v___x_2395_ = v___x_2378_;
v_isShared_2396_ = v_isSharedCheck_2411_;
goto v_resetjp_2394_;
}
else
{
lean_inc(v_a_2393_);
lean_dec(v___x_2378_);
v___x_2395_ = lean_box(0);
v_isShared_2396_ = v_isSharedCheck_2411_;
goto v_resetjp_2394_;
}
v_resetjp_2394_:
{
lean_object* v___x_2398_; 
lean_inc(v_a_2393_);
if (v_isShared_2396_ == 0)
{
v___x_2398_ = v___x_2395_;
goto v_reusejp_2397_;
}
else
{
lean_object* v_reuseFailAlloc_2410_; 
v_reuseFailAlloc_2410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2410_, 0, v_a_2393_);
v___x_2398_ = v_reuseFailAlloc_2410_;
goto v_reusejp_2397_;
}
v_reusejp_2397_:
{
uint8_t v___x_2399_; 
v___x_2399_ = l_Lean_Exception_isInterrupt(v_a_2393_);
if (v___x_2399_ == 0)
{
uint8_t v___x_2400_; 
v___x_2400_ = l_Lean_Exception_isRuntime(v_a_2393_);
if (v___x_2400_ == 0)
{
lean_object* v___x_2401_; 
lean_dec_ref(v___x_2398_);
v___x_2401_ = l_Lean_Meta_SavedState_restore___redArg(v_a_2377_, v___y_2355_, v___y_2357_);
if (lean_obj_tag(v___x_2401_) == 0)
{
lean_dec_ref_known(v___x_2401_, 1);
v_a_2360_ = v_b_2353_;
goto v___jp_2359_;
}
else
{
lean_object* v_a_2402_; lean_object* v___x_2404_; uint8_t v_isShared_2405_; uint8_t v_isSharedCheck_2409_; 
lean_dec_ref(v_b_2353_);
v_a_2402_ = lean_ctor_get(v___x_2401_, 0);
v_isSharedCheck_2409_ = !lean_is_exclusive(v___x_2401_);
if (v_isSharedCheck_2409_ == 0)
{
v___x_2404_ = v___x_2401_;
v_isShared_2405_ = v_isSharedCheck_2409_;
goto v_resetjp_2403_;
}
else
{
lean_inc(v_a_2402_);
lean_dec(v___x_2401_);
v___x_2404_ = lean_box(0);
v_isShared_2405_ = v_isSharedCheck_2409_;
goto v_resetjp_2403_;
}
v_resetjp_2403_:
{
lean_object* v___x_2407_; 
if (v_isShared_2405_ == 0)
{
v___x_2407_ = v___x_2404_;
goto v_reusejp_2406_;
}
else
{
lean_object* v_reuseFailAlloc_2408_; 
v_reuseFailAlloc_2408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2408_, 0, v_a_2402_);
v___x_2407_ = v_reuseFailAlloc_2408_;
goto v_reusejp_2406_;
}
v_reusejp_2406_:
{
return v___x_2407_;
}
}
}
}
else
{
lean_dec(v_a_2377_);
lean_dec_ref(v_b_2353_);
return v___x_2398_;
}
}
else
{
lean_dec(v_a_2393_);
lean_dec(v_a_2377_);
lean_dec_ref(v_b_2353_);
return v___x_2398_;
}
}
}
}
}
else
{
lean_object* v_a_2412_; lean_object* v___x_2414_; uint8_t v_isShared_2415_; uint8_t v_isSharedCheck_2419_; 
lean_dec(v_fvarId_2375_);
lean_del_object(v___x_2371_);
lean_dec(v_subst_2369_);
lean_dec_ref(v_fields_2368_);
lean_dec(v_mvarId_2367_);
lean_dec_ref(v_b_2353_);
v_a_2412_ = lean_ctor_get(v___x_2376_, 0);
v_isSharedCheck_2419_ = !lean_is_exclusive(v___x_2376_);
if (v_isSharedCheck_2419_ == 0)
{
v___x_2414_ = v___x_2376_;
v_isShared_2415_ = v_isSharedCheck_2419_;
goto v_resetjp_2413_;
}
else
{
lean_inc(v_a_2412_);
lean_dec(v___x_2376_);
v___x_2414_ = lean_box(0);
v_isShared_2415_ = v_isSharedCheck_2419_;
goto v_resetjp_2413_;
}
v_resetjp_2413_:
{
lean_object* v___x_2417_; 
if (v_isShared_2415_ == 0)
{
v___x_2417_ = v___x_2414_;
goto v_reusejp_2416_;
}
else
{
lean_object* v_reuseFailAlloc_2418_; 
v_reuseFailAlloc_2418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2418_, 0, v_a_2412_);
v___x_2417_ = v_reuseFailAlloc_2418_;
goto v_reusejp_2416_;
}
v_reusejp_2416_:
{
return v___x_2417_;
}
}
}
}
else
{
lean_dec_ref(v___x_2374_);
lean_del_object(v___x_2371_);
lean_dec(v_subst_2369_);
lean_dec_ref(v_fields_2368_);
lean_dec(v_mvarId_2367_);
v_a_2360_ = v_b_2353_;
goto v___jp_2359_;
}
}
}
else
{
lean_object* v___x_2421_; 
v___x_2421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2421_, 0, v_b_2353_);
return v___x_2421_;
}
v___jp_2359_:
{
size_t v___x_2361_; size_t v___x_2362_; 
v___x_2361_ = ((size_t)1ULL);
v___x_2362_ = lean_usize_add(v_i_2351_, v___x_2361_);
v_i_2351_ = v___x_2362_;
v_b_2353_ = v_a_2360_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__0___boxed(lean_object* v_as_2422_, lean_object* v_i_2423_, lean_object* v_stop_2424_, lean_object* v_b_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_){
_start:
{
size_t v_i_boxed_2431_; size_t v_stop_boxed_2432_; lean_object* v_res_2433_; 
v_i_boxed_2431_ = lean_unbox_usize(v_i_2423_);
lean_dec(v_i_2423_);
v_stop_boxed_2432_ = lean_unbox_usize(v_stop_2424_);
lean_dec(v_stop_2424_);
v_res_2433_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__0(v_as_2422_, v_i_boxed_2431_, v_stop_boxed_2432_, v_b_2425_, v___y_2426_, v___y_2427_, v___y_2428_, v___y_2429_);
lean_dec(v___y_2429_);
lean_dec_ref(v___y_2428_);
lean_dec(v___y_2427_);
lean_dec_ref(v___y_2426_);
lean_dec_ref(v_as_2422_);
return v_res_2433_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__1(lean_object* v_indicesFVarIds_2434_, size_t v_sz_2435_, size_t v_i_2436_, lean_object* v_bs_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_){
_start:
{
uint8_t v___x_2443_; 
v___x_2443_ = lean_usize_dec_lt(v_i_2436_, v_sz_2435_);
if (v___x_2443_ == 0)
{
lean_object* v___x_2444_; 
v___x_2444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2444_, 0, v_bs_2437_);
return v___x_2444_;
}
else
{
lean_object* v_v_2445_; lean_object* v___x_2446_; lean_object* v_bs_x27_2447_; lean_object* v_a_2449_; lean_object* v___x_2454_; uint8_t v___x_2455_; 
v_v_2445_ = lean_array_uget(v_bs_2437_, v_i_2436_);
v___x_2446_ = lean_unsigned_to_nat(0u);
v_bs_x27_2447_ = lean_array_uset(v_bs_2437_, v_i_2436_, v___x_2446_);
v___x_2454_ = lean_array_get_size(v_indicesFVarIds_2434_);
v___x_2455_ = lean_nat_dec_lt(v___x_2446_, v___x_2454_);
if (v___x_2455_ == 0)
{
v_a_2449_ = v_v_2445_;
goto v___jp_2448_;
}
else
{
size_t v___x_2456_; size_t v___x_2457_; lean_object* v___x_2458_; 
v___x_2456_ = ((size_t)0ULL);
v___x_2457_ = lean_usize_of_nat(v___x_2454_);
v___x_2458_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__0(v_indicesFVarIds_2434_, v___x_2456_, v___x_2457_, v_v_2445_, v___y_2438_, v___y_2439_, v___y_2440_, v___y_2441_);
if (lean_obj_tag(v___x_2458_) == 0)
{
lean_object* v_a_2459_; 
v_a_2459_ = lean_ctor_get(v___x_2458_, 0);
lean_inc(v_a_2459_);
lean_dec_ref_known(v___x_2458_, 1);
v_a_2449_ = v_a_2459_;
goto v___jp_2448_;
}
else
{
lean_object* v_a_2460_; lean_object* v___x_2462_; uint8_t v_isShared_2463_; uint8_t v_isSharedCheck_2467_; 
lean_dec_ref(v_bs_x27_2447_);
v_a_2460_ = lean_ctor_get(v___x_2458_, 0);
v_isSharedCheck_2467_ = !lean_is_exclusive(v___x_2458_);
if (v_isSharedCheck_2467_ == 0)
{
v___x_2462_ = v___x_2458_;
v_isShared_2463_ = v_isSharedCheck_2467_;
goto v_resetjp_2461_;
}
else
{
lean_inc(v_a_2460_);
lean_dec(v___x_2458_);
v___x_2462_ = lean_box(0);
v_isShared_2463_ = v_isSharedCheck_2467_;
goto v_resetjp_2461_;
}
v_resetjp_2461_:
{
lean_object* v___x_2465_; 
if (v_isShared_2463_ == 0)
{
v___x_2465_ = v___x_2462_;
goto v_reusejp_2464_;
}
else
{
lean_object* v_reuseFailAlloc_2466_; 
v_reuseFailAlloc_2466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2466_, 0, v_a_2460_);
v___x_2465_ = v_reuseFailAlloc_2466_;
goto v_reusejp_2464_;
}
v_reusejp_2464_:
{
return v___x_2465_;
}
}
}
}
v___jp_2448_:
{
size_t v___x_2450_; size_t v___x_2451_; lean_object* v___x_2452_; 
v___x_2450_ = ((size_t)1ULL);
v___x_2451_ = lean_usize_add(v_i_2436_, v___x_2450_);
v___x_2452_ = lean_array_uset(v_bs_x27_2447_, v_i_2436_, v_a_2449_);
v_i_2436_ = v___x_2451_;
v_bs_2437_ = v___x_2452_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__1___boxed(lean_object* v_indicesFVarIds_2468_, lean_object* v_sz_2469_, lean_object* v_i_2470_, lean_object* v_bs_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_){
_start:
{
size_t v_sz_boxed_2477_; size_t v_i_boxed_2478_; lean_object* v_res_2479_; 
v_sz_boxed_2477_ = lean_unbox_usize(v_sz_2469_);
lean_dec(v_sz_2469_);
v_i_boxed_2478_ = lean_unbox_usize(v_i_2470_);
lean_dec(v_i_2470_);
v_res_2479_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__1(v_indicesFVarIds_2468_, v_sz_boxed_2477_, v_i_boxed_2478_, v_bs_2471_, v___y_2472_, v___y_2473_, v___y_2474_, v___y_2475_);
lean_dec(v___y_2475_);
lean_dec_ref(v___y_2474_);
lean_dec(v___y_2473_);
lean_dec_ref(v___y_2472_);
lean_dec_ref(v_indicesFVarIds_2468_);
return v_res_2479_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices(lean_object* v_s_u2081_2480_, lean_object* v_s_u2082_2481_, lean_object* v_a_2482_, lean_object* v_a_2483_, lean_object* v_a_2484_, lean_object* v_a_2485_){
_start:
{
lean_object* v_indicesFVarIds_2487_; size_t v_sz_2488_; size_t v___x_2489_; lean_object* v___x_2490_; 
v_indicesFVarIds_2487_ = lean_ctor_get(v_s_u2081_2480_, 1);
v_sz_2488_ = lean_array_size(v_s_u2082_2481_);
v___x_2489_ = ((size_t)0ULL);
v___x_2490_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_spec__1(v_indicesFVarIds_2487_, v_sz_2488_, v___x_2489_, v_s_u2082_2481_, v_a_2482_, v_a_2483_, v_a_2484_, v_a_2485_);
return v___x_2490_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices___boxed(lean_object* v_s_u2081_2491_, lean_object* v_s_u2082_2492_, lean_object* v_a_2493_, lean_object* v_a_2494_, lean_object* v_a_2495_, lean_object* v_a_2496_, lean_object* v_a_2497_){
_start:
{
lean_object* v_res_2498_; 
v_res_2498_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices(v_s_u2081_2491_, v_s_u2082_2492_, v_a_2493_, v_a_2494_, v_a_2495_, v_a_2496_);
lean_dec(v_a_2496_);
lean_dec_ref(v_a_2495_);
lean_dec(v_a_2494_);
lean_dec_ref(v_a_2493_);
lean_dec_ref(v_s_u2081_2491_);
return v_res_2498_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0___redArg(lean_object* v_ctorNames_2499_, lean_object* v_us_2500_, lean_object* v_params_2501_, lean_object* v_majorFVarId_2502_, size_t v_sz_2503_, size_t v_i_2504_, lean_object* v_bs_2505_){
_start:
{
uint8_t v___x_2506_; 
v___x_2506_ = lean_usize_dec_lt(v_i_2504_, v_sz_2503_);
if (v___x_2506_ == 0)
{
lean_dec(v_majorFVarId_2502_);
lean_dec(v_us_2500_);
return v_bs_2505_;
}
else
{
lean_object* v_v_2507_; lean_object* v___x_2508_; lean_object* v_bs_x27_2509_; lean_object* v___y_2511_; lean_object* v___x_2516_; lean_object* v___x_2517_; uint8_t v___x_2518_; 
v_v_2507_ = lean_array_uget(v_bs_2505_, v_i_2504_);
v___x_2508_ = lean_unsigned_to_nat(0u);
v_bs_x27_2509_ = lean_array_uset(v_bs_2505_, v_i_2504_, v___x_2508_);
v___x_2516_ = lean_usize_to_nat(v_i_2504_);
v___x_2517_ = lean_array_get_size(v_ctorNames_2499_);
v___x_2518_ = lean_nat_dec_lt(v___x_2516_, v___x_2517_);
if (v___x_2518_ == 0)
{
lean_object* v___x_2519_; lean_object* v___x_2520_; 
lean_dec(v___x_2516_);
v___x_2519_ = lean_box(0);
v___x_2520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2520_, 0, v_v_2507_);
lean_ctor_set(v___x_2520_, 1, v___x_2519_);
v___y_2511_ = v___x_2520_;
goto v___jp_2510_;
}
else
{
lean_object* v_mvarId_2521_; lean_object* v_fields_2522_; lean_object* v_subst_2523_; lean_object* v___x_2525_; uint8_t v_isShared_2526_; uint8_t v_isSharedCheck_2538_; 
v_mvarId_2521_ = lean_ctor_get(v_v_2507_, 0);
v_fields_2522_ = lean_ctor_get(v_v_2507_, 1);
v_subst_2523_ = lean_ctor_get(v_v_2507_, 2);
v_isSharedCheck_2538_ = !lean_is_exclusive(v_v_2507_);
if (v_isSharedCheck_2538_ == 0)
{
v___x_2525_ = v_v_2507_;
v_isShared_2526_ = v_isSharedCheck_2538_;
goto v_resetjp_2524_;
}
else
{
lean_inc(v_subst_2523_);
lean_inc(v_fields_2522_);
lean_inc(v_mvarId_2521_);
lean_dec(v_v_2507_);
v___x_2525_ = lean_box(0);
v_isShared_2526_ = v_isSharedCheck_2538_;
goto v_resetjp_2524_;
}
v_resetjp_2524_:
{
lean_object* v_ctorName_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v_ctorApp_2530_; lean_object* v___x_2531_; lean_object* v_subst_2532_; lean_object* v___x_2534_; 
v_ctorName_2527_ = lean_array_fget_borrowed(v_ctorNames_2499_, v___x_2516_);
lean_dec(v___x_2516_);
lean_inc(v_us_2500_);
lean_inc(v_ctorName_2527_);
v___x_2528_ = l_Lean_mkConst(v_ctorName_2527_, v_us_2500_);
v___x_2529_ = l_Lean_mkAppN(v___x_2528_, v_params_2501_);
v_ctorApp_2530_ = l_Lean_mkAppN(v___x_2529_, v_fields_2522_);
v___x_2531_ = l_Lean_Meta_FVarSubst_erase(v_subst_2523_, v_majorFVarId_2502_);
lean_inc(v_majorFVarId_2502_);
v_subst_2532_ = l_Lean_Meta_FVarSubst_insert(v___x_2531_, v_majorFVarId_2502_, v_ctorApp_2530_);
if (v_isShared_2526_ == 0)
{
lean_ctor_set(v___x_2525_, 2, v_subst_2532_);
v___x_2534_ = v___x_2525_;
goto v_reusejp_2533_;
}
else
{
lean_object* v_reuseFailAlloc_2537_; 
v_reuseFailAlloc_2537_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2537_, 0, v_mvarId_2521_);
lean_ctor_set(v_reuseFailAlloc_2537_, 1, v_fields_2522_);
lean_ctor_set(v_reuseFailAlloc_2537_, 2, v_subst_2532_);
v___x_2534_ = v_reuseFailAlloc_2537_;
goto v_reusejp_2533_;
}
v_reusejp_2533_:
{
lean_object* v___x_2535_; lean_object* v___x_2536_; 
lean_inc(v_ctorName_2527_);
v___x_2535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2535_, 0, v_ctorName_2527_);
v___x_2536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2536_, 0, v___x_2534_);
lean_ctor_set(v___x_2536_, 1, v___x_2535_);
v___y_2511_ = v___x_2536_;
goto v___jp_2510_;
}
}
}
v___jp_2510_:
{
size_t v___x_2512_; size_t v___x_2513_; lean_object* v___x_2514_; 
v___x_2512_ = ((size_t)1ULL);
v___x_2513_ = lean_usize_add(v_i_2504_, v___x_2512_);
v___x_2514_ = lean_array_uset(v_bs_x27_2509_, v_i_2504_, v___y_2511_);
v_i_2504_ = v___x_2513_;
v_bs_2505_ = v___x_2514_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0___redArg___boxed(lean_object* v_ctorNames_2539_, lean_object* v_us_2540_, lean_object* v_params_2541_, lean_object* v_majorFVarId_2542_, lean_object* v_sz_2543_, lean_object* v_i_2544_, lean_object* v_bs_2545_){
_start:
{
size_t v_sz_boxed_2546_; size_t v_i_boxed_2547_; lean_object* v_res_2548_; 
v_sz_boxed_2546_ = lean_unbox_usize(v_sz_2543_);
lean_dec(v_sz_2543_);
v_i_boxed_2547_ = lean_unbox_usize(v_i_2544_);
lean_dec(v_i_2544_);
v_res_2548_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0___redArg(v_ctorNames_2539_, v_us_2540_, v_params_2541_, v_majorFVarId_2542_, v_sz_boxed_2546_, v_i_boxed_2547_, v_bs_2545_);
lean_dec_ref(v_params_2541_);
lean_dec_ref(v_ctorNames_2539_);
return v_res_2548_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals(lean_object* v_s_2549_, lean_object* v_ctorNames_2550_, lean_object* v_majorFVarId_2551_, lean_object* v_us_2552_, lean_object* v_params_2553_){
_start:
{
size_t v_sz_2554_; size_t v___x_2555_; lean_object* v___x_2556_; 
v_sz_2554_ = lean_array_size(v_s_2549_);
v___x_2555_ = ((size_t)0ULL);
v___x_2556_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0___redArg(v_ctorNames_2550_, v_us_2552_, v_params_2553_, v_majorFVarId_2551_, v_sz_2554_, v___x_2555_, v_s_2549_);
return v___x_2556_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals___boxed(lean_object* v_s_2557_, lean_object* v_ctorNames_2558_, lean_object* v_majorFVarId_2559_, lean_object* v_us_2560_, lean_object* v_params_2561_){
_start:
{
lean_object* v_res_2562_; 
v_res_2562_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals(v_s_2557_, v_ctorNames_2558_, v_majorFVarId_2559_, v_us_2560_, v_params_2561_);
lean_dec_ref(v_params_2561_);
lean_dec_ref(v_ctorNames_2558_);
return v_res_2562_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0(lean_object* v_ctorNames_2563_, lean_object* v_us_2564_, lean_object* v_params_2565_, lean_object* v_majorFVarId_2566_, lean_object* v_as_2567_, size_t v_sz_2568_, size_t v_i_2569_, lean_object* v_bs_2570_){
_start:
{
lean_object* v___x_2571_; 
v___x_2571_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0___redArg(v_ctorNames_2563_, v_us_2564_, v_params_2565_, v_majorFVarId_2566_, v_sz_2568_, v_i_2569_, v_bs_2570_);
return v___x_2571_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0___boxed(lean_object* v_ctorNames_2572_, lean_object* v_us_2573_, lean_object* v_params_2574_, lean_object* v_majorFVarId_2575_, lean_object* v_as_2576_, lean_object* v_sz_2577_, lean_object* v_i_2578_, lean_object* v_bs_2579_){
_start:
{
size_t v_sz_boxed_2580_; size_t v_i_boxed_2581_; lean_object* v_res_2582_; 
v_sz_boxed_2580_ = lean_unbox_usize(v_sz_2577_);
lean_dec(v_sz_2577_);
v_i_boxed_2581_ = lean_unbox_usize(v_i_2578_);
lean_dec(v_i_2578_);
v_res_2582_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals_spec__0(v_ctorNames_2572_, v_us_2573_, v_params_2574_, v_majorFVarId_2575_, v_as_2576_, v_sz_boxed_2580_, v_i_boxed_2581_, v_bs_2579_);
lean_dec_ref(v_as_2576_);
lean_dec_ref(v_params_2574_);
lean_dec_ref(v_ctorNames_2572_);
return v_res_2582_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_2588_; lean_object* v___x_2589_; 
v___x_2588_ = l_Lean_maxRecDepthErrorMessage;
v___x_2589_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2589_, 0, v___x_2588_);
return v___x_2589_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_2590_; lean_object* v___x_2591_; 
v___x_2590_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__3);
v___x_2591_ = l_Lean_MessageData_ofFormat(v___x_2590_);
return v___x_2591_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; 
v___x_2592_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__4);
v___x_2593_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__2));
v___x_2594_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2594_, 0, v___x_2593_);
lean_ctor_set(v___x_2594_, 1, v___x_2592_);
return v___x_2594_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg(lean_object* v_ref_2595_){
_start:
{
lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; 
v___x_2597_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___closed__5);
v___x_2598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2598_, 0, v_ref_2595_);
lean_ctor_set(v___x_2598_, 1, v___x_2597_);
v___x_2599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2599_, 0, v___x_2598_);
return v___x_2599_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg___boxed(lean_object* v_ref_2600_, lean_object* v___y_2601_){
_start:
{
lean_object* v_res_2602_; 
v_res_2602_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg(v_ref_2600_);
return v_res_2602_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0(lean_object* v_00_u03b1_2603_, lean_object* v_ref_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_){
_start:
{
lean_object* v___x_2610_; 
v___x_2610_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg(v_ref_2604_);
return v___x_2610_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___boxed(lean_object* v_00_u03b1_2611_, lean_object* v_ref_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_){
_start:
{
lean_object* v_res_2618_; 
v_res_2618_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0(v_00_u03b1_2611_, v_ref_2612_, v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_);
lean_dec(v___y_2616_);
lean_dec_ref(v___y_2615_);
lean_dec(v___y_2614_);
lean_dec_ref(v___y_2613_);
return v_res_2618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_unifyEqs_x3f(lean_object* v_numEqs_2620_, lean_object* v_mvarId_2621_, lean_object* v_subst_2622_, lean_object* v_caseName_x3f_2623_, lean_object* v_a_2624_, lean_object* v_a_2625_, lean_object* v_a_2626_, lean_object* v_a_2627_){
_start:
{
lean_object* v_toCold_2629_; lean_object* v_currRecDepth_2630_; lean_object* v_ref_2631_; uint16_t v_optionFlags_2632_; uint8_t v_suppressElabErrors_2633_; uint8_t v_isRecordingDeps_2634_; lean_object* v_maxRecDepth_2635_; lean_object* v___x_2636_; uint8_t v___x_2637_; uint8_t v___x_2683_; 
v_toCold_2629_ = lean_ctor_get(v_a_2626_, 0);
lean_inc_ref(v_toCold_2629_);
v_currRecDepth_2630_ = lean_ctor_get(v_a_2626_, 1);
lean_inc(v_currRecDepth_2630_);
v_ref_2631_ = lean_ctor_get(v_a_2626_, 2);
lean_inc(v_ref_2631_);
v_optionFlags_2632_ = lean_ctor_get_uint16(v_a_2626_, sizeof(void*)*3);
v_suppressElabErrors_2633_ = lean_ctor_get_uint8(v_a_2626_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2634_ = lean_ctor_get_uint8(v_a_2626_, sizeof(void*)*3 + 3);
lean_dec_ref(v_a_2626_);
v_maxRecDepth_2635_ = lean_ctor_get(v_toCold_2629_, 3);
v___x_2636_ = lean_unsigned_to_nat(0u);
v___x_2637_ = lean_nat_dec_eq(v_numEqs_2620_, v___x_2636_);
v___x_2683_ = lean_nat_dec_eq(v_maxRecDepth_2635_, v___x_2636_);
if (v___x_2683_ == 0)
{
uint8_t v___x_2684_; 
v___x_2684_ = lean_nat_dec_eq(v_currRecDepth_2630_, v_maxRecDepth_2635_);
if (v___x_2684_ == 0)
{
goto v___jp_2638_;
}
else
{
lean_object* v___x_2685_; 
lean_dec(v_currRecDepth_2630_);
lean_dec_ref(v_toCold_2629_);
lean_dec(v_caseName_x3f_2623_);
lean_dec(v_subst_2622_);
lean_dec(v_mvarId_2621_);
lean_dec(v_numEqs_2620_);
v___x_2685_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Cases_unifyEqs_x3f_spec__0___redArg(v_ref_2631_);
return v___x_2685_;
}
}
else
{
goto v___jp_2638_;
}
v___jp_2638_:
{
if (v___x_2637_ == 0)
{
lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; 
v___x_2639_ = lean_unsigned_to_nat(1u);
v___x_2640_ = lean_nat_add(v_currRecDepth_2630_, v___x_2639_);
lean_dec(v_currRecDepth_2630_);
v___x_2641_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2641_, 0, v_toCold_2629_);
lean_ctor_set(v___x_2641_, 1, v___x_2640_);
lean_ctor_set(v___x_2641_, 2, v_ref_2631_);
lean_ctor_set_uint16(v___x_2641_, sizeof(void*)*3, v_optionFlags_2632_);
lean_ctor_set_uint8(v___x_2641_, sizeof(void*)*3 + 2, v_suppressElabErrors_2633_);
lean_ctor_set_uint8(v___x_2641_, sizeof(void*)*3 + 3, v_isRecordingDeps_2634_);
v___x_2642_ = l_Lean_Meta_intro1Core(v_mvarId_2621_, v___x_2637_, v_a_2624_, v_a_2625_, v___x_2641_, v_a_2627_);
if (lean_obj_tag(v___x_2642_) == 0)
{
lean_object* v_a_2643_; lean_object* v_fst_2644_; lean_object* v_snd_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; 
v_a_2643_ = lean_ctor_get(v___x_2642_, 0);
lean_inc(v_a_2643_);
lean_dec_ref_known(v___x_2642_, 1);
v_fst_2644_ = lean_ctor_get(v_a_2643_, 0);
lean_inc(v_fst_2644_);
v_snd_2645_ = lean_ctor_get(v_a_2643_, 1);
lean_inc(v_snd_2645_);
lean_dec(v_a_2643_);
v___x_2646_ = ((lean_object*)(l_Lean_Meta_Cases_unifyEqs_x3f___closed__0));
lean_inc(v_caseName_x3f_2623_);
v___x_2647_ = l_Lean_Meta_unifyEq_x3f(v_snd_2645_, v_fst_2644_, v_subst_2622_, v___x_2646_, v_caseName_x3f_2623_, v_a_2624_, v_a_2625_, v___x_2641_, v_a_2627_);
if (lean_obj_tag(v___x_2647_) == 0)
{
lean_object* v_a_2648_; lean_object* v___x_2650_; uint8_t v_isShared_2651_; uint8_t v_isSharedCheck_2663_; 
v_a_2648_ = lean_ctor_get(v___x_2647_, 0);
v_isSharedCheck_2663_ = !lean_is_exclusive(v___x_2647_);
if (v_isSharedCheck_2663_ == 0)
{
v___x_2650_ = v___x_2647_;
v_isShared_2651_ = v_isSharedCheck_2663_;
goto v_resetjp_2649_;
}
else
{
lean_inc(v_a_2648_);
lean_dec(v___x_2647_);
v___x_2650_ = lean_box(0);
v_isShared_2651_ = v_isSharedCheck_2663_;
goto v_resetjp_2649_;
}
v_resetjp_2649_:
{
if (lean_obj_tag(v_a_2648_) == 1)
{
lean_object* v_val_2652_; lean_object* v_mvarId_2653_; lean_object* v_subst_2654_; lean_object* v_numNewEqs_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; 
lean_del_object(v___x_2650_);
v_val_2652_ = lean_ctor_get(v_a_2648_, 0);
lean_inc(v_val_2652_);
lean_dec_ref_known(v_a_2648_, 1);
v_mvarId_2653_ = lean_ctor_get(v_val_2652_, 0);
lean_inc(v_mvarId_2653_);
v_subst_2654_ = lean_ctor_get(v_val_2652_, 1);
lean_inc(v_subst_2654_);
v_numNewEqs_2655_ = lean_ctor_get(v_val_2652_, 2);
lean_inc(v_numNewEqs_2655_);
lean_dec(v_val_2652_);
v___x_2656_ = lean_nat_sub(v_numEqs_2620_, v___x_2639_);
lean_dec(v_numEqs_2620_);
v___x_2657_ = lean_nat_add(v___x_2656_, v_numNewEqs_2655_);
lean_dec(v_numNewEqs_2655_);
lean_dec(v___x_2656_);
v_numEqs_2620_ = v___x_2657_;
v_mvarId_2621_ = v_mvarId_2653_;
v_subst_2622_ = v_subst_2654_;
v_a_2626_ = v___x_2641_;
goto _start;
}
else
{
lean_object* v___x_2659_; lean_object* v___x_2661_; 
lean_dec(v_a_2648_);
lean_dec_ref_known(v___x_2641_, 3);
lean_dec(v_caseName_x3f_2623_);
lean_dec(v_numEqs_2620_);
v___x_2659_ = lean_box(0);
if (v_isShared_2651_ == 0)
{
lean_ctor_set(v___x_2650_, 0, v___x_2659_);
v___x_2661_ = v___x_2650_;
goto v_reusejp_2660_;
}
else
{
lean_object* v_reuseFailAlloc_2662_; 
v_reuseFailAlloc_2662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2662_, 0, v___x_2659_);
v___x_2661_ = v_reuseFailAlloc_2662_;
goto v_reusejp_2660_;
}
v_reusejp_2660_:
{
return v___x_2661_;
}
}
}
}
else
{
lean_object* v_a_2664_; lean_object* v___x_2666_; uint8_t v_isShared_2667_; uint8_t v_isSharedCheck_2671_; 
lean_dec_ref_known(v___x_2641_, 3);
lean_dec(v_caseName_x3f_2623_);
lean_dec(v_numEqs_2620_);
v_a_2664_ = lean_ctor_get(v___x_2647_, 0);
v_isSharedCheck_2671_ = !lean_is_exclusive(v___x_2647_);
if (v_isSharedCheck_2671_ == 0)
{
v___x_2666_ = v___x_2647_;
v_isShared_2667_ = v_isSharedCheck_2671_;
goto v_resetjp_2665_;
}
else
{
lean_inc(v_a_2664_);
lean_dec(v___x_2647_);
v___x_2666_ = lean_box(0);
v_isShared_2667_ = v_isSharedCheck_2671_;
goto v_resetjp_2665_;
}
v_resetjp_2665_:
{
lean_object* v___x_2669_; 
if (v_isShared_2667_ == 0)
{
v___x_2669_ = v___x_2666_;
goto v_reusejp_2668_;
}
else
{
lean_object* v_reuseFailAlloc_2670_; 
v_reuseFailAlloc_2670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2670_, 0, v_a_2664_);
v___x_2669_ = v_reuseFailAlloc_2670_;
goto v_reusejp_2668_;
}
v_reusejp_2668_:
{
return v___x_2669_;
}
}
}
}
else
{
lean_object* v_a_2672_; lean_object* v___x_2674_; uint8_t v_isShared_2675_; uint8_t v_isSharedCheck_2679_; 
lean_dec_ref_known(v___x_2641_, 3);
lean_dec(v_caseName_x3f_2623_);
lean_dec(v_subst_2622_);
lean_dec(v_numEqs_2620_);
v_a_2672_ = lean_ctor_get(v___x_2642_, 0);
v_isSharedCheck_2679_ = !lean_is_exclusive(v___x_2642_);
if (v_isSharedCheck_2679_ == 0)
{
v___x_2674_ = v___x_2642_;
v_isShared_2675_ = v_isSharedCheck_2679_;
goto v_resetjp_2673_;
}
else
{
lean_inc(v_a_2672_);
lean_dec(v___x_2642_);
v___x_2674_ = lean_box(0);
v_isShared_2675_ = v_isSharedCheck_2679_;
goto v_resetjp_2673_;
}
v_resetjp_2673_:
{
lean_object* v___x_2677_; 
if (v_isShared_2675_ == 0)
{
v___x_2677_ = v___x_2674_;
goto v_reusejp_2676_;
}
else
{
lean_object* v_reuseFailAlloc_2678_; 
v_reuseFailAlloc_2678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2678_, 0, v_a_2672_);
v___x_2677_ = v_reuseFailAlloc_2678_;
goto v_reusejp_2676_;
}
v_reusejp_2676_:
{
return v___x_2677_;
}
}
}
}
else
{
lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; 
lean_dec(v_ref_2631_);
lean_dec(v_currRecDepth_2630_);
lean_dec_ref(v_toCold_2629_);
lean_dec(v_caseName_x3f_2623_);
lean_dec(v_numEqs_2620_);
v___x_2680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2680_, 0, v_mvarId_2621_);
lean_ctor_set(v___x_2680_, 1, v_subst_2622_);
v___x_2681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2681_, 0, v___x_2680_);
v___x_2682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2682_, 0, v___x_2681_);
return v___x_2682_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_unifyEqs_x3f___boxed(lean_object* v_numEqs_2686_, lean_object* v_mvarId_2687_, lean_object* v_subst_2688_, lean_object* v_caseName_x3f_2689_, lean_object* v_a_2690_, lean_object* v_a_2691_, lean_object* v_a_2692_, lean_object* v_a_2693_, lean_object* v_a_2694_){
_start:
{
lean_object* v_res_2695_; 
v_res_2695_ = l_Lean_Meta_Cases_unifyEqs_x3f(v_numEqs_2686_, v_mvarId_2687_, v_subst_2688_, v_caseName_x3f_2689_, v_a_2690_, v_a_2691_, v_a_2692_, v_a_2693_);
lean_dec(v_a_2693_);
lean_dec(v_a_2691_);
lean_dec_ref(v_a_2690_);
return v_res_2695_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__0(lean_object* v_snd_2696_, size_t v_sz_2697_, size_t v_i_2698_, lean_object* v_bs_2699_){
_start:
{
uint8_t v___x_2700_; 
v___x_2700_ = lean_usize_dec_lt(v_i_2698_, v_sz_2697_);
if (v___x_2700_ == 0)
{
lean_dec(v_snd_2696_);
return v_bs_2699_;
}
else
{
lean_object* v_v_2701_; lean_object* v___x_2702_; lean_object* v_bs_x27_2703_; lean_object* v___x_2704_; size_t v___x_2705_; size_t v___x_2706_; lean_object* v___x_2707_; 
v_v_2701_ = lean_array_uget(v_bs_2699_, v_i_2698_);
v___x_2702_ = lean_unsigned_to_nat(0u);
v_bs_x27_2703_ = lean_array_uset(v_bs_2699_, v_i_2698_, v___x_2702_);
lean_inc(v_snd_2696_);
v___x_2704_ = l_Lean_Meta_FVarSubst_apply(v_snd_2696_, v_v_2701_);
lean_dec(v_v_2701_);
v___x_2705_ = ((size_t)1ULL);
v___x_2706_ = lean_usize_add(v_i_2698_, v___x_2705_);
v___x_2707_ = lean_array_uset(v_bs_x27_2703_, v_i_2698_, v___x_2704_);
v_i_2698_ = v___x_2706_;
v_bs_2699_ = v___x_2707_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__0___boxed(lean_object* v_snd_2709_, lean_object* v_sz_2710_, lean_object* v_i_2711_, lean_object* v_bs_2712_){
_start:
{
size_t v_sz_boxed_2713_; size_t v_i_boxed_2714_; lean_object* v_res_2715_; 
v_sz_boxed_2713_ = lean_unbox_usize(v_sz_2710_);
lean_dec(v_sz_2710_);
v_i_boxed_2714_ = lean_unbox_usize(v_i_2711_);
lean_dec(v_i_2711_);
v_res_2715_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__0(v_snd_2709_, v_sz_boxed_2713_, v_i_boxed_2714_, v_bs_2712_);
return v_res_2715_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1_spec__1(lean_object* v_numEqs_2716_, lean_object* v_as_2717_, size_t v_i_2718_, size_t v_stop_2719_, lean_object* v_b_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_){
_start:
{
lean_object* v_a_2727_; uint8_t v___x_2731_; 
v___x_2731_ = lean_usize_dec_eq(v_i_2718_, v_stop_2719_);
if (v___x_2731_ == 0)
{
lean_object* v___x_2732_; lean_object* v_toInductionSubgoal_2733_; lean_object* v_ctorName_2734_; lean_object* v___x_2736_; uint8_t v_isShared_2737_; uint8_t v_isSharedCheck_2768_; 
v___x_2732_ = lean_array_uget(v_as_2717_, v_i_2718_);
v_toInductionSubgoal_2733_ = lean_ctor_get(v___x_2732_, 0);
v_ctorName_2734_ = lean_ctor_get(v___x_2732_, 1);
v_isSharedCheck_2768_ = !lean_is_exclusive(v___x_2732_);
if (v_isSharedCheck_2768_ == 0)
{
v___x_2736_ = v___x_2732_;
v_isShared_2737_ = v_isSharedCheck_2768_;
goto v_resetjp_2735_;
}
else
{
lean_inc(v_ctorName_2734_);
lean_inc(v_toInductionSubgoal_2733_);
lean_dec(v___x_2732_);
v___x_2736_ = lean_box(0);
v_isShared_2737_ = v_isSharedCheck_2768_;
goto v_resetjp_2735_;
}
v_resetjp_2735_:
{
lean_object* v_mvarId_2738_; lean_object* v_fields_2739_; lean_object* v_subst_2740_; lean_object* v___x_2742_; uint8_t v_isShared_2743_; uint8_t v_isSharedCheck_2767_; 
v_mvarId_2738_ = lean_ctor_get(v_toInductionSubgoal_2733_, 0);
v_fields_2739_ = lean_ctor_get(v_toInductionSubgoal_2733_, 1);
v_subst_2740_ = lean_ctor_get(v_toInductionSubgoal_2733_, 2);
v_isSharedCheck_2767_ = !lean_is_exclusive(v_toInductionSubgoal_2733_);
if (v_isSharedCheck_2767_ == 0)
{
v___x_2742_ = v_toInductionSubgoal_2733_;
v_isShared_2743_ = v_isSharedCheck_2767_;
goto v_resetjp_2741_;
}
else
{
lean_inc(v_subst_2740_);
lean_inc(v_fields_2739_);
lean_inc(v_mvarId_2738_);
lean_dec(v_toInductionSubgoal_2733_);
v___x_2742_ = lean_box(0);
v_isShared_2743_ = v_isSharedCheck_2767_;
goto v_resetjp_2741_;
}
v_resetjp_2741_:
{
lean_object* v___x_2744_; 
lean_inc_ref(v___y_2723_);
lean_inc(v_ctorName_2734_);
lean_inc(v_numEqs_2716_);
v___x_2744_ = l_Lean_Meta_Cases_unifyEqs_x3f(v_numEqs_2716_, v_mvarId_2738_, v_subst_2740_, v_ctorName_2734_, v___y_2721_, v___y_2722_, v___y_2723_, v___y_2724_);
if (lean_obj_tag(v___x_2744_) == 0)
{
lean_object* v_a_2745_; 
v_a_2745_ = lean_ctor_get(v___x_2744_, 0);
lean_inc(v_a_2745_);
lean_dec_ref_known(v___x_2744_, 1);
if (lean_obj_tag(v_a_2745_) == 0)
{
lean_del_object(v___x_2742_);
lean_dec_ref(v_fields_2739_);
lean_del_object(v___x_2736_);
lean_dec(v_ctorName_2734_);
v_a_2727_ = v_b_2720_;
goto v___jp_2726_;
}
else
{
lean_object* v_val_2746_; lean_object* v_fst_2747_; lean_object* v_snd_2748_; size_t v_sz_2749_; size_t v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2753_; 
v_val_2746_ = lean_ctor_get(v_a_2745_, 0);
lean_inc(v_val_2746_);
lean_dec_ref_known(v_a_2745_, 1);
v_fst_2747_ = lean_ctor_get(v_val_2746_, 0);
lean_inc(v_fst_2747_);
v_snd_2748_ = lean_ctor_get(v_val_2746_, 1);
lean_inc_n(v_snd_2748_, 2);
lean_dec(v_val_2746_);
v_sz_2749_ = lean_array_size(v_fields_2739_);
v___x_2750_ = ((size_t)0ULL);
v___x_2751_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__0(v_snd_2748_, v_sz_2749_, v___x_2750_, v_fields_2739_);
if (v_isShared_2743_ == 0)
{
lean_ctor_set(v___x_2742_, 2, v_snd_2748_);
lean_ctor_set(v___x_2742_, 1, v___x_2751_);
lean_ctor_set(v___x_2742_, 0, v_fst_2747_);
v___x_2753_ = v___x_2742_;
goto v_reusejp_2752_;
}
else
{
lean_object* v_reuseFailAlloc_2758_; 
v_reuseFailAlloc_2758_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2758_, 0, v_fst_2747_);
lean_ctor_set(v_reuseFailAlloc_2758_, 1, v___x_2751_);
lean_ctor_set(v_reuseFailAlloc_2758_, 2, v_snd_2748_);
v___x_2753_ = v_reuseFailAlloc_2758_;
goto v_reusejp_2752_;
}
v_reusejp_2752_:
{
lean_object* v___x_2755_; 
if (v_isShared_2737_ == 0)
{
lean_ctor_set(v___x_2736_, 0, v___x_2753_);
v___x_2755_ = v___x_2736_;
goto v_reusejp_2754_;
}
else
{
lean_object* v_reuseFailAlloc_2757_; 
v_reuseFailAlloc_2757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2757_, 0, v___x_2753_);
lean_ctor_set(v_reuseFailAlloc_2757_, 1, v_ctorName_2734_);
v___x_2755_ = v_reuseFailAlloc_2757_;
goto v_reusejp_2754_;
}
v_reusejp_2754_:
{
lean_object* v___x_2756_; 
v___x_2756_ = lean_array_push(v_b_2720_, v___x_2755_);
v_a_2727_ = v___x_2756_;
goto v___jp_2726_;
}
}
}
}
else
{
lean_object* v_a_2759_; lean_object* v___x_2761_; uint8_t v_isShared_2762_; uint8_t v_isSharedCheck_2766_; 
lean_del_object(v___x_2742_);
lean_dec_ref(v_fields_2739_);
lean_del_object(v___x_2736_);
lean_dec(v_ctorName_2734_);
lean_dec_ref(v_b_2720_);
lean_dec(v_numEqs_2716_);
v_a_2759_ = lean_ctor_get(v___x_2744_, 0);
v_isSharedCheck_2766_ = !lean_is_exclusive(v___x_2744_);
if (v_isSharedCheck_2766_ == 0)
{
v___x_2761_ = v___x_2744_;
v_isShared_2762_ = v_isSharedCheck_2766_;
goto v_resetjp_2760_;
}
else
{
lean_inc(v_a_2759_);
lean_dec(v___x_2744_);
v___x_2761_ = lean_box(0);
v_isShared_2762_ = v_isSharedCheck_2766_;
goto v_resetjp_2760_;
}
v_resetjp_2760_:
{
lean_object* v___x_2764_; 
if (v_isShared_2762_ == 0)
{
v___x_2764_ = v___x_2761_;
goto v_reusejp_2763_;
}
else
{
lean_object* v_reuseFailAlloc_2765_; 
v_reuseFailAlloc_2765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2765_, 0, v_a_2759_);
v___x_2764_ = v_reuseFailAlloc_2765_;
goto v_reusejp_2763_;
}
v_reusejp_2763_:
{
return v___x_2764_;
}
}
}
}
}
}
else
{
lean_object* v___x_2769_; 
lean_dec(v_numEqs_2716_);
v___x_2769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2769_, 0, v_b_2720_);
return v___x_2769_;
}
v___jp_2726_:
{
size_t v___x_2728_; size_t v___x_2729_; 
v___x_2728_ = ((size_t)1ULL);
v___x_2729_ = lean_usize_add(v_i_2718_, v___x_2728_);
v_i_2718_ = v___x_2729_;
v_b_2720_ = v_a_2727_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1_spec__1___boxed(lean_object* v_numEqs_2770_, lean_object* v_as_2771_, lean_object* v_i_2772_, lean_object* v_stop_2773_, lean_object* v_b_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_){
_start:
{
size_t v_i_boxed_2780_; size_t v_stop_boxed_2781_; lean_object* v_res_2782_; 
v_i_boxed_2780_ = lean_unbox_usize(v_i_2772_);
lean_dec(v_i_2772_);
v_stop_boxed_2781_ = lean_unbox_usize(v_stop_2773_);
lean_dec(v_stop_2773_);
v_res_2782_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1_spec__1(v_numEqs_2770_, v_as_2771_, v_i_boxed_2780_, v_stop_boxed_2781_, v_b_2774_, v___y_2775_, v___y_2776_, v___y_2777_, v___y_2778_);
lean_dec(v___y_2778_);
lean_dec_ref(v___y_2777_);
lean_dec(v___y_2776_);
lean_dec_ref(v___y_2775_);
lean_dec_ref(v_as_2771_);
return v_res_2782_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1(lean_object* v_numEqs_2785_, lean_object* v_as_2786_, lean_object* v_start_2787_, lean_object* v_stop_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_){
_start:
{
lean_object* v___x_2794_; uint8_t v___x_2795_; 
v___x_2794_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1___closed__0));
v___x_2795_ = lean_nat_dec_lt(v_start_2787_, v_stop_2788_);
if (v___x_2795_ == 0)
{
lean_object* v___x_2796_; 
lean_dec(v_numEqs_2785_);
v___x_2796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2796_, 0, v___x_2794_);
return v___x_2796_;
}
else
{
lean_object* v___x_2797_; uint8_t v___x_2798_; 
v___x_2797_ = lean_array_get_size(v_as_2786_);
v___x_2798_ = lean_nat_dec_le(v_stop_2788_, v___x_2797_);
if (v___x_2798_ == 0)
{
uint8_t v___x_2799_; 
v___x_2799_ = lean_nat_dec_lt(v_start_2787_, v___x_2797_);
if (v___x_2799_ == 0)
{
lean_object* v___x_2800_; 
lean_dec(v_numEqs_2785_);
v___x_2800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2800_, 0, v___x_2794_);
return v___x_2800_;
}
else
{
size_t v___x_2801_; size_t v___x_2802_; lean_object* v___x_2803_; 
v___x_2801_ = lean_usize_of_nat(v_start_2787_);
v___x_2802_ = lean_usize_of_nat(v___x_2797_);
v___x_2803_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1_spec__1(v_numEqs_2785_, v_as_2786_, v___x_2801_, v___x_2802_, v___x_2794_, v___y_2789_, v___y_2790_, v___y_2791_, v___y_2792_);
return v___x_2803_;
}
}
else
{
size_t v___x_2804_; size_t v___x_2805_; lean_object* v___x_2806_; 
v___x_2804_ = lean_usize_of_nat(v_start_2787_);
v___x_2805_ = lean_usize_of_nat(v_stop_2788_);
v___x_2806_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1_spec__1(v_numEqs_2785_, v_as_2786_, v___x_2804_, v___x_2805_, v___x_2794_, v___y_2789_, v___y_2790_, v___y_2791_, v___y_2792_);
return v___x_2806_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1___boxed(lean_object* v_numEqs_2807_, lean_object* v_as_2808_, lean_object* v_start_2809_, lean_object* v_stop_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_){
_start:
{
lean_object* v_res_2816_; 
v_res_2816_ = l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1(v_numEqs_2807_, v_as_2808_, v_start_2809_, v_stop_2810_, v___y_2811_, v___y_2812_, v___y_2813_, v___y_2814_);
lean_dec(v___y_2814_);
lean_dec_ref(v___y_2813_);
lean_dec(v___y_2812_);
lean_dec_ref(v___y_2811_);
lean_dec(v_stop_2810_);
lean_dec(v_start_2809_);
lean_dec_ref(v_as_2808_);
return v_res_2816_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs(lean_object* v_numEqs_2817_, lean_object* v_subgoals_2818_, lean_object* v_a_2819_, lean_object* v_a_2820_, lean_object* v_a_2821_, lean_object* v_a_2822_){
_start:
{
lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; 
v___x_2824_ = lean_unsigned_to_nat(0u);
v___x_2825_ = lean_array_get_size(v_subgoals_2818_);
v___x_2826_ = l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs_spec__1(v_numEqs_2817_, v_subgoals_2818_, v___x_2824_, v___x_2825_, v_a_2819_, v_a_2820_, v_a_2821_, v_a_2822_);
return v___x_2826_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs___boxed(lean_object* v_numEqs_2827_, lean_object* v_subgoals_2828_, lean_object* v_a_2829_, lean_object* v_a_2830_, lean_object* v_a_2831_, lean_object* v_a_2832_, lean_object* v_a_2833_){
_start:
{
lean_object* v_res_2834_; 
v_res_2834_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs(v_numEqs_2827_, v_subgoals_2828_, v_a_2829_, v_a_2830_, v_a_2831_, v_a_2832_);
lean_dec(v_a_2832_);
lean_dec_ref(v_a_2831_);
lean_dec(v_a_2830_);
lean_dec_ref(v_a_2829_);
lean_dec_ref(v_subgoals_2828_);
return v_res_2834_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0(lean_object* v___x_2846_, lean_object* v_ctx_2847_, lean_object* v_mvarId_2848_, lean_object* v_majorFVarId_2849_, lean_object* v_givenNames_2850_, uint8_t v_useNatCasesAuxOn_2851_, lean_object* v_interestingCtors_x3f_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_){
_start:
{
lean_object* v___x_2858_; 
lean_inc(v___y_2856_);
lean_inc_ref(v___y_2855_);
lean_inc(v___y_2854_);
lean_inc_ref(v___y_2853_);
v___x_2858_ = lean_infer_type(v___x_2846_, v___y_2853_, v___y_2854_, v___y_2855_, v___y_2856_);
if (lean_obj_tag(v___x_2858_) == 0)
{
lean_object* v_a_2859_; lean_object* v___x_2860_; 
v_a_2859_ = lean_ctor_get(v___x_2858_, 0);
lean_inc(v_a_2859_);
lean_dec_ref_known(v___x_2858_, 1);
v___x_2860_ = l_Lean_Meta_getInductiveUniverseAndParams(v_a_2859_, v___y_2853_, v___y_2854_, v___y_2855_, v___y_2856_);
if (lean_obj_tag(v___x_2860_) == 0)
{
lean_object* v_a_2861_; lean_object* v_fst_2862_; lean_object* v_snd_2863_; lean_object* v___y_2865_; lean_object* v___y_2866_; lean_object* v___y_2867_; lean_object* v___y_2868_; lean_object* v___y_2869_; lean_object* v___y_2892_; lean_object* v___y_2893_; lean_object* v___y_2894_; lean_object* v___y_2895_; lean_object* v___y_2901_; lean_object* v___y_2902_; lean_object* v___y_2903_; lean_object* v___y_2904_; 
v_a_2861_ = lean_ctor_get(v___x_2860_, 0);
lean_inc(v_a_2861_);
lean_dec_ref_known(v___x_2860_, 1);
v_fst_2862_ = lean_ctor_get(v_a_2861_, 0);
lean_inc(v_fst_2862_);
v_snd_2863_ = lean_ctor_get(v_a_2861_, 1);
lean_inc(v_snd_2863_);
lean_dec(v_a_2861_);
if (lean_obj_tag(v_interestingCtors_x3f_2852_) == 1)
{
lean_object* v_val_2914_; lean_object* v___x_2915_; lean_object* v_env_2916_; lean_object* v___x_2917_; uint8_t v___x_2918_; uint8_t v___x_2919_; lean_object* v___x_2920_; 
v_val_2914_ = lean_ctor_get(v_interestingCtors_x3f_2852_, 0);
lean_inc(v_val_2914_);
lean_dec_ref_known(v_interestingCtors_x3f_2852_, 1);
v___x_2915_ = lean_st_ref_get(v___y_2856_);
v_env_2916_ = lean_ctor_get(v___x_2915_, 0);
lean_inc_ref(v_env_2916_);
lean_dec(v___x_2915_);
v___x_2917_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__5));
v___x_2918_ = 1;
v___x_2919_ = l_Lean_Environment_contains(v_env_2916_, v___x_2917_, v___x_2918_);
v___x_2920_ = lean_st_ref_get(v___y_2856_);
if (v___x_2919_ == 0)
{
lean_dec(v___x_2920_);
lean_dec(v_val_2914_);
v___y_2901_ = v___y_2853_;
v___y_2902_ = v___y_2854_;
v___y_2903_ = v___y_2855_;
v___y_2904_ = v___y_2856_;
goto v___jp_2900_;
}
else
{
lean_object* v_inductiveVal_2921_; lean_object* v_toConstantVal_2922_; lean_object* v_ctors_2923_; lean_object* v_name_2924_; lean_object* v_env_2925_; lean_object* v___x_2926_; uint8_t v___x_2927_; 
v_inductiveVal_2921_ = lean_ctor_get(v_ctx_2847_, 0);
v_toConstantVal_2922_ = lean_ctor_get(v_inductiveVal_2921_, 0);
v_ctors_2923_ = lean_ctor_get(v_inductiveVal_2921_, 4);
v_name_2924_ = lean_ctor_get(v_toConstantVal_2922_, 0);
v_env_2925_ = lean_ctor_get(v___x_2920_, 0);
lean_inc_ref(v_env_2925_);
lean_dec(v___x_2920_);
lean_inc(v_name_2924_);
v___x_2926_ = l_Lean_mkCtorIdxName(v_name_2924_);
v___x_2927_ = l_Lean_Environment_contains(v_env_2925_, v___x_2926_, v___x_2918_);
if (v___x_2927_ == 0)
{
lean_dec(v_val_2914_);
v___y_2901_ = v___y_2853_;
v___y_2902_ = v___y_2854_;
v___y_2903_ = v___y_2855_;
v___y_2904_ = v___y_2856_;
goto v___jp_2900_;
}
else
{
lean_object* v___x_2928_; lean_object* v___x_2929_; uint8_t v___x_2930_; 
v___x_2928_ = lean_array_get_size(v_val_2914_);
v___x_2929_ = lean_unsigned_to_nat(0u);
v___x_2930_ = lean_nat_dec_eq(v___x_2928_, v___x_2929_);
if (v___x_2930_ == 0)
{
lean_object* v___x_2931_; uint8_t v___x_2932_; 
v___x_2931_ = l_List_lengthTR___redArg(v_ctors_2923_);
v___x_2932_ = lean_nat_dec_lt(v___x_2928_, v___x_2931_);
lean_dec(v___x_2931_);
if (v___x_2932_ == 0)
{
lean_dec(v_val_2914_);
v___y_2901_ = v___y_2853_;
v___y_2902_ = v___y_2854_;
v___y_2903_ = v___y_2855_;
v___y_2904_ = v___y_2856_;
goto v___jp_2900_;
}
else
{
lean_object* v___x_2933_; 
lean_inc(v_name_2924_);
lean_dec_ref(v_ctx_2847_);
lean_inc(v_val_2914_);
v___x_2933_ = l_Lean_Meta_mkSparseCasesOn(v_name_2924_, v_val_2914_, v___y_2853_, v___y_2854_, v___y_2855_, v___y_2856_);
if (lean_obj_tag(v___x_2933_) == 0)
{
lean_object* v_a_2934_; lean_object* v___x_2935_; 
v_a_2934_ = lean_ctor_get(v___x_2933_, 0);
lean_inc(v_a_2934_);
lean_dec_ref_known(v___x_2933_, 1);
lean_inc(v_majorFVarId_2849_);
v___x_2935_ = l_Lean_MVarId_induction(v_mvarId_2848_, v_majorFVarId_2849_, v_a_2934_, v_givenNames_2850_, v___y_2853_, v___y_2854_, v___y_2855_, v___y_2856_);
lean_dec(v___y_2856_);
lean_dec_ref(v___y_2855_);
lean_dec(v___y_2854_);
lean_dec_ref(v___y_2853_);
if (lean_obj_tag(v___x_2935_) == 0)
{
lean_object* v_a_2936_; lean_object* v___x_2938_; uint8_t v_isShared_2939_; uint8_t v_isSharedCheck_2944_; 
v_a_2936_ = lean_ctor_get(v___x_2935_, 0);
v_isSharedCheck_2944_ = !lean_is_exclusive(v___x_2935_);
if (v_isSharedCheck_2944_ == 0)
{
v___x_2938_ = v___x_2935_;
v_isShared_2939_ = v_isSharedCheck_2944_;
goto v_resetjp_2937_;
}
else
{
lean_inc(v_a_2936_);
lean_dec(v___x_2935_);
v___x_2938_ = lean_box(0);
v_isShared_2939_ = v_isSharedCheck_2944_;
goto v_resetjp_2937_;
}
v_resetjp_2937_:
{
lean_object* v___x_2940_; lean_object* v___x_2942_; 
v___x_2940_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals(v_a_2936_, v_val_2914_, v_majorFVarId_2849_, v_fst_2862_, v_snd_2863_);
lean_dec(v_snd_2863_);
lean_dec(v_val_2914_);
if (v_isShared_2939_ == 0)
{
lean_ctor_set(v___x_2938_, 0, v___x_2940_);
v___x_2942_ = v___x_2938_;
goto v_reusejp_2941_;
}
else
{
lean_object* v_reuseFailAlloc_2943_; 
v_reuseFailAlloc_2943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2943_, 0, v___x_2940_);
v___x_2942_ = v_reuseFailAlloc_2943_;
goto v_reusejp_2941_;
}
v_reusejp_2941_:
{
return v___x_2942_;
}
}
}
else
{
lean_object* v_a_2945_; lean_object* v___x_2947_; uint8_t v_isShared_2948_; uint8_t v_isSharedCheck_2952_; 
lean_dec(v_val_2914_);
lean_dec(v_snd_2863_);
lean_dec(v_fst_2862_);
lean_dec(v_majorFVarId_2849_);
v_a_2945_ = lean_ctor_get(v___x_2935_, 0);
v_isSharedCheck_2952_ = !lean_is_exclusive(v___x_2935_);
if (v_isSharedCheck_2952_ == 0)
{
v___x_2947_ = v___x_2935_;
v_isShared_2948_ = v_isSharedCheck_2952_;
goto v_resetjp_2946_;
}
else
{
lean_inc(v_a_2945_);
lean_dec(v___x_2935_);
v___x_2947_ = lean_box(0);
v_isShared_2948_ = v_isSharedCheck_2952_;
goto v_resetjp_2946_;
}
v_resetjp_2946_:
{
lean_object* v___x_2950_; 
if (v_isShared_2948_ == 0)
{
v___x_2950_ = v___x_2947_;
goto v_reusejp_2949_;
}
else
{
lean_object* v_reuseFailAlloc_2951_; 
v_reuseFailAlloc_2951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2951_, 0, v_a_2945_);
v___x_2950_ = v_reuseFailAlloc_2951_;
goto v_reusejp_2949_;
}
v_reusejp_2949_:
{
return v___x_2950_;
}
}
}
}
else
{
lean_object* v_a_2953_; lean_object* v___x_2955_; uint8_t v_isShared_2956_; uint8_t v_isSharedCheck_2960_; 
lean_dec(v_val_2914_);
lean_dec(v_snd_2863_);
lean_dec(v_fst_2862_);
lean_dec(v___y_2856_);
lean_dec_ref(v___y_2855_);
lean_dec(v___y_2854_);
lean_dec_ref(v___y_2853_);
lean_dec_ref(v_givenNames_2850_);
lean_dec(v_majorFVarId_2849_);
lean_dec(v_mvarId_2848_);
v_a_2953_ = lean_ctor_get(v___x_2933_, 0);
v_isSharedCheck_2960_ = !lean_is_exclusive(v___x_2933_);
if (v_isSharedCheck_2960_ == 0)
{
v___x_2955_ = v___x_2933_;
v_isShared_2956_ = v_isSharedCheck_2960_;
goto v_resetjp_2954_;
}
else
{
lean_inc(v_a_2953_);
lean_dec(v___x_2933_);
v___x_2955_ = lean_box(0);
v_isShared_2956_ = v_isSharedCheck_2960_;
goto v_resetjp_2954_;
}
v_resetjp_2954_:
{
lean_object* v___x_2958_; 
if (v_isShared_2956_ == 0)
{
v___x_2958_ = v___x_2955_;
goto v_reusejp_2957_;
}
else
{
lean_object* v_reuseFailAlloc_2959_; 
v_reuseFailAlloc_2959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2959_, 0, v_a_2953_);
v___x_2958_ = v_reuseFailAlloc_2959_;
goto v_reusejp_2957_;
}
v_reusejp_2957_:
{
return v___x_2958_;
}
}
}
}
}
else
{
lean_dec(v_val_2914_);
v___y_2901_ = v___y_2853_;
v___y_2902_ = v___y_2854_;
v___y_2903_ = v___y_2855_;
v___y_2904_ = v___y_2856_;
goto v___jp_2900_;
}
}
}
}
else
{
lean_dec(v_interestingCtors_x3f_2852_);
v___y_2901_ = v___y_2853_;
v___y_2902_ = v___y_2854_;
v___y_2903_ = v___y_2855_;
v___y_2904_ = v___y_2856_;
goto v___jp_2900_;
}
v___jp_2864_:
{
lean_object* v_inductiveVal_2870_; lean_object* v_ctors_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; 
v_inductiveVal_2870_ = lean_ctor_get(v_ctx_2847_, 0);
lean_inc_ref(v_inductiveVal_2870_);
lean_dec_ref(v_ctx_2847_);
v_ctors_2871_ = lean_ctor_get(v_inductiveVal_2870_, 4);
lean_inc(v_ctors_2871_);
lean_dec_ref(v_inductiveVal_2870_);
v___x_2872_ = lean_array_mk(v_ctors_2871_);
lean_inc(v_majorFVarId_2849_);
v___x_2873_ = l_Lean_MVarId_induction(v_mvarId_2848_, v_majorFVarId_2849_, v___y_2869_, v_givenNames_2850_, v___y_2867_, v___y_2866_, v___y_2865_, v___y_2868_);
lean_dec(v___y_2868_);
lean_dec_ref(v___y_2865_);
lean_dec(v___y_2866_);
lean_dec_ref(v___y_2867_);
if (lean_obj_tag(v___x_2873_) == 0)
{
lean_object* v_a_2874_; lean_object* v___x_2876_; uint8_t v_isShared_2877_; uint8_t v_isSharedCheck_2882_; 
v_a_2874_ = lean_ctor_get(v___x_2873_, 0);
v_isSharedCheck_2882_ = !lean_is_exclusive(v___x_2873_);
if (v_isSharedCheck_2882_ == 0)
{
v___x_2876_ = v___x_2873_;
v_isShared_2877_ = v_isSharedCheck_2882_;
goto v_resetjp_2875_;
}
else
{
lean_inc(v_a_2874_);
lean_dec(v___x_2873_);
v___x_2876_ = lean_box(0);
v_isShared_2877_ = v_isSharedCheck_2882_;
goto v_resetjp_2875_;
}
v_resetjp_2875_:
{
lean_object* v___x_2878_; lean_object* v___x_2880_; 
v___x_2878_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals(v_a_2874_, v___x_2872_, v_majorFVarId_2849_, v_fst_2862_, v_snd_2863_);
lean_dec(v_snd_2863_);
lean_dec_ref(v___x_2872_);
if (v_isShared_2877_ == 0)
{
lean_ctor_set(v___x_2876_, 0, v___x_2878_);
v___x_2880_ = v___x_2876_;
goto v_reusejp_2879_;
}
else
{
lean_object* v_reuseFailAlloc_2881_; 
v_reuseFailAlloc_2881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2881_, 0, v___x_2878_);
v___x_2880_ = v_reuseFailAlloc_2881_;
goto v_reusejp_2879_;
}
v_reusejp_2879_:
{
return v___x_2880_;
}
}
}
else
{
lean_object* v_a_2883_; lean_object* v___x_2885_; uint8_t v_isShared_2886_; uint8_t v_isSharedCheck_2890_; 
lean_dec_ref(v___x_2872_);
lean_dec(v_snd_2863_);
lean_dec(v_fst_2862_);
lean_dec(v_majorFVarId_2849_);
v_a_2883_ = lean_ctor_get(v___x_2873_, 0);
v_isSharedCheck_2890_ = !lean_is_exclusive(v___x_2873_);
if (v_isSharedCheck_2890_ == 0)
{
v___x_2885_ = v___x_2873_;
v_isShared_2886_ = v_isSharedCheck_2890_;
goto v_resetjp_2884_;
}
else
{
lean_inc(v_a_2883_);
lean_dec(v___x_2873_);
v___x_2885_ = lean_box(0);
v_isShared_2886_ = v_isSharedCheck_2890_;
goto v_resetjp_2884_;
}
v_resetjp_2884_:
{
lean_object* v___x_2888_; 
if (v_isShared_2886_ == 0)
{
v___x_2888_ = v___x_2885_;
goto v_reusejp_2887_;
}
else
{
lean_object* v_reuseFailAlloc_2889_; 
v_reuseFailAlloc_2889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2889_, 0, v_a_2883_);
v___x_2888_ = v_reuseFailAlloc_2889_;
goto v_reusejp_2887_;
}
v_reusejp_2887_:
{
return v___x_2888_;
}
}
}
}
v___jp_2891_:
{
lean_object* v_inductiveVal_2896_; lean_object* v_toConstantVal_2897_; lean_object* v_name_2898_; lean_object* v___x_2899_; 
v_inductiveVal_2896_ = lean_ctor_get(v_ctx_2847_, 0);
v_toConstantVal_2897_ = lean_ctor_get(v_inductiveVal_2896_, 0);
v_name_2898_ = lean_ctor_get(v_toConstantVal_2897_, 0);
lean_inc(v_name_2898_);
v___x_2899_ = l_Lean_mkCasesOnName(v_name_2898_);
v___y_2865_ = v___y_2892_;
v___y_2866_ = v___y_2894_;
v___y_2867_ = v___y_2893_;
v___y_2868_ = v___y_2895_;
v___y_2869_ = v___x_2899_;
goto v___jp_2864_;
}
v___jp_2900_:
{
lean_object* v___x_2905_; 
v___x_2905_ = lean_st_ref_get(v___y_2904_);
if (v_useNatCasesAuxOn_2851_ == 0)
{
lean_dec(v___x_2905_);
v___y_2892_ = v___y_2903_;
v___y_2893_ = v___y_2901_;
v___y_2894_ = v___y_2902_;
v___y_2895_ = v___y_2904_;
goto v___jp_2891_;
}
else
{
lean_object* v_inductiveVal_2906_; lean_object* v_toConstantVal_2907_; lean_object* v_env_2908_; lean_object* v_name_2909_; lean_object* v___x_2910_; uint8_t v___x_2911_; 
v_inductiveVal_2906_ = lean_ctor_get(v_ctx_2847_, 0);
v_toConstantVal_2907_ = lean_ctor_get(v_inductiveVal_2906_, 0);
v_env_2908_ = lean_ctor_get(v___x_2905_, 0);
lean_inc_ref(v_env_2908_);
lean_dec(v___x_2905_);
v_name_2909_ = lean_ctor_get(v_toConstantVal_2907_, 0);
v___x_2910_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__1));
v___x_2911_ = lean_name_eq(v_name_2909_, v___x_2910_);
if (v___x_2911_ == 0)
{
lean_dec_ref(v_env_2908_);
v___y_2892_ = v___y_2903_;
v___y_2893_ = v___y_2901_;
v___y_2894_ = v___y_2902_;
v___y_2895_ = v___y_2904_;
goto v___jp_2891_;
}
else
{
lean_object* v___x_2912_; uint8_t v___x_2913_; 
v___x_2912_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___closed__3));
v___x_2913_ = l_Lean_Environment_contains(v_env_2908_, v___x_2912_, v___x_2911_);
if (v___x_2913_ == 0)
{
v___y_2892_ = v___y_2903_;
v___y_2893_ = v___y_2901_;
v___y_2894_ = v___y_2902_;
v___y_2895_ = v___y_2904_;
goto v___jp_2891_;
}
else
{
v___y_2865_ = v___y_2903_;
v___y_2866_ = v___y_2902_;
v___y_2867_ = v___y_2901_;
v___y_2868_ = v___y_2904_;
v___y_2869_ = v___x_2912_;
goto v___jp_2864_;
}
}
}
}
}
else
{
lean_object* v_a_2961_; lean_object* v___x_2963_; uint8_t v_isShared_2964_; uint8_t v_isSharedCheck_2968_; 
lean_dec(v___y_2856_);
lean_dec_ref(v___y_2855_);
lean_dec(v___y_2854_);
lean_dec_ref(v___y_2853_);
lean_dec(v_interestingCtors_x3f_2852_);
lean_dec_ref(v_givenNames_2850_);
lean_dec(v_majorFVarId_2849_);
lean_dec(v_mvarId_2848_);
lean_dec_ref(v_ctx_2847_);
v_a_2961_ = lean_ctor_get(v___x_2860_, 0);
v_isSharedCheck_2968_ = !lean_is_exclusive(v___x_2860_);
if (v_isSharedCheck_2968_ == 0)
{
v___x_2963_ = v___x_2860_;
v_isShared_2964_ = v_isSharedCheck_2968_;
goto v_resetjp_2962_;
}
else
{
lean_inc(v_a_2961_);
lean_dec(v___x_2860_);
v___x_2963_ = lean_box(0);
v_isShared_2964_ = v_isSharedCheck_2968_;
goto v_resetjp_2962_;
}
v_resetjp_2962_:
{
lean_object* v___x_2966_; 
if (v_isShared_2964_ == 0)
{
v___x_2966_ = v___x_2963_;
goto v_reusejp_2965_;
}
else
{
lean_object* v_reuseFailAlloc_2967_; 
v_reuseFailAlloc_2967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2967_, 0, v_a_2961_);
v___x_2966_ = v_reuseFailAlloc_2967_;
goto v_reusejp_2965_;
}
v_reusejp_2965_:
{
return v___x_2966_;
}
}
}
}
else
{
lean_object* v_a_2969_; lean_object* v___x_2971_; uint8_t v_isShared_2972_; uint8_t v_isSharedCheck_2976_; 
lean_dec(v___y_2856_);
lean_dec_ref(v___y_2855_);
lean_dec(v___y_2854_);
lean_dec_ref(v___y_2853_);
lean_dec(v_interestingCtors_x3f_2852_);
lean_dec_ref(v_givenNames_2850_);
lean_dec(v_majorFVarId_2849_);
lean_dec(v_mvarId_2848_);
lean_dec_ref(v_ctx_2847_);
v_a_2969_ = lean_ctor_get(v___x_2858_, 0);
v_isSharedCheck_2976_ = !lean_is_exclusive(v___x_2858_);
if (v_isSharedCheck_2976_ == 0)
{
v___x_2971_ = v___x_2858_;
v_isShared_2972_ = v_isSharedCheck_2976_;
goto v_resetjp_2970_;
}
else
{
lean_inc(v_a_2969_);
lean_dec(v___x_2858_);
v___x_2971_ = lean_box(0);
v_isShared_2972_ = v_isSharedCheck_2976_;
goto v_resetjp_2970_;
}
v_resetjp_2970_:
{
lean_object* v___x_2974_; 
if (v_isShared_2972_ == 0)
{
v___x_2974_ = v___x_2971_;
goto v_reusejp_2973_;
}
else
{
lean_object* v_reuseFailAlloc_2975_; 
v_reuseFailAlloc_2975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2975_, 0, v_a_2969_);
v___x_2974_ = v_reuseFailAlloc_2975_;
goto v_reusejp_2973_;
}
v_reusejp_2973_:
{
return v___x_2974_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___boxed(lean_object* v___x_2977_, lean_object* v_ctx_2978_, lean_object* v_mvarId_2979_, lean_object* v_majorFVarId_2980_, lean_object* v_givenNames_2981_, lean_object* v_useNatCasesAuxOn_2982_, lean_object* v_interestingCtors_x3f_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_, lean_object* v___y_2988_){
_start:
{
uint8_t v_useNatCasesAuxOn_boxed_2989_; lean_object* v_res_2990_; 
v_useNatCasesAuxOn_boxed_2989_ = lean_unbox(v_useNatCasesAuxOn_2982_);
v_res_2990_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0(v___x_2977_, v_ctx_2978_, v_mvarId_2979_, v_majorFVarId_2980_, v_givenNames_2981_, v_useNatCasesAuxOn_boxed_2989_, v_interestingCtors_x3f_2983_, v___y_2984_, v___y_2985_, v___y_2986_, v___y_2987_);
return v_res_2990_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn(lean_object* v_mvarId_2991_, lean_object* v_majorFVarId_2992_, lean_object* v_givenNames_2993_, lean_object* v_ctx_2994_, uint8_t v_useNatCasesAuxOn_2995_, lean_object* v_interestingCtors_x3f_2996_, lean_object* v_a_2997_, lean_object* v_a_2998_, lean_object* v_a_2999_, lean_object* v_a_3000_){
_start:
{
lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___f_3004_; lean_object* v___x_3005_; 
lean_inc(v_majorFVarId_2992_);
v___x_3002_ = l_Lean_mkFVar(v_majorFVarId_2992_);
v___x_3003_ = lean_box(v_useNatCasesAuxOn_2995_);
lean_inc(v_mvarId_2991_);
v___f_3004_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lam__0___boxed), 12, 7);
lean_closure_set(v___f_3004_, 0, v___x_3002_);
lean_closure_set(v___f_3004_, 1, v_ctx_2994_);
lean_closure_set(v___f_3004_, 2, v_mvarId_2991_);
lean_closure_set(v___f_3004_, 3, v_majorFVarId_2992_);
lean_closure_set(v___f_3004_, 4, v_givenNames_2993_);
lean_closure_set(v___f_3004_, 5, v___x_3003_);
lean_closure_set(v___f_3004_, 6, v_interestingCtors_x3f_2996_);
v___x_3005_ = l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2___redArg(v_mvarId_2991_, v___f_3004_, v_a_2997_, v_a_2998_, v_a_2999_, v_a_3000_);
return v___x_3005_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___boxed(lean_object* v_mvarId_3006_, lean_object* v_majorFVarId_3007_, lean_object* v_givenNames_3008_, lean_object* v_ctx_3009_, lean_object* v_useNatCasesAuxOn_3010_, lean_object* v_interestingCtors_x3f_3011_, lean_object* v_a_3012_, lean_object* v_a_3013_, lean_object* v_a_3014_, lean_object* v_a_3015_, lean_object* v_a_3016_){
_start:
{
uint8_t v_useNatCasesAuxOn_boxed_3017_; lean_object* v_res_3018_; 
v_useNatCasesAuxOn_boxed_3017_ = lean_unbox(v_useNatCasesAuxOn_3010_);
v_res_3018_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn(v_mvarId_3006_, v_majorFVarId_3007_, v_givenNames_3008_, v_ctx_3009_, v_useNatCasesAuxOn_boxed_3017_, v_interestingCtors_x3f_3011_, v_a_3012_, v_a_3013_, v_a_3014_, v_a_3015_);
lean_dec(v_a_3015_);
lean_dec_ref(v_a_3014_);
lean_dec(v_a_3013_);
lean_dec_ref(v_a_3012_);
return v_res_3018_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0___closed__0(void){
_start:
{
lean_object* v___x_3019_; double v___x_3020_; 
v___x_3019_ = lean_unsigned_to_nat(0u);
v___x_3020_ = lean_float_of_nat(v___x_3019_);
return v___x_3020_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0(lean_object* v_cls_3024_, lean_object* v_msg_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_){
_start:
{
lean_object* v_ref_3031_; lean_object* v___x_3032_; lean_object* v_a_3033_; lean_object* v___x_3035_; uint8_t v_isShared_3036_; uint8_t v_isSharedCheck_3078_; 
v_ref_3031_ = lean_ctor_get(v___y_3028_, 2);
v___x_3032_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected_spec__0_spec__0(v_msg_3025_, v___y_3026_, v___y_3027_, v___y_3028_, v___y_3029_);
v_a_3033_ = lean_ctor_get(v___x_3032_, 0);
v_isSharedCheck_3078_ = !lean_is_exclusive(v___x_3032_);
if (v_isSharedCheck_3078_ == 0)
{
v___x_3035_ = v___x_3032_;
v_isShared_3036_ = v_isSharedCheck_3078_;
goto v_resetjp_3034_;
}
else
{
lean_inc(v_a_3033_);
lean_dec(v___x_3032_);
v___x_3035_ = lean_box(0);
v_isShared_3036_ = v_isSharedCheck_3078_;
goto v_resetjp_3034_;
}
v_resetjp_3034_:
{
lean_object* v___x_3037_; lean_object* v_traceState_3038_; lean_object* v_env_3039_; lean_object* v_nextMacroScope_3040_; lean_object* v_ngen_3041_; lean_object* v_auxDeclNGen_3042_; lean_object* v_cache_3043_; lean_object* v_recordedDeps_3044_; lean_object* v_messages_3045_; lean_object* v_infoState_3046_; lean_object* v_snapshotTasks_3047_; lean_object* v___x_3049_; uint8_t v_isShared_3050_; uint8_t v_isSharedCheck_3077_; 
v___x_3037_ = lean_st_ref_take(v___y_3029_);
v_traceState_3038_ = lean_ctor_get(v___x_3037_, 4);
v_env_3039_ = lean_ctor_get(v___x_3037_, 0);
v_nextMacroScope_3040_ = lean_ctor_get(v___x_3037_, 1);
v_ngen_3041_ = lean_ctor_get(v___x_3037_, 2);
v_auxDeclNGen_3042_ = lean_ctor_get(v___x_3037_, 3);
v_cache_3043_ = lean_ctor_get(v___x_3037_, 5);
v_recordedDeps_3044_ = lean_ctor_get(v___x_3037_, 6);
v_messages_3045_ = lean_ctor_get(v___x_3037_, 7);
v_infoState_3046_ = lean_ctor_get(v___x_3037_, 8);
v_snapshotTasks_3047_ = lean_ctor_get(v___x_3037_, 9);
v_isSharedCheck_3077_ = !lean_is_exclusive(v___x_3037_);
if (v_isSharedCheck_3077_ == 0)
{
v___x_3049_ = v___x_3037_;
v_isShared_3050_ = v_isSharedCheck_3077_;
goto v_resetjp_3048_;
}
else
{
lean_inc(v_snapshotTasks_3047_);
lean_inc(v_infoState_3046_);
lean_inc(v_messages_3045_);
lean_inc(v_recordedDeps_3044_);
lean_inc(v_cache_3043_);
lean_inc(v_traceState_3038_);
lean_inc(v_auxDeclNGen_3042_);
lean_inc(v_ngen_3041_);
lean_inc(v_nextMacroScope_3040_);
lean_inc(v_env_3039_);
lean_dec(v___x_3037_);
v___x_3049_ = lean_box(0);
v_isShared_3050_ = v_isSharedCheck_3077_;
goto v_resetjp_3048_;
}
v_resetjp_3048_:
{
uint64_t v_tid_3051_; lean_object* v_traces_3052_; lean_object* v___x_3054_; uint8_t v_isShared_3055_; uint8_t v_isSharedCheck_3076_; 
v_tid_3051_ = lean_ctor_get_uint64(v_traceState_3038_, sizeof(void*)*1);
v_traces_3052_ = lean_ctor_get(v_traceState_3038_, 0);
v_isSharedCheck_3076_ = !lean_is_exclusive(v_traceState_3038_);
if (v_isSharedCheck_3076_ == 0)
{
v___x_3054_ = v_traceState_3038_;
v_isShared_3055_ = v_isSharedCheck_3076_;
goto v_resetjp_3053_;
}
else
{
lean_inc(v_traces_3052_);
lean_dec(v_traceState_3038_);
v___x_3054_ = lean_box(0);
v_isShared_3055_ = v_isSharedCheck_3076_;
goto v_resetjp_3053_;
}
v_resetjp_3053_:
{
lean_object* v___x_3056_; lean_object* v___x_3057_; double v___x_3058_; uint8_t v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3067_; 
v___x_3056_ = lean_box(0);
v___x_3057_ = lean_box(0);
v___x_3058_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0___closed__0);
v___x_3059_ = 0;
v___x_3060_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0___closed__1));
v___x_3061_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3061_, 0, v_cls_3024_);
lean_ctor_set(v___x_3061_, 1, v___x_3057_);
lean_ctor_set(v___x_3061_, 2, v___x_3060_);
lean_ctor_set_float(v___x_3061_, sizeof(void*)*3, v___x_3058_);
lean_ctor_set_float(v___x_3061_, sizeof(void*)*3 + 8, v___x_3058_);
lean_ctor_set_uint8(v___x_3061_, sizeof(void*)*3 + 16, v___x_3059_);
v___x_3062_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0___closed__2));
v___x_3063_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3063_, 0, v___x_3061_);
lean_ctor_set(v___x_3063_, 1, v_a_3033_);
lean_ctor_set(v___x_3063_, 2, v___x_3062_);
lean_inc(v_ref_3031_);
v___x_3064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3064_, 0, v_ref_3031_);
lean_ctor_set(v___x_3064_, 1, v___x_3063_);
v___x_3065_ = l_Lean_PersistentArray_push___redArg(v_traces_3052_, v___x_3064_);
if (v_isShared_3055_ == 0)
{
lean_ctor_set(v___x_3054_, 0, v___x_3065_);
v___x_3067_ = v___x_3054_;
goto v_reusejp_3066_;
}
else
{
lean_object* v_reuseFailAlloc_3075_; 
v_reuseFailAlloc_3075_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3075_, 0, v___x_3065_);
lean_ctor_set_uint64(v_reuseFailAlloc_3075_, sizeof(void*)*1, v_tid_3051_);
v___x_3067_ = v_reuseFailAlloc_3075_;
goto v_reusejp_3066_;
}
v_reusejp_3066_:
{
lean_object* v___x_3069_; 
if (v_isShared_3050_ == 0)
{
lean_ctor_set(v___x_3049_, 4, v___x_3067_);
v___x_3069_ = v___x_3049_;
goto v_reusejp_3068_;
}
else
{
lean_object* v_reuseFailAlloc_3074_; 
v_reuseFailAlloc_3074_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3074_, 0, v_env_3039_);
lean_ctor_set(v_reuseFailAlloc_3074_, 1, v_nextMacroScope_3040_);
lean_ctor_set(v_reuseFailAlloc_3074_, 2, v_ngen_3041_);
lean_ctor_set(v_reuseFailAlloc_3074_, 3, v_auxDeclNGen_3042_);
lean_ctor_set(v_reuseFailAlloc_3074_, 4, v___x_3067_);
lean_ctor_set(v_reuseFailAlloc_3074_, 5, v_cache_3043_);
lean_ctor_set(v_reuseFailAlloc_3074_, 6, v_recordedDeps_3044_);
lean_ctor_set(v_reuseFailAlloc_3074_, 7, v_messages_3045_);
lean_ctor_set(v_reuseFailAlloc_3074_, 8, v_infoState_3046_);
lean_ctor_set(v_reuseFailAlloc_3074_, 9, v_snapshotTasks_3047_);
v___x_3069_ = v_reuseFailAlloc_3074_;
goto v_reusejp_3068_;
}
v_reusejp_3068_:
{
lean_object* v___x_3070_; lean_object* v___x_3072_; 
v___x_3070_ = lean_st_ref_put(v___y_3029_, v___x_3069_);
if (v_isShared_3036_ == 0)
{
lean_ctor_set(v___x_3035_, 0, v___x_3056_);
v___x_3072_ = v___x_3035_;
goto v_reusejp_3071_;
}
else
{
lean_object* v_reuseFailAlloc_3073_; 
v_reuseFailAlloc_3073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3073_, 0, v___x_3056_);
v___x_3072_ = v_reuseFailAlloc_3073_;
goto v_reusejp_3071_;
}
v_reusejp_3071_:
{
return v___x_3072_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0___boxed(lean_object* v_cls_3079_, lean_object* v_msg_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_){
_start:
{
lean_object* v_res_3086_; 
v_res_3086_ = l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0(v_cls_3079_, v_msg_3080_, v___y_3081_, v___y_3082_, v___y_3083_, v___y_3084_);
lean_dec(v___y_3084_);
lean_dec_ref(v___y_3083_);
lean_dec(v___y_3082_);
lean_dec_ref(v___y_3081_);
return v_res_3086_;
}
}
static lean_object* _init_l_Lean_Meta_Cases_cases___lam__0___closed__2(void){
_start:
{
lean_object* v___x_3090_; lean_object* v___x_3091_; 
v___x_3090_ = ((lean_object*)(l_Lean_Meta_Cases_cases___lam__0___closed__1));
v___x_3091_ = l_Lean_MessageData_ofFormat(v___x_3090_);
return v___x_3091_;
}
}
static lean_object* _init_l_Lean_Meta_Cases_cases___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3092_; lean_object* v___x_3093_; 
v___x_3092_ = lean_obj_once(&l_Lean_Meta_Cases_cases___lam__0___closed__2, &l_Lean_Meta_Cases_cases___lam__0___closed__2_once, _init_l_Lean_Meta_Cases_cases___lam__0___closed__2);
v___x_3093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3093_, 0, v___x_3092_);
return v___x_3093_;
}
}
static lean_object* _init_l_Lean_Meta_Cases_cases___lam__0___closed__9(void){
_start:
{
lean_object* v___x_3100_; lean_object* v___x_3101_; 
v___x_3100_ = ((lean_object*)(l_Lean_Meta_Cases_cases___lam__0___closed__8));
v___x_3101_ = l_Lean_stringToMessageData(v___x_3100_);
return v___x_3101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_cases___lam__0(lean_object* v_mvarId_3102_, lean_object* v___x_3103_, lean_object* v_majorFVarId_3104_, lean_object* v_givenNames_3105_, lean_object* v_interestingCtors_x3f_3106_, lean_object* v___x_3107_, uint8_t v_useNatCasesAuxOn_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_){
_start:
{
lean_object* v___x_3114_; 
lean_inc(v___x_3103_);
lean_inc(v_mvarId_3102_);
v___x_3114_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_3102_, v___x_3103_, v___y_3109_, v___y_3110_, v___y_3111_, v___y_3112_);
if (lean_obj_tag(v___x_3114_) == 0)
{
lean_object* v___x_3115_; 
lean_dec_ref_known(v___x_3114_, 1);
lean_inc(v_majorFVarId_3104_);
v___x_3115_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f(v_majorFVarId_3104_, v___y_3109_, v___y_3110_, v___y_3111_, v___y_3112_);
if (lean_obj_tag(v___x_3115_) == 0)
{
lean_object* v_a_3116_; 
v_a_3116_ = lean_ctor_get(v___x_3115_, 0);
lean_inc(v_a_3116_);
lean_dec_ref_known(v___x_3115_, 1);
if (lean_obj_tag(v_a_3116_) == 0)
{
lean_object* v___x_3117_; lean_object* v___x_3118_; 
lean_dec_ref(v___x_3107_);
lean_dec(v_interestingCtors_x3f_3106_);
lean_dec_ref(v_givenNames_3105_);
lean_dec(v_majorFVarId_3104_);
v___x_3117_ = lean_obj_once(&l_Lean_Meta_Cases_cases___lam__0___closed__3, &l_Lean_Meta_Cases_cases___lam__0___closed__3_once, _init_l_Lean_Meta_Cases_cases___lam__0___closed__3);
v___x_3118_ = l_Lean_Meta_throwTacticEx___redArg(v___x_3103_, v_mvarId_3102_, v___x_3117_, v___y_3109_, v___y_3110_, v___y_3111_, v___y_3112_);
return v___x_3118_;
}
else
{
lean_object* v_val_3119_; lean_object* v___x_3121_; uint8_t v_isShared_3122_; uint8_t v_isSharedCheck_3184_; 
lean_dec(v___x_3103_);
v_val_3119_ = lean_ctor_get(v_a_3116_, 0);
v_isSharedCheck_3184_ = !lean_is_exclusive(v_a_3116_);
if (v_isSharedCheck_3184_ == 0)
{
v___x_3121_ = v_a_3116_;
v_isShared_3122_ = v_isSharedCheck_3184_;
goto v_resetjp_3120_;
}
else
{
lean_inc(v_val_3119_);
lean_dec(v_a_3116_);
v___x_3121_ = lean_box(0);
v_isShared_3122_ = v_isSharedCheck_3184_;
goto v_resetjp_3120_;
}
v_resetjp_3120_:
{
lean_object* v___x_3123_; 
lean_inc(v_val_3119_);
v___x_3123_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices(v_val_3119_, v___y_3109_, v___y_3110_, v___y_3111_, v___y_3112_);
if (lean_obj_tag(v___x_3123_) == 0)
{
lean_object* v_a_3124_; uint8_t v___x_3125_; 
v_a_3124_ = lean_ctor_get(v___x_3123_, 0);
lean_inc(v_a_3124_);
lean_dec_ref_known(v___x_3123_, 1);
v___x_3125_ = lean_unbox(v_a_3124_);
if (v___x_3125_ == 0)
{
lean_object* v___x_3126_; 
v___x_3126_ = l_Lean_Meta_generalizeIndices(v_mvarId_3102_, v_majorFVarId_3104_, v___y_3109_, v___y_3110_, v___y_3111_, v___y_3112_);
if (lean_obj_tag(v___x_3126_) == 0)
{
lean_object* v_a_3127_; lean_object* v___y_3129_; lean_object* v___y_3130_; lean_object* v___y_3131_; lean_object* v___y_3132_; lean_object* v_toCold_3142_; lean_object* v_options_3143_; uint8_t v_hasTrace_3144_; 
v_a_3127_ = lean_ctor_get(v___x_3126_, 0);
lean_inc(v_a_3127_);
lean_dec_ref_known(v___x_3126_, 1);
v_toCold_3142_ = lean_ctor_get(v___y_3111_, 0);
v_options_3143_ = lean_ctor_get(v_toCold_3142_, 2);
v_hasTrace_3144_ = lean_ctor_get_uint8(v_options_3143_, sizeof(void*)*1);
if (v_hasTrace_3144_ == 0)
{
lean_del_object(v___x_3121_);
lean_dec_ref(v___x_3107_);
v___y_3129_ = v___y_3109_;
v___y_3130_ = v___y_3110_;
v___y_3131_ = v___y_3111_;
v___y_3132_ = v___y_3112_;
goto v___jp_3128_;
}
else
{
lean_object* v_inheritedTraceOptions_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; uint8_t v___x_3151_; 
v_inheritedTraceOptions_3145_ = lean_ctor_get(v_toCold_3142_, 11);
v___x_3146_ = ((lean_object*)(l_Lean_Meta_Cases_cases___lam__0___closed__4));
v___x_3147_ = ((lean_object*)(l_Lean_Meta_Cases_cases___lam__0___closed__5));
v___x_3148_ = l_Lean_Name_mkStr3(v___x_3146_, v___x_3147_, v___x_3107_);
v___x_3149_ = ((lean_object*)(l_Lean_Meta_Cases_cases___lam__0___closed__7));
lean_inc(v___x_3148_);
v___x_3150_ = l_Lean_Name_append(v___x_3149_, v___x_3148_);
v___x_3151_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3145_, v_options_3143_, v___x_3150_);
lean_dec(v___x_3150_);
if (v___x_3151_ == 0)
{
lean_dec(v___x_3148_);
lean_del_object(v___x_3121_);
v___y_3129_ = v___y_3109_;
v___y_3130_ = v___y_3110_;
v___y_3131_ = v___y_3111_;
v___y_3132_ = v___y_3112_;
goto v___jp_3128_;
}
else
{
lean_object* v_mvarId_3152_; lean_object* v___x_3153_; lean_object* v___x_3155_; 
v_mvarId_3152_ = lean_ctor_get(v_a_3127_, 0);
v___x_3153_ = lean_obj_once(&l_Lean_Meta_Cases_cases___lam__0___closed__9, &l_Lean_Meta_Cases_cases___lam__0___closed__9_once, _init_l_Lean_Meta_Cases_cases___lam__0___closed__9);
lean_inc(v_mvarId_3152_);
if (v_isShared_3122_ == 0)
{
lean_ctor_set(v___x_3121_, 0, v_mvarId_3152_);
v___x_3155_ = v___x_3121_;
goto v_reusejp_3154_;
}
else
{
lean_object* v_reuseFailAlloc_3166_; 
v_reuseFailAlloc_3166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3166_, 0, v_mvarId_3152_);
v___x_3155_ = v_reuseFailAlloc_3166_;
goto v_reusejp_3154_;
}
v_reusejp_3154_:
{
lean_object* v___x_3156_; lean_object* v___x_3157_; 
v___x_3156_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3156_, 0, v___x_3153_);
lean_ctor_set(v___x_3156_, 1, v___x_3155_);
v___x_3157_ = l_Lean_addTrace___at___00Lean_Meta_Cases_cases_spec__0(v___x_3148_, v___x_3156_, v___y_3109_, v___y_3110_, v___y_3111_, v___y_3112_);
if (lean_obj_tag(v___x_3157_) == 0)
{
lean_dec_ref_known(v___x_3157_, 1);
v___y_3129_ = v___y_3109_;
v___y_3130_ = v___y_3110_;
v___y_3131_ = v___y_3111_;
v___y_3132_ = v___y_3112_;
goto v___jp_3128_;
}
else
{
lean_object* v_a_3158_; lean_object* v___x_3160_; uint8_t v_isShared_3161_; uint8_t v_isSharedCheck_3165_; 
lean_dec(v_a_3127_);
lean_dec(v_a_3124_);
lean_dec(v_val_3119_);
lean_dec(v_interestingCtors_x3f_3106_);
lean_dec_ref(v_givenNames_3105_);
v_a_3158_ = lean_ctor_get(v___x_3157_, 0);
v_isSharedCheck_3165_ = !lean_is_exclusive(v___x_3157_);
if (v_isSharedCheck_3165_ == 0)
{
v___x_3160_ = v___x_3157_;
v_isShared_3161_ = v_isSharedCheck_3165_;
goto v_resetjp_3159_;
}
else
{
lean_inc(v_a_3158_);
lean_dec(v___x_3157_);
v___x_3160_ = lean_box(0);
v_isShared_3161_ = v_isSharedCheck_3165_;
goto v_resetjp_3159_;
}
v_resetjp_3159_:
{
lean_object* v___x_3163_; 
if (v_isShared_3161_ == 0)
{
v___x_3163_ = v___x_3160_;
goto v_reusejp_3162_;
}
else
{
lean_object* v_reuseFailAlloc_3164_; 
v_reuseFailAlloc_3164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3164_, 0, v_a_3158_);
v___x_3163_ = v_reuseFailAlloc_3164_;
goto v_reusejp_3162_;
}
v_reusejp_3162_:
{
return v___x_3163_;
}
}
}
}
}
}
v___jp_3128_:
{
lean_object* v_mvarId_3133_; lean_object* v_fvarId_3134_; lean_object* v_numEqs_3135_; uint8_t v___x_3136_; lean_object* v___x_3137_; 
v_mvarId_3133_ = lean_ctor_get(v_a_3127_, 0);
v_fvarId_3134_ = lean_ctor_get(v_a_3127_, 2);
v_numEqs_3135_ = lean_ctor_get(v_a_3127_, 3);
lean_inc(v_numEqs_3135_);
v___x_3136_ = lean_unbox(v_a_3124_);
lean_dec(v_a_3124_);
lean_inc(v_fvarId_3134_);
lean_inc(v_mvarId_3133_);
v___x_3137_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn(v_mvarId_3133_, v_fvarId_3134_, v_givenNames_3105_, v_val_3119_, v___x_3136_, v_interestingCtors_x3f_3106_, v___y_3129_, v___y_3130_, v___y_3131_, v___y_3132_);
if (lean_obj_tag(v___x_3137_) == 0)
{
lean_object* v_a_3138_; lean_object* v___x_3139_; 
v_a_3138_ = lean_ctor_get(v___x_3137_, 0);
lean_inc(v_a_3138_);
lean_dec_ref_known(v___x_3137_, 1);
v___x_3139_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices(v_a_3127_, v_a_3138_, v___y_3129_, v___y_3130_, v___y_3131_, v___y_3132_);
lean_dec(v_a_3127_);
if (lean_obj_tag(v___x_3139_) == 0)
{
lean_object* v_a_3140_; lean_object* v___x_3141_; 
v_a_3140_ = lean_ctor_get(v___x_3139_, 0);
lean_inc(v_a_3140_);
lean_dec_ref_known(v___x_3139_, 1);
v___x_3141_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs(v_numEqs_3135_, v_a_3140_, v___y_3129_, v___y_3130_, v___y_3131_, v___y_3132_);
lean_dec(v_a_3140_);
return v___x_3141_;
}
else
{
lean_dec(v_numEqs_3135_);
return v___x_3139_;
}
}
else
{
lean_dec(v_numEqs_3135_);
lean_dec(v_a_3127_);
return v___x_3137_;
}
}
}
else
{
lean_object* v_a_3167_; lean_object* v___x_3169_; uint8_t v_isShared_3170_; uint8_t v_isSharedCheck_3174_; 
lean_dec(v_a_3124_);
lean_del_object(v___x_3121_);
lean_dec(v_val_3119_);
lean_dec_ref(v___x_3107_);
lean_dec(v_interestingCtors_x3f_3106_);
lean_dec_ref(v_givenNames_3105_);
v_a_3167_ = lean_ctor_get(v___x_3126_, 0);
v_isSharedCheck_3174_ = !lean_is_exclusive(v___x_3126_);
if (v_isSharedCheck_3174_ == 0)
{
v___x_3169_ = v___x_3126_;
v_isShared_3170_ = v_isSharedCheck_3174_;
goto v_resetjp_3168_;
}
else
{
lean_inc(v_a_3167_);
lean_dec(v___x_3126_);
v___x_3169_ = lean_box(0);
v_isShared_3170_ = v_isSharedCheck_3174_;
goto v_resetjp_3168_;
}
v_resetjp_3168_:
{
lean_object* v___x_3172_; 
if (v_isShared_3170_ == 0)
{
v___x_3172_ = v___x_3169_;
goto v_reusejp_3171_;
}
else
{
lean_object* v_reuseFailAlloc_3173_; 
v_reuseFailAlloc_3173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3173_, 0, v_a_3167_);
v___x_3172_ = v_reuseFailAlloc_3173_;
goto v_reusejp_3171_;
}
v_reusejp_3171_:
{
return v___x_3172_;
}
}
}
}
else
{
lean_object* v___x_3175_; 
lean_dec(v_a_3124_);
lean_del_object(v___x_3121_);
lean_dec_ref(v___x_3107_);
v___x_3175_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn(v_mvarId_3102_, v_majorFVarId_3104_, v_givenNames_3105_, v_val_3119_, v_useNatCasesAuxOn_3108_, v_interestingCtors_x3f_3106_, v___y_3109_, v___y_3110_, v___y_3111_, v___y_3112_);
return v___x_3175_;
}
}
else
{
lean_object* v_a_3176_; lean_object* v___x_3178_; uint8_t v_isShared_3179_; uint8_t v_isSharedCheck_3183_; 
lean_del_object(v___x_3121_);
lean_dec(v_val_3119_);
lean_dec_ref(v___x_3107_);
lean_dec(v_interestingCtors_x3f_3106_);
lean_dec_ref(v_givenNames_3105_);
lean_dec(v_majorFVarId_3104_);
lean_dec(v_mvarId_3102_);
v_a_3176_ = lean_ctor_get(v___x_3123_, 0);
v_isSharedCheck_3183_ = !lean_is_exclusive(v___x_3123_);
if (v_isSharedCheck_3183_ == 0)
{
v___x_3178_ = v___x_3123_;
v_isShared_3179_ = v_isSharedCheck_3183_;
goto v_resetjp_3177_;
}
else
{
lean_inc(v_a_3176_);
lean_dec(v___x_3123_);
v___x_3178_ = lean_box(0);
v_isShared_3179_ = v_isSharedCheck_3183_;
goto v_resetjp_3177_;
}
v_resetjp_3177_:
{
lean_object* v___x_3181_; 
if (v_isShared_3179_ == 0)
{
v___x_3181_ = v___x_3178_;
goto v_reusejp_3180_;
}
else
{
lean_object* v_reuseFailAlloc_3182_; 
v_reuseFailAlloc_3182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3182_, 0, v_a_3176_);
v___x_3181_ = v_reuseFailAlloc_3182_;
goto v_reusejp_3180_;
}
v_reusejp_3180_:
{
return v___x_3181_;
}
}
}
}
}
}
else
{
lean_object* v_a_3185_; lean_object* v___x_3187_; uint8_t v_isShared_3188_; uint8_t v_isSharedCheck_3192_; 
lean_dec_ref(v___x_3107_);
lean_dec(v_interestingCtors_x3f_3106_);
lean_dec_ref(v_givenNames_3105_);
lean_dec(v_majorFVarId_3104_);
lean_dec(v___x_3103_);
lean_dec(v_mvarId_3102_);
v_a_3185_ = lean_ctor_get(v___x_3115_, 0);
v_isSharedCheck_3192_ = !lean_is_exclusive(v___x_3115_);
if (v_isSharedCheck_3192_ == 0)
{
v___x_3187_ = v___x_3115_;
v_isShared_3188_ = v_isSharedCheck_3192_;
goto v_resetjp_3186_;
}
else
{
lean_inc(v_a_3185_);
lean_dec(v___x_3115_);
v___x_3187_ = lean_box(0);
v_isShared_3188_ = v_isSharedCheck_3192_;
goto v_resetjp_3186_;
}
v_resetjp_3186_:
{
lean_object* v___x_3190_; 
if (v_isShared_3188_ == 0)
{
v___x_3190_ = v___x_3187_;
goto v_reusejp_3189_;
}
else
{
lean_object* v_reuseFailAlloc_3191_; 
v_reuseFailAlloc_3191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3191_, 0, v_a_3185_);
v___x_3190_ = v_reuseFailAlloc_3191_;
goto v_reusejp_3189_;
}
v_reusejp_3189_:
{
return v___x_3190_;
}
}
}
}
else
{
lean_object* v_a_3193_; lean_object* v___x_3195_; uint8_t v_isShared_3196_; uint8_t v_isSharedCheck_3200_; 
lean_dec_ref(v___x_3107_);
lean_dec(v_interestingCtors_x3f_3106_);
lean_dec_ref(v_givenNames_3105_);
lean_dec(v_majorFVarId_3104_);
lean_dec(v___x_3103_);
lean_dec(v_mvarId_3102_);
v_a_3193_ = lean_ctor_get(v___x_3114_, 0);
v_isSharedCheck_3200_ = !lean_is_exclusive(v___x_3114_);
if (v_isSharedCheck_3200_ == 0)
{
v___x_3195_ = v___x_3114_;
v_isShared_3196_ = v_isSharedCheck_3200_;
goto v_resetjp_3194_;
}
else
{
lean_inc(v_a_3193_);
lean_dec(v___x_3114_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_cases___lam__0___boxed(lean_object* v_mvarId_3201_, lean_object* v___x_3202_, lean_object* v_majorFVarId_3203_, lean_object* v_givenNames_3204_, lean_object* v_interestingCtors_x3f_3205_, lean_object* v___x_3206_, lean_object* v_useNatCasesAuxOn_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_){
_start:
{
uint8_t v_useNatCasesAuxOn_boxed_3213_; lean_object* v_res_3214_; 
v_useNatCasesAuxOn_boxed_3213_ = lean_unbox(v_useNatCasesAuxOn_3207_);
v_res_3214_ = l_Lean_Meta_Cases_cases___lam__0(v_mvarId_3201_, v___x_3202_, v_majorFVarId_3203_, v_givenNames_3204_, v_interestingCtors_x3f_3205_, v___x_3206_, v_useNatCasesAuxOn_boxed_3213_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_);
lean_dec(v___y_3211_);
lean_dec_ref(v___y_3210_);
lean_dec(v___y_3209_);
lean_dec_ref(v___y_3208_);
return v_res_3214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_cases(lean_object* v_mvarId_3218_, lean_object* v_majorFVarId_3219_, lean_object* v_givenNames_3220_, uint8_t v_useNatCasesAuxOn_3221_, lean_object* v_interestingCtors_x3f_3222_, lean_object* v_a_3223_, lean_object* v_a_3224_, lean_object* v_a_3225_, lean_object* v_a_3226_){
_start:
{
lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___f_3231_; lean_object* v___x_3232_; 
v___x_3228_ = ((lean_object*)(l_Lean_Meta_Cases_cases___closed__0));
v___x_3229_ = ((lean_object*)(l_Lean_Meta_Cases_cases___closed__1));
v___x_3230_ = lean_box(v_useNatCasesAuxOn_3221_);
lean_inc(v_mvarId_3218_);
v___f_3231_ = lean_alloc_closure((void*)(l_Lean_Meta_Cases_cases___lam__0___boxed), 12, 7);
lean_closure_set(v___f_3231_, 0, v_mvarId_3218_);
lean_closure_set(v___f_3231_, 1, v___x_3229_);
lean_closure_set(v___f_3231_, 2, v_majorFVarId_3219_);
lean_closure_set(v___f_3231_, 3, v_givenNames_3220_);
lean_closure_set(v___f_3231_, 4, v_interestingCtors_x3f_3222_);
lean_closure_set(v___f_3231_, 5, v___x_3228_);
lean_closure_set(v___f_3231_, 6, v___x_3230_);
v___x_3232_ = l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2___redArg(v_mvarId_3218_, v___f_3231_, v_a_3223_, v_a_3224_, v_a_3225_, v_a_3226_);
if (lean_obj_tag(v___x_3232_) == 0)
{
return v___x_3232_;
}
else
{
lean_object* v_a_3233_; uint8_t v___x_3234_; 
v_a_3233_ = lean_ctor_get(v___x_3232_, 0);
v___x_3234_ = l_Lean_Exception_isInterrupt(v_a_3233_);
if (v___x_3234_ == 0)
{
uint8_t v___x_3235_; 
lean_inc(v_a_3233_);
v___x_3235_ = l_Lean_Exception_isRuntime(v_a_3233_);
if (v___x_3235_ == 0)
{
lean_object* v___x_3236_; 
lean_inc(v_a_3233_);
lean_dec_ref_known(v___x_3232_, 1);
v___x_3236_ = l_Lean_Meta_throwNestedTacticEx___redArg(v___x_3229_, v_a_3233_, v_a_3223_, v_a_3224_, v_a_3225_, v_a_3226_);
return v___x_3236_;
}
else
{
return v___x_3232_;
}
}
else
{
return v___x_3232_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_cases___boxed(lean_object* v_mvarId_3237_, lean_object* v_majorFVarId_3238_, lean_object* v_givenNames_3239_, lean_object* v_useNatCasesAuxOn_3240_, lean_object* v_interestingCtors_x3f_3241_, lean_object* v_a_3242_, lean_object* v_a_3243_, lean_object* v_a_3244_, lean_object* v_a_3245_, lean_object* v_a_3246_){
_start:
{
uint8_t v_useNatCasesAuxOn_boxed_3247_; lean_object* v_res_3248_; 
v_useNatCasesAuxOn_boxed_3247_ = lean_unbox(v_useNatCasesAuxOn_3240_);
v_res_3248_ = l_Lean_Meta_Cases_cases(v_mvarId_3237_, v_majorFVarId_3238_, v_givenNames_3239_, v_useNatCasesAuxOn_boxed_3247_, v_interestingCtors_x3f_3241_, v_a_3242_, v_a_3243_, v_a_3244_, v_a_3245_);
lean_dec(v_a_3245_);
lean_dec_ref(v_a_3244_);
lean_dec(v_a_3243_);
lean_dec_ref(v_a_3242_);
return v_res_3248_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_cases(lean_object* v_mvarId_3249_, lean_object* v_majorFVarId_3250_, lean_object* v_givenNames_3251_, uint8_t v_useNatCasesAuxOn_3252_, lean_object* v_interestingCtors_x3f_3253_, lean_object* v_a_3254_, lean_object* v_a_3255_, lean_object* v_a_3256_, lean_object* v_a_3257_){
_start:
{
lean_object* v___x_3259_; 
v___x_3259_ = l_Lean_Meta_Cases_cases(v_mvarId_3249_, v_majorFVarId_3250_, v_givenNames_3251_, v_useNatCasesAuxOn_3252_, v_interestingCtors_x3f_3253_, v_a_3254_, v_a_3255_, v_a_3256_, v_a_3257_);
return v___x_3259_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_cases___boxed(lean_object* v_mvarId_3260_, lean_object* v_majorFVarId_3261_, lean_object* v_givenNames_3262_, lean_object* v_useNatCasesAuxOn_3263_, lean_object* v_interestingCtors_x3f_3264_, lean_object* v_a_3265_, lean_object* v_a_3266_, lean_object* v_a_3267_, lean_object* v_a_3268_, lean_object* v_a_3269_){
_start:
{
uint8_t v_useNatCasesAuxOn_boxed_3270_; lean_object* v_res_3271_; 
v_useNatCasesAuxOn_boxed_3270_ = lean_unbox(v_useNatCasesAuxOn_3263_);
v_res_3271_ = l_Lean_MVarId_cases(v_mvarId_3260_, v_majorFVarId_3261_, v_givenNames_3262_, v_useNatCasesAuxOn_boxed_3270_, v_interestingCtors_x3f_3264_, v_a_3265_, v_a_3266_, v_a_3267_, v_a_3268_);
lean_dec(v_a_3268_);
lean_dec_ref(v_a_3267_);
lean_dec(v_a_3266_);
lean_dec_ref(v_a_3265_);
return v_res_3271_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1___redArg(lean_object* v_x_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_){
_start:
{
lean_object* v___x_3278_; 
v___x_3278_ = l_Lean_Meta_saveState___redArg(v___y_3274_, v___y_3276_);
if (lean_obj_tag(v___x_3278_) == 0)
{
lean_object* v_a_3279_; lean_object* v___x_3280_; 
v_a_3279_ = lean_ctor_get(v___x_3278_, 0);
lean_inc(v_a_3279_);
lean_dec_ref_known(v___x_3278_, 1);
lean_inc(v___y_3276_);
lean_inc_ref(v___y_3275_);
lean_inc(v___y_3274_);
lean_inc_ref(v___y_3273_);
v___x_3280_ = lean_apply_5(v_x_3272_, v___y_3273_, v___y_3274_, v___y_3275_, v___y_3276_, lean_box(0));
if (lean_obj_tag(v___x_3280_) == 0)
{
lean_object* v_a_3281_; lean_object* v___x_3283_; uint8_t v_isShared_3284_; uint8_t v_isSharedCheck_3289_; 
lean_dec(v_a_3279_);
v_a_3281_ = lean_ctor_get(v___x_3280_, 0);
v_isSharedCheck_3289_ = !lean_is_exclusive(v___x_3280_);
if (v_isSharedCheck_3289_ == 0)
{
v___x_3283_ = v___x_3280_;
v_isShared_3284_ = v_isSharedCheck_3289_;
goto v_resetjp_3282_;
}
else
{
lean_inc(v_a_3281_);
lean_dec(v___x_3280_);
v___x_3283_ = lean_box(0);
v_isShared_3284_ = v_isSharedCheck_3289_;
goto v_resetjp_3282_;
}
v_resetjp_3282_:
{
lean_object* v___x_3285_; lean_object* v___x_3287_; 
v___x_3285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3285_, 0, v_a_3281_);
if (v_isShared_3284_ == 0)
{
lean_ctor_set(v___x_3283_, 0, v___x_3285_);
v___x_3287_ = v___x_3283_;
goto v_reusejp_3286_;
}
else
{
lean_object* v_reuseFailAlloc_3288_; 
v_reuseFailAlloc_3288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3288_, 0, v___x_3285_);
v___x_3287_ = v_reuseFailAlloc_3288_;
goto v_reusejp_3286_;
}
v_reusejp_3286_:
{
return v___x_3287_;
}
}
}
else
{
lean_object* v_a_3290_; lean_object* v___x_3292_; uint8_t v_isShared_3293_; uint8_t v_isSharedCheck_3320_; 
v_a_3290_ = lean_ctor_get(v___x_3280_, 0);
v_isSharedCheck_3320_ = !lean_is_exclusive(v___x_3280_);
if (v_isSharedCheck_3320_ == 0)
{
v___x_3292_ = v___x_3280_;
v_isShared_3293_ = v_isSharedCheck_3320_;
goto v_resetjp_3291_;
}
else
{
lean_inc(v_a_3290_);
lean_dec(v___x_3280_);
v___x_3292_ = lean_box(0);
v_isShared_3293_ = v_isSharedCheck_3320_;
goto v_resetjp_3291_;
}
v_resetjp_3291_:
{
uint8_t v___x_3294_; 
v___x_3294_ = l_Lean_Exception_isInterrupt(v_a_3290_);
if (v___x_3294_ == 0)
{
uint8_t v___x_3295_; 
lean_inc(v_a_3290_);
v___x_3295_ = l_Lean_Exception_isRuntime(v_a_3290_);
if (v___x_3295_ == 0)
{
lean_object* v___x_3296_; 
lean_del_object(v___x_3292_);
lean_dec(v_a_3290_);
v___x_3296_ = l_Lean_Meta_SavedState_restore___redArg(v_a_3279_, v___y_3274_, v___y_3276_);
if (lean_obj_tag(v___x_3296_) == 0)
{
lean_object* v___x_3298_; uint8_t v_isShared_3299_; uint8_t v_isSharedCheck_3304_; 
v_isSharedCheck_3304_ = !lean_is_exclusive(v___x_3296_);
if (v_isSharedCheck_3304_ == 0)
{
lean_object* v_unused_3305_; 
v_unused_3305_ = lean_ctor_get(v___x_3296_, 0);
lean_dec(v_unused_3305_);
v___x_3298_ = v___x_3296_;
v_isShared_3299_ = v_isSharedCheck_3304_;
goto v_resetjp_3297_;
}
else
{
lean_dec(v___x_3296_);
v___x_3298_ = lean_box(0);
v_isShared_3299_ = v_isSharedCheck_3304_;
goto v_resetjp_3297_;
}
v_resetjp_3297_:
{
lean_object* v___x_3300_; lean_object* v___x_3302_; 
v___x_3300_ = lean_box(0);
if (v_isShared_3299_ == 0)
{
lean_ctor_set(v___x_3298_, 0, v___x_3300_);
v___x_3302_ = v___x_3298_;
goto v_reusejp_3301_;
}
else
{
lean_object* v_reuseFailAlloc_3303_; 
v_reuseFailAlloc_3303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3303_, 0, v___x_3300_);
v___x_3302_ = v_reuseFailAlloc_3303_;
goto v_reusejp_3301_;
}
v_reusejp_3301_:
{
return v___x_3302_;
}
}
}
else
{
lean_object* v_a_3306_; lean_object* v___x_3308_; uint8_t v_isShared_3309_; uint8_t v_isSharedCheck_3313_; 
v_a_3306_ = lean_ctor_get(v___x_3296_, 0);
v_isSharedCheck_3313_ = !lean_is_exclusive(v___x_3296_);
if (v_isSharedCheck_3313_ == 0)
{
v___x_3308_ = v___x_3296_;
v_isShared_3309_ = v_isSharedCheck_3313_;
goto v_resetjp_3307_;
}
else
{
lean_inc(v_a_3306_);
lean_dec(v___x_3296_);
v___x_3308_ = lean_box(0);
v_isShared_3309_ = v_isSharedCheck_3313_;
goto v_resetjp_3307_;
}
v_resetjp_3307_:
{
lean_object* v___x_3311_; 
if (v_isShared_3309_ == 0)
{
v___x_3311_ = v___x_3308_;
goto v_reusejp_3310_;
}
else
{
lean_object* v_reuseFailAlloc_3312_; 
v_reuseFailAlloc_3312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3312_, 0, v_a_3306_);
v___x_3311_ = v_reuseFailAlloc_3312_;
goto v_reusejp_3310_;
}
v_reusejp_3310_:
{
return v___x_3311_;
}
}
}
}
else
{
lean_object* v___x_3315_; 
lean_dec(v_a_3279_);
if (v_isShared_3293_ == 0)
{
v___x_3315_ = v___x_3292_;
goto v_reusejp_3314_;
}
else
{
lean_object* v_reuseFailAlloc_3316_; 
v_reuseFailAlloc_3316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3316_, 0, v_a_3290_);
v___x_3315_ = v_reuseFailAlloc_3316_;
goto v_reusejp_3314_;
}
v_reusejp_3314_:
{
return v___x_3315_;
}
}
}
else
{
lean_object* v___x_3318_; 
lean_dec(v_a_3279_);
if (v_isShared_3293_ == 0)
{
v___x_3318_ = v___x_3292_;
goto v_reusejp_3317_;
}
else
{
lean_object* v_reuseFailAlloc_3319_; 
v_reuseFailAlloc_3319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3319_, 0, v_a_3290_);
v___x_3318_ = v_reuseFailAlloc_3319_;
goto v_reusejp_3317_;
}
v_reusejp_3317_:
{
return v___x_3318_;
}
}
}
}
}
else
{
lean_object* v_a_3321_; lean_object* v___x_3323_; uint8_t v_isShared_3324_; uint8_t v_isSharedCheck_3328_; 
lean_dec_ref(v_x_3272_);
v_a_3321_ = lean_ctor_get(v___x_3278_, 0);
v_isSharedCheck_3328_ = !lean_is_exclusive(v___x_3278_);
if (v_isSharedCheck_3328_ == 0)
{
v___x_3323_ = v___x_3278_;
v_isShared_3324_ = v_isSharedCheck_3328_;
goto v_resetjp_3322_;
}
else
{
lean_inc(v_a_3321_);
lean_dec(v___x_3278_);
v___x_3323_ = lean_box(0);
v_isShared_3324_ = v_isSharedCheck_3328_;
goto v_resetjp_3322_;
}
v_resetjp_3322_:
{
lean_object* v___x_3326_; 
if (v_isShared_3324_ == 0)
{
v___x_3326_ = v___x_3323_;
goto v_reusejp_3325_;
}
else
{
lean_object* v_reuseFailAlloc_3327_; 
v_reuseFailAlloc_3327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3327_, 0, v_a_3321_);
v___x_3326_ = v_reuseFailAlloc_3327_;
goto v_reusejp_3325_;
}
v_reusejp_3325_:
{
return v___x_3326_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1___redArg___boxed(lean_object* v_x_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_){
_start:
{
lean_object* v_res_3335_; 
v_res_3335_ = l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1___redArg(v_x_3329_, v___y_3330_, v___y_3331_, v___y_3332_, v___y_3333_);
lean_dec(v___y_3333_);
lean_dec_ref(v___y_3332_);
lean_dec(v___y_3331_);
lean_dec_ref(v___y_3330_);
return v_res_3335_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1(lean_object* v_00_u03b1_3336_, lean_object* v_x_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_){
_start:
{
lean_object* v___x_3343_; 
v___x_3343_ = l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1___redArg(v_x_3337_, v___y_3338_, v___y_3339_, v___y_3340_, v___y_3341_);
return v___x_3343_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1___boxed(lean_object* v_00_u03b1_3344_, lean_object* v_x_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_){
_start:
{
lean_object* v_res_3351_; 
v_res_3351_ = l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1(v_00_u03b1_3344_, v_x_3345_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_);
lean_dec(v___y_3349_);
lean_dec_ref(v___y_3348_);
lean_dec(v___y_3347_);
lean_dec_ref(v___y_3346_);
return v_res_3351_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_MVarId_casesRec_spec__0(lean_object* v_a_3352_, lean_object* v_a_3353_){
_start:
{
if (lean_obj_tag(v_a_3352_) == 0)
{
lean_object* v___x_3354_; 
v___x_3354_ = l_List_reverse___redArg(v_a_3353_);
return v___x_3354_;
}
else
{
lean_object* v_head_3355_; lean_object* v_toInductionSubgoal_3356_; lean_object* v_tail_3357_; lean_object* v___x_3359_; uint8_t v_isShared_3360_; uint8_t v_isSharedCheck_3366_; 
v_head_3355_ = lean_ctor_get(v_a_3352_, 0);
v_toInductionSubgoal_3356_ = lean_ctor_get(v_head_3355_, 0);
lean_inc_ref(v_toInductionSubgoal_3356_);
v_tail_3357_ = lean_ctor_get(v_a_3352_, 1);
v_isSharedCheck_3366_ = !lean_is_exclusive(v_a_3352_);
if (v_isSharedCheck_3366_ == 0)
{
lean_object* v_unused_3367_; 
v_unused_3367_ = lean_ctor_get(v_a_3352_, 0);
lean_dec(v_unused_3367_);
v___x_3359_ = v_a_3352_;
v_isShared_3360_ = v_isSharedCheck_3366_;
goto v_resetjp_3358_;
}
else
{
lean_inc(v_tail_3357_);
lean_dec(v_a_3352_);
v___x_3359_ = lean_box(0);
v_isShared_3360_ = v_isSharedCheck_3366_;
goto v_resetjp_3358_;
}
v_resetjp_3358_:
{
lean_object* v_mvarId_3361_; lean_object* v___x_3363_; 
v_mvarId_3361_ = lean_ctor_get(v_toInductionSubgoal_3356_, 0);
lean_inc(v_mvarId_3361_);
lean_dec_ref(v_toInductionSubgoal_3356_);
if (v_isShared_3360_ == 0)
{
lean_ctor_set(v___x_3359_, 1, v_a_3353_);
lean_ctor_set(v___x_3359_, 0, v_mvarId_3361_);
v___x_3363_ = v___x_3359_;
goto v_reusejp_3362_;
}
else
{
lean_object* v_reuseFailAlloc_3365_; 
v_reuseFailAlloc_3365_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3365_, 0, v_mvarId_3361_);
lean_ctor_set(v_reuseFailAlloc_3365_, 1, v_a_3353_);
v___x_3363_ = v_reuseFailAlloc_3365_;
goto v_reusejp_3362_;
}
v_reusejp_3362_:
{
v_a_3352_ = v_tail_3357_;
v_a_3353_ = v___x_3363_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3___lam__0(lean_object* v_mvarId_3368_, lean_object* v___x_3369_, lean_object* v___x_3370_, uint8_t v___x_3371_, lean_object* v___x_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_){
_start:
{
lean_object* v___x_3378_; 
v___x_3378_ = l_Lean_Meta_Cases_cases(v_mvarId_3368_, v___x_3369_, v___x_3370_, v___x_3371_, v___x_3372_, v___y_3373_, v___y_3374_, v___y_3375_, v___y_3376_);
if (lean_obj_tag(v___x_3378_) == 0)
{
lean_object* v_a_3379_; lean_object* v___x_3381_; uint8_t v_isShared_3382_; uint8_t v_isSharedCheck_3389_; 
v_a_3379_ = lean_ctor_get(v___x_3378_, 0);
v_isSharedCheck_3389_ = !lean_is_exclusive(v___x_3378_);
if (v_isSharedCheck_3389_ == 0)
{
v___x_3381_ = v___x_3378_;
v_isShared_3382_ = v_isSharedCheck_3389_;
goto v_resetjp_3380_;
}
else
{
lean_inc(v_a_3379_);
lean_dec(v___x_3378_);
v___x_3381_ = lean_box(0);
v_isShared_3382_ = v_isSharedCheck_3389_;
goto v_resetjp_3380_;
}
v_resetjp_3380_:
{
lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3387_; 
v___x_3383_ = lean_array_to_list(v_a_3379_);
v___x_3384_ = lean_box(0);
v___x_3385_ = l_List_mapTR_loop___at___00Lean_MVarId_casesRec_spec__0(v___x_3383_, v___x_3384_);
if (v_isShared_3382_ == 0)
{
lean_ctor_set(v___x_3381_, 0, v___x_3385_);
v___x_3387_ = v___x_3381_;
goto v_reusejp_3386_;
}
else
{
lean_object* v_reuseFailAlloc_3388_; 
v_reuseFailAlloc_3388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3388_, 0, v___x_3385_);
v___x_3387_ = v_reuseFailAlloc_3388_;
goto v_reusejp_3386_;
}
v_reusejp_3386_:
{
return v___x_3387_;
}
}
}
else
{
lean_object* v_a_3390_; lean_object* v___x_3392_; uint8_t v_isShared_3393_; uint8_t v_isSharedCheck_3397_; 
v_a_3390_ = lean_ctor_get(v___x_3378_, 0);
v_isSharedCheck_3397_ = !lean_is_exclusive(v___x_3378_);
if (v_isSharedCheck_3397_ == 0)
{
v___x_3392_ = v___x_3378_;
v_isShared_3393_ = v_isSharedCheck_3397_;
goto v_resetjp_3391_;
}
else
{
lean_inc(v_a_3390_);
lean_dec(v___x_3378_);
v___x_3392_ = lean_box(0);
v_isShared_3393_ = v_isSharedCheck_3397_;
goto v_resetjp_3391_;
}
v_resetjp_3391_:
{
lean_object* v___x_3395_; 
if (v_isShared_3393_ == 0)
{
v___x_3395_ = v___x_3392_;
goto v_reusejp_3394_;
}
else
{
lean_object* v_reuseFailAlloc_3396_; 
v_reuseFailAlloc_3396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3396_, 0, v_a_3390_);
v___x_3395_ = v_reuseFailAlloc_3396_;
goto v_reusejp_3394_;
}
v_reusejp_3394_:
{
return v___x_3395_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3___lam__0___boxed(lean_object* v_mvarId_3398_, lean_object* v___x_3399_, lean_object* v___x_3400_, lean_object* v___x_3401_, lean_object* v___x_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_){
_start:
{
uint8_t v___x_6231__boxed_3408_; lean_object* v_res_3409_; 
v___x_6231__boxed_3408_ = lean_unbox(v___x_3401_);
v_res_3409_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3___lam__0(v_mvarId_3398_, v___x_3399_, v___x_3400_, v___x_6231__boxed_3408_, v___x_3402_, v___y_3403_, v___y_3404_, v___y_3405_, v___y_3406_);
lean_dec(v___y_3406_);
lean_dec_ref(v___y_3405_);
lean_dec(v___y_3404_);
lean_dec_ref(v___y_3403_);
return v_res_3409_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5(lean_object* v_p_3415_, lean_object* v_mvarId_3416_, lean_object* v_as_3417_, size_t v_sz_3418_, size_t v_i_3419_, lean_object* v_b_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_){
_start:
{
uint8_t v___x_3426_; 
v___x_3426_ = lean_usize_dec_lt(v_i_3419_, v_sz_3418_);
if (v___x_3426_ == 0)
{
lean_object* v___x_3427_; 
lean_dec(v_mvarId_3416_);
lean_dec_ref(v_p_3415_);
v___x_3427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3427_, 0, v_b_3420_);
return v___x_3427_;
}
else
{
lean_object* v_snd_3428_; lean_object* v___x_3430_; uint8_t v_isShared_3431_; uint8_t v_isSharedCheck_3496_; 
v_snd_3428_ = lean_ctor_get(v_b_3420_, 1);
v_isSharedCheck_3496_ = !lean_is_exclusive(v_b_3420_);
if (v_isSharedCheck_3496_ == 0)
{
lean_object* v_unused_3497_; 
v_unused_3497_ = lean_ctor_get(v_b_3420_, 0);
lean_dec(v_unused_3497_);
v___x_3430_ = v_b_3420_;
v_isShared_3431_ = v_isSharedCheck_3496_;
goto v_resetjp_3429_;
}
else
{
lean_inc(v_snd_3428_);
lean_dec(v_b_3420_);
v___x_3430_ = lean_box(0);
v_isShared_3431_ = v_isSharedCheck_3496_;
goto v_resetjp_3429_;
}
v_resetjp_3429_:
{
lean_object* v___x_3432_; lean_object* v_a_3434_; lean_object* v_a_3441_; 
v___x_3432_ = lean_box(0);
v_a_3441_ = lean_array_uget(v_as_3417_, v_i_3419_);
if (lean_obj_tag(v_a_3441_) == 0)
{
v_a_3434_ = v_snd_3428_;
goto v___jp_3433_;
}
else
{
lean_object* v_val_3442_; lean_object* v___x_3444_; uint8_t v_isShared_3445_; uint8_t v_isSharedCheck_3495_; 
v_val_3442_ = lean_ctor_get(v_a_3441_, 0);
v_isSharedCheck_3495_ = !lean_is_exclusive(v_a_3441_);
if (v_isSharedCheck_3495_ == 0)
{
v___x_3444_ = v_a_3441_;
v_isShared_3445_ = v_isSharedCheck_3495_;
goto v_resetjp_3443_;
}
else
{
lean_inc(v_val_3442_);
lean_dec(v_a_3441_);
v___x_3444_ = lean_box(0);
v_isShared_3445_ = v_isSharedCheck_3495_;
goto v_resetjp_3443_;
}
v_resetjp_3443_:
{
lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; 
v___x_3446_ = lean_box(0);
v___x_3447_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5___closed__0));
lean_inc_ref(v_p_3415_);
lean_inc(v___y_3424_);
lean_inc_ref(v___y_3423_);
lean_inc(v___y_3422_);
lean_inc_ref(v___y_3421_);
lean_inc(v_val_3442_);
v___x_3448_ = lean_apply_6(v_p_3415_, v_val_3442_, v___y_3421_, v___y_3422_, v___y_3423_, v___y_3424_, lean_box(0));
if (lean_obj_tag(v___x_3448_) == 0)
{
lean_object* v_a_3449_; uint8_t v___x_3450_; 
v_a_3449_ = lean_ctor_get(v___x_3448_, 0);
lean_inc(v_a_3449_);
lean_dec_ref_known(v___x_3448_, 1);
v___x_3450_ = lean_unbox(v_a_3449_);
lean_dec(v_a_3449_);
if (v___x_3450_ == 0)
{
lean_del_object(v___x_3444_);
lean_dec(v_val_3442_);
lean_dec(v_snd_3428_);
v_a_3434_ = v___x_3447_;
goto v___jp_3433_;
}
else
{
lean_object* v___x_3451_; lean_object* v___x_3452_; uint8_t v___x_3453_; lean_object* v___x_3454_; lean_object* v___f_3455_; lean_object* v___x_3456_; 
v___x_3451_ = l_Lean_LocalDecl_fvarId(v_val_3442_);
lean_dec(v_val_3442_);
v___x_3452_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5___closed__1));
v___x_3453_ = 0;
v___x_3454_ = lean_box(v___x_3453_);
lean_inc(v_mvarId_3416_);
v___f_3455_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3___lam__0___boxed), 10, 5);
lean_closure_set(v___f_3455_, 0, v_mvarId_3416_);
lean_closure_set(v___f_3455_, 1, v___x_3451_);
lean_closure_set(v___f_3455_, 2, v___x_3452_);
lean_closure_set(v___f_3455_, 3, v___x_3454_);
lean_closure_set(v___f_3455_, 4, v___x_3432_);
v___x_3456_ = l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1___redArg(v___f_3455_, v___y_3421_, v___y_3422_, v___y_3423_, v___y_3424_);
if (lean_obj_tag(v___x_3456_) == 0)
{
lean_object* v_a_3457_; lean_object* v___x_3459_; uint8_t v_isShared_3460_; uint8_t v_isSharedCheck_3478_; 
v_a_3457_ = lean_ctor_get(v___x_3456_, 0);
v_isSharedCheck_3478_ = !lean_is_exclusive(v___x_3456_);
if (v_isSharedCheck_3478_ == 0)
{
v___x_3459_ = v___x_3456_;
v_isShared_3460_ = v_isSharedCheck_3478_;
goto v_resetjp_3458_;
}
else
{
lean_inc(v_a_3457_);
lean_dec(v___x_3456_);
v___x_3459_ = lean_box(0);
v_isShared_3460_ = v_isSharedCheck_3478_;
goto v_resetjp_3458_;
}
v_resetjp_3458_:
{
if (lean_obj_tag(v_a_3457_) == 0)
{
lean_del_object(v___x_3459_);
lean_del_object(v___x_3444_);
lean_dec(v_snd_3428_);
v_a_3434_ = v___x_3447_;
goto v___jp_3433_;
}
else
{
lean_object* v___x_3462_; 
lean_del_object(v___x_3430_);
lean_dec(v_mvarId_3416_);
lean_dec_ref(v_p_3415_);
lean_inc_ref(v_a_3457_);
if (v_isShared_3445_ == 0)
{
lean_ctor_set(v___x_3444_, 0, v_a_3457_);
v___x_3462_ = v___x_3444_;
goto v_reusejp_3461_;
}
else
{
lean_object* v_reuseFailAlloc_3477_; 
v_reuseFailAlloc_3477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3477_, 0, v_a_3457_);
v___x_3462_ = v_reuseFailAlloc_3477_;
goto v_reusejp_3461_;
}
v_reusejp_3461_:
{
lean_object* v___x_3464_; uint8_t v_isShared_3465_; uint8_t v_isSharedCheck_3475_; 
v_isSharedCheck_3475_ = !lean_is_exclusive(v_a_3457_);
if (v_isSharedCheck_3475_ == 0)
{
lean_object* v_unused_3476_; 
v_unused_3476_ = lean_ctor_get(v_a_3457_, 0);
lean_dec(v_unused_3476_);
v___x_3464_ = v_a_3457_;
v_isShared_3465_ = v_isSharedCheck_3475_;
goto v_resetjp_3463_;
}
else
{
lean_dec(v_a_3457_);
v___x_3464_ = lean_box(0);
v_isShared_3465_ = v_isSharedCheck_3475_;
goto v_resetjp_3463_;
}
v_resetjp_3463_:
{
lean_object* v___x_3466_; lean_object* v___x_3468_; 
v___x_3466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3466_, 0, v___x_3462_);
lean_ctor_set(v___x_3466_, 1, v___x_3446_);
if (v_isShared_3465_ == 0)
{
lean_ctor_set_tag(v___x_3464_, 0);
lean_ctor_set(v___x_3464_, 0, v___x_3466_);
v___x_3468_ = v___x_3464_;
goto v_reusejp_3467_;
}
else
{
lean_object* v_reuseFailAlloc_3474_; 
v_reuseFailAlloc_3474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3474_, 0, v___x_3466_);
v___x_3468_ = v_reuseFailAlloc_3474_;
goto v_reusejp_3467_;
}
v_reusejp_3467_:
{
lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3472_; 
v___x_3469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3469_, 0, v___x_3468_);
v___x_3470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3470_, 0, v___x_3469_);
lean_ctor_set(v___x_3470_, 1, v_snd_3428_);
if (v_isShared_3460_ == 0)
{
lean_ctor_set(v___x_3459_, 0, v___x_3470_);
v___x_3472_ = v___x_3459_;
goto v_reusejp_3471_;
}
else
{
lean_object* v_reuseFailAlloc_3473_; 
v_reuseFailAlloc_3473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3473_, 0, v___x_3470_);
v___x_3472_ = v_reuseFailAlloc_3473_;
goto v_reusejp_3471_;
}
v_reusejp_3471_:
{
return v___x_3472_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3479_; lean_object* v___x_3481_; uint8_t v_isShared_3482_; uint8_t v_isSharedCheck_3486_; 
lean_del_object(v___x_3444_);
lean_del_object(v___x_3430_);
lean_dec(v_snd_3428_);
lean_dec(v_mvarId_3416_);
lean_dec_ref(v_p_3415_);
v_a_3479_ = lean_ctor_get(v___x_3456_, 0);
v_isSharedCheck_3486_ = !lean_is_exclusive(v___x_3456_);
if (v_isSharedCheck_3486_ == 0)
{
v___x_3481_ = v___x_3456_;
v_isShared_3482_ = v_isSharedCheck_3486_;
goto v_resetjp_3480_;
}
else
{
lean_inc(v_a_3479_);
lean_dec(v___x_3456_);
v___x_3481_ = lean_box(0);
v_isShared_3482_ = v_isSharedCheck_3486_;
goto v_resetjp_3480_;
}
v_resetjp_3480_:
{
lean_object* v___x_3484_; 
if (v_isShared_3482_ == 0)
{
v___x_3484_ = v___x_3481_;
goto v_reusejp_3483_;
}
else
{
lean_object* v_reuseFailAlloc_3485_; 
v_reuseFailAlloc_3485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3485_, 0, v_a_3479_);
v___x_3484_ = v_reuseFailAlloc_3485_;
goto v_reusejp_3483_;
}
v_reusejp_3483_:
{
return v___x_3484_;
}
}
}
}
}
else
{
lean_object* v_a_3487_; lean_object* v___x_3489_; uint8_t v_isShared_3490_; uint8_t v_isSharedCheck_3494_; 
lean_del_object(v___x_3444_);
lean_dec(v_val_3442_);
lean_del_object(v___x_3430_);
lean_dec(v_snd_3428_);
lean_dec(v_mvarId_3416_);
lean_dec_ref(v_p_3415_);
v_a_3487_ = lean_ctor_get(v___x_3448_, 0);
v_isSharedCheck_3494_ = !lean_is_exclusive(v___x_3448_);
if (v_isSharedCheck_3494_ == 0)
{
v___x_3489_ = v___x_3448_;
v_isShared_3490_ = v_isSharedCheck_3494_;
goto v_resetjp_3488_;
}
else
{
lean_inc(v_a_3487_);
lean_dec(v___x_3448_);
v___x_3489_ = lean_box(0);
v_isShared_3490_ = v_isSharedCheck_3494_;
goto v_resetjp_3488_;
}
v_resetjp_3488_:
{
lean_object* v___x_3492_; 
if (v_isShared_3490_ == 0)
{
v___x_3492_ = v___x_3489_;
goto v_reusejp_3491_;
}
else
{
lean_object* v_reuseFailAlloc_3493_; 
v_reuseFailAlloc_3493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3493_, 0, v_a_3487_);
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
v___jp_3433_:
{
lean_object* v___x_3436_; 
if (v_isShared_3431_ == 0)
{
lean_ctor_set(v___x_3430_, 1, v_a_3434_);
lean_ctor_set(v___x_3430_, 0, v___x_3432_);
v___x_3436_ = v___x_3430_;
goto v_reusejp_3435_;
}
else
{
lean_object* v_reuseFailAlloc_3440_; 
v_reuseFailAlloc_3440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3440_, 0, v___x_3432_);
lean_ctor_set(v_reuseFailAlloc_3440_, 1, v_a_3434_);
v___x_3436_ = v_reuseFailAlloc_3440_;
goto v_reusejp_3435_;
}
v_reusejp_3435_:
{
size_t v___x_3437_; size_t v___x_3438_; 
v___x_3437_ = ((size_t)1ULL);
v___x_3438_ = lean_usize_add(v_i_3419_, v___x_3437_);
v_i_3419_ = v___x_3438_;
v_b_3420_ = v___x_3436_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5___boxed(lean_object* v_p_3498_, lean_object* v_mvarId_3499_, lean_object* v_as_3500_, lean_object* v_sz_3501_, lean_object* v_i_3502_, lean_object* v_b_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_, lean_object* v___y_3508_){
_start:
{
size_t v_sz_boxed_3509_; size_t v_i_boxed_3510_; lean_object* v_res_3511_; 
v_sz_boxed_3509_ = lean_unbox_usize(v_sz_3501_);
lean_dec(v_sz_3501_);
v_i_boxed_3510_ = lean_unbox_usize(v_i_3502_);
lean_dec(v_i_3502_);
v_res_3511_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5(v_p_3498_, v_mvarId_3499_, v_as_3500_, v_sz_boxed_3509_, v_i_boxed_3510_, v_b_3503_, v___y_3504_, v___y_3505_, v___y_3506_, v___y_3507_);
lean_dec(v___y_3507_);
lean_dec_ref(v___y_3506_);
lean_dec(v___y_3505_);
lean_dec_ref(v___y_3504_);
lean_dec_ref(v_as_3500_);
return v_res_3511_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4(lean_object* v_p_3512_, lean_object* v_mvarId_3513_, lean_object* v_as_3514_, size_t v_sz_3515_, size_t v_i_3516_, lean_object* v_b_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_, lean_object* v___y_3521_){
_start:
{
uint8_t v___x_3523_; 
v___x_3523_ = lean_usize_dec_lt(v_i_3516_, v_sz_3515_);
if (v___x_3523_ == 0)
{
lean_object* v___x_3524_; 
lean_dec(v_mvarId_3513_);
lean_dec_ref(v_p_3512_);
v___x_3524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3524_, 0, v_b_3517_);
return v___x_3524_;
}
else
{
lean_object* v_snd_3525_; lean_object* v___x_3527_; uint8_t v_isShared_3528_; uint8_t v_isSharedCheck_3593_; 
v_snd_3525_ = lean_ctor_get(v_b_3517_, 1);
v_isSharedCheck_3593_ = !lean_is_exclusive(v_b_3517_);
if (v_isSharedCheck_3593_ == 0)
{
lean_object* v_unused_3594_; 
v_unused_3594_ = lean_ctor_get(v_b_3517_, 0);
lean_dec(v_unused_3594_);
v___x_3527_ = v_b_3517_;
v_isShared_3528_ = v_isSharedCheck_3593_;
goto v_resetjp_3526_;
}
else
{
lean_inc(v_snd_3525_);
lean_dec(v_b_3517_);
v___x_3527_ = lean_box(0);
v_isShared_3528_ = v_isSharedCheck_3593_;
goto v_resetjp_3526_;
}
v_resetjp_3526_:
{
lean_object* v___x_3529_; lean_object* v_a_3531_; lean_object* v_a_3538_; 
v___x_3529_ = lean_box(0);
v_a_3538_ = lean_array_uget(v_as_3514_, v_i_3516_);
if (lean_obj_tag(v_a_3538_) == 0)
{
v_a_3531_ = v_snd_3525_;
goto v___jp_3530_;
}
else
{
lean_object* v_val_3539_; lean_object* v___x_3541_; uint8_t v_isShared_3542_; uint8_t v_isSharedCheck_3592_; 
v_val_3539_ = lean_ctor_get(v_a_3538_, 0);
v_isSharedCheck_3592_ = !lean_is_exclusive(v_a_3538_);
if (v_isSharedCheck_3592_ == 0)
{
v___x_3541_ = v_a_3538_;
v_isShared_3542_ = v_isSharedCheck_3592_;
goto v_resetjp_3540_;
}
else
{
lean_inc(v_val_3539_);
lean_dec(v_a_3538_);
v___x_3541_ = lean_box(0);
v_isShared_3542_ = v_isSharedCheck_3592_;
goto v_resetjp_3540_;
}
v_resetjp_3540_:
{
lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; 
v___x_3543_ = lean_box(0);
v___x_3544_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5___closed__0));
lean_inc_ref(v_p_3512_);
lean_inc(v___y_3521_);
lean_inc_ref(v___y_3520_);
lean_inc(v___y_3519_);
lean_inc_ref(v___y_3518_);
lean_inc(v_val_3539_);
v___x_3545_ = lean_apply_6(v_p_3512_, v_val_3539_, v___y_3518_, v___y_3519_, v___y_3520_, v___y_3521_, lean_box(0));
if (lean_obj_tag(v___x_3545_) == 0)
{
lean_object* v_a_3546_; uint8_t v___x_3547_; 
v_a_3546_ = lean_ctor_get(v___x_3545_, 0);
lean_inc(v_a_3546_);
lean_dec_ref_known(v___x_3545_, 1);
v___x_3547_ = lean_unbox(v_a_3546_);
lean_dec(v_a_3546_);
if (v___x_3547_ == 0)
{
lean_del_object(v___x_3541_);
lean_dec(v_val_3539_);
lean_dec(v_snd_3525_);
v_a_3531_ = v___x_3544_;
goto v___jp_3530_;
}
else
{
lean_object* v___x_3548_; lean_object* v___x_3549_; uint8_t v___x_3550_; lean_object* v___x_3551_; lean_object* v___f_3552_; lean_object* v___x_3553_; 
v___x_3548_ = l_Lean_LocalDecl_fvarId(v_val_3539_);
lean_dec(v_val_3539_);
v___x_3549_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5___closed__1));
v___x_3550_ = 0;
v___x_3551_ = lean_box(v___x_3550_);
lean_inc(v_mvarId_3513_);
v___f_3552_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3___lam__0___boxed), 10, 5);
lean_closure_set(v___f_3552_, 0, v_mvarId_3513_);
lean_closure_set(v___f_3552_, 1, v___x_3548_);
lean_closure_set(v___f_3552_, 2, v___x_3549_);
lean_closure_set(v___f_3552_, 3, v___x_3551_);
lean_closure_set(v___f_3552_, 4, v___x_3529_);
v___x_3553_ = l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1___redArg(v___f_3552_, v___y_3518_, v___y_3519_, v___y_3520_, v___y_3521_);
if (lean_obj_tag(v___x_3553_) == 0)
{
lean_object* v_a_3554_; lean_object* v___x_3556_; uint8_t v_isShared_3557_; uint8_t v_isSharedCheck_3575_; 
v_a_3554_ = lean_ctor_get(v___x_3553_, 0);
v_isSharedCheck_3575_ = !lean_is_exclusive(v___x_3553_);
if (v_isSharedCheck_3575_ == 0)
{
v___x_3556_ = v___x_3553_;
v_isShared_3557_ = v_isSharedCheck_3575_;
goto v_resetjp_3555_;
}
else
{
lean_inc(v_a_3554_);
lean_dec(v___x_3553_);
v___x_3556_ = lean_box(0);
v_isShared_3557_ = v_isSharedCheck_3575_;
goto v_resetjp_3555_;
}
v_resetjp_3555_:
{
if (lean_obj_tag(v_a_3554_) == 0)
{
lean_del_object(v___x_3556_);
lean_del_object(v___x_3541_);
lean_dec(v_snd_3525_);
v_a_3531_ = v___x_3544_;
goto v___jp_3530_;
}
else
{
lean_object* v___x_3559_; 
lean_del_object(v___x_3527_);
lean_dec(v_mvarId_3513_);
lean_dec_ref(v_p_3512_);
lean_inc_ref(v_a_3554_);
if (v_isShared_3542_ == 0)
{
lean_ctor_set(v___x_3541_, 0, v_a_3554_);
v___x_3559_ = v___x_3541_;
goto v_reusejp_3558_;
}
else
{
lean_object* v_reuseFailAlloc_3574_; 
v_reuseFailAlloc_3574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3574_, 0, v_a_3554_);
v___x_3559_ = v_reuseFailAlloc_3574_;
goto v_reusejp_3558_;
}
v_reusejp_3558_:
{
lean_object* v___x_3561_; uint8_t v_isShared_3562_; uint8_t v_isSharedCheck_3572_; 
v_isSharedCheck_3572_ = !lean_is_exclusive(v_a_3554_);
if (v_isSharedCheck_3572_ == 0)
{
lean_object* v_unused_3573_; 
v_unused_3573_ = lean_ctor_get(v_a_3554_, 0);
lean_dec(v_unused_3573_);
v___x_3561_ = v_a_3554_;
v_isShared_3562_ = v_isSharedCheck_3572_;
goto v_resetjp_3560_;
}
else
{
lean_dec(v_a_3554_);
v___x_3561_ = lean_box(0);
v_isShared_3562_ = v_isSharedCheck_3572_;
goto v_resetjp_3560_;
}
v_resetjp_3560_:
{
lean_object* v___x_3563_; lean_object* v___x_3565_; 
v___x_3563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3563_, 0, v___x_3559_);
lean_ctor_set(v___x_3563_, 1, v___x_3543_);
if (v_isShared_3562_ == 0)
{
lean_ctor_set_tag(v___x_3561_, 0);
lean_ctor_set(v___x_3561_, 0, v___x_3563_);
v___x_3565_ = v___x_3561_;
goto v_reusejp_3564_;
}
else
{
lean_object* v_reuseFailAlloc_3571_; 
v_reuseFailAlloc_3571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3571_, 0, v___x_3563_);
v___x_3565_ = v_reuseFailAlloc_3571_;
goto v_reusejp_3564_;
}
v_reusejp_3564_:
{
lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3569_; 
v___x_3566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3566_, 0, v___x_3565_);
v___x_3567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3567_, 0, v___x_3566_);
lean_ctor_set(v___x_3567_, 1, v_snd_3525_);
if (v_isShared_3557_ == 0)
{
lean_ctor_set(v___x_3556_, 0, v___x_3567_);
v___x_3569_ = v___x_3556_;
goto v_reusejp_3568_;
}
else
{
lean_object* v_reuseFailAlloc_3570_; 
v_reuseFailAlloc_3570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3570_, 0, v___x_3567_);
v___x_3569_ = v_reuseFailAlloc_3570_;
goto v_reusejp_3568_;
}
v_reusejp_3568_:
{
return v___x_3569_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3576_; lean_object* v___x_3578_; uint8_t v_isShared_3579_; uint8_t v_isSharedCheck_3583_; 
lean_del_object(v___x_3541_);
lean_del_object(v___x_3527_);
lean_dec(v_snd_3525_);
lean_dec(v_mvarId_3513_);
lean_dec_ref(v_p_3512_);
v_a_3576_ = lean_ctor_get(v___x_3553_, 0);
v_isSharedCheck_3583_ = !lean_is_exclusive(v___x_3553_);
if (v_isSharedCheck_3583_ == 0)
{
v___x_3578_ = v___x_3553_;
v_isShared_3579_ = v_isSharedCheck_3583_;
goto v_resetjp_3577_;
}
else
{
lean_inc(v_a_3576_);
lean_dec(v___x_3553_);
v___x_3578_ = lean_box(0);
v_isShared_3579_ = v_isSharedCheck_3583_;
goto v_resetjp_3577_;
}
v_resetjp_3577_:
{
lean_object* v___x_3581_; 
if (v_isShared_3579_ == 0)
{
v___x_3581_ = v___x_3578_;
goto v_reusejp_3580_;
}
else
{
lean_object* v_reuseFailAlloc_3582_; 
v_reuseFailAlloc_3582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3582_, 0, v_a_3576_);
v___x_3581_ = v_reuseFailAlloc_3582_;
goto v_reusejp_3580_;
}
v_reusejp_3580_:
{
return v___x_3581_;
}
}
}
}
}
else
{
lean_object* v_a_3584_; lean_object* v___x_3586_; uint8_t v_isShared_3587_; uint8_t v_isSharedCheck_3591_; 
lean_del_object(v___x_3541_);
lean_dec(v_val_3539_);
lean_del_object(v___x_3527_);
lean_dec(v_snd_3525_);
lean_dec(v_mvarId_3513_);
lean_dec_ref(v_p_3512_);
v_a_3584_ = lean_ctor_get(v___x_3545_, 0);
v_isSharedCheck_3591_ = !lean_is_exclusive(v___x_3545_);
if (v_isSharedCheck_3591_ == 0)
{
v___x_3586_ = v___x_3545_;
v_isShared_3587_ = v_isSharedCheck_3591_;
goto v_resetjp_3585_;
}
else
{
lean_inc(v_a_3584_);
lean_dec(v___x_3545_);
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
v___jp_3530_:
{
lean_object* v___x_3533_; 
if (v_isShared_3528_ == 0)
{
lean_ctor_set(v___x_3527_, 1, v_a_3531_);
lean_ctor_set(v___x_3527_, 0, v___x_3529_);
v___x_3533_ = v___x_3527_;
goto v_reusejp_3532_;
}
else
{
lean_object* v_reuseFailAlloc_3537_; 
v_reuseFailAlloc_3537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3537_, 0, v___x_3529_);
lean_ctor_set(v_reuseFailAlloc_3537_, 1, v_a_3531_);
v___x_3533_ = v_reuseFailAlloc_3537_;
goto v_reusejp_3532_;
}
v_reusejp_3532_:
{
size_t v___x_3534_; size_t v___x_3535_; lean_object* v___x_3536_; 
v___x_3534_ = ((size_t)1ULL);
v___x_3535_ = lean_usize_add(v_i_3516_, v___x_3534_);
v___x_3536_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5(v_p_3512_, v_mvarId_3513_, v_as_3514_, v_sz_3515_, v___x_3535_, v___x_3533_, v___y_3518_, v___y_3519_, v___y_3520_, v___y_3521_);
return v___x_3536_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4___boxed(lean_object* v_p_3595_, lean_object* v_mvarId_3596_, lean_object* v_as_3597_, lean_object* v_sz_3598_, lean_object* v_i_3599_, lean_object* v_b_3600_, lean_object* v___y_3601_, lean_object* v___y_3602_, lean_object* v___y_3603_, lean_object* v___y_3604_, lean_object* v___y_3605_){
_start:
{
size_t v_sz_boxed_3606_; size_t v_i_boxed_3607_; lean_object* v_res_3608_; 
v_sz_boxed_3606_ = lean_unbox_usize(v_sz_3598_);
lean_dec(v_sz_3598_);
v_i_boxed_3607_ = lean_unbox_usize(v_i_3599_);
lean_dec(v_i_3599_);
v_res_3608_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4(v_p_3595_, v_mvarId_3596_, v_as_3597_, v_sz_boxed_3606_, v_i_boxed_3607_, v_b_3600_, v___y_3601_, v___y_3602_, v___y_3603_, v___y_3604_);
lean_dec(v___y_3604_);
lean_dec_ref(v___y_3603_);
lean_dec(v___y_3602_);
lean_dec_ref(v___y_3601_);
lean_dec_ref(v_as_3597_);
return v_res_3608_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2(lean_object* v_init_3609_, lean_object* v_p_3610_, lean_object* v_mvarId_3611_, lean_object* v_n_3612_, lean_object* v_b_3613_, lean_object* v___y_3614_, lean_object* v___y_3615_, lean_object* v___y_3616_, lean_object* v___y_3617_){
_start:
{
if (lean_obj_tag(v_n_3612_) == 0)
{
lean_object* v_cs_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; size_t v_sz_3622_; size_t v___x_3623_; lean_object* v___x_3624_; 
v_cs_3619_ = lean_ctor_get(v_n_3612_, 0);
v___x_3620_ = lean_box(0);
v___x_3621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3621_, 0, v___x_3620_);
lean_ctor_set(v___x_3621_, 1, v_b_3613_);
v_sz_3622_ = lean_array_size(v_cs_3619_);
v___x_3623_ = ((size_t)0ULL);
v___x_3624_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__3(v_init_3609_, v_p_3610_, v_mvarId_3611_, v_cs_3619_, v_sz_3622_, v___x_3623_, v___x_3621_, v___y_3614_, v___y_3615_, v___y_3616_, v___y_3617_);
if (lean_obj_tag(v___x_3624_) == 0)
{
lean_object* v_a_3625_; lean_object* v___x_3627_; uint8_t v_isShared_3628_; uint8_t v_isSharedCheck_3639_; 
v_a_3625_ = lean_ctor_get(v___x_3624_, 0);
v_isSharedCheck_3639_ = !lean_is_exclusive(v___x_3624_);
if (v_isSharedCheck_3639_ == 0)
{
v___x_3627_ = v___x_3624_;
v_isShared_3628_ = v_isSharedCheck_3639_;
goto v_resetjp_3626_;
}
else
{
lean_inc(v_a_3625_);
lean_dec(v___x_3624_);
v___x_3627_ = lean_box(0);
v_isShared_3628_ = v_isSharedCheck_3639_;
goto v_resetjp_3626_;
}
v_resetjp_3626_:
{
lean_object* v_fst_3629_; 
v_fst_3629_ = lean_ctor_get(v_a_3625_, 0);
if (lean_obj_tag(v_fst_3629_) == 0)
{
lean_object* v_snd_3630_; lean_object* v___x_3631_; lean_object* v___x_3633_; 
v_snd_3630_ = lean_ctor_get(v_a_3625_, 1);
lean_inc(v_snd_3630_);
lean_dec(v_a_3625_);
v___x_3631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3631_, 0, v_snd_3630_);
if (v_isShared_3628_ == 0)
{
lean_ctor_set(v___x_3627_, 0, v___x_3631_);
v___x_3633_ = v___x_3627_;
goto v_reusejp_3632_;
}
else
{
lean_object* v_reuseFailAlloc_3634_; 
v_reuseFailAlloc_3634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3634_, 0, v___x_3631_);
v___x_3633_ = v_reuseFailAlloc_3634_;
goto v_reusejp_3632_;
}
v_reusejp_3632_:
{
return v___x_3633_;
}
}
else
{
lean_object* v_val_3635_; lean_object* v___x_3637_; 
lean_inc_ref(v_fst_3629_);
lean_dec(v_a_3625_);
v_val_3635_ = lean_ctor_get(v_fst_3629_, 0);
lean_inc(v_val_3635_);
lean_dec_ref_known(v_fst_3629_, 1);
if (v_isShared_3628_ == 0)
{
lean_ctor_set(v___x_3627_, 0, v_val_3635_);
v___x_3637_ = v___x_3627_;
goto v_reusejp_3636_;
}
else
{
lean_object* v_reuseFailAlloc_3638_; 
v_reuseFailAlloc_3638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3638_, 0, v_val_3635_);
v___x_3637_ = v_reuseFailAlloc_3638_;
goto v_reusejp_3636_;
}
v_reusejp_3636_:
{
return v___x_3637_;
}
}
}
}
else
{
lean_object* v_a_3640_; lean_object* v___x_3642_; uint8_t v_isShared_3643_; uint8_t v_isSharedCheck_3647_; 
v_a_3640_ = lean_ctor_get(v___x_3624_, 0);
v_isSharedCheck_3647_ = !lean_is_exclusive(v___x_3624_);
if (v_isSharedCheck_3647_ == 0)
{
v___x_3642_ = v___x_3624_;
v_isShared_3643_ = v_isSharedCheck_3647_;
goto v_resetjp_3641_;
}
else
{
lean_inc(v_a_3640_);
lean_dec(v___x_3624_);
v___x_3642_ = lean_box(0);
v_isShared_3643_ = v_isSharedCheck_3647_;
goto v_resetjp_3641_;
}
v_resetjp_3641_:
{
lean_object* v___x_3645_; 
if (v_isShared_3643_ == 0)
{
v___x_3645_ = v___x_3642_;
goto v_reusejp_3644_;
}
else
{
lean_object* v_reuseFailAlloc_3646_; 
v_reuseFailAlloc_3646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3646_, 0, v_a_3640_);
v___x_3645_ = v_reuseFailAlloc_3646_;
goto v_reusejp_3644_;
}
v_reusejp_3644_:
{
return v___x_3645_;
}
}
}
}
else
{
lean_object* v_vs_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; size_t v_sz_3651_; size_t v___x_3652_; lean_object* v___x_3653_; 
v_vs_3648_ = lean_ctor_get(v_n_3612_, 0);
v___x_3649_ = lean_box(0);
v___x_3650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3650_, 0, v___x_3649_);
lean_ctor_set(v___x_3650_, 1, v_b_3613_);
v_sz_3651_ = lean_array_size(v_vs_3648_);
v___x_3652_ = ((size_t)0ULL);
v___x_3653_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4(v_p_3610_, v_mvarId_3611_, v_vs_3648_, v_sz_3651_, v___x_3652_, v___x_3650_, v___y_3614_, v___y_3615_, v___y_3616_, v___y_3617_);
if (lean_obj_tag(v___x_3653_) == 0)
{
lean_object* v_a_3654_; lean_object* v___x_3656_; uint8_t v_isShared_3657_; uint8_t v_isSharedCheck_3668_; 
v_a_3654_ = lean_ctor_get(v___x_3653_, 0);
v_isSharedCheck_3668_ = !lean_is_exclusive(v___x_3653_);
if (v_isSharedCheck_3668_ == 0)
{
v___x_3656_ = v___x_3653_;
v_isShared_3657_ = v_isSharedCheck_3668_;
goto v_resetjp_3655_;
}
else
{
lean_inc(v_a_3654_);
lean_dec(v___x_3653_);
v___x_3656_ = lean_box(0);
v_isShared_3657_ = v_isSharedCheck_3668_;
goto v_resetjp_3655_;
}
v_resetjp_3655_:
{
lean_object* v_fst_3658_; 
v_fst_3658_ = lean_ctor_get(v_a_3654_, 0);
if (lean_obj_tag(v_fst_3658_) == 0)
{
lean_object* v_snd_3659_; lean_object* v___x_3660_; lean_object* v___x_3662_; 
v_snd_3659_ = lean_ctor_get(v_a_3654_, 1);
lean_inc(v_snd_3659_);
lean_dec(v_a_3654_);
v___x_3660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3660_, 0, v_snd_3659_);
if (v_isShared_3657_ == 0)
{
lean_ctor_set(v___x_3656_, 0, v___x_3660_);
v___x_3662_ = v___x_3656_;
goto v_reusejp_3661_;
}
else
{
lean_object* v_reuseFailAlloc_3663_; 
v_reuseFailAlloc_3663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3663_, 0, v___x_3660_);
v___x_3662_ = v_reuseFailAlloc_3663_;
goto v_reusejp_3661_;
}
v_reusejp_3661_:
{
return v___x_3662_;
}
}
else
{
lean_object* v_val_3664_; lean_object* v___x_3666_; 
lean_inc_ref(v_fst_3658_);
lean_dec(v_a_3654_);
v_val_3664_ = lean_ctor_get(v_fst_3658_, 0);
lean_inc(v_val_3664_);
lean_dec_ref_known(v_fst_3658_, 1);
if (v_isShared_3657_ == 0)
{
lean_ctor_set(v___x_3656_, 0, v_val_3664_);
v___x_3666_ = v___x_3656_;
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
v_a_3669_ = lean_ctor_get(v___x_3653_, 0);
v_isSharedCheck_3676_ = !lean_is_exclusive(v___x_3653_);
if (v_isSharedCheck_3676_ == 0)
{
v___x_3671_ = v___x_3653_;
v_isShared_3672_ = v_isSharedCheck_3676_;
goto v_resetjp_3670_;
}
else
{
lean_inc(v_a_3669_);
lean_dec(v___x_3653_);
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
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__3(lean_object* v_init_3677_, lean_object* v_p_3678_, lean_object* v_mvarId_3679_, lean_object* v_as_3680_, size_t v_sz_3681_, size_t v_i_3682_, lean_object* v_b_3683_, lean_object* v___y_3684_, lean_object* v___y_3685_, lean_object* v___y_3686_, lean_object* v___y_3687_){
_start:
{
uint8_t v___x_3689_; 
v___x_3689_ = lean_usize_dec_lt(v_i_3682_, v_sz_3681_);
if (v___x_3689_ == 0)
{
lean_object* v___x_3690_; 
lean_dec(v_mvarId_3679_);
lean_dec_ref(v_p_3678_);
v___x_3690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3690_, 0, v_b_3683_);
return v___x_3690_;
}
else
{
lean_object* v_snd_3691_; lean_object* v___x_3693_; uint8_t v_isShared_3694_; uint8_t v_isSharedCheck_3725_; 
v_snd_3691_ = lean_ctor_get(v_b_3683_, 1);
v_isSharedCheck_3725_ = !lean_is_exclusive(v_b_3683_);
if (v_isSharedCheck_3725_ == 0)
{
lean_object* v_unused_3726_; 
v_unused_3726_ = lean_ctor_get(v_b_3683_, 0);
lean_dec(v_unused_3726_);
v___x_3693_ = v_b_3683_;
v_isShared_3694_ = v_isSharedCheck_3725_;
goto v_resetjp_3692_;
}
else
{
lean_inc(v_snd_3691_);
lean_dec(v_b_3683_);
v___x_3693_ = lean_box(0);
v_isShared_3694_ = v_isSharedCheck_3725_;
goto v_resetjp_3692_;
}
v_resetjp_3692_:
{
lean_object* v___x_3695_; lean_object* v_a_3696_; lean_object* v___x_3697_; 
v___x_3695_ = lean_box(0);
v_a_3696_ = lean_array_uget_borrowed(v_as_3680_, v_i_3682_);
lean_inc(v_snd_3691_);
lean_inc(v_mvarId_3679_);
lean_inc_ref(v_p_3678_);
v___x_3697_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2(v_init_3677_, v_p_3678_, v_mvarId_3679_, v_a_3696_, v_snd_3691_, v___y_3684_, v___y_3685_, v___y_3686_, v___y_3687_);
if (lean_obj_tag(v___x_3697_) == 0)
{
lean_object* v_a_3698_; lean_object* v___x_3700_; uint8_t v_isShared_3701_; uint8_t v_isSharedCheck_3716_; 
v_a_3698_ = lean_ctor_get(v___x_3697_, 0);
v_isSharedCheck_3716_ = !lean_is_exclusive(v___x_3697_);
if (v_isSharedCheck_3716_ == 0)
{
v___x_3700_ = v___x_3697_;
v_isShared_3701_ = v_isSharedCheck_3716_;
goto v_resetjp_3699_;
}
else
{
lean_inc(v_a_3698_);
lean_dec(v___x_3697_);
v___x_3700_ = lean_box(0);
v_isShared_3701_ = v_isSharedCheck_3716_;
goto v_resetjp_3699_;
}
v_resetjp_3699_:
{
if (lean_obj_tag(v_a_3698_) == 0)
{
lean_object* v___x_3702_; lean_object* v___x_3704_; 
lean_dec(v_mvarId_3679_);
lean_dec_ref(v_p_3678_);
v___x_3702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3702_, 0, v_a_3698_);
if (v_isShared_3694_ == 0)
{
lean_ctor_set(v___x_3693_, 0, v___x_3702_);
v___x_3704_ = v___x_3693_;
goto v_reusejp_3703_;
}
else
{
lean_object* v_reuseFailAlloc_3708_; 
v_reuseFailAlloc_3708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3708_, 0, v___x_3702_);
lean_ctor_set(v_reuseFailAlloc_3708_, 1, v_snd_3691_);
v___x_3704_ = v_reuseFailAlloc_3708_;
goto v_reusejp_3703_;
}
v_reusejp_3703_:
{
lean_object* v___x_3706_; 
if (v_isShared_3701_ == 0)
{
lean_ctor_set(v___x_3700_, 0, v___x_3704_);
v___x_3706_ = v___x_3700_;
goto v_reusejp_3705_;
}
else
{
lean_object* v_reuseFailAlloc_3707_; 
v_reuseFailAlloc_3707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3707_, 0, v___x_3704_);
v___x_3706_ = v_reuseFailAlloc_3707_;
goto v_reusejp_3705_;
}
v_reusejp_3705_:
{
return v___x_3706_;
}
}
}
else
{
lean_object* v_a_3709_; lean_object* v___x_3711_; 
lean_del_object(v___x_3700_);
lean_dec(v_snd_3691_);
v_a_3709_ = lean_ctor_get(v_a_3698_, 0);
lean_inc(v_a_3709_);
lean_dec_ref_known(v_a_3698_, 1);
if (v_isShared_3694_ == 0)
{
lean_ctor_set(v___x_3693_, 1, v_a_3709_);
lean_ctor_set(v___x_3693_, 0, v___x_3695_);
v___x_3711_ = v___x_3693_;
goto v_reusejp_3710_;
}
else
{
lean_object* v_reuseFailAlloc_3715_; 
v_reuseFailAlloc_3715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3715_, 0, v___x_3695_);
lean_ctor_set(v_reuseFailAlloc_3715_, 1, v_a_3709_);
v___x_3711_ = v_reuseFailAlloc_3715_;
goto v_reusejp_3710_;
}
v_reusejp_3710_:
{
size_t v___x_3712_; size_t v___x_3713_; 
v___x_3712_ = ((size_t)1ULL);
v___x_3713_ = lean_usize_add(v_i_3682_, v___x_3712_);
v_i_3682_ = v___x_3713_;
v_b_3683_ = v___x_3711_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3717_; lean_object* v___x_3719_; uint8_t v_isShared_3720_; uint8_t v_isSharedCheck_3724_; 
lean_del_object(v___x_3693_);
lean_dec(v_snd_3691_);
lean_dec(v_mvarId_3679_);
lean_dec_ref(v_p_3678_);
v_a_3717_ = lean_ctor_get(v___x_3697_, 0);
v_isSharedCheck_3724_ = !lean_is_exclusive(v___x_3697_);
if (v_isSharedCheck_3724_ == 0)
{
v___x_3719_ = v___x_3697_;
v_isShared_3720_ = v_isSharedCheck_3724_;
goto v_resetjp_3718_;
}
else
{
lean_inc(v_a_3717_);
lean_dec(v___x_3697_);
v___x_3719_ = lean_box(0);
v_isShared_3720_ = v_isSharedCheck_3724_;
goto v_resetjp_3718_;
}
v_resetjp_3718_:
{
lean_object* v___x_3722_; 
if (v_isShared_3720_ == 0)
{
v___x_3722_ = v___x_3719_;
goto v_reusejp_3721_;
}
else
{
lean_object* v_reuseFailAlloc_3723_; 
v_reuseFailAlloc_3723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3723_, 0, v_a_3717_);
v___x_3722_ = v_reuseFailAlloc_3723_;
goto v_reusejp_3721_;
}
v_reusejp_3721_:
{
return v___x_3722_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__3___boxed(lean_object* v_init_3727_, lean_object* v_p_3728_, lean_object* v_mvarId_3729_, lean_object* v_as_3730_, lean_object* v_sz_3731_, lean_object* v_i_3732_, lean_object* v_b_3733_, lean_object* v___y_3734_, lean_object* v___y_3735_, lean_object* v___y_3736_, lean_object* v___y_3737_, lean_object* v___y_3738_){
_start:
{
size_t v_sz_boxed_3739_; size_t v_i_boxed_3740_; lean_object* v_res_3741_; 
v_sz_boxed_3739_ = lean_unbox_usize(v_sz_3731_);
lean_dec(v_sz_3731_);
v_i_boxed_3740_ = lean_unbox_usize(v_i_3732_);
lean_dec(v_i_3732_);
v_res_3741_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__3(v_init_3727_, v_p_3728_, v_mvarId_3729_, v_as_3730_, v_sz_boxed_3739_, v_i_boxed_3740_, v_b_3733_, v___y_3734_, v___y_3735_, v___y_3736_, v___y_3737_);
lean_dec(v___y_3737_);
lean_dec_ref(v___y_3736_);
lean_dec(v___y_3735_);
lean_dec_ref(v___y_3734_);
lean_dec_ref(v_as_3730_);
lean_dec_ref(v_init_3727_);
return v_res_3741_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2___boxed(lean_object* v_init_3742_, lean_object* v_p_3743_, lean_object* v_mvarId_3744_, lean_object* v_n_3745_, lean_object* v_b_3746_, lean_object* v___y_3747_, lean_object* v___y_3748_, lean_object* v___y_3749_, lean_object* v___y_3750_, lean_object* v___y_3751_){
_start:
{
lean_object* v_res_3752_; 
v_res_3752_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2(v_init_3742_, v_p_3743_, v_mvarId_3744_, v_n_3745_, v_b_3746_, v___y_3747_, v___y_3748_, v___y_3749_, v___y_3750_);
lean_dec(v___y_3750_);
lean_dec_ref(v___y_3749_);
lean_dec(v___y_3748_);
lean_dec_ref(v___y_3747_);
lean_dec_ref(v_n_3745_);
lean_dec_ref(v_init_3742_);
return v_res_3752_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3_spec__6(lean_object* v_p_3756_, lean_object* v_mvarId_3757_, lean_object* v_as_3758_, size_t v_sz_3759_, size_t v_i_3760_, lean_object* v_b_3761_, lean_object* v___y_3762_, lean_object* v___y_3763_, lean_object* v___y_3764_, lean_object* v___y_3765_){
_start:
{
uint8_t v___x_3767_; 
v___x_3767_ = lean_usize_dec_lt(v_i_3760_, v_sz_3759_);
if (v___x_3767_ == 0)
{
lean_object* v___x_3768_; 
lean_dec(v_mvarId_3757_);
lean_dec_ref(v_p_3756_);
v___x_3768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3768_, 0, v_b_3761_);
return v___x_3768_;
}
else
{
lean_object* v_snd_3769_; lean_object* v___x_3771_; uint8_t v_isShared_3772_; uint8_t v_isSharedCheck_3836_; 
v_snd_3769_ = lean_ctor_get(v_b_3761_, 1);
v_isSharedCheck_3836_ = !lean_is_exclusive(v_b_3761_);
if (v_isSharedCheck_3836_ == 0)
{
lean_object* v_unused_3837_; 
v_unused_3837_ = lean_ctor_get(v_b_3761_, 0);
lean_dec(v_unused_3837_);
v___x_3771_ = v_b_3761_;
v_isShared_3772_ = v_isSharedCheck_3836_;
goto v_resetjp_3770_;
}
else
{
lean_inc(v_snd_3769_);
lean_dec(v_b_3761_);
v___x_3771_ = lean_box(0);
v_isShared_3772_ = v_isSharedCheck_3836_;
goto v_resetjp_3770_;
}
v_resetjp_3770_:
{
lean_object* v___x_3773_; lean_object* v_a_3775_; lean_object* v_a_3782_; 
v___x_3773_ = lean_box(0);
v_a_3782_ = lean_array_uget(v_as_3758_, v_i_3760_);
if (lean_obj_tag(v_a_3782_) == 0)
{
v_a_3775_ = v_snd_3769_;
goto v___jp_3774_;
}
else
{
lean_object* v_val_3783_; lean_object* v___x_3785_; uint8_t v_isShared_3786_; uint8_t v_isSharedCheck_3835_; 
v_val_3783_ = lean_ctor_get(v_a_3782_, 0);
v_isSharedCheck_3835_ = !lean_is_exclusive(v_a_3782_);
if (v_isSharedCheck_3835_ == 0)
{
v___x_3785_ = v_a_3782_;
v_isShared_3786_ = v_isSharedCheck_3835_;
goto v_resetjp_3784_;
}
else
{
lean_inc(v_val_3783_);
lean_dec(v_a_3782_);
v___x_3785_ = lean_box(0);
v_isShared_3786_ = v_isSharedCheck_3835_;
goto v_resetjp_3784_;
}
v_resetjp_3784_:
{
lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; 
v___x_3787_ = lean_box(0);
v___x_3788_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3_spec__6___closed__0));
lean_inc_ref(v_p_3756_);
lean_inc(v___y_3765_);
lean_inc_ref(v___y_3764_);
lean_inc(v___y_3763_);
lean_inc_ref(v___y_3762_);
lean_inc(v_val_3783_);
v___x_3789_ = lean_apply_6(v_p_3756_, v_val_3783_, v___y_3762_, v___y_3763_, v___y_3764_, v___y_3765_, lean_box(0));
if (lean_obj_tag(v___x_3789_) == 0)
{
lean_object* v_a_3790_; uint8_t v___x_3791_; 
v_a_3790_ = lean_ctor_get(v___x_3789_, 0);
lean_inc(v_a_3790_);
lean_dec_ref_known(v___x_3789_, 1);
v___x_3791_ = lean_unbox(v_a_3790_);
lean_dec(v_a_3790_);
if (v___x_3791_ == 0)
{
lean_del_object(v___x_3785_);
lean_dec(v_val_3783_);
lean_dec(v_snd_3769_);
v_a_3775_ = v___x_3788_;
goto v___jp_3774_;
}
else
{
lean_object* v___x_3792_; lean_object* v___x_3793_; uint8_t v___x_3794_; lean_object* v___x_3795_; lean_object* v___f_3796_; lean_object* v___x_3797_; 
v___x_3792_ = l_Lean_LocalDecl_fvarId(v_val_3783_);
lean_dec(v_val_3783_);
v___x_3793_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5___closed__1));
v___x_3794_ = 0;
v___x_3795_ = lean_box(v___x_3794_);
lean_inc(v_mvarId_3757_);
v___f_3796_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3___lam__0___boxed), 10, 5);
lean_closure_set(v___f_3796_, 0, v_mvarId_3757_);
lean_closure_set(v___f_3796_, 1, v___x_3792_);
lean_closure_set(v___f_3796_, 2, v___x_3793_);
lean_closure_set(v___f_3796_, 3, v___x_3795_);
lean_closure_set(v___f_3796_, 4, v___x_3773_);
v___x_3797_ = l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1___redArg(v___f_3796_, v___y_3762_, v___y_3763_, v___y_3764_, v___y_3765_);
if (lean_obj_tag(v___x_3797_) == 0)
{
lean_object* v_a_3798_; lean_object* v___x_3800_; uint8_t v_isShared_3801_; uint8_t v_isSharedCheck_3818_; 
v_a_3798_ = lean_ctor_get(v___x_3797_, 0);
v_isSharedCheck_3818_ = !lean_is_exclusive(v___x_3797_);
if (v_isSharedCheck_3818_ == 0)
{
v___x_3800_ = v___x_3797_;
v_isShared_3801_ = v_isSharedCheck_3818_;
goto v_resetjp_3799_;
}
else
{
lean_inc(v_a_3798_);
lean_dec(v___x_3797_);
v___x_3800_ = lean_box(0);
v_isShared_3801_ = v_isSharedCheck_3818_;
goto v_resetjp_3799_;
}
v_resetjp_3799_:
{
if (lean_obj_tag(v_a_3798_) == 0)
{
lean_del_object(v___x_3800_);
lean_del_object(v___x_3785_);
lean_dec(v_snd_3769_);
v_a_3775_ = v___x_3788_;
goto v___jp_3774_;
}
else
{
lean_object* v___x_3803_; 
lean_del_object(v___x_3771_);
lean_dec(v_mvarId_3757_);
lean_dec_ref(v_p_3756_);
lean_inc_ref(v_a_3798_);
if (v_isShared_3786_ == 0)
{
lean_ctor_set(v___x_3785_, 0, v_a_3798_);
v___x_3803_ = v___x_3785_;
goto v_reusejp_3802_;
}
else
{
lean_object* v_reuseFailAlloc_3817_; 
v_reuseFailAlloc_3817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3817_, 0, v_a_3798_);
v___x_3803_ = v_reuseFailAlloc_3817_;
goto v_reusejp_3802_;
}
v_reusejp_3802_:
{
lean_object* v___x_3805_; uint8_t v_isShared_3806_; uint8_t v_isSharedCheck_3815_; 
v_isSharedCheck_3815_ = !lean_is_exclusive(v_a_3798_);
if (v_isSharedCheck_3815_ == 0)
{
lean_object* v_unused_3816_; 
v_unused_3816_ = lean_ctor_get(v_a_3798_, 0);
lean_dec(v_unused_3816_);
v___x_3805_ = v_a_3798_;
v_isShared_3806_ = v_isSharedCheck_3815_;
goto v_resetjp_3804_;
}
else
{
lean_dec(v_a_3798_);
v___x_3805_ = lean_box(0);
v_isShared_3806_ = v_isSharedCheck_3815_;
goto v_resetjp_3804_;
}
v_resetjp_3804_:
{
lean_object* v___x_3807_; lean_object* v___x_3809_; 
v___x_3807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3807_, 0, v___x_3803_);
lean_ctor_set(v___x_3807_, 1, v___x_3787_);
if (v_isShared_3806_ == 0)
{
lean_ctor_set(v___x_3805_, 0, v___x_3807_);
v___x_3809_ = v___x_3805_;
goto v_reusejp_3808_;
}
else
{
lean_object* v_reuseFailAlloc_3814_; 
v_reuseFailAlloc_3814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3814_, 0, v___x_3807_);
v___x_3809_ = v_reuseFailAlloc_3814_;
goto v_reusejp_3808_;
}
v_reusejp_3808_:
{
lean_object* v___x_3810_; lean_object* v___x_3812_; 
v___x_3810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3810_, 0, v___x_3809_);
lean_ctor_set(v___x_3810_, 1, v_snd_3769_);
if (v_isShared_3801_ == 0)
{
lean_ctor_set(v___x_3800_, 0, v___x_3810_);
v___x_3812_ = v___x_3800_;
goto v_reusejp_3811_;
}
else
{
lean_object* v_reuseFailAlloc_3813_; 
v_reuseFailAlloc_3813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3813_, 0, v___x_3810_);
v___x_3812_ = v_reuseFailAlloc_3813_;
goto v_reusejp_3811_;
}
v_reusejp_3811_:
{
return v___x_3812_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3819_; lean_object* v___x_3821_; uint8_t v_isShared_3822_; uint8_t v_isSharedCheck_3826_; 
lean_del_object(v___x_3785_);
lean_del_object(v___x_3771_);
lean_dec(v_snd_3769_);
lean_dec(v_mvarId_3757_);
lean_dec_ref(v_p_3756_);
v_a_3819_ = lean_ctor_get(v___x_3797_, 0);
v_isSharedCheck_3826_ = !lean_is_exclusive(v___x_3797_);
if (v_isSharedCheck_3826_ == 0)
{
v___x_3821_ = v___x_3797_;
v_isShared_3822_ = v_isSharedCheck_3826_;
goto v_resetjp_3820_;
}
else
{
lean_inc(v_a_3819_);
lean_dec(v___x_3797_);
v___x_3821_ = lean_box(0);
v_isShared_3822_ = v_isSharedCheck_3826_;
goto v_resetjp_3820_;
}
v_resetjp_3820_:
{
lean_object* v___x_3824_; 
if (v_isShared_3822_ == 0)
{
v___x_3824_ = v___x_3821_;
goto v_reusejp_3823_;
}
else
{
lean_object* v_reuseFailAlloc_3825_; 
v_reuseFailAlloc_3825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3825_, 0, v_a_3819_);
v___x_3824_ = v_reuseFailAlloc_3825_;
goto v_reusejp_3823_;
}
v_reusejp_3823_:
{
return v___x_3824_;
}
}
}
}
}
else
{
lean_object* v_a_3827_; lean_object* v___x_3829_; uint8_t v_isShared_3830_; uint8_t v_isSharedCheck_3834_; 
lean_del_object(v___x_3785_);
lean_dec(v_val_3783_);
lean_del_object(v___x_3771_);
lean_dec(v_snd_3769_);
lean_dec(v_mvarId_3757_);
lean_dec_ref(v_p_3756_);
v_a_3827_ = lean_ctor_get(v___x_3789_, 0);
v_isSharedCheck_3834_ = !lean_is_exclusive(v___x_3789_);
if (v_isSharedCheck_3834_ == 0)
{
v___x_3829_ = v___x_3789_;
v_isShared_3830_ = v_isSharedCheck_3834_;
goto v_resetjp_3828_;
}
else
{
lean_inc(v_a_3827_);
lean_dec(v___x_3789_);
v___x_3829_ = lean_box(0);
v_isShared_3830_ = v_isSharedCheck_3834_;
goto v_resetjp_3828_;
}
v_resetjp_3828_:
{
lean_object* v___x_3832_; 
if (v_isShared_3830_ == 0)
{
v___x_3832_ = v___x_3829_;
goto v_reusejp_3831_;
}
else
{
lean_object* v_reuseFailAlloc_3833_; 
v_reuseFailAlloc_3833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3833_, 0, v_a_3827_);
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
v___jp_3774_:
{
lean_object* v___x_3777_; 
if (v_isShared_3772_ == 0)
{
lean_ctor_set(v___x_3771_, 1, v_a_3775_);
lean_ctor_set(v___x_3771_, 0, v___x_3773_);
v___x_3777_ = v___x_3771_;
goto v_reusejp_3776_;
}
else
{
lean_object* v_reuseFailAlloc_3781_; 
v_reuseFailAlloc_3781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3781_, 0, v___x_3773_);
lean_ctor_set(v_reuseFailAlloc_3781_, 1, v_a_3775_);
v___x_3777_ = v_reuseFailAlloc_3781_;
goto v_reusejp_3776_;
}
v_reusejp_3776_:
{
size_t v___x_3778_; size_t v___x_3779_; 
v___x_3778_ = ((size_t)1ULL);
v___x_3779_ = lean_usize_add(v_i_3760_, v___x_3778_);
v_i_3760_ = v___x_3779_;
v_b_3761_ = v___x_3777_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3_spec__6___boxed(lean_object* v_p_3838_, lean_object* v_mvarId_3839_, lean_object* v_as_3840_, lean_object* v_sz_3841_, lean_object* v_i_3842_, lean_object* v_b_3843_, lean_object* v___y_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_, lean_object* v___y_3847_, lean_object* v___y_3848_){
_start:
{
size_t v_sz_boxed_3849_; size_t v_i_boxed_3850_; lean_object* v_res_3851_; 
v_sz_boxed_3849_ = lean_unbox_usize(v_sz_3841_);
lean_dec(v_sz_3841_);
v_i_boxed_3850_ = lean_unbox_usize(v_i_3842_);
lean_dec(v_i_3842_);
v_res_3851_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3_spec__6(v_p_3838_, v_mvarId_3839_, v_as_3840_, v_sz_boxed_3849_, v_i_boxed_3850_, v_b_3843_, v___y_3844_, v___y_3845_, v___y_3846_, v___y_3847_);
lean_dec(v___y_3847_);
lean_dec_ref(v___y_3846_);
lean_dec(v___y_3845_);
lean_dec_ref(v___y_3844_);
lean_dec_ref(v_as_3840_);
return v_res_3851_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3(lean_object* v_p_3852_, lean_object* v_mvarId_3853_, lean_object* v_as_3854_, size_t v_sz_3855_, size_t v_i_3856_, lean_object* v_b_3857_, lean_object* v___y_3858_, lean_object* v___y_3859_, lean_object* v___y_3860_, lean_object* v___y_3861_){
_start:
{
uint8_t v___x_3863_; 
v___x_3863_ = lean_usize_dec_lt(v_i_3856_, v_sz_3855_);
if (v___x_3863_ == 0)
{
lean_object* v___x_3864_; 
lean_dec(v_mvarId_3853_);
lean_dec_ref(v_p_3852_);
v___x_3864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3864_, 0, v_b_3857_);
return v___x_3864_;
}
else
{
lean_object* v_snd_3865_; lean_object* v___x_3867_; uint8_t v_isShared_3868_; uint8_t v_isSharedCheck_3932_; 
v_snd_3865_ = lean_ctor_get(v_b_3857_, 1);
v_isSharedCheck_3932_ = !lean_is_exclusive(v_b_3857_);
if (v_isSharedCheck_3932_ == 0)
{
lean_object* v_unused_3933_; 
v_unused_3933_ = lean_ctor_get(v_b_3857_, 0);
lean_dec(v_unused_3933_);
v___x_3867_ = v_b_3857_;
v_isShared_3868_ = v_isSharedCheck_3932_;
goto v_resetjp_3866_;
}
else
{
lean_inc(v_snd_3865_);
lean_dec(v_b_3857_);
v___x_3867_ = lean_box(0);
v_isShared_3868_ = v_isSharedCheck_3932_;
goto v_resetjp_3866_;
}
v_resetjp_3866_:
{
lean_object* v___x_3869_; lean_object* v_a_3871_; lean_object* v_a_3878_; 
v___x_3869_ = lean_box(0);
v_a_3878_ = lean_array_uget(v_as_3854_, v_i_3856_);
if (lean_obj_tag(v_a_3878_) == 0)
{
v_a_3871_ = v_snd_3865_;
goto v___jp_3870_;
}
else
{
lean_object* v_val_3879_; lean_object* v___x_3881_; uint8_t v_isShared_3882_; uint8_t v_isSharedCheck_3931_; 
v_val_3879_ = lean_ctor_get(v_a_3878_, 0);
v_isSharedCheck_3931_ = !lean_is_exclusive(v_a_3878_);
if (v_isSharedCheck_3931_ == 0)
{
v___x_3881_ = v_a_3878_;
v_isShared_3882_ = v_isSharedCheck_3931_;
goto v_resetjp_3880_;
}
else
{
lean_inc(v_val_3879_);
lean_dec(v_a_3878_);
v___x_3881_ = lean_box(0);
v_isShared_3882_ = v_isSharedCheck_3931_;
goto v_resetjp_3880_;
}
v_resetjp_3880_:
{
lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; 
v___x_3883_ = lean_box(0);
v___x_3884_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3_spec__6___closed__0));
lean_inc_ref(v_p_3852_);
lean_inc(v___y_3861_);
lean_inc_ref(v___y_3860_);
lean_inc(v___y_3859_);
lean_inc_ref(v___y_3858_);
lean_inc(v_val_3879_);
v___x_3885_ = lean_apply_6(v_p_3852_, v_val_3879_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_, lean_box(0));
if (lean_obj_tag(v___x_3885_) == 0)
{
lean_object* v_a_3886_; uint8_t v___x_3887_; 
v_a_3886_ = lean_ctor_get(v___x_3885_, 0);
lean_inc(v_a_3886_);
lean_dec_ref_known(v___x_3885_, 1);
v___x_3887_ = lean_unbox(v_a_3886_);
lean_dec(v_a_3886_);
if (v___x_3887_ == 0)
{
lean_del_object(v___x_3881_);
lean_dec(v_val_3879_);
lean_dec(v_snd_3865_);
v_a_3871_ = v___x_3884_;
goto v___jp_3870_;
}
else
{
lean_object* v___x_3888_; lean_object* v___x_3889_; uint8_t v___x_3890_; lean_object* v___x_3891_; lean_object* v___f_3892_; lean_object* v___x_3893_; 
v___x_3888_ = l_Lean_LocalDecl_fvarId(v_val_3879_);
lean_dec(v_val_3879_);
v___x_3889_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2_spec__4_spec__5___closed__1));
v___x_3890_ = 0;
v___x_3891_ = lean_box(v___x_3890_);
lean_inc(v_mvarId_3853_);
v___f_3892_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3___lam__0___boxed), 10, 5);
lean_closure_set(v___f_3892_, 0, v_mvarId_3853_);
lean_closure_set(v___f_3892_, 1, v___x_3888_);
lean_closure_set(v___f_3892_, 2, v___x_3889_);
lean_closure_set(v___f_3892_, 3, v___x_3891_);
lean_closure_set(v___f_3892_, 4, v___x_3869_);
v___x_3893_ = l_Lean_observing_x3f___at___00Lean_MVarId_casesRec_spec__1___redArg(v___f_3892_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_);
if (lean_obj_tag(v___x_3893_) == 0)
{
lean_object* v_a_3894_; lean_object* v___x_3896_; uint8_t v_isShared_3897_; uint8_t v_isSharedCheck_3914_; 
v_a_3894_ = lean_ctor_get(v___x_3893_, 0);
v_isSharedCheck_3914_ = !lean_is_exclusive(v___x_3893_);
if (v_isSharedCheck_3914_ == 0)
{
v___x_3896_ = v___x_3893_;
v_isShared_3897_ = v_isSharedCheck_3914_;
goto v_resetjp_3895_;
}
else
{
lean_inc(v_a_3894_);
lean_dec(v___x_3893_);
v___x_3896_ = lean_box(0);
v_isShared_3897_ = v_isSharedCheck_3914_;
goto v_resetjp_3895_;
}
v_resetjp_3895_:
{
if (lean_obj_tag(v_a_3894_) == 0)
{
lean_del_object(v___x_3896_);
lean_del_object(v___x_3881_);
lean_dec(v_snd_3865_);
v_a_3871_ = v___x_3884_;
goto v___jp_3870_;
}
else
{
lean_object* v___x_3899_; 
lean_del_object(v___x_3867_);
lean_dec(v_mvarId_3853_);
lean_dec_ref(v_p_3852_);
lean_inc_ref(v_a_3894_);
if (v_isShared_3882_ == 0)
{
lean_ctor_set(v___x_3881_, 0, v_a_3894_);
v___x_3899_ = v___x_3881_;
goto v_reusejp_3898_;
}
else
{
lean_object* v_reuseFailAlloc_3913_; 
v_reuseFailAlloc_3913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3913_, 0, v_a_3894_);
v___x_3899_ = v_reuseFailAlloc_3913_;
goto v_reusejp_3898_;
}
v_reusejp_3898_:
{
lean_object* v___x_3901_; uint8_t v_isShared_3902_; uint8_t v_isSharedCheck_3911_; 
v_isSharedCheck_3911_ = !lean_is_exclusive(v_a_3894_);
if (v_isSharedCheck_3911_ == 0)
{
lean_object* v_unused_3912_; 
v_unused_3912_ = lean_ctor_get(v_a_3894_, 0);
lean_dec(v_unused_3912_);
v___x_3901_ = v_a_3894_;
v_isShared_3902_ = v_isSharedCheck_3911_;
goto v_resetjp_3900_;
}
else
{
lean_dec(v_a_3894_);
v___x_3901_ = lean_box(0);
v_isShared_3902_ = v_isSharedCheck_3911_;
goto v_resetjp_3900_;
}
v_resetjp_3900_:
{
lean_object* v___x_3903_; lean_object* v___x_3905_; 
v___x_3903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3903_, 0, v___x_3899_);
lean_ctor_set(v___x_3903_, 1, v___x_3883_);
if (v_isShared_3902_ == 0)
{
lean_ctor_set(v___x_3901_, 0, v___x_3903_);
v___x_3905_ = v___x_3901_;
goto v_reusejp_3904_;
}
else
{
lean_object* v_reuseFailAlloc_3910_; 
v_reuseFailAlloc_3910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3910_, 0, v___x_3903_);
v___x_3905_ = v_reuseFailAlloc_3910_;
goto v_reusejp_3904_;
}
v_reusejp_3904_:
{
lean_object* v___x_3906_; lean_object* v___x_3908_; 
v___x_3906_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3906_, 0, v___x_3905_);
lean_ctor_set(v___x_3906_, 1, v_snd_3865_);
if (v_isShared_3897_ == 0)
{
lean_ctor_set(v___x_3896_, 0, v___x_3906_);
v___x_3908_ = v___x_3896_;
goto v_reusejp_3907_;
}
else
{
lean_object* v_reuseFailAlloc_3909_; 
v_reuseFailAlloc_3909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3909_, 0, v___x_3906_);
v___x_3908_ = v_reuseFailAlloc_3909_;
goto v_reusejp_3907_;
}
v_reusejp_3907_:
{
return v___x_3908_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3915_; lean_object* v___x_3917_; uint8_t v_isShared_3918_; uint8_t v_isSharedCheck_3922_; 
lean_del_object(v___x_3881_);
lean_del_object(v___x_3867_);
lean_dec(v_snd_3865_);
lean_dec(v_mvarId_3853_);
lean_dec_ref(v_p_3852_);
v_a_3915_ = lean_ctor_get(v___x_3893_, 0);
v_isSharedCheck_3922_ = !lean_is_exclusive(v___x_3893_);
if (v_isSharedCheck_3922_ == 0)
{
v___x_3917_ = v___x_3893_;
v_isShared_3918_ = v_isSharedCheck_3922_;
goto v_resetjp_3916_;
}
else
{
lean_inc(v_a_3915_);
lean_dec(v___x_3893_);
v___x_3917_ = lean_box(0);
v_isShared_3918_ = v_isSharedCheck_3922_;
goto v_resetjp_3916_;
}
v_resetjp_3916_:
{
lean_object* v___x_3920_; 
if (v_isShared_3918_ == 0)
{
v___x_3920_ = v___x_3917_;
goto v_reusejp_3919_;
}
else
{
lean_object* v_reuseFailAlloc_3921_; 
v_reuseFailAlloc_3921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3921_, 0, v_a_3915_);
v___x_3920_ = v_reuseFailAlloc_3921_;
goto v_reusejp_3919_;
}
v_reusejp_3919_:
{
return v___x_3920_;
}
}
}
}
}
else
{
lean_object* v_a_3923_; lean_object* v___x_3925_; uint8_t v_isShared_3926_; uint8_t v_isSharedCheck_3930_; 
lean_del_object(v___x_3881_);
lean_dec(v_val_3879_);
lean_del_object(v___x_3867_);
lean_dec(v_snd_3865_);
lean_dec(v_mvarId_3853_);
lean_dec_ref(v_p_3852_);
v_a_3923_ = lean_ctor_get(v___x_3885_, 0);
v_isSharedCheck_3930_ = !lean_is_exclusive(v___x_3885_);
if (v_isSharedCheck_3930_ == 0)
{
v___x_3925_ = v___x_3885_;
v_isShared_3926_ = v_isSharedCheck_3930_;
goto v_resetjp_3924_;
}
else
{
lean_inc(v_a_3923_);
lean_dec(v___x_3885_);
v___x_3925_ = lean_box(0);
v_isShared_3926_ = v_isSharedCheck_3930_;
goto v_resetjp_3924_;
}
v_resetjp_3924_:
{
lean_object* v___x_3928_; 
if (v_isShared_3926_ == 0)
{
v___x_3928_ = v___x_3925_;
goto v_reusejp_3927_;
}
else
{
lean_object* v_reuseFailAlloc_3929_; 
v_reuseFailAlloc_3929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3929_, 0, v_a_3923_);
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
v___jp_3870_:
{
lean_object* v___x_3873_; 
if (v_isShared_3868_ == 0)
{
lean_ctor_set(v___x_3867_, 1, v_a_3871_);
lean_ctor_set(v___x_3867_, 0, v___x_3869_);
v___x_3873_ = v___x_3867_;
goto v_reusejp_3872_;
}
else
{
lean_object* v_reuseFailAlloc_3877_; 
v_reuseFailAlloc_3877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3877_, 0, v___x_3869_);
lean_ctor_set(v_reuseFailAlloc_3877_, 1, v_a_3871_);
v___x_3873_ = v_reuseFailAlloc_3877_;
goto v_reusejp_3872_;
}
v_reusejp_3872_:
{
size_t v___x_3874_; size_t v___x_3875_; lean_object* v___x_3876_; 
v___x_3874_ = ((size_t)1ULL);
v___x_3875_ = lean_usize_add(v_i_3856_, v___x_3874_);
v___x_3876_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3_spec__6(v_p_3852_, v_mvarId_3853_, v_as_3854_, v_sz_3855_, v___x_3875_, v___x_3873_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_);
return v___x_3876_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3___boxed(lean_object* v_p_3934_, lean_object* v_mvarId_3935_, lean_object* v_as_3936_, lean_object* v_sz_3937_, lean_object* v_i_3938_, lean_object* v_b_3939_, lean_object* v___y_3940_, lean_object* v___y_3941_, lean_object* v___y_3942_, lean_object* v___y_3943_, lean_object* v___y_3944_){
_start:
{
size_t v_sz_boxed_3945_; size_t v_i_boxed_3946_; lean_object* v_res_3947_; 
v_sz_boxed_3945_ = lean_unbox_usize(v_sz_3937_);
lean_dec(v_sz_3937_);
v_i_boxed_3946_ = lean_unbox_usize(v_i_3938_);
lean_dec(v_i_3938_);
v_res_3947_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3(v_p_3934_, v_mvarId_3935_, v_as_3936_, v_sz_boxed_3945_, v_i_boxed_3946_, v_b_3939_, v___y_3940_, v___y_3941_, v___y_3942_, v___y_3943_);
lean_dec(v___y_3943_);
lean_dec_ref(v___y_3942_);
lean_dec(v___y_3941_);
lean_dec_ref(v___y_3940_);
lean_dec_ref(v_as_3936_);
return v_res_3947_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2(lean_object* v_p_3948_, lean_object* v_mvarId_3949_, lean_object* v_t_3950_, lean_object* v_init_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_){
_start:
{
lean_object* v_root_3957_; lean_object* v_tail_3958_; lean_object* v___x_3959_; 
v_root_3957_ = lean_ctor_get(v_t_3950_, 0);
v_tail_3958_ = lean_ctor_get(v_t_3950_, 1);
lean_inc(v_mvarId_3949_);
lean_inc_ref(v_p_3948_);
lean_inc_ref(v_init_3951_);
v___x_3959_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__2(v_init_3951_, v_p_3948_, v_mvarId_3949_, v_root_3957_, v_init_3951_, v___y_3952_, v___y_3953_, v___y_3954_, v___y_3955_);
lean_dec_ref(v_init_3951_);
if (lean_obj_tag(v___x_3959_) == 0)
{
lean_object* v_a_3960_; lean_object* v___x_3962_; uint8_t v_isShared_3963_; uint8_t v_isSharedCheck_3996_; 
v_a_3960_ = lean_ctor_get(v___x_3959_, 0);
v_isSharedCheck_3996_ = !lean_is_exclusive(v___x_3959_);
if (v_isSharedCheck_3996_ == 0)
{
v___x_3962_ = v___x_3959_;
v_isShared_3963_ = v_isSharedCheck_3996_;
goto v_resetjp_3961_;
}
else
{
lean_inc(v_a_3960_);
lean_dec(v___x_3959_);
v___x_3962_ = lean_box(0);
v_isShared_3963_ = v_isSharedCheck_3996_;
goto v_resetjp_3961_;
}
v_resetjp_3961_:
{
if (lean_obj_tag(v_a_3960_) == 0)
{
lean_object* v_a_3964_; lean_object* v___x_3966_; 
lean_dec(v_mvarId_3949_);
lean_dec_ref(v_p_3948_);
v_a_3964_ = lean_ctor_get(v_a_3960_, 0);
lean_inc(v_a_3964_);
lean_dec_ref_known(v_a_3960_, 1);
if (v_isShared_3963_ == 0)
{
lean_ctor_set(v___x_3962_, 0, v_a_3964_);
v___x_3966_ = v___x_3962_;
goto v_reusejp_3965_;
}
else
{
lean_object* v_reuseFailAlloc_3967_; 
v_reuseFailAlloc_3967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3967_, 0, v_a_3964_);
v___x_3966_ = v_reuseFailAlloc_3967_;
goto v_reusejp_3965_;
}
v_reusejp_3965_:
{
return v___x_3966_;
}
}
else
{
lean_object* v_a_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; size_t v_sz_3971_; size_t v___x_3972_; lean_object* v___x_3973_; 
lean_del_object(v___x_3962_);
v_a_3968_ = lean_ctor_get(v_a_3960_, 0);
lean_inc(v_a_3968_);
lean_dec_ref_known(v_a_3960_, 1);
v___x_3969_ = lean_box(0);
v___x_3970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3970_, 0, v___x_3969_);
lean_ctor_set(v___x_3970_, 1, v_a_3968_);
v_sz_3971_ = lean_array_size(v_tail_3958_);
v___x_3972_ = ((size_t)0ULL);
v___x_3973_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2_spec__3(v_p_3948_, v_mvarId_3949_, v_tail_3958_, v_sz_3971_, v___x_3972_, v___x_3970_, v___y_3952_, v___y_3953_, v___y_3954_, v___y_3955_);
if (lean_obj_tag(v___x_3973_) == 0)
{
lean_object* v_a_3974_; lean_object* v___x_3976_; uint8_t v_isShared_3977_; uint8_t v_isSharedCheck_3987_; 
v_a_3974_ = lean_ctor_get(v___x_3973_, 0);
v_isSharedCheck_3987_ = !lean_is_exclusive(v___x_3973_);
if (v_isSharedCheck_3987_ == 0)
{
v___x_3976_ = v___x_3973_;
v_isShared_3977_ = v_isSharedCheck_3987_;
goto v_resetjp_3975_;
}
else
{
lean_inc(v_a_3974_);
lean_dec(v___x_3973_);
v___x_3976_ = lean_box(0);
v_isShared_3977_ = v_isSharedCheck_3987_;
goto v_resetjp_3975_;
}
v_resetjp_3975_:
{
lean_object* v_fst_3978_; 
v_fst_3978_ = lean_ctor_get(v_a_3974_, 0);
if (lean_obj_tag(v_fst_3978_) == 0)
{
lean_object* v_snd_3979_; lean_object* v___x_3981_; 
v_snd_3979_ = lean_ctor_get(v_a_3974_, 1);
lean_inc(v_snd_3979_);
lean_dec(v_a_3974_);
if (v_isShared_3977_ == 0)
{
lean_ctor_set(v___x_3976_, 0, v_snd_3979_);
v___x_3981_ = v___x_3976_;
goto v_reusejp_3980_;
}
else
{
lean_object* v_reuseFailAlloc_3982_; 
v_reuseFailAlloc_3982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3982_, 0, v_snd_3979_);
v___x_3981_ = v_reuseFailAlloc_3982_;
goto v_reusejp_3980_;
}
v_reusejp_3980_:
{
return v___x_3981_;
}
}
else
{
lean_object* v_val_3983_; lean_object* v___x_3985_; 
lean_inc_ref(v_fst_3978_);
lean_dec(v_a_3974_);
v_val_3983_ = lean_ctor_get(v_fst_3978_, 0);
lean_inc(v_val_3983_);
lean_dec_ref_known(v_fst_3978_, 1);
if (v_isShared_3977_ == 0)
{
lean_ctor_set(v___x_3976_, 0, v_val_3983_);
v___x_3985_ = v___x_3976_;
goto v_reusejp_3984_;
}
else
{
lean_object* v_reuseFailAlloc_3986_; 
v_reuseFailAlloc_3986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3986_, 0, v_val_3983_);
v___x_3985_ = v_reuseFailAlloc_3986_;
goto v_reusejp_3984_;
}
v_reusejp_3984_:
{
return v___x_3985_;
}
}
}
}
else
{
lean_object* v_a_3988_; lean_object* v___x_3990_; uint8_t v_isShared_3991_; uint8_t v_isSharedCheck_3995_; 
v_a_3988_ = lean_ctor_get(v___x_3973_, 0);
v_isSharedCheck_3995_ = !lean_is_exclusive(v___x_3973_);
if (v_isSharedCheck_3995_ == 0)
{
v___x_3990_ = v___x_3973_;
v_isShared_3991_ = v_isSharedCheck_3995_;
goto v_resetjp_3989_;
}
else
{
lean_inc(v_a_3988_);
lean_dec(v___x_3973_);
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
}
else
{
lean_object* v_a_3997_; lean_object* v___x_3999_; uint8_t v_isShared_4000_; uint8_t v_isSharedCheck_4004_; 
lean_dec(v_mvarId_3949_);
lean_dec_ref(v_p_3948_);
v_a_3997_ = lean_ctor_get(v___x_3959_, 0);
v_isSharedCheck_4004_ = !lean_is_exclusive(v___x_3959_);
if (v_isSharedCheck_4004_ == 0)
{
v___x_3999_ = v___x_3959_;
v_isShared_4000_ = v_isSharedCheck_4004_;
goto v_resetjp_3998_;
}
else
{
lean_inc(v_a_3997_);
lean_dec(v___x_3959_);
v___x_3999_ = lean_box(0);
v_isShared_4000_ = v_isSharedCheck_4004_;
goto v_resetjp_3998_;
}
v_resetjp_3998_:
{
lean_object* v___x_4002_; 
if (v_isShared_4000_ == 0)
{
v___x_4002_ = v___x_3999_;
goto v_reusejp_4001_;
}
else
{
lean_object* v_reuseFailAlloc_4003_; 
v_reuseFailAlloc_4003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4003_, 0, v_a_3997_);
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
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2___boxed(lean_object* v_p_4005_, lean_object* v_mvarId_4006_, lean_object* v_t_4007_, lean_object* v_init_4008_, lean_object* v___y_4009_, lean_object* v___y_4010_, lean_object* v___y_4011_, lean_object* v___y_4012_, lean_object* v___y_4013_){
_start:
{
lean_object* v_res_4014_; 
v_res_4014_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2(v_p_4005_, v_mvarId_4006_, v_t_4007_, v_init_4008_, v___y_4009_, v___y_4010_, v___y_4011_, v___y_4012_);
lean_dec(v___y_4012_);
lean_dec_ref(v___y_4011_);
lean_dec(v___y_4010_);
lean_dec_ref(v___y_4009_);
lean_dec_ref(v_t_4007_);
return v_res_4014_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesRec___lam__0(lean_object* v_p_4018_, lean_object* v_mvarId_4019_, lean_object* v___y_4020_, lean_object* v___y_4021_, lean_object* v___y_4022_, lean_object* v___y_4023_){
_start:
{
lean_object* v_lctx_4025_; lean_object* v_decls_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; lean_object* v___x_4029_; 
v_lctx_4025_ = lean_ctor_get(v___y_4020_, 2);
v_decls_4026_ = lean_ctor_get(v_lctx_4025_, 1);
v___x_4027_ = lean_box(0);
v___x_4028_ = ((lean_object*)(l_Lean_MVarId_casesRec___lam__0___closed__0));
v___x_4029_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_casesRec_spec__2(v_p_4018_, v_mvarId_4019_, v_decls_4026_, v___x_4028_, v___y_4020_, v___y_4021_, v___y_4022_, v___y_4023_);
if (lean_obj_tag(v___x_4029_) == 0)
{
lean_object* v_a_4030_; lean_object* v___x_4032_; uint8_t v_isShared_4033_; uint8_t v_isSharedCheck_4042_; 
v_a_4030_ = lean_ctor_get(v___x_4029_, 0);
v_isSharedCheck_4042_ = !lean_is_exclusive(v___x_4029_);
if (v_isSharedCheck_4042_ == 0)
{
v___x_4032_ = v___x_4029_;
v_isShared_4033_ = v_isSharedCheck_4042_;
goto v_resetjp_4031_;
}
else
{
lean_inc(v_a_4030_);
lean_dec(v___x_4029_);
v___x_4032_ = lean_box(0);
v_isShared_4033_ = v_isSharedCheck_4042_;
goto v_resetjp_4031_;
}
v_resetjp_4031_:
{
lean_object* v_fst_4034_; 
v_fst_4034_ = lean_ctor_get(v_a_4030_, 0);
lean_inc(v_fst_4034_);
lean_dec(v_a_4030_);
if (lean_obj_tag(v_fst_4034_) == 0)
{
lean_object* v___x_4036_; 
if (v_isShared_4033_ == 0)
{
lean_ctor_set(v___x_4032_, 0, v___x_4027_);
v___x_4036_ = v___x_4032_;
goto v_reusejp_4035_;
}
else
{
lean_object* v_reuseFailAlloc_4037_; 
v_reuseFailAlloc_4037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4037_, 0, v___x_4027_);
v___x_4036_ = v_reuseFailAlloc_4037_;
goto v_reusejp_4035_;
}
v_reusejp_4035_:
{
return v___x_4036_;
}
}
else
{
lean_object* v_val_4038_; lean_object* v___x_4040_; 
v_val_4038_ = lean_ctor_get(v_fst_4034_, 0);
lean_inc(v_val_4038_);
lean_dec_ref_known(v_fst_4034_, 1);
if (v_isShared_4033_ == 0)
{
lean_ctor_set(v___x_4032_, 0, v_val_4038_);
v___x_4040_ = v___x_4032_;
goto v_reusejp_4039_;
}
else
{
lean_object* v_reuseFailAlloc_4041_; 
v_reuseFailAlloc_4041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4041_, 0, v_val_4038_);
v___x_4040_ = v_reuseFailAlloc_4041_;
goto v_reusejp_4039_;
}
v_reusejp_4039_:
{
return v___x_4040_;
}
}
}
}
else
{
lean_object* v_a_4043_; lean_object* v___x_4045_; uint8_t v_isShared_4046_; uint8_t v_isSharedCheck_4050_; 
v_a_4043_ = lean_ctor_get(v___x_4029_, 0);
v_isSharedCheck_4050_ = !lean_is_exclusive(v___x_4029_);
if (v_isSharedCheck_4050_ == 0)
{
v___x_4045_ = v___x_4029_;
v_isShared_4046_ = v_isSharedCheck_4050_;
goto v_resetjp_4044_;
}
else
{
lean_inc(v_a_4043_);
lean_dec(v___x_4029_);
v___x_4045_ = lean_box(0);
v_isShared_4046_ = v_isSharedCheck_4050_;
goto v_resetjp_4044_;
}
v_resetjp_4044_:
{
lean_object* v___x_4048_; 
if (v_isShared_4046_ == 0)
{
v___x_4048_ = v___x_4045_;
goto v_reusejp_4047_;
}
else
{
lean_object* v_reuseFailAlloc_4049_; 
v_reuseFailAlloc_4049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4049_, 0, v_a_4043_);
v___x_4048_ = v_reuseFailAlloc_4049_;
goto v_reusejp_4047_;
}
v_reusejp_4047_:
{
return v___x_4048_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesRec___lam__0___boxed(lean_object* v_p_4051_, lean_object* v_mvarId_4052_, lean_object* v___y_4053_, lean_object* v___y_4054_, lean_object* v___y_4055_, lean_object* v___y_4056_, lean_object* v___y_4057_){
_start:
{
lean_object* v_res_4058_; 
v_res_4058_ = l_Lean_MVarId_casesRec___lam__0(v_p_4051_, v_mvarId_4052_, v___y_4053_, v___y_4054_, v___y_4055_, v___y_4056_);
lean_dec(v___y_4056_);
lean_dec_ref(v___y_4055_);
lean_dec(v___y_4054_);
lean_dec_ref(v___y_4053_);
return v_res_4058_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesRec___lam__1(lean_object* v_p_4059_, lean_object* v_mvarId_4060_, lean_object* v___y_4061_, lean_object* v___y_4062_, lean_object* v___y_4063_, lean_object* v___y_4064_){
_start:
{
lean_object* v___f_4066_; lean_object* v___x_4067_; 
lean_inc(v_mvarId_4060_);
v___f_4066_ = lean_alloc_closure((void*)(l_Lean_MVarId_casesRec___lam__0___boxed), 7, 2);
lean_closure_set(v___f_4066_, 0, v_p_4059_);
lean_closure_set(v___f_4066_, 1, v_mvarId_4060_);
v___x_4067_ = l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2___redArg(v_mvarId_4060_, v___f_4066_, v___y_4061_, v___y_4062_, v___y_4063_, v___y_4064_);
return v___x_4067_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesRec___lam__1___boxed(lean_object* v_p_4068_, lean_object* v_mvarId_4069_, lean_object* v___y_4070_, lean_object* v___y_4071_, lean_object* v___y_4072_, lean_object* v___y_4073_, lean_object* v___y_4074_){
_start:
{
lean_object* v_res_4075_; 
v_res_4075_ = l_Lean_MVarId_casesRec___lam__1(v_p_4068_, v_mvarId_4069_, v___y_4070_, v___y_4071_, v___y_4072_, v___y_4073_);
lean_dec(v___y_4073_);
lean_dec_ref(v___y_4072_);
lean_dec(v___y_4071_);
lean_dec_ref(v___y_4070_);
return v_res_4075_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesRec(lean_object* v_mvarId_4076_, lean_object* v_p_4077_, lean_object* v_a_4078_, lean_object* v_a_4079_, lean_object* v_a_4080_, lean_object* v_a_4081_){
_start:
{
lean_object* v___f_4083_; lean_object* v___x_4084_; 
v___f_4083_ = lean_alloc_closure((void*)(l_Lean_MVarId_casesRec___lam__1___boxed), 7, 1);
lean_closure_set(v___f_4083_, 0, v_p_4077_);
v___x_4084_ = l_Lean_Meta_saturate(v_mvarId_4076_, v___f_4083_, v_a_4078_, v_a_4079_, v_a_4080_, v_a_4081_);
return v___x_4084_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesRec___boxed(lean_object* v_mvarId_4085_, lean_object* v_p_4086_, lean_object* v_a_4087_, lean_object* v_a_4088_, lean_object* v_a_4089_, lean_object* v_a_4090_, lean_object* v_a_4091_){
_start:
{
lean_object* v_res_4092_; 
v_res_4092_ = l_Lean_MVarId_casesRec(v_mvarId_4085_, v_p_4086_, v_a_4087_, v_a_4088_, v_a_4089_, v_a_4090_);
lean_dec(v_a_4090_);
lean_dec_ref(v_a_4089_);
lean_dec(v_a_4088_);
lean_dec_ref(v_a_4087_);
return v_res_4092_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0___redArg(lean_object* v_e_4093_, lean_object* v___y_4094_){
_start:
{
uint8_t v___x_4096_; 
v___x_4096_ = l_Lean_Expr_hasMVar(v_e_4093_);
if (v___x_4096_ == 0)
{
lean_object* v___x_4097_; 
v___x_4097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4097_, 0, v_e_4093_);
return v___x_4097_;
}
else
{
lean_object* v___x_4098_; lean_object* v_mctx_4099_; lean_object* v___x_4100_; lean_object* v_fst_4101_; lean_object* v_snd_4102_; lean_object* v___x_4103_; lean_object* v_cache_4104_; lean_object* v_zetaDeltaFVarIds_4105_; lean_object* v_postponed_4106_; lean_object* v_diag_4107_; lean_object* v___x_4109_; uint8_t v_isShared_4110_; uint8_t v_isSharedCheck_4116_; 
v___x_4098_ = lean_st_ref_get(v___y_4094_);
v_mctx_4099_ = lean_ctor_get(v___x_4098_, 0);
lean_inc_ref(v_mctx_4099_);
lean_dec(v___x_4098_);
v___x_4100_ = l_Lean_instantiateMVarsCore(v_mctx_4099_, v_e_4093_);
v_fst_4101_ = lean_ctor_get(v___x_4100_, 0);
lean_inc(v_fst_4101_);
v_snd_4102_ = lean_ctor_get(v___x_4100_, 1);
lean_inc(v_snd_4102_);
lean_dec_ref(v___x_4100_);
v___x_4103_ = lean_st_ref_take(v___y_4094_);
v_cache_4104_ = lean_ctor_get(v___x_4103_, 1);
v_zetaDeltaFVarIds_4105_ = lean_ctor_get(v___x_4103_, 2);
v_postponed_4106_ = lean_ctor_get(v___x_4103_, 3);
v_diag_4107_ = lean_ctor_get(v___x_4103_, 4);
v_isSharedCheck_4116_ = !lean_is_exclusive(v___x_4103_);
if (v_isSharedCheck_4116_ == 0)
{
lean_object* v_unused_4117_; 
v_unused_4117_ = lean_ctor_get(v___x_4103_, 0);
lean_dec(v_unused_4117_);
v___x_4109_ = v___x_4103_;
v_isShared_4110_ = v_isSharedCheck_4116_;
goto v_resetjp_4108_;
}
else
{
lean_inc(v_diag_4107_);
lean_inc(v_postponed_4106_);
lean_inc(v_zetaDeltaFVarIds_4105_);
lean_inc(v_cache_4104_);
lean_dec(v___x_4103_);
v___x_4109_ = lean_box(0);
v_isShared_4110_ = v_isSharedCheck_4116_;
goto v_resetjp_4108_;
}
v_resetjp_4108_:
{
lean_object* v___x_4112_; 
if (v_isShared_4110_ == 0)
{
lean_ctor_set(v___x_4109_, 0, v_snd_4102_);
v___x_4112_ = v___x_4109_;
goto v_reusejp_4111_;
}
else
{
lean_object* v_reuseFailAlloc_4115_; 
v_reuseFailAlloc_4115_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4115_, 0, v_snd_4102_);
lean_ctor_set(v_reuseFailAlloc_4115_, 1, v_cache_4104_);
lean_ctor_set(v_reuseFailAlloc_4115_, 2, v_zetaDeltaFVarIds_4105_);
lean_ctor_set(v_reuseFailAlloc_4115_, 3, v_postponed_4106_);
lean_ctor_set(v_reuseFailAlloc_4115_, 4, v_diag_4107_);
v___x_4112_ = v_reuseFailAlloc_4115_;
goto v_reusejp_4111_;
}
v_reusejp_4111_:
{
lean_object* v___x_4113_; lean_object* v___x_4114_; 
v___x_4113_ = lean_st_ref_put(v___y_4094_, v___x_4112_);
v___x_4114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4114_, 0, v_fst_4101_);
return v___x_4114_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0___redArg___boxed(lean_object* v_e_4118_, lean_object* v___y_4119_, lean_object* v___y_4120_){
_start:
{
lean_object* v_res_4121_; 
v_res_4121_ = l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0___redArg(v_e_4118_, v___y_4119_);
lean_dec(v___y_4119_);
return v_res_4121_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0(lean_object* v_e_4122_, lean_object* v___y_4123_, lean_object* v___y_4124_, lean_object* v___y_4125_, lean_object* v___y_4126_){
_start:
{
lean_object* v___x_4128_; 
v___x_4128_ = l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0___redArg(v_e_4122_, v___y_4124_);
return v___x_4128_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0___boxed(lean_object* v_e_4129_, lean_object* v___y_4130_, lean_object* v___y_4131_, lean_object* v___y_4132_, lean_object* v___y_4133_, lean_object* v___y_4134_){
_start:
{
lean_object* v_res_4135_; 
v_res_4135_ = l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0(v_e_4129_, v___y_4130_, v___y_4131_, v___y_4132_, v___y_4133_);
lean_dec(v___y_4133_);
lean_dec_ref(v___y_4132_);
lean_dec(v___y_4131_);
lean_dec_ref(v___y_4130_);
return v_res_4135_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesAnd___lam__0(lean_object* v_localDecl_4139_, lean_object* v___y_4140_, lean_object* v___y_4141_, lean_object* v___y_4142_, lean_object* v___y_4143_){
_start:
{
lean_object* v___x_4145_; lean_object* v___x_4146_; lean_object* v_a_4147_; lean_object* v___x_4149_; uint8_t v_isShared_4150_; uint8_t v_isSharedCheck_4158_; 
v___x_4145_ = l_Lean_LocalDecl_type(v_localDecl_4139_);
v___x_4146_ = l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0___redArg(v___x_4145_, v___y_4141_);
v_a_4147_ = lean_ctor_get(v___x_4146_, 0);
v_isSharedCheck_4158_ = !lean_is_exclusive(v___x_4146_);
if (v_isSharedCheck_4158_ == 0)
{
v___x_4149_ = v___x_4146_;
v_isShared_4150_ = v_isSharedCheck_4158_;
goto v_resetjp_4148_;
}
else
{
lean_inc(v_a_4147_);
lean_dec(v___x_4146_);
v___x_4149_ = lean_box(0);
v_isShared_4150_ = v_isSharedCheck_4158_;
goto v_resetjp_4148_;
}
v_resetjp_4148_:
{
lean_object* v___x_4151_; lean_object* v___x_4152_; uint8_t v___x_4153_; lean_object* v___x_4154_; lean_object* v___x_4156_; 
v___x_4151_ = ((lean_object*)(l_Lean_MVarId_casesAnd___lam__0___closed__1));
v___x_4152_ = lean_unsigned_to_nat(2u);
v___x_4153_ = l_Lean_Expr_isAppOfArity(v_a_4147_, v___x_4151_, v___x_4152_);
lean_dec(v_a_4147_);
v___x_4154_ = lean_box(v___x_4153_);
if (v_isShared_4150_ == 0)
{
lean_ctor_set(v___x_4149_, 0, v___x_4154_);
v___x_4156_ = v___x_4149_;
goto v_reusejp_4155_;
}
else
{
lean_object* v_reuseFailAlloc_4157_; 
v_reuseFailAlloc_4157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4157_, 0, v___x_4154_);
v___x_4156_ = v_reuseFailAlloc_4157_;
goto v_reusejp_4155_;
}
v_reusejp_4155_:
{
return v___x_4156_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesAnd___lam__0___boxed(lean_object* v_localDecl_4159_, lean_object* v___y_4160_, lean_object* v___y_4161_, lean_object* v___y_4162_, lean_object* v___y_4163_, lean_object* v___y_4164_){
_start:
{
lean_object* v_res_4165_; 
v_res_4165_ = l_Lean_MVarId_casesAnd___lam__0(v_localDecl_4159_, v___y_4160_, v___y_4161_, v___y_4162_, v___y_4163_);
lean_dec(v___y_4163_);
lean_dec_ref(v___y_4162_);
lean_dec(v___y_4161_);
lean_dec_ref(v___y_4160_);
lean_dec_ref(v_localDecl_4159_);
return v_res_4165_;
}
}
static lean_object* _init_l_Lean_MVarId_casesAnd___closed__3(void){
_start:
{
lean_object* v___x_4170_; lean_object* v___x_4171_; 
v___x_4170_ = ((lean_object*)(l_Lean_MVarId_casesAnd___closed__2));
v___x_4171_ = l_Lean_MessageData_ofFormat(v___x_4170_);
return v___x_4171_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesAnd(lean_object* v_mvarId_4172_, lean_object* v_a_4173_, lean_object* v_a_4174_, lean_object* v_a_4175_, lean_object* v_a_4176_){
_start:
{
lean_object* v___f_4178_; lean_object* v___x_4179_; 
v___f_4178_ = ((lean_object*)(l_Lean_MVarId_casesAnd___closed__0));
v___x_4179_ = l_Lean_MVarId_casesRec(v_mvarId_4172_, v___f_4178_, v_a_4173_, v_a_4174_, v_a_4175_, v_a_4176_);
if (lean_obj_tag(v___x_4179_) == 0)
{
lean_object* v_a_4180_; lean_object* v___x_4181_; lean_object* v___x_4182_; 
v_a_4180_ = lean_ctor_get(v___x_4179_, 0);
lean_inc(v_a_4180_);
lean_dec_ref_known(v___x_4179_, 1);
v___x_4181_ = lean_obj_once(&l_Lean_MVarId_casesAnd___closed__3, &l_Lean_MVarId_casesAnd___closed__3_once, _init_l_Lean_MVarId_casesAnd___closed__3);
v___x_4182_ = l_Lean_Meta_exactlyOne(v_a_4180_, v___x_4181_, v_a_4173_, v_a_4174_, v_a_4175_, v_a_4176_);
lean_dec(v_a_4180_);
return v___x_4182_;
}
else
{
lean_object* v_a_4183_; lean_object* v___x_4185_; uint8_t v_isShared_4186_; uint8_t v_isSharedCheck_4190_; 
v_a_4183_ = lean_ctor_get(v___x_4179_, 0);
v_isSharedCheck_4190_ = !lean_is_exclusive(v___x_4179_);
if (v_isSharedCheck_4190_ == 0)
{
v___x_4185_ = v___x_4179_;
v_isShared_4186_ = v_isSharedCheck_4190_;
goto v_resetjp_4184_;
}
else
{
lean_inc(v_a_4183_);
lean_dec(v___x_4179_);
v___x_4185_ = lean_box(0);
v_isShared_4186_ = v_isSharedCheck_4190_;
goto v_resetjp_4184_;
}
v_resetjp_4184_:
{
lean_object* v___x_4188_; 
if (v_isShared_4186_ == 0)
{
v___x_4188_ = v___x_4185_;
goto v_reusejp_4187_;
}
else
{
lean_object* v_reuseFailAlloc_4189_; 
v_reuseFailAlloc_4189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4189_, 0, v_a_4183_);
v___x_4188_ = v_reuseFailAlloc_4189_;
goto v_reusejp_4187_;
}
v_reusejp_4187_:
{
return v___x_4188_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesAnd___boxed(lean_object* v_mvarId_4191_, lean_object* v_a_4192_, lean_object* v_a_4193_, lean_object* v_a_4194_, lean_object* v_a_4195_, lean_object* v_a_4196_){
_start:
{
lean_object* v_res_4197_; 
v_res_4197_ = l_Lean_MVarId_casesAnd(v_mvarId_4191_, v_a_4192_, v_a_4193_, v_a_4194_, v_a_4195_);
lean_dec(v_a_4195_);
lean_dec_ref(v_a_4194_);
lean_dec(v_a_4193_);
lean_dec_ref(v_a_4192_);
return v_res_4197_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_substEqs___lam__0(lean_object* v_localDecl_4198_, lean_object* v___y_4199_, lean_object* v___y_4200_, lean_object* v___y_4201_, lean_object* v___y_4202_){
_start:
{
lean_object* v___x_4204_; lean_object* v___x_4205_; lean_object* v_a_4206_; lean_object* v___x_4208_; uint8_t v_isShared_4209_; uint8_t v_isSharedCheck_4220_; 
v___x_4204_ = l_Lean_LocalDecl_type(v_localDecl_4198_);
v___x_4205_ = l_Lean_instantiateMVars___at___00Lean_MVarId_casesAnd_spec__0___redArg(v___x_4204_, v___y_4200_);
v_a_4206_ = lean_ctor_get(v___x_4205_, 0);
v_isSharedCheck_4220_ = !lean_is_exclusive(v___x_4205_);
if (v_isSharedCheck_4220_ == 0)
{
v___x_4208_ = v___x_4205_;
v_isShared_4209_ = v_isSharedCheck_4220_;
goto v_resetjp_4207_;
}
else
{
lean_inc(v_a_4206_);
lean_dec(v___x_4205_);
v___x_4208_ = lean_box(0);
v_isShared_4209_ = v_isSharedCheck_4220_;
goto v_resetjp_4207_;
}
v_resetjp_4207_:
{
uint8_t v___x_4210_; 
v___x_4210_ = l_Lean_Expr_isEq(v_a_4206_);
if (v___x_4210_ == 0)
{
uint8_t v___x_4211_; lean_object* v___x_4212_; lean_object* v___x_4214_; 
v___x_4211_ = l_Lean_Expr_isHEq(v_a_4206_);
lean_dec(v_a_4206_);
v___x_4212_ = lean_box(v___x_4211_);
if (v_isShared_4209_ == 0)
{
lean_ctor_set(v___x_4208_, 0, v___x_4212_);
v___x_4214_ = v___x_4208_;
goto v_reusejp_4213_;
}
else
{
lean_object* v_reuseFailAlloc_4215_; 
v_reuseFailAlloc_4215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4215_, 0, v___x_4212_);
v___x_4214_ = v_reuseFailAlloc_4215_;
goto v_reusejp_4213_;
}
v_reusejp_4213_:
{
return v___x_4214_;
}
}
else
{
lean_object* v___x_4216_; lean_object* v___x_4218_; 
lean_dec(v_a_4206_);
v___x_4216_ = lean_box(v___x_4210_);
if (v_isShared_4209_ == 0)
{
lean_ctor_set(v___x_4208_, 0, v___x_4216_);
v___x_4218_ = v___x_4208_;
goto v_reusejp_4217_;
}
else
{
lean_object* v_reuseFailAlloc_4219_; 
v_reuseFailAlloc_4219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4219_, 0, v___x_4216_);
v___x_4218_ = v_reuseFailAlloc_4219_;
goto v_reusejp_4217_;
}
v_reusejp_4217_:
{
return v___x_4218_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_substEqs___lam__0___boxed(lean_object* v_localDecl_4221_, lean_object* v___y_4222_, lean_object* v___y_4223_, lean_object* v___y_4224_, lean_object* v___y_4225_, lean_object* v___y_4226_){
_start:
{
lean_object* v_res_4227_; 
v_res_4227_ = l_Lean_MVarId_substEqs___lam__0(v_localDecl_4221_, v___y_4222_, v___y_4223_, v___y_4224_, v___y_4225_);
lean_dec(v___y_4225_);
lean_dec_ref(v___y_4224_);
lean_dec(v___y_4223_);
lean_dec_ref(v___y_4222_);
lean_dec_ref(v_localDecl_4221_);
return v_res_4227_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_substEqs(lean_object* v_mvarId_4229_, lean_object* v_a_4230_, lean_object* v_a_4231_, lean_object* v_a_4232_, lean_object* v_a_4233_){
_start:
{
lean_object* v___f_4235_; lean_object* v___x_4236_; 
v___f_4235_ = ((lean_object*)(l_Lean_MVarId_substEqs___closed__0));
v___x_4236_ = l_Lean_MVarId_casesRec(v_mvarId_4229_, v___f_4235_, v_a_4230_, v_a_4231_, v_a_4232_, v_a_4233_);
if (lean_obj_tag(v___x_4236_) == 0)
{
lean_object* v_a_4237_; lean_object* v___x_4238_; lean_object* v___x_4239_; 
v_a_4237_ = lean_ctor_get(v___x_4236_, 0);
lean_inc(v_a_4237_);
lean_dec_ref_known(v___x_4236_, 1);
v___x_4238_ = lean_obj_once(&l_Lean_MVarId_casesAnd___closed__3, &l_Lean_MVarId_casesAnd___closed__3_once, _init_l_Lean_MVarId_casesAnd___closed__3);
v___x_4239_ = l_Lean_Meta_ensureAtMostOne(v_a_4237_, v___x_4238_, v_a_4230_, v_a_4231_, v_a_4232_, v_a_4233_);
lean_dec(v_a_4237_);
return v___x_4239_;
}
else
{
lean_object* v_a_4240_; lean_object* v___x_4242_; uint8_t v_isShared_4243_; uint8_t v_isSharedCheck_4247_; 
v_a_4240_ = lean_ctor_get(v___x_4236_, 0);
v_isSharedCheck_4247_ = !lean_is_exclusive(v___x_4236_);
if (v_isSharedCheck_4247_ == 0)
{
v___x_4242_ = v___x_4236_;
v_isShared_4243_ = v_isSharedCheck_4247_;
goto v_resetjp_4241_;
}
else
{
lean_inc(v_a_4240_);
lean_dec(v___x_4236_);
v___x_4242_ = lean_box(0);
v_isShared_4243_ = v_isSharedCheck_4247_;
goto v_resetjp_4241_;
}
v_resetjp_4241_:
{
lean_object* v___x_4245_; 
if (v_isShared_4243_ == 0)
{
v___x_4245_ = v___x_4242_;
goto v_reusejp_4244_;
}
else
{
lean_object* v_reuseFailAlloc_4246_; 
v_reuseFailAlloc_4246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4246_, 0, v_a_4240_);
v___x_4245_ = v_reuseFailAlloc_4246_;
goto v_reusejp_4244_;
}
v_reusejp_4244_:
{
return v___x_4245_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_substEqs___boxed(lean_object* v_mvarId_4248_, lean_object* v_a_4249_, lean_object* v_a_4250_, lean_object* v_a_4251_, lean_object* v_a_4252_, lean_object* v_a_4253_){
_start:
{
lean_object* v_res_4254_; 
v_res_4254_ = l_Lean_MVarId_substEqs(v_mvarId_4248_, v_a_4249_, v_a_4250_, v_a_4251_, v_a_4252_);
lean_dec(v_a_4252_);
lean_dec_ref(v_a_4251_);
lean_dec(v_a_4250_);
lean_dec_ref(v_a_4249_);
return v_res_4254_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkByCasesSubgoal___lam__0(lean_object* v_goalType_4255_, lean_object* v_tag_4256_, lean_object* v_hyp_4257_, lean_object* v___y_4258_, lean_object* v___y_4259_, lean_object* v___y_4260_, lean_object* v___y_4261_){
_start:
{
lean_object* v___x_4263_; 
v___x_4263_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_goalType_4255_, v_tag_4256_, v___y_4258_, v___y_4259_, v___y_4260_, v___y_4261_);
if (lean_obj_tag(v___x_4263_) == 0)
{
lean_object* v_a_4264_; lean_object* v___x_4265_; lean_object* v___x_4266_; lean_object* v___x_4267_; uint8_t v___x_4268_; uint8_t v___x_4269_; uint8_t v___x_4270_; lean_object* v___x_4271_; 
v_a_4264_ = lean_ctor_get(v___x_4263_, 0);
lean_inc_n(v_a_4264_, 2);
lean_dec_ref_known(v___x_4263_, 1);
v___x_4265_ = lean_unsigned_to_nat(1u);
v___x_4266_ = lean_mk_empty_array_with_capacity(v___x_4265_);
lean_inc_ref(v_hyp_4257_);
v___x_4267_ = lean_array_push(v___x_4266_, v_hyp_4257_);
v___x_4268_ = 0;
v___x_4269_ = 1;
v___x_4270_ = 1;
v___x_4271_ = l_Lean_Meta_mkLambdaFVars(v___x_4267_, v_a_4264_, v___x_4268_, v___x_4269_, v___x_4268_, v___x_4269_, v___x_4270_, v___y_4258_, v___y_4259_, v___y_4260_, v___y_4261_);
lean_dec_ref(v___x_4267_);
if (lean_obj_tag(v___x_4271_) == 0)
{
lean_object* v_a_4272_; lean_object* v___x_4274_; uint8_t v_isShared_4275_; uint8_t v_isSharedCheck_4283_; 
v_a_4272_ = lean_ctor_get(v___x_4271_, 0);
v_isSharedCheck_4283_ = !lean_is_exclusive(v___x_4271_);
if (v_isSharedCheck_4283_ == 0)
{
v___x_4274_ = v___x_4271_;
v_isShared_4275_ = v_isSharedCheck_4283_;
goto v_resetjp_4273_;
}
else
{
lean_inc(v_a_4272_);
lean_dec(v___x_4271_);
v___x_4274_ = lean_box(0);
v_isShared_4275_ = v_isSharedCheck_4283_;
goto v_resetjp_4273_;
}
v_resetjp_4273_:
{
lean_object* v___x_4276_; lean_object* v___x_4277_; lean_object* v___x_4278_; lean_object* v___x_4279_; lean_object* v___x_4281_; 
v___x_4276_ = l_Lean_Expr_mvarId_x21(v_a_4264_);
lean_dec(v_a_4264_);
v___x_4277_ = l_Lean_Expr_fvarId_x21(v_hyp_4257_);
lean_dec_ref(v_hyp_4257_);
v___x_4278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4278_, 0, v___x_4276_);
lean_ctor_set(v___x_4278_, 1, v___x_4277_);
v___x_4279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4279_, 0, v_a_4272_);
lean_ctor_set(v___x_4279_, 1, v___x_4278_);
if (v_isShared_4275_ == 0)
{
lean_ctor_set(v___x_4274_, 0, v___x_4279_);
v___x_4281_ = v___x_4274_;
goto v_reusejp_4280_;
}
else
{
lean_object* v_reuseFailAlloc_4282_; 
v_reuseFailAlloc_4282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4282_, 0, v___x_4279_);
v___x_4281_ = v_reuseFailAlloc_4282_;
goto v_reusejp_4280_;
}
v_reusejp_4280_:
{
return v___x_4281_;
}
}
}
else
{
lean_object* v_a_4284_; lean_object* v___x_4286_; uint8_t v_isShared_4287_; uint8_t v_isSharedCheck_4291_; 
lean_dec(v_a_4264_);
lean_dec_ref(v_hyp_4257_);
v_a_4284_ = lean_ctor_get(v___x_4271_, 0);
v_isSharedCheck_4291_ = !lean_is_exclusive(v___x_4271_);
if (v_isSharedCheck_4291_ == 0)
{
v___x_4286_ = v___x_4271_;
v_isShared_4287_ = v_isSharedCheck_4291_;
goto v_resetjp_4285_;
}
else
{
lean_inc(v_a_4284_);
lean_dec(v___x_4271_);
v___x_4286_ = lean_box(0);
v_isShared_4287_ = v_isSharedCheck_4291_;
goto v_resetjp_4285_;
}
v_resetjp_4285_:
{
lean_object* v___x_4289_; 
if (v_isShared_4287_ == 0)
{
v___x_4289_ = v___x_4286_;
goto v_reusejp_4288_;
}
else
{
lean_object* v_reuseFailAlloc_4290_; 
v_reuseFailAlloc_4290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4290_, 0, v_a_4284_);
v___x_4289_ = v_reuseFailAlloc_4290_;
goto v_reusejp_4288_;
}
v_reusejp_4288_:
{
return v___x_4289_;
}
}
}
}
else
{
lean_object* v_a_4292_; lean_object* v___x_4294_; uint8_t v_isShared_4295_; uint8_t v_isSharedCheck_4299_; 
lean_dec_ref(v_hyp_4257_);
v_a_4292_ = lean_ctor_get(v___x_4263_, 0);
v_isSharedCheck_4299_ = !lean_is_exclusive(v___x_4263_);
if (v_isSharedCheck_4299_ == 0)
{
v___x_4294_ = v___x_4263_;
v_isShared_4295_ = v_isSharedCheck_4299_;
goto v_resetjp_4293_;
}
else
{
lean_inc(v_a_4292_);
lean_dec(v___x_4263_);
v___x_4294_ = lean_box(0);
v_isShared_4295_ = v_isSharedCheck_4299_;
goto v_resetjp_4293_;
}
v_resetjp_4293_:
{
lean_object* v___x_4297_; 
if (v_isShared_4295_ == 0)
{
v___x_4297_ = v___x_4294_;
goto v_reusejp_4296_;
}
else
{
lean_object* v_reuseFailAlloc_4298_; 
v_reuseFailAlloc_4298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4298_, 0, v_a_4292_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkByCasesSubgoal___lam__0___boxed(lean_object* v_goalType_4300_, lean_object* v_tag_4301_, lean_object* v_hyp_4302_, lean_object* v___y_4303_, lean_object* v___y_4304_, lean_object* v___y_4305_, lean_object* v___y_4306_, lean_object* v___y_4307_){
_start:
{
lean_object* v_res_4308_; 
v_res_4308_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkByCasesSubgoal___lam__0(v_goalType_4300_, v_tag_4301_, v_hyp_4302_, v___y_4303_, v___y_4304_, v___y_4305_, v___y_4306_);
lean_dec(v___y_4306_);
lean_dec_ref(v___y_4305_);
lean_dec(v___y_4304_);
lean_dec_ref(v___y_4303_);
return v_res_4308_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkByCasesSubgoal(lean_object* v_p_4309_, lean_object* v_hName_4310_, lean_object* v_goalType_4311_, lean_object* v_tag_4312_, lean_object* v_a_4313_, lean_object* v_a_4314_, lean_object* v_a_4315_, lean_object* v_a_4316_){
_start:
{
lean_object* v___f_4318_; lean_object* v___x_4319_; 
v___f_4318_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkByCasesSubgoal___lam__0___boxed), 8, 2);
lean_closure_set(v___f_4318_, 0, v_goalType_4311_);
lean_closure_set(v___f_4318_, 1, v_tag_4312_);
v___x_4319_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop_spec__0___redArg(v_hName_4310_, v_p_4309_, v___f_4318_, v_a_4313_, v_a_4314_, v_a_4315_, v_a_4316_);
return v___x_4319_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkByCasesSubgoal___boxed(lean_object* v_p_4320_, lean_object* v_hName_4321_, lean_object* v_goalType_4322_, lean_object* v_tag_4323_, lean_object* v_a_4324_, lean_object* v_a_4325_, lean_object* v_a_4326_, lean_object* v_a_4327_, lean_object* v_a_4328_){
_start:
{
lean_object* v_res_4329_; 
v_res_4329_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkByCasesSubgoal(v_p_4320_, v_hName_4321_, v_goalType_4322_, v_tag_4323_, v_a_4324_, v_a_4325_, v_a_4326_, v_a_4327_);
lean_dec(v_a_4327_);
lean_dec_ref(v_a_4326_);
lean_dec(v_a_4325_);
lean_dec_ref(v_a_4324_);
return v_res_4329_;
}
}
static lean_object* _init_l_Lean_MVarId_byCases___lam__0___closed__7(void){
_start:
{
lean_object* v___x_4341_; lean_object* v___x_4342_; lean_object* v___x_4343_; 
v___x_4341_ = lean_box(0);
v___x_4342_ = ((lean_object*)(l_Lean_MVarId_byCases___lam__0___closed__6));
v___x_4343_ = l_Lean_Expr_const___override(v___x_4342_, v___x_4341_);
return v___x_4343_;
}
}
static lean_object* _init_l_Lean_MVarId_byCases___lam__0___closed__10(void){
_start:
{
lean_object* v___x_4347_; lean_object* v___x_4348_; 
v___x_4347_ = ((lean_object*)(l_Lean_MVarId_byCases___lam__0___closed__9));
v___x_4348_ = l_Lean_stringToMessageData(v___x_4347_);
return v___x_4348_;
}
}
static lean_object* _init_l_Lean_MVarId_byCases___lam__0___closed__11(void){
_start:
{
lean_object* v___x_4349_; lean_object* v___x_4350_; 
v___x_4349_ = lean_obj_once(&l_Lean_MVarId_byCases___lam__0___closed__10, &l_Lean_MVarId_byCases___lam__0___closed__10_once, _init_l_Lean_MVarId_byCases___lam__0___closed__10);
v___x_4350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4350_, 0, v___x_4349_);
return v___x_4350_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_byCases___lam__0(lean_object* v_mvarId_4351_, lean_object* v_p_4352_, lean_object* v_hName_4353_, lean_object* v___y_4354_, lean_object* v___y_4355_, lean_object* v___y_4356_, lean_object* v___y_4357_){
_start:
{
lean_object* v___x_4359_; 
lean_inc(v_mvarId_4351_);
v___x_4359_ = l_Lean_MVarId_getType(v_mvarId_4351_, v___y_4354_, v___y_4355_, v___y_4356_, v___y_4357_);
if (lean_obj_tag(v___x_4359_) == 0)
{
lean_object* v_a_4360_; lean_object* v___x_4361_; 
v_a_4360_ = lean_ctor_get(v___x_4359_, 0);
lean_inc(v_a_4360_);
lean_dec_ref_known(v___x_4359_, 1);
lean_inc(v_mvarId_4351_);
v___x_4361_ = l_Lean_MVarId_getTag(v_mvarId_4351_, v___y_4354_, v___y_4355_, v___y_4356_, v___y_4357_);
if (lean_obj_tag(v___x_4361_) == 0)
{
lean_object* v_a_4362_; lean_object* v___y_4364_; lean_object* v___y_4365_; lean_object* v___y_4366_; lean_object* v___y_4367_; lean_object* v___x_4415_; 
v_a_4362_ = lean_ctor_get(v___x_4361_, 0);
lean_inc(v_a_4362_);
lean_dec_ref_known(v___x_4361_, 1);
lean_inc(v_a_4360_);
v___x_4415_ = l_Lean_Meta_isProp(v_a_4360_, v___y_4354_, v___y_4355_, v___y_4356_, v___y_4357_);
if (lean_obj_tag(v___x_4415_) == 0)
{
lean_object* v_a_4416_; uint8_t v___x_4417_; 
v_a_4416_ = lean_ctor_get(v___x_4415_, 0);
lean_inc(v_a_4416_);
lean_dec_ref_known(v___x_4415_, 1);
v___x_4417_ = lean_unbox(v_a_4416_);
lean_dec(v_a_4416_);
if (v___x_4417_ == 0)
{
lean_object* v___x_4418_; lean_object* v___x_4419_; lean_object* v___x_4420_; 
v___x_4418_ = ((lean_object*)(l_Lean_MVarId_byCases___lam__0___closed__8));
v___x_4419_ = lean_obj_once(&l_Lean_MVarId_byCases___lam__0___closed__11, &l_Lean_MVarId_byCases___lam__0___closed__11_once, _init_l_Lean_MVarId_byCases___lam__0___closed__11);
lean_inc(v_mvarId_4351_);
v___x_4420_ = l_Lean_Meta_throwTacticEx___redArg(v___x_4418_, v_mvarId_4351_, v___x_4419_, v___y_4354_, v___y_4355_, v___y_4356_, v___y_4357_);
if (lean_obj_tag(v___x_4420_) == 0)
{
lean_dec_ref_known(v___x_4420_, 1);
v___y_4364_ = v___y_4354_;
v___y_4365_ = v___y_4355_;
v___y_4366_ = v___y_4356_;
v___y_4367_ = v___y_4357_;
goto v___jp_4363_;
}
else
{
lean_object* v_a_4421_; lean_object* v___x_4423_; uint8_t v_isShared_4424_; uint8_t v_isSharedCheck_4428_; 
lean_dec(v_a_4362_);
lean_dec(v_a_4360_);
lean_dec(v_hName_4353_);
lean_dec_ref(v_p_4352_);
lean_dec(v_mvarId_4351_);
v_a_4421_ = lean_ctor_get(v___x_4420_, 0);
v_isSharedCheck_4428_ = !lean_is_exclusive(v___x_4420_);
if (v_isSharedCheck_4428_ == 0)
{
v___x_4423_ = v___x_4420_;
v_isShared_4424_ = v_isSharedCheck_4428_;
goto v_resetjp_4422_;
}
else
{
lean_inc(v_a_4421_);
lean_dec(v___x_4420_);
v___x_4423_ = lean_box(0);
v_isShared_4424_ = v_isSharedCheck_4428_;
goto v_resetjp_4422_;
}
v_resetjp_4422_:
{
lean_object* v___x_4426_; 
if (v_isShared_4424_ == 0)
{
v___x_4426_ = v___x_4423_;
goto v_reusejp_4425_;
}
else
{
lean_object* v_reuseFailAlloc_4427_; 
v_reuseFailAlloc_4427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4427_, 0, v_a_4421_);
v___x_4426_ = v_reuseFailAlloc_4427_;
goto v_reusejp_4425_;
}
v_reusejp_4425_:
{
return v___x_4426_;
}
}
}
}
else
{
v___y_4364_ = v___y_4354_;
v___y_4365_ = v___y_4355_;
v___y_4366_ = v___y_4356_;
v___y_4367_ = v___y_4357_;
goto v___jp_4363_;
}
}
else
{
lean_object* v_a_4429_; lean_object* v___x_4431_; uint8_t v_isShared_4432_; uint8_t v_isSharedCheck_4436_; 
lean_dec(v_a_4362_);
lean_dec(v_a_4360_);
lean_dec(v_hName_4353_);
lean_dec_ref(v_p_4352_);
lean_dec(v_mvarId_4351_);
v_a_4429_ = lean_ctor_get(v___x_4415_, 0);
v_isSharedCheck_4436_ = !lean_is_exclusive(v___x_4415_);
if (v_isSharedCheck_4436_ == 0)
{
v___x_4431_ = v___x_4415_;
v_isShared_4432_ = v_isSharedCheck_4436_;
goto v_resetjp_4430_;
}
else
{
lean_inc(v_a_4429_);
lean_dec(v___x_4415_);
v___x_4431_ = lean_box(0);
v_isShared_4432_ = v_isSharedCheck_4436_;
goto v_resetjp_4430_;
}
v_resetjp_4430_:
{
lean_object* v___x_4434_; 
if (v_isShared_4432_ == 0)
{
v___x_4434_ = v___x_4431_;
goto v_reusejp_4433_;
}
else
{
lean_object* v_reuseFailAlloc_4435_; 
v_reuseFailAlloc_4435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4435_, 0, v_a_4429_);
v___x_4434_ = v_reuseFailAlloc_4435_;
goto v_reusejp_4433_;
}
v_reusejp_4433_:
{
return v___x_4434_;
}
}
}
v___jp_4363_:
{
lean_object* v___x_4368_; lean_object* v___x_4369_; lean_object* v___x_4370_; 
v___x_4368_ = ((lean_object*)(l_Lean_MVarId_byCases___lam__0___closed__1));
lean_inc(v_a_4362_);
v___x_4369_ = l_Lean_Name_append(v_a_4362_, v___x_4368_);
lean_inc(v_a_4360_);
lean_inc(v_hName_4353_);
lean_inc_ref(v_p_4352_);
v___x_4370_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkByCasesSubgoal(v_p_4352_, v_hName_4353_, v_a_4360_, v___x_4369_, v___y_4364_, v___y_4365_, v___y_4366_, v___y_4367_);
if (lean_obj_tag(v___x_4370_) == 0)
{
lean_object* v_a_4371_; lean_object* v_fst_4372_; lean_object* v_snd_4373_; lean_object* v___x_4374_; lean_object* v___x_4375_; lean_object* v___x_4376_; lean_object* v___x_4377_; 
v_a_4371_ = lean_ctor_get(v___x_4370_, 0);
lean_inc(v_a_4371_);
lean_dec_ref_known(v___x_4370_, 1);
v_fst_4372_ = lean_ctor_get(v_a_4371_, 0);
lean_inc(v_fst_4372_);
v_snd_4373_ = lean_ctor_get(v_a_4371_, 1);
lean_inc(v_snd_4373_);
lean_dec(v_a_4371_);
lean_inc_ref(v_p_4352_);
v___x_4374_ = l_Lean_mkNot(v_p_4352_);
v___x_4375_ = ((lean_object*)(l_Lean_MVarId_byCases___lam__0___closed__3));
v___x_4376_ = l_Lean_Name_append(v_a_4362_, v___x_4375_);
lean_inc(v_a_4360_);
v___x_4377_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkByCasesSubgoal(v___x_4374_, v_hName_4353_, v_a_4360_, v___x_4376_, v___y_4364_, v___y_4365_, v___y_4366_, v___y_4367_);
if (lean_obj_tag(v___x_4377_) == 0)
{
lean_object* v_a_4378_; lean_object* v_fst_4379_; lean_object* v_snd_4380_; lean_object* v___x_4382_; uint8_t v_isShared_4383_; uint8_t v_isSharedCheck_4398_; 
v_a_4378_ = lean_ctor_get(v___x_4377_, 0);
lean_inc(v_a_4378_);
lean_dec_ref_known(v___x_4377_, 1);
v_fst_4379_ = lean_ctor_get(v_a_4378_, 0);
v_snd_4380_ = lean_ctor_get(v_a_4378_, 1);
v_isSharedCheck_4398_ = !lean_is_exclusive(v_a_4378_);
if (v_isSharedCheck_4398_ == 0)
{
v___x_4382_ = v_a_4378_;
v_isShared_4383_ = v_isSharedCheck_4398_;
goto v_resetjp_4381_;
}
else
{
lean_inc(v_snd_4380_);
lean_inc(v_fst_4379_);
lean_dec(v_a_4378_);
v___x_4382_ = lean_box(0);
v_isShared_4383_ = v_isSharedCheck_4398_;
goto v_resetjp_4381_;
}
v_resetjp_4381_:
{
lean_object* v___x_4384_; lean_object* v___x_4385_; lean_object* v___x_4386_; lean_object* v___x_4388_; uint8_t v_isShared_4389_; uint8_t v_isSharedCheck_4396_; 
v___x_4384_ = lean_obj_once(&l_Lean_MVarId_byCases___lam__0___closed__7, &l_Lean_MVarId_byCases___lam__0___closed__7_once, _init_l_Lean_MVarId_byCases___lam__0___closed__7);
v___x_4385_ = l_Lean_mkApp4(v___x_4384_, v_p_4352_, v_a_4360_, v_fst_4372_, v_fst_4379_);
v___x_4386_ = l_Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1___redArg(v_mvarId_4351_, v___x_4385_, v___y_4365_);
v_isSharedCheck_4396_ = !lean_is_exclusive(v___x_4386_);
if (v_isSharedCheck_4396_ == 0)
{
lean_object* v_unused_4397_; 
v_unused_4397_ = lean_ctor_get(v___x_4386_, 0);
lean_dec(v_unused_4397_);
v___x_4388_ = v___x_4386_;
v_isShared_4389_ = v_isSharedCheck_4396_;
goto v_resetjp_4387_;
}
else
{
lean_dec(v___x_4386_);
v___x_4388_ = lean_box(0);
v_isShared_4389_ = v_isSharedCheck_4396_;
goto v_resetjp_4387_;
}
v_resetjp_4387_:
{
lean_object* v___x_4391_; 
if (v_isShared_4383_ == 0)
{
lean_ctor_set(v___x_4382_, 0, v_snd_4373_);
v___x_4391_ = v___x_4382_;
goto v_reusejp_4390_;
}
else
{
lean_object* v_reuseFailAlloc_4395_; 
v_reuseFailAlloc_4395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4395_, 0, v_snd_4373_);
lean_ctor_set(v_reuseFailAlloc_4395_, 1, v_snd_4380_);
v___x_4391_ = v_reuseFailAlloc_4395_;
goto v_reusejp_4390_;
}
v_reusejp_4390_:
{
lean_object* v___x_4393_; 
if (v_isShared_4389_ == 0)
{
lean_ctor_set(v___x_4388_, 0, v___x_4391_);
v___x_4393_ = v___x_4388_;
goto v_reusejp_4392_;
}
else
{
lean_object* v_reuseFailAlloc_4394_; 
v_reuseFailAlloc_4394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4394_, 0, v___x_4391_);
v___x_4393_ = v_reuseFailAlloc_4394_;
goto v_reusejp_4392_;
}
v_reusejp_4392_:
{
return v___x_4393_;
}
}
}
}
}
else
{
lean_object* v_a_4399_; lean_object* v___x_4401_; uint8_t v_isShared_4402_; uint8_t v_isSharedCheck_4406_; 
lean_dec(v_snd_4373_);
lean_dec(v_fst_4372_);
lean_dec(v_a_4360_);
lean_dec_ref(v_p_4352_);
lean_dec(v_mvarId_4351_);
v_a_4399_ = lean_ctor_get(v___x_4377_, 0);
v_isSharedCheck_4406_ = !lean_is_exclusive(v___x_4377_);
if (v_isSharedCheck_4406_ == 0)
{
v___x_4401_ = v___x_4377_;
v_isShared_4402_ = v_isSharedCheck_4406_;
goto v_resetjp_4400_;
}
else
{
lean_inc(v_a_4399_);
lean_dec(v___x_4377_);
v___x_4401_ = lean_box(0);
v_isShared_4402_ = v_isSharedCheck_4406_;
goto v_resetjp_4400_;
}
v_resetjp_4400_:
{
lean_object* v___x_4404_; 
if (v_isShared_4402_ == 0)
{
v___x_4404_ = v___x_4401_;
goto v_reusejp_4403_;
}
else
{
lean_object* v_reuseFailAlloc_4405_; 
v_reuseFailAlloc_4405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4405_, 0, v_a_4399_);
v___x_4404_ = v_reuseFailAlloc_4405_;
goto v_reusejp_4403_;
}
v_reusejp_4403_:
{
return v___x_4404_;
}
}
}
}
else
{
lean_object* v_a_4407_; lean_object* v___x_4409_; uint8_t v_isShared_4410_; uint8_t v_isSharedCheck_4414_; 
lean_dec(v_a_4362_);
lean_dec(v_a_4360_);
lean_dec(v_hName_4353_);
lean_dec_ref(v_p_4352_);
lean_dec(v_mvarId_4351_);
v_a_4407_ = lean_ctor_get(v___x_4370_, 0);
v_isSharedCheck_4414_ = !lean_is_exclusive(v___x_4370_);
if (v_isSharedCheck_4414_ == 0)
{
v___x_4409_ = v___x_4370_;
v_isShared_4410_ = v_isSharedCheck_4414_;
goto v_resetjp_4408_;
}
else
{
lean_inc(v_a_4407_);
lean_dec(v___x_4370_);
v___x_4409_ = lean_box(0);
v_isShared_4410_ = v_isSharedCheck_4414_;
goto v_resetjp_4408_;
}
v_resetjp_4408_:
{
lean_object* v___x_4412_; 
if (v_isShared_4410_ == 0)
{
v___x_4412_ = v___x_4409_;
goto v_reusejp_4411_;
}
else
{
lean_object* v_reuseFailAlloc_4413_; 
v_reuseFailAlloc_4413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4413_, 0, v_a_4407_);
v___x_4412_ = v_reuseFailAlloc_4413_;
goto v_reusejp_4411_;
}
v_reusejp_4411_:
{
return v___x_4412_;
}
}
}
}
}
else
{
lean_object* v_a_4437_; lean_object* v___x_4439_; uint8_t v_isShared_4440_; uint8_t v_isSharedCheck_4444_; 
lean_dec(v_a_4360_);
lean_dec(v_hName_4353_);
lean_dec_ref(v_p_4352_);
lean_dec(v_mvarId_4351_);
v_a_4437_ = lean_ctor_get(v___x_4361_, 0);
v_isSharedCheck_4444_ = !lean_is_exclusive(v___x_4361_);
if (v_isSharedCheck_4444_ == 0)
{
v___x_4439_ = v___x_4361_;
v_isShared_4440_ = v_isSharedCheck_4444_;
goto v_resetjp_4438_;
}
else
{
lean_inc(v_a_4437_);
lean_dec(v___x_4361_);
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
lean_dec(v_hName_4353_);
lean_dec_ref(v_p_4352_);
lean_dec(v_mvarId_4351_);
v_a_4445_ = lean_ctor_get(v___x_4359_, 0);
v_isSharedCheck_4452_ = !lean_is_exclusive(v___x_4359_);
if (v_isSharedCheck_4452_ == 0)
{
v___x_4447_ = v___x_4359_;
v_isShared_4448_ = v_isSharedCheck_4452_;
goto v_resetjp_4446_;
}
else
{
lean_inc(v_a_4445_);
lean_dec(v___x_4359_);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_byCases___lam__0___boxed(lean_object* v_mvarId_4453_, lean_object* v_p_4454_, lean_object* v_hName_4455_, lean_object* v___y_4456_, lean_object* v___y_4457_, lean_object* v___y_4458_, lean_object* v___y_4459_, lean_object* v___y_4460_){
_start:
{
lean_object* v_res_4461_; 
v_res_4461_ = l_Lean_MVarId_byCases___lam__0(v_mvarId_4453_, v_p_4454_, v_hName_4455_, v___y_4456_, v___y_4457_, v___y_4458_, v___y_4459_);
lean_dec(v___y_4459_);
lean_dec_ref(v___y_4458_);
lean_dec(v___y_4457_);
lean_dec_ref(v___y_4456_);
return v_res_4461_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_byCases(lean_object* v_mvarId_4462_, lean_object* v_p_4463_, lean_object* v_hName_4464_, lean_object* v_a_4465_, lean_object* v_a_4466_, lean_object* v_a_4467_, lean_object* v_a_4468_){
_start:
{
lean_object* v___f_4470_; lean_object* v___x_4471_; 
lean_inc(v_mvarId_4462_);
v___f_4470_ = lean_alloc_closure((void*)(l_Lean_MVarId_byCases___lam__0___boxed), 8, 3);
lean_closure_set(v___f_4470_, 0, v_mvarId_4462_);
lean_closure_set(v___f_4470_, 1, v_p_4463_);
lean_closure_set(v___f_4470_, 2, v_hName_4464_);
v___x_4471_ = l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2___redArg(v_mvarId_4462_, v___f_4470_, v_a_4465_, v_a_4466_, v_a_4467_, v_a_4468_);
return v___x_4471_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_byCases___boxed(lean_object* v_mvarId_4472_, lean_object* v_p_4473_, lean_object* v_hName_4474_, lean_object* v_a_4475_, lean_object* v_a_4476_, lean_object* v_a_4477_, lean_object* v_a_4478_, lean_object* v_a_4479_){
_start:
{
lean_object* v_res_4480_; 
v_res_4480_ = l_Lean_MVarId_byCases(v_mvarId_4472_, v_p_4473_, v_hName_4474_, v_a_4475_, v_a_4476_, v_a_4477_, v_a_4478_);
lean_dec(v_a_4478_);
lean_dec_ref(v_a_4477_);
lean_dec(v_a_4476_);
lean_dec_ref(v_a_4475_);
return v_res_4480_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_byCasesDec___lam__0(lean_object* v_mvarId_4484_, lean_object* v_p_4485_, lean_object* v_hName_4486_, lean_object* v_dec_4487_, lean_object* v___y_4488_, lean_object* v___y_4489_, lean_object* v___y_4490_, lean_object* v___y_4491_){
_start:
{
lean_object* v___x_4493_; 
lean_inc(v_mvarId_4484_);
v___x_4493_ = l_Lean_MVarId_getType(v_mvarId_4484_, v___y_4488_, v___y_4489_, v___y_4490_, v___y_4491_);
if (lean_obj_tag(v___x_4493_) == 0)
{
lean_object* v_a_4494_; lean_object* v___x_4495_; 
v_a_4494_ = lean_ctor_get(v___x_4493_, 0);
lean_inc(v_a_4494_);
lean_dec_ref_known(v___x_4493_, 1);
lean_inc(v_mvarId_4484_);
v___x_4495_ = l_Lean_MVarId_getTag(v_mvarId_4484_, v___y_4488_, v___y_4489_, v___y_4490_, v___y_4491_);
if (lean_obj_tag(v___x_4495_) == 0)
{
lean_object* v_a_4496_; lean_object* v___x_4497_; 
v_a_4496_ = lean_ctor_get(v___x_4495_, 0);
lean_inc(v_a_4496_);
lean_dec_ref_known(v___x_4495_, 1);
lean_inc(v_a_4494_);
v___x_4497_ = l_Lean_Meta_getLevel(v_a_4494_, v___y_4488_, v___y_4489_, v___y_4490_, v___y_4491_);
if (lean_obj_tag(v___x_4497_) == 0)
{
lean_object* v_a_4498_; lean_object* v___x_4499_; lean_object* v___x_4500_; lean_object* v___x_4501_; 
v_a_4498_ = lean_ctor_get(v___x_4497_, 0);
lean_inc(v_a_4498_);
lean_dec_ref_known(v___x_4497_, 1);
v___x_4499_ = ((lean_object*)(l_Lean_MVarId_byCases___lam__0___closed__1));
lean_inc(v_a_4496_);
v___x_4500_ = l_Lean_Name_append(v_a_4496_, v___x_4499_);
lean_inc(v_a_4494_);
lean_inc(v_hName_4486_);
lean_inc_ref(v_p_4485_);
v___x_4501_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkByCasesSubgoal(v_p_4485_, v_hName_4486_, v_a_4494_, v___x_4500_, v___y_4488_, v___y_4489_, v___y_4490_, v___y_4491_);
if (lean_obj_tag(v___x_4501_) == 0)
{
lean_object* v_a_4502_; lean_object* v_fst_4503_; lean_object* v_snd_4504_; lean_object* v___x_4506_; uint8_t v_isShared_4507_; uint8_t v_isSharedCheck_4546_; 
v_a_4502_ = lean_ctor_get(v___x_4501_, 0);
lean_inc(v_a_4502_);
lean_dec_ref_known(v___x_4501_, 1);
v_fst_4503_ = lean_ctor_get(v_a_4502_, 0);
v_snd_4504_ = lean_ctor_get(v_a_4502_, 1);
v_isSharedCheck_4546_ = !lean_is_exclusive(v_a_4502_);
if (v_isSharedCheck_4546_ == 0)
{
v___x_4506_ = v_a_4502_;
v_isShared_4507_ = v_isSharedCheck_4546_;
goto v_resetjp_4505_;
}
else
{
lean_inc(v_snd_4504_);
lean_inc(v_fst_4503_);
lean_dec(v_a_4502_);
v___x_4506_ = lean_box(0);
v_isShared_4507_ = v_isSharedCheck_4546_;
goto v_resetjp_4505_;
}
v_resetjp_4505_:
{
lean_object* v___x_4508_; lean_object* v___x_4509_; lean_object* v___x_4510_; lean_object* v___x_4511_; 
lean_inc_ref(v_p_4485_);
v___x_4508_ = l_Lean_mkNot(v_p_4485_);
v___x_4509_ = ((lean_object*)(l_Lean_MVarId_byCases___lam__0___closed__3));
v___x_4510_ = l_Lean_Name_append(v_a_4496_, v___x_4509_);
lean_inc(v_a_4494_);
v___x_4511_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkByCasesSubgoal(v___x_4508_, v_hName_4486_, v_a_4494_, v___x_4510_, v___y_4488_, v___y_4489_, v___y_4490_, v___y_4491_);
if (lean_obj_tag(v___x_4511_) == 0)
{
lean_object* v_a_4512_; lean_object* v_fst_4513_; lean_object* v_snd_4514_; lean_object* v___x_4516_; uint8_t v_isShared_4517_; uint8_t v_isSharedCheck_4537_; 
v_a_4512_ = lean_ctor_get(v___x_4511_, 0);
lean_inc(v_a_4512_);
lean_dec_ref_known(v___x_4511_, 1);
v_fst_4513_ = lean_ctor_get(v_a_4512_, 0);
v_snd_4514_ = lean_ctor_get(v_a_4512_, 1);
v_isSharedCheck_4537_ = !lean_is_exclusive(v_a_4512_);
if (v_isSharedCheck_4537_ == 0)
{
v___x_4516_ = v_a_4512_;
v_isShared_4517_ = v_isSharedCheck_4537_;
goto v_resetjp_4515_;
}
else
{
lean_inc(v_snd_4514_);
lean_inc(v_fst_4513_);
lean_dec(v_a_4512_);
v___x_4516_ = lean_box(0);
v_isShared_4517_ = v_isSharedCheck_4537_;
goto v_resetjp_4515_;
}
v_resetjp_4515_:
{
lean_object* v___x_4518_; lean_object* v___x_4519_; lean_object* v___x_4521_; 
v___x_4518_ = ((lean_object*)(l_Lean_MVarId_byCasesDec___lam__0___closed__1));
v___x_4519_ = lean_box(0);
if (v_isShared_4507_ == 0)
{
lean_ctor_set_tag(v___x_4506_, 1);
lean_ctor_set(v___x_4506_, 1, v___x_4519_);
lean_ctor_set(v___x_4506_, 0, v_a_4498_);
v___x_4521_ = v___x_4506_;
goto v_reusejp_4520_;
}
else
{
lean_object* v_reuseFailAlloc_4536_; 
v_reuseFailAlloc_4536_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4536_, 0, v_a_4498_);
lean_ctor_set(v_reuseFailAlloc_4536_, 1, v___x_4519_);
v___x_4521_ = v_reuseFailAlloc_4536_;
goto v_reusejp_4520_;
}
v_reusejp_4520_:
{
lean_object* v___x_4522_; lean_object* v___x_4523_; lean_object* v___x_4524_; lean_object* v___x_4526_; uint8_t v_isShared_4527_; uint8_t v_isSharedCheck_4534_; 
v___x_4522_ = l_Lean_Expr_const___override(v___x_4518_, v___x_4521_);
v___x_4523_ = l_Lean_mkApp5(v___x_4522_, v_a_4494_, v_p_4485_, v_dec_4487_, v_fst_4503_, v_fst_4513_);
v___x_4524_ = l_Lean_MVarId_assign___at___00Lean_Meta_generalizeTargetsEq_spec__1___redArg(v_mvarId_4484_, v___x_4523_, v___y_4489_);
v_isSharedCheck_4534_ = !lean_is_exclusive(v___x_4524_);
if (v_isSharedCheck_4534_ == 0)
{
lean_object* v_unused_4535_; 
v_unused_4535_ = lean_ctor_get(v___x_4524_, 0);
lean_dec(v_unused_4535_);
v___x_4526_ = v___x_4524_;
v_isShared_4527_ = v_isSharedCheck_4534_;
goto v_resetjp_4525_;
}
else
{
lean_dec(v___x_4524_);
v___x_4526_ = lean_box(0);
v_isShared_4527_ = v_isSharedCheck_4534_;
goto v_resetjp_4525_;
}
v_resetjp_4525_:
{
lean_object* v___x_4529_; 
if (v_isShared_4517_ == 0)
{
lean_ctor_set(v___x_4516_, 0, v_snd_4504_);
v___x_4529_ = v___x_4516_;
goto v_reusejp_4528_;
}
else
{
lean_object* v_reuseFailAlloc_4533_; 
v_reuseFailAlloc_4533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4533_, 0, v_snd_4504_);
lean_ctor_set(v_reuseFailAlloc_4533_, 1, v_snd_4514_);
v___x_4529_ = v_reuseFailAlloc_4533_;
goto v_reusejp_4528_;
}
v_reusejp_4528_:
{
lean_object* v___x_4531_; 
if (v_isShared_4527_ == 0)
{
lean_ctor_set(v___x_4526_, 0, v___x_4529_);
v___x_4531_ = v___x_4526_;
goto v_reusejp_4530_;
}
else
{
lean_object* v_reuseFailAlloc_4532_; 
v_reuseFailAlloc_4532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4532_, 0, v___x_4529_);
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
}
else
{
lean_object* v_a_4538_; lean_object* v___x_4540_; uint8_t v_isShared_4541_; uint8_t v_isSharedCheck_4545_; 
lean_del_object(v___x_4506_);
lean_dec(v_snd_4504_);
lean_dec(v_fst_4503_);
lean_dec(v_a_4498_);
lean_dec(v_a_4494_);
lean_dec_ref(v_dec_4487_);
lean_dec_ref(v_p_4485_);
lean_dec(v_mvarId_4484_);
v_a_4538_ = lean_ctor_get(v___x_4511_, 0);
v_isSharedCheck_4545_ = !lean_is_exclusive(v___x_4511_);
if (v_isSharedCheck_4545_ == 0)
{
v___x_4540_ = v___x_4511_;
v_isShared_4541_ = v_isSharedCheck_4545_;
goto v_resetjp_4539_;
}
else
{
lean_inc(v_a_4538_);
lean_dec(v___x_4511_);
v___x_4540_ = lean_box(0);
v_isShared_4541_ = v_isSharedCheck_4545_;
goto v_resetjp_4539_;
}
v_resetjp_4539_:
{
lean_object* v___x_4543_; 
if (v_isShared_4541_ == 0)
{
v___x_4543_ = v___x_4540_;
goto v_reusejp_4542_;
}
else
{
lean_object* v_reuseFailAlloc_4544_; 
v_reuseFailAlloc_4544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4544_, 0, v_a_4538_);
v___x_4543_ = v_reuseFailAlloc_4544_;
goto v_reusejp_4542_;
}
v_reusejp_4542_:
{
return v___x_4543_;
}
}
}
}
}
else
{
lean_object* v_a_4547_; lean_object* v___x_4549_; uint8_t v_isShared_4550_; uint8_t v_isSharedCheck_4554_; 
lean_dec(v_a_4498_);
lean_dec(v_a_4496_);
lean_dec(v_a_4494_);
lean_dec_ref(v_dec_4487_);
lean_dec(v_hName_4486_);
lean_dec_ref(v_p_4485_);
lean_dec(v_mvarId_4484_);
v_a_4547_ = lean_ctor_get(v___x_4501_, 0);
v_isSharedCheck_4554_ = !lean_is_exclusive(v___x_4501_);
if (v_isSharedCheck_4554_ == 0)
{
v___x_4549_ = v___x_4501_;
v_isShared_4550_ = v_isSharedCheck_4554_;
goto v_resetjp_4548_;
}
else
{
lean_inc(v_a_4547_);
lean_dec(v___x_4501_);
v___x_4549_ = lean_box(0);
v_isShared_4550_ = v_isSharedCheck_4554_;
goto v_resetjp_4548_;
}
v_resetjp_4548_:
{
lean_object* v___x_4552_; 
if (v_isShared_4550_ == 0)
{
v___x_4552_ = v___x_4549_;
goto v_reusejp_4551_;
}
else
{
lean_object* v_reuseFailAlloc_4553_; 
v_reuseFailAlloc_4553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4553_, 0, v_a_4547_);
v___x_4552_ = v_reuseFailAlloc_4553_;
goto v_reusejp_4551_;
}
v_reusejp_4551_:
{
return v___x_4552_;
}
}
}
}
else
{
lean_object* v_a_4555_; lean_object* v___x_4557_; uint8_t v_isShared_4558_; uint8_t v_isSharedCheck_4562_; 
lean_dec(v_a_4496_);
lean_dec(v_a_4494_);
lean_dec_ref(v_dec_4487_);
lean_dec(v_hName_4486_);
lean_dec_ref(v_p_4485_);
lean_dec(v_mvarId_4484_);
v_a_4555_ = lean_ctor_get(v___x_4497_, 0);
v_isSharedCheck_4562_ = !lean_is_exclusive(v___x_4497_);
if (v_isSharedCheck_4562_ == 0)
{
v___x_4557_ = v___x_4497_;
v_isShared_4558_ = v_isSharedCheck_4562_;
goto v_resetjp_4556_;
}
else
{
lean_inc(v_a_4555_);
lean_dec(v___x_4497_);
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
lean_dec(v_a_4494_);
lean_dec_ref(v_dec_4487_);
lean_dec(v_hName_4486_);
lean_dec_ref(v_p_4485_);
lean_dec(v_mvarId_4484_);
v_a_4563_ = lean_ctor_get(v___x_4495_, 0);
v_isSharedCheck_4570_ = !lean_is_exclusive(v___x_4495_);
if (v_isSharedCheck_4570_ == 0)
{
v___x_4565_ = v___x_4495_;
v_isShared_4566_ = v_isSharedCheck_4570_;
goto v_resetjp_4564_;
}
else
{
lean_inc(v_a_4563_);
lean_dec(v___x_4495_);
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
else
{
lean_object* v_a_4571_; lean_object* v___x_4573_; uint8_t v_isShared_4574_; uint8_t v_isSharedCheck_4578_; 
lean_dec_ref(v_dec_4487_);
lean_dec(v_hName_4486_);
lean_dec_ref(v_p_4485_);
lean_dec(v_mvarId_4484_);
v_a_4571_ = lean_ctor_get(v___x_4493_, 0);
v_isSharedCheck_4578_ = !lean_is_exclusive(v___x_4493_);
if (v_isSharedCheck_4578_ == 0)
{
v___x_4573_ = v___x_4493_;
v_isShared_4574_ = v_isSharedCheck_4578_;
goto v_resetjp_4572_;
}
else
{
lean_inc(v_a_4571_);
lean_dec(v___x_4493_);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_byCasesDec___lam__0___boxed(lean_object* v_mvarId_4579_, lean_object* v_p_4580_, lean_object* v_hName_4581_, lean_object* v_dec_4582_, lean_object* v___y_4583_, lean_object* v___y_4584_, lean_object* v___y_4585_, lean_object* v___y_4586_, lean_object* v___y_4587_){
_start:
{
lean_object* v_res_4588_; 
v_res_4588_ = l_Lean_MVarId_byCasesDec___lam__0(v_mvarId_4579_, v_p_4580_, v_hName_4581_, v_dec_4582_, v___y_4583_, v___y_4584_, v___y_4585_, v___y_4586_);
lean_dec(v___y_4586_);
lean_dec_ref(v___y_4585_);
lean_dec(v___y_4584_);
lean_dec_ref(v___y_4583_);
return v_res_4588_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_byCasesDec(lean_object* v_mvarId_4589_, lean_object* v_p_4590_, lean_object* v_dec_4591_, lean_object* v_hName_4592_, lean_object* v_a_4593_, lean_object* v_a_4594_, lean_object* v_a_4595_, lean_object* v_a_4596_){
_start:
{
lean_object* v___f_4598_; lean_object* v___x_4599_; 
lean_inc(v_mvarId_4589_);
v___f_4598_ = lean_alloc_closure((void*)(l_Lean_MVarId_byCasesDec___lam__0___boxed), 9, 4);
lean_closure_set(v___f_4598_, 0, v_mvarId_4589_);
lean_closure_set(v___f_4598_, 1, v_p_4590_);
lean_closure_set(v___f_4598_, 2, v_hName_4592_);
lean_closure_set(v___f_4598_, 3, v_dec_4591_);
v___x_4599_ = l_Lean_MVarId_withContext___at___00Lean_Meta_generalizeTargetsEq_spec__2___redArg(v_mvarId_4589_, v___f_4598_, v_a_4593_, v_a_4594_, v_a_4595_, v_a_4596_);
return v___x_4599_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_byCasesDec___boxed(lean_object* v_mvarId_4600_, lean_object* v_p_4601_, lean_object* v_dec_4602_, lean_object* v_hName_4603_, lean_object* v_a_4604_, lean_object* v_a_4605_, lean_object* v_a_4606_, lean_object* v_a_4607_, lean_object* v_a_4608_){
_start:
{
lean_object* v_res_4609_; 
v_res_4609_ = l_Lean_MVarId_byCasesDec(v_mvarId_4600_, v_p_4601_, v_dec_4602_, v_hName_4603_, v_a_4604_, v_a_4605_, v_a_4606_, v_a_4607_);
lean_dec(v_a_4607_);
lean_dec_ref(v_a_4606_);
lean_dec(v_a_4605_);
lean_dec_ref(v_a_4604_);
return v_res_4609_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4661_; lean_object* v___x_4662_; lean_object* v___x_4663_; 
v___x_4661_ = lean_unsigned_to_nat(4241171151u);
v___x_4662_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_));
v___x_4663_ = l_Lean_Name_num___override(v___x_4662_, v___x_4661_);
return v___x_4663_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4665_; lean_object* v___x_4666_; lean_object* v___x_4667_; 
v___x_4665_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_));
v___x_4666_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_);
v___x_4667_ = l_Lean_Name_str___override(v___x_4666_, v___x_4665_);
return v___x_4667_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4669_; lean_object* v___x_4670_; lean_object* v___x_4671_; 
v___x_4669_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_));
v___x_4670_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_);
v___x_4671_ = l_Lean_Name_str___override(v___x_4670_, v___x_4669_);
return v___x_4671_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4672_; lean_object* v___x_4673_; lean_object* v___x_4674_; 
v___x_4672_ = lean_unsigned_to_nat(2u);
v___x_4673_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_);
v___x_4674_ = l_Lean_Name_num___override(v___x_4673_, v___x_4672_);
return v___x_4674_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4676_; uint8_t v___x_4677_; lean_object* v___x_4678_; lean_object* v___x_4679_; 
v___x_4676_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_));
v___x_4677_ = 0;
v___x_4678_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_);
v___x_4679_ = l_Lean_registerTraceClass(v___x_4676_, v___x_4677_, v___x_4678_);
return v___x_4679_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2____boxed(lean_object* v_a_4680_){
_start:
{
lean_object* v_res_4681_; 
v_res_4681_ = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Cases_4241171151____hygCtx___hyg_2_();
return v_res_4681_;
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
